#!/usr/bin/env python3
"""
Complete Stock Monitor - 24/7 Stock Alert System
Monitors stocks for 20% gains within 2-hour trading windows and sends Discord alerts
All-in-one file for easy GitHub upload

Required packages: pip install yfinance schedule requests feedparser pytz

Environment variables needed:
- DISCORD_WEBHOOK_URL: Your Discord webhook URL for alerts

Usage:
1. Set DISCORD_WEBHOOK_URL environment variable
2. Create config.json with your stock symbols (see DEFAULT_CONFIG below)
3. Run: python complete_stock_monitor.py
"""

import os
import time
import schedule
import logging
import json
import yfinance as yf
import requests
import feedparser
from datetime import datetime, timedelta, time as time_obj
import pytz
from collections import defaultdict, deque
from typing import Dict, List, Optional, Tuple
import calendar
import re

# ======================== DEFAULT CONFIGURATION ========================

DEFAULT_CONFIG = {
    "symbols": ["AAPL", "GOOGL", "MSFT", "AMZN", "TSLA", "META", "NVDA", "AMD"],
    "gain_threshold": 20.0,
    "time_window_hours": 2,
    "check_interval_minutes": 10,
    "market_hours_aware": True,
    "news_api_key": None,
    "max_retries": 3,
    "retry_delay": 30,
    "request_delay": 3
}

# ======================== LOGGING SETUP ========================

class AESTFormatter(logging.Formatter):
    def converter(self, timestamp):
        dt = datetime.fromtimestamp(timestamp)
        aest = pytz.timezone('Australia/Sydney')
        return dt.replace(tzinfo=pytz.UTC).astimezone(aest)
    
    def formatTime(self, record, datefmt=None):
        dt = self.converter(record.created)
        if datefmt:
            s = dt.strftime(datefmt)
        else:
            s = dt.strftime('%Y-%m-%d %H:%M:%S %Z')
        return s

def setup_logging():
    """Setup logging with AEST timestamps"""
    logger = logging.getLogger()
    logger.setLevel(logging.INFO)
    
    # Create console handler
    handler = logging.StreamHandler()
    formatter = AESTFormatter('%(asctime)s - %(levelname)s - %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    
    # Create file handler
    file_handler = logging.FileHandler('stock_monitor.log')
    file_handler.setFormatter(formatter)
    logger.addHandler(file_handler)
    
    return logger

# ======================== MARKET HOURS HELPER ========================

class MarketHours:
    """Helper class to determine US stock market trading hours"""
    
    def __init__(self):
        self.eastern = pytz.timezone('US/Eastern')
        
        # Trading hours (all times in Eastern)
        self.premarket_start = time_obj(4, 0)      # 4:00 AM
        self.regular_start = time_obj(9, 30)       # 9:30 AM  
        self.regular_end = time_obj(16, 0)         # 4:00 PM
        self.afterhours_end = time_obj(20, 0)      # 8:00 PM
        
    def get_market_holidays_2025(self) -> List[datetime]:
        """Get list of market holidays for 2025"""
        holidays = [
            datetime(2025, 1, 1),   # New Year's Day
            datetime(2025, 1, 20),  # MLK Day
            datetime(2025, 2, 17),  # Presidents Day
            datetime(2025, 4, 18),  # Good Friday
            datetime(2025, 5, 26),  # Memorial Day
            datetime(2025, 6, 19),  # Juneteenth
            datetime(2025, 7, 4),   # Independence Day
            datetime(2025, 9, 1),   # Labor Day
            datetime(2025, 11, 27), # Thanksgiving
            datetime(2025, 12, 25), # Christmas
        ]
        return holidays
    
    def is_market_holiday(self, dt: datetime) -> bool:
        """Check if given date is a market holiday"""
        holidays = self.get_market_holidays_2025()
        date_only = dt.date()
        return any(holiday.date() == date_only for holiday in holidays)
    
    def is_weekend(self, dt: datetime) -> bool:
        """Check if given date is weekend"""
        return dt.weekday() >= 5  # Saturday=5, Sunday=6
    
    def is_extended_trading_hours(self, dt: datetime) -> bool:
        """Check if given datetime is within extended trading hours"""
        # Convert to Eastern time
        if dt.tzinfo is None:
            dt = pytz.UTC.localize(dt)
        dt_et = dt.astimezone(self.eastern)
        
        # Check if it's a trading day
        if self.is_weekend(dt_et) or self.is_market_holiday(dt_et):
            return False
        
        # Check if within extended hours
        current_time = dt_et.time()
        return self.premarket_start <= current_time <= self.afterhours_end
    
    def is_regular_trading_hours(self, dt: datetime) -> bool:
        """Check if given datetime is within regular trading hours"""
        if not self.is_extended_trading_hours(dt):
            return False
            
        # Convert to Eastern time
        if dt.tzinfo is None:
            dt = pytz.UTC.localize(dt)
        dt_et = dt.astimezone(self.eastern)
        
        current_time = dt_et.time()
        return self.regular_start <= current_time < self.regular_end
    
    def get_trading_status(self, dt: datetime = None) -> str:
        """Get current trading status as human-readable string"""
        if dt is None:
            dt = datetime.now(pytz.UTC)
        
        if self.is_regular_trading_hours(dt):
            return "Regular Hours"
        elif self.is_extended_trading_hours(dt):
            if dt.astimezone(self.eastern).time() < self.regular_start:
                return "Pre-Market"
            else:
                return "After Hours"
        elif self.is_weekend(dt):
            return "Weekend"
        elif self.is_market_holiday(dt):
            return "Market Holiday"
        else:
            return "Market Closed"
    
    def calculate_trading_minutes_between(self, start_dt: datetime, end_dt: datetime) -> int:
        """Calculate actual trading minutes between two datetimes"""
        if start_dt >= end_dt:
            return 0
        
        if start_dt.tzinfo is None:
            start_dt = pytz.UTC.localize(start_dt)
        if end_dt.tzinfo is None:
            end_dt = pytz.UTC.localize(end_dt)
        
        total_minutes = 0
        current_dt = start_dt
        
        while current_dt < end_dt:
            if self.is_extended_trading_hours(current_dt):
                # Count minutes in trading hours
                next_minute = current_dt + timedelta(minutes=1)
                if next_minute <= end_dt:
                    total_minutes += 1
            current_dt += timedelta(minutes=1)
        
        return total_minutes

# ======================== PRICE TRACKER ========================

class PriceTracker:
    def __init__(self, market_hours_aware=True):
        """Initialize price tracker with rolling windows"""
        # Store price history for each symbol
        # Each entry: (timestamp, price)
        self.price_history = defaultdict(deque)
        self.max_history_hours = 3  # Keep 3 hours of history for safety
        self.market_hours_aware = market_hours_aware
        self.market_hours = MarketHours() if market_hours_aware else None
        
        mode = "market-hours-aware" if market_hours_aware else "continuous"
        logging.info(f"Price Tracker initialized ({mode})")
    
    def update_price(self, symbol, price):
        """Update price for a symbol with current timestamp"""
        aest = pytz.timezone('Australia/Sydney')
        timestamp = datetime.now(aest)
        
        # Add new price point
        self.price_history[symbol].append((timestamp, price))
        
        # Clean old entries (older than max_history_hours)
        cutoff_time = timestamp - timedelta(hours=self.max_history_hours)
        
        while (self.price_history[symbol] and 
               self.price_history[symbol][0][0] < cutoff_time):
            self.price_history[symbol].popleft()
    
    def get_lowest_price_in_window(self, symbol, hours=2):
        """Get lowest price within specified hours using trading-time logic"""
        if symbol not in self.price_history or not self.price_history[symbol]:
            return None, None, None
        
        current_time = datetime.now(pytz.timezone('Australia/Sydney'))
        history = list(self.price_history[symbol])
        
        if not self.market_hours_aware:
            # Simple time-based window
            cutoff_time = current_time - timedelta(hours=hours)
            valid_prices = [(ts, price) for ts, price in history if ts >= cutoff_time]
        else:
            # Market-hours-aware window (only count trading minutes)
            target_trading_minutes = hours * 60
            trading_minutes_found = 0
            valid_prices = []
            
            # Go backwards through history, counting only trading minutes
            for timestamp, price in reversed(history):
                if self.market_hours.is_extended_trading_hours(timestamp):
                    valid_prices.append((timestamp, price))
                    trading_minutes_found += 1
                    
                    if trading_minutes_found >= target_trading_minutes:
                        break
            
            valid_prices.reverse()  # Restore chronological order
        
        if not valid_prices:
            return None, None, None
        
        # Find the lowest price in the valid window
        lowest_price = min(valid_prices, key=lambda x: x[1])
        lowest_timestamp, lowest_value = lowest_price
        
        # Calculate actual duration
        latest_timestamp = max(valid_prices, key=lambda x: x[0])[0]
        if self.market_hours_aware:
            # Calculate trading minutes between lowest point and now
            duration_minutes = self.market_hours.calculate_trading_minutes_between(
                lowest_timestamp, latest_timestamp
            )
        else:
            # Simple time difference
            duration_minutes = int((latest_timestamp - lowest_timestamp).total_seconds() / 60)
        
        return lowest_value, lowest_timestamp, duration_minutes

# ======================== NEWS FILTER ========================

class NewsFilter:
    def __init__(self, news_api_key=None):
        """Initialize news filter"""
        self.news_api_key = news_api_key or os.getenv('NEWS_API_KEY')
        self.cache = {}
        self.cache_duration_hours = 1  # Cache news for 1 hour
        
        logging.info("News Filter initialized")
    
    def has_company_news(self, symbol):
        """Check if stock has recent company-specific news"""
        # Check cache first
        cache_key = symbol
        current_time = datetime.now(pytz.timezone('Australia/Sydney'))
        
        if cache_key in self.cache:
            cached_time, cached_result = self.cache[cache_key]
            if current_time - cached_time < timedelta(hours=self.cache_duration_hours):
                return cached_result
        
        # Check multiple news sources
        has_news = self._check_news_sources(symbol)
        
        # Cache the result
        self.cache[cache_key] = (current_time, has_news)
        
        return has_news
    
    def _check_news_sources(self, symbol):
        """Check multiple news sources for company-specific news"""
        sources = [
            self._check_yahoo_finance_news,
            self._check_google_news
        ]
        
        for source_func in sources:
            try:
                if source_func(symbol):
                    return True
            except Exception as e:
                logging.warning(f"News source check failed for {symbol}: {e}")
        
        return False
    
    def _check_yahoo_finance_news(self, symbol):
        """Check Yahoo Finance news RSS feed"""
        try:
            url = f"https://feeds.finance.yahoo.com/rss/2.0/headline?s={symbol}&region=US&lang=en-US"
            response = requests.get(url, timeout=10)
            
            if response.status_code == 200:
                feed = feedparser.parse(response.content)
                
                # Check if there are recent entries (last 24 hours)
                cutoff_time = datetime.now(pytz.UTC) - timedelta(hours=24)
                
                for entry in feed.entries[:5]:  # Check first 5 entries
                    if hasattr(entry, 'published_parsed'):
                        entry_time = datetime(*entry.published_parsed[:6], tzinfo=pytz.UTC)
                        
                        if entry_time > cutoff_time:
                            # Check if it's company-specific news
                            if self._is_company_specific_news(entry.title, symbol):
                                logging.info(f"{symbol}: Company news found - {entry.title}")
                                return True
                
        except Exception as e:
            logging.debug(f"{symbol}: Yahoo Finance news check failed: {e}")
        
        return False
    
    def _check_google_news(self, symbol):
        """Check Google News RSS feed"""
        try:
            query = f"{symbol} stock"
            url = f"https://news.google.com/rss/search?q={query}&hl=en-US&gl=US&ceid=US:en"
            
            response = requests.get(url, timeout=10)
            
            if response.status_code == 200:
                feed = feedparser.parse(response.content)
                
                # Check recent entries
                cutoff_time = datetime.now(pytz.UTC) - timedelta(hours=24)
                
                for entry in feed.entries[:3]:  # Check first 3 entries
                    if hasattr(entry, 'published_parsed'):
                        entry_time = datetime(*entry.published_parsed[:6], tzinfo=pytz.UTC)
                        
                        if entry_time > cutoff_time:
                            if self._is_company_specific_news(entry.title, symbol):
                                logging.info(f"{symbol}: Google news found - {entry.title}")
                                return True
                
        except Exception as e:
            logging.debug(f"{symbol}: Google News check failed: {e}")
        
        return False
    
    def _is_company_specific_news(self, title, symbol):
        """Determine if news is company-specific vs general market news"""
        title_lower = title.lower()
        symbol_lower = symbol.lower()
        
        # Company-specific keywords
        company_keywords = [
            'earnings', 'revenue', 'profit', 'loss', 'ceo', 'cfo',
            'acquisition', 'merger', 'partnership', 'deal', 'contract',
            'product launch', 'new product', 'upgrade', 'downgrade',
            'lawsuit', 'settlement', 'investigation', 'sec',
            'guidance', 'forecast', 'outlook', 'results',
            'dividend', 'split', 'buyback', 'insider'
        ]
        
        # Market/general keywords that should NOT trigger filtering
        general_keywords = [
            'market', 'sector', 'industry', 'economy', 'fed',
            'interest rates', 'inflation', 'gdp', 'jobs report',
            'top gainers', 'best performers', 'rally', 'broad market'
        ]
        
        # If it contains general market keywords, allow it
        for keyword in general_keywords:
            if keyword in title_lower:
                return False
        
        # If it contains the stock symbol and company-specific keywords
        if symbol_lower in title_lower:
            for keyword in company_keywords:
                if keyword in title_lower:
                    return True
        
        return False

# ======================== DISCORD NOTIFIER ========================

class DiscordNotifier:
    def __init__(self, webhook_url):
        """Initialize Discord notifier"""
        self.webhook_url = webhook_url
        self.max_retries = 3
        self.retry_delay = 5
        
        logging.info("Discord Notifier initialized")
    
    def send_alert(self, symbol, current_price, lowest_price, percentage_change, duration_minutes=None):
        """Send stock alert to Discord"""
        # Get AEST timestamp
        aest = pytz.timezone('Australia/Sydney')
        timestamp = datetime.now(aest).strftime('%Y-%m-%d %H:%M:%S AEST')
        
        # Calculate price change
        price_change = current_price - lowest_price
        
        # Format duration
        if duration_minutes is not None:
            if duration_minutes < 60:
                duration_text = f"{duration_minutes} minutes"
            else:
                hours = duration_minutes // 60
                mins = duration_minutes % 60
                if mins > 0:
                    duration_text = f"{hours}h {mins}m"
                else:
                    duration_text = f"{hours} hours"
        else:
            duration_text = "within 2 hours"
        
        # Create embed message
        embed = {
            "title": f"🚀 Stock Alert: {symbol}",
            "description": f"**{percentage_change:.2f}%** gain in {duration_text}!",
            "color": 0x00ff00,  # Green color
            "fields": [
                {
                    "name": "Current Price",
                    "value": f"${current_price:.2f}",
                    "inline": True
                },
                {
                    "name": "Starting Price",
                    "value": f"${lowest_price:.2f}",
                    "inline": True
                },
                {
                    "name": "Change",
                    "value": f"+${price_change:.2f} (+{percentage_change:.2f}%)",
                    "inline": True
                },
                {
                    "name": "Duration",
                    "value": duration_text,
                    "inline": True
                },
                {
                    "name": "Time (AEST)",
                    "value": timestamp,
                    "inline": False
                }
            ],
            "footer": {
                "text": "Stock Monitor Alert System"
            }
        }
        
        payload = {
            "embeds": [embed]
        }
        
        return self._send_webhook(payload)
    
    def send_cycle_notification(self, processed_count, alerts_sent, errors):
        """Send cycle completion notification"""
        # Get AEST timestamp
        aest = pytz.timezone('Australia/Sydney')
        timestamp = datetime.now(aest).strftime('%Y-%m-%d %H:%M:%S AEST')
        
        # Create embed message
        embed = {
            "title": "📊 Monitoring Cycle Complete",
            "description": f"Finished checking {processed_count} stocks",
            "color": 0x3498db,  # Blue color
            "fields": [
                {
                    "name": "Stocks Processed",
                    "value": str(processed_count),
                    "inline": True
                },
                {
                    "name": "Alerts Sent",
                    "value": str(alerts_sent),
                    "inline": True
                },
                {
                    "name": "Errors",
                    "value": str(errors),
                    "inline": True
                },
                {
                    "name": "Time (AEST)",
                    "value": timestamp,
                    "inline": False
                }
            ],
            "footer": {
                "text": "Next check in 10 minutes"
            }
        }
        
        payload = {
            "embeds": [embed]
        }
        
        return self._send_webhook(payload)
    
    def _send_webhook(self, payload):
        """Send webhook with retry logic"""
        for attempt in range(self.max_retries):
            try:
                response = requests.post(
                    self.webhook_url,
                    json=payload,
                    timeout=10
                )
                
                if response.status_code == 204:
                    return True
                else:
                    logging.warning(f"Discord webhook failed with status {response.status_code}")
                    
            except Exception as e:
                logging.error(f"Discord webhook attempt {attempt + 1} failed: {e}")
                
                if attempt < self.max_retries - 1:
                    time.sleep(self.retry_delay)
        
        return False

# ======================== STOCK MONITOR ========================

class StockMonitor:
    def __init__(self, config, discord_webhook):
        """Initialize the stock monitor"""
        self.config = config
        self.symbols = config.get('symbols', [])
        self.gain_threshold = config.get('gain_threshold', 20.0)
        self.time_window_hours = config.get('time_window_hours', 2)
        self.max_retries = config.get('max_retries', 3)
        self.retry_delay = config.get('retry_delay', 30)
        self.request_delay = config.get('request_delay', 2)
        
        # Initialize components
        market_hours_aware = config.get('market_hours_aware', True)
        self.price_tracker = PriceTracker(market_hours_aware=market_hours_aware)
        self.news_filter = NewsFilter(config.get('news_api_key'))
        self.discord_notifier = DiscordNotifier(discord_webhook)
        
        # Track daily alerts to prevent duplicates
        self.daily_alerts = defaultdict(set)
        self.last_reset_date = datetime.now(pytz.timezone('Australia/Sydney')).date()
        
        logging.info(f"Stock Monitor initialized with {len(self.symbols)} symbols")
    
    def check_stocks(self):
        """Check all stocks for 20% gains within 2-hour window"""
        cycle_start_time = datetime.now(pytz.timezone('Australia/Sydney'))
        logging.info(f"Starting stock check cycle for {len(self.symbols)} symbols...")
        
        # Check if we need to reset daily alerts
        current_date = datetime.now(pytz.timezone('Australia/Sydney')).date()
        if current_date != self.last_reset_date:
            self.reset_daily_alerts()
        
        alerts_sent = 0
        errors = 0
        processed = 0
        
        for symbol in self.symbols:
            try:
                processed += 1
                if self._check_single_stock(symbol):
                    alerts_sent += 1
                
                # Add delay between requests to avoid rate limiting
                if processed % 10 == 0:
                    time.sleep(self.request_delay)
                
                # Log progress every 100 symbols
                if processed % 100 == 0:
                    logging.info(f"Progress: {processed}/{len(self.symbols)} symbols checked")
                    
            except Exception as e:
                errors += 1
                if errors <= 10:  # Only log first 10 errors to avoid spam
                    logging.error(f"Error checking {symbol}: {e}")
        
        # Send cycle completion notification
        cycle_duration = (datetime.now(pytz.timezone('Australia/Sydney')) - cycle_start_time).total_seconds()
        logging.info(f"Stock check cycle completed. {processed} processed, {alerts_sent} alerts sent, {errors} errors.")
        
        try:
            self.discord_notifier.send_cycle_notification(processed, alerts_sent, errors)
            logging.info("Discord cycle completion notification sent successfully")
        except Exception as e:
            logging.warning(f"Failed to send cycle notification: {e}")
    
    def _check_single_stock(self, symbol):
        """Check a single stock for gain threshold"""
        try:
            # Get current price
            current_price = self._get_stock_price(symbol)
            if current_price is None:
                return False
            
            # Update price history
            self.price_tracker.update_price(symbol, current_price)
            
            # Get lowest price in the time window
            lowest_price, lowest_timestamp, duration_minutes = self.price_tracker.get_lowest_price_in_window(
                symbol, self.time_window_hours
            )
            
            if lowest_price is None:
                return False
            
            # Calculate percentage change
            percentage_change = ((current_price - lowest_price) / lowest_price) * 100
            
            # Check if it meets the gain threshold
            if percentage_change >= self.gain_threshold:
                # Check if we already sent an alert for this stock today
                today = datetime.now(pytz.timezone('Australia/Sydney')).date()
                if symbol in self.daily_alerts[today]:
                    return False
                
                # Check for company-specific news
                if self.news_filter.has_company_news(symbol):
                    logging.info(f"{symbol}: Skipping alert due to recent company news")
                    return False
                
                # Send alert
                success = self.discord_notifier.send_alert(
                    symbol, current_price, lowest_price, percentage_change, duration_minutes
                )
                
                if success:
                    # Mark as alerted for today
                    self.daily_alerts[today].add(symbol)
                    logging.info(f"Alert sent for {symbol}: {percentage_change:.2f}% gain")
                    return True
                else:
                    logging.error(f"Failed to send alert for {symbol}")
            
            return False
            
        except Exception as e:
            logging.error(f"Error checking {symbol}: {e}")
            return False
    
    def _get_stock_price(self, symbol):
        """Get current stock price with retries"""
        for attempt in range(self.max_retries):
            try:
                ticker = yf.Ticker(symbol)
                
                # Try to get current price from info
                info = ticker.info
                if info and 'currentPrice' in info:
                    return float(info['currentPrice'])
                
                # Fallback to recent history
                hist = ticker.history(period="1d", interval="1m")
                if not hist.empty:
                    return float(hist['Close'].iloc[-1])
                
                logging.warning(f"{symbol}: No Yahoo Finance data available")
                return None
                
            except Exception as e:
                logging.warning(f"{symbol}: Yahoo Finance attempt {attempt + 1} failed: {e}")
                if attempt < self.max_retries - 1:
                    time.sleep(self.retry_delay)
        
        logging.error(f"{symbol}: All price sources failed")
        return None
    
    def reset_daily_alerts(self):
        """Reset daily alert tracking"""
        aest = pytz.timezone('Australia/Sydney')
        current_date = datetime.now(aest).date()
        
        # Keep only today's alerts, remove older ones
        keys_to_remove = [date for date in self.daily_alerts.keys() if date < current_date]
        for key in keys_to_remove:
            del self.daily_alerts[key]
        
        self.last_reset_date = current_date
        logging.info("Daily alerts reset")

# ======================== CONFIGURATION MANAGEMENT ========================

def load_config():
    """Load configuration from config.json or create default"""
    try:
        with open('config.json', 'r') as f:
            config = json.load(f)
        logging.info("Configuration loaded from config.json")
        return config
    except FileNotFoundError:
        logging.info("config.json not found, creating default configuration")
        with open('config.json', 'w') as f:
            json.dump(DEFAULT_CONFIG, f, indent=4)
        return DEFAULT_CONFIG
    except json.JSONDecodeError as e:
        logging.error(f"Error parsing config.json: {e}")
        return DEFAULT_CONFIG

# ======================== MAIN EXECUTION ========================

def main():
    """Main entry point for the stock monitoring service"""
    logger = setup_logging()
    logger.info("Starting Stock Monitor Service...")
    
    # Load configuration
    config = load_config()
    
    # Validate Discord webhook URL
    discord_webhook = os.getenv('DISCORD_WEBHOOK_URL')
    
    if not discord_webhook:
        logger.error("DISCORD_WEBHOOK_URL environment variable not set!")
        logger.error("Please set your Discord webhook URL:")
        logger.error("export DISCORD_WEBHOOK_URL='https://discord.com/api/webhooks/YOUR_WEBHOOK_URL'")
        return
    
    # Initialize stock monitor
    monitor = StockMonitor(config, discord_webhook)
    
    # Schedule monitoring every 10 minutes
    check_interval = config.get('check_interval_minutes', 10)
    schedule.every(check_interval).minutes.do(monitor.check_stocks)
    
    # Schedule daily reset at market open (9:30 AM AEST)
    schedule.every().day.at("09:30").do(monitor.reset_daily_alerts)
    
    logger.info(f"Monitoring {len(config.get('symbols', []))} stocks...")
    logger.info(f"Service started. Checking stocks every {check_interval} minutes.")
    
    # Run initial check
    monitor.check_stocks()
    
    # Keep the service running
    try:
        while True:
            schedule.run_pending()
            time.sleep(60)  # Check every minute for scheduled tasks
    except KeyboardInterrupt:
        logger.info("Service stopped by user")
    except Exception as e:
        logger.error(f"Unexpected error: {e}")
        logger.info("Restarting service in 60 seconds...")
        time.sleep(60)
        main()  # Restart the service

if __name__ == "__main__":
    main()