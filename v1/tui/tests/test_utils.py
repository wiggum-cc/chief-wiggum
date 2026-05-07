"""Tests for shared utilities."""

import time
from wiggum_tui.utils import format_relative_time


class TestFormatRelativeTime:
    """Tests for format_relative_time."""

    def test_just_now(self):
        """Future timestamps should show 'just now'."""
        future = int(time.time()) + 100
        assert format_relative_time(future) == "just now"

    def test_seconds_ago(self):
        """Recent timestamps should show seconds."""
        now = int(time.time())
        result = format_relative_time(now - 5)
        assert "seconds ago" in result

    def test_one_second_ago(self):
        """Single second should use singular form."""
        now = int(time.time())
        result = format_relative_time(now - 1)
        assert result == "1 second ago"

    def test_minutes_ago(self):
        """Timestamps 1-59 minutes ago should show minutes."""
        now = int(time.time())
        result = format_relative_time(now - 180)  # 3 minutes
        assert "3 minutes ago" == result

    def test_one_minute_ago(self):
        """Single minute should use singular form."""
        now = int(time.time())
        result = format_relative_time(now - 60)
        assert result == "1 minute ago"

    def test_hours_ago(self):
        """Timestamps 1-23 hours ago should show hours."""
        now = int(time.time())
        result = format_relative_time(now - 7200)  # 2 hours
        assert "2 hours ago" == result

    def test_one_hour_ago(self):
        """Single hour should use singular form."""
        now = int(time.time())
        result = format_relative_time(now - 3600)
        assert result == "1 hour ago"

    def test_days_ago(self):
        """Timestamps 1-7 days ago should show days."""
        now = int(time.time())
        result = format_relative_time(now - 172800)  # 2 days
        assert "2 days ago" == result

    def test_one_day_ago(self):
        """Single day should use singular form."""
        now = int(time.time())
        result = format_relative_time(now - 86400)
        assert result == "1 day ago"

    def test_more_than_7_days_shows_date(self):
        """Timestamps >7 days should show ISO date."""
        now = int(time.time())
        result = format_relative_time(now - 864000)  # 10 days
        # Should be in YYYY-MM-DD HH:MM format
        assert "-" in result
        assert ":" in result
        assert "ago" not in result

    def test_zero_seconds_ago(self):
        """Zero diff should show '0 seconds ago'."""
        now = int(time.time())
        result = format_relative_time(now)
        assert "second" in result
