"""Tests for metrics_reader module."""

import json
from pathlib import Path

from wiggum_tui.data.metrics_reader import (
    read_metrics,
    format_tokens,
    format_cost,
    format_duration,
    format_context,
)
from wiggum_tui.data.models import Metrics


class TestReadMetrics:
    """Tests for read_metrics function."""

    def test_file_not_found(self, tmp_path: Path):
        result = read_metrics(tmp_path / "nonexistent.json")
        assert isinstance(result, Metrics)
        assert result.total_workers == 0
        assert result.total_cost == 0.0

    def test_empty_file(self, tmp_path: Path):
        metrics_file = tmp_path / "metrics.json"
        metrics_file.write_text("")
        result = read_metrics(metrics_file)
        assert result.total_workers == 0

    def test_invalid_json(self, tmp_path: Path):
        metrics_file = tmp_path / "metrics.json"
        metrics_file.write_text("not valid json")
        result = read_metrics(metrics_file)
        assert result.total_workers == 0

    def test_parses_summary(self, tmp_path: Path, sample_metrics_data: dict):
        metrics_file = tmp_path / "metrics.json"
        metrics_file.write_text(json.dumps(sample_metrics_data))

        result = read_metrics(metrics_file)

        assert result.total_workers == 5
        assert result.successful_workers == 3
        assert result.failed_workers == 1
        assert result.success_rate == 75.0
        assert result.total_time == "01:23:45"
        assert result.total_time_seconds == 5025
        assert result.total_cost == 2.50

    def test_parses_tokens(self, tmp_path: Path, sample_metrics_data: dict):
        metrics_file = tmp_path / "metrics.json"
        metrics_file.write_text(json.dumps(sample_metrics_data))

        result = read_metrics(metrics_file)

        assert result.tokens.input == 150000
        assert result.tokens.output == 50000
        assert result.tokens.cache_creation == 10000
        assert result.tokens.cache_read == 80000
        assert result.tokens.total == 290000

    def test_parses_cost_breakdown(self, tmp_path: Path, sample_metrics_data: dict):
        metrics_file = tmp_path / "metrics.json"
        metrics_file.write_text(json.dumps(sample_metrics_data))

        result = read_metrics(metrics_file)

        assert result.cost_breakdown.input == 1.50
        assert result.cost_breakdown.output == 0.75
        assert result.cost_breakdown.cache_creation == 0.15
        assert result.cost_breakdown.cache_read == 0.10
        assert result.cost_breakdown.total == 2.50

    def test_parses_context(self, tmp_path: Path, sample_metrics_data: dict):
        metrics_file = tmp_path / "metrics.json"
        metrics_file.write_text(json.dumps(sample_metrics_data))

        result = read_metrics(metrics_file)

        assert result.context.tokens == 45000
        assert result.context.size == 200000
        assert result.context.percent == 22.5

    def test_parses_workers(self, tmp_path: Path, sample_metrics_data: dict):
        metrics_file = tmp_path / "metrics.json"
        metrics_file.write_text(json.dumps(sample_metrics_data))

        result = read_metrics(metrics_file)

        assert len(result.workers) == 1
        worker = result.workers[0]
        assert worker.worker_id == "worker-TEST-001-1700000000"
        assert worker.status == "success"
        assert worker.time_spent == "00:15:30"
        assert worker.time_seconds == 930
        assert worker.cost == 0.50
        assert worker.pr_url == "https://github.com/example/repo/pull/123"
        assert worker.tokens.input == 30000
        assert worker.tokens.output == 10000
        assert worker.context.percent == 4.5

    def test_handles_missing_sections(self, tmp_path: Path):
        metrics_file = tmp_path / "metrics.json"
        metrics_file.write_text("{}")

        result = read_metrics(metrics_file)

        assert result.total_workers == 0
        assert result.tokens.input == 0
        assert result.cost_breakdown.total == 0.0
        assert result.workers == []

    def test_fixture_metrics_file(self, ralph_with_workers: Path):
        metrics_file = ralph_with_workers / "metrics.json"
        result = read_metrics(metrics_file)

        assert result.total_workers == 2
        assert result.successful_workers == 1
        assert result.failed_workers == 1
        assert result.success_rate == 50.0
        assert len(result.workers) == 1


class TestFormatTokens:
    """Tests for format_tokens function."""

    def test_small_numbers(self):
        assert format_tokens(0) == "0"
        assert format_tokens(123) == "123"
        assert format_tokens(999) == "999"

    def test_thousands(self):
        assert format_tokens(1000) == "1.0K"
        assert format_tokens(1500) == "1.5K"
        assert format_tokens(45000) == "45.0K"
        assert format_tokens(999999) == "1000.0K"

    def test_millions(self):
        assert format_tokens(1000000) == "1.0M"
        assert format_tokens(1500000) == "1.5M"
        assert format_tokens(2500000) == "2.5M"


class TestFormatCost:
    """Tests for format_cost function."""

    def test_zero(self):
        assert format_cost(0) == "$0.00"

    def test_small_values(self):
        assert format_cost(0.01) == "$0.01"
        assert format_cost(0.99) == "$0.99"

    def test_larger_values(self):
        assert format_cost(1.23) == "$1.23"
        assert format_cost(10.50) == "$10.50"
        assert format_cost(100.00) == "$100.00"

    def test_rounds_correctly(self):
        assert format_cost(1.234) == "$1.23"
        assert format_cost(1.235) == "$1.24"
        assert format_cost(1.999) == "$2.00"


class TestFormatDuration:
    """Tests for format_duration function."""

    def test_seconds_only(self):
        assert format_duration(0) == "0s"
        assert format_duration(30) == "30s"
        assert format_duration(59) == "59s"

    def test_minutes_and_seconds(self):
        assert format_duration(60) == "1m 0s"
        assert format_duration(90) == "1m 30s"
        assert format_duration(3599) == "59m 59s"

    def test_hours_and_minutes(self):
        assert format_duration(3600) == "1h 0m"
        assert format_duration(3660) == "1h 1m"
        assert format_duration(7200) == "2h 0m"
        assert format_duration(5025) == "1h 23m"


class TestFormatContext:
    """Tests for format_context function."""

    def test_zero(self):
        assert format_context(0) == "0.0%"

    def test_whole_numbers(self):
        assert format_context(50.0) == "50.0%"
        assert format_context(100.0) == "100.0%"

    def test_decimals(self):
        assert format_context(22.5) == "22.5%"
        assert format_context(33.33) == "33.3%"
        assert format_context(66.666) == "66.7%"
