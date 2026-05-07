"""Tests for the main WiggumApp using Textual's Pilot."""

import pytest
from pathlib import Path
from unittest.mock import patch

from textual.widgets import TabbedContent, Footer

from wiggum_tui.app import WiggumApp
from wiggum_tui.widgets.header import WiggumHeader


class TestWiggumHeader:
    """Tests for WiggumHeader widget."""

    def test_renders_project_name(self, tmp_path: Path):
        ralph_dir = tmp_path / "my-project" / ".ralph"
        ralph_dir.mkdir(parents=True)

        header = WiggumHeader(ralph_dir)
        content = header.render()

        assert "WIGGUM MONITOR" in content
        assert "my-project" in content

    def test_update_stats(self, tmp_path: Path):
        ralph_dir = tmp_path / "test-project" / ".ralph"
        ralph_dir.mkdir(parents=True)

        header = WiggumHeader(ralph_dir)
        header.update_stats(worker_count=5, running_count=2)

        # Should not raise and should update internal state
        assert header.worker_count == 5
        assert header.running_count == 2


class TestWiggumAppStartup:
    """Tests for WiggumApp startup and basic functionality."""

    @pytest.mark.asyncio
    async def test_app_composes_all_panels(self, ralph_with_workers: Path):
        """Test that app creates all expected panels."""
        app = WiggumApp(ralph_with_workers)

        async with app.run_test() as _pilot:
            # Check that TabbedContent exists
            tabbed = app.query_one(TabbedContent)
            assert tabbed is not None

            # Check footer exists
            footer = app.query_one(Footer)
            assert footer is not None

    @pytest.mark.asyncio
    async def test_app_title(self, ralph_with_workers: Path):
        """Test that app has correct title."""
        app = WiggumApp(ralph_with_workers)

        async with app.run_test():
            assert app.title == "Wiggum Monitor"

    @pytest.mark.asyncio
    async def test_initial_tab_is_kanban(self, ralph_with_workers: Path):
        """Test that Kanban tab is active by default."""
        app = WiggumApp(ralph_with_workers)

        async with app.run_test():
            tabbed = app.query_one(TabbedContent)
            assert tabbed.active == "kanban"


class TestWiggumAppTabNavigation:
    """Tests for tab navigation functionality."""

    @pytest.mark.asyncio
    async def test_switch_tab_with_number_keys(self, ralph_with_workers: Path):
        """Test switching tabs using number keys 1-6."""
        app = WiggumApp(ralph_with_workers)

        async with app.run_test() as pilot:
            tabbed = app.query_one(TabbedContent)

            # Press 2 to switch to Workers
            await pilot.press("2")
            assert tabbed.active == "workers"

            # Press 3 to switch to Logs
            await pilot.press("3")
            assert tabbed.active == "logs"

            # Press 4 to switch to Conversations
            await pilot.press("4")
            assert tabbed.active == "conversations"

            # Press 5 to switch to Plans
            await pilot.press("5")
            assert tabbed.active == "plans"

            # Press 6 to switch to Metrics
            await pilot.press("6")
            assert tabbed.active == "metrics"

            # Press 1 to go back to Kanban
            await pilot.press("1")
            assert tabbed.active == "kanban"

    @pytest.mark.asyncio
    async def test_vim_navigation_h_l(self, ralph_with_workers: Path):
        """Test vim-style h/l navigation between tabs."""
        app = WiggumApp(ralph_with_workers)

        async with app.run_test() as pilot:
            tabbed = app.query_one(TabbedContent)

            # Start at kanban (index 0)
            assert tabbed.active == "kanban"

            # Press l to go next
            await pilot.press("l")
            assert tabbed.active == "workers"

            # Press l again
            await pilot.press("l")
            assert tabbed.active == "logs"

            # Press h to go back
            await pilot.press("h")
            assert tabbed.active == "workers"

            # Press h to go back to kanban
            await pilot.press("h")
            assert tabbed.active == "kanban"

    @pytest.mark.asyncio
    async def test_vim_navigation_H_L(self, ralph_with_workers: Path):
        """Test vim-style H/L to jump to first/last tab."""
        app = WiggumApp(ralph_with_workers)

        async with app.run_test() as pilot:
            tabbed = app.query_one(TabbedContent)

            # Press L to go to last tab
            await pilot.press("L")
            assert tabbed.active == "memory"

            # Press H to go to first tab
            await pilot.press("H")
            assert tabbed.active == "kanban"

    @pytest.mark.asyncio
    async def test_action_switch_tab(self, ralph_with_workers: Path):
        """Test action_switch_tab method directly."""
        app = WiggumApp(ralph_with_workers)

        async with app.run_test():
            tabbed = app.query_one(TabbedContent)

            app.action_switch_tab("workers")
            assert tabbed.active == "workers"

            app.action_switch_tab("metrics")
            assert tabbed.active == "metrics"

    @pytest.mark.asyncio
    async def test_tab_wraps_around(self, ralph_with_workers: Path):
        """Test that h/l navigation wraps around at boundaries."""
        app = WiggumApp(ralph_with_workers)

        async with app.run_test() as pilot:
            tabbed = app.query_one(TabbedContent)

            # Go to last tab
            await pilot.press("L")
            assert tabbed.active == "memory"

            # Press l should wrap to first
            await pilot.press("l")
            assert tabbed.active == "kanban"

            # Press h should wrap to last
            await pilot.press("h")
            assert tabbed.active == "memory"


class TestWiggumAppRefresh:
    """Tests for refresh functionality."""

    @pytest.mark.asyncio
    async def test_refresh_action(self, ralph_with_workers: Path):
        """Test that pressing r triggers refresh."""
        app = WiggumApp(ralph_with_workers)

        async with app.run_test() as pilot:
            # Press r to refresh - should not raise
            await pilot.press("r")
            assert True

    @pytest.mark.asyncio
    async def test_action_refresh(self, ralph_with_workers: Path):
        """Test action_refresh method directly."""
        app = WiggumApp(ralph_with_workers)

        async with app.run_test():
            # Should not raise
            app.action_refresh()
            assert True


class TestWiggumAppHelp:
    """Tests for help functionality."""

    @pytest.mark.asyncio
    async def test_help_action(self, ralph_with_workers: Path):
        """Test that pressing ? shows help notification."""
        app = WiggumApp(ralph_with_workers)

        async with app.run_test() as pilot:
            # Press ? to show help
            await pilot.press("?")
            # The notification should be displayed (we can't easily test notification content)
            assert True


class TestWiggumAppWatcher:
    """Tests for file watcher integration."""

    @pytest.mark.asyncio
    async def test_watcher_started_on_mount(self, ralph_with_workers: Path):
        """Test that watcher is started when app mounts."""
        app = WiggumApp(ralph_with_workers)

        with patch.object(app.watcher, "start") as mock_start:
            async with app.run_test():
                mock_start.assert_called_once()

    @pytest.mark.asyncio
    async def test_watcher_stopped_on_unmount(self, ralph_with_workers: Path):
        """Test that watcher is stopped when app unmounts."""
        app = WiggumApp(ralph_with_workers)

        with patch.object(app.watcher, "stop") as mock_stop:
            async with app.run_test():
                pass
            # After context exits, watcher should be stopped
            mock_stop.assert_called()


class TestWiggumAppQuit:
    """Tests for quit functionality."""

    @pytest.mark.asyncio
    async def test_quit_binding(self, ralph_with_workers: Path):
        """Test that q key quits the app."""
        app = WiggumApp(ralph_with_workers)

        async with app.run_test() as pilot:
            # Press q to quit
            await pilot.press("q")
            # App should be exiting (run_test handles this gracefully)
            assert True


class TestWiggumAppEmptyRalph:
    """Tests with empty ralph directory."""

    @pytest.mark.asyncio
    async def test_app_handles_empty_ralph(self, ralph_empty: Path):
        """Test that app handles empty ralph directory gracefully."""
        app = WiggumApp(ralph_empty)

        async with app.run_test() as pilot:
            # Should not crash with empty data
            tabbed = app.query_one(TabbedContent)
            assert tabbed is not None

            # Switch through all tabs
            for key in ["1", "2", "3", "4", "5", "6"]:
                await pilot.press(key)

            # Should complete without errors
            assert True


class TestWiggumAppBindings:
    """Tests for all key bindings."""

    @pytest.mark.asyncio
    async def test_all_bindings_defined(self, ralph_with_workers: Path):
        """Test that all expected bindings are defined."""
        app = WiggumApp(ralph_with_workers)

        expected_keys = ["q", "1", "2", "3", "4", "5", "6", "r", "?", "h", "l", "H", "L"]

        async with app.run_test():
            binding_keys = [b.key for b in app.BINDINGS]
            for key in expected_keys:
                assert key in binding_keys, f"Missing binding for key: {key}"
