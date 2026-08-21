"""Covers the --data-dir contract added to Games/DESIGN.md after an incident
where Games/data/ (shared across every agent's server process) got wiped
during ad hoc cleanup: the default must stay games_root/data, but an explicit
data_dir must be honored so tests and smoke runs never touch the shared
directory.
"""
import tempfile
import threading
import unittest
import urllib.request
from pathlib import Path

from server.app import run_server


class DataDirTests(unittest.TestCase):
    def _start(self, games_root: Path, data_dir=None):
        import http.server

        from server.handler import make_handler
        from server.jobs import JobRegistry
        from server.persistence import Storage

        storage = Storage(data_dir if data_dir is not None else games_root / "data")
        handler_cls = make_handler(games_root, storage, JobRegistry())
        httpd = http.server.ThreadingHTTPServer(("127.0.0.1", 0), handler_cls)
        thread = threading.Thread(target=httpd.serve_forever, daemon=True)
        thread.start()
        return httpd, thread, storage

    def test_explicit_data_dir_is_used_instead_of_default(self):
        with tempfile.TemporaryDirectory() as games_root_s, tempfile.TemporaryDirectory() as scratch_s:
            games_root = Path(games_root_s)
            (games_root / "portal").mkdir()
            (games_root / "portal" / "index.html").write_text("<html></html>")
            scratch = Path(scratch_s) / "scratch-data"

            httpd, thread, storage = self._start(games_root, data_dir=scratch)
            try:
                self.assertEqual(storage.data_dir, scratch)
                self.assertTrue(scratch.is_dir())
                self.assertFalse((games_root / "data").exists())
            finally:
                httpd.shutdown()
                httpd.server_close()
                thread.join(timeout=5)

    def test_default_data_dir_is_games_root_slash_data(self):
        with tempfile.TemporaryDirectory() as games_root_s:
            games_root = Path(games_root_s)
            (games_root / "portal").mkdir()
            (games_root / "portal" / "index.html").write_text("<html></html>")

            httpd, thread, storage = self._start(games_root, data_dir=None)
            try:
                self.assertEqual(storage.data_dir, games_root / "data")
            finally:
                httpd.shutdown()
                httpd.server_close()
                thread.join(timeout=5)


class ServeMainArgParsingTests(unittest.TestCase):
    def test_data_dir_and_port_flags_parsed(self):
        # Exercises serve.py's own argparse setup directly (not server.app's),
        # since that's what a user or a test harness actually invokes.
        import importlib.util
        import sys

        serve_path = Path(__file__).resolve().parents[2] / "serve.py"
        spec = importlib.util.spec_from_file_location("games_serve_cli_test", serve_path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)

        calls = []
        module.run_server = lambda games_root, port, data_dir: calls.append((games_root, port, data_dir))
        module.main(["--port", "9123", "--data-dir", "/tmp/whatever-scratch"])
        self.assertEqual(len(calls), 1)
        _, port, data_dir = calls[0]
        self.assertEqual(port, 9123)
        self.assertEqual(data_dir, Path("/tmp/whatever-scratch"))

    def test_default_port_and_no_data_dir(self):
        import importlib.util

        serve_path = Path(__file__).resolve().parents[2] / "serve.py"
        spec = importlib.util.spec_from_file_location("games_serve_cli_test2", serve_path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)

        calls = []
        module.run_server = lambda games_root, port, data_dir: calls.append((games_root, port, data_dir))
        module.main([])
        _, port, data_dir = calls[0]
        self.assertEqual(port, 8710)
        self.assertIsNone(data_dir)


if __name__ == "__main__":
    unittest.main()
