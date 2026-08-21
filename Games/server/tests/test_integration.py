"""End-to-end tests: a real ThreadingHTTPServer, hit over an actual socket
with urllib, covering route dispatch, static serving, and error shapes that
unit-level route tests (which call handler functions directly) don't
exercise: HTTP status codes, Content-Type headers, and JSON body framing.
"""
import json
import tempfile
import threading
import unittest
import urllib.error
import urllib.request
from http.server import ThreadingHTTPServer
from pathlib import Path

from server.handler import make_handler
from server.jobs import JobRegistry
from server.persistence import Storage
from server.tests.testutil import StubEngine, sample_profile, sample_table


class IntegrationTests(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)
        (self.root / "portal").mkdir()
        (self.root / "portal" / "index.html").write_text("<html>hello portal</html>")
        (self.root / "games" / "standoff").mkdir(parents=True)
        (self.root / "games" / "standoff" / "index.html").write_text("<html>standoff</html>")

        storage = Storage(self.root / "data")
        jobs = JobRegistry()
        handler_cls = make_handler(self.root, storage, jobs)
        self.httpd = ThreadingHTTPServer(("127.0.0.1", 0), handler_cls)
        self.port = self.httpd.server_address[1]
        self.thread = threading.Thread(target=self.httpd.serve_forever, daemon=True)
        self.thread.start()

        self._stub = StubEngine()
        self._stub.__enter__()

    def tearDown(self):
        self._stub.__exit__(None, None, None)
        self.httpd.shutdown()
        self.httpd.server_close()
        self.thread.join(timeout=5)
        self._tmp.cleanup()

    def url(self, path: str) -> str:
        return f"http://127.0.0.1:{self.port}{path}"

    def get(self, path: str):
        with urllib.request.urlopen(self.url(path)) as resp:
            return resp.status, resp.headers.get("Content-Type"), resp.read()

    def post(self, path: str, payload):
        data = json.dumps(payload).encode("utf-8")
        req = urllib.request.Request(self.url(path), data=data, method="POST",
                                      headers={"Content-Type": "application/json"})
        with urllib.request.urlopen(req) as resp:
            return resp.status, json.loads(resp.read())

    def test_root_serves_portal_html(self):
        status, content_type, body = self.get("/")
        self.assertEqual(status, 200)
        self.assertEqual(content_type, "text/html")
        self.assertIn(b"hello portal", body)

    def test_game_mount_serves_its_own_index(self):
        status, content_type, body = self.get("/standoff/")
        self.assertEqual(status, 200)
        self.assertIn(b"standoff", body)

    def test_unknown_static_path_is_404_json(self):
        with self.assertRaises(urllib.error.HTTPError) as cm:
            self.get("/nope-does-not-exist.html")
        self.assertEqual(cm.exception.code, 404)
        payload = json.loads(cm.exception.read())
        self.assertIn("error", payload)

    def test_evaluate_endpoint_round_trip(self):
        status, payload = self.post("/api/evaluate", {"table": sample_table(), "profile": sample_profile()})
        self.assertEqual(status, 200)
        self.assertIn("exploitability", payload)

    def test_stats_endpoint_get(self):
        status, content_type, body = self.get("/api/stats")
        self.assertEqual(status, 200)
        self.assertEqual(content_type, "application/json")
        payload = json.loads(body)
        self.assertEqual(payload["candidates"], 0)

    def test_bad_json_body_is_400(self):
        req = urllib.request.Request(
            self.url("/api/evaluate"), data=b"{not json", method="POST",
            headers={"Content-Type": "application/json"},
        )
        with self.assertRaises(urllib.error.HTTPError) as cm:
            urllib.request.urlopen(req)
        self.assertEqual(cm.exception.code, 400)

    def test_invalid_table_is_400_even_though_engine_is_available(self):
        with self.assertRaises(urllib.error.HTTPError) as cm:
            self.post("/api/evaluate", {"table": [[1, 2]], "profile": sample_profile()})
        self.assertEqual(cm.exception.code, 400)

    def test_unknown_api_route_is_404(self):
        with self.assertRaises(urllib.error.HTTPError) as cm:
            self.get("/api/does-not-exist")
        self.assertEqual(cm.exception.code, 404)

    def test_full_candidate_submission_and_listing(self):
        status, payload = self.post(
            "/api/candidates",
            {"table": sample_table(), "game": "standoff", "session": "sess-x", "provenance": {}},
        )
        self.assertEqual(status, 200)
        self.assertIn("id", payload)

        status, content_type, body = self.get("/api/candidates")
        self.assertEqual(status, 200)
        listing = json.loads(body)
        self.assertEqual(len(listing["candidates"]), 1)
        self.assertEqual(listing["candidates"][0]["game"], "standoff")


if __name__ == "__main__":
    unittest.main()
