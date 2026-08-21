"""HTTP request handler: routing, JSON (de)serialization, static fallback.

make_handler(games_root, storage, jobs) returns a BaseHTTPRequestHandler
subclass bound to that server state, suitable for passing to
http.server.ThreadingHTTPServer.
"""
from __future__ import annotations

import json
import math
import re
import traceback
from http.server import BaseHTTPRequestHandler
from pathlib import Path
from urllib.parse import parse_qs, urlsplit

from server import routes
from server.jobs import JobRegistry
from server.persistence import Storage
from server.static import resolve_static

# The engine legitimately reports +inf (e.g. "no killing profile found in
# this family") and Python's json.dumps renders that as the bare token
# `Infinity`, which is not valid JSON and makes every browser's JSON.parse
# throw. Sanitize to a finite sentinel clearly outside any real
# exploitability value (payoffs are clamped to [-4, 4], so no genuine score
# can approach this) before any response is serialized.
_INF_SENTINEL = 1.0e9


def _json_safe(obj):
    if isinstance(obj, float):
        if math.isnan(obj):
            return None
        if math.isinf(obj):
            return _INF_SENTINEL if obj > 0 else -_INF_SENTINEL
        return obj
    if isinstance(obj, dict):
        return {k: _json_safe(v) for k, v in obj.items()}
    if isinstance(obj, list):
        return [_json_safe(v) for v in obj]
    if isinstance(obj, tuple):
        return [_json_safe(v) for v in obj]
    return obj

# (method, path pattern, routes.<handler name>)
ROUTES = (
    ("POST", re.compile(r"^/api/evaluate/?$"), "evaluate"),
    ("POST", re.compile(r"^/api/attack/?$"), "attack"),
    ("GET", re.compile(r"^/api/jobs/(?P<job_id>[^/]+)/?$"), "job_status"),
    ("POST", re.compile(r"^/api/attack_batch/?$"), "attack_batch"),
    ("POST", re.compile(r"^/api/filters/?$"), "filters"),
    ("GET", re.compile(r"^/api/tables/curated/?$"), "curated_tables"),
    ("POST", re.compile(r"^/api/candidates/?$"), "post_candidate"),
    ("GET", re.compile(r"^/api/candidates/?$"), "get_candidates"),
    ("POST", re.compile(r"^/api/profiles/?$"), "post_profile"),
    ("GET", re.compile(r"^/api/stats/?$"), "stats"),
    ("POST", re.compile(r"^/api/harden/?$"), "harden"),
)


def make_handler(games_root: Path, storage: Storage, jobs: JobRegistry):
    class Handler(BaseHTTPRequestHandler):
        server_version = "GamesPortal/1.0"

        def log_message(self, fmt, *args):  # quieter default test/run output
            pass

        # -- dispatch ---------------------------------------------------

        def do_GET(self):
            self._dispatch("GET")

        def do_POST(self):
            self._dispatch("POST")

        def _dispatch(self, method: str) -> None:
            parsed = urlsplit(self.path)
            path = parsed.path
            for m, pattern, name in ROUTES:
                if m != method:
                    continue
                match = pattern.match(path)
                if match:
                    self._handle_api(name, match.groupdict(), parse_qs(parsed.query))
                    return
            if method == "GET":
                self._handle_static(path)
                return
            self._send_json(404, {"error": "not found"})

        def _handle_api(self, name: str, path_params: dict, query: dict) -> None:
            handler_fn = getattr(routes, name)
            ctx = routes.Context(games_root=games_root, storage=storage, jobs=jobs)
            try:
                body = self._read_json_body() if self.command == "POST" else None
                status, payload = handler_fn(ctx, path_params, query, body)
                self._send_json(status, payload)
            except routes.ApiError as e:
                self._send_json(e.status, {"error": str(e)})
            except ConnectionError:
                # The client hung up mid-request or mid-response (browser
                # navigation, cancelled fetch).  There is nobody to answer.
                self.close_connection = True
            except Exception:
                traceback.print_exc()
                try:
                    self._send_json(500, {"error": "internal server error"})
                except ConnectionError:
                    self.close_connection = True

        def _read_json_body(self) -> dict:
            length = int(self.headers.get("Content-Length", 0) or 0)
            raw = self.rfile.read(length) if length else b""
            if not raw:
                return {}
            try:
                parsed = json.loads(raw.decode("utf-8"))
            except (json.JSONDecodeError, UnicodeDecodeError) as e:
                raise routes.ApiError(400, "invalid JSON body") from e
            if not isinstance(parsed, dict):
                raise routes.ApiError(400, "JSON body must be an object")
            return parsed

        # -- responses ----------------------------------------------------

        def _send_json(self, status: int, payload) -> None:
            data = json.dumps(_json_safe(payload)).encode("utf-8")
            self.send_response(status)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            self.wfile.write(data)

        def _handle_static(self, path: str) -> None:
            result = resolve_static(games_root, path)
            if result is None:
                self._send_json(404, {"error": "not found"})
                return
            file_path, content_type = result
            try:
                data = file_path.read_bytes()
            except OSError:
                self._send_json(404, {"error": "not found"})
                return
            self.send_response(200)
            self.send_header("Content-Type", content_type)
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            self.wfile.write(data)

    return Handler
