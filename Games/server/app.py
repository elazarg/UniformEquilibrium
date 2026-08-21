"""Server construction: wires persistence + jobs into the HTTP handler and
runs http.server.ThreadingHTTPServer bound to 127.0.0.1.
"""
from __future__ import annotations

from http.server import ThreadingHTTPServer
from pathlib import Path
from typing import Optional

from server.handler import make_handler
from server.jobs import JobRegistry
from server.persistence import Storage


def run_server(games_root: Path, port: int = 8710, data_dir: Optional[Path] = None) -> None:
    # Per DESIGN.md: Games/data/ is never deleted or truncated by anyone,
    # since multiple agents' server processes share it. Tests and smoke runs
    # MUST pass an explicit scratch data_dir instead of relying on the
    # games_root/data default.
    storage = Storage(data_dir if data_dir is not None else games_root / "data")
    jobs = JobRegistry()
    handler_cls = make_handler(games_root, storage, jobs)
    httpd = ThreadingHTTPServer(("127.0.0.1", port), handler_cls)
    print(f"Games portal serving on http://127.0.0.1:{port}/  "
          f"(data: {storage.data_dir})  (Ctrl+C to stop)")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        httpd.server_close()
