#!/usr/bin/env python3
"""Entry point for the Games/ portal HTTP server.

Usage: python3 Games/serve.py [--port 8710]

Serves the static game portal and JSON API described in Games/DESIGN.md.
Stdlib only (http.server.ThreadingHTTPServer); binds 127.0.0.1.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

# Make `Games/` importable as the root for the `server` (and, once it lands,
# `engine`) packages, regardless of the caller's current working directory.
_GAMES_ROOT = Path(__file__).resolve().parent
if str(_GAMES_ROOT) not in sys.path:
    sys.path.insert(0, str(_GAMES_ROOT))

from server.app import run_server  # noqa: E402  (import after sys.path setup)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description="Games/ portal server")
    parser.add_argument("--port", type=int, default=8710, help="TCP port (default: 8710)")
    parser.add_argument(
        "--data-dir", type=Path, default=None,
        help="Persistence directory (default: Games/data/). Per DESIGN.md, "
             "Games/data/ is shared and never deleted or truncated by anyone "
             "-- tests and smoke runs must pass a scratch directory here.",
    )
    args = parser.parse_args(argv)
    run_server(_GAMES_ROOT, port=args.port, data_dir=args.data_dir)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
