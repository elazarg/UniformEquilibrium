#!/usr/bin/env python3
"""Run the sequencer's browser checks in headless Chrome.

Six pages, each one loading the real index.html with its real module graph:

* ``play.html``      the whole play flow in rehearsal mode, including the
                     forbidden-vocabulary scan of the play surface
* ``payloads.html``  every ``?table=`` arrival shape as a real page load
* ``handoff.html``   the real atlas "Attack it" navigation into the sequencer
* ``offline.html``   the house answering 503
* ``sanitized.html`` sanitized 1e9 / null values from the API
* ``audio.html``     transport, ghost overlay and the toggles

``handoff.html`` needs the portal server (it drives the real atlas page);
``offline.html`` and ``sanitized.html`` bring their own stub servers. The
portal server is started with ``--data-dir`` pointing at a scratch directory,
so no check can ever write to ``Games/data``.

Usage:
    python3 Games/games/sequencer/tests/run_browser_tests.py [--chrome PATH]

The Chrome binary is taken from ``--chrome``, then ``$SEQUENCER_CHROME``, then
a short list of usual locations (including the Windows install reachable from
WSL). Exit status is non-zero if any page reports FAIL.
"""

from __future__ import annotations

import argparse
import http.server
import os
import re
import shutil
import socket
import subprocess
import sys
import tempfile
import threading
import time
from functools import partial
from pathlib import Path

TESTS = Path(__file__).resolve().parent
GAME = TESTS.parent
GAMES_ROOT = GAME.parent.parent

CHROME_CANDIDATES = (
    "google-chrome",
    "chromium",
    "chromium-browser",
    "/mnt/c/Program Files/Google/Chrome/Application/chrome.exe",
    "/mnt/c/Program Files (x86)/Google/Chrome/Application/chrome.exe",
    "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
)


def find_chrome(explicit: str | None) -> str:
    for candidate in filter(None, (explicit, os.environ.get("SEQUENCER_CHROME"))):
        if Path(candidate).exists() or shutil.which(candidate):
            return candidate
    for candidate in CHROME_CANDIDATES:
        if Path(candidate).exists() or shutil.which(candidate):
            return candidate
    raise SystemExit(
        "no Chrome found; pass --chrome PATH or set SEQUENCER_CHROME"
    )


def free_port() -> int:
    with socket.socket() as sock:
        sock.bind(("127.0.0.1", 0))
        return sock.getsockname()[1]


def wait_for(port: int, path: str = "/", timeout: float = 20.0) -> bool:
    import urllib.request

    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            with urllib.request.urlopen(f"http://127.0.0.1:{port}{path}", timeout=1):
                return True
        except Exception:
            time.sleep(0.25)
    return False


class QuietHandler(http.server.SimpleHTTPRequestHandler):
    def log_message(self, *args):  # the runner's own report is the output
        pass


def serve_static(directory: Path, port: int) -> threading.Thread:
    handler = partial(QuietHandler, directory=str(directory))
    server = http.server.ThreadingHTTPServer(("127.0.0.1", port), handler)
    server.daemon_threads = True
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    return thread


def profile_argument(chrome: str, profile: Path, index: int) -> str:
    """A profile directory the browser can actually write to.

    A Windows Chrome reached from WSL cannot use a Linux path, and silently
    produces no output when handed one, so translate to a Windows path there.
    """

    if "/mnt/" in chrome.replace("\\", "/") and chrome.lower().endswith(".exe"):
        translated = shutil.which("wslpath")
        if translated:
            done = subprocess.run(
                ["wslpath", "-w", str(profile)], capture_output=True, text=True
            )
            if done.returncode == 0 and done.stdout.strip():
                return done.stdout.strip()
        return f"C:\\Temp\\sequencer-tests\\p{index}"
    return str(profile)


def run_page(
    chrome: str, url: str, profile: Path, index: int = 0, budget_ms: int = 40000
) -> tuple[str, str]:
    result = subprocess.run(
        [
            chrome,
            "--headless=new",
            "--disable-gpu",
            "--no-sandbox",
            "--autoplay-policy=no-user-gesture-required",
            f"--user-data-dir={profile_argument(chrome, profile, index)}",
            f"--virtual-time-budget={budget_ms}",
            "--dump-dom",
            url,
        ],
        capture_output=True,
        text=True,
        timeout=180,
    )
    dom = result.stdout
    if not dom.strip() and result.stderr.strip():
        return "FAIL", f"(browser produced no page)\n{result.stderr.strip()[:800]}"
    verdict = "FAIL"
    match = re.search(r"<title>(PASS|FAIL)</title>", dom)
    if match:
        verdict = match.group(1)
    body = re.search(r'<pre id="out">(.*?)</pre>', dom, re.S)
    detail = body.group(1) if body else "(no report produced)"
    return verdict, detail


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--chrome", default=None)
    parser.add_argument("--keep-going", action="store_true")
    args = parser.parse_args()
    chrome = find_chrome(args.chrome)

    scratch = Path(tempfile.mkdtemp(prefix="sequencer-tests-"))
    data_dir = scratch / "data"
    data_dir.mkdir()
    profile_root = scratch / "chrome"
    profile_root.mkdir()

    static_port = free_port()
    portal_port = free_port()
    serve_static(GAME, static_port)

    portal = subprocess.Popen(
        [
            sys.executable,
            str(GAMES_ROOT / "serve.py"),
            "--port",
            str(portal_port),
            "--data-dir",
            str(data_dir),
        ],
        cwd=str(GAMES_ROOT.parent),
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    stubs = [
        subprocess.Popen(
            [sys.executable, str(TESTS / name), str(GAME)],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        for name in ("stub503.py", "stub_sanitized.py")
    ]

    ready_portal = wait_for(portal_port, "/sequencer/")
    time.sleep(1.0)

    pages = [
        ("play", f"http://127.0.0.1:{static_port}/tests/play.html"),
        ("payloads", f"http://127.0.0.1:{static_port}/tests/payloads.html"),
        ("audio", f"http://127.0.0.1:{static_port}/tests/audio.html"),
        ("offline (503)", "http://127.0.0.1:8794/tests/offline.html"),
        ("sanitized", "http://127.0.0.1:8795/tests/sanitized.html"),
    ]
    if ready_portal:
        pages.append(("handoff", f"http://127.0.0.1:{portal_port}/sequencer/tests/handoff.html"))
    else:
        print("! portal server did not come up; skipping the hand-off check")

    failures = 0
    try:
        for index, (name, url) in enumerate(pages):
            verdict, detail = run_page(chrome, url, profile_root / f"p{index}", index)
            print(f"\n=== {name}: {verdict} ===")
            print(detail.strip())
            if verdict != "PASS":
                failures += 1
                if not args.keep_going:
                    continue
    finally:
        portal.terminate()
        for stub in stubs:
            stub.terminate()
        leftovers = sorted(p.name for p in data_dir.iterdir())
        print(f"\nscratch data dir wrote: {leftovers or 'nothing'}")
        shutil.rmtree(scratch, ignore_errors=True)

    print(f"\n{len(pages) - failures}/{len(pages)} pages passed")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
