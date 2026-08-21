"""In-process background job registry for deep attacks (POST /api/attack
with level:"deep") and GET /api/jobs/<id> polling.

Jobs survive only for the server process lifetime; nothing here is
persisted. A single worker thread drains a queue, so submitted jobs run one
at a time rather than each getting its own thread: a deep attack is ~65-75s
of pure Python (per the engine team), and under the GIL several of those
running "concurrently" would only contend with each other and with
foreground request handling, not actually overlap usefully. Serializing
keeps that contention to whichever games are actively polling, not
compounding it across every deep job in flight.
"""
from __future__ import annotations

import queue
import threading
import uuid
from typing import Any, Callable, Dict, Optional


class JobRegistry:
    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._jobs: Dict[str, Dict[str, Any]] = {}
        self._queue: "queue.Queue[tuple]" = queue.Queue()
        self._worker = threading.Thread(target=self._run_worker, daemon=True)
        self._worker.start()

    def submit(self, fn: Callable[..., Any], *args, **kwargs) -> str:
        job_id = str(uuid.uuid4())
        # GET /api/jobs/<id> only documents "running"|"done"|"error"; a
        # queued-but-not-yet-started job is reported as "running" too --
        # from the client's perspective both just mean "not done yet".
        with self._lock:
            self._jobs[job_id] = {"status": "running", "result": None}
        self._queue.put((job_id, fn, args, kwargs))
        return job_id

    def _run_worker(self) -> None:
        while True:
            job_id, fn, args, kwargs = self._queue.get()
            try:
                result = fn(*args, **kwargs)
            except Exception as exc:  # report the failure, don't crash the worker
                with self._lock:
                    self._jobs[job_id] = {"status": "error", "result": str(exc)}
                continue
            with self._lock:
                self._jobs[job_id] = {"status": "done", "result": result}

    def get(self, job_id: str) -> Optional[Dict[str, Any]]:
        with self._lock:
            job = self._jobs.get(job_id)
            return dict(job) if job is not None else None
