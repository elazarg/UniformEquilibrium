import threading
import time
import unittest

from server.jobs import JobRegistry


class JobRegistryTests(unittest.TestCase):
    def test_simple_job_reports_done_with_result(self):
        registry = JobRegistry()
        job_id = registry.submit(lambda x: x * 2, 21)
        self._wait_until_finished(registry, job_id)
        job = registry.get(job_id)
        self.assertEqual(job["status"], "done")
        self.assertEqual(job["result"], 42)

    def test_failing_job_reports_error_status(self):
        def boom():
            raise ValueError("kaboom")

        registry = JobRegistry()
        job_id = registry.submit(boom)
        self._wait_until_finished(registry, job_id)
        job = registry.get(job_id)
        self.assertEqual(job["status"], "error")
        self.assertIn("kaboom", job["result"])

    def test_unknown_job_id_returns_none(self):
        registry = JobRegistry()
        self.assertIsNone(registry.get("no-such-id"))

    def test_jobs_run_serially_not_concurrently(self):
        # Regression coverage for the GIL-contention concern the engine team
        # flagged: two "slow" jobs submitted back to back must not overlap in
        # wall-clock time -- a single worker thread drains them one at a time.
        registry = JobRegistry()
        events = []
        lock = threading.Lock()

        def slow_job(label):
            with lock:
                events.append((label, "start"))
            time.sleep(0.1)
            with lock:
                events.append((label, "end"))
            return label

        job_a = registry.submit(slow_job, "a")
        job_b = registry.submit(slow_job, "b")
        self._wait_until_finished(registry, job_a)
        self._wait_until_finished(registry, job_b)

        # If they overlapped, "b start" would appear before "a end".
        labels = [(label, phase) for label, phase in events]
        self.assertEqual(labels, [("a", "start"), ("a", "end"), ("b", "start"), ("b", "end")])

    def _wait_until_finished(self, registry: JobRegistry, job_id: str, timeout: float = 5.0):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            job = registry.get(job_id)
            if job is not None and job["status"] != "running":
                return job
            time.sleep(0.005)
        self.fail(f"job {job_id} did not finish within {timeout}s")


if __name__ == "__main__":
    unittest.main()
