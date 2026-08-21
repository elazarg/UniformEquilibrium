import tempfile
import time
import unittest
from pathlib import Path

from server import routes
from server.jobs import JobRegistry
from server.persistence import Storage
from server.tests.testutil import (
    StubEngine,
    sample_attack_result,
    sample_evaluate_result,
    sample_profile,
    sample_table,
)


class RouteTestCase(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        storage = Storage(Path(self._tmp.name) / "data")
        self.ctx = routes.Context(games_root=Path(self._tmp.name), storage=storage, jobs=JobRegistry())

    def tearDown(self):
        self._tmp.cleanup()

    def call(self, fn, body=None, path_params=None, query=None):
        return fn(self.ctx, path_params or {}, query or {}, body)


class EvaluateRouteTests(RouteTestCase):
    def test_valid_request_returns_engine_result(self):
        with StubEngine():
            status, payload = self.call(routes.evaluate, {"table": sample_table(), "profile": sample_profile()})
        self.assertEqual(status, 200)
        self.assertEqual(payload, sample_evaluate_result())

    def test_missing_table_is_400(self):
        with StubEngine():
            with self.assertRaises(routes.ApiError) as cm:
                self.call(routes.evaluate, {"profile": sample_profile()})
        self.assertEqual(cm.exception.status, 400)

    def test_missing_profile_is_400(self):
        with StubEngine():
            with self.assertRaises(routes.ApiError) as cm:
                self.call(routes.evaluate, {"table": sample_table()})
        self.assertEqual(cm.exception.status, 400)

    def test_invalid_table_shape_is_400(self):
        with StubEngine():
            with self.assertRaises(routes.ApiError) as cm:
                self.call(routes.evaluate, {"table": [[1, 2, 3, 4]], "profile": sample_profile()})
        self.assertEqual(cm.exception.status, 400)

    def test_engine_unavailable_is_503(self):
        with StubEngine(omit=("engine.evaluator",)):
            with self.assertRaises(routes.ApiError) as cm:
                self.call(routes.evaluate, {"table": sample_table(), "profile": sample_profile()})
        self.assertEqual(cm.exception.status, 503)


class AttackRouteTests(RouteTestCase):
    def test_standard_level_runs_synchronously(self):
        with StubEngine():
            status, payload = self.call(routes.attack, {"table": sample_table(), "level": "standard"})
        self.assertEqual(status, 200)
        self.assertEqual(payload["level"], "standard")
        self.assertIn("score", payload)

    def test_default_level_is_standard(self):
        with StubEngine():
            status, payload = self.call(routes.attack, {"table": sample_table()})
        self.assertEqual(status, 200)
        self.assertEqual(payload["level"], "standard")

    def test_invalid_level_is_400(self):
        with StubEngine():
            with self.assertRaises(routes.ApiError) as cm:
                self.call(routes.attack, {"table": sample_table(), "level": "ultra"})
        self.assertEqual(cm.exception.status, 400)

    def test_deep_level_returns_job_id_immediately(self):
        # The background worker thread doesn't dequeue and run the job
        # synchronously with submission (see server/jobs.py's single-worker
        # queue), so the stub must stay installed until the job actually
        # finishes -- tearing it down early would let the real engine.battery
        # load from disk instead and run an actual ~70s deep attack.
        with StubEngine(run_level=lambda table, level, profiles=(): sample_attack_result(level=level)):
            status, payload = self.call(routes.attack, {"table": sample_table(), "level": "deep"})
            self.assertEqual(status, 200)
            self.assertIn("job", payload)

            job_id = payload["job"]
            for _ in range(100):
                _, job_payload = self.call(routes.job_status, path_params={"job_id": job_id})
                if job_payload["status"] != "running":
                    break
                time.sleep(0.01)
        self.assertEqual(job_payload["status"], "done")
        self.assertEqual(job_payload["result"]["level"], "deep")

    def test_unknown_job_id_is_404(self):
        with self.assertRaises(routes.ApiError) as cm:
            self.call(routes.job_status, path_params={"job_id": "nonexistent"})
        self.assertEqual(cm.exception.status, 404)


class AttackBatchRouteTests(RouteTestCase):
    def test_batch_preserves_order(self):
        tables = [sample_table(), sample_table()]
        with StubEngine(run_level=lambda table, level, profiles=(): sample_attack_result(level=level)):
            status, payload = self.call(routes.attack_batch, {"tables": tables, "level": "replay"})
        self.assertEqual(status, 200)
        self.assertEqual(len(payload["results"]), 2)

    def test_empty_tables_list_is_400(self):
        with self.assertRaises(routes.ApiError) as cm:
            self.call(routes.attack_batch, {"tables": [], "level": "replay"})
        self.assertEqual(cm.exception.status, 400)

    def test_deep_level_rejected_for_batch(self):
        with self.assertRaises(routes.ApiError) as cm:
            self.call(routes.attack_batch, {"tables": [sample_table()], "level": "deep"})
        self.assertEqual(cm.exception.status, 400)

    def test_bad_table_in_batch_is_400(self):
        with self.assertRaises(routes.ApiError) as cm:
            self.call(routes.attack_batch, {"tables": [sample_table(), [[1, 2]]], "level": "replay"})
        self.assertEqual(cm.exception.status, 400)


class LibraryWiringTests(RouteTestCase):
    """The attacker library (DESIGN.md: replayed against every table an
    attack touches) is every stored profile record, threaded through to
    engine.run_battery's library_profiles parameter. These tests catch the
    regression where that wiring is silently dropped (routes call
    engine.run_battery(table, level) with no third argument).
    """

    def _seed_one_profile(self):
        self.call(
            routes.post_profile,
            {"profile": sample_profile(), "source": {"game": "sequencer", "session": "s1", "table_id": "seed"}},
        )

    def test_attack_passes_stored_profiles_to_engine(self):
        self._seed_one_profile()
        captured = {}

        def fake_run_level(table, level="standard", profiles=(), abandon_at=None):
            captured["profiles"] = list(profiles)
            return sample_attack_result(level=level)

        with StubEngine(run_level=fake_run_level):
            self.call(routes.attack, {"table": sample_table(), "level": "standard"})
        self.assertEqual(len(captured["profiles"]), 1)
        self.assertEqual(captured["profiles"][0]["profile"], sample_profile())

    def test_attack_with_empty_library_passes_empty_list(self):
        captured = {}

        def fake_run_level(table, level="standard", profiles=(), abandon_at=None):
            captured["profiles"] = list(profiles)
            return sample_attack_result(level=level)

        with StubEngine(run_level=fake_run_level):
            self.call(routes.attack, {"table": sample_table(), "level": "standard"})
        self.assertEqual(captured["profiles"], [])

    def test_post_candidate_passes_stored_profiles_to_engine(self):
        self._seed_one_profile()
        captured = {}

        def fake_run_level(table, level="standard", profiles=(), abandon_at=None):
            captured["profiles"] = list(profiles)
            return sample_attack_result(level=level, score=0.5)

        with StubEngine(run_level=fake_run_level):
            self.call(routes.post_candidate, {"table": sample_table(), "game": "g", "session": "s"})
        self.assertEqual(len(captured["profiles"]), 1)

    def test_attack_batch_passes_stored_profiles_to_engine(self):
        self._seed_one_profile()
        captured = []

        def fake_run_level(table, level="standard", profiles=(), abandon_at=None):
            captured.append(list(profiles))
            return sample_attack_result(level=level)

        with StubEngine(run_level=fake_run_level):
            self.call(routes.attack_batch, {"tables": [sample_table(), sample_table()], "level": "replay"})
        self.assertEqual(len(captured), 2)
        for profiles in captured:
            self.assertEqual(len(profiles), 1)

    def test_deep_job_passes_stored_profiles_to_engine(self):
        self._seed_one_profile()
        captured = {}

        def fake_run_level(table, level="standard", profiles=(), abandon_at=None):
            captured["profiles"] = list(profiles)
            return sample_attack_result(level=level)

        with StubEngine(run_level=fake_run_level):
            status, payload = self.call(routes.attack, {"table": sample_table(), "level": "deep"})
            job_id = payload["job"]
            for _ in range(100):
                _, job_payload = self.call(routes.job_status, path_params={"job_id": job_id})
                if job_payload["status"] != "running":
                    break
                time.sleep(0.01)
        self.assertEqual(job_payload["status"], "done")
        self.assertEqual(len(captured["profiles"]), 1)


class FiltersRouteTests(RouteTestCase):
    def test_valid_table_returns_filter_result(self):
        with StubEngine():
            status, payload = self.call(routes.filters, {"table": sample_table()})
        self.assertEqual(status, 200)
        self.assertIn("pass", payload)
        self.assertIn("filters", payload)

    def test_engine_api_report_passed_through_verbatim(self):
        # engine.filters.api_report already emits the DESIGN.md wire shape,
        # so the route must be a pure pass-through -- no server-side reshaping.
        report = {
            "pass": False,
            "pass_1_to_5": True,
            "margin": 0.1,
            "first_failing": "6_no_lcp_solution",
            "filters": {
                "1_toggle_instability": {"pass": True},
                "2_viable_owner": {"pass": True, "note": "owner found"},
                "3_collider_and_preemptor": {"pass": True},
                "4_preemption_cycle": {"pass": True},
                "5_iterated_normal_core": {"pass": True},
                "6_no_lcp_solution": {"pass": False},
            },
        }
        with StubEngine(api_report=lambda table, margin=0.1: report):
            status, payload = self.call(routes.filters, {"table": sample_table()})
        self.assertEqual(status, 200)
        self.assertEqual(payload, report)


class CuratedTablesRouteTests(RouteTestCase):
    def test_returns_tables_list(self):
        curated = [{"id": "seed", "name": "Solan-Vieille", "table": sample_table(), "known_score": None, "note": ""}]
        with StubEngine(curated_tables=lambda: curated):
            status, payload = self.call(routes.curated_tables)
        self.assertEqual(status, 200)
        self.assertEqual(payload["tables"], curated)


class CandidatesRouteTests(RouteTestCase):
    def test_post_candidate_records_server_evaluation_not_client_claim(self):
        client_lie = {"score": 0.99, "binding_attack": "none", "level": "standard", "elapsed": 0, "breakdown": {}}
        with StubEngine(run_level=lambda table, level, profiles=(): sample_attack_result(score=0.5)):
            status, payload = self.call(
                routes.post_candidate,
                {
                    "table": sample_table(),
                    "game": "standoff",
                    "session": "sess-1",
                    "provenance": {"evaluation": client_lie},
                },
            )
        self.assertEqual(status, 200)
        record = payload["record"]
        self.assertEqual(record["evaluation"]["score"], 0.5)  # server's number, not the client's 0.99
        self.assertEqual(record["status"], "proposed")  # 0.5 >= eps_kill

    def test_killed_candidate_gets_killed_status_and_profile(self):
        with StubEngine(run_level=lambda table, level, profiles=(): sample_attack_result(score=0.005)):
            status, payload = self.call(
                routes.post_candidate,
                {"table": sample_table(), "game": "sequencer", "session": "s2"},
            )
        record = payload["record"]
        self.assertEqual(record["status"], "killed")
        self.assertEqual(record["tier"], "numerical-wide")
        self.assertIsNotNone(record["killed_by"])

    def test_narrow_kill_tier(self):
        with StubEngine(run_level=lambda table, level, profiles=(): sample_attack_result(score=0.015)):
            _, payload = self.call(
                routes.post_candidate,
                {"table": sample_table(), "game": "sequencer", "session": "s3"},
            )
        self.assertEqual(payload["record"]["tier"], "numerical-narrow")

    def test_survivor_tier_when_not_killed(self):
        with StubEngine(run_level=lambda table, level, profiles=(): sample_attack_result(score=0.5)):
            _, payload = self.call(
                routes.post_candidate,
                {"table": sample_table(), "game": "sequencer", "session": "s4"},
            )
        self.assertEqual(payload["record"]["tier"], "survivor-standard")
        self.assertIsNone(payload["record"]["killed_by"])

    def test_missing_game_is_400(self):
        with StubEngine():
            with self.assertRaises(routes.ApiError) as cm:
                self.call(routes.post_candidate, {"table": sample_table(), "session": "s"})
        self.assertEqual(cm.exception.status, 400)

    def test_get_candidates_returns_newest_first(self):
        with StubEngine(run_level=lambda table, level, profiles=(): sample_attack_result(score=0.5)):
            self.call(routes.post_candidate, {"table": sample_table(), "game": "g", "session": "s1"})
            self.call(routes.post_candidate, {"table": sample_table(), "game": "g", "session": "s2"})
            status, payload = self.call(routes.get_candidates)
        self.assertEqual(status, 200)
        self.assertEqual(len(payload["candidates"]), 2)
        self.assertEqual(payload["candidates"][0]["session"], "s2")

    def test_get_candidates_respects_limit_query_param(self):
        with StubEngine(run_level=lambda table, level, profiles=(): sample_attack_result(score=0.5)):
            for i in range(3):
                self.call(routes.post_candidate, {"table": sample_table(), "game": "g", "session": f"s{i}"})
            status, payload = self.call(routes.get_candidates, query={"limit": ["1"]})
        self.assertEqual(len(payload["candidates"]), 1)

    def test_bad_limit_is_400(self):
        with self.assertRaises(routes.ApiError) as cm:
            self.call(routes.get_candidates, query={"limit": ["abc"]})
        self.assertEqual(cm.exception.status, 400)


class ProfilesRouteTests(RouteTestCase):
    def test_post_profile_with_table_id_source(self):
        status, payload = self.call(
            routes.post_profile,
            {"profile": sample_profile(), "source": {"game": "sequencer", "session": "s1", "table_id": "seed"}},
        )
        self.assertEqual(status, 200)
        self.assertIn("id", payload)

    def test_post_profile_missing_source_table_reference_is_400(self):
        with self.assertRaises(routes.ApiError) as cm:
            self.call(routes.post_profile, {"profile": sample_profile(), "source": {"game": "g", "session": "s"}})
        self.assertEqual(cm.exception.status, 400)

    def test_post_profile_invalid_profile_is_400(self):
        with self.assertRaises(routes.ApiError) as cm:
            self.call(
                routes.post_profile,
                {"profile": {"period": 99, "hazards": []}, "source": {"game": "g", "session": "s", "table_id": "x"}},
            )
        self.assertEqual(cm.exception.status, 400)


class StatsRouteTests(RouteTestCase):
    def test_empty_stats(self):
        status, payload = self.call(routes.stats)
        self.assertEqual(status, 200)
        self.assertEqual(payload, {"candidates": 0, "best_score": None, "library_profiles": 0, "kills": 0, "games": []})

    def test_stats_aggregate_candidates_and_profiles(self):
        with StubEngine(run_level=lambda table, level, profiles=(): sample_attack_result(score=0.5)):
            self.call(routes.post_candidate, {"table": sample_table(), "game": "standoff", "session": "s1"})
        with StubEngine(run_level=lambda table, level, profiles=(): sample_attack_result(score=0.005)):
            self.call(routes.post_candidate, {"table": sample_table(), "game": "breeder", "session": "s2"})
        self.call(routes.post_profile, {"profile": sample_profile(), "source": {"game": "g", "session": "s", "table_id": "x"}})

        status, payload = self.call(routes.stats)
        self.assertEqual(status, 200)
        self.assertEqual(payload["candidates"], 2)
        self.assertEqual(payload["kills"], 1)
        self.assertEqual(payload["library_profiles"], 1)
        self.assertEqual(payload["best_score"], 0.5)
        self.assertEqual(payload["games"], ["breeder", "standoff"])


class HardenRouteTests(RouteTestCase):
    def test_harden_returns_engine_result(self):
        with StubEngine():
            status, payload = self.call(routes.harden, {"table": sample_table(), "profile": sample_profile()})
        self.assertEqual(status, 200)
        self.assertEqual(payload["tier"], "exact")

    def test_harden_engine_unavailable_is_503(self):
        with StubEngine(omit=("engine.rational",)):
            with self.assertRaises(routes.ApiError) as cm:
                self.call(routes.harden, {"table": sample_table(), "profile": sample_profile()})
        self.assertEqual(cm.exception.status, 503)


if __name__ == "__main__":
    unittest.main()
