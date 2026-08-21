"""The offline verifier: merge-on-read, verdicts, and append-only updates."""

from __future__ import annotations

import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))

import verify_candidates as verifier  # noqa: E402
from engine import battery, model  # noqa: E402

SEED_KILLER = {
    "period": 2,
    "hazards": [[0.25, 0.0, 0.25, 0.0], [0.0, 0.25, 0.0, 0.25]],
}


def replay_attack(table, profiles):
    return battery.run_level(table, "replay", profiles=profiles)


def quick_attack(table, profiles):
    return battery.run_level(table, "quick", profiles=profiles)


class MergeOnRead(unittest.TestCase):
    def test_updates_are_folded_into_records(self) -> None:
        lines = [
            {"id": "a", "table": [], "status": "proposed"},
            {"id": "b", "table": [], "status": "proposed"},
            {"id": "a", "update": {"status": "killed", "tier": "numerical-wide"}},
            {"id": "a", "update": {"tier": "exact"}, "updated": "2026-01-01T00:00:00Z"},
        ]
        merged = verifier.merge_records(lines)
        self.assertEqual([record["id"] for record in merged], ["a", "b"])
        self.assertEqual(merged[0]["status"], "killed")
        self.assertEqual(merged[0]["tier"], "exact")
        self.assertEqual(merged[0]["updated"], "2026-01-01T00:00:00Z")
        self.assertEqual(merged[1]["status"], "proposed")

    def test_orphan_updates_are_kept_not_dropped(self) -> None:
        merged = verifier.merge_records([{"id": "ghost", "update": {"status": "x"}}])
        self.assertEqual(merged, [{"id": "ghost", "orphan_update": {"status": "x"}}])

    def test_malformed_lines_are_skipped(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "candidates.jsonl"
            path.write_text(
                '{"id": "a", "table": []}\nnot json\n\n[1,2,3]\n', encoding="utf-8"
            )
            merged = verifier.merge_records(verifier.read_lines(path))
            self.assertEqual([record["id"] for record in merged], ["a"])

    def test_missing_file_reads_as_empty(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            self.assertEqual(verifier.load_candidates(Path(folder)), [])
            self.assertEqual(verifier.load_library(Path(folder)), [])

    def test_library_deduplicates_and_rejects_bad_profiles(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "profiles.jsonl"
            with path.open("w", encoding="utf-8") as handle:
                for record in (
                    {"id": "p1", "profile": SEED_KILLER},
                    {"id": "p2", "profile": SEED_KILLER},
                    {"id": "p3", "profile": {"period": 1, "hazards": [[2.0] * 4]}},
                    {"id": "p4", "note": "no profile"},
                ):
                    handle.write(json.dumps(record) + "\n")
            library = verifier.load_library(Path(folder))
            self.assertEqual([record["id"] for record in library], ["p1"])


class Verification(unittest.TestCase):
    def setUp(self) -> None:
        self.folder = tempfile.TemporaryDirectory()
        self.data = Path(self.folder.name)
        self.candidate = {
            "id": "cand-1",
            "created": "2026-01-01T00:00:00Z",
            "table": model.table_to_wire(model.seed_table()),
            "game": "standoff",
            "session": "test",
            "provenance": {"trace": "hand written"},
            "status": "proposed",
        }
        self.write(self.data / "candidates.jsonl", [self.candidate])

    def tearDown(self) -> None:
        self.folder.cleanup()

    def write(self, path: Path, records) -> None:
        with path.open("w", encoding="utf-8") as handle:
            for record in records:
                handle.write(json.dumps(record) + "\n")

    def lines(self, path: Path) -> list[dict]:
        return verifier.read_lines(path)

    def test_survivor_is_recorded_without_a_kill(self) -> None:
        updates = verifier.run(
            self.data, attack=quick_attack, log=lambda message: None
        )
        self.assertEqual(len(updates), 1)
        update = updates[0]["update"]
        self.assertEqual(update["status"], "proposed")
        self.assertEqual(update["tier"], "survivor-quick")
        self.assertIsNone(update["killed_by"])
        self.assertNotIn("exact_check", update)
        # Append-only: the original line is untouched and one line was added.
        lines = self.lines(self.data / "candidates.jsonl")
        self.assertEqual(len(lines), 2)
        self.assertEqual(lines[0], self.candidate)
        self.assertEqual(lines[1]["id"], "cand-1")
        merged = verifier.load_candidates(self.data)
        self.assertEqual(merged[0]["tier"], "survivor-quick")

    def test_library_kill_is_recorded_with_an_exact_check(self) -> None:
        self.write(self.data / "profiles.jsonl", [{"id": "p1", "profile": SEED_KILLER}])
        updates = verifier.run(
            self.data, attack=replay_attack, log=lambda message: None
        )
        update = updates[0]["update"]
        self.assertEqual(update["status"], "killed")
        self.assertEqual(update["tier"], "exact")
        self.assertEqual(update["evaluation"]["binding_attack"], "library_replay")
        self.assertTrue(update["exact_check"]["kills"])
        # Halves round the 0.25 hazards away (round-half-to-even sends 0.5 to
        # 0), and thirds do not kill, so quarters are the simplest snapping.
        self.assertEqual(update["exact_check"]["denominator"], 4)
        self.assertEqual(update["killed_by"], update["exact_check"]["profile"])

    def test_killing_profile_is_added_to_the_library(self) -> None:
        self.write(self.data / "profiles.jsonl", [{"id": "p1", "profile": SEED_KILLER}])
        verifier.run(self.data, attack=replay_attack, log=lambda message: None)
        records = self.lines(self.data / "profiles.jsonl")
        self.assertEqual(len(records), 2)
        self.assertEqual(records[1]["source"]["candidate_id"], "cand-1")
        self.assertEqual(records[1]["kills"][0]["candidate_id"], "cand-1")
        self.assertEqual(
            records[1]["kills"][0]["table_hash"], model.table_hash(model.seed_table())
        )

    def test_no_record_profiles_leaves_the_library_alone(self) -> None:
        self.write(self.data / "profiles.jsonl", [{"id": "p1", "profile": SEED_KILLER}])
        verifier.run(
            self.data,
            attack=replay_attack,
            record_profiles=False,
            log=lambda message: None,
        )
        self.assertEqual(len(self.lines(self.data / "profiles.jsonl")), 1)

    def test_dry_run_writes_nothing(self) -> None:
        updates = verifier.run(
            self.data, attack=quick_attack, dry_run=True, log=lambda message: None
        )
        self.assertEqual(len(updates), 1)
        self.assertEqual(len(self.lines(self.data / "candidates.jsonl")), 1)

    def test_survivors_below_the_deep_level_stay_in_the_queue(self) -> None:
        # A quick-level survivor is still "proposed": surviving a cheap attack
        # is not a verdict, so the next run picks it up again.
        verifier.run(self.data, attack=quick_attack, log=lambda message: None)
        again = verifier.run(self.data, attack=quick_attack, log=lambda message: None)
        self.assertEqual([line["id"] for line in again], ["cand-1"])

    def test_killed_candidates_leave_the_queue(self) -> None:
        self.write(self.data / "profiles.jsonl", [{"id": "p1", "profile": SEED_KILLER}])
        verifier.run(self.data, attack=replay_attack, log=lambda message: None)
        again = verifier.run(self.data, attack=replay_attack, log=lambda message: None)
        self.assertEqual(again, [])

    def test_illegal_tables_are_skipped_not_recorded(self) -> None:
        broken = dict(self.candidate, id="cand-2", table=[[0.0] * 4] * 3)
        with (self.data / "candidates.jsonl").open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(broken) + "\n")
        updates = verifier.run(
            self.data, attack=quick_attack, log=lambda message: None
        )
        self.assertEqual([line["id"] for line in updates], ["cand-1"])

    def test_limit_and_status_selection(self) -> None:
        second = dict(self.candidate, id="cand-2")
        with (self.data / "candidates.jsonl").open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(second) + "\n")
        updates = verifier.run(
            self.data, limit=1, attack=quick_attack, log=lambda message: None
        )
        self.assertEqual([line["id"] for line in updates], ["cand-1"])
        updates = verifier.run(
            self.data,
            statuses=("verified",),
            attack=quick_attack,
            log=lambda message: None,
        )
        self.assertEqual(updates, [])

    def test_appended_lines_are_strict_json(self) -> None:
        # The battery reports "no bound" as an infinity, which json.dumps would
        # otherwise write as the non-standard Infinity token that a browser's
        # JSON.parse rejects.
        def reject(token):
            raise AssertionError(f"non-standard JSON constant {token}")

        verifier.run(self.data, attack=quick_attack, log=lambda message: None)
        for path in ("candidates.jsonl", "profiles.jsonl"):
            target = self.data / path
            if not target.exists():
                continue
            for line in target.read_text(encoding="utf-8").splitlines():
                json.loads(line, parse_constant=reject)

    def test_main_runs_standalone_on_an_empty_directory(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            with contextlib.redirect_stdout(io.StringIO()):
                code = verifier.main(
                    ["--data-dir", folder, "--dry-run", "--level", "quick"]
                )
            self.assertEqual(code, 0)


if __name__ == "__main__":
    unittest.main()
