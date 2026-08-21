import tempfile
import unittest
from pathlib import Path

from server.persistence import JsonlFile, Storage


class JsonlFileTests(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.path = Path(self._tmp.name) / "records.jsonl"
        self.f = JsonlFile(self.path)

    def tearDown(self):
        self._tmp.cleanup()

    def test_read_merged_on_missing_file_is_empty(self):
        self.assertEqual(self.f.read_merged(), [])

    def test_append_and_read_back(self):
        self.f.append({"id": "a", "value": 1})
        self.f.append({"id": "b", "value": 2})
        records = self.f.read_merged()
        self.assertEqual([r["id"] for r in records], ["a", "b"])
        self.assertEqual(records[0]["value"], 1)

    def test_update_line_merges_onto_base(self):
        self.f.append({"id": "a", "value": 1, "status": "proposed"})
        self.f.append({"id": "a", "update": {"status": "killed"}, "updated": "2026-01-01T00:00:00Z"})
        records = self.f.read_merged()
        self.assertEqual(len(records), 1)
        self.assertEqual(records[0]["status"], "killed")
        self.assertEqual(records[0]["value"], 1)  # untouched fields survive
        self.assertEqual(records[0]["updated"], "2026-01-01T00:00:00Z")

    def test_multiple_update_lines_apply_in_order(self):
        self.f.append({"id": "a", "status": "proposed"})
        self.f.append({"id": "a", "update": {"status": "verified"}, "updated": "t1"})
        self.f.append({"id": "a", "update": {"status": "killed"}, "updated": "t2"})
        records = self.f.read_merged()
        self.assertEqual(records[0]["status"], "killed")
        self.assertEqual(records[0]["updated"], "t2")

    def test_update_line_for_unknown_id_is_dropped(self):
        self.f.append({"id": "ghost", "update": {"status": "killed"}, "updated": "t1"})
        self.assertEqual(self.f.read_merged(), [])

    def test_duplicate_non_update_line_merges_not_replaces(self):
        # Matches Games/scripts/verify_candidates.py's merge_records: a
        # second full (non-update) line sharing an id patches the existing
        # record rather than replacing it, so a field only the first line
        # carried is never lost.
        self.f.append({"id": "a", "table": [1, 2, 3], "game": "standoff"})
        self.f.append({"id": "a", "session": "s1"})
        records = self.f.read_merged()
        self.assertEqual(len(records), 1)
        self.assertEqual(records[0]["table"], [1, 2, 3])  # from the first line
        self.assertEqual(records[0]["game"], "standoff")  # from the first line
        self.assertEqual(records[0]["session"], "s1")  # from the second line

    def test_base_record_order_preserved_regardless_of_update_lines(self):
        self.f.append({"id": "a"})
        self.f.append({"id": "b"})
        self.f.append({"id": "a", "update": {"x": 1}, "updated": "t"})
        records = self.f.read_merged()
        self.assertEqual([r["id"] for r in records], ["a", "b"])

    def test_malformed_line_is_skipped_not_raised(self):
        # Games/data/'s lines can never be removed, so a single corrupt line
        # (e.g. a process killed mid-append) must not turn every future read
        # into a permanent crash -- there would be no way to recover.
        self.f.append({"id": "a", "value": 1})
        with self.path.open("a", encoding="utf-8") as fh:
            fh.write("not json at all\n")
            fh.write('{"truncated": tr\n')  # invalid JSON
            fh.write("[1, 2, 3]\n")  # valid JSON, but not an object
            fh.write('{"no_id_field": true}\n')  # object, but no "id"
            fh.write('{"id": 123, "value": "int id, not str"}\n')  # id not a string
        self.f.append({"id": "b", "value": 2})
        records = self.f.read_merged()
        self.assertEqual([r["id"] for r in records], ["a", "b"])

    def test_update_line_missing_updated_field_does_not_erase_prior_timestamp(self):
        self.f.append({"id": "a", "status": "proposed"})
        self.f.append({"id": "a", "update": {"status": "verified"}, "updated": "t1"})
        self.f.append({"id": "a", "update": {"status": "killed"}})  # no "updated" key
        records = self.f.read_merged()
        self.assertEqual(records[0]["status"], "killed")
        self.assertEqual(records[0]["updated"], "t1")  # not clobbered to None

    def test_lines_are_never_rewritten_file_only_grows(self):
        self.f.append({"id": "a", "value": 1})
        size_after_first = self.path.stat().st_size
        self.f.append({"id": "a", "update": {"value": 2}, "updated": "t"})
        size_after_second = self.path.stat().st_size
        self.assertGreater(size_after_second, size_after_first)
        lines = self.path.read_text().splitlines()
        self.assertEqual(len(lines), 2)


class StorageTests(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.storage = Storage(Path(self._tmp.name) / "data")

    def tearDown(self):
        self._tmp.cleanup()

    def test_creates_data_dir(self):
        self.assertTrue(self.storage.data_dir.is_dir())

    def test_candidates_newest_first(self):
        self.storage.add_candidate({"id": "1", "created": "t1"})
        self.storage.add_candidate({"id": "2", "created": "t2"})
        records = self.storage.list_candidates()
        self.assertEqual([r["id"] for r in records], ["2", "1"])

    def test_candidates_limit(self):
        for i in range(5):
            self.storage.add_candidate({"id": str(i), "created": f"t{i}"})
        records = self.storage.list_candidates(limit=2)
        self.assertEqual(len(records), 2)
        self.assertEqual([r["id"] for r in records], ["4", "3"])

    def test_update_candidate_merges(self):
        self.storage.add_candidate({"id": "1", "status": "proposed"})
        self.storage.update_candidate("1", {"status": "killed"})
        records = self.storage.list_candidates()
        self.assertEqual(records[0]["status"], "killed")

    def test_profiles_round_trip(self):
        self.storage.add_profile({"id": "p1", "created": "t1"})
        records = self.storage.list_profiles()
        self.assertEqual(len(records), 1)
        self.assertEqual(records[0]["id"], "p1")

    def test_separate_files_for_candidates_and_profiles(self):
        self.storage.add_candidate({"id": "c1"})
        self.storage.add_profile({"id": "p1"})
        self.assertTrue((self.storage.data_dir / "candidates.jsonl").exists())
        self.assertTrue((self.storage.data_dir / "profiles.jsonl").exists())
        self.assertEqual(len(self.storage.list_candidates()), 1)
        self.assertEqual(len(self.storage.list_profiles()), 1)


if __name__ == "__main__":
    unittest.main()
