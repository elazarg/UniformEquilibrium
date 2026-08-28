from fractions import Fraction
from pathlib import Path
import tempfile
import unittest

from fin4_exact_search.engine import (
    ProfileCertificate,
    RationalLaw,
    RewardTable,
    composition_count,
    composition_unrank,
    read_json,
    terminal_semantics,
    write_json_atomic,
)


ROOT = Path(__file__).resolve().parents[1]


class ExactPrimitiveTests(unittest.TestCase):
    def test_table_validation_and_hash(self) -> None:
        table = RewardTable.from_json(read_json(ROOT / "examples/zero_table.json"))
        self.assertTrue(table.normalized)
        self.assertEqual(table.digest, RewardTable.zero().digest)

    def test_after_support_deadline_is_distinct_from_never(self) -> None:
        rows = []
        for mask in range(1, 16):
            row = [Fraction(0)] * 4
            if mask == 0b0011:
                row[0] = Fraction(1)
            rows.append(tuple(row))
        reward = RewardTable(tuple(rows))
        laws = [RationalLaw.pure(6, None) for _ in range(4)]
        laws[1] = RationalLaw.pure(6, 5)
        payoff, cap, debt, exploitability = terminal_semantics(reward, laws)
        self.assertEqual(payoff[0], 0)
        self.assertEqual(cap[0], 1)
        self.assertEqual(debt[0], 1)
        self.assertEqual(exploitability, 1)

    def test_profile_certificate_roundtrip(self) -> None:
        reward = RewardTable.zero()
        laws = tuple(RationalLaw.pure(1, None) for _ in range(4))
        certificate = ProfileCertificate.build(reward, laws, Fraction(1, 10))
        certificate.verify()
        loaded = ProfileCertificate.from_json(certificate.to_json())
        loaded.verify()
        self.assertEqual(loaded.exploitability, 0)

    def test_profile_schema_requires_independent_marginals(self) -> None:
        payload = {
            "kind": "fin4-rational-finite-clock-profile-v1",
            "reward": RewardTable.zero().to_json(),
            "clock_bound": 1,
            "joint_law": {"all_never": "1"},
            "epsilon": "1",
            "payoff": ["0"] * 4,
            "cap": ["0"] * 4,
            "debt": ["0"] * 4,
            "exploitability": "0",
        }
        with self.assertRaises(KeyError):
            ProfileCertificate.from_json(payload)

    def test_composition_unrank_is_complete(self) -> None:
        values = {
            composition_unrank(4, 3, rank)
            for rank in range(composition_count(4, 3))
        }
        self.assertEqual(len(values), composition_count(4, 3))
        self.assertTrue(all(sum(value) == 4 for value in values))

    def test_compressed_json_is_byte_deterministic(self) -> None:
        payload = {"b": ["2/3", 1], "a": {"value": "-1/5"}}
        with tempfile.TemporaryDirectory() as directory:
            first = Path(directory) / "first.json.gz"
            second = Path(directory) / "second.json.gz"
            write_json_atomic(first, payload)
            write_json_atomic(second, payload)
            self.assertEqual(first.read_bytes(), second.read_bytes())
            self.assertEqual(read_json(first), payload)


if __name__ == "__main__":
    unittest.main()
