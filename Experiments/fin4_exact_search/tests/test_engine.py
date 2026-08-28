from contextlib import redirect_stdout
from fractions import Fraction
import io
from pathlib import Path
from random import Random
import tempfile
import unittest

from fin4_exact_search.engine import (
    Interval,
    LowerTreeCertificate,
    ProfileCertificate,
    RationalLaw,
    RewardTable,
    ScaleSearch,
    WorkRegion,
    build_outer_problem,
    canonical_lower_partition,
    composition_count,
    composition_unrank,
    make_region,
    read_json,
    terminal_semantics,
    write_json_atomic,
)
from fin4_exact_search.cli import main as cli_main


ROOT = Path(__file__).resolve().parents[1]


class ExactEngineTests(unittest.TestCase):
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

    def test_profile_schema_rejects_joint_law_without_marginals(self) -> None:
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

    def test_outer_formula_matches_exact_semantics_randomly(self) -> None:
        random = Random(20260828)
        for _ in range(8):
            rows = [
                tuple(Fraction(random.randint(-5, 5), 5) for _ in range(4))
                for _mask in range(1, 16)
            ]
            reward = RewardTable(tuple(rows))
            clock = 9
            laws = []
            for _player in range(4):
                weights = [random.randrange(0, 8) for _ in range(clock + 1)]
                if not sum(weights):
                    weights[-1] = 1
                denominator = sum(weights)
                laws.append(
                    RationalLaw(
                        clock,
                        tuple(Fraction(value, denominator) for value in weights[:-1]),
                        Fraction(weights[-1], denominator),
                    )
                )
            payoff, cap, _debt, exploitability = terminal_semantics(reward, laws)
            problem = build_outer_problem(reward, 1)
            bounds = {}
            for name, variable in problem.variable_index.items():
                if name.startswith("point.u"):
                    value = payoff[int(name[-1])]
                elif name.startswith("point.b"):
                    value = cap[int(name[-1])]
                else:
                    player = int(name[1])
                    atom = name.split(".")[1]
                    if atom == "N":
                        value = laws[player].never
                    else:
                        time_index = int(atom[1:])
                        value = 0 if time_index == clock else laws[player].finite[time_index]
                bounds[variable] = Interval.point(Fraction(value))
            cache = {}
            for equality in problem.equalities:
                enclosure = problem.factory.eval_interval(
                    equality, problem.root_box, bounds, cache
                )
                self.assertEqual(enclosure, Interval.point(Fraction(0)))
            for inequality in problem.inequalities:
                enclosure = problem.factory.eval_interval(
                    inequality, problem.root_box, bounds, cache
                )
                self.assertGreaterEqual(enclosure.lo, 0)
            objective = problem.factory.eval_interval(
                problem.objective, problem.root_box, bounds, cache
            )
            self.assertEqual(objective, Interval.point(exploitability))

    def test_scale_search_checkpoint_resume(self) -> None:
        search = ScaleSearch(RewardTable.zero(), Fraction(100))
        self.assertIsNone(search.step())  # one lower split
        checkpoint = search.to_checkpoint_json()
        resumed = ScaleSearch.from_checkpoint_json(checkpoint)
        result = resumed.step()  # first upper profile is all Never
        self.assertIsNotNone(result)
        assert result is not None
        self.assertEqual(result.kind, "profile")
        result.certificate.verify()

    def test_coarse_to_fine_campaign_and_completed_resume(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            work_dir = Path(directory) / "campaign"
            output = io.StringIO()
            with redirect_stdout(output):
                status = cli_main(
                    [
                        "campaign",
                        "--table",
                        str(ROOT / "examples" / "zero_table.json"),
                        "--start-epsilon",
                        "100",
                        "--work-dir",
                        str(work_dir),
                        "--stop-after-scales",
                        "3",
                        "--max-steps",
                        "1",
                        "--checkpoint-every",
                        "1",
                        "--report-every",
                        "1",
                    ]
                )
            self.assertEqual(status, 2)
            paused = read_json(work_dir / "campaign.checkpoint.json.gz")
            self.assertEqual(paused["status"], "running")
            with redirect_stdout(io.StringIO()):
                status = cli_main(
                    [
                        "campaign",
                        "--table",
                        str(ROOT / "examples" / "zero_table.json"),
                        "--start-epsilon",
                        "100",
                        "--work-dir",
                        str(work_dir),
                        "--stop-after-scales",
                        "3",
                        "--max-steps",
                        "20",
                        "--checkpoint-every",
                        "1",
                        "--report-every",
                        "1",
                        "--resume",
                    ]
                )
            self.assertEqual(status, 0)
            checkpoint = read_json(work_dir / "campaign.checkpoint.json.gz")
            self.assertEqual(checkpoint["status"], "requested-scales-complete")
            self.assertEqual(
                [item["epsilon"] for item in checkpoint["completed"]],
                ["100", "50", "25"],
            )
            with redirect_stdout(io.StringIO()):
                resumed = cli_main(
                    [
                        "campaign",
                        "--table",
                        str(ROOT / "examples" / "zero_table.json"),
                        "--start-epsilon",
                        "100",
                        "--work-dir",
                        str(work_dir),
                        "--stop-after-scales",
                        "3",
                        "--resume",
                    ]
                )
            self.assertEqual(resumed, 0)

    def test_checkpoint_file_roundtrip(self) -> None:
        search = ScaleSearch(RewardTable.zero(), Fraction(100))
        search.step()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "state.json.gz"
            write_json_atomic(path, search.to_checkpoint_json())
            resumed = ScaleSearch.from_checkpoint_json(read_json(path))
            self.assertEqual(resumed.steps, search.steps)
            self.assertEqual(resumed.reward, search.reward)

    def test_checkpoint_contract_tampering_is_rejected(self) -> None:
        search = ScaleSearch(RewardTable.zero(), Fraction(100))
        payload = search.to_checkpoint_json()
        payload["lower"]["gamma"] = "1"
        with self.assertRaises(ValueError):
            ScaleSearch.from_checkpoint_json(payload)

    def test_compressed_json_is_byte_deterministic(self) -> None:
        payload = {"b": ["2/3", 1], "a": {"value": "-1/5"}}
        with tempfile.TemporaryDirectory() as directory:
            first = Path(directory) / "first.json.gz"
            second = Path(directory) / "second.json.gz"
            write_json_atomic(first, payload)
            write_json_atomic(second, payload)
            self.assertEqual(first.read_bytes(), second.read_bytes())
            self.assertEqual(read_json(first), payload)

    def test_region_identifier_and_partition_are_deterministic(self) -> None:
        reward = RewardTable.zero()
        first = make_region(
            reward,
            Fraction(100),
            "upper",
            {"diagonal_start": 2, "diagonal_end": 8},
        )
        second = WorkRegion.from_json(first.to_json())
        self.assertEqual(first.region_id, second.region_id)
        partition_a = canonical_lower_partition(reward, Fraction(100), 3)
        partition_b = canonical_lower_partition(reward, Fraction(100), 3)
        self.assertEqual(
            [region.region_id for region in partition_a],
            [region.region_id for region in partition_b],
        )
        self.assertEqual(len(partition_a), 8)

    def test_flat_verifier_has_no_python_recursion_limit(self) -> None:
        reward = RewardTable.zero()
        problem = build_outer_problem(reward, 1)
        variable = "p0.t9"  # the constrained-zero auxiliary mass
        depth = 1200
        # Build a preorder chain with explicit indices; the final left leaf is
        # invalid on purpose, so verification must reach it and raise
        # ValueError rather than RecursionError.
        chain = []
        for index in range(depth):
            split = 2 * index
            left = 2 * (index + 1) if index + 1 < depth else 2 * depth
            right = split + 1
            chain.append(
                {
                    "kind": "split",
                    "variable": variable,
                    "cut": Fraction(1, 2 ** (index + 1)),
                    "left": left,
                    "right": right,
                }
            )
            chain.append({"kind": "leaf", "reason": "eq", "index": 1})
        chain.append({"kind": "leaf", "reason": "goal", "index": 0})
        certificate = LowerTreeCertificate(
            reward, 1, Fraction(1, 10), tuple(), tuple(chain)
        )
        with self.assertRaises(ValueError):
            certificate.verify()

    def test_zero_table_rejects_false_positive_lower_goal(self) -> None:
        certificate = LowerTreeCertificate(
            RewardTable.zero(),
            1,
            Fraction(1, 10),
            tuple(),
            ({"kind": "leaf", "reason": "goal", "index": 0},),
        )
        with self.assertRaises(ValueError):
            certificate.verify()


if __name__ == "__main__":
    unittest.main()
