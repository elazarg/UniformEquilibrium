from fractions import Fraction
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
from random import Random
import tempfile
import unittest
from unittest.mock import patch

from fin4_exact_search.direct_oracle import (
    DIRECT_LOWER_KIND,
    DIRECT_SEARCH_STATE_KIND,
    DIRECT_SCALE_CHECKPOINT_KIND,
    ConfigurableDirectScaleContract,
    DirectHazardLowerSearch,
    DirectHazardLowerTreeCertificate,
    DirectScaleSearch,
    RobustGapCertificate,
    build_direct_hazard_problem,
    eval_direct_hazard_exact,
    finite_clock_support,
    hazard_profile,
    hazards_to_law,
    law_to_hazards,
    required_direct_level,
)
from fin4_exact_search.engine import RationalLaw, RewardTable, terminal_semantics
from fin4_exact_search.engine import write_json_atomic
from fin4_exact_search.cli import main as cli_main


def sample_reward(seed: int) -> RewardTable:
    random = Random(seed)
    return RewardTable(
        tuple(
            tuple(Fraction(random.randrange(-5, 6), 5) for _ in range(4))
            for _mask in range(1, 16)
        )
    )


class DirectOracleTests(unittest.TestCase):
    def test_rational_hazard_roundtrip(self) -> None:
        law = RationalLaw(
            4,
            (Fraction(1, 5), Fraction(1, 10), Fraction(1, 4), Fraction(0)),
            Fraction(9, 20),
        )
        hazards = law_to_hazards(law)
        self.assertEqual(hazards_to_law(hazards), law)

    def test_direct_expression_matches_terminal_semantics(self) -> None:
        for seed in range(12):
            reward = sample_reward(seed)
            level = 1
            clock = finite_clock_support(level)
            random = Random(1000 + seed)
            hazards = tuple(
                tuple(Fraction(random.randrange(5), 4) for _ in range(clock))
                for _player in range(4)
            )
            laws = hazard_profile(hazards)
            _payoff, _cap, _debt, exploitability = terminal_semantics(
                reward, laws
            )
            problem = build_direct_hazard_problem(reward, level)
            self.assertEqual(
                eval_direct_hazard_exact(problem, hazards), exploitability
            )

    def test_dense_level_ten_has_no_recursion_failure(self) -> None:
        reward = RewardTable(
            tuple(
                tuple(Fraction(1) for _player in range(4))
                for _mask in range(1, 16)
            )
        )
        level = 10
        clock = finite_clock_support(level)
        hazards = tuple(
            tuple(Fraction(0) for _time in range(clock))
            for _player in range(4)
        )
        problem = build_direct_hazard_problem(reward, level)
        self.assertEqual(len(problem.variable_names), 4 * clock)
        self.assertFalse(problem.equalities)
        self.assertFalse(problem.inequalities)
        self.assertEqual(eval_direct_hazard_exact(problem, hazards), 1)

    def test_false_direct_lower_leaf_is_rejected(self) -> None:
        certificate = DirectHazardLowerTreeCertificate(
            RewardTable.zero(),
            1,
            Fraction(1, 10),
            tuple(),
            ({"kind": "leaf", "reason": "goal", "index": 0},),
        )
        self.assertEqual(certificate.to_json()["kind"], DIRECT_LOWER_KIND)
        with self.assertRaises(ValueError):
            certificate.verify()

    def test_direct_certificate_roundtrip_preserves_distinct_kind(self) -> None:
        reward = RewardTable(
            tuple(
                (
                    Fraction(1 if mask & 1 else 0),
                    Fraction(0),
                    Fraction(0),
                    Fraction(0),
                )
                for mask in range(1, 16)
            )
        )
        problem = build_direct_hazard_problem(reward, 1)
        prefix = tuple(
            (name, Fraction(1, 100), False)
            for name in problem.variable_names
        )
        search = DirectHazardLowerSearch(problem, Fraction(1, 2), prefix)
        certificate = search.step()
        self.assertIsNotNone(certificate)
        assert certificate is not None
        certificate.verify()
        loaded = DirectHazardLowerTreeCertificate.from_json(
            certificate.to_json()
        )
        loaded.verify()
        self.assertEqual(loaded, certificate)
        self.assertFalse(loaded.is_global)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "regional.json.gz"
            write_json_atomic(path, certificate.to_json())
            output = io.StringIO()
            with redirect_stdout(output):
                self.assertEqual(cli_main(["verify", str(path)]), 0)
            self.assertIn("regional", output.getvalue())
            self.assertIn("no global eta conclusion", output.getvalue())
            self.assertNotIn("eta_lower=", output.getvalue())

    def test_robust_gap_wrapper_roundtrip_and_arithmetic(self) -> None:
        lower = DirectHazardLowerTreeCertificate(
            RewardTable.zero(),
            1,
            Fraction(25),
            tuple(),
            ({"kind": "leaf", "reason": "goal", "index": 0},),
        )
        robust = RobustGapCertificate(lower, Fraction(1, 4), Fraction(1, 2))
        self.assertEqual(RobustGapCertificate.from_json(robust.to_json()), robust)
        with patch.object(
            DirectHazardLowerTreeCertificate,
            "verify_positive_global",
            return_value=Fraction(1),
        ):
            robust.verify()
            with self.assertRaises(ValueError):
                RobustGapCertificate(
                    lower, Fraction(1, 4), Fraction(3, 4)
                ).verify()

    def test_direct_lower_search_state_roundtrip(self) -> None:
        problem = build_direct_hazard_problem(RewardTable.zero(), 1)
        search = DirectHazardLowerSearch(problem, Fraction(1, 10))
        self.assertIsNone(search.step())
        state = search.to_state_json()
        resumed = DirectHazardLowerSearch.from_state_json(problem, state)
        self.assertEqual(resumed.steps, search.steps)
        self.assertEqual(resumed.nodes, search.nodes)
        self.assertEqual(resumed.stack, search.stack)

    def test_direct_frontier_stores_constant_size_events(self) -> None:
        problem = build_direct_hazard_problem(RewardTable.zero(), 1)
        search = DirectHazardLowerSearch(problem, Fraction(1, 10))
        for _ in range(500):
            self.assertIsNone(search.step())
        resumed = DirectHazardLowerSearch.from_state_json(
            problem, json.loads(json.dumps(search.to_state_json()))
        )
        for _ in range(500):
            self.assertIsNone(search.step())
            self.assertIsNone(resumed.step())
        self.assertEqual(resumed.nodes, search.nodes)
        self.assertEqual(resumed.current_node, search.current_node)
        self.assertEqual(resumed.bounds, search.bounds)
        self.assertEqual(resumed.stack, search.stack)
        self.assertLessEqual(len(search.bounds), len(problem.variable_names))
        self.assertTrue(
            all(len(event) == 4 and not isinstance(event[-1], dict)
                for event in search.stack)
        )
        state = search.to_state_json()
        self.assertEqual(len(state["stack"]), len(search.stack))
        self.assertTrue(
            all(set(event) == {"action", "target", "variable", "interval"}
                for event in state["stack"])
        )

    def test_configurable_scale_contract_has_strict_transport_margin(self) -> None:
        for epsilon, alpha in (
            (Fraction(1, 3), Fraction(1, 2)),
            (Fraction(7, 5), Fraction(3, 4)),
            (Fraction(100), Fraction(1, 10)),
        ):
            contract = ConfigurableDirectScaleContract(epsilon, alpha)
            contract.verify()
            self.assertEqual(
                contract.level, required_direct_level(epsilon, alpha)
            )
            if contract.level > 1:
                self.assertGreaterEqual(
                    Fraction(24, contract.level - 1),
                    (1 - alpha) * epsilon,
                )
            self.assertLess(
                contract.compression_error, (1 - alpha) * epsilon
            )
            self.assertEqual(
                contract.lower_finite_threshold,
                alpha * epsilon + Fraction(24, contract.level),
            )
            self.assertEqual(contract.certified_global_lower, alpha * epsilon)
            self.assertEqual(contract.upper_target, epsilon)
            self.assertEqual(
                ConfigurableDirectScaleContract.from_json(contract.to_json()),
                contract,
            )

    def test_direct_scale_search_fair_checkpoint_resume(self) -> None:
        search = DirectScaleSearch(
            RewardTable.zero(), Fraction(100), Fraction(1, 2)
        )
        self.assertIsNone(search.step())  # direct lower fork splits once
        checkpoint = search.to_checkpoint_json()
        self.assertEqual(checkpoint["kind"], DIRECT_SCALE_CHECKPOINT_KIND)
        self.assertEqual(checkpoint["lower"]["kind"], DIRECT_SEARCH_STATE_KIND)
        resumed = DirectScaleSearch.from_checkpoint_json(
            json.loads(json.dumps(checkpoint))
        )
        result = resumed.step()  # exact v1 all-Never profile
        self.assertIsNotNone(result)
        assert result is not None
        self.assertEqual(result.kind, "profile")
        result.certificate.verify()
        self.assertEqual(resumed.turn, 2)
        self.assertEqual(resumed.steps, 2)

    def test_direct_scale_checkpoint_rejects_contract_tampering(self) -> None:
        search = DirectScaleSearch(
            RewardTable.zero(), Fraction(100), Fraction(1, 2)
        )
        checkpoint = search.to_checkpoint_json()
        checkpoint["contract"]["alpha"] = "1/3"
        with self.assertRaises(ValueError):
            DirectScaleSearch.from_checkpoint_json(checkpoint)


if __name__ == "__main__":
    unittest.main()
