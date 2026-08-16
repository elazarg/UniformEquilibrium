from __future__ import annotations

from copy import deepcopy
from fractions import Fraction
from pathlib import Path
import json
import tempfile
import unittest

from Experiments.quitting_repair_cegis.cegis import (
    _template_games,
    run_cegis_manifest,
)
from Experiments.quitting_repair_cegis.model import RationalQuittingGame
from Experiments.quitting_repair_cegis.profiles import (
    evaluate_cutoff_one,
    evaluate_cyclic_word,
    evaluate_stationary,
)
from Experiments.quitting_repair_cegis.regressions.generate_expected import (
    PACKAGE as GENERATED_PACKAGE,
    direct_result,
)
from Experiments.quitting_repair_cegis.report import (
    dump_report,
    make_repair_report,
    validate_claim_discipline,
    verify_report,
)
from Experiments.quitting_repair_cegis.search import SearchConfig, run_repair_ladder

PACKAGE = Path(__file__).resolve().parents[1]
TABLES = PACKAGE / "tables"
REGRESSIONS = PACKAGE / "regressions"
EXPECTED = REGRESSIONS / "expected"


class SearchAndReportTests(unittest.TestCase):
    def setUp(self) -> None:
        self.config = SearchConfig.from_dict(
            {
                "probabilities": ["0", "1/4", "1/2", "2/3", "1"],
                "max_period": 2,
                "max_word_roots": 6,
                "max_words": 1000,
            }
        )

    def test_positive_report_recomputes_exactly(self) -> None:
        game = RationalQuittingGame.from_path(TABLES / "cutoff_one_mixed.json")
        result = run_repair_ladder(game, self.config)
        self.assertIsNotNone(result.finding)
        report = make_repair_report(game, result, self.config)
        verify_report(game, report)
        self.assertEqual(
            report["machine_check"]["lean"]["status"],
            "actual_data_adapter_checked",
        )
        self.assertEqual(
            report["machine_check"]["lean"]["data_fingerprint"],
            report["table_fingerprint"],
        )

        corrupted = deepcopy(report)
        corrupted["certificate"]["value"][0] = "1"
        with self.assertRaises(ValueError):
            verify_report(game, corrupted)

        false_kernel_status = deepcopy(report)
        false_kernel_status["machine_check"]["lean"]["status"] = "kernel_checked"
        with self.assertRaises(ValueError):
            verify_report(game, false_kernel_status)

    def test_actual_adapter_status_is_exact_data_and_certificate_specific(self) -> None:
        game = RationalQuittingGame.from_path(TABLES / "cutoff_one_mixed.json")
        alternative = evaluate_cutoff_one(game, (Fraction(1), Fraction(1)))
        self.assertTrue(alternative.exact)
        alternative_report = make_repair_report(
            game,
            direct_result("cutoff_one", alternative, "alternative exact root"),
            self.config,
        )
        self.assertEqual(
            alternative_report["machine_check"]["lean"]["status"],
            "theorem_schema_only",
        )

        zero_rewards = tuple(
            tuple(Fraction(0) for _ in range(game.players))
            for _ in range(1 << game.players)
        )
        changed = RationalQuittingGame(
            name=game.name,
            players=game.players,
            rewards=zero_rewards,
            hints=game.hints,
            source=game.source,
        )
        changed_report = make_repair_report(
            changed,
            run_repair_ladder(changed, self.config),
            self.config,
        )
        self.assertEqual(
            changed_report["machine_check"]["lean"]["status"],
            "theorem_schema_only",
        )

    def test_negative_claim_discipline(self) -> None:
        invalid = {
            "schema": "quitting-repair-report/v1",
            "classification": "nonexistence",
            "certificate": {"kind": "stationary_gap", "gap": "1/10"},
        }
        with self.assertRaises(ValueError):
            validate_claim_discipline(invalid)

        valid_filter = {
            "schema": "quitting-repair-report/v1",
            "classification": "filter",
            "claim": "bounded_search_filter_only",
            "proves_nonexistence": False,
            "fixed_gap": "1/10",
            "tested": 1,
            "minimum_regret": "1/10",
        }
        validate_claim_discipline(valid_filter)

    def test_fixed_gap_cegis_has_filter_and_repair(self) -> None:
        manifest = REGRESSIONS / "fixed_gap_cegis.json"
        run = run_cegis_manifest(manifest)
        self.assertEqual(run.candidates, 2)
        self.assertEqual(
            [report["classification"] for report in run.reports],
            ["filter", "repair"],
        )
        self.assertFalse(run.reports[0]["proves_nonexistence"])

        with manifest.open("r", encoding="utf-8") as handle:
            raw_manifest = json.load(handle)
        games = list(_template_games(raw_manifest, manifest.resolve()))
        self.assertEqual(len(games), 2)
        committed_reports = []
        for number, (game, report) in enumerate(zip(games, run.reports, strict=True)):
            committed = json.loads(
                (EXPECTED / "fixed-gap-cegis" / f"{number:04d}.json").read_text(
                    encoding="utf-8"
                )
            )
            verify_report(game, committed)
            self.assertEqual(committed, report)
            committed_reports.append(
                {
                    "file": f"{number:04d}.json",
                    "table": report["table"],
                    "classification": report["classification"],
                }
            )
        committed_index = json.loads(
            (EXPECTED / "fixed-gap-cegis" / "index.json").read_text(
                encoding="utf-8"
            )
        )
        self.assertEqual(
            committed_index,
            {
                "schema": "quitting-table-cegis-summary/v1",
                "candidates": run.candidates,
                "reused_witnesses": len(run.witnesses),
                "reports": committed_reports,
            },
        )

    def test_committed_reports_are_reproducible(self) -> None:
        self.assertEqual(GENERATED_PACKAGE, PACKAGE)

        cutoff_game = RationalQuittingGame.from_path(TABLES / "cutoff_one_mixed.json")
        cutoff_report = json.loads(
            (EXPECTED / "cutoff-one.json").read_text(encoding="utf-8")
        )

        stationary_game = RationalQuittingGame.from_path(
            TABLES / "full_interval_stationary_repair.json"
        )
        stationary = evaluate_stationary(
            stationary_game, (Fraction(1, 2), Fraction(1), Fraction(1, 4))
        )
        stationary_report = make_repair_report(
            stationary_game,
            direct_result(
                "quitter_pair",
                stationary,
                "known exact two-mixer/sure-quitter regression",
            ),
            self.config,
        )

        cyclic_game = RationalQuittingGame.from_path(
            TABLES / "constant_one_cycle.json"
        )
        cyclic = evaluate_cyclic_word(
            cyclic_game, ((Fraction(1), Fraction(0)), (Fraction(0), Fraction(1)))
        )
        cyclic_report = make_repair_report(
            cyclic_game,
            direct_result(
                "holonomy_word", cyclic, "known exact two-phase regression"
            ),
            self.config,
        )
        self.assertEqual(
            stationary_report["machine_check"]["lean"]["status"],
            "theorem_schema_only",
        )
        self.assertEqual(
            cyclic_report["machine_check"]["lean"]["status"],
            "theorem_schema_only",
        )

        generated_reports = (
            (
                cutoff_game,
                make_repair_report(
                    cutoff_game,
                    run_repair_ladder(cutoff_game, self.config),
                    self.config,
                ),
                "cutoff-one.json",
            ),
            (stationary_game, stationary_report, "stationary-pair.json"),
            (cyclic_game, cyclic_report, "accepted-holonomy-word.json"),
        )
        for game, generated, filename in generated_reports:
            committed = json.loads((EXPECTED / filename).read_text(encoding="utf-8"))
            verify_report(game, committed)
            self.assertEqual(committed, generated)

        # Regeneration is tested in a temporary copy to ensure the script's
        # deterministic payload, not filesystem timestamps, is the artifact.
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "report.json"
            dump_report(cutoff_report, output)
            self.assertEqual(
                output.read_text(encoding="utf-8"),
                (EXPECTED / "cutoff-one.json").read_text(encoding="utf-8"),
            )


if __name__ == "__main__":
    unittest.main()
