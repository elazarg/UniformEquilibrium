#!/usr/bin/env python3
"""Unit tests for the static Lean import-graph checker."""

from __future__ import annotations

import pathlib
import tempfile
import unittest

from scripts import check_import_graph


class ImportParserTests(unittest.TestCase):
    def test_parses_multiline_imports_and_ignores_comments_and_literals(self) -> None:
        source = '''
/- import Not.A.Module -/
import First.Module
import
  Second.Module
import Third.Module Fourth.Module
def example := "import Fake.Module"
-- import Commented.Module
def primedName' := 0
import Fifth.Module
'''
        self.assertEqual(
            check_import_graph.parse_imports(source),
            [
                check_import_graph.ParsedImport("First.Module", 3),
                check_import_graph.ParsedImport("Second.Module", 4),
                check_import_graph.ParsedImport("Third.Module", 6),
                check_import_graph.ParsedImport("Fourth.Module", 6),
                check_import_graph.ParsedImport("Fifth.Module", 10),
            ],
        )


class ImportGraphTests(unittest.TestCase):
    def write(self, root: pathlib.Path, relative: str, source: str) -> None:
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")

    def test_reachability_and_lane_diagnostics_are_actionable(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            self.write(
                root,
                "lakefile.lean",
                """
lean_lib MathUE where
lean_lib UniformEquilibrium where
""",
            )
            self.write(root, "MathUE.lean", "import MathUE.Kernel\n")
            self.write(root, "MathUE/Kernel.lean", "import GameTheory.Basic\n")
            self.write(root, "MathUE/Orphan.lean", "")
            self.write(
                root,
                "UniformEquilibrium.lean",
                "import UniformEquilibrium.Root\n",
            )
            self.write(
                root,
                "UniformEquilibrium/Root.lean",
                "import Research.Probe\n",
            )
            self.write(root, "UniformEquilibrium/Orphan.lean", "")
            self.write(root, "Research.lean", "import Research.Probe\n")
            self.write(root, "Research/Probe.lean", "")

            failures = check_import_graph.check_import_graph(root)

            self.assertTrue(
                any("MathUE/Orphan.lean" in failure and "MathUE.lean" in failure
                    for failure in failures)
            )
            self.assertTrue(
                any("UniformEquilibrium/Orphan.lean" in failure for failure in failures)
            )
            self.assertTrue(
                any("imports research-only module Research.Probe" in failure
                    for failure in failures)
            )
            self.assertTrue(
                any("MathUE module MathUE.Kernel imports game-semantic" in failure
                    for failure in failures)
            )

    def test_ignores_lean_sources_outside_canonical_roots(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            self.write(root, "lakefile.lean", "lean_lib UniformEquilibrium where\n")
            self.write(root, "UniformEquilibrium.lean", "")
            for relative in (
                ".agents/Scratch.lean",
                "math/fable/Ignored.lean",
                "Unrelated/Ignored.lean",
                "Loose.lean",
            ):
                self.write(root, relative, "import Missing.LocalModule\n")

            self.assertEqual(check_import_graph.check_import_graph(root), [])

    def test_discovers_all_declared_library_roots(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            self.write(
                root,
                "lakefile.lean",
                "lean_lib Alpha where\nlean_lib Beta where\n",
            )
            self.write(root, "Alpha.lean", "")
            self.write(root, "Beta.lean", "")
            self.assertEqual(
                [umbrella.name for umbrella in check_import_graph.discover_umbrellas(root)],
                ["Alpha", "Beta"],
            )

    def test_discovers_nested_diagnostics_umbrella(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            self.write(root, "lakefile.lean", "lean_lib UniformEquilibrium where\n")
            self.write(root, "UniformEquilibrium.lean", "")
            self.write(root, "UniformEquilibrium/Diagnostics.lean", "")
            self.assertEqual(
                [umbrella.name for umbrella in check_import_graph.discover_umbrellas(root)],
                ["UniformEquilibrium", "UniformEquilibrium.Diagnostics"],
            )

    def test_nested_umbrella_owns_subtree(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            self.write(root, "lakefile.lean", "lean_lib UniformEquilibrium where\n")
            self.write(
                root,
                "UniformEquilibrium.lean",
                "import UniformEquilibrium.Production\n",
            )
            self.write(root, "UniformEquilibrium/Production.lean", "")
            self.write(
                root,
                "UniformEquilibrium/Diagnostics.lean",
                "import UniformEquilibrium.Diagnostics.Leaf\n",
            )
            self.write(root, "UniformEquilibrium/Diagnostics/Leaf.lean", "")
            self.assertEqual(check_import_graph.check_import_graph(root), [])

    def test_mathue_may_import_gametheory_generic_math(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            self.write(root, "lakefile.lean", "lean_lib MathUE where\n")
            self.write(root, "MathUE.lean", "import MathUE.Kernel\n")
            self.write(
                root,
                "MathUE/Kernel.lean",
                "import GameTheory.Math.Probability.FinDist\n",
            )
            self.assertEqual(check_import_graph.check_import_graph(root), [])

    def test_layer_boundaries_are_directional(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            self.write(
                root,
                "lakefile.lean",
                "lean_lib UniformEquilibrium where\n",
            )
            self.write(
                root,
                "UniformEquilibrium.lean",
                """\
import UniformEquilibrium.Certificates.BadArchitecture
import UniformEquilibrium.Quitting.BadDiagnostics
import UniformEquilibrium.Certificates.BadDiagnostics
import UniformEquilibrium.Architectures.CertificateConsumer
import UniformEquilibrium.Diagnostics.QuittingConsumer
import UniformEquilibrium.Diagnostics.CertificateConsumer
import UniformEquilibrium.Certificates.Neutral
""",
            )
            self.write(
                root,
                "UniformEquilibrium/Certificates/BadArchitecture.lean",
                "import UniformEquilibrium.Architectures.Api\n",
            )
            self.write(
                root,
                "UniformEquilibrium/Quitting/BadDiagnostics.lean",
                "import UniformEquilibrium.Diagnostics.Api\n",
            )
            self.write(
                root,
                "UniformEquilibrium/Certificates/BadDiagnostics.lean",
                "import UniformEquilibrium.Diagnostics.Api\n",
            )
            self.write(
                root,
                "UniformEquilibrium/Architectures/CertificateConsumer.lean",
                "import UniformEquilibrium.Certificates.Api\n",
            )
            self.write(
                root,
                "UniformEquilibrium/Diagnostics/QuittingConsumer.lean",
                "import UniformEquilibrium.Quitting.Api\n",
            )
            self.write(
                root,
                "UniformEquilibrium/Diagnostics/CertificateConsumer.lean",
                "import UniformEquilibrium.Certificates.Api\n",
            )
            self.write(
                root,
                "UniformEquilibrium/Certificates/Neutral.lean",
                "import Mathlib\n",
            )
            for relative in (
                "UniformEquilibrium/Architectures/Api.lean",
                "UniformEquilibrium/Diagnostics/Api.lean",
                "UniformEquilibrium/Quitting/Api.lean",
                "UniformEquilibrium/Certificates/Api.lean",
            ):
                self.write(root, relative, "")

            failures = check_import_graph.check_import_graph(root)

            self.assertEqual(len(failures), 3)
            self.assertTrue(
                any(
                    "Certificates.BadArchitecture -> "
                    "UniformEquilibrium.Architectures.Api" in failure
                    for failure in failures
                )
            )
            self.assertTrue(
                any(
                    "Quitting.BadDiagnostics -> "
                    "UniformEquilibrium.Diagnostics.Api" in failure
                    for failure in failures
                )
            )
            self.assertTrue(
                any(
                    "Certificates.BadDiagnostics -> "
                    "UniformEquilibrium.Diagnostics.Api" in failure
                    for failure in failures
                )
            )
            self.assertFalse(
                any("CertificateConsumer ->" in failure for failure in failures)
            )
            self.assertFalse(
                any("Certificates.Neutral ->" in failure for failure in failures)
            )

    def test_research_experiments_boundary_is_directional(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            self.write(
                root,
                "lakefile.lean",
                "lean_lib Research where\nlean_lib Experiments where\n",
            )
            self.write(
                root,
                "Research.lean",
                "import Research.BadExperiments\n",
            )
            self.write(
                root,
                "Research/BadExperiments.lean",
                "import Research.Interface\nimport Experiments.Evidence\n",
            )
            self.write(root, "Experiments.lean", "import Experiments.Consumer\n")
            self.write(
                root,
                "Experiments/Consumer.lean",
                "import Research.Interface\nimport Experiments.Evidence\n",
            )
            self.write(root, "Experiments/Evidence.lean", "")
            self.write(root, "Research/Interface.lean", "")

            failures = check_import_graph.check_import_graph(root)

            self.assertEqual(len(failures), 2)
            self.assertTrue(
                any("forbidden architectural edge Research.BadExperiments -> "
                    "Experiments.Evidence" in failure for failure in failures)
            )
            self.assertTrue(
                any("imports research module Research.Interface; promote"
                    in failure for failure in failures)
            )

    def test_literature_and_production_boundaries(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            self.write(
                root,
                "lakefile.lean",
                "lean_lib Literature where\n"
                "lean_lib UniformEquilibrium where\n"
                "lean_lib Research where\n",
            )
            self.write(root, "Literature.lean", "import Literature.BadResearch\n")
            self.write(
                root,
                "Literature/BadResearch.lean",
                "import Research.Evidence\n",
            )
            self.write(root, "Research.lean", "import Literature.Proof\n")
            self.write(
                root,
                "Research/Literature/Proof.lean",
                "import Literature.Papers.Example\n",
            )
            self.write(root, "Research/Evidence.lean", "")
            self.write(root, "Literature/Papers/Example.lean", "")
            self.write(
                root,
                "UniformEquilibrium.lean",
                "import UniformEquilibrium.BadLiterature\n",
            )
            self.write(
                root,
                "UniformEquilibrium/BadLiterature.lean",
                "import Literature.Papers.Example\n",
            )

            failures = check_import_graph.check_import_graph(root)

            self.assertTrue(
                any("Literature.BadResearch -> Research.Evidence" in failure
                    for failure in failures)
            )
            self.assertTrue(
                any("UniformEquilibrium.BadLiterature -> "
                    "Literature.Papers.Example" in failure
                    for failure in failures)
            )
            self.assertFalse(
                any("Literature.Proof -> Literature.Papers.Example" in failure
                    for failure in failures)
            )

    def test_unrelated_research_cannot_import_literature(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            self.write(root, "lakefile.lean", "lean_lib Research where\n")
            self.write(root, "Research.lean", "import Research.Proof\n")
            self.write(
                root,
                "Research/Proof.lean",
                "import Literature.Papers.Example\n",
            )
            self.write(root, "Literature/Papers/Example.lean", "")

            failures = check_import_graph.check_import_graph(root)

            self.assertTrue(
                any("nothing imports the literature lane" in failure
                    for failure in failures)
            )

    def test_inventory_and_internal_api_ratchets(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            self.write(
                root,
                "lakefile.lean",
                "lean_lib MathUE where\n"
                "lean_lib UniformEquilibrium where\n"
                "lean_lib Research where\n",
            )
            self.write(
                root,
                "MathUE.lean",
                "import MathUE.Kernel\nimport MathUE.BadInternal\n",
            )
            self.write(root, "MathUE/Kernel.lean", "")
            self.write(
                root,
                "MathUE/BadInternal.lean",
                "namespace Math.CurveSelection.ExtractionScratch\n"
                "end Math.CurveSelection.ExtractionScratch\n",
            )
            self.write(
                root,
                "UniformEquilibrium.lean",
                "import MathUE\n"
                "import MathUE.Kernel\n"
                "import UniformEquilibrium.Diagnostics.Quitting.All\n",
            )
            self.write(
                root,
                "UniformEquilibrium/Diagnostics/Quitting/All.lean",
                "import UniformEquilibrium.Diagnostics.Quitting."
                "CounterexampleRegime.All\n",
            )
            self.write(
                root,
                "UniformEquilibrium/Diagnostics/Quitting/"
                "CounterexampleRegime/All.lean",
                "",
            )
            self.write(root, "Research.lean", "import Research.Consumer\n")
            self.write(
                root,
                "Research/Consumer.lean",
                "import UniformEquilibrium.Diagnostics.Quitting.All\n"
                "import UniformEquilibrium.Diagnostics.Quitting."
                "CounterexampleRegime.All\n",
            )

            failures = check_import_graph.check_import_graph(root)

            self.assertEqual(len(failures), 4)
            self.assertTrue(any("redundant direct import MathUE.Kernel" in failure
                for failure in failures))
            self.assertTrue(any("inventory-only facade" in failure
                for failure in failures))
            self.assertTrue(any("ExtractionScratch" in failure
                for failure in failures))


if __name__ == "__main__":
    unittest.main()
