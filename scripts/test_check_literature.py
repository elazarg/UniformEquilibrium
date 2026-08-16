#!/usr/bin/env python3
"""Unit tests for Literature claim-status validation."""

from __future__ import annotations

import pathlib
import tempfile
import unittest

from scripts.check_literature import check_claim_declarations


class ClaimDeclarationTests(unittest.TestCase):
    def write(self, root: pathlib.Path, relative: str, source: str) -> None:
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")

    def test_accepts_unicode_and_escaped_multiline_fully_qualified_names(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            self.write(
                root,
                "GameTheory/Canonical.lean",
                "namespace GameTheory\n"
                "theorem deep_ε_result : True := by trivial\n"
                "end GameTheory\n",
            )
            self.write(
                root,
                "Literature/Papers/Example.lean",
                "namespace Literature.Papers.Example\n"
                "def statement : Prop := True\n"
                "theorem proof : statement := by trivial\n"
                "def record : True := by trivial\n"
                "auditStatus := .claimAuditInProgress\n"
                "-- The status syntax permits Lean's escaped line splice.\n"
                "status := .refutedInLean\n"
                '  "Literature.Papers.Example.statement"\n'
                '  "GameTheory.\\\n'
                'deep_ε_result"\n'
                "end Literature.Papers.Example\n",
            )

            self.assertEqual(check_claim_declarations(root), [])

    def test_reports_missing_proof_declaration(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            self.write(
                root,
                "Literature/Papers/Example.lean",
                "namespace Literature.Papers.Example\n"
                "def statement : Prop := True\n"
                "status := .provedInLean\n"
                '  "Literature.Papers.Example.statement" "missing"\n'
                "end Literature.Papers.Example\n",
            )

            failures = check_claim_declarations(root)

            self.assertTrue(any("missing" in failure for failure in failures))

    def test_open_claim_requires_research_consumer(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            self.write(
                root,
                "Literature/Papers/Example.lean",
                "namespace Literature.Papers.Example\n"
                "def statement : Prop := True\n"
                "auditStatus := .claimAuditInProgress\n"
                'status := .openInLean "Literature.Papers.Example.statement"\n'
                "end Literature.Papers.Example\n",
            )

            failures = check_claim_declarations(root)

            self.assertTrue(any("no active Research.Literature" in failure
                                for failure in failures))

            self.write(
                root,
                "Research/Literature/Example/Statement.lean",
                "import Literature.Papers.Example\n"
                "#check Literature.Papers.Example.statement\n",
            )
            self.assertEqual(check_claim_declarations(root), [])

    def test_final_proof_cannot_point_to_research(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            self.write(
                root,
                "Literature/Papers/Example.lean",
                "namespace Literature.Papers.Example\n"
                "def statement : Prop := True\n"
                "auditStatus := .claimAuditInProgress\n"
                "status := .provedInLean\n"
                '  "Literature.Papers.Example.statement"\n'
                '  "Research.Literature.Example.proof"\n'
                "end Literature.Papers.Example\n",
            )
            self.write(
                root,
                "Research/Literature/Example/Proof.lean",
                "namespace Research.Literature.Example\n"
                "theorem proof : True := by trivial\n"
                "end Research.Literature.Example\n",
            )

            failures = check_claim_declarations(root)

            self.assertTrue(any("belongs to a non-final lane" in failure
                                for failure in failures))

    def test_statement_must_be_owned_by_its_paper_module(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            self.write(
                root,
                "UniformEquilibrium/Canonical.lean",
                "namespace GameTheory\n"
                "theorem result : True := by trivial\n"
                "end GameTheory\n",
            )
            self.write(
                root,
                "Literature/Papers/Example.lean",
                "auditStatus := .correspondenceComplete\n"
                "status := .provedInLean\n"
                '  "GameTheory.result" "GameTheory.result"\n',
            )

            failures = check_claim_declarations(root)

            self.assertTrue(any("is not owned by Literature.Papers.Example"
                                in failure for failure in failures))

    def test_namespace_survives_an_ended_section(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            self.write(
                root,
                "Literature/Papers/Example.lean",
                "namespace Literature.Papers.Example\n"
                "section\n"
                "def helper : True := by trivial\n"
                "end\n"
                "def statement : Prop := True\n"
                "theorem proof : statement := by trivial\n"
                "auditStatus := .correspondenceComplete\n"
                "status := .provedInLean\n"
                '  "Literature.Papers.Example.statement"\n'
                '  "Literature.Papers.Example.proof"\n'
                "end Literature.Papers.Example\n",
            )

            self.assertEqual(check_claim_declarations(root), [])


if __name__ == "__main__":
    unittest.main()
