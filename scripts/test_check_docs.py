#!/usr/bin/env python3
"""Regression tests for documentation policy checks."""

from __future__ import annotations

import pathlib
import tempfile
import unittest

from scripts.check_docs import (
    PRUNED_DIRECTORIES as DOCS_PRUNED_DIRECTORIES,
    ROOT,
    TIMELESS_DOCS,
    is_dedicated_history_or_evidence,
    named_source_reference_issues,
    project_markdown_files,
    source_reference_issues,
    timeless_document_issues,
)
from scripts.normalize_markdown_names import (
    PRUNED_DIRECTORIES as NAME_PRUNED_DIRECTORIES,
)


class TimelessDocumentTests(unittest.TestCase):
    def test_named_source_reference_validation(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            (root / "Owner.lean").write_text(
                "theorem first := True\ntheorem second := True\n",
                encoding="utf-8",
            )
            self.assertEqual(
                named_source_reference_issues(
                    "`second` (`Owner.lean`)\n"
                    "| A1 | `first` | `Owner.lean` | description |",
                    root,
                ),
                [],
            )
            self.assertEqual(
                named_source_reference_issues(
                    "`absent` (`Owner.lean`)",
                    root,
                ),
                ["named source reference absent not found in Owner.lean"],
            )

    def test_named_source_reference_survives_a_move_within_its_file(self) -> None:
        """Resolution is by name, so inserting lines above a cited declaration
        is not a documentation failure."""
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            owner = root / "Owner.lean"
            reference = "`first` (`Owner.lean`)"
            owner.write_text("theorem first := True\n", encoding="utf-8")
            self.assertEqual(named_source_reference_issues(reference, root), [])
            owner.write_text(
                "-- padding\n" * 40 + "theorem first := True\n",
                encoding="utf-8",
            )
            self.assertEqual(named_source_reference_issues(reference, root), [])

    def test_source_reference_validation(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            (root / "Owner.lean").write_text("one\ntwo\nthree\n", encoding="utf-8")
            self.assertEqual(source_reference_issues("`Owner.lean`", root), [])
            self.assertEqual(
                source_reference_issues("`Missing.lean`", root),
                ["missing source reference Missing.lean"],
            )

    def test_line_pinned_source_reference_is_rejected(self) -> None:
        """A line number goes stale on any insertion above the declaration, so
        a reference may not carry one even while the line is still correct."""
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            (root / "Owner.lean").write_text("one\ntwo\nthree\n", encoding="utf-8")
            self.assertEqual(
                source_reference_issues("`Owner.lean:2` and `Owner.lean:1-3`", root),
                [
                    "line-pinned source reference Owner.lean:2; "
                    "cite the declaration name instead",
                    "line-pinned source reference Owner.lean:1-3; "
                    "cite the declaration name instead",
                ],
            )

    def test_every_top_level_document_is_living(self) -> None:
        self.assertLessEqual(
            set((ROOT / "docs").glob("*.md")),
            set(TIMELESS_DOCS),
        )

    def test_lane_readmes_and_manifests_are_living(self) -> None:
        expected = {
            document
            for lane in ("Research", "Reverse", "Theorems", "UniformEquilibrium")
            for pattern in ("README.md", "MANIFEST.md")
            for document in (ROOT / lane).rglob(pattern)
        }
        self.assertLessEqual(expected, set(TIMELESS_DOCS))

    def test_methods_and_current_designs_are_living(self) -> None:
        methods = set((ROOT / "docs" / "methods").glob("*.md"))
        designs = {
            document
            for document in (ROOT / "docs" / "design").glob("*.md")
            if "Historical design record."
            not in document.read_text(encoding="utf-8")[:512]
        }
        self.assertLessEqual(methods | designs, set(TIMELESS_DOCS))

    def test_every_markdown_file_has_exactly_one_lifetime(self) -> None:
        documents = set(project_markdown_files())
        living = set(TIMELESS_DOCS) & documents
        evidence = {
            document
            for document in documents
            if is_dedicated_history_or_evidence(document)
        }
        self.assertFalse(living & evidence)
        self.assertEqual(documents, living | evidence)

    def test_private_literature_is_not_project_documentation(self) -> None:
        self.assertIn("literature", DOCS_PRUNED_DIRECTORIES)
        self.assertIn("literature", NAME_PRUNED_DIRECTORIES)

    def test_transition_record_is_history_not_living(self) -> None:
        transition = ROOT / "TRANSITION.md"
        self.assertNotIn(transition, TIMELESS_DOCS)
        self.assertTrue(is_dedicated_history_or_evidence(transition))

    def test_scoped_evidence_records_are_not_living(self) -> None:
        records = (
            ROOT / "docs" / "audits" / "README.md",
            ROOT / "docs" / "references" / "README.md",
            ROOT / "docs" / "case-studies" / "FTV_ARCHITECTURE_ANALYSIS.md",
            ROOT / "docs" / "design" / "HISTORY_CARRIER.md",
            ROOT / "Reverse" / "Tasks" / "Q194_SEMIALGEBRAIC_BARRIER_COMPLETENESS.md",
            ROOT / "Reverse" / "Runs" / "Q194_ONE_PALM_SPINE_COMPRESSION.md",
            ROOT / "Experiments" / "README.md",
        )
        for record in records:
            with self.subTest(record=record):
                self.assertNotIn(record, TIMELESS_DOCS)
                self.assertTrue(is_dedicated_history_or_evidence(record))

    def test_current_plan_is_allowed(self) -> None:
        text = """# Engineering roadmap

## Acceptance gates

Run the full build when a dependency pin changes.
Repository-transition provenance belongs in `TRANSITION.md`.
"""
        self.assertEqual(timeless_document_issues(text), [])

    def test_raw_commit_hash_is_rejected(self) -> None:
        issues = timeless_document_issues("Pinned dependency: 0123456789abcdef")
        self.assertIn("contains a raw Git commit hash", issues)

    def test_git_url_hash_is_rejected(self) -> None:
        issues = timeless_document_issues(
            "See https://github.com/example/project/tree/deadbee"
        )
        self.assertIn("contains a raw Git commit hash", issues)

    def test_numeric_source_identifier_is_allowed(self) -> None:
        self.assertEqual(
            timeless_document_issues("JSTOR stable identifier 3690127"),
            [],
        )

    def test_hexadecimal_doi_suffix_is_allowed(self) -> None:
        self.assertEqual(
            timeless_document_issues("DOI 10.1234/abcdef123456"),
            [],
        )

    def test_calendar_snapshot_is_rejected(self) -> None:
        issues = timeless_document_issues("Status as of 2026-08-15")
        self.assertIn("contains a calendar-dated snapshot", issues)

    def test_changelog_heading_is_rejected(self) -> None:
        for heading in (
            "## Changelog",
            "### Historical baseline",
            "## Phase 12 completed",
            "## Progress table",
        ):
            with self.subTest(heading=heading):
                self.assertIn(
                    "contains a changelog-style heading",
                    timeless_document_issues(heading),
                )

    def test_repository_change_narrative_is_rejected(self) -> None:
        for sentence in (
            "The first pass of this document got the evidence wrong.",
            "The theorem landed at deadbee.",
            "The forwarding shim was removed after promotion.",
            "This correction remains from the previous revision.",
        ):
            with self.subTest(sentence=sentence):
                self.assertIn(
                    "contains repository-change narrative",
                    timeless_document_issues(sentence),
                )

    def test_mathematical_removal_is_allowed(self) -> None:
        self.assertEqual(
            timeless_document_issues(
                "The transient state has been removed from the graph."
            ),
            [],
        )

    def test_forward_phase_heading_is_allowed(self) -> None:
        self.assertEqual(
            timeless_document_issues("### 3. Prove one stochastic semantic waist"),
            [],
        )

    def test_history_document_link_is_allowed(self) -> None:
        self.assertEqual(
            timeless_document_issues(
                "Extraction provenance belongs in [`TRANSITION.md`](../TRANSITION.md)."
            ),
            [],
        )


if __name__ == "__main__":
    unittest.main()
