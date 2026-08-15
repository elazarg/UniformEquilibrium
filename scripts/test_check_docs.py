#!/usr/bin/env python3
"""Regression tests for documentation policy checks."""

from __future__ import annotations

import unittest

from scripts.check_docs import timeless_document_issues


class TimelessDocumentTests(unittest.TestCase):
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
