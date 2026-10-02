"""Keep the silent default build inside the action's cache-save boundary."""

from __future__ import annotations

import pathlib
import re
import shlex
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[1]


class LeanWorkflowTests(unittest.TestCase):
    def setUp(self) -> None:
        self.workflow = (ROOT / ".github/workflows/ci.yml").read_text()
        step = re.search(
            r"^      - uses: leanprover/lean-action@[^\n]+\n"
            r"(?P<configuration>(?:^        .*(?:\n|$))+)",
            self.workflow,
            re.MULTILINE,
        )
        self.assertIsNotNone(step, "Lean CI must use the action's build/cache owner")
        assert step is not None
        self.configuration = step.group("configuration")

    def test_project_build_precedes_action_cache_save(self) -> None:
        self.assertRegex(self.configuration, r"(?m)^          build: true$")
        self.assertNotRegex(self.workflow, r"(?m)^      - run: lake .*\bbuild\b")

    def test_build_is_silent_and_rejects_information(self) -> None:
        options = re.search(r"(?m)^          build-args: (.+)$", self.configuration)
        self.assertIsNotNone(options)
        assert options is not None
        arguments = shlex.split(options.group(1))
        self.assertEqual(len(arguments), 1)
        self.assertEqual(shlex.split(arguments[0]), ["--quiet", "--iofail"])
        self.assertRegex(self.workflow, r'(?m)^      LEAN_NUM_THREADS: "1"$')


if __name__ == "__main__":
    unittest.main()
