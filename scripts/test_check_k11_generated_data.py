#!/usr/bin/env python3
"""Regression tests for the K11 payload integrity checker."""

from __future__ import annotations

import copy
import importlib.util
import json
import pathlib
import shutil
import tempfile
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[1]
CHECKER_PATH = ROOT / "scripts" / "check_k11_generated_data.py"
SPEC = importlib.util.spec_from_file_location("check_k11_generated_data", CHECKER_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load {CHECKER_PATH}")
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


def artifact_path(name: str) -> pathlib.Path:
    entry = CHECKER.load_manifest()["artifacts"][name]
    return CHECKER.resolve_project_path(ROOT, entry["path"])


class K11GeneratedDataTests(unittest.TestCase):
    def test_repository_matches_manifest(self) -> None:
        self.assertEqual(CHECKER.check_repository(), [])

    def test_manifest_covers_every_payload_class(self) -> None:
        artifacts = CHECKER.load_manifest()["artifacts"]
        self.assertEqual(set(artifacts), set(CHECKER.PARSERS))

    def test_dyadic_center_shape_change_is_rejected(self) -> None:
        text = artifact_path("dyadic_data").read_text(encoding="utf-8")
        changed = text.replace("  0.070773162508252468,", "", 1)
        with self.assertRaisesRegex(CHECKER.PayloadError, "has 30 entries"):
            CHECKER.parse_dyadic_data(changed)

    def test_preconditioner_shape_change_is_rejected(self) -> None:
        text = artifact_path("preconditioner").read_text(encoding="utf-8")
        changed = text.replace("  -7130412613540890,\n", "", 1)
        with self.assertRaisesRegex(CHECKER.PayloadError, "has 30 entries"):
            CHECKER.parse_preconditioner(changed)

    def test_preconditioner_row_routing_swap_is_rejected(self) -> None:
        text = artifact_path("preconditioner").read_text(encoding="utf-8")
        changed = text.replace(
            "    preconditionerNumeratorRow01,\n"
            "    preconditionerNumeratorRow02,",
            "    preconditionerNumeratorRow02,\n"
            "    preconditionerNumeratorRow01,",
            1,
        )
        with self.assertRaisesRegex(CHECKER.PayloadError, "row routing"):
            CHECKER.parse_preconditioner(changed)

    def test_preconditioner_wrapper_change_is_rejected(self) -> None:
        text = artifact_path("preconditioner").read_text(encoding="utf-8")
        changed = text.replace(
            "  (preconditionerNumerator row column : ℚ) / "
            "preconditionerScale",
            "  (preconditionerNumerator row column : ℚ) * "
            "preconditionerScale",
            1,
        )
        with self.assertRaisesRegex(CHECKER.PayloadError, "scale wrapper"):
            CHECKER.parse_preconditioner(changed)

    def test_jacobian_reversed_interval_is_rejected(self) -> None:
        text = artifact_path("jacobian_cache").read_text(encoding="utf-8")
        changed = text.replace(
            "⟨(-56861261462224415),\n    (56861261462224416)⟩",
            "⟨(56861261462224417),\n    (56861261462224416)⟩",
            1,
        )
        with self.assertRaisesRegex(CHECKER.PayloadError, "is reversed"):
            CHECKER.parse_jacobian(changed)

    def test_jacobian_row_routing_swap_is_rejected(self) -> None:
        text = artifact_path("jacobian_cache").read_text(encoding="utf-8")
        changed = text.replace(
            "Fin.cases jacobianBoxCacheRow00\n"
            "      (fun t0 => Fin.cases jacobianBoxCacheRow01",
            "Fin.cases jacobianBoxCacheRow01\n"
            "      (fun t0 => Fin.cases jacobianBoxCacheRow00",
            1,
        )
        with self.assertRaisesRegex(CHECKER.PayloadError, "row routing"):
            CHECKER.parse_jacobian(changed)

    def test_jacobian_constructor_change_is_rejected(self) -> None:
        text = artifact_path("jacobian_cache").read_text(encoding="utf-8")
        changed = text.replace(
            "Vector.ofFn jacobianBoxCacheRow",
            "Vector.ofFn (fun row => jacobianBoxCacheRow row)",
            1,
        )
        with self.assertRaisesRegex(CHECKER.PayloadError, "cache constructor"):
            CHECKER.parse_jacobian(changed)

    def test_row_zero_reversed_interval_is_rejected(self) -> None:
        text = artifact_path("row_zero_cache").read_text(encoding="utf-8")
        changed = text.replace(
            "⟨198820559, 198820768⟩", "⟨198820769, 198820768⟩", 1
        )
        with self.assertRaisesRegex(CHECKER.PayloadError, "is reversed"):
            CHECKER.parse_row_zero_cache(changed)

    def test_payload_mutation_is_rejected_for_every_artifact(self) -> None:
        mutations = {
            "dyadic_data": (
                "0.070773162508252468",
                "0.070773162508252469",
            ),
            "preconditioner": (
                "-7130412613540890",
                "-7130412613540891",
            ),
            "jacobian_cache": (
                "-56861261462224415",
                "-56861261462224414",
            ),
            "row_zero_cache": ("198820559", "198820560"),
        }
        manifest = CHECKER.load_manifest()
        with tempfile.TemporaryDirectory() as directory:
            temporary_root = pathlib.Path(directory)
            manifest_path = temporary_root / "manifest.json"
            for entry in manifest["artifacts"].values():
                source = CHECKER.resolve_project_path(ROOT, entry["path"])
                target = CHECKER.resolve_project_path(
                    temporary_root, entry["path"]
                )
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source, target)
            manifest_path.write_text(json.dumps(manifest), encoding="utf-8")

            for name, (before, after) in mutations.items():
                with self.subTest(artifact=name):
                    target = CHECKER.resolve_project_path(
                        temporary_root, manifest["artifacts"][name]["path"]
                    )
                    original = target.read_text(encoding="utf-8")
                    self.assertIn(before, original)
                    target.write_text(
                        original.replace(before, after, 1), encoding="utf-8"
                    )
                    errors = CHECKER.check_repository(
                        temporary_root, manifest_path
                    )
                    self.assertTrue(
                        any(error.startswith(f"{name}:") for error in errors),
                        errors,
                    )
                    target.write_text(original, encoding="utf-8")

    def test_manifest_path_drift_is_rejected(self) -> None:
        manifest = copy.deepcopy(CHECKER.load_manifest())
        manifest["artifacts"]["dyadic_data"]["path"] = "missing.lean"
        with tempfile.TemporaryDirectory() as directory:
            manifest_path = pathlib.Path(directory) / "manifest.json"
            manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
            errors = CHECKER.check_repository(ROOT, manifest_path)
        self.assertTrue(
            any(error.startswith("dyadic_data:") for error in errors), errors
        )

    def test_manifest_provenance_record_drift_is_rejected(self) -> None:
        manifest = copy.deepcopy(CHECKER.load_manifest())
        manifest["provenance_record"] = (
            "Experiments/certsearch/block_pair/K11/MANIFEST.md#missing"
        )
        with tempfile.TemporaryDirectory() as directory:
            manifest_path = pathlib.Path(directory) / "manifest.json"
            manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
            errors = CHECKER.check_repository(ROOT, manifest_path)
        self.assertIn(
            "K11 integrity manifest must point to its owning provenance record",
            errors,
        )

    def test_manifest_fingerprint_drift_is_rejected(self) -> None:
        manifest = copy.deepcopy(CHECKER.load_manifest())
        manifest["artifacts"]["row_zero_cache"][
            "logical_payload_sha256"
        ] = "0" * 64
        with tempfile.TemporaryDirectory() as directory:
            manifest_path = pathlib.Path(directory) / "manifest.json"
            manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
            errors = CHECKER.check_repository(ROOT, manifest_path)
        self.assertTrue(
            any(
                error.startswith("row_zero_cache: logical_payload_sha256")
                for error in errors
            ),
            errors,
        )

    def test_payload_digest_ignores_unparsed_comments(self) -> None:
        text = artifact_path("jacobian_cache").read_text(encoding="utf-8")
        original = CHECKER.logical_digest(CHECKER.parse_jacobian(text))
        changed = CHECKER.logical_digest(
            CHECKER.parse_jacobian("/- note -/\n" + text)
        )
        self.assertEqual(original, changed)


if __name__ == "__main__":
    unittest.main()
