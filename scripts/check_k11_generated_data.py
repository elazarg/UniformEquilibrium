#!/usr/bin/env python3
"""Check the integrity of the migrated K11 numeric Lean payloads.

This checker does not recreate the lost q117 numerical computation.  It
parses the surviving exact integers from the checked-in Lean files, validates
their matrix shape and basic invariants, and compares both the source bytes
and a formatting-independent logical payload digest with the provenance
manifest.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import sys
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST_PATH = (
    ROOT
    / "Experiments"
    / "certsearch"
    / "block_pair"
    / "k11_generated_data_manifest.json"
)
EXPECTED_CLASSIFICATION = (
    "migrated_checked_in_evidence_without_reproducible_original_producer"
)
MATRIX_SIZE = 31

PRECONDITIONER_ROW_RE = re.compile(
    r"def preconditionerNumeratorRow(Zero|\d{2})\s*:\s*"
    r"PreconditionerIndex\s*→\s*ℤ\s*:=\s*!\[(.*?)\n\]",
    re.DOTALL,
)
JACOBIAN_ROW_RE = re.compile(
    r"def jacobianBoxCacheRow(\d{2})\s*:\s*"
    r"Vector \(DyadicInterval JacobianCachePrecision\) 31\s*:=\s*"
    r"Vector\.ofFn\s*!\[(.*?)\n\]",
    re.DOTALL,
)
INTERVAL_RE = re.compile(r"⟨\s*\((-?\d+)\),\s*\((-?\d+)\)⟩", re.DOTALL)


class PayloadError(ValueError):
    """A surviving Lean payload does not have its recorded structure."""


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def logical_digest(payload: dict[str, Any]) -> str:
    encoded = json.dumps(
        payload, ensure_ascii=True, separators=(",", ":"), sort_keys=True
    ).encode("ascii")
    return sha256_bytes(encoded)


def expected_row_labels(zero_name: str) -> list[str]:
    return [zero_name, *(f"{index:02d}" for index in range(1, MATRIX_SIZE))]


def parse_preconditioner(text: str) -> dict[str, Any]:
    scale_match = re.search(
        r"def preconditionerScale\s*:\s*ℤ\s*:=\s*2\s*\^\s*(\d+)", text
    )
    if scale_match is None:
        raise PayloadError("missing preconditionerScale power")

    matches = PRECONDITIONER_ROW_RE.findall(text)
    labels = [label for label, _ in matches]
    expected_labels = expected_row_labels("Zero")
    if labels != expected_labels:
        raise PayloadError(
            f"preconditioner row labels are {labels!r}, expected {expected_labels!r}"
        )

    rows: list[list[int]] = []
    for label, body in matches:
        entries = [int(value) for value in re.findall(r"-?\d+", body)]
        if len(entries) != MATRIX_SIZE:
            raise PayloadError(
                f"preconditioner row {label} has {len(entries)} entries, "
                f"expected {MATRIX_SIZE}"
            )
        rows.append(entries)

    abs_sum_match = re.search(
        r"def preconditionerRowZeroAbsSum\s*:\s*ℤ\s*:=\s*(\d+)", text
    )
    if abs_sum_match is None:
        raise PayloadError("missing preconditionerRowZeroAbsSum")
    recorded_abs_sum = int(abs_sum_match.group(1))
    computed_abs_sum = sum(abs(value) for value in rows[0])
    if recorded_abs_sum != computed_abs_sum:
        raise PayloadError(
            "preconditioner row-zero absolute sum is "
            f"{recorded_abs_sum}, computed {computed_abs_sum}"
        )

    return {
        "kind": "rational_preconditioner_numerators",
        "scale_power": int(scale_match.group(1)),
        "row_zero_absolute_sum": recorded_abs_sum,
        "rows": rows,
    }


def parse_jacobian(text: str) -> dict[str, Any]:
    precision_match = re.search(
        r"abbrev JacobianCachePrecision\s*:\s*ℕ\s*:=\s*(\d+)", text
    )
    if precision_match is None:
        raise PayloadError("missing JacobianCachePrecision")

    matches = JACOBIAN_ROW_RE.findall(text)
    labels = [label for label, _ in matches]
    expected_labels = expected_row_labels("00")
    if labels != expected_labels:
        raise PayloadError(
            f"Jacobian row labels are {labels!r}, expected {expected_labels!r}"
        )

    rows: list[list[list[int]]] = []
    for label, body in matches:
        entries = [
            [int(lower), int(upper)]
            for lower, upper in INTERVAL_RE.findall(body)
        ]
        if len(entries) != MATRIX_SIZE:
            raise PayloadError(
                f"Jacobian row {label} has {len(entries)} intervals, "
                f"expected {MATRIX_SIZE}"
            )
        for column, (lower, upper) in enumerate(entries):
            if lower > upper:
                raise PayloadError(
                    f"Jacobian interval ({int(label)}, {column}) is reversed: "
                    f"{lower} > {upper}"
                )
        rows.append(entries)

    return {
        "kind": "dyadic_jacobian_intervals",
        "precision": int(precision_match.group(1)),
        "rows": rows,
    }


PARSERS = {
    "preconditioner": parse_preconditioner,
    "jacobian_cache": parse_jacobian,
}


def resolve_project_path(root: pathlib.Path, relative_text: str) -> pathlib.Path:
    relative = pathlib.PurePosixPath(relative_text)
    if relative.is_absolute() or ".." in relative.parts:
        raise PayloadError(f"manifest path escapes the repository: {relative_text}")
    return root.joinpath(*relative.parts)


def calculate_artifact(
    root: pathlib.Path, name: str, entry: dict[str, Any]
) -> dict[str, Any]:
    parser = PARSERS.get(name)
    if parser is None:
        raise PayloadError(f"unsupported artifact key {name!r}")
    path = resolve_project_path(root, entry["path"])
    source = path.read_bytes()
    payload = parser(source.decode("utf-8"))
    rows = payload["rows"]
    calculated = {
        "source_file_sha256": sha256_bytes(source),
        "logical_payload_sha256": logical_digest(payload),
        "rows": len(rows),
        "columns": len(rows[0]) if rows else 0,
    }
    if name == "preconditioner":
        calculated["scale_power"] = payload["scale_power"]
        calculated["row_zero_absolute_sum"] = payload["row_zero_absolute_sum"]
    elif name == "jacobian_cache":
        calculated["precision"] = payload["precision"]
    return calculated


def load_manifest(path: pathlib.Path = MANIFEST_PATH) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def check_repository(
    root: pathlib.Path = ROOT, manifest_path: pathlib.Path = MANIFEST_PATH
) -> list[str]:
    errors: list[str] = []
    try:
        manifest = load_manifest(manifest_path)
    except (OSError, json.JSONDecodeError) as error:
        return [f"cannot read K11 provenance manifest: {error}"]

    if manifest.get("schema_version") != 1:
        errors.append("unsupported K11 provenance manifest schema_version")
    if manifest.get("classification") != EXPECTED_CLASSIFICATION:
        errors.append(
            "K11 provenance manifest must retain its explicit "
            "non-regeneration classification"
        )
    if manifest.get("integrity_check_reproducible") is not True:
        errors.append("K11 integrity check must remain classified as reproducible")
    if manifest.get("original_numeric_generation_reproducible") is not False:
        errors.append(
            "K11 original numeric generation must remain classified as "
            "non-reproducible"
        )

    artifacts = manifest.get("artifacts")
    if not isinstance(artifacts, dict) or set(artifacts) != set(PARSERS):
        errors.append(
            "K11 provenance manifest must describe exactly preconditioner and "
            "jacobian_cache"
        )
        return errors

    for name, entry in artifacts.items():
        try:
            actual = calculate_artifact(root, name, entry)
        except (KeyError, OSError, UnicodeDecodeError, PayloadError) as error:
            errors.append(f"{name}: {error}")
            continue
        for field, actual_value in actual.items():
            expected_value = entry.get(field)
            if expected_value != actual_value:
                errors.append(
                    f"{name}: {field} is {actual_value!r}, "
                    f"manifest records {expected_value!r}"
                )
    return errors


def print_hashes(root: pathlib.Path, manifest_path: pathlib.Path) -> int:
    manifest = load_manifest(manifest_path)
    for name, entry in manifest["artifacts"].items():
        calculated = calculate_artifact(root, name, entry)
        print(name)
        for field, value in calculated.items():
            print(f"  {field}: {value}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--show-hashes",
        action="store_true",
        help="print current file and normalized payload hashes",
    )
    args = parser.parse_args()
    if args.show_hashes:
        return print_hashes(ROOT, MANIFEST_PATH)

    errors = check_repository()
    if errors:
        print("K11 generated-data check failed:", file=sys.stderr)
        print(*errors, sep="\n", file=sys.stderr)
        return 1
    print("K11 migrated generated-data integrity check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
