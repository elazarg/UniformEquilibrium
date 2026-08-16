#!/usr/bin/env python3
"""Check the integrity of the checked-in K11 numeric Lean payloads.

This checker does not recreate the numerical computation. It parses the exact
rationals and integers from the checked-in Lean files, validates their shapes
and basic invariants, and compares both the source bytes and a
formatting-independent logical payload digest with the integrity manifest.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import sys
from fractions import Fraction
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
    "checked_in_evidence_without_reproducible_generator"
)
EXPECTED_SCHEMA_VERSION = 2
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
FLEX_INTERVAL_RE = re.compile(
    r"⟨\s*\(?(-?\d+)\)?\s*,\s*\(?(-?\d+)\)?\s*⟩", re.DOTALL
)
ROW_ZERO_VECTOR_NAMES = (
    "residualAtCenterCache",
    "preconditionedJacobianProductRowZeroCache",
    "preconditionedBRowZeroCache",
)
ROW_ZERO_SCALAR_NAMES = (
    "preconditionedResidualRowZero",
    "preconditionedRemainderRowZero",
    "krawczykRowZeroCache",
    "boxRowZeroCache",
)


class PayloadError(ValueError):
    """A checked-in Lean payload does not have its recorded structure."""


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def logical_digest(payload: dict[str, Any]) -> str:
    encoded = json.dumps(
        payload, ensure_ascii=True, separators=(",", ":"), sort_keys=True
    ).encode("ascii")
    return sha256_bytes(encoded)


def expected_row_labels(zero_name: str) -> list[str]:
    return [zero_name, *(f"{index:02d}" for index in range(1, MATRIX_SIZE))]


def fraction_payload(value: Fraction) -> list[int]:
    return [value.numerator, value.denominator]


def parse_dyadic_data(text: str) -> dict[str, Any]:
    precision_match = re.search(r"abbrev Precision\s*:\s*ℕ\s*:=\s*(\d+)", text)
    if precision_match is None:
        raise PayloadError("missing dyadic-data Precision")

    center_match = re.search(
        r"def center\s*:\s*HazardIndex\s*→\s*ℚ\s*:=\s*!\[(.*?)\n\]",
        text,
        re.DOTALL,
    )
    if center_match is None:
        raise PayloadError("missing dyadic-data center vector")
    center = [
        Fraction(token)
        for token in re.findall(r"-?\d+(?:\.\d+)?", center_match.group(1))
    ]
    if len(center) != MATRIX_SIZE:
        raise PayloadError(
            f"dyadic-data center has {len(center)} entries, expected {MATRIX_SIZE}"
        )

    radius_match = re.search(
        r"def radius\s*:\s*ℚ\s*:=\s*(-?\d+)\s*/\s*(\d+)", text
    )
    if radius_match is None:
        raise PayloadError("missing dyadic-data rational radius")
    radius = Fraction(int(radius_match.group(1)), int(radius_match.group(2)))
    if radius < 0:
        raise PayloadError(f"dyadic-data radius is negative: {radius}")

    box_match = re.search(
        r"def box\s*\(index\s*:\s*HazardIndex\)\s*:\s*"
        r"DyadicInterval Precision\s*:=\s*"
        r"⟨Rat\.floor\s*\(\(center index - radius\)\s*\*\s*"
        r"DyadicInterval\.scale Precision\),\s*"
        r"Rat\.ceil\s*\(\(center index \+ radius\)\s*\*\s*"
        r"DyadicInterval\.scale Precision\)⟩",
        text,
        re.DOTALL,
    )
    if box_match is None:
        raise PayloadError("dyadic-data box is not the recorded outward rounding")

    return {
        "kind": "exact_dyadic_box_data",
        "precision": int(precision_match.group(1)),
        "center": [fraction_payload(value) for value in center],
        "radius": fraction_payload(radius),
    }


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

    routing_match = re.search(
        r"def preconditionerNumerator\s*:.*?\s*:=\s*"
        r"fun row column\s*=>\s*\(Vector\.ofFn\s*!\[(.*?)\]\)"
        r"\.get row column",
        text,
        re.DOTALL,
    )
    if routing_match is None:
        raise PayloadError("missing preconditioner row/column assembly")
    row_routing = re.findall(
        r"preconditionerNumeratorRow(?:Zero|\d{2})", routing_match.group(1)
    )
    expected_routing = [
        "preconditionerNumeratorRowZero",
        *(f"preconditionerNumeratorRow{index:02d}" for index in range(1, 31)),
    ]
    if row_routing != expected_routing:
        raise PayloadError(
            f"preconditioner row routing is {row_routing!r}, "
            f"expected {expected_routing!r}"
        )

    wrapper_match = re.search(
        r"def preconditioner\s*\(row column\s*:\s*PreconditionerIndex\)"
        r"\s*:\s*ℚ\s*:=\s*"
        r"\(preconditionerNumerator row column\s*:\s*ℚ\)\s*/\s*"
        r"preconditionerScale",
        text,
    )
    if wrapper_match is None:
        raise PayloadError("missing rational preconditioner scale wrapper")

    return {
        "kind": "rational_preconditioner_numerators",
        "scale_power": int(scale_match.group(1)),
        "row_zero_absolute_sum": recorded_abs_sum,
        "rows": rows,
        "row_routing": row_routing,
        "wrapper": "preconditionerNumerator/preconditionerScale",
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

    routing_match = re.search(
        r"def jacobianBoxCacheRow\s*\(row\s*:\s*Fin 31\)\s*:.*?"
        r"\s*:=\s*(.*?)\n\ndef jacobianBoxCache\s*:",
        text,
        re.DOTALL,
    )
    if routing_match is None:
        raise PayloadError("missing Jacobian Fin.cases row assembly")
    routing_body = routing_match.group(1)
    expected_routing = [
        f"jacobianBoxCacheRow{index:02d}" for index in range(MATRIX_SIZE)
    ]
    row_routing = re.findall(r"jacobianBoxCacheRow\d{2}", routing_body)
    if row_routing != expected_routing:
        raise PayloadError(
            f"Jacobian row routing is {row_routing!r}, "
            f"expected {expected_routing!r}"
        )

    expected_body = "Fin.cases jacobianBoxCacheRow00"
    for index in range(MATRIX_SIZE - 1):
        expected_body += (
            f" (fun t{index} => Fin.cases "
            f"jacobianBoxCacheRow{index + 1:02d}"
        )
    expected_body += " (fun impossible => Fin.elim0 impossible)"
    for index in reversed(range(MATRIX_SIZE - 1)):
        expected_body += f" t{index})"
    expected_body += " row"

    token_pattern = r"[A-Za-z_][A-Za-z0-9_]*|\d+|=>|[().]"
    if re.findall(token_pattern, routing_body) != re.findall(
        token_pattern, expected_body
    ):
        raise PayloadError("Jacobian Fin.cases assembly does not match row order")

    constructor_match = re.search(
        r"def jacobianBoxCache\s*:\s*"
        r"Vector \(Vector \(DyadicInterval JacobianCachePrecision\) 31\) 31"
        r"\s*:=\s*Vector\.ofFn jacobianBoxCacheRow",
        text,
    )
    if constructor_match is None:
        raise PayloadError("missing final Jacobian cache constructor")

    return {
        "kind": "dyadic_jacobian_intervals",
        "precision": int(precision_match.group(1)),
        "rows": rows,
        "row_routing": row_routing,
        "constructor": "Vector.ofFn jacobianBoxCacheRow",
    }


def parse_row_zero_cache(text: str) -> dict[str, Any]:
    precision_match = re.search(
        r"abbrev CachePrecision\s*:\s*ℕ\s*:=\s*(\d+)", text
    )
    if precision_match is None:
        raise PayloadError("missing row-zero CachePrecision")

    vectors: dict[str, list[list[int]]] = {}
    for name in ROW_ZERO_VECTOR_NAMES:
        match = re.search(
            rf"def {name}\s*:\s*"
            r"Vector \(DyadicInterval CachePrecision\) 31\s*:=\s*"
            r"Vector\.ofFn\s*!\[(.*?)\n\]",
            text,
            re.DOTALL,
        )
        if match is None:
            raise PayloadError(f"missing row-zero vector {name}")
        entries = [
            [int(lower), int(upper)]
            for lower, upper in FLEX_INTERVAL_RE.findall(match.group(1))
        ]
        if len(entries) != MATRIX_SIZE:
            raise PayloadError(
                f"row-zero vector {name} has {len(entries)} intervals, "
                f"expected {MATRIX_SIZE}"
            )
        for index, (lower, upper) in enumerate(entries):
            if lower > upper:
                raise PayloadError(
                    f"row-zero interval {name}[{index}] is reversed: "
                    f"{lower} > {upper}"
                )
        vectors[name] = entries

    scalars: dict[str, list[int]] = {}
    for name in ROW_ZERO_SCALAR_NAMES:
        match = re.search(
            rf"def {name}\s*:\s*DyadicInterval CachePrecision\s*:=\s*"
            r"⟨\s*\(?(-?\d+)\)?\s*,\s*\(?(-?\d+)\)?\s*⟩",
            text,
            re.DOTALL,
        )
        if match is None:
            raise PayloadError(f"missing row-zero scalar {name}")
        lower, upper = (int(value) for value in match.groups())
        if lower > upper:
            raise PayloadError(
                f"row-zero scalar {name} is reversed: {lower} > {upper}"
            )
        scalars[name] = [lower, upper]

    return {
        "kind": "dyadic_row_zero_cache",
        "precision": int(precision_match.group(1)),
        "vectors": vectors,
        "scalars": scalars,
    }


PARSERS = {
    "dyadic_data": parse_dyadic_data,
    "preconditioner": parse_preconditioner,
    "jacobian_cache": parse_jacobian,
    "row_zero_cache": parse_row_zero_cache,
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
    calculated = {
        "source_file_sha256": sha256_bytes(source),
        "logical_payload_sha256": logical_digest(payload),
    }
    if name == "dyadic_data":
        calculated["precision"] = payload["precision"]
        calculated["center_count"] = len(payload["center"])
        calculated["radius_numerator"] = payload["radius"][0]
        calculated["radius_denominator"] = payload["radius"][1]
    elif name == "preconditioner":
        rows = payload["rows"]
        calculated["rows"] = len(rows)
        calculated["columns"] = len(rows[0]) if rows else 0
        calculated["scale_power"] = payload["scale_power"]
        calculated["row_zero_absolute_sum"] = payload["row_zero_absolute_sum"]
    elif name == "jacobian_cache":
        rows = payload["rows"]
        calculated["rows"] = len(rows)
        calculated["columns"] = len(rows[0]) if rows else 0
        calculated["precision"] = payload["precision"]
    elif name == "row_zero_cache":
        vectors = payload["vectors"]
        calculated["precision"] = payload["precision"]
        calculated["vector_count"] = len(vectors)
        calculated["vector_length"] = len(next(iter(vectors.values())))
        calculated["scalar_count"] = len(payload["scalars"])
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
        return [f"cannot read K11 integrity manifest: {error}"]

    if manifest.get("schema_version") != EXPECTED_SCHEMA_VERSION:
        errors.append("unsupported K11 integrity manifest schema_version")
    if manifest.get("classification") != EXPECTED_CLASSIFICATION:
        errors.append(
            "K11 integrity manifest must retain its explicit "
            "generator-availability classification"
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
            "K11 integrity manifest must describe exactly dyadic_data, "
            "preconditioner, jacobian_cache, and row_zero_cache"
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
    print("K11 generated-data integrity check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
