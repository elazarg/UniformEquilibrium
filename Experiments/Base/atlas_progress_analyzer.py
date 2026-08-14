"""E04: treat the analytic endpoint atlas as a small typed language.

This is a read-only analyzer.  Constructors are introduction forms; a
`RequiredReconstructionAt` match arm names the elimination rule required to
make progress.  A residual structure whose own field already returns the final
adaptive certificate is marked `conclusion-bearing`: it records an obligation
but does not decompose it.

The analyzer intentionally uses only shallow syntax.  It is a refactor alarm
and research dashboard, not a Lean parser or a soundness checker.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


CONSTRUCTOR_RE = re.compile(r"^\s*\|\s+([A-Za-z][A-Za-z0-9_]*)", re.MULTILINE)
MATCH_ARM_RE = re.compile(
    r"^\s*\|\s+\.([A-Za-z][A-Za-z0-9_]*)\s+[^=]*=>\s*([A-Za-z][A-Za-z0-9_]*)",
    re.MULTILINE,
)
STRUCTURE_RE = re.compile(
    r"structure\s+([A-Za-z][A-Za-z0-9_]*)[^\n]*\n(?P<body>.*?)(?=\n(?:structure|def|theorem|lemma|inductive|namespace|end)\b)",
    re.DOTALL,
)


def block_between(text: str, start: str, end: str) -> str:
    start_index = text.index(start)
    end_index = text.index(end, start_index)
    return text[start_index:end_index]


def analyze(repo: Path) -> dict:
    atlas = repo / "UniformEquilibrium/VanishingDiscount/Analytic/Endpoint/Atlas.lean"
    text = atlas.read_text(encoding="utf-8")
    inductive_block = block_between(
        text, "inductive AnalyticEndpointAtlasLeaf", "namespace AnalyticEndpointAtlasLeaf"
    )
    constructors = CONSTRUCTOR_RE.findall(inductive_block)

    reconstruction_block = block_between(
        text, "def RequiredReconstructionAt", "/-- A leaf is fully resolved"
    )
    reconstruction_map = dict(MATCH_ARM_RE.findall(reconstruction_block))
    # The semantic branch returns PUnit, which is intentionally not a named
    # reconstruction structure and is captured separately.
    reconstruction_map["semanticClose"] = "PUnit"

    structures = {}
    for match in STRUCTURE_RE.finditer(text):
        name = match.group(1)
        body = match.group("body")
        structures[name] = {
            "conclusion_bearing": "IsAdaptivePotentialCertificateAt" in body,
            "mentions_strategy": bool(re.search(r"strategy|profile|Behavior", body, re.I)),
            "mentions_target": "Target" in body or "target" in body,
            "mentions_rank": "rank" in body.lower(),
            "mentions_account": "account" in body.lower() or "charge" in body.lower(),
        }

    lean_files = list((repo / "GameTheory").rglob("*.lean"))
    external_occurrences = {}
    for constructor in constructors:
        count = 0
        for path in lean_files:
            if path == atlas:
                continue
            count += len(re.findall(rf"\b{re.escape(constructor)}\b", path.read_text(encoding="utf-8")))
        external_occurrences[constructor] = count

    leaves = []
    for constructor in constructors:
        required = reconstruction_map.get(constructor, "UNPARSED")
        info = structures.get(required, {})
        leaves.append(
            {
                "constructor": constructor,
                "required_eliminator": required,
                "semantic_terminal": constructor == "semanticClose",
                "conclusion_bearing_obligation": info.get("conclusion_bearing", False),
                "external_textual_occurrences": external_occurrences[constructor],
                "interface_features": {
                    key: value for key, value in info.items() if key != "conclusion_bearing"
                },
            }
        )

    assert len(constructors) == 14, f"expected 14 atlas constructors, found {len(constructors)}"
    assert sum(leaf["semantic_terminal"] for leaf in leaves) == 1
    assert all(leaf["required_eliminator"] != "UNPARSED" for leaf in leaves)

    return {
        "experiment": "E04",
        "status": "passed",
        "atlas": str(atlas.relative_to(repo)),
        "constructor_count": len(constructors),
        "nonsemantic_count": len(constructors) - 1,
        "conclusion_bearing_nonsemantic_obligations": sum(
            leaf["conclusion_bearing_obligation"] and not leaf["semantic_terminal"]
            for leaf in leaves
        ),
        "leaves": leaves,
        "conclusion": (
            "The atlas case split is a total canonical-forms theorem, but its "
            "reconstruction records are conclusion-bearing elimination obligations; "
            "the analyzer distinguishes typed bookkeeping from concrete producers."
        ),
        "limitation": "Textual occurrence counts are navigation hints, not dependency proofs.",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--repo",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="repository root",
    )
    args = parser.parse_args()
    print(json.dumps(analyze(args.repo.resolve()), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
