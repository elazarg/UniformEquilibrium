#!/usr/bin/env python3
"""Generate and check the Lean data block for the promoted cutoff table."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
TABLE = ROOT / "Experiments" / "quitting_repair_cegis" / "tables" / "cutoff_one_mixed.json"
ADAPTER = ROOT / "UniformEquilibrium" / "Diagnostics" / "Quitting" / "CutoffOneMixedActual.lean"
BEGIN = "-- BEGIN GENERATED CUTOFF_ONE_MIXED_DATA"
END = "-- END GENERATED CUTOFF_ONE_MIXED_DATA"

sys.path.insert(0, str(ROOT))

from Experiments.quitting_repair_cegis.model import RationalQuittingGame, fraction_text
from Experiments.quitting_repair_cegis.profiles import evaluate_cutoff_one
from Experiments.quitting_repair_cegis.report import (
    ACTUAL_CUTOFF_FINGERPRINT,
    table_fingerprint,
)


def _lean_vector(values: tuple[object, ...]) -> str:
    return "![" + ", ".join(fraction_text(value) for value in values) + "]"


def _lean_set(players: tuple[int, ...]) -> str:
    if not players:
        return "∅"
    return "{" + ", ".join(str(player) for player in players) + "}"


def load_promoted_game() -> RationalQuittingGame:
    game = RationalQuittingGame.from_path(TABLE)
    if table_fingerprint(game) != ACTUAL_CUTOFF_FINGERPRINT:
        raise ValueError("the promoted cutoff table fingerprint changed")
    if game.players != 2:
        raise ValueError("the promoted cutoff adapter expects exactly two players")
    roots = game.hints.get("cutoff_one_roots", [])
    if tuple(tuple(str(value) for value in root) for root in roots) != (
        ("1/2", "1/2"),
    ):
        raise ValueError("the promoted cutoff adapter expects the hinted root (1/2, 1/2)")
    evaluation = evaluate_cutoff_one(game, ("1/2", "1/2"))
    if not evaluation.exact:
        raise ValueError("the promoted cutoff table is not an exact cutoff-one repair")
    if evaluation.value != (0, 0):
        raise ValueError("the promoted cutoff table does not have payoff (0, 0)")
    return game


def render_block(game: RationalQuittingGame | None = None) -> str:
    game = game or load_promoted_game()
    rows = []
    for mask in range(1, 1 << game.players):
        players = tuple(
            player for player in range(game.players) if mask & (1 << player)
        )
        rows.append((players, game.payoff(mask)))
    branches = [
        f"if quitters.1 = {_lean_set(players)} then {_lean_vector(payoff)}"
        for players, payoff in rows[:-1]
    ]
    if not rows:
        raise ValueError("the promoted cutoff table has no reward rows")
    reward = "  " + "\n  else ".join(branches)
    reward += "\n  else " + _lean_vector(rows[-1][1])
    evaluation = evaluate_cutoff_one(game, ("1/2", "1/2"))
    fingerprint = table_fingerprint(game)
    return "\n".join(
        (
            BEGIN,
            "-- checked finite table",
            f"-- fingerprint: {fingerprint}",
            "abbrev Player := Fin 2",
            "abbrev Terminal := {S : Finset Player // S.Nonempty}",
            "",
            "/-- The two-player terminal reward rows from the source table. -/",
            "def reward (quitters : Terminal) : Payoff Player :=",
            reward,
            "",
            "/-- The hinted `(1/2, 1/2)` product root from the source table. -/",
            "def root : Player → PMF Bool := fun _ => PMF.uniformOfFintype Bool",
            "",
            "/-- The exact zero-tail payoff recomputed from the source table. -/",
            f"def value : Payoff Player := {_lean_vector(evaluation.value)}",
            END,
        )
    ) + "\n"


def replace_block(text: str, block: str) -> str:
    begin = text.find(BEGIN)
    end = text.find(END)
    if begin < 0 or end < 0 or end < begin:
        raise ValueError("adapter is missing generated data markers")
    end += len(END)
    return text[:begin] + block.rstrip("\n") + text[end:]


def check_adapter_text(actual: str, expected: str | None = None) -> list[str]:
    expected = expected or render_block()
    try:
        normalized = replace_block(actual, expected)
    except ValueError as exc:
        return [f"{ADAPTER.relative_to(ROOT)}: {exc}"]
    if normalized != actual:
        return [
            f"{ADAPTER.relative_to(ROOT)}: generated cutoff data is stale; "
            "run python scripts/generate_quitting_repair_adapters.py"
        ]
    return []


def check_adapter() -> list[str]:
    try:
        expected = render_block()
    except (OSError, TypeError, ValueError) as exc:
        return [str(exc)]
    return check_adapter_text(ADAPTER.read_text(encoding="utf-8"), expected)


def write_adapter() -> None:
    expected = render_block()
    actual = ADAPTER.read_text(encoding="utf-8")
    ADAPTER.write_text(replace_block(actual, expected), encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    if args.check:
        errors = check_adapter()
        if errors:
            for error in errors:
                print(error, file=sys.stderr)
            return 1
        print("quitting repair adapter data is fresh")
        return 0
    write_adapter()
    print(f"generated {ADAPTER.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
