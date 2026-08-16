"""Exact search for the incidence-to-return-selection seam.

The search uses a two-player literal profile with player 0 always continuing,
player 1 quitting only at the first stage with rational probability ``q``,
and both players continuing forever after survival.  Its outcome law is

    q * {1} + (1-q) * Never.

For every small integer quitting table we compute the prescribed payoff and
the full behavioral best-response envelope exactly over ``Fraction``.  We
then ask for:

* zero debt of the marked player 0;
* positive total debt and positive terminal incidence of player 1;
* a lower-hazard co-realized source with positive, strictly smaller debt;
* strict dominance of Quit by Continue in the finite cap game.

The last condition makes all-Continue the unique exact cap--Nash root.  Hence
no root can spend the positive source--target debt excess, despite exact
reward-moment coupling and positive same-law incidence.

This is a local-passport audit, not a counterexample to the quitting-game
conjecture: the displayed table also has the all-Continue executable profile
with zero debt.  In particular the positive source is not a global carrier
minimum.  The point is that incidence and reward-moment data do not encode
that missing global provenance or any sign-aligned exercise premium.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product


@dataclass(frozen=True)
class Table:
    # Coordinates are rewards at {0}, {1}, and {0,1}.
    r0_0: int
    r0_1: int
    r0_01: int
    r1_0: int
    r1_1: int
    r1_01: int


@dataclass(frozen=True)
class Semantic:
    prescribed: tuple[Q, Q]
    cap: tuple[Q, Q]

    @property
    def debt(self) -> tuple[Q, Q]:
        return tuple(b - u for u, b in zip(self.prescribed, self.cap))  # type: ignore[return-value]

    @property
    def total_debt(self) -> Q:
        return sum(self.debt, Q(0))


def one_stage_semantic(table: Table, q: Q) -> Semantic:
    """Exact terminal semantics of ``Continue x Bernoulli(q)`` at time 0."""

    prescribed = (q * table.r0_1, q * table.r1_1)
    best0_quit = q * table.r0_01 + (1 - q) * table.r0_0
    best0_continue = q * table.r0_1 + (1 - q) * max(0, table.r0_0)
    best1 = max(0, table.r1_1)
    return Semantic(
        prescribed,
        (max(best0_quit, best0_continue), Q(best1)),
    )


def quit_strictly_dominated_in_cap_game(table: Table, cap: tuple[Q, Q]) -> bool:
    """Check both pure opponent endpoints; affine extension is automatic."""

    return (
        table.r0_0 < cap[0]
        and table.r0_01 < table.r0_1
        and table.r1_1 < cap[1]
        and table.r1_01 < table.r1_0
    )


def search() -> dict[str, object]:
    hazards = (Q(1, 4), Q(1, 2), Q(3, 4))
    checked = 0
    for entries in product(range(-1, 2), repeat=6):
        table = Table(*entries)
        for source_q in hazards:
            source = one_stage_semantic(table, source_q)
            if source.total_debt <= 0:
                continue
            for target_q in hazards:
                if target_q <= source_q:
                    continue
                checked += 1
                target = one_stage_semantic(table, target_q)
                if target.debt[0] != 0:
                    continue
                if target.total_debt <= source.total_debt:
                    continue
                if not quit_strictly_dominated_in_cap_game(table, target.cap):
                    continue
                excess = target.total_debt - source.total_debt
                return {
                    "checked": checked,
                    "table": table.__dict__,
                    "source_q": str(source_q),
                    "target_q": str(target_q),
                    "source": {
                        "prescribed": tuple(map(str, source.prescribed)),
                        "cap": tuple(map(str, source.cap)),
                        "debt": tuple(map(str, source.debt)),
                    },
                    "target": {
                        "prescribed": tuple(map(str, target.prescribed)),
                        "cap": tuple(map(str, target.cap)),
                        "debt": tuple(map(str, target.debt)),
                    },
                    "opponent_incidence": str(target_q),
                    "unique_cap_nash_survival": "1",
                    "unique_cap_nash_absorption": "0",
                    "required_return_charge_at_tolerance_zero": str(excess),
                    "selection_holds": False,
                    "global_minimum_warning": (
                        "The all-Continue executable profile has zero debt; "
                        "the positive source is not a global carrier minimum."
                    ),
                }
    raise RuntimeError("no local passport found")


if __name__ == "__main__":
    import json

    print(json.dumps(search(), indent=2, sort_keys=True))
