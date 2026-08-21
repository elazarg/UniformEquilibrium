"""Quitting weights: coalitional payoff tables over n players.

A quitting weight assigns a payoff vector to every nonempty coalition of
players (the set of players who quit simultaneously at that stage).  This
module fixes the exact-rational representation used throughout
`Experiments/certsearch/`, the affine gauge used to normalize a weight, the
per-coordinate invariant matrix `B`, and five named reference weights embedded
in the tracked data.

Only the Python standard library is used (`fractions.Fraction` for exact
rational arithmetic); no `numpy`, no `sympy`.  See P13 in
`Experiments/PROPOSALS.md` ("certificate-guided weight search") for the
research context, and `Experiments/certsearch/README.md` for what this slice
covers and what slice two adds.

## Representation

Players are the integers `0, ..., n-1`.  A weight is

    dict[frozenset[int], tuple[Fraction, ...]]

mapping every nonempty coalition `J subseteq {0,...,n-1}` to its payoff
vector `r(J)`, a length-`n` tuple with `r(J)[i] = r_i(J)`, the payoff to
player `i` when exactly the players in `J` quit simultaneously.  `check_weight`
asserts every nonempty coalition of the implied player set is present with a
vector of the right length -- a mistranscribed or partial table is a
programming error here, not a silent gap.

## The gauge

Coordinatewise translation and positive scaling of a weight

    r'_i(J) = (r_i(J) - c_i) / s_i,   s_i > 0

preserves every exactly-complementary sequence coordinatewise. The gauge
fixed here, `gauge_normalize`, uses this freedom to pin every coordinate's
solo value `d_i = r_i({i})` into `{-1, 0, +1}`:

    r'_i(J) = r_i(J) / |d_i|   if d_i != 0     (c_i = 0, s_i = |d_i|)
    r'_i(J) = r_i(J)           if d_i == 0     (c_i = 0, s_i = 1, identity)

Translation is fixed at `c_i = 0` throughout and never exercised: the sign of
`d_i` already matches the sign of its target `sign(d_i)`, so only the
magnitude needs fixing, by scaling alone. (The zero-solo case has nothing to
scale by, since `d_i = 0` is already its own canonical representative.)
`gauge_normalize` is provided for the orbit-profiler slice (P13 slice two);
none of the filters in `filters.py` require it, because the invariant matrix
`B` below is invariant up to positive per-row rescaling under any gauge
choice, and the decisions every filter in this file makes (a sign, a
feasibility, an exhaustion) do not change under positive rescaling of a row.

## The invariant matrix

    B[i][j] = r_i({j}) - r_i({i}),    B[i][i] = 0 by construction.

This is Question 154 section 1's `B_{ij} = r_i({j}) - d_i`, computed directly
from the raw (not gauge-normalized) table -- normalizing first is optional,
since `B' = B` up to a positive scale on row `i` (by `1/s_i`) under the gauge
above, which changes no sign and hence no filter decision.
"""

from __future__ import annotations

from fractions import Fraction as Fr
from itertools import combinations
from typing import Dict, FrozenSet, Iterable, List, Tuple

Weight = Dict[FrozenSet[int], Tuple[Fr, ...]]


def players(w: Weight) -> int:
    """Number of players `n`, read off any table entry's vector length."""
    return len(next(iter(w.values())))


def all_nonempty_coalitions(n: int) -> Iterable[FrozenSet[int]]:
    ids = range(n)
    for size in range(1, n + 1):
        for combo in combinations(ids, size):
            yield frozenset(combo)


def check_weight(w: Weight) -> None:
    """Sanity check: every nonempty coalition of the implied player set `n`
    is present, with a payoff vector of length exactly `n`."""
    if not w:
        raise ValueError("empty weight")
    n = players(w)
    for J, vec in w.items():
        if not J:
            raise ValueError("coalition must be nonempty")
        if len(vec) != n:
            raise ValueError(
                f"coalition {sorted(J)} has payoff vector of length {len(vec)}, "
                f"expected {n}"
            )
        if not J.issubset(range(n)):
            raise ValueError(
                f"coalition {sorted(J)} uses a player id outside range(0, {n})"
            )
    missing = set(all_nonempty_coalitions(n)) - set(w.keys())
    if missing:
        raise ValueError(f"missing coalitions: {sorted(sorted(J) for J in missing)}")


def r(w: Weight, J: Iterable[int], i: int) -> Fr:
    """`r_i(J)` for a nonempty coalition `J` given as any iterable of player
    ids (e.g. `{1}`, `(0, 2)`, `frozenset({0, 1})`)."""
    return w[frozenset(J)][i]


def solo(w: Weight, i: int) -> Fr:
    """`d_i = r_i({i})`, the solo-quit value."""
    return w[frozenset({i})][i]


def invariant_matrix(w: Weight) -> List[List[Fr]]:
    """`B[i][j] = r_i({j}) - r_i({i})`; `B[i][i] = 0` by construction.
    Question 154 section 1, eq. preceding (5)."""
    n = players(w)
    d = [solo(w, i) for i in range(n)]
    return [[r(w, {j}, i) - d[i] for j in range(n)] for i in range(n)]


def gauge_normalize(w: Weight) -> Weight:
    """The affine gauge documented at the top of this module: coordinatewise
    positive scaling by `|d_i|` (translation `c_i = 0`, unused), pinning
    every solo value into `{-1, 0, +1}`."""
    n = players(w)
    d = [solo(w, i) for i in range(n)]
    s = [abs(d[i]) if d[i] != 0 else Fr(1) for i in range(n)]
    out: Weight = {}
    for J, vec in w.items():
        out[J] = tuple(vec[i] / s[i] for i in range(n))
    return out


# --------------------------------------------------------------------------
# Five named reference weights.
# --------------------------------------------------------------------------

def _F(numerator: int, denominator: int = 1) -> Fr:
    return Fr(numerator, denominator)


#: `G_eps`, the `epsilon`-perturbed published cyclic table, `epsilon = 1/10`.
#: Reference data for Solan 2001's three-player family with the `epsilon`-bonus
#: on two-quitter entries).  Players `0, 1, 2` here are the document's
#: `1, 2, 3`.  Transcribed with the document's own entries (not rescaled by
#: 1/3 for the `||r||_inf <= 1` convention -- the document notes that
#: rescaling "changes nothing, by the same affine invariance", so this file
#: keeps the literal published numbers).
def g_eps_weight(eps: Fr = _F(1, 10)) -> Weight:
    one_plus_eps = 1 + eps
    w: Weight = {
        frozenset({0}): (_F(1), _F(3), _F(0)),
        frozenset({1}): (_F(0), _F(1), _F(3)),
        frozenset({2}): (_F(3), _F(0), _F(1)),
        frozenset({0, 1}): (one_plus_eps, _F(0), _F(1)),
        frozenset({1, 2}): (_F(1), one_plus_eps, _F(0)),
        frozenset({0, 2}): (_F(0), _F(1), one_plus_eps),
        frozenset({0, 1, 2}): (_F(0), _F(0), _F(0)),
    }
    check_weight(w)
    return w


G_EPS = g_eps_weight()


#: The Q154 reference weight. Players `0, 1, 2` are the reference table's
#: `1, 2, 3`.
#: This is the weight with `epsilon`-cycles at every tolerance, absorbed mass
#: always `7/8`, but *no* exact cycle of any period -- the question's answer.
Q154_WEIGHT: Weight = {
    frozenset({0}): (_F(-1, 2), _F(1, 2), _F(-1)),
    frozenset({1}): (_F(-1), _F(-1, 2), _F(1, 2)),
    frozenset({2}): (_F(1, 2), _F(-1), _F(-1, 2)),
    frozenset({0, 1}): (_F(-1, 4), _F(-1, 2), _F(1, 2)),
    frozenset({1, 2}): (_F(1, 2), _F(-1, 4), _F(-1, 2)),
    frozenset({0, 2}): (_F(-1, 2), _F(1, 2), _F(-1, 4)),
    frozenset({0, 1, 2}): (_F(-1, 2), _F(-1, 2), _F(-1, 2)),
}
check_weight(Q154_WEIGHT)


#: The two-player counterexample:
#: `UniformEquilibrium/Quitting/Boundary/Repair/DisjunctionCounterexample.lean`,
#: module docstring and `def reward`.  Player `0` is the file's `false`,
#: player `1` is the file's `true`.  `r({0}) = r({1}) = (1, -1)`,
#: `r({0,1}) = (0, 1)`.  Lies outside both branches of the zero-solo/cycle
#: disjunction (not zero-solo; its one absorbing complementary cycle is not
#: admissible).
TWO_PLAYER_COUNTEREXAMPLE: Weight = {
    frozenset({0}): (_F(1), _F(-1)),
    frozenset({1}): (_F(1), _F(-1)),
    frozenset({0, 1}): (_F(0), _F(1)),
}
check_weight(TWO_PLAYER_COUNTEREXAMPLE)


#: The unperturbed Flesch-Thuijsman-Vrieze table:
#: `UniformEquilibrium/Quitting/Examples/Cyclic/ThreePlayer/AdmissibleCycle.lean`, module
#: docstring.  Players `0, 1, 2` here are the file's `Player` values `0, 1,
#: 2` directly (no reindexing).  This is `G_EPS` at `epsilon = 0`: the period-
#: one no-join fence fails identically here (see validate.py), but the
#: admissible cycle is the *period-three* phase-rotation block at rate `1/2`,
#: not a period-one solo-quitter row.
FTV_WEIGHT: Weight = {
    frozenset({0}): (_F(1), _F(3), _F(0)),
    frozenset({1}): (_F(0), _F(1), _F(3)),
    frozenset({2}): (_F(3), _F(0), _F(1)),
    frozenset({0, 1}): (_F(1), _F(0), _F(1)),
    frozenset({0, 2}): (_F(0), _F(1), _F(1)),
    frozenset({1, 2}): (_F(1), _F(1), _F(0)),
    frozenset({0, 1, 2}): (_F(0), _F(0), _F(0)),
}
check_weight(FTV_WEIGHT)


#: The hostile table:
#: `UniformEquilibrium/Quitting/Punishment/IsolatedPunishmentCeiling.lean`,
#: `QuittingIsolatedPunishmentLowerBoundCounterexample.reward`.  Player `0`
#: is the file's `false`, player `1` is the file's `true`.  Literal Lean
#: source: `fun S i => if i = true then (if S = {true} then 0 else -1000)
#: else 0`.  So `r({0}) = (0, -1000)` (S = {false} != {true}), `r({1}) =
#: (0, 0)` (S = {true}), `r({0,1}) = (0, -1000)` (S = {false,true} !=
#: {true}); player `0`'s (false's) payoff is 0 in every coalition.
HOSTILE_WEIGHT: Weight = {
    frozenset({0}): (_F(0), _F(-1000)),
    frozenset({1}): (_F(0), _F(0)),
    frozenset({0, 1}): (_F(0), _F(-1000)),
}
check_weight(HOSTILE_WEIGHT)


NAMED_WEIGHTS = {
    "G_EPS (eps=1/10)": G_EPS,
    "Q154": Q154_WEIGHT,
    "TWO_PLAYER_COUNTEREXAMPLE": TWO_PLAYER_COUNTEREXAMPLE,
    "FTV": FTV_WEIGHT,
    "HOSTILE": HOSTILE_WEIGHT,
}
