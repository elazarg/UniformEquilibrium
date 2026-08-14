"""E23: can the landed owner-obstruction cokernel express E06's typed holonomy?

E06 (`owner_monodromy.py`) exhibits a two-edge cycle whose *aggregate* charge
is a coboundary -- zero scalar holonomy -- while its *owner-typed* holonomy is
`(1, -1)`.  `Math/LinearAlgebra/OwnerObstructionCokernel.lean` defines, for a
finite owner-labeled system, the cokernel

    Obstruction sys i = (T -> R) / ownerNormals sys i,

where `mem_ownerNormals_iff` (line 821) says `alpha` is certifiable by owner
`i` exactly when

    alpha w = sum_e eta_e R_e w + sum_n nu_n Q_n w + sum_u mu_u S_u w
              + (H (src w) - sum_v trans w v * H v)

for multipliers whose internal `Y`-block cancels and whose unilateral
multipliers `mu` are supported on owner `i`'s rows.  This script instantiates
that definition on E06's cycle and asks whether some owner's class is nonzero.

The flow structure is the file's own `TwoCycleObstruction.system`
(OwnerObstructionCokernel.lean:1265): `src = id`, `trans b v = [v = !b]`, two
edges owned by the two different owners, and the empty typed cell.
"""

from __future__ import annotations

import itertools
import json
from fractions import Fraction
from typing import Sequence

Vector = tuple[Fraction, ...]


# --------------------------------------------------------------------------
# exact linear algebra
# --------------------------------------------------------------------------


def echelon(rows: Sequence[Sequence[Fraction]]) -> list[Vector]:
    work = [list(row) for row in rows]
    if not work:
        return []
    width = len(work[0])
    pivot_row = 0
    for column in range(width):
        pivot = next(
            (r for r in range(pivot_row, len(work)) if work[r][column] != 0), None
        )
        if pivot is None:
            continue
        work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
        scale = work[pivot_row][column]
        work[pivot_row] = [entry / scale for entry in work[pivot_row]]
        for r in range(len(work)):
            if r == pivot_row or work[r][column] == 0:
                continue
            factor = work[r][column]
            work[r] = [a - factor * b for a, b in zip(work[r], work[pivot_row])]
        pivot_row += 1
        if pivot_row == len(work):
            break
    return [tuple(row) for row in work[:pivot_row] if any(e != 0 for e in row)]


def rank(rows: Sequence[Sequence[Fraction]]) -> int:
    return len(echelon(rows))


def in_span(basis: Sequence[Vector], vector: Sequence[Fraction]) -> bool:
    return rank([list(b) for b in basis] + [list(vector)]) == rank(
        [list(b) for b in basis]
    )


def kernel(rows: Sequence[Sequence[Fraction]], width: int) -> list[Vector]:
    reduced = echelon(rows)
    pivots = [next(j for j in range(width) if row[j] != 0) for row in reduced]
    free = [j for j in range(width) if j not in pivots]
    basis: list[Vector] = []
    for f in free:
        solution = [Fraction(0)] * width
        solution[f] = Fraction(1)
        for row, pivot in zip(reversed(reduced), reversed(pivots)):
            solution[pivot] = -sum(
                (row[j] * solution[j] for j in range(width) if j != pivot),
                Fraction(0),
            )
        basis.append(tuple(solution))
    return basis


# --------------------------------------------------------------------------
# the owner-labeled system
# --------------------------------------------------------------------------


class OwnerSystem:
    """`OwnerObstructionCokernel.OwnerSystem` with all blocks given explicitly.

    Index conventions follow the Lean structure: `A`/`R` are the structural
    rows, `C`/`Q` the owner-neutral rows, `B`/`S` the owner-tagged unilateral
    rows, `Y` the internal columns and `T` the boundary columns.
    """

    def __init__(
        self,
        owners: Sequence[str],
        internal: int,
        targets: int,
        vertices: int,
        src: Sequence[int],
        trans: Sequence[Sequence[Fraction]],
        structural: Sequence[tuple[Vector, Vector]] = (),
        neutral: Sequence[tuple[Vector, Vector]] = (),
        unilateral: Sequence[tuple[str, Vector, Vector]] = (),
    ) -> None:
        self.owners = list(owners)
        self.internal = internal
        self.targets = targets
        self.vertices = vertices
        self.src = list(src)
        self.trans = [tuple(row) for row in trans]
        self.structural = list(structural)
        self.neutral = list(neutral)
        self.unilateral = list(unilateral)

    def coboundary(self, potential: Sequence[Fraction]) -> Vector:
        """`H (src w) - sum_v trans w v * H v`, the account drift block."""
        return tuple(
            potential[self.src[w]]
            - sum(
                (self.trans[w][v] * potential[v] for v in range(self.vertices)),
                Fraction(0),
            )
            for w in range(self.targets)
        )

    def coboundary_space(self) -> list[Vector]:
        generators = []
        for v in range(self.vertices):
            potential = [Fraction(int(u == v)) for u in range(self.vertices)]
            generators.append(list(self.coboundary(potential)))
        return echelon(generators)

    def owner_normals(self, owner: str | None) -> list[Vector]:
        """`ownerNormals sys i` (or `globalNormals` when `owner is None`):
        signed multiplier combinations whose internal block cancels, plus an
        account coboundary."""
        rows: list[tuple[Vector, Vector]] = list(self.structural) + list(self.neutral)
        for who, internal_row, boundary_row in self.unilateral:
            if owner is None or who == owner:
                rows.append((internal_row, boundary_row))
        width = len(rows)
        if width == 0:
            multiplier_space: list[Vector] = []
        else:
            constraints = [
                [rows[k][0][y] for k in range(width)] for y in range(self.internal)
            ]
            multiplier_space = (
                kernel(constraints, width)
                if constraints
                else [
                    tuple(Fraction(int(i == k)) for i in range(width))
                    for k in range(width)
                ]
            )
        generators = [list(v) for v in self.coboundary_space()]
        for combination in multiplier_space:
            generators.append(
                [
                    sum(
                        (combination[k] * rows[k][1][w] for k in range(width)),
                        Fraction(0),
                    )
                    for w in range(self.targets)
                ]
            )
        return echelon(generators)

    def obstruction_dimension(self, owner: str | None) -> int:
        return self.targets - len(self.owner_normals(owner))

    def class_is_zero(self, owner: str | None, alpha: Sequence[Fraction]) -> bool:
        return in_span(self.owner_normals(owner), alpha)

    def incidence(self, x: Sequence[Fraction]) -> Vector:
        """`OwnerLabeledFlowHolonomy.incidence`: net flow at each vertex."""
        return tuple(
            sum(
                (
                    x[w] * (Fraction(int(self.src[w] == v)) - self.trans[w][v])
                    for w in range(self.targets)
                ),
                Fraction(0),
            )
            for v in range(self.vertices)
        )


def holonomy(alpha: Sequence[Fraction], x: Sequence[Fraction]) -> Fraction:
    return sum((a * b for a, b in zip(alpha, x)), Fraction(0))


# --------------------------------------------------------------------------
# E06's cycle
# --------------------------------------------------------------------------

OWNERS = ["Alice", "Bob"]
# E06's `mixed_cycle`: x -> y owned by Alice with charge 1, y -> x owned by Bob
# with charge -1.  Vertices 0 = x, 1 = y; edge b leaves vertex b.
EDGE_OWNER = ["Alice", "Bob"]
MIXED_CHARGE = (Fraction(1), Fraction(-1))
# E06's `pure_canceling_cycle`: both legs owned by Alice.
PURE_EDGE_OWNER = ["Alice", "Alice"]
PURE_CHARGE = (Fraction(3), Fraction(-3))


def two_cycle(unilateral: Sequence[tuple[str, Vector, Vector]] = ()) -> OwnerSystem:
    """`TwoCycleObstruction.system`: `src = id`, `trans b v = [v = !b]`."""
    return OwnerSystem(
        owners=OWNERS,
        internal=0,
        targets=2,
        vertices=2,
        src=[0, 1],
        trans=[
            (Fraction(0), Fraction(1)),
            (Fraction(1), Fraction(0)),
        ],
        unilateral=unilateral,
    )


def typed_charge(
    charge: Sequence[Fraction], edge_owner: Sequence[str], owner: str
) -> Vector:
    """E06's owner-typed decomposition of a charge cochain: keep the legs of
    one owner and zero the rest.  `sum(typed_charge(.., i)) ` is exactly E06's
    `typed_cycle_sum` coordinate for owner `i`."""
    return tuple(
        value if who == owner else Fraction(0)
        for value, who in zip(charge, edge_owner)
    )


def cycle_sum(alpha: Sequence[Fraction]) -> Fraction:
    return sum(alpha, Fraction(0))


def run() -> dict:
    system = two_cycle()
    coboundaries = system.owner_normals("Alice")

    # (0) sanity against the Lean file: the certifiable subspace is the
    # coboundary line, the cokernel is one dimensional, and it does not depend
    # on the owner because the typed blocks are empty.
    assert coboundaries == system.owner_normals("Bob")
    assert coboundaries == system.owner_normals(None)
    assert len(coboundaries) == 1
    assert system.obstruction_dimension("Alice") == 1
    # `TwoCycleObstruction.obstructionClass_coboundary_eq_zero`
    assert system.class_is_zero("Alice", (Fraction(1), Fraction(-1)))
    # `TwoCycleObstruction.obstructionClass_ne_zero` (0 < a1 + a2)
    for a1, a2 in itertools.product(range(-2, 3), repeat=2):
        alpha = (Fraction(a1), Fraction(a2))
        assert system.class_is_zero("Alice", alpha) == (a1 + a2 == 0)
    # the uniform occupation is the separating obstruction test of the file
    uniform = (Fraction(1, 2), Fraction(1, 2))
    assert system.incidence(uniform) == (Fraction(0), Fraction(0))

    # (1) THE DIRECT MAPPING FAILS.  E06's aggregate charge is a coboundary, so
    # its class vanishes for every owner: the cokernel, applied to the charge
    # cochain E06 actually forms, cannot see the typed phenomenon.
    aggregate_classes = {
        owner: system.class_is_zero(owner, MIXED_CHARGE) for owner in OWNERS
    }
    assert all(aggregate_classes.values())

    # (2) Nor does moving the owner labels into the unilateral rows help.  Give
    # each owner a unilateral row that explains its own leg; the other owner is
    # still left with exactly the coboundaries, and the aggregate charge is one.
    with_rows = two_cycle(
        unilateral=[
            (
                EDGE_OWNER[w],
                tuple(),
                tuple(Fraction(int(t == w)) for t in range(2)),
            )
            for w in range(2)
        ]
    )
    row_classes = {owner: with_rows.class_is_zero(owner, MIXED_CHARGE) for owner in OWNERS}
    assert all(row_classes.values())
    assert with_rows.obstruction_dimension("Alice") == 0

    # (3) THE RE-ENCODING THAT WORKS.  Take the class of each owner's *restricted*
    # charge cochain.  On this system the cokernel is one dimensional and the
    # class map is exactly the cycle sum, so the tuple of owner classes IS E06's
    # typed holonomy vector.
    typed = {
        owner: typed_charge(MIXED_CHARGE, EDGE_OWNER, owner) for owner in OWNERS
    }
    typed_classes_zero = {
        owner: system.class_is_zero(owner, typed[owner]) for owner in OWNERS
    }
    assert typed_classes_zero == {"Alice": False, "Bob": False}
    typed_holonomy = tuple(cycle_sum(typed[owner]) for owner in OWNERS)
    assert typed_holonomy == (Fraction(1), Fraction(-1))  # E06's `typed`
    # the same numbers read off the separating obstruction test, up to the
    # normalization of the uniform circulation
    assert tuple(
        2 * holonomy(typed[owner], uniform) for owner in OWNERS
    ) == typed_holonomy
    # and the aggregate is the sum of the owner classes, which cancels
    assert cycle_sum(MIXED_CHARGE) == sum(typed_holonomy, Fraction(0)) == 0

    # (4) E06's custody-pure control: both legs owned by Alice.  Every owner's
    # restricted class vanishes, matching E06's `pure_typed == (0, 0)`.
    pure_typed = {
        owner: typed_charge(PURE_CHARGE, PURE_EDGE_OWNER, owner) for owner in OWNERS
    }
    assert all(system.class_is_zero(owner, pure_typed[owner]) for owner in OWNERS)
    assert tuple(cycle_sum(pure_typed[owner]) for owner in OWNERS) == (
        Fraction(0),
        Fraction(0),
    )

    return {
        "experiment": "E23",
        "status": "passed",
        "system": "TwoCycleObstruction.system (empty typed cell, two-cycle flow)",
        "certifiable_subspace_dimension": len(coboundaries),
        "obstruction_dimension": system.obstruction_dimension("Alice"),
        "owner_normals_depend_on_owner": False,
        "aggregate_charge": [str(x) for x in MIXED_CHARGE],
        "aggregate_class_is_zero_for_every_owner": aggregate_classes,
        "unilateral_row_encoding_class_is_zero": row_classes,
        "owner_restricted_charges": {
            owner: [str(x) for x in typed[owner]] for owner in OWNERS
        },
        "owner_restricted_class_is_zero": typed_classes_zero,
        "recovered_typed_holonomy": [str(x) for x in typed_holonomy],
        "e06_typed_holonomy": ["1", "-1"],
        "conclusion": (
            "The landed owner-obstruction cokernel expresses E06's typed "
            "holonomy only after a re-encoding.  Applied to the charge cochain "
            "E06 actually forms -- the aggregate charge (1, -1) -- every "
            "owner's class is ZERO, because the cochain is an account "
            "coboundary and the owner label enters `ownerNormals` only through "
            "the unilateral rows, which are empty on this flow; adding "
            "unilateral rows for the legs only enlarges the certifiable "
            "subspace and keeps every class zero.  If instead one takes the "
            "class of each owner's RESTRICTED charge cochain, the resulting "
            "tuple of classes is exactly E06's typed holonomy (1, -1), and it "
            "is separated by the file's own uniform-circulation obstruction "
            "test.  So the phenomenon is expressible, but only by an "
            "owner-indexed family of classes that the current definition does "
            "not form."
        ),
        "limitation": (
            "The cokernel is a real vector space, so it records the rational "
            "typed holonomy and not E06's finite-cover monodromy order; and on "
            "a graph with several independent cycles the cokernel quotients by "
            "all coboundaries at once, which is coarser than E06's per-cycle "
            "sums."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True, default=str))
