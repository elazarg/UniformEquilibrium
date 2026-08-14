"""Exact finite screens for the minimum terminal-semantic counterexample face.

This module deliberately does not search random reward tables.  It supplies
two certificate replayers that are sound consequences of current production
theorems:

1. The prescribed coordinate of a point in the executable terminal-semantic
   carrier lies in the convex hull of Never's zero vector and the finitely
   many coalition reward vectors.  Membership is decided over ``Fraction``
   by enumerating affinely independent supports of size at most ``n + 1``
   (Caratheodory).  An explicit separating functional can also certify
   nonmembership independently of the enumeration.

2. Once a caller supplies the prerequisites of PR #56's compatible exact-two
   packet alternative, every singleton-tight inactive outsider is classified
   by the exact lexicographic jet

       L_w = m1*(r_w({w,1})-r_w({w}))
           + m2*(r_w({w,2})-r_w({w})),
       Q_w = m1*m2*(r_w({w,1,2})-r_w({w,1})
                    -r_w({w,2})+r_w({w})).

   ``L < 0`` or ``L == 0 and Q <= 0`` is harmless.  A local survivor must
   have ``L > 0`` or ``L == 0 and Q > 0`` for at least one such outsider.
   This function does NOT infer packet compatibility, the punishment floor,
   or box viability; those prerequisites are explicit arguments.

The built-in regression shows why the first screen matters.  For the
four-player table whose singleton coalition ``{i}`` pays the basis vector
``e_i`` and whose other coalitions pay zero, the abstract all-Continue pair
with prescribed vector ``(1,1,1,1)`` satisfies the bare local plateau
equations, but cannot lie in the semantic carrier: the sum functional is 4
at the candidate and at most 1 on every terminal reward atom.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr
from itertools import combinations
import json
from typing import Dict, FrozenSet, Iterable, Optional, Sequence, Tuple


Coalition = FrozenSet[int]
Vector = Tuple[Fr, ...]
Reward = Dict[Coalition, Vector]


def _dot(left: Sequence[Fr], right: Sequence[Fr]) -> Fr:
    return sum((x * y for x, y in zip(left, right)), Fr(0))


def _all_nonempty_coalitions(n: int) -> Iterable[Coalition]:
    for size in range(1, n + 1):
        for coalition in combinations(range(n), size):
            yield frozenset(coalition)


def _rref_unique(
    columns: Sequence[Sequence[Fr]], target: Sequence[Fr]
) -> Optional[Tuple[Fr, ...]]:
    """Solve ``columns * weights = target`` when the columns are independent.

    ``None`` means inconsistent or non-unique.  A minimal convex
    representation can always be chosen affinely independent, so only unique
    systems are required by ``moment_membership``.
    """

    column_count = len(columns)
    row_count = len(target)
    matrix = [
        [columns[col][row] for col in range(column_count)] + [target[row]]
        for row in range(row_count)
    ]
    pivot_row = 0
    pivots: list[int] = []
    for col in range(column_count):
        pivot = next(
            (row for row in range(pivot_row, row_count) if matrix[row][col]),
            None,
        )
        if pivot is None:
            continue
        matrix[pivot_row], matrix[pivot] = matrix[pivot], matrix[pivot_row]
        value = matrix[pivot_row][col]
        matrix[pivot_row] = [entry / value for entry in matrix[pivot_row]]
        for row in range(row_count):
            if row == pivot_row or matrix[row][col] == 0:
                continue
            factor = matrix[row][col]
            matrix[row] = [
                matrix[row][k] - factor * matrix[pivot_row][k]
                for k in range(column_count + 1)
            ]
        pivots.append(col)
        pivot_row += 1
        if pivot_row == row_count:
            break
    for row in range(pivot_row, row_count):
        if all(matrix[row][col] == 0 for col in range(column_count)) and matrix[row][-1] != 0:
            return None
    if len(pivots) != column_count:
        return None
    solution = [Fr(0)] * column_count
    for row, col in enumerate(pivots):
        solution[col] = matrix[row][-1]
    return tuple(solution)


@dataclass(frozen=True)
class MomentCertificate:
    feasible: bool
    atoms_checked: int
    support: Tuple[Optional[Coalition], ...] = ()
    weights: Tuple[Fr, ...] = ()


def moment_membership(reward: Reward, prescribed: Vector) -> MomentCertificate:
    """Decide membership in ``conv({0} union {reward(S)})`` exactly.

    ``None`` denotes Never's zero atom in a returned support.  Exhaustion is
    complete by Caratheodory's theorem in payoff dimension ``n``.
    """

    n = len(prescribed)
    atoms: list[Tuple[Optional[Coalition], Vector]] = [
        (None, tuple(Fr(0) for _ in range(n)))
    ]
    atoms.extend((coalition, reward[coalition]) for coalition in _all_nonempty_coalitions(n))
    checked = 0
    augmented_target = tuple(prescribed) + (Fr(1),)
    for size in range(1, min(n + 1, len(atoms)) + 1):
        for selected in combinations(atoms, size):
            checked += 1
            columns = [vector + (Fr(1),) for _name, vector in selected]
            weights = _rref_unique(columns, augmented_target)
            if weights is None or any(weight < 0 for weight in weights):
                continue
            return MomentCertificate(
                True,
                checked,
                tuple(name for name, _vector in selected),
                weights,
            )
    return MomentCertificate(False, checked)


def verify_moment_separator(
    reward: Reward, prescribed: Vector, functional: Vector
) -> dict[str, object]:
    """Replay the strict separating certificate ``a.v > max(0, a.r(S))``."""

    candidate = _dot(functional, prescribed)
    atom_values = {
        "{" + ",".join(str(player) for player in sorted(coalition)) + "}":
            _dot(functional, vector)
        for coalition, vector in reward.items()
    }
    ceiling = max([Fr(0), *atom_values.values()])
    return {
        "valid": candidate > ceiling,
        "candidate_value": candidate,
        "atom_ceiling": ceiling,
        "atom_values": atom_values,
    }


@dataclass(frozen=True)
class OutsiderJet:
    outsider: int
    linear: Fr
    quadratic: Fr

    @property
    def positive_lexicographic(self) -> bool:
        return self.linear > 0 or (self.linear == 0 and self.quadratic > 0)

    @property
    def harmless(self) -> bool:
        return self.linear < 0 or (self.linear == 0 and self.quadratic <= 0)


def two_owner_outsider_jet(
    reward: Reward,
    owners: Tuple[int, int],
    masses: Tuple[Fr, Fr],
    outsider: int,
) -> OutsiderJet:
    """Evaluate PR #56's exact outsider jet for one supplied packet face."""

    first, second = owners
    m_first, m_second = masses
    if first == second or outsider in owners:
        raise ValueError("owners must be distinct and outsider inactive")
    if m_first <= 0 or m_second <= 0 or m_first + m_second != 1:
        raise ValueError("exact-two masses must be positive and normalized")

    def r(coalition: set[int]) -> Fr:
        return reward[frozenset(coalition)][outsider]

    solo = r({outsider})
    with_first = r({outsider, first})
    with_second = r({outsider, second})
    with_both = r({outsider, first, second})
    linear = m_first * (with_first - solo) + m_second * (with_second - solo)
    quadratic = m_first * m_second * (
        with_both - with_first - with_second + solo
    )
    return OutsiderJet(outsider, linear, quadratic)


def compatible_two_owner_jet_screen(
    reward: Reward,
    owners: Tuple[int, int],
    masses: Tuple[Fr, Fr],
    singleton_tight_inactive: Sequence[int],
    *,
    compatible_exact_two_packet: bool,
) -> dict[str, object]:
    """Replay the PR #56 local alternative without inventing prerequisites."""

    if not compatible_exact_two_packet:
        return {
            "applicable": False,
            "reason": "compatible exact-two packet certificate not supplied",
        }
    jets = [
        two_owner_outsider_jet(reward, owners, masses, outsider)
        for outsider in singleton_tight_inactive
    ]
    escapes = [jet for jet in jets if jet.positive_lexicographic]
    return {
        "applicable": True,
        "jets": [
            {
                "outsider": jet.outsider,
                "L": jet.linear,
                "Q": jet.quadratic,
                "classification": (
                    "positive_lexicographic_escape"
                    if jet.positive_lexicographic
                    else "harmless_local_gate"
                ),
            }
            for jet in jets
        ],
        "survives_local_gate": bool(escapes),
        "escape_outsiders": [jet.outsider for jet in escapes],
        "warning": "No punishment-floor or reward-box viability is inferred.",
    }


def _basis_singleton_table(n: int) -> Reward:
    reward: Reward = {}
    for coalition in _all_nonempty_coalitions(n):
        if len(coalition) == 1:
            owner = next(iter(coalition))
            reward[coalition] = tuple(Fr(int(player == owner)) for player in range(n))
        else:
            reward[coalition] = tuple(Fr(0) for _ in range(n))
    return reward


def _jet_regression_table() -> Reward:
    """A complete zero table modified only on outsider-jet coordinates."""

    n = 4
    reward: Reward = {
        coalition: tuple(Fr(0) for _ in range(n))
        for coalition in _all_nonempty_coalitions(n)
    }

    def replace(coalition: set[int], who: int, value: Fr) -> None:
        key = frozenset(coalition)
        vector = list(reward[key])
        vector[who] = value
        reward[key] = tuple(vector)

    # Outsider 2: L = 0 and Q = 1/4, the exact positive quadratic escape.
    replace({2}, 2, Fr(0))
    replace({0, 2}, 2, Fr(0))
    replace({1, 2}, 2, Fr(0))
    replace({0, 1, 2}, 2, Fr(1))
    # Outsider 3: L = -1, a harmless first-order gate.
    replace({3}, 3, Fr(0))
    replace({0, 3}, 3, Fr(-1))
    replace({1, 3}, 3, Fr(-1))
    replace({0, 1, 3}, 3, Fr(0))
    return reward


def run_regressions() -> dict[str, object]:
    basis = _basis_singleton_table(4)
    false_plateau = tuple(Fr(1) for _ in range(4))
    rejected = moment_membership(basis, false_plateau)
    separator = verify_moment_separator(
        basis, false_plateau, tuple(Fr(1) for _ in range(4))
    )
    accepted = moment_membership(
        basis, tuple(Fr(1, 4) for _ in range(4))
    )
    jet = compatible_two_owner_jet_screen(
        _jet_regression_table(),
        (0, 1),
        (Fr(1, 2), Fr(1, 2)),
        (2, 3),
        compatible_exact_two_packet=True,
    )

    assert not rejected.feasible
    assert separator["valid"]
    assert accepted.feasible
    assert accepted.weights == (Fr(1, 4),) * 4
    assert jet["survives_local_gate"]
    assert jet["escape_outsiders"] == [2]
    return {
        "status": "passed",
        "abstract_plateau_moment_rejection": {
            "feasible": rejected.feasible,
            "supports_checked": rejected.atoms_checked,
            "separator": separator,
        },
        "moment_positive_control": {
            "support": accepted.support,
            "weights": accepted.weights,
        },
        "pr56_jet_replay": jet,
        "conclusion": (
            "Bare all-Continue plateau equations admit false positives.  "
            "The terminal reward-moment polytope is a sound exact carrier "
            "screen, and the PR #56 lexicographic jet is a separate local "
            "screen once its packet prerequisites are supplied."
        ),
    }


def _json_default(value: object) -> object:
    if isinstance(value, Fr):
        return str(value)
    if isinstance(value, frozenset):
        return sorted(value)
    if value is None:
        return "Never"
    raise TypeError(type(value).__name__)


if __name__ == "__main__":
    print(json.dumps(run_regressions(), indent=2, sort_keys=True, default=_json_default))
