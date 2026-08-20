"""E10: exact exhaustive equilibrium-support census for 2x2 games.

Claude proposed a computational census of analytic atlas leaves.  Connecting
the full stochastic atlas to an executable classifier is not yet available.
This dry run tests the census methodology on every 2x2 bimatrix game with
payoffs in {-1,0,1}: exact enumeration, explicit degeneracy separation, stable
classification keys, and machine-checkable aggregate counts.
"""

from __future__ import annotations

import itertools
import json
from collections import Counter
from fractions import Fraction

from arc_orientation_scan import completely_mixed_equilibrium, pure_nash


def matrix(entries: tuple[int, ...]):
    return [
        [Fraction(entries[0]), Fraction(entries[1])],
        [Fraction(entries[2]), Fraction(entries[3])],
    ]


def is_nondegenerate_response_table(a, b) -> bool:
    # No player is indifferent between pure responses to a pure opponent action.
    return (
        a[0][0] != a[1][0]
        and a[0][1] != a[1][1]
        and b[0][0] != b[0][1]
        and b[1][0] != b[1][1]
    )


def run() -> dict:
    values = (-1, 0, 1)
    counts = Counter()
    nondegenerate_counts = Counter()
    orientation_counts = Counter()
    total = 0

    for entries in itertools.product(values, repeat=8):
        a = matrix(entries[:4])
        b = matrix(entries[4:])
        pure_count = len(pure_nash(a, b))
        mixed = completely_mixed_equilibrium(a, b)
        mixed_count = int(mixed is not None)
        counts[(pure_count, mixed_count)] += 1
        total += 1

        if is_nondegenerate_response_table(a, b):
            nondegenerate_counts[(pure_count, mixed_count)] += 1
            # In a nondegenerate 2x2 game, equilibria occur in the familiar
            # unique-pure, unique-mixed, or two-pure-plus-one-mixed patterns.
            assert (pure_count, mixed_count) in {(1, 0), (0, 1), (2, 1)}

        if mixed is not None:
            determinant = mixed["indifference_orientation_determinant"]
            orientation_counts["positive" if determinant > 0 else "negative"] += 1

    assert total == 3**8
    assert sum(counts.values()) == total
    assert sum(orientation_counts.values()) == sum(
        count for (pure_count, mixed_count), count in counts.items() if mixed_count
    )

    def encode(counter: Counter) -> dict:
        return {
            f"pure={pure},mixed={mixed}": count
            for (pure, mixed), count in sorted(counter.items())
        }

    return {
        "experiment": "E10",
        "status": "passed",
        "games_enumerated": total,
        "all_support_patterns": encode(counts),
        "nondegenerate_support_patterns": encode(nondegenerate_counts),
        "mixed_orientation_counts": dict(sorted(orientation_counts.items())),
        "conclusion": (
            "An exact census cleanly separates generic support patterns from a "
            "large degenerate boundary.  The same discipline should be retained "
            "when a machine-readable stochastic-atlas classifier becomes available."
        ),
        "limitation": (
            "This validates the census pipeline, not the atlas conjecture: these "
            "are one-shot 2x2 games and the orientation is the local indifference determinant."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
