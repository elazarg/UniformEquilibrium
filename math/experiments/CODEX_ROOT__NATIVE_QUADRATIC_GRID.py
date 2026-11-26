"""Exact four-owner calendar grid for the native quadratic regret coefficient."""

from fractions import Fraction
from itertools import product


def grid_minima(gamma, joining, weights, resolution, *, tolerance=None, endpoint=None):
    """Return least grid costs with and without the passive endpoint constraint.

    The return order is (free, constrained), with None for an empty set. Use
    integer or Fraction entries. The default tolerance gives the certified
    all-calendar approximation in the accompanying native quadratic grid note. A supplied endpoint restricts the
    search to those integer counts summing to resolution. With tolerance zero,
    any finite cost is a feasible upper bound for its respective coefficient.
    """
    if not isinstance(resolution, int) or resolution < 1:
        raise ValueError("resolution must be a positive integer")
    matrices = [gamma, joining]
    for matrix in matrices:
        if len(matrix) != 4 or any(len(row) != 4 for row in matrix):
            raise ValueError("expected two four-by-four matrices")
        if any(matrix[i][i] != 0 for i in range(4)):
            raise ValueError("native pair matrices have zero diagonal")
    if len(weights) != 4 or min(weights) <= 0:
        raise ValueError("expected four positive recipient weights")
    if endpoint is None:
        caps = (resolution,) * 4
    else:
        caps = tuple(endpoint)
        if (len(caps) != 4 or any(not isinstance(v, int) or v < 0 for v in caps)
                or sum(caps) != resolution):
            raise ValueError("endpoint counts must be nonnegative integers totaling resolution")

    if tolerance is None:
        bound = max(1, *(abs(value) for matrix in matrices for row in matrix for value in row))
        threshold = 1 + 16 * bound
    else:
        if tolerance < 0:
            raise ValueError("tolerance must be nonnegative")
        threshold = resolution * tolerance

    def states(prefix, remaining):
        if len(prefix) == 4:
            yield prefix
            return
        for value in range(min(remaining, caps[len(prefix)]) + 1):
            yield from states(prefix + (value,), remaining - value)

    cost = {(0, 0, 0, 0): 0}
    best_free = best_constrained = None
    for total in states((), resolution):
        if not any(total):
            continue
        passive = [sum(g * n for g, n in zip(row, total)) for row in gamma]
        best = None
        # The lexicographic enumeration processes every proper predecessor first.
        for old in product(*(range(count + 1) for count in total)):
            if old not in cost:
                continue
            step = tuple(n - p for n, p in zip(total, old))
            residual = [v - sum(j * k for j, k in zip(row, step))
                        for v, row in zip(passive, joining)]
            if min(residual) < -threshold:
                continue
            candidate = cost[old] + sum(w * k * g for w, k, g in zip(weights, step, residual))
            if best is None or candidate < best:
                best = candidate
        if best is None:
            continue
        cost[total] = best
        if sum(total) != resolution:
            continue
        if best_free is None or best < best_free:
            best_free = best
        if min(passive) >= -threshold and (best_constrained is None or best < best_constrained):
            best_constrained = best

    return tuple(None if value is None else Fraction(value) / resolution**2
                 for value in (best_free, best_constrained))


if __name__ == "__main__":
    # The asymmetric center in QUADRATIC_COST_AND_ALLNEVER_SOURCE_EXCLUSION.md.
    gamma = [[0, -2, 3, -1], [-1, 0, -1, 3], [3, -1, 0, -1], [-1, 3, -1, 0]]
    difference = [[0, 3, Fraction(5, 2), -2], [-Fraction(1, 5000), 0, 2, Fraction(1, 2)],
                  [2, -2, 0, 6], [3, 10, -Fraction(1, 2), 0]]
    joining = [[g - k for g, k in zip(row, diff)] for row, diff in zip(gamma, difference)]
    free, constrained = grid_minima(gamma, joining, [1] * 4, 256,
                                    tolerance=0, endpoint=(255, 0, 1, 0))
    # The published Gram bound gives kappa_plus >= 1/57 on every calendar.
    assert constrained is None and free == Fraction(2295, 131072) < Fraction(1, 57)
    print(f"kappa <= {free} < 1/57 <= kappa_plus")
