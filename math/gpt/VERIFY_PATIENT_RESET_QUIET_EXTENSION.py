#!/usr/bin/env python3
"""Exact regression checks for FUTURE_WITHDRAWAL_AND_PATIENT_RESET_QUIET_EXTENSION.md.

Standard library only. No numerical solver, random sampling, Lean compilation,
or conjecture-wide search is performed. The proof of the general theorem is
in the companion note. All arithmetic below uses fractions.Fraction.
"""
from fractions import Fraction as F
from itertools import product

# A coalition is its bit mask. Never has no terminal reward entry.
R = {
    1: (1, 3, -1, -1),
    2: (4, 0, -1, -1),
    3: (2, 4, -1, -3),
    4: (0, -1, 0, 3),
    5: (2, -1, -2, -4),
    6: (0, -2, 1, 5),
    7: (-3, 0, 0, 0),
    8: (0, -1, 3, 0),
    9: (2, -1, -1, -6),
    10: (0, 1, -1, 3),
    11: (1, 0, 1, -4),
    12: (0, -1, 1, 1),
    13: (1, -1, 0, -6),
    14: (0, 0, 0, 3),
    15: (1, 0, -1, F(1, 2)),
}
R = {A: tuple(map(F, row)) for A, row in R.items()}
S = 7
OUT = 3
SINGLETON = tuple(R[1 << i][i] for i in range(4))
LAMBDA = (F(0), F(0), F(3))
MU = (F(1, 2), F(0), F(0))


def subsets(mask: int) -> list[int]:
    return [A for A in range(1, 16) if A & mask == A]


def lower_escape(i: int, child: int) -> F:
    return min([max(F(0), SINGLETON[i])] + [R[A][i] for A in subsets(child & ~(1 << i))])


def leave_lower(i: int, A: int, child: int) -> F:
    if not A & (1 << i):
        return F(0)
    after = A & ~(1 << i)
    return (R[after][i] if after else lower_escape(i, child)) - R[A][i]


def checked_slacks() -> tuple[list[F], list[F]]:
    future, join = [], []
    for A in subsets(S):
        bonus = sum(MU[i] * leave_lower(i, A, S) for i in range(3))
        future.append(sum(LAMBDA[i] * (SINGLETON[i] - R[A][i])
                          for i in range(3)) + bonus
                      - (SINGLETON[OUT] - R[A][OUT]))
        join.append(sum(LAMBDA[i] * (R[A | (1 << i)][i] - R[A][i])
                        for i in range(3)) + bonus
                    - (R[A | (1 << OUT)][OUT] - R[A][OUT]))
    assert SINGLETON == (1, 0, 0, 0)
    assert (sum(LAMBDA[i] * SINGLETON[i] + MU[i] * max(SINGLETON[i], 0)
                for i in range(3)) - SINGLETON[OUT]) == F(1, 2)
    assert future == list(map(F, [F(3, 2), 2, 1, 3, 1, 2, F(3, 2)]))
    assert join == list(map(F, [F(3, 2), 2, 5, 2, 1, 2, 1]))
    assert min(future + join) == 1
    return future, join


# Every old proper-child test fails already on ONE join row.
# child -> (outside player, tested first coalition)
OLD_REJECTION = {
    1: (1, 1), 2: (2, 2), 3: (2, 3), 4: (0, 4),
    5: (1, 5), 6: (0, 4), 7: (3, 7), 8: (0, 8),
    9: (1, 9), 10: (0, 10), 11: (2, 3), 12: (0, 12),
    13: (1, 13), 14: (0, 14),
}


def reject_old_tests() -> None:
    for child, (k, A) in OLD_REJECTION.items():
        ids = [i for i in range(4) if child & (1 << i)]
        assert A & child == A and not child & (1 << k)
        coefficients = [R[A | (1 << i)][i] - R[A][i] for i in ids]
        bound = R[A | (1 << k)][k] - R[A][k]
        assert all(x <= 0 for x in coefficients) and bound >= F(1, 2)
        # A zero coefficient is structural: the player already belongs to A.
        assert all(x < 0 or A & (1 << i) for i, x in zip(ids, coefficients))


NEVER = 4  # Four distinct finite dates suffice for the four-clock order types.


def realized(clocks: dict[int, int], recipient: int, cutoff: int = 4) -> F:
    first = min(clocks.values())
    if first == NEVER or first >= cutoff:
        return F(0)
    A = sum(1 << i for i, t in clocks.items() if t == first)
    return R[A][recipient]


def order_type_checks() -> int:
    checked = 0
    for t0, t1, t2, z in product(range(5), repeat=4):
        clocks = {0: t0, 1: t1, 2: t2}
        accelerated = dict(clocks)
        accelerated[2] = min(t2, z)
        cancelled = dict(clocks)
        cancelled[0] = t0 if t0 < z else NEVER
        parent_quiet = dict(clocks)
        parent_quiet[3] = NEVER
        parent_reply = dict(clocks)
        parent_reply[3] = z
        if t0 < z or z == NEVER:
            patient_payoff = realized(clocks, 0)
        else:
            first_opponent = min(t1, t2)
            if first_opponent == NEVER:
                patient_payoff = max(F(0), SINGLETON[0])
            else:
                coalition = sum(1 << i for i in (1, 2)
                                if clocks[i] == first_opponent)
                patient_payoff = R[coalition][0]
        patient_gain = patient_payoff - realized(clocks, 0)
        outside_terminal = realized(parent_reply, 3) - realized(parent_quiet, 3)
        early_terminal = realized(accelerated, 2) - realized(clocks, 2)
        assert outside_terminal <= 3 * early_terminal + F(1, 2) * patient_gain
        # Nonincreasing weights on the ordered finite dates are nonnegative
        # combinations of these prefix-indicator weights (plus a zero weight).
        for cutoff in range(5):
            outside = realized(parent_reply, 3, cutoff) - realized(parent_quiet, 3, cutoff)
            early = realized(accelerated, 2, cutoff) - realized(clocks, 2, cutoff)
            cancel = realized(cancelled, 0, cutoff) - realized(clocks, 0, cutoff)
            assert outside <= 3 * early + F(1, 2) * cancel
            checked += 1
    return checked


def expected(laws: list[dict[int, F]], recipient: int) -> F:
    result = F(0)
    for times in product(*(tuple(law) for law in laws)):
        weight = F(1)
        for law, t in zip(laws, times):
            weight *= law[t]
        result += weight * realized(dict(enumerate(times)), recipient)
    return result


def finite_equilibrium_check() -> tuple[tuple[F, ...], tuple[F, ...]]:
    hazards = (F(1, 2), F(2, 5), F(1), F(0))
    laws = [{0: q, NEVER: 1 - q} for q in hazards]
    U = tuple(expected(laws, i) for i in range(4))
    caps = []
    for i in range(4):
        values = []
        for deadline in (0, 1, NEVER):
            changed = list(laws)
            changed[i] = {deadline: F(1)}
            values.append(expected(changed, i))
        caps.append(max(values))
    assert U == (F(0), F(-1), F(-2, 5), F(7, 10))
    assert U == tuple(caps)
    return U, tuple(caps)


def determinant(a: list[list[F]]) -> F:
    a = [row[:] for row in a]
    ans = F(1)
    for j in range(len(a)):
        pivots = [i for i in range(j, len(a)) if a[i][j]]
        if not pivots:
            return F(0)
        p = pivots[0]
        if p != j:
            a[p], a[j] = a[j], a[p]
            ans = -ans
        pivot = a[j][j]
        ans *= pivot
        for i in range(j + 1, len(a)):
            scale = a[i][j] / pivot
            for k in range(j + 1, len(a)):
                a[i][k] -= scale * a[j][k]
            a[i][j] = 0
    return ans


def stationary_residual(q: tuple[F, ...], i: int) -> F:
    others = [j for j in range(4) if j != i]
    alpha = F(1)
    for j in others:
        alpha *= 1 - q[j]
    quit_value = F(0)
    continue_contribution = F(0)
    for bits in product((0, 1), repeat=3):
        probability = F(1)
        A = 0
        for j, bit in zip(others, bits):
            probability *= q[j] if bit else 1 - q[j]
            if bit:
                A |= 1 << j
        quit_value += probability * R[A | (1 << i)][i]
        if A:
            continue_contribution += probability * R[A][i]
    return (1 - alpha) * quit_value - continue_contribution


def structural_checks() -> None:
    G = [[R[1 << j][i] - SINGLETON[i] for j in range(4)] for i in range(4)]
    assert G == [[0, 3, -1, -1], [3, 0, -1, -1],
                 [-1, -1, 0, 3], [-1, -1, 3, 0]]
    B = [[F(x, 15) for x in row] for row in
         [[2, 7, 3, 3], [7, 2, 3, 3], [3, 3, 2, 7], [3, 3, 7, 2]]]
    assert determinant(G) == 45
    assert all(sum(G[i][k] * B[k][j] for k in range(4)) == int(i == j)
               for i in range(4) for j in range(4))
    assert all(x > 0 for row in B for x in row)
    assert all(sum(row) == 1 for row in B)
    assert not any(G[i][j] <= 0 <= G[j][i]
                   for i in range(4) for j in range(4) if i != j)
    all_one = tuple(F(1) for _ in range(4))
    assert tuple(stationary_residual(all_one, i) for i in range(4)) == (1, 1, -2, F(1, 2))
    q = (F(0), F(0), F(1), F(0))
    assert stationary_residual(q, 0) - stationary_residual(q, 1) == 3
    for A in range(1, 16):
        # The exhibited profitable toggle never deletes the only quitter.
        gains = [(R[A ^ (1 << i)][i] - R[A][i], i)
                 for i in range(4) if A ^ (1 << i)]
        assert max(gains)[0] >= 1
    assert SINGLETON[0] == 1  # All-Never is also exploitable.
    assert R[3][0] > SINGLETON[0] and R[3][1] > SINGLETON[1]


def main() -> None:
    future, join = checked_slacks()
    reject_old_tests()
    count = order_type_checks()
    U, B = finite_equilibrium_check()
    structural_checks()
    print('PASS: patient Never-row slack = 1/2; other 14 row slacks are at least 1.')
    print('Future slacks:', ', '.join(map(str, future)))
    print('Join slacks:', ', '.join(map(str, join)))
    print('PASS: all 14 old proper-child tests have explicit one-row rejection certificates.')
    print('PASS: 625 terminal patient-reset order-type checks.')
    print(f'PASS: {count} plain-cancellation clock-order / monotone-evaluation checks.')
    print('PASS: explicit full-cap equilibrium: U = B =', tuple(map(str, U)))
    print('PASS: singleton inverse/determinant, quotient witnesses, and no-pure checks.')
    print('These are exact mathematical regressions, not Lean-checked theorems.')


if __name__ == '__main__':
    main()
