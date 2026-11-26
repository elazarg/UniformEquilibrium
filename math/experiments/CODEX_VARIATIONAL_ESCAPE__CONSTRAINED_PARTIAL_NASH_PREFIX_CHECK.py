"""Exact finite algebra for the constrained observer-prefix argument.

The tail tuples below test algebraic identities only. They are not claimed
to be realizable positive-absorbing-gap games or global constrained minima.
The unrestricted and compact-source claims require the note's proof.
"""

from fractions import Fraction as F
from itertools import product
from random import Random


def prod(xs):
    ans = F(1)
    for x in xs:
        ans *= x
    return ans


def subsets(players):
    players = tuple(players)
    for bits in product((0, 1), repeat=len(players)):
        yield frozenset(j for j, bit in zip(players, bits) if bit)


def root_values(z, q, b):
    Q, P, H, C, gap, regret = [], [], [], [], [], []
    for i in range(4):
        opp = tuple(j for j in range(4) if j != i)
        quit, passive = F(0), F(0)
        for coalition in subsets(opp):
            mass = prod(q[j] if j in coalition else 1 - q[j] for j in opp)
            quit += mass * z[i, coalition | {i}]
            if coalition:
                passive += mass * z[i, coalition]
        survive = prod(1 - q[j] for j in opp)
        cont = passive + survive * b[i]
        delta = quit - cont
        Q.append(quit)
        P.append(passive)
        H.append(survive)
        C.append(cont)
        gap.append(delta)
        regret.append(max((1 - q[i]) * delta, -q[i] * delta))
    return Q, P, H, C, gap, regret


def nash_coordinate(q, gap):
    return (q == 0 and gap <= 0) or (q == 1 and gap >= 0) or (
        0 < q < 1 and gap == 0
    )


def random_table(rng):
    z = {}
    for coalition in subsets(range(4)):
        if coalition:
            for i in range(4):
                z[i, coalition] = F(0) if coalition == {i} else F(rng.randint(-6, 6))
    assert len(z) == 60
    return z


def main():
    rng = Random(750312)
    identities = 0
    observer_repairs = 0
    auxiliary_bounds = 0

    for _ in range(900):
        z = random_table(rng)
        q = tuple(F(rng.randrange(5), 4) for _ in range(4))
        b = tuple(F(rng.randrange(-6, 7), 3) for _ in range(4))
        debt = tuple(F(rng.randrange(6), 5) for _ in range(4))
        u = tuple(b[i] - debt[i] for i in range(4))
        Q, P, H, C, gap, R = root_values(z, q, b)
        s = prod(1 - qi for qi in q)
        for i in range(4):
            new_u = q[i] * Q[i] + (1 - q[i]) * (P[i] + H[i] * u[i])
            new_b = max(Q[i], C[i])
            assert new_b - new_u == R[i] + s * debt[i]
            assert R[i] >= 0
        identities += 1

        h = rng.randrange(4)
        a = F(rng.randrange(9), 4)
        lowered = tuple(b[i] - (a if i == h else 0) for i in range(4))
        aux_gap = root_values(z, q, lowered)[4]
        assert aux_gap[h] == gap[h] + H[h] * a
        for i in range(4):
            if i != h:
                assert aux_gap[i] == gap[i]
        if nash_coordinate(q[h], aux_gap[h]):
            assert R[h] <= q[h] * H[h] * a
            auxiliary_bounds += 1

        if all(nash_coordinate(q[i], gap[i]) for i in range(4) if i != h):
            nu = F(1, 25)
            penalty = F(2, 7)
            pivot_debt = F(3, 8)
            constrained_u = tuple(b[i] - (pivot_debt if i == h else 0) for i in range(4))
            new_debts = []
            for i in range(4):
                new_u = q[i] * Q[i] + (1 - q[i]) * (
                    P[i] + H[i] * constrained_u[i]
                )
                new_debts.append(max(Q[i], C[i]) - new_u)
            assert all(new_debts[i] == 0 for i in range(4) if i != h)
            assert new_debts[h] + penalty * s * nu == (
                R[h] + s * (pivot_debt + penalty * nu)
            )
            observer_repairs += 1

    # The preemption estimate keeps q_h before dividing: no uniform positive
    # lower bound on that root probability is used.
    lower_bounds = 0
    for M in (F(1), F(3), F(10)):
        for D in (M / 10, M, 2 * M):
            ratio = D / (4 * D + 8 * M)  # eta/m
            for qh in (F(1, 1000000), F(1, 7), F(1)):
                for a, b in product((F(0), F(1, 2), F(1)), repeat=2):
                    qj, qk = a * ratio * qh, b * ratio * qh
                    exact_lower = qh * D * (1 - qj) * (1 - qk) - 2 * M * (qj + qk)
                    coarse_lower = qh * (D * (1 - 2 * ratio) - 4 * M * ratio)
                    assert exact_lower >= coarse_lower > 0
                    assert qj < 1 and qk < 1
                    lower_bounds += 1

    # Critical-face solo prefixes, including zero observer caps and
    # nonpositive contacts. These are algebraic tail controls only.
    solo_checks = 0
    for b_obs in product((F(0), F(1, 4), F(2)), repeat=3):
        for contacts in product((F(-2), F(0), F(3)), repeat=3):
            if any(b == 0 and delta > 0 for b, delta in zip(b_obs, contacts)):
                continue
            z = random_table(rng)
            h = 0
            for i in range(1, 4):
                z[i, frozenset((0, i))] = z[i, frozenset((0,))] + contacts[i - 1]
            m, penalty, nu = F(1), F(1, 2), F(1, 16)
            b = (m,) + b_obs
            pivot_debt = m - penalty * nu
            u = (penalty * nu,) + b_obs
            bounds = [F(1, 2)] + [
                bi / (2 * (bi + delta))
                for bi, delta in zip(b_obs, contacts) if delta > 0
            ]
            p = min(bounds)
            assert 0 < p < 1
            q = (p, F(0), F(0), F(0))
            Q, P, H, C, gap, R = root_values(z, q, b)
            assert all(nash_coordinate(q[i], gap[i]) for i in range(1, 4))
            assert R[h] == p * m
            assert max(Q[h], C[h]) == m
            new_pivot_u = q[h] * Q[h] + (1 - q[h]) * (P[h] + H[h] * u[h])
            new_pivot_debt = max(Q[h], C[h]) - new_pivot_u
            assert new_pivot_debt + penalty * (1 - p) * nu == m
            assert R[h] + (1 - p) * pivot_debt == new_pivot_debt
            assert (1 - p) * F(1, 2) < F(1, 2)
            solo_checks += 1

    assert auxiliary_bounds > 0 and observer_repairs > 0
    print(
        f"PASS: {identities} full prefix identities; "
        f"{observer_repairs} observer-Nash repairs; "
        f"{auxiliary_bounds} auxiliary bounds; "
        f"{lower_bounds} critical-face lower bounds; "
        f"{solo_checks} exact solo-prefix controls."
    )


if __name__ == "__main__":
    main()
