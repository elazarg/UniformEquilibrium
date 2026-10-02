#!/usr/bin/env python3
"""Exact finite checks for weak-singleton-payoff exclusion.

Standard library only. The analytic theorems are in the companion Markdown.
Checks here do not establish universal equilibrium existence on their own.

  python VERIFY_WEAK_SINGLETON_EXCLUSION.py

The finite-profile cap calculation checks every relevant pure response date,
plus a date after the cutoff and Never, independently of the backward ledger.
For finite opponent laws these exhaust unrestricted response values.
"""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path

N = 4
A, B = 3, 12  # {0,1}, {2,3}
Z_PLUS = {1, 8, 9}   # nonempty subsets of {0,3}
Z_MINUS = {2, 4, 6}  # nonempty subsets of {1,2}
R = [
    [0, 0, 0, 0],
    [1, -20, 1, 1],
    [0, 0, 1, 1],
    [21, 0, 0, 0],
    [0, 0, 0, F(1001, 1000)],
    [1, 0, 0, 1],
    [0, 0, 3, -2],
    [1, -2, 2, 2],
    [1, -20, 1, 0],
    [1, -20, 2, 0],
    [1, 0, -1, 3],
    [1, 0, -1, 2],
    [1, 1, 1, 1],
    [1, 0, -2, 1],
    [1, 0, 1, 3],
    [1, 0, 3, -2],
]
R = [[F(x) for x in row] for row in R]
SINGLETON = [R[1 << i][i] for i in range(N)]
M = F(21)


def mul(xs):
    out = F(1)
    for x in xs:
        out *= x
    return out


def endpoints(q, v):
    """Quit, Continue, deleted survival, and passive absorption numerator."""
    Q, C, beta, H = ([F(0) for _ in range(N)] for _ in range(4))
    for i in range(N):
        beta[i] = mul(1-q[j] for j in range(N) if j != i)
        for mask in range(1 << N):
            if mask & (1 << i):
                continue
            mass = mul(q[j] if mask & (1 << j) else 1-q[j]
                       for j in range(N) if j != i)
            Q[i] += mass*R[mask | (1 << i)][i]
            if mask:
                H[i] += mass*R[mask][i]
        C[i] = H[i] + beta[i]*v[i]
    return Q, C, beta, H


def prefix(U, caps, q):
    Q, C, beta, _ = endpoints(q, U)
    return ([q[i]*Q[i]+(1-q[i])*C[i] for i in range(N)],
            [max(Q[i], C[i]+beta[i]*(caps[i]-U[i])) for i in range(N)])


def ledger(rows):
    """Backward cap/payoff recursion; rows are in chronological order."""
    U = [F(0)]*N
    caps = [max(x, F(0)) for x in SINGLETON]
    for q in reversed(rows):
        U, caps = prefix(U, caps, q)
    return U, caps


def independent_semantics(rows):
    """Forward outcome sums and maximum over all pure response classes."""
    U = [F(0)]*N
    reached = F(1)
    passive = [F(0)]*N
    deleted_survival = [F(1)]*N
    replies = [[] for _ in range(N)]
    for q in rows:
        for mask in range(1, 1 << N):
            mass = reached*mul(q[j] if mask & (1 << j) else 1-q[j]
                               for j in range(N))
            for i in range(N):
                U[i] += mass*R[mask][i]
        Q, _, beta, H = endpoints(q, [F(0)]*N)
        for i in range(N):
            replies[i].append(passive[i]+deleted_survival[i]*Q[i])
            passive[i] += deleted_survival[i]*H[i]
            deleted_survival[i] *= beta[i]
        reached *= mul(1-x for x in q)
    for i in range(N):
        replies[i].append(passive[i]+deleted_survival[i]*SINGLETON[i])
        replies[i].append(passive[i])  # Never
    return U, [max(x) for x in replies]


def law_coalitions(laws):
    """Law entries are masses at 0, 1, Never. Enumerate actual product draws."""
    mass = [F(0)]*(1 << N)
    for clocks in product(range(3), repeat=N):
        prob = mul(laws[i][clocks[i]] for i in range(N))
        if not prob:
            continue
        t = min(clocks)
        mask = 0 if t == 2 else sum(1 << i for i in range(N) if clocks[i] == t)
        mass[mask] += prob
    assert sum(mass) == 1
    return mass


def run_checks():
    # Rational parameterization of the exact maximum identity:
    # d=2t+t^2/a, optimum=t^2/a, gap=(delta-t)^2/(a+delta).
    # The universal identity is proved algebraically in the manuscript.
    scalar_count = 0
    for a in [F(1, 3), F(1), F(2), F(42)]:
        for t in [F(1, 100), F(1, 3), F(1), F(5)]:
            d = 2*t+t*t/a
            for k in range(20):
                delta = d*F(k, 19)
                gap = t*t/a-delta*(d-delta)/(a+delta)
                assert gap == (delta-t)**2/(a+delta)
                assert gap >= 0
                scalar_count += 1
    assert scalar_count == 320
    assert SINGLETON == [1, 0, 0, 0]
    assert max(abs(x) for row in R for x in row) == M
    for mask in range(1, 1 << N):
        assert R[mask][0]-SINGLETON[0] <= 20*(mask == A)-(mask in Z_MINUS)
        assert R[mask][1]-SINGLETON[1] <= (mask == B)-20*(mask in Z_PLUS)
    assert F(20)*1 == F(1)*20

    # Strict separation from product-low; weak, but not strict, payoff deficit.
    assert R[B] == [1, 1, 1, 1]
    assert R[B][2] > SINGLETON[2] and R[B][3] > SINGLETON[3]
    assert [R[B][i]-SINGLETON[i] for i in range(N)] == [0, 1, 1, 1]
    correlated = [(R[A][i]+R[B][i])/2 for i in range(N)]
    assert all(correlated[i] > SINGLETON[i] for i in range(N))

    # Every nonempty pure coalition has a profitable membership toggle.
    toggle_witnesses = {}
    for mask in range(1, 1 << N):
        witnesses = [i for i in range(N) if R[mask ^ (1 << i)][i] > R[mask][i]]
        assert witnesses, mask
        toggle_witnesses[str(mask)] = witnesses[0]
    # No stationary profile with exactly one active player, at any positive hazard.
    solo_observers = [1, 0, 0, 1]
    for i, j in enumerate(solo_observers):
        passive = R[1 << i][j]
        assert passive < SINGLETON[j]
        assert passive < R[(1 << i) | (1 << j)][j]

    # Exhaustive finite regression for the determinant, not a universal proof.
    laws = [(F(a, 2), F(b, 2), F(2-a-b, 2))
            for a in range(3) for b in range(3-a)]
    count = 0
    for profile in product(laws, repeat=N):
        m = law_coalitions(profile)
        zp, zm = sum(m[x] for x in Z_PLUS), sum(m[x] for x in Z_MINUS)
        assert m[A]*m[B] <= zp*zm
        payoff = [sum(m[mask]*R[mask][i] for mask in range(16)) for i in range(N)]
        assert min(payoff[i]-SINGLETON[i] for i in range(N)) <= 0
        count += 1
    assert count == 1296

    # Source exercising the concentrated-debt branch, not merely an auxiliary root.
    seed = [[F(0), F(1, 200), F(0), F(0)], [F(0), F(0), F(1), F(1)]]
    U, caps = ledger(seed)
    assert (U, caps) == independent_semantics(seed)
    assert U == [F(199, 200), F(199, 200), F(1), F(1)]
    assert caps == [F(11, 10), F(1), F(1), F(200199, 200000)]
    D = sum(caps[i]-U[i] for i in range(N))
    assert D == F(22199, 200000)
    eps, tau, theta = F(1, 10), F(1, 80), F(1, 3360)
    assert min(caps[i]-SINGLETON[i] for i in range(N)) > D-tau
    assert U[0] <= SINGLETON[0]
    assert sum(caps[i]-U[i] for i in [1, 2, 3]) < tau
    solo = [theta, F(0), F(0), F(0)]
    k = 0
    while min(U[j]-SINGLETON[j] for j in [1, 2, 3]) > eps/2:
        old_U, old_B = U, caps
        Q, C, _, _ = endpoints(solo, old_U)
        assert all(C[j] > Q[j] for j in [1, 2, 3])
        U, caps = prefix(old_U, old_B, solo)
        assert caps[0] == old_B[0]
        for j in [1, 2, 3]:
            assert caps[j]-U[j] == (1-theta)*(old_B[j]-old_U[j])
        new_D = sum(caps[i]-U[i] for i in range(N))
        assert new_D <= D
        D = new_D
        assert D >= eps
        k += 1
        assert k < 1000
    assert k == 155
    assert min(caps[i]-SINGLETON[i] for i in range(N)) <= D-tau
    rows = [solo]*k + seed
    assert (U, caps) == independent_semantics(rows)
    boundary_D = D

    # An exact rational auxiliary root at the literal boundary source.
    q = [F(1), F(1, 3), F(10, 11), F(0)]
    h = D-tau/2
    v = [caps[i]-h for i in range(N)]
    Q, C, _, _ = endpoints(q, v)
    regrets = [max(Q[i], C[i])-(q[i]*Q[i]+(1-q[i])*C[i]) for i in range(N)]
    assert regrets == [0, 0, 0, 0]
    A_floor = tau/(4*M+tau)
    eta = A_floor*tau/(8*N)
    Delta = A_floor*tau/8
    assert max(regrets) <= eta
    U, caps = prefix(U, caps, q)
    assert sum(caps[i]-U[i] for i in range(N)) <= D-Delta
    final_rows = [q]+rows
    assert (U, caps) == independent_semantics(final_rows)
    assert U == caps == [F(53, 33), F(-20, 11), F(2, 3), F(14, 11)]

    # Also disclose that this particular fixture has a shorter exact equilibrium.
    # The long witness validates the new source-preserving branch; it is not a
    # minimal strategy or an obstruction to other equilibrium methods.
    short_U, short_B = independent_semantics([q])
    assert short_U == short_B == U

    report = {
        'status': 'all exact finite checks passed',
        'table_bound': str(M),
        'scalar_maximization_identity_checks': scalar_count,
        'clock_grid_profiles': count,
        'seed_total_debt': str(F(22199, 200000)),
        'solo_rows': k,
        'debt_after_solo_rows_approx': float(boundary_D),
        'final_total_debt': '0',
        'final_payoff_and_caps': [str(x) for x in U],
        'final_profile_rows': len(final_rows),
        'fixture_also_has_a_one_row_exact_equilibrium': True,
        'pure_coalition_toggle_witnesses_by_bitmask': toggle_witnesses,
        'scope': 'Finite arithmetic regression only. No Lean compilation; no universal theorem follows from this grid.'
    }
    return report


if __name__ == '__main__':
    report = run_checks()
    print(json.dumps(report, indent=2))
    Path(__file__).with_name('WEAK_SINGLETON_EXCLUSION_CHECKS.json').write_text(
        json.dumps(report, indent=2)+'\n', encoding='utf-8')
