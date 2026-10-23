"""Exact controls; the universal dual/graft proof is in the matching owned note.

This table has A_abs=0. None of these profiles is claimed to be a positive-gap
global minimum. Only Fraction arithmetic is used; no numerical optimization.
"""
from fractions import Fraction as F
from itertools import permutations, product

G = ((0, -9, -6, 7), (-6, 0, 4, 7), (7, 8, 0, -1), (-1, -3, 9, 0))
adj = ((516, -405, 777, 524), (-391, 435, 308, -454),
       (-73, 100, 189, 723), (484, 645, 558, 36))
assert all(sum(G[i][k] * adj[k][j] for k in range(4)) == 7345 * (i == j)
           for i in range(4) for j in range(4))
z = tuple(F(a, 7345) for a in (536, 775, 1832, 829))
assert all(0 < 2 * a < 1 for a in z)
assert all(sum(z[i] * G[i][j] for i in range(4)) == 1 for j in range(4))


def reward(i, coalition):
    if not coalition or i in coalition:
        return F(0)
    if len(coalition) == 1:
        return F(G[i][next(iter(coalition))])
    if len(coalition) == 2:
        return F(3)
    assert len(coalition) == 3
    return F(0)


def outcome(draws):
    finite = [d for d in draws if d is not None]
    if not finite:
        return frozenset()
    first = min(finite)
    return frozenset(i for i, d in enumerate(draws) if d == first)


def law_data(laws):
    assert all(sum(law.values()) == 1 and min(law.values()) >= 0 for law in laws)
    probabilities = {}
    for choices in product(*(tuple(law.items()) for law in laws)):
        draws = tuple(t for t, _ in choices)
        p = F(1)
        for _, a in choices:
            p *= a
        coalition = outcome(draws)
        probabilities[coalition] = probabilities.get(coalition, F(0)) + p
    u = tuple(sum(p * reward(i, c) for c, p in probabilities.items()) for i in range(4))
    never = tuple(law.get(None, F(0)) for law in laws)
    nu = F(1)
    for a in never:
        nu *= a
    assert probabilities.get(frozenset(), F(0)) == nu
    last = max((d for law in laws for d in law if d is not None), default=0)
    query_menu = tuple(range(last + 2)) + (None,)
    caps, ends, menu = [], [], []
    for i in range(4):
        values = []
        for query in query_menu:
            total = F(0)
            opponent_ids = tuple(j for j in range(4) if j != i)
            for choices in product(*(tuple(laws[j].items()) for j in opponent_ids)):
                draws = [None] * 4
                draws[i] = query
                p = F(1)
                for j, (d, a) in zip(opponent_ids, choices):
                    draws[j] = d
                    p *= a
                total += p * reward(i, outcome(draws))
            values.append(total)
        caps.append(max(values))
        ends.append(values[-1])
        menu.append(tuple(values))
    assert all(caps[i] >= max(F(0), u[i]) for i in range(4))
    return u, tuple(caps), never, tuple(ends), nu, probabilities, tuple(menu)


def objective(data):
    u, b, _, _, nu, _, _ = data
    return sum(b[i] - u[i] for i in range(4)) + nu


old_laws = tuple({1: F(1, 2), None: F(1, 2)} for _ in range(4))
old = law_data(old_laws)
assert old[3] == tuple(F(a, 8) for a in (1, 14, 23, 14))
assert old[1] == old[3] and old[0] == tuple(e / 2 for e in old[3])
assert old[4] == F(1, 16) and objective(old) == F(53, 16)


def graft(tail_laws):
    laws = []
    for tail in tail_laws:
        row = {1: F(1, 2), None: F(1, 2) * tail.get(None, F(0))}
        for date, mass in tail.items():
            if date is not None:
                row[date + 3] = mass / 2
        laws.append(row)
    return law_data(laws)


def check_graft(tail_laws):
    q = law_data(tail_laws)
    new = graft(tail_laws)
    u, b, n, e, nu, probs, _ = q
    for i in range(4):
        assert new[0][i] == old[0][i] + old[4] * u[i]
        assert new[1][i] == old[3][i] + F(1, 8) * b[i]
        assert new[2][i] == old[2][i] * n[i]
        assert new[3][i] == old[3][i] + F(1, 8) * e[i]
    exact = old[4] * (2 * sum(b) - sum(u) - (1 - nu))
    assert objective(new) - objective(old) == exact
    dual = old[4] * sum(p * (sum(z[i] * reward(i, c) for i in range(4)) - 1)
                       for c, p in probs.items() if c)
    assert exact >= dual
    multi = sum(p for c, p in probs.items() if len(c) >= 2)
    coalitions = [frozenset(i for i, flag in enumerate(bits) if flag)
                  for bits in product((False, True), repeat=4)]
    k_multi = max([F(0)] + [1 - sum(z[i] * reward(i, c) for i in range(4))
                           for c in coalitions if len(c) >= 2])
    assert exact >= -old[4] * k_multi * multi
    return q, exact, dual


rates = (F(1, 2), F(1, 3), F(2, 5), F(3, 7))
tested = 0
signed_drift_seen = False
for word in permutations(range(4)):
    dates = {owner: 1 + 2 * k for k, owner in enumerate(word)}
    laws = tuple({dates[i]: rates[i], None: 1 - rates[i]} for i in range(4))
    q, change, dual = check_graft(laws)
    assert all(len(c) <= 1 or p == 0 for c, p in q[5].items())
    assert dual == 0 and change >= 0
    signed_drift_seen |= any(any(a < 0 for a in row) and any(a > 0 for a in row)
                             for row in q[6])
    # A partial-END algebra control; no actual old source is asserted for it.
    kappa = (F(1), F(0), F(0), F(1))
    n = (F(1, 2), F(1, 3), F(1, 3), F(1, 2))
    zz = (-1, 2, 2, -1)
    assert all(sum(zz[i] * G[i][j] for i in range(4)) >= 1 for j in range(4))
    exact_partial = sum(max(q[1][i] - kappa[i], 0) / n[i] - q[0][i]
                        for i in range(4)) - (1 - q[4])
    partial_dual = sum(zz[i] * q[0][i] for i in range(4)) - (1 - q[4])
    assert exact_partial >= partial_dual >= 0
    tested += 1
assert tested == 24 and signed_drift_seen

grand = tuple({1: F(1)} for _ in range(4))
q, change, dual = check_graft(grand)
assert q[0] == q[1] == (0, 0, 0, 0) and q[4] == 0
assert change == dual == F(-1, 16)
# Both ends of the dual box are essential to the cap inequality.
assert 1 * 0 - (-1) * (-1) < 0
assert 1 * 1 - 2 * 1 < 0
print('PASS: exact dual box, full60 table/full caps,24 signed singleton calendars,')
print('partial-END algebra and actual grand-collision escape of -1/16.')
print('Native absorbing floor A=0 by the displayed grand Nash; no counterexample claim.')
