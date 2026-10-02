#!/usr/bin/env python3
"""Feasibility probe for the one-round screening system (attack note, section 16).

Purpose. Search for an exact rational feasible point of the one-round
minimum-return screening system: table entries, marked row, limit tail pair,
and prefix aggregates satisfying (C1)-(C8) with the row-replacement family
{all-Continue, four pure singletons, pure marked pair}. A feasible point is
negative information (screening alone cannot refute one round's local data)
and a concrete local model; failure to find one proves nothing.

Method. Stage 1: float search (random restarts + coordinate descent on total
violation). Stage 2: rationalize and verify every constraint in exact
Fractions. A point is reported only if stage 2 passes with margin.

Self-test. Before probing, the two-cut assembly (graft identities) and the
stationary tail formulas are validated against direct exact computation on an
explicit profile (prefix row + window row + stationary tail). Run with
--selftest to run only that.

Caveats (also in the note): (C6)-(C7) are encoded at fact-base fidelity, not
transcribed from the checked packet fields; prefix aggregates are free
subject to (C1), so realizability by an actual prefix is NOT checked; the
probe uses reward bound R = 1.

Repro: python3 one_round_probe.py [--selftest] [--seed N] [--iters N]
"""

from __future__ import annotations

import argparse
import itertools
import random
from fractions import Fraction as Q
from typing import Dict, List, Sequence, Tuple

N = 4
PLAYERS = range(N)
MASKS = range(1, 16)  # nonempty coalitions as bitmasks


def members(mask: int) -> List[int]:
    return [i for i in PLAYERS if mask & (1 << i)]


# ----------------------------------------------------------------------
# Row calculus (exact for Fraction inputs, float for float inputs)
# ----------------------------------------------------------------------

def coalition_prob(q: Sequence, mask: int) -> object:
    """pi_q(mask): exactly the players in mask quit at the row."""
    p = q[0] * 0 + 1
    for i in PLAYERS:
        p = p * (q[i] if mask & (1 << i) else (1 - q[i]))
    return p


def deleted_prob(q: Sequence, mask: int, obs: int) -> object:
    """pi^{-obs}_q(mask): mask subset of others; obs's action removed."""
    p = q[0] * 0 + 1
    for i in PLAYERS:
        if i == obs:
            continue
        p = p * (q[i] if mask & (1 << i) else (1 - q[i]))
    return p


def row_quantities(reward: Dict[int, Sequence], q: Sequence):
    """Return (rho_V, U_V, rho_del, W_V, M_V); vectors indexed by player."""
    rho_V = coalition_prob(q, 0)
    U_V = [sum(coalition_prob(q, m) * reward[m][i] for m in MASKS)
           for i in PLAYERS]
    rho_del, W_V, M_V = [], [], []
    for i in PLAYERS:
        others = [m for m in range(16) if not (m & (1 << i))]
        rho_del.append(deleted_prob(q, 0, i))
        W_V.append(sum(deleted_prob(q, m, i) * reward[m][i]
                       for m in others if m != 0))
        M_V.append(sum(deleted_prob(q, m, i) * reward[m | (1 << i)][i]
                       for m in others))
    return rho_V, U_V, rho_del, W_V, M_V


def two_cut(reward, q, u, b, rho_a, rho_a_del, U_pi, W_pi, M_pi):
    """Whole-round (U_i, B_i) by the exact two-cut decomposition."""
    rho_V, U_V, rho_del, W_V, M_V = row_quantities(reward, q)
    U, B = [], []
    for i in PLAYERS:
        U.append(U_pi[i] + rho_a * (U_V[i] + rho_V * u[i]))
        inner = max(M_V[i], W_V[i] + rho_del[i] * b[i])
        B.append(max(M_pi[i], W_pi[i] + rho_a_del[i] * inner))
    return U, B


# ----------------------------------------------------------------------
# Stationary tail formulas (attack note, Theorem 9.1) -- exact
# ----------------------------------------------------------------------

def stationary_pair(reward, q):
    """(U_i, B_i) of the stationary profile with rates q (q != 0)."""
    U, B = [], []
    for i in PLAYERS:
        others = [m for m in range(16) if not (m & (1 << i))]
        beta = deleted_prob(q, 0, i)
        h_del = 1 - beta
        VQ = sum(deleted_prob(q, m, i) * reward[m | (1 << i)][i]
                 for m in others)
        if h_del != 0:
            VN = sum(deleted_prob(q, m, i) * reward[m][i]
                     for m in others if m != 0) / h_del
        else:
            VN = q[0] * 0
        h = q[i] + (1 - q[i]) * h_del
        assert h != 0, "stationary tail needs q != 0"
        U.append((q[i] * VQ + (1 - q[i]) * h_del * VN) / h)
        B.append(max(VQ, VN))
    return U, B


# ----------------------------------------------------------------------
# Self-test: direct vs two-cut on prefix-row + window-row + stationary tail
# ----------------------------------------------------------------------

def direct_pair(reward, rows: List[Sequence], tail_q):
    """(U_i, B_i) of profile: finitely many rows then stationary tail_q.

    Direct computation from first principles: U by forward absorption;
    B_i as max over quit dates (0..len(rows)+1 inside, then the stationary
    segment collapses to two values) and Never.
    """
    T = len(rows)
    U = []
    for i in PLAYERS:
        surv, total = 1, 0
        for row in rows:
            for m in MASKS:
                total += surv * coalition_prob(row, m) * reward[m][i]
            surv *= coalition_prob(row, 0)
        tU, _ = stationary_pair(reward, tail_q)
        total += surv * tU[i]
        U.append(total)
    B = []
    for i in PLAYERS:
        # value of quitting at date t (deviator continues before t)
        values = []
        for t in range(T + 1):
            surv_del, collect = 1, 0
            for s in range(min(t, T)):
                row = rows[s]
                others = [m for m in range(16) if not (m & (1 << i))]
                for m in others:
                    if m != 0:
                        collect += surv_del * deleted_prob(row, m, i) \
                            * reward[m][i]
                surv_del *= deleted_prob(row, 0, i)
            if t < T:
                row = rows[t]
                others = [m for m in range(16) if not (m & (1 << i))]
                quit_val = sum(deleted_prob(row, m, i)
                               * reward[m | (1 << i)][i] for m in others)
                values.append(collect + surv_del * quit_val)
            else:
                # reaching the stationary tail: cap there is stationary B
                _, tB = stationary_pair(reward, tail_q)
                values.append(collect + surv_del * tB[i])
        # Never inside the finite rows then Never in tail is dominated by
        # the tail-cap branch above (stationary B already includes Never).
        B.append(max(values))
    return U, B


def selftest() -> None:
    rnd = random.Random(7)

    def rq() -> Q:
        return Q(rnd.randint(-8, 8), 8)

    reward = {m: [rq() for _ in PLAYERS] for m in MASKS}
    p0 = [Q(1, 5), Q(0), Q(1, 3), Q(0)]
    x = [Q(1, 2), Q(1, 7), Q(0), Q(1, 4)]
    tail = [Q(1, 6), Q(1, 9), Q(1, 8), Q(1, 10)]

    # direct on [p0, x] + tail
    U_direct, B_direct = direct_pair(reward, [p0, x], tail)

    # two-cut: prefix = [p0], window = x, tail pair from stationary formulas
    tU, tB = stationary_pair(reward, tail)
    rho_a = coalition_prob(p0, 0)
    rho_a_del = [deleted_prob(p0, 0, i) for i in PLAYERS]
    U_pi = [sum(coalition_prob(p0, m) * reward[m][i] for m in MASKS)
            for i in PLAYERS]
    W_pi, M_pi = [], []
    for i in PLAYERS:
        others = [m for m in range(16) if not (m & (1 << i))]
        W_pi.append(sum(deleted_prob(p0, m, i) * reward[m][i]
                        for m in others if m != 0))
        M_pi.append(sum(deleted_prob(p0, m, i) * reward[m | (1 << i)][i]
                        for m in others))
    U_tc, B_tc = two_cut(reward, x, tU, tB, rho_a, rho_a_del,
                         U_pi, W_pi, M_pi)

    assert U_direct == U_tc, (U_direct, U_tc)
    assert B_direct == B_tc, (B_direct, B_tc)
    print("selftest OK: direct == two-cut (exact, Fractions)")


# ----------------------------------------------------------------------
# The one-round system (C1)-(C8); violation function and exact check
# ----------------------------------------------------------------------

J, O, P = 0, 1, 2  # labels: singleton owner j=0, forced o=1, payer p=2
PAIR = (1 << J) | (1 << O)

COMPARISON_ROWS = [
    [0, 0, 0, 0],                      # all-Continue
    [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1],
    [1, 1, 0, 0],                      # pure marked pair {j,o}
]


def violations(v: Dict[str, object]) -> List[Tuple[str, object]]:
    """List of (name, violation_amount>0) for the point v.

    v holds: reward (dict), x (row), u, b, rho_a, rho_a_del, U_pi, W_pi,
    M_pi, Dstar, lam.
    """
    out = []
    r, x = v["reward"], v["x"]
    u, b = v["u"], v["b"]
    rho_a, rho_a_del = v["rho_a"], v["rho_a_del"]
    U_pi, W_pi, M_pi = v["U_pi"], v["W_pi"], v["M_pi"]
    Dstar, lam = v["Dstar"], v["lam"]
    gamma = Dstar / 4
    g = lam * Dstar / 3

    def need(name, expr):  # expr >= 0 required
        if expr < 0:
            out.append((name, -expr))

    # C1 consistency
    need("Dstar>0", Dstar - Q(1, 1000) if isinstance(Dstar, Q)
         else Dstar - 1e-3)
    need("lam>0", lam - (Q(1, 1000) if isinstance(lam, Q) else 1e-3))
    for i in PLAYERS:
        need("x>=0", x[i]); need("x<=1", 1 - x[i])
        need("rho_del<=1", 1 - rho_a_del[i])
        need("rho_a<=rho_del", rho_a_del[i] - rho_a)
        need("b>=u", b[i] - u[i])
        need("|u|<=1", 1 - abs(u[i])); need("|b|<=1", 1 - abs(b[i]))
        need("|Mpi|<=1", 1 - abs(M_pi[i]))
        need("|Upi|", (1 - rho_a) - abs(U_pi[i]))
        need("|Wpi|", (1 - rho_a_del[i]) - abs(W_pi[i]))
    need("rho_a>=0", rho_a)
    for m in MASKS:
        for i in PLAYERS:
            need("|r|<=1", 1 - abs(r[m][i]))
    # solos nonnegative (punishment-normality for free)
    for i in PLAYERS:
        need("solo>=0", r[1 << i][i])
    # C2 mark floor
    need("C2", rho_a * coalition_prob(x, PAIR) - lam)
    # C3 tail return
    gap3 = sum(b[i] - u[i] for i in PLAYERS) - Dstar
    if gap3 != 0:
        out.append(("C3", abs(gap3)))
    # C4 whole-round minimality (equality)
    U, B = two_cut(r, x, u, b, rho_a, rho_a_del, U_pi, W_pi, M_pi)
    gap4 = sum(B[i] - U[i] for i in PLAYERS) - Dstar
    if gap4 != 0:
        out.append(("C4", abs(gap4)))
    # C5 row replacements
    for k, y in enumerate(COMPARISON_ROWS):
        yq = [Q(c) if isinstance(rho_a, Q) else float(c) for c in y]
        Uy, By = two_cut(r, yq, u, b, rho_a, rho_a_del, U_pi, W_pi, M_pi)
        need(f"C5[{k}]", sum(By[i] - Uy[i] for i in PLAYERS) - Dstar)
    # C6 zero forced-owner defect (fact-base fidelity):
    # o's quit-branch and continue-branch row values agree when 0<x_o<1.
    _, _, rho_del, W_V, M_V = row_quantities(r, x)
    valQ_o = M_V[O]
    valC_o = W_V[O] + rho_del[O] * b[O]
    if 0 < x[O] < 1:
        gap6 = valQ_o - valC_o
        if gap6 != 0:
            out.append(("C6", abs(gap6)))
    elif x[O] == 1:
        need("C6", valQ_o - valC_o)
    else:
        need("C6", valC_o - valQ_o)
    # C7 payer gain >= g: payer's off-branch beats prescribed branch by g.
    valQ_p = M_V[P]
    valC_p = W_V[P] + rho_del[P] * b[P]
    prescribed = x[P] * valQ_p + (1 - x[P]) * valC_p
    need("C7", max(valQ_p, valC_p) - prescribed - g)
    # C8 collider margin
    need("C8", r[PAIR][O] - r[1 << J][O] - gamma)
    return out


def total_violation(v) -> float:
    return float(sum(a for _, a in violations(v)))


# ----------------------------------------------------------------------
# Search
# ----------------------------------------------------------------------

def random_point(rnd) -> Dict[str, object]:
    r = {m: [rnd.uniform(-1, 1) for _ in PLAYERS] for m in MASKS}
    for i in PLAYERS:
        r[1 << i][i] = rnd.uniform(0, 1)
    return {
        "reward": r,
        "x": [rnd.uniform(0, 1) for _ in PLAYERS],
        "u": [rnd.uniform(-1, 1) for _ in PLAYERS],
        "b": [rnd.uniform(-1, 1) for _ in PLAYERS],
        "rho_a": rnd.uniform(0.2, 1),
        "rho_a_del": [rnd.uniform(0.2, 1) for _ in PLAYERS],
        "U_pi": [rnd.uniform(-0.5, 0.5) for _ in PLAYERS],
        "W_pi": [rnd.uniform(-0.5, 0.5) for _ in PLAYERS],
        "M_pi": [rnd.uniform(-1, 1) for _ in PLAYERS],
        "Dstar": rnd.uniform(0.05, 0.5),
        "lam": rnd.uniform(0.01, 0.2),
    }


def flatten(v):
    keys = []
    vals = []
    for m in MASKS:
        for i in PLAYERS:
            keys.append(("reward", m, i)); vals.append(v["reward"][m][i])
    for name in ("x", "u", "b", "rho_a_del", "U_pi", "W_pi", "M_pi"):
        for i in PLAYERS:
            keys.append((name, i)); vals.append(v[name][i])
    for name in ("rho_a", "Dstar", "lam"):
        keys.append((name,)); vals.append(v[name])
    return keys, vals


def unflatten(keys, vals):
    v = {"reward": {m: [0.0] * N for m in MASKS},
         "x": [0.0] * N, "u": [0.0] * N, "b": [0.0] * N,
         "rho_a_del": [0.0] * N, "U_pi": [0.0] * N, "W_pi": [0.0] * N,
         "M_pi": [0.0] * N, "rho_a": 0.0, "Dstar": 0.0, "lam": 0.0}
    for k, val in zip(keys, vals):
        if k[0] == "reward":
            v["reward"][k[1]][k[2]] = val
        elif len(k) == 2:
            v[k[0]][k[1]] = val
        else:
            v[k[0]] = val
    return v


def search(seed: int, iters: int):
    rnd = random.Random(seed)
    best = None
    for restart in range(40):
        v = random_point(rnd)
        keys, vals = flatten(v)
        score = total_violation(v)
        step = 0.25
        for it in range(iters):
            k = rnd.randrange(len(vals))
            old = vals[k]
            vals[k] = old + rnd.uniform(-step, step)
            cand = unflatten(keys, vals)
            s2 = total_violation(cand)
            if s2 <= score:
                score = s2
            else:
                vals[k] = old
            if it % 500 == 499:
                step = max(step * 0.7, 1e-4)
            if score < 1e-9:
                break
        if best is None or score < best[0]:
            best = (score, unflatten(keys, vals))
        if best[0] < 1e-9:
            break
    return best


def rationalize_and_check(v, den=10000):
    def rat(z):
        return Q(z).limit_denominator(den)

    w = {"reward": {m: [rat(z) for z in v["reward"][m]] for m in MASKS},
         "x": [rat(z) for z in v["x"]],
         "u": [rat(z) for z in v["u"]],
         "b": [rat(z) for z in v["b"]],
         "rho_a_del": [rat(z) for z in v["rho_a_del"]],
         "U_pi": [rat(z) for z in v["U_pi"]],
         "W_pi": [rat(z) for z in v["W_pi"]],
         "M_pi": [rat(z) for z in v["M_pi"]],
         "rho_a": rat(v["rho_a"]), "Dstar": rat(v["Dstar"]),
         "lam": rat(v["lam"])}
    # Equalities C3, C4, C6 rarely survive rationalization exactly; repair
    # C3 by adjusting b, then re-derive Dstar from C4 -- er, both cannot be
    # pinned independently; instead treat C3/C4/C6 with tolerance zero and
    # report the exact residuals for manual repair.
    return w, violations(w)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--iters", type=int, default=4000)
    args = ap.parse_args()
    if args.selftest:
        selftest()
        return
    selftest()
    score, v = search(args.seed, args.iters)
    print(f"float search: total violation = {score:.3e}")
    if score < 1e-6:
        w, viols = rationalize_and_check(v)
        print("rationalized point residuals:")
        for name, amt in viols:
            print(f"  {name}: {float(amt):.3e}")
        if not viols:
            print("EXACT FEASIBLE POINT FOUND")
            print(w)
    else:
        worst = sorted(violations(v), key=lambda t: -float(t[1]))[:8]
        print("no feasible point found; worst residuals:")
        for name, amt in worst:
            print(f"  {name}: {float(amt):.3e}")


if __name__ == "__main__":
    main()
