"""Exact finite regressions for CARDINAL_FREE_LCP_INDEX_ESCAPE.md.

Run with Python 3 and SymPy installed:
    python VERIFY_CARDINAL_FREE_LCP_INDEX_ESCAPE.py

All assertions use Fraction or SymPy exact arithmetic. The script checks
algebra and concrete instances, not the universal topological theorem.
"""
from __future__ import annotations

from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path
import random
from typing import Sequence

import sympy as sp

Reward = list[list[F]]


def endpoints(reward: Reward, q: Sequence[F], i: int) -> tuple[F, F, F]:
    """Quit payoff Q, absorbing Continue contribution H, opponent survival."""
    n = len(q)
    if len(reward) != 1 << n:
        raise ValueError("Reward table must include all bitmasks; empty row is unused.")
    Q = H = F(0)
    alpha = F(1)
    for j in range(n):
        if j != i:
            alpha *= 1 - q[j]
    for mask in range(1 << n):
        if mask & (1 << i):
            continue
        mass = F(1)
        for j in range(n):
            if j != i:
                mass *= q[j] if mask & (1 << j) else 1 - q[j]
        Q += mass * reward[mask | (1 << i)][i]
        if mask:
            H += mass * reward[mask][i]
    return Q, H, alpha


def finite_semantics(
    reward: Reward, rows: Sequence[Sequence[F]], horizon: int | None = None
) -> tuple[list[F], list[F]]:
    """Exact prescribed payoffs and COMPLETE caps for a consecutive finite word.

    The extra late finite response and Never are included in the seed.
    For a finite horizon, all later dates are dominated by the first late
    date (nonnegative singleton) or by Never (negative singleton).
    """
    n = len(reward[0])
    N = len(rows)
    if horizon is not None and horizon < 1:
        raise ValueError("The horizon must be positive.")

    def weight(t: int) -> F:
        return F(1) if horizon is None else F(max(horizon - t - 1, 0), horizon)

    U = [F(0)] * n
    B = [weight(N) * max(reward[1 << i][i], F(0)) for i in range(n)]
    for t in range(N - 1, -1, -1):
        q = rows[t]
        if len(q) != n or any(x < 0 or x > 1 for x in q):
            raise ValueError("Every row must be a vector of probabilities.")
        newU, newB = [], []
        for i in range(n):
            Q, H, alpha = endpoints(reward, q, i)
            Q *= weight(t)
            H *= weight(t)
            newU.append(q[i] * Q + (1 - q[i]) * (H + alpha * U[i]))
            newB.append(max(Q, H + alpha * B[i]))
        U, B = newU, newB
    return U, B


def check_discount_algebra() -> dict[str, int]:
    rng = random.Random(20260909)
    identities = sign_cases = 0
    for n in range(2, 7):
        for _ in range(40):
            reward = [[F(rng.randint(-9, 9), 3) for _ in range(n)]
                      for _ in range(1 << n)]
            q = [F(rng.randrange(11), 10) for _ in range(n)]
            lam = F(rng.randrange(1, 10), 10)
            d = 1 - lam
            C = F(1)
            for x in q:
                C *= 1 - x
            L = 1 - d * C
            assert L > 0
            for i in range(n):
                Q, H, alpha = endpoints(reward, q, i)
                R = q[i] * Q + (1 - q[i]) * H
                u = d * R / L
                D = (1 - d * alpha) * Q - H
                assert L * (Q - H - alpha * u) == D
                identities += 1
                if Q < 0 and D >= 0:
                    assert alpha < 1
                    assert H / (1 - alpha) <= Q
                    sign_cases += 1
    assert sign_cases > 0
    return {"discount_identity_coordinates": identities,
            "negative_quit_domination_cases": sign_cases}


def check_linearization() -> int:
    rng = random.Random(91209)
    z = sp.Symbol('z')
    cases = 0
    for n in range(2, 6):
        r = [[sp.Integer(rng.randint(-4, 4)) for _ in range(n)]
             for _ in range(1 << n)]
        h = [sp.Integer(rng.randint(-3, 3)) for _ in range(n)]
        # Signed h tests the ambient, not merely nonnegative, expansion.
        for i in range(n):
            alpha = sp.prod(1 - z * h[j] for j in range(n) if j != i)
            Q = H = sp.Integer(0)
            for mask in range(1 << n):
                if mask & (1 << i):
                    continue
                mass = sp.prod((z * h[j] if mask & (1 << j) else 1 - z * h[j])
                               for j in range(n) if j != i)
                Q += mass * r[mask | (1 << i)][i]
                if mask:
                    H += mass * r[mask][i]
            D_discount = sp.expand((1 - (1 - z) * alpha) * Q - H)
            D_zero = sp.expand((1 - alpha) * Q - H)
            s_i = r[1 << i][i]
            Gh = sum((r[1 << j][i] - s_i) * h[j] for j in range(n))
            assert D_discount.coeff(z, 0) == 0
            assert D_discount.coeff(z, 1) == s_i - Gh
            assert D_zero.coeff(z, 0) == 0
            assert D_zero.coeff(z, 1) == -Gh
            cases += 1
    return cases


def check_matrices() -> dict[str, object]:
    G = sp.Matrix([[0, 2, 1, -3], [-3, 0, 2, 3],
                   [-3, 2, 0, 2], [3, -3, -1, 0]])
    assert G.det() == -3 and all(x > 0 for x in G.inv())
    u = sp.Matrix([10, 1, 1, 1])
    v = sp.Matrix([1, 10, 1, 1])
    sigma = -(v.T * G * u)[0]
    assert sigma == 250
    G5 = G.row_join(-G * u).col_join((-v.T * G).row_join(sp.zeros(1)))
    expected = sp.Matrix([[0, 2, 1, -3, 0], [-3, 0, 2, 3, 25],
                          [-3, 2, 0, 2, 26], [3, -3, -1, 0, -26],
                          [30, -1, -20, -29, 0]])
    assert G5 == expected and G5.det() == -750
    inverse = (G.inv() + u * v.T / sigma).row_join(u / sigma)
    inverse = inverse.col_join((v.T / sigma).row_join(sp.ones(1) / sigma))
    assert G5 * inverse == sp.eye(5) and all(x > 0 for x in inverse)

    i, j = next((i, j) for i in range(5) for j in range(5) if G5[i, j] < 0)
    t = 1
    while True:
        u6 = sp.ones(5, 1); v6 = sp.ones(5, 1)
        u6[j] += t; v6[i] += t
        sig6 = -(v6.T * G5 * u6)[0]
        if sig6 > 0:
            break
        t *= 2
    G6 = G5.row_join(-G5 * u6).col_join((-v6.T * G5).row_join(sp.zeros(1)))
    assert all(G6[i, i] == 0 for i in range(6))
    assert G6.det() == G5.det() * sig6 < 0
    assert all(x > 0 for x in G6.inv())

    W = sp.Matrix([[0, 7, -7, -1], [3, 0, -9, 9],
                   [1, -1, 0, 7], [-1, 5, 3, 0]])
    a = sp.Matrix([1, 2, 3, 5]); selected = []
    assert all(any(W[i, j] < 0 for i in range(4)) for j in range(4))
    for k in range(2, 5):
        for Jt in combinations(range(4), k):
            J = list(Jt); K = [i for i in range(4) if i not in J]
            T = W.extract(J, J)
            assert T.det() != 0
            h = T.inv() * a.extract(J, [0])
            w = W.extract(K, J) * h - a.extract(K, [0]) if K else sp.zeros(0, 1)
            if all(x > 0 for x in h) and all(x >= 0 for x in w):
                assert all(x > 0 for x in w)
                selected.append((list(J), int(sp.sign(T.det()))))
    assert selected == [([0, 1, 2], -1), ([1, 2, 3], -1), ([0, 1, 2, 3], 1)]
    assert sum(index for _, index in selected) == -1

    P = sp.Matrix([[0, 1, 0, 0], [0, 0, 1, 0],
                   [0, 0, 0, 1], [1, 0, 0, 0]])
    Pe = P - (sp.ones(4) - sp.eye(4)) / 20
    assert P.det() == -1 and all(x >= 0 for x in P.inv())
    assert Pe.det() < 0 and all(x > 0 for x in Pe.inv())
    return {"five_player_determinant": str(G5.det()),
            "six_player_determinant": str(G6.det()),
            "multibranch_supports_and_indices": selected,
            "weak_inverse_boundary_checked": True}


def check_negative_owner_compiler() -> dict[str, object]:
    # Two-player zero-sum table, delta=1/2. The zero-discount endpoint
    # q=(0,1/4) has negative sole-owner singleton -1/2.
    r = [[F(0), F(0)], [F(1), F(-1)],
         [F(1, 2), F(-1, 2)], [F(-1), F(1)]]
    h, p = F(1, 4), F(1, 100)
    T, L = 30, 100
    punishment = [[p, F(0)] for _ in range(L)]
    _, BP = finite_semantics(r, punishment)
    Qpun = F(-1, 2) + F(3, 2) * p
    assert BP[1] == Qpun == F(-97, 200)
    eta = F(3, 2) * p
    rows = [[F(0), h] for _ in range(T)] + punishment
    U, B = finite_semantics(r, rows)
    v = [F(1, 2), F(-1, 2)]
    survival = (1 - h) ** T
    assert all(abs(U[i] - v[i]) <= 2 * survival for i in range(2))
    assert B[1] <= v[1] + eta
    assert B[0] <= v[0] + 2 * survival
    E = max(B[i] - U[i] for i in range(2))
    assert E <= eta + 4 * survival
    for H in (100, 500, 5000):
        UH, BH = finite_semantics(r, rows, H)
        EH = max(BH[i] - UH[i] for i in range(2))
        assert EH <= E + F(2 * (len(rows) + 1), H)
        assert all(abs(UH[i] - U[i]) <= F(len(rows) + 1, H) for i in range(2))
    return {"negative_owner_tail_cap": str(BP[1]), "dates": len(rows),
            "terminal_exploitability_decimal": float(E),
            "finite_horizons_checked": [100, 500, 5000]}


def stationary_semantics(reward: Reward, q: Sequence[F]) -> tuple[list[F], list[F]]:
    n = len(q)
    C = F(1)
    for x in q:
        C *= 1 - x
    a = 1 - C
    if a <= 0:
        return [F(0)] * n, [max(reward[1 << i][i], F(0)) for i in range(n)]
    U, B = [], []
    for i in range(n):
        Q, H, alpha = endpoints(reward, q, i)
        U.append((q[i] * Q + (1 - q[i]) * H) / a)
        B.append(max(Q, H / (1 - alpha)) if alpha < 1
                 else max(reward[1 << i][i], F(0)))
    return U, B


def check_stationary_repair() -> dict[str, object]:
    rng = random.Random(190926)
    branches = {"all_deleted_clocks": 0, "nonpositive_owner": 0, "sole_owner_repair": 0}
    checks = 0
    for n in range(2, 7):
        for dominant in (False, True):
            for _ in range(20):
                q = ([F(1, 2)] + [F(1, rng.randrange(1000, 2000)) for _ in range(n - 1)]
                     if dominant else [F(rng.randrange(1, 10), 10) for _ in range(n)])
                C = F(1)
                for z in q:
                    C *= 1 - z
                a = 1 - C
                y = F(1, 10)
                lam = a * y * y
                d = 1 - lam
                reward = [[F(rng.randint(-5, 5)) for _ in range(n)]
                          for _ in range(1 << n)]
                # Fix the own singleton coordinate of each recipient so that
                # this literal q is an exact mixed discounted equilibrium.
                for i in range(n):
                    reward[1 << i][i] = F(0)
                    Q0, H, alpha = endpoints(reward, q, i)
                    reward[1 << i][i] = (H / (1 - d * alpha) - Q0) / alpha
                for i in range(n):
                    Q, H, alpha = endpoints(reward, q, i)
                    assert (1 - d * alpha) * Q - H == 0
                M = max(abs(z) for row in reward[1:] for z in row)
                assert M > 0
                V, B = stationary_semantics(reward, q)
                b = [1 - endpoints(reward, q, i)[2] for i in range(n)]
                theta = y / 2
                small = [i for i in range(n) if b[i] < theta * a]
                if not small:
                    p = q
                    branches["all_deleted_clocks"] += 1
                else:
                    k = small[0]
                    assert q[k] > (1 - theta) * a
                    if V[k] <= 0:
                        p = q
                        branches["nonpositive_owner"] += 1
                    else:
                        p = [F(0)] * n
                        p[k] = q[k]
                        branches["sole_owner_repair"] += 1
                Up, Bp = stationary_semantics(reward, p)
                E = max(Bp[i] - Up[i] for i in range(n))
                assert E <= M * (y * y + 2 * y)
                assert E <= 3 * M * y
                checks += 1
    assert all(v > 0 for v in branches.values())
    # Explicit rational discounted equilibrium approaching a negative sole owner.
    for den in (10, 20, 100, 1000):
        p = F(1, den)
        lam = (p + 3 * p * p) / (1 - 4 * p + 3 * p * p)
        q = [p, F(1, 4) + F(3, 4) * p]
        r = [[F(0), F(0)], [F(1), F(-1)],
             [F(1, 2), F(-1, 2)], [F(-1), F(1)]]
        assert 0 < lam < 1
        for i in range(2):
            Q, H, alpha = endpoints(r, q, i)
            assert (1 - (1 - lam) * alpha) * Q - H == 0
        U, B = stationary_semantics(r, q)
        assert B == [F(1, 2), F(-1, 2) + F(3, 2) * p]
        denominator = 1 + 6 * p - 3 * p * p
        assert B[0] - U[0] == 6 * p * p / denominator
        assert B[1] - U[1] == 3 * p * (1 - p) * (1 + 3 * p) / (2 * denominator)
    return {"stationary_repair_profiles": checks, "stationary_repair_branches": branches,
            "exact_signed_discount_families": 4}


def main() -> None:
    result = {"status": "all exact assertions passed",
              "scope": "Finite algebraic regressions, not a proof or Lean validation."}
    result.update(check_discount_algebra())
    result["ambient_linearization_coordinates"] = check_linearization()
    result.update(check_matrices())
    result.update(check_negative_owner_compiler())
    result.update(check_stationary_repair())
    out = Path(__file__).with_name("CARDINAL_FREE_LCP_INDEX_ESCAPE_CHECKS.json")
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
