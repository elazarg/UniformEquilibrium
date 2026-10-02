"""Exact checks for THREE_CYCLE_PASSIVE_INHERITANCE.md.

Dependencies: Python 3.10+ and sympy.
Run: python VERIFY_THREE_CYCLE_PASSIVE_INHERITANCE.py
The assertions are regression evidence, not a proof of the universal theorem.
No floating-point arithmetic is used for acceptance.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import combinations
import json
import random
from pathlib import Path
import sympy as sp


def matrix_certificate() -> dict:
    G = sp.Matrix([[0,-1,2,-2], [2,0,-1,1], [-1,2,0,1], [-1,2,2,0]])
    T = G[:3,:3]
    B = T.inv()
    w = G[3,:3] * B
    assert T.det() == 7 and G.det() == 3
    assert B == sp.Matrix([[2,4,1], [1,2,4], [4,1,2]]) / 7
    assert w == sp.Matrix([[8,2,11]]) / 7
    assert min(B) > 0 and min(w) > 0
    assert G.inv() == sp.Matrix([[2,2,2,-1], [5,2,8,-4],
                                [-4,-1,-7,5], [-8,-2,-11,7]]) / 3
    assert min(G.inv()) < 0 < max(G.inv())
    assert all(any(G[i,j] < 0 for i in range(4)) for j in range(4))
    inventory, admitted = [], []
    for size in range(2,5):
        for support in combinations(range(4), size):
            outside = [i for i in range(4) if i not in support]
            principal = G.extract(support, support)
            determinant = principal.det()
            assert determinant != 0
            h = principal.inv() * sp.ones(size,1)
            slack = G.extract(outside, support) * h - sp.ones(len(outside),1)
            accepted = all(x > 0 for x in h) and all(x >= 0 for x in slack)
            if accepted:
                assert all(x > 0 for x in slack)
                admitted.append((support, int(sp.sign(determinant))))
            inventory.append({"support":list(support), "det":str(determinant),
                              "h":list(map(str,h)), "outside_slack":list(map(str,slack)),
                              "admissible":accepted})
    assert admitted == [((0,1,2),1)]
    from itertools import permutations
    assert not any(all(G[p[k],p[(k+1)%4]] < 0 for k in range(4))
                   for p in permutations(range(4)))
    return {"matrix": [list(map(int,G.row(i))) for i in range(4)],
            "degree_from_regular_supports":1, "inventory":inventory}


def symbolic_rate_checks() -> int:
    A0,A1,A2 = sp.symbols('A0 A1 A2', positive=True)
    P = A0*A1*A2
    t = [(P-1)/(1+A1+A0*A1),
         (P-1)/(1+A2+A1*A2),
         (P-1)/(1+A0+A2*A0)]
    q = [x/(1+x) for x in t]
    c = [1-x for x in q]
    identities = [t[0]-A2*q[1], t[1]-A0*q[2], t[2]-A1*q[0],
                  c[0]*c[1]*c[2]-1/P]
    for expr in identities:
        assert sp.factor(expr) == 0
    return len(identities)


def prefix_values(reward:dict[int,list[F]], rows:list[tuple[int,F]], n:int=4):
    s = [reward[1<<i][i] for i in range(n)]
    U, B = [F(0)]*n, [max(F(0), x) for x in s]
    for j,h in reversed(rows):
        old_u, old_b = U[:], B[:]
        for i in range(n):
            if i == j:
                U[i] = h*s[i]+(1-h)*old_u[i]
                B[i] = max(s[i],old_b[i])
            else:
                rsolo = reward[1<<j][i]
                quitnow = (1-h)*s[i]+h*reward[(1<<i)|(1<<j)][i]
                U[i] = h*rsolo+(1-h)*old_u[i]
                B[i] = max(quitnow,h*rsolo+(1-h)*old_b[i])
    return U,B


def forward_cap(reward:dict[int,list[F]], rows:list[tuple[int,F]], i:int) -> F:
    """All displayed deadlines, the first late deadline, and Never."""
    s = reward[1<<i][i]
    accumulated, survival = F(0), F(1)
    deadlines = []
    for j,h in rows:
        if i == j:
            Q,H,beta = s,F(0),F(1)
        else:
            Q = (1-h)*s+h*reward[(1<<i)|(1<<j)][i]
            H = h*reward[1<<j][i]
            beta = 1-h
        deadlines.append(accumulated+survival*Q)
        accumulated += survival*H
        survival *= beta
    deadlines += [accumulated+survival*s, accumulated]
    return max(deadlines)


def finite_regressions() -> dict:
    rng = random.Random(20260909)
    G = [[0,-1,2,-2], [2,0,-1,1], [-1,2,0,1], [-1,2,2,0]]
    tested = 0
    max_rows = 0
    for case in range(48):
        s = [F(rng.randint(-24,24),4) for _ in range(4)]
        # All 44 nonsingleton coordinates are independently assigned, with both signs.
        reward = {mask:[F(rng.randint(-80,80),4) for _ in range(4)]
                  for mask in range(1,16)}
        for j in range(4):
            reward[1<<j] = [s[i]+G[i][j] for i in range(4)]
        M = max(F(1),*(abs(x) for row in reward.values() for x in row))
        v = [s[0],s[1]+1,s[2],s[3]+F(2,7)]
        for N,K in [(1,1),(3,2),(8,3),(13,4)]:
            # N equal unconditional pieces of a half-hazard phase.
            one_cycle = [(j,F(1,2*N-k)) for j in range(3) for k in range(N)]
            rows = one_cycle*K
            U,B = prefix_values(reward,rows)
            assert U == [(1-F(1,8)**K)*x for x in v]
            assert all(B[i] == forward_cap(reward,rows,i) for i in range(4))
            delta = F(1,N+1)
            bound = 2*M*delta+2*M*F(1,4)**K+M*F(1,8)**K
            assert all(F(0) <= B[i]-U[i] <= bound for i in range(4))
            # Check every microstage surplus in the infinite periodic solution.
            next_v = v[:]
            values = []
            for j,h in reversed(one_cycle):
                cur = [h*reward[1<<j][i]+(1-h)*next_v[i] for i in range(4)]
                assert cur[j] == s[j] == next_v[j]
                assert all(cur[i] >= s[i] for i in range(4))
                for i in range(4):
                    Q = s[i] if i == j else (1-h)*s[i]+h*reward[(1<<i)|(1<<j)][i]
                    assert Q-cur[i] <= 2*M*delta
                values.append(cur)
                next_v = cur
            assert next_v == v
            max_rows = max(max_rows,len(rows))
            tested += 1
    return {"signed_reward_tables":48, "finite_profiles":tested,
            "full_cap_scans":4*tested, "largest_calendar":max_rows,
            "checks":"exact fractions; every finite deadline plus late and Never"}


def main() -> None:
    result = {"matrix_certificate":matrix_certificate(),
              "symbolic_identities":symbolic_rate_checks(),
              "finite_regressions":finite_regressions(),
              "lean_checked":False}
    out = Path(__file__).with_name('THREE_CYCLE_PASSIVE_INHERITANCE_CHECKS.json')
    out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k!='matrix_certificate'},indent=2))

if __name__ == '__main__':
    main()
