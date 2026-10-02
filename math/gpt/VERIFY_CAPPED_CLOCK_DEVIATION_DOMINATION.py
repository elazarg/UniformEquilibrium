"""Exact regression checks for capped-clock outsider deviation domination.

Python 3.10+, standard library only. No floating-point acceptance.
Run: python VERIFY_CAPPED_CLOCK_DEVIATION_DOMINATION.py
The finite checks supplement, rather than prove, the universal theorem.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from typing import Callable
import json
import random

Clock = int | None  # None is Never, ordered after all finite dates.
Reward = dict[int, tuple[F, ...]]
Law = dict[Clock, F]
Weight = Callable[[Clock], F]
S = (0, 1, 2)
K = 3


def minimum(a: Clock, b: Clock) -> Clock:
    if a is None: return b
    if b is None: return a
    return min(a, b)


def outcome(clocks: tuple[Clock, ...], players: tuple[int, ...]):
    finite = [t for t in clocks if t is not None]
    if not finite: return None, 0
    t = min(finite)
    return t, sum(1 << i for i, x in zip(players, clocks) if x == t)


def value(r: Reward, clocks: tuple[Clock, ...], players: tuple[int, ...],
          who: int, f: Weight) -> F:
    t, A = outcome(clocks, players)
    return F(0) if A == 0 else f(t) * r[A][who]


def expected(r: Reward, laws: tuple[Law, ...], players: tuple[int, ...],
             who: int, f: Weight) -> F:
    result = F(0)
    for terms in product(*(list(law.items()) for law in laws)):
        mass = F(1)
        for _, p in terms: mass *= p
        if mass:
            result += mass * value(r, tuple(t for t, _ in terms), players, who, f)
    return result


def cap_debts(r: Reward, laws: tuple[Law, ...], players: tuple[int, ...], f: Weight):
    U = [expected(r, laws, players, i, f) for i in players]
    last = max((t for law in laws for t in law if t is not None), default=-1)
    # After last, a pure response only varies its weighted own-singleton term.
    # Its maximum is at the first late date or at Never, for every tested f.
    dates = tuple(range(last + 2)) + (None,)
    B = []
    for j, i in enumerate(players):
        B.append(max(expected(r, laws[:j] + ({t: F(1)},) + laws[j+1:],
                              players, i, f) for t in dates))
    assert all(b >= u for b, u in zip(B, U))
    return U, B, [b-u for b, u in zip(B, U)]


def slacks(r: Reward, lam: tuple[F, F, F]):
    s = tuple(r[1 << i][i] for i in range(4))
    result = {"Never": sum(lam[i]*s[i] for i in S) - s[K]}
    for A in range(1, 8):
        result[f"future_{A}"] = r[A][K] - s[K] - sum(
            lam[i]*(r[A][i]-s[i]) for i in S)
        result[f"join_{A}"] = sum(
            lam[i]*(r[A | (1 << i)][i] - r[A][i]) for i in S
        ) - (r[A | 8][K]-r[A][K])
    return result


def fixture() -> Reward:
    rows = {
      1:(1,4,0,0), 2:(4,1,0,0), 4:(0,0,1,4), 8:(0,0,4,1),
      3:(2,2,1,2), 5:(2,1,2,4), 9:(2,0,1,2),
      6:(0,2,2,4), 10:(1,2,0,2), 12:(1,1,2,2),
      7:(1,2,0,0), 11:(0,1,0,-1), 13:(0,0,0,1),
      14:(0,0,1,0), 15:(-1,-1,-1,-1)}
    return {A:tuple(map(F,row)) for A,row in rows.items()}


def test_fixture():
    r = fixture(); lam = (F(0), F(0), F(2))
    ss = slacks(r, lam)
    assert len(ss) == 15 and min(ss.values()) == 1
    G = [[r[1 << j][i]-r[1 << i][i] for j in range(4)] for i in range(4)]
    assert G == [[0,3,-1,-1],[3,0,-1,-1],[-1,-1,0,3],[-1,-1,3,0]]
    assert not any(i != j and G[i][j] <= 0 <= G[j][i]
                   for i in range(4) for j in range(4))
    pure_gaps = {}
    for A in range(1,16):
        clocks = tuple(0 if A & (1 << i) else None for i in range(4))
        laws = tuple({t:F(1)} for t in clocks)
        _, _, debt = cap_debts(r,laws,(0,1,2,3),terminal)
        pure_gaps[str(A)] = str(max(debt))
        assert max(debt) >= 1
    laws = ({0:F(1)}, {0:F(2,3),None:F(1,3)},
            {0:F(2,3),None:F(1,3)}, {None:F(1)})
    U,B,D = cap_debts(r,laws,(0,1,2,3),terminal)
    assert U == B == [F(13,9), F(2), F(2,3), F(4,3)]
    return {"raw_slacks":{k:str(v) for k,v in ss.items()},
            "pure_coalition_gaps":pure_gaps,
            "one_date_equilibrium_payoff":list(map(str,U))}


def terminal(t: Clock) -> F:
    return F(0) if t is None else F(1)


def horizon(H: int) -> Weight:
    # The live stage pays zero; absorption reward starts one stage later.
    return lambda t: F(0) if t is None else F(max(0,H-t-1),H)


def discount(t: Clock) -> F:
    return F(0) if t is None else F(2,3)**(t+1)


def make_certified(rng: random.Random, lam: tuple[F,F,F]) -> Reward:
    r = {A:[F(rng.randrange(-8,9),2) for _ in range(4)] for A in range(1,16)}
    s = [r[1 << i][i] for i in S]
    sK = sum(lam[i]*s[i] for i in S)-F(rng.randrange(1,5),2)
    r[8][3] = sK
    for A in range(1,8):
        r[A][3] = sK+sum(lam[i]*(r[A][i]-s[i]) for i in S)+F(rng.randrange(1,5),2)
        r[A|8][3] = r[A][3]+sum(lam[i]*(r[A|(1<<i)][i]-r[A][i]) for i in S)-F(rng.randrange(1,5),2)
    result = {A:tuple(row) for A,row in r.items()}
    assert min(slacks(result,lam).values()) > 0
    return result


def pathwise(r: Reward, lam, clocks, t: Clock, f: Weight):
    parent0 = value(r,clocks+(None,),S+(K,),K,f)
    parent1 = value(r,clocks+(t,),S+(K,),K,f)
    rhs = F(0)
    for j,i in enumerate(S):
        original = value(r,clocks,S,i,f)
        altered = clocks[:j]+(minimum(clocks[j],t),)+clocks[j+1:]
        rhs += lam[j]*(value(r,altered,S,i,f)-original)
    assert parent1-parent0 <= rhs


def cap_law(law: Law, deadline: Law) -> Law:
    result: Law = {}
    for t,p in law.items():
        for u,q in deadline.items():
            v = minimum(t,u)
            result[v] = result.get(v,F(0))+p*q
    assert sum(result.values()) == 1
    return result


def random_law(rng: random.Random) -> Law:
    atoms = (0,1,2,None)
    weights = [rng.randrange(0,6) for _ in atoms]
    if not sum(weights): weights[0]=1
    return {t:F(w,sum(weights)) for t,w in zip(atoms,weights) if w}


def regressions():
    rng = random.Random(20260909)
    fs = [terminal,discount,horizon(1),horizon(3),horizon(9)]
    counts = {"signed_tables":0,"pathwise_inequalities":0,
              "full_cap_transfers":0,"randomized_deviation_compilations":0}
    for case in range(16):
        lam = tuple(F(rng.randrange(0,6),2) for _ in S)
        r = make_certified(rng,lam)
        counts["signed_tables"] += 1
        for clocks in product((0,1,2,None),repeat=3):
            for t in (0,1,2,3,None):
                for f in fs:
                    pathwise(r,lam,clocks,t,f)
                    counts["pathwise_inequalities"] += 1
        laws = tuple(random_law(rng) for _ in S)
        deadline = random_law(rng)
        for f in fs:
            U,B,d = cap_debts(r,laws,S,f)
            Up,Bp,dp = cap_debts(r,laws+({None:F(1)},),S+(K,),f)
            assert Up[:3] == U and Bp[:3] == B
            assert dp[3] <= sum(lam[i]*d[i] for i in S)
            counts["full_cap_transfers"] += 1
            lhs = expected(r,laws+(deadline,),S+(K,),K,f)-Up[3]
            rhs = F(0)
            for i in S:
                capped = cap_law(laws[i],deadline)
                changed = laws[:i]+(capped,)+laws[i+1:]
                rhs += lam[i]*(expected(r,changed,S,i,f)-U[i])
            assert lhs <= rhs
            counts["randomized_deviation_compilations"] += 1
    return counts


def boundary_tests():
    # Pure-clock tests recover every one of the 15 inequalities exactly.
    rng = random.Random(19)
    r = make_certified(rng,(F(1,2),F(1),F(2)))
    lam = (F(1,2),F(1),F(2))
    def residual(clocks,t):
        lhs = value(r,clocks+(t,),S+(K,),K,terminal)-value(r,clocks+(None,),S+(K,),K,terminal)
        rhs = sum(lam[i]*(value(r,clocks[:i]+(minimum(clocks[i],t),)+clocks[i+1:],S,i,terminal)
                              -value(r,clocks,S,i,terminal)) for i in S)
        return rhs-lhs
    ss = slacks(r,lam)
    assert residual((None,None,None),0) == ss['Never']
    for A in range(1,8):
        assert residual(tuple(1 if A&(1<<i) else None for i in S),0) == ss[f'future_{A}']
        assert residual(tuple(0 if A&(1<<i) else None for i in S),0) == ss[f'join_{A}']
    return {"exact_necessity_tests":15}


def positive_singleton_relaxation():
    rng = random.Random(812)
    tested = 0
    for _ in range(20):
        lam = (F(1,2),F(0),F(3,2))
        base = make_certified(rng,lam)
        r = {A:list(row) for A,row in base.items()}
        r[1][0] = F(1)  # A fixed positive child own singleton.
        s = [r[1<<i][i] for i in S]
        sk = sum(lam[i]*s[i] for i in S)+F(1)
        r[8][3] = sk
        for A in range(1,8):
            r[A][3] = sk+sum(lam[i]*(r[A][i]-s[i]) for i in S)+F(1)
            r[A|8][3] = r[A][3]+sum(lam[i]*(r[A|(1<<i)][i]-r[A][i]) for i in S)-F(1)
        r = {A:tuple(row) for A,row in r.items()}
        raw = slacks(r,lam)
        assert raw['Never'] == -1
        assert all(v>=0 for label,v in raw.items() if label!='Never')
        laws = tuple(random_law(rng) for _ in S)
        _,_,d = cap_debts(r,laws,S,terminal)
        _,_,dp = cap_debts(r,laws+({None:F(1)},),S+(K,),terminal)
        never = F(1)
        for law in laws: never *= law.get(None,F(0))
        assert d[0] >= never
        assert dp[3] <= sum(lam[i]*d[i] for i in S)+never
        assert dp[3] <= sum(lam[i]*d[i] for i in S)+d[0]
        tested += 1
    return {"fourteen_row_transfers_without_Never_constraint":tested}


def unchanged_child_no_go_duals():
    # The attached unchanged-child obstruction has a one-row Farkas
    # certificate against each of these raw deletion LPs.
    r = {}
    for A in range(1,16):
        a = [bool(A&(1<<i)) for i in range(4)]
        r[A] = tuple(map(F,(1 if a[0] else 2*int(a[2]),
                            (2*int(a[0])-1)*int(a[1]),
                            (2*int(a[1])-1)*int(a[2]),int(a[3]))))
    result = []
    for k in range(4):
        child = tuple(i for i in range(4) if i!=k)
        if k==0:
            A=8
            v=[r[1<<i][i]-r[A][i] for i in child]
            b=r[1<<k][k]-r[A][k]
            label='future_{3}'
        else:
            A=sum(1<<i for i in child)
            v=[r[A|(1<<i)][i]-r[A][i] for i in child]
            b=r[A|(1<<k)][k]-r[A][k]
            label='join_full_child'
        assert all(x<=0 for x in v) and b>0
        result.append({"omitted":k,"row":label,"child_coefficients":list(map(str,v)),
                       "positive_outside_gain":str(b)})
    return result


def main():
    result = {"status":"exact finite regression evidence; not Lean checked",
              "fixture":test_fixture(),"regressions":regressions(),
              "boundary_tests":boundary_tests(),
              "positive_singleton_relaxation":positive_singleton_relaxation(),
              "no_go_duals":unchanged_child_no_go_duals()}
    target = Path(__file__).with_name('CAPPED_CLOCK_DEVIATION_DOMINATION_CHECKS.json')
    target.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))

if __name__ == '__main__': main()
