# A four-player quitting game requiring four simultaneous movers in period two

Use independent behavioral quitting hazards, finite real rewards at the first nonempty exit, and zero live and joint Never payoffs. Write s_i for the own singleton reward and Z_i(T)=r_i(T)−s_i for native exit rewards. For a player facing independent opponent hazards, write H for the probability no opponent quits, P for the expected native exit payoff when waiting, with a contribution of zero at the empty event, and Q for the expected native payoff when quitting. A mover is a player with positive hazard.

Take the baseline with singleton matrix

    G = [ 0 −1 −1  5; −5 0 2 −1; −2 4 0 −5; 3 −4 2 0 ].

Writing q for the hazard vector of a date and g=Gq, take P_i=g_i and Q_i=−g_i for i=1,2,3. In row zero take P_0=g_0+160q_2q_3 and Q_0=−g_0+40q_1(1−q_2). These polynomials determine all native entries. A common positive bump adds η to each participant reward in each nonsingleton coalition. It increases Q_i by η(1−H_i) and leaves all P_i fixed.

**Theorem.** Assume that every native entry of the game differs by at most 1/2048 from the baseline, and that Z_2(T)+Z_2(T∪{2})>0 on each nonempty subset T of the three opponents of player 2. The original game has an exact period-two terminal Nash equilibrium with movers 02 in the first phase and 0123 in the second. It supplies a fixed original uniform payoff for arbitrary signed own levels.

For the lower bound, take positive own levels and require the same strict sum inequalities in all four rows. In a sufficiently small open neighborhood of the baseline intersected with those restrictions, every exact period-two terminal Nash equilibrium has a date with all four movers, and the minimum total number of positive player-date hazards in a period is exactly six. This class is nonempty in every sufficiently small baseline neighborhood, as witnessed by common positive bumps. The neighborhood size for this lower bound is qualitative. For common positive bumps up to 1/10000 and own levels one, every stretch of dates with at most two movers in a proper exact equilibrium has total hazard at most 254804. In particular a proper equilibrium cannot have at most two movers on every sufficiently late date, even with an aperiodic calendar. For all sufficiently small positive bumps, the same conclusion covers every exact terminal Nash profile because a reachable sure date is then impossible.

On that all-row open class, the games escape the two-unrestricted-recipient raw implication for every assignment of the scheduled rows. In each row the singleton signs include both signs. Join a pure positive-supplier axis point to a pure negative-supplier axis point in the proper opponent cube without passing through the origin. Along this path P crosses zero at a point where Q>0 by the strict sum inequalities. With the two scheduled opponents quiet and these three hazards at the passive date, the old test gives A=P=0 and B=−(1−H)Q<0. For the joint stationary joining test, the baseline vector (41/150,191/300,289/300,9/25) has each g_i=1/5. Here P_0=6961/125 and Q_0=1651/2250. All four P_i are strictly positive and all four Q_i−P_i strictly negative. The strict comparisons persist nearby. The two distinct signs on each row's axes also obstruct both uniform stationary surface sign tests for every surface H_i=d in (0,1), since on each singleton axis the corresponding Q has the opposite strict sign to P. The proportional additive baseline rows make this immediate, and row zero has the same opposite strict signs on its negative supplier 1 and its positive supplier 3.

## Exact continuation calendar and perturbation proof

For each of two phases v,w let

    B_iv=P_iv+H_iv P_iw−(1−H_iv H_iw)Q_iv.

When D_i=1−H_iv H_iw>0, the value of Never at v is (P_iv+H_iv P_iw)/D_i. If all B_iv≥0 and they vanish whenever i moves, the Never values satisfy the two policy recursions including every mixture. Every quit offer is bounded by that continuation value. Geometric absorption under each unilateral replacement follows if every player faces an opponent acting with positive probability each period. Bellman iteration gives optimality against every unilateral law, including Never. The uniform geometric bound makes the long finite-horizon payoff and deviation comparisons converge uniformly. All terminal outcomes add the same s_i in the original game.

List the six allowed hazards in temporal order. The first phase has two coordinates q_0,q_2 and the other four coordinates belong to the second phase. Write J for their indices in the flattened two-date calendar. Use f=B_J, M=(Df(c))^(-1) and the box ||x−c||∞≤r. The following bounds use exact rational polynomial arithmetic.

    c=(0,82431479,14930574,33242022,26138181,20621388)/10^8,
    J=(0,2,4,5,6,7),     r=1/1000,
    ||M||∞ < 0.654,             ||M f(c)||∞ < 0.000000004,
    sup ||I−M Df||∞ < 0.020,  inf min(B_1,first,B_3,first) > 3.061.

For the fixed-point step allow the component t=q_0A to have either sign. At most one hazard is negative, by at most r, and it is in phase A. The absolute weights of the interpolated payout table in that phase sum to at most 1+2r, while H_iA≤1+r and |1−H_iA H_iB|≤1. Thus every residual perturbation has absolute value at most 3.01δ in the whole box. For the perturbed active residual f_new the continuous map x↦x−M f_new(x) maps the box strictly into itself for δ≤1/2048, since 4·10^(−9)+0.020r+0.654·3.01/2048<r. Brouwer supplies an active root. Both omitted inequalities remain strict because their perturbation is at most 3.01/2048.

At its root, the indifference equations of row 2 give V_2v=Q_2v=P_2v+H_2v V_2w even throughout the signed box. The phase-B hazards give D_2>0 even when t is negative. Write J_2=Z_2(02)>0 and g_2=Z_2(0)<0. The first-date identities give V_2A=J_2 t and V_2B=(J_2−g_2)t/(1−t). The second-date identity then reads

    P_2B+Q_2B=t[2(J_2−g_2)/(1−t)−H_2B J_2].

The bracket is strictly positive throughout the box. The phase-B hazards are in the proper cube, so the strict sum hypothesis in row 2 implies P_2B+Q_2B>0. Hence t>0 and the six-player-date solution is a genuine proper equilibrium. In fact strict positivity is needed only for this single row on the indicated phase-B box.

For reproducibility, substitute x=c+u in the six active polynomials. For any resulting polynomial p define N(p)=sum_m |p_m|r^|m| over its monomials. Take the maximum over rows i of the sum over k of N((I−M Df)_(ik)). Bound each omitted polynomial below by B_j(c)−N(B_j−B_j(c)). The exact verification below uses Python and SymPy's rational polynomial ring.

```python
import sympy as s
from sympy.polys.rings import ring
from sympy import QQ
R,*u=ring('u0,u1,u2,u3,u4,u5',QQ)
c=[QQ(n,10**8) for n in [0,82431479,14930574,33242022,26138181,20621388]];r=QQ(1,1000)
v=[uc+h for uc,h in zip(c,u)];A=[v[0],R.zero,v[1],R.zero];C=v[2:]
G=[[0,-1,-1,5],[-5,0,2,-1],[-2,4,0,-5],[3,-4,2,0]]
from math import prod
P=[];Q=[];H=[]
for t in [A,C]:
 for i in range(4):
  p=sum(G[i][j]*t[j] for j in range(4));q=-p
  if i==0:p+=160*t[2]*t[3];q+=40*t[1]*(1-t[2])
  P.append(p);Q.append(q);H.append(prod(1-t[j] for j in range(4) if j!=i))
B=[P[j]+H[j]*P[k]-(1-H[j]*H[k])*Q[j] for j,k in ((j,(j+4)%8) for j in range(8))]
J=[0,2,4,5,6,7];f=[B[j] for j in J];D=[[b.diff(g) for g in u] for b in f]
def mag(p):return sum(abs(a)*r**sum(m) for m,a in p.items())
M=s.Matrix([[p.get((0,)*6,0) for p in row] for row in D]).inv()
rows=[[QQ.convert(M[i,j]) for j in range(6)] for i in range(6)]
disp=max(abs(sum(w*b.get((0,)*6,0) for w,b in zip(row,f))) for row in rows);norm=max(sum(abs(w) for w in row) for row in rows)
L=max(sum(mag(int(i==k)-sum(w*d[k] for w,d in zip(row,D))) for k in range(6)) for i,row in enumerate(rows))
slack=min(B[j].get((0,)*6)-mag(B[j]-B[j].get((0,)*6)) for j in [1,3])
assert norm<QQ(654,1000) and disp<QQ(4,10**9)
assert L<QQ(20,1000) and slack>QQ(3061,1000)
```

## Why a full date is needed

Argue by contradiction along strict-sum tables converging to the baseline with no four-mover date in their proposed exact calendars. A phase reached with positive probability inherits unilateral optimality after that history. Every owner's original upper punishment value equals s_i. Constant independent hazard 1/2 absorbs almost surely and each date's native contribution is (P_i+Q_i)/2≥0, while all-Never opponents give the converse since s_i>0. At a reached phase the prescribed continuation thus earns at least s_i. If a sure phase occurs, use the first such phase. Each player facing a sure rival compares immediate offers, and a sole sure owner can withdraw and then guarantee s_i against the actual future opponents. This gives a sure-quitter head with the native punishment continuation zero. Its closed inequalities pass to a sure head at the baseline. The exact census below excludes all such heads. Thus all phases are reached and all hazards are proper for large indices. The same reasoning rules out convergence of proper hazards to a sure date. At each proper date the realized continuation is at least s_i, and its native value is bounded. For a player facing a sure rival in the limit the continuation multiplier vanishes. For a sole sure player, an actually positive hazard gives indifference and permits replacing the bounded next-phase value below by native zero. The limiting head again contradicts the census. With at least two recurring owners, geometric absorption under continuation bounds native values by the largest absolute native entry, independently of the own levels.

For a proper calendar, all quiet gives original payoff zero while quitting earns s_i>0. A sole recurring owner j cannot be an equilibrium. Some other owner i has strictly negative native singleton reward against j; i's prescribed payoff therefore falls below s_i, contradicting security. With at least two recurring owners every player faces geometric opponent absorption, and its strict-sum security continuation at each phase is strictly positive in native units. In fact some reached opponent exit has positive probability, and the constant-half strategy has strictly positive native contribution there. A solitary mover's forced Quit would pay native zero, which excludes that date type. A blank date may be deleted. If one of the two dates is blank this gives a stationary equilibrium on the remaining date. The terminal Never and infinite-deadline values are unchanged, and the one-date Bellman inequalities on the nonblank phase give stationary optimality. Such a sequence approaching the baseline is impossible. A nonzero proper limiting stationary profile satisfies the continuous Never comparison numerators and gives native Nash when at least two owners act. A sole positive owner is excluded by an outside negative singleton. Sure limits were already excluded. If the hazards vanish, normalize them by their total. First-order expansion gives a nonzero homogeneous complementary vector of G. That G is R0 follows from invertibility of every nonsingleton principal block and a negative entry in each column. Thus we may use two nonblank dates each having at least two movers.

For completeness the finite check below first verifies all three baseline facts. It checks the principal determinants and negative singleton columns for R0. A sure head satisfies Q_i−P_i≥0 at sure players, equality at proper movers and Q_i−P_i≤0 at quiet players, using zero native punishment in the sole-sure case. In a nonzero proper stationary equilibrium the comparison is P_i−(1−H_i)Q_i≥0 with equality at positive hazards. For rows 1,2,3 this is a positive multiple of (Gq)_i in the stationary test, and the head uses the same signs since P_i−Q_i=2(Gq)_i. For each status assignment the code eliminates the active ordinary rows by linear equations and checks the remaining exact polynomial inequalities.

For a two-mover date, both players need positive expected forced offers, which have the signs of their participant entries against the mate. The only possibilities near the baseline are 01,02,13. Triple 023 is impossible because in row 3 all three forced entries against the nonempty subsets of {0,2} are strictly negative. Hence the six phase masks, encoded by bit 2^i for owner i, are 3,5,10,7,11,14. After a subsequence the two masks are constant. Pass to a limit x of their hazards. The inequalities B_iv≥0 and B_iv=0 for the active mask coordinates pass to the limit, even when a formerly active hazard vanishes. All phase P_iA+P_iB≥0 as well. Indeed before taking limits, proper play makes Continue optimal and V_iv=P_iv+H_iv V_iw. Summation yields (1−H_iB)V_iA+(1−H_iA)V_iB≥0. Q_iv≥0 for a mask-active owner since it equals the nonnegative value. No nonzero hazard can lie outside the two masks. If the entire calendar vanishes, divide the B comparisons by the sum of all eight hazards. They are uniformly (G(q_A+q_B))_i plus o(sum q), including varying rewards. Thus the sum of the two normalized phases gives a nonzero, nonnegative complementary vector of G, again impossible. We have a nonzero proper point in one of 21 closed support systems.

Here is the full system for any unordered pair of masks. Outside the masks put q_iv=0. Inside allow 0≤q_iv<1, with the total over both phases positive. Impose B_iv≥0 everywhere, equality and Q_iv≥0 on every mask-active choice, and P_iA+P_iB≥0 for each i. If an ordinary owner i=1,2,3 belongs to both masks we may add P_iA=P_iB=0. Indeed its equality B_iv=(2−H_iA H_iB)P_iv+H_iv P_iw=0 in both phases has strictly positive determinant whenever D_i>0. At D_i=0 neither phase has opponents of i and both passive offers already vanish. The following complete exact rational decision eliminates those linear equalities first. The upper triangle of results in mask order 3,5,10,7,11,14 is entirely unsatisfiable. This is computer-assisted ordinary mathematics. The code uses SymPy and the QF_NRA decision procedure in z3-solver. A run returning unknown fails the assertion.

```python
import itertools
import sympy as s
import z3
M=s.Matrix([[0,-1,-1,5],[-5,0,2,-1],[-2,4,0,-5],[3,-4,2,0]])
X=s.symbols('x0:8'); menu=[3,5,10,7,11,14]
def solve(ma,mb):
  t=[[X[4*d+i] if m>>i&1 else s.S(0) for i in range(4)] for d,m in enumerate((ma,mb))]
  active=[4*d+i for d,m in enumerate((ma,mb)) for i in range(4) if m>>i&1]
  pv=[M*s.Matrix(row) for row in t];com=ma&mb
  common=[4*d+i for d in (0,1) for i in [1,2,3] if com>>i&1]
  eq=[pv[j//4][j%4] for j in common]
  variables=[X[j] for j in active];sol=next(iter(s.linsolve(eq,variables)),variables) if eq else variables;dct=dict(zip(variables,sol))
  t=[[x.subs(dct) for x in row] for row in t];vs=sorted(set().union(*(x.free_symbols for row in t for x in row)),key=str)
  z=[z3.Real(str(v)) for v in vs];ps=[];qs=[];hs=[]
  for row in t:
   ps0=M*s.Matrix(row); qs0=-ps0;ps0[0]+=160*row[2]*row[3];qs0[0]+=40*row[1]*(1-row[2]);ps.extend(ps0);qs.extend(qs0)
   hs.extend(s.prod(1-row[j] for j in range(4) if j!=i) for i in range(4))
  B=[ps[j]+hs[j]*ps[k]-(1-hs[j]*hs[k])*qs[j] for j,k in ((j,(j+4)%8) for j in range(8))]
  def expr(e):
   if not vs:return z3.RealVal(str(e))
   poly=s.Poly(e,*vs);den,p=poly.clear_denoms()
   return sum(int(a)*sprod(v**k if k>1 else v for v,k in zip(z,m) if k) for m,a in p.terms())
  sl=z3.SolverFor('QF_NRA')
  g=[expr(f) for row in t for f in row];sl.add([x>=0 for x in g]);sl.add([expr(1-x)>0 for row in t for x in row]);sl.add(sum(g)>0)
  for j in range(4):sl.add(expr(ps[j]+ps[j+4])>=0)
  for j in range(8):
    eqB=expr(B[j]);sl.add(eqB==0 if j in active else eqB>=0)
    if j in active:sl.add(expr(qs[j])>=0)
  ret=sl.check()
  assert ret==z3.unsat, (ma,mb,ret)
def sprod(xs):
 r=1
 for x in xs:r*=x
 return r
def baseline_checks():
    assert all(M.extract(v,v).det()!=0 for k in (2,3,4)
               for v in itertools.combinations(range(4),k))
    assert all(min(M[:,i])<0 for i in range(4))
    zero,one=s.S(0),s.S(1)
    for head in (True,False):
        for status in itertools.product((0,1,2) if head else (0,1),repeat=4):
            if (head and 2 not in status) or not any(status): continue
            q=[(zero,X[i],one)[k] for i,k in enumerate(status)]
            variables=[X[i] for i,k in enumerate(status) if k==1]
            p=M*s.Matrix(q)
            eq=[p[i] for i in range(1,4) if status[i]==1 and p[i]!=0]
            if eq:
                if not variables: continue
                sol=s.linsolve(eq,variables)
                if sol==s.EmptySet: continue
                sub=dict(zip(variables,next(iter(sol))))
                q=[g.subs(sub) for g in q];p=M*s.Matrix(q)
            z=[z3.Real(str(g)) for g in X[:4]]
            def convert(g):
                poly=s.Poly(g,*X[:4]);den,p0=poly.clear_denoms()
                return sum(int(a)*sprod(x**k for x,k in zip(z,m) if k) for m,a in p0.terms())
            sl=z3.SolverFor('QF_NRA')
            for i,k in enumerate(status):
                if k==1: sl.add(convert(q[i])>0,convert(1-q[i])>0)
            raw=p[0];Q=-raw+40*q[1]*(1-q[2]);P=raw+160*q[2]*q[3]
            p[0]=P-Q if head else P-(1-s.prod(1-w for w in q[1:]))*Q
            for i,k in enumerate(status):
                a=convert(p[i]);sl.add((a>=0,a==0,a<=0)[k])
            assert sl.check()==z3.unsat,(head,status)

if __name__=='__main__':
 baseline_checks()
 for a,b in itertools.combinations_with_replacement(menu,2):solve(a,b)
```

For example, the five-variable case 02|013 also has a short scalar contradiction. Write A=(u,0,y,0), B=(v,x,0,z). If y=1 this was already a sure case. Owner 0 indifference on both dates gives

    2y/(1−y)=41x−5z,    (1−x)(1−z)y=42x−10z.

If x>0 and 5z≤4x, the second equality gives y≥34x, contrary to the first equality's 2y≤41x. Thus 5z>4x, making P_2A+P_2B=−2u−2v+4x−5z negative. If x=0 the equations imply y=z=0 and the same sum constraint forces u=v=0. Either outcome contradicts the census conditions. The full test allows both masks to lose any of their active hazards at the limit. Consequently its emptiness proves the stated open-neighborhood exclusion by compactness.

## Every proper exact equilibrium needs a date with at least three movers

In the shifted two-free-row calibration above, take own levels one and
0<δ≤1/10000, where δ denotes the common participant bump. The following applies to every exact terminal Nash profile
in which all reached hazards are strictly below one. The dates can be
nonperiodic and may have arbitrarily small hazards.

At every date an owner can guarantee strictly more than its own level
if a rival has a positive hazard at that or a later date. Indeed its
constant-hazard 1/2 deviation absorbs almost surely. Its conditional
expected native absorbing contribution is (P_i+Q_i)/2, strictly
positive whenever a rival hazard is positive. In the three additive
rows this is δ(1−H_i)/2. Row 0 has the extra nonnegative term
80q_2q_3+20q_1(1−q_2). Every fixed date is reached with positive
probability under either profile. No suffix can have just one owner
ever active, because an outsider with negative singleton comparison
against that owner earns less than its own level both on that exit and
on Never. Such an outsider exists in each column. An all-quiet suffix
fails immediately. Tail optimality therefore gives strictly positive
native values V_i(t), where V is the original conditional payoff minus
the own level. A mover at a solo date would earn zero from its Quit
action. Thus there are no solo dates. Delete blank dates, which leave
the values untouched.

At every remaining date with exactly two movers, their joining
entries must both be positive because the active forced offers are
V_i=J_ij q_j. The only pairs are A=01, B=02 and C=13. On these dates
the passive offer is (Γq)_i (the exceptional q_2q_3 term vanishes).
Every player continues with positive probability, so

    V_i(t)=(Γq(t))_i+H_i(t)V_i(t+1).

The sum of all hazards on any infinite suffix of the equilibrium calendar diverges. Otherwise tail exit
probabilities would approach zero by the union bound, giving original
continuation payoffs tending to zero whereas immediate quitting tends
to the own level one.

For these bumped tables with s_i=1 all native exit rewards and the native Never payoff −1 are bounded above rowwise by M=(164,7,8,5), by direct substitution in the four expected payoff polynomials at all pure opponent subsets. Thus 0<V_i(t)≤M_i on every reached date, including on a pair-only interval of a more general exact calendar.

A linear potential now bounds total hazard uniformly in time. Its five
integer rows and the small exact checks below are included to make the
finite inequalities reproducible. Encode the state at a letter e={a,b}
(a<b) by y=(q_a,q_b,V_c,V_d), where c<d are the quiet players. Denote
by v_i its native value with the unshifted forced offer substituted at
active owners. This gives v_a=J^0_ab q_b, v_b=J^0_ba q_a, v_c=V_c, v_d=V_d,
where J^0_ij=−Γ_ij+40·1_((i,j)=(0,1)). Write m_a=q_b,m_b=q_a,
m_c=m_d=0, so the true values are v_i+δm_i. Let q_i=0 for quiet
owners. On a transition e to f, use primes for the second state and
set D=1/10000. The following are homogeneous linear inequalities in
the eight entries z=(y,y').

    y,y'≥0;
    v_i−Σ_j J^0_ij q_j≥0 for quiet i, on both dates;
    v'_i−v_i+(Γq)_i+D m'_i≥0 for all i;
    v_i−v'_i−(Γq)_i+M_i Σ_(j≠i) q_j+D m_i≥0 for all i.

The quiet forced offer equals the indicated unshifted sum plus the
nonnegative bump. For the dynamic inequalities use
0≤V'_i−V_i+(Γq)_i=(1−H_i)V'_i≤M_i Σ_(j≠i)q_j and 0<δ≤D.

For the current and next letter use the row

    AA, AC    (−25979,−56677,−344,0)
    AB        (−9315,−63342,−2011,0)
    BA,BB,BC  (−4022,−1700,−530,0)
    CA, CC    (0,−5196,−1382,−344)
    CB        (−20,−504,−1483,−1383).

For every triple e,f,g the permitted transitions just listed satisfy

    Y_ef y − Y_fg y' ≥ q_a+q_b.                              (*)

One reproducible rational check numbers the cone rows 0–19 as follows:
the two quiet constraints at e in increasing quiet-player order, the
two at f likewise, the four lower dynamics by increasing owner, the four
upper dynamics by owner, and the eight coordinate nonnegativity rows.
For e,f,g in lexicographic order A<B<C, take the rows whose zero-based
bits are set in the corresponding integer:

    67824,262516,67824,393332,393332,393332,131318,786556,131318,
    344176,344176,344176,196720,196720,196720,917616,786556,917616,
    18808,278643,18808,100473,100473,100473,67952,524535,67952.

In each of the 27 cases the coefficient vector of (*) minus its right
side is an exact nonnegative combination of the selected rows. The following rational Gaussian elimination on the transposed selected rows verifies all 27 nonnegative combinations.

```python
"""Verify the 27 one-date certificates for every common shift in [0, 1/10000]."""

from fractions import Fraction
from itertools import product

GAMMA = ((0, -1, -1, 5), (-5, 0, 2, -1), (-2, 4, 0, -5), (3, -4, 2, 0))
PAIRS = ((0, 1), (0, 2), (1, 3))
CAP = (164, 7, 8, 5)
AA = (-25979, -56677, -344, 0)
AB = (-9315, -63342, -2011, 0)
BA = (-4022, -1700, -530, 0)
CA = (0, -5196, -1382, -344)
CB = (-20, -504, -1483, -1383)
POTENTIAL = ((AA, AB, AA), (BA, BA, BA), (CA, CB, CA))
MASKS = (
    67824, 262516, 67824, 393332, 393332, 393332, 131318, 786556, 131318,
    344176, 344176, 344176, 196720, 196720, 196720, 917616, 786556, 917616,
    18808, 278643, 18808, 100473, 100473, 100473, 67952, 524535, 67952,
)


def state(pair, shift):
    a, b = PAIRS[pair]
    outsiders = sorted(set(range(4)) - {a, b})
    join = [[-g + 40 * (i == 0 and j == 1) for j, g in enumerate(row)]
            for i, row in enumerate(GAMMA)]
    value = [[0] * 4 for _ in range(4)]
    value[a][1] = join[a][b] + shift
    value[b][0] = join[b][a] + shift
    for col, i in enumerate(outsiders, start=2):
        value[i][col] = 1
    gaps = [[-join[i][a], -join[i][b], *value[i][2:]] for i in outsiders]
    passive = [[row[a], row[b], 0, 0] for row in GAMMA]
    exposure = [[int(i != a), int(i != b), 0, 0] for i in range(4)]
    return value, gaps, passive, exposure


def constraints(pair, successor, first_shift, second_shift):
    value, gaps, passive, exposure = state(pair, first_shift)
    after, next_gaps, _, _ = state(successor, second_shift)
    rows = [g + [0] * 4 for g in gaps] + [[0] * 4 + g for g in next_gaps]
    for i in range(4):
        rows.append([p - v for p, v in zip(passive[i], value[i])] + after[i])
    for i in range(4):
        rows.append([v - p + CAP[i] * x for v, p, x in zip(value[i], passive[i],
                                                            exposure[i])]
                    + [-v for v in after[i]])
    return rows


def check_cone(rows, mask, target):
    vectors = [v for k, v in enumerate(rows) if (mask >> k) & 1]
    n = len(vectors)
    system = [list(map(Fraction, row)) for row in zip(*vectors, target)]
    for col in range(n):
        pivot = next(k for k in range(col, 8) if system[k][col])
        system[col], system[pivot] = system[pivot], system[col]
        system[col] = [x / system[col][col] for x in system[col]]
        for k in range(8):
            if k != col:
                m = system[k][col]
                system[k] = [x - m * y for x, y in zip(system[k], system[col])]
    weights = [system[k][-1] for k in range(n)]
    assert all(c >= 0 for c in weights)
    assert all(sum(w * v[j] for w, v in zip(weights, vectors)) == target[j]
               for j in range(8))


def main():
    shifts = (Fraction(0), Fraction(1, 10000))
    for mask, (e, f, g) in zip(MASKS, product(range(3), repeat=3), strict=True):
        endpoint_rows = [constraints(e, f, s, t) for s, t in product(shifts, repeat=2)]
        rows = [[max(column) for column in zip(*r)] for r in zip(*endpoint_rows)]
        rows += [[int(i == j) for j in range(8)] for i in range(8)]
        target = list(POTENTIAL[e][f]) + [-x for x in POTENTIAL[f][g]]
        target[0] -= 1
        target[1] -= 1
        check_cone(rows, mask, target)
    print("Verified all 27 rational cone certificates.")


if __name__ == "__main__":
    main()
```

Sum (*) on successive nonblank dates. Every potential is between −254800 and zero by the five displayed rows and the bounds (1,1,M_c,M_d) on the state. On any finite sequence of pair dates with no intervening date having three or four movers, (*) applies up to two dates before the endpoint. The last two dates contribute at most four more hazard units. Hence every such interval has total hazard at most 254804. An eventual pair-only calendar therefore has a finite tail hazard sum,
contradicting the divergence already proved. This excludes all proper
pair-only equilibria, including all nonperiodic behavioral profiles in
that class. It also excludes an eventually pair-only tail.

## Lean handoff

The checked declaration `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean` takes a behavioral terminal ε-Nash profile for each positive ε to existence of a fixed original uniform-equilibrium payoff. The six-hazard construction supplies one exact behavioral terminal Nash profile for all ε. Formalizing this application requires the two-phase Bellman argument and rational fixed-point bounds. The support census and the rational cone certificates for the lower bounds also remain to be formalized.
