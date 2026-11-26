# A signed solo/triple quadratic producer for quitting equilibrium

## Exact statement

Four players use independent behavioral Quit/Continue strategies at the
single live state. The first nonempty quitting coalition D pays finite
original reward R_i(D); live play and Never pay zero. A deviator may replace
its complete behavioral strategy. Put kappa_i=R_i({i}) and, on nonempty
coalitions only, Z_i(D)=R_i(D)-kappa_i. Thus native own singletons vanish.
The original kappa_i may have either sign. Their removal will be justified
by opponents-only absorption, not by changing the live or Never reward.

Choose four distinct roles (r,j,k,o). Player r is active at both phases,
players j,k at the second phase, and player o always continues. The theorem
below is a finite raw-table criterion: a two-by-two linear solve, at most
two explicitly selected quadratic roots, and four endpoint inequalities.
It supplies the hazards and the actual continuation values. No strategic
witness or positivity of continuation values is assumed.

Write Gamma_ab=Z_a({b}). Form

    M=[ Z_r({r,k}), Z_r({r,j}); Gamma_rk, Gamma_rj ],
    h=[-Z_r({r,j,k}); -Z_r({j,k})].

Require det M != 0. Compute (u,v)^T=M^-1 h and retain the role assignment
only if u>0 and v>0. Set

    a=1/(1+u), c=1/(1+v).                                  (1)

These will be the second-phase hazards of j and k. For a scalar z, put
q_j=a, q_r=z, q_k=c, q_o=0. Define, directly from the raw table,

    Q_i(z)=sum_(S subset I\{i}) p_i(S;q) Z_i(S union{i}),
    P_i(z)=sum_(nonempty S subset I\{i}) p_i(S;q) Z_i(S),
    H_i(z)=product_(l!=i)(1-q_l),
    p_i(S;q)=product_(l in S)q_l product_(l notin S,l!=i)(1-q_l).

For i=j,k these Q_i,P_i are affine functions of z. Set d_j=1-c, d_k=1-a,
G_i=Gamma_ir, and

    Phi_i(z)=Q_i(z)-P_i(z)-d_i(1-z)Q_i(z),
    L_i(z)=d_i(1-z)(G_i-Q_i(z)),
    F(z)=d_j(G_j-Q_j(z))Phi_k(z)
                  -d_k(G_k-Q_k(z))Phi_j(z).                 (2)

F has degree at most two: the cubic terms in the displayed expression
cancel. Require F to be a nonzero polynomial. Enumerate its real roots
by the linear or quadratic formula. For each real root b in (0,1), use
an index i in {j,k} for which L_i(b)!=0, and set

    s=Phi_i(b)/L_i(b).                                      (3)

Discard the candidate unless 0<s<1. If both L_j and L_k vanish, this
candidate is outside the stated test. Because F(b)=0, either allowed
choice of i gives all the remaining active-player equalities.

For each retained candidate define phase-B values X by

    X_r=0, X_j=Q_j(b), X_k=Q_k(b),
    C=(1-a)(1-b)(1-c),
    X_o=[P_o(b)+C s Gamma_or]/[1-C(1-s)].                    (4)

Define phase-A values

    Y=s Gamma_.r+(1-s)X.                                   (5)

In particular Y_r=0. The denominator in (4) is positive. Check the four
raw endpoint inequalities

    s Z_i({i,r}) <= Y_i    for i=j,k,o,
    Q_o(b) <= X_o.                                         (6)

THEOREM. Every candidate passing (1)--(6) produces a period-two exact
terminal Nash profile, at either initial phase, by repeating

    phase A: player r quits with probability s, others Continue;
    phase B: hazards q_j=a,q_r=b,q_k=c,q_o=0.                (7)

The original fixed payoff targets are kappa+Y and kappa+X. Each is a
uniform-equilibrium payoff, witnessed at every accuracy by the same profile.
All behavioral deviations, including Never, are included.

When F has a simple selected root and every inequality in (6) is strict,
the resulting raw class is open in all sixty original reward coordinates.
The class includes the explicit table below, where one phase-A native
continuation is negative. It is not restricted to a positive-value chamber.

## Why the linear and quadratic solves are sufficient

Since the phase-A owner r mixes alone and its own native singleton is zero,
its desired values at both phases are zero. At phase B, its Quit and passive
immediate values depend only on a,c, not on b. In odds x=a/(1-a),y=c/(1-c),

    Q_r/[(1-a)(1-c)]=Z_r(rj)x+Z_r(rk)y+Z_r(rjk)xy,
    P_r/[(1-a)(1-c)]=Gamma_rj x+Gamma_rk y+Z_r(jk)xy.

Dividing by xy>0 gives exactly the linear system M(u,v)^T=h with
u=1/x,v=1/y. Hence (1) gives Q_r=P_r=0. This proves both active comparisons
for r and its payoff recursions.

For i=j,k, prescribed continuation after phase B is Y_i. At phase B a
properly mixing owner must satisfy Q_i=P_i+H_i Y_i. Substituting
Y_i=s G_i+(1-s)Q_i gives exactly

    Phi_i(b)-s L_i(b)=0.                                   (8)

The determinant of the two linear equations in s is

    Phi_k L_j-Phi_j L_k=(1-b)F(b).

Therefore (2)--(3) solve both equations, even if one of the L_i is zero.
The definitions make the phase-B prescribed payoff equal to X_i, because
its Quit and Continue payoffs both equal X_i. At phase A, the quiet owner's
prescribed Continue payoff is exactly Y_i by (5).

For completeness, writing Q_j=A+Bz and Q_k=D+Ez shows that the cubic terms
in F are -d_j d_k B E z^3 and +d_j d_k B E z^3. Thus all root selection is
linear or quadratic. This cancellation is algebraic and uses no sign premise.

For the quiet player o, phase-B prescribed Continue value is
P_o(b)+C Y_o. Equations (4)--(5) solve this recursion exactly. At phase A,
Quit pays s Z_o({o,r}), whereas Continue pays Y_o. At phase B, Quit pays
Q_o(b), whereas Continue pays X_o. The last two inequalities in (6) are
therefore exactly this player's full local comparisons. The first two
inequalities give the analogous phase-A comparisons for j,k. No comparison
is omitted because a continuation coordinate is negative.

The one-step Bellman equations and all local Nash comparisons are now
proved by raw algebra. This constructs the needed annotations; it does not
assume the existence of a periodic certificate as part of the table class.

## Actual payoffs, unrestricted caps, and original uniformity

Every player faces a strictly positive opponents-only absorption chance in
each pair of dates. For r, the phase-B opponents j,k both have positive
hazards. For j or k, phase-A owner r has positive hazard. For o, phase A
already supplies positive opponents-only absorption. Consequently

    delta=1-max_i product_(phase A,B) H_i >0.

Under every unilateral behavioral replacement, live survival after n complete
periods is at most (1-delta)^n. This bound depends only on the prescribed
opponents. It is valid for arbitrary history-dependent randomized deviations.
There is just one live public history; conditional private randomization
changes the deviator's Quit hazard, not this opponents-only bound.

Iterating the policy recursion makes its remainder vanish geometrically, so
X and Y are the actual native terminal payoffs. Iterating the local maximum
inequalities bounds every deviator's terminal payoff by the corresponding
value: bounded future annotations have a remainder at most a constant times
(1-delta)^n. Hence the profile is exact terminal Nash against all behavioral
replacements. Equivalently, each pure deadline and Never is bounded, and
private-randomization disintegration covers every behavioral response.

All prescribed and unilaterally deviated profiles absorb almost surely.
Adding kappa_i to every nonempty reward therefore adds exactly kappa_i to
both prescribed and deviated terminal payoffs. The original live and Never
payoffs remain zero. Thus the native Nash comparisons transfer exactly to R.
Moreover the expected absorption time is at most 2/delta, uniformly over
all deviators. If M bounds the original terminal rewards, the difference
between terminal payoff and the T-stage average payoff is at most
2M E[tau]/T (a harmless extra factor covers time-index conventions). This
bound tends to zero uniformly over deviations. Exact terminal Nash therefore
yields the stated fixed original uniform payoff, using the same profile.

## Completeness within the nondegenerate two-phase architecture

Suppose a profile of the exact form (7), with all four displayed hazards in
(0,1), is exact terminal Nash. Every phase has positive reach probability,
so a profitable one-stage conditional replacement at either phase would
contradict that Nash property. At phase A, r's indifference forces X_r=0,
and hence Y_r=0. At phase B its indifference and policy recursion force
Q_r=P_r=0. If det M!=0, (1) therefore recovers a,c uniquely. The j,k
comparisons force (8), hence F(b)=0; if at least one L_i(b)!=0, (3)
recovers s. The quiet comparisons are exactly (6).

Thus, whenever det M!=0, F is not identically zero, and at least one
L_i(b) is nonzero, the finite test is both necessary and sufficient for this
proper two-phase architecture. One may test all twenty-four role assignments.
Degenerate linear-system or identically-zero-polynomial cases, zero/sure
hazards, and longer solo-return schedules are not classified here.
This does not assert completeness of the architecture for arbitrary Fin4.

## A fully specified exact new sign configuration

Use roles (r,j,k,o)=(1,0,3,2). The complete native table is below; coalition
mask m has bit i exactly when i quits. Original rewards may be R_i(D)=1+Z_i(D),
with zero live and Never payoff.

| Mask | Z0 | Z1 | Z2 | Z3 |
|---|---:|---:|---:|---:|
|1|0|-2|2|2|
|2|5|0|-1|-1|
|3|-12|-6|-3|10|
|4|-1|1|0|-1|
|5|-15/4|0|15/2|0|
|6|-10|-3|-5|-3|
|7|-30|30|30|30|
|8|-1|1|-1|0|
|9|0|-3|10|13/2|
|10|3|-2|0|-4/5|
|11|-30|10|30|-1000|
|12|-3|10|-3|0|
|13|-3|-3|-3|0|
|14|-3|10|3|3|
|15|3|-30|-30|-30|

Here

    M=[-2,-6;1,-2], h=(-10,3), (u,v)=(19/5,2/5),
    a=5/24, c=5/7.

The remaining polynomial F, multiplied by the positive number 56448, is

    P(b)=175496570 b^2-12603641 b+64295.                     (9)

Its smaller root is

    b=[12603641-sqrt(113717558584281)]/350993140,
    5526/10^6 < b < 5527/10^6.                              (10)

The opposite signs of P at these rational endpoints and its negative
derivative throughout the interval certify this root without numerical
assumptions. Formula (3) becomes

    s=(-348b^2-1080b+35)/(2(-174b^2+139b+35)).                (11)

Rational interval evaluation using (9)--(11) gives

    .405730 < s < .405748,
    phase-A quiet gaps for owners(0,2,3):
       (-6.817,-6.815), (-2.287,-2.286), (-.034,-.032),
    phase-B quiet gap for owner2: (-2.816,-2.814).           (12)

All decimal endpoints here denote exact decimal rationals. Every active gap
is identically zero modulo P. The native values satisfy

    Y0 in(1.9470,1.9472), Y1=0,
    Y2 in(.2576,.2577), Y3 in(-.292,-.291),
    X0 in(-.1374,-.1373), X1=0,
    X2 in(1.1162,1.1164), X3 in(.1917,.1920).                (13)

In particular Y3 is strictly negative, and its phase-A quitting premium
Z3({1,3})=-4/5 is negative. Direct endpoint comparison remains valid.
There is no claim that these native values are nonnegative or that zero
native Never payoff gives an owner a free zero response against absorbing
opponents.

Exact reproducibility can use rational polynomial arithmetic in Q[b]/(P).
For any rational expression, divide numerator and denominator by P and
retain their affine remainders. On (10), bound both affine remainders by
their endpoint values; reciprocal bounds are valid whenever zero is excluded.
This proves (12)--(13) and all denominator and hazard signs. The complete
embedded checker below implements exactly these steps from the literal table.

## Robustness and unbounded coordinate freedom

At this table the Jacobian of (P_r,Q_r) with respect to (a,c) is -10.
For the remaining equations f_i=Phi_i-s L_i, after solving f_j=0,

    f_k=P(b)/[2304(174b+35)],
    det D_(s,b)(f_j,f_k)=-(1-b)P'(b)/56448 !=0

at the selected root. Thus the algebraic branch is nonsingular. Equivalently,
the linear inverse, the simple quadratic root, the physical hazard bounds,
and all four strict quiet inequalities persist under sufficiently small
changes of every original reward coordinate. Own-level normalization is a
continuous linear map, so this is open in all sixty original coordinates.

There is also explicit unbounded freedom, without relying on a neighborhood.
For active recipients i in {r,j,k}, every reward on a coalition containing
the permanently quiet owner o is unused in every unilateral comparison for
i. These twenty-four coordinates are arbitrary finite real numbers. For o,
increasing any reward on a nonempty coalition contained in {r,j,k} increases
its actual prescribed values, while leaving its Quit offers unchanged;
decreasing any reward on a coalition containing o and at least one other
player decreases its Quit offers while leaving its prescribed values
unchanged. These fourteen independent one-sided changes preserve the same
hazards and all quiet comparisons. Arbitrary recipientwise shifts of all
nonempty rewards are also valid by opponents-only absorption.

These freedoms describe the actual proved class. They do not assert that
all reward tables, all passive-row perturbations in both directions, or all
possible dynamic sources are covered.

## Source correspondence and formal handoff

`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate` in
`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean` consume exact
policy recursions, local root Nash, and playerwise opponents-only contraction.
The present proof produces each input from the finite raw criterion; the
existing compiler itself does not select rates from arbitrary rewards.
These declarations were inspected in source, without a new Lean build.

The new mathematical content is the signed raw producer and the complete
nondegenerate two-phase classification. The shared-owner linear elimination
and quadratic cancellation are algebraic mechanisms that also appear in
positive-return constructions; no novelty claim is made for those operations.
The direct four-inequality return permits negative native continuations and
avoids imposing positivity merely to justify a longer wash schedule.

A formalization can first define the raw polynomial coefficients and prove
the cubic cancellation. It can then prove the linear-system central-owner
identities, the two active contact equations, and the four quiet comparisons,
construct a two-phase `cycle` and `value`, and apply the existing compiler.
No field of the raw criterion should assert existence of an equilibrium,
continuation, or periodic certificate. The rates are the displayed algebraic
functions of rewards and one of at most two real polynomial roots.

Arbitrary Fin4 remains open. This theorem gives one explicit raw existence
class and a finite decision test for its specified nondegenerate architecture.

## Embedded exact check

Save this code as a Python file and run it with Python3 and SymPy. Decimal
printing is only for readability; every assertion uses exact rational or
polynomial arithmetic.

```python
"""Exact certificate for the literal solo1 / joint013 periodic equilibrium.
Ordinary rational/algebraic mathematics, not a Lean check.
"""
import sympy as S
from itertools import product
b,t,a,c=S.symbols('b t a c')
rows={1:'0 -2 2 2',2:'5 0 -1 -1',3:'-12 -6 -3 10',4:'-1 1 0 -1',5:'-15/4 0 15/2 0',6:'-10 -3 -5 -3',7:'-30 30 30 30',8:'-1 1 -1 0',9:'0 -3 10 13/2',10:'3 -2 0 -4/5',11:'-30 10 30 -1000',12:'-3 10 -3 0',13:'-3 -3 -3 0',14:'-3 10 3 3',15:'3 -30 -30 -30'}
Z={m:list(map(S.Rational,row.split())) for m,row in rows.items()};Z[0]=[0]*4
poly=S.Poly(175496570*b*b-12603641*b+64295,b)
lo=S.Rational(5526,10**6);hi=S.Rational(5527,10**6)
assert poly.eval(lo)>0>poly.eval(hi)
assert poly.diff().eval(lo)<0 and poly.diff().eval(hi)<0
av=S.Rational(5,24);cv=S.Rational(5,7)
tv=(-348*b*b-1080*b+35)/(2*(-174*b*b+139*b+35))

def reduce_at_root(expr):
 n,d=S.cancel(expr).as_numer_denom()
 n=S.rem(n,poly.as_expr(),b);d=S.rem(d,poly.as_expr(),b)
 return S.cancel(n/d)

def interval(expr):
 """Rational interval bound on a reduced affine-over-affine expression."""
 n,d=S.fraction(reduce_at_root(expr));pn=S.Poly(n,b);pd=S.Poly(d,b)
 assert pn.degree()<=1 and pd.degree()<=1,(pn,pd)
 nl,nh=sorted([pn.eval(lo),pn.eval(hi)]);dl,dh=sorted([pd.eval(lo),pd.eval(hi)])
 assert dl*dh>0,(dl,dh)
 vals=[x/y for x in (nl,nh) for y in (dl,dh)]
 return min(vals),max(vals)

def bounds(label,expr):
 l,h=interval(expr);print(label,':',reduce_at_root(expr),'in',float(l),float(h));return l,h

assert bounds('solo hazard',tv)[0]>0 and interval(tv)[1]<1
assert interval(1-tv)[0]>0

def root(q):
 P=[];Q=[];H=[]
 for i in range(4):
  pp=qq=0
  for m in range(16):
   if m>>i&1:continue
   pr=S.prod(q[j] if m>>j&1 else 1-q[j] for j in range(4) if j!=i)
   pp+=pr*Z[m][i];qq+=pr*Z[m|1<<i][i]
  P.append(S.factor(pp));Q.append(S.factor(qq));H.append(S.prod(1-q[j] for j in range(4) if j!=i))
 cc=S.prod(1-z for z in q)
 bb=S.Matrix([q[i]*Q[i]+(1-q[i])*P[i] for i in range(4)])
 return S.Matrix(P),S.Matrix(Q),S.Matrix(H),S.factor(cc),bb

P,Q,H,cc,bb=root([a,b,0,c])
assert S.expand(P[1])==-2*a+c-2*a*c
assert S.expand(Q[1])==-6*a-2*c+18*a*c
assert P[1].subs({a:av,c:cv})==Q[1].subs({a:av,c:cv})==0
assert S.det(S.Matrix([P[1],Q[1]]).jacobian([a,c])).subs({a:av,c:cv})==-10
for z in (P[1],Q[1]):assert z.subs({a:av,c:cv})==0

P0,Q0,H0,c0,b0=root([0,tv,0,0]);P1,Q1,H1,c1,b1=root([av,b,0,cv])
VA=(b0+c0*b1)/(1-c0*c1);VB=b1+c1*VA
G0=Q0-P0-S.matrix_multiply_elementwise(H0,VB)
G1=Q1-P1-S.matrix_multiply_elementwise(H1,VA)
for k,G,active in [(0,G0,[1]),(1,G1,[0,1,3])]:
 for i,g in enumerate(G):
  v=reduce_at_root(g)
  if i in active:assert v==0,(k,i,v)
  else:assert bounds('quiet gap '+str((k,i)),g)[1]<0,(k,i,g)
for k,V in enumerate([VA,VB]):
 for i,v in enumerate(V):bounds('native value '+str((k,i)),v)
# Direct two-contact reduction after the central player's equalities.
v0=-S.Rational(174,7)*b;v3=S.Rational(65,48)-S.Rational(50477,240)*b
f=v0-(30*b-5)/7-2*(1-b)/7*(5*t+(1-t)*v0)
g=v3-(S.Rational(5,12)+S.Rational(7,8)*b)-S.Rational(19,24)*(1-b)*(-t+(1-t)*v3)
assert S.factor(f.subs(t,tv))==0
assert S.cancel(g.subs(t,tv)-poly.as_expr()/(2304*(174*b+35)))==0
# The active contact Jacobian is nonzero, by two nonsingular blocks.
jac=S.factor(S.det(S.Matrix([f,g]).jacobian([t,b])).subs(t,tv))
assert reduce_at_root(jac+(1-b)*poly.diff().as_expr()/56448)==0
assert interval(jac)[0]>0
# Every deviator faces independent periodic opponent absorption.
for i in range(4):assert interval(H0[i]*H1[i])[0]>0 and interval(H0[i]*H1[i])[1]<1
print('PASS: exact algebraic Nash certificate, all four quiet inequalities, nonzero active Jacobian.')
```
