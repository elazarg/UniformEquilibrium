# A repeated-pair raw equilibrium slab and algebraic producer

Complete ordinary mathematics. A scalar intermediate-value argument produces
an exact three-phase equilibrium from raw reward inequalities. In particular,
an explicit 41-parameter family permits one passive reward throughout [-1/10,1/5],
twelve independent joining rewards unbounded below, twenty-four arbitrary
reward coordinates, and four arbitrary own singleton levels. A finite
algebraic criterion also supplies full sixty-dimensional neighborhoods.
All unilateral behavioral replacements are allowed. The fixed terminal payoff
is a uniform-equilibrium target. This is not a solution of Fin4 or a Lean
verification.

## 1. Actual game and complete raw theorem

There are four players. At each live date they independently choose Continue
or Quit with private randomization and the observed public history. The first
nonempty quitting coalition C absorbs at a finite vector R(C). Live dates,
including the selecting date, and perpetual Continue pay zero. A unilateral
deviation replaces one player's entire behavioral strategy.

Choose arbitrary finite own levels ell_i=R_i({i}) and use native entries
Z_i(C)=R_i(C)-ell_i for nonempty C. In this theorem the off-diagonal singleton
matrix is fixed at

```
Gamma=[[0,1001/1000,-4,-1/1000],
       [11/10,0,-1/5,-1/10],
       [-1/2000,-3/20,0,101/100],
       [-13/200,-39/1000,11/10,0]].
```

Fix the four scheduled participant entries at

```
Z_0(03)=9/1000, Z_3(03)=1/200,
Z_1(12)=13/10, Z_2(12)=9/20,
```

and three passive entries at

```
Z_0(12)=-114126225102031811/2301677348322650000000,
Z_2(03)=16857064217550611361/16857006656318800000,
Z_3(12)=1540799386594877837/1539763290995000000.
```

Allow the fourth passive entry to vary throughout

    theta=Z_1(03) in[-1/10,1/5].                         (1)

The only other restrictions are these twelve upper bounds:

| Recipient | Joining a singleton | Joining the other singleton | Joining the scheduled pair |
| --- | --- | --- | --- |
| 0 | Z_0(01)<=1/1000 | Z_0(02)<=1/100 | Z_0(012)<=0 |
| 1 | Z_1(01)<=1/10 | Z_1(13)<=3/10 | Z_1(013)<=1 |
| 2 | Z_2(02)<=1/2000 | Z_2(23)<=1/100 | Z_2(023)<=0 |
| 3 | Z_3(13)<=1/1000 | Z_3(23)<=1/10 | Z_3(123)<=0 |

Each of these twelve coordinates can decrease independently without bound.
All 24 unmentioned nonsingleton coordinates are arbitrary finite reals: eight
passive pair coordinates, eight unused participant triple coordinates, four
passive triple coordinates, and four grand-coalition coordinates. The four
own levels are arbitrary as well. Thus the displayed parameterization has 41
independent continuous directions; it is not itself claimed full-dimensional.

**Raw slab theorem.** Every such actual table has an exact terminal Nash
profile whose repeated chronological supports are 03,03,12, with all six
hazards strictly between zero and one. One fixed actual payoff vector is a
uniform-equilibrium payoff, witnessed by the same profile at every accuracy
and all sufficiently long finite horizons. Section 4 also proves the same
conclusion for a separate finite raw algebraic criterion with nonempty
sixty-dimensional interior. Neither theorem assumes a strategic root,
continuation vector, cycle, minimum source, or other equilibrium witness.

Section 2 defines a literal point in the slab. Sections 6--11 prove that this
point, and a sufficiently small full reward neighborhood, lie outside every
stationary profile, every fixed-disjoint-pair two-phase profile, every
true-punishment sure-first root, all nontrivial positively row-scaled response
quotients, and the explicitly defined raw criteria below. No claim is made
that every point of the slab avoids those criteria, or that an unspecified
maximal neighborhood of some other local construction has been excluded.

## 2. All sixty exact center rewards

Use the following initial matrices to specify the singleton comparisons:

    A0=[[0,1,-6,-1/100],
        [1,0,-3/2,-2/5],
        [-1/1000,-3/5,0,1],
        [-7/100,-1/25,1,0]],
    J0=[[0,1/1000,2,9/1000],
        [1/10,0,13/10,3/10],
        [1/2000,9/20,0,1/100],
        [1/200,1/1000,1/10,0]],
    Gamma=A0+J0.

The FINAL participant-pair matrix J equals J0 except J_02=1/100.
The actual contact matrix is A=Gamma-J, not A0. Both Gamma and A have
strict matching signs for favorites (01)(23), and both inverses are
strictly positive. These matrix facts are checked, although the producer
does not require them as additional hypotheses.

For recipient i and opponent subset B, use passive rewards P_i(B) and
joining rewards Q_i(B). Both are zero at B=empty. For singleton B={j},
put P_i(B)=Gamma_ij and Q_i(B)=J_ij. For opponent pairs 01,02,03,12,13,23
respectively use signs +1,-1,+1,+1,-1,-1. Let Delta_i(B) be that sign for
the smaller owner outside B and its negative for the larger owner outside
B. Initially put

    P_i(B)=max(0,-Delta_i(B)), Q_i(B)=max(0,Delta_i(B)).

Replace precisely these five opponent-pair entries:

    Q_0(12)=0,
    P_0(12)=-114126225102031811/2301677348322650000000,
    P_1(03)=-348008157802289/2515995359124050000-1/1000000,
    P_2(03)=16857064217550611361/16857006656318800000,
    P_3(12)=1540799386594877837/1539763290995000000.    (2)

For the full opponent triple put P_i(B)=1 and Q_i(B)=0. Now define

    Z_i(C)=Q_i(C minus{i}) if i belongs to C,
    Z_i(C)=P_i(C) otherwise,
    r*_i(C)=1+Z_i(C).                               (3)

This specifies every reward. All native participant comparisons are
nonnegative, all participant pairs are strictly positive, all own
comparisons are zero, and |r*_i(C)|<=3. The four adjusted passive entries
are approximately -0.000049584,-0.000139318,1.000003415,1.000672893.
No decimal approximation is used in the proof.

For an explicit scope comparison define theta0 to be
-348008157802289/2515995359124050000, and define r0 by the same sixty-entry
recipe except P_1(03)=theta0. The present point r* has theta*=theta0-10^{-6}.
Consequently it is outside the explicitly specified cube
|r_i(C)-r0_i(C)|<=10^{-9}. It is strictly inside the slab(1). The complete
comparison below is recomputed at r*, not inferred from r0. This proves a
literal enlargement beyond that stated cube; it makes no assertion about
unknown maximal neighborhoods of any local existence theorem.

## 3. Exact repeated-pair compression

### 3.1. Active equations

Use native own singleton reward zero, disjoint pairs A={a,b} and B, and mate
map m. Write p_i=J_i,m(i)>0 and g_i=Gamma_i,m(i)<0 for i in A. For j in A set

```
beta_j=(p_m(j)-Gamma_m(j),j)/p_m(j)>1,
d_j=1+beta_j, D=d_a*d_b.
```

Given effective hazards r_j in(0,1), set the physical first and second A-date
hazards to x_j=r_j/d_j and y_j=beta_j*r_j/(d_j-r_j). These are proper,
y_j=beta_j*x_j/(1-x_j), and r_j=1-(1-x_j)(1-y_j). The active equalities
between the two A dates hold identically. The first-date active value of i is
p_i*x_m(i), so the effective scheduled joining coefficient is
p'_i=p_i/d_m(i). The effective contact coefficient satisfies

```
(p'_i-g_i)*r_m/(1-r_m)=(p_i-g_i)*y_m/(1-y_m).
```

Conditional on both A owners having finite clocks in this block, the
probabilities of a tie, a first, and b first are respectively
(1+beta_a*beta_b)/D, beta_b/D, beta_a/D. Thus for every i in B replace its
passive A-pair reward P_i(A) by

```
P'_i(A)=((1+beta_a*beta_b)*P_i(A)
         +beta_b*Gamma_i,a+beta_a*Gamma_i,b)/D.
```

Keep all singleton Gamma entries, the B scheduled joining coefficients, and
the A owners' passive B-pair rewards unchanged. The six physical active
equations are exactly the four fixed-pair active equations with these data.
This is an equality of payoff recursions, not a compression of observation
opportunities for inactive owners.

### 3.2. Both original inactive deadlines

For i in B write L_i=Z_i({i,a,b}). Its early-A Quit query is a multiaffine
polynomial in r with zero empty coefficient and Bernstein coefficients

```
E_a=J_i,a/d_a, E_b=J_i,b/d_b,
E_ab=(beta_b*J_i,a+beta_a*J_i,b+L_i)/D.
```

Its late-A Quit query, measured at the beginning of the block after following
Continue through the first date, has coefficients

```
L_a=(Gamma_i,a+beta_a*J_i,a)/d_a,
L_b=(Gamma_i,b+beta_b*J_i,b)/d_b,
L_ab=(beta_b*Gamma_i,a+beta_a*Gamma_i,b
      +P_i(A)+beta_a*beta_b*L_i)/D.
```

The formula follows by expanding P_i(x)+H_i(x)Q_i(y), using
1-y_j=d_j*(1-r_j)/(d_j-r_j). Therefore the effective block value must dominate
both displayed query polynomials. Componentwise maxima give a sufficient
single effective joining row, but may be conservative. For i in A the
inactive B-date query is unchanged. Section 5 proves the complete date-or-Never cap from proper rates and these
inequalities. The compression alone does not imply the inequalities.

## 4. Finite raw algebraic production

### 4.1. Actual inputs and the fixed test

The actual game has live reward zero and arbitrary finite absorbing rewards
R_i(C), for four players and every nonempty coalition C. Set
ell_i=R_i({i}) and Z_i(C)=R_i(C)-ell_i. Define Gamma_ij=Z_i({j}),
J_ij=Z_i({i,j}), and the mate map m=(3,2,1,0). The schedules are A=03
and B=12. Write P_i=Z_i(B) for i in A and P_i=Z_i(A) for i in B;
write Q_i=Z_i({i} union B) for i in A and Q_i=Z_i({i} union A) for
i in B. Thus Q_i is one scalar triple joining reward, not a whole query
function. All quantities below are computed from these 32 native entries:
twelve Gamma, twelve J, four P, and four Q. The four ell_i are arbitrary.

Assume strict matching signs for Gamma, with favorite pairs01 and23, and
J_i,m(i)>0 for all i. No sign restriction is imposed on other joining
rewards. Perform the compression of Section 3, denoting compressed scheduled
premiums by p_i, contact coefficients c_i=p_i-Gamma_i,m(i), and compressed
passive coefficients by P'_i. In particular P'_0=P_0 and P'_3=P_3.
The following weak raw guards will suffice for all monotonicity used here:

```
Gamma01>=p0, Gamma02<=P0<=Gamma01,
Gamma32>=p3, Gamma31<=P3<=Gamma32,
Gamma20<=P'2<=Gamma23, Gamma23>=p2.                 (M0)
```

No determinant, inverse, or eigenvalue hypothesis is required in this
section. The two scalar residuals are now defined directly in the native entries. For B hazards (y,t) in(0,1)^2 put

```
H=(1-y)*(1-t),
R_i(y,t)=Gamma_i1*y*(1-t)+Gamma_i2*t*(1-y)+P_i*y*t,
                         i in A.
```

Whenever R_i>0 define

```
f_i(y,t)=2*R_i /
  [c_i+R_i-p_i*H+sqrt((c_i+R_i-p_i*H)^2+4*p_i*H*R_i)].       (C1)
```

The denominator is positive, since c_i>p_i. Formula(C1) is the unique
root z in(0,1) of c_i*z/(1-z)-p_i*H*z=R_i. Set
r0=f_3(y,t), r3=f_0(y,t), r1=y, r2=t. Define

```
G_i(r)=Gamma_ij*r_j*(1-r_k)+Gamma_ik*r_k*(1-r_j)+P'_i*r_j*r_k
       +p_i*r_m(i)*(1-r_j)*(1-r_k)-c_i*r_m(i)/(1-r_m(i)),
```

where {j,k} is the pair opposite i. Only i=1,2 are used for the residual
test; the other two equations hold by construction.

The following rectangles and endpoint brackets are FIXED independently of
the game. For n=0,...,299 let

```
a_n=12/25+n/10000, b_n=a_n+1/10000, h_n=(a_n+b_n)/2,
t_n=(3/5)*h_n-51233/500000+(h_n-49351/100000)^2/2,
L_n=t_n-1/8000, U_n=t_n+1/8000,
C_n=[a_n,b_n] times[L_n,U_n].
```

At y=12/25 use the endpoint t bracket
[1856348,1856349]/10^7. At y=51/100 use
[2036449,2036450]/10^7. None of these numbers is an equilibrium rate input.

Here is a finite test on the raw table. Interval arithmetic means the
standard enclosing arithmetic with exact real endpoints, including min/max
for products and reciprocal intervals of fixed sign. Formula(C1) gives
algebraic, rather than strategic, endpoints.

1. On every C_n and both endpoint brackets, require R_0,R_3>0 at all
   four corners. The redundant repeated corners on a degenerate endpoint
   bracket cause no problem.
2. For a rectangle Y times T, define its A enclosure by

```
r0 in[f_3(Y.hi,T.lo), f_3(Y.lo,T.hi)],
r3 in[f_0(Y.lo,T.hi), f_0(Y.hi,T.lo)], r1 in Y, r2 in T.      (C2)
```

   Define the lower G2 enclosure by evaluating G2 at
   (r0.hi,Y.hi,r3.lo), and its upper enclosure by evaluating at
   (r0.lo,Y.lo,r3.hi); r2 does not enter G2 explicitly. On each
   Y=[a_n,b_n], require the lower enclosure at T={L_n} to be strictly
   positive and the upper enclosure at T={U_n} strictly negative.
3. On every full C_n, compute all six physical gaps described in 4.3 by
   interval arithmetic using(C2), and require their lower endpoints >0.
4. On each endpoint bracket require the same strict G2 signs at its two
   t endpoints. Enclose G1 by ordinary interval arithmetic on(C2).
   Require its lower endpoint >0 at y=12/25 and its upper endpoint <0
   at y=51/100.

Call this the fixed-tube reward criterion. It consists of finitely many
explicit inequalities in the 32 native coordinates. Square roots are of
strictly positive expressions with prescribed positive signs, so this is a
semialgebraic raw class. For rational input it can be certified by rational
bisection of(C1) and outward interval arithmetic. No solution of the active
equations, continuation vector, cycle, or existential strategic witness is
an input to the criterion.

### 4.2. Why the test produces the active rates

Under(M0), implicit differentiation of(C1) yields

```
partial_y r0<0, partial_t r0>0,
partial_y r3>0, partial_t r3<0.
```

For example, before division by the positive implicit derivative, the
numerator for partial_y r3 is
(Gamma01-p0*r3)*(1-t)+(P0-Gamma02)*t>0. The numerator for
partial_t r3 is
(Gamma02-p0*r3)*(1-y)+(P0-Gamma01)*y<0. The two formulas for r0
are the corresponding row 3 expressions. This proves(C2).

At fixed(y,r3), the derivative of G2 with respect to r0 is
(Gamma20-p2*y)*(1-r3)+(P'2-Gamma23)*r3<0. Its derivative with
respect to r3 is
(Gamma23-p2*y)*(1-r0)+(P'2-Gamma20)*r0>0. Its explicit derivative
with respect to y is
p2*(1-r0)*(1-r3)-c2/(1-y)^2<0. Consequently the sharper G2
enclosures in the test are valid. Along the actual response functions,
G2 strictly decreases in t.

For each fixed y, the set of t in(0,1) for which R0,R3>0 is an interval:
R0 is strictly decreasing in t and R3 strictly increasing. On that entire
interval G2 is strictly decreasing. Every rectangle therefore contains
exactly one root t(y) for each y in its horizontal range. The strict
endpoint signs and continuity make t(y) continuous. At the shared cuts of
adjacent rectangles, uniqueness in the ENTIRE legal interval identifies
their roots, even though no overlap of the preassigned vertical tubes was
assumed. They form one continuous branch on[12/25,51/100]. The separate
endpoint brackets contain those same roots by the same uniqueness argument.

The G1 endpoint test and the intermediate value theorem now supply a
y in(12/25,51/100) for which G1=0 on this branch. All four effective
hazards are proper. Section 3 then produces the six physical hazards

```
phase0: x0=r0/d0, x3=r3/d3;
phase1: z0=beta0*r0/(d0-r0), z3=beta3*r3/(d3-r3);
phase2: y1=r1, y2=r2.
```

Both A dates have support 03; phase 2 has support 12. All six active
indifference equations hold exactly. The produced root may be nonunique;
neither uniqueness nor an inverse-function theorem is needed.

### 4.3. The six physical inactive gaps

For i in A, define its phase 2 value

```
V_i^2=c_i*r_m(i)/(1-r_m(i)).
```

Its inactive gap at phase 2 is

```
V_i^2-[J_i1*r1*(1-r2)+J_i2*r2*(1-r1)+Q_i*r1*r2].           (C3)
```

For i in B define V_i^2=p_i*r_m(i). For h=(h0,h3), put

```
Passive_i(h)=Gamma_i0*h0*(1-h3)+Gamma_i3*h3*(1-h0)+P_i*h0*h3,
Quit_i(h)=J_i0*h0*(1-h3)+J_i3*h3*(1-h0)+Q_i*h0*h3,
V_i^1=Passive_i(z)+(1-z0)*(1-z3)*V_i^2,
V_i^0=Passive_i(x)+(1-x0)*(1-x3)*V_i^1.
```

The two inactive gaps for i are V_i^0-Quit_i(x) and
V_i^1-Quit_i(z). These are the four other gaps in test3. Off the common
zero of G1,G2 these formulas are merely algebraic annotations; at the zero
they are the actual cyclic policy values. Interval lower bounds on the
whole tube suffice at that zero. This distinction prevents imposing an
unproved policy interpretation away from the produced root.

For i in A the other values are V_i^0=J_i,m(i)*x_m(i) and
V_i^1=J_i,m(i)*z_m(i). The compression identity proves their active
indifferences and phase 2 policy recursion. For i in B, G_i=0 is precisely
the active phase 2 indifference against continuation V_i^0. Thus the 12
phase/player policy recursions hold, the six active queries are equalities,
and the six inactive queries are strictly below the policy value.

### 4.4. Exact verification for the entire displayed slab

Appendix A uses exact Fraction arithmetic, 44 bisection steps for each
algebraic response, and the fixed 300 rectangles of Section 4.1. It checks
all raw monotonicity guards, all positive passive-corner conditions, and
strict G2 signs on both boundaries of every rectangle. The uniform G2 sign
margin exceeds 1/250. The two fixed endpoint brackets also have strict G2
signs. These finite facts contain no numerical root acceptance.

Only the effective row 1 passive reward changes. Its exact expression is

    P_1(theta)=[(1+beta_0 beta_3)theta
                +beta_3 Gamma_10+beta_0 Gamma_13]/(d_0d_3).

In particular its coefficient of theta is 149/285>0. The active A responses
r0(y1,y2),r3(y1,y2) and G_2 do not involve theta. Therefore all 300 tube cells,
the unique continuous branch y2=f(y1), its endpoint brackets in Section 4.1, and its
uniform G_2 boundary margins remain valid throughout (1).

At either endpoint, G_1 is affine in theta with positive coefficient
(149/285)r0r3. Outward evaluation with theta in the entire interval[-1/10,1/5]
on the exact endpoint enclosures in Section 4.1 proves

    G_1(12/25,f(12/25);theta)>1/50,
    G_1(51/100,f(51/100);theta)<-1/125                  (S1)

uniformly in theta. These are exact rational acceptance inequalities in the
checker in Appendix A, not decimal observations. For each theta the IVT now produces
an exact root of all four effective active equations somewhere on the same
branch. Select one such root once, before choosing an approximation accuracy.

### 4.5. The original inactive deadlines throughout the slab

In the original physical value formulas in Section 4.3, only the passive reward
P_1^native changes, and it is exactly theta. In particular this variation is
not confined to a joining coordinate or an unused coordinate: it changes
the actual first03 and second03 continuation equations for recipient 1 and
changes the selected active root.

Evaluate those original formulas over every tube box, with theta enclosed
by[-1/10,1/5] and with the joining coordinates at their displayed upper caps.
Exact outward rational interval arithmetic gives

| Inactive owner and physical date | Gap, uniformly in theta |
| --- | ---: |
| owner 0, final12 date | >1/250 |
| owner 3, final12 date | >17/100 |
| owner 1, first03 date | >9/50 |
| owner 1, second03 date | >1/3000 |
| owner 2, first03 date | >1/2 |
| owner 2, second03 date | >2/5 |

The two bounds for recipient 1 include both occurrences of theta in its
first03 continuation recursion. No cancellation or independence between
these occurrences is assumed: interval arithmetic over-encloses them.

Each queried joining reward appears in its immediate Quit endpoint with a
nonnegative probability coefficient. Decreasing any of the twelve capped
coordinates therefore preserves every displayed gap. Those decreases do not
alter any active indifference or policy equation, because the scheduled
participant coordinates remain fixed. All twenty-four arbitrary coordinates
are absent from the policy and every unilateral endpoint under this support
word. A unilateral response can meet at most the scheduled pair, so it cannot
create an unqueried grand event or an additional passive-triple event.

At the root produced by (S1), the annotations satisfy all policy recursions
and active indifferences, and every inactive owner strictly prefers Continue.
Thus the original three-phase certificate is complete for every table in
the slab. Every prescribed hazard is proper, and every opponent-deleted
period contracts. Section 5 supplies all complete behavioral caps and the
fixed-target uniform conclusion.

Finally, arbitrary own levels cause no gap: the prescribed opponents force
absorption almost surely under every unilateral replacement. Every such
actual terminal comparison therefore equals its native comparison plus the
same ell_i. The native literal Never outcome has not been shifted. Geometric
tails control the finite-horizon discrepancy for the original game.

## 5. Complete behavioral deviations and a fixed uniform target

Repeat the three phases forever, using independent private randomization.
For any unilateral complete behavioral replacement, the opponents still
have a strictly positive probability of quitting during each three-date
block. Their no-quit probability q_i is the product of their fixed Continue
probabilities over one cycle and satisfies q_i<1. This remains true when
the deviator always Continues or conditions arbitrarily on the public
history. Absorption is therefore almost sure for every such replacement.

At each live history, the Bellman inequalities just proved bound either
choice and hence every mixed choice by the current policy value, with
equality for the prescribed profile. Iterating through N dates leaves a
bounded residual multiplied by opponent survival, which tends to zero.
Every deterministic deadline, Never, and every behavioral randomization
among complete deviations is capped. This proves exact terminal Nash.
The arbitrary offsets ell_i cause no problem: absorption is almost sure
even under a unilateral deviation, so adding ell_i to all absorbing
payoffs simply adds ell_i to every compared terminal payoff.

Let M be the largest absolute actual absorbing reward. The absorption time
under any unilateral deviation is dominated by the first opponent quit,
whose expected time is at most 3/(1-q_i), up to the harmless convention for
counting the selecting date. Thus the difference between the expected
terminal reward and the T-date average reward is bounded by a constant/T,
uniformly over all complete deviations. The same holds for the profile.
Its exact terminal vector, with the offsets restored, is one fixed target.
For every epsilon>0, the SAME profile is epsilon-Nash and within epsilon
of that target at every sufficiently long horizon. This is the required
uniform-equilibrium payoff conclusion.

The corresponding Lean interfaces are
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`, and
`IsUniformEquilibriumPayoff` in
`GameTheory/GameTheory/Stochastic/Uniform.lean`. Their exact contraction and
full behavioral quantifiers agree with this ordinary proof. No Lean build
or formalization of the present producer is asserted.

## 6. Complete fixed two-pair exclusion at the center

All arguments in this section concern the literal table r* in(2)--(3).

### 6.1 Every proper four-owner schedule

Fix a mate involution m. For the opposite pair {j,k} to i put

    p_i=J_i,m(i), c_i=p_i-Gamma_i,m(i),
    C_i=Gamma_ij q_j(1-q_k)+Gamma_ik q_k(1-q_j)
            +Z_i({j,k})q_jq_k+p_i q_m(i)(1-q_j)(1-q_k),
    Q_i=J_ij q_j(1-q_k)+J_ik q_k(1-q_j)
            +Z_i({i,j,k})q_jq_k,
    E_i=(1-q_m(i))C_i-c_i q_m(i),
    H_i=(1-q_m(i))Q_i-c_i q_m(i).                  (14)

Every proper fixed-pair equilibrium must satisfy E=0 and H<=0. Indeed
active indifference fixes its active native value as p_i q_m(i) and its
inactive native value as c_i q_m(i)/(1-q_m(i)); (14) gives precisely the
inactive policy and Quit tests.

For the favorite partition 01|23, c_i=-1. Its inactive value would be
negative, while immediate Quit has nonnegative native value. This excludes
that schedule.

For each crossing partition the standalone exact checker proves

    q in[0,1]^4, E(q)=0, H(q)<=0 imply q=0.         (15)

The fields have coordinatewise degree at most two. Their tensor Bernstein
coefficients, with denominators cleared, are integer arrays. A midpoint
subdivision retains both children, and a box is discarded only when an
E coordinate has strictly one sign, or an H coordinate is strictly
positive, throughout the box. Those implications follow from the convex
hull property of Bernstein coefficients.

The one analytic terminal rule is the origin cube [0,1/256]^4. Write
E(q)=Gamma q+R(q). If L=||Gamma^{-1}||_infinity and K is the largest sum
of absolute nonlinear monomial coefficients in one E row, then
||R(q)||_infinity<=K||q||_infinity^2. The exact check L K/256<1 implies
that E=0 in that cube forces q=0. This requires no support assumption.

The complete deterministic subdivision terminates as follows:

| Schedule | Nodes | Leaves | Maximum depth |
| --- | ---: | ---: | ---: |
| 02|13 | 103 | 52 | 32 |
| 03|12 | 893 | 447 | 39 |

No small box or exhausted search budget is accepted as a proof. Every
point, face and splitting plane belongs to a retained child until one of
the exact rules applies. This establishes (15) and excludes every proper
four-owner schedule, rather than merely a finite collection of roots.

### 6.2 Every sure-hazard case

An exact equilibrium's continuation after a positive-probability live
history is itself exact Nash, since a profitable full continuation deviation
can be appended after that history. Consider the first reached paired
phase containing a sure quitter i, with mate j.

If {i,j} is crossing, owner j's Quit value is J_ji>0 and its Continue
value is Gamma_ji<0, because i quits surely. Hence j must also quit
surely. Each pure crossing pair has an outsider strictly preferring to
join. For 03 the positive difference is 1-P_1(03); for 12 it is
-P_0(12)>0; the other two crossing pairs retain a difference of one.
Thus no crossing sure phase is Nash.

If {i,j} is favorite and j has positive hazard q, owner i's native
Continue-minus-Quit value is at least
(Gamma_ij-J_ij)q=q>0. Its continuation full cap is nonnegative because
all native participant rewards are nonnegative. This excludes i's sure
Quit. If j's hazard is zero, choose a crossing observer of i; it receives
negative Gamma_ki and can instead join for positive J_ki. These cases
exhaust every sure paired phase, even against an arbitrary continuation.

### 6.3 Every zero-hazard case

Assume all hazards are below one. If both phases are nonempty and one
owner has zero hazard, one phase is solo. Its sole mixing owner has native
Quit value zero and no opponent quits there; proper mixing forces its
next-phase value to be zero. At that opposite nonempty phase, immediate
Quit has strictly positive expectation: positive participant pairs and
proper opponent hazards give a positive singleton-opponent event, and all
other participant rewards are nonnegative. Contradiction.

If one phase is empty, only the other phase absorbs. For two proper active
owners i,j, policy and indifference force J_ij q_j=Gamma_ij. This is
impossible: crossing Gamma is negative, while favorite Gamma_ij=J_ij+1.
With only one active owner, a crossing observer gets actual payoff
1+Gamma_ki<1 and immediate Quit guarantees at least one. With no active
owner, AllNever pays zero and immediate Quit pays one. All zero-hazard
patterns are exhausted.

## 7. Positive architecture gap and robust separation

Suppose a sequence of fixed two-pair profiles had exploitability tending
to zero. Fix its finite schedule choice on a subsequence and take a hazard
limit q* in the compact cube.

If q* has at least two positive coordinates, joint and every opponent-
deleted absorption probability are positive. Prescribed terminal values
are continuous there. The full cap is also continuous: if H_i<1 is
opponent period survival, e_i is the Never payoff, and L_i^0,L_i^1 are
the two first-period deadline payoffs, later deadlines have values
(1-H_i^k)e_i+H_i^k L_i^t. Thus the full cap is exactly
max(e_i,L_i^0,L_i^1), a finite maximum of continuous functions. The limit
would be exact Nash, contrary to Section 6.

If q* has exactly one positive coordinate j, a negative-crossing observer
i has limiting payoff 1+Gamma_ij<1, while immediate Quit guarantees one.
This also gives a positive limiting deviation gain.

Finally suppose q* is zero. Write h=sum_i q_i>0 and pass to a limit
w=q/h in the unit simplex. Singleton first exits have period masses
q_j+O(h^2), all simultaneous exits have mass O(h^2), and period absorption
is h+O(h^2). Hence prescribed values converge to 1+(Gamma w)_i. Immediate
Quit guarantees one, so vanishing debt implies Gamma w>=0. A singleton
support contradicts a negative-crossing observer. For any w_i>0 on a
support of size at least two, the Never response tends to
1+(Gamma w)_i/(1-w_i). Its Nash bound forces (Gamma w)_i=0.
Thus Gamma_SS w_S=0 for the support S. Every principal Gamma block of
size at least two is nonsingular, as checked exactly, contradiction.

Therefore the center has some strictly positive gap d over the entire
fixed-pair family. Changing all rewards by at most eta changes every
prescribed or deviating terminal payoff by at most eta, uniformly over
all profiles. Each exploitability changes by at most 2 eta. The gap
therefore persists on a sufficiently small full-dimensional neighborhood.
The strict fixed-tube tests of Section 4 persist on a full reward neighborhood
of r*. Intersecting those neighborhoods proves the strict open separation.
This establishes no universal lower bound against longer-period or
unrestricted strategies; Section 4 produces an exact longer-period escape.

## 8. Complete stationary exclusion, with a positive gap

For a stationary hazard vector q define

    H_i=product_(j!=i)(1-q_j),
    P_i=sum_(nonempty B subset I minus{i}) Pr_q(B) Z_i(B),
    Q_i=sum_(B subset I minus{i}) Pr_q(B) Z_i(B union{i}),
    F_i=(1-H_i)Q_i-P_i.                            (16)

At any nonzero stationary Nash profile these polynomials satisfy

    q_i>0 implies F_i>=0,
    q_i<1 implies F_i<=0.                         (17)

Indeed the actual stationary policy value is
1+[q_i Q_i+(1-q_i)P_i]/[1-(1-q_i)H_i]. The difference between its Quit
and Continue endpoints is F_i/[1-(1-q_i)H_i]. The denominator is positive
at every nonzero profile. This proves (17), including every zero and sure
coordinate. AllNever itself is not Nash: immediate Quit pays one.

The standalone checker excludes (17) on the entire cube except the origin.
It uses tensor Bernstein coefficients of coordinatewise degree two. A box
is rejected only if some F_i is strictly negative while its lower bound
on q_i is positive, or F_i is strictly positive while its upper bound on
q_i is less than one. These are exactly the negations of necessary
conditions (17), rather than merely proper-interior equations. Each split
retains both closed children.

The analytic origin cube is [0,1/256]^4. Its support census is complete:

* With singleton support {j}, a crossing observer i has
  F_i=q_j(J_ij q_j-Gamma_ij)>0, violating its zero-hazard condition.
* With support {i,j}, the active field at i is
  q_j(J_ij q_j-Gamma_ij). It cannot vanish: crossing Gamma is negative,
  while favorite Gamma_ij>J_ij>0. Both active hazards are proper here.
* Every three-owner support has an owner i whose favorite is absent.
  Write its other two members j,k. Both Gamma_ij and Gamma_ik are negative,
  the displayed final table has P_i({j,k})>=0 for this choice, and Q_i>=0.
  Put c=-Gamma_ij-Gamma_ik>0 and K_i=P_i({j,k}). For positive q_j,q_k<=d,
  dividing the passive expectation by q_jq_k gives
  P_i(q)/(q_jq_k)
  =Gamma_ij(1/q_k-1)+Gamma_ik(1/q_j-1)+K_i
  <=-c(1/d-1)+K_i<0,
  since d(c+K_i)<c at d=1/256. Thus F_i>0, whereas this proper active
  owner requires equality.
* With full support, F=-Gamma q+R(q). The exact constants are

      K=659197794573564328261/25159953591240500000,
      L=59425126500/10327361611,
      ||R(q)||_infinity<=K||q||_infinity^2, L K/256<1.

  Consequently F=0 forces q=0, outside full support.

The deterministic whole-cube run finishes with 566521 nodes, 283261
leaves and maximum depth62; precisely one leaf invokes the analytic origin
rule. A stopping budget can only raise an error. Every other leaf carries
an exact integer sign bound and the cube is covered in full. Hence there
is no exact stationary Nash profile at the final table.

This exclusion has a strictly positive full behavioral exploitability gap,
not merely absence of exact roots. The compactification proof in Section 7
applies verbatim with one phase: with at least two positive limiting
hazards, the full cap is the maximum of Quit-now and Never and is
continuous; a lone positive limiting owner harms a crossing observer; and
at the zero vector normalized first-exit masses give Gamma w>=0 and
Gamma_SS w_S=0 on the positive support. The same principal-block and
singleton-sign checks exclude the last case. The stationary gap persists
under a sufficiently small arbitrary perturbation of all sixty rewards
by the uniform2 eta bound. It excludes all vanishing-error stationary
families as well as all exact stationary producers.

## 9. Every true-punishment sure-first root is excluded

The actual punishment value of every owner at the center is exactly one.
Immediate Quit guarantees at least one against any opponents because all
actual participant rewards are at least one. Opponents choosing Never
make its best attainable payoff exactly one. Both minimax inequalities
are therefore explicit; no surrogate punishment annotation is being used.

For a first product root with at least one sure quitter, every non-sure
owner has a sure opponent. Its continuation is immaterial. A sure owner
can face all opponents Continue; its punishment continuation is one,
i.e. zero in the native coordinates. Thus, setting

    g_i=Q_i-P_i,                                   (18)

necessary root conditions on the entire sure boundary are

    q_i>0 implies g_i>=0,
    q_i<1 implies g_i<=0.                          (19)

The same conditions are necessary with EVERY arbitrary off-path behavioral
continuation. Its full response cap is at least one, since immediate Quit
still guarantees one. A sure owner's Continue deviation therefore has cap
at least P_i+H_i*0 in native coordinates, and its necessary Quit comparison
is no weaker than(19). This excludes sure-first equilibrium certificates
with arbitrary off-path tails, not only a stationary tail or a pure root.

For the faces q_a=1 with a=0,2,3, the exact Bernstein checker substitutes
that identity into (18), then checks all other coordinates in [0,1].
The sign rules are those of (19), and all closed children are retained.
The complete counts are

| Sure owner a | Nodes | Leaves | Maximum depth |
| --- | ---: | ---: | ---: |
| 0 | 127 | 64 | 15 |
| 2 | 157341 | 78671 | 44 |
| 3 | 19 | 10 | 5 |

The remaining face has a short exact proof. Set q_1=1 and write
x=q_0,y=q_2,z=q_3. Put delta=P_3(12)-1>0. Direct expansion gives

    g_2=(-12xz+2x+2z+3)/5,
    g_3=[26(1-x)(1-y)-25]/25-delta*y*(1-x).        (20)

If z>0, (19) forces g_3>=0 and hence (1-x)(1-y)>=25/26. In particular
x,y<=1/26. Formula(20) then gives g_2>0, because 2-12/26>0. Condition(19)
forces y=1, a contradiction. Therefore z=0. Now g_2=(2x+3)/5>0 forces
y=1. On that edge g_0=-P_0(12)>0 forces x=1. At (x,y,z)=(1,1,0),
however, g_1=-1, contradicting its sure-Quit condition. The checker verifies
all four displayed identities and strict constants exactly.

The union of these four compact faces is the entire sure-first boundary.
No pure, partly sure, fully sure, or mixed support is omitted. The absence
of a root is robust: the true punishment values change by at most eta
when each raw reward changes by at most eta. This follows by applying the
same payoff bound to every strategy pair and then taking suprema and
infima. The root Nash residual is continuous in the compact hazard cube,
raw rewards and punishment vector. Its positive minimum on the compact
sure boundary therefore persists for all sufficiently small raw reward
perturbations. The same lower-bound comparison covers arbitrary legitimate
equilibrium continuations there.

## 10. All fourteen response quotients, including positive row scales

A response-invariant quotient on a nontrivial partition requires the
response rows of two owners in every merged block to agree after the
block hazards are identified. Allow even arbitrary positive constant
recipient scales. At discount zero the relevant response polynomial is
exactly F in(16): the offset one cancels since
(1-H_i)(1+Q_i)-[(1-H_i)+P_i]=F_i. Proportional coefficient vectors are
necessary. A nonzero two-coefficient minor rules out all constant scales,
without choosing or bounding those scales.

For each partition below, blocks are written in the variable order used
by the monomial exponents. The two indicated rows belong to one merged
block. The checker constructs all fifteen set partitions, omits only the
discrete one, substitutes one variable per block, and verifies each
nonzero minor. An exponent such as001 means the third variable.

| Partition | Rows | Monomials | Nonzero minor |
| --- | --- | --- | --- |
| 01/2/3 | 0,1 | 001;010 | -1999/5000 |
| 1/02/3 | 0,2 | 001;010 | 8080001/2000000 |
| 1/2/03 | 0,3 | 001;010 | -2611/10000 |
| 0/12/3 | 1,2 | 001;010 | 217/1000 |
| 012/3 | 0,1 | 01;10 | -188/625 |
| 12/03 | 1,2 | 01;10 | 519/10000 |
| 0/2/13 | 1,3 | 001;010 | -589/5000 |
| 02/13 | 0,2 | 01;10 | 6879/2000 |
| 2/013 | 0,1 | 01;10 | 19/5 |
| 0/1/23 | 2,3 | 001;010 | 12561/100000 |
| 01/23 | 0,1 | 01;10 | -2563/625 |
| 1/023 | 0,2 | 01;10 | -820719/2000000 |
| 0/123 | 1,2 | 01;10 | -18917/20000 |
| 0123 | 0,1 | 1;2 | 3112221024252102198132230270331393557/289550476329036845482038736625000000 |

The discrete partition retains Gamma. It is R0: if a nonzero nonnegative
complementary vector has support S of size at least two, complementarity
would give Gamma_SS w_S=0, contrary to the exact principal-block checks.
A singleton support has a negative crossing residual. Also

    det Gamma=10327361611/10000000000>0,
    Gamma^{-1}>0.

Its R0 degree is therefore +1. The direct elementary degree calculation
is that at offset -1 every complementary solution satisfies
w=Gamma^{-1}(1+y)>0, where y>=0 is its residual. Complementarity forces
y=0, giving the unique regular solution Gamma^{-1}1 with positive
orientation. Thus the discrete quotient supplies no degree-not-one exit.
This agrees with the independently inspected theorem
`r0Degree_eq_sign_det_of_nonnegative_inverse` in
`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`; its separate R0
premise has just been supplied explicitly.

All fourteen minors stay nonzero under a sufficiently small arbitrary
reward perturbation. R0, its degree, and the strict matching signs likewise
persist here: the same finitely many nonzero principal minors and negative
singleton residuals retain their signs, and det Gamma and the positive
inverse retain theirs. Thus every nontrivial positively row-scaled response
partition is excluded throughout a reward neighborhood, while the discrete
partition retains degree one. The
source definition inspected was `QuittingResponseInvariantOnUnitCube` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
No quotient of a different, unspecified kind is being excluded.

## 11. Further complete raw-criterion comparisons

The stationary and fixed-pair gaps are architecture-wide. In particular,
no parameter choice in a raw criterion guaranteeing an exact stationary
profile or a proper fixed-disjoint-pair two-phase profile can apply here.
Nor can a sequence of stationary or fixed-pair approximate profiles have
vanishing full debt at the center. This includes any sufficiently-large-
jackpot criterion whose conclusion is a full-support stationary profile,
regardless of which coalition entries grow or how its threshold is chosen.
No numerical estimate of an unspecified threshold is used.

The comparisons below state their necessary guards explicitly. All owner
choices, relabelings and positive recipient factors are allowed. The
native own-singleton convention forces the offset to be the actual own
singleton. Thus offsets cancel in the comparisons and positive recipient
factors preserve every sign used below.

### 11.1 Complete polynomial row-weight and odds-wall exclusion

This rules out a broader class than testing finitely many weights. Choose
ANY positive odds rho_j and ANY four positive multiaffine row weights
m_i(u). Choose one favorite pair with an orientation, or both favorite
pairs with an orientation each. Define

    D_j(u)=1+(rho_j-1)u_j,
    psi_j(u_j)=rho_j*u_j/D_j(u),
    G_i(u)=m_i(u) product_(j!=i)D_j(u)^2 F_i(psi(u)). (21)

The necessary ordered-wall inequalities are G_i>=G_k wherever u_i=u_k
for each preferred owner i and its favorite partner k. These inequalities
may be weak. Any coefficientwise finite Bernstein wall test is included,
since its nonnegative coefficients imply these whole-wall inequalities.
We prove that NO such selection can pass at this center.

The multiplier in(21) is strictly positive and psi preserves every cube
face. Thus G and F have equivalent cube complementarity. Let K be the
cube restricted by u_i>=u_k for the selected oriented pairs. For eta>0
let v equal one at selected preferred owners and zero elsewhere. Brouwer
applied to the Euclidean projection of u+G(u)+eta*v onto K supplies a
point u with the variational inequality

    (G(u)+eta*v) dot (z-u)<=0 for every z in K.       (22)

Write f=G+eta*v. Away from tied pairs, individual feasible coordinate
changes give ordinary cube complementarity. At an interior tied pair,
increasing its preferred coordinate gives f_i<=0 and decreasing the
partner gives f_k>=0, whereas the wall inequality gives f_i>=f_k+eta.
This is impossible. At a tied zero pair, increasing the preferred
coordinate gives f_i<=0 and then f_k<0. At a tied one pair, decreasing
the partner gives f_k>=0 and then f_i>0. Hence(22) always gives ordinary
cube complementarity for f, including every tied boundary.

These points cannot collapse to zero as eta decreases to zero. At zero,

    G(0)=0, DG(0)=-M,
    M=diag(m_i(0))*Gamma*diag(rho_i).

If u tends to zero, divide the complementarity conditions by
max(||u||_infinity,eta), passing to a subsequence. The resulting w,tau
satisfy

    w>=0 in the ordered cone, tau>=0,
    M w>=tau*v, w_i((M w)_i-tau*v_i)=0,
    max(||w||_infinity,tau)=1.                     (23)

If tau=0, every support of size at least two would give a kernel vector
of a principal M block. Such blocks are nonsingular because the
corresponding Gamma blocks are nonsingular. A singleton support violates
a negative crossing coordinate of M w>=0. Thus tau cannot be zero.

If tau>0, choose any selected preferred pair i,k. Lower w_i to w_k to
obtain w'. The wall inequality, differentiated at the origin along w',
gives (M w')_i<=(M w')_k. Restoring w_i does not change row i because
M_ii=0, while it increases row k because M_ki>0. Therefore
(M w)_i<=(M w)_k. If w_k>0 then both i and k belong to the positive
support and(23) instead gives (M w)_i=tau and (M w)_k=0. If w_k=0,
row i has zero own contribution, zero favorite contribution and only
nonpositive crossing contributions, contradicting (M w)_i>=tau>0.
This exhausts(23) and proves noncollapse.

A nonzero limit point as eta decreases is consequently complementary for
G, so its psi image is nonzero and complementary for F. Section 8 excludes
that point. We have ruled out ALL positive odds, ALL positive multiaffine
row weights and every one-pair or two-pair orientation at once. Unbounded
parameter sequences are not an exception: any individual successful
selection would give this contradiction. The proof also applies on the
sufficiently small reward neighborhood where Section 8's gap and Section 10's
strict singleton facts persist. Own levels there remain positive, so no
negative-own boundary clause supplies an additional case.

### 11.2 Direct sign, core and calendar guards

Here are additional finite necessary guards and their complete failures:

| Necessary raw guard | Why every selection fails here |
| --- | --- |
| A rotating pair pattern requires a participant-pair premium -b/2 with b>0, with arbitrary ordered or unordered passive parameters. | All twelve J_ij are strictly positive. |
| A triple-singleton collision-box pattern requires J_ij-Gamma_ij>0 for all six directed pairs inside its chosen triple, before selecting any good subset of that triple. | Every three-owner subset contains a favorite pair with J_ij-Gamma_ij=-1. |
| A three-owner joint pattern requires two distinct positive off-diagonal singleton entries in one column. | Every Gamma column has exactly one positive off-diagonal entry. |
| A marked calendar chooses two unmarked owners, partitions the other owners into ordered nonempty blocks, and uses positive weights lambda_i. For every coalition C, the first block B meeting C must satisfy sum_(i in C intersect B)lambda_i Z_i(C)<=0. | Choose any marked i and any unmarked j. For C={i,j}, the required sum is lambda_i J_ij>0. Every choice of blocks and positive weights fails. |
| A literal passive-triple chamber has own singleton1, an adjacent participant reward-1, and an opposite participant reward0; free passive triple and grand rewards do not change these entries. | Its necessary negative participant-pair premiums contradict J_ij>0 under every relabeling or positive recipient factor. |
| A mixed-sign or joining-attractive triple-core condition requires the greatest premium core to contain exactly three owners. A premium core is a nonempty set in which each owner has a participant coalition inside the set paying strictly above its own singleton. | Every pair here is such a core; in particular the whole four-owner set is a core. The greatest core has size four. Independently every triple contains a negative favorite joining difference. |
| A signed-column two-pair construction requires r_i({i} union T)<=s_i-B_i with B_i>=0 for every nonempty T in i's opposite pair. | Every partition caps eight directed participant-pair premiums by a nonpositive number, while all twelve possible premiums are strictly positive. |

Two further parameter screens are useful even without the architecture
gaps. Suppose opposite-row comparison permits arbitrary positive native
recipient factors a_i. Preference0 toward1 requires simultaneously

    a0*Gamma_03<=a1*Gamma_13,
    a0*Gamma_01<=a1*Gamma_10.

They force a0/a1>=100 and a0/a1<=1100/1001. The reverse preference
requires a1*Gamma_12<=a0*Gamma_02 and a1*Gamma_10<=a0*Gamma_01, forcing
a1/a0>=20 and a1/a0<=1001/1100. Both orientations fail. The positive
singleton graph forces any favorite-pair selection to include01, so the
entire two-pair comparison criterion is excluded.

For a bounded inverse-corner or nonmatching positive-passive-pair test,
write B=Gamma^{-1}. Suppose its computed positive caps have definitions

    kappa=lower/(4 upper), Q>=3c_i,
    rmin<=1/(32 upper Q), ell_i=c_i kappa rmin/2,
    0<lower<=upper,

with an inverse box including its zero corner and a required pair cap
J_ij<=ell_i for every opposite scheduled owner j. Then
ell_i<=1/(768 upper). After row factor a_i>0, the zero corner forces
upper>=B_ii/a_i. Its necessary scale-invariant consequence is
J_ij B_ii<=1/768. Row1 violates this for EVERY other owner j:

    J_1j B_11>=262600550/10327361611>1/768.

Every schedule caps two such row 1 pairs, so all schedules, opposite-role
choices and positive recipient factors fail.

### 11.3 Product, trap and singleton-cycle guards

A condition requiring every nonempty product quitting support to have an
active owner whose conditional Quit reward is at most its own singleton
fails at the pure coalition02. Both active native Quit rewards J_02 and
J_20 are strictly positive. This excludes the complete product-low
condition, not just one selected support-peeling computation.

Call a nonempty set S a premium trap if each member has some participant
coalition inside S paying above its own singleton. All pairs are traps
here. A common leaver required to lie in EVERY trap cannot exist, since
there are disjoint traps01 and23. A support-specific leaver condition
requires some i in each trap S with

    r_i(T union{i})<=r_i(T)
    for every nonempty T subset S minus{i}.         (24)

For S={0,2}, each of its two owners has strictly positive joining
difference J_ij-Gamma_ij=-A_ij>0. Neither satisfies(24), regardless of
any protected-owner choices. The weighted alternative also fails: with
strictly positive trap weights, the subset T={2} has inserted leave sum
w_0(J_02-Gamma_02)>0. Hence even a weak nonpositive weighted leave-sum
condition cannot hold on this trap.

A no-harm singleton owner h must have Gamma_ih>=0 for EVERY i!=h.
Every column here has two negative crossings. A singleton escort edge
h to k requires Gamma_hk<=0<=Gamma_kh. Every mutual pair here instead
has two entries of the same strict sign, so there is no escort edge.
Consequently no nontrivial closed singleton escort walk, and no balanced
singleton cycle requiring such an edge at each change of owner, exists
at any period or under any relabeling. These are complete combinatorial
failures, not searches up to a selected period.

### 11.4 Every literal proper-child future/join certificate

Choose any nonempty proper child C of the four owners. For an outsider h,
the literal quiet-extension certificate seeks nonnegative weights w_i,
i in C, satisfying for EVERY nonempty S subset C

    -Z_h(S)<=-sum_(i in C) w_i Z_i(S),              (25)
    Z_h(S union{h})-Z_h(S)
      <=sum_(i in C)w_i[Z_i(S union{i})-Z_i(S)].   (26)

These are respectively the future-deadline and simultaneous-join rows.
Even the version dropping its separate joint-Never row requires(25)--(26).
We exclude these weaker requirements for every one of the fourteen
possible proper children. Consequently adding the Never row cannot help.

For a singleton child {j}, choose a crossing outsider h and use S={j}.
The left side of(26) is J_hj-Gamma_hj>0, while its right side is zero.
For pair children take S=C and the following outsider:

    C:          01  02  03  12  13  23
    outsider h:  2   3   1   0   2   1.

Each left side of(26) is strictly positive and every right side is zero.
In particular the tiny gain for child12 is -P_0(12)>0; it is not discarded
as a numerical zero.

For three of the triple children, the indicated joining row gives

    C=012, h=3, S=02: 1<=-w_1,
    C=013, h=2, S=01: 1<=-w_3,
    C=023, h=1, S=23: 1<=-w_0.

All are impossible. For the last triple C=123 and outsider0, the future
row S=12 requires

    -P_0(12)<=-(13/10)w_1-(9/20)w_2-P_3(12)w_3.   (27)

The left side is strictly positive and every coefficient on the right is
strictly negative. Thus no nonnegative weights satisfy it. This is a full
selection-set obstruction; no weight bound or selected linear-program
solution is used. A positive recipient factor for h can be divided out,
and factors for child owners are absorbed into the arbitrary nonnegative
weights. All fourteen failures therefore survive every positive row scaling.
Their strict sign margins also persist under sufficiently small raw
perturbations.

The stronger deadline-withdrawal security certificate also fails; this
does not follow merely from the capped-clock calculation. Such a
certificate adds arbitrary nonnegative withdrawal weights b_i to(26):

    Z_h(S union{h})-Z_h(S)
      <=sum_(i in C)[a_i A_i(S)+b_i W_i(S)],        (28)

where a_i,b_i>=0, A_i(S)=r_i(S union{i})-r_i(S), and

    W_i(S)=0 if i is not in S;
    W_i(S)=r_i(S minus{i})-r_i(S) if i is in S and |S|>=2;
    W_i({i})=ell_i-s_i.

Here the allowed terminal restart floor is
ell_i=max(ell_i^0,gamma_i), where ell_i^0 is the minimum of zero and
all passive child-coalition rewards, and gamma_i is the maximum over
hazards t in[0,1] of the minimum of s_i and the finitely many values
(1-t)r_i(T)+t r_i(T union{i}) for nonempty T subset C minus{i}.
Thus ell_i^0<=0 and gamma_i<=s_i. Our own rewards s_i=1 are positive,
so ell_i<=s_i. Truncating this floor at zero only decreases it. Both the
untruncated terminal and all-evaluation versions are included. In fact
the following proof allows ANY singleton floor at most s_i.

Choose the following rows; singleton children use any crossing outsider:

| Child C | Outsider h | Coalition S |
| --- | --- | --- |
| {j} | any crossing h of j | {j} |
| 01 | 2 | 1 |
| 23 | 1 | 2 |
| 02 | 3 | 02 |
| 03 | 1 | 03 |
| 12 | 0 | 12 |
| 13 | 2 | 13 |
| 012 | 3 | 02 |
| 013 | 2 | 13 |
| 023 | 1 | 03 |
| 123 | 0 | 12 |

In EVERY row the outsider's left side of(28) is strictly positive,
all child advance gains A_i(S) are nonpositive, and all withdrawal gains
are nonpositive. The checker verifies these statements for all fourteen
children. For a nonsingleton S in the table, S is crossing, so each
member's withdrawal gain is Gamma_ij-J_ij=A_ij<0. For singleton S,
the bound ell_i<=s_i gives the required nonpositive withdrawal. The only
nonzero advance gains are negative: for the two favorite children they
are -1, and for the four triple children they are respectively
-1,-1,-P_2(03),-P_3(12). The latter two passive rewards are strictly
positive. The outsider gains for the two favorite children are3/5 and3/2;
for the four triple children they are respectively
1,1,1-P_1(03),-P_0(12), all strictly positive.

Therefore(28) is impossible for every pair of nonnegative weight vectors,
even with the stronger security floors. This directly covers the larger
certificate rather than inferring its failure from a smaller sufficient
condition. Positive recipient factors are absorbed into the weights after
dividing by the outsider factor. The strict signs and positive own rewards
persist on a reward neighborhood, while the security bound ell_i<=s_i
continues to follow from its literal singleton constraint.

### 11.5. Exact class scope and open neighborhoods

Every direct obstruction above uses strict inequalities or a finite discrete
structure preserved by them. The all-parameter weighted-wall obstruction
uses the robust stationary gap and strict singleton structure. At r*, all
raw monotonicity guards used in Section 4 hold strictly, and every fixed-tube
sign and physical-gap test has a strict margin. Their exact algebraic
expressions are continuous. Therefore a full sixty-dimensional neighborhood
of r* satisfies the raw producer criterion. Intersect it with the two
architecture-gap neighborhoods, the sure-boundary neighborhood, the fourteen
nonzero-minor neighborhoods, and the direct-guard neighborhoods. This gives
a nonempty full sixty-dimensional open class with the produced equilibrium
and all the stated exclusions.

This neighborhood can also be chosen disjoint from the explicitly specified
10^{-9} cube around r0 in Section 2, because the displacement is 10^{-6}.
No numerical separation radius is asserted. The41-parameter slab is much
larger and unbounded in several directions; its other points are not claimed
to avoid the older criteria. No statement excludes all longer-period
strategies or an unspecified maximal neighborhood of another local theorem.
The mathematical increment is a reward-only scalar production theorem and
a broad explicit reward slab, with an audited point outside that stated
calibration cube. The full Fin4 conjecture remains open.

## 12. Source correspondence and standalone reproduction

The existing periodic consumer declarations were inspected directly:
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.
Their policy, exact root Nash and opponent-deleted contraction inputs
are all supplied above. These citations describe the consumer contract;
this ordinary proof is not a new Lean verification.

For the additional raw guards, the exact definitions
`HasProductLowQuittingPremium`, `HasSupportSpecificQuittingLeavers`,
`HasWeightedQuittingTrapLeavers`, and `IsCommonQuittingPremiumLeaver`
were inspected in the corresponding files
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`,
`UniformEquilibrium/Quitting/Classification/SupportSpecificQuittingPremiumLeavers.lean`,
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`,
and `UniformEquilibrium/Quitting/Classification/CommonQuittingPremiumLeaver.lean`.
The child rows are the literal requirements in
`CappedClockParentRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`
and `CappedClockParentFutureJoinCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPositiveSingletonQuietExtension.lean`.
The larger raw certificate `DeadlineSecurityRewardCertificate` was
inspected in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityMixedRaw.lean`,
its security optimization and singleton constraint in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityLP.lean`,
and its untruncated terminal counterpart
`DeadlineSecurityTerminalRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityTerminalDebt.lean`.
Their guards are fully written and contradicted above; no Lean verification
of the present table is inferred from reading those definitions.

Appendix A verifies all 300 branch tubes and all physical inactive gaps
throughout the entire passive interval[-1/10,1/5]. It requires only Python3.
Save its contents as BRANCH_CHECK.py and run

    python BRANCH_CHECK.py

Appendix B contains the complete literal table r* and all comparison code. It
requires Python3, SymPy and NumPy. Save it as COMPARISON_CHECK.py and run

    python COMPARISON_CHECK.py --full-comparison

Without the flag it checks the two fixed-pair covers, stationary origin,
analytic sure face, quotient minors, and direct child obstructions. With
the flag it also covers the entire stationary cube and remaining sure faces.
Every polynomial and bound is recomputed from the literal data. No numerical
root solver, floating-point acceptance tolerance, external checker, or
untracked certificate is a premise. The scalar IVT, full behavioral caps,
uniform horizons, compactness gaps, and direct criterion comparisons are
proved in the text.

For formalization the raw input should be the reward inequalities and the
fixed finite interval tests, not a structure field assuming a cyclic Nash
profile. The output consists of the produced rates and policy values, the
exact root inequalities at all three phases, opponent-cycle contraction,
and the resulting uniform-equilibrium payoff.

## Appendix A. Exact branch and slab checker

```python
"""Exact rational verification of a repeated-pair passive-reward slab.

All acceptance arithmetic uses Fraction. Literal queried data, fixed branch
tubes, endpoint signs, and all physical inactive caps are contained here.
The argument uses no numerical root solver or supplied equilibrium rates.
"""

from fractions import Fraction as F

G = (
    (F(0), F(1001,1000), F(-4), F(-1,1000)),
    (F(11,10), F(0), F(-1,5), F(-1,10)),
    (F(-1,2000), F(-3,20), F(0), F(101,100)),
    (F(-13,200), F(-39,1000), F(11,10), F(0)),
)
J = (
    (F(0), F(1,1000), F(1,100), F(9,1000)),
    (F(1,10), F(0), F(13,10), F(3,10)),
    (F(1,2000), F(9,20), F(0), F(1,100)),
    (F(1,200), F(1,1000), F(1,10), F(0)),
)
P_NATIVE = (
    -F(114126225102031811,2301677348322650000000),
    -F(348008157802289,2515995359124050000),
    F(16857064217550611361,16857006656318800000),
    F(1540799386594877837,1539763290995000000),
)
Q_TRIPLE = (F(0), F(1), F(0), F(0))
MATE=(3,2,1,0)
BETA={0:F(14),3:F(10,9)}
D={j:1+BETA[j] for j in (0,3)}
P_SCHEDULED={i:J[i][MATE[i]]/(D[MATE[i]] if i in (0,3) else 1) for i in range(4)}
C={i:P_SCHEDULED[i]-G[i][MATE[i]] for i in range(4)}
P=list(P_NATIVE)
for i in (1,2):
    P[i]=((1+BETA[0]*BETA[3])*P[i]+BETA[3]*G[i][0]+BETA[0]*G[i][3])/(D[0]*D[3])


class Interval:
    def __init__(self,lo,hi=None):
        self.lo=F(lo);self.hi=F(lo if hi is None else hi)
        assert self.lo<=self.hi
    def __add__(self,other):
        o=iv(other);return Interval(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return Interval(-self.hi,-self.lo)
    def __sub__(self,other):return self+-iv(other)
    def __rsub__(self,other):return iv(other)+-self
    def __mul__(self,other):
        o=iv(other);a=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi)
        return Interval(min(a),max(a))
    __rmul__=__mul__
    def __truediv__(self,other):
        o=iv(other);assert o.lo*o.hi>0
        return self*Interval(1/o.hi,1/o.lo)
    def __rtruediv__(self,other):return iv(other)/self
    def __repr__(self):return f'[{float(self.lo):.9g},{float(self.hi):.9g}]'


def iv(x):return x if isinstance(x,Interval) else Interval(x)


def active_interval(i,y1,y2,bits=44):
    """Unique positive effective mate hazard for an A recipient."""
    survival=(1-y1)*(1-y2)
    passive=G[i][1]*y1*(1-y2)+G[i][2]*y2*(1-y1)+P[i]*y1*y2
    assert passive>0
    lo=F(0);hi=F(1)
    for _ in range(bits):
        mid=(lo+hi)/2
        # Multiply the strictly decreasing unscaled equation by 1-mid.
        f=(passive+P_SCHEDULED[i]*mid*survival)*(1-mid)-C[i]*mid
        if f>0:lo=mid
        else:hi=mid
    return Interval(lo,hi)


def a_box(y1,y2):
    """Use the exact global signs of both active implicit derivatives."""
    y1=iv(y1);y2=iv(y2)
    r0lo=active_interval(3,y1.hi,y2.lo).lo
    r0hi=active_interval(3,y1.lo,y2.hi).hi
    r3lo=active_interval(0,y1.lo,y2.hi).lo
    r3hi=active_interval(0,y1.hi,y2.lo).hi
    return {0:Interval(r0lo,r0hi),1:y1,2:y2,3:Interval(r3lo,r3hi)}


def E(i,r,native_p1=None):
    j,k=[h for h in range(4) if h not in(i,MATE[i])]
    passive=P[i]
    if i==1 and native_p1 is not None:
        passive=((1+BETA[0]*BETA[3])*native_p1+BETA[3]*G[1][0]+BETA[0]*G[1][3])/(D[0]*D[3])
    return (G[i][j]*r[j]*(1-r[k])+G[i][k]*r[k]*(1-r[j])+passive*r[j]*r[k]
            +P_SCHEDULED[i]*r[MATE[i]]*(1-r[j])*(1-r[k])
            -C[i]*r[MATE[i]]/(1-r[MATE[i]]))


def g2_interval(y1,y2):
    """Exact partial signs yield sharper bounds than naive intervals."""
    r=a_box(y1,y2)
    lower={0:r[0].hi,1:r[1].hi,2:r[2].lo,3:r[3].lo}
    upper={0:r[0].lo,1:r[1].lo,2:r[2].hi,3:r[3].hi}
    return Interval(E(2,lower),E(2,upper))


def original_gaps(r,native_p1=None):
    u={j:r[j]/D[j] for j in (0,3)}
    v={j:BETA[j]*r[j]/(D[j]-r[j]) for j in (0,3)}
    gaps={}
    for i in (0,3):
        value=C[i]*r[MATE[i]]/(1-r[MATE[i]])
        quit=J[i][1]*r[1]*(1-r[2])+J[i][2]*r[2]*(1-r[1])+Q_TRIPLE[i]*r[1]*r[2]
        gaps[2,i]=value-quit
    for i in (1,2):
        passive=P_NATIVE[i] if i!=1 or native_p1 is None else native_p1
        value2=P_SCHEDULED[i]*r[MATE[i]]
        value1=(G[i][0]*v[0]*(1-v[3])+G[i][3]*v[3]*(1-v[0])
                +passive*v[0]*v[3]+(1-v[0])*(1-v[3])*value2)
        value0=(G[i][0]*u[0]*(1-u[3])+G[i][3]*u[3]*(1-u[0])
                +passive*u[0]*u[3]+(1-u[0])*(1-u[3])*value1)
        for phase,hazards,value in ((0,u,value0),(1,v,value1)):
            quit=(J[i][0]*hazards[0]*(1-hazards[3])
                  +J[i][3]*hazards[3]*(1-hazards[0])
                  +Q_TRIPLE[i]*hazards[0]*hazards[3])
            gaps[phase,i]=value-quit
    return gaps


def main():
    assert all(J[i][MATE[i]]>0 for i in range(4))
    assert all(G[i][MATE[i]]<0 for i in range(4))
    assert all(BETA[j]==(J[MATE[j]][j]-G[MATE[j]][j])/J[MATE[j]][j] for j in (0,3))
    # Raw comparisons establish all monotonicity used by a_box/g2_interval.
    assert G[0][1]>=P_SCHEDULED[0] and P[0]>G[0][2] and P[0]<G[0][1]
    assert G[3][2]>=P_SCHEDULED[3] and G[3][1]<=P[3]<=G[3][2]
    assert G[2][0]<=P[2]<=G[2][3] and G[2][3]>P_SCHEDULED[2]
    assert C[2]>P_SCHEDULED[2]
    left=F(48,100);right=F(51,100);count=300
    certificates=[];gap_lower={};sign_margin=None;slab_gap_lower={}
    slab=Interval(-F(1,10),F(1,5))
    overall={i:None for i in range(4)}
    for n in range(count):
        ylo=left+(right-left)*n/count;yhi=left+(right-left)*(n+1)/count
        mid=(ylo+yhi)/2
        center=Interval(F(3,5)*mid-F(51233,500000)+(mid-F(49351,100000))**2/2)
        radius=F(1,8000)
        yl=center.lo-radius;yu=center.hi+radius
        for yy in (ylo,yhi):
            for tt in (yl,yu):
                for i in (0,3):
                    passive=G[i][1]*yy*(1-tt)+G[i][2]*tt*(1-yy)+P[i]*yy*tt
                    assert passive>0
        low_sign=g2_interval(Interval(ylo,yhi),yl)
        high_sign=g2_interval(Interval(ylo,yhi),yu)
        assert low_sign.lo>0 and high_sign.hi<0,(n,low_sign,high_sign)
        margin=min(low_sign.lo,-high_sign.hi)
        sign_margin=margin if sign_margin is None else min(sign_margin,margin)
        r=a_box(Interval(ylo,yhi),Interval(yl,yu))
        for i in range(4):
            old=overall[i]
            overall[i]=r[i] if old is None else Interval(min(old.lo,r[i].lo),max(old.hi,r[i].hi))
        gaps=original_gaps(r)
        for key,value in gaps.items():
            assert value.lo>0,(n,key,value)
            gap_lower[key]=min(gap_lower.get(key,value.lo),value.lo)
        for key,value in original_gaps(r,slab).items():
            assert value.lo>0,('slab',n,key,value)
            slab_gap_lower[key]=min(slab_gap_lower.get(key,value.lo),value.lo)
        certificates.append((ylo,yhi,yl,yu))
    endpoints=((left,F(1856348,10**7),F(1856349,10**7),1),
               (right,F(2036449,10**7),F(2036450,10**7),-1))
    for y,lo,hi,sgn in endpoints:
        assert g2_interval(y,lo).lo>0 and g2_interval(y,hi).hi<0
        z=Interval(lo,hi);r=a_box(y,z);g1=E(1,r)
        assert (g1.lo>F(1,25) if sgn==1 else g1.hi<-F(1,20))
        slab_g1=E(1,r,slab)
        assert (slab_g1.lo>F(1,50) if sgn==1 else slab_g1.hi<-F(1,125))
        print('Endpoint y1',y,'y2',z,'G1',g1)
        print('Slab endpoint G1',slab_g1)
    targets={(2,0):F(1,250),(2,3):F(17,100),(0,1):F(21,100),
             (1,1):F(3,100),(0,2):F(1,2),(1,2):F(2,5)}
    assert all(gap_lower[key]>bound for key,bound in targets.items())
    slab_targets=dict(targets)
    slab_targets[0,1]=F(9,50)
    slab_targets[1,1]=F(1,3000)
    assert all(slab_gap_lower[key]>bound for key,bound in slab_targets.items())
    assert sign_margin>F(1,250)
    print('All 300 branch cells: exact strict G2 boundary signs PASS')
    print('Certified original inactive gap bounds', {str(k):str(v) for k,v in targets.items()})
    print('G2 uniform boundary sign margin exceeds 1/250')
    print('Overall hazard enclosures',overall)
    print('Certified slab original gap bounds', {str(k):str(v) for k,v in slab_targets.items()})
    return certificates,gap_lower


if __name__=='__main__':main()

```

## Appendix B. Complete comparison checker

```python
"""Exact complete comparisons at an explicit repeated-pair slab point.

All proof arithmetic is rational or Python integer. All literal raw data and checking code needed by this calibration are
contained here, including the integer Bernstein subdivision routines.
No numerical root solver is used and no certificate box is accepted merely
because a search budget expires.
"""
import argparse
import itertools
import json
from fractions import Fraction
import numpy as np
import sympy as s

I=range(4)
A=s.Matrix([[0,1,-6,-s.Rational(1,100)],
 [1,0,-s.Rational(3,2),-s.Rational(2,5)],
 [-s.Rational(1,1000),-s.Rational(3,5),0,1],
 [-s.Rational(7,100),-s.Rational(1,25),1,0]])
J=s.Matrix([[0,s.Rational(1,1000),2,s.Rational(9,1000)],
 [s.Rational(1,10),0,s.Rational(13,10),s.Rational(3,10)],
 [s.Rational(1,2000),s.Rational(9,20),0,s.Rational(1,100)],
 [s.Rational(1,200),s.Rational(1,1000),s.Rational(1,10),0]])
Gamma=A+J
J[0,2]=s.Rational(1,100)
A=Gamma-J
q=s.symbols('q0:4')
SIGNS={(0,1):1,(0,2):-1,(0,3):1,(1,2):1,(1,3):-1,(2,3):-1}

def table():
    z={}
    for i in I:
        for mask in range(1,16):
            opp=[j for j in I if mask>>j&1 and j!=i]
            if not opp:
                value=0
            elif len(opp)==1:
                value=J[i,opp[0]] if mask>>i&1 else Gamma[i,opp[0]]
            elif len(opp)==2:
                outside=[j for j in I if j not in opp]
                delta=SIGNS[tuple(opp)]*(1 if i==outside[0] else -1)
                value=max(0,delta) if mask>>i&1 else max(0,-delta)
            else:
                value=0 if mask>>i&1 else 1
            z[i,mask]=s.Rational(value)
    z[0,7]=0
    z[0,6]=-s.Rational(114126225102031811,2301677348322650000000)
    z[1,9]=-s.Rational(348008157802289,2515995359124050000)-s.Rational(1,10**6)
    z[2,9]=s.Rational(16857064217550611361,16857006656318800000)
    z[3,6]=s.Rational(1540799386594877837,1539763290995000000)
    return z

def fields(z,mate):
    equations=[];gaps=[]
    for i in I:
        j,k=[a for a in I if a not in(i,mate[i])]
        m=mate[i];p=J[i,m];c=-A[i,m]
        passive=z[i,(1<<j)|(1<<k)]
        joining=z[i,(1<<i)|(1<<j)|(1<<k)]
        D=(1-q[j])*(1-q[k])
        C=(Gamma[i,j]*q[j]*(1-q[k])+Gamma[i,k]*q[k]*(1-q[j])
           +passive*q[j]*q[k]+p*q[m]*D)
        Q=J[i,j]*q[j]*(1-q[k])+J[i,k]*q[k]*(1-q[j])+joining*q[j]*q[k]
        equations.append(s.Poly(s.expand((1-q[m])*C-c*q[m]),*q))
        gaps.append(s.Poly(s.expand((1-q[m])*Q-c*q[m]),*q))
    for i in I:
        assert equations[i].total_degree()<=4
        assert equations[i].coeff_monomial(1)==0
        for j in I:
            assert equations[i].coeff_monomial(q[j])==Gamma[i,j]
    assert all(p.degree(variable)<=2 for p in equations+gaps for variable in q)
    return equations,gaps

def coefficients(polys):
    raw=[]
    for p in polys:
        for alpha in itertools.product(range(3),repeat=4):
            raw.append(sum(value*s.prod(s.binomial(alpha[j],mon[j])/s.binomial(2,mon[j])
                           for j in I)for mon,value in p.terms()
                           if all(mon[j]<=alpha[j]for j in I)))
    denominator=int(s.ilcm(*(s.denom(v)for v in raw)))
    arr=np.array([int(v*denominator)for v in raw],dtype=object).reshape(8,3,3,3,3)
    return denominator,arr

def split(b,axis):
    v=np.moveaxis(b,axis+1,-1)
    a0,a1,a2=v[...,0],v[...,1],v[...,2]
    mid=a0+2*a1+a2
    left=np.stack((4*a0,2*(a0+a1),mid),axis=-1)
    right=np.stack((mid,2*(a1+a2),4*a2),axis=-1)
    return np.moveaxis(left,-1,axis+1),np.moveaxis(right,-1,axis+1)

def certify(z,mate):
    equations,gaps=fields(z,mate)
    L=max(sum(abs(v)for v in row)for row in Gamma.inv().tolist())
    K=max(sum(abs(v)for mon,v in p.terms()if sum(mon)>=2)for p in equations)
    delta=Fraction(1,256)
    assert L*K*s.Rational(1,256)<1
    den,b=coefficients(equations+gaps)
    stack=[(b,(Fraction(0),)*4,(Fraction(1),)*4,'')]
    leaves=[];nodes=0;maxdepth=0
    while stack:
        b,lo,hi,path=stack.pop();nodes+=1;maxdepth=max(maxdepth,len(path))
        reason=None;bound=None;index=None
        if max(hi)<=delta:
            reason='analytic_origin'
        else:
            flat=b.reshape(8,-1)
            mins=[min(row)for row in flat];maxs=[max(row)for row in flat]
            for i in I:
                if mins[i]>0:
                    reason,index,bound='equation_positive',i,int(mins[i]);break
                if maxs[i]<0:
                    reason,index,bound='equation_negative',i,int(maxs[i]);break
            if reason is None:
                for i in I:
                    if mins[4+i]>0:
                        reason,index,bound='inactive_gap_positive',i,int(mins[4+i]);break
        if reason is not None:
            leaves.append({'path':path,'reason':reason,'index':index,'integer_bound':bound,
                           'denominator':den*4**len(path),'lo':list(map(str,lo)),
                           'hi':list(map(str,hi))})
            continue
        if len(path)>=100 or nodes>1000000:
            raise RuntimeError('Unresolved box: no proof accepted at a stopping budget')
        axis=max(I,key=lambda i:hi[i]-lo[i]);mid=(lo[axis]+hi[axis])/2
        left,right=split(b,axis)
        lo1=list(lo);lo1[axis]=mid
        hi0=list(hi);hi0[axis]=mid
        stack.append((right,tuple(lo1),hi,path+'1'))
        stack.append((left,lo,tuple(hi0),path+'0'))
    return {'mate':mate,'L':str(L),'K':str(K),'delta':str(delta),
            'nodes':nodes,'maxdepth':maxdepth,'leaves':leaves}


# Exact stationary complementarity sign-cover routines.
def stationary_fields(z):
    H=[];P=[];QQ=[]
    for i in I:
        pp=qq=0
        for mask in range(16):
            if mask>>i&1:continue
            w=s.prod(q[j] if mask>>j&1 else 1-q[j] for j in I if j!=i)
            pp+=z[i,mask]*w
            qq+=z[i,mask|1<<i]*w
        H.append(s.prod(1-q[j] for j in I if j!=i))
        P.append(s.expand(pp));QQ.append(s.expand(qq))
    F=[s.Poly(s.expand((1-H[i])*QQ[i]-P[i]),*q)for i in I]
    g=[s.expand(QQ[i]-P[i])for i in I]
    return H,F,g

def stationary_coefficients(polys):
    assert all(poly.degree(q[j])<=2 for poly in polys for j in I)
    raw=[]
    for i in I:
        for alpha in itertools.product(range(3),repeat=4):
            value=sum(v*s.prod(s.binomial(alpha[j],mon[j])/s.binomial(2,mon[j])
                        for j in I) for mon,v in polys[i].terms()
                        if all(mon[j]<=alpha[j] for j in I))
            raw.append(s.sympify(value))
    denominator=int(s.ilcm(*(s.denom(v)for v in raw)))
    arr=np.array([int(v*denominator)for v in raw],dtype=object).reshape(4,3,3,3,3)
    return denominator,arr

def stationary_split_coefficients(b,axis):
    # Both child arrays represent their exact polynomials at FOUR TIMES
    # the parent's positive common denominator. Thus all sign tests below
    # use integers only; no interval rounding or tolerance is involved.
    v=np.moveaxis(b,axis+1,-1)
    a0,a1,a2=v[...,0],v[...,1],v[...,2]
    middle=a0+2*a1+a2
    left=np.stack((4*a0,2*(a0+a1),middle),axis=-1)
    right=np.stack((middle,2*(a1+a2),4*a2),axis=-1)
    return np.moveaxis(left,-1,axis+1),np.moveaxis(right,-1,axis+1)

def stationary_certify(polys,lo,hi,origin_delta=None,max_nodes=200000,max_depth=120):
    denominator,b=stationary_coefficients(polys)
    stack=[(list(lo),list(hi),b,0,'')]
    leaves=[];nodes=0;maxdepth=0
    while stack:
        lo,hi,b,depth,path=stack.pop()
        nodes+=1;maxdepth=max(maxdepth,depth)
        record={'path':path,'lo':list(map(str,lo)),'hi':list(map(str,hi))}
        if origin_delta is not None and max(hi)<=origin_delta:
            record['kind']='origin';leaves.append(record);continue
        witness=None
        for i in I:
            row=b[i].flatten()
            if lo[i]>0 and max(row)<0:
                witness=(i,'negative',int(max(row)));break
            if hi[i]<1 and min(row)>0:
                witness=(i,'positive',int(min(row)));break
        if witness is not None:
            i,sign,bound=witness
            record.update(kind='field',owner=i,sign=sign,numerator=str(bound),
                          denominator=str(denominator*4**depth))
            leaves.append(record);continue
        if depth>=max_depth or nodes>=max_nodes:
            raise RuntimeError('Unexcluded box after budget: '+str({
                'nodes':nodes,'depth':depth,'lo':list(map(str,lo)),
                'hi':list(map(str,hi)),'stack':len(stack)}))
        widths=[hi[i]-lo[i]for i in I]
        maximum=max(widths)
        choices=[i for i in I if widths[i]==maximum]
        axis=choices[depth%len(choices)]
        left,right=stationary_split_coefficients(b,axis)
        middle=(lo[axis]+hi[axis])/2
        lower=lo.copy();lower[axis]=middle
        upper=hi.copy();upper[axis]=middle
        # Every split retains BOTH closed children, whose union is the
        # parent. Starting with the whole cube or face proves coverage.
        stack.append((lower,hi,right,depth+1,path+str(axis)+'1'))
        stack.append((lo,upper,left,depth+1,path+str(axis)+'0'))
    assert nodes==2*len(leaves)-1
    return {'nodes':nodes,'depth':maxdepth,'source_denominator':denominator,'leaves':leaves}


def partitions(items):
    if not items:
        yield []
        return
    first,*rest=items
    for part in partitions(rest):
        yield [[first]]+[block[:] for block in part]
        for j in range(len(part)):
            yield [([first]+block if k==j else block[:])
                   for k,block in enumerate(part)]


def class_comparison(z,full):
    native=dict(z)
    native.update({(i,0):s.S.Zero for i in I})
    H,F,g=stationary_fields(native)
    fav=(1,0,3,2)
    assert all(F[i].coeff_monomial(1)==0 for i in I)
    assert all(F[i].coeff_monomial(q[j])==-Gamma[i,j] for i in I for j in I)
    K=max(sum(abs(v) for mon,v in f.terms() if sum(mon)>=2) for f in F)
    L=max(sum(abs(v) for v in row) for row in Gamma.inv().tolist())
    delta=s.Rational(1,256)
    assert L==s.Rational(59425126500,10327361611)
    assert K==s.Rational(659197794573564328261,25159953591240500000)
    assert K*L*delta<1
    for owner in I:
        other=next(i for i in I if i not in(owner,fav[owner]))
        t=s.Symbol('t')
        test=F[other].as_expr().subs({q[i]:t if i==owner else 0 for i in I})
        assert s.expand(test-t*(J[other,owner]*t-Gamma[other,owner]))==0
        assert J[other,owner]>0 and Gamma[other,owner]<0
    for i,j in itertools.combinations(I,2):
        t=s.Symbol('t')
        test=F[i].as_expr().subs({q[h]:t if h==j else 0 for h in I})
        assert s.expand(test-t*(J[i,j]*t-Gamma[i,j]))==0
        assert Gamma[i,j]<0 or Gamma[i,j]>J[i,j]>0
    triple_records=[]
    for support in itertools.combinations(I,3):
        i=next(i for i in support if fav[i] not in support)
        j,k=[h for h in support if h!=i]
        c=-Gamma[i,j]-Gamma[i,k]
        passive=z[i,(1<<j)|(1<<k)]
        assert c>0 and passive>=0 and delta*(c+passive)<c
        triple_records.append((support,i,str(c),str(passive)))
    print('PASS: complete stationary analytic origin; K=',K,'L=',L,flush=True)

    # Entire sure-owner-1 face, analytically, including all zero/sure edges.
    x,y,zz=q[0],q[2],q[3]
    gface=[s.expand(v.subs(q[1],1)) for v in g]
    correction=z[3,6]-1
    assert correction>0
    assert s.expand(gface[2]-(-12*x*zz+2*x+2*zz+3)/5)==0
    assert s.expand(gface[3]-((26*(1-x)*(1-y)-25)/25
                              -correction*y*(1-x)))==0
    assert s.expand(gface[0].subs({y:1,zz:0})+z[0,6])==0
    assert gface[1].subs({x:1,y:1,zz:0})==-1
    assert s.Rational(2)-s.Rational(12,26)>0
    print('PASS: exact sure-owner-1 face identities and strict sign chain',flush=True)

    quotient_records=[]
    for part in partitions(list(I)):
        if len(part)==4:continue
        variables=s.symbols('t:'+str(len(part)))
        sub={q[i]:variables[j] for j,block in enumerate(part) for i in block}
        polys=[s.Poly(f.as_expr().subs(sub),*variables) for f in F]
        witness=None
        for block in part:
            for i,j in itertools.combinations(block,2):
                monoms=sorted(set(polys[i].monoms())|set(polys[j].monoms()),
                              key=lambda mon:(sum(mon),mon))
                for a,b in itertools.combinations(monoms,2):
                    minor=(polys[i].coeff_monomial(a)*polys[j].coeff_monomial(b)
                           -polys[i].coeff_monomial(b)*polys[j].coeff_monomial(a))
                    if minor!=0:
                        witness={'rows':[i,j],'monomials':[a,b],'minor':str(minor)}
                        break
                if witness:break
            if witness:break
        assert witness is not None
        quotient_records.append({'partition':part,**witness})
    assert len(quotient_records)==14
    assert Gamma.inv()[1,1]*min(J[1,j] for j in I if j!=1)==s.Rational(262600550,10327361611)>s.Rational(1,768)
    assert Gamma[1,0]/Gamma[0,1]==s.Rational(1100,1001)<100
    assert Gamma[0,1]/Gamma[1,0]==s.Rational(1001,1100)<20
    assert Gamma.det()==s.Rational(10327361611,10000000000)>0
    # Together with the principal-minor and singleton-sign tests above,
    # inverse positivity gives R0 degree +1, not the old non-Q guard.
    print('PASS: all fourteen positively row-scaled response quotients excluded',flush=True)
    # Literal proper-child future/join row obstructions, all nonnegative weights.
    for child in I:
        outside=next(i for i in I if i not in(child,fav[child]))
        assert z[outside,(1<<child)|(1<<outside)]-z[outside,1<<child]>0
    for child,outside in (((0,1),2),((0,2),3),((0,3),1),
                          ((1,2),0),((1,3),2),((2,3),1)):
        mask=sum(1<<i for i in child)
        assert z[outside,mask|(1<<outside)]-z[outside,mask]>0
    for child,outside,coalition in (((0,1,2),3,(0,2)),
                                    ((0,1,3),2,(0,1)),
                                    ((0,2,3),1,(2,3))):
        mask=sum(1<<i for i in coalition)
        assert z[outside,mask|(1<<outside)]-z[outside,mask]==1
        absent=next(i for i in child if i not in coalition)
        assert z[absent,mask|(1<<absent)]-z[absent,mask]==-1
    assert -z[0,6]>0
    assert [z[i,6] for i in (1,2,3)]==[s.Rational(13,10),s.Rational(9,20),z[3,6]]
    assert all(z[i,6]>0 for i in (1,2,3))
    print('PASS: all fourteen literal proper-child future/join obstructions',flush=True)
    security_rows=[((i,),next(h for h in I if h not in(i,fav[i])),(i,)) for i in I]
    security_rows += [((0,1),2,(1,)),((2,3),1,(2,)),
                      ((0,2),3,(0,2)),((0,3),1,(0,3)),
                      ((1,2),0,(1,2)),((1,3),2,(1,3)),
                      ((0,1,2),3,(0,2)),((0,1,3),2,(1,3)),
                      ((0,2,3),1,(0,3)),((1,2,3),0,(1,2))]
    assert len(security_rows)==14
    for child,outside,coalition in security_rows:
        mask=sum(1<<i for i in coalition)
        assert z[outside,mask|(1<<outside)]-z[outside,mask]>0
        for i in child:
            advance=z[i,mask|(1<<i)]-z[i,mask]
            assert advance<=0
            if i not in coalition:continue
            if len(coalition)>1:
                withdrawal=z[i,mask^(1<<i)]-z[i,mask]
                assert withdrawal<0
            else:
                # A singleton withdrawal floor is <= own reward, by the
                # security LP singleton row and zeroFloor<=0<own reward.
                assert z[i,1<<i]==0
    print('PASS: all fourteen literal security-withdrawal child obstructions',flush=True)

    result={'K':str(K),'L':str(L),'delta':str(delta),
            'triple_origin':triple_records,'quotients':quotient_records}
    if full:
        stationary=stationary_certify(F,[Fraction(0)]*4,[Fraction(1)]*4,
                                     Fraction(1,256),1000000,120)
        assert (stationary['nodes'],len(stationary['leaves']),stationary['depth'])==(566521,283261,62)
        assert sum(leaf['kind']=='origin' for leaf in stationary['leaves'])==1
        print('PASS: ENTIRE stationary cube',stationary['nodes'],len(stationary['leaves']),stationary['depth'],flush=True)
        faces={}
        for anchor,expected in ((0,(127,64,15)),(2,(157341,78671,44)),(3,(19,10,5))):
            polys=[s.Poly(v.subs(q[anchor],1),*q) for v in g]
            lo=[Fraction(0)]*4;hi=[Fraction(1)]*4
            lo[anchor]=hi[anchor]=Fraction(1)
            face=stationary_certify(polys,lo,hi,None,200000,100)
            assert (face['nodes'],len(face['leaves']),face['depth'])==expected
            faces[anchor]=face
            print('PASS: ENTIRE true-punishment sure face',anchor,face['nodes'],len(face['leaves']),face['depth'],flush=True)
        result.update(stationary=stationary,sure_faces=faces)
    else:
        print('Complete stationary/sure covers require --full-comparison.',flush=True)
    return result


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--full-comparison',action='store_true')
    args=parser.parse_args()
    z=table()
    theta0=-s.Rational(348008157802289,2515995359124050000)
    assert z[1,9]==theta0-s.Rational(1,10**6)
    assert -s.Rational(1,10)<z[1,9]<s.Rational(1,5)
    assert abs(z[1,9]-theta0)>s.Rational(1,10**9)
    assert len(z)==60
    assert all(z[i,1<<i]==0 for i in I)
    assert all(z[i,mask]>=0 for i in I for mask in range(1,16) if mask>>i&1)
    assert max(abs(1+value) for value in z.values())==3
    assert all(v>0 for v in Gamma.inv()) and all(v>0 for v in A.inv())
    assert all(J[i,j]>0 for i in I for j in I if j!=i)
    fav=(1,0,3,2)
    assert all(A[i,fav[i]]==1 for i in I)
    assert all(Gamma[i,j]<0 for i in I for j in I if j not in(i,fav[i]))
    assert all(Gamma.extract(S,S).det()!=0 for size in (2,3,4)
               for S in itertools.combinations(I,size))
    for a,b in itertools.combinations(I,2):
        if fav[a]==b:
            assert J[a,b]<Gamma[a,b]
            continue
        mask=(1<<a)|(1<<b)
        assert any(z[i,mask|(1<<i)]>z[i,mask] for i in I if i not in(a,b))
    records=[certify(z,mate) for mate in ((2,3,0,1),(3,2,1,0))]
    assert [(r['nodes'],len(r['leaves']),r['maxdepth']) for r in records]==[(103,52,32),(893,447,39)]
    for record in records:
        print('PASS: complete crossing schedule',record['mate'],record['nodes'],len(record['leaves']),record['maxdepth'],flush=True)
    comparison=class_comparison(z,args.full_comparison)
    print('PASS: literal displacement is 10^-6 > 10^-9; branch slab contains it',flush=True)
    return comparison

if __name__=='__main__':main()

```
