# Periodic uniform equilibria without positive triple eigenmodes

A four-player quitting family has a proper sixty-four-phase equilibrium at
its zero endpoint and for every sufficiently small positive parameter. A
separate twenty-five-phase equilibrium is produced at the explicit parameter
1/1000. Every positive-parameter table has no positive real eigenvalue on any
of its four triple transverse maps. Each certified table has a full
sixty-dimensional open UE neighborhood. On the same parameter interval,
stationary and fixed disjoint-pair profiles have positive full behavioral
exploitability gaps, and all sure-first roots fail. Complete raw-selector
comparisons and standalone exact checkers are included below. The general
Fin4 UE conjecture remains open.

## 1. Raw family, literal table and theorem

Four players `I={0,1,2,3}` independently choose Continue or Quit at one live
state. Every nonempty quitter coalition absorbs permanently. Live and Never
rewards are zero. Actual absorbing rewards are `r_i(S)=1+Z_i(S)`, with own
native singleton rewards `Z_i({i})=0`.

For `0≤δ≤1/1000` define

```
Aδ = [0       1       -6       -1/100]
     [1       0       -3/2     -2/5]
     [-δ     -3/5      0        1]
     [-7/100 -1/25     1        0].
```

The favorite pairs are01 and23. Every favorite premium is `J_i,f(i)=1/100`.
On the directed crossings `02,21,13,30` set `J_ij=−(9/10)A_ij`; on the
other four crossings set `J_ij=−(1/10)A_ij`. Put `Γ=A+J`, and set

```
Z_i({j})=Γ_ij,             Z_i({i,j})=J_ij,     i≠j.
```

For opponent pairs `B=01,02,03,12,13,23`, respectively assign signs
`+1,−1,+1,+1,−1,−1`. The smaller outsider receives this sign as `Δ_i(B)`;
the larger receives its negative. Set

```
Z_i(B)=max(0,−Δ_i(B)),     Z_i(B∪{i})=max(0,Δ_i(B)),
Z_i(I\{i})=1,            Z_i(I)=0.
```

These rules specify all sixty raw entries. The varying entries are
`Z_2({0})=−9δ/10` and `Z_2({0,2})=δ/10`.

At every positive parameter, Γ and A have strict favorite-positive,
crossing-negative signs, all twelve participant pair premiums are positive,
and both Γ and A have strictly positive inverses. These inverse assertions
follow by exact endpoint determinant and adjugate checks: the matrices vary
in only their20 entry, so all those polynomials are affine in δ. The literal
checkers include the required identities and endpoint positivity.

**Theorem.** There is δ*>0 such that every table with `0≤δ<δ*` has an
exact terminal Nash profile repeating the physical support word

```
sixty copies of012, followed by013,013,013,013.             (1a)
```

The table at `δ=1/1000` also has an exact terminal Nash profile repeating

```
123,123,023,023,023, followed by twenty copies of012.        (1b)
```

Every scheduled hazard is strictly between zero and one; every omitted owner
strictly prefers Continue. Each profile supplies one fixed UE payoff against
all behavioral deviations. There is a full sixty-dimensional open reward
neighborhood of the zero endpoint with the first conclusion, and another
such neighborhood of the explicit1/1000 table with the second conclusion.
At each positive parameter certified by these conclusions, the neighborhood
can retain both positive inverses, all strict matching signs, absence of any
positive real triple eigenvalue, the complete architecture gaps and the
stated raw-selector exclusions.

The comparison proofs cover the whole closed interval`[0,1/1000]`. The
producer does not claim every intermediate parameter: its explicit scope is
the endpoint neighborhood, all sufficiently small positive parameters and
the separate1/1000 neighborhood. No minimal-period or complete periodic
strategy classification is claimed.

## 2. Every triple lacks a positive real eigenvalue

For a triple S, its transverse root derivative at zero is
`M_S=−J_S A_S^-1`. Let λ be real. Exact determinant expansion gives

```
det(λA_S+J_S)
 =(λ+1/100)[K_H(S)(λ−9/10)²+K_L(S)(λ−1/10)²],             (2)
```

with

| S | K_H | K_L |
| --- | ---: | ---: |
| 012 | 18/5 | 3δ/2 |
| 013 | 7/250 | 1/2500 |
| 023 | 21/50 | δ/100 |
| 123 | 6/25 | 3/50 |

For every positive δ, both weights are positive. The bracket in (2) is
strictly positive for every real λ, since its two squared terms cannot
vanish together. Each A_S is invertible, with determinant `K_H+K_L>0`.
Thus M_S has the negative eigenvalue `−1/100` and a nonreal conjugate pair,
and no positive real eigenvalue. This exhausts all four triples, not merely
the supports chosen for the cycle.

Positive recipient scaling sends `(A_S,J_S)` to `(D A_S,D J_S)` and M_S to
`D M_S D^-1`. Relabeling also conjugates these matrices. Hence no positive
row-scale or role choice creates a positive real mode. At the literal table,
the negative eigenvalue is strictly below zero and the conjugate pair has
nonzero imaginary parts. These spectral separations persist under sufficiently
small independent raw reward perturbations. Any raw producer that requires
some positive real triple eigenmode, including a positive Jordan mode, fails
on this full-dimensional neighborhood.

This is a spectral statement about individual triple maps. It does not
exclude finite legal trajectories or compositions of different supports.
The actual cycle is obtained next from such a composition.

## 3. Exact quadratic root branches and policy maps

For a triple S and native continuation cap b, write scheduled odds as
`x_i=q_i/(1−q_i)`, setting the omitted odds to zero. Active indifference is

```
b_i=−A_iu x_u−A_iv x_v+Δ_i({u,v})x_u x_v,    i∈S,          (3)
```

where `{u,v}=S\{i}`. At the fixed parameter `d=1/1000`, the twenty-five-phase branches
solve a quadratic `αx²+βx−γ=0` with

```
x=2γ/[β+sqrt(β²+4αγ)].                                    (4)
```

For S=012, x is owner0's odds, and

```
α=b0+6−2d,
β=18/5−9b0/10+(6−d)b1+2b2+3d/2,
γ=9b0/10−b1b2−18b1/5+3b2/2,
x1=(b2−dx)/(3/5+x),        x2=(b1+x)/(3/2−x).             (5)
```

For S=023, x is again owner0's odds, and

```
α=b0+21/50−2d/25,
β=21/50+d/100+2b2/25+db3−6b3,
γ=b0+b2b3+b2/100+6b3,
x2=(7x/100−b3)/(1−x),      x3=(dx−b2)/(1+x).              (6)
```

For S=123, x is owner1's odds, and

```
α=51/250+b1,
β=3/10−11b2/25+9b3/10,
γ=b1+2b2/5+3b3/2−b2b3,
x2=(x/25−b3)/(1+x),        x3=(3x/5−b2)/(1−x).            (7)
```

The exact checker verifies (3) for each branch: after the two rational
substitutions, the remaining numerator is divisible by the displayed
quadratic. Formula (4) satisfies that quadratic wherever its denominator is
nonzero. The interval checks below keep every square-root argument strictly
positive and every denominator away from zero. Thus these are smooth root
maps on an open neighborhood of the entire certified return cube.

For any odds vector and owner i define literal native forced-Continue and
forced-Quit endpoints by

```
D_i=∏_(j≠i)(1+x_j),
C_i=[b_i+Σ_(nonempty B⊆I\{i}) Z_i(B)∏_(j∈B)x_j]/D_i,
Q_i=[Σ_(B⊆I\{i}) Z_i(B∪{i})∏_(j∈B)x_j]/D_i.             (8)
```

The map `T_S(b)` returns Q_i for active owners, and C_i for the omitted
owner. Equation (3) makes Q_i=C_i on every active row. For the omitted owner
we retain the exact gap `Q_i−C_i`. No game entry or contact corner is discarded
in these endpoint computations.

## 4. Two explicit finite contractions produce the cycles

### 4.1 The positive-parameter twenty-five-phase cycle

Let

```
c=(.6032426876986211, .1316536363074683,
   .3158582125684314, .0018524455688325833),
r=10^−10,             B={b:||b−c||∞≤r}.                   (9)
```

All displayed decimals in c are exact rational numbers. Apply the backward
root maps in the sequence

```
twenty copies of T012, then three T023, then two T123,
F=T123²∘T023³∘T012²⁰.                                    (10)
```

The complete exact interval checker establishes, uniformly for every b∈B,

```
||DF(b)||∞ <1/100,
||F(c)−c||∞ <10^−14,
all active hazards >1/10000 and <1,
every omitted-owner gap <−1/10.                            (11)
```

The sharper computed enclosures are derivative norm below `.001942750`,
center defect below `1.252·10^−16`, active hazard above `.0001768071408`,
and omitted gap below `−.1347693674`; only the rational bounds in (11) are
used. All square roots, root denominators, endpoint denominators and positive
hazards are checked on the full cube, not only at its center.

For completeness, the enclosure mechanism is an induction. The checker
propagates the point image of c and the interval Jacobian with respect to the
four original coordinates. At each stage its current image enclosure is
replaced by the point image plus that Jacobian applied to `[-r,r]^4`.
The multivariable mean-value theorem validates this replacement. Every next
root map and its derivative is evaluated on the resulting enclosure, so the
chain rule gives a bound for the derivative on all of B. This avoids using
a floating-point orbit as an exact strategy. The point images themselves
are enclosed by outward 512-bit integer interval arithmetic; rounding is
included in every operation. Floating-point conversion is used only to
print diagnostic decimal bounds.

From (11),

```
||F(b)−c||∞ ≤10^−14+r/100 < r.                            (12)
```

Thus F maps the closed cube B strictly into itself and is a contraction.
It has a unique fixed point b* there. This produces the continuation caps;
they are not supplied as an equilibrium witness. Every root along the fixed
return has proper probabilities and strict inactive comparisons by (11).
Because each T maps a continuation to the preceding phase, reversing the
composition order gives exactly the physical word (1b).

### 4.2 The endpoint sixty-four-phase cycle

At δ=0 use the same raw construction and literal endpoint maps, with active
support012 or013. A generic probability elimination specifies the exact
branches without additional odds formulas. For active ordered owners
`i<j<k`, put `q_i=X,q_j=Y,q_k=z`, and write their native continuation
coordinates as b. For any active owner a and the other two active owners
u,v, define

```
h_a=−b_a,                 a_a=b_a−A_au,
b_a'=b_a−A_av,            d_a=Δ_a({u,v})+A_au+A_av−b_a.
```

Here `b_a'` denotes a polynomial coefficient, not a continuation value.
Use `(u,v)=(j,k),(i,k),(i,j)` in rows i,j,k respectively. The exact active
Quit-minus-Continue polynomial in these probabilities is

```
h_i+a_i Y+b_i' z+d_i Yz,
h_j+a_j X+b_j' z+d_j Xz,
h_k+a_k X+b_k' Y+d_k XY.                                (13)
```

This follows by expanding the two-opponent product probabilities: own
singleton is zero, singleton joining difference is `J−Γ=−A`, and the
opponent-pair joining difference is Δ. Define the linear polynomials

```
n_X(z)=−h_j−b_j'z,        d_X(z)=a_j+d_jz,
n_Y(z)=−h_i−b_i'z,        d_Y(z)=a_i+d_iz.
```

Set X=n_X/d_X and Y=n_Y/d_Y. Then the first two equations in (13) vanish
identically. The third, multiplied by d_Xd_Y, becomes

```
C0+C1z+C2z²=h_k d_Xd_Y+a_k n_Xd_Y+b_k'n_Yd_X+d_k n_Xn_Y.
```

Choose the branch

```
z=[−C1+sqrt(C1²−4C2C0)]/(2C2).                          (14)
```

Every division denominator is bounded away from zero, and the discriminant
is strictly positive, in the full interval check below. Hence (14) solves
the third equation exactly and defines a smooth local root map. Interval
inclusion of zero in an active gap is only a consistency check; exact active
equality follows from this polynomial identity. The output map returns the
literal forced-Continue endpoint for every owner, which equals the Quit
endpoint for the three active owners.

Let e be the following vector of exact rational decimals, all of whose
digits are part of the certificate:

```
e0=0.004118890025300792583695362537695543715792236764499152011090139632874172171045056749651981915674295160396853309659441455604098529901
e1=0.0001243482175163461881555454679752314397549106941919952765786180159590206637434094660072037251656962047098682135801304677257343514117
e2=0.00004190775560804728637263339044829948663033445855611154354232280109276626865643290562544450787265172745534118001684634872489965234201
e3=0.3690086159884435465928283186669010332053764555876554382079574148441777874623973295113738211805241067838667431903560321552244727305
```

Put `s=10^−110` and `E={b:||b−e||∞≤s}`. Apply four T013 maps and then
sixty T012 maps, giving

```
G=T012⁶⁰∘T013⁴.                                         (15)
```

The complete standalone endpoint checker uses outward1024-bit integer
intervals and exact first-derivative propagation on E. It certifies

```
||DG||∞<1/1000,           ||G(e)−e||∞<s/100,
1/20000<every active hazard<9/10,
every omitted-owner Quit−Continue gap<−13/100.             (16)
```

Its sharper diagnostic bounds are derivative norm below`8.154·10^−5`
and center defect below`3·10^−131`. All192 active hazards and all64
omitted-owner comparisons are covered on the entire cube. The joint survival
probability over the cycle is also below1/10000; the deviation argument below
uses the stronger structural opponent-survival consequence of the hazard
bounds. The interval computation propagates both values and the four original
partial derivatives through all64 formulas, including every arithmetic
rounding error. It reads no external data or supplied strategy.

The inequalities `||G(b)−e||∞≤s/100+s/1000<s` and `||DG||∞<1` produce a
unique fixed point e* in E by contraction. Reversing the backward composition
gives exactly the physical word(1a). At δ=0 this is already a proper exact
cycle, with strictly legal omitted owners. Its full-reward openness in
Section6 supplies the stated all-sufficiently-small-positive family with
the SAME fixed period64. No asymptotic period growth or limiting-cycle
assertion is needed for this family.

## 5. Unrestricted behavioral and fixed-target uniform equilibrium

For either certified cycle, at every phase three owners mix properly and the fourth continues. Fix an
owner i and remove its randomization. At least two scheduled opponents
remain at every phase, each with hazard above1/20000. For a period of
length P∈{25,64}, their survival is at most `(19999/20000)^(2P)<1`,
irrespective of i's
behavioral stopping rule. Absorption occurs almost surely against every
unilateral behavioral deviation and has a common geometric tail bound.
The native subtraction of one is consequently legitimate in these terminal
comparisons; it is not applied to a positive-probability Never event.

The cyclic continuation values satisfy exact forced-Quit/Continue equality
on each active row and strict Quit disadvantage on each omitted row.
Iterating the one-step inequalities bounds every history-dependent,
randomized unilateral deviation by the prescribed cyclic value. The residual
continuation term tends to zero under the opponent survival bound. This proves
exact terminal Nash against the entire behavioral deviation class.

Let `v=1+b*` or `v=1+e*` be the actual terminal vector at the respective
chosen initial phase.
The same geometric bound gives a finite uniform bound on expected absorption
time under all unilateral deviations. Bounded rewards then make finite-horizon
average payoffs differ from their terminal payoffs by O(1/T), uniformly over
all those deviations. For every ε>0, the fixed cyclic profile is ε-Nash for
all sufficiently large horizons and has payoff within ε of the SAME v.
This is the fixed-target UE contract. Neither the target nor the strategy
needs to vary with the horizon.

## 6. Full raw open classes and the comparison scope

The active root equations have nonsingular probability Jacobians along each
certified cycle. Differentiate their smooth explicit solution with respect
to the three active continuation coordinates. The derivative of the active
gap with respect to its own continuation is diagonal with entries equal
to minus the product of the two opponents' Continue probabilities, all
nonzero. Thus the square probability Jacobian has a right inverse and is
invertible. Equivalently, the odds equations(3) have derivative−I in their
active continuation coordinates. Both formulations give the same conclusion.
The return Jacobians `I−DF(b*)` and `I−DG(e*)` are invertible by the strict
contraction bounds. The implicit-function theorem therefore continues every
active root and the return fixed point under arbitrary independent
perturbations of the sixty actual absorbing rewards. Own singleton levels
may vary: subtracting each recipient's level is an affine local coordinate
change, not a restriction on the perturbation. Proper hazards, strict omitted
gaps and opponent absorption persist. Section5 supplies the full behavioral
and fixed-target consumer for every continued table.

In particular, the endpoint table has an open full-reward neighborhood U0
of exact64-phase equilibria. The raw parameter map is continuous at zero,
so some δ*>0 satisfies `r(δ)∈U0` for every `0≤δ<δ*`. We may shrink δ*
to at most1/1000. This proves the first theorem assertion with one fixed
period. The explicit1/1000 table separately has an open neighborhood U1
of exact25-phase equilibria.

Every positive parameter in the certified range has all four triple spectral
pairs nonreal, the remaining eigenvalues negative, both inverse matrices
positive and all matching signs strict. The stationary and fixed-pair gaps
proved below persist on a common raw neighborhood of the entire closed
parameter interval. The additional direct raw contradictions have strict
local margins at each positive parameter. Intersecting the appropriate
neighborhoods gives a full sixty-dimensional open existence class with all
claimed separations at each such positive table. At the endpoint itself,
the full UE neighborhood and the robust architecture gaps are asserted;
absence of a positive triple eigenvalue and all positive-parameter raw guards
are not asserted on that whole endpoint neighborhood.

The result rules out a positive real mode on some single triple as a necessary
hypothesis for these periodic constructions. It does not claim that every
table without such a mode is solved, or nonmembership in an unspecified
maximal neighborhood or a different branch of an earlier local periodic
theorem. The complete comparisons below concern specified architectures,
criteria, role choices and positive row scalings.

## 7. Literal family and statement

Let0≤δ≤1/1000. Four independently randomized players have a single live
state, Boolean Continue/Quit actions, permanent absorption on every nonempty
quitter coalition, and zero live and Never payoff. Actual absorbing rewards
are r_i(C)=1+Z_i(C), with Z_i({i})=0. Favorite pairs are01 and23. Define

```
Aδ = [0       1       -6       -1/100]
     [1       0       -3/2     -2/5]
     [-δ     -3/5      0        1]
     [-7/100 -1/25     1        0].
```

For distinct i,j set J_ij=1/100 if j is i's favorite. On crossing edges
02,21,13,30 set J_ij=−(9/10)A_ij; on03,12,20,31 set
J_ij=−(1/10)A_ij. Thus the high/low ratios are J_ij/(-A_ij), not
ratios of Γ entries. Set Γ=A+J, hence

```
Γδ = [0        101/100 -3/5      -9/1000]
     [101/100  0       -27/20    -1/25]
     [-9δ/10  -3/50     0         101/100]
     [-7/1000 -9/250    101/100   0].
```

Put Z_i({j})=Γ_ij and Z_i({i,j})=J_ij. For opponent pairs B in the order
01,02,03,12,13,23, assign signs+1,−1,+1,+1,−1,−1. The smaller outside
owner receives that sign as Δ_i(B), the larger its negative. Define
Z_i(B)=max(0,−Δ_i(B)) and Z_i(B+i)=max(0,Δ_i(B)). An opponent triple
pays1 and the grand coalition pays0 in native coordinates. These rules
specify all sixty entries; only Z_2({0})=−9δ/10 and Z_2({0,2})=δ/10 vary.
The literal positive table is δ=1/1000; the exact comparison checks cover
the whole closed interval stated here.

**Comparison theorem.** Over the ENTIRE closed parameter interval:

1. Every stationary prescribed profile has full behavioral terminal
   exploitability bounded below by one fixed positive number.
2. The same holds over all prescribed profiles repeating two fixed disjoint
   pairs, all three partitions, both orders, and all zero/proper/sure hazards.
3. No sure-first root with any arbitrary behavioral continuation is exact Nash;
   its necessary one-date regret has a uniform positive lower bound.
4. All fourteen nondiscrete positively row-scaled response partitions fail.
   The discrete matrix is R0 with degree+1, so it supplies no degree-not-one exit.

The architecture gaps persist in a common sufficiently small full-reward
neighborhood of the parameter interval. Each strictly positive parameter
also has its own raw neighborhood on which the additional direct criteria
in Section 13 fail. No gap against arbitrary prescribed behavioral strategies
is asserted; the longer-period equilibria above are compatible with these
claims. No minimum possible period or complete classification of equilibria
is inferred.

## 8. Complete uniform stationary exclusion

For stationary hazards q∈[0,1]^4 define, in native coordinates,

```
H_i=∏_(j≠i)(1−q_j),
P_i=Σ_(nonempty B⊆I\{i})Pr_q(B) Z_i(B),
Q_i=Σ_(B⊆I\{i})Pr_q(B) Z_i(B+i),
F_i=(1−H_i)Q_i−P_i.                                (1)
```

At every nonzero stationary Nash profile,

```
q_i>0 ⇒ F_i≥0,       q_i<1 ⇒ F_i≤0.                 (2)
```

Indeed actual prescribed value is
1+[q_i Q_i+(1−q_i)P_i]/[1−(1−q_i)H_i]. Substitution gives forced-Quit
minus Continue endpoint equal to F_i/[1−(1−q_i)H_i]. The denominator
is positive at every nonzero profile. This establishes(2) on every boundary,
not merely in the proper interior. AllNever has actual value0 and immediate
Quit gives1, so it is excluded separately.

### 8.1 The analytic origin cube

Use hazard radius h=1/512. The support census is complete:

* With singleton support{j}, choose an observer i with a fixed Γ_ij<0
  throughout the interval. Its inactive field is
  F_i=q_j(J_ij q_j−Γ_ij)>0, violating(2).
* With support{i,j}, a proper active field equals
  q_j(J_ij q_j−Γ_ij). For a favorite pair Γ_ij=J_ij+1, so it cannot
  vanish. For a crossing pair choose a direction with Γ_ij<0≤J_ij;
  this includes02 atδ=0 by choosing i=0. Again the active field cannot vanish.
* For a triple support, choose its owner i whose favorite is absent. For
  its two active opponents j,k set c=−Γ_ij−Γ_ik and K_i=Z_i({j,k}).
  Both singleton Γ entries are nonpositive. The lower bounds on c and
  the exact K_i, for triples012,013,023,123 respectively, are

  ```
  c≥3/50,43/1000,609/1000,139/100;       K_i=0,1,1,0.
  ```

  Hence h(c+K_i)<c uniformly. For positive q_j,q_k≤h,

  ```
  P_i/(q_jq_k)
   =Γ_ij(1/q_k−1)+Γ_ik(1/q_j−1)+K_i
   ≤−c(1/h−1)+K_i<0.
  ```

  All participant native rewards are nonnegative, so Q_i≥0. Thus F_i>0,
  contrary to the required equality for this proper active owner. No full
  four-dimensional inverse bound is being applied to a proper triple.
* For full support, F=−Γδ q+Rδ(q). Exact coefficient and inverse bounds are

  ```
  ||Rδ(q)||∞≤K||q||∞²,    K=135711/1000,
  ||Γδ^-1||∞≤L=123883650000/50416886717,
  K L/512=8406187012575/12906722999552<1.
  ```

  Therefore F=0 forces ||q||∞≤KL||q||∞², impossible for positive
  ||q||∞≤1/512.

These bounds are uniform in δ. Every polynomial coefficient is affine in
δ, so the nonlinear absolute-coefficient sum is convex and bounded by its
endpoint maximum. The determinant and every adjugate entry of Γδ are
strictly positive affine functions at both endpoints. Each inverse row sum
is a fractional linear function of δ, hence has its maximum at an endpoint.
The exact determinant is

```
det Γδ=(504187037−18169830δ)/500000000>0,
min Γ0^-1=126000/504187037>0.
```

The checker verifies all endpoint positivity and coefficient identities
symbolically. The radius1/256 does not satisfy this family's full-support KL bound;
the proof uses radius1/512.

### 8.2 The complete cube

Each F_i has degree at most2 separately in each hazard. For a polynomial
Σ_β a_β q^β, its tensor Bernstein coefficient of multidegree(2,2,2,2) is

```
b_α=Σ_(β≤α)a_β∏_j binom(α_j,β_j)/binom(2,β_j).
```

The polynomial lies in the convex hull of those coefficients. Clear rational
denominators and retain integer arrays at BOTH parameter endpoints. Affine
parameter dependence implies that every intermediate coefficient is the
corresponding convex combination. A closed hazard box is rejected only if
some F_i is strictly negative at all coefficients at both endpoints while
the box has q_i>0, or strictly positive throughout while its box has q_i<1.
Either case contradicts(2). The small origin cube uses Section 8.1.

A midpoint split changes a Bernstein coordinate slice(a0,a1,a2) to

```
left=(4a0,2(a0+a1),a0+2a1+a2),
right=(a0+2a1+a2,2(a1+a2),4a2),
```

at four times the previous positive denominator. Every sign test and split
therefore uses Python integers only. Both closed children are retained,
including their common face. A finite node/depth budget can only raise an
error; it never accepts an unresolved box.

The deterministic whole-parameter run terminates with **1568351 nodes,
784176 leaves, maximum depth80, and exactly one analytic-origin leaf**.
Every leaf has the stated exact sign or analytic reason. Its union covers
[0,1]^4, including all zero and sure faces. Thus the only point satisfying(2)
is q=0, which was already excluded as an actual Nash profile.

## 9. Complete fixed-pair exclusion

Fix a mate involution m and positive proper hazards q_i. Put p_i=J_i,m and
c_i=J_i,m−Γ_i,m=−A_i,m. At its active phase, owner i's value is p_i q_m.
Its value W_i at the opposite phase satisfies active indifference, giving
W_i=c_i q_m/(1−q_m). For the opposite pair{j,k}, let

```
D=(1−q_j)(1−q_k),
C_i=Γ_ij q_j(1−q_k)+Γ_ik q_k(1−q_j)
    +Z_i({j,k})q_jq_k+p_i q_m D,
Q_i=J_ij q_j(1−q_k)+J_ik q_k(1−q_j)+Z_i({i,j,k})q_jq_k,
E_i=(1−q_m)C_i−c_i q_m,
H_i=(1−q_m)Q_i−c_i q_m.                             (3)
```

Every proper two-pair Nash must satisfy E=0,H≤0. For favorite schedule01|23,
c_i=−1 gives W_i<0 while immediate Quit has nonnegative native reward,
so that schedule is impossible.

For the two crossing schedules E=Γδ q+Rδ(q). With the same L as above,
exact nonlinear bounds give K=38803/1000 for02|13 and K=481/100 for03|12.
In both cases LK/256<1, so the only E-root in[0,1/256]^4 is0. A complete
Bernstein cover, keeping both δ endpoints as in Section 8, rejects any other
box when some E row is uniformly strictly signed or some H row uniformly
strictly positive. It terminates with

| Schedule | Nodes | Leaves | Maximum depth |
| --- | ---: | ---: | ---: |
| 02 / 13 | 109 | 55 | 32 |
| 03 / 12 | 339 | 170 | 35 |

Thus E=0,H≤0 implies q=0 on the ENTIRE hazard cube, uniformly across δ.

To pass to all actual fixed-pair profiles, sure hazards are ruled out by
Section 10 at their first positive-probability reached occurrence. Assume every
hazard is below1. If both phases are nonempty and one is solo, its sole
proper mixer i has Quit value0 and sees no current opponent quit. Its next
phase value must therefore be0. Immediate Quit at that next phase is
strictly positive if some active opponent j has J_ij>0, because the event
that exactly j quits has positive probability and all participant rewards
are nonnegative. The only potential exception is δ=0,i=2 and opposite
active support exactly{0}. Then owner0 is itself solo in that opposite
phase and the same argument applied to it uses J_02=27/5>0. Contradiction.

If one phase is empty, a proper two-owner active phase requires
J_ij q_j=Γ_ij for both owners. Favorite Γ_ij=J_ij+1 makes this impossible;
a crossing pair has at least one direction Γ_ij<0≤J_ij, including02 atδ=0.
One sole active owner harms a fixed negative-crossing observer, which can
instead guarantee1 by immediate Quit. AllNever gives0 instead of1. These
cases exhaust every zero/sure pattern. A continuation reached with positive
probability must itself be exact Nash, since a profitable continuation
replacement lifts to a profitable original replacement. Thus the phasewise
arguments have the required actual strategic meaning.

## 10. Uniform punishment and all sure-first faces

Every actual participant reward is at least1 throughout the closed parameter
interval. Immediate Quit therefore guarantees1 against every opponent law.
Opponents choosing Never hold the complete response cap to exactly1. Thus
all true actual punishment values equal1, and every arbitrary off-path
continuation has full cap at least1. Native punishment values are zero.

Changing J while keeping A and every higher contact corner fixed leaves
ALL native endpoint differences g_i identically unchanged. Thus the literal
face formulas below apply to the present high/low table as well.

For current hazards q, let g_i(q) be native forced-Quit minus forced-Continue
payoff when all-Continue has value0. A root with a sure owner h requires

```
q_i>0 ⇒ g_i≥0,       q_i<1 ⇒ g_i≤0.                 (1)
```

For i≠h, a sure opponent makes the continuation irrelevant. For h, an
arbitrary actual continuation cap b_h≥1 makes its exact Quit-minus-Continue
cap comparison g_h−H_h(b_h−1)≤g_h. Consequently (1) is necessary even
for arbitrary behavioral tails. The following four analyses exhaust the
closed sure boundary.

### Sure owner0

Write x=q1,y=q2,z=q3 and a=δ+(1−δ)x. The opponent gaps are

```
g1=−1+2z(1−y),
g2=a−(1+a)z,
g3=[7−107x+93y(1−x)]/100.                           (2)
```

On the parameter interval0≤a≤1. If y>0, g2≥0 gives z≤a/(1+a)≤1/2.
Then g1<0 forces x=0. Formula(2) makes g3>0, forcing z=1, a
contradiction. Hence y=0. The two remaining opponent gaps are 2z−1 and
(7−107x)/100. Their boundary signs force x,z to be proper, so
x=7/107,z=1/2. At this unique opponent equilibrium,

```
g2=50(δ−1)/107<0,      g0=−13/214<0.
```

Thus the sure owner would withdraw.

### Sure owner1

Write x=q0,y=q2,z=q3. None of the face's gaps depends on δ, because
owner1's sure action prevents the only two changed coalitions from occurring.
The relevant formulas are

```
g0=−1+2y(1−z),
g2=[−12xz+2x+2z+3]/5,
g3=[26(1−x)(1−y)−25]/25.                            (3)
```

If z>0, g3≥0 forces x,y≤1/26. Then g0<0 gives x=0 and g2>0 gives
y=1, contradiction. Hence z=0. Now g2>0 gives y=1, and g0=1 gives
x=1. At this unique opponent equilibrium g1=−1<0.

### Sure owner2

Write x=q0,y=q1,z=q3. All three opponent gaps are independent of δ:

```
g0=6−5y−7z+5yz,
g1=[3−5x−z+xz]/2,
g3=−1+2x(1−y).                                     (4)
```

If x=0, the signs force y=1,z=0, then g0=1 contradicts x=0. If x=1,
they force y=0,z=1, then g0=−1 contradicts x=1. Thus x is proper and
g0=0 yields z=(6−5y)/(7−5y)∈[1/2,6/7]. This makes z proper; g3=0
yields x=1/[2(1−y)] and y<1/2. The case y=0 would give x=1/2,z=6/7
and g1=1/28>0. Hence all three are proper. The remaining equation is
20y²−30y+1=0, with unique admissible root

```
x=(−5+√205)/18, y=(15−√205)/20, z=(22−√205)/9.
```

The sure owner's gap has derivative x(1−y)(1−z)≥0 with respect to δ.
Its maximum on the parameter interval is therefore its value at1/1000:

```
g2≤(170187−12919√205)/18000<0,
12919²·205−170187²=5251000036>0.
```

Thus this owner also withdraws, uniformly across the interval.

### Sure owner3

Write x=q0,y=q1,z=q2. Again every face gap is independent of δ. The
opponent formulas are

```
g0=[101(1−y)(1−z)−100]/100,
g1=[−13xz+3x+3z+2]/5,
g2=−1+2y(1−x).                                     (5)
```

If x>0, g0≥0 gives y,z≤1/101. Then g2<0 forces z=0 and g1>0 forces
y=1, contradiction. Hence x=0; then g1>0 forces y=1 and g2=1 forces
z=1. At this unique opponent equilibrium g3=−1<0.

The four arguments cover every zero, proper and sure opponent pattern.
The exact checker verifies all δ-dependent identities and monotonicity;
(3)--(5) for the opponents are the unchanged literal polynomial expansions.
The compact parameter interval times the four closed sure faces has no point
satisfying(1). The continuous maximum one-date regret consequently has a
strictly positive minimum there. Every complete actual root with a behavioral
tail has at least this regret, since its relevant continuation cap is≥1.
Raw payoff perturbations preserve that strict exclusion by continuity and
the immediate-Quit cap bound1−η. This also excludes every singleton-base
certificate using true punishment, regardless of its free carrier.

## 11. Uniform positive gaps for both architectures

Suppose parameters δ_n in the compact interval and stationary or fixed-pair profiles q_n
had full behavioral terminal exploitability tending to0. Pass to limits
δ_n→δ* and q_n→q*, fixing the architecture and finite schedule choice on a subsequence.

If q* has at least two positive coordinates, every opponent-deleted period
survival is below1. Both the prescribed payoff and full response cap vary
continuously with δ and q there. Indeed if H_i is opponent period survival,
N_i is literal Never value and L_i(t) is the deadline value at first-period
phase t, the corresponding deadline in period k has value

```
(1−H_i^k)N_i+H_i^k L_i(t).
```

Every behavioral stopping law is a mixture of deadlines and Never, so the
full cap is exactly max(N_i,L_i(0)) for a stationary profile and max(N_i,L_i(0),L_i(1)) for a two-phase profile. A zero limiting gap would give
an exact Nash in the fixed architecture atδ*, contrary to Sections 8–10.

If q* has only one positive coordinate j, choose a negative crossing observer
whose Γ_ij is fixed across δ. Its prescribed value tends to1+Γ_ij<1,
while immediate Quit guarantees1. Again the gap cannot vanish.

Finally suppose q*=0. Put h_n=sum_i q_ni>0 and take w_n=q_n/h_n→w in
the unit simplex. Uniform bounded rewards and the fixed one-phase or two-phase period give
singleton first-exit masses q_nj+O(h_n²), total collision mass O(h_n²), and
total absorption h_n+O(h_n²). Prescribed actual values therefore tend to
1+(Γδ* w)_i. Immediate Quit≥1 implies y=Γδ* w≥0. A singleton support
is excluded by the preceding fixed negative crossing. Thus every w_i<1.
For w_i>0 the actual Never response tends to
1+y_i/(1−w_i). Vanishing debt and y_i≥0 force y_i=0 on the positive support.
Hence w≥0,y≥0,w_i y_i=0.

This is impossible solely from Γδ*^-1>0. If y=0, invertibility gives w=0.
If y≠0, strict inverse positivity gives w=Γδ*^-1 y strictly positive in
EVERY coordinate, and complementarity then forces y=0. Both contradict
sum_i w_i=1. This argument deliberately avoids assuming the principal02
block is nonsingular atδ=0.

Every possible limiting case is excluded, proving one positive gap d over
the whole closed parameter interval and the union of both architecture families. Changing
raw rewards by at mostη changes every prescribed and deviating terminal
payoff by at mostη, uniformly over every profile; the literal Never payoff
stays0. Thus exploitability changes by at most2η. A uniform raw tube of
radius below d/2 retains positive stationary and fixed-pair gaps. For each fixed strategy,
finite-horizon averages converge to terminal payoffs by bounded convergence,
so this gap also prevents arbitrary-accuracy uniform witnesses within either
architecture.

## 12. Every response quotient and all positive row-weight walls

### 12.1 The fourteen nondiscrete partitions

A literal response-invariant quotient requires proportional stationary
response rows after identifying hazards within each block. Positive recipient
scaling changes a two-row coefficient minor only by a positive factor.
The following exact minors are nonzero throughout0≤δ≤1/1000. Monomial
coordinates follow the displayed block order. For exponents α,β the minor
is coefficient_i(α) coefficient_j(β)−coefficient_i(β) coefficient_j(α).

| Blocks | Rows | α | β | Minor |
| --- | --- | --- | --- | --- |
| 01/2/3 | 0,1 | 001 | 010 | −237/20000 |
| 1/02/3 | 0,2 | 001 | 010 | 303/500+81δ/10000 |
| 1/2/03 | 0,3 | 001 | 010 | −1329/100000 |
| 0/12/3 | 1,2 | 001 | 010 | 13659/10000 |
| 012/3 | 0,1 | 01 | 10 | 973/50000 |
| 12/03 | 1,2 | 01 | 10 | 13053/10000−243δ/200 |
| 0/2/13 | 1,3 | 001 | 010 | −89/1000 |
| 02/13 | 0,2 | 01 | 10 | 57/100−9009δ/10000 |
| 2/013 | 0,1 | 01 | 10 | −15387/20000 |
| 0/1/23 | 2,3 | 001 | 010 | 303/12500 |
| 01/23 | 0,1 | 01 | 10 | 78881/100000 |
| 1/023 | 0,2 | 01 | 10 | 909δ/1000−24589/25000 |
| 0/123 | 1,2 | 01 | 10 | 1251δ/1000−1919/2000 |
| 0123 | 0,1 | 1 | 2 | −56331/10000 |

The checker enumerates all fifteen partitions and computes every displayed
minor from the literal polynomial fields. For each minor the sum of the
absolute nonconstant coefficients times(1/1000)^degree is smaller than
the absolute constant. This excludes a zero throughout the closed interval,
including the full-block quotient where linear coefficients alone would
not suffice. The actual own offset1 cancels from the zero-discount field F.

The discrete quotient retains Γδ. Strict inverse positivity implies R0:
for w≥0,y=Γw≥0,w_i y_i=0, either y=0 and w=0, or y≠0 and w=Γ^-1 y>0
in every coordinate, again forcing y=0. At offset−1, any complementary
solution has w=Γ^-1(1+y)>0, hence y=0 and w=Γ^-1 1. This unique regular
solution has orientation sign(detΓ)=+1. Thus the R0 degree is+1. The
principal02 block is singular atδ=0, but this proof does not need that block
to be nonsingular. All quotient and degree obstructions persist on a raw
neighborhood of the compact parameter interval by their strict margins.

### 12.2 Arbitrary positive odds, row factors and pair orientations

Choose any positive odds ρ_j and positive C¹ row factors m_i on the cube.
This includes every positive multiaffine or constant weighting. Put

```
ψ_j(u)=ρ_j u_j/[1+(ρ_j−1)u_j],
D_j(u)=1+(ρ_j−1)u_j,
G_i(u)=m_i(u)∏_(j≠i)D_j(u)² F_i(ψ(u)).
```

Choose one favorite pair or both, orienting each as preferred i and partner k,
and let K be the cube with u_i≥u_k on the selected pairs. The ordered-wall
requirement is G_i≥G_k whenever u_i=u_k in K. No such choice can succeed.

Suppose it did. For η>0 let v be1 on preferred owners and0 elsewhere.
Brouwer supplies a fixed point of projection_K(u+G(u)+ηv). Write f=G+ηv.
The fixed-point variational inequality gives ordinary cube complementarity:
at an interior tied pair, feasible increase of i gives f_i≤0 and feasible
decrease of k gives f_k≥0, contradicting f_i≥f_k+η. At a tied zero corner,
f_i≤0 and f_k<f_i; at a tied one corner, f_k≥0 and f_i>f_k. At untied
coordinates the order normal is inactive. Disjoint pairs cause no extra
intersection case. Thus the same complementarity holds at every fixed point.

If a sequence η→0 has a nonzero limiting fixed point, positive factors and
ψ transfer it to a nonzero complementary F point, contradicting Section 8.
Suppose instead u_η→0. At zero, DG(0)=−M with
M=diag(m(0)) Γ diag(ρ), so M^-1 is strictly positive and M_ii=0.
Normalize by max(||u_η||∞,η). A subsequential limit w,τ satisfies

```
w≥0 in the ordered cone, τ≥0, max(||w||∞,τ)=1,
Mw≥τv,                 w_i[(Mw)_i−τv_i]=0.           (4)
```

If τ=0, the inverse-positive R0 argument just given forces w=0, impossible.
If τ>0, write Mw=τv+y with y≥0. Since v is nonzero and M^-1>0,
w=M^-1(τv+y) is strictly positive in EVERY coordinate. Hence complementarity
forces Mw=τv.

Choose any selected preferred pair i,k. Differentiating the tied-wall guard
at zero gives(Mw')_i≤(Mw')_k for an ordered vector w' tied on that pair.
Lower w_i to w_k to obtain w'. Restoring w_i leaves row i unchanged because
M_ii=0 and increases row k because the favorite entry M_ki>0. Thus
(Mw)_i≤(Mw)_k. But Mw=τv gives the opposite strict differenceτ. This
contradiction proves noncollapse and excludes every odds, factor and orientation
selection. Unbounded parameters are not a loophole: any single successful
selection would supply this contradiction.

This inverse-positive version does not use strict negativity of every
crossing coefficient. Therefore it remains valid even around theδ=0 table,
provided the stationary gap, inverse positivity and positive favorite entries
persist. Those are strict uniform facts already established. Positive
recipient scales are absorbed into the row factors.

## 13. Remaining direct raw guards

The architecture conclusions already exclude every raw producer whose output
is stationary, sure-first with a punishment tail, or fixed disjoint-pair
period two. In particular they cover every valid sufficiently-large parameter
choice in stationary coalition-jackpot constructions, without estimating an
unspecified threshold. Source-mode reductions with additional semantic-source
hypotheses are not silently treated as raw existence theorems.

For each positive δ, the remaining finite necessary guards fail over all
owner roles, relabelings and positive recipient factors:

* Every J_ij>0. Thus negative participant-pair chambers and rotating templates
  requiring a pair premium−b/2 with b>0 fail. A full four-owner premium core
  is witnessed by favorite pairs01 and23, so conditions requiring greatest
  core size at most three fail. Those disjoint traps also exclude a common
  leaver required to lie in every trap.
* The pure crossing pair03 has both participant premiums positive. It refutes
  the product-low requirement. On that trap both joining differences are
  positive, so neither owner is a support-specific weak leaver. With strictly
  positive trap weights, the coalition{3} gives a strictly positive inserted
  joining sum at owner0, excluding every weighted leaver selection.
* Every triple contains a favorite edge with J−Γ=−1, which violates the
  six-positive-difference guard for a triple collision box. Each Γ column
  has just one positive off-diagonal entry, excluding the joint-positive
  passive triple requirement. Signed inverse-column inactive caps require
  positive opposite-pair premiums to be nonpositive and also fail.
* Any marked-calendar condition requiring nonpositive positively weighted
  participant premium at the first marked block is contradicted by a
  coalition{i,j} with marked i and unmarked j: its sum is λ_i J_ij>0.
  This covers every marking, ordered partition and positive weight choice.
* Every column has a negative crossing, so there is no no-harm singleton.
  Mutual singleton signs are equal and strict for δ>0, so there is no escort
  edge. Atδ=0 the only possible edge is0→2 and there is no directed cycle.
  The balanced-singleton-cycle-to-escort implication therefore excludes all
  balanced singleton certificates, including repeated-owner presentations.

Opposite-row order fails for every positive recipient scaling. For
preference0 over1, the singleton requirements

```
a0 Γ03≤a1 Γ13,       a0 Γ01≤a1 Γ10
```

force a0/a1≥40/9 and≤1. For preference1 over0, the singleton requirement
a1 Γ12≤a0 Γ02 forces a1/a0≥4/9, but the contact requirement

```
a1 Z_1({0,2})≤a0 Z_0({1,2})
```

forces a1/a0≤0 because these native rewards are1 and0. Both contradictions
persist under small arbitrary perturbations: the strict lower bounds stay
away from the corresponding upper bounds. Merely citing a positive-to-zero
comparison without this ratio control would not establish robustness against
unbounded row scales. The favorite01 pair is present in every two-favorite-pair
orientation; Section 12.2 covers the broader one-pair weight selection too.

For bounded-inverse-corner and nonmatching-positive-passive guards, their
computed inactive cap obeys ell_i≤1/(768 U). This follows from
ell_i=c_i κ r_min/2, κ≤1/4, r_min≤1/(32 U Q), Q≥3c_i.
Under recipient scale a_i>0, U≥(Γ^-1)_ii/a_i. Every required opposite
joining premium must therefore satisfy J_ij(Γ^-1)_ii≤1/768.
Here no whole-row minimum shortcut is needed: enumerate all three schedules.
The favorite schedule01|23 already fails c_i=−A_i,m>0. For02|13 use
owner3's opposite entry J_30=63/1000; for03|12 use owner0's opposite
entry J_02=27/5. Writing B=Γδ^-1, exact identities give

```
detΓδ·[J_30 B33−1/768]
  =(29705382630δ+375434083)/384000000000>0,
detΓδ·[J_02 B00−1/768]
  =(18169830δ+106306948963)/384000000000>0.            (5)
```

Thus every schedule and positive scale fails, uniformly along the parameter
interval. Both margins are strict and persist on a raw neighborhood.

### Every literal proper child, including security withdrawals

For a nonempty proper child C and outsider h, allow arbitrary nonnegative
advance weights a_i and withdrawal weights d_i. Necessary future and joining
rows, for every nonempty S⊆C, are

```
−Z_h(S)≤Σ_(i∈C)a_i[−Z_i(S)],
Z_h(S+h)−Z_h(S)
 ≤Σ_(i∈C){a_i[Z_i(S+i)−Z_i(S)]+d_i W_i(S)}.          (6)
```

Here W_i=0 for i∉S, and W_i=Z_i(S−i)−Z_i(S) for nonsingleton S containing
i. For S={i}, it is the chosen actual restart floor minus own singleton1.
The basic zero floor, evaluated-security floor and untruncated terminal-security
floor are all≤1: the security LP has that literal singleton upper constraint,
and its additional zero floor is≤0. Thus W_i≤0 for singleton S, even in the
strongest listed version. No guessed or numerically optimized floor is used.

For singleton child j choose crossing outsider h by0→3,1→2,2→0,3→1.
The joining left side is strictly positive and its right side nonpositive.
For crossing pair children02,03,12,13 use S=C and outsiders3,1,0,2. The
left side is1, advance coefficients vanish identically, and withdrawal
coefficients are the nonpositive crossing A entries. For favorite child01
choose h=2,S={1}: the row is3/5≤−a0+d1(γ1−1)≤0. For favorite child23
choose h=1,S={2}: it is3/2≤−a3+d2(γ2−1)≤0.

Three triple-child joining contradictions are exact contact identities:

```
C012,h3,S02: 1≤−a1−6d0−δ d2,
C013,h2,S13: 1≤−a0−(2/5)d1−(1/25)d3,
C023,h1,S03: 1≤−a2−(1/100)d0−(7/100)d3.
```

For the last child C123,h0, add TEN TIMES the future row S12 to the future
row S={2}. The resulting contradiction is

```
3/5≤−(3/20)a1−(27/5)a2−(1101/100)a3≤0.                  (7)
```

The factor ten is useful: every resulting coefficient is strictly negative,
so this certificate is robust under small arbitrary raw perturbations even
with unbounded nonnegative weights. All fourteen children are covered;
advance-only and future/join-only certificates are included by setting d=0.
Positive recipient scales divide out at the outsider and are absorbed into
the child weights. For each positive δ, every nonstructural coefficient in
these witnesses has a strict sign, yielding its own full raw neighborhood.
Atδ=0 the coefficient−δ d2 vanishes; the exact family contradiction still
holds, but that row alone does not prove an open full-reward obstruction there.

The standalone pair checker also verifies(5), both order contradictions,
and all fourteen security-child duals at both parameter endpoints, including
the structural-zero conditions for the positive-parameter neighborhood claim.

These comparisons prove separation from the stated architectures and raw
criteria. They do not prove nonmembership in an unspecified maximal
neighborhood or a different equilibrium branch of an earlier local reset
existence theorem. The producers above state their scope directly; this comparison is not a
minimal-period or unrestricted nonexistence claim.

## 14. Complete reproduction and source correspondence

Appendices A, B, C and D are complete standalone checkers. Save them as
`complex_25_check.py`, `complex_64_check.py`, `complex_stationary_check.py`
and `complex_pair_check.py`, respectively, and run

```
python complex_25_check.py
python complex_64_check.py
python complex_stationary_check.py
python complex_pair_check.py
```

Python 3, SymPy and NumPy suffice; Appendix B itself uses only the standard
library. No saved strategic root, numerical solver, external certificate
payload or unlisted source import is used. The cap-box centers are rational
input data for complete contraction tests, not assumed fixed points.
Appendix A verifies every quadratic root identity, all four symbolic spectral
factors, both inverse-matrix positivity checks and the entire25-phase cap cube.
Appendix B verifies the generic elimination identities and the entire64-phase
endpoint cube. Appendix C verifies every origin support, all fourteen quotient
minors and the entire1568351-node stationary cube across the parameter interval.
Its optional `--origin-only` omits the final cube and is not a complete
stationary check. Appendix D verifies all sure-face identities, both complete
pair covers, inverse/order bounds and all fourteen security-child duals.
Its optional `--write-certificate FILE.json` records pair leaves as output,
never as an input assumption. All acceptance tests are exact rational or
integer comparisons; floating-point conversion only prints diagnostics.

The contraction, openness, unrestricted behavioral consumer and compactification
arguments are the mathematical proofs above. Checking the displayed finite
bounds does not replace those arguments.

The exact game-semantic contracts are `IsεQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/FirstBranch.lean`, and
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.

The native scalar complementarity correspondence is
`stationaryQuittingGain_complementarity_iff_endpoints` in
`UniformEquilibrium/Quitting/Stationary/Gain.lean`. The quotient predicate is
`QuittingResponseInvariantOnUnitCube` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`,
and its discrete degree calculation matches
`r0Degree_eq_sign_det_of_nonnegative_inverse` in
`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`.
The complete sure-face comparison covers `QuittingSingletonBaseCertificate`
in `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingletonBaseSemanticDispatch.lean`.
The exact leaver definitions are `HasProductLowQuittingPremium`,
`HasSupportSpecificQuittingLeavers`, `HasWeightedQuittingTrapLeavers` and
`IsCommonQuittingPremiumLeaver` in the corresponding files under
`UniformEquilibrium/Quitting/Classification/`. The singleton-cycle implication
is `BalancedSingletonCycleCertificate.exists_escortCycle` in
`UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean`.
The raw quiet-child definitions are `DeadlineWithdrawalRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalRaw.lean`,
`DeadlineSecurityRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityMixedRaw.lean`,
and `DeadlineSecurityTerminalRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityTerminalDebt.lean`.
The singleton floor bound is `deadlineWithdrawalSecurityValue_le_singleton`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityLP.lean`.
The results here are ordinary mathematical proofs. The finite contraction
certificates and parameterized comparisons are not asserted to be Lean-checked
instances of those declarations.


## Appendix A. Exact twenty-five-phase producer

```python
"""Exact 25-phase root producer for a four-player complex-spectrum table.

Python 3 and SymPy. Literal raw rewards, rational cap box and every proof
bound are supplied here. All acceptance uses exact outward integer intervals
or symbolic rational identities; floats only print results. No saved strategy
or external certificate data is read.
"""
from fractions import Fraction as F
from math import isqrt
BITS=512;D=1<<BITS
class Iv:
 def __init__(self,lo,hi=None,raw=False):
  if raw:self.lo,self.hi=lo,hi;return
  x=F(lo);self.lo=x.numerator*D//x.denominator;self.hi=-((-x.numerator*D)//x.denominator)
 @classmethod
 def box(cls,c,r):
  a=cls(F(c)-F(r));b=cls(F(c)+F(r));return cls(a.lo,b.hi,True)
 def __add__(self,o):
  if isinstance(o,Jet):return NotImplemented
  o=iv(o);return Iv(self.lo+o.lo,self.hi+o.hi,True)
 __radd__=__add__
 def __neg__(self):return Iv(-self.hi,-self.lo,True)
 def __sub__(self,o):return self+-iv(o)
 def __rsub__(self,o):return iv(o)+-self
 def __mul__(self,o):
  if isinstance(o,Jet):return NotImplemented
  o=iv(o);xs=[a*b for a in(self.lo,self.hi)for b in(o.lo,o.hi)]
  return Iv(min(xs)//D,-((-max(xs))//D),True)
 __rmul__=__mul__
 def __truediv__(self,o):
  o=iv(o);assert not o.lo<=0<=o.hi,('zero denominator',o.lo,o.hi)
  pairs=[(a*D,b)for a in(self.lo,self.hi)for b in(o.lo,o.hi)]
  return Iv(min(a//b for a,b in pairs),max(-((-a)//b)for a,b in pairs),True)
 def __rtruediv__(self,o):return iv(o)/self
 def sqrt(self):
  assert self.lo>0
  a=isqrt(self.lo*D);b=isqrt(self.hi*D)
  return Iv(a,b+(b*b<self.hi*D),True)
 def absupper(self):return max(-self.lo,self.hi)
 def lower(self):return float(F(self.lo,D))
 def upper(self):return float(F(self.hi,D))
 def __repr__(self):return str((self.lower(),self.upper()))
def iv(x):return x if isinstance(x,Iv)else Iv(x)
class Jet:
 def __init__(self,v,d=None):self.v=iv(v);self.d=[Iv(0)]*4 if d is None else d
 def __add__(self,o):
  o=jet(o);return Jet(self.v+o.v,[a+b for a,b in zip(self.d,o.d)])
 __radd__=__add__
 def __neg__(self):return Jet(-self.v,[-x for x in self.d])
 def __sub__(self,o):return self+-jet(o)
 def __rsub__(self,o):return jet(o)+-self
 def __mul__(self,o):
  o=jet(o);return Jet(self.v*o.v,[a*o.v+self.v*b for a,b in zip(self.d,o.d)])
 __rmul__=__mul__
 def __truediv__(self,o):
  o=jet(o);v=self.v/o.v
  return Jet(v,[(a-v*b)/o.v for a,b in zip(self.d,o.d)])
 def __rtruediv__(self,o):return jet(o)/self
 def sqrt(self):
  v=self.v.sqrt();return Jet(v,[a/(2*v)for a in self.d])
def jet(x):return x if isinstance(x,Jet)else Jet(x)


I=range(4);delta=F(1,1000);fav=(1,0,3,2);high={(0,2),(2,1),(1,3),(3,0)}
A=[[0,1,-6,-F(1,100)],[1,0,-F(3,2),-F(2,5)],[-delta,-F(3,5),0,1],[-F(7,100),-F(1,25),1,0]]
J=[[F(0)if i==j else F(1,100)if j==fav[i]else -A[i][j]*(F(9,10)if(i,j)in high else F(1,10))for j in I]for i in I]
SIGNS={(0,1):1,(0,2):-1,(0,3):1,(1,2):1,(1,3):-1,(2,3):-1};Z={}
for i in I:
 for mask in range(1,16):
  B=[j for j in I if mask>>j&1 and j!=i]
  if not B:v=0
  elif len(B)==1:v=J[i][B[0]]if mask>>i&1 else A[i][B[0]]+J[i][B[0]]
  elif len(B)==2:
   out=[j for j in I if j not in B];d=SIGNS[tuple(B)]*(1 if i==out[0]else-1);v=max(0,d)if mask>>i&1 else max(0,-d)
  else:v=0 if mask>>i&1 else 1
  Z[i,mask]=F(v)
WORD=[(0,1,2)]*20+[(0,2,3)]*3+[(1,2,3)]*2
CENTER=list(map(F,['.6032426876986211','.1316536363074683','.3158582125684314','.0018524455688325833']))

def odds012(b):
 b0,b1,b2,b3=b
 aa=b0+6-2*delta;bb=F(18,5)-F(9,10)*b0+(6-delta)*b1+2*b2+F(3,2)*delta;cc=F(9,10)*b0-b1*b2-F(18,5)*b1+F(3,2)*b2
 x=2*cc/(bb+(bb*bb+4*aa*cc).sqrt());y=(b2-delta*x)/(F(3,5)+x);w=(b1+x)/(F(3,2)-x)
 return[x,y,w,Jet(0)]
def odds023(b):
 b0,b1,b2,b3=b
 aa=b0+F(21,50)-F(2,25)*delta;bb=F(21,50)+delta/100+F(2,25)*b2+delta*b3-6*b3;cc=b0+b2*b3+b2/100+6*b3
 x=2*cc/(bb+(bb*bb+4*aa*cc).sqrt());y=(F(7,100)*x-b3)/(1-x);w=(delta*x-b2)/(1+x)
 return[x,Jet(0),y,w]
def odds123(b):
 b0,b1,b2,b3=b
 aa=F(51,250)+b1;bb=F(3,10)-F(11,25)*b2+F(9,10)*b3;cc=b1+F(2,5)*b2+F(3,2)*b3-b2*b3
 x=2*cc/(bb+(bb*bb+4*aa*cc).sqrt());y=(x/25-b3)/(1+x);w=(F(3,5)*x-b2)/(1-x)
 return[Jet(0),x,y,w]
ROOTS={(0,1,2):odds012,(0,2,3):odds023,(1,2,3):odds123}

def stage(b,support):
 odds=ROOTS[support](b);C=[];Q=[]
 for i in I:
  cn=b[i];qn=Jet(0);den=Jet(1)
  for j in I:
   if j!=i:den*=1+odds[j]
  for mask in range(16):
   if mask>>i&1:continue
   w=Jet(1)
   for j in I:
    if mask>>j&1:w*=odds[j]
   if mask:cn+=Z[i,mask]*w
   qn+=Z[i,mask|1<<i]*w
  C.append(cn/den);Q.append(qn/den)
 out=[Q[i]if i in support else C[i]for i in I]
 omitted=next(i for i in I if i not in support)
 return out,odds,Q[omitted]-C[omitted]
def ab(x):return F(x.absupper(),D)

def point_map():
 b=[Jet(c,[Iv(int(i==j))for j in I])for i,c in enumerate(CENTER)]
 for support in WORD:b,_,_=stage(b,support)
 return b

def verify(radius=F(1,10**10)):
 p=[Jet(c)for c in CENTER]
 b=[Jet(Iv.box(c,radius),[Iv(int(i==j))for j in I])for i,c in enumerate(CENTER)]
 rad=Iv.box(0,radius);minq=F(1);maxgap=F(-1)
 for number,support in enumerate(WORD):
  p,_,_=stage(p,support)
  old=[x.d[:]for x in b]
  local=[Jet(x.v,[Iv(int(i==j))for j in I])for i,x in enumerate(b)]
  b,odds,gap=stage(local,support)
  assert all(x.v.lo>0 for i,x in enumerate(odds)if i in support),(number,[(x.v)for x in odds])
  assert gap.v.hi<0,(number,gap.v)
  minq=min(minq,min(F((odds[i]/(1+odds[i])).v.lo,D)for i in support));maxgap=max(maxgap,F(gap.v.hi,D))
  for x in b:x.d=[sum((x.d[j]*old[j][k]for j in I),Iv(0))for k in I]
  for i in I:b[i].v=p[i].v+sum((rad*b[i].d[j]for j in I),Iv(0))
 normF=max(sum(ab(x)for x in row.d)for row in b)
 print('DIRECT normF',float(normF))
 assert normF<F(1,100)
 defect=max(ab(p[i].v-CENTER[i])for i in I)
 assert defect<F(1,10**14)
 assert minq>F(1,10000) and maxgap<-F(1,10)
 assert defect+normF*radius<radius
 print('PASS direct contraction:',float(normF),'defect',float(defect),
       'radius',float(radius),'minimum hazard',float(minq),'maximum inactive gap',float(maxgap))



def symbolic_audit():
 import sympy as S
 b=S.symbols('b0:4');v=S.symbols('v');ds=S.Rational(1,1000)
 ss=lambda f:S.Rational(f.numerator,f.denominator)
 AA=S.Matrix([[ss(F(x))for x in row]for row in A]);JJ=S.Matrix([[ss(x)for x in row]for row in J])
 assert all(v>0 for v in AA.inv()) and all(v>0 for v in (AA+JJ).inv())
 roots={
  (0,1,2):[v,(b[2]-ds*v)/(S.Rational(3,5)+v),(b[1]+v)/(S.Rational(3,2)-v),0],
  (0,2,3):[v,0,(S.Rational(7,100)*v-b[3])/(1-v),(ds*v-b[2])/(1+v)],
  (1,2,3):[0,v,(v/25-b[3])/(1+v),(S.Rational(3,5)*v-b[2])/(1-v)]}
 abc={
  (0,1,2):(b[0]+6-2*ds,S.Rational(18,5)-S.Rational(9,10)*b[0]+(6-ds)*b[1]+2*b[2]+S.Rational(3,2)*ds,S.Rational(9,10)*b[0]-b[1]*b[2]-S.Rational(18,5)*b[1]+S.Rational(3,2)*b[2]),
  (0,2,3):(b[0]+S.Rational(21,50)-S.Rational(2,25)*ds,S.Rational(21,50)+ds/100+S.Rational(2,25)*b[2]+ds*b[3]-6*b[3],b[0]+b[2]*b[3]+b[2]/100+6*b[3]),
  (1,2,3):(S.Rational(51,250)+b[1],S.Rational(3,10)-S.Rational(11,25)*b[2]+S.Rational(9,10)*b[3],b[1]+S.Rational(2,5)*b[2]+S.Rational(3,2)*b[3]-b[2]*b[3])}
 for support in WORD:
  odds=roots[support];aa,bb,cc=abc[support];pol=S.Poly(aa*v*v+bb*v-cc,v)
  for i in support:
   gap=-b[i]
   for mask in range(1,16):
    if mask>>i&1:continue
    ww=S.prod(odds[j]for j in I if mask>>j&1)
    gap+=ss(Z[i,mask|1<<i]-Z[i,mask])*ww
   numerator=S.cancel(gap).as_numer_denom()[0]
   assert S.rem(S.Poly(numerator,v),pol)==0
 # The complete spectral identity is retained symbolically in the weak loss.
 dd,ll=S.symbols('delta lambda');Ap=AA.copy();Ap[2,0]=-dd
 Jp=S.Matrix(4,4,lambda i,j:0 if i==j else S.Rational(1,100)if j==fav[i]else -Ap[i,j]*(S.Rational(9,10)if(i,j)in high else S.Rational(1,10)))
 for mat in (Ap,Ap+Jp):
  det=S.expand(mat.det());adj=mat.adjugate()
  assert S.degree(det,dd)<=1 and all(S.degree(v,dd)<=1 for v in adj)
  for endpoint in (0,ds):
   assert det.subs(dd,endpoint)>0 and all(v.subs(dd,endpoint)>0 for v in adj)
 weights={(0,1,2):(S.Rational(18,5),3*dd/2),
          (0,1,3):(S.Rational(7,250),S.Rational(1,2500)),
          (0,2,3):(S.Rational(21,50),dd/100),
          (1,2,3):(S.Rational(6,25),S.Rational(3,50))}
 for support,(kh,kl)in weights.items():
  expected=(ll+S.Rational(1,100))*(kh*(ll-S.Rational(9,10))**2+kl*(ll-S.Rational(1,10))**2)
  assert S.factor((ll*Ap.extract(support,support)+Jp.extract(support,support)).det()-expected)==0
  assert kh.subs(dd,ds)>0 and kl.subs(dd,ds)>0
 print('PASS literal endpoint equations for all three quadratic root branches and all four spectral identities')

if __name__=='__main__':
 symbolic_audit();verify()
 print('PASS exact 25-phase producer box; the behavioral and openness consumers are proved in the accompanying manuscript')
```

## Appendix B. Exact sixty-four-phase endpoint producer

```python
"""Exact dyadic validation of the high/low table at the zero endpoint.

Standard-library only. All60 rewards, the fixed64-date word and all
certificate numbers are literal in this file. Every arithmetic operation
rounds outwards.
"""
from fractions import Fraction as F
from itertools import combinations
from math import isqrt
import time
BITS=1024;D=1<<BITS
class Iv:
 def __init__(self,lo,hi=None,raw=False):
  if raw:self.lo,self.hi=lo,hi;return
  x=F(lo);self.lo=x.numerator*D//x.denominator;self.hi=-((-x.numerator*D)//x.denominator)
 @classmethod
 def box(cls,c,r):
  a=cls(F(c)-F(r));b=cls(F(c)+F(r));return cls(a.lo,b.hi,True)
 def __add__(self,o):
  if isinstance(o,Jet):return NotImplemented
  o=iv(o);return Iv(self.lo+o.lo,self.hi+o.hi,True)
 __radd__=__add__
 def __neg__(self):return Iv(-self.hi,-self.lo,True)
 def __sub__(self,o):return self+-iv(o)
 def __rsub__(self,o):return iv(o)+-self
 def __mul__(self,o):
  if isinstance(o,Jet):return NotImplemented
  o=iv(o);xs=[a*b for a in(self.lo,self.hi)for b in(o.lo,o.hi)]
  return Iv(min(xs)//D,-((-max(xs))//D),True)
 __rmul__=__mul__
 def __truediv__(self,o):
  o=iv(o);assert not o.lo<=0<=o.hi,('zero denominator',o.lo,o.hi)
  pairs=[(a*D,b)for a in(self.lo,self.hi)for b in(o.lo,o.hi)]
  return Iv(min(a//b for a,b in pairs),max(-((-a)//b)for a,b in pairs),True)
 def __rtruediv__(self,o):return iv(o)/self
 def sqrt(self):
  assert self.lo>0
  a=isqrt(self.lo*D);b=isqrt(self.hi*D)
  return Iv(a,b+(b*b<self.hi*D),True)
 def absupper(self):return max(-self.lo,self.hi)
 def lower(self):return float(F(self.lo,D))
 def upper(self):return float(F(self.hi,D))
 def __repr__(self):return str((self.lower(),self.upper()))
def iv(x):return x if isinstance(x,Iv)else Iv(x)
class Jet:
 def __init__(self,v,d=None):self.v=iv(v);self.d=[Iv(0)]*4 if d is None else d
 def __add__(self,o):
  o=jet(o);return Jet(self.v+o.v,[a+b for a,b in zip(self.d,o.d)])
 __radd__=__add__
 def __neg__(self):return Jet(-self.v,[-x for x in self.d])
 def __sub__(self,o):return self+-jet(o)
 def __rsub__(self,o):return jet(o)+-self
 def __mul__(self,o):
  o=jet(o);return Jet(self.v*o.v,[a*o.v+self.v*b for a,b in zip(self.d,o.d)])
 __rmul__=__mul__
 def __truediv__(self,o):
  o=jet(o);v=self.v/o.v
  return Jet(v,[(a-v*b)/o.v for a,b in zip(self.d,o.d)])
 def __rtruediv__(self,o):return jet(o)/self
 def sqrt(self):
  v=self.v.sqrt();return Jet(v,[a/(2*v)for a in self.d])
def jet(x):return x if isinstance(x,Jet)else Jet(x)

A=[[F(x)for x in row]for row in[[0,1,-6,'-.01'],[1,0,'-1.5','-.4'],[0,'-.6',0,1],['-.07','-.04',1,0]]]
J=[[F(x)for x in row]for row in[[0,'.01','5.4','.001'],['.01',0,'.15','.36'],[0,'.54',0,'.01'],['.063','.004','.01',0]]]
Z={}
for i in range(4):
 Z[i,1<<i]=F(0)
 for j in range(4):
  if i!=j:Z[i,1<<j]=A[i][j]+J[i][j];Z[i,(1<<i)|(1<<j)]=J[i][j]
for pair,sg in zip(combinations(range(4),2),(1,-1,1,1,-1,-1)):
 mask=sum(1<<j for j in pair);outside=[i for i in range(4)if i not in pair]
 for n,i in enumerate(outside):
  delta=sg*(-1 if n else 1);Z[i,mask]=F(max(0,-delta));Z[i,mask|(1<<i)]=F(max(0,delta))
for i in range(4):Z[i,15^(1<<i)]=F(1);Z[i,15]=F(0)
assert len(Z)==60

def coeff(a,u,v,b):
 delta=Z[a,(1<<a)|(1<<u)|(1<<v)]-Z[a,(1<<u)|(1<<v)]
 return -b[a],b[a]-A[a][u],b[a]-A[a][v],delta+A[a][u]+A[a][v]-b[a]
def mul(a,b):return[a[0]*b[0],a[0]*b[1]+a[1]*b[0],a[1]*b[1]]
def step(b,S):
 i,j,k=map(int,S)
 ci,ai,bi,di=coeff(i,j,k,b);cj,aj,bj,dj=coeff(j,i,k,b);ck,ak,bk,dk=coeff(k,i,j,b)
 nx=[-cj,-bj];dx=[aj,dj];ny=[-ci,-bi];dy=[ai,di]
 terms=[mul(dx,dy),mul(nx,dy),mul(ny,dx),mul(nx,ny)]
 cc=[sum(t[l]*a for t,a in zip(terms,[ck,ak,bk,dk]))for l in range(3)]
 disc=cc[1]*cc[1]-4*cc[2]*cc[0]
 zz=(-cc[1]+disc.sqrt())/(2*cc[2]);q=[Jet(0)]*4
 q[i]=(nx[0]+nx[1]*zz)/(dx[0]+dx[1]*zz);q[j]=(ny[0]+ny[1]*zz)/(dy[0]+dy[1]*zz);q[k]=zz
 out=[];gs=[]
 for a in range(4):
  opp=[l for l in range(4)if l!=a];P=Jet(0);Q=Jet(0);H=Jet(1)
  for l in opp:H*=1-q[l]
  for bits in range(8):
   mask=0;wt=Jet(1)
   for ii,l in enumerate(opp):
    if bits>>ii&1:mask|=1<<l;wt*=q[l]
    else:wt*=1-q[l]
   if mask:P+=wt*Z[a,mask]
   Q+=wt*Z[a,mask|(1<<a)]
  out.append(P+H*b[a]);gs.append(Q-out[-1])
 return out,q,gs
word=['013']*4+['012']*60

def compose(center,radius,verbose=False):
 b=[Jet(Iv.box(x,radius),[Iv(int(i==j))for j in range(4)])for i,x in enumerate(center)]
 minq=D;maxq=0;inactive=-10*D;surv=Iv(1);rows=[]
 for t,S in enumerate(word):
  b,q,g=step(b,S)
  for i in map(int,S):
   assert q[i].v.lo>0 and q[i].v.hi<D
   minq=min(minq,q[i].v.lo);maxq=max(maxq,q[i].v.hi)
  assert all(g[int(i)].v.lo <= 0 <= g[int(i)].v.hi for i in S)
  omitted=next(i for i in range(4)if str(i)not in S)
  assert g[omitted].v.hi<0
  inactive=max(inactive,g[omitted].v.hi)
  for i in range(4):surv*=1-q[i].v
  rows.append({'support':S,'cap':[(x.v.lower(),x.v.upper())for x in b],'hazards':[(x.v.lower(),x.v.upper())for x in q],'inactive':g[omitted].v.upper()})
  if verbose:print('phase',t,'width',max((x.v.hi-x.v.lo)/D for x in b),flush=True)
 return b,{'minq':minq,'maxq':maxq,'inactive':inactive,'survival':surv,'rows':rows}

def audit_symbolic_active_equations():
 # Sparse exact polynomials in b0,b1,b2,b3,z. No symbolic dependency.
 zero=(0,0,0,0,0)
 def const(a):return {} if not a else {zero:F(a)}
 def var(k):
  e=[0]*5;e[k]=1;return {tuple(e):F(1)}
 def add(*ps):
  out={}
  for p in ps:
   for e,c in p.items():out[e]=out.get(e,F(0))+c
  return {e:c for e,c in out.items()if c}
 def neg(p):return {e:-c for e,c in p.items()}
 def sub(p,q):return add(p,neg(q))
 def prod(*ps):
  out=const(1)
  for p in ps:
   nxt={}
   for e,c in out.items():
    for f,d in p.items():
     g=tuple(x+y for x,y in zip(e,f));nxt[g]=nxt.get(g,F(0))+c*d
   out={e:c for e,c in nxt.items()if c}
  return out
 b=[var(i)for i in range(4)];z=var(4)
 def row(a,u,v):
  delta=Z[a,(1<<a)|(1<<u)|(1<<v)]-Z[a,(1<<u)|(1<<v)]
  return neg(b[a]),sub(b[a],const(A[a][u])),sub(b[a],const(A[a][v])),sub(const(delta+A[a][u]+A[a][v]),b[a])
 def pmul(a,b):return[prod(a[0],b[0]),add(prod(a[0],b[1]),prod(a[1],b[0])),prod(a[1],b[1])]
 for i,j,k in [(0,1,2),(0,1,3)]:
  ci,ai,bi,di=row(i,j,k);cj,aj,bj,dj=row(j,i,k);ck,ak,bk,dk=row(k,i,j)
  nx=[neg(cj),neg(bj)];dx=[aj,dj];ny=[neg(ci),neg(bi)];dy=[ai,di]
  at=lambda p:add(p[0],prod(p[1],z))
  NX,DX,NY,DY=map(at,[nx,dx,ny,dy])
  assert not add(prod(ci,DY),prod(ai,NY),prod(bi,z,DY),prod(di,z,NY))
  assert not add(prod(cj,DX),prod(aj,NX),prod(bj,z,DX),prod(dj,z,NX))
  terms=[pmul(dx,dy),pmul(nx,dy),pmul(ny,dx),pmul(nx,ny)]
  cc=[add(*(prod(t[l],a)for t,a in zip(terms,[ck,ak,bk,dk])))for l in range(3)]
  cleared=add(prod(ck,DX,DY),prod(ak,NX,DY),prod(bk,NY,DX),prod(dk,NX,NY))
  assert cleared==add(cc[0],prod(cc[1],z),prod(cc[2],z,z))
 print('PASS: exact polynomial elimination identities for012 and013 active rows.')

if __name__=='__main__':
 audit_symbolic_active_equations()
 center=[F(x)for x in ['0.004118890025300792583695362537695543715792236764499152011090139632874172171045056749651981915674295160396853309659441455604098529901', '0.0001243482175163461881555454679752314397549106941919952765786180159590206637434094660072037251656962047098682135801304677257343514117', '0.00004190775560804728637263339044829948663033445855611154354232280109276626865643290562544450787265172745534118001684634872489965234201', '0.3690086159884435465928283186669010332053764555876554382079574148441777874623973295113738211805241067838667431903560321552244727305']];radius=F(1,10**110)
 start=time.time();image,stats=compose(center,radius)
 lip=max(sum(x.absupper()for x in row.d)for row in image)
 assert lip*1000<D,('Lipschitz',float(F(lip,D)))
 atcenter,_=compose(center,0)
 residual=max((atcenter[i].v-Iv(center[i])).absupper()for i in range(4))
 assert F(residual,D)<radius/100
 assert F(residual,D)+F(lip,D)*radius<radius
 assert stats['minq']*20000>D
 assert stats['maxq']*10<9*D
 assert stats['inactive']*100<-13*D
 assert stats['survival'].hi*10000<D
 print('PASS: exact dyadic contraction; Lipschitz < 1/1000; residual < radius/100; radius',radius)
 print('PASS: all192 active hazards >1/20000 and <9/10; all64 omitted gaps <-13/100; joint survival <1/10000.')
 print('actual bounds:',float(F(lip,D)),float(F(residual,D)),stats['survival'],'time',time.time()-start)
```

## Appendix C. Complete stationary and quotient audit

```python
"""Uniform stationary and response-quotient audit for the high/low crossing family.

Python 3, SymPy, NumPy. Standalone: no external source/data imports.
The literal family has actual rewards 1+Z, live and Never reward zero.
Every arithmetic exclusion uses rational numbers or Python integer objects.
Both closed children of every split are retained; endpoint coefficient tests
cover every delta in [0,1/1000] by affine interpolation. Budget exhaustion
raises an error, never a proof result. No unrestricted UE obstruction claimed.
"""
import argparse
import itertools
from fractions import Fraction
import numpy as np
import sympy as s

I=tuple(range(4))
Q=Fraction
q=s.symbols('q0:4')
FAVORITE=(1,0,3,2)

def table(delta):
    R=s.Rational
    A=s.Matrix([[0,1,-6,-R(1,100)], [1,0,-R(3,2),-R(2,5)],
        [-delta,-R(3,5),0,1], [-R(7,100),-R(1,25),1,0]])
    J=s.Matrix(4,4,lambda i,j:0 if i==j else R(1,100) if j==FAVORITE[i] else -A[i,j]*(R(9,10) if (i,j) in ((0,2),(2,1),(1,3),(3,0)) else R(1,10)))
    Gamma=A+J
    z={(i,0):s.S.Zero for i in I}
    for i in I:
        z[i,1<<i]=s.S.Zero
        for j in I:
            if j!=i:
                z[i,1<<j]=Gamma[i,j]
                z[i,(1<<i)|(1<<j)]=J[i,j]
    for pair,sign in zip(itertools.combinations(I,2),(1,-1,1,1,-1,-1)):
        mask=sum(1<<j for j in pair)
        outside=[i for i in I if not mask>>i&1]
        for order,i in enumerate(outside):
            delta=sign*(-1 if order else 1)
            z[i,mask]=s.sympify(max(0,-delta))
            z[i,mask|(1<<i)]=s.sympify(max(0,delta))
    for i in I:
        z[i,15^(1<<i)]=s.S.One
        z[i,15]=s.S.Zero
    assert len(z)==64
    return z

def fields(z):
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

def coefficients(polys):
    assert len(polys)==8
    assert all(poly.degree(q[j])<=2 for poly in polys for j in I)
    raw=[]
    for poly in polys:
        for alpha in itertools.product(range(3),repeat=4):
            value=sum(v*s.prod(s.binomial(alpha[j],mon[j])/s.binomial(2,mon[j])
                        for j in I) for mon,v in poly.terms()
                        if all(mon[j]<=alpha[j] for j in I))
            raw.append(s.sympify(value))
    denominator=int(s.ilcm(*(s.denom(v)for v in raw)))
    arr=np.array([int(v*denominator)for v in raw],dtype=object).reshape(8,3,3,3,3)
    return denominator,arr

def split_coefficients(b,axis):
    # Both child arrays represent their exact polynomials at FOUR TIMES
    # the parent's positive common denominator. Thus all sign tests below
    # use integers only; no interval rounding or tolerance is involved.
    v=np.moveaxis(b,axis+1,-1)
    a0,a1,a2=v[...,0],v[...,1],v[...,2]
    middle=a0+2*a1+a2
    left=np.stack((4*a0,2*(a0+a1),middle),axis=-1)
    right=np.stack((middle,2*(a1+a2),4*a2),axis=-1)
    return np.moveaxis(left,-1,axis+1),np.moveaxis(right,-1,axis+1)

def certify(polys,max_nodes=2000000,max_depth=120):
    denominator,b=coefficients(polys)
    stack=[([Q(0)]*4,[Q(1)]*4,b,0)]
    nodes=leaves=depthmax=origin=0
    while stack:
        lo,hi,b,depth=stack.pop()
        nodes+=1;depthmax=max(depthmax,depth)
        if nodes%100000==0:print("Progress nodes",nodes,"stack",len(stack),"depth",depth,flush=True)
        if max(hi)<=Q(1,512):
            leaves+=1;origin+=1;continue
        witness=False
        for i in I:
            # Rows i and i+4 are the two parameter endpoints. Each
            # intermediate Bernstein coefficient is their convex blend.
            row=np.concatenate((b[i].flatten(),b[i+4].flatten()))
            if (lo[i]>0 and max(row)<0) or (hi[i]<1 and min(row)>0):
                witness=True;break
        if witness:
            leaves+=1;continue
        if nodes>=max_nodes or depth>=max_depth:
            raise RuntimeError('Unexcluded box after budget: '+str({
                'nodes':nodes,'depth':depth,'lo':lo,'hi':hi}))
        widths=[hi[i]-lo[i]for i in I]
        choices=[i for i in I if widths[i]==max(widths)]
        axis=choices[depth%len(choices)]
        left,right=split_coefficients(b,axis)
        middle=(lo[axis]+hi[axis])/2
        lower=lo.copy();lower[axis]=middle
        upper=hi.copy();upper[axis]=middle
        stack.append((lower,hi,right,depth+1))
        stack.append((lo,upper,left,depth+1))
    assert nodes==2*leaves-1
    assert origin==1
    print('PASS: uniform entire high/low stationary cube',nodes,'nodes',leaves,'leaves',depthmax,'depth',origin,'origin',flush=True)

def partitions(items):
    if not items:
        yield ()
        return
    first,*rest=items
    for part in partitions(rest):
        yield ((first,),)+part
        for j,block in enumerate(part):
            yield part[:j]+((first,)+block,)+part[j+1:]

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--origin-only',action='store_true')
    parser.add_argument('--max-nodes',type=int,default=2000000)
    parser.add_argument('--max-depth',type=int,default=120)
    args=parser.parse_args()
    d=s.Symbol('delta',real=True);dmax=s.Rational(1,1000)
    z=table(d);H,F,g=fields(z)
    assert len(z)==64
    assert z[2,1]==-9*d/10 and z[2,5]==d/10
    assert all(not value.has(d)for key,value in z.items()if key not in((2,1),(2,5)))
    assert all(s.Poly(f.as_expr(),d).degree()<=1 for f in F)
    Gamma=s.Matrix([[z[i,1<<j]for j in I]for i in I])
    J=s.Matrix([[z[i,(1<<i)|(1<<j)]if i!=j else 0 for j in I]for i in I])
    A=Gamma-J
    endpoints=[]
    for dd in (s.S.Zero,dmax):
        zz={key:value.subs(d,dd)for key,value in z.items()}
        FF=[s.Poly(f.as_expr().subs(d,dd),*q)for f in F]
        GG=Gamma.subs(d,dd);JJ=J.subs(d,dd)
        assert all(zz[i,m]>=0 for i in I for m in range(1,16)if m>>i&1)
        assert all(FF[i].coeff_monomial(1)==0 for i in I)
        assert all(FF[i].coeff_monomial(q[j])==-GG[i,j]for i in I for j in I)
        KK=max(sum(abs(v)for mon,v in f.terms()if sum(mon)>=2)for f in FF)
        BB=GG.inv();LL=max(sum(BB.row(i))for i in I)
        assert min(BB)>0
        endpoints.append((zz,FF,GG,JJ,KK,LL))
    # Determinant and every adjugate entry are affine in delta and
    # strictly positive at both endpoints, hence throughout the interval.
    for matrix in (Gamma,A):
        det=s.expand(matrix.det());adj=matrix.adjugate()
        assert s.Poly(det,d).degree()<=1
        assert all(s.Poly(v,d).degree()<=1 for v in adj)
        assert all(det.subs(d,dd)>0 and min(adj.subs(d,dd))>0 for dd in (0,dmax))
    print("Gamma determinant",s.factor(Gamma.det()),"inverse min at0",min(Gamma.subs(d,0).inv()),flush=True)
    assert min(A.subs(d,0).inv())==s.Rational(40,773)
    K=max(e[4]for e in endpoints);L=max(e[5]for e in endpoints)
    # Coefficient absolute sums are convex in delta. Each inverse row
    # sum is a positive affine/affine quotient, monotone or constant.
    assert K*L/512<1
    for owner in I:
        other=next(i for i in I if all(e[2][i,owner]<0 for e in endpoints))
        for zz,FF,GG,JJ,KK,LL in endpoints:
            t=s.Symbol('t')
            got=FF[other].as_expr().subs({q[i]:t if i==owner else 0 for i in I})
            assert s.expand(got-t*(JJ[other,owner]*t-GG[other,owner]))==0
            assert JJ[other,owner]>0
    for i,j in itertools.combinations(I,2):
        for zz,FF,GG,JJ,KK,LL in endpoints:
            assert GG[i,j]<0 or GG[i,j]>JJ[i,j]>0
            t=s.Symbol('t')
            got=FF[i].as_expr().subs({q[h]:t if h==j else 0 for h in I})
            assert s.expand(got-t*(JJ[i,j]*t-GG[i,j]))==0
    for support in itertools.combinations(I,3):
        owner=next(i for i in support if FAVORITE[i]not in support)
        j,k=[h for h in support if h!=owner]
        for zz,FF,GG,JJ,KK,LL in endpoints:
            cross=-GG[owner,j]-GG[owner,k];passive=zz[owner,(1<<j)|(1<<k)]
            assert GG[owner,j]<=0 and GG[owner,k]<=0 and passive>=0
            assert (cross+passive)/512<cross
    print('PASS: uniform all-support origin; K=',K,'L=',L,'KL/512=',K*L/512)
    print('PASS: Gamma and A inverses strictly positive throughout [0,1/1000]')
    count=0;invariant=[]
    for part in partitions(list(I)):
        ts=s.symbols('t:'+str(len(part)))
        sub={q[i]:ts[j]for j,block in enumerate(part)for i in block}
        polys=[s.Poly(ff.as_expr().subs(sub),*ts)for ff in F]
        witness=None
        for block in part:
            for i,j in itertools.combinations(block,2):
                monoms=sorted(set(polys[i].monoms())|set(polys[j].monoms()),key=lambda a:(sum(a),a))
                for aa,bb in itertools.combinations(monoms,2):
                    minor=s.expand(polys[i].coeff_monomial(aa)*polys[j].coeff_monomial(bb)
                        -polys[i].coeff_monomial(bb)*polys[j].coeff_monomial(aa))
                    if minor.subs(d,0)!=0:
                        witness=(i,j,aa,bb,minor);break
                if witness:break
            if witness:break
        if witness:
            minor=s.Poly(witness[-1],d);constant=minor.coeff_monomial(1)
            print("Quotient minor",part,witness,flush=True)
            # This simple exact perturbation bound rules out a zero on
            # the WHOLE closed parameter interval, not only near zero.
            remainder=sum(abs(c)*dmax**mon[0]for mon,c in minor.terms()if mon[0]>0)
            assert remainder<abs(constant)
            count+=1
        else:
            invariant.append(part)
    assert count==14 and invariant==[((0,),(1,),(2,),(3,))]
    print('PASS: all15 partitions;all14 nondiscrete coefficient minors nonzero uniformly')
    print('PASS: discrete Gamma has positive inverse/determinant;R0 degree+1')
    if not args.origin_only:
        certify(endpoints[0][1]+endpoints[1][1],args.max_nodes,args.max_depth)
    print('SCOPE: stationary prescribed profiles and response quotients only;no UE gap claim')

if __name__=='__main__':main()
```

## Appendix D. Complete pair, sure-face and raw-dual audit

```python
"""Uniform exact proper alternating-pair exclusion for the high/low crossing family.

Python 3, SymPy, NumPy. All proof arithmetic is rational or Python integer.
All sixty rewards and proof rules are supplied here; no data files are read.
Optional --write-certificate PATH records every exact dyadic leaf.
This excludes proper four-owner two-pair Nash, not arbitrary equilibria.
"""
import argparse
import itertools
import json
from fractions import Fraction
import numpy as np
import sympy as s

I=range(4)
delta_parameter=s.symbols("delta_parameter",real=True)
A=s.Matrix([[0,1,-6,-s.Rational(1,100)],
 [1,0,-s.Rational(3,2),-s.Rational(2,5)],
 [-delta_parameter,-s.Rational(3,5),0,1],
 [-s.Rational(7,100),-s.Rational(1,25),1,0]])
FAVORITE=(1,0,3,2)
J=s.Matrix(4,4,lambda i,j:0 if i==j else s.Rational(1,100) if j==FAVORITE[i] else -A[i,j]*(s.Rational(9,10) if (i,j) in ((0,2),(2,1),(1,3),(3,0)) else s.Rational(1,10)))
Gamma=A+J
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
            z[i,mask]=s.sympify(value)
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
    arr=np.array([int(v*denominator)for v in raw],dtype=object).reshape(16,3,3,3,3)
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
    assert all(s.Poly(p.as_expr(),delta_parameter).degree()<=1 for p in equations+gaps)
    ends=[s.S.Zero,s.Rational(1,1000)]
    # Every inverse entry has a positive affine numerator and one common
    # positive affine denominator. Each row sum is fractional linear, so
    # its supremum on this parameter interval is at an endpoint.
    determinant=s.expand(Gamma.det());adjugate=Gamma.adjugate()
    assert s.Poly(determinant,delta_parameter).degree()<=1
    assert all(s.Poly(v,delta_parameter).degree()<=1 for v in adjugate)
    assert all(determinant.subs(delta_parameter,d)>0 for d in ends)
    assert all(v.subs(delta_parameter,d)>0 for v in adjugate for d in ends)
    L=max(sum(Gamma.subs(delta_parameter,d).inv().row(i))for d in ends for i in I)
    # Coefficient absolute-value sums are convex in the parameter.
    K=max(sum(abs(v.subs(delta_parameter,d))for mon,v in p.terms()if sum(mon)>=2)
          for p in equations for d in ends)
    origin_radius=Fraction(1,256)
    assert L*K/256<1
    endpoints=[s.Poly(p.as_expr().subs(delta_parameter,d),*q)
               for d in ends for p in equations+gaps]
    den,b=coefficients(endpoints)
    stack=[(b,(Fraction(0),)*4,(Fraction(1),)*4,'')]
    leaves=[];nodes=0;maxdepth=0
    while stack:
        b,lo,hi,path=stack.pop();nodes+=1;maxdepth=max(maxdepth,len(path))
        reason=None;bound=None;index=None
        if max(hi)<=origin_radius:
            reason='analytic_origin'
        else:
            flat=b.reshape(16,-1)
            mins=[min(min(flat[i]),min(flat[8+i]))for i in range(8)]
            maxs=[max(max(flat[i]),max(flat[8+i]))for i in range(8)]
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
    assert nodes==2*len(leaves)-1
    return {'mate':mate,'L':str(L),'K':str(K),'origin_radius':str(origin_radius),
            'nodes':nodes,'maxdepth':maxdepth,'leaves':leaves}

def sure_faces(z):
    gaps=[]
    for i in I:
        value=0
        for mask in range(16):
            if mask>>i&1:continue
            w=s.prod(q[j] if mask>>j&1 else 1-q[j] for j in I if j!=i)
            value+=(z[i,mask|(1<<i)]-(z[i,mask] if mask else 0))*w
        gaps.append(s.factor(value))
    x,y,w=s.symbols('x y w')
    f0=[s.expand(g.subs(dict(zip(q,(1,x,y,w)))))for g in gaps]
    assert s.expand(f0[1]-(-1+2*w*(1-y)))==0
    a=delta_parameter+(1-delta_parameter)*x
    assert s.expand(f0[2]-(a-(1+a)*w))==0
    assert s.expand(f0[3]-(7-107*x+93*y*(1-x))/100)==0
    assert s.simplify(f0[0].subs({x:s.Rational(7,107),y:0,w:s.Rational(1,2)}))==-s.Rational(13,214)
    assert s.simplify(f0[2].subs({x:s.Rational(7,107),y:0,w:s.Rational(1,2)}))==(50*delta_parameter-50)/107
    for owner in (1,3):
        assert all(s.diff(g.subs(q[owner],1),delta_parameter)==0 for g in gaps)
    assert all(s.diff(g.subs(q[2],1),delta_parameter)==0 for i,g in enumerate(gaps)if i!=2)
    radical=s.sqrt(205)
    point={q[0]:(-5+radical)/18,q[1]:(15-radical)/20,q[2]:1,q[3]:(22-radical)/9}
    upper=s.simplify(gaps[2].subs(point).subs(delta_parameter,s.Rational(1,1000)))
    assert s.simplify(upper-(170187-12919*radical)/18000)==0
    assert 12919**2*205-170187**2>0
    assert s.expand(s.diff(gaps[2],delta_parameter)-q[0]*(1-q[1])*(1-q[3]))==0
    print('PASS all parameter-dependent sure-face identities; remaining faces unchanged')

def raw_guards(z):
    d=delta_parameter;ends=(s.S.Zero,s.Rational(1,1000));B=Gamma.inv()
    for who,other in ((3,0),(0,2)):
        margin=s.factor(Gamma.det()*(B[who,who]*J[who,other]-s.Rational(1,768)))
        assert s.Poly(margin,d).degree()<=1
        assert all(margin.subs(d,t)>0 for t in ends)
        print('Exact scheduled inverse-cap obstruction',who,other,margin)
    # Literal opposite-row guards fail for each possible preferred edge.
    for i,j,mask,swapped in ((0,1,12,12),(1,0,5,6),(2,3,9,5),(3,2,3,3)):
        assert z[i,mask]==1 and z[j,swapped]==0
    assert Gamma[1,3]/Gamma[0,3]==s.Rational(40,9)
    assert Gamma[0,2]/Gamma[1,2]==s.Rational(4,9)
    assert Gamma[1,0]/Gamma[0,1]==1
    checked=0
    for mask in range(1,15):
        child=[i for i in I if mask>>i&1]
        if len(child)==1:
            j=child[0];h={0:3,1:2,2:0,3:1}[j];S=mask
        elif len(child)==2:
            h={3:2,5:3,9:1,6:0,10:2,12:1}[mask]
            S={3:2,12:4}.get(mask,mask)
        elif mask==14:
            # Ten times future S12 plus future S2 gives a strict dual,
            # including all nonnegative advance weights without bounds.
            lhs=-10*z[0,6]-z[0,4]
            coeff=[-10*z[i,6]-z[i,4]for i in child]
            assert lhs==s.Rational(3,5) and coeff==[-s.Rational(3,20),-s.Rational(27,5),-s.Rational(1101,100)]
            checked+=1;continue
        else:h,S={7:(3,5),11:(2,10),13:(1,9)}[mask]
        lhs=z[h,S|(1<<h)]-z[h,S]
        advance=[z[i,S|(1<<i)]-z[i,S]for i in child]
        withdrawal=[s.S.Zero if not S>>i&1 or S==(1<<i)
                    else z[i,S^(1<<i)]-z[i,S]for i in child]
        assert all(s.Poly(v,d).degree()<=1 for v in [lhs]+advance+withdrawal)
        assert all(lhs.subs(d,t)>0 for t in ends)
        assert all(v.subs(d,t)<=0 for v in advance+withdrawal for t in ends)
        # At positive delta the only zero coefficients are structural
        # membership zeros or the universal singleton floor upper bound0.
        assert all(v.subs(d,ends[1])<0 or S>>i&1 for i,v in zip(child,advance))
        assert all(v.subs(d,ends[1])<0 or not S>>i&1 or S==(1<<i)
                   for i,v in zip(child,withdrawal))
        checked+=1
    assert checked==14
    print('PASS uniform inverse-corner/order obstructions and all14 literal security-child duals')

def boundary_jordan_lead():
    lam=s.Symbol('lambda');active=(0,1,2)
    aa=A.extract(active,active);jj=J.extract(active,active)
    target=(lam+s.Rational(1,100))*(s.Rational(3,2)*delta_parameter*(lam-s.Rational(1,10))**2
                                 +s.Rational(18,5)*(lam-s.Rational(9,10))**2)
    assert s.expand((lam*aa+jj).det()-target)==0
    a0=aa.subs(delta_parameter,0);j0=jj.subs(delta_parameter,0);r=s.Rational(9,10)
    x=s.Matrix([s.Rational(120,91),0,1]);v=-a0*x
    y=s.Matrix([s.Rational(1650,8281),s.Rational(600,91),0]);u=-a0*y
    m=-j0*a0.inv()
    assert v==s.Matrix([6,s.Rational(33,182),0])
    assert u==s.Matrix([-s.Rational(600,91),-s.Rational(1650,8281),s.Rational(360,91)])
    assert (m-r*s.eye(3))*v==s.zeros(3,1)
    assert (m-r*s.eye(3))*u==v
    assert (j0+r*a0)*y==v
    assert all(t>=0 for t in x) and all(t>=0 for t in y) and all(x[i]+y[i]>0 for i in range(3))
    print('PASS exact boundary012 Jordan chain; linear transient only, not a nonlinear root trajectory')

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write-certificate')
    args=parser.parse_args();z=table();sure_faces(z);raw_guards(z);boundary_jordan_lead()
    friendly=(1,0,3,2)
    assert all(-A[i,friendly[i]]==-1 for i in I)
    records=[certify(z,mate)for mate in ((2,3,0,1),(3,2,1,0))]
    if args.write_certificate:
        with open(args.write_certificate,'w')as out:json.dump(records,out,indent=2)
    for r in records:
        print('PASS uniform delta[0,1/1000]',r['mate'],r['nodes'],'nodes',len(r['leaves']),'leaves',
              'depth',r['maxdepth'],'K',r['K'],'L',r['L'])
    print('PASS complete proper two-pair parameter cube; semantic zero/sure cases require the accompanying proof')

if __name__=='__main__':main()
```
