# Triple–singleton phases with finite collision-box caps

This is an ordinary-mathematics uniform-equilibrium producer from raw
four-player reward data. No odds, policy, strategic certificate or
normalization is supplied. The completion family has a full sixty-coordinate
open neighborhood outside the concrete persistent-base screens and the
other raw criteria compared below. It does not cover every Fin4 table and
is not a Lean verification.

### Exact raw statement

Let I={0,1,2,3}, A={0,1,2}, b=3. At every live date each player privately
and independently chooses Continue or Quit; public past actions are observed.
The first nonempty quitting coalition S absorbs at a finite real vector r(S).
The live date selecting absorption pays zero, subsequent stages pay r(S),
and joint Never pays zero. Every unilateral replacement is a complete
behavioral strategy. All claims concern expected payoff. Put s_i=r_i({i}),
Γ_ii=0 and Γ_ij=r_i({j})−s_i for i≠j.

For distinct i,j∈A define Π_ij=r_i({i,j})−s_i and
c_ij=r_i({i,j})−r_i({j}). For i∈A, writing A−i={j,k}, put

    Π_iA=r_i(A)−s_i,                 c_iA=r_i(A)−r_i({j,k}),
    M_i=max(0,Π_ij,Π_ik,Π_iA),      B_i=max(0,Γ_ib,M_i),
    R_j=min[i∈A−j] B_i/c_ij.                         (T1)

Assume the following finite raw inequalities:

    c_ij>0 for all six ordered i≠j in A,
    c_iA≥0 for every i∈A.                            (T2a)

For each i∈A separately assume at least one of the two raw alternatives:

    r_i({i,b})≤s_i;                                   (T2b)
    Π_ij≥0, Π_ik≥0, Π_iA≥0 and r_i({i,b})≤r_i({b}).   (T2c)

Different players may use different alternatives. Under(T2b) their within-A
participant premiums remain arbitrary signed data. Under(T2c) those three
premiums are nonnegative, but own levels and all other rewards may still
have either sign.

For the singleton player b put a=r_b(I)−s_b and define the multiaffine
polynomial

    C_b(X)=Σ[j∈A](r_b({b,j})−s_b)X_j
          +Σ[{j,k}⊆A](r_b({b,j,k})−s_b)X_jX_k
          +aX_0X_1X_2.

For every nonempty subset S⊆A let v^S_j=R_j if j∈S and v^S_j=0
otherwise. Require the seven finite raw tests

    C_b(v^S)≤0                for every ∅≠S⊆A.       (T3)

There is no separate sign assumption on the three pair coefficients, the
three triple coefficients or a. If some R_j=0, coincident vertices are
simply repeated tests; no division by R_j is needed.

Subject to the stated comparisons, singleton levels, passive rewards on A
coalitions, other participant rewards and a itself are arbitrary signed
finite numbers.
In particular the grand participant premium a may be strictly positive.
There is no matrix, normalization, root, hazard or equilibrium hypothesis.

Theorem: every such table has one fixed uniform-equilibrium payoff. More
precisely, if its actual Γ is R0 of degree one, the proof produces a nonzero
nonnegative odds vector with at least two positive coordinates, and an
exact terminal Nash profile alternating the joint A row and the solo b row.
The same profile delivers one fixed target and is an approximate Nash
profile for every sufficiently large finite horizon. Properness of all four
coordinates is not claimed. Otherwise the existing original-game no-UE
degree criterion supplies the existence alternative. This is not stationary
repetition of a finite persistent-base profile.

### Tracked mathematical dependencies

The original-game reduction is
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`.
Its statement supplies full R0 and degree one from bare original no UE,
without auxiliary-game no UE, own-sign or strategic assumptions.

The degree convention is given by `r0Degree`,
`localDegree_lcpMinBoxProblem_zero_eq_r0Degree` and
`isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean`, and
`ambientDegree_lcpMinMap_zero_eq_r0Degree` in
`MathUE/LinearProgramming/R0AmbientDegree.lean`. The latter identifies the
same literal homogeneous minimum map on every open bounded origin
neighborhood. The needed homotopy, excision and empty-fiber degree facts
are `ambientDegree_homotopy` in
`MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`,
`ambientDegree_excision` in
`MathUE/Topology/AmbientDegreeProperties.lean`, and
`ambientDegree_eq_zero_of_forall_ne` in `MathUE/Topology/AmbientDegree.lean`.
These interfaces refer to the same literal minimum map. No arbitrary
chart comparison or finite/nondegenerate nonlinear root census is assumed.

### The nonlinear complementarity system

For X≥0 write q_i=X_i/(1+X_i). For i∈A−{j,k} define

    D_i=(1+X_j)(1+X_k),
    P_i=Π_ij X_j+Π_ik X_k+Π_iA X_jX_k,
    L_i=c_ij X_j+c_ik X_k+c_iA X_jX_k,
    U_i=s_i+P_i/D_i,             W_i=s_i+L_i.        (T4)

For b put U_b=W_b=s_b. U is the value before the A date; W is the
value before the b date. In the A row, player i's forced Quit endpoint is
exactly U_i. Its forced Continue endpoint with tail W is also U_i:
multiply by D_i, use Γ_ij=Π_ij−c_ij and
r_i({j,k})−s_i=Π_iA−c_iA. Thus no active-coordinate equation is lost.
The b-date Continue endpoint is (U_i+X_b r_i({b}))/(1+X_b).
Its excess over W_i is e_i/(1+X_b), where

    e_i=Γ_ib X_b−(1+X_b)L_i+P_i/D_i.                (T5)

For b, the A-date Continue excess over s_b is e_b/D_A, with

    D_A=∏[j∈A](1+X_j),
    e_b=Σ[j∈A]Γ_bj X_j
         +Σ[{j,k}⊆A](r_b({j,k})−s_b)X_jX_k
         +(r_b(A)−s_b)X_0X_1X_2.                    (T6)

There is no sign condition on the last four coefficients. The desired
system is X≥0, e≥0, X_i e_i=0. It has the form e=ΓX−N(X), where

    N_i=Π_ij X_j+Π_ik X_k−P_i/D_i
         +X_b(c_ij X_j+c_ik X_k)
         +(1+X_b)c_iA X_jX_k                       for i∈A,
    N_b=−Σ[{j,k}⊆A](r_b({j,k})−s_b)X_jX_k
         −(r_b(A)−s_b)X_0X_1X_2.                   (T7)

Every N_i is continuous on the orthant and N(X)=O(‖X‖²) at zero.
Extending by N(x⁺), where positive part is coordinatewise, gives a
continuous field on all of ℝ⁴ with the same quadratic bound at zero.

### All feasible nonnegative odds are bounded

Consider the larger set E={X≥0:e(X)≥0}, not merely roots. For i∈A,
P_i/D_i is a convex combination of 0,Π_ij,Π_ik,Π_iA, hence is≤M_i.
Since L_i≥0, (T5) gives

    (1+X_b)L_i≤Γ_ib X_b+M_i,
    L_i≤(Γ_ib X_b+M_i)/(1+X_b)≤B_i.                (T8)

Therefore X_j≤B_i/c_ij for every i∈A−j, and X_j≤R_j.
R0 implies some i∈A has Γ_ib<0: otherwise column b is nonnegative
and X=e_b is a nonzero homogeneous complementary solution. For that i,
(T8), together with L_i≥0, gives X_b≤M_i/(−Γ_ib). Thus E is
closed and bounded. These bounds do not use the signs of any passive A
reward, and do not use the grand joining cap that is being proved later.

### A global degree zero and local degree one force a nonzero root

Assume Γ is R0 with degree one. Define, coordinatewise,

    H_λ(x)=min(x,Γx−N(x⁺)−λ·1),          λ≥0.       (T9)

A zero of H_λ has x≥0 and e(x)≥λ·1, so every zero belongs to the
same bounded E. Choose an open origin-centered ball containing E strictly.
For λ larger than every coordinate of e on E, H_λ has no zero.
The continuous homotopy H_{tλ} has no frontier zero; homotopy invariance
and empty-fiber normalization give total degree zero for H_0 on that ball.

The homogeneous field F(x)=min(x,Γx) has only the origin as a zero.
By compactness of the unit sphere and positive homogeneity, ‖F(x)‖≥m‖x‖
for some m>0. Coordinatewise minimum is 1-Lipschitz in its second entry,
so min(x,Γx−tN(x⁺)) differs from F by O(‖x‖²), uniformly in t∈[0,1].
On a sufficiently small sphere the entire homotopy is nonzero. Its local
degree is therefore the homogeneous R0 degree, namely one, by the exact
source comparison cited above. If H_0 had no zero other than the origin,
excision from the large ball to the small ball would equate zero and one.
Consequently H_0 has a nonzero complementary root X.

Such a root cannot have singleton support. Support {b} would give a
nonnegative column b of Γ. For support {j}⊆A and each i∈A−j,
(T5) gives Γ_ij≥Π_ij X_j/(1+X_j). If Π_ij<0 then
Γ_ij=Π_ij−c_ij<Π_ij<Π_ij X_j/(1+X_j), impossible. Otherwise
Γ_ij≥0. Equation(T6) gives Γ_bj≥0. Hence column j would be
nonnegative, again contradicting R0. Thus at least two q_i are positive.
All q_i are strictly below one because every X_i is finite.

### The seven vertex tests give the actual passive Quit cap

For i∈A, the forced Quit endpoint on the passive b date is
(s_i+X_b r_i({i,b}))/(1+X_b). Under(T2b) it is≤s_i≤W_i.
Under(T2c) the cap follows from the corrected policy equation below.
For b, the A-date forced Quit minus s_b is exactly

    C_b(X)/D_A.                                      (T10)

A multiaffine function on the box ∏[j∈A][0,R_j] is a convex combination
of its vertex values. Explicitly, if R_j>0 use weights X_j/R_j and
1−X_j/R_j in that coordinate; if R_j=0 the coordinate is constantly zero.
Iterating these affine identities gives the stated convex combination.
The empty vertex has C_b(0)=0, and(T3) bounds the other seven vertices.
Since(T8) puts every produced X in this box, C_b(X)≤0. This includes
all simultaneous double and triple opponent outcomes; none is discarded.

A useful sufficient subclass has a⁺=max(a,0),
r_b({b,j})≤s_b and
r_b({b,j,k})−s_b≤−a⁺R_l/3 for {j,k,l}=A. Each quadratic term is then
at most −a⁺X_0X_1X_2/3, so the three terms offset aX_0X_1X_2.
The vertex condition is strictly broader; a positive triple coefficient
can instead be offset by the linear terms. A complete raw-scope witness
is given below.

The subclass with all seven nonempty anchor participant rewards bounded
by s_b has no additional UE coverage. Under
bare original no UE, `nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`
positively rescales every own premium and joining comparison. Those seven
anchor caps force the greatest premium core into A; its empty/pair cases
are consumed by `exists_uniformEquilibriumPayoff_of_empty_or_signed_pair_core_weakSameSign`
in `UniformEquilibrium/Quitting/Classification/Existence/SignedPairCoreRewardClosure.lean`,
and its joining-attractive triple case by the corresponding triple-core
theorem. A positive anchor grand premium leaves that particular
whole-class inclusion; the separating table below also defeats the exact
concrete punishment-tail consumers.

### Inactive coordinates, actual payoff and arbitrary behavioral replies

If q_i>0, complementarity gives e_i=0 and (U_i,W_i) already obey both
policy equations. Put (U_i*,W_i*)=(U_i,W_i) in this case. For inactive
i∈A put d_i=1/D_i and d_b=1/(1+X_b). The actual policy values are

    ΔW_i=[e_i/(1+X_b)]/[1−d_i d_b]≥0,
    ΔU_i=d_i ΔW_i,
    (U_i*,W_i*)=(U_i+ΔU_i,W_i+ΔW_i).                (T11)

The denominator is positive: at least one positive hazard belongs to
another player. The A-date Continue equation is increased by d_iΔW_i;
the b-date Continue equation is increased by e_i/(1+X_b)+d_bΔU_i.
These are exactly the two increments in(T11). This is a payoff correction,
not silent equality of an inactive nominal Continue row. Forced Quit
endpoints do not depend on continuation; the active-date one equals U_i,
so it is≤U_i* in either case, with equality when q_i>0.

For every i∈A the corrected passive-date policy equation is exactly

    W_i*=(U_i*+X_b r_i({b}))/(1+X_b).

Under(T2b) its Quit endpoint is≤s_i≤W_i≤W_i*. Under(T2c), P_i/D_i≥0
and the correction is nonnegative, hence U_i*≥U_i≥s_i. Therefore

    (s_i+X_b r_i({i,b}))/(1+X_b)
      ≤(U_i*+X_b r_i({b}))/(1+X_b)=W_i*.

Thus both alternatives give the same full passive endpoint inequality,
including every inactive boundary. No comparison with an uncorrected
inactive Continue payoff is used.

If q_b=0, set ΔU_b=ΔW_b=e_b/(D_A−1)≥0. Here D_A>1 by nonzero
support. The solo row is a Continue transition, and the A row adds
e_b/D_A+ΔW_b/D_A=ΔW_b. Its forced Quit cap(T10) is≤s_b≤U_b*;
the solo Quit endpoint is s_b≤W_b*. If q_b>0 its residual is zero,
so no correction is needed. This exhausts every support boundary.

The prescribed profile alternates A hazards (q_0,q_1,q_2,0) and solo
b hazards (0,0,0,q_b), independently afresh after each surviving live
date. Every coordinate of the corrected U*,W* satisfies the actual
policy expectation equation. Overall period survival is
ρ=∏[i∈I](1−q_i)<1, so bounded policy-equation solutions are unique:
iterate a full period, and the residual vanishes as ρ^n. Therefore these
vectors are the profile's actual terminal continuation payoffs. In
particular they lie in the coordinate reward bound, even with signed s.

For a complete deviator i, opponents' period survival is
ρ_i=∏[j≠i](1−q_j)<1. Conditional on any surviving live history their
private fresh coins still have exactly those scheduled hazards. No own
strategy can raise the probability that all opponents survive n periods
above ρ_i^n. The two endpoint inequalities consequently telescope along
every actual behavioral reply; its terminal payoff is≤U_i*. The tail
error is bounded by 2Mρ_i^n when |r_i(S)|≤M. This includes arbitrary
late quitting, Never, private memories and off-prescription unilateral
histories. Neither public correlation nor a bounded controller is assumed.

For τ the first quitting date, uniformly over all unilateral replies,
E[τ+1]≤2/(1−ρ_i). Put B=2/min[i∈I](1−ρ_i)<∞. With the stated
initial-zero horizon convention,
the payoff coefficient for absorption at τ is (N−τ−1)_+/N. Thus the
terminal-versus-N-average discrepancy is≤MB/N for both the profile and
every reply. Its payoff is within MB/N of the FIXED target U*, and its
N-average unilateral Nash error is≤2MB/N. The target and one profile
precede ε and work for all large N. No accuracy-varying target is selected.

Finally, under hypothetical original no UE the cited source forces R0
and degree one. The complete construction just given supplies a fixed
uniform target, contradiction. This proves raw UE existence under(T2a),
the per-player(T2b)/(T2c) disjunctions, and(T3).

### A fresh complete strict table

Here all own singleton levels are1. Entries are in player order0,1,2,3:

| S | r(S) |
|---|---|
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (5,5,1,1) |
| 02 | (1/2,1,1/2,1) |
| 03 | (1/2,3,3,−1) |
| 12 | (1,1/2,1/2,1) |
| 13 | (3,1/2,3,−1) |
| 23 | (3,3,0,0) |
| 012 | (2,2,2,1) |
| 013 | (13,−7,3,11/15) |
| 023 | (−7,3,4,13/15) |
| 123 | (3,13,−7,13/15) |
| 0123 | (2,2,2,21/20) |

The A pair joining coefficients are c_01=c_10=1 and the other four
c_ij=1/2. All c_iA=1. Formula(T1) gives M=(4,4,1), B=(4,4,3)
and R=(4,4,8). The solo premium a=1/20 is strictly positive.
For the passive singleton row, the three caps are strict (1/2,1/2,0)<1.
The seven nonempty vertex values of C_b are

| S | C_b(v^S) |
|---|---|
| 0 | −8 |
| 1 | −8 |
| 2 | −8 |
| 01 | −304/15 |
| 02 | −304/15 |
| 12 | −304/15 |
| 012 | −152/5 |

Thus every inequality has strict slack at this center.

For a strict enlargement of the raw scope, change only r_b(013) from
11/15 to11/10. Its triple coefficient is now1/10>0. The single vertices
and the02/12 vertices are unchanged; the01 vertex is−72/5 and the full
vertex is−368/15, both strictly negative. This altered table satisfies
the theorem while violating the sufficient coefficientwise subclass.
The full actual-source separation below is asserted for the original
sixty-coordinate table, not automatically transferred to this alteration.

The passive-cap disjunction also strictly enlarges the raw scope. From the
original table change only r₂(02),r₂(12) to1 and r₂(23) to2. Then
Π₂,02=Π₂,12=0, Π₂,A=1 and r₂(23)=2≤r₂(3)=4, so player2 satisfies(T2c)
but violates(T2b). The other two players retain(T2b). The new radii are
(3,3,8), whose box is contained in the original(4,4,8) box; the unchanged
anchor polynomial remains nonpositive there by the already verified vertex
test. All pair joins remain positive and the three triple joins remain1.
This is a complete raw-scope stress, not a second source-separation claim.

Its Γ is the favorable matching H=3 matrix, with off-diagonal favorable
entries3 at01/10/23/32 and all others−1. Every principal matrix with
support size2,3 or4 is nonsingular (determinants−9 or−1,6,45 respectively).
Each column has a negative entry, excluding singleton homogeneous roots;
hence Γ is R0. For the explicit residual ΓX−1, the only complementary
solution is X=1 with
full support: favorite-pair roots have negative inactive residuals,
harmful-pair roots are negative, and every triple solution has negative
coordinates. Its active determinant45 is positive, so degree is one.
The tracked convention is offset+ΓX, so this is offset−1, not offset+1.
`isStandardQ_of_r0Degree_ne_zero` therefore gives standard Q as well.
The inverse is the strict positive matching inverse with rows
(2,7,3,3)/15, (7,2,3,3)/15, (3,3,2,7)/15, (3,3,7,2)/15.
Thus the example does not leave the actual no-UE singleton source merely
by violating Q, R0 or degree one.

### Every concrete large-base screen fails

Take free=I−E. The following table gives the COMPLETE Nash carrier of
each induced free game: there is exactly the listed point. Its member
gaps are Quit-minus-Continue, in increasing base order.

| E | Free order | Unique free hazards | Base member gaps |
|---|---|---|---|
| 01 | 2,3 | (16/19,1/2) | (33/38,−27/38) |
| 02 | 1,3 | (8/11,1/2) | (−57/44,9/44) |
| 03 | 1,2 | (0,1) | (−10,−2/15) |
| 12 | 0,3 | (8/11,1/2) | (63/44,−57/44) |
| 13 | 0,2 | (1,0) | (−10,−4/15) |
| 23 | 0,1 | (0,1) | (−10,−2/15) |
| 012 | 3 | (1) | (−1,−1,−1) |
| 013 | 2 | (0) | (10,−10,−4/15) |
| 023 | 1 | (0) | (−10,1,−2/15) |
| 123 | 0 | (0) | (10,−10,−2/15) |
| I | none | () | (−1,−1,−1,1/20) |

Completeness is elementary, not numerical: in each A-pair free game,
the child joining gap is1−2q_b; b's gap changes from−4/15 or−2/15
to1/20 as the child quits. This is a strict matching-pennies square,
so both hazards are proper and the displayed zero equations are unique.
For bases containing b, each one-free game has a strictly signed gap.
On base03 the free1 gap is−10+9q₂<0, forcing q₁=0, and then the free2
gap1−2q₁ forces q₂=1. On base13 the free2 gap is−10+9q₀<0,
forcing q₂=0, and the free0 gap10−11q₂ forces q₀=1. On base23 the
free0 gap is−10+9q₁<0, forcing q₀=0, and the free1 gap10−11q₀
forces q₁=1. Thus these are complete strict-dominance calculations,
not a sampled root census. Direct substitution gives all listed gaps.

`quittingPersistentLargeBaseExcess_nonpos_iff` and
`exists_uniformPayoff_or_persistentLargeBase_pos_gap` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`
therefore cannot output this table through their nonpositive-screen arm.
Choosing fewer free players cannot help: a successful outsider-join screen
would extend that point by zero hazards to a Nash point of the full free
game, which has already been exhausted here.

### All four singleton punishment screens fail, with exact completeness

Write G_j for a free player's induced Quit-minus-Continue difference.
With anchor0 and free order1,2,3 these are

    G₁=1−11q₃+9q₂q₃,
    2G₂=1+q₁+q₃−5q₁q₃,
    G₃=−1+(11/15)q₁+(13/15)q₂−(11/20)q₁q₂.

The boundary q₃=0 forces q₁=q₂=1 and then G₃>0; q₃=1 forces
q₁=0,q₂=1 and then G₃<0. Thus q₃ is proper. G₃=0 forces
q₁,q₂>0. If q₁=1 and q₂ is proper, G₂=0 gives q₃=1/2 and
G₁<0. If both q₁,q₂ are proper, G₂=0 with q₁<1 forces q₃>1/2,
while G₁=0 with q₂<1 forces q₃<1/2. Therefore q₂=1,
q₃=1/2, and G₃=0 gives q₁=8/11. It is the unique Nash point.

For anchor1 and free order0,2,3,

    G₀=1+9q₃−11q₂q₃,
    2G₂=1+q₀−21q₃+17q₀q₃,
    G₃=−1+(11/15)q₀+(13/15)q₂−(11/20)q₀q₂.

Again q₃ is proper and q₀,q₂>0. If q₀ is proper, G₀=0 gives
q₃>1/2 unless q₂=1; but G₂=0 with q₂ proper requires q₃<1/2.
If q₂=1 then q₃=1/2 and G₂<0 for q₀<1. Hence q₀=1,
q₃=1/2 and q₂=16/19 uniquely. The endpoint signs verify it.

For anchor2 and free order0,1,3,

    2G₀=1+q₁−21q₃+17q₁q₃,
    2G₁=1+q₀+19q₃−23q₀q₃,
    G₃=−4+(58/15)(q₀+q₁)−(221/60)q₀q₁.

The same boundary check forces q₃ proper and q₀,q₁>0. Both proper
would force q₃<1/2 from G₀=0 and q₃>1/2 from G₁=0.
If q₀=1 and q₁ proper, q₃=1/2 makes G₀<0. Thus q₁=1,
q₃=1/2 and q₀=8/11 uniquely. These three anchors have a sure free
player, so their owner-floor excess is independent of the punishment tail:
it is respectively57/44,27/38,57/44>0 by the preceding large-base table.

For anchor3 and free order0,1,2 the free differences are

    2G₀=1+19q₁−21q₂−q₁q₂,
    2G₁=1−21q₀+19q₂−q₀q₂,
    G₂=−4+5q₀−6q₁+4q₀q₁.

There is exactly one Nash point, (4/5,0,1/21). To prove completeness,
suppose q₁>0. Then q₂=0 would force q₀=1 and G₁<0; q₀=0 would
make G₂<0, hence q₂=0, also impossible. q₀=1 makes G₁<0,
q₂=1 makes G₀<0 and then G₂<0, and q₁=1 makes G₂≤−1.
Thus all three would be proper. Put T(t)=(1+19t)/(21+t). The first
two zero equations imply q₂=T(q₁), q₀=T(q₂). T is increasing with
its sole unit-interval fixed point α=√2−1. If q₁≤α, then q₀≤α
and G₂≤−4+5α<0. If q₁≥α, then q₀≤q₂≤q₁, so
G₂≤−4−q₀+4q₀²≤−1. Both contradict G₂=0. Therefore q₁=0.
The remaining two response equations rule out all boundaries and give
q₀=4/5,q₂=1/21. At that point G₁=−112/15<0.

At this last free Nash law, player3's zero-tail Quit-minus-Continue
difference is−968/1575. All of player3's PASSIVE rewards are nonnegative;
Never guarantees at least0 against every complete opponent plan. Hence
P₃=quittingPunishmentValue reward3≥0. Its actual floor excess is

    968/1575+(4/21)P₃≥968/1575>0.                    (T12)

This is an exact punishment-priced failure, not substitution of stationary
Never for punishment. Thus `exists_uniformPayoff_or_singletonBase_pos_gap`
and `quittingSingletonBaseOwnerFloorExcess` in the same concrete source
cannot consume any of the four singleton bases. Free-subset alternatives
again embed into the exhausted complete free carrier.

### Major phase, core and matrix comparisons

Every two-pair partition contains a cross pair {b,j}. Its b joining gap
is−1,−1 or−4 for j=0,1,2, respectively. Thus every partition fails
the unrestricted complementary-pair raw joining criterion c_i≥0.
For the strict favorable-matching criteria, either harmful matching has
a b participant premium−2 below its harmful singleton comparison−1.
The positive-inverse general criterion requires nonnegative participant
premiums and fails at b on every word. For any signed-inverse cone word,
Γ⁻¹diag(σ)>0 forces σ=(1,1,1,1), while σ_bΠ_b≥0 fails.

The opposite-sign matching architecture requires scheduled pairs to be
harmful singleton pairs, and one scheduled pair must have both joining
coefficients negative. Under either harmful matching, one pair lies
inside A and has both joining coefficients positive; the pair containing b
has opposite signs. Thus no harmful scheduled pair has both coefficients
negative, under any relabeling preserving the singleton signs. The pair23
does have both coefficients−4, but it is the favorable singleton pair and
cannot be the required harmful scheduled pair. Any proper two-pair profile
in which every phase
value is below its own singleton is also impossible: its within-A pair
has W_i=s_i+c_ijX_j>s_i for each A member. This excludes the accepted
below-singleton family and its actual below-floor local branch, without
guessing a neighborhood radius.

The favorable singleton graph is the two disjoint2-cycles, so no cyclic
ordering of three or four distinct players has its required positive
singleton edges. It excludes the actual `CyclicChildJointPhase.RawTable`
in `UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSource.lean`
and the signed four-cycle raw producers. The cyclic-child matrix/passive
exit has the same missing directed3-cycle. Independently every deleted
triple inverse has a negative diagonal entry, excluding the relevant
nonnegative-child-inverse dispatch. These are raw source failures, not
exclusions of arbitrary supplied Bellman certificates.

`PairedCycle.RawRegion.eq_partner_of_singleton_lt` in
`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean` permits only
one below-own singleton in each recipient row; this table has two.
The pure A hazard profile also has every active forced-Quit payoff above
own: it gives2 to each A member. It directly violates
`HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`,
independently of the tail annotation.

The grand coalition is a premium trap (all four participant premiums are
strictly positive), so the greatest premium core is I, not a pair or triple.
Joining-attractive and mixed-sign triple-CORE results do not consume it.
The trap A is joining-attractive with every within-A nonempty joining gap
strictly positive. Thus its proper-subset leave sums are positive for all
positive weights, excluding weighted leave and boxed-charge tests there.
More directly every player's cross-pair participant reward is below own,
so the maximal protected set is empty. `HasSupportSpecificQuittingLeavers`
cannot supply a protected leaver for the nonempty trap A.

The literal triple-core condition in
`exists_uniformEquilibriumPayoff_of_weakJoiningAttractive_core`
(`UniformEquilibrium/Quitting/Classification/Existence/JoiningAttractiveCoreRewardClosure.lean`)
is card(core)=3, not the existence of some joining-attractive triple trap.
The full-core distinction here is
therefore a genuine input difference, not reliance on its headline name.

The stationary guard sources fail as well. For each ordered(owner,passive),
a pure opponent coalition T containing owner with positive passive joining
gain is, in ordered pairs01,02,03,10,12,13,20,21,23,30,31,32,

    T=(0,0,012,1,1,012,2,2,012,13,23,03),
    gain=(1,1/2,1/20,1,1/2,1/20,1/2,1/2,1/20,10,10,1).

With a sure opponent, the actual zero-discount stationary displacement
is that literal joining gain. Every upper face in
`QuittingOneSidedWeakUnitGuards` therefore fails; the structure and its raw
companion are in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.
For the two-sided half-polynomial source,
`QuittingHalfWeakPolynomialGuards.reciprocal_pos` in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`
forces the selected reciprocal singleton pair to be01 or23, using the
literal nonnegative full inverse. For01, recipient1 with partner0 hazard
1/2 and outsiders2,3 sure has upper-face displacement(10−1)/2=9/2>0.
For23, recipient2 with partner3 hazard1/2, outsider0 sure and outsider1
Never has displacement(1/2+1)/2=3/4>0. Thus both polynomial upper-face
families fail, under every relabeling; their stronger finite raw subclasses
fail too. This does not exclude every stationary all-proper Nash profile.

For `HasGlobalQuittingWeightedFloor` the coalition{b} has inserted
premiums(−1/2,−1/2,−1,0), forcing weights0,1,2 to vanish. Coalition{0}
then has player3 inserted premium−2, forcing its weight to vanish too.
No positive trap-weight vector exists. The exact definitions
are `HasProtectedParticipantPremiums`/`HasSupportSpecificQuittingLeavers`
in `UniformEquilibrium/Quitting/Classification/SupportSpecificQuittingPremiumLeavers.lean`,
`HasWeightedQuittingTrapLeavers` in
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`,
and `QuittingTrapChargeCoefficients` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`.
These are raw structural hypotheses of their weak existence consumers,
not arbitrary supplied Bellman or stationary certificates.

### A small structural fourteen-child check

For proper nonempty child S use a pure child coalition T and omitted k:

| S | T | k | Omitted joining gain |
|---|---|---|---|
| 0 | 0 | 1 | 1 |
| 1 | 1 | 0 | 1 |
| 2 | 2 | 0 | 1/2 |
| 3 | 3 | 0 | 1/2 |
| 01 | 01 | 2 | 1 |
| 02 | 02 | 1 | 1 |
| 03 | 0 | 1 | 1 |
| 12 | 12 | 0 | 1 |
| 13 | 1 | 0 | 1 |
| 23 | 3 | 0 | 1/2 |
| 012 | 012 | 3 | 1/20 |
| 013 | 01 | 2 | 1 |
| 023 | 02 | 1 | 1 |
| 123 | 12 | 0 | 1 |

Members of nonsingleton T have strictly positive withdrawal gaps; child
nonmembers have strictly negative joining gaps. Singleton owners have
own1 and child opponents Never. Thus each child profile is exact terminal
Nash, has zero child debt, and has zero Never mass. Every advance joining
margin is≤0 and every withdrawal margin is≤0 at this T, including all
five actual restart-floor operations (their singleton floors are≤own1).
The strictly positive omitted J row defeats both universal child-debt
extensions and all five `WithdrawalFutureJoinRewardCertificate` kinds
in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`.
This is a structural extra screen, not a replacement for the concrete-base
audit above. It does not exclude arbitrary selected-child continuations.

### An open raw neighborhood, without assuming a common Nash witness

Every theorem hypothesis at the displayed table is strict and is continuous
in all sixty reward coordinates: c denominators stay positive, and maxima
and finite minima in(T1) are continuous. The full core remains I, and the
strict trap A, empty protected set and zero weighted-floor tests persist.
The negative cross-pair joining gaps persist as well.

Each finite free-game Nash carrier is nonempty and compact. Under convergent
reward tables, any convergent sequence of its Nash points is Nash for the
limit table, by continuity of the finite endpoint inequalities. Every
center carrier just proved is a singleton, and its concrete excess is
strictly positive. The actual punishment value is 1-Lipschitz in the
coordinate reward sup norm: each terminal payoff changes by at most that
norm for every complete profile, and infimum/supremum preserve the bound.
If arbitrarily close tables had a nonpositive concrete screen, choose its
Nash point and a convergent hazard subsequence; the limiting screen would
contradict the displayed strict center excess. This proves one full
sixty-coordinate open neighborhood failing every concrete screen, while
remaining in the buffered triple–singleton existence class. Neither a
common product witness nor correlated play nor an unspecified IFT oracle
is used. The producer is the same raw theorem on every nearby table.

Scope: this is a raw UE completion theorem and an explicit actual-source
separator, with a full open neighborhood. It asserts no all-table Fin4
solution, stationary strategy-class completeness, properness of all odds,
quantified exclusion of arbitrary local-center families or Lean
implementation. Existence of a stationary Nash root for an individual
table would not establish inclusion in an older raw-table producer.

Signed stress for the R0/degree-one branch: translate every terminal
coordinate in player row i by any constant d_i. All quantities Γ,Π,c,M,B,R
and(T2a)–(T3), including the per-player alternatives, remain unchanged,
so the same odds root works. The profile and every unilateral reply
against its fixed opponents absorbs almost surely, giving actual values
(U_i*+d_i,W_i*+d_i). Thus arbitrary signed own levels, including all
s_i=−1 obtained by d_i=−2, are retained. This is not a claim that
source-failure certificates transfer through arbitrary Never-preserving
affine transformations. Independently r_b(01),r_b(02),r_b(12),r_b(A)
may be replaced by any four signed numbers: they change(T6), but not the
raw criterion or its feasible-odds bound. Their existence proof is the
global degree argument, not a supplied fixed root. The fixture's separate
source census is not transferred to those arbitrary completions.

### Strategic inputs and Lean handoff

No strategic object is an input of the raw theorem. The singleton matrix
is computed from r. Under hypothetical no UE, the named original-game
criterion produces its R0/degree-one certificate. The nonlinear degree
argument then produces X, rather than assuming it. The hazards, inactive
corrections, profile, terminal target and one common unilateral tail bound
are all explicit functions of that produced X and the raw table. No child
equilibrium, punishment strategy, correlated terminal law or externally
selected response is used in this construction. Punishment values occur
only in the independent implemented-source coverage comparison.

A narrow formalization can separate the following declarations:

- A raw `TripleSingletonCollisionBox` predicate containing(T1), the six
  strict pair joins, three weak triple joins, the per-player passive-cap
  alternatives and the seven vertex inequalities. It should contain no
  root, strategy, payoff or equilibrium field.
- A nonlinear complementarity producer under `IsR0Matrix Γ` and
  `r0Degree Γ hR0=1`, returning finite X≥0 with e≥0, X_i e_i=0, the
  bounds X_j≤R_j and at least two positive coordinates. The new content
  is(T4)–(T9), compact feasible-odds isolation and local/global degree
  separation; the named ambient-degree declarations supply the topological
  library interface, not the nonlinear root itself.
- A date-parity behavioral profile built from q_i=X_i/(1+X_i), with the
  corrected actual continuation vectors. Prove the unrestricted terminal
  statement in the existing semantic form
  `(quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0 profile`.
  The new consumer is the full endpoint-and-deleted-clock argument here,
  including inactive coordinates; a supplied stationary-root verifier is
  not its substitute.
- The direct same-profile bound2MB/N and delivery boundMB/N, followed by
  the theorem shape
  `∃ payoff, (quittingGame reward).IsUniformEquilibriumPayoff none payoff`.
  Compose it with
  `finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` for unconditional
  raw-class existence. Do not make R0 or the strategic root an assumed
  field of that final raw theorem.

The current result is ordinary mathematics, not a claim that these suggested
declarations already exist or that the new producer has been checked in Lean.
