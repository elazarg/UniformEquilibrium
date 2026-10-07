# Nonlinear phase escape and the missing semantic boundary dispatch

Identity: CODEX_NOETHER. Ordinary mathematics, not checked in Lean here.

Status: the explicit unbounded regularized-root family below is proved.
It falsifies a tempting global compactness implication, not UE existence.
The displayed escape table is itself covered by a pure-pair equilibrium.
Two nonnegative triple-join rows already give a complete bounded producer
under the additional raw sign and passive-cap conditions at the end.
The actual singleton punishment source also consumes the one-coordinate
escape mode under the explicitly stated cylinder cap; multi-coordinate
escapes remain open.
The live question is whether actual no-UE concrete-base gaps exclude or
consume EVERY escape mode, instead of assuming one more reward sign.
No export or conjecture-facing increment is claimed here.

## Finite question

Four players use private independent Continue/Quit coins and observe the
public past. The first nonempty quitting coalition absorbs; the live and
absorption-selecting date pay zero, subsequent dates pay its finite signed
reward vector, and Never pays zero. Unilateral deviations are unrestricted
complete behavioral replacements. Put A={0,1,2}, b=3 and consider two
calendar rows: joint A, then solo b.

The buffered triple–singleton candidate is recorded in
`notes/CODEX_NOETHER__MATCHING_JOINT_PRODUCER_FALSIFICATION.md`, section
“A buffered triple–singleton producer beyond the concrete-base screens”.
Its root producer uses strict six pair joins and weak three triple joins
inside A to bound every feasible nonnegative odds vector. That frozen
candidate is not being modified here. This note asks what survives if
the triple joins can be negative while the six pair joins stay positive.

The question is GLOBAL and semantic: given the actual R0/degree-one
singleton source and all concrete persistent-base gaps supplied by original
no UE, can every unbounded regularized phase branch be dispatched to a
genuine UE continuation or contradicted? A bounded supplied root is not
the desired conclusion. A positive answer would have to preserve the
actual payoff cap and all-coordinate target, not merely a limiting hazard.

## Source interfaces inspected

- `finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff`, in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`,
  supplies full original singleton R0 and degree one without a strategic
  premise.
- `ambientDegree_homotopy`, in
  `MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`, requires one
  bounded region whose frontier avoids zeros for the entire homotopy.
  R0 is not a substitute for that common nonlinear isolation hypothesis.
- `exists_uniformPayoff_or_singletonBase_pos_gap` and
  `exists_uniformPayoff_or_persistentLargeBase_pos_gap`, in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`,
  supply the actual induced-Nash compact gaps under no UE. The singleton
  tail is the real punishment value, not stationary Never.

These declarations and the definitions used below were inspected in
place. The conjectural semantic boundary dispatch is not an implemented
consequence of these interfaces.

## Complete escape table

The singleton comparison matrix is the matching H=3 matrix: favorable
entries3 at01,10,23,32 and all other off-diagonal entries−1. All own
singletons are1. Its principal support determinants are−9 or−1 for
pairs,6 for triples,45 for the full matrix; each singleton column has a
negative entry. Thus Γ is R0. Its only solution at positive offset1 is
the full-support vector1 with positive determinant45, giving degree one
and hence standard Q by `isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean`.

The full reward table is:

| S | r(S), in player order0,1,2,3 |
|---|---|
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (5,5,3,1) |
| 02 | (1/2,3,1/2,1) |
| 03 | (1/2,3,3,−1) |
| 12 | (3,1/2,1/2,1) |
| 13 | (3,1/2,3,−1) |
| 23 | (3,3,0,0) |
| 012 | (2,2,2,2) |
| 013 | (13,−7,3,11/15) |
| 023 | (−7,3,4,13/15) |
| 123 | (3,13,−7,13/15) |
| I | (2,2,2,21/20) |

The six within-A pair joins remain c_01=c_10=1 and all four others1/2.
But all three triple joins are c_iA=−1. Every other finite inequality of
the buffered candidate remains true: M=(4,4,1), B=(4,4,3), R=(4,4,8),
three passive solo caps, three anchor pair caps, and the three strictly
buffered triple caps with a=1/20. The anchor's four passive A rewards
are not among those hypotheses; r_b(A)=2 is permitted signed data.

## An unbounded family of actual regularized zeros

For i∈A write A−i={j,k} and define

    D_i=(1+X_j)(1+X_k),
    P_i=Π_ijX_j+Π_ikX_k+Π_iA X_jX_k,
    L_i=c_ijX_j+c_ikX_k+c_iA X_jX_k,
    e_i=Γ_ibX_b−(1+X_b)L_i+P_i/D_i.

For b the residual is the full passive A polynomial

    e_b=Σ[j∈A]Γ_bjX_j
      +Σ[{j,k}⊆A](r_b({j,k})−s_b)X_jX_k
      +(r_b(A)−s_b)X_0X_1X_2.

These are exactly ΓX−N(X), with N(X)=O(‖X‖²) at zero. Extend N by
positive part and set H_λ(x)=min(x,Γx−N(x⁺)−λ·1), λ≥0.

On X=(x,x,y,0) the first two residuals coincide and

    e₀=e₁=−x−y/2+xy+(4x−y/2+xy)/[(1+x)(1+y)],
    e₂=x²−x+(x²−x)/(1+x)²,
    e_b=x²y−2x+3y.                                  (E1)

Fix any x>2. At y=x,

    e₀−e₂=−x(x−2)(x+4)/[2(x+1)²]<0.

At y=x+1,

    e₀−e₂=(x⁴+3x³+10x²+9x−3)/[2(x+1)²(x+2)]>0.

Also

    ∂e₀/∂y=x−1/2−(3x+1/2)/[(1+x)(1+y)²]>0

for x≥2 and y≥x: the fraction is<1/3 and x−1/2≥3/2.
Therefore there is a unique y(x)∈(x,x+1) with e₀=e₂.
Put λ(x)=e₂(x)>0. Since y>x,

    e_b>x³+x>λ(x),      λ(x)<x²,      λ(x)→∞.

Consequently X(x)=(x,x,y(x),0) is an EXACT zero of H_{λ(x)}:
the three positive A coordinates have residual exactly λ(x), and the
zero b coordinate has residual strictly larger than λ(x). These zeros
escape every bounded region. This is not merely an unbounded feasible
ray or numerical sequence.

The minimal false implication is now explicit:

    singleton R0/degree1 + positive pair joins + finite collision buffers
    ⇒ one bounded isolating region for every H_λ, λ≥0.

The three nonnegative triple joins are genuinely doing load-bearing work
in the buffered producer. Local R0 isolation at the origin still holds;
the global shift homotopy loses uniform compactness. No conclusion about
absence of a nonlinear root at λ=0 follows from this escape family.

## Why this is not a surviving UE table

Coalition01 is a pure terminal equilibrium. Members0,1 have joining
differences5−4=1. Player2's joining difference at01 is2−3=−1, and
player3's is11/15−1=−4/15. Hence no outsider joins and no member
withdraws. At least two sure quitters make every unilateral deviation
absorb at date0 against a remaining sure opponent; its entire strategy
reduces to the two initial endpoints. Thus this is exact terminal Nash,
and one fixed uniform target is r(01)=(5,5,3,1).

It is covered both by `isUniformEquilibriumPayoff_setReward_of_pureSetNash`
in `UniformEquilibrium/Quitting/Root/PureSetNashSureExit.lean` and by the
actual concrete persistent-base screen at E=01. The escape family is
therefore an internal guardrail, not additional UE counterexample-class
narrowing. It cannot be promoted by calling its regularized roots a
residual source.

## Concrete next question

The natural stronger hypothesis is the actual semantic one: EVERY
concrete persistent-base screen remains strictly positive on its full
induced Nash carrier. Does that force all unbounded H_λ branches into a
different limit configuration, or does it furnish a genuine boundary
consumer even when the phase residual itself is unbounded?

The present example cannot answer that question because its pure01 source
already wins. One must derive the limiting free-player Nash law and the
owner punishment floor from the escaping branch itself; simply taking
q_i→1 sends A to a coalition with negative joining differences and is
not such an adapter. The regularization λ→∞ changes the Bellman
equations, so it supplies neither actual policy values nor a strategy.
Any argument overlooking this distinction would repeat the earlier
mistake of confusing an analytic object with a consumed equilibrium.

## Removing the easy pure exit still does not defeat the actual source

Modify only the three passive anchor pair coordinates of the displayed
escape table:

    r_b(01)=r_b(02)=r_b(12)=−1.

The pure01 exit is no longer Nash: the anchor's joining gain is now
11/15−(−1)=26/15>0. The six pair joins, three negative triple joins,
and the three residuals e₀,e₁,e₂ are unchanged. The anchor residual becomes

    e_b=x²y−2(x²+2xy)−2x+3y.

For x≥8 and y∈(x,x+1), this is greater than

    x³−6x²−3x>x²>λ(x).

Thus the same exact shifted roots still escape. Removing the convenient
pure equilibrium has not repaired the global isolation implication.

Nevertheless the ACTUAL singleton0 source consumes this modified table.
Take the induced free-player product probabilities, in order1,2,3,

    μ=(15/41,0,1/11).

At this point the free joining gaps of players1 and3 are exactly zero;
player2's gap is −9/451<0. Hence μ is a genuine induced finite Nash law,
not a correlated law or a numerical root. The owner's zero-tail
Continue-to-Quit gap and the empty-free probability are

    E g₀=573/451,       p_empty=260/451.

The actual punishment value obeys P₀≤1/2: opponents can make player2 quit
at date0, leaving owner0 the two endpoints r₀(02)=1/2 and r₀(2)=0.
This is the direct unilateral-cap bound used by
`quittingPunishmentValue_le_stationaryUnilateralCap` in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean`.
Consequently the literal concrete-source owner floor excess is

    −573/451+(260/451)P₀≤−443/451<0.

There are no outsiders when free=I−{0}. The free components vanish by
the induced Nash property, so
`exists_uniformPayoff_or_singletonBase_pos_gap` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`
forces a uniform equilibrium payoff. This is not an all-Nash census:
one exact favorable point of the actual source already suffices.

The guardrail is sharper than a pure-exit observation. An unbounded
analytic branch can survive both the loss of the triple sign and the
removal of its first easy boundary equilibrium, yet another real
punishment-tail consumer still closes the table. No separation from all
concrete-base screens is claimed. The global question above remains open.

## Two good triple rows suffice: a structural producer extension

This is a complete ordinary-mathematics extension of the compactness and
strategy argument, not an independently reviewed result or new export.
All notation, raw signed-game semantics and the fields e,H_λ are as above.
The extension is stated from raw data; it does not assume a root.

Assume all six c_ij>0 for distinct i,j∈A. Choose a raw subset G⊆A with
at least two members and require c_iA≥0 for i∈G. Require either G=A or
Γ_ib<0 for at least one i∈G. If G=A, hypothetical no UE supplies this
negative comparison from R0, as in the full buffered proof. For each
good i∈G allow either passive-cap alternative

    r_i(ib)≤s_i,

or

    Π_ij,Π_ik,Π_iA≥0 and r_i(ib)≤r_i(b).

Every bad i∈A−G must satisfy the second alternative. Its triple joining
difference c_iA may be negative. Define the radii using only the good rows:

    R_j=min[i∈G−{j}] B_i/c_ij,
    B_i=max(0,Γ_ib,M_i),
    M_i=max(0,Π_ij,Π_ik,Π_iA).

Each minimizing set is nonempty because |G|≥2. Finally assume the seven
nonempty box-vertex inequalities C_b(R·1_S)≤0, S⊆A, where

    C_b(X)=Σ_j(r_b(bj)−s_b)X_j
      +Σ_{j<k}(r_b(bjk)−s_b)X_jX_k
      +(r_b(I)−s_b)X_0X_1X_2.

Conclusion: every such raw table has a uniform equilibrium payoff. In the
R0/degree-one branch it has the same explicitly produced period-two
terminal Nash and fixed-target/all-large-horizon conclusion. No particular
sign is imposed on the remaining rewards or singleton levels.

Proof of global isolation: for every X≥0 with e(X)≥0 and every i∈G,
L_i≥0 and P_i/D_i≤M_i. Therefore

    L_i≤B_i,       X_j≤B_i/c_ij for j≠i.

The good rows together bound all X_j, j∈A, by the displayed R_j. A good
row with Γ_ib<0 also gives X_b≤M_i/(−Γ_ib). The same compact set
contains every zero of every shifted H_λ. All the local R0/degree-one,
global degree-zero and nonzero/singleton-support exclusion arguments are
literally unchanged. In particular the support proof uses c_ij>0 but
does not use the signs of c_iA, since the quadratic triple term vanishes
on singleton support. Thus the internally produced finite root has at
least two positive odds.

Proof of strategic cap for a bad row: the algebraic active identity
W_i=s_i+L_i remains valid when L_i is negative. The residual e_i and
inactive correction are unchanged. Since the three Π coefficients are
nonnegative, U_i≥s_i, hence U_i*≥s_i. The exact corrected policy equation
is W_i*=(U_i*+X_b r_i(b))/(1+X_b), and so

    Q_i^b=(s_i+X_b r_i(ib))/(1+X_b)≤W_i*.

For a good row using the first alternative, W_i*≥W_i≥s_i gives the old
cap; for a good row using the second, the displayed argument applies.
The multiaffine vertex test gives b's actual passive cap on the produced
box. Every other policy equation, active endpoint inequality and inactive
correction remains valid. Bounded corrected values are uniquely the actual
policy payoffs by period survival<1. Opponent survival<1 follows from the
two-positive-support conclusion, so the full behavioral telescoping and
direct horizon bounds apply unchanged. This supplies the complete consumer,
not merely a local nonlinear root.

A complete raw-scope stress is obtained from the strict sixty-coordinate
table of the buffered candidate by changing only

    r₂(01)=3,      r₂(02)=r₂(12)=1,      r₂(23)=2.

All other coordinates stay exactly those displayed there. Then G={0,1}
has c₀A=c₁A=1, Γ₀b=Γ₁b=−1, while c₂A=2−3=−1. The six pair joins
remain positive. The bad row2 has Π₂,02=Π₂,12=0, Π₂,A=1 and
r₂(23)=2≤r₂(3)=4. The good-row radii are(4,4,8), so the strict anchor
vertex values are unchanged. This table satisfies the new raw producer
but violates the all-three-nonnegative-triple condition. This is a raw-scope
test only: no inherited assertion about all concrete-base screens is made
for the modified table. The original strict table still belongs to this
stronger family and retains its separately proved source separation.

The extension shows precisely where the symmetric escape uses more than
one bad row. It does not prove that actual all-base gaps supply a suitable
G, and it does not settle escapes with fewer than two good rows or with
only bad rows having negative Γ_ib. Those are still the global question.

## A real singleton-source consumer for one-coordinate escape

The following semantic boundary lemma is proved in ordinary mathematics.
It is internal, not independently reviewed. Unlike the two-good-row bound,
it uses the actual concrete-base screen to consume an unbounded shifted
root branch. It does not consume arbitrary multicoordinate escapes.

Relabel the good owner as0. Assume all six c_ij>0, c₀A≥0 and Γ₀b<0.
Put M=M₀, R₁=M/c₀₁ and R₂=M/c₀₂. A shifted zero has

    X₁≤R₁,       X₂≤R₂,       X_b≤M/(−Γ₀b),       0≤λ≤M.  (B1)

Indeed e₀≥λ≥0 and L₀≥0 give all three coordinate bounds as before;
also e₀=Γ₀bX_b−(1+X_b)L₀+P₀/D₀≤M. No condition on c₁A or c₂A
is used. Thus the only potentially unbounded coordinate is X₀.

Write d_j=r_b(bj)−s_b and d_jk=r_b(bjk)−s_b, and split the anchor's
passive Quit polynomial into its constant and X₀ parts:

    C_b(X)=C⁰(X₁,X₂)+X₀ C¹(X₁,X₂),
    C⁰=d₁X₁+d₂X₂+d₁₂X₁X₂,
    C¹=d₀+d₀₁X₁+d₀₂X₂+aX₁X₂.

Assume the three nonempty vertex values of C⁰ on[0,R₁]×[0,R₂] are≤0,
and all four vertex values of C¹ are≤0. Bilinear interpolation gives

    C_b(X)≤0 whenever X₀≥0, X₁∈[0,R₁], X₂∈[0,R₂].   (B2)

These are seven finite raw tests on a cylinder, not an unspecified bound
at infinity. Coincident zero-radius vertices cause no difficulty.

Boundary lemma: if Pun₀=quittingPunishmentValue reward0≤s₀ and an unbounded
sequence of zeros of H_λ exists, then the actual singleton0 concrete
persistent-base screen has a nonpositive point. Consequently the existing
original-game compiler already gives a uniform equilibrium payoff.

Proof: take a sequence Xⁿ,λ_n with H_{λ_n}(Xⁿ)=0 and X₀ⁿ→∞. By(B1),
pass to a subsequence on which X₁ⁿ,X₂ⁿ,X_bⁿ,λ_n converge to finite
limits x₁,x₂,x_b,λ. Set q_j=x_j/(1+x_j) for j=1,2. Consider the
literal induced free game at base{0}, with free probabilities(q₁,q₂,0)
for players1,2,b.

For i∈{1,2}, let k be the other element. Because P_i/D_i is uniformly
bounded and the other odds are bounded, division of the residual by X₀ⁿ
gives

    e_i(Xⁿ)/X₀ⁿ→−(1+x_b)(c_i0+c_iA x_k).

Since e_i≥λ_n≥0, c_i0+c_iA x_k≤0. If x_i>0, then X_iⁿ>0 eventually;
complementarity makes e_i=λ_n, bounded by M, and this coefficient is zero.
The free joining gap at the proposed base0 law is exactly

    (c_i0+c_iA x_k)/(1+x_k).

It is≤0 when q_i=0 and equals0 when q_i>0. Neither q_i can equal1 by
finite(B1), so this is precisely free-player Nash for players1 and2.
This argument uses the leading coefficient, not a false limit of an
unbounded nominal continuation value.

For b, its A-date Continue endpoint with nominal tail s_b is
s_b+e_b(Xⁿ)/D_A(Xⁿ)≥s_b. Its Quit endpoint is
s_b+C_b(Xⁿ)/D_A(Xⁿ)≤s_b by(B2). As X₀ⁿ→∞, the empty-A probability
vanishes and the two endpoints converge to the literal Continue/Quit
payoffs in the same finite free game with player0 sure. Therefore playerb
weakly prefers Continue at that game point. The probabilities(q₁,q₂,0)
are an actual independent induced finite Nash law for ALL three free
players, not only for the two leading residual coordinates.

For owner0, both U₀ and W₀ depend only on x₁,x₂ and remain finite.
The forced-Quit value is U₀. The algebraic active Continue endpoint with
tail W₀ equals U₀, irrespective of the shifted owner residual. Because
W₀=s₀+L₀≥s₀≥Pun₀, substituting the real punishment tail Pun₀ can only
decrease that endpoint. This is exactly

    quittingSingletonBaseOwnerFloorExcess reward0 root≤0.

There are no outsiders: free=I−{0}. Its full singleton maximum is therefore
nonpositive by `quittingSingletonBaseExcess_nonpos_iff`, and the actual
induced-Nash source theorem
`exists_uniformPayoff_or_singletonBase_pos_gap` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`
must take its UE arm. This proves the boundary lemma, including Never
through the existing punishment-tail semantic consumer. The shifted λ
equations are NOT asserted to be Bellman equations of a strategy.

Under actual no UE and Pun₀≤s₀, the source thus excludes every unbounded
zero sequence. By(B1) all λ are already bounded, so the full zero family
is bounded. Its λ>M slice is empty. Local degree one and global degree
zero now produce a nonzero H₀ root without requiring c₁A,c₂A≥0.
The same six strict pair joins exclude singleton support. This is a
genuine source-to-analytic-root adapter; its proof requires only the
actual singleton0 gap, not a conjectural implication from a renamed
positive minimum. It does not make the root into full Nash unless the
remaining passive endpoint caps are supplied.

For raw signed no-UE data, Pun₀≤s₀ need not hold on the original table.
There is an exact implemented adapter rather than a silent sign repair:
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`
produces the literal normalized table r̂_i(S)=(r_i(S)−offset_i)/s_p with
s_p>0, original no UE for r̂, and its `normal` field actual punishment≤ŝ_i
for EVERY i.
The definitions `quittingSinglePivotOffset` and
`quittingSinglePivotNormalizedReward` in
`UniformEquilibrium/Quitting/Root/SinglePivotNormalization.lean` show that
Γ,Π,c and all C coefficients scale by the same positive1/s_p, while
the radii stay unchanged. Thus(B1)–(B2) and every raw joining comparison
survive this actual source normalization. No arbitrary affine invariance
of the zero-Never game is assumed. These exact declarations and fields
were inspected for this adapter.

Adding the checked passive-cap alternatives gives a complete raw UE
corollary: owner0 may use r₀(0b)≤s₀ or its nonnegative-premium alternative;
the two other A players must have Π_ij,Π_ik,Π_iA≥0 and r_i(ib)≤r_i(b).
On the normalized actual source the boundary lemma eliminates escape,
and the root plus actual-value cap proof supplies the remaining terminal
consumer. Alternatively an escaped branch is consumed directly by the
existing singleton punishment source. This yields UE existence, not a
promise that the boundary arm has one fixed exact period-two strategy or
an accuracy-independent punishment plan.

The structural limit is still clear: this dispatch concerns one divergent
odds coordinate with a good row controlling every other coordinate. If
two or three A coordinates diverge, the nominal owner tail itself can
diverge, the other odds need not have finite limits, and this
argument does not apply. The exact symmetric escape family above remains
the unresolved multicoordinate guardrail. Nor is any new counterexample-
class increment claimed for this internal corollary without a full actual
source-overlap comparison.

Concrete next question: can a multicoordinate escape be split into an
actual finite-Nash face with admissible member gaps, or does a second
regularization select a lower-scale owner whose nominal tail remains
bounded? The available compact global positive minimum supplies an actual
semantic restriction, but no link from it to these shifted polynomial
roots has yet been proved. A rate limit alone cannot fill that link.
