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
The delayed-anchor proof below is valid, but its present passive caps
already admit the immediate singletonb source; that arm is not new UE
coverage. The actual singleton screen also supplies the negative good-row
comparison needed by the useful escape adapter.
The completed raw negative-premium joint/solo producer is canonical in
`exports/NEGATIVE_PREMIUM_CYCLIC_CHILD_UNIFORM_EQUILIBRIUM.md`.
Its cyclic child has no good triple-join row; its root is produced by an
exact scalar crossing on the stated fixed-row completion family.
The final internal rescaling test shows that opponent-quiet compactification
can preserve R0/degree1 and exact punishment normality while losing both
actual induced-Nash and owner-floor boundary conditions. That test is
covered by a pure pair and is not additional UE coverage.
The later universal-escape section proves a simultaneous-infinity branch for the
ORIGINAL scalar shift whenever every triple join is negative and the
outsider's passive triple premium is positive. The accepted cyclic-child
table realizes it while satisfying R0/degree1, punishment normality and
all concrete-base positive gaps. Those finite screens cannot provide the
missing common isolation; no conclusion about the global semantic minimum
or no-UE is inferred from the artificial branch.
The full sixty-coordinate producer is canonical in
`exports/FULL_DIMENSIONAL_CYCLIC_CHILD_UNIFORM_EQUILIBRIUM.md`.
It removes fixed-row equalities locally, not the general no-good-child
obligation. Its duplicate proof is replaced below by the canonical link;
the distinct universal escape and no-source caveats remain here.
This remains internal ordinary mathematics, with no Lean or export seal.
The genuinely arbitrary all-A escape classification is still open.
The new final planar-degree argument produces cyclic policies for a
nonuniform raw negative-premium family under twelve actual endpoint caps.
Its H≤0 branch has an actual child-only consumer. Class increment is
unproved; its early test is already covered. A negative outside inverse
weight selects the favorable active-origin determinant correction, but
does not yet supply the remaining cap/deviation dispatch.
The latest actual switch test excludes all six proper three-row words
with two pivot0 joints at an explicit negative-corrected-determinant table.
That table has an exact existing punishment-root consumer. This falsifies
the adjacent-role-switch mechanism, not UE; no class increment is claimed.
The final clock tests distinguish two issues: identical relative likelihoods
do not retain tied coalition outcomes, even for actual entropy near-minimizers;
and every one-atom insertion can raise debt while a legal ordered three-atom
insertion lowers it. These are exact scope regressions, not new UE classes.

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
negative entry. Thus Γ is R0. Its only solution at offset−1 is
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

An exact positive test of the adapter changes only three passive entries
of the strict sixty-coordinate buffered table:

    r₁(02)=12,       r₂(01)=7,       r_b(012)=102.

The singleton Γ and all six strict pair joins are unchanged. The triple
joins are(1,−10,−5). The good owner0 has Γ₀b=−1 and cylinder radii(4,8).
Its C⁰ vertices are0,−8,−8,−304/15. Its C¹ vertices are
−2,−46/15,−46/15,−38/15. Thus the cylinder cap is strict.

There really is an unbounded shifted-root family here, not merely a
formal boundary point. Set X₀=1/z, X_b=0 and define, for i=1,2,

    F_i(z,x₁,x₂)=z[e_i(1/z,x₁,x₂,0)−e₀(x₁,x₂,0)].

Each F_i extends smoothly through z=0: the only 1/z term of e_i is
−(c_i0+c_iA x_k)/z, and its rational P_i/D_i term has denominator
(1+z)(1+x_k) after cancellation. The extensions at zero are

    F₁(0,x₁,x₂)=−1+10x₂,
    F₂(0,x₁,x₂)=−1/2+5x₁.

Their common zero is(1/10,1/10), with x-Jacobian
[[0,10],[5,0]], determinant−50. The ordinary implicit function theorem
therefore gives x₁(z),x₂(z)>0 for all sufficiently small positive z,
converging to that point and solving F₁=F₂=0 exactly. Put
λ(z)=e₀(x₁(z),x₂(z),0); its limit is416/3025>0.
The anchor residual divided by X₀ tends to

    Γ_b0+(r_b(01)−s_b)/10+(r_b(02)−s_b)/10
      +(r_b(A)−s_b)/100=−1+101/100=1/100>0.

Hence e_b>λ eventually. These are actual zeros of H_λ with three
positive A odds, b odds zero, bounded λ and X₀→∞. In contrast to the
earlier symmetric escape, the shift stays bounded.

The consumed induced law is exactly(q₁,q₂,q_b)=(1/11,1/11,0) at base0.
The two free A joining gaps are zero. Anchorb's Continue and Quit payoffs
are respectively122/121 and−1659/2420, so its joining gap is
−4099/2420<0. Owner0 has U₀=157/121, W₀=29/25 and quiet-free
probability100/121. A literal punishment makes player2 quit surely on
the next date if owner0 deviated to Continue and both free players were
quiet. Its owner cap is max(r₀(02),r₀(2))=1/2, so actual Pun₀≤1/2.
The source owner floor is therefore≤

    (100/121)(1/2−29/25)=−66/121<0.

This exact independent product law plus the specified date-one punishment
is itself terminal Nash against every complete behavioral replacement:
all nonowner deviations still absorb against owner0 at date0 and reduce
to their already checked finite endpoints; an owner deviation either
absorbs at date0 or meets the fixed date-one sure quitter. No private
memory, late stopping or Never can improve that cap. It realizes fixed
target(157,572,77,122)/121. Under the initial-zero convention it is even
exact Nash at every positive horizon: the nonowner endpoint payoffs share
the common factor(N−1)/N; the owner's quiet punishment return is at most
(N−2)_+/N times1/2, which is≤(N−1)/N times1/2. The same strict owner
floor still controls its entire reply. Target delivery error is O(1/N).

Thus the semantic consumer is nonvacuous and retains a true signed-game
punishment cap rather than a nominal phase tail. This table is already
covered by the actual singleton source; it is a mechanism test, not an
additional UE class or a request for another export.

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

## Owner–anchor escape: compactness modulo two real UE consumers

The negative comparison Γ₀b<0 is not needed for the semantic dispatch once
both possible unbounded coordinates are treated. The following complete
ordinary-mathematics mechanism stays internal: no actual-source increment
or independent review is claimed. It does not consume escape with no good
triple row.

Assume all six c_ij>0 and c₀A≥0. Put

    B=max(0,Γ₀b,M₀),       R₁=B/c₀₁,       R₂=B/c₀₂.

Require the same seven cylinder vertex tests, now at these radii. Owner0
may use either passive-cap alternative; players1,2 must use the second:
Π_ij,Π_ik,Π_iA≥0 and r_i(ib)≤r_i(b). These are finite raw conditions
only. There is no sign assumption on Γ₀b,c₁A,c₂A or any own singleton.
The conclusion is raw UE existence, not necessarily one exact period-two
profile. The boundary consumer below uses accuracy-dependent punishments.

For a shifted zero, the good row still gives X₁≤R₁,X₂≤R₂ and

    0≤λ≤M₀+max(Γ₀b,0)X_b.                         (B3)

Thus only X₀ and X_b may escape. Work on the actual normalized no-UE
source: it supplies every Pun_i≤s_i and own levels in{0,1}, together with
literal Γ R0/degree one. All raw comparisons and cylinder tests survive
its positive common scaling, as proved above.

If X₀→∞, even with X_b→∞, divide the other A residuals by
X₀(1+X_b). Bound(B3) makes λ/[X₀(1+X_b)]→0. The terms Γ_ibX_b and
P_i/D_i also vanish after this division, leaving

    −(c_i0+c_iA x_k).

The same Nash complementarity and owner floor argument gives a genuine
singleton0 induced Nash law and admissible actual punishment floor.
The b endpoint comparison needs no bound on X_b because its A-date
endpoints depend only on A odds and satisfy C_b≤0≤e_b. This dispatch
consumes the simultaneous owner–anchor escape, not just X_b bounded.

It remains to treat X_b→∞ with X₀ bounded. Pass to a subsequence on
which all A odds converge to finite x_i. Since X_b>0 eventually,
complementarity gives λ=e_b(X_A), hence λ is bounded on this branch.
Dividing(T5) by1+X_b yields

    Γ_ib−L_i(x_A)≥0,
    Γ_ib=L_i(x_A) whenever x_i>0.                  (B4)

The anchor residual itself satisfies e_b(x_A)≥0. Let q_i=x_i/(1+x_i).
The two-date profile is: at date0 the A players use q and b Continues;
after quiet survival, at date1 b quits surely and all A players Continue.
If b unexpectedly Continues at date1, the other players switch from
date2 to a stationary near-punishment of b. On its prescribed path the
profile absorbs by date1, regardless of the punishment choice.

Before date1 the A player's Continue value is exactly r_i(b)=s_i+Γ_ib.
At date0 its Quit endpoint is U_i=s_i+P_i/D_i. The algebraic Continue
identity with nominal tail s_i+L_i shows that the actual Continue endpoint
with tail r_i(b) is

    U_i+[Γ_ib−L_i]/D_i.

By(B4), an active q_i has equality and an inactive player weakly prefers
Continue. These are the full date0 Nash endpoint inequalities. At date1,
the passive Quit payoff r_i(ib) is≤r_i(b) for both bad players by their
raw cap. For the good owner, the second cap works directly; under its
first cap, Γ₀b≥L₀≥0 from(B4), so
r₀(0b)≤s₀≤r₀(b). All nonowner complete deviations therefore reduce to
these two-date endpoints: b still quits surely at date1 and absorbs them.

The actual on-path A payoff is

    V_i=U_i+(1−q_i)[Γ_ib−L_i]/D_i.

This retains the inactive correction explicitly; an inactive nominal U_i
is not silently identified with its policy payoff. The anchor's actual
date0 Continue value is

    V_b=s_b+e_b(x_A)/D_A≥s_b.

Its forced Quit endpoint is s_b+C_b(x_A)/D_A≤s_b by the cylinder cap.
At date1 it receives s_b by Quit. To make Continue unprofitable up toη,
choose stationary opponents with complete terminal best-reply cap≤Pun_b+η
≤s_b+η. Their existence follows from the literal real infimum and
`quittingPunishmentValue_eq_stationaryPunishmentValue` in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean`; the infimum is not
assumed attained. The first-date endpoint inequality and this actual
tail cap bound EVERY complete behavioral reply by V_b+η. Late stopping,
private memories and Never are included in the stationary stopping cap,
not guessed from one nominal continuation number.

The finite-horizon consumer is also explicit. If any stationary punishment
opponent has positive hazard, opponent survival is geometric and the
terminal-to-horizon error is≤C_η/H for every complete reply over H
remaining stages. If all punishment opponents Never, their horizon reply
cap is≤max(s_b,0)=s_b because the normalized own level is nonnegative.
The two live prefix dates contribute zero and shifting the remaining
horizon into the original N average costs O(1/N). The on-path payoff
vector V is independent ofη, absorbs by date1 and differs from its
N-average realization by at most2M/N. All A deviations share that bounded
absorption clock; the anchor deviations have gain at mostη+C_η/N.
Chooseη before N, then choose N large for every prescribed accuracy.
Thus this is one FIXED uniform target, with no claim that its punishment
profile is independent of accuracy or that it is exact terminal Nash.

Consequently actual no UE excludes every unbounded shifted-root sequence:
one of the two just proved consumers would give UE for the same actual
normalized table. On a bounded zero family, λ is bounded by(B3), so a
larger shift has no zero; local degree one/global degree zero produces
a finite nonzero H₀ root. Its six pair joins exclude singleton support.
The good-row floor and bad-row nonnegative-premium alternatives give
every passive endpoint inequality, and the usual inactive corrections and
deleted-clock argument supply a full exact terminal profile and uniform
target. That is the final alternative, also contradicting normalized no UE.
This proves the stated raw existence corollary without substituting a
convenient global isolation assumption for the semantic source.

The original-game conclusion is only obtained through the actual
normalization's retained no-UE field. A row translation does not in general
pull this delayed-anchor/punishment strategy back: an all-Never punishment
tail can retain positive Never mass, and the original anchor's own reward
can be negative. No false affine-invariance or fixed-profile claim for
arbitrary original signed tables is being made.

### Exact nonvacuous delayed-anchor escape test

From the strict sixty-coordinate buffered table change only

    r₀(02)=r₁(12)=1,       r₀(03)=r₁(13)=0,
    r₀(12)=r₁(02)=5,       r₂(01)=0.

All other coordinates remain literally those of that table. Take the
good owner as2 rather than0. The six pair joins are(1,1,1,1,1/2,1/2)
in ordered01,02,10,12,20,21. The triple joins are(−3,−3,2). The bad
players0,1 have within-A premiums(4,0,1) and passive cap0≤r_i(b)=0.
Good player2 uses its original cap r₂(23)=0≤own1, with Γ₂b=3.
Its B=3 and cylinder radii are(6,6) on coordinates0,1.
The constant anchor-polynomial vertices are0,−12,−12,−168/5;
the coefficient vertices are−1,−9/5,−9/5,−4/5. All tests pass.

There is an actual shifted-root branch with X_b→∞ and X_A→(1,1,1).
Put X_b=1/w and define F_i(w,X_A)=w(e_i−e_b) for i∈A. It extends
smoothly at w=0 with F_i(0,X_A)=Γ_ib−L_i. At X_A=1 these three
values vanish. The X_A-Jacobian there is

    [[0,2,2],[2,0,2],[−5/2,−5/2,0]],

with determinant−20. The ordinary implicit function theorem gives an
exact positive X_A(w)→1 for all sufficiently small w>0. Here
λ(w)=e_b(X_A(w))→1>0, so H_λ=0 with all four coordinates positive.
This is a bounded-shift, anchor-only unbounded branch. Its limiting
periodic policy is NOT stationary terminal Nash: at the anchor's solo
row its nominal Continue advantage is still positive.

The correct consumer uses A hazards(1/2,1/2,1/2) once, then b sure,
then all opponents Never if b refused its sure exit. The A first-date
endpoints both equal(9/4,9/4,1), and their passive date-one Quit caps
are(0,0,0)≤r_A(b)=(0,0,4). The anchor's date0 Continue and Quit values
are9/8 and151/480 respectively. Its solo Quit value is1, whereas after
refusing it the literal all-Never punishment cap is max(own1,0)=1.
Thus the profile is exact TERMINAL Nash against all complete behavioral
deviations, with fixed target(9/4,9/4,1,9/8).

It is also one fixed uniform profile. Every A deviation absorbs by date1.
An anchor deviation reaching the punishment tail earns at most1 at every
remaining horizon, including late Quit and Never. For N≥2 its exact
N-average payoff vector is

    (9(N−1)/(4N), 9(N−1)/(4N), (2N−3)/(2N), (9N−10)/(8N)).

The delivery sup-norm error is9/(4N). Players0,1 have equal initial
endpoints. Player2's Continue endpoint loses1/N relative to its Quit
endpoint, and its prescribed half mixture therefore has exact best-reply
gain1/(2N). The anchor's Continue payoff exceeds its initial Quit payoff
by(389N−449)/(480N)>0, and at date1 any delayed own1 return loses
weakly to its prescribed earliest exit. Thus the exact horizon Nash
error is1/(2N); N=1 has zero payoff and zero error. Exact finite-horizon
Nash is NOT claimed. The accuracy tends to zero at the same fixed target.

This stress proves that the delayed-anchor arm repairs a genuinely
non-Bellman escape limit by an actual observed-deviation punishment.
No full concrete-source census or new UE-class increment is claimed for
the test table. It is not being added to the frozen export.

### Exact source inclusion of the delayed-anchor arm

The current passive-cap hypotheses make the anchor-only escape arm an
existing-source branch, not an additional existence class. At that limit
every bad A row already has r_i(ib)≤r_i(b). A good row using the second
alternative does too. A good row using the first has Γ_ib≥L_i≥0 from
(B4), and hence r_i(ib)≤s_i≤r_i(b). Therefore ALL three players have
nonpositive joining gaps into singletonb.

At base{b}, choose the complete free law with all A hazards zero. It is
induced finite Nash precisely because these three joining gaps are≤0.
There are no outsiders. The owner's actual singleton floor is simply
Pun_b−s_b≤0. Thus
`exists_uniformPayoff_or_singletonBase_pos_gap` already closes the table.
The delayed two-date proof remains a correct stronger fixed-policy test,
but is not a counterexample-class increment. In particular its seven-
coordinate stress is consumed by this literal certificate, without a
full carrier census or an invented same-profile punishment infimum.

This observation also PRODUCES the negative good-row comparison on actual
source-screen survivors. With one good row0 and the other two using the
second cap, singletonb all-Never cannot be induced Nash with an admissible
owner floor. Since Pun_b≤s_b on the actual normalized no-UE source,
player0 must have

    r₀(0b)−r₀(b)>0.

Its second cap is consequently impossible; it uses the first cap and
r₀(0b)≤s₀ then forces Γ₀b=r₀(b)−s₀<0. This is not an extra
reward assumption or a nominal phase comparison: the actual full free
carrier and actual punishment floor give it. The one-coordinate escape
adapter above can therefore use the source-selected negative row.

More generally, if |G|≥2 and every bad row uses the second cap, absence
of the same immediate singletonb certificate forces some GOOD row to
have positive joining into b and therefore negative Γ_ib. This supplies
the good negative comparison used in the two-good-row bounded proof.
The additional raw comparison clause in the frozen theorem is sufficient
but not necessary once this actual normalization/source dispatch is used.
No revision of the frozen export is proposed here.

Next global obligation: remove the last good-row assumption or classify
escaping faces when every c_iA<0. In that case all A odds may diverge,
λ need not stay below the scale of the leading joining coefficients, and
neither finite-face adapter above is yet valid. MORSE's source-screen
survivor emphasizes that mere R0/degree, punishment normality and all
fifteen positive concrete gaps are jointly consistent. The required next
step is another actual phase/boundary consumer, not an algebraic claim
that those source fields contradict each other.

## Canonical negative-premium cyclic-child result

The completed raw producer and its sixty-coordinate whole-source comparison
are in `exports/NEGATIVE_PREMIUM_CYCLIC_CHILD_UNIFORM_EQUILIBRIUM.md`.
Its raw family fixes four singleton rows and one negative-premium joint
row, imposes twelve unilateral-collision caps, and leaves twenty-eight
coordinates arbitrary. It produces a joint03/solo1/solo2 cycle for
0<ε<15/26 and a child-only solo3/solo1/solo2 cycle for 15/26≤ε≤1.
The canonical high-ε B value is (24/13,1,3,1).
All strategic inputs, signed own levels, actual behavioral replies,
realization, fixed target and horizon estimates are covered there.
That result does not consume an arbitrary no-good triple-join child.
The distinct nonlinear escape tests and actual-source caveats above
remain internal and are not consequences of this fixed-row producer.

## Opponent-quiet compactification: exact failure of the boundary-law adapter

### Precise broader question

Keep A={0,1,2}, b=3, six strict positive pair joins c_ij and arbitrary
negative triple joins c_iA. Do actual R0/degree1, punishment normality
and every literal persistent-base positive gap force a finite nonzero
two-phase root, or can a rescaled escape be dispatched to another actual
strategy? There is no supplied favorable root in this question.

A natural attempt changes the regularization, not the target zeros.
For i∈A put D_i=(1+X_j)(1+X_k), let
P_i=Π_ij X_j+Π_ik X_k+Π_iA X_jX_k and
L_i=c_ij X_j+c_ik X_k+c_iA X_jX_k. The old residual is

    e_i=Γ_ib X_b−(1+X_b)L_i+P_i/D_i.

Let q_i=X_i/(1+X_i), and divide e_i by (1+X_b)D_i. Define

    J_i=c_ij q_j(1−q_k)+c_ik q_k(1−q_j)+c_iA q_jq_k,
    π_i=Π_ij q_j(1−q_k)+Π_ik q_k(1−q_j)+Π_iA q_jq_k,
    E_i=Γ_ib q_b(1−q_j)(1−q_k)−J_i
                    +(1−q_b)(1−q_j)(1−q_k)π_i.           (R1)

For b divide its passive excess e_b by D_A=∏[i∈A](1+X_i).
The resulting E_b is the expected passive increment over s_b under
independent A hazards, with zero increment on the empty event. All four
E extend polynomially to the compact hazard cube. Their derivative at0
is Γ, and their finite unshifted zeros are exactly those of e.
At q_A=(1,1,1), one has E_i=−c_iA and E_b=r_b(A)−s_b.
Thus a full-A escape for the uniformly shifted E_i−λ would require
three equal negative-triple-join magnitudes; distinct raw magnitudes
rule out that particular boundary. This is a true algebraic observation,
not yet a semantic existence theorem.

The obstacle is that this shift destroys the old leading-coefficient
finite-Nash dispatch. At an owner escape it can leave J_i=−λ<0 at
a proper free hazard. Such a free player strictly prefers Continue in
the actual induced game. The following exact test preserves even the
linear source and true punishment screens; it falsifies using the
limiting law without reselection.

### Complete rational early test

All owns are1. Give every coordinate by the table

| S | r(S), in player order0,1,2,3 |
|---|---|
| 0 | (1,0,0,4) |
| 1 | (4,1,0,0) |
| 2 | (4,0,1,0) |
| 3 | (0,4,4,1) |
| 01 | (5,1,8,4) |
| 02 | (5,8,1,4) |
| 03 | (1,1,1,1) |
| 12 | (8,1,1,0) |
| 13 | (1,1,1,1) |
| 23 | (1,1,1,1) |
| 012 | (5,5,5,4) |
| 013 | (1,1,1,1) |
| 023 | (1,1,1,1) |
| 123 | (1,1,1,1) |
| I | (1,1,1,1) |

Then c_ij=1 for all six A pair joins, c_iA=−3 for all three
triple joins. The participant premiums in row0 are (4,4,4);
in rows1 and2 they are (0,0,4). The singleton matrix is

    Γ=((0,3,3,−1),(−1,0,−1,3),
       (−1,−1,0,3),(3,−1,−1,0)).                       (R2)

Its pair principal determinants in order01,02,03,12,13,23 are
(3,3,3,−1,3,3), triple determinants in order012,013,023,123
are (6,26,26,6), and full determinant49. Every column has a
negative entry and all supports of size≥2 have nonsingular principal
matrix, so Γ is R0. At offset−1, all pair solutions have a negative
coordinate; triples012 and123 have negative coordinates, while
013 and023 have active vector(1/2,1/2,1/2) and omitted residual−1/2.
The only root is (25,13,13,29)/49, with positive full determinant.
The exact root-sum theorem therefore gives degree1 and standard Q.
The inspected implementation is `exists_finset_r0Degree_eq_sum_sign_det`
in `MathUE/LinearProgramming/R0DegreeSum.lean` and
`isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean`.

Every participant reward is at least1, so immediate Quit guarantees1.
The actual punishment value is at most max(own1,0)=1 by
`quittingPunishmentValue_le_max_solo` in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean`.
Hence every actual punishment value equals1, with no nominal phase
annotation substituted for a true cap.

Set q_0=t, q_1=q_2=r, q_b=0. Formula(R1) becomes

    E_0(r)=−2r+5r²+4(1−r)²(2r−r²),
    E_1(t,r)=E_2(t,r)=−t−r+5tr+4tr(1−t)(1−r),
    E_b(t,r)=3t−(1−t)(2r−r²).                         (R3)

At t=1,r=1/2, the first three values equal1 and E_b=3.
For H=E_1−E_0 the exact derivatives there are H_r=3 and H_t=1/2.
The ordinary implicit function theorem produces r(t)→1/2 for all
t<1 sufficiently close to1, with H(t,r(t))=0 and r'(1)=−1/6.
Put λ(t)=E_0(r(t))→1. All three active hazards are proper, λ>0,
and E_b>λ. Thus this is an exact finite shifted-root branch
E≥λ, q_i(E_i−λ)=0, with X_0→∞ and X_1,X_2→1,X_b=0.
It is not a numerical root.

The boundary free law (q_1,q_2,q_b)=(1/2,1/2,0) at base{0}
has each child's joining gap

    c_i0(1−1/2)+c_iA/2=−1.

Both proper children strictly prefer Continue, so this is NOT an induced
Nash law. The owner fails the true floor too: Quit has expectation4,
while Continue with the actual punishment tail1 has expectation17/4.
Its literal singleton floor excess is1/4>0. Rescaling preserved finite
target zeros but did not preserve the semantic boundary certificate.

### Scope and remaining obligation

This is an exact failed implication, not a no-UE table: sure01 is a
full-behavior terminal Nash profile. Its owners have joining gaps1,1;
player2 joining01 has gap−3, and player3 has gap−3. One other sure owner
absorbs any unilateral late response, and the quiet outsiders also see
immediate absorption. In the actual large-base screen choose E={0,1}
and the complete free law with players2,3 both Continue. That law is
induced Nash, the two member excess components are both−1, and there
are no missing outsiders. Thus
`exists_uniformPayoff_or_persistentLargeBase_pos_gap` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`
already consumes the table. It does not satisfy every concrete-base
positive gap.

The compactification may still be useful if the actual positive-gap
source forces a DIFFERENT independent Nash law after escape. The limiting
law itself is not that witness, even with R0/degree1 and exact Pun=s.
The next question is whether whole finite-Nash reselection and the global
positive minimum can rule out or consume these rescaled boundary roots
without imposing a convenient triple sign. No such implication is proved
here. This guardrail and the bounded polynomial reformulation remain
internal supporting mathematics; they do not narrow UE counterexamples.

## Universal all-coordinate escape of the original scalar shift

### Exact raw statement

Let A be any three-player subset of four players, and let b be its
complement. The finite table is arbitrary and signed. For i∈A and
{j,k}=A−{i}, put s_i=r_i(i),

    c_ij=r_i(ij)−r_i(j),
    c_iA=r_i(A)−r_i(jk),       a_i=−c_iA,
    δ=r_b(A)−s_b.

Assume only a_i>0 for all three i and δ>0. No restriction on the six
pair joins, singleton matrix, other rewards or own signs is needed.
Use exactly the original residuals e_i, not the compactification(R1):

    e_i=Γ_ib X_b−(1+X_b)L_i+P_i/D_i,
    L_i=c_ij X_j+c_ik X_k−a_i X_jX_k,
    P_i=Π_ij X_j+Π_ik X_k+Π_iA X_jX_k,
    D_i=(1+X_j)(1+X_k),
    e_b=Σ_j Γ_bj X_j
        +Σ_{j<k}(r_b(jk)−s_b)X_jX_k+δ∏[j∈A]X_j.       (S1)

Here Γ_ij=r_i(j)−s_i and Π_iS=r_i(S)−s_i. There is an
exact positive branch satisfying e_i(X)=λ for ALL four i, with

    X_b=1/w,
    X_i=(a_i/δ+o(1))/w,
    λ=(a_0a_1a_2/δ²+o(1))/w³                       (S2)

as w→0+. The product in(S2) uses the three labels in A. Thus every
coordinate tends to infinity and λ tends to infinity. These are roots
of the original shifted complementarity problem, with every coordinate
strictly active. They are not claimed to be strategic Bellman roots.

### Complete proof

Fix X_b=1/w, write X_i=y_i/w and λ=κ/w³, and multiply the four
equations e_i−λ=0 by w³. The scaled functions extend smoothly at
w=0, y_i>0. Indeed

    P_i/D_i=[w(Π_ij y_j+Π_ik y_k)+Π_iA y_jy_k]
                                   /[(w+y_j)(w+y_k)],

whose denominators remain positive near the point below. The exact
scaled i equation is

    F_i=(1+w)a_i y_jy_k
        −w(1+w)(c_ij y_j+c_ik y_k)+Γ_ib w²
        +w³ P_i/D_i−κ,

and the exact b equation is

    F_b=δ∏[i∈A]y_i
         +wΣ_{j<k}(r_b(jk)−s_b)y_jy_k
         +w²Σ_jΓ_bj y_j−κ.                         (S3)

At w=0 their positive solution is

    y_i=a_i/δ,             κ=a_0a_1a_2/δ²>0.       (S4)

It is the unique positive solution after fixing X_b's scale: comparison
of F_i=0 with F_b=0 gives a_i/(δ y_i)=1. To check nonsingularity,
replace each of the three F_i rows by F_i−F_b. At(S4) the y-Jacobian
in these rows is diagonal with entries−κ/y_i, and their κ-derivatives
are0. The last row's κ-derivative is−1. Therefore the full four-variable
Jacobian determinant is

    κ³/(y_0y_1y_2)>0.

The ordinary implicit function theorem gives smooth y_i(w),κ(w) near0
with the positive limits(S4). For all sufficiently small w>0 they are
positive and solve(S3). Reversing the scaling proves(S1)–(S2).
All reward-table lower-order terms are retained. There is no strategic
root supplied and no symmetry hypothesis on the three magnitudes.

In particular, neither generic inequality among the three a_i nor
R0/degree1 of Γ removes this original full escape. The ratios of the
escaping odds adjust automatically to a_i/δ. The only use of an implicit
function theorem is at an explicitly produced, nonsingular infinity
chart, not at an assumed favorable finite equilibrium root.

### Actual finite-screen survivor realizing the branch

Use the complete canonical rational table in
`exports/NEGATIVE_PREMIUM_CYCLIC_CHILD_UNIFORM_EQUILIBRIUM.md`, with
ε=100/729, A={1,2,3}, b=0. For this literal table

    a_1=a_2=a_3=2−ε=1358/729,             δ=1.

Thus(S2) gives an exact branch with all three child odds asymptotic to
(1358/729)/w, the pivot odds1/w, and λ asymptotic to
(1358/729)³/w³. The table's full singleton matrix is R0 of degree1,
its actual punishment values are1−ε≤own1, and every full or partial
concrete persistent-base carrier has a strictly positive attained gap;
the canonical document gives their exact whole-selection-set proof.
Unlike the regression(R2), this table is NOT consumed by another
concrete-base witness.

This establishes that the complete finite linear/punishment/base-gap
screens can coexist with universal nonlinear scalar-shift escape.
The table nevertheless has a UE, produced by a DIFFERENT three-row
architecture in the canonical theorem. Its global semantic minimum is
therefore zero. No contradiction to a positive global minimum under
actual no UE is being asserted.

### Direction consequence and nonclaims

The nominal A-to-b value s_i+L_i on this branch diverges to−∞ like
−a_i y_jy_k/w², although every actual reward and every realized policy
value for this one fixed finite table is bounded. Thus these shifted
annotations cannot be used as actual payoff caps or targets. Taking
the all-sure hazard limit does not repair them: the three A joining
gaps c_iA are strictly negative, so its owners do not even pass the
actual joint-date action test.

A bounded scalar-shift argument cannot close the general no-good/
positive-passive-premium chamber merely by appending Γ degree,
punishment normality or the fifteen positive base gaps. It must change
the regularization or use a genuinely different phase/boundary strategy.
The positive global semantic minimum might still rule out this chamber
through such an actual strategy, but no transfer from that minimum to
(S1) is proved. This is a universal obstruction to a specific isolation
route, not an additional counterexample-class restriction or UE theorem.
The next concrete target is an actual producer for the positive-leading
escape geometry, rather than a claim that the artificial branch is absent.

## Canonical full sixty-coordinate producer

The complete theorem and proof are now in
`exports/FULL_DIMENSIONAL_CYCLIC_CHILD_UNIFORM_EQUILIBRIUM.md`.
For every η>0 its fully displayed rational center has an unconditional
full sixty-coordinate UE neighborhood. The four ACTUAL active-gap
Jacobian is nonsingular and all eight passive comparisons are strict.
The same original-game profile supplies one target at every sufficiently
large horizon against unrestricted behavioral replacements.

At the explicit source-comparison center η=50/729, punishment remains
629/729 and the unique punishment-priced root is
(593/5525,1/10,1/10,1/10). The canonical proof excludes all65
base/free carriers, all14 universal child quiet-lift families and the
stated finite phase/core sources, including arbitrary positive-row-scale
quotients. A further singleton-coordinate perturbation gives a full open
subball outside the fixed-row criterion too.

This is local in reward space. It is not an arbitrary no-good-child
consumer and does not remove the distinct simultaneous-infinity branch
proved above. The earlier scalar-escape and semantic-boundary caveats
remain independent research obligations.

## Planar degree for a nonuniform negative-premium cyclic child

Status: the finite root and endpoint arguments below are ordinary
mathematics, not Lean checked. No new class increment is asserted:
the exact early test is already covered. The global question is whether
actual hard-source data can supply or dispatch the passive cap conditions.

### Raw data and actual equations

Own singleton rewards s_i may be arbitrary signed. Relative singleton
comparisons, not a transformation of Never, are

    Γ=[[0,v₁,v₂,u],
       [−h₁,0,−b₁,a₁],
       [−h₂,a₂,0,−b₂],
       [−h₃,−b₃,a₃,0]],

where a_i,b_i,h_i>0, u<ξ<0, −h₃<η<0 and
β=a₁a₂a₃−b₁b₂b₃>0. On03 prescribe participant premiums ξ,η
and passive premiums a₁−h₁,−h₂−b₂. Other entries are arbitrary
subject to the twelve caps below. No root is supplied.

For joint03 rates p,y and solo1,solo2 rates z,w put

    A=a₁y−h₁p, δ=h₃+η,
    z=(h₂p+b₂y)/[a₂(1−p)(1−y)], w=A/(A+b₁),
    R=y(ξ−u)/(1−y)−v₁z−(1−z)[v₂w+ξy(1−w)],
    T=pδ/(1−p)+b₃z−(1−z)[a₃w+ηp(1−w)].           (D1)

A proper zero of R,T gives the relative phase values

    V_A=(ξy,A,0,ηp),
    V_B=(y(ξ−u)/(1−y),0,a₂z,pδ/(1−p)),
    V_C=(v₂w+ξy(1−w),0,0,a₃w+ηp(1−w)).             (D2)

Adding s_i restores original annotations. Both joint owners are
indifferent; the other two owners have their own singleton annotation.
The A2 recursion is −h₂p−b₂y+a₂z(1−p)(1−y)=0, the C1
recursion is −b₁w+(1−w)A=0, and the remaining B0/B3 recursions
are R=T=0. Thus all policy equations, not nominal floors, are checked.

### Boundary signs produce a root without a supplied branch

Define

    α=δ+b₃h₂/a₂+a₃h₁/b₁, τ=a₂b₁α/β,
    L=−uτ−v₁(h₂+b₂τ)/a₂−v₂(a₁τ−h₁)/b₁,
    y₀=β/[a₁(b₂b₃+a₃(a₂+b₂))],
    z₀=b₂y₀/[a₂(1−y₀)], w₀=a₁y₀/(a₁y₀+b₁),
    H=R(0,y₀).

If L<0 and H>0, a proper zero exists. Consider the curvilinear triangle

    p>0, A>0, C=a₂(1−p)(1−y)−h₂p−b₂y>0.

Its y bounds are the increasing line h₁p/a₁ and the strictly decreasing
function[a₂−(a₂+h₂)p]/[a₂+b₂−a₂p]. They meet exactly once.
Its closure stays away from p=1,y=1, and(D1) extends continuously.

On A=0, w=0 gives T=pδ/(1−p)+b₃z−(1−z)ηp>0 away from0.
On C=0, z=1 gives T=pδ/(1−p)+b₃>0.
On p=0, multiplication by positive denominators shows T has exactly
two zeros,0 and y₀, with T<0 between them and T>0 above y₀.
The product gap gives0<y₀<a₂/(a₂+b₂).

Near0,

    T=αp−[β/(a₂b₁)]y+O((p+y)²).

Its local zero curve is y=τp+O(p²), strictly above A=0:
α−βh₁/(a₁a₂b₁)
=δ+b₃h₂/a₂+b₂b₃h₁/(a₁a₂)>0.
Along that curve R=Lp+O(p²)<0.

Remove a tiny corner p+y<t. On this new straight boundary T has
exactly one zero, since its tangential derivative is
α+β/(a₂b₁)>0 at0 and nearby; its R coordinate is negative.
The only other boundary T-zero is(0,y₀), where R=H>0.
Both crossings change sign; T is nonzero on the rest of the boundary.
The loop(R,T) therefore has winding number±1: the two half-plane
arcs join opposite horizontal rays, once above and once below the axis.
Each half-plane contracts, so no additional winding is possible.
If there were no interior zero, normalization would extend that loop
to a disk in the circle, impossible. This proves a proper zero without
uniqueness, nonsingularity or a selected quadratic branch.

### Finite caps pay the complete passive bill

For participant premiums J_i(S)=r_i(S)−s_i put

    q_min=h₂b₂/[(a₂+h₂)(a₂+b₂)],
    m₀=a₂q_min(ξ−u)/(h₂a₁/h₁+b₂)>0,
    m₁=b₁b₂b₃/(a₂a₃), m₃=b₁b₂b₃/(a₁a₂),
    m_C=v₂+ξa₂a₃/(b₂b₃).

Assume

    J₁(01)≤0,  J₁(13)≤m₁, J₁(013)≤0;
    J₂(02)≤0,  J₂(23)≤0,  J₂(023)≤0;
    J₀(01)≤m₀, J₃(13)≤0,  J₂(12)≤a₂;
    J₀(02)≤m_C,J₃(23)≤m₃, J₁(12)≤0.              (D3)

At a zero, T=0 implies

    V_C,3=[pδ/(1−p)+b₃z]/(1−z)>b₃z/(1−z),
    w>(b₃/a₃)z, z≥b₂y/a₂, A>m₁y.

Hence A1 Quit≤m₁(1−p)y<A, A2 Quit≤0=Continue;
B2 Quit≤a₂z=Continue, B3 Quit≤0<Continue;
and C1 Quit≤0=Continue.
Since w<A/b₁<a₁y/b₁, one has z/w>b₁b₂/(a₁a₂).
This gives V_C,3/w>m₃, paying C3.

Also y(1−w)/w=b₁y/A<a₂a₃/(b₂b₃). Multiplying by ξ<0
gives V_C,0/w>m_C, paying C0 even when m_C<0.
Finally p<a₂/(a₂+h₂), y<a₂/(a₂+b₂), p/y<a₁/h₁ give

    y/z≥a₂q_min/(h₂a₁/h₁+b₂), V_B,0/z>m₀,

paying B0. All eight passive endpoints, including013 and023, are covered.

Actual value realization and unrestricted deviations follow by period
contraction: every deleted player leaves proper opponent clocks.
The opponent-only quiet probability is geometrically bounded uniformly
over complete history-dependent replacements, Never and late stopping.
Iterating the endpoint inequalities gives exact terminal Nash.
The same tail under the project's zero selecting-date convention gives
N-average Nash error≤2C/N, with C=3M max_i1/(1−ρ_i).
One profile supplies one fixed actual target at all sufficiently large
horizons. Arbitrary signs of s_i cause no problem, because opponents
alone absorb almost surely even against any unilateral replacement.

### The nonpositive H branch is a genuine child-only consumer

The p=0 child rates y₀,z₀,w₀ are proper and form exact terminal Nash
in123. The reverse-pair caps in(D3) pay its low passive comparisons;
m₁<a₁ and m₃<a₃ follow from β>0 and pay the high ones.
The B2 cap pays the remaining high comparison.

The pivot's actual A gap in this quiet lift is
(1−y₀)H/[1−(1−y₀)(1−z₀)(1−w₀)].
When H≤0 its actual A value is at least ξy₀. Propagating actual
Continue values then dominates the forced B/C annotations(D2).
The B0/C0 cap bounds above still hold at p=0, using T=0 and the same
domain bounds. Thus every pivot passive endpoint passes too, and the
child-only profile is full-game terminal Nash.

Accordingly L<0 and(D3) produce UE for the ENTIRE raw family:
H≤0 gives the quiet child; H>0 gives the interior degree root.
The genuine remaining restriction is the cap bill, not a missing branch.

### Singleton determinant correction and source-facing selection

Exact expansion gives

    C₃=a₁a₂v₂+a₂b₁u+b₁b₂v₁,
    −βL=detΓ+ηC₃.                                (D4)

Positive detΓ alone does not suffice for a chosen partner.
Take a_i=3,b_i=h₁=h₃=1,h₂=1/10,u=−1,v₁=v₂=1.
Then detΓ=31/10,C₃=7, and η=−1/2 gives detΓ+ηC₃=−2/5.
Every nonsingleton principal determinant is nonzero and every singleton
column has a negative entry. The sole offset−1 complementary root is

    (130/31,40/31,67/31,76/31),

with determinant31/10. Thus Γ is R0 of degree1, but L<0 fails.
No concrete-base or semantic-minimum assertion is made for this test.

There is nevertheless a meaningful selected-partner implication.
If D is the child singleton matrix and g=(v₁,v₂,u), block algebra gives

    detD=β, detΓ=β gD⁻¹h=Σ_i h_i C_i,
    C_i=β(gD⁻¹)_i.

A negative outside inverse weight makes its corresponding C_i<0.
Scheduling THAT partner with η_i<0 then makes detΓ+η_iC_i>0
whenever detΓ>0. So an actual passive-inverse failure can furnish
the correct active-origin sign, not for every partner but for a selected
one. This does not provide its signed joint data or passive cap tests.

Inspected source: JointPhaseData and exists_pivot in
MathUE/CyclicChildJointPhasePivot.lean assume eta_nonneg and use a
canceled endpoint interval; that hypothesis is not silently dropped here.
outsideInverseWeight_eq in
UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicChildPassiveInverseExit.lean
is the relevant source adapter. The algebraic block identity is proved;
the exact no-UE hypothesis match remains to be checked before global use.

### Covered exact test and next question

For a_i=3,b_i=h_i=1,u=−1,v₁=v₂=1,ξ=η=−1/100,

    β=26, α=1297/300, τ=1297/2600,
    L=−1293/2600, H=737/675,
    y₀=z₀=w₀=2/3, m₀=297/6400.

The canonical ε=1/100 table satisfies(D3). This is a covered
consistency test, not increment evidence or a new export candidate.

Next question: can a selected negative outside cofactor and actual
all-base/global-minimum source data supply a complete passive-cap
disjunction, or dispatch its failed cap to a different phase strategy?
The source-facing sign selection is real; another cap refinement on the
already-covered table would not answer this general dispatch obligation.

### Early actual failed-cap dispatch and a selected-partner obstruction

At the canonical cyclic table, change only r₁(013) to1+c.
For every c≥2 the literal sure base013, with player2 Continue, is
exact terminal Nash. The three owner joining gaps are respectively
0,c−2,2−ε, all nonnegative; outsider2 has joining1−2=−1.
Absorption at date0 persists against every single replacement because
two sure opponents remain. This is an actual persistent-large-base
consumer, not a supplied phase root. Thus sufficiently large failure
of that simultaneous A1 cap is already dispatched by an existing source.
The interval0<c<2 is not settled by this screen, nor asserted to violate
the actual passive endpoint of the produced interior policy.

More importantly, the negative-cofactor selection alone does NOT select
an admissible single-joint word. For the canonical singleton data,
C₁=−5,C₂=11,C₃=7. The favorable determinant correction selects
partner1, but its pivot comparison is u=Γ₀₁=1 and its pivot
participant premium is ξ=ε<1. Any proper joint01/solo2/solo3
policy with owner0 active indifference would consequently have

    V_B,0=s₀+y(ε−1)/(1−y)<s₀.

At B, pivot0's forced Quit payoff is EXACTLY s₀, since both its
singleton and its joining reward on02 equal s₀. Therefore its actual
passive endpoint fails, for EVERY proper hazard vector in this word.
No degree or cap estimate can repair that policy. This is an exact
source-facing failure, not a missing numerical root.

The actual successful word joint03/solo1/solo2 instead uses C₃>0;
its negative η correction is adverse, but detΓ+ηC₃ remains positive
for the stated small-negative-premium family. The negative outside weight
is still real algebraic information. Turning it into a phase producer
requires extra role release or repeated owner activity, not simply
choosing its partner and claiming that all caps follow from no UE.

## A failed-cap-driven two-joint switch in the corrected-determinant regime

This is an exact falsification of a proposed schedule-switch mechanism,
not a UE counterexample. The complete table below is ALREADY consumed by
the concrete punishment-root source. No additional coverage is claimed.

Use original own singleton levels1 and the full table

| S | r(S) |
|---|---|
| 0 | (1,0,9/10,0) |
| 1 | (2,1,4,0) |
| 2 | (2,0,1,4) |
| 3 | (0,4,0,1) |
| 01 | (11/10,1/2,39/10,−1) |
| 02 | (1,−1,1/2,3) |
| 03 | (1/2,3,−1/10,1/2) |
| 12 | (3,1,11/10,3) |
| 13 | (1,11/10,3,1) |
| 23 | (1,3,1/2,11/10) |
| 012 | (11/10,1/2,3/5,2) |
| 013 | (3/5,3/5,29/10,1/2) |
| 023 | (1/2,2,1/2,3/5) |
| 123 | (2,11/10,11/10,11/10) |
| I | (1,1,1,1) |

Its singleton matrix is the earlier h₂=1/10 regression: R0 of degree1,
determinant31/10 and only offset−1 root
(130/31,40/31,67/31,76/31). The harmful joint03 has η=−1/2,
so its active-origin corrected determinant is−2/5, not positive.
These are exact finite calculations, not assumed no-UE source data.

### Every proper three-row, two-joint pivot0 switch fails

Consider the class in which pivot0 appears with two distinct children
in two joint rows, and the remaining child has a solo row. All five
scheduled hazards are proper; every other hazard is0. Cyclic rotation
does not change the following classification. There are six ordered
choices. Values below are original actual values minus own1.

First note the necessary pivot indifference at any joint0j with child
hazard t:

    V_next,0=t(ξ_j−Γ₀ⱼ)/(1−t),

while the pivot's current forced-Quit value is ξ_j t.
Here(ξ₁,ξ₂,ξ₃)=(1/10,0,−1/2), while
(Γ₀₁,Γ₀₂,Γ₀₃)=(1,1,−1).

Both joint01→joint02 and joint02→joint01 fail immediately:
the earlier favorite joint requires a negative next pivot value,
while the next favorite joint's active pivot value is nonnegative.
Joint03→joint02 also fails immediately: the former requires a strictly
positive next pivot value, but the latter's active value is0.

For joint03→joint01→solo2, active pivot indifference at joint01
forces V_C,0=−9t/[10(1−t)]<0. But at solo2 the pivot's forced
Quit value is0 because r₀(02)=r₀(0)=1. Its ACTUAL passive test fails.

For joint01→joint03→solo2, let p,t be the first row's pivot/child1
hazards and q the next row's pivot hazard. Child3's active value in
the next row is−q/2. At the first row its actual Continue value is

    V_A,3=−p−t−q(1−p)(1−t)/2,

whereas its forced Quit value is−p/2, because both03 and013 pay it1/2
and13 pays its own1. Its Quit-minus-Continue gap is

    p/2+t+q(1−p)(1−t)/2>0.

Thus adding the pivot to the failed-cap row merely creates an earlier
profitable Quit for a DIFFERENT child, for every proper vector.

The remaining word joint02→joint03→solo1 cannot even satisfy all five
active equations. Write p,x for its first-row pivot/child2 hazards,
q,y for its second-row pivot/child3 hazards and z for its solo1 hazard.
The pivot equations give

    V_A,0=0, V_B,0=−y/2, V_C,0=z,
    x=y/(2+y), z=y/[2(1−y)], 0<y<2/3.               (W1)

Child1 is active only in the solo row, hence V_C,1=V_A,1=0.
Its B value is3y−q, so its A recursion forces

    q=3y−(p+x)/[(1−p)(1−x)].                       (W2)

Child3's active B value is−q/2. Its A recursion and(W2) give

    V_A,3=−p+3x−q(1−p)(1−x)/2
         =[y/2+p(5y/2−1)]/(2+y),
    V_C,3=−z+(1−z)V_A,3.                           (W3)

If y<2/5, then V_A,3<y/[2(2+y)] and(W1) implies V_C,3<0.
If y≥2/5, discard the negative terms in the first expression of(W3):
V_A,3<3x, and

    V_C,3<−z+3x(1−z)
          =y(4−10y)/[2(1−y)(2+y)]≤0.

But active child3 indifference at B requires
V_C,3=q/[2(1−q)]>0, a contradiction.

This exhausts all six ordered partner choices in this strategy class.
It does not exclude sure boundaries, additional phases, different
repeated owners, nonpivot joint rows or approximate rather than exact
periodic policies. It is not a general finite-calendar impossibility.

### The actual old source already consumes this test table

Every participant reward is at least1/2. Each player's complete
punishment value equals1/2: immediate Quit guarantees it; sure3 caps
players0,2, and sure0 caps players1,3 at1/2, with passive reward0.
These are actual all-behavior opponent strategies, not stationary-Never
surrogates.

At continuation(1/2,1/2,1/2,1/2) the exact product root

    (q₀,q₁,q₂,q₃)=(1,0,5/29,2/5)

has owner gaps

    (8/29, −23/50, 0, 0).

The quiet-coordinate sign is correct for player1; players2,3 are proper
and indifferent; player0 is sure and its gap is positive.
For direct calculation, player2's gap is−2/5+q₃;
player3's is1/2−(29/10)q₂. At their displayed values player1's
gap is−23/50 and the pivot's punishment-tail gap is8/29.

The induced base0 source therefore accepts this table. The exact
inspected general consumer is
quittingPunishmentSureRootTarget_isUniformEquilibriumPayoff_and_floor in
UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterPayoff.lean.
It consumes the actual punishment root with a sure quitter and fixes its
literal initial target before every error request. This is distinct
from a strategy-class absence theorem.

Here even the strategy can be supplied directly: use the displayed root
at date0; after the off-path all-Continue event, prescribe sure3 next
date and all other players Continue. Every deviation except player0's
absorbs at date0. Player0's later responses are capped by1/2 because
sure3 then absorbs. Its date0 Continue payoff is at most76/145,
strictly below its actual target4/5. All complete behavioral replacements,
Never and delayed stopping are thereby covered.

The original target is

    (4/5,149/145,1/2,15/29).

Absorption occurs by date1 against every unilateral replacement, so
original horizon payoffs differ from terminal payoffs by at most2M/N.
The same profile and this target work at all sufficiently large horizons.
The test is thus solved by an existing raw source, not a surviving table.

### Source fences and direction change

The narrow existing no-go inspected is
not_isZeroNash_selfMembershipReward_of_pureContinue in
UniformEquilibrium/Diagnostics/Quitting/CyclicKofNFeasibilityObstruction.lean:
a prescribed pure-Continue role with strict opponent absorption can be
intrinsically infeasible even in an already solved game. It does not
supply this table's six-word exclusion or exclude arbitrary schedules.

The inspected phase-switch consumer
quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le in
UniformEquilibrium/Quitting/Cycles/PhaseSwitchDeviationCap.lean requires
an ACTUAL truncated-plan cap and an ACTUAL punishment-response cap.
It does not turn a profitable passive action into such a source.

The attempted adjacent-role switch is now falsified rather than repaired
with another assumed cap bill. The negative corrected determinant test
also hits an existing sure-root consumer, so it supplies no new class.
The next global route should address actual continuation selection beyond
a fixed short-word inventory; the minimum-debt/ordered-clock representation
is a candidate, with tied atoms, Never and uniform pure-response control
kept explicit rather than treated as harmless compactness details.

## Exact entropy near-minimizers still need collision marks

This finite test uses a DIFFERENT game from the preceding table. Four
players have the common reward

    r_i(S)=1 if |S|=1, and r_i(S)=0 otherwise,
    r_i(∅)=0.

All terminal rewards lie in[0,1]. Here D denotes the SUM of the four
complete behavioral terminal deviation gains. For stopping laws μ_i on
finite dates together with Never, write μ̄=(μ₀+μ₁+μ₂+μ₃)/4 and

    I=Σ_i KL(μ_i‖μ̄).

The all-sure profile at date0 has target0 and D=0: any unilateral
replacement still leaves three sure opponents, so the first quitting
coalition has size at least3. Its four identical laws give I=0.

Alternatively let the four laws be identical and uniform on{1,…,L},
with no Never mass. The unique-minimum probability is exactly

    4 L⁻⁴ Σ_{k=0}^{L−1} k³=(1−1/L)².

Thus every target coordinate is(1−1/L)². Pure Quit at date0 earns1,
and no deviation can earn more than1, so every complete cap is1 and

    D=8/L−4/L²,       I=0.

These are actual η-near minimizers of D+τI for every fixed τ≥0 once
L is large; its global infimum is0. The relative likelihood densities
dμ_i/d(Σ_j μ_j) are identically1/4 for both constructions. Therefore
strong convergence of these densities alone cannot retain the target:
the sure tied atom has target0, whereas the diffuse sequence tends to
target1. This does not refute compactness retaining atom endpoints,
collision marks and the complete tester set. It only refutes their
replacement by relative-density convergence alone.

## An ordered empty-slot variation defeats every one-atom direction

This second test uses four player-indexed rewards

    r_i({i})=1,
    r_i(S)=2 if i∈S and |S|≥2,
    r_i(S)=0 if i∉S,
    r_i(∅)=0.                                           (M1)

The all-Never profile has payoff0, complete cap1 in each coordinate,
D=4 and I=0. It is not a global minimum: sure-all is an exact terminal
Nash profile with target2. The question is instead whether legal
variations inserting only one formerly empty simultaneous date can
detect debt descent.

### Every sufficiently small one-date insertion raises the objective

Give player i probability q_i of Quit at one new common date and
probability1−q_i of Never. Let O_i=Π_{j≠i}(1−q_j).
Its immediate Quit value is2−O_i. Any earlier tester earns1; any later
tester earns O_i, because a preceding opponent coalition pays player i
zero. Never earns0. Hence the COMPLETE cap is2−O_i, and the actual
payoff is q_i(2−O_i). Consequently

    D=8−2Σ_i q_i−4Π_i(1−q_i).

Set s=Σ_i q_i. The Bonferroni bound
1−Π_i(1−q_i)≥s−Σ_{i<j}q_iq_j≥s−s²/2 gives

    D−4≥2s(1−s)>0 whenever0<s<1.                       (M2)

This includes all unequal private probabilities, not merely symmetric
ones. Since I≥0, the same strict inequality holds for D+τI for every
τ≥0. Thus the entire small one-atom insertion cone is blocked.

### Three newly ordered dates give actual full-cap descent

For 0<δ≤1, give EVERY player mass a=δ/3 at each of three ordered
finite dates and mass1−δ at Never. All four laws remain identical,
so I=0 exactly. For a pure tester at new date t∈{1,2,3}, its payoff is

    Q_t=2[1−(t−1)a]³−[1−ta]³.                          (M3)

An opponent quitting earlier pays zero. Conditional on no earlier
opponent quit, a tie pays2 and no tie pays1; this proves(M3).
Earlier testers earn1, testers strictly between dates have no tie and
earn the corresponding opponent survival cube, late testers earn
(1−δ)³, and Never earns0. The displayed Q_t decrease in t: writing
x=1−(t−1)a≥a,

    Q_t=x³+3ax²−3a²x+a³,
    dQ_t/dx=3x²+6ax−3a²>0.

Thus the exact full cap is Q₁=2−(1−a)³. The actual payoff is
U=a(Q₁+Q₂+Q₃). Direct polynomial expansion gives

    D−4=−4δ²(6δ²−13δ+9)/27<0.                          (M4)

Indeed the quadratic is positive on the whole real line, since its
leading coefficient is positive and its discriminant is−47.
For instance δ=1/4 gives D−4=−49/864.
All complete behavioral replacements are included: along the unique
live all-Continue history, a replacement selects a distribution over
pure stopping dates and Never. Its payoff is a convex average of the
pure values just bounded. No bounded-controller restriction is used.

This is a concrete consumed legal microcalendar variation, not just
transport of a supplied signed measure. All new dates lie in an empty
old calendar, so no hidden positive old atom or newly available old
response has been declared free. The old earlier, intermediate, late
and Never tests were checked explicitly. Several ordered private
clocks can therefore lower D+τI even though all simultaneous single-
atom directions raise it. The descent is second order inδ; the first-
order one-atom variational inequalities do not encode it.

### Scope and next question

Neither test supplies a positive GLOBAL minimum or a new counterexample
class. Both games already have exact sure equilibria. The first test
rules out density-only payoff continuity at actual near-minimizers.
The second rules out a local-descent/completeness inference from
one-atom insertions, even when entropy does not change. It does not
refute a marked-calendar compactness theorem or transport retaining
all tester marks, and it does not prove that every nonminimum profile
has an ordered-slot descent.

The next concrete question is to insert an ordered microcalendar after
the last finite atom of an ACTUAL positive-gap source, shifting only
its Never masses. Track each owner's literal late-response cap and
the full survival factor. Can the no-UE source conditions force
descent there, or can an exact signed table block every such tail
insertion? A nominal continuation value or a co-located signed-atom
direction is not a substitute for that complete test.
