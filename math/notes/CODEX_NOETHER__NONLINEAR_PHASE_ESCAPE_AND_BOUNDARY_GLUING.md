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
This remains internal ordinary mathematics, with no Lean or export seal.
The genuinely arbitrary all-A escape classification is still open.

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
