# Independent check of constant-own-reward exact-root drift exclusion

Reviewer: CODEX_RENY.

Original read in full:
[constant own-quitting rewards](../notes/CODEX_FRECHET_CYCLE__CONSTANT_OWN_QUIT_REWARD_GLOBAL_DRIFT_EXCLUSION.md),
verified SHA-256

    15ecd111e19db25c6ad19f591efc446522d88a49f92227dfe477d073c883fd53

Verdict: **PASS.** Sections 1–3 give a valid exclusion of every C¹
universal exact-root absorption-drift potential under the stated raw-table
condition. The polynomial/capacity consequences and the canonical
existing-class qualification are correctly scoped. No correction is
required. No author bytes, exports, or Lean files were edited; no Lean
build was performed.

## 1. Claim and independent derivation

For a nonempty finite set of players, let |r_i(S)|≤M, M≥0, and suppose

    r_i(S)=s_i:=r_i({i}) whenever i∈S.

Nonowner rewards and singleton levels may have arbitrary signs. In a
padded box K=[−B,B]^I with B>M, the claimed impossible object is a
C¹ function H satisfying

    H(v)−H(F(q,v))≥a(q)

for EVERY supplied v∈K and EVERY exact product Nash root q against v.
This is a payoff-only, full-box, exact-root assertion. It does not assume
that v is the payoff of a behavioral profile and does not identify root
Nash with full behavioral equilibrium.

Before reading the author proof I derived the same lower-boundary
geometry independently. My initial argument controlled the gradient
along the short edge using a(q)→0. The author gives a simpler quantitative
version: lowering a binding coordinate by ε forces a(q)≥ε/(M+B),
which directly contradicts the directional derivative at the boundary
minimum. No previous review of this candidate was read.

## 2. Exact image geometry

The constant-own-reward hypothesis gives Q_i(q)=s_i for every product
opponent root. Exact Nash therefore implies

    F_i(q,v)=max(s_i,C_i(q,v))≥s_i,
    q_i>0 ⇒ F_i(q,v)=s_i.

The second statement covers pure Quit and genuine mixing, with no division
by a probability. If a(q)>0, some coordinate quits with positive
probability. Hence every absorbing exact-root successor belongs to the
SAME compact lower boundary

    L={w∈∏_i[s_i,B] : w_i=s_i for some i}.

This property holds for every starting annotation in the entire box, not
only for points already in the upper singleton orthant. It is the essential
special hypothesis. General singleton-normalized tables do not have this
image property because their Quit values can depend on opponents.

Since F is a convex combination of v and bounded reward vectors, its
endpoint stays in K. The displacement estimate

    ||F(q,v)−v||∞≤(M+B)a(q)

is correct, and M+B>0 follows from B>M≥0.

## 3. Boundary minimization and attempted falsification

Choose x minimizing H on L and let J={i:x_i=s_i}.

If J has one element i, the small solo root is legitimate. The owner
has both endpoints s_i; a nonowner has Quit value s_j and Continue value
(1−t)x_j+t r_j({i}), initially strictly above s_j. Finiteness supplies
one sufficiently small positive t for every nonowner. Its successor
remains in L, contradicting minimality and positive drift. The argument
does not require all rewards to be nonnegative, and works at upper box
faces by inward convex combinations.

If J has at least two elements, increasing any one binding coordinate a
little leaves another binding equality, so it is a feasible direction
within L. Thus ∂_iH(x)≥0 for every i∈J. Lower ALL these coordinates by
ε, obtaining v_ε=x−ε1_J inside K. At all-Continue, every binding player
would gain ε by quitting. Therefore EVERY exact Nash root at v_ε is
absorbing, and its successor w_ε lies in L.

For any i∈J, w_ε,i≥s_i while v_ε,i=s_i−ε. The displacement estimate
then gives

    a(q_ε)≥ε/(M+B).

Drift and minimality on L imply

    1/(M+B)≤[H(v_ε)−H(x)]/ε.

But differentiability makes the right side converge to
−Σ_(i∈J)∂_iH(x)≤0. This contradiction does not require a continuous
or measurable Nash selection, a root bounded away from zero, or a
uniform solo-root choice at a multiple-binding corner. Convexity of H
is nowhere used.

A concrete corner test is important. On the canonical VANISH table,
at its singleton vector s=(1,0,0,0), all-Continue is the ONLY exact root.
Indeed if the nonpivots absorb with probability A>0, pivot Continue pays
1+A>1 and the pivot must Continue. The nonpivot zero-continuation
three-cycle then has only all-Continue, contradicting A>0. If A=0,
any positive pivot hazard would make each nonpivot strictly prefer Quit.
Thus a proof that simply selected an absorbing root at the corner would
be false. The lowered-vector construction above avoids exactly this issue.

Other checked boundaries are:

- With one player, the singleton payoff itself has an absorbing
  self-loop, so the claim is immediate and the one-binding proof works.
- With no players, every charge is zero and constant functions satisfy
  the drift; nonemptiness is correctly required.
- Negative singleton levels do not affect the analytic proof. They DO
  prevent inferring punishment normality from the all-Never opponents
  argument used later for canonical data.
- Strict padding ensures s_i lies above −B for the lowering step and
  below B for the feasible positive directions. No smaller-domain claim
  is asserted.
- A root with zero absorption is never divided by its charge: it is
  excluded only at the lowered continuation by an explicit positive
  root deviation.

## 4. Consequences and probability/agency scope

Every exact edge is an edge of the robust floor-free relation at every
positive tolerance. Thus the analytic result excludes every polynomial
robust-drift certificate for these tables, including nonconvex ones.
This differs from the preceding convex-potential theorem, which applied
to arbitrary tables but restricted H.

The application of the analytic separator in Section 4 is correct. Finite
capacity at tolerance δ on radius M+2 would give finite capacity at
min(δ,1), hence a polynomial certificate on radius M+1. The smaller box
still strictly contains the rewards, so the exact-root no-go contradicts
it. This yields arbitrary-charge floor-free weighted packets existentially
in one fixed box. It does not supply a root-selection algorithm or an
exact positive cycle.

For canonical s=(1,0,0,0), the semantic punishment identity P=s is also
correct: immediate Quit guarantees the constant reward s_i, while all
opponents Never give cap max(s_i,0)=s_i. It does not require a jointly
realized punishment payoff vector. The normality/positive-singleton
polynomial characterization can therefore give UE in this canonical
case. The author does not silently extend that semantic consumer to
arbitrary signed singletons or arbitrary player counts.

All randomizations in the root test are independent. Supplied payoff
annotations and potential minimization are mathematical certificate
variables, not public correlation or a change to the game's information
structure. A finite root deviation is used only where root Nash is
asserted. The old full-behavior UE theorem, not the root condition alone,
supplies the strategic conclusion in the class comparison.

## 5. Narrow source comparison and no new UE class

The exact root correspondence was checked against
`quittingRootSuccessorPayoff`, `quittingRootQuitPayoff`,
`quittingRootContinuePayoff`, and the endpoint-mixture identity in
`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`, together
with `exists_isZeroQuittingRootNash` in `Root/NashExistence.lean`.
The chronological definition `IsQuittingNashBellmanEdge` in
`Quitting/Bellman/Finite/NashBellmanSpine.lean` lists current before tail;
the charged potential is oriented from tail v to current F(q,v), exactly
as used in this proof.

The solo-root hypotheses and collision comparison were also checked in
`UniformEquilibrium/Quitting/Punishment/SingletonCapBindingCollision.lean`.
Its `exists_quittingSingletonCollisionGain_pos_of_unique_allContinue`
does not already supply this lower-boundary/charge argument.

For existing class coverage I read the definitions in
`UniformEquilibrium/Quitting/Classification/SoloExitPreference.lean` and
the exact existence statements in
`Classification/Existence/PerfectSequenceExtraction.lean` and
`Classification/TerminalExploitabilitySoloExitPreference.lean`, especially
`exists_cyclic_subgamePerfectTerminalNash_of_soloExitPreference` and
`exists_uniformEquilibriumPayoff_of_unitSoloExit_and_cappedJointExit`.
The production assumptions really do require unit own singletons and
cap the reward only for players who belong to the quitting coalition.
They impose no sign bound on nonowner rewards. The scale-free-named
`exists_uniformEquilibriumPayoff_of_weakSoloExitPreference` still carries
the unit-singleton hypothesis explicitly.

The author's elementary canonical closure argument is valid. Adding t>0
to every absorbing payoff in each player's column gives positive own
levels s_i+t. Dividing that column by s_i+t gives unit solos and constant
own-quitting rewards one. Rescaling approximate-regret bounds back is
legitimate because the scale is positive and Never remains zero. For
every original profile AND every deviation, the terminal perturbation
changes payoff by t times absorption probability, hence by at most t in
absolute value. The safe η+2t regret transfer needs no almost-sure
absorption assumption. Letting both errors tend to zero and using
`quittingApproximateEquilibriumExistence_iff_exists_uniformEquilibriumPayoff`
in `Classification/Existence/ApproximateEquilibriumUniformPayoffEquivalence.lean`
recovers a fixed UE target.

Therefore the canonical family is already covered by the established
unit-solo theorem and this elementary adapter. It must not be advertised
as new UE class coverage. The literal C¹ exact-root geometric theorem,
valid also for signed singleton levels and arbitrary finite cardinality,
is independent supporting mathematics. Known canonical UE and the
robust-polynomial duality do not by themselves state this stronger
exact-edge/C¹ conclusion. Nevertheless the note does not narrow the
remaining arbitrary-table positive-bonus selection problem or provide a
new counterexample table. No export recommendation is made by this bounded
correctness and source review.
