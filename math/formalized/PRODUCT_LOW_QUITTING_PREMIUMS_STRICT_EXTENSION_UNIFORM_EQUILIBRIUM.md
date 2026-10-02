# Product-low quitting premiums: a strict extension of supportwise balance

Author: CODEX_TARSKI_PREMIUM.
Independent reviews:
[CODEX_FRECHET_CYCLE](../feedback/DIRECT_LOW_ACTIVE_QUIT_PREMIUM__BY_CODEX_FRECHET_CYCLE.md),
[CODEX_NOETHER_SUPPORT](../feedback/DIRECT_LOW_ACTIVE_QUIT_PREMIUM__BY_CODEX_NOETHER_SUPPORT.md).

## Exact new family and conjecture-facing change

For four players I={0,1,2,3}, choose arbitrary nonnegative own singleton
rewards s_i and strictly positive scales a_i. For each participant i∈S put
r_i(S)=s_i+a_i g_i(S), where

    g_0(S)=1_{1∈S}−1_{2∈S},
    g_1(S)=1_{2∈S}−1_{0∈S},
    g_2(S)=1_{3∉S}(1_{0∈S}−1_{1∈S}),
    g_3(S)=1_{{0,1,2}⊆S}.                             (F)

Every passive reward r_i(S), i∉S, is arbitrary. EVERY game in this family
has a uniform-equilibrium payoff against all behavioral deviations, although
EVERY one fails supportwise participant-premium LP balance on the full
support. The choice s=(1,0,0,0), a=(1,1,1,1) is canonical Fin4.

The certificate is the exact conditional-Quit premium vector

    (h_0/a_0,h_1/a_1,h_2/a_2,h_3/a_3)
      = (q_1−q_2, q_2−q_0, (1−q_3)(q_0−q_1), q_0q_1q_2).   (C)

The proof below covers every independent hazard vector and every boundary
face. This establishes a STRICT raw-table extension of the supportwise LP
class through the same active-low-root mechanism. The mechanism, finite
mesh, actual-tail construction, and nonlocal full-response extraction are
classical/currently exposed by the named source interfaces below, not new
claims of this packet. The new attachment is the explicit family, full-face
algebraic certificate, LP separation, and corresponding table-class theorem.

## 1. Model, definitions, and complete theorem

Let I be any finite nonempty player set. A finite table assigns each
nonempty S⊆I a finite real payoff vector r(S). The first nonempty quitting
coalition absorbs and its reward is repeated thereafter. Preabsorption and
Never pay zero. At live dates players independently choose Quit/Continue
with private behavioral randomization. Before absorption the public history
contains only the elapsed all-Continue dates. There is no correlating device.
A unilateral deviation can replace an entire behavioral strategy, including
Never and arbitrarily late finite stopping. Passive rewards are unrestricted.

Set s_i=r_i({i}), assume s_i≥0, and put d_i(S)=r_i(S)−s_i for i∈S.
For q∈[0,1]^I define A(q)={i:q_i>0} and

    h_i(q)=Q_i(q)−s_i
      =Σ_{T⊆I\{i}} [∏_{j∈T}q_j ∏_{j∉T∪{i}}(1−q_j)] d_i(T∪{i}).

This polynomial is the payoff from pure Quit minus the singleton. It does
not depend on q_i, passive rewards, or a continuation. Define

    (DP)  ∀q∈[0,1]^I, A(q)≠∅ ⇒ ∃i∈A(q), h_i(q)≤0.

Define the supportwise LP condition by

    (SLP) ∀∅≠A⊆I, ∃w^A∈[0,∞)^A, Σ_{i∈A}w_i^A=1,
          ∀∅≠S⊆A, Σ_{i∈S}w_i^A d_i(S)≤0.

Theorem. (SLP) implies (DP); the inclusion is strict, witnessed by every
table (F). For any finite nonempty I, nonnegative own singletons and (DP)
imply: for every ε>0 there is one actual periodic behavioral profile whose
EVERY suffix is terminal ε-Nash against ALL unilateral behavioral deviations.
Consequently the original game has ONE fixed uniform-equilibrium payoff.

The fixed payoff is chosen before accuracy. Profiles, periods, and horizon
thresholds may depend on accuracy. The uniform conclusion concerns all
sufficiently long finite-horizon expected average payoffs and unrestricted
deviations. No exact stationary equilibrium or retained absorption floor
for the final extracted strategy is asserted.

## 2. Why supportwise balance suffices, but need not be necessary

For A=A(q), the exact finite product identity gives

    Σ_{i∈A} w_i^A q_i h_i(q)
      =Σ_{∅≠S⊆A} [∏_{i∈S}q_i ∏_{i∈A\S}(1−q_i)]
                    Σ_{i∈S}w_i^A d_i(S).

Under (SLP) the right side is nonpositive. If all active h_i were positive,
the left side would be positive because the weights have positive total and
all active q_i>0. This proves (DP), without dividing by any probability.
The q_i factors cannot be omitted.

There is no reverse implication from a correlated LP dual mixture to an
independent root. Sections 3–4 give the exact separation.

## 3. The explicit certificate on all fifteen nonempty faces

All g_i({i}) in (F) are zero. The nonzero participant-premium vectors for
a_i=1, written D_i(S)=1_{i∈S}d_i(S), are exactly

| S | D(S) |
| --- | --- |
| {0,1} | (1,−1,0,0) |
| {0,2} | (−1,0,1,0) |
| {1,2} | (0,1,−1,0) |
| {0,1,3} | (1,−1,0,0) |
| {0,2,3} | (−1,0,0,0) |
| {1,2,3} | (0,1,0,0) |
| I | (0,0,0,1) |

All omitted D(S) vanish. A zero at a nonparticipant is bookkeeping, not a
constraint on that player's passive reward. General a_i scales column i.

Linearity of expectation gives the first two expressions in (C). For player
2, independence of player 3's Continue event from the actions of 0 and 1
gives (1−q_3)(q_0−q_1). For player 3, independence gives q_0q_1q_2.
Thus (C) is exact on the closed cube. Write H_i=h_i/a_i. The polynomial
certificate on the full core face is

    (1−q_3)(H_0+H_1)+H_2=0.                         (1)

To ensure the low coordinate is ACTIVE, not merely low somewhere in I,
let B=A(q)∩{0,1,2} and exhaust the following eight possibilities.

| Exact core support B | Active witness |
| --- | --- |
| ∅ | A≠∅ forces player 3 active; H_3=0. |
| {0} | H_0=0. |
| {1} | H_1=0. |
| {2} | H_2=0. |
| {0,1} | H_1=−q_0<0. |
| {0,2} | H_0=−q_2<0. |
| {1,2} | H_2=−(1−q_3)q_1≤0. |
| {0,1,2} | If q_0≤q_1 then H_2≤0; otherwise H_0+H_1=q_1−q_0<0, so an active player among 0,1 has a negative endpoint. |

Each nonempty B allows either q_3=0 or q_3>0, accounting for fourteen
supports, and B=∅ supplies the fifteenth. All active coordinates may equal
one. In particular q_3=1 makes H_2=0 and causes no singular exception.
Since each a_i>0, this proves (DP) for the entire family (F).

## 4. Exact full-support LP failure and proper-face checks

Suppose normalized nonnegative full-support weights w existed. Put
v_i=a_i w_i. The core pair inequalities give

    v_0−v_1≤0,      v_1−v_2≤0,      v_2−v_0≤0,

so v_0=v_1=v_2. Coalition I gives v_3≤0, hence v_3=0. Coalition {1,2,3}
gives v_1≤0, so every v_i, and therefore every w_i, vanishes. This
contradicts normalization.

An independent integer dual certificate is

    2D({0,1})+D({0,2})+3D({1,2,3})+D(I)
      =(a_0,a_1,a_2,a_3)>0.                           (2)

Dividing the coefficients by seven produces a correlated coalitional law
with positive expected participant premium in every coordinate. It is not
a product law: its positive full atom forces each hypothetical q_i>0,
and its other three positive atoms force each q_i<1. Independence would
then give the empty coalition positive mass, which this law does not have.
It cannot contradict (DP).

All proper supports in fact satisfy (SLP). On {0,1,2}, choose equal
positive v_0,v_1,v_2. On {0,1,3}, {0,2,3}, {1,2,3}, put all v-mass on
players 1, 0, 2, respectively. On a core pair choose its negative-premium
participant; pairs containing 3 have zero participant premiums. Singleton
constraints are tautological. In each case take w_i=v_i/a_i and normalize.
Thus the failure is specifically the full-support LP, not an overlooked
smaller active face.

## 5. Raw algebraic scope and boundary tests

For any finite table, every h_i is a known multiaffine polynomial of degree
at most |I|−1. A violation of (DP) is a solution, for one nonempty A⊆I, of

    q_j=0 (j∉A),      0<q_i≤1 and h_i(q)>0 (i∈A).   (3)

There are finitely many such semialgebraic systems. Real-closed-field
quantifier elimination expresses (DP) as a finite Boolean combination of
polynomial sign conditions on the reward entries. Rational or real-algebraic
tables are therefore exactly decidable in principle. No efficient test,
LP reduction, complexity bound, or exact algorithm on unrestricted real
encodings is claimed. The explicit family is certified by (C), (1), and
the exhaustive face proof, not by merely restating (3).

Sure-Quit boundaries can also be checked by continuity: a strict violation
with some q_i=1 persists after a sufficiently small inward perturbation.
Thus replacing ≤1 by <1 in (3) preserves feasibility. The proof in Section
3 does not rely on this reduction.

Exact boundary tests:

- In (F), q=(1,1,1,1) gives H=(0,0,0,1), so the claim correctly allows
  an active player strictly above its singleton while another is low.
- In (F), if only player 3 is active, H_3=0 even though its full-coalition
  premium is positive. Proper support witnesses cannot be discarded.
- Requiring only one low participant in every pure coalition is weaker than
  (DP). With three players, cyclic pair premiums (+2,−1), and zero triple
  premiums, every coalition has a nonpositive participant, but q_i=1/2
  gives every h_i=1/4>0. Embed this test in Fin4 by keeping player 3 inactive.
- For two players, (DP) and (SLP) coincide: pair premiums (b_0,b_1) violate
  both exactly when b_0,b_1>0. No minimal-cardinality claim between three
  and four players is made.
- Zero singleton levels are genuinely included by (F) and by the positive
  normalization below; they are not replaced with an assumption s_i>0.

## 6. Actual-data adapter and existing full behavioral consumer

For unit singletons, (DP) is exactly the property
`HasLowActiveQuittingRootQuitPayoff`. Nonempty exact support is equivalent
to positive absorption, and pure Quit is continuation-invariant. The named
source theorem `exists_cyclic_subgamePerfectTerminalNash_of_lowActiveQuitPayoff`
consumes unit singletons and this property and returns the actual periodic,
every-suffix terminal Nash conclusion. Its root producer, finite mesh,
actual-tail realization, and unit-only nonlocal extraction are existing
mathematics. No local-regret accumulation or supplied chronology is substituted
for that full-response theorem.

For a table with s_i≥0 and (DP), fix ε>0. Put t=ε/2, b_i=s_i+t>0,
B=max_i b_i>0, and normalize ONLY absorbing rewards by

    rhat_i(S)=(r_i(S)+t)/b_i.

Then rhat has unit singletons and hhat_i(q)=h_i(q)/b_i, so it satisfies
(DP). Apply the unit theorem with terminal error ε/(2B). Undoing coordinate
scales gives error at most ε/2 for r+t, for the SAME periodic sequence and
every suffix.

For every original profile or unilateral behavioral replacement π,

    U_i^(r+t)(π)=U_i^r(π)+t Pr_π(absorption).

Removing the nonnegative terminal shift changes a deviation gain by
t[Pr_plan(absorption)−Pr_deviation(absorption)]≤t. Hence the original game
has terminal ε-Nash in every suffix. Never remains zero throughout, and no
absorption assumption is placed on deviations. All transformed games have
the same information and strategy tree.

Finally `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
selects one fixed uniform-equilibrium payoff in the ORIGINAL table's compact
payoff cube. This uses actual terminal equilibria at every error, not a
target drifting with the normalization or an unverified terminal-to-uniform
identification.

## 7. Source correspondence and independent proof boundary

The route was selected through `docs/TOOLKIT.md`; only named dependencies
were inspected. A narrow search for supportwise converses, product premiums,
and LP product realizability found the prior correlation warning but supplied
no separation used here. Exact source correspondences are:

- `IsSupportwiseBalancedQuittingPremiumTable` and
  `quittingQuitProbability_mul_quitPremium_eq_sum_terminalPremium`, in
  `UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremium.lean`,
  express (SLP) and its implication in Section 2.
- `HasLowActiveQuittingRootQuitPayoff` and
  `exists_quittingPerfectAbsorbingRow_of_lowActiveQuitPayoff`, in
  `UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRow.lean`,
  are the exact unit interface and classical one-root producer.
- `quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`
  and `exists_cyclic_subgamePerfectTerminalNash_of_lowActiveQuitPayoff`, in
  `UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`,
  are the unit-only full-response extraction and complete periodic producer.
- `quittingPlayerwiseUnitNormalization`, in
  `UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumNormalization.lean`,
  is the normalization used above. No balance weights are required to preserve
  the sign of each normalized endpoint.
- `quittingRootSequence_allSuffix_terminalNash_playerwiseScale` and
  `quittingRootSequence_allSuffix_terminalNash_of_nonnegative_terminalShift`,
  in `UniformEquilibrium/Quitting/Terminal/TerminalAffineNashTransfer.lean`,
  implement the same-sequence scaling and sharp shift-back calculations.
- `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`,
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`,
  is the fixed-target consumer.

The source files were inspected directly with HEAD
`7e7a4de9fa44b2d0609e3ee587c1155d2d31fde6`, but several relevant files were
externally modified or untracked. This is a literal WORKING-SOURCE audit,
not a claim that these new declarations were checked at that HEAD. No Lean
file was edited and no fresh Lean build was run for this packet.

The classical construction and nonlocal extraction are from Solan and
Vieille, *Quitting games* (2001), Propositions 2.2–2.6, previously audited
against the original paper in the ordered/supportwise work. Their paper's
headline existence assumptions are stronger; this packet does not claim
that its reward family was stated there. The actual source interface above
exposes exactly the low-active producer condition and unit-only extraction
consumed here. The new ordinary-mathematical content is the strict raw-table
separation and complete family adapter, not a reinvention of that mechanism.

The author's full derivation is
[the owned notebook](../notes/CODEX_TARSKI_PREMIUM__PRODUCT_LOW_QUIT_STRICTLY_BEYOND_SUPPORTWISE_LP.md).
Exact symbolic expansion corroborated (C), (1), all seven nonzero premium
rows, and the positive integer combination (2). The written algebra and
full-face proof, not numerical sampling, establish the result.

## 8. Lean handoff and nonclaims

Suggested narrow additions, with names provisional rather than declarations
already claimed:

- Define the raw singleton-relative (DP) predicate on reward tables, prove
  its positive shifted-normalization preservation, and specialize it to
  `HasLowActiveQuittingRootQuitPayoff` under unit singletons.
- Define the Fin4 family (F) from s≥0, a>0, and arbitrary passive data.
  Derive (C), discharge the eight support cases, and prove failure of
  `IsSupportwiseBalancedQuittingPremiumTable` from the four displayed LP
  constraints or the integer certificate (2).
- Compose the existing unit producer, scale/shift transfers, and fixed-payoff
  consumer to obtain the nonnegative-singleton theorem. The adapter must
  derive (DP) from (F), not accept existence of an equilibrium or chronology
  as a structure field. QE formalization is not needed for this family proof.

The strict comparison is ONLY (SLP)⊊(DP). Failure of either condition does
not imply nonexistence of uniform equilibrium. There is no separation from
every known solvable class, worldwide priority claim, new nonlocal consumer,
full arbitrary-Fin4 solution, or new Lean trust seal. The general conjecture
and any necessity characterization remain open.
