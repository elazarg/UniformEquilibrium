# Product-low Quit premiums strictly exceed the supportwise LP class

Author: CODEX_TARSKI_PREMIUM.

Status: proved ordinary mathematics, pending independent review. An exact
four-player family satisfies the active-low condition at EVERY independent
product root but fails the supportwise participant-premium LP. The family
allows arbitrary passive rewards, arbitrary nonnegative singleton rewards,
and arbitrary positive coordinate scales. A canonical Fin4 member has own
singletons (1,0,0,0). No Lean build, export, literature-priority claim, or
arbitrary-game uniform-equilibrium claim is made here.

The new point is the strict raw-table separation and its short algebraic
certificate. The active-low-root consumer is already present in the external
working sources and is classical in mechanism; it is not a new extraction
argument. This note does not resume the stopped finite-menu recutting route.

## 1. Exact finite data and the two conditions

Let I be finite and nonempty. At each live date players independently choose
Quit or Continue. The first nonempty quitting coalition S gives every player
i the real absorbing reward r_i(S); preabsorption and Never pay zero.
Information and deviations are those of the usual behavioral quitting game:
no correlation device is added, and unilateral replacements include all
behavioral stopping laws, finite dates, and Never. Set

    s_i = r_i({i}),
    d_i(S) = r_i(S)−s_i                       for i∈S,
    D_i(S) = 1_{i∈S} d_i(S).

The participant-premium conditions concern only d_i(S) for participants.
Rewards to i∉S remain entirely unrestricted.

For a product hazard vector q∈[0,1]^I define its exact active set and the
conditional pure-Quit premium by

    A(q) = {i:q_i>0},
    h_i(q) = Q_i(q)−s_i
           = Σ_{T⊆I\{i}} [∏_{j∈T}q_j ∏_{j∉T∪{i}}(1−q_j)] d_i(T∪{i}).

Thus h_i does not depend on q_i, any continuation vector, passive rewards,
or a Nash condition. Consider the direct product condition

    (DP)  ∀q∈[0,1]^I, A(q)≠∅ ⇒ ∃i∈A(q), h_i(q)≤0.

The supportwise LP condition is

    (SLP) ∀∅≠A⊆I, ∃w^A∈[0,∞)^A, Σ_{i∈A}w_i^A=1,
          ∀∅≠S⊆A, Σ_{i∈S}w_i^A d_i(S)≤0.

These are raw-table predicates. In particular, (DP) quantifies over EVERY
product root, not merely a selected equilibrium root against a continuation.

Proposition 1. (SLP) implies (DP), but the converse is false for Fin4.

The implication is the exact product identity. For A=A(q), its LP weights
give

    Σ_{i∈A}w_i^A q_i h_i(q)
      = Σ_{∅≠S⊆A} [∏_{i∈S}q_i ∏_{i∈A\S}(1−q_i)]
                     Σ_{i∈S}w_i^A d_i(S)
      ≤ 0.

If all active h_i were positive, at least one left term would be strictly
positive and all would be nonnegative. The q_i factors are essential.
There is no division, so q_i=1 is included.

## 2. Exact separating table family

Take I={0,1,2,3}, choose ANY s_i≥0 and ANY a_i>0. For each participant
i∈S prescribe r_i(S)=s_i+a_i g_i(S), where

    g_0(S) = 1_{1∈S}−1_{2∈S},
    g_1(S) = 1_{2∈S}−1_{0∈S},
    g_2(S) = 1_{3∉S}(1_{0∈S}−1_{1∈S}),
    g_3(S) = 1_{{0,1,2}⊆S}.

Every g_i({i}) is zero, so the actual singleton rewards are exactly s_i.
For EVERY nonparticipant i∉S choose r_i(S) arbitrarily and independently
of these prescriptions. This completely specifies a family of finite games.

For a_i=1 the nonzero participant-premium vectors D(S) are precisely:

| S | D_0(S) | D_1(S) | D_2(S) | D_3(S) |
| --- | ---: | ---: | ---: | ---: |
| {0,1} | 1 | −1 | 0 | 0 |
| {0,2} | −1 | 0 | 1 | 0 |
| {1,2} | 0 | 1 | −1 | 0 |
| {0,1,3} | 1 | −1 | 0 | 0 |
| {0,2,3} | −1 | 0 | 0 | 0 |
| {1,2,3} | 0 | 1 | 0 | 0 |
| {0,1,2,3} | 0 | 0 | 0 | 1 |

All omitted D(S) are zero. Zero entries at nonparticipants are bookkeeping
for D, NOT restrictions on their passive rewards. General a_i multiplies
column i by a_i. Choosing a_i=1 and s=(1,0,0,0) gives the promised exact
canonical Fin4 table, with arbitrary passive completion.

Independence gives the complete endpoint calculation, with H_i=h_i/a_i:

    H_0(q) = q_1−q_2,
    H_1(q) = q_2−q_0,
    H_2(q) = (1−q_3)(q_0−q_1),
    H_3(q) = q_0 q_1 q_2.                              (2)

For example, conditional on player 2 quitting, the event that player 3
continues is independent of the actions of players 0 and 1. Its probability
is 1−q_3, so the expected third prescribed premium is exactly the displayed
product. The other formulas are linearity and the probability that all
three core players quit. No conditional-independence assumption beyond
the stated independent root law is used.

## 3. Full-face proof, including every sure-Quit boundary

Since a_i>0, H_i and h_i have the same sign. Write B=A(q)∩{0,1,2}.
The following exhaustive cases directly prove (DP):

| Exact core support B | An active low endpoint |
| --- | --- |
| ∅ | Nonempty A forces q_3>0; H_3=0. |
| {0} | H_0=0. |
| {1} | H_1=0. |
| {2} | H_2=0. |
| {0,1} | H_1=−q_0<0. |
| {0,2} | H_0=−q_2<0. |
| {1,2} | H_2=−(1−q_3)q_1≤0. |
| {0,1,2} | If q_0≤q_1, then H_2≤0; if q_0>q_1, then H_0+H_1=q_1−q_0<0, so one of the active players 0,1 has a negative endpoint. |

For each nonempty B this proof allows either q_3=0 or 0<q_3≤1, accounting
for all fourteen such exact active sets; B=∅ accounts for A={3}. All other
active probabilities may equal one. In particular q_3=1 simply makes H_2
zero and creates no missing or singular face.

On the full core face the useful algebraic certificate is

    (1−q_3)(H_0+H_1)+H_2 = 0.                         (3)

When q_3<1 all three coefficients are positive. At q_3=1 the positive
coefficient of H_2 remains and H_2=0 directly. The separate support cases
ensure that an inactive coordinate is never accepted as the witness.
This polynomial identity and the eight sign cases, rather than root
sampling or quantified feasibility alone, certify the whole cube.

## 4. Exact failure of the full-support LP

Suppose full-support LP weights w_i≥0 existed and summed to one. Put
v_i=a_i w_i≥0. The three core pair inequalities read

    v_0−v_1≤0,      v_1−v_2≤0,      v_2−v_0≤0,

so v_0=v_1=v_2. The full coalition gives v_3≤0, hence v_3=0. The coalition
{1,2,3} gives v_1≤0, hence all v_i are zero. Since all a_i>0, all w_i are
zero, contradicting normalization. Thus (SLP) fails on A=I for EVERY
member of the displayed arbitrary-passive family.

An independent exact dual certificate makes the correlation issue explicit:

    2D({0,1}) + D({0,2}) + 3D({1,2,3}) + D(I)
      = (a_0,a_1,a_2,a_3) > 0 coordinatewise.          (4)

Dividing the coefficients by seven gives a probability distribution on
coalitions with positive expected participant premium in every coordinate.
It is not a product law. Its four positive-support atoms force every product
parameter, if one existed, to lie strictly between zero and one: the full
atom forces all q_i>0 and the other three atoms show each coordinate is
sometimes absent. A product law would then give the empty coalition positive
mass, whereas this distribution gives it zero. The strict separation is
exactly why LP dual coalitional mixtures cannot be silently identified with
independent roots.

For completeness, no smaller face of this example hides the LP failure.
On {0,1,2}, take v_0=v_1=v_2>0 and v_3=0. On {0,1,3}, {0,2,3}, and
{1,2,3}, respectively put all v-mass on players 1, 0, and 2. Each displayed
choice has nonpositive participant premium on every contained coalition.
On a core pair choose its negative-premium participant; on a pair containing
3 every participant premium is zero; singletons are tautological. Normalize
w_i=v_i/a_i by its positive total. Hence every proper support passes (SLP),
but the full support does not.

## 5. Finite algebraic testability

For any finite raw table, each h_i(q) is a specified multiaffine polynomial
of degree at most |I|−1. For each nonempty A set q_j=0 outside A. A violation
of (DP) is a solution to one of the finitely many systems

    0<q_i≤1 and h_i(q)>0                for every i∈A.  (5)

Thus (DP) is a finite real-closed-field condition on the raw reward entries.
Quantifier elimination expresses it as a finite Boolean combination of
polynomial sign conditions in those entries. For rational or real-algebraic
input tables it is effectively decidable in principle. There is no claim of
a cheap LP test, a specific complexity bound, or exact computation from
arbitrarily encoded real numbers.

One may replace ≤1 in (5) by <1 without changing feasibility: all the strict
endpoint inequalities persist under a sufficiently small perturbation of
any sure-Quit coordinates below one, by continuity. This observation is not
needed in the full-face proof above, which already includes the boundary.

For two players the two criteria do coincide. If the pair premiums are
(b_0,b_1), its two active endpoint premiums are b_0q_1 and b_1q_0. The full
face violates (DP) exactly when both b_i>0, which is exactly when no
nonnegative normalized pair weighting has nonpositive weighted premium.
Singleton faces are automatic. No claim about minimal separating cardinality
three versus four is made here.

## 6. Existing semantic consumer and nonnegative-singleton transport

Corollary. For any finite nonempty I, (DP) together with s_i≥0 gives, at
every ε>0, an actual periodic behavioral profile whose every suffix is
terminal ε-Nash against ALL unilateral behavioral replacements. Consequently
the game has ONE fixed uniform-equilibrium payoff. This applies to every
table in Section 2, including every canonical passive completion.

This corollary composes the already available low-active-root producer with
the following normalization; it does not reconstruct or replace its classical
finite mesh, actual-tail realization, or full-response extraction.

For unit singletons, (DP) is exactly the property named
`HasLowActiveQuittingRootQuitPayoff`: nonempty exact support is equivalent
to positive root absorption, and pure Quit does not read the continuation.
The literal declaration
`exists_cyclic_subgamePerfectTerminalNash_of_lowActiveQuitPayoff` consumes
unit singletons and this property. Its conclusion quantifies over every
suffix of one actual periodic root sequence and over unrestricted behavioral
deviations. It does not merely verify ordinary one-row regret, and it does
not require the caller to supply a chronology, continuation region, or root
sequence. The underlying unit-only nonlocal extraction is classical.

For merely nonnegative singletons, fix ε>0, put t=ε/2 and b_i=s_i+t>0,
and normalize absorbing rewards, but not Never, by

    rhat_i(S) = (r_i(S)+t)/b_i.

The new own singletons are one and hhat_i(q)=h_i(q)/b_i. Thus (DP) is
preserved by positive coordinate scaling, even when some original s_i=0.
Let B=max_i b_i>0. Apply the unit producer at terminal error ε/(2B).
The same periodic strategy against the terminal table r+t then has error
at most ε/2 for every player and suffix.

For EVERY profile π, including any unilateral behavioral replacement,

    U_i^(r+t)(π) = U_i^r(π)+t Pr_π(absorption).

Since both absorption probabilities lie in [0,1], removing the positive
terminal-only shift increases a deviation gain by at most t, not a fixed
constant independent of the profile. The original table therefore has
terminal ε-Nash in every suffix. Never stays zero, and deviations need not
absorb. No division by an original zero singleton occurs.

Finally apply the existing terminal-all-errors fixed-payoff selection theorem
to the ORIGINAL game. The target is chosen once before accuracy; profiles,
periods, and horizon thresholds may depend on accuracy. This last application
does not take a limit of equilibria while forgetting Never or changing the
target game.

## 7. Source audit, exact checks, and scope

A narrow duplicate/no-go search in conference notes, feedback, and questions
for supportwise converses, product premiums, and LP product realizability
found the prior explicit warning that LP duals need not be product laws, but
no existing separation was used. The source route was selected through the
canonical entry points in `docs/TOOLKIT.md`, not a global Lean-tree survey.

Source declarations inspected directly:

- `IsSupportwiseBalancedQuittingPremiumTable`,
  `quittingQuitProbability_mul_quitPremium_eq_sum_terminalPremium`,
  `weighted_quittingRootQuitPremium_sum_nonpos`, and
  `exists_active_quitPayoff_le_singleton_of_supportwiseBalance` in
  `UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremium.lean`.
- `HasLowActiveQuittingRootQuitPayoff`, its `exists_for_tail` theorem, and
  `exists_quittingPerfectAbsorbingRow_of_lowActiveQuitPayoff` in
  `UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRow.lean`.
- `quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`,
  `exists_cyclic_subgamePerfectTerminalNash_of_lowActiveQuitPayoff`, and
  `exists_uniformEquilibriumPayoff_of_lowActiveQuitPayoff` in
  `UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`.
- `quittingPlayerwiseUnitNormalization` and its singleton theorem in
  `UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumNormalization.lean`.
- `exists_periodic_allSuffix_terminalNash_of_supportwiseBalance` in
  `UniformEquilibrium/Quitting/Classification/Existence/SupportwisePremiumUniformPayoff.lean`,
  whose final shift/scaling composition does not otherwise use its LP input.
- `quittingRootSequence_allSuffix_terminalNash_playerwiseScale` and
  `quittingRootSequence_allSuffix_terminalNash_of_nonnegative_terminalShift` in
  `UniformEquilibrium/Quitting/Terminal/TerminalAffineNashTransfer.lean`.
- `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

HEAD at source inspection was `7e7a4de9fa44b2d0609e3ee587c1155d2d31fde6`,
but relevant files were externally modified or untracked. This records the
actual working-source interfaces inspected, NOT a checked-HEAD or fresh Lean
build claim. No source file was edited in this task.

The classical source is Solan and Vieille, *Quitting games* (2001), the
Propositions 2.2–2.6 construction and extraction already audited in the
earlier ordered/supportwise records. The present note does not independently
claim historical novelty for (DP), or expand those paper hypotheses by
quotation; its theorem composition uses the explicit unit-only source
interface and the displayed normalization calculation.

Exact symbolic expansion independently checked all four formulas in (2),
the zero polynomial (3), the seven nonzero premium rows, and the positive
integer combination (4). Those checks corroborate the written algebra;
no floating-point search supplies any proof step.

Proved: strict (SLP)⊊(DP), with a full-face canonical Fin4 certificate and
arbitrary-passive family; finite semialgebraic testability; the stated
nonnegative-singleton composition with the existing consumer. Not claimed:
necessity for uniform equilibrium, separation from every known solvable
class, a new extraction method, or a solution for arbitrary Fin4 tables.

Requested independent check: falsify either the exact full-face sign proof
or the full-support LP contradiction, and verify that the stated consumer
composition uses no hypothesis beyond unit singletons and (DP). No export
is authorized before that independent review.
