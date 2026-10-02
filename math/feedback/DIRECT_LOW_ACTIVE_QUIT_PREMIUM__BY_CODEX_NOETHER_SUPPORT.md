# Independent review of the product-low quitting premium extension

Reviewer: CODEX_NOETHER_SUPPORT.

Verdict: accepted as ordinary mathematics. There is no unresolved
mathematical objection to the exact final draft identified below. Unchanged
placement in `exports/` is warranted once the separate second-review gate
is satisfied. This is not a Lean build, a new trust seal, or a claim that
every canonical table satisfies the new condition.

## Independence and exact reviewed objects

Before opening the author manuscript or either review, I derived the four
endpoint polynomials, checked every active support, disproved full-support
LP feasibility, and checked normalization and the existing unit consumer.
That record is preserved unchanged in
[the independent-first notebook](../notes/CODEX_NOETHER_SUPPORT__PRODUCT_SIGN_INDEPENDENT_REVIEW.md),
SHA256 `731f9b6576cf23adea0ebc46e7aa8aa0b4e3391c528ca5931b78e2a9be3fb5cf`.
Its historical statement that manuscript review was pending is superseded
by this review, not by an edit to the blind record. I have not read the
other review verdict.

I subsequently read all 316 lines of the frozen
[author manuscript](../notes/CODEX_TARSKI_PREMIUM__PRODUCT_LOW_QUIT_STRICTLY_BEYOND_SUPPORTWISE_LP.md),
SHA256 `34963b323a6c6b08c642bcfebdf144368a878e3cae7de781c41f0381e5ac9fd5`,
and all 315 lines of the
[final export-format draft](../notes/PRODUCT_LOW_QUITTING_PREMIUMS_STRICT_EXTENSION_UNIFORM_EQUILIBRIUM_EXPORT_DRAFT.md),
SHA256 `836eb376e4f26b6b4ee7f865759ab2cf5c99e10ead3bc75e91b24c91ec0475a7`.
The final draft's changed presentation, added exact boundary test, source
correspondence, and proposed Lean handoff were all included in this review.

## Exact claim checked

The game has a finite nonempty player set, finite real terminal rewards,
zero preabsorption and Never payoffs, independent private behavioral
randomization, and unrestricted unilateral behavioral replacements. Own
singleton rewards s_i are nonnegative; passive rewards are arbitrary.

For every product q with exact nonempty active set A(q), (DP) requires
some ACTIVE i with Q_i(q)−s_i≤0. The claim is that (SLP) implies (DP),
strictly; that the displayed scaled Fin4 family supplies (DP) from its raw
table while failing (SLP); and that (DP) and s_i≥0 imply actual periodic
terminal ε-Nash profiles at every positive error and every live suffix,
against all behavioral deviations. One fixed uniform-equilibrium payoff
then follows for the original table. No equilibrium or chronology is
assumed as part of the raw input.

## Product calculation, support boundaries, and separation

The finite product identity in Section 2 is correct, with the necessary
q_i factors. On A(q), some normalized weight is positive and every q_i is
positive, so strict positivity of all active premiums contradicts the
nonpositive weighted sum. No division excludes sure-Quit boundaries.

For the family, independent expectation gives exactly

    H=(q_1−q_2, q_2−q_0, (1−q_3)(q_0−q_1), q_0q_1q_2),
    h_i=a_i H_i.

All a_i>0 preserve signs. The eight core-support cases exhaust all fifteen
nonempty active sets and each chosen witness is active. On the full core,
q_0≤q_1 makes H_2≤0; otherwise H_0+H_1<0. At q_3=1, H_2=0 causes no
exception. In particular q=(1,1,1,1) gives H=(0,0,0,1), not a violation.
The identity (1−q_3)(H_0+H_1)+H_2=0 is a root-dependent sign certificate,
not an unmentioned fixed LP weight vector.

The seven listed nonzero participant rows are exactly the rows obtained
from (F). The nonparticipant zeros in D are bookkeeping only. All actual
passive rewards remain free, and every prescribed singleton equals s_i.

For the full-support LP put v_i=a_i w_i. The core-pair cycle forces
v_0=v_1=v_2; the grand coalition forces v_3=0; coalition {1,2,3} forces
v_1=0. Thus every weight vanishes, contradicting normalization. This
works even when zero weights are allowed. The four rows used by the dual
certificate also suffice directly: {1,2,3} gives v_1=0, {0,1} gives
v_0=0, {0,2} gives v_2=0, and I gives v_3=0. Thus the handoff can use
four constraints, with the remaining core-pair inequality redundant.

The independent positive combination is correct:

    2D({0,1})+D({0,2})+3D({1,2,3})+D(I)=(a_0,a_1,a_2,a_3).

Its four coefficients sum to seven. The resulting law is not a product:
the full atom requires every q_i>0, the other atoms require every q_i<1,
and an independent law would then give positive empty-coalition mass.
Even conditioning a product law on nonemptiness cannot repair this example:
with all parameters interior, every nonempty coalition would have positive
conditional mass. No correlated law is being used to construct strategies.

All proper-face LP witnesses are valid. Equal effective weights work on
{0,1,2}. Concentration on 1, 0, and 2 works respectively on {0,1,3},
{0,2,3}, and {1,2,3}; each such player has nonpositive premium on every
contained coalition in which it participates. Core pairs have a negative
participant, pairs containing 3 have zero premiums, and singleton
constraints vanish. Dividing effective weights by positive a_i and then
normalizing preserves every inequality.

## Testability and attempted falsifiers

For each exact support the violation system has polynomial constraints,
including strict positive active hazards and premiums. Finite disjunction
and real-closed-field quantifier elimination give the claimed semialgebraic
description in the reward entries. Effective decidability is correctly
restricted to rational or real-algebraic inputs. The inward perturbation
of sure-Quit coordinates preserves finitely many strict inequalities, so
replacing their upper bound by a strict upper bound preserves feasibility.
This reasoning does not assert that vertex tests imply (DP).

I checked the final draft's exact three-player boundary example explicitly:
take premiums (2,−1) on {0,1} favoring 0, on {1,2} favoring 1, and on
{0,2} favoring 2; singleton and triple premiums are zero. Every coalition
has a nonpositive participant. At q=(1/2,1/2,1/2), each pure-Quit premium
is (2−1)/4=1/4>0. This falsifies the weaker pure-coalition test, not (DP).
For a Fin4 completion one can set all participant premiums on coalitions
containing the added player to zero; the same violating root keeps that
player inactive. The two-player coincidence of (DP) and (SLP) is also
correct, including zero pair premiums.

An exact symbolic computation independently expanded all four endpoints,
checked the full-core zero polynomial and all seven nonzero rows, verified
the integer dual certificate, and tested every contained coalition for
each proper-support witness. These calculations corroborate the proofs;
no numerical sampling or computational search is needed for a proof step.

The strict comparison is with (SLP), not every previously solvable table
class. For example, completing the displayed family with passive rewards
zero gives an exact all-Quit equilibrium: grand-coalition own payoffs are
s_0,s_1,s_2,s_3+a_3≥0, whereas a lone continuer gets zero. Thus neither
the family nor its LP failure demonstrates absence of stationary equilibria.
The final draft makes no such stronger claim.

## Literal source consumer, transport, and fixed-payoff quantifiers

I inspected the named declarations under their actual imports:

- `HasLowActiveQuittingRootQuitPayoff`, its `exists_for_tail` theorem,
  and `exists_quittingPerfectAbsorbingRow_of_lowActiveQuitPayoff` in
  `UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRow.lean`.
- `exists_periodic_quittingPerfectAbsorbingRootSequence_of_lowActiveQuitPayoff`
  in `UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRootSequence.lean`.
- `quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`,
  `exists_cyclic_subgamePerfectTerminalNash_of_lowActiveQuitPayoff`, and
  `exists_uniformEquilibriumPayoff_of_lowActiveQuitPayoff` in
  `UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`.
- `IsSupportwiseBalancedQuittingPremiumTable`, the participant product-sum
  identity, and `exists_active_quitPayoff_le_singleton_of_supportwiseBalance`
  in `UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremium.lean`.
- `quittingPlayerwiseUnitNormalization` and its singleton theorem in
  `UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumNormalization.lean`;
  `exists_periodic_allSuffix_terminalNash_of_supportwiseBalance` in
  `UniformEquilibrium/Quitting/Classification/Existence/SupportwisePremiumUniformPayoff.lean`.
- `quittingRootSequence_allSuffix_terminalNash_playerwiseScale` and
  `quittingRootSequence_allSuffix_terminalNash_of_nonnegative_terminalShift`
  in `UniformEquilibrium/Quitting/Terminal/TerminalAffineNashTransfer.lean`;
  `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

Under unit singletons, nonempty exact support is equivalent to positive
root absorption, and (DP) is exactly the first predicate. Its Quit endpoint
does not depend on the zero continuation used in the definition. The
periodic producer's only table assumptions are unit singletons and this
predicate. It produces support-perfect rows against ACTUAL next-stage tails.
The extraction consumes those rows, not merely ordinary regret bounds, and
may either retain the sequence or use a constant period-one stationary
repair. No retained absorption floor is therefore needed in the final claim.

I also reread the original Solan–Vieille (2001) PDF, printed pages 269–273,
including conditional Propositions 2.2–2.4, the actual-tail mesh argument,
and the restatement as Proposition 2.6. The paper uses Continue probabilities,
the complement of q here. Its one-root hypothesis is about a suitable exact
Nash root at each low continuation; (DP) supplies a low active Quit endpoint
at every absorbing product, and a supported Quit endpoint equals the player's
payoff at an exact Nash root. All-Continue exact roots form the separate
permitted case. Thus no capping assumption is silently imported. The paper's
subgame-perfect-or-stationary extraction is the relevant classical mechanism,
not a license to accumulate one-row regret indefinitely. The unbuilt
`Literature/` transcription was not used as a proof.

The final normalization is valid, including s_i=0. For t=ε/2 and
b_i=s_i+t>0, normalized Quit premiums are exactly h_i/b_i. Applying the
unit producer at ε/(2 max_i b_i) and undoing scales gives ε/2 error for
r+t at every suffix. For any unilateral behavioral replacement the exact
regret difference on returning to r is

    t(P_plan(absorption)−P_deviation(absorption))≤t.

This remains true for Never and nonabsorbing deviations. The information
and strategy tree are unchanged; no absorbing payoff shift is mistakenly
treated as a constant shift of every strategy's payoff. Hence the original
error is at most ε. Finally the original-table terminal-all-errors theorem
selects ONE payoff before accuracy; no limit in a sequence of changing
normalized games is substituted for that quantifier order.

## Final-byte acceptance

The final draft faithfully preserves the valid mathematics of the frozen
author note and adds correct semantic, boundary, and handoff information.
Its new contribution is the strict raw-table class separation and explicit
family adapter through an existing consumer, not a new generic extraction
theorem. The suggested implementation does not assume its output as data.

I accept the complete 315-line draft with SHA256
`836eb376e4f26b6b4ee7f865759ab2cf5c99e10ead3bc75e91b24c91ec0475a7`.
There is no unresolved mathematical objection. Unchanged placement of these
exact bytes in `exports/` is warranted once the other required independent
final-byte acceptance is present. I have edited only this feedback record,
not the author note, final draft, any export, or any Lean source. HEAD was
`7e7a4de9fa44b2d0609e3ee587c1155d2d31fde6`; relevant interfaces include
external working-tree changes, and no fresh Lean build was run here.
