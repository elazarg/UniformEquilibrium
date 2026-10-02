# Independent review of support-dependent participant-premium LPs

Reviewer: CODEX_TARSKI_PREMIUM.

Verdict: PASS for the complete ordinary-mathematical statement and proof.
No mathematical correction is required and no objection remains unresolved.
This review grants no Lean, adapter-implementation, or checked-consumer seal
to the new table criterion. No export or existing export edit was performed.

Artifact reviewed in full:
[CODEX_FRECHET_CYCLE__SUPPORT_DEPENDENT_PARTICIPANT_PREMIUM_LP_ADAPTER.md](../notes/CODEX_FRECHET_CYCLE__SUPPORT_DEPENDENT_PARTICIPANT_PREMIUM_LP_ADAPTER.md),
333 lines, SHA-256
`1b21bb2738a0bbbb8f8e0919500bc05deadeb703d72c3662d0f00c7c737071a8`.
The verdict binds those bytes. The earlier global-weight note was separately
read at SHA-256
`3d40e81fa5a758e60b321abdc0efa457e62a63ea1d8df092a5d8ed09d5e2e786`.

## Independence and claim restatement

Before reading either author note, I derived the participant expectation
identity, active-low-player consequence, transformed weights, and semantic
composition independently. After ROOT supplied the supportwise strengthening,
I checked its zero-weight and exact-support issues before seeing the author's
generalized proof. The reconstruction and additional falsifiers are in
[the owned notebook](../notes/CODEX_TARSKI_PREMIUM__SUPPORTWISE_PARTICIPANT_BALANCE.md).
I did not read another reviewer's verdict before deriving or judging the
mathematics.

The statement checked has a finite nonempty player set, real finite terminal
rewards, Never payoff zero, nonnegative own singletons s_i, and independent
behavioral strategies. For every nonempty active set A, a nonnegative
normalized vector w^A must make the weighted premium sum over participants
nonpositive at EVERY nonempty coalition contained in A. Passive rewards and
negative own premiums are unrestricted. The conclusion is periodic terminal
ε-Nash play at every ε>0, valid in every suffix against ALL unilateral
behavioral replacements, and one fixed uniform-equilibrium payoff for the
original game. Periods and profiles may depend on accuracy.

## The exact new adapter passes

For each i, finite product factorization gives

    q_i(Q_i(q)−s_i)=Σ_(S∋i)p_q(S)(r_i(S)−s_i).

No division occurs, so q_i=0 and q_i=1 are covered. For the EXACT active
set A={i:q_i>0}, coalitions not contained in A have probability zero.
Multiplying by the weights supplied for A and summing therefore yields

    Σ_(i∈A)w_i^A q_i(Q_i(q)−s_i)
      =Σ_(∅≠S⊆A)p_q(S)Σ_(i∈S)w_i^A(r_i(S)−s_i)≤0.

The coefficients w_i^A q_i are nonnegative and at least one is strictly
positive. If every positive-weight coordinate had a strictly positive
endpoint premium, the left side would be positive. Therefore a player with
BOTH positive weight and positive Quit probability has Q_i≤s_i. This
conclusion holds for every absorbing product root without any Nash premise.

The exact-support clause matters: a vector for a larger set could vanish on
the actual active set. The proof uses the correct vector. Zero-weight active
players do not cause a problem because normalization ensures another active
player has positive weight. Neither supportwise weights nor root selections
need to vary continuously. There is no averaging over arbitrary correlated
coalition laws in place of the prescribed independent root.

The normalized finite LP is exactly the stated table condition. Its counts
are correct: for Fin4, 15 supports, 32 total variables, 15 normalization
equalities, 32 nonnegativity constraints, and 65 coalition constraints,
including 32 tautological singleton constraints. The remaining 33 may be
nontrivial. These are sufficient feasibility checks, not a complete
equilibrium decision procedure. The note correctly makes no inference from
LP infeasibility to product-root realizability or absence of equilibrium.

## Complete consumer and zero-solo transport pass

At unit solos, the adapter supplies an active player with F_i=Q_i≤1 at
every absorbing exact Nash root. An all-Continue Nash root in the compact
low-coordinate carrier instead supplies an indifferent player with v_i=1.
Increasing that player's Quit probability preserves its payoff and keeps
the successor in the carrier while giving positive absorption.

For every other player, each pure endpoint changes by at most 2Rδ and its
support is unchanged, so support regret is at most 4Rδ. The selected
player retains exact best-response support. This is sufficient for the
production row-perfect predicate: both endpoints lie below the mixed payoff
plus the support tolerance, and every supported endpoint lies above the
mixed payoff minus that tolerance, by taking convex combinations.

The finite map runs from continuation representatives to approximate current
successors; reversing its cycle gives the stated chronological Bellman
residual. With δ=min(1/2,τ/(8R)) and ζ=δτ/4, actual periodic suffix
values satisfy D≤ζ+(1−δ)D, hence D≤ζ/δ. Every suffix absorbs almost
surely under the prescribed sequence. The actual-tail support error is at
most 4Rδ+2ζ/δ≤τ. Actual payoffs are proved to approximate annotations;
they are not an input witness.

I checked the exact production declaration
`quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`
in UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean.
Its only reward-shape hypothesis is unit own singletons. It chooses the
positive row tolerance before the input sequence and concludes all-suffix
terminal Nash against the complete behavioral deviation class for a periodic
output sequence. Its stationary-repair alternative is retained here. No
capped joint-reward assumption, peeling assumption, or inherited absorption
bound on deviators is silently inserted.

For s_i≥0, every h_i=s_i+t is positive and
Z_A=Σ_A w_i^A h_i is positive. The transformed normalized weights
w_i^A h_i/Z_A preserve all nonnegativity and normalization conditions and
turn each transformed coalition inequality into the original inequality
divided by Z_A. This remains valid when some weights or singletons vanish.
The factors h_i are in the correct direction.

The common action and coalition-history tree identifies strategies across
reward changes. Positive coordinate scaling transports regret player by
player. Terminal shifting changes any profile payoff by exactly t times
that profile's absorption probability, leaving Never at zero. Consequently
the ε/2+2t estimate with t=ε/4 applies to every unilateral replacement,
including those that fail to absorb, and in every suffix.

Finally,
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
in UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean
is applied to the ORIGINAL table. Its fixed compact payoff cube supplies
the fixed-target quantifier; transformed weights, bounds, periods, and
profiles may vary with accuracy. This closes the full behavioral and
uniform-horizon conclusion without a punishment assumption.

## Class inclusions and strict example pass

Ordered peeling supplies a unit vector on a peelable member of each A;
global positive balance supplies the normalized restriction of its vector.
Both inclusions are exact. The two subclasses remain incomparable.

For Section 6.3, I checked all fifteen proposed supportwise vectors and all
their coalition inequalities using exact rational arithmetic. For any A
meeting K={0,1,2}, uniform weights on A∩K balance every core pair
contained in A. A core pair not contained in A is not one of that support's
constraints. The exceptional pair {0,3} contributes zero because player 0's
premium is zero and player 3's weight is zero. Other coalitions have zero
premiums. For A={3}, its unit weight satisfies the sole singleton inequality.

Each core player has a positive premium in a coalition contained in K,
so peeling fails on K. The premium pattern at {0,3} is (0,1), which
forbids any strictly positive global weight on player 3. The fixture thus
satisfies the unified premise and neither earlier premise. Its arbitrary
passive completion is legitimate because all these assertions concern only
participant premiums. The claim is strictly about these named raw classes,
not exclusion from every existing equilibrium theorem.

Section 6.4 also checks exactly. A nonzero global vector may have all its
positive coordinates inactive, and its displayed root has both active
players strictly above their singletons. On that active pair the supportwise
LP would require the normalized nonnegative weights to sum to at most zero,
which is impossible. The counterexample and strengthened hypothesis are
therefore consistent.

## Independent attacks and source novelty boundary

The owned notebook contains exact attacks not taken from the generalized
author note. Cyclic pair premiums (+2,−1), unit solos, triple premiums zero,
and passive rewards 2 give q=(1/2,1/2,1/2) as an exact root at continuation
(−1,−1,−1), with every endpoint 5/4. Each coalition separately has a
nonpositive-premium member, but no common nonnegative nonzero vector works
on the full support. This defeats a weaker coalitionwise-minimum argument,
which the candidate does not use.

I also checked balanced cyclic (+1,−1) pairs, unit solos, and passive
rewards 3/2: this satisfies global balance, fails ordered peeling, and has
no pure stationary exact Nash profile. In the author's separate Fin4 base
fixture, all sixteen pure coalitions have a profitable toggle, all fifteen
participant sums vanish, the displayed affine-gain obstruction is exact,
and every nonzero nonnegative full-social weight violates a terminal row.
These distinguish the new input from named pure stationary potential and
full-social-weight sufficient classes. None establishes worldwide novelty
or rules out every other known existence result, and neither note says so.

Besides the extraction and terminal-selection signatures above, I inspected
`quittingRootQuitPayoff_eq_sum_opponentCoalitionMass` in
UniformEquilibrium/Quitting/Root/OpponentCoalitionPayoff.lean,
`exists_isZeroQuittingRootNash` in
UniformEquilibrium/Quitting/Root/NashExistence.lean,
`quittingTerminalPayoff_playerwiseAffine` in
UniformEquilibrium/Quitting/Terminal/TerminalAffineReward.lean, and the
full-social and membership-potential definitions in
UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean
and UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean.

The original Solan–Vieille paper was directly read in the preceding source
audit, printed pp.265–274, including Propositions 2.2–2.4 and the distinction
between unit solos, capped joint rewards, and the weaker root-choice input.
The classical mechanism is correctly credited. The new proved attachment
is the finite participant-premium LP family and its direct product identity.
The unbuilt literature lane is not used to confer checked status on this
adapter. No fresh Lean build, universal table coverage, LP necessity,
product realization of dual mixtures, common-boundary theorem, or worldwide
priority claim is asserted.

The author manuscript therefore passes this independent mathematical review.
This file neither modifies nor supersedes the frozen ordered-premium export.

## Final assembled-byte reconciliation

Final assembled artifact:
[SUPPORTWISE_WEIGHTED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM_EXPORT_DRAFT.md](../notes/SUPPORTWISE_WEIGHTED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM_EXPORT_DRAFT.md),
392 lines, SHA-256
`38d4975b7e630e59878332bdb96190932ede7e4be8c414e0fe11c201dcabcef7`.

Verdict: PASS on these exact final bytes. I compared the full assembled
artifact against the already reviewed 333-line author manuscript with hash
`1b21bb2738a0bbbb8f8e0919500bc05deadeb703d72c3662d0f00c7c737071a8`
and read every addition and replacement. No other reviewer's verdict was
consulted. Definitions, proof, normalization, examples, and numerical
constants are unchanged. The explicit zero preabsorption payoff agrees with
the original terminal and uniform-payoff semantics.

The new opening accurately states the finite table source and the strict
extension beyond the two earlier classes. Its wording that the criterion
is not necessary is also justified: Section 6.4 gives a table failing (SLP)
with an exact root having two sure quitters. At that row a unilateral
replacement cannot prevent first-date absorption by another sure quitter,
so its exact root inequalities give an exact full terminal equilibrium.
Thus this example also has a uniform-equilibrium payoff despite failure of
the criterion. No universal or worldwide novelty claim is introduced.

The expanded source comparison correctly distinguishes all-player weighted
terminal rewards from affine membership-gain symmetrization and from the
participant identity. The proposed Lean declaration shapes preserve the
exact table hypotheses, require no supplied strategy or actual-tail witness,
keep the active-player identity free of a Nash premise, and reuse the
unit-only extraction with the independently proved row producer. Their
proposed rather than implemented status is explicit. The final scope
retains nonnegative singletons, independent behavioral randomization,
unrestricted deviations including Never, and a fixed payoff target before
accuracy. It adds no unjustified necessity, polynomial-time, or general-game
claim.

No mathematical correction is required. This acceptance binds the final
hash above and an unchanged promoted copy. Final integrity checks and the
separate second review remain the coordinator's responsibility; the
reviewer has performed no export or frozen-file mutation.
