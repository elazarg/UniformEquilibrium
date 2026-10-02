# Independent whole-proof falsification review of ordered quitting premiums

Reviewer: CODEX_TARSKI_PREMIUM.

Verdict: PASS for the complete mathematical export candidate below. I found
no unresolved mathematical objection and require no correction. This review
is ordinary mathematical verification and static inspection of named source
declarations. It does not confer an L, A, or C seal, assert a new Lean build,
or authorize self-export by the author.

Reviewed artifact:
[ORDERED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM_EXPORT_DRAFT.md](../notes/ORDERED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM_EXPORT_DRAFT.md),
643 lines, SHA-256
`a42680e45fe7a8a373337a624808eefee1fc5a3b53507eda32cb5a7e5e7f3b6e`.
All sections, including the auxiliary theorem, independent Fin4 composition,
six boundary tests, source correspondence, handoff, and scope, were read.
This verdict binds those bytes, including an unchanged copy promoted under
the mathematical result name; substantive edits require renewed review.

Final-definition reconciliation: the final version adds exactly 17 lines
defining the punishment vector and floor-free weighted capacity in Section 8.
Removing precisely that definition block reproduces the previously reviewed
SHA-256 `6fb963c64a0f85bc3c3f94947dccd829d9f9f07661a36a7272d525f335f863b8`.
I checked the addition: its opponent/own law quantifiers, free starts,
length-zero paths, charge sum, weighted Bellman defect, and ordinary root
regret agree exactly with the source definitions and the argument below.
It improves self-containment and leaves every mathematical verdict unchanged.

## Independence and exact claims checked

I reconstructed the selected-root, marginal perturbation, reversed finite
cycle, actual-tail contraction, and zero-singleton transport before receiving
the assembled draft, without reading another reviewer's verdict. My derivation,
source audit, and independent small falsifiers are retained in
[the owned notebook](../notes/CODEX_TARSKI_PREMIUM__ORDERED_PREMIUM_ADVERSARIAL_AUDIT.md).
The original Solan–Vieille PDF and exact production signatures were inspected
directly, rather than accepting the contributor notes as theorem truth.

The main claim checked is: every finite nonempty independent behavioral
quitting game with Never payoff zero, nonnegative own singleton payoffs, and
the finite condition that every active set has a member with no positive
own-quitting premium on its internal coalitions has periodic terminal
approximate Nash profiles at every positive error, valid against every
unilateral behavioral replacement in every surviving-date suffix. This gives
one fixed uniform-equilibrium payoff. Negative own premiums and passive
rewards are unrestricted.

The separate auxiliary claim adds nonnegative own premiums and permits signed
singletons. Under that additional hypothesis, peeling is equivalent to the
all-root singleton-boundary property, and excludes every C¹ unit-drift
function on a neighborhood of the padded box. I did not extend this theorem
or its punishment consequence to signed premiums.

## Main proof audit

- **Finite condition and order.** The deletion proof is exact in both
  directions. Under weak peeling, a positive premium forces a previously
  deleted member; conversely the earliest member of any active set has no
  such premium internally. Neither argument needs nonnegative premiums.
  The order is on labels and imposes no chronology on strategies.
- **Root selection.** For an absorbing exact root, the selected active
  player receives a convex combination of rewards at most its unit solo,
  so its Quit endpoint is at most 1. Since Quit has positive support,
  its prescribed value equals that endpoint. At an all-Continue Nash root,
  all continuation coordinates are at least 1; the carrier supplies one
  equal to 1. This handles every pure and mixed support boundary.
- **Marginal activation.** Increasing only the selected Quit probability
  preserves its payoff: it was mixed and indifferent, surely Quit, or the
  indifferent all-Continue player. Other players retain their supports and
  each pure endpoint changes by at most 2Rδ. Their supported-action versus
  pure-action gaps therefore remain at most 4Rδ. The new successor is in
  the low-coordinate carrier, and absorption is at least δ.
- **Finite cycle orientation.** A finite map sends an annotation to a
  representative near its prefixed successor. Reversing a directed cycle
  assigns each chosen root its original source annotation as next-tail value.
  Consequently the displayed Bellman residual is in the chronological
  direction required for the actual behavioral profile. No continuous
  selection or public correlation is required.
- **Actual tails.** Periodic repetition has every-suffix survival bounded
  by (1−δ)^n. Its bounded periodic terminal values satisfy exact Bellman
  recursion. The maximum discrepancy over one period obeys
  D≤ζ+(1−δ)D and hence D≤ζ/δ. The stated constants give
  4Rδ+2ζ/δ≤τ. The actual tails are constructed, not supplied or assumed.
- **Production predicate.** Supported-action versus pure-action regret
  bounds imply every `QuittingPlayerRowεPerfect` clause by averaging over
  supported actions. There is no missing factor in this conversion.
- **Nonlocal extraction.** The exact production declaration
  `quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`
  in UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean
  has `QuittingUnitSoloExit` as its only reward-shape hypothesis. It chooses
  a positive row tolerance before quantifying the sequence, its absorption
  floor, and period. It concludes full behavioral terminal Nash in every
  suffix for a periodic output sequence. The stationary branch is permitted
  and is period one. The main proof applies precisely this interface.
- **Zero-singleton closure.** Positive coordinate scaling by s_i+t preserves
  signs of premiums and scales each player's deviations by the same positive
  number. The same action/coalition-history tree identifies the strategies
  between games. The terminal shift changes a profile payoff by exactly
  t times its absorption probability. Thus the ε/2+2t estimate with
  t=ε/4 works for every profile and replacement, including positive Never
  probability. Accuracy-dependent normalized bounds cause no quantifier
  problem.
- **Fixed target.** The final invocation of
  `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
  in UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean
  is on the original table. Its fixed reward cube contains all transported
  approximate-Nash payoffs. This selects one payoff before accuracy and does
  not assume a common period, normalized game, or moving target.

## Auxiliary theorem and Fin4 route

For the all-root boundary implication, nonnegative premiums give Q_i≥s_i
for EVERY player. Peeling supplies an active player with Q_i=s_i. These
are exactly the two different uses needed for membership in L_B.

For the converse, failure of peeling on A gives every member a strictly
positive premium at an internal coalition. Using a common 0<t<1 makes
each such coalition positive probability; nonnegative premiums prevent
cancellation. The chosen continuation coordinates make each active player
indifferent and tend to its singleton. Inactive coordinates set to B strictly
prefer Continue for small t because B>s_j. Finiteness gives one t for all
constraints, and M<B gives strict upper successor bounds. This proves the
equivalence on each padded box without a hidden source restriction.

For the C¹ argument, the unique binding-coordinate case uses a small solo
root and the exact spectator endpoint formula, including the simultaneous
pair reward. In the multiple binding-coordinate case, raising one binding
coordinate remains on L_B, forcing its directional derivative nonnegative.
Lowering all binding coordinates stays in the full box because s_i>−B.
Every Nash root then absorbs; the uniform displacement bound forces charge
at least ε/(M+B). Minimality contradicts the nonpositive limiting difference
quotient. This does not require a continuous root branch or convex H.

The Fin4 argument correctly adds nonnegative premiums and nonnegative
singletons, so immediate Quit and all-Never opponents prove P=s. The
analytic separator is applied with inner radius M+1 and outer radius M+2,
with ε=min(δ,1). Smaller tolerance gives a subset of the outer relation,
so a finite-capacity counterassumption at δ implies one at ε. Exact
Nash/Bellman edges lie in every positive-tolerance tested relation; Section 4
therefore excludes the produced polynomial. The conclusion has ONE fixed
box before both tolerance and requested charge.

I read the analytic separator's exact statement, edge/packet definitions,
and proof in
[the frozen polynomial packet](../exports/POLYNOMIAL_FORWARD_CERTIFICATES_WITHOUT_PUNISHMENT_FLOORS.md),
SHA-256 `14191a09b4a42149e0c893666603d85b2e2f1fb3bcd0240af0e0619aaeefc9d6`.
The relevant floor-removal and weighted-consumer signatures were inspected:
`hasFloorFreeAbsorptionWeightedFiniteForwardPackets_iff_weighted` in
UniformEquilibrium/Quitting/Projective/FloorFreeForwardPacketInputRemoval.lean,
and `quittingGame_exists_uniformEquilibriumPayoff_of_absorptionWeightedPackets`
in UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketProducer.lean.
They accept the stated normality and positive reward-containing radius;
the required radius M+2 satisfies every bound. No sure-root or
positive-singleton alternative is silently added.

## Explicit falsification attempts

All six final-draft examples are valid with their stated complete-table
defaults. I checked the active-player leave and inactive-player join
inequalities in the displayed pure roots. Finite exact arithmetic also
verified weak peeling/order agreement and the advertised roots in examples
1–4. In example 4, player 0's punishment is exactly zero: immediate Quit
guarantees nonnegative reward, and an opponent who quits surely at the first
date caps its payoff at zero. Thus the claimed strict P₀<s₀ boundary is real.

The owned notebook adds the following independent attacks:

1. The two-player signed table r({1})=(1,0), r({2})=(−2,1), and
   r({1,2})=(−1,2) passes weak peeling and has an exact absorbing root
   with value (−1,2). This defeats extension of the singleton lower orthant
   to signed premiums but is harmless to the low-coordinate carrier.
2. In the unit-solo table r({1})=(1,1), r({2})=(5,1), and
   r({1,2})=(1,1), stationary q=(t,t²) has support error at most 4t
   against actual tails and positive row absorption. Its player-1 Never
   gain tends to 4 as t tends to zero. At t=1/10, the exact support gap
   is 40/109 and Never gain is 400/109. Therefore small local support
   error cannot replace the nonlocal extraction. The draft explicitly
   preserves that consumer and its stationary-repair alternative.
3. Positive own pair premiums for both players can destroy peeling while
   both Quit surely remains exact Nash. Thus the draft correctly avoids
   asserting necessity or a negative gap outside its class.

These attacks found genuine failures of stronger implications, all of which
the frozen draft explicitly avoids. They leave no objection to its claims.

## Source, agency, and export boundaries

Original paper inspected: Solan and Vieille, “Quitting Games,” Mathematics of
Operations Research 26(2), 265–285 (2001), DOI 10.1287/moor.26.2.265.10549,
local literature/SOLAN_VIEILLE_2001__QUITTING_GAMES__JSTOR.pdf, printed
pp.265–274. Definition 2.1 uses support perfection, Proposition 2.2 states
the weaker root-choice condition and distinguishes it from A.2, Proposition
2.3 supplies the reversed cycle/actual-tail argument, and Propositions 2.4/2.6
supply nonlocal extraction. Continue/Quit probability orientation and zero
Never semantics are correctly translated. No literature-lane declaration is
used as an unbuilt axiom or as evidence of production status.

The root-existence, capped-generator, unit-only extraction, affine transport,
terminal-selection, solo-preemption, sure-chamber, and coalition-toggle
declarations listed in Section 7 were inspected in their named source files.
`quittingTerminalPayoff_playerwiseAffine` explicitly contains the absorption
factor multiplying the shift. The cited old generators retain their capped
inputs; the new mathematical producer is not falsely described as already
implemented. All Section 7 source files and the two Section 8 consumer files
are unchanged between the recorded inspected HEAD e9f3e90 and current HEAD
c6ca930; the preserved earlier source-audit identity is therefore consistent.
All four proof hashes in Section 10 match their referenced files.

At live histories no event beyond the date is observed before somebody
quits. Independent private behavioral randomization therefore has the
stopping-law representation used here, and the production conclusion quantifies
the complete behavioral replacement class. The paper and source consumers
explicitly include Never; neither almost-sure absorption of the prescribed
profile nor period bounds restrict the deviator. The theorem produces one
admissible strategy family for this class and claims no strategy-class
completeness for arbitrary tables or arbitrary equilibrium payoffs.

The strict named improvement is the actual finite-table adapter into the
existing low-payoff-quitter mechanism beyond capped joint quitting rewards.
The draft credits the classical mechanism and disclaims worldwide priority,
full arbitrary-game existence, effective length bounds, and unperformed Lean
implementation. Its mathematical export gate is satisfied from this
reviewer's perspective, subject to the separately required second independent
review and ROOT's final integrity/promotion checks.
