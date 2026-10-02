# Independent rereview of Sections 1--3

Reviewer: Codex Laplace

## Verdict

**PASS** for the repaired Sections 1--3 as ordinary mathematics, not checked
Lean.  I found no remaining mathematical objection.  The two defects in the
Codex Noether review are now repaired at the correct interfaces.

This verdict does not attach an `L` seal.  In particular,
`FinFourSourceFaithfulMinimumTargetRegeneration` is a proposed new wrapper,
not a declaration at the current repository head.  The point of this review
is that the wrapper is constructible from the stated inputs, rather than
merely specifying a desired output.

## Claim checked

The repaired claim is conditional on a supplied literal endpoint sequence.
If actual profiles converge jointly in terminal semantics and terminal law to
a positive-debt minimum point, and one fixed terminal has a uniformly positive
mass at supplied marked dates, then arbitrarily deep exact cap--Nash root
words can be prepended while retaining:

* the literal supplied profiles as suffixes;
* the supplied marked dates, shifted by the exact word lengths;
* convergence of prefixed total debt to the same positive minimum; and
* every two-counterfactual response contrast, scaled by opponent survival
  tending to one.

For a `ConcentratedCollisionThreeRoleEndpointLaw`, the strong specialization
additionally assumes `1 < marked.val.card` and returns a regenerated Fin4
minimum source together with an explicit chronology whose profiles and marks
are pointwise equal to the incoming target-profile and marked-date sequences.

## Repairs from the first review

### Nonsingleton collision input

Section 2 now takes

\[
  1 < |\texttt{marked}|
\]

as an explicit hypothesis of the source-faithful adapter.  This is exactly the
extra argument required by
`ConcentratedCollisionThreeRoleEndpointLaw.perRank_mass_chain` in
`Research/Quitting/ConcentratedCollisionThreeRoleEndpointLaw.lean`.  The note
no longer tries to recover that fact from the public endpoint object.

Consequently, at every retained rank the target profile has the routed
terminal at the original date with mass at least `packet.resolution`, which is
strictly positive.  Thus Section 1 applies with the literal choices

\[
  \sigma_n=\tau_n,\qquad
  t_n=\texttt{packet.mark (endpoint.ranks n)},\qquad
  \lambda=\texttt{packet.resolution}.
\]

Without the nonsingleton input, the note correctly claims only the weaker
construction that retains the target profiles but reselects finite-window
marks from the positive limiting terminal-law coordinate.

### Public source-faithful chronology

The proposed `FinFourSourceFaithfulMinimumTargetRegeneration` is a legitimate
producer/wrapper.  A concrete construction order is:

1. use `endpoint.target_joint_tendsto`, the equality-arm minimum identity, and
   `perRank_mass_chain endpoint hcollision n` to run the supplied-realizer
   construction on the literal target profiles and original marks;
2. obtain cutoffs and cap--Nash words while keeping those profile and mark
   functions unchanged;
3. build the new `QuittingMinimumLawCausalSuffixAtom` from that tuple;
4. build `next : FinFourMinimumAtomProducer` exactly as in
   `ConcentratedCollisionThreeRoleEndpointLaw.nonempty_finFourMinimumTargetRegeneration`
   in `Research/Quitting/FinFourProducerAtlas/ThreeRoleRegeneration.lean`, but
   with this source-faithful atom; and
5. build both the regeneration record and an explicit
   `FinFourMinimumAtomChronology next` from the same tuple.

The pointwise profile and mark equalities are then constructor equalities and
may be exposed propositionally as fields of the wrapper.  No equality is
inferred from, or needed against, the existential proof stored in
`next.atom.chronology`.  The resulting explicit chronology is already a
chronology of the same `next`, which is what downstream consumers require.
The point, terminal, residual, and terminal-mass fields are simultaneously the
same ones used by the checked regeneration constructor.

## Survival, cutoff, and atom transport

`exists_quittingCapNashRootStack` and
`quittingTerminalDebtSum_capNashRootStack_eq` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean` give
the words and exact identity

\[
  D(W_n*\sigma_n)=c_nD(\sigma_n).
\]

The literal debt infimum bounds the left side below by (D_*>0), while
`quittingCapNashStackContinueProduct_le_one` and nonnegative terminal debt
bound it above by (D(\sigma_n)).  Since the latter tends to (D_*), both the
prefixed debt and (c_n) tend to their claimed limits.  Division is safe at
every rank because (D(\sigma_n)\ge D_*>0).

`quittingStageCoalitionMass_literalRootStack_add_length` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`
gives the exact shifted-atom identity.  Coordinate convergence and stage-mass
domination give the limiting law bound.  The complete terminal-law coordinate
is the increasing sum of nonnegative stage masses, so
`exists_finiteWindow_sum_stageCoalitionMass_gt` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionWindow.lean`
supplies the cutoff.  Replacing it by `max h_n (t_n + 1)` preserves the strict
window inequality and places the original mark inside the window.  Arbitrary
values at the finitely many early ranks are harmless because the chronology's
causal field is eventual.

There is no reversal of the root word and no off-by-one defect: a word of
length `n + 1` shifts the incoming marked stage to `n + 1 + t_n`.

## Behavioral and pure-time response transport

Equation (3.2) has the correct factor.  Iterating
`quittingRootAndContinuationDeviation` and
`quittingTerminalPayoff_update_rootAndContinuationDeviation_eq` from
`UniformEquilibrium/Quitting/Root/FirstBranch.lean` constructs the shifted
version of any complete behavioral suffix strategy.  Both counterfactuals
force the observer to Continue throughout the prefix.  Prefix absorption by
an opponent therefore contributes the same payoff to both, and the suffix
difference is reached exactly with probability

\[
  c_{-o,n}=\Pr(\text{all opponents Continue through }W_n).
\]

Equivalently,
`quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` reduces
arbitrary behavioral deviations to their live hazards, after which
`quittingRootSequenceTerminalValue_sub_eq_jointSurvivalWeight_mul` in
`UniformEquilibrium/Quitting/Paths/SurvivalWindowLanding.lean` applies.  In the
deviated live-root sequence the observer's prefix coordinate is surely
Continue, so its joint-survival weight is precisely the original opponents'
survival weight.

Rootwise joint survival is at most opponent survival, hence

\[
  c_n\le c_{-o,n}\le1.
\]

Thus (c_n\to1) implies (c_{-o,n}\to1).  The identity is rankwise exact for
arbitrary behavioral plans and therefore applies pairwise to any finite menu.

The edge cases are also correct.  Prefixing `Never` by sure Continue leaves
`Never`; a relative finite quit date (q_n), even when unbounded in (n),
becomes the absolute date (|W_n|+q_n).  These pure-time cases already
substantially overlap the checked
`quittingRelativePureTimeTerminalValue_sub_prefixTransport` in
`UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean`.  The
note now states that overlap honestly.  Its new content is the source-faithful
attachment and the arbitrary-behavioral shift adapter, not a new pure-time
transport theorem.

The qualification to two-counterfactual contrasts is necessary and is
present: the statement does not identify the lower shifted counterfactual
with the newly prefixed prescribed profile, and it does not claim one-factor
transport for a raw gain against that profile.

## Boundary and falsification checks

* A manually constructed endpoint lacking nonsingletonity no longer
  falsifies the strong adapter, because nonsingletonity is now an input.
* A zero-survival prefix is impossible in the positive-minimum regime; the
  debt-infimum lower bound in fact forces every selected product positive and
  the squeeze forces it to one asymptotically.
* Observer Quit mass in a prescribed cap root does not affect the
  two-counterfactual comparison, because both shifted deviations override it
  by sure Continue.  It is exactly why raw prescribed-profile gain is not
  asserted.
* Off-live-history behavior introduces no information assumption: terminal
  quitting payoffs depend on the unique all-Continue live history, as captured
  by the checked live-hazard reduction.
* Nothing in Sections 1--3 repairs observer rotation, cross-coordinate cap
  leakage, the paid residual consumer, or the full conjecture.  The note keeps
  those boundaries explicit.

## Declaration and build audit

I inspected the named declarations above under their actual imports, as well
as `QuittingMinimumLawCausalSuffixAtom` and
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`,
`FinFourMinimumAtomChronology` and
`FinFourMinimumAtomProducer.nonempty_chronology` in
`Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`,
and `FinFourThreeRoleMinimumTargetRegeneration` in
`Research/Quitting/FinFourProducerAtlas/ThreeRoleRegeneration.lean`.

At the current head, targeted Lean checks succeeded for:

* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
* `Research/Quitting/ConcentratedCollisionThreeRoleEndpointLaw.lean`;
* `Research/Quitting/FinFourProducerAtlas/ThreeRoleRegeneration.lean`; and
* `UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean`.

The proposed source-faithful wrapper itself remains ordinary mathematics
pending external formalization.
