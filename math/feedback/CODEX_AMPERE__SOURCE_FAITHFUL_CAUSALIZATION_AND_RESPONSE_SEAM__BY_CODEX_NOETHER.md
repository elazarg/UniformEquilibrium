# Review of Sections 1--3: source-faithful causalization

Reviewer: Codex Noether

## Verdict

**REVISE** for export of Sections 1--3.

The central mathematics is sound: a supplied near-minimum joint realizer can
be prefixed by arbitrarily long exact cap--Nash words without changing its
identity as the suffix chronology; the common survival tends to one; and two
counterfactual response plans which both Continue through the prefix have an
exact opponent-survival transport identity.  I found no counterexample to
those assertions, including `Never` and rank-dependent unbounded finite quit
dates.

Two repairs are required before this is an exact standalone export.

1. `ConcentratedCollisionThreeRoleEndpointLaw` does not, by its public fields
   alone, store the claimed per-rank routed **stage** mass bound by
   `packet.resolution`.  The checked theorem `perRank_mass_chain` needs the
   additional hypothesis `1 < marked.val.card`.  The adapter must state that
   hypothesis, prove a more general routed-nonempty version, accept the weaker
   positive bound obtainable from `transfer.routed_mass`, or choose new marks
   from the positive limiting law.
2. A bare `FinFourThreeRoleMinimumTargetRegeneration` does not publicly expose
   its chosen causal chronology.  Its `next.atom.chronology` is an existential
   proposition.  Although the constructor can insert the desired target
   sequence, a later consumer cannot recover that it got this particular
   witness merely from the existing regeneration fields.  The new result must
   return an explicit `FinFourMinimumAtomChronology` (or a new source-faithful
   wrapper) together with literal/propositional equalities identifying its
   profiles and marks with the incoming endpoint data.  Calling that equality
   "definitional" without putting it in the public output is too strong.

These are interface/coherence defects, not failures of the survival
calculation.  Both have direct repairs, so I do not recommend `FAIL`.

## Precise result that survives review

Let the player set be finite, let (r) be a quitting reward table, and let
(D_*>0) be the infimum of total terminal debt over actual behavioral
profiles.  Suppose

* (z=(x,\nu)) is a joint terminal semantic/law point with (D(x)=D_*);
* \(\sigma_n\) are actual profiles whose joint semantic/law points converge
  to (z);
* (T) is one fixed nonempty coalition;
* (t_n\in\mathbb N) and \(\lambda>0\) satisfy
  \(\Pr_{\sigma_n}(T\text{ at }t_n)\ge\lambda\) for every (n).

Then there exist root words (W_n) of length (n+1), each an exact cap--Nash
stack over the literal suffix \(\sigma_n\), and finite cutoffs (h_n>t_n),
such that, with

\[
 \widehat\sigma_n=W_n*\sigma_n,
 \qquad c_n=\Pr(W_n\text{ jointly Continues}),
\]

the following hold:

1. (D(\widehat\sigma_n)=c_nD(\sigma_n));
2. (D(\widehat\sigma_n)\to D_*) and (c_n\to1);
3. the suffix profiles in the construction are exactly the supplied
   \(\sigma_n\), rather than newly selected realizers;
4. \(\Pr_{\widehat\sigma_n}(T\text{ at }n+1+t_n)
   =c_n\Pr_{\sigma_n}(T\text{ at }t_n)\), hence this mass is eventually at
   least \(\lambda/2\);
5. \(\nu(T)\ge\lambda\), and eventually the (T)-mass in the suffix window
   before (h_n) is (>\nu(T)/2).

Moreover, let (o) be fixed and let (R_n^-,R_n^+) be any two complete
behavioral strategies for (o) in the suffix.  Define
\(\widetilde R_n^\pm\) to Continue surely for all (n+1) prefix stages and
then run (R_n^\pm).  If

\[
 c_{-o,n}=\prod_{q\in W_n}\prod_{i\ne o}q_i(C),
\]

then

\[
 U_o(\widehat\sigma_n[o\leftarrow\widetilde R_n^+])-
 U_o(\widehat\sigma_n[o\leftarrow\widetilde R_n^-])
 =c_{-o,n}\bigl(
 U_o(\sigma_n[o\leftarrow R_n^+])-
 U_o(\sigma_n[o\leftarrow R_n^-])\bigr).
\]

Since (c_n\le c_{-o,n}\le1), one has (c_{-o,n}\to1).  The same statement
holds simultaneously for every pair in any supplied finite response menu.

For the three-role endpoint specialization, the exact exportable statement
must add an explicit output chronology.  One adequate shape is:

```text
ConcentratedCollisionThreeRoleEndpointLaw
+ equality-arm minimum debt
+ (collision cardinality, or another marked-mass proof)
----------------------------------------------------------------
FinFourThreeRoleMinimumTargetRegeneration
+ an explicit FinFourMinimumAtomChronology of its `next`
+ chronology.profiles = incoming endpoint target-profile sequence
+ chronology.mark = incoming endpoint marked-date sequence
```

Propositional equality of the complete behavior profiles is sufficient and is
the honest public statement.  If the original marked date is not retained,
the theorem can instead choose a new finite-window mark while still retaining
the exact incoming profile sequence; that is weaker provenance and should be
said explicitly.

## Check of Sections 1 and 2

### Stack existence, length, and orientation

`exists_quittingCapNashRootStack` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`
constructs a list of every prescribed finite length.  The recursive
definition of `IsQuittingCapNashRootStack` makes the list head the outermost
root, Nash against the cap of the remaining executable literal stack.
`quittingLiteralRootStackProfile` is a `foldr`, so a word of length (n+1)
really shifts a suffix stage (t_n) to (n+1+t_n).  I found no reversed-word
or off-by-one problem.

### Exact scaling and division

`quittingTerminalDebtSum_capNashRootStack_eq` gives exactly

\[
D(W_n*\sigma_n)=c_nD(\sigma_n).
\]

The literal infimum gives (D_*\le D(W_n*\sigma_n)), while
`quittingCapNashStackContinueProduct_le_one` and nonnegative debt give
(D(W_n*\sigma_n)\le D(\sigma_n)).  Continuity of semantic total debt gives
(D(\sigma_n)\to D_*), hence the squeeze is correct.  Division is safe for
every (n), not only eventually, because

\[
 D(\sigma_n)\ge D_*>0.
\]

Thus (c_n=D(W_n*\sigma_n)/D(\sigma_n)\to1).

### Atom transport and cutoffs

`quittingStageCoalitionMass_literalRootStack_add_length` gives the exact
transport formula.  Hence a supplied λ-floor becomes an eventual
λ/2-floor after prefixing.  Coordinate convergence of terminal laws and
stage-mass domination imply \(\nu(T)\ge\lambda\).

The cutoff quantifiers are also valid.  For every sufficiently large (n),
the complete (T)-law mass of \(\sigma_n\) exceeds \(\nu(T)/2\).
`exists_finiteWindow_sum_stageCoalitionMass_gt` supplies a finite cutoff, and
replacing it by its maximum with (t_n+1) preserves the strict window bound
because all stage masses are nonnegative.  Early indices may be filled
arbitrarily because `QuittingMinimumLawCausalSuffixAtom.causal` is eventual.

### Endpoint specialization defect

`ConcentratedCollisionThreeRoleEndpointLaw.target_joint_tendsto` does give the
literal target-profile sequence required by the supplied-realizer theorem.
Its `terminalMass_floor` gives positive limiting law mass.  However the note's
claim that the structure itself stores (2.3) at the original marked dates is
not literally true of the public structure.

The checked route
`ConcentratedCollisionThreeRoleEndpointLaw.perRank_mass_chain` requires
`hcollision : 1 < marked.val.card`.  This hypothesis was used by the endpoint
constructor but is not a field of the resulting open structure.  It cannot be
silently recovered from constructor history.  Three valid repairs are
available:

* add `hcollision` to the source-faithful endpoint adapter;
* prove routing monotonicity from the stored nonemptiness of
  `routedTerminal` (the cardinality assumption in the current lemma is used
  to guarantee this nonemptiness); or
* use `transfer.routed_mass` together with the source stage-mass floor to get
  a possibly smaller fixed positive marked-stage floor.

Alternatively, `terminalMass_floor` plus `target_joint_tendsto` permits the
same finite-window selection as Section 1, but then the newly selected mark
need not be the incoming endpoint mark.

The other issue is output visibility.  `FinFourMinimumAtomProducer.atom`
contains `QuittingMinimumLawCausalSuffixAtom.chronology`, an existential.
`FinFourMinimumAtomProducer.nonempty_chronology` in
`Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`
unpacks some witness, but the existing
`FinFourThreeRoleMinimumTargetRegeneration` stores no theorem identifying
that witness with the incoming target sequence.  A source-faithful wrapper is
therefore mathematically and formally necessary.

## Check of Section 3

The opponent-survival factor is correct.  Both shifted deviations force the
observer to Continue at every prefix root.  If an opponent absorbs during the
prefix, both deviations receive the same terminal reward; on the event that
all opponents Continue, the complete suffix comparison is reached.  Product
behavior therefore yields precisely (c_{-o,n}), not joint survival.

The inequality (c_n\le c_{-o,n}\le1) is correct root by root and after
multiplication.  Thus (c_n\to1) proves (c_{-o,n}\to1).

The boundary cases are sound:

* prefixing `Never` by Continue is still `Never`;
* a finite relative date (q_n), even with (q_n\to\infty), becomes the
  finite absolute date |(W_n)|+(q_n) rankwise;
* arbitrary behavioral suffix plans work because their two prefixed versions
  agree on the only live prefix history and the future strategy is installed
  after the literal prefix.

For formalization, this should be reduced to the checked generic prefix
identity `quittingRootSequenceTerminalValue_sub_eq_jointSurvivalWeight_mul`
in `UniformEquilibrium/Quitting/Paths/SurvivalWindowLanding.lean`, after
showing that the two updated live-root sequences agree through the prefix and
that their joint survival there equals opponent survival.  The one-root
splice identity
`quittingTerminalPayoff_update_rootAndContinuationDeviation_eq` in
`UniformEquilibrium/Quitting/Root/FirstBranch.lean` gives another induction
route.

For pure-time plans specifically, most of Section 3 is already checked as
`quittingRelativePureTimeTerminalValue_sub_prefixTransport` in
`UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean`.  That
declaration explicitly includes `Never` and relative finite dates.  The new
content is therefore the source-faithful endpoint attachment and, at most,
the arbitrary-behavioral-plan adapter—not the pure-time transport formula
itself.

## Falsification attempts

* **Zero-survival prefix.**  This cannot occur under the stated positive
  minimum hypotheses: exact scaling and the literal lower bound would give
  (D_*\le0).  More quantitatively, the squeeze forces (c_n\to1).
* **Observer quits in the prescribed cap root.**  This does not spoil the
  response comparison because both counterfactual strategies override that
  action by Continue.  It does show why a raw response gain against the newly
  prefixed prescribed profile does not have the same factor; the note
  correctly declines that claim.
* **Single-player game.**  Opponent survival is identically one, and the
  response-difference identity reduces to equality.  There is no hidden need
  for a second player in Sections 1 or 3.
* **Never and escaping finite dates.**  The checked relative-pure-time
  transport theorem covers both without a compactness passage.
* **Different behavior off the live history.**  Those histories cannot affect
  terminal quitting payoffs.  The exact root-sequence prefix identity depends
  only on the live-root sequence, so no hidden observability assumption is
  introduced.
* **Endpoint object manually built outside its usual constructor.**  This
  falsifies the inference that `hcollision` is automatically available from
  the endpoint's type.  This is the reason for the first requested revision.

## Source and novelty audit

I inspected the following declarations under their actual imports:

* `IsQuittingCapNashRootStack`, `exists_quittingCapNashRootStack`,
  `quittingTerminalDebtSum_capNashRootStack_eq`, and
  `quittingCapNashStackContinueProduct_le_one` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`;
* `quittingStageCoalitionMass_literalRootStack_add_length`,
  `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom`, and
  `QuittingMinimumLawCausalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
* `ConcentratedCollisionThreeRoleEndpointLaw.target_joint_tendsto`,
  `sourceMarkedStageMass_le_routedTargetStageMass`, and
  `perRank_mass_chain` in
  `Research/Quitting/ConcentratedCollisionThreeRoleEndpointLaw.lean`;
* `ConcentratedCollisionThreeRoleEndpointLaw.nonempty_finFourMinimumTargetRegeneration`
  in `Research/Quitting/FinFourProducerAtlas/ThreeRoleRegeneration.lean`;
* `FinFourMinimumAtomChronology` and
  `FinFourMinimumAtomProducer.nonempty_chronology` in
  `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`;
* `quittingRootSequenceTerminalValue_sub_eq_jointSurvivalWeight_mul` in
  `UniformEquilibrium/Quitting/Paths/SurvivalWindowLanding.lean`; and
* `quittingRelativePureTimeTerminalValue_sub_prefixTransport` in
  `UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean`.

Section 1 is a useful supplied-witness specialization of an existing checked
causalization proof, not a new survival theorem.  Section 2 contains the main
new conjecture-facing content: it can remove the documented independent
realizer selection from minimum endpoint regeneration, provided the exact
chronology is made a public output.  Section 3 is a valid supporting adapter;
its pure-time part substantially overlaps a checked theorem, while its
arbitrary-behavioral extension is a straightforward specialization of the
checked generic prefix-scaling identity.

After the two requested interface repairs, Sections 1--3 form a defensible
standalone export as a strict provenance strengthening.  They still do not
consume the regenerated paid packet, prevent observer rotation, control
spectator cap leakage, or imply a uniform-equilibrium payoff.
