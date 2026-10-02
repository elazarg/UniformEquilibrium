# Fin4 minimum-return silent-padding two-cut source adapter

Authors: `CODEX_DESCENDANT`

Independent review:
[PAIRED_HULL_REVIEW](../feedback/CODEX_DESCENDANT__POSTMARK_IMMEDIATE_ATOM_OR_REACHED_TWO_CUT__BY_PAIRED_HULL_REVIEW.md)

## Exact statement

In a finite quitting game, every player independently chooses Continue or
Quit at every live date. The first nonempty quitting coalition \(S\) ends the
game with payoff \(r(S)\); all-Never has payoff zero. For an actual behavioral
profile \(\sigma\), write

\[
 U_i(\sigma)
\]

for its terminal payoff and

\[
 B_i(\sigma)=\sup_{\tau_i}U_i(\tau_i,\sigma_{-i})
\]

for the unrestricted cap. The supremum covers every unilateral behavioral
replacement, including Never, randomized hazards, and arbitrarily late pure
stopping times. Put

\[
 d_i(\sigma)=B_i(\sigma)-U_i(\sigma),
 \qquad
 D(\sigma)=\sum_i d_i(\sigma).
\]

Let \(s_n\) be actual behavioral profiles on `Fin 4` whose joint
semantic/law points converge along one strict subsequence:

\[
 (Z(s_n),\nu_n)\longrightarrow (z_*,\nu),
 \qquad D(Z(s_n))\longrightarrow D_*>0,
 \tag{1.1}
\]

where \(z_*\) is a global minimum and the same quantitative Fin4 hard
residual is retained.  In the atlas application, \(s_n\) is literally the
continuation after the forced-pair date in rank \(n\) of one
`FinFourMinimumReturnPacket`.

The positive-finite-atom theorem selects one fixed nonempty coalition \(A\)
with

\[
 \mu:=\nu(A)>0.
 \tag{1.2}
\]

Write

\[
 w_{n,t}(A)
 =\Pr_{s_n}(\text{first terminal coalition is }A\text{ at date }t).
 \tag{1.3}
\]

Then

\[
 \sum_{t\ge0}w_{n,t}(A)=\nu_n(A)\longrightarrow\mu.
 \tag{1.4}
\]

Then, for every fixed \(0<\chi<\mu\), after deleting finitely many indices
there are positive integers \(e_n\) and profiles \(\bar s_n\), obtained by
prefixing one deterministic all-Continue row to \(s_n\), which instantiate
`QuittingUniformlyReachedPostMarkTwoCutBlock` with

\[
 \operatorname{markedRow}=0,
 \qquad
 \operatorname{entryCut}=1,
 \qquad
 \operatorname{exitCut}=e_n+1,
 \tag{1.5}
\]

with entry reach exactly one and total marginal Quit hazard strictly greater
than \(\chi\) between the cuts. The entry suffix has the same live-root
semantics as \(s_n\), and the exit suffix has the same live-root semantics as
\(\operatorname{suffix}_{e_n}s_n\).

## Proof

### Universal silent-padding construction

Fix once and for all any

\[
 0<\chi<\mu.
 \tag{2.1}
\]

For example, \(\chi=\mu/2\).  By (1.4), eventually \(\nu_n(A)>\chi\).
For every such \(n\), countable additivity gives a finite integer
\(e_n>0\) with

\[
 \sum_{0\le t<e_n}w_{n,t}(A)>\chi.
 \tag{2.2}
\]

Construct \(\bar s_n\) by prefixing one deterministic all-Continue product
root to \(s_n\).  Thus the new date zero is terminally silent and, on its
probability-one all-Continue branch, the literal continuation is exactly
\(s_n\).  Put

\[
 \operatorname{markedRow}_n=0,
 \qquad
 \operatorname{entryCut}_n=1,
 \qquad
 \operatorname{exitCut}_n=e_n+1.
 \tag{2.3}
\]

Then:

1. \(0<1<e_n+1\);
2. joint reach from the start of \(\bar s_n\) to the entry cut is exactly
   one;
3. the roots in the block \([1,e_n+1)\) are literally the roots of \(s_n\)
   at dates \([0,e_n)\); and
4. the exit suffix is literally \(\operatorname{suffix}_{e_n}s_n\).

At every original date \(t\), stage mass factors as live mass times the
conditional root coalition mass.  Hence

\[
 w_{n,t}(A)
 \le \Pr_{q_{n,t}}(\text{absorb})
 \le \sum_{i<4}q_{n,t,i}(Q).
 \tag{2.4}
\]

Summing (2.4) over the finite window in (2.2) gives

\[
 \sum_{0\le t<e_n}\sum_{i<4}q_{n,t,i}(Q)>\chi.
 \tag{2.5}
\]

Therefore \(\bar s_n\), with (2.3), is a literal
`QuittingUniformlyReachedPostMarkTwoCutBlock` with

\[
 \operatorname{reachFloor}=1,
 \qquad
 \operatorname{hazardFloor}=\chi.
 \tag{2.6}
\]

The all-Continue prefix changes neither prescribed payoff nor terminal law.
Its effect on the unrestricted cap is

\[
 U_i(\bar s_n)=U_i(s_n),
 \qquad
 B_i(\bar s_n)=\max\{r_i(\{i\}),B_i(s_n)\},
 \qquad
 \mathcal L(\bar s_n)=\mathcal L(s_n).
 \tag{2.7}
\]

Indeed, a deviator either Quits at the new silent row and receives its
singleton reward, or Continues and then has exactly its original unrestricted
response problem.  At the limiting positive global minimum, the checked
singleton margin gives

\[
 B_i(z_*)\ge r_i(\{i\})+D_*
 \qquad(i<4).
 \tag{2.8}
\]

Cap-coordinate convergence in (1.1) therefore makes
\(B_i(s_n)>r_i(\{i\})\) for every player eventually.  After deleting that
finite prefix, (2.7) improves to the full semantic equality

\[
 Z(\bar s_n)=Z(s_n).
 \tag{2.9}
\]

The padding also introduces no scaling into any update made from the entry
profile, because entry is reached with probability one.  Thus the two-cut
entry profile has semantic pair \(Z(s_n)\), and its paid splice is the silent
prefix of the corresponding actual update of \(s_n\).

This proves the adapter.  No split according to the location of the atom is
needed.

### Checked two-cut consequence

Put

\[
 K=(1-e^{-\chi})D_*,
 \qquad
 \delta={e^\chi-1\over2}D_*.
 \tag{3.1}
\]

The checked positive-minimum two-cut theorem gives, at every retained rank,
one of:

\[
 D(\operatorname{suffix}_{e_n}s_n)\ge D_*+\delta,
 \tag{3.2}
\]

or some player \(p_n\) with

\[
 d_{p_n}(s_n)>K/8.
 \tag{3.3}
\]

In the second arm, choose tolerance \(K/16\).  The Fin4 paid-splice theorem
supplies an unrestricted behavioral replacement of \(p_n\), starting in
the literal profile \(s_n\), whose payoff gain is strictly greater than

\[
 K/16,
 \tag{3.4}
\]

whose updated entry-profile \(p_n\)-debt is at most \(K/16\), and whose
whole padded-parent debt decrease equals the same gain exactly.  Because the
silent row has reach one, (3.4) has no extra reach factor.

After finite-label subsequence selection, either (3.2) holds throughout or
one fixed payer realizes the paid arm throughout.  Neither conclusion is
yet a return or a renewable source transition.

## Conjecture-facing change

The checked declaration
`QuittingUniformlyReachedPostMarkTwoCutBlock.finFour_offMinimum_or_exists_paidSplice`
previously consumed a supplied reached two-cut block.  The construction above
supplies that input from every `FinFourMinimumReturnPacket`, using its exact
post-date tail family and one finite atom of the limiting minimum law.

This closes the source side of the weak post-mark two-cut interface.  The
live obligation is narrowed to the two outputs in
[`FIN4_POST_MARK_TWO_CUT_RENEWABLE_CHILD_SOURCE.md`](../questions/FIN4_POST_MARK_TWO_CUT_RENEWABLE_CHILD_SOURCE.md):
consume the literal off-minimum exit (3.2), or consume and regenerate the
actual paid splice (3.3)--(3.4).  This result does not solve that consumer
question.

## Adapter and consumer

For a checked `FinFourMinimumReturnPacket parent`, at source rank \(n\) let
\(m_n\) be its retained forced-pair stage and define

\[
 s_n=\operatorname{quittingAllContinueProfileSpine}
   (\operatorname{reward},
    (\operatorname{packet.stream.frame}\ n).\operatorname{targetProfile},
    m_n+1).
 \tag{4.1}
\]

The named source equalities

* `FinFourStabilizedForcedPairStream.tail_eq_framePostDateTail`,
* `FinFourMinimumReturnPacket.forcedPairTail_eq_tail`, and
* `FinFourMinimumReturnPacket.tailDebt_tendsto_minimum`

identify (4.1) with the packet's literal post-date tail and give
\(D(s_n)\to D_*\).  Joint compactness is applied to this same sequence; it
does not replace the profiles.  At the resulting minimum joint-law limit,
`exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` supplies
\(A\) and \(\mu>0\).  Equations (2.1)--(2.6) then construct the padded
two-cut block rank by rank from these exact \(s_n\).

The production adapter packages:

1. the existing strict refinement carrying joint semantic/law convergence;
2. a fixed \(\chi\), preferably \(\mu/2\);
3. finite truncations \(e_n\) of the same atom coordinate;
4. the root sequence obtained by prepending `quittingAllContinueRoot`; and
5. eventual cap neutrality from
   `minimumTerminalSemantic_singletonMargin`; and
6. the exact shift identities for entry, exit, payoff, cap, law, and paid
   update.

No new game-theoretic hypothesis, source causalization, or response
selection is used in constructing the block.  Its checked downstream
consumer is
`QuittingUniformlyReachedPostMarkTwoCutBlock.finFour_offMinimum_or_exists_paidSplice`,
which returns precisely (3.2) or (3.3)--(3.4).

## Definitions and assumptions

All probabilities are taken under the ordinary product law of the displayed
behavioral profile.  Entry reach is unconditional from the beginning of the
padded profile.  The hazard sum is a sum of conditional marginal Quit
probabilities at the actual live roots; it is not terminal-law mass or exact
cap-root absorption.

The paid splice changes one player's complete behavioral strategy.  It is
approximately cap-attaining; no compactness or attainment of the behavioral
strategy supremum is assumed.  Because only that player's own strategy is
changed, its cap against the fixed opponents is unchanged, which is why its
debt decrease equals its payoff gain.  No cap equality is asserted for the
other players.

### Artificial-mark boundary

The row named `markedRow` in (2.3) is only a terminally silent padding row
inserted to satisfy the structural inequality in the checked record.  It is
not:

* the original forced-pair mark;
* a positive stage atom;
* a paid first-disagreement row;
* an exact cap--Nash certificate; or
* a row reached in the original unpadded chronology.

This is mathematically legitimate for the present two-cut consumer because
the checked theorems use only `markedRow_lt_entryCut`; they never charge,
inspect, or preserve the marked row.  It also exposes the exact specification
boundary: `QuittingUniformlyReachedPostMarkTwoCutBlock` encodes a positive
entry/hazard window preceded by one row, not ancestry from a strategically
meaningful mark.  Any later theorem that needs a retained marked atom or paid
row must carry that datum in a stronger source-indexed structure and cannot
recover it from this adapter.

The checked two-cut structure is built from a displayed root sequence.  The
canonical history-independent profile reconstructed from that sequence has
the same live roots as the literal profile
`quittingRootThenContinuationProfile reward quittingAllContinueRoot s_n`.
All payoff, cap, law, entry, exit, and paid-splice claims use the standard
live-root/canonical-profile equality.  Definitional equality of the two
complete off-path behavioral strategy objects is neither needed nor claimed.

Reattaching the padded tail behind the original pure forced-pair mark keeps
that earlier root literal, but its joint-Continue probability may be zero.
Consequently (3.4) is not a positive-gain deviation of the original
forced-pair profile.

## Source correspondence

The checked source declarations are:

* `FinFourStabilizedForcedPairStream.tail_eq_framePostDateTail` and
  `FinFourMinimumReturnPacket.tailDebt_tendsto_minimum` in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionAtlas.lean`;
* `FinFourMinimumReturnPacket.forcedPairTail_eq_tail` and
  `FinFourMinimumReturnPacket.normalizedDecoratedFamily_postDateSpine_eq_reference`
  in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionConsumers.lean`;
* `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
* `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`;
* `quittingRootCoalitionMass_le_absorptionMass_of_nonempty` and
  `quittingRootAbsorptionMass_le_sum_quitRates`; and
* `QuittingUniformlyReachedPostMarkTwoCutBlock.finFour_offMinimum_or_exists_paidSplice`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveMinimumTwoCutPaidSplice.lean`.

The finite-window estimate with `entryCut = 0` follows directly from the
positive limiting atom and was already part of the source analysis.  It does
not inhabit the checked strict post-mark wrapper because no natural-number
`markedRow` precedes zero.  The new content is the exact silent-padding
adapter from that window to the checked structure, the cap maximum formula,
and the composition with the literal Fin4 minimum-return source.

No original-paper theorem is translated.  The result is an internal
composition of checked quitting-game semantics and the elementary finite
window proof above.  It gives no strong two-return conclusion: exit-suffix
near-minimality, exact Nash--Bellman roots in the block, renewal, and terminal
consumption remain absent.

## Boundary tests

### Unpadded location corollary

If one insists that every named row belong to the original \(s_n\), take the
fixed threshold \(\mu/8\).  After a strict subsequence, either

\[
 w_{n,0}(A)\ge\mu/8
 \tag{7.1}
\]

cofinally, or

\[
 w_{n,0}(A)<\mu/8,
 \qquad
 \sum_{t\ge1}w_{n,t}(A)>5\mu/8
 \tag{7.2}
\]

eventually.  In the second arm choose \(e_n>1\) with

\[
 \sum_{1\le t<e_n}w_{n,t}(A)>\mu/2.
 \tag{7.3}
\]

Then survival to date one is greater than \(5\mu/8\), and the marginal
hazard in \([1,e_n)\) is greater than \(\mu/2\).  This is the exact
unmodified-profile dichotomy checked by `FablePostmarkAtomBlock`.  The first
arm can itself be treated as a one-row block only after padding or by using
the weaker `entryCut = 0` structure.

### Timing and cap regressions

If \(s_n\) absorbs surely in \(A\) at date zero, no positive hazard need
remain after its first row.  The padded construction still works: the
original date-zero row becomes the block row at padded date one.  If \(s_n\)
Continues at date zero and absorbs surely at date \(N\), the same construction
selects a window ending after date \(N\).  Thus the universal adapter covers
both endpoint timings without pretending that hazard renews after the atom.

Cap neutrality genuinely uses the minimum margin.  For a local regression,
let one opponent Quit surely at the original date zero and let all remaining
opponents Continue.  Give player \(i\) payoff zero both from joining that
quitter and from Continuing while it Quits, but give \(i\) singleton reward
one.  Against the original profile, every response of \(i\) pays zero, so its
cap is zero.  Prefixing one all-Continue row gives \(i\) the new option to
Quit alone for one, raising its cap to one while leaving the prescribed law
and payoff unchanged.  Hence an arbitrary silent prefix need not preserve the
semantic pair; (2.8) is the exact source-specific repair.

## Scope and nonclaims

The theorem does not supply:

* a literal downstream block after an independently selected paid row;
* a near-minimum exit suffix;
* positive outer reach through the original pure forced pair;
* target-side control of the other three unrestricted caps;
* a source-preserving child with a renewable finite rank;
* a charged admissible-payoff return;
* terminal approximants or a uniform-equilibrium payoff.

## Lean handoff

The narrow implementation has two parts.

1. Prove a general finite-player constructor from an actual profile family,
   one terminal label with limiting mass \(\mu>0\), and \(0<\chi<\mu\).  It
   should select finite windows and construct padded
   `QuittingUniformlyReachedPostMarkTwoCutBlock`s with mark zero, entry one,
   reach one, and hazard floor \(\chi\).  It should expose the exact
   payoff/law identities and cap maximum formula (2.7).
2. Prove a `FinFourMinimumReturnPacket` adapter which jointly compactifies
   the exact tails (4.1), selects the finite atom, invokes the general
   constructor, proves eventual cap neutrality from
   `minimumTerminalSemantic_singletonMargin`, and returns the checked
   off-minimum/paid split with constants (3.1)--(3.4).

Define the padded root sequence by `quittingAllContinueRoot` at date zero and
the original `quittingProfileLiveRoot` shifted by one thereafter.  Use the
canonical live-root profile identities rather than asserting definitional
equality of complete off-path strategies.  Immediate sure absorption,
delayed sure absorption, and the cap-raising regression are the relevant
finite tests.

## Lean formalization record

The packet prefix above had SHA-256
`09a57ab443e7093295f8c604b7f476d20480932724066ed0fa4ff59a12d2fa9d`.
Its checked production and Research implementation landed in commit
`99777dc725859cd4321de692a5b728bcf537a441`.

The generic silent-prefix mechanics are owned by
`quittingSilentPrefixRoots` and
`quittingRootSequenceProfile_silentPrefix_succ` in
`UniformEquilibrium/Quitting/Paths/RootSequenceSilentPrefix.lean`.
`quittingTerminalSemanticPair_rootSequenceProfile_profileLiveRoot` and
`quittingTerminalPayoff_rootSequence_silentPrefix_eq` in
`UniformEquilibrium/Diagnostics/Quitting/SilentPrefixTerminalSemantics.lean`
give the exact live-root semantic transport and the coordinatewise
singleton-reward maximum formula for the unrestricted cap.

The finite-window and block construction is checked in
`UniformEquilibrium/Diagnostics/Quitting/SilentPaddingTwoCutSource.lean`.
In particular,
`quittingTerminalOutcomeMass_rootSequence_silentPrefix_eq` preserves the
complete terminal outcome law, including Never;
`quittingSilentPaddingTwoCutBlock_entryReach_eq_one` gives literal entry
reach one; and
`exists_finFour_silentPaddingTwoCutBlock_with_paidSpliceAlternative` returns
the exact Fin4 off-minimum-or-paid-splice alternative with the packet's
constants and update identities.

`FinFourMinimumTailFiniteAtomCompactification.eventually_nonempty_silentPaddingTwoCutRealization`
in
`UniformEquilibrium/Diagnostics/Quitting/MinimumTailSilentPaddingConsumer.lean`
uses one common joint compactification and one fixed positive finite-law atom
at every sufficiently late retained rank. The standard finite-label
subsequence corollary is supplied by
`Math.exists_fixed_label_on_strictMono_subsequence` in
`MathUE/Topology/FiniteLabelSubsequence.lean`.
Finally,
`FinFourMinimumReturnPacket.exists_finiteAtomCompactification_eventually_silentPaddingTwoCutRealization`
in
`Research/Quitting/FinFourProducerAtlas/MinimumReturnPacketSilentPaddingAdapter.lean`
is the literal adapter from the actual minimum-return packet tails.

The generic construction and supplied-data compiler have seals `M` and `L`.
The Research minimum-return adapter supplies branch-local source seal `A`.
Calling the already checked two-cut alternative gives `C` only for that
local off-minimum-or-paid-splice split. There is no renewable child, return,
meaningful chronology through the artificial row, Nash certificate,
nonpayer cap control, terminal approximation, or uniform-equilibrium payoff.
