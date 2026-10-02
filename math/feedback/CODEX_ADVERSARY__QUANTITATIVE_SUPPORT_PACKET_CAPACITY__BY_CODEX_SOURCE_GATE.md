# Export-gate source audit: quantitative support-packet capacity

**Reviewer:** `CODEX_SOURCE_GATE`  
**Date:** 2026-08-30  
**Object reviewed:**
[`CODEX_ADVERSARY__QUANTITATIVE_SUPPORT_PACKET_CAPACITY.md`](../notes/CODEX_ADVERSARY__QUANTITATIVE_SUPPORT_PACKET_CAPACITY.md)  
**Verdict:** **FAIL as a current export packet.**  Theorem 1 and Corollaries
2--3 are correct ordinary mathematics with the stated one-tolerance constants.
Section 4 is not correct at its present level of generality.  More
fundamentally, the central capacity bound is precisely the kind of
"approximate-capacity barrier with no source consequence" excluded by the
maintained question until it is composed with a terminal consumer, renewable
finite rank, or complete positive-gap table.  The correct generic theorem is
worth retaining and formalizing, but it does not by itself cross the current
conference export boundary.

No author note, export, or Lean source was modified.

## 1. Claim audited and exact sources

The central claim is the following.  If a finite quitting reward table has an
unrestricted-behavior terminal exploitability gap \(\gamma>0\), and if
\(m\) closed balls of radius \(\delta/3\) cover a fixed compact payoff carrier,
then, below the displayed gap-dependent error scale, every support-\(\delta\),
punishment-floor, exact forward Bellman packet has raw absorption strictly
less than \(2m\).

I inspected the following declarations and their proofs narrowly.

- `exists_same_label_with_large_charge_gap` and
  `exists_close_pair_with_large_charge_gap_of_finite_labels` in
  `MathUE/FiniteChargedReturn.lean`;
- `exists_charge_threshold_for_close_pair_of_compact` in
  `MathUE/CompactFiniteChargedReturn.lean`;
- `QuittingFiniteForwardPacket`,
  `exists_singleSeamProjectiveLasso_of_finiteForwardPackets`, and
  `quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets` in
  `UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`;
- `quittingFiniteSingleSeamProjectiveLasso_of_reversedForwardBlock` in
  `UniformEquilibrium/Quitting/Projective/ForwardBlockSingleSeam.lean`;
- `QuittingFiniteSingleSeamProjectiveLasso.exists_supportRationalDivergentPath`
  in
  `UniformEquilibrium/Quitting/Projective/SingleSeamProjectiveLasso.lean`;
- `exists_isεAsymptoticNash_of_divergentAbsorption_supportRationalPath` in
  `UniformEquilibrium/Quitting/Paths/SupportWitnessPathCompiler.lean`;
- `HasTerminalExploitabilityGap` in
  `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`;
- `QuittingTerminalExploitabilityWitness.terminalExploitability` in
  `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityWitness.lean`;
- `quittingRewardBound` in
  `UniformEquilibrium/Quitting/RewardBound.lean`;
- `terminalExploitabilityGap_le_two_mul_bound` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/NormalTerminalGapConstrainedStationary.lean`;
  and
- `FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean`.

For nonduplication I also compared Proposition 5.1 and Section 7 of
[`CODEX_ADVERSARY__TWO_ROOT_SWITCH_FORWARD_PACKET_BARRIER.md`](../notes/CODEX_ADVERSARY__TWO_ROOT_SWITCH_FORWARD_PACKET_BARRIER.md),
and the live acceptable-answer boundary in
[`FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md`](../archive/FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md).

## 2. The correct central calculation

Let \(q_u\in[0,1]\) be the one-row absorption masses.  If their total is at
least \(2m\), label every displayed value by one of the supplied ball centres.
Two values with the same label have distance at most

\[
 2\delta/3<\delta.
\]

The finite labelled charged-return theorem gives \(s<t\) with

\[
 \operatorname{dist}(U_s,U_t)<\delta,
 \qquad \sum_{u=s}^{t-1}q_u\ge1.                       \tag{2.1}
\]

Since all \(q_u\) lie in \([0,1]\), the checked product estimate used by the
finite-forward compiler gives

\[
 W:=1-\prod_{u=s}^{t-1}(1-q_u)\ge\frac12.              \tag{2.2}
\]

Reverse the forward block.  Exact Bellman recursion makes every nonclosing
policy equation exact.  The support error is \(\delta\), the endpoint seam is
at most \(\delta\) in every coordinate, and

\[
 \delta\le (\delta+\delta)W.
\]

Thus
`quittingFiniteSingleSeamProjectiveLasso_of_reversedForwardBlock` produces a
lasso of error

\[
 e=2\delta.                                             \tag{2.3}
\]

The floor \(P-\delta\le U\) is stronger than the required lasso floor
\(P-2\delta\le U\).  One small proof obligation omitted from the prose should
be stated: (2.1), nonnegativity of all \(q_u\), and positivity of the sum imply
that some row has \(q_u>0\); its reversed phase supplies the lasso's required
`absorbingPhase` field.

The lasso-to-path theorem doubles both tolerances.  The path therefore has
support and rationality error \(4\delta\).  Substitution into the checked path
compiler gives one actual behavioral profile with unrestricted unilateral
exploitability at most

\[
 2(4\delta)+4\delta+\sqrt{4\delta}(2+7B)
 =12\delta+2C\sqrt\delta,
 \qquad C=2+7B.                                        \tag{2.4}
\]

`HasTerminalExploitabilityGap` quantifies over the same full behavioral
strategy class.  Applying it to that profile yields the reverse lower bound
\(\gamma\), hence

\[
 \gamma\le12\delta+2C\sqrt\delta.                      \tag{2.5}
\]

Solving equality after setting \(x=\sqrt\delta\) gives exactly

\[
 \delta_*=
 \frac{(\sqrt{C^2+12\gamma}-C)^2}{144}.
\]

Therefore the contradiction for \(0<\delta<\delta_*\) is correct.  There is
no stationary-deviation, bounded-controller, expectation, or stopping-time
weakening in this composition.

The coordinate estimate

\[
 B\le |I|(2^{|I|}-1)M
\]

also follows exactly from `quittingRewardBound`, which is the sum of the
absolute values of all coordinates over all nonempty coalitions.

## 3. Prescribed-cover source correction

The numerical \(2m\) bound is correct, but the direct source named for it must
be changed.  `exists_charge_threshold_for_close_pair_of_compact` chooses its
own finite cover internally.  Its public conclusion does not return the
threshold associated with an arbitrarily supplied cover \(F\).

For the theorem as stated, the direct checked input is
`exists_close_pair_with_large_charge_gap_of_finite_labels`: choose one
supplied centre covering each \(U_t\), use the centre as the finite label, and
use the \(2\delta/3<\delta\) same-label diameter estimate.  Compactness is not
used after \(F\) has been supplied; its only role is to guarantee that some
finite cover exists.

This is a source/formalization repair, not a defect in the ordinary theorem.
The export statement should also name the actual payoff topology: the
repository's finite-product metric on `Payoff I`.  The coordinate seam follows
from `dist_le_pi_dist`.

## 4. Fatal defect in the Fin4 application

Let \(a\)'s Quit probability be \(1-\varepsilon\), let \(k\)'s Quit
probability be \(t\in(0,1)\), and suppose the \(k\)-collision increment is at
least \(\gamma\).  If both relevant terminal and continuation coordinates
have absolute value at most \(M\), the \(k\)-endpoint difference satisfies

\[
 D_k\ge \gamma-\varepsilon(\gamma+2M).
\]

Because \(k\) plays Continue with positive probability, support-\(\delta\)
Nash gives \(D_k\le\delta\), and hence

\[
 \varepsilon\ge
 \frac{\gamma-\delta}{\gamma+2M}.                      \tag{4.1}
\]

This is a **lower bound on Continue probability**, hence an upper bound on
the owner Quit probability.  It does not imply that the row has absorption
at least one half.  For example, set \(M=\gamma=1\),

\[
 \varepsilon=99/100,
 \qquad t=1/1000,
 \qquad r_k(\{a,k\})=1,
 \qquad r_k(\{a\})=r_k(\{k\})=0,
 \qquad U_k=1/99.
\]

Then \(D_k=0\), so the two supported actions of \(k\) meet even zero-error
support optimality in this coordinate, while the joint absorption is

\[
 1-(99/100)(999/1000)=1099/100000<1/2.
\]

The `<4m` conclusion is valid only if "literal scale" is explicitly defined
as the equality choice

\[
 \varepsilon=(\gamma-\delta)/(\gamma+2M),
\]

or if an independent upper bound \(\varepsilon\le\bar\varepsilon<1\) or
Quit floor \(t\ge\tau>0\) is assumed.  The note's general bound
`number < 2m/(1-barEpsilon)` is correct under the stated upper bound.

There is a second missing hypothesis in the derivation of (4.1): a coordinate
bound on terminal rewards does not bound an arbitrary carrier value.  An
all-Continue Bellman step can retain a continuation coordinate outside the
reward box.  Add either

\[
 K\subseteq[-M,M]^I
\]

or the local hypothesis \(|U_{t,k}|\le M\) at every counted switch date.
The intended actual terminal-payoff carrier may have this property, but
`QuittingFiniteForwardPacket` does not include it automatically.

The final observation about the canonical descreened row is otherwise
correct: \(t=1/2\) itself gives a charge floor, while its supported
\(k\)-endpoint gap at least \(\gamma/2\) prevents it from entering the
small-support-error regime.

## 5. Novelty and maintained-question fit

The qualitative fixed-error compact-capacity theorem and the calculation

\[
 \gamma\le6e+(2+7B)\sqrt{2e}
\]

already appear in Proposition 7.1 and Proposition 5.1 of the author's earlier
two-root-switch note.  Relative to that conference record, the new content is
the prescribed-cover \(2m\) wrapper and the explicit coordinate-bound
corollary.  Relative to checked Lean, it is useful to expose the following
facts now buried in compiler proofs:

1. a terminal-gap exclusion for one supplied single-seam lasso; and
2. a one-packet-to-lasso wrapper for a supplied finite cover.

That is legitimate formalization infrastructure, but it does not yet answer
the maintained question.  The question
`FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md` accepts a negative
capacity result only when the source-derived barrier is carried to a terminal
consumer, renewable finite rank, or complete positive-gap table.  It lists an
"approximate-capacity barrier with no source consequence" as a nonanswer.

Here the gap is assumed at the start, and the resulting capacity bound is not
fed back into a hard-residual transition, rank, or constructed table.  Section
4 merely says how many rows of an independently imposed charge scale could
occur; no source theorem forces those rows onto one packet.  Thus the note is
a correct conditional restriction on a hypothetical counterexample, not a
complete positive or negative answer to the live producer question.

## 6. Eight export criteria

| Criterion | Result | Required repair |
|---|---|---|
| 1. Exact self-contained statement | **FAIL** | Define product roots, the payoff metric, Bellman map, support-local Nash, behavioral punishment value, and `HasTerminalExploitabilityGap`; specify all coercions and the role of a supplied cover. |
| 2. Complete proof/no deferred lemma | **FAIL current packet** | Theorem 1 is complete after adding the positive absorbing-phase argument and direct finite-label cover step.  Correct or remove Section 4. |
| 3. Probability/agency audit | **FAIL presentation** | State explicitly that roots randomize independently in each row, histories are publicly observed as in the quitting game, absorption is the first nonempty Quit coalition, and the terminal gap/path compiler use unrestricted behavioral unilateral deviations. |
| 4. Adapter/consumer or named obligation | **FAIL** | Supply the source consequence required by `FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md`; a standalone barrier is explicitly a nonanswer there. |
| 5. Positive and negative boundary tests | **FAIL** | Add exact tests for absence of a terminal gap, strictness/equality of the error threshold, a packet below the `2m` trigger, and the Fin4 low-charge regression above. |
| 6. Source and nonduplication audit | **FAIL current text** | Cite the finite-label theorem for prescribed `F`, distinguish direct `HasTerminalExploitabilityGap` from the packaged witness field, and narrow novelty against the earlier two-root-switch note. |
| 7. Independent review(s) | **FAIL unresolved** | The existing independent review and this audit agree on the Section 4 defect.  Resolve it and obtain a clean post-repair review.  The unrestricted-behavior semantic claim warrants retaining both reviews and the explicit falsification attempt. |
| 8. Lean handoff | **PASS with minor repair** | The proposed split into a generic lasso exclusion and a finite-cover packet wrapper is formalizable and does not assume the conclusion.  Add `exists_close_pair_with_large_charge_gap_of_finite_labels` and the positive-phase extraction to the handoff. |

## 7. Strengthening and recommended disposition

A sharper natural theorem separates support error \(\delta\) from seam radius
\(\eta\).  If \(0<\eta\le\delta\), and \(m_\eta\) balls of radius
\(\eta/3\) cover the carrier, charge \(2m_\eta\) gives a lasso of error

\[
 e=\delta+\eta.
\]

The exact contradiction condition becomes

\[
 6(\delta+\eta)+(2+7B)\sqrt{2(\delta+\eta)}<\gamma.     \tag{7.1}
\]

This is stronger than fixing \(\eta=\delta\), and it isolates topology from
support accuracy.  In particular, after choosing a sufficiently small
positive \(\eta\), fixed support error is excluded up to

\[
 \delta<
 \frac{(\sqrt{C^2+12\gamma}-C)^2}{72},
\]

twice the note's one-tolerance threshold.  This strengthening is optional for
correctness but preferable in a reusable formal theorem.

Recommended disposition:

- retain/formalize the generic lasso exclusion and prescribed-cover wrapper
  as internal infrastructure;
- remove Corollary 3 from the novelty claim, since it is a direct tolerance-
  weakening specialization of the checked finite-forward consumer;
- correct or quarantine the Fin4 counting application; and
- do **not** place a packet in `exports/` until a source consequence closes or
  strictly narrows the maintained question in the sense its own acceptable-
  answer section requires.
