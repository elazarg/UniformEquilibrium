# Review of arbitrary-clock purification to the off-minimum port

**Reviewer:** `SOCIAL_WEIGHT_REVIEW`  
**Verdict:** PASS, with bounded statement/API clarifications before export

## Claim checked

Starting from one actual realizing sequence whose complete terminal-semantic
debt converges to the positive global minimum, purify the players one at a
time to pure stopping times or Never.  A strict-debt limit gives an actual
off-minimum paid port.  If every purification limit remains minimal, finite
calendar-type stabilization produces one actual canonical pure-clock global
minimum, to which the reviewed deadline-rank theorem applies.

I tried to falsify the argument at the arbitrary-support selection, cap
transport, iteration, unbounded deadline, exact-attainment, and source
provenance steps.  I found no mathematical counterexample.

## 1. Arbitrary-support selection is valid

Against fixed opponents, one player's behavioral strategy induces a
probability law on `Option Nat`, and its payoff is the expectation of the
pure-time/Never payoff function.  Therefore some point in the positive
support has payoff at least the average.  For a completely formal proof, if
all positive-support values were strictly below the average, select any one
positive-support point; its weighted deficit is strictly positive and every
other weighted deficit is nonnegative, contradicting zero total deficit.

Replacing the player by this pure point weakly raises that player's payoff.
The player's unrestricted cap is exactly unchanged because only its own
strategy changed.  The note correctly makes no assertion about any other
cap.  In particular, the construction does not rely on cap attainment or on
continuity of caps under a deadline escaping to infinity.

## 2. Sequential purification survives cap leakage

Later replacements leave the already purified players' literal strategies
pure, although their payoffs, caps, and debts can change.  This is all the
induction needs.  At each stage, boundedness of complete terminal-semantic
debt permits a convergent scalar subsequence, and global minimality forces
its limit to be at least (D_*).

If the limit is strictly larger than (D_*), a finite discard supplies a
uniform positive excess.  In Fin4 a stabilized maximum-debt player has a
uniform positive debt floor.  The actual-reach paid-first-disagreement
theorem applies to the original mixed target profile and covers
unrestricted behavioral responses; it does not require replacing the source
by a positive-support pure component.  Thus the strict branch is genuinely
source attached.

The note should state one concrete chosen floor, rather than only “fixed
positive debt floor.”  For example, if the excess limit is
(L-D_*=2\varepsilon>0), then eventually

\[
 D(\operatorname{Sem}(\sigma_n^{k+1}))\ge D_*+\varepsilon,
\]

and the stabilized maximum debtor has debt at least
((D_*+\varepsilon)/4).  Any smaller fixed (\Delta>0) can be fed to the
actual-reach theorem.

## 3. The finite calendar quotient is exact

The proposed calendar data are sufficient.  For each player, remove that
player from the ordered tie partition and inspect the earliest remaining
opponent block.  If it exists at date (m), every pure response has exactly
one of the three values

\[
 s_i,\qquad r_i(A\cup\{i\}),\qquad r_i(A),
\]

according as it stops before, at, or after (m).  The early singleton option
is present exactly when (m>0).  The ordered partition plus the global
zero/positive first-deadline flag determines this even when the player is the
sole member of the first block: deleting a date-zero singleton exposes a
strictly later, hence positive, opponent deadline.  If there is no finite
opponent deadline, the only values are (s_i) and zero.

Behavioral responses merely average these pure values, so their supremum is
the displayed finite maximum.  Consequently prescribed payoff, unrestricted
cap, deterministic terminal law, and debt are identical for two profiles of
the same calendar type.  Absolute deadline values and gaps are irrelevant.

For definition-level clarity, the all-Never case should make the third field
of the calendar type an explicit three-way value `none / zero / positive`,
or declare it ignored when the ordered finite partition is empty.

## 4. Exact minimum attainment and deadline-rank use are valid

After all players are purified, finitely many calendar types permit one
constant-type subsequence.  By the preceding lemma, its semantic pairs are
literally one fixed pair, not merely convergent.  Since their debts converge
to (D_*), that fixed pair has debt exactly (D_*), and any retained profile is
an actual canonical pure-time/Never global minimum.

The theorem recorded in
`formalized/PURE_FINITE_CLOCK_MINIMUM_DEADLINE_RANK_TO_PAID_PORT.md` applies
to exactly this object.  It allows arbitrary finite deadlines and Never,
rules out the all-Never endpoint at positive global minimum, and returns an
actual off-minimum pure-clock profile with a complete pure-time/Never best
response and literal first disagreement.  Its finite replacement ancestry
composes with the at-most-four purification ancestry.

## 5. Provenance and exact nonclaim

Every operation is a literal unilateral replacement of the corresponding
incoming actual profile.  In the strict branch, targets and paid rows remain
on one strict refinement.  In the equality branch, choosing one member of
the stabilized subsequence retains a finite literal path back to one member
of the original realizing sequence.  A constant sequence at that attained
pure minimum also carries a positive finite terminal atom, because the
all-Never pure profile cannot be a positive global minimum.

This is enough for the claimed contraction to an actual off-minimum paid
port.  It is not a renewable chronology and does not consume the off-minimum
port.  The note states both limitations correctly.

## 6. Novelty and Lean-facing caution

The existing formalized finite-clock entrance uses finite support to choose
cap-attaining or least-debt support points.  The new argument removes finite
support: it needs only a non-worse positive-support pure point, and sends a
strict limit to the approximate-cap actual-reach theorem.  This is a genuine
extension, not a restatement of the finite-clock packet.

The two cited `fable/lean` inputs are scratch-lane kernel checks, not current
production declarations.  Any export should say this literally and list the
ordinary source theorem needed for the expectation identity.  This is a
certification issue, not a mathematical gap.

Subject to the two presentation repairs above (an explicit strict-branch
floor and a total definition of the empty calendar type), I recommend this
as an export candidate.  It contracts the arbitrary-clock minimum entrance
to the already isolated off-minimum paid-port waist; it does not claim that
the waist is consumed.
