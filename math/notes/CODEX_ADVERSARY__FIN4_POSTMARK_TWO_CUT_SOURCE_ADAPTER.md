# Fin4 post-mark two-cut source adapter: exact orientation audit

Author: `CODEX_ADVERSARY`

Status (updated 2026-08-30): **THE STRONG TWO-RETURN FORM STILL FAILS, BUT A
WEAKER EXHAUSTIVE LITERAL TWO-CUT PRODUCER IS NOW PROVED IN ORDINARY
MATHEMATICS FROM THE INTEGRATED FIN4 SOURCE.**  After compactifying the actual
post-mark tails, a positive finite atom at their minimum joint-law limit gives
`entryCut = 0` and a moving finite `exitCut` with order-one hazard.  The exit
need not return to the minimum.  This is enough for the reviewed two-cut
coercivity dichotomy, but not by itself for the requested renewable-child or
terminal consumer.

## Question

In the minimum-return arm of the current Fin4 source-preserving atlas, can
the post-mark two-cut input required by `NONZERO_PERSIST_ATTEMPT_1`, Followup 3, be
obtained from the checked source data?  More precisely, can one obtain actual
profiles $s_n$, each literally the continuation after the already retained
marked row, and cuts
$\operatorname{entryCut}_n<\operatorname{exitCut}_n$ such that

\[
D(s_n)\longrightarrow D_*,
\qquad
\Pr_{s_n}(\text{reach }\operatorname{entryCut}_n)\ge r>0,
\]

\[
\sum_{t=\operatorname{entryCut}_n}^{\operatorname{exitCut}_n-1}
  \sum_i q_{n,t,i}\ge\chi>0,
\qquad
D(\operatorname{suffix}_{\operatorname{exitCut}_n}s_n)
  \longrightarrow D_*?
\tag{1}
\]

All roots in the displayed block must be literal consecutive live roots of
that same $s_n$.  The marked row to be retained must occur strictly before
the beginning of $s_n$; a same-date sibling or a separately selected later
rank is not a substitute.

The answer to the displayed strong condition (1), which requires the exit
suffix to return to the minimum, remains **no from the current declarations**.
The packet directly supplies only the first convergence and exact post-mark
ancestry.  Two tempting substitutes are ruled out exactly: the stored
cap--Nash word is upstream and has vanishing total hazard, whereas the
forced-pair row is the retained mark itself and its charged sibling is not
asserted whole-profile near-minimal.  Sections 8--12 below record a later
derived construction which does supply a literal charged block, with no exit
return assertion.

This is an API/source theorem, not a claim that no accidental realization of
(1) can occur for a particular packet.  No positive-minimum Fin4
counterexample is asserted.

## 1. What the current minimum-return packet really supplies

Fix `packet : FinFourMinimumReturnPacket parent`.  For rank $n$, put

\[
m_n=(\operatorname{packet.stream.frame} n).\operatorname{stage}
\]

and define the actual behavioral continuation

\[
s_n=
\operatorname{quittingAllContinueProfileSpine}
  (\operatorname{packet.stream.frame} n).\operatorname{targetProfile}
  (m_n+1).
\tag{2}
\]

The declaration
`FinFourStabilizedForcedPairStream.tail_eq_framePostDateTail` identifies the
semantic pair of (2) with `packet.stream.tail n`.  Therefore
`FinFourMinimumReturnPacket.tailDebt_tendsto_minimum` proves

\[
D(s_n)\longrightarrow D_*.
\tag{3}
\]

The same continuation is literal behind the forced-pair and paid siblings:

- `FinFourStabilizedForcedPairStream.forcedPair_postDateSpine_eq_reference`;
- `FinFourStabilizedForcedPairStream.payerTarget_postDateSpine_eq_reference`;
- `FinFourMinimumReturnPacket.forcedPairTail_eq_tail`; and
- `FinFourMinimumReturnPacket.normalizedDecoratedFamily_postDateSpine_eq_reference`.

Thus (2)--(3) are not merely carrier convergence.  They give exactly the
post-mark behavioral profile and the near-minimum start required by (1), and
reattaching a replacement of $s_n$ leaves the preceding forced-pair row
literal.

What is absent is any cut, marked mass, reach floor, hazard floor, or later
near-minimum suffix **inside (2)**.  In particular,
`tailDebt_tendsto_minimum` is a statement at the entrance of (2); it does not
state convergence after any positive moving cut of (2).

## 2. The stored exact root word is on the wrong side and is asymptotically hazard-free

Every frame also stores `rootStack`, with

`FinFourSourcePreservingSingletonFrame.referenceProfile_eq_literalRootStack`
and `FinFourSourcePreservingSingletonFrame.rootStack_nash`.  This word is not
inside (2).

In the selected-row constructor,

\[
m_n=\lvert\operatorname{rootStack}_n\rvert+
       \operatorname{mark}_n
\]

definitionally by
`QuittingNonsingletonMinimumLawTransfer.shiftedStage`.  In the owner-clock
constructor, `FinFourOwnerCompressedSingletonEndpoint.anchor_le_selectedStage`
likewise puts the whole word no later than the marked row.  The post-mark
continuation (2) begins at $m_n+1$.  Hence no root of the stored cap--Nash
word is a post-mark root of $s_n$.

There is also a quantitative no-go, independent of this ordering.  Write

\[
P_n=\prod_{x\in\operatorname{rootStack}_n}
       \prod_{i\in\operatorname{Fin}4}(1-q_i(x))
\]

and

\[
H_n^{\rm stack}=\sum_{x\in\operatorname{rootStack}_n}\sum_i q_i(x).
\]

`QuittingNonsingletonMinimumLawTransfer.tendsto_capNashStackContinueProduct_one`
applies to the exact source words and gives $P_n\to1$.  Equivalently, its
proof uses the checked identity
`quittingTerminalDebtSum_capNashRootStack_eq`: both the unprefixed source debt
and the prefixed reference debt tend to the same positive $D_*$, so exact
cap--Nash scaling forces the survival factor to tend to one.

Eventually $P_n>0$, and the elementary inequality

\[
-\log(1-u)\ge u\qquad(0\le u<1)
\]

gives

\[
0\le H_n^{\rm stack}
\le -\log P_n\longrightarrow0.
\tag{4}
\]

Every consecutive subword has hazard at most $H_n^{\rm stack}$.  Therefore
no subblock of the checked cap--Nash word can satisfy a fixed
$\chi>0$ on a cofinal subsequence.  Moving that word across the mark is not
only unsupported ancestry; it would also fail the required charge.

This is the source-attached version of the positive-minimum exact-block
coercivity obstruction: an exact cap--Nash block cannot have both endpoint
debts tend to the same positive minimum while retaining order-one hazard.

## 3. The charged row is the retained mark, not a downstream block

The declarations

- `FinFourSourcePreservingForcedPairPacket.resolution_le_forcedPairStageMass`,
- `FinFourSourcePreservingForcedPairPacket.payerRoutedStageMass_eq_forcedPairStageMass`,
  and
- `FinFourMinimumReturnPacket.minimumTailSource`

give a fixed positive reached-mass floor at the forced-pair row and preserve
its literal post-date spine.  This is useful charge, but it occurs at
$m_n$, while $s_n$ begins at $m_n+1$.

There are two invalid ways to use it.

1. Starting the block at or before $m_n$ makes the charged row part of the
   replacement domain.  A complete best response from the block entrance is
   then not proved to retain the marked root or its atom.  This loses the
   ancestry conclusion for which Followup 3 moved to a post-mark source.
2. Using the forced-pair or paid sibling as the near-minimum block parent is
   not licensed.  `referenceDebt_tendsto` is about `referenceProfile`, and
   `tailDebt_tendsto_minimum` is about the post-date tail.  No declaration
   says that `forcedAdapter.targetProfile`, `payerAdapter.targetProfile`, or
   `frame.targetProfile` has whole debt tending to $D_*$.

Thus the current fields are distributed across different temporal ports:

\[
\begin{array}{c|c}
\text{port} & \text{checked information}\\ \hline
\text{reference parent} & D\to D_*;\ \text{stored cap word upstream}\\
\text{marked sibling at }m_n & \text{positive reached mass / paid row}\\
\text{post-mark continuation }s_n & D(s_n)\to D_*\ \text{and literal ancestry}
\end{array}
\]

No one row of this table supplies (1).

## 4. `drop` and `trajectory` do not create consecutive play dates

`FinFourMinimumReturnPacket.drop_row` and `drop_frame` say only that rank
$k$ of the dropped **index stream** is rank $k+1$ of the original stream.
`FinFourMinimumReturnTrajectory.packet_succ` iterates this reindexing.

There is no declaration of the form

\[
s_n=w_n\triangleright s_{n+1}
\quad\text{or}\quad
s_{n+1}=\operatorname{suffix}_{L_n}s_n.
\tag{5}
\]

Indeed the underlying `QuittingMinimumLawCausalSuffixAtom.chronology` stores
`profiles : ℕ → BehaviorProfile`, convergences, cap--Nash prefix
words, and one positive row in each selected profile.  It has no nesting
equality between `profiles n` and `profiles (n+1)`.  Strict monotonicity of
`sourceRank` is an ordering of indices, not (5).

Consequently one may not take the marked row of rank $n+1$ as the
`entryCut` row inside the post-mark continuation of rank $n$.  This is the exact field
missing from the current packet.

A local timing regression shows why positive marked mass cannot fill it.  A
behavioral profile may Continue until one date, absorb surely in one
coalition at that date, and be all-Continue afterward.  Its marked mass is
one and its post-mark hazard is zero.  This is only a regression for the
timing implication (not a positive-minimum game), but it proves that marked
mass plus literal post-date equality does not imply downstream renewal.

## 5. Exact same-witness repair interface

The required proposed API is a family of proof-relevant witnesses, one at
each rank, with all of the following fields on the same object:

1. `parentProfile` and `markedDate`, carrying the already certified marked
   row;
2. `postMarkContinuation`, with the literal equality

   \[
   \operatorname{postMarkContinuation}
   =\operatorname{quittingAllContinueProfileSpine}
      (\operatorname{parentProfile})(\operatorname{markedDate}+1);
   \tag{5a}
   \]

3. natural-number fields `entryCut`, `exitCut`, and
   `entryCut_lt_exitCut`;
4. the actual roots at all dates in `[entryCut, exitCut)`, read from
   `postMarkContinuation` rather than copied from another profile;
5. a uniform reach floor from the beginning of that continuation to
   `entryCut`;
6. a uniform total marginal-hazard floor on the literal block;
7. convergence of the debt of `postMarkContinuation` to $D_*$; and
8. convergence of the debt of its literal `exitCut` suffix to $D_*$.

Fields 2, 4, and 8 are the same-witness/ancestry clauses.  They rule out
assembling the start convergence from `stream.tail n`, the charged row from
another sibling, and the exit convergence from a later rank.  The current
packet has fields 1--2 and 7, but not 3--6 or 8.

## 6. Minimal sufficient producer field and proof

The full general two-cut structure is not necessary.  A single renewed
post-mark row suffices.  Add to the minimum-return packet, after a strict
subsequence if needed:

- a date $c_n\in\mathbb N$ in the actual post-mark profile $s_n$;
- a nonempty coalition $A_n$;
- one fixed \(\lambda>0\) such that

  \[
  \lambda\le
  \operatorname{StageMass}(s_n,c_n,A_n);
  \tag{6}
  \]

- and the recurrent endpoint condition

  \[
  D(\operatorname{suffix}_{c_n+1}s_n)\longrightarrow D_*.
  \tag{7}
  \]

These must be fields of (2), not facts about another rank profile.  Call this
the **post-mark renewed-row field**.

Then (1) follows with

\[
\operatorname{entryCut}_n=c_n,\qquad
\operatorname{exitCut}_n=c_n+1,\qquad
r=\lambda,\qquad\chi=\lambda.
\]

Indeed, if $R_n$ is the reach of $c_n$, (6) gives
$R_n\ge\lambda$.  If $a_n$ is the conditional absorption probability at
that row, then

\[
\lambda\le R_n\Pr(A_n\mid c_n)\le a_n
\]

because $R_n\le1$, and the total marginal hazard of the row is at least
$a_n$.  Thus both uniform floors hold.  Equations (3) and (7) give the two
debt limits.  The roots are literal by construction, and the original
retained mark precedes the entrance of $s_n$, so every modification of
$s_n$ retains that marked row exactly.

An equivalent, more general repair is a proof-relevant factorization

\[
\widehat s_n=
A_n\triangleright x_n^{\rm mark}\triangleright
\bigl(w_n\triangleright u_n\bigr),
\]

where $s_n=w_n\triangleright u_n$, the two cuts are indices in the literal
word $w_n$, and the four estimates in (1) are stored.  A semantic equality,
shared rank label, or convergence of independently selected profiles is not
enough.

## 7. Verdict for the original strong adapter (superseded in part by Section 8)

**FAIL for the version requiring the exit suffix to return to (D_*).**  The
near-minimum post-mark start is already checked and literal.  What remains
new in that stronger version is downstream *return*: a charged block whose
literal exit suffix again approaches (D_*).

The one-row producer (6)--(7) remains a sufficient repair for that strong
form.  Neither the vanishing-hazard upstream cap word, the same-date
forced-pair sibling, nor rank-stream `drop` realizes it.  Section 8 shows,
however, that a multirow block with no prior exit-return promise follows from
the complete integrated source by a different argument.

## Source declarations inspected

- `QuittingMinimumLawCausalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
- `FinFourMinimumAtomProducer` in
  `Research/Quitting/FinFourProducerAtlas/Source.lean`;
- `QuittingNonsingletonMinimumLawTransfer.shiftedStage`, `SelectedRows`, and
  `tendsto_capNashStackContinueProduct_one` in
  `Research/Quitting/NonsingletonMinimumLawLinearTransfer.lean`;
- `FinFourMinimumAtomChronology` and
  `FinFourOwnerCompressedSingletonEndpoint.anchor_le_selectedStage` in
  `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`;
- `FinFourSourcePreservingSingletonFrame` and
  `FinFourSourcePreservingCofinalSingletonPacket` in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingSingletonFrames.lean`;
- the marked-mass and post-date-spine declarations in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingForcedPair.lean`;
- `FinFourMinimumReturnPacket`, `tailDebt_tendsto_minimum`, `drop`, and
  `trajectory` in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionAtlas.lean`;
- `forcedPairTail_eq_tail`, `minimumTailSource`, and
  `normalizedDecoratedFamily_postDateSpine_eq_reference` in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionConsumers.lean`;
- `quittingTerminalDebtSum_capNashRootStack_eq` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`;
- `questions/FIN4_MINIMUM_RETURN_CAPSTONE.md`; and
- the minimum-return and source-faithful causalization entries in
  `docs/TOOLKIT.md` and the corresponding current boundary in
  `docs/FRONTIER.md`.

No AGKRS source or literature claim was used.  No Lean file or export was
modified.

## 8. Update: a finite-window producer with `entryCut = 0`

The preceding audit asked for too much at the producer stage.  The exit
suffix need not already be near-minimal: the reviewed two-cut theorem was
designed precisely to return the alternative that it is uniformly
off-minimum.  Once that return requirement is removed, the integrated Fin4
source does produce the block on one literal chronology.

Continue to write (s_n) for the actual post-mark profiles in (2).  Pass to
one strict subsequence on which their complete joint semantic/law points
converge:

\[
 \bigl(Z(s_n),\mathcal L(s_n)\bigr)\longrightarrow P=(z_*,\nu).
 \tag{8.1}
\]

This is compactness of `quittingTerminalSemanticLawCarrier`; no new realizing
profiles are selected.  Continuity of total debt and (3) give

\[
 D(z_*)=D_*.
 \tag{8.2}
\]

Apply
`exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` to the same
hard residual and this exact point (P).  It gives one nonempty terminal
coalition (A) and

\[
 \mu:=\nu(\mathrm{some}\ A)>0.
 \tag{8.3}
\]

Now apply `nonempty_sourceFaithfulMinimumCausalChronology` to the same
reindexed family (s_n), the same point (P), and (A).  Its finite-window
field gives, eventually, literal natural numbers (e_n) such that

\[
 \frac\mu2<
 \sum_{t<e_n}\operatorname{StageMass}(s_n,t,A).
 \tag{8.4}
\]

After deleting the finite exceptional prefix, set

\[
 \operatorname{entryCut}_n=0,
 \qquad
 \operatorname{exitCut}_n=e_n,
 \qquad
 \chi=\frac\mu2,
 \qquad r_0=1.
 \tag{8.5}
\]

Equation (8.4) implies (e_n>0), so these really are two distinct cuts.  If
(x_{n,t}) is the actual live root of (s_n) at date (t), then for every
(t)

\[
 \operatorname{StageMass}(s_n,t,A)
 \le \Pr_{x_{n,t}}(\text{absorption})
 \le \sum_{i\in\operatorname{Fin}4}q_{n,t,i}.
 \tag{8.6}
\]

The first inequality follows by factoring stage mass as live mass times the
root (A)-mass, then discarding the live factor and using
`quittingRootCoalitionMass_le_absorptionMass_of_nonempty`.  The second is the
finite union bound, exposed as
`quittingRootAbsorptionMass_le_sum_quitRates` (equivalently the
`sum_quitProbability` wrapper).  Summing (8.6) and using (8.4) gives

\[
 H_n:=\sum_{t<e_n}\sum_iq_{n,t,i}>\chi.
 \tag{8.7}
\]

The block begins at the start of (s_n), so its reach is exactly one.  Its
start pair is (Z(s_n)), and its end pair is literally

\[
 Z\bigl(\operatorname{suffix}_{e_n}s_n\bigr).
 \tag{8.8}
\]

Thus (8.5)--(8.8) are a genuine same-profile, same-history two-cut packet.
The construction never treats a later packet rank as a date of an earlier
profile and never imports a floor from another sibling.

## 9. Exact coercivity output and constants

Put

\[
 K=(1-e^{-\chi})D_*,
 \qquad
 \delta=\frac{e^\chi-1}{2}D_*.
 \tag{9.1}
\]

Apply
[`POSITIVE_MINIMUM_TWO_CUT_COERCIVITY_AND_PAID_SPLICE.md`](../formalized/POSITIVE_MINIMUM_TWO_CUT_COERCIVITY_AND_PAID_SPLICE.md)
to the literal block (8.5).  At every retained rank, exactly one of the
following conclusions may be selected:

1. the literal exit suffix (u_n=\operatorname{suffix}_{e_n}s_n) satisfies

   \[
   D(u_n)\ge D_*+\delta;
   \tag{9.2}
   \]

2. some player (p_n\) has entry debt

   \[
   d_{p_n}(s_n)>K/8,
   \tag{9.3}
   \]

   and, for every (eta>0), has an actual complete behavioral replacement
   from the start of (s_n) with payoff gain (>K/8-eta) and target
   (p_n)-debt at most (eta).

There are only four players.  Hence, after another strict subsequence, either
(9.2) holds throughout, or the paid arm holds throughout with one fixed
player (p).  In the paid arm choose (eta_n\downarrow0).  The resulting
literal target profiles (t_n) satisfy

\[
 d_p(t_n)\longrightarrow0,
 \qquad
 U_p(t_n)-U_p(s_n)\ge K/8-o(1).
 \tag{9.4}
\]

This is stronger than the fixed-tolerance conclusion needed merely to show a
positive gain.  It uses unrestricted behavioral caps; no stationary or
finite-controller completeness is assumed.

## 10. What is and is not source-preserving

The chronology through (8.8) is fully source-faithful in the following exact
sense.  Each (s_n) is the literal continuation of the original packet
profile after its marked date, and every root in the two-cut block is read
from that same (s_n).  Reindexing for compactness does not change this
ancestry.

There is nevertheless an important outer-reach boundary.  The reach floor
(r_0=1) is measured from the post-mark port (s_n).  The preceding forced
row contains a sure quitter, so its joint-Continue branch can have probability
zero.  Therefore neither the paid gain in (9.4) nor any target payoff change
is bounded below after reattaching the target behind that earlier row.  A
cross-tail closure does preserve the earlier root and atom literally, but it
does not create positive probability of reaching its replacement tail.

This distinction is harmless for the two-cut theorem, whose parent here is
(s_n), but fatal to any claim that (9.4) is already a profitable deviation
of the original forced-pair profile.  A uniform floor stated on another
sibling or at another packet rank cannot repair it.

## 11. Downstream audit

The two exhaustive outputs are real, but neither is already a terminal
consumer.

### 11.1 Off-minimum exit suffix

The profiles (u_n) in (9.2) are literal suffixes of the actual (s_n), so
their provenance is stronger than abstract carrier membership.  They do not,
however, instantiate the checked `FinFourUniformEscapePacket`: that dependent
type requires the tails of one stabilized forced-pair frame stream, with its
stored entrance, labels, rows, and packet equalities.  The moving suffixes
(u_n) have none of those fields.  The generic same-tail maximal-cap-root
dispatch can be applied to each (u_n), but its return/undercharge residual is
not a uniform-equilibrium consumer.

### 11.2 Paid targets

Compactify the actual target pairs and laws of (t_n).  Their total debts are
bounded below by (D_*), so after a strict subsequence either they stay above
(D_*+	heta) for some (	heta>0), or their debts tend to (D_*).  The first
case is another actual off-minimum endpoint with no terminal consumer.

In the second case, let (T) be the exact minimum joint-law limit.  The same
hard residual and
`exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` select a
positive finite atom at (T).  Applying
`nonempty_sourceFaithfulMinimumCausalChronology` to the same literal target
family (t_n) reconstructs a complete `FinFourMinimumAtomProducer` at (T)
with unchanged residual and without changing that family.  This part is a
genuine source transition in ordinary mathematics.

It is not automatically a strict support descent from the incoming minimum
point (P): (9.4) deletes (p), but other debt coordinates may become
positive.  The standard half-stopping-law construction gives a minimum point
(H) whose support is

\[
 \operatorname{supp}_+(H)
 =\operatorname{supp}_+(P)\cup\operatorname{supp}_+(T),
 \tag{11.1}
\]

and hence

\[
 \operatorname{supp}_+(T)\subsetneq\operatorname{supp}_+(H)
 \tag{11.2}
\]

because (pin\operatorname{supp}_+(P)) and
(p\notin\operatorname{supp}_+(T)).  This is the asymptotic-zero version of
`exists_minimumEndpointSupportRankHandoff_or_debtAscent`, already proved in
ordinary mathematics in
[`CODEX_ADVERSARY__FIN4_POSTMARK_DIRECT_DEBT_HANDOFF.md`](CODEX_ADVERSARY__FIN4_POSTMARK_DIRECT_DEBT_HANDOFF.md).
The current checked theorem assumes exact zero target debt at every rank, so
the approximate-cap version is not yet a named Lean adapter.  Moreover the
strict comparison parent is the newly produced half-mixture point (H), not
the incoming point (P).  Thus it gives a one-use entry into the renewable
rank language, not a recursive edge from the original packet.

## 12. Final verdict and minimal remaining hypotheses

There is no longer a source gap for the **weak exhaustive block**:

\[
 D(s_n)\to D_*,\quad
 \operatorname{entryCut}_n=0,\quad
 \operatorname{reach}=1,\quad
 H_n\ge\mu/2,
 \tag{12.1}
\]

with a literal exit suffix in the same (s_n).  The smallest genuinely new
formal lemma is the adapter composing joint compactification,
`exists_positive_finiteLawAtom_of_finFourHardResidual_minimum`, and the
finite-window field of
`nonempty_sourceFaithfulMinimumCausalChronology` into (12.1).  Its proof is
only (8.6) and finite reindexing.

The stronger two-return condition (D(u_n)\to D_*) is still not forced.  A
minimal extra hypothesis for that form is exactly tightness of the charged
windows at the minimum:

\[
 D(\operatorname{suffix}_{e_n}s_n)\longrightarrow D_*.
 \tag{12.2}
\]

Without (12.2), the correct exhaustive conclusion is not failure but the
off-minimum/paid dichotomy of Section 9.  To turn that dichotomy into a checked
recursive source descent requires either:

- a consumer for the literal off-minimum suffix/target families; or
- the approximate-zero support-handoff adapter plus a typed construction of
  both the half-parent and target minimum sources.

To lift any paid gain back through the preceding forced row additionally
requires a positive joint-Continue floor there.  This is impossible to infer
from the marked atom floor and may be false for the actual sure-quitter row.

## Additional declarations inspected for the update

- `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
- `QuittingSourceFaithfulMinimumCausalChronology` and
  `nonempty_sourceFaithfulMinimumCausalChronology` in
  `Research/Quitting/SourceFaithfulMinimumLawCausalization.lean`;
- `quittingRootCoalitionMass_le_absorptionMass_of_nonempty` in
  `UniformEquilibrium/Quitting/Cycles/CyclicGreenDebt.lean` and
  `quittingRootAbsorptionMass_le_sum_quitRates` in
  `UniformEquilibrium/Quitting/Stationary/ReturnedBlockTangentObstruction.lean`;
- `quittingTerminalSemanticDebt_halfStoppingLawProfile_le` and
  `exists_minimumEndpointSupportRankHandoff_or_debtAscent` in
  `Research/Quitting/StoppingLawMinimumEndpointSupportRankHandoff.lean`;
- `FinFourUniformEscapePacket` and its dependent tail fields in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionAtlas.lean`;
- the generic off-minimum same-tail dispatch in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionConsumers.lean`;
- `quittingSelfTailClosure` and `quittingCrossTailClosure` in
  `UniformEquilibrium/Quitting/Root/SelfTailClosure.lean`; and
- `FinFourSelfTailLowRow` in
  `Research/Quitting/FinFourProducerAtlas/SelfTailContraction.lean`.

The last construction independently duplicates a nonsingleton selected row
behind itself, but its copied row's successor is not proved near-minimal and
it does not cover the singleton source arm.  It is therefore consistent with,
and strictly less general than, the finite-window producer above.
