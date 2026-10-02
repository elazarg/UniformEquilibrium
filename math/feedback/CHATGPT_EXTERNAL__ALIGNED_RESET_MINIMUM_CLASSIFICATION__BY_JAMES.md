# Independent review of aligned reset minimum classification

Reviewer: `JAMES`

Reviewed artifact:
[`notes/CHATGPT_EXTERNAL__ALIGNED_RESET_MINIMUM_CLASSIFICATION.md`](../notes/CHATGPT_EXTERNAL__ALIGNED_RESET_MINIMUM_CLASSIFICATION.md)

Original supplied source: `../ALIGNED_MIN.md`

Repository head inspected: `29a172f`

## Verdict

**REVISE, then PASS as an internal classification.  Do not export.**

The R/I/D/X partition, the joint-law lift, the reset-barrier coercivity, the
minimum-fiber re-extraction, and the aggregate identity are mathematically
correct.  The note also correctly omits the supplied source's unsupported
claim that Fin4 support rank can increase only once.

Three qualifications are mandatory before the note should be marked reviewed
PASS:

1. State the complete dependent hypotheses for the bridge construction.  In
   particular, retaining a positive atom is a field of the bridge, while
   calling it an opponent-incidence atom also uses the external hypotheses on
   `packet.terminal`, `other`, and `packet.observer` from
   `nonempty_minimizerBridge`.
2. In arm I, restored tangent positivity gives the predicate
   `HasQuittingStoppingLawFlatSupportEntry`, but that definition does **not**
   itself contain the column-flatness hypothesis.  If the result is called an
   exhaustive *flat branch*, separately assume or prove
   `forall mover, sum observer, frontier.tangent mover observer = 0`.
3. Qualify arm D as one strict support-cardinality re-extraction, not a complete
   regenerated aligned-rectangle recursion.  Nothing in the theorem supplies
   a new rectangle packet, bridge, chronological edge, or consumer at the new
   base.

These are statement/scope repairs, not failures of the displayed algebra.

## Claim audited

Let `frontier` be a positive-minimum tangent family, let `packet`, `dispatch`,
and `limit` be the dependent rectangle data, and let
`bridge : QuittingStoppingLawRectangleMinimizerBridge limit other`.  Write

\[
b=\texttt{frontier.base},\qquad
g=\texttt{bridge.global.1},\qquad
f=\texttt{bridge.fixed},
\]

\[
A=\{i:d_i(b)>0\},\qquad G=\{i:d_i(g)>0\},\qquad
\delta_o=D(g)-D(b).
\]

Assume the equality half of `bridge.aligned_or_lawPremium`, equivalently
`D(f)=D(g)`.  The proposed conclusion partitions the data into:

- R: `delta_o > 0`;
- I: `delta_o = 0` and `d_o(b)=0`;
- D: `delta_o = 0`, `d_o(b)>0`, and `G subset A`;
- X: `delta_o = 0`, `d_o(b)>0`, and `G` is not a subset of `A`.

The additional conclusions are a uniform observer-debt moat in R, conditional
support-entry provenance in I, strict support re-extraction in D, and a new
positive-debt coordinate in X.

## Declarations and files checked

I checked the current declarations rather than relying on the supplied prose:

- `QuittingPositiveMinimumDebtTangentFamily` and
  `exists_positiveMinimumDebtTangentFamily_of_pair` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`;
- `HasQuittingStoppingLawFlatSupportEntry` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/ExhaustiveTangentAlternative.lean`;
- `QuittingStoppingLawVanishingDebtRectangleSequence` and its producer in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/OffDiagonal/AtomRectangleSequenceAlternative.lean`;
- `QuittingStoppingLawRectangleMinimizerBridge`,
  `nonempty_minimizerBridge`, and `eventually_literal_lawPremium` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/RectangleResetFaceMinimizer.lean`;
- `QuittingFixedLawResetDispatch` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`;
- `quittingTerminalSemanticLawCarrier_isCompact` and
  `mem_terminalSemanticLawCarrier_of_joint_tendsto` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`;
- `exists_reextractedFrontier_of_minimumFiberEndpoint` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/NormalizedCurvaturePaidRow.lean`;
- the maintained boundary in
  `questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`; and
- the precise desired aligned-minimizer output in
  `notes/CHATGPT_EXTERNAL__FIN4_RECTANGLE_CAPSTONE_SPECIFICATION.md`.

No external-paper claim is used.

## 1. Joint-law lift: PASS

For every `n`, the literal point

\[
z_n=(\operatorname{Sem}(\texttt{frontier.source }n),
     \operatorname{Law}(\texttt{frontier.source }n))
\]

is in the joint carrier.  The joint carrier is compact by
`quittingTerminalSemanticLawCarrier_isCompact`.  A convergent subsequence has
some limit `(b,mu_b)`: the first component must be `b` because
`frontier.source_tendsto` already gives convergence of the whole first
sequence.  Closedness of the carrier, or directly
`mem_terminalSemanticLawCarrier_of_joint_tendsto`, puts `(b,mu_b)` in the
joint carrier.

This is the correct reason that no extra law-realization premise is required.
The law is only a subsequential limit; the argument does not claim that `b`
is attained by one behavioral profile.

## 2. Alignment fields and the fixed stall: PASS with one provenance wording repair

The declaration stores

\[
D(g)\le D(f)
\]

and the disjunction

\[
(D(f)=D(g)\ \wedge\ \text{every exact root at }f.2\text{ is allC})
\quad\vee\quad D(g)<D(f).
\]

Thus the assumed equality excludes the strict-premium branch and gives the
unique-root statement exactly as claimed.  Since
`fixed_dispatch.joint` and `fixed_dispatch.reset` place
`(f,dispatch.cluster.2)` on the reset face, equality with the global reset
minimum makes `f` another objective minimizer of that face.  This does not
identify `f` with `g`.

The positive-absorption half of `fixed_dispatch.dynamic_exit` is impossible:
its exact root would have to be allC, whose absorption is zero.  Therefore the
right-hand dynamic-exit alternative is selected and `f` is an exact allC
self-prefix.

The complete endpoint law and the positive `packet.terminal` atom are retained
at `f`.  To call that atom an opponent-incidence atom, however, the statement
must retain the hypotheses used to build the bridge: the relevant `other`
belongs to `packet.terminal`, differs from the observer, and the selected
orientation has the required reward sign.  Those facts are inputs to
`nonempty_minimizerBridge`; they are not all recoverable from an arbitrary
value of the bridge structure alone.

## 3. R/I/D/X exhaustiveness: PASS

Projection of `bridge.global_mem` gives `g` in the semantic carrier.  Global
minimality of `b` yields `D(b)<=D(g)`, so `delta_o>=0`.

- If the inequality is strict, R holds.
- Otherwise `D(g)=D(b)`.  Split on whether `d_o(b)=0`.
- In the active-observer half, split on `G subset A`.

These tests are mutually exclusive and exhaustive.  In D,
`o in A` and `bridge.global_reset` gives `o notin G`, hence `G` is a strict
subset of `A`.  In X, an element of `G\A` has positive debt at `g`; carrier
nonnegativity and nonmembership in `A` give debt exactly zero at `b`.

I found no missing fifth case.

## 4. Minimum-fiber re-extraction: PASS

In I/D/X, `D(g)=D(b)>0`.  For every semantic-carrier candidate `x`,

\[
D(g)=D(b)\le D(x).
\]

Together with projected carrier membership, these are precisely the
hypotheses of `exists_positiveMinimumDebtTangentFamily_of_pair`.  Its output
contains literal behavioral profiles converging to `g`; no attainment of `g`
is assumed.

The support of every resulting family is intrinsic to its base, so after
rewriting `next.base=g`, it is exactly `G`.  Consequently D gives a strict
natural-valued support-cardinality decrease.

The proposed generic reset-point lemma is not duplicated verbatim by current
main.  The closest checked theorem,
`exists_reextractedFrontier_of_minimumFiberEndpoint`, is specialized to a
`FullReplacementCluster` and uses flatness plus no-entry to prove its support
inclusion.  Here inclusion `G subset A` is an explicit hypothesis, so the
generic proof is the elementary re-extraction argument in the note.

What D does **not** provide is the next rectangle packet or reset bridge.
Calling it a “finite-rank regeneration” is acceptable only in the narrow
sense of regenerating a tangent family at smaller support.  It is not by
itself a closed recursion or a semantic chronology.

## 5. Restored tangent provenance: conditional PASS, with a flatness warning

The producer of the rectangle sequence first chooses `mover, observer` with

\[
0<\texttt{frontier.tangent mover observer},
\]

and defines a positive charge from that entry.  The final structure
`QuittingStoppingLawVanishingDebtRectangleSequence` stores the same labels and
positive charge, but does not store a theorem relating that charge back to the
tangent.  Therefore the current opaque packet does lose the stated
provenance.  Adding the proposed field, or returning an extending wrapper from
the producer, is a legitimate strengthening.

In I, the restored inequality, active membership of `mover`, and
`d_observer(b)=0` prove the bare predicate

`HasQuittingStoppingLawFlatSupportEntry b A frontier.tangent`.

Despite its name, the definition of this predicate only asserts an active
column entering a zero-debt coordinate.  It does not assert

\[
\sum_j \texttt{frontier.tangent mover }j=0.
\]

The rectangle packet can arise before the positive-slope/flat split.  Thus the
note must not claim that I enters the *flat branch* of
`IsQuittingStoppingLawExhaustiveTangentAlternative` unless column flatness is
also carried.  The current wording “the existing datum” is defensible after
this warning; “exactly the existing flat support-entry arm” would be too
strong.

## 6. Aggregate identity and Fin4 constant: PASS

Since `d_o(g)=0`,

\[
\begin{aligned}
D(g)-D(b)
 &=\sum_{j\ne o}(d_j(g)-d_j(b)) +(0-d_o(b)),
\end{aligned}
\]

which rearranges to the displayed identity

\[
\sum_{j\ne o}(d_j(g)-d_j(b))
=d_o(b)+D(g)-D(b).
\]

For `Fin 4`, the complement of `o` has three elements, so an averaging
argument gives one opponent with change at least one third of the right-hand
side.  No sign assumption on the individual changes is needed.  The note is
correct that this does not decide whether the recipient was already active.

## 7. Compact observer-debt coercivity: PASS

In R, the base joint-law lift is an element of

\[
C=K^{law}\cap\{z:D(z.1)\le D(b)+\delta_o/2\},
\]

so `C` is nonempty.  It is compact as a closed sublevel of the compact joint
carrier.  If a point in `C` had observer debt zero, reset-face minimality would
give

\[
D(b)+\delta_o=D(g)\le D(z.1)
\le D(b)+\delta_o/2,
\]

a contradiction.  Observer debt is continuous and nonnegative on the
carrier, hence its minimum on `C` is strictly positive.  This proves the
uniform `epsilon_o` statement.

For formal precision, define `C` as the intersection with the law carrier;
the displayed set-builder alone should not be read as a subset of the entire
ambient Euclidean space.

## 8. Falsification of the stronger supplied-source orbit claim

The supplied `../ALIGNED_MIN.md` goes beyond the conference note and claims
that, under repeated local support transitions, rank can increase only once
from two to three.  This does not follow from the local rule “the selected
active observer is absent from the next support.”

On four labels, the support sequence

\[
\{0,1\}\longrightarrow\{1,2,3\}
\longrightarrow\{0,1\}\longrightarrow\{1,2,3\}
\]

is compatible with the displayed local incidence rules by selecting observer
`0`, then observer `2`, then observer `0`.  It has two separate rank
increases.  No current field connects the independently re-extracted tangent
families or forces monotonicity across these reselections.  Pigeonhole counts
inside a segment of fixed rank are elementary, but they do not create a
chronological or law-compatible support orbit.

The reviewed conference note correctly omits this unsupported iteration
claim.  It must remain omitted.

## 9. Conjecture-facing and export assessment

Arm D is the only arm with a literal complexity decrease: it returns a
positive-minimum tangent family whose support cardinality is strictly smaller.
This matches one conditional output requested by
`CHATGPT_EXTERNAL__FIN4_RECTANGLE_CAPSTONE_SPECIFICATION`, but only after
assuming the precise no-new-support condition that the specification lists as
missing.

The complete classification does not force D:

- R is a compact observer-debt barrier without a paid chronology or return;
- I is, after a structure strengthening, a support-entry datum without its
  missing consumer and without automatic flatness;
- X is an un-well-founded support exchange; and
- D does not regenerate a new rectangle bridge or close the surrounding
  recursion.

Accordingly this is useful internal geometry, not an export-gate result.  It
does not eliminate the aligned-minimizer chamber, supply a producer from all
maintained inputs, reach uniform payoff, or strictly decrease one maintained
rank in every surviving arm.  It also lacks the boundary examples and complete
actual-data-to-consumer packet required by `exports/README.md`.

Recommended disposition: retain in `notes/` after the three scope repairs
above.  If formalized internally, the worthwhile narrow declarations are:

1. the generic same-minimum reset/no-new-support re-extraction lemma;
2. the compact reset-barrier observer-debt moat; and
3. a strengthened rectangle-sequence producer returning the positive tangent
   provenance, explicitly separate from any flatness claim.

