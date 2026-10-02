# Aligned reset minimizers: barrier, entry, descent, or exchange

**Identity:** `CHATGPT_EXTERNAL`

**Source:** `../ALIGNED_MIN.md`, supplied directly by the user on 2026-08-26.

**Status:** `REVIEWED AFTER SCOPE REPAIR`; ordinary mathematics, not
Lean-checked; internal classification, not export-qualified.

Independent review:

-
  [`feedback/CHATGPT_EXTERNAL__ALIGNED_RESET_MINIMUM_CLASSIFICATION__BY_JAMES.md`](../feedback/CHATGPT_EXTERNAL__ALIGNED_RESET_MINIMUM_CLASSIFICATION__BY_JAMES.md)

The review validates the R/I/D/X partition, the joint-law lift, compact
coercivity in R, minimum-fiber re-extraction, and the aggregate identity. It
requires three qualifications used below: opponent-incidence language retains
the full bridge-construction hypotheses; tangent positivity in I gives the
bare support-entry predicate but not column flatness; and D is one strict
support re-extraction, not a regenerated rectangle recursion. In particular,
the stronger claim that local Fin4 support rank can increase only once is
false: the local rules permit support oscillation.

## Question

In the aligned branch of
`QuittingStoppingLawRectangleMinimizerBridge.aligned_or_lawPremium`, what does
equality of the fixed-law and global reset-face objective values actually
imply relative to the original positive global minimum?

Alignment says

\[
 D(f)=D(g),
\]

where `g=bridge.global.1` minimizes total debt on the observer-reset face and
`f=bridge.fixed` retains the selected endpoint law.  It does **not** say
`D(g)=D(b)` for `b=frontier.base`, nor does it identify `f=g`.

Put

\[
 \delta_o=D(g)-D(b)\ge0,
 \qquad
 A=\{i:d_i(b)>0\},
 \qquad
 G=\{i:d_i(g)>0\}.
\]

## Exact classification

Under the aligned hypothesis, every exact cap-Nash root at `f.2` is
all-Continue.  Moreover exactly one of the following occurs.

### R. Positive reset barrier

\[
 \delta_o>0.
\]

Then `d_o(b)>0`, every joint semantic/law point with observer debt zero has
debt at least `D(b)+delta_o`, and `f` attains this reset-face value while
retaining the endpoint law and atom incidence.  Its exact cap correspondence
is the all-Continue stall.

The arm is uniformly coercive.  On the compact joint-law sublevel

\[
 C=\{z:D(z.1)\le D(b)+\delta_o/2\},
\]

observer debt has a strictly positive minimum:

\[
 \exists\varepsilon_o>0,\quad
 z\in C\Longrightarrow d_o(z.1)\ge\varepsilon_o.
 \tag{1}
\]

The base has a joint-law lift because the tangent family stores actual source
profiles converging semantically to `b`; compactness of the finite outcome-law
simplex supplies a joint-law subsequential limit over `b`.

### I. Minimum fiber, observer inactive

\[
 D(g)=D(b),\qquad d_o(b)=0.
\]

A positive minimum tangent family can be re-extracted at `g`, but the reset
does not remove an old active coordinate.  The rectangle construction chose
the observer from a strictly positive tangent entry of an active mover;
however `QuittingStoppingLawVanishingDebtRectangleSequence` currently drops
that field.  Adding

```lean
observer_tangent_pos :
  0 < frontier.tangent mover observer
```

to the packet or an extending wrapper would turn this arm into the existing
bare `HasQuittingStoppingLawFlatSupportEntry` datum. Despite its name, that
predicate does not assert that the tangent column sums to zero. Entering the
flat branch additionally requires a separate flatness hypothesis. The bare
support-entry datum still has no local checked conjecture-closing consumer.

### D. Strict support descent

\[
 D(g)=D(b),\qquad d_o(b)>0,\qquad G\subseteq A.
\]

Since `global_reset` gives `d_o(g)=0`, one has

\[
 G\subsetneq A.
\]

Re-extraction at the supplied carrier minimum `g` gives a new actual positive
minimum tangent family whose positive-debt support is strictly smaller. This
is one genuine support-cardinality decrease. It does not itself produce a new
rectangle packet, bridge, chronological edge, or closed recursion.

The reusable generic lemma is: a carrier point on the same positive global
minimum fiber, resetting one source-active owner and introducing no new
positive-debt coordinate, admits re-extraction with strict support inclusion.

### X. Minimum-fiber support exchange

\[
 D(g)=D(b),\qquad d_o(b)>0,\qquad G\nsubseteq A.
\]

Then some newcomer `j` satisfies

\[
 d_j(b)=0,
 \qquad
 d_j(g)>0.
\]

Re-extraction at `g` is still available, but support cardinality need not
decrease.  This is the exact no-new-debtor obstruction.

## Proof account

1. `bridge.global_mem` projects to semantic-carrier membership of `g`; global
   minimality of `b` gives `D(b)<=D(g)`.
2. Alignment selects the equality branch of `aligned_or_lawPremium`, proving
   unique all-Continue exact cap roots at `f`.  Since `f` is a reset point
   with `D(f)=D(g)` and `g` is reset-face minimal, `f` is also objective-
   minimal on that face.
3. If `D(g)>D(b)` and `d_o(b)=0`, the joint-law lift of `b` would be a cheaper
   reset candidate, contradiction.  Compactness yields (1).
4. If `D(g)=D(b)`, carrier membership, inherited global minimality, and
   positivity permit `exists_positiveMinimumDebtTangentFamily_of_pair` at
   `g`.
5. The support split is the elementary partition into inactive observer,
   active observer with `G subset A`, and active observer with a newcomer.

The aligned fixed-law dispatch's absorbing dynamic branch is impossible:
unique all-Continue exact cap roots are incompatible with its required
positive absorption.

## Aggregate identity

For every bridge, not only the aligned one,

\[
 \boxed{
 \sum_{j\ne o}(d_j(g)-d_j(b))
 =d_o(b)+D(g)-D(b).
 }
 \tag{2}
\]

For literal `Fin 4`, some opponent receives debt change at least one third of
the right-hand side.  This does not distinguish an old active recipient from
a newcomer and therefore does not collapse D/X.

## Conjecture-facing boundary

This is a strict geometric refinement, not the capstone.  The live arms after
the classification are:

- R: consume a uniform near-minimum observer-debt barrier;
- I: consume a flat support entry after restoring its actual provenance;
- X: consume or well-found a minimum-fiber support exchange.

Only D is already a finite-rank regeneration.

## Review request

Check the joint-law lift of `frontier.base`, the exact alignment fields,
re-extraction theorem hypotheses, disjointness/exhaustiveness of R/I/D/X,
the packet-field loss in I, identity (2), and compact coercivity (1).  Also
search for an existing generic re-extraction/support-subset lemma before
adding a duplicate.
