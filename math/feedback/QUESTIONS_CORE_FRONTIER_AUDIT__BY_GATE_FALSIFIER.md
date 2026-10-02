# Audit of the core Fin4 frontier questions

Author: `CODEX_GATE_FALSIFIER`

## Verdict

The uniform-escape and minimum-return capstones are still open and should
remain the two top-level Fin4 questions.  Neither `docs/FRONTIER.md`,
`docs/TOOLKIT.md`, the checked Research declarations, the formalization
records, nor the three completed note-mining audits contain a terminal
consumer for either capstone.

The five files do not, however, describe five independent unresolved
components.

1. `FIN4_UNIFORM_ESCAPE_CAPSTONE.md` is a genuine top-level component.
2. `FIN4_MINIMUM_RETURN_CAPSTONE.md` is the other genuine top-level component,
   but its discussion of support descent incorrectly reads as though that
   conditional branch exhausted minimum return.
3. `FIN4_RENEWABLE_ORIENTATION_OR_COUNTEREXAMPLE.md` is a route-specific
   reduction inside minimum return.  Its equality side overlaps the
   minimum-return capstone and its strict side already has a separate focused
   question.
4. `PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md` is a useful parent fork for the two
   independent paid/reset questions.  It is not a third component of the
   source-preserving uniform-escape/minimum-return atlas.
5. `FIN4_HARD_RESIDUAL_SEMANTIC_CLOSURE.md` combines the paid/reset fork, the
   minimum-law atom route, and permission to use any other hard-residual
   argument.  It is consequently an open-ended restatement of the Fin4 task,
   not an independent atlas node.  In its present form it duplicates both the
   paid-cap parent question and the two top-level capstones.

No one of the five accepts a mere new atom, limit, or local inequality as a
solution.  Their stated acceptable conclusions are genuinely
conjecture-facing.  The required repairs are about exhaustiveness,
self-containment, and removal of duplicated parent questions, not about
tightening a permissive progress criterion.

## Current mathematical dependency map

The checked source-preserving completion theorem gives, from a hypothetical
bounded Fin4 counterexample, exactly

\[
\text{uniform tail escape}\quad\text{or}\quad\text{minimum return}.
\]

The corresponding propositions `FinFourUniformEscapeCapstone` and
`FinFourMinimumReturnCapstone` are still explicitly assumptions of the
conditional Fin4 completion theorem.  This is the right top level.

On uniform escape, every retained actual tail has the checked same-tail
maximal-root dispatch:

\[
\text{half-floor return selection}
\quad\text{or}\quad
\text{universal same-tail undercharge},
\]

with a further all-Continue/blocker alternative in the undercharged arm.
This is a structural dispatch, not a terminal consumer.

On minimum return, normalized-prefix minimization gives an exhaustive
strict-inert/equality split.  The equality arm now has an actual endpoint
decoder with five possible outputs:

\[
\begin{array}{c}
\text{endpoint debt ascent},\
\text{routed singleton},\
\text{prescribed finite atom},\
\text{strict response ascent},\
\text{compiled response rectangle}.
\end{array}
\]

Independently, the canonical maximal-prefix route gives

\[
\text{minimum-endpoint support handoff}
\quad\text{or}\quad
\text{coherent strict normalized endpoint}
\quad\text{or}\quad
\text{strict ray stall}.
\]

Only the first of these three canonical outputs enters the renewable
support-cardinality descent.  Conditional on that handoff, the descent is
complete and well founded and ends at positive total tangent slope, flat
support entry, or an off-minimum paid first disagreement.  Those three exits
remain unconsumed.  It is therefore false to present this descent as an
unconditional reduction of every minimum-return packet.

The normalized-passport result which eliminates positive-absorption root
support entry does not eliminate the different terminal exit called *flat
tangent support entry*.  The latter remains a live input to the two-tier
chronological-shadowing question.

The paid/reset maximal-root fork is also still open:

\[
\text{source regeneration}
\quad\text{or}\quad
\text{repaired-source regeneration}
\quad\text{or}\quad
\text{unique all-Continue at both caps}.
\]

Its first two arms lack a renewable finite rank or return, and its last arm
lacks a consumer.  Near-minimum absorption collapse rules out only the naive
fixed-charge argument along sources whose debt tends to the minimum; it does
not eliminate any of these three arms.

The note-mining reports found candidate bridges into chronological shadowing,
response installation, and paid/reset regeneration, but no completed theorem
which changes this map.

## Per-file dispositions

### `FIN4_UNIFORM_ESCAPE_CAPSTONE.md`

**Disposition: KEEP, with a self-contained rewrite.**

The mathematical premise is current.  The exact source-preserving atlas still
has this terminal structural mode, and the same-tail maximal-root dispatch has
not consumed it.

Required repairs:

1. Define \(U_i,B_i,d_i,D\) in this file.  “Use the same notation as” another
   question makes the statement non-self-contained.
2. Replace the redundant pair “fixed terminal exploitability gap” and
   “positive minimum debt” by one exact relation.  For example, assume
   \(D_*:=\inf_\sigma D(\sigma)>0\), note that this gives
   \(\max_i d_i(\sigma)\ge D_*/4\), and separately assume the minimizing joint
   semantic/law point and its atom.
3. State the paid endpoint quantitatively as a common lower bound \(g>0\),
   not merely as “a fixed positive gain,” and state explicitly that all rows
   are actual profiles from one chronology.
4. Record the already available same-tail maximal-root dispatch.  Re-deriving
   that dispatch is not an answer, just as producing another escape tail is
   not an answer.
5. Replace “Equivalent acceptable conclusions” by “Acceptable ways to prove
   the conclusion.”  Terminal approximate Nash profiles, a charged return,
   and a contradiction are proof routes, not literally the same proposition
   without the separate checked equivalences and consumers.

A suitable replacement outline is:

> Let \(D_*:=\inf_\sigma\sum_i(B_i(\sigma)-U_i(\sigma))>0\).  Suppose one
> minimizing joint semantic/law point has a finite atom of mass \(\mu>0\), and
> one fixed actual realizing chronology has cofinally many marked rows with
> fixed roles, marked mass at least \(\lambda>0\), a pure forced pair, one zero
> marked defect, one endpoint gain at least \(g>0\), exact own-debt
> subtraction, lossless mass routing, and literal post-row tail preservation.
> Assume every displayed post-row tail has debt at least \(D_*+\delta\), where
> \(\delta>0\).  Show that no such data can coexist with \(D_*>0\), by producing
> terminal approximants with one limiting payoff, a positive admissible
> near-return, or another terminal consumer.  Equivalently, construct an
> actual positive-gap table carrying all these data.

Then add one short paragraph saying that every displayed tail already admits
the maximal exact-root return-selection/universal-undercharge dispatch and
that the requested theorem must consume that dispatch rather than restate it.

One minimal Lean reference is enough:
`SourcePreservingCompletionAtlas.lean` and
`SourcePreservingCompletionConsumers.lean`.

### `FIN4_MINIMUM_RETURN_CAPSTONE.md`

**Disposition: KEEP, but replace the “finite support descent available”
section.**

The capstone itself is still open.  Its mathematical entrance is current.
The incorrect implication is the suggestion that the renewable support
descent is available from every minimum-return packet and that its three exits
are therefore the only remaining task.

What is actually checked is conditional:

\[
\text{canonical support handoff}
\Longrightarrow
\text{finite renewable support descent to three exits}.
\]

The source-facing canonical theorem may instead return a coherent strict
normalized endpoint or a strict ray stall.  The separate normalized equality
decoder may return any of the five endpoint outcomes listed above.  These
additional outputs must not disappear from the question.

Required repairs:

1. Keep the eight source-attached minimum-return hypotheses and the terminal
   conclusion.
2. Replace the unconditional support-descent paragraph by a “known
   conditional reductions” paragraph.  It should state both the canonical
   three-way dispatch and the normalized strict-inert/equality decoder.
3. Say explicitly that solving only the support-handoff branch does not solve
   this capstone; on that branch, reconstructing the finite descent is also
   not a solution because it is already available.
4. Define the endpoint gain by one common positive floor and remove “checked,”
   “current,” and “open task” from the mathematical body.
5. Use at most one short source reference.  The relevant umbrella is the
   source-preserving completion atlas; route-specific source filenames belong
   in the focused questions.

A suitable replacement for the stale middle section is:

> Two source-preserving reductions may be used.  First, normalized-prefix
> minimization yields either a strict off-minimum unique-all-Continue point or
> a minimum-return endpoint with an actual finite endpoint decoder.  Second,
> the canonical maximal-prefix construction yields either a minimum-endpoint
> support handoff, a coherent strict normalized endpoint, or a strict ray
> stall.  Conditional on the support handoff, a finite support-cardinality
> descent terminates at positive tangent slope, flat support entry, or an
> off-minimum paid first disagreement.  These are supplied reductions, not
> acceptable final conclusions.

The phrase “source-preserving finite-rank descent whose terminal states all
have terminal consumers” is strong enough and should remain: it cannot be
satisfied by the already checked descent, because its exits are not consumed.

### `FIN4_HARD_RESIDUAL_SEMANTIC_CLOSURE.md`

**Disposition: REMOVE from the core roadmap, or rewrite as a deliberately
open-ended hard-residual problem.**

As written, this is not a separate residual state.  Its paid/reset data and
selector-independent alternative are precisely the parent fork in
`PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`; its two live children are precisely
`FIN4_PAID_RESET_REGENERATION_RANK.md` and
`FIN4_DOUBLE_UNIQUE_CAP_CLOSURE.md`.  Its “independent atom route” is the
starting point of the source-preserving uniform-escape/minimum-return atlas.
Finally, “use an independent construction from the same hard-residual data”
makes the question simply the entire Fin4 theorem in hard-residual normal
form.

There is no false mathematical premise here, and a valid answer would indeed
be a breakthrough.  The problem is classification: keeping it beside the two
exhaustive capstones suggests a third atlas component where none has been
proved.

Preferred action: archive this file and keep the exact paid/reset parent fork
plus the two top-level source-preserving capstones.

If an open-ended direct question is desired, replace the entire middle with:

> Let a four-player reward table satisfy the explicitly stated quantitative
> hard-residual inequalities and suppose \(D_*>0\).  Prove that these
> inequalities are inconsistent, produce terminal approximate Nash profiles
> with one limiting payoff, or construct an explicit table with a certified
> positive exploitability gap against every behavioral profile.

Such a file should not also reproduce the paid/reset fork, charge-collapse
route, and minimum-law atom route.  Those are separate questions with exact
interfaces.  Also delete the unused proper-principal hypothesis unless the
hard-residual inequalities are written out and that hypothesis is part of the
claimed direct attack.

### `FIN4_RENEWABLE_ORIENTATION_OR_COUNTEREXAMPLE.md`

**Disposition: REPLACE as a route summary, or archive in favor of its focused
children.  Do not keep the present statement as an independent SCC.**

The normalized minimizer alternative remains valid, including the strict
toll inequality.  The strict inert point remains unconsumed.  But the file's
minimum-return arm is already part of `FIN4_MINIMUM_RETURN_CAPSTONE.md`, and
its strict arm is already the subject of
`FIN4_STRICT_NORMALIZED_INERT_IMPOSSIBILITY_OR_MODEL.md`.

The equality-arm description is also incomplete relative to the current
actual decoder.  A regenerated minimum source or endpoint ascent is only the
first split.  The checked decoder further exposes routed singleton,
prescribed-atom, response-ascent, and compiled-rectangle outputs.  Some of
those outputs remain unconsumed.  The canonical support descent is a separate
conditional route and should not be presented as the automatic continuation
of every equality outcome.

Preferred action: archive this combined question.  Let the minimum-return
capstone cover the equality side and the strict-inert question cover the
strict side.

If a connector question is intentionally retained, its mathematical data
must state the true exhaustive output:

\[
\text{strict normalized inert}
\quad\text{or}\quad
\begin{cases}
\text{endpoint ascent},\\
\text{routed singleton},\\
\text{prescribed atom},\\
\text{response ascent},\\
\text{compiled response rectangle}.
\end{cases}
\]

The question would then be: consume every one of these alternatives into a
terminal conclusion, one finite-rank transition system with consumed leaves,
or an explicit positive-gap table.  The inert toll should be stated with all
sign hypotheses, including \(s=M-mL\ge0\), so that
\(R\ge\min(aL,cs/m)\) is unambiguous.  This combined connector is valid but
deliberately duplicates its child questions; it should not be counted as an
additional SCC.

### `PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`

**Disposition: KEEP as the parent paid/reset fork, with minor rewriting.**

This file has a useful exact role which the hard-residual umbrella lacks: it
asks for one consumer of a concrete three-way alternative on two actual
profiles.  Its two children can be attacked independently, while a theorem
using interaction between them can answer the parent directly.

The mathematics is current.  Positive-absorption regeneration is literal and
source-attached, paired unique all-Continue is still unconsumed, and the
near-minimum charge-collapse theorem does not settle either arm.

Required repairs:

1. Say that the three-way alternative is selector-independent and that the
   two positive-regeneration alternatives need not be mutually exclusive.
2. Scope the charge-collapse statement explicitly to sequences whose initial
   profile debts tend to \(D_*\).  It is not a no-charge theorem for every
   regenerated orbit.
3. Define the finite returned object directly: an exact punishment-floor
   prefix whose sum of one-stage root absorption masses has a fixed positive
   lower bound and whose endpoint payoff seam tends to zero.  This matches the
   actual near-return consumer and prevents “positive cumulative charge” from
   being interpreted as an unsigned semantic toll.
4. Remove the links from the mathematical statement if strict
   self-containment is desired.  A final sentence may say that the two arms
   are also posed separately, without making those files part of the
   hypotheses.
5. Keep only the maximal-double-regeneration and cumulative-return modules in
   the short reference section.  The charge-collapse source can be included
   there if the no-go paragraph remains.

The file should be described in the roadmap as a **parent fork**, not as an
independent terminal SCC and not as a third source-preserving capstone.

## Recommended maintained set

For a nonduplicative core roadmap, retain:

1. `FIN4_UNIFORM_ESCAPE_CAPSTONE.md` — top-level structural component;
2. `FIN4_MINIMUM_RETURN_CAPSTONE.md` — top-level structural component;
3. `FIN4_TWO_TIER_CHRONOLOGICAL_SHADOWING.md` — shared terminal-exit producer;
4. `FIN4_PAID_RESET_REGENERATION_RANK.md` — paid/reset regenerative child;
5. `FIN4_DOUBLE_UNIQUE_CAP_CLOSURE.md` — paired unique-cap child;
6. `FIN4_STRICT_NORMALIZED_INERT_IMPOSSIBILITY_OR_MODEL.md` — strict inert
   child; and
7. `PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md` — optional parent fork for items 4
   and 5.

Remove `FIN4_HARD_RESIDUAL_SEMANTIC_CLOSURE.md` from the component list, and
remove or demote `FIN4_RENEWABLE_ORIENTATION_OR_COUNTEREXAMPLE.md` to a route
summary.  If either is retained, it must be labelled as an umbrella whose
children are already counted, not as an additional unresolved component.

This organization records exactly what is finite and what is not: the checked
source atlas has two terminal structural modes, while the normalized and
paid/reset constructions are nonexclusive transition systems inside or
parallel to those modes.  No present theorem proves that all of those
transition systems form one finite SCC decomposition.

## Sources inspected

- `docs/FRONTIER.md` and `docs/TOOLKIT.md`;
- `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionAtlas.lean`;
- `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionConsumers.lean`;
- `Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean`;
- `Research/Quitting/FinFourProducerAtlas/MinimumResponseChordActualDecoder.lean`;
- `Research/Quitting/FinFourProducerAtlas/StrictEndpointNormalizedReturn.lean`;
- `Research/Quitting/FinFourProducerAtlas/CanonicalPairMinimumEndpointRenewal.lean`;
- `Research/Quitting/FinFourPaidCapMaximalDoubleRegeneration.lean`;
- `Research/Quitting/FinFourPaidResetDoubleDescentRegeneration.lean`;
- `Research/Quitting/PaidRowCapPortDispatch.lean`;
- the relevant records in `formalized/`, especially the source-preserving
  completion atlas, normalized passport minimizer, renewable canonical
  support descent, strict endpoint normalized return, and minimum-response
  decoder; and
- all three completed note-mining reports.

