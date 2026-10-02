# Scope audit of `GRAMMAR_2.md`

Reviewer: `SCOPE_AUDIT`

## Consolidation re-audit — final verdict

**Pass as the canonical replacement, with minor editorial qualifications.**

I re-audited the consolidated `meta/GRAMMAR.md`, the extracted
`meta/VANISHING_REACH_SUFFIX_NO_GO.md`, and
`questions/QUITTING_COMPOSITIONALLY_SUFFICIENT_STATE.md`.  The substantive
objections in the first review have been resolved:

* the grammar now has a title, an ordinary-mathematics status block, finite
  player and reward context, and an explicit sufficient-schema/nonproducer
  boundary;
* `ClosedSelect` now distinguishes actual standalone output from a certified
  legal named edge;
* finite cases and `TraceRank` now require complete closed tagged branch
  relations with compact witnesses and trace-safe visible children;
* the rank-one counterexample now uses an explicit legal complete-replacement
  child construction;
* the triangular decoder records the missing fixed-column outer convergence;
* the terminal consumer, dispatch-selected exit, maximal-root discrepancy,
  and final sufficient-architecture summary have the corrected scopes; and
* the valid vanishing-reach suffix obstruction has been preserved in a
  separate author-owned note with all essential qualifications.

No valid mathematical content from the two predecessor notes appears to have
been lost.  The selected-root, comparison-transport optimization,
tight-minimization, decoder, pointwise rank, common-execution diagonal,
terminal consumer, and maximal-root no-go material all remain in
`GRAMMAR.md`.  The former grammar's distinctive `CSR_1` calculation,
protected-source unit separation, law-intrinsic rank self-loop, reach-weighted
nonclaim, and off-path-provenance qualification remain in
`VANISHING_REACH_SUFFIX_NO_GO.md`.

The organization is now coherent: `GRAMMAR.md` is the positive sufficient
schema with its two rank uses and one representative optimization boundary;
the vanishing-reach result is a focused law-level boundary note; and the
question states the still-open construction-facing instantiation task.  The
removed `EXECUTABLE_ADAPTERS.md` and detailed maximal-root note no longer
create competing live theorem statements, while their valid content is
retained in the canonical grammar.

Most importantly, neither new note overclaims an answer to the full question.
`GRAMMAR.md` explicitly does not produce its certificates from an arbitrary
table and ends by isolating the construction-specific obligations.  The
vanishing-reach note explicitly permits reach-weighted consumers, external
phase ranks, and richer behavioral provenance.  It is therefore a valid
narrow no-go, but it does **not** by itself satisfy the question's stronger
“acceptable negative answer” clause, which would also have to exclude every
claimed renewable ranked enlargement.  The grammar does not say otherwise.

Four small cleanup points remain; none changes the verdict.

1. Define the reward bound `R` over the specified Never payoff as well as all
   nonempty terminal coalitions, or explicitly extend `r` to the empty
   coalition before taking the maximum.
2. In the decoder assumptions, state `c_n >= 0` explicitly before using its
   series tails as error bounds.  Nonnegativity follows automatically on a
   nonempty executed domain from equation (27), but should be part of the
   certificate data.
3. In the operation table, rename “fixed-law minimizer” to “tight moving-law
   minimizer with comparison transport” so that it matches Section 3.3 and
   the final summary.
4. Cite
   `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact`
   (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
   in the project's standard declaration-and-file format in Section 9.1.

Subject to those editorial corrections, `meta/GRAMMAR.md` can replace the
former `GRAMMAR.md`/`EXECUTABLE_ADAPTERS.md` pair without a mathematical or
scope regression.

## Initial audit before consolidation (superseded)

`GRAMMAR_2.md` is a substantial correction of both the earlier grammar and
`EXECUTABLE_ADAPTERS.md`.  Its central distinction is right: a natural-valued
rank proves pointwise termination, whereas an edge visible in a compact
diagonal needs a separate closed-limit or executable-decoder certificate.  The
common execution sequence, explicit minimization-error limit, closed ancestry
relation, and narrowly stated maximal-root obstruction repair the main defects
identified by the earlier reviews.

Sections 9 and 10 are mathematically sound at their intended conditional and
relation-level scopes.  Section 11 is not yet a correct summary as written:
“maximal correct generic architecture” is an unsupported necessity claim,
“root debt” is not the hypothesis used in Section 9, and the renewable-exit
summary drops the selected-successor qualification needed by Corollary 5.

I would accept this as the canonical **sufficient proof-relevant adapter
schema** after the repairs below.  I would not yet treat it as a complete
replacement for both predecessor notes, for two reasons.

1. The valid vanishing-reach `CSR_1` obstruction from the former
   `GRAMMAR.md` has disappeared rather than being preserved in a corrected
   standalone statement.
2. The file has no title, status block, fixed finite-player/reward context, or
   explicit dependency on `EXECUTABLE_COMPACT_STATE.md`.  In particular, the
   reward bound `R` used in the downstream estimate is not defined.

These are ordinary-mathematics conclusions.  I did not check `GRAMMAR_2.md`
in Lean, and the note should not be presented as a Lean-checked grammar or as
a producer from arbitrary quitting-game data.

## Claim being checked

The intended consolidation has four parts:

1. a finite-constructor trace schema whose certified edges commute with a
   total-variation diagonal;
2. a separate pointwise ranked producer, promotable to trace status only under
   stronger bounded and closed branch data;
3. terminal-Nash and post-limit rank consumers; and
4. a precisely scoped obstruction to the bare exact same-source
   absorption-maximal cap-root trace.

I checked Sections 9--11 directly and compared the full note with the current
`EXECUTABLE_ADAPTERS.md`, `EXECUTABLE_COMPACT_STATE.md`, the standalone
maximal-root no-go, and the surviving reviews of the former grammar.
`meta/GRAMMAR.md` itself was absent during this audit, so preservation of its
content was checked against its three independent feedback files.

## 1. Section 9.1 is a valid conditional consumer

Assume the initial stopping-law packets converge in total variation,

$$
s_m\longrightarrow s_\infty,
$$

their prescribed payoffs converge to one vector `v`, and

$$
B_i(s_m)-U_i(s_m)\leq\eta_m,
\qquad \eta_m\downarrow0.
$$

Continuity gives

$$
U(s_\infty)=v,
\qquad
B_i(s_\infty)-U_i(s_\infty)\leq0.
$$

The opposite inequality holds because player `i`'s prescribed behavioral
strategy is itself among the complete unilateral replacements defining the
cap.  Thus equality holds in every coordinate, and a behavioral realization
of `s_infinity` is an exact terminal Nash profile against unrestricted
behavioral deviations.  This proof is correct.

The consumer can be made sharper and better connected to the project:

* `s_infinity` is first a packet of stopping laws, not literally a behavior
  profile.  Invoke the canonical stopping-law-to-behavior realization before
  calling it the single controller.
* The exact terminal Nash profile gives the uniform-equilibrium payoff `v` by
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
  Alternatively, the supplied sequence is consumed directly by
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in the same
  file.  Section 9 should state this conjecture-facing conclusion and
  immediately repeat that no arbitrary-table producer is supplied.
* The argument depends only on total-variation convergence of the root
  packets.  It is not a new consumer specific to each trace constructor; the
  grammar's role is to produce the common convergent root and legal traces.
  A short corollary after Theorem 7 is enough.

The phrase “vanishing root debt” in item 7 of Section 11 should be replaced by
“vanishing unrestricted terminal exploitability (terminal debt).”  Equations
(58)--(59) make no root-local assumption.

## 2. Section 9.2 is correct with a selected-successor qualification

Once one actual limiting node has been reconstructed, Theorem 4 may indeed be
run pointwise.  No continuity of the child selector is then needed.  The
dispatch-selected chain is actual, legal, finite, and has at most the initial
natural rank many nonterminal transitions.

Corollary 5 proves the following exact statement:

> No nonempty set of nonterminal nodes is closed under the child selected by
> the recorded dispatch.

It does not say that every graph-theoretic component for every available legal
transition has an exit.  A node may have other legal successors unrelated to
the ranked dispatch.  Consequently item 8 of Section 11 should retain
“dispatch-selected” or define “component” using only the selected-successor
relation.

## 3. Section 10 has the right no-go scope

The two-player cap and exact-root calculations agree with the independent
audit of `MAXIMAL_ROOT_ADAPTER_NO_GO.md`:

$$
B(\mu^z)=(z,0),
$$

$$
F(\mu^z)=\{(0,0)\}\quad(z>0),
\qquad
F(\mu^0)=[0,1]\times\{0\},
$$

and maximizing one-stage absorption selects `(0,0)` for positive `z` but
`(1,0)` at `z=0`.  The same-source trace relation is not closed.  Replacing
the limiting root by the unique legal maximizer changes player 2's prescribed
payoff and unrestricted cap from zero to one.

The new approximate-maximality strengthening is also correct.  At the limit
source, an exact root `(x_1,0)` that is epsilon-maximal for absorption has

$$
x_1\geq1-\varepsilon,
$$

and both displayed player-2 semantic coordinates are at least
`1 - epsilon`.  Therefore along `epsilon_m -> 0` the discrepancy from the
all-Never limiting trace tends to one and cannot vanish.

Two wording repairs would prevent later misuse.

1. For positive `epsilon`, the discrepancy is at least `1 - epsilon`; it is
   not literally a unit distance at every index.  Say that it **tends to
   one**.
2. “Strategic error” here means a discrepancy in prescribed-payoff and
   unrestricted-cap coordinates.  It is not exploitability of the repaired
   profile: both displayed coordinates change together.  Calling it a fixed
   “semantic trace discrepancy” is safer.

The final bullets correctly preserve the decisive scope distinction.  In
particular, this example does not obstruct vanishing approximate **root-Nash
equations**.  It only strengthens the no-go from exact maximization to
vanishing approximate maximization **within the exact-root correspondence**.
It also says nothing about a restricted Fin4 source class unless that class is
shown to contain this bifurcation.

## 4. The `TraceRank` surface needs one explicit closure repair

Theorem 6 has the right proof idea, but the displayed `TraceRank(K)` data do
not quite state the hypothesis used by its proof.  Item 3 requires terminal
branch predicates to be closed.  No corresponding item explicitly requires
each **successor branch satisfaction relation** to be closed.  Nevertheless
the proof says that closedness preserves the chosen successor branch at the
limit.

Require, for every recorded terminal or successor tag, that the complete
branch relation be closed.  On a successor branch this relation should include
the parent node, fixed child-rank tag, all witnesses, the certified
`TraceEdge`, and the resulting child equality.  The child should explicitly
carry the recursively smaller `TraceRank` certificate.  If terminal results
or backward maps are visible trace ports, their complete input-output
relations must also be trace-safe, as the current item 6 intends.

With that clarification, finite union over branch tags and induction on the
fixed rank bound justify Theorem 6.  Without it, an open successor test can
reproduce exactly the rank-one discontinuity of Section 6 while satisfying
the literal terminal-only closedness condition.

This repair matters to Sections 8 and 11 because Theorem 7 cites Theorem 6 as
the reason every visible ranked trace survives the common diagonal.

## 5. “Maximal architecture” is not proved

The two-sorted architecture is a useful sufficient interface.  Nothing in the
note proves that it is maximal among generic executable architectures.  The
maximal-root example excludes one bare relation; it does not exclude other
closed relations, quotient traces, direct semantic compilers, measurable
selection plus an independent continuity theorem, or other proof-relevant
constructors.

Accordingly, change

> The maximal correct generic architecture is therefore ...

to

> A corrected sufficient generic architecture is ...

and rename Theorem 7 from “maximal coherent executable diagonal” to
“coherent executable diagonal for the certified grammar.”  “Maximal” is
especially confusing beside Section 10, where it refers to maximizing an
absorption objective rather than maximality of a grammar.

Three other summary edits are needed.

* Item 1 should say “tight moving-law minimizers with closed graph,
  comparison transport, and a convergent recorded error,” not “tight
  fixed-law minimizers.”  Section 3.3 intentionally proves the moving-fibre
  version, and exact minimization additionally needs limiting error zero.
* Item 6 produces a compatible family of executions of all finite diagrams.
  Calling this an “actual projective execution” is fine only after that term
  is defined to mean the compatible family in equation (56), rather than one
  separately defined infinite executable object.
* Item 9 should say “fixed payoff-and-cap trace discrepancy,” not “fixed
  strategic obstruction,” for the reason above.

## 6. Ambient data and status are missing

As a canonical replacement, the note needs to be self-contained about its
ambient contract.  Add at the top:

* a title and status block;
* a fixed finite, nonempty player set `I`;
* a fixed bounded quitting reward table, the Never payoff convention, and
  the definition of the reward bound `R` used in equations (39) and later
  semantic estimates;
* a precise reference to the elementary tight-fusion theorem imported from
  `EXECUTABLE_COMPACT_STATE.md`;
* the distinction between a stopping-law packet and a chosen behavioral
  realization; and
* the explicit nonclaim that this is a conditional verifier/schema, not a
  producer for arbitrary Fin4 or arbitrary finite quitting tables and not a
  Lean-checked theorem.

The description “finite proof-relevant grammar” also needs one sentence of
qualification.  The constructor signature and every diagram are finite, but
`ClosedSelect` and `Decode` are parameterized by arbitrary compact spaces,
closed relations, moduli, programs, ancestry proofs, and semantic consumers.
Thus this is a finite-constructor proof-relevant schema, not a finite code
type or a strategy-class completeness theorem.

## 7. Preservation, novelty, and duplication

The consolidation record is:

| Material | Status in `GRAMMAR_2.md` | Recommended treatment |
|---|---|---|
| Selected roots, robust optimization, tight minimization, decoding | Largely repeats the corrected `EXECUTABLE_ADAPTERS.md` | Retain here if that file is retired; do not maintain both as live canonical statements |
| Pointwise rank with terminal consumer and backward map | Corrected and clearer | Retain |
| Common-execution diagonal excluding bare rank | Repeats and strengthens the current adapter theorem | Retain once `TraceRank` branch closure is explicit |
| Trace/control two-sort distinction, finite cases, bounded `TraceRank` | Genuinely useful new organization | Retain |
| Rank-one discontinuity example | New explicit witness for the old rank gap | Retain, possibly as a compact proposition |
| Vanishing-error maximality inside exact roots | New strengthening of the maximal-root no-go | Retain |
| Full maximal-root calculation | Duplicates `MAXIMAL_ROOT_ADAPTER_NO_GO.md` | Choose one canonical proof and cross-reference it from the other file |
| Terminal convergence consumer | Repeats both predecessor notes | Reduce to a short corollary and cite the checked terminal-to-uniform theorem |
| Vanishing-reach `CSR_1` no-go from the old grammar | Missing | Restore in corrected narrow form or place it in a standalone author-owned note |

The last row is a substantive loss.  The earlier reviews agreed on the valid
core:

> On the total-variation space of stopping laws, the positive-reach
> depth-one suffix map has no single-valued continuous extension at
> `delta_0`; its graph closure has the full fibre
> `{delta_0} x Delta(K)`.  That closure is not an exact legal positive-reach
> suffix edge.  Under exact protected-source law operations it cannot
> reconstruct the `delta_infinity` branch with vanishing law error, and no
> law-intrinsic natural rank decreases along every closure edge.

The necessary nonclaims are equally important: this does not obstruct
reach-weighted consumers, separately stored off-path behavioral
continuations, restricted boundary selections, or ranks enlarged by an
external finite-use counter.  Since the former `GRAMMAR.md` is already absent,
leaving this result only in review files would discard its strongest original
contribution.  It should be restored before declaring the replacement
complete.

## 8. Recommended canonical organization

A lower-duplication order would be:

1. title, status, ambient finite quitting data, and dependency on the audited
   elementary core;
2. the two sorts and the typed finite-constructor trace schema;
3. closed selection, optimization, minimization, decoding, and finite-case
   instances;
4. pointwise rank, the rank-one continuity counterexample, and bounded
   trace-rank promotion;
5. the common-execution diagonal theorem;
6. short terminal-to-uniform and post-limit rank corollaries;
7. two explicitly relation-level boundary examples: maximal-root
   bifurcation and vanishing-reach suffix closure; and
8. a final “sufficient architecture and open producer obligations” section.

If the detailed maximal-root proof remains in
`MAXIMAL_ROOT_ADAPTER_NO_GO.md`, Section 10 should state only the theorem, the
new epsilon-maximal exact-root corollary, and the nonclaims.  Conversely, if
Section 10 becomes canonical, retire the standalone duplicate.  The same
single-source rule should be used when retiring `EXECUTABLE_ADAPTERS.md`.

## Sources and declarations inspected

* `meta/GRAMMAR_2.md`;
* `meta/EXECUTABLE_ADAPTERS.md`;
* `meta/EXECUTABLE_COMPACT_STATE.md`;
* `meta/MAXIMAL_ROOT_ADAPTER_NO_GO.md`;
* `meta/SUFFIX_INFORMATION_OBSTRUCTION.md`;
* `feedback/GRAMMAR__BY_SCOPE_AUDIT.md`;
* `feedback/GRAMMAR__BY_DIAGONAL_AUDIT.md`;
* `feedback/GRAMMAR__BY_CONDITIONING_AUDIT.md`;
* the three reviews of `EXECUTABLE_ADAPTERS.md`;
* `docs/FRONTIER.md` and `docs/TOOLKIT.md` for the current producer/consumer
  boundary;
* `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact`,
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`, and
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`);
* `quittingContinuationBestResponseValue`
  (`UniformEquilibrium/Quitting/Root/FirstBranch.lean`); and
* `quittingContinuationBestResponseValue_compactStoppingLawProfile_tendsto`
  (`UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`).

No literature claim was used.

## Consolidation check completed

The requested recheck has now been performed.  The ambient/status block,
complete `TraceRank` successor-branch closure, and separate narrowly scoped
vanishing-reach result are present.  The final boundary separates schema
theorems, the checked external terminal consumer, and construction-specific
producer obligations.  The final verdict is the pass recorded at the top of
this file.
