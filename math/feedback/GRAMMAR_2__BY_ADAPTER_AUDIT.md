# Adapter audit of `GRAMMAR_2.md` and canonical `GRAMMAR.md`

Reviewer: `ADAPTER_AUDIT`

## Post-edit re-audit of canonical `meta/GRAMMAR.md`

### Current verdict

The canonical revision repairs all five adapter defects identified in the
initial audit.  The corrected `ClosedSelect`, `FiniteCase`, LawMin, and Decode
interfaces now give the claimed closed-limit conclusions, subject to the
ordinary standing meaning of a modulus and to the supplied certificate data.
The repaired material is a sound sufficient proof-relevant schema; it is
still, correctly, not a producer from arbitrary quitting-game data.

| Earlier defect | Canonical repair | Verdict |
|---|---|---|
| An actual output law was not typed as a legal edge from its input | `ClosedSelect` now carries `Legal_a` and theorem (5a) | Repaired |
| `FiniteCase` omitted branch coverage and full branch relations | (10a) requires ambient-closed covering relations, permits boundary overlap, and requires smaller trace-safe branches | Repaired |
| A LawMin error was an undeclared potentially unbounded witness | The error is prescribed convergent exogenous data or lies in a declared `[0,E]` | Repaired |
| Decode used a merely relative closed domain | `X` is closed and `W` is closed directly in `S^p x Z` | Repaired |
| Uniform triangular tails did not control fixed outer columns | The paragraph after (40) now requires convergence of every fixed certified column and all its witnesses | Repaired |

For `ClosedSelect`, Lemma 1 could state the legal conclusion explicitly, but
it follows immediately: closedness gives `(s,w) in R`, and (5a) then gives
`Legal_a(s,w,G(s,w))`.  No closedness of `Legal_a` is needed because legality
is proved at every point of the already closed certificate domain.  The
separate closed `Anc` relation remains the stronger source-provenance field.

The `FiniteCase` repair has the right topology.  Closed branches need not be
disjoint, so a boundary can retain an approximating tag while another tag is
also legal.  Compactness of branch witnesses is inherited from the standing
compact-auxiliary-data convention and from each smaller certified branch.

The LawMin repair is also exact.  Lemma 2 proves `epsilon`-minimality at the
limiting error and exact minimality only when the error tends to zero.  If the
error is stored in `[0,E]`, it is an ordinary compact witness coordinate; if
it is prescribed convergent exogenous data, no witness extraction is needed.

The Decode repair closes the outer-domain gap.  A converging sequence in
`W`, including its compact `Z` coordinate, now remains in `W`.  For triangular
decoders, fixed-column convergence plus the uniform tail estimate is enough:
the tail estimate passes to the fixed-column limits, makes those limits
Cauchy in the inner depth, and identifies the outer decoded limit.

### Minor residual clarifications in `meta/GRAMMAR.md`

These do not invalidate the five repaired constructors.

1. The reward bound should explicitly include the specified all-Never payoff.
   If `r` is still typed only on nonempty quitting coalitions, the displayed
   `R = max_{i,S}|r_i(S)|` does not visibly bound the Never coordinate used in
   later payoff estimates.  Either extend `r` to the empty coalition in the
   notation or take the maximum of the nonempty-table bound and the Never
   payoff bound.
2. The reach paragraph after (39) should distinguish the original floor from
   positivity.  If one law has reach at least `alpha` and the propagated law
   error is below `alpha/2`, the other law is guaranteed reach at least
   `alpha/2`, not necessarily `alpha`.  Both are in the legal positive-reach
   suffix domain, and the finite suffix modulus may be run on the smaller
   floor.
3. `Root(mu,x)` is still described rather than defined.  The closedness claim
   is correct for the intended non-strict complementarity inequalities, but a
   canonical self-contained note should display those inequalities or name
   their exact prior definition.
4. The ancestry conclusion in Lemma 1 follows directly from (8) after the
   limiting pair is shown to lie in `R`; its invocation of closedness of
   `Anc` is redundant in this formulation.  Closedness is essential for
   Decode and for any formulation that assumes ancestry only along the
   approximating executions.

### Audit of `questions/QUITTING_COMPOSITIONALLY_SUFFICIENT_STATE.md`

The question now accurately requests the corrected two-sort interface:
trace-visible ranked branches carry complete closed tagged relations, while a
bare ranked producer is used only after reconstructing an actual node and
must contain terminal consumers and backward outcome maps.  Its nonanswers
also correctly reject semantic closure without legal source ancestry,
vanished-reach conditioning, bare rank inequalities, and restricted deviation
classes.

The main compactness quantifier is nevertheless false as written.  It asks:

> Prove that every increasing, restriction-compatible sequence of finite
> executions in this grammar has a convergent subsequence.

Actual stopping laws are not total-variation compact.  Even for the constant
diagram consisting only of its initial port, the one-player sequence

\[
 \mu_m=\delta_m
\]

has no total-variation convergent subsequence.  The question must either make
tightness a grammar passport or restrict the quantifier to common execution
sequences satisfying the elementary tight-fusion hypotheses:

* finite-coordinate and Never-coordinate limits for every initial and
  exogenous law input;
* one eventual finite-date tail envelope for each persistent such input;
* recorded positive reach floors for persistent suffixes; and
* compactness or prescribed convergence for every additional witness and
  error coordinate.

After this repair, the requested compatible limiting family and the
one-controller conclusion for one initial port are mathematically accurate.

Three outcome clauses should also be tightened.

* “Terminal approximate Nash profiles with one limiting payoff” should mean
  errors tending to zero, unrestricted behavioral caps, and terminal payoffs
  tending to one fixed target.  Those quantifiers feed the checked terminal
  selection endpoint; an unrelated approximate profile at each depth does
  not.
* “A renewable consumed exit from every nonterminal component” should refer
  to the **dispatch-selected successor relation**.  A supplied rank need not
  decrease on every edge of a larger ambient legal-transition graph.
* A counterexample outcome should say explicitly that one fixed positive
  terminal exploitability gap holds against **every behavioral profile**, as
  in `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  (`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`).  An
  independently checkable finite certificate is decisive only when its
  soundness theorem establishes that unrestricted universal quantifier.

Finally, the acceptable-negative clause should not quantify informally over
“every proposed renewable ranked enlargement.”  Without a fixed class of
allowed enlargements, that is not a mathematical proposition: an enlargement
may add an external use counter, new state, or even circular outcome data.
The defensible alternatives are:

1. define one exact adapter contract and prove that no certificate of any of
   its listed constructors exists; or
2. refute a specifically proposed ranked enlargement, including its claimed
   terminal and backward consumers.

Failure of one exact same-source trace relation need not exclude every
enlarged-state control algorithm.  This scope distinction is already handled
correctly in the canonical grammar and should be mirrored in the question.

### Post-edit conclusion

`meta/GRAMMAR.md` passes the requested adapter re-audit after the minor
clarifications above.  The maintained question does not yet pass literally:
its universal subsequence claim needs tight-fusion hypotheses, and its exit,
counterexample, and acceptable-negative quantifiers need the stated scope
repairs.  These are edits to the question surface, not new gaps in the
canonical adapter lemmas.

## Initial verdict on superseded `meta/GRAMMAR_2.md`

The remainder of this file preserves the initial audit that motivated the
repairs summarized above.  Its statements that repairs are still needed
refer to the superseded draft, not to canonical `meta/GRAMMAR.md`.

The mathematical cores of the selected-root, moving-optimization, moving-
minimization, and fixed summable-decoder arguments are correct.  In
particular:

* a recorded exact cap root has a closed constraint graph and literal
  prefixing is continuous;
* closed graph plus comparison transport is sufficient to preserve an
  optimizer over a moving compact feasible set;
* the stated common tail envelope gives a compact total-variation law
  carrier, with the Never atom retained separately;
* Lemma 2 correctly preserves the limiting approximation error and needs
  error tending to zero for exact limiting minimization; and
* Theorem 3 correctly gives an actual law-valued limit, the tail bound, and
  continuity of a fixed decoder.

Three theorem-surface repairs are still needed before these sections define
the claimed trace grammar.

1. `ClosedSelect` says that `G` is an "actual behavioral compiler," but the
   displayed data only type it as a map into actual standalone stopping laws.
   They do not state that `G(s,w)` is a legal edge output constructed from
   `s`.  Actuality of the endpoint is not legality of the transition.
2. `FiniteCase` does not yet type its closed branch relation, its coverage of
   the adapter domain, or its branch-specific witness data.  The intended
   constant-tag subsequence argument is correct once those data are stated.
3. In Decode, `W` is only said to be closed as a subset of `X x Z`, while
   `X` need not be closed in the ambient source space.  This suffices for the
   pointwise decoder but not for invoking that decoder at an outer limiting
   source.  The later diagonal needs `W` ambient-closed, or a separate theorem
   that the limiting source remains in `X` and the limiting pair remains in
   `W`.

There are also two smaller exactness issues: a varying LawMin error needs a
declared compact coordinate (or must be treated as prescribed convergent
exogenous data), and the triangular-decoder sentence needs fixed-column
outer convergence in addition to uniform tail summability.

Thus Sections 3.1--3.3 and the pointwise part of Section 4 pass as ordinary
mathematics.  Sections 1--2 and the outer-limit use of Section 4 remain a
conditional interface, not yet a fully typed finite grammar.  Nothing in
this review is a new Lean-checked theorem.

## Claim being checked

The document introduces a trace language whose non-elementary edges are
closed selected relations, finite recorded branches, robust selected roots or
optimizers, and summably decoded limits.  The intended conclusion of these
sections is stronger than law-level compactness: every limiting output must
remain an actual legal, and when requested source-faithful, successor of the
same limiting input.

The audit therefore separates four properties:

1. compactness or subsequential convergence of recorded witnesses;
2. closedness of the mathematical selection constraint;
3. actuality and continuity of the output stopping law; and
4. legality and source ancestry of the edge from its named input.

The displayed optimization lemmas establish items 1--3 for their concrete
compilers.  Item 4 requires an explicit typed edge theorem; it is not implied
merely by membership of the output in `S^q`.

## Sources inspected

The immediate mathematical bases were `meta/EXECUTABLE_COMPACT_STATE.md` and
`meta/EXECUTABLE_ADAPTERS.md`.  I also inspected the following exact Lean
interfaces rather than treating those conference notes as theorem truth.

* `toScalarHazard`, `toScalarHazard_stopMass`, and
  `toScalarHazard_neverMass`
  (`MathUE/Probability/StoppingLawReconstruction.lean`) reconstruct an actual
  hazard from every complete stopping law.
* `quittingStoppingLawBehaviorStrategy` and
  `quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy`
  (`UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`)
  give the quitting-game behavioral realization and recover its stopping law
  exactly.
* `isClosed_isεQuittingRootEndpointNash_simplex` and
  `isCompact_and_nonempty_setOf_isZeroQuittingRootEndpointNash_root`
  (`UniformEquilibrium/Quitting/Boundary/Repair/ComplementarityClosed.lean`)
  check joint closedness of endpoint complementarity and compact nonemptiness
  of each fixed-tail exact-root slice in simplex coordinates.
* `QuittingSourceFaithfulMinimumCausalization` and
  `nonempty_sourceFaithfulMinimumCausalization`
  (`Research/Quitting/SourceFaithfulMinimumLawCausalization.lean`) show what an
  existing source-faithful interface retains: the supplied profile and mark
  families are indices, while only cutoffs and finite root words are selected.
* `sourceFaithfulTargetProfile`, `sourceFaithfulTargetMark`,
  `FinFourSourceFaithfulMinimumTargetRegeneration`, `chronology_profile_eq`,
  and `chronology_mark_eq`
  (`Research/Quitting/FinFourProducerAtlas/SourceFaithfulThreeRoleRegeneration.lean`)
  retain literal incoming chronology data.  This is richer than an untyped
  source label on an output law.

The last two files are in `Research`, not the integrated production surface;
they are evidence about the shape of the relevant adapter data, not a claim
that `GRAMMAR_2.md` has been formalized.

## 1. Ambient source category

The ambient law choice is sound, but its hypotheses should be literal:

> Fix a finite nonempty player type `I` and a bounded finite quitting reward
> table.  Give `Delta(K)` its full `ell^1(K)` metric, where the Never point is
> a separate coordinate.

Finiteness of `I` is used in the sum metric, the finite root polynomials, the
compact root cube, and every finite-player constant.  As currently written,
Section 1 defines the unweighted sum in (1) without first saying that `I` is
finite; for infinite `I` the displayed quantity may be infinite and is not a
metric on all of `S`.

With finite `I`, `S` is complete because probability vectors form a closed
subset of `ell^1(K)`.  The stopping-law reconstruction declarations above
justify the word "actual": every point is realized by a behavioral strategy
on the live spine.  This says nothing yet about whether an arbitrary map
between packets is a permitted source-derived operation.

The phrase "all compact auxiliary parameters" should also distinguish
compact witnesses from prescribed convergent exogenous coordinates.  This
becomes relevant for the real-valued approximation error in Section 3.3.

## 2. `ClosedSelect`

### 2.1 The limit calculation is correct

Suppose `R` is closed in the ambient product, `(s_m,w_m)` belongs to `R`, and
`(s_m,w_m)` tends to `(s,w)`.  Then `(s,w)` belongs to `R`.  The modulus gives

\[
 G(s_m,w_m)\longrightarrow G(s,w).
\]

If (8) is a field required at every point of `R`, then ancestry at the limit
actually follows directly by applying (8) to `(s,w)`.  Alternatively, it
follows by passing the triples through the closed relation.  Thus the cited
closedness of `Anc` is harmless but redundant for Lemma 1 as presently
stated.  It becomes substantive if ancestry is supplied only along the
approximating executions or includes additional converging witnesses.

### 2.2 Actual output is not yet legal edge semantics

The type

\[
 G:R\to S^q
\]

only says that the output is an actual standalone law packet.  For example,
with `p=q=1`, singleton `W`, `R=S x W`, and

\[
 G(s,*)=\delta_\infty,
\]

all displayed closedness and modulus conditions hold.  Nevertheless this is
not a positive-reach depth-one suffix of the source `delta_0`, nor is it a
literal prefix construction from that source.  Calling `G` an "actual
behavioral compiler" does not resolve the ambiguity unless that phrase is
defined to include a proof of the named edge semantics.

Every `ClosedSelect` occurrence therefore needs a typed relation such as

\[
 \mathsf{Legal}_E(s,w,G(s,w)),
\]

or a closed witnessed graph already proved to be a subrelation of the named
legal operation.  When all that is intended is a freely selected exogenous
law, the edge should say so.  When ancestry matters, the stated `Anc` plus
the semantic implication is a sufficient stronger field.

This repair is already satisfied by the concrete exact-root edge: the output
is the literal prefix `T_x mu`.  It is not automatic for the generic
constructor.

### 2.3 `FiniteCase`

The finite-tag subsequence argument is correct.  A sound interface should
state, for each `b in B`, a relation

\[
 P_b\subseteq \text{(full input and branch-witness carrier)}
\]

such that:

* `P_b` is closed in the declared ambient topology;
* the `P_b` cover the adapter domain;
* recorded membership in `P_b` is part of an execution; and
* the branch adapter is a trace-safe grammar expression on `P_b` with all its
  own compact witnesses and legal-edge certificates.

The predicates need not be disjoint.  Overlap is often exactly how a closed
finite cover handles a boundary.  If they are required to be disjoint as well
as closed and exhaustive, only clopen partitions are available.  The
document's warning about `g(s)>0` is correct: recording its truth value does
not close that branch.

The current phrase "a closed-selected or decoded adapter `E_b`" is narrower
than the grammar displayed in (2).  If elementary, composite, nested-case,
and already certified trace-rank branches are also intended, write simply
that every `E_b` is a trace-safe expression of smaller syntax height.

## 3. Selected roots and moving optimization

### 3.1 Recorded exact cap roots pass

For bounded rewards, total-variation convergence of opponent law packets
gives uniform convergence of every deterministic stopping-time response
payoff.  Hence

\[
 |B_i(\mu)-B_i(\nu)|
 \le R\sum_{j\ne i}\|\mu_j-\nu_j\|_1
\]

under the note's `ell^1` convention.  The exact complementarity inequalities
are finite non-strict polynomial inequalities in the root and continuous in
the cap.  Therefore (12) is closed.  This agrees with the checked endpoint
closedness declaration cited above.

The prefix estimate (14) is also correct player by player and after summing.
Thus the exact-root occurrence is a valid `ClosedSelect` instance with
witness cube `[0,1]^I`, closed root relation, literal-prefix compiler, and
literal source ancestry.  No continuous endogenous root selector is being
asserted.

The definition of `Root(mu,x)` should either reproduce the exact
complementarity inequalities or name the earlier definition on which it
depends.  "Finite product-root inequalities" is not by itself an exact
standalone definition, although the claimed closedness is correct under the
intended definition.

### 3.2 Robust moving argmax and argmin pass

The hypotheses in (15)--(17) are sufficient.  Closed graph is the outer
semicontinuity needed for limiting feasibility.  Comparison transport (16)
is the inner semicontinuity needed to approximate every competitor that is
available only at the limiting source.  Continuity of `f` on the feasible
graph then permits passage through the maximizing inequality.  Compactness
of `A` and closed fibres give existence and subsequential compactness.

The same proof with reversed inequalities yields Lemma 2.  For every
`eta in F(s)`, take the comparison lift `eta_m`; then

\[
 \Phi(s,\rho)\le \Phi(s,\eta)+\varepsilon.
\]

Taking the infimum gives (23).  The requirement
`epsilon_m -> 0` for an exact limiting minimizer is therefore exact, not a
technical convenience.  Without convergence, `limsup epsilon_m` gives the
safe displayed upper bound (and `liminf` can in fact be used when all the
other displayed quantities converge).

The tail in (19) should be described explicitly as the late **finite-date**
tail.  The compactness proof uses the finite core

\[
 \{0,\ldots,N,\infty\},
\]

so the Never atom is retained, not forced to zero.  Under that reading,
`L_T` is compact in full `ell^1(K)`.

### 3.3 What optimization does not itself supply

The optimizer lemmas close the selected-witness relation.  To instantiate
`ClosedSelect`, one must still specify the actual output compiler `G`, its
modulus, and any required ancestry.  This is automatic for a maximal exact
root followed by literal prefixing.  It is not automatic for a selected law:
outputting the minimizer `rho` gives an actual standalone behavior, but it
does not make `rho` a source-faithful descendant of `s`.

There is also a small syntactic mismatch for approximate minimizers.  If the
recorded witness is `(rho,epsilon)`, the natural relation is closed in

\[
 L_T\times[0,E]
\]

for a declared finite `E`.  The current grammar requires compact witness
spaces but only later assumes the error sequence converges.  Convergence does
make that one sequence bounded, but a grammar certificate should either
declare the compact error interval in advance, treat `epsilon_m` as a
prescribed convergent exogenous coordinate, or restrict the constructor to a
fixed tolerance (especially `epsilon=0`).

## 4. Source-faithful summable Decode

### 4.1 The fixed decoder theorem passes

For each fixed input `xi in W`, (27)--(28) make `M_n(xi)` Cauchy.  Since
`S^q` is complete, its limit is an actual probability-law packet.  Telescoping
gives (35), and inserting the two `M_N` approximants gives exactly (36).
Choosing `N` before using the modulus of that one finite macro proves
continuity; no equicontinuity over decoder depth is required.

For a fixed `(s,z)`, (32) and closedness of `Anc` give (37).  Together with
the explicit semantic theorem (33), this is a sufficient source-faithfulness
certificate.  Crucially, it is an assumption about the intended source
relation, not a consequence of summable convergence alone.

The project examples show why the semantic theorem must be precise.  Existing
source-faithful causalization retains literal profile and marked-date
families, not just an endpoint law carrying a textual source name.  If the
intended ancestry mentions profiles, dates, marks, deleted laws, or backward
compilers, those objects must occur in `Z`/`Anc` with an adequate topology,
or the compiler must retain them by definitional equality.  A relation only
on stopping-law endpoints can certify only the source property encoded by
those endpoints.

### 4.2 Outer-domain closure is missing

The hypotheses say

\[
 X\subseteq S^p,\qquad W\subseteq X\times Z,
\]

and then call `W` closed.  Normally this means relatively closed in
`X x Z`.  If `X` is not closed in `S^p`, a sequence in `W` may converge in
the ambient product to a source outside `X`, where `D` is undefined.

A minimal model is a relatively closed domain parametrized by `t in (0,1]`
with sources

\[
 s_t=t\delta_0+(1-t)\delta_\infty.
\]

The points with `t=1/m` converge in `S` to the omitted `t=0` source.  Relative
closedness of `W` does not license evaluation of the decoder there.

The pointwise Theorem 3 is unaffected because it keeps `(s,z)` fixed in
`W`.  The later outer diagonal requires one of:

* `X` closed in `S^p` and `W` closed in `X x Z`;
* `W` closed directly in the ambient `S^p x Z`; or
* a separate domain-preservation theorem for the reconstructed limit.

The same ambient/relative distinction applies to `Anc` when ancestry is
passed along a changing outer source rather than at one fixed decoder input.

### 4.3 The triangular sentence needs a fixed-column hypothesis

Condition (40) controls the error between each row's decoder and a fixed
inner truncation.  By itself it says nothing about the outer behavior of that
fixed truncation.  For example, setting `M_{m,n}=delta_m` for every `n` gives
zero seam bounds and hence satisfies (40), while the decoded rows have no
total-variation convergent subsequence.

A triangular theorem should additionally require, after the common outer
subsequence extraction, that every fixed column `M_{m,N}` is an execution of
one persistent lower-grammar macro and converges to a compatible limiting
macro `M_{infinity,N}`.  This is the missing hypothesis stated explicitly in
the earlier adapter note as "every fixed inner macro commutes with the outer
limit."  Uniform summability then permits exchanging the outer and inner
limits.

### 4.4 Reach-budget wording

If a decoded source has suffix reach at least `alpha` and its approximation
has law error below `alpha/2`, the approximation is guaranteed reach at least
`alpha/2`, not the original floor `alpha`.  This is enough for legality and
for a suffix modulus recomputed on the `alpha/2` domain.  The sentence after
(39) should say which object has the certified `alpha` floor and should not
claim that both objects meet that same floor unless extra slack was assumed.

## Required repairs before downstream use

The shortest exact repair is:

1. state finite nonempty `I` and bounded rewards in Section 1;
2. add a typed legal-edge theorem to every `ClosedSelect`, with `Anc` as the
   stronger source-faithful option;
3. define each `FiniteCase` branch as a closed covering relation on the full
   branch data;
4. package LawMin errors in a fixed compact carrier or prescribe their
   convergence as exogenous data;
5. make decoder domains ambient-closed (or prove domain preservation); and
6. add fixed-column convergence to the triangular decoder clause.

With those changes, the selected-root and moving-optimization results and the
fixed source-faithful decoder provide the intended trace-safe constructors.
They remain sufficient certificate schemas: they do not establish that the
current Fin4 source-regeneration steps actually supply comparison transport,
summable seams, or closed ancestry.

## Concrete next question

Can one current nontrivial Fin4 regeneration be written as an ambient-closed
`Anc` relation whose coordinates retain the literal profile and marked-date
family, and whose finite macros satisfy one source-uniform summable seam
bound?  Answering that for one edge would test whether `Decode` is merely a
sound schema or an adapter available at the present frontier.
