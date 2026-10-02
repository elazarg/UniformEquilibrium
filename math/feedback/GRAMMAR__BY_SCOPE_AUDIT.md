# Scope audit of `GRAMMAR.md`

Reviewer: `SCOPE_AUDIT`

## Status and verdict

The one-player vanishing-reach calculation is correct and worth preserving.
It proves a sharp relation-level obstruction: the graph closure of the
positive-reach depth-one suffix relation has two incompatible actual target
laws over the source \(\delta_0\), neither of which is a legal suffix of that
source.  Under the document's explicit protected-source interpretation, an
exact-source elementary reconstruction cannot approximate the
\(\delta_\infty\) branch.  The same closed relation also has a self-loop, so
no natural-valued function can strictly decrease on every pair in the
relation.

This is a valid narrow warning about **closed-suffix regeneration**, and it
can satisfy the acceptable-negative clause of
`questions/QUITTING_COMPOSITIONALLY_SUFFICIENT_STATE.md` once the adapter
contract is stated at exactly that relation-level scope.  It does not justify
the opening sentence that the residual question as a whole has a negative
answer.  It refutes one deliberately defined edge, not every admissible
grammar or every use of suffix regeneration.

The positive part of `GRAMMAR.md` should not replace
`meta/EXECUTABLE_ADAPTERS.md`.  It largely duplicates that corrected note,
while omitting hypotheses that the correction made essential.  In particular:

1. a `CW` edge is required only to have a closed graph, not to have a proved
   actual legal edge semantics;
2. an `RC` target is merely close to an executable output and may then be used
   as if it were itself an executable descendant; and
3. `RD` edges are included directly in the coherent-diagonal theorem even
   though rank decrease proves termination, not limit commutation.

The third point repeats the precise error already removed from the corrected
adapter theorem.  As written, the positive coherent-diagonal theorem is not
proved.

All conclusions here are ordinary mathematics, not new Lean-checked results.

## Claim being checked

The document makes two logically different claims.

First, it proposes three proof-relevant constructors, `CW`, `RC`, and `RD`,
and claims that increasing finite diagrams built from them have one coherent
actual execution under compactness, simultaneous finite realizability,
vanishing reconstruction error, and persistent positive reach.

Second, it defines

\[
 \operatorname{CSR}_1=
 \overline{\{(\mu,S_1\mu):q_1(\mu)>0\}}
\]

and claims that this particular closed-suffix relation admits none of the
three permitted adapter types.

These claims should be separated.  The second contains a sound narrow
obstruction.  The first is a conditional interface sketch with substantive
typing and closure gaps.

## 1. The vanishing-reach example is exact

For the one-player table

\[
 r(\{1\})=1,\qquad r(\varnothing)=0,
\]

the displayed semantic formulas are correct:

\[
 U(\mu)=1-\mu(\infty),\qquad B(\mu)=1,
 \qquad B(\mu)-U(\mu)=\mu(\infty).
\]

With \(p_n=2^{-n}\), let

\[
 \mu_n^Q=(1-p_n)\delta_0+p_n\delta_1,
 \qquad
 \mu_n^N=(1-p_n)\delta_0+p_n\delta_\infty.
\]

Both converge in total variation to \(\delta_0\), their depth-one reach is
\(p_n\), and

\[
 S_1\mu_n^Q=\delta_0,
 \qquad
 S_1\mu_n^N=\delta_\infty.
\]

Consequently

\[
 (\delta_0,\delta_0),
 (\delta_0,\delta_\infty)
 \in \operatorname{CSR}_1,
\]

while \(q_1(\delta_0)=0\).  Thus neither pair is a literal legal
positive-reach suffix execution at the limiting source.  This is the clean
mathematical core: conditioning at vanishing mass has incompatible cluster
values even on finitely supported, uniformly tight actual laws.

There is one minor wording correction.  The sources do not both have support
contained in \(\{0,1\}\), because \(\mu_n^N\) has an \(\infty\) atom.  Their
**finite-date support** is contained in \(\{0,1\}\), and their full supports
are finite.

## 2. Exact-source reconstruction fails under the stated protected grammar

Suppose the source coordinate is literally \(\delta_0\), is protected from
replacement, and the allowed elementary descendants are formed by finite
prefixing, concatenation, and legal positive-reach suffixing.  Every such
descendant has zero Never mass.  The induction in `GRAMMAR.md` is correct:

- a finite prefix with an almost-surely finite continuation remains
  almost surely finite;
- finite concatenation has the same property; and
- conditioning an almost-surely finite law on a positive-mass survival event
  does not create Never mass.

Hence every protected descendant \(\nu\) satisfies

\[
 \nu(\infty)=0,
 \qquad
 d_{\mathrm{TV}}(\nu,\delta_\infty)=1.
\]

This is a genuine fixed reconstruction error.  It is stronger and clearer to
state it as a total-variation and prescribed-payoff separation.  The sentence
about a fixed tester currently says that the deviation gain is zero on every
faithful recovery and one at the target.  That distinguishes the target from
the recovery, but it is not a positive exploitability error *of the recovery*.
No such claim is needed: loss of source provenance and the unit law/payoff
separation already meet the intended obstruction.

The scope assumption is essential.  By the definition of graph closure,
every pair in \(\operatorname{CSR}_1\) has legal approximating pairs with
varying sources.  In particular,

\[
 (1-\varepsilon)\delta_0+\varepsilon\delta_\infty
\]

has suffix \(\delta_\infty\).  Thus the example does **not** refute an
approximation notion that permits the source itself to be reselected at each
accuracy.  It refutes the exact-same-source, protected-provenance
reconstruction required for a one-controller diagonal.  The theorem should
say this in its statement, not only in the proof.

## 3. The rank statement is valid only at relation level

The calculation

\[
 (\delta_\infty,\delta_\infty)\in\operatorname{CSR}_1
\]

is correct.  Therefore there is no function

\[
 R:\Delta(\overline{\mathbb N})\to\mathbb N
\]

such that \(R(\tau)<R(\mu)\) for **every**
\((\mu,\tau)\in\operatorname{CSR}_1\).

That is the exact theorem.  It should not be enlarged to “no ranked adapter
can exist” without fixing what a ranked adapter must do with every relation
pair.  A ranked producer may declare some states terminal, restrict the
transition subrelation, or compile a whole finite ranked subtree into another
adapter.  The self-loop rules out a strict rank on the full `CSR_1` relation;
it does not rule out all algorithms that mention this relation internally.

For the acceptable-negative answer, define the edge contract to require that
every `CSR_1` pair is an admissible nonterminal transition.  Under that
contract the self-loop is decisive.  Otherwise retain only the closed-limit
and protected-reconstruction no-go and do not claim the universal rank
conclusion.

## 4. `CW` does not yet encode legality

The proposed `CW` constructor assumes only

\[
 (x,w,y)\in G_a
\]

for a named closed set \(G_a\).  Closedness says that witnessed pairs survive
limits.  It does not say that a surviving pair is a legal game execution from
its source.

This omission creates an internal contradiction.  On a fixed tight carrier,
`CSR_1` is itself a named closed relation between actual law states and hence
would qualify syntactically as a `CW` edge.  The later no-go correctly says
that its pairs over \(\delta_0\) are not legal suffix executions.  Therefore
the `CW` definition is too weak to support the claimed actual-execution
semantics.

A sound constructor needs both:

1. a typed actual legality relation
   \(\operatorname{Legal}_a(x,w,y)\); and
2. a theorem that this legality relation is closed on the declared carrier,
   or a closed witnessed graph already defined as a subset of that legal
   relation.

Selected exact roots satisfy this stronger contract because the witnessed
root inequalities pass to the limit and the output is the literal prefix.
An arbitrary named closed graph does not.

## 5. `RC` does not yet define executable target ports

The `RC` data produce an actual elementary output \(\widehat y=P(x)\) and
only assert

\[
 d_{\mathrm{TV}}(\widehat y,y)\le\varepsilon.
\]

Nothing displayed makes \(y\) itself an elementary descendant of \(x\).
If subsequent edges are allowed to use \(y\) as an exact source port, the
grammar has promoted a nearby standalone law into a fresh executable source.
That is precisely the operation the prose says is forbidden.

There are two coherent repairs:

- make \(\widehat y\), not \(y\), the executable output port, and carry \(y\)
  only as a semantic comparison witness with an accumulated error ledger; or
- replace the one-shot approximation by a summably Cauchy decoded macro and
  a typed closed ancestry relation, as in Proposition 5 of the corrected
  `EXECUTABLE_ADAPTERS.md`.

The present `RC` fields also do not encode approximate optimality.  Therefore
the classification claiming that `RC` automatically covers approximate
maximizers and minimizers is unsupported unless objective error and
comparison transport are added explicitly.

## 6. The coherent-diagonal theorem fails for `RD`

The claim that each finite constraint set \(F_n\) is closed does not follow
for ranked edges.  The inequality \(m'<m\) is closed because the ranks are
discrete, but the actual child transition, branch selection, terminal
consumer, and any backward outcome compiler may be discontinuous in the
source.  Strict rank decrease bounds evaluation length; it supplies no
topological limit theorem.

This is exactly the issue repaired in `EXECUTABLE_ADAPTERS.md`: ranked
producers are excluded from its coherent-diagonal theorem until the entire
solved ranked transition is compiled into a closed adapter.  `GRAMMAR.md`
should inherit that boundary.  The valid options are:

- remove `RD` from the compact intersection theorem and keep it as a separate
  pointwise well-founded producer; or
- require a closed graph or continuous actual compilation for the fully
  evaluated ranked subtree, including terminal and backward maps.

There are two additional typing omissions:

- the displayed `RD` constructor does not contain a total step function or a
  backward outcome map, so terminal consumers alone do not produce an outcome
  at the original node; and
- if ranks are assignment variables, \(\mathbb N\) is not a compact witness
  factor.  Ranks must be fixed syntax labels, uniformly bounded on the
  relevant subtree, or removed from the compact extraction space.

Accordingly, the finite-intersection argument may become valid for repaired
`CW` edges and fixed executable reconstructions on compact tight boxes.  It is
not valid for the three-constructor grammar as written.

## 7. Precision and novelty relative to the other two documents

Most of the positive material is duplication:

- the actual stopping-law carrier and positive-reach conditioning estimate
  repeat `EXECUTABLE_COMPACT_STATE.md`;
- recorded closed selectors, compact optimization, tight minimization, and
  executable reconstruction repeat the adapter taxonomy in
  `EXECUTABLE_ADAPTERS.md`;
- the summable controller-port paragraph repeats the decoded-limit/Cauchy
  mechanism; and
- the terminal-Nash discussion is only the supplied consumer already present
  in the compact-state and adapter documents.

The useful new pieces are narrower:

1. the explicit protected-provenance syntax idea;
2. the compact finite-intersection formulation using simultaneous
   finite-diagram realizability with one fixed initial port; and
3. the minimal one-player incompatible-suffix example at vanishing reach.

The first remains an untyped proposal.  The second is potentially clean after
removing `RD` and distinguishing exact executable ports from approximate
semantic witnesses.  The third is the strongest material in the file and is
ready to preserve after the scope corrections above.

The file is not yet a “precise finite grammar.”  It gives three constructor
names whose parameters range over arbitrary compact spaces, closed sets,
programs, moduli, provenance assertions, and consumer proofs, without an
inductive syntax, typed port signatures, legal-execution relation, or
restriction operation.  This is a proof-relevant adapter schema.  It should
be labelled as such unless those data are formally defined.

## 8. Recommended organization

Use `meta/EXECUTABLE_COMPACT_STATE.md` as the elementary stopping-law and
tight-fusion foundation.  Use corrected `meta/EXECUTABLE_ADAPTERS.md` as the
canonical positive non-elementary adapter schema.  Do not maintain a second,
weaker positive grammar in `GRAMMAR.md`.

The clean organization is:

1. move the one-player result into a standalone file such as
   `meta/VANISHING_REACH_SUFFIX_CLOSURE_NO_GO.md`;
2. state its status as an exact ordinary-mathematics no-go for the full
   `CSR_1` relation under exact-source protected provenance;
3. cross-reference it from the reach-boundary discussion of
   `EXECUTABLE_ADAPTERS.md` or `EXECUTABLE_COMPACT_STATE.md`; and
4. either retire `GRAMMAR.md` or reduce it to a short comparison page pointing
   to the elementary theorem, corrected adapter schema, maximal-root no-go,
   and vanishing-reach no-go.

The opening conclusion should become:

> The `CSR_1` edge gives an acceptable narrow negative answer to the stated
> question: raw graph closure of positive-reach suffixing does not preserve
> legal same-source execution, and its \(\delta_\infty\) branch has unit
> protected-source reconstruction error.  This does not rule out grammars
> retaining a positive reach floor, decoded source-faithful macros, or a
> separately closed compiled ranked subtree.

That wording records exactly what the example proves and does not duplicate
or weaken the corrected positive adapter theorem.

## Sources inspected

- `questions/QUITTING_COMPOSITIONALLY_SUFFICIENT_STATE.md`;
- `meta/EXECUTABLE_COMPACT_STATE.md`;
- `meta/EXECUTABLE_ADAPTERS.md`;
- `meta/MAXIMAL_ROOT_ADAPTER_NO_GO.md`;
- `meta/GRAMMAR.md`;
- `feedback/EXECUTABLE_ADAPTERS__BY_TOPOLOGY_AUDIT.md`;
- `feedback/EXECUTABLE_ADAPTERS__BY_DIAGONAL_AUDIT.md`;
- `feedback/EXECUTABLE_ADAPTERS__BY_NOGO_AUDIT.md`;
- `feedback/EXECUTABLE_COMPACT_STATE__BY_RECONSTRUCTION_AUDIT.md`;
- `docs/FRONTIER.md`; and
- `docs/TOOLKIT.md`.

## Requested next check

After separating the no-go, check whether the fixed-initial-port finite-
intersection argument can be stated entirely for the four corrected closed
adapter classes, with executable ports and semantic comparison witnesses as
different types.  That is the only positive content in `GRAMMAR.md` not
already subsumed verbatim by the corrected adapter note.
