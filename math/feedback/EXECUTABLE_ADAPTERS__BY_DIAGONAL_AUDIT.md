# Independent diagonal audit of `EXECUTABLE_ADAPTERS.md`

## Status and verdict

The selected-root, robust-argmax, tight fixed-law, and fixed-decoder arguments
contain a sound closed-limit core.  The two-player maximal-root example is also
correct and gives an independently checkable fixed-error obstruction to using
the bare maximal-root relation in a closed diagonal language.

Theorem 9 is not proved at its stated scope.  There are two separate issues.

1. Its statement does not introduce the common restriction-compatible
   sequence of actual executions to which “coordinate coherence,” “one
   subsequence,” and convergence of traces refer.  That data is explicit in
   Theorem 1 of `meta/EXECUTABLE_COMPACT_STATE.md` and has to be imported into
   the theorem statement, not only alluded to.
2. More substantially, Proposition 6 proves pointwise termination of supplied
   ranked data, but it proves no closedness or continuity of the terminal
   consumer or backward compiler.  Consequently a `RankStep` edge need not
   commute with the outer total-variation limit.  An exact one-step
   counterexample is given below.

Thus one coherent initial controller follows from the earlier elementary
tight-fusion theorem once its full hypotheses and execution packet are
assumed.  A coherent limiting execution for all five new constructors does
not yet follow.  The terminal-Nash paragraph is a valid conditional consumer
of an already supplied tight vanishing-debt root sequence; it is not a
producer and does not use the non-elementary grammar in an essential way.  The
renewable-exit paragraph is the conclusion already stored in the `RankStep`
certificate.

On the maintained question, the note gives a good acceptable negative answer
for the specifically defined **bare maximal-root edge**.  It does not yet give
the claimed positive finite grammar with a coherent actual diagonal, and it
does not produce any of the required data from an arbitrary reward table.

## Claim audited

Theorem 9 is intended to say the following.  Given increasing finite rooted
diagrams and compatible actual executions, tightness reconstructs one actual
initial stopping-law profile; after extracting all compact witnesses, each
`SelRoot`, `ArgOpt`, `LawMin`, `Decode`, and `RankStep` occurrence remains
legal; and every fixed finite trace is the trace of one limiting execution
from that same initial profile.

I checked separately:

1. whether the five-constructor language has actual instances;
2. whether the four compact/decoded constructors commute with limits;
3. whether rank termination implies limit commutation;
4. whether the conclusion really gives one controller rather than one profile
   per depth; and
5. whether either displayed consumer supplies conjecture-facing data.

## 1. Nonvacuity versus certificate loading

The constructor classes are nonempty, but this is much weaker than a
nontrivial producer theorem.

* `SelRoot` has simple actual instances, and more generally the auxiliary
  finite binary game has a mixed Nash root.  Once the root is recorded,
  Proposition 1 correctly proves closedness of the exact-root inequalities and
  continuity of the literal prefix.
* `ArgOpt` has constant-feasible-set examples; Proposition 2 is the standard
  closed-graph plus comparison-lift argument.
* `LawMin` has singleton and other fixed tight feasible-set examples.
* `Decode` has at least constant sequences `M_n = M`, and genuine summably
  Cauchy refinements when those have independently been constructed.
* `RankStep` has every terminal certificate as a rank-zero example.

So the grammar is not empty.  It is, however, proof-loaded enough that
nonvacuity gives no Fin4 coverage.  In particular, a `Decode` label already
contains the source-rooted macros and a summable seam theorem, while a
`RankStep` label already contains a terminal consumer or a smaller child and a
backward map for the desired outcome.  Proposition 6 is then structural
recursion over that supplied proof object.  It is sound as a verifier, but it
does not construct the proof object.

There is also no precise finite syntax yet.  The five constructor **names**
are finite, but their parameters range over arbitrary compact spaces,
correspondences, outcome types, sequences of macros, real seam bounds,
provenance maps, and consumer proofs.  “Coded sequence” is asserted without a
code type, evaluation relation, or closure rule.  This can be a useful
proof-relevant schema, but it is not yet a defined finite grammar whose legal
executions and traces support structural induction.

## 2. The four closed or decoded constructors

### Selected roots

Proposition 1 is correct.  The cap vector is continuous in total variation,
the complementarity inequalities are closed in `(x,b)`, and the one-root
prefix estimate proves convergence of the actual output laws.  No continuous
root selector is being smuggled in.

### Compact optimization

Proposition 2 is correct.  Closed graph gives feasibility of the limiting
maximizer, and comparison lift supplies approximants to every limiting
competitor.  Passing the maximizing inequalities to the limit then proves
maximality.  The comparison-lift hypothesis is essential.

### Fixed-law minimization

Lemma 3 and Proposition 4 are correct for a fixed closed subset of the stated
tight carrier.  There is a mismatch in Theorem 9, however.  Proposition 4
requires the recorded approximation errors to tend to zero in order to
conclude exact minimality.  Theorem 9 assumes only a fixed tail envelope and
does not say whether a persistent occurrence is exact, has one fixed
approximation tolerance, or has tolerances tending to zero.  A repaired
theorem should either:

* restrict `LawMin` occurrences to exact minimizers;
* retain a convergent tolerance and conclude minimality at that limiting
  tolerance; or
* explicitly assume `epsilon_m -> 0` before invoking Proposition 4.

For a source-dependent feasible carrier, the note correctly observes that an
additional comparison-lift property is required.

### Decoded limits

Proposition 5 gives the right analytic argument at the stopping-law level,
provided the intended hypotheses are made literal:

\[
 d(M_N(s,z),M_N(s',z'))
 \leq \omega_N(d(s,s')+d_Z(z,z'))
\]

must hold on `W`, including dependence on `z`, and the seam bound must be
uniform on `W`.  Then one first chooses `N` from the summable tail and only
afterward applies the fixed-macro modulus.  This proves continuity of `D` and
actuality of its law-valued output.

Two qualifications remain.

1. The “common source-provenance map” is not defined as a relation and no
   closedness theorem for it is stated.  Proposition 5 proves convergence of
   output laws.  It proves preservation of any stronger source-faithful
   ancestry assertion only after that assertion is defined and shown closed,
   or after the decoder constructs the ancestry literally.
2. If a decoder occurrence itself varies with the outer execution, (27) is
   only part of a triangular theorem.  One must also specify the limiting
   fixed-depth macros, their mutual compatibility, and the limiting decoder.
   For a persistent occurrence with fixed `M_n`, `c_n`, and `W`, the
   non-triangular Proposition 5 is enough.

Accordingly, `Decode` edges commute as law-valued maps under a clear repaired
hypothesis.  The present text does not yet prove every additional provenance
field in the claimed complete trace commutes.

## 3. Exact obstruction to the `RankStep` part of Theorem 9

Strict decrease of a natural rank controls the **length** of an evaluation.
It does not control how the evaluated outcome varies with the source.  The
type in (28) puts no topology, closed-graph condition, or modulus on either a
terminal consumer or the backward map

\[
 \mathcal O(N')\longrightarrow\mathcal O(N).
\]

Here is a one-step instance satisfying the displayed rank interface but
failing the conclusion of Theorem 9.

Let there be one stopping-law coordinate and put

\[
 \mu^m=\frac1m\delta_0+\left(1-\frac1m\right)\delta_\infty,
 \qquad
 \mu^\infty=\delta_\infty.
\]

Then `mu^m -> mu^infinity` in the note's full `l1` metric, with distance
`2/m`, and the family has a uniform finite-tail bound (all finite mass is at
date zero).

For every source `s`, take a rank-one parent and a rank-zero child.  Let the
actual child adapter be the identity, let both outcome types be the space of
actual stopping laws, and let the rank-zero terminal consumer return its
source law.  Use as backward compiler the actual-law-valued function

\[
 H(\eta)=
 \begin{cases}
 \delta_1,&\eta=\delta_\infty,\\
 \delta_0,&\eta\ne\delta_\infty.
 \end{cases}
\]

Every datum required by (28) exists:

* the child is actual;
* the rank drops from one to zero;
* the terminal child has a consumer; and
* `H` maps every child outcome to an actual parent outcome.

The diagram and both branch tags are fixed.  Nevertheless its evaluated
parent outcomes are

\[
 H(\mu^m)=\delta_0\quad\text{for every }m,
 \qquad
 H(\mu^\infty)=\delta_1.
\]

Their `l1` distance is two.  No subsequence of the finite executions converges
to the legal evaluated outcome at the limiting source.  Proposition 6 still
applies perfectly: each evaluation terminates after one transition.  What
fails is precisely limit commutation.

If evaluated ranked outcomes are part of the “complete trace,” this is a
counterexample to Theorem 9 as stated.  If they are not part of the trace,
then `RankStep` has not been given compositional edge semantics and cannot
support the claimed backward consumer.  Either interpretation requires a
repair.

A sufficient repair is to require that the fully evaluated ranked compiler
has a closed graph (or a total-variation modulus) into a specified actual
outcome space.  One can derive that structurally if:

* the root rank is fixed, hence gives a uniform finite expansion bound;
* terminal outcome relations are closed and actual;
* child adapters commute with the source limit;
* branch data have a closed/stabilizing rule; and
* every backward compiler is continuous, or itself carries a closed-limit
  executable adapter.

Alternatively, remove `RankStep` from Theorem 9 and first expand each supplied
ranked evaluation into a finite certified macro whose complete input-output
commutation theorem has already been proved.  Rank descent alone cannot play
the role of that theorem.

## 4. Missing execution data in Theorem 9

Theorem 1 of `meta/EXECUTABLE_COMPACT_STATE.md` starts with a common
restriction-compatible sequence `s_m` of actual executions of `P_m`.  Its
`s_m` includes initial laws, exogenous law inputs, and every varying finite
parameter.  Theorem 9 instead introduces only the diagrams `P_k`, then says
that inputs satisfy coordinate-coherence conditions and concludes that there
is “one subsequence of executions.”  No execution sequence has been
quantified.

This is not merely notation: the countable witness extraction requires, for
every occurrence already present in `P_k`, a tail sequence of legal witnesses
coming from actual executions of all later diagrams.  The exact theorem
surface should begin with such an `s_m` and require that restriction of the
`P_{m+1}` execution to `P_m` is the prescribed `P_m` execution, including all
edge labels and witnesses that are meant to persist.

The terms “complete trace,” “limiting execution,” and the extension relation
also need definitions for the enlarged grammar.  Once those are supplied,
the countable compact-witness diagonal is standard for `SelRoot`, `ArgOpt`,
exact/tolerance-coherent `LawMin`, and fixed `Decode` occurrences.  It does
not cure the ranked discontinuity above.

## 5. Does one coherent controller follow?

At the initial port, yes, but only from the elementary theorem's full
hypotheses.  Coordinate convergence plus eventual finite-tail tightness gives
one total-variation limit `mu^infinity`; the stopping-law-to-hazard compiler
makes it one behavioral profile.  Taking a subsequence to converge auxiliary
compact witnesses does not change that already unique initial limit.  This is
the genuine one-controller conclusion proved in
`meta/EXECUTABLE_COMPACT_STATE.md`.

What does not follow is that every new edge in the infinite union is a legal
edge of one limiting execution.  `SelRoot`, robust `ArgOpt`, repaired
`LawMin`, and repaired `Decode` can be added by a topological induction.  The
rank counterexample prevents adding arbitrary `RankStep` data in the same
way.  Thus the sentence “the root controller is the same for all `k`” is true
about the reconstructed root, but it does not establish the stronger
complete-trace conclusion of Theorem 9.

## 6. Consumers and scope

### Terminal Nash

Assuming a tight root sequence with

\[
 U(\mu^m)\to v,
 \qquad
 B_i(\mu^m)-U_i(\mu^m)\to0,
\]

the terminal-Nash argument is correct.  Total-variation convergence of the
root laws gives convergence of prescribed payoffs and complete behavioral
caps, and `B_i >= U_i` gives equality at the limit.  The checked theorem
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
then consumes that exact terminal Nash profile into a uniform-equilibrium
payoff.

This conclusion does not need any non-elementary edge.  It is the same
conditional consumer as Theorem 2 of `meta/EXECUTABLE_COMPACT_STATE.md`, and
the note supplies neither the tight root sequence nor vanishing debt from an
arbitrary reward table.  The checked equivalence
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in
the same Lean file confirms that arbitrary-game production of such profiles
is exactly conjecture-facing, not a routine consequence of a trace language.

### Renewable exit

Corollary 7 correctly rules out a recurrent component **after** every node has
been equipped with the rank-decreasing `step` datum in (28).  The advertised
exit and its backward transport are precisely fields of that datum.  No
particular regeneration relation is shown to admit the rank, actual child
adapter, terminal consumer, or backward compiler.  This is supplied-object
verification, not a renewable-rank producer.

### Relation to the maintained question

Theorem 8 does provide meaningful progress on
`questions/QUITTING_COMPOSITIONALLY_SUFFICIENT_STATE.md`.  Its reward-table
calculation is exact:

* for positive `z`, the unique exact root is `(0,0)`;
* at `z=0`, the maximal root is `(1,0)`;
* keeping the limiting selected root violates maximality; and
* reselecting the legal maximal root changes player 2's payoff and complete
  cap by exactly one.

Thus the bare maximal-root edge has a nonclosed graph and an order-one
recovery obstruction even for tight actual finite-support sources.  This is a
valid negative result of the kind explicitly requested.

The rest of the note is best classified as a conditional certificate schema.
It does not yet answer the positive architecture request because `RankStep`
does not commute and the grammar/execution objects are not defined.  It also
does not produce a terminal approximation, positive chronological return, or
ranked exit from arbitrary game data.  The final scope disclaimer correctly
admits the missing Fin4 adapters, but the opening “right completion,” Theorem
9, and the claim that the extended grammar has both consumers are stronger
than the proved mathematics.

## 7. Suggested revision gate

Before treating the positive grammar as answered:

1. Define nodes, typed ports, legal executions, complete traces, syntax
   height, restriction, and all constructor parameter/code types.
2. State Theorem 9 with one common sequence of full actual execution packets
   exactly as in the elementary tight-fusion theorem.
3. Add the missing `LawMin` tolerance quantifier and the full `Decode`
   continuity/provenance hypotheses.
4. Either remove `RankStep` from the diagonal theorem or prove closedness of
   its fully evaluated outcome compiler under explicit terminal and backward
   continuity hypotheses.
5. Label the two consumers as supplied-certificate consumers and retain
   Theorem 8 as the independently valid negative answer.

The concrete falsification test for any revision is the discontinuous
one-step backward compiler above.  A repaired ranked theorem must exclude it
by a stated hypothesis rather than by calling the backward function
“actual.”

## Sources inspected

Conference and project records:

* `questions/QUITTING_COMPOSITIONALLY_SUFFICIENT_STATE.md`;
* `meta/EXECUTABLE_ADAPTERS.md`;
* `meta/EXECUTABLE_COMPACT_STATE.md`;
* `docs/FRONTIER.md`; and
* `docs/TOOLKIT.md`.

Lean declarations checked for semantic scope:

* `quittingUniformEquilibriumPayoffConjecture` in
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean`;
* `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` and
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
* `quittingTerminalPayoff_update_stoppingLawMixture_eq`, which uses the
  pure-time stopping-law mixture interface, in
  `UniformEquilibrium/Quitting/Paths/StoppingLawMixture.lean`; and
* `VanishingDebtAtomChronologicalConsumer` and
  `PaidFirstDisagreementAdmissibleReturnConsumer` in
  `UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`.

No Lean theorem is claimed for the new grammar or for Theorem 9; this audit is
ordinary mathematics.
