# Diagonal audit of `GRAMMAR.md`

## Status and verdict

This review checks Sections 2 and 4: the `CW`/`RC`/`RD` grammar, compactness
of the assignment space, closedness of finite execution sets, simultaneous
finite-prefix realizability, and the claimed one-controller conclusion.

The closed-relation core is sound: a countable family of constraints on
compact carriers has a coherent global assignment when every complete edge
satisfaction relation is closed and every finite family is simultaneously
realizable.  This is exactly the scope of the checked dependent compact
finite-prefix theorem.

Section 4 is nevertheless false for the grammar as stated.  `RD` requires a
legal transition and a strict natural-rank decrease, but does not require the
legal-transition relation, terminal consumer, or any backward compiler to be
closed.  Rank discreteness closes only the inequality on ranks.  It does not
close the law-valued transition.  A one-step positive-reach suffix gives an
exact counterexample below: every finite diagram is simultaneously
executable from one fixed initial port, all law boxes are compact, all `CW`
relations are closed, and the only ranked step is `1 -> 0`; nonetheless no
global execution exists.

There are three further theorem-surface gaps.

1. A "closed TV-tight box" must mean a closed **uniformly** late-finite-tail
   tight family.  Individual tightness is automatic for each countable law
   and does not make a family TV-compact.
2. The provenance DAGs, dates, ranks, branch tags, and program parameters are
   part of the declared state but are absent from the definition of
   `Omega`.  Unbounded discrete factors such as `Nat` are not compact.  They
   must be fixed by the diagram, restricted to finite sets, or supplied with
   separate compact carriers.
3. A coherent assignment containing a TV-Cauchy sequence of controller ports
   yields an actual limit law, but it does not by itself show that every
   requested trace is executable from that limit.  That stronger conclusion
   needs the restriction-compatible execution and fixed-trace convergence
   hypotheses of the tight-fusion theorem.

Accordingly, `CW` can be retained, `RC` can be retained after its elementary
program and provenance relation are made explicitly continuous/closed, and
`RD` can be used for pointwise well-founded recursion.  `RD` cannot enter the
coherent-diagonal theorem until the entire solved ranked transition has its
own closed-limit adapter.

The conclusions here are ordinary mathematics, not new Lean-checked
declarations.

## Claim audited

The intended theorem is:

> Increasing finite diagrams made from `CW`, `RC`, and `RD` edges, each
> simultaneously executable from one fixed actual initial port, admit one
> coherent infinite execution; a summably Cauchy sequence of controller ports
> then fuses to one actual controller from which all persistent operations and
> unrestricted caps are recovered.

I separated this into five questions:

1. Are the carriers in `Omega` compact?
2. Is the full satisfaction relation of each constructor closed?
3. Does finite simultaneous realizability give the finite-intersection
   property required by compactness?
4. Does strict natural rank repair a nonclosed transition?
5. Does the resulting assignment produce one controller that executes every
   fixed requested trace?

## 1. What survives in the three constructors

### `CW`

The abstract `CW` constructor is sound provided its words are read literally:
the **complete witnessed relation**

$$
  G_a\subseteq X\times W\times Y
$$

is closed, and `X`, `W`, and `Y` are compact Hausdorff carriers of all data
that may vary.  Pullback along coordinate projections then gives a closed
constraint in the global product.

The fixed-competitor argmax example is correct.  Compactness of `W` supplies
existence of a maximizer, while continuity of `f` makes its optimality
relation closed.  For a moving feasible set, storing the selected point is
not enough: either the optimality relation itself must be proved closed, or
one needs outer graph closure plus the inner comparison-lift property already
identified in `EXECUTABLE_ADAPTERS.md`.

The phrase "selected cap root, provided the selected root itself is stored"
should therefore remain subordinate to the requirement that the witnessed
root relation has been proved closed.  Storage alone does not close a
discontinuous selection rule.

### `RC`

There is a correct closed-relation version of `RC`.  Fix one elementary
program `P`, including all discrete labels and suffix dates, and require:

* its input domain, including every reach inequality `q >= rho`, is closed;
* `P` is continuous on that domain in the declared topology;
* every varying law input and continuous parameter lies in a compact carrier;
* the full provenance/ancestry relation is closed; and
* the semantic modulus tends to zero with the reconstruction error at the
  fixed reach margin.

Then

$$
  P(x)=\widehat y,
  \qquad d_{\rm TV}(\widehat y,y)\le\varepsilon
$$

is a closed constraint.  Positive-reach suffixing has the needed continuity
on `q >= rho`, and finite prefixing, concatenation, and explicit replacement
are continuous elementary operations.

The present text does not quite state this typed version.  In particular:

* "actual finite elementary program" does not by itself assert continuity;
* `d_TV` compares only law coordinates, while an attached state also contains
  provenance and witness fields;
* "obtained ... without replacement" is a syntactic description, not yet a
  closed mathematical relation; and
* approximate maximizer/minimizer status is not implied by law proximity
  alone and must be included in the certificate relation or semantic modulus.

If one logical `RC` edge is tightened through errors `epsilon_n -> 0`, the
same program and target coordinates must persist and all earlier error
constraints must remain present.  Otherwise the notation
`D_n subset D_(n+1)` does not imply nested satisfaction sets.  For exact
semantic recovery one also needs

$$
  \omega_{a,k}(\varepsilon_n,\rho)\longrightarrow0.
$$

There is no need for one global reach constant across every edge in an
infinite diagram.  For finite-trace reconstruction it is enough that each
fixed persistent suffix edge `e` has its own floor `rho_e > 0`, uniform over
the approximations of that edge.  A universal infimum over all edge
occurrences may be zero without harming any fixed finite trace.

### `RD`

Strict natural-rank descent proves only that a supplied ranked branch has
finite length.  It does not prove any topological statement about the chosen
child.

Even as a pointwise outcome producer, the displayed `RD` data are incomplete.
A terminal consumer produces an outcome only at a terminal state.  To produce
an outcome at the original state after following a smaller child, the edge
also needs a backward compiler from the child's outcome to the parent's
outcome.  This is the datum that the corrected ranked-producer interface in
`EXECUTABLE_ADAPTERS.md` makes explicit.

For a compact diagonal, still more is required: the entire legal-transition
certificate, selected child, terminal outcome relation, branch data, and
backward compiler must form a closed relation or continuous map on compact
typed carriers.  Rank descent cannot substitute for this closed-limit
passport.

## 2. Exact counterexample to Section 4

Take one player and the compact TV family

$$
  \mu_t=(1-t)\delta_0+t\delta_\infty,
  \qquad 0\le t\le1.
$$

It is isometric to `[0,1]` in total variation.  At depth one,

$$
  q_1(\mu_t)=t,
  \qquad S_1\mu_t=\delta_\infty\quad(t>0).
$$

Use one arbitrary fixed actual initial port `sigma^0`.  A closed `CW` edge
selects an auxiliary source `mu_t` from the displayed compact family.  Add
one `RD` edge

$$
  (\mu_t,1)\longrightarrow(\delta_\infty,0)
$$

whose legal-transition certificate is literal positive-reach suffixing at
depth one.  Thus the ranked edge is legal exactly when `t > 0`.  Give the
rank-zero target any fixed named terminal consumer.

For every positive integer `j`, add a `CW` constraint

$$
  t\le\frac1j.
$$

This is a closed constraint; if an output port is required syntactically, it
can point to a fixed dummy law.  Let `D_n` contain the selector, the single
ranked edge, and the first `n` such constraints.

Every `D_n` has a simultaneous actual execution from exactly the same initial
port: choose `t=1/n` (with the harmless reindexing `1/(n+1)` if diagrams start
at zero).  All port boxes are compact and uniformly tight.  Every `CW` graph
is closed.  There are no `RC` edges.  The only ranked transition strictly
decreases from one to zero and has a terminal consumer.

But a global execution would require

$$
  t>0
  \quad\text{and}\quad
  t\le\frac1j\quad\text{for every }j,
$$

which is impossible.  Equivalently, the finite satisfaction set in the
`t`-coordinate is

$$
  (0,1/n],
$$

which is not closed.  Its only limiting candidate is `t=0`, where the ranked
suffix transition is illegal.

This counterexample satisfies all five displayed assumptions of Section 4.
It shows exactly why the sentence

> rank inequalities are closed because `Nat` is discrete

does not prove that `F_n` is closed: the ranked inequality is closed, but the
law-valued legality relation of `RD` is not.  It also shows that putting an
external rank budget around a vanishing-reach operation does not make that
operation commute with a compact outer limit.

## 3. Compactness of `Omega`

The law-level compactness argument is valid under a precise uniform
tightness definition.  For each player coordinate, require a tail envelope
`T_p(N) -> 0` such that

$$
  \sum_{m>N}\mu(m)\le T_p(N)
$$

for every law in `K_p`, with the Never atom retained separately.  A closed
family satisfying this bound is compact in `ell^1`, hence in total variation.
A finite product over players remains compact.

The current attached state is larger than its law coordinate.  It contains a
finite provenance DAG, a tuple including dates and branch tags, and sometimes
a natural rank.  Section 4 instead writes `Omega` as the product of only the
law boxes "together with the finite compact witness factors."  Three repairs
are needed.

1. There are generally countably many witness occurrences in `D_infty`, not
   one finite collection.  Their full product is compact when **each** factor
   is compact; countability is harmless.
2. A variable date or rank in discrete `Nat` is not compact.  Such labels must
   be fixed by the edge occurrence, range over a fixed finite set, or be
   excluded from the compact coordinate space.
3. Variable finite DAG shapes have no declared topology or compactness.  The
   clean formulation fixes the finite provenance shape syntactically at each
   occurrence and topologizes only its compact law/real parameters.  If shapes
   vary, a compact carrier and a closed evaluation relation must be supplied.

Thus "the tight boxes make `Omega` compact" is correct only after every
non-law coordinate has also been accounted for.

## 4. Simultaneous realizability is the right compatibility hypothesis

Assumption 5 is the correct strength of nonemptiness.  Separate existence of
each edge, port, or depth would not suffice.  Once all full edge relations are
closed in a common compact product and the diagrams literally increase, a
simultaneous execution of every finite diagram makes the closed satisfaction
sets nonempty and nested.  The finite-intersection argument then gives one
global assignment.

This agrees exactly with
`exists_dependentInfiniteChain_of_finitePrefixes` in
`MathUE/Topology/CompactDependentFinitePrefixRelation.lean`.  Its hypothesis
`hgraph` requires the **whole adjacent relation graph** to be closed; it does
not accept a nonclosed relation merely because an auxiliary rank inequality
is closed.  Likewise,
`exists_infiniteChain_of_budgetedFinitePrefixes` in
`MathUE/Topology/CompactBudgetedPrefixRelation.lean` retains all elapsed
budget constraints only because the relation graph and continuous weight
constraints are closed.

So the reference to the dependent inverse-limit theorem is appropriate, but
that checked theorem diagnoses rather than repairs the missing `RD`
closedness.

## 5. What the compact intersection does and does not give

After the preceding repairs, an element of the compact intersection is one
coherent assignment of values to every port and witness occurrence.  This is
a useful conclusion.  It is not automatically one law that serves as every
controller port.

There is also an ambiguity in the statement.  If `sigma^0` is literally the
common initial controller of every finite execution, then the controller was
already fixed in assumption 5.  If instead the controllers are the varying
ports `sigma_n`, the theorem must explain how each requested depth is attached
to all sufficiently late `sigma_m` and how those executions restrict to one
another.

The summable estimates

$$
  d_{\rm TV}(\sigma_{n+1},\sigma_n)\le\beta_n,
  \qquad \sum_n\beta_n<\infty
$$

do correctly imply that `sigma_n` converges in TV to an actual stopping-law
profile `sigma*`.  Every probability law on the countable stopping space has
a canonical behavioral realization, as checked by
`quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy` in
`UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`.

But the displayed estimates alone do not imply that a trace attached to
`sigma_n` is a trace from `sigma*`.  The required extra statement is:

> for every fixed requested program `P_k`, all sufficiently late executions
> contain the same restriction-labeled copy of `P_k`, their input and
> exogenous law coordinates converge to those of `sigma*`, every varying
> finite-dimensional parameter converges, every suffix in `P_k` has its own
> persistent positive reach floor, and every non-elementary relation in the
> trace is closed.

Under those hypotheses, topological induction through `P_k` proves trace
convergence and literal execution from `sigma*`.  This is the content of the
ordinary-mathematical tight-fusion theorem in
`meta/EXECUTABLE_COMPACT_STATE.md`; it is not one of Section 4's five stated
assumptions.

For finite quitting games, unrestricted-cap convergence under TV convergence
is mathematically sound: pure-time extremality identifies the full behavioral
cap, and the bounded payoff functions are uniformly Lipschitz in the
opponents' law profile.  The relevant checked semantic declarations are
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` and
`quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile` in
`UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`.
Still, cap convergence is a quitting-game semantic lemma, not a formal
consequence of the abstract `CW`/`RC`/`RD` grammar.  It must be assumed or
invoked at the one-controller corollary.

## 6. Corrected theorem surface

A valid compact theorem can be stated as follows.

> Let the set of port and witness occurrences be countable.  Give every
> occurrence a nonempty compact Hausdorff carrier.  For every edge occurrence
> `e`, let `C_e` be the complete satisfaction relation on its incident ports
> and witnesses, and assume `C_e` is closed.  Fix required initial coordinates.
> If every finite family of edge constraints has a simultaneous assignment
> with those same initial coordinates, then one global assignment satisfies
> every edge.

Constructor-specific consequences are then:

* `CW` supplies `C_e` directly;
* `RC` supplies `C_e` from a fixed continuous elementary program, a fixed
  positive reach domain, closed metric/error constraints, and closed
  provenance; and
* `RD` is admitted only if its **entire** legal solved-transition relation has
  independently been proved closed.  Strict rank remains useful for
  pointwise termination, but is not part of the closedness proof.

A separate one-controller corollary may then invoke the full tight-fusion
hypotheses for a common restriction-compatible sequence of executions.  An
alternative clean repair is to omit `RD` from the diagonal theorem entirely,
use rank induction only at fixed actual states, and compile its solved output
into `CW` or `RC` before taking any outer limit.

## Sources inspected

I used the stopping-law and inverse-limit routes named in `docs/TOOLKIT.md`
and inspected the following declarations and source documents:

* `exists_dependentInfiniteChain_of_finitePrefixes` in
  `MathUE/Topology/CompactDependentFinitePrefixRelation.lean`;
* `exists_infiniteChain_of_budgetedFinitePrefixes` in
  `MathUE/Topology/CompactBudgetedPrefixRelation.lean`;
* `quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy` in
  `UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`;
* `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
* `quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile` and
  `quittingTerminalSemanticPair_eq_of_opponentTight_lawLimit` in
  `UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`;
* `quittingTerminalPayoff_update_sub_le_two_mul_bound_mul_stoppingLawTV` in
  `UniformEquilibrium/Quitting/Paths/StoppingLawExposure.lean`;
* the tight-fusion hypotheses and Theorem 1 in
  `meta/EXECUTABLE_COMPACT_STATE.md`; and
* the repaired separation between pointwise rank recursion and closed-limit
  adapters in `meta/EXECUTABLE_ADAPTERS.md`.

## Requested next check

After repair, the decisive application question is:

> Does any intended renewable Fin4 transition have a compact witnessed
> solved-transition graph that remains closed when its source laws converge,
> including the terminal consumer and backward compiler?

Without such an application theorem, ranked descent remains a supplied
pointwise producer and cannot be used inside the coherent one-controller
diagonal.
