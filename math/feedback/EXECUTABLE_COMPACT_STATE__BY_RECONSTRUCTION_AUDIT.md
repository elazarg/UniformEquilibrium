# Reconstruction audit of `EXECUTABLE_COMPACT_STATE.md`

## Verdict

The tightness-to-actuality argument at the heart of Theorem 1 is sound.  For
one fixed family of stopping laws, coordinate convergence together with
eventual uniform tightness of the finite-date tails gives an actual law on
\(\mathbb N\sqcup\{\infty\}\), convergence in total variation, and hence
uniform convergence of all pure-time response values and the unrestricted
cap.  Fixed finite prefixing, fixed or total-variation-convergent complete
replacement, and positive-reach fixed-depth suffixing commute with this
limit.

The theorem as stated nevertheless has two substantive coherence gaps.  Its
hypotheses control named source ports, but not every exogenous law-valued
program parameter.  They also do not say enough to turn separately
reconstructed ports into the execution of one root source when a program may
contain named continuation, regeneration, or limit-witness edges.  The proof
establishes a coherent family of actual port laws for the elementary operation
grammar; it does not establish the claimed one-controller conclusion for the
larger program language currently declared in Section 2.

These gaps look repairable by strengthening the theorem's interface.  They
are not counterexamples to the intended elementary tight-fusion lemma, but
they block the current global theorem surface.

## Re-audit after revision

The revised note closes both substantive gaps identified below.

* An elementary program is now explicitly a finite rooted directed acyclic
  diagram.  Every derived port is obtained from earlier ports by one of the
  operations whose limit behavior is proved.  Non-elementary regeneration,
  rank, limit-witness and endogenous-selector edges are excluded unless they
  carry a separate closed-limit executable adapter.
* Coordinate coherence and eventual finite-tail tightness now apply to every
  initial port and every exogenous law-valued input, including replacement and
  continuation laws.  Thus the escaping replacement sequence
  \(\rho^m=\delta_m\) no longer satisfies the hypotheses.
* The conclusion now distinguishes one actual controller when there is one
  initial port from a coherent packet when there are several independent
  initial ports.
* The clock/tester obstruction has been narrowed to cylinder traces and the
  rooted elementary grammar, which is the scope supported by the argument.

With these changes, the mathematical repair is sufficient.  Reconstruct the
initial and exogenous inputs in total variation, then induct over a
topological ordering of each fixed finite diagram.  The elementary operations
commute at every edge, so every derived port is actual.  Compatibility of the
increasing rooted diagrams makes the resulting finite executions restrictions
of one limiting execution.  No all-depth uniform tightness is used.

I retain only two editorial/interface corrections:

1. In the proof of Theorem 1, “Fix a named port \(a\)” should read “Fix an
   initial port or exogenous law-valued input \(a\).”  Coordinate coherence
   and tightness are assumed only there; derived ports are obtained afterward
   by the topological induction.
2. If exogenous inputs or root parameters vary with \(m\), the notation
   \(\operatorname{Tr}_{P_k}(s_m)\) should regard \(s_m\) as the complete
   execution-input packet, not only the initial ports.  Alternatively write
   the trace as a function of the initial packet and the explicit program
   parameters separately.  Their limiting values are part of the limiting
   execution even though they are not additional controllers.

Neither point is a remaining mathematical objection.  Subject to these
clarifications, I now regard the elementary tight-fusion reconstruction,
operation commutation, one-controller conclusion, terminal-Nash consumer and
the narrowed clock/tester obstruction as correct ordinary mathematics.

## Claim audited

Theorem 1 claims that an increasing family of finite programs and actual
executions, with coordinate coherence, portwise tightness, positive reach
margins and literal operation coherence, determines one actual source packet
whose trace realizes every fixed program and to which every program operation
commutes.

I checked separately:

1. reconstruction of a probability law at each port;
2. total-variation convergence;
3. commutation of each displayed elementary operation;
4. compatibility across the increasing programs; and
5. whether these local facts imply one global actual source.

## 1. The portwise reconstruction is correct

Fix one eventual port \(a\) and player \(i\).  Write the coordinate limits as

\[
 \mu_i^a(n)=\lim_m\mu_i^{m,a}(n),\qquad
 \mu_i^a(\infty)=\lim_m\mu_i^{m,a}(\infty).
\]

For a tail cutoff supplied by tightness,

\[
 \sup_{m\ge m_0}\sum_{n>N}\mu_i^{m,a}(n)\le\varepsilon,
\]

the finite partial sum plus the Never atom has limiting mass at least
\(1-\varepsilon\).  Nonnegativity and finite partial sums give the reverse
mass bound, so the coordinate limits sum to one.  The limit has no late atom.

The same cutoff proves total-variation convergence.  On
\(\{0,\ldots,N,\infty\}\) there are finitely many convergent coordinates;
the source tails are uniformly small, and the limit tail is small by passage
through finite partial sums.  Hence

\[
 \lVert\mu_i^{m,a}-\mu_i^a\rVert_1\longrightarrow0.
\]

No cutoff uniform over future ports is needed.  Countably many independently
chosen cutoffs cause no diagonal problem because the conclusion is only for
each fixed finite program.

This part agrees with the checked stopping-law infrastructure, in particular
the pure-time mixture theorem
`quittingRootSequenceHazardTerminalValue_eq_expect_stoppingLaw`, exact
stopping-law reconstruction in
`quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile`, and the tight
semantic realization results in
`OpponentTightTerminalSemanticRealization.lean`.

## 2. The displayed elementary operations commute

For fixed finite operation data, the stated arguments are valid.

### Prefix and concatenation

For a fixed-length prefix whose root probabilities converge coordinatewise,
the finite stopping masses and survival multiplier converge.  The displayed
total-variation estimate proves commutation.  The length and every discrete
label must be eventually fixed; an unbounded or changing prefix length is not
a convergent parameter of this lemma.

### Complete replacement

Coordinate overwrite commutes provided the replacement law itself converges
in total variation to an actual law.  This qualification is essential and is
missing from the tight-fusion hypotheses as written; see the first
counterexample below.

### Positive-reach suffix

For a fixed depth and a lower bound on every conditioning mass, normalized
restriction is total-variation continuous.  Thus the suffix law is the
literal suffix of the reconstructed source.  The theorem does not cover a
zero-reach suffix, a depth tending to infinity, or a suffix label that changes
after it has entered the projective program.

### Semantic coordinates

Product total variation controls the terminal law and prescribed payoff.
Opponent total variation controls every deterministic stopping-time response
uniformly, so taking the supremum also controls the unrestricted cap.  The
Late boundary value causes no problem here: total-variation tightness has
already removed late finite escape, while the supremum over finite times may
still converge to the displayed Late value.

Thus the proof really does give convergence of the full semantic trace for a
fixed elementary program.

## 3. Missing tightness for law-valued parameters

The hypotheses impose coordinate convergence and tightness on each named
source port.  Section 2, however, also permits replacement laws, named
continuations and other law-valued inputs.  Literal operation coherence says
that such parameters may “converge with the corresponding explicit
operation-parameter error included in (41),” but it does not state that this
error tends to zero or that their finite tails are tight.

This distinction is mathematical, not terminological.  Keep every source
port fixed at an actual tight law, and let a program replace player \(i\) by

\[
 \rho_i^m=\delta_m.
\]

The replacement parameters converge coordinatewise in the split compact
clock to \(\delta_\omega\).  All source-port tightness hypotheses still hold.
The replaced node has no actual limiting law on
\(\mathbb N\sqcup\{\infty\}\).  Reconstructing the source ports therefore
does not reconstruct this legal program node.

If “included in (41)” was intended to require a total-variation error tending
to zero, then this example is excluded, but that requirement must be stated.
The clean repair is:

> Coordinate convergence and eventual finite-tail tightness apply to every
> exogenous law-valued input of the program, including replacement laws and
> independently named continuations.

Equivalently, require every such parameter to converge in total variation to
an actual law.  Derived laws need no separate tightness assumption once the
program is built from the elementary continuous operations.

## 4. Portwise actuality is not yet one-source actuality

The proof reconstructs a law separately for every named port and then says
that restriction coherence makes these laws one source packet.  This is
correct only after the program has been specified as a rooted operation
diagram.

For the elementary grammar, the needed statement is straightforward:

* designate the initial source ports;
* require every other port to be the result of one displayed elementary
  operation on earlier ports in every actual execution;
* require the discrete diagram and operation labels to be eventually fixed;
  and
* prove the limiting equality along a topological ordering of the finite
  diagram.

Then every derived limiting port is definitionally the operation applied to
the reconstructed predecessor, and a fixed \(P_k\) is one actual execution.
Nested program restriction makes these finite executions agree.

The present program language is broader.  Its labels may include a
“regeneration or limit witness,” arbitrary named source ports, reach proofs,
and roots selected by auxiliary equations.  None of the estimates in Theorem
1 proves that these relations are closed under the chosen convergence.
Actual witnesses at every finite stage do not suffice for a nonclosed
relation.  For example, a regeneration interface may require a strict
positive quantity; witnesses with values \(1/m\) can be legal at every stage
while their limit fails that requirement.  A natural-valued rank inequality,
source-faithful provenance assertion, or maximal-selector property likewise
needs its own stability theorem rather than merely convergence of the
underlying laws.

There are two honest theorem surfaces:

1. restrict Theorem 1 to the elementary rooted grammar of prefix,
   concatenation, total-variation-convergent replacement, and
   positive-reach fixed-depth suffix; or
2. let every non-elementary edge carry a separately proved closed-limit or
   executable reconstruction theorem as part of the tight-fusion passport.

Without one of these repairs, the conclusion “every program operation in
\(P_k\) is realized” is stronger than the proof.

There is also a naming issue with mathematical content.  If a program has
several independent initial source ports, the construction yields one
coherent **packet of actual profiles**, not one behavioral profile.  To obtain
one controller, there must be one designated root source and every other port
must be derived from it by the rooted diagram.

## 5. Projective coherence

The restriction map

\[
 \pi_{QP}:X_Q\longrightarrow X_P
\]

is valid when restriction of every actual legal \(Q\)-execution is a legal
\(P\)-execution.  Continuity then sends the closure into \(X_P\).  Surjectivity
is neither proved nor needed.

Projective coherence by itself does not imply actuality of an inverse-limit
point.  The clock/tester example correctly demonstrates this.  Theorem 1
instead obtains actuality from total-variation tightness and a common tail of
actual executions.  This is the correct logical direction.

For clarity, the theorem should index one common sequence of executions by
the largest program and take restrictions to every earlier program.  If
different subsequences are selected independently for different \(P_k\), the
one-source conclusion fails.  The present statement appears to intend one
common sequence \(s_m\), and under that reading there is no subsequence
coherence gap.

## 6. The clock/tester obstruction

The displayed two-player computation is correct:

* the clock's prescribed payoff is \(-1\);
* its cap is \(0\), attained by Never;
* the tester's cap is \(1/n\); and
* uniform finite stopping laws converge to a unit Late atom while the
  semantic pair converges to \((U,B)=((-1,0),(0,0))\).

No actual profile realizes that semantic pair.  Prescribed payoff \(-1\) for
the clock forces a finite singleton-clock outcome almost surely.  A
probability law on countably many finite dates has a positive atom, which the
tester can exploit by tying at that date.

The summable-budget argument is also correct and gives the fixed payoff error
\(1/2\).

What is not yet proved by the displayed computation is the literal statement
that **every finite program** in the broad language of Section 2 has a
compatible approximation.  The note proves compatibility for the root trace
and every finite family of clock-coordinate tests.  It can be extended by an
induction to any fixed program made from the elementary operations above,
provided its reach domains remain legal.  It does not automatically extend to
arbitrary regeneration, selected-root, or provenance requirements.  Theorem
4 should either make that elementary program class explicit or include the
induction.

The negative conclusion needed for the architecture is already obtained from
the smaller statement: a compact projective root state with complete payoff
and cap coordinates need not be actually realizable.  The broader
“every-program” wording is unnecessary.

## 7. Recommended corrected theorem

A defensible tight-fusion theorem would assume:

1. each \(P_k\) is a finite rooted directed acyclic diagram of elementary
   operations;
2. all initial source ports and every exogenous law-valued parameter have
   coordinate limits and eventual finite-tail tightness;
3. all root-word parameters converge in their fixed finite-dimensional
   cubes, and all discrete labels and depths are eventually fixed;
4. every suffix edge has an eventual positive reach margin for every player;
5. every non-elementary edge is excluded or carries a separate closed-limit
   executable adapter; and
6. the diagrams are literal restrictions of one increasing diagram and use
   one common tail of actual executions.

Then there is one actual limiting execution of every fixed \(P_k\), the
executions are compatible under restriction, and all terminal laws, payoffs,
obstacles and caps converge.  If there is one initial source, these executions
come from one actual behavioral controller.  If there are several independent
initial ports, the conclusion is instead one coherent packet of actual
controllers.

Under this corrected theorem, Theorem 2 is valid: vanishing debt and payoff
convergence pass to the actual limit, and the reverse cap inequality follows
because the prescribed strategy is an admissible replacement.

## Final assessment

The central reconstruction mechanism is genuine and formalizable.  It gives
exactly the useful positive statement suggested by the earlier compactness
no-go: programwise continuity plus sourcewise tightness can recover one actual
diagonal without an all-depth uniform modulus.

The present note should not yet be exported as a completed architecture.  It
must first close the law-parameter and rooted-diagram gaps, or narrow Theorem 1
to the elementary program class actually covered by its proof.  The negative
clock/tester boundary remains valid after that narrowing.

## Lean declarations inspected

* `quittingRootSequenceHazardTerminalValue_eq_expect_stoppingLaw` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`;
* `quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile` in
  `UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`;
* `quittingTerminalSemanticPair_compactStoppingLawProfile_tendsto` in the same
  file;
* `quittingTerminalSemanticPair_eq_of_opponentTight_lawLimit` in the same
  file; and
* `quittingTerminalPayoff_update_sub_le_two_mul_bound_mul_stoppingLawTV` in
  `UniformEquilibrium/Quitting/Paths/StoppingLawExposure.lean`.
