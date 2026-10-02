# Review of `meta/CONSUME.md`

## Claim reviewed

The note proposes three things:

1. a no-go for treating every legal source manipulation as one untyped
   recurrent relation;
2. a generic occupation-measure/duality consumer for a compact serial system
   of actual chronological edges; and
3. a remaining “neutral-core theorem” intended to isolate the Fin4 gap.

I checked these claims against the information-state results in
`meta/MARKOV_COMPLETE.md`, the topology boundary summarized in
`meta/SUFFICIENT_STATE.md`, the exact tester representation in
`meta/CONTROLLER_VS_TESTER.md`, and the checked payoff-near-return interface
`QuittingPositiveAdmissiblePayoffNearReturnFamily` in
`UniformEquilibrium/Quitting/Projective/PunishmentFloorNearReturn.lean`.

## Verdict

The note contains a genuine and useful generic consumer.  Its strongest
conjecture-facing form is not the displayed cumulative-charge theorem, but a
fixed-positive-edge recurrence theorem that maps directly into the checked
payoff-near-return consumer.

The no-go for an untyped legal-operation relation is also valid, with one
important qualification about sure absorption and unilateral deviations.

The “neutral-core theorem” is presently an architectural schema, not a new
Fin4 reduction.  No concrete compact serial chronological edge system is
produced from the hard residual.  Without that producer, the neutral-core
statement merely gives a new name to the remaining conjecture-level
chronology problem.

## Valid contributions

### 1. The fifth alternative is circular unless independently certified

If every actual profile satisfies

\[
D(\sigma)\ge D_*>0,
\]

then, for four players,

\[
\max_i d_i(\sigma)\ge D_*/4.
\]

Thus returning the input table together with the assumed positive minimum is
not a new negative certificate.  Requiring a concrete table and an
independently checkable positive-gap certificate is the correct repair.

### 2. Full actual profiles give exact set-theoretic update information

The compact product

\[
\Sigma=([0,1]^4)^{\mathbb N}
\]

contains every actual behavioral profile and supports exact prefix, suffix,
and complete-strategy replacement operations.  Against fixed opponents, an
arbitrary behavioral strategy is exactly a probability law on pure finite
stopping dates plus Never.  Hence the pure-time menus determine the complete
unilateral cap.

This agrees with the sharper information classification in
`MARKOV_COMPLETE.md`: order-three labelled counterfactual laws are the first
replacement-closed level for four players, and are losslessly equivalent on
actual profiles to the four marginal stopping laws.

The wording “a compositionally complete compact source state” should be
restricted to the actual profile coordinate itself.  The ambient product
`X_raw` is compact, but it contains inconsistent annotation tuples.  The
subspace in which every annotation is required to equal the semantic datum of
the displayed profile need not be closed.  Thus the safe conclusion is:

> There is a compact actual carrier with exact legal operations, but the
> strategic observables needed by the proof can be discontinuous on it.

### 3. The cap-discontinuity example is correct

For the spectator-reward table, profiles with all players quitting at a date
tending to infinity converge coordinatewise to all-Continue, while every
finite profile has cap one and the limit profile has cap zero.  This is the
right simple witness that compact actual-profile topology and continuous
unrestricted caps cannot be had simultaneously when finite hazard
coordinates identify the actual profile.

The abstract trilemma should explicitly assume a compact Hausdorff topology
(or sequentially compact metric topology) and that the continuous finite
coordinates separate actual profiles.  Under those hypotheses the cluster
argument is sound.

### 4. Untyped recurrence is invalid

The cycle

\[
x\xrightarrow{\text{all-Continue prefix}}P_{\mathbf C}x
 \xrightarrow{\text{suffix}}x
\]

and the identity pairs in complete-strategy replacement show that recurrence
in a relation containing all legal manipulations has no constructive meaning.
The rational spectator table makes the failure concrete: a zero-charge legal
two-cycle can coexist with order-one exploitability at both displayed states.

This is a genuine no-go, not merely terminology.  Source construction,
selection, normalization, replacement, and compactification must be treated
as horizontal operations unless a separate commuting-seam theorem turns them
into an executable temporal transition.

### 5. Invariant occupation exists for a compact serial chronological system

Let `E` be a compact metric edge space with continuous source and target maps
into a compact metric state space `C`.  If every state has a successor in
`C`, empirical edge measures along one infinite path have an invariant weak
limit.  This theorem is correct and elementary.

The result is conditional in the application: exact actual chronological
edges are not automatically compact, and the current Fin4 reduction has not
yet produced such a serial edge system.

## The typed-edge consumer can be strengthened

The displayed positive-mean theorem concludes that return segments have
arbitrarily large *total* charge.  That is not, by itself, the interface used
by the checked consumer.  `QuittingPositiveAdmissiblePayoffNearReturnFamily`
requires one fixed positive **single-edge threshold** and, at every endpoint
tolerance, a path containing an edge above that threshold.

Fortunately invariant occupation gives exactly this stronger conclusion.

### Fixed-edge-threshold recurrence theorem

Let

\[
s,t:E\to C
\]

be a compact serial edge system, let `q : E -> [0,Q]` be measurable and
nonnegative, and let `pi` be invariant with

\[
\int q\,d\pi>0.
\]

Then there exist `delta > 0` and one `v` in a compact semantic observation
space `Z` such that, for every `epsilon > 0`, there is a finite legal path

\[
x_0\to x_1\to\cdots\to x_N
\]

whose observed endpoints are both within `epsilon` of `v` and for which

\[
q(e_k)\ge\delta
\]

for at least one edge of the path.

Indeed, choose `delta > 0` with

\[
\pi\{e:q(e)\ge\delta\}>0,
\]

pass to an ergodic component on which that edge set still has positive
measure, and choose `v` in the support of the stationary semantic law.
Typical trajectories visit every semantic neighborhood of `v` infinitely
often and also visit the high-edge set infinitely often.  A high-edge visit
can therefore be bracketed by two visits to the same prescribed semantic
neighborhood.

This avoids the unnecessary parameter `A` and matches the checked consumer
exactly.

### Exact decoding data required

To turn this abstract theorem into a quitting-game consumer, each atomic
typed edge `e : x -> y` should carry an exact decoder with:

1. a floor-admissible state `Phi(x)` for every object;
2. a `QuittingPunishmentFloorAdmissibleEdge` whose `current` is `Phi(x)` and
   whose `tail` is `Phi(y)`;
3. `q(e)` equal to that edge's literal absorption charge;
4. a semantic observation equal to the prescribed payoff coordinate of
   `Phi(x)`; and
5. if source provenance is needed upstream, a literal finite block realizing
   the same predecessor/continuation identity against actual profiles.

A sampled forward chronology `x_0 -> ... -> x_N` decodes to the admissible
charged path in reverse predecessor order, from `Phi(x_N)` to `Phi(x_0)`.
Endpoint payoff closeness is symmetric, and the high edge survives the
reversal.  The fixed-edge-threshold theorem therefore directly constructs a
`QuittingPositiveAdmissiblePayoffNearReturnFamily`, after which the checked
uniform-payoff theorem applies.

For macro-edges, “additive admissible charge” is not enough.  A macro-edge
must either expose one constituent admissible edge with charge at least its
declared threshold, or the downstream consumer must be changed to consume
total charge.  Arbitrarily large sums of arbitrarily small edge charges do
not satisfy the existing high-edge interface.

## Qualification to the sure-absorption rule

The statement

> if the joint Continue probability of a block is zero, its chronological
> target must be a cemetery state

is too broad for unrestricted unilateral deviations.  If one player is the
only sure quitter, that player can deviate to Continue and expose the nominal
off-path suffix; its cap can therefore depend on that suffix.

The correct screening condition is player-deleted as well as prescribed:

\[
c(B)=0
\quad\text{and}\quad
H_i(B)=0\quad\text{for every player }i,
\]

where `H_i(B)` is survival of all opponents of `i` through the block.  Under
this stronger condition neither prescribed play nor any unilateral deviation
can reach the continuation, so a semantic cemetery target is sound.

The pure nonsingleton forced-pair row satisfies this stronger condition: after
any one player changes strategy, another designated quitter remains.  Hence
the note's conclusion about forced-pair label cycles remains valid even though
the general rule needs correction.

## Duality

The unconstrained duality

\[
\max_{\pi:\,s_\#\pi=t_\#\pi}\int q\,d\pi
=
\inf_f\max_e\bigl(q(e)+f(t(e))-f(s(e))\bigr)
\]

is the standard compact continuous linear-programming dual and is plausible
under the stated compactness and continuity assumptions.

The constrained version should distinguish two cases:

* when invariant measures with zero mean displacement exist, state the
  Lagrange duality over that nonempty compact feasible set;
* when none exist, separately state a strict separation theorem, preferably
  with an arbitrarily slightly weakened positive margin rather than claiming
  attainment of an optimal continuous potential.

Also retain the note's important warning: a displacement of the form
`z(target)-z(source)` automatically has zero invariant mean and cannot impose
an additional constraint.

## The neutral-core claim

There is a precise abstract statement available:

> For a **supplied** compact serial typed chronological system, if no invariant
> occupation has positive decoded edge charge, then every invariant
> occupation is supported on zero-charge edges; if a finite rank is
> nonincreasing, it is also supported on rank-flat edges.

This follows immediately from nonnegativity and invariance.  It is a useful
normal form.

The stronger claim in the note—that this neutral core is “precisely the
present four-player gap”—has not been established.  The missing producer is:

\[
\text{Fin4 positive-minimum hard residual}
\Longrightarrow
\begin{array}{c}
\text{terminal output, or renewable exit, or a compact serial}\\
\text{source-matched typed chronological system with exact decoding.}
\end{array}
\]

No such system, its serial dispatch, or its compactness is constructed in the
note.  Moreover the proposed neutral-core alternatives are not specified from
fixed data `C,E,q,rho,T`; for arbitrary choices, identity zero-charge edges
would manufacture a neutral core in every game.  In that form the theorem is
equivalent in difficulty to the original conjecture and is a relabeling, not
a reduction.

The line “all positive-charge and strict-exit components are consumed” should
also be weakened.  A positive-charge edge or an available rank-decreasing
exit does not suffice: an invariant occupation may avoid it.  What is proved
is that an invariant measure with positive mean charge is consumed, and that
an invariant measure gives zero mass to every strict rank decrease when rank
is nonincreasing.

## Recommended issue-based `meta/` organization

Keep `SUFFICIENT_STATE.md` as a short index and synthesis document.  Split the
substantive material by mathematical issue:

1. `REPLACEMENT_INFORMATION.md` — the content now in `MARKOV_COMPLETE.md`:
   exact counterfactual order and marginal-law compression.
2. `SUFFIX_INFORMATION.md` — the current suffix-information obstruction.
3. `STATE_TOPOLOGIES.md` — compactness, stability, and approximation regimes.
4. `TESTER_LEDGER_AND_DUALITY.md` — the exact finite-dimensional tester ledger,
   Never transversality, and controller/tester value theorem.
5. `CHRONOLOGICAL_EDGE_CONSUMER.md` — only the generic typed-edge occupation,
   fixed-threshold recurrence, rank, and Lyapunov results.
6. `FIN4_NEUTRAL_CORE_PROBLEM.md` — the exact missing producer from the Fin4
   hard residual and the data a neutral component would have to retain.
7. `NEGATIVE_CERTIFICATES.md` — only if the invariant-barrier and explicit
   positive-gap route grows enough to merit separation from the tester file.

`CONSUME.md` should not remain as one long file mixing a counterexample to an
old specification, generic occupation theory, current Fin4 claims, and
organizational conclusions.  The clean boundary is: the typed-edge consumer
is a theorem; producing the typed system and eliminating its neutral
invariant supports are open issues.

## Final assessment

There is export-quality ordinary mathematics after three corrections:

1. restrict the compact state claim to the actual profile carrier rather than
   the possibly inconsistent annotated product;
2. replace joint sure absorption by all-deleted-player screening where a
   cemetery semantics is claimed; and
3. state positive occupation in the fixed-single-edge-threshold form and give
   the exact decoder into the checked admissible relation.

The neutral-core normal form is useful for organizing the frontier, but it is
not independently conjecture-reducing until the Fin4 hard residual is proved
to generate the required compact serial typed chronological system.
