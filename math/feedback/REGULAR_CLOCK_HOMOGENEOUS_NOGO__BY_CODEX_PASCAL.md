# Second falsification of the fixed-period homogeneous no-go

Reviewer: `CODEX_PASCAL`

Reviewed note:
[`../notes/CODEX_SYNTHESIS__FIN4_MONODROMY_BLOCKER_SEPARATION_AND_REGULAR_CLOCK_NOGO.md`](../notes/CODEX_SYNTHESIS__FIN4_MONODROMY_BLOCKER_SEPARATION_AND_REGULAR_CLOCK_NOGO.md)

First review incorporated:
[`CODEX_SYNTHESIS__FIN4_MONODROMY_BLOCKER_SEPARATION_AND_REGULAR_CLOCK_NOGO__BY_CODEX_MAXWELL.md`](CODEX_SYNTHESIS__FIN4_MONODROMY_BLOCKER_SEPARATION_AND_REGULAR_CLOCK_NOGO__BY_CODEX_MAXWELL.md)

## Verdict

**MATHEMATICALLY APPROVE; DO NOT EXPORT STANDALONE.**  The rate-free fixed-period
theorem and the corrected zero-order classification survive a second
independent falsification attempt.  The conclusion really uses terminal
exploitability against unrestricted behavioral deviations: the global
`Never` deviation is what replaces the little-`o(total hazard)` endpoint
hypothesis in the already checked returned-block tangent theorem.

The mathematically valid content is:

1. a fixed-period word converging rootwise to all Continue, with terminal
   exploitability tending to zero, gives either an exact all-Never profile or
   a homogeneous simplex-LCP witness; and
2. for an arbitrary fixed-period limit, two limiting active players give an
   exact terminal Nash profile, while one limiting active player is the only
   singular arm and its limiting debt is exactly the negative part of that
   player's own singleton reward.

As a classification of a *supplied terminal-approximating family*, this says
that the only singular fixed-period limit is the one-active,
negative-singleton exceptional-owner arm.  It does **not**, however, pass the
conference export gate.  The hypothesis `e_n -> 0` is already the established
terminal semantic endpoint: by
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`,
the supplied family itself already gives a uniform-equilibrium payoff.  In a
Fin4 hard residual its existence also contradicts the retained terminal gap
directly, without using the homogeneous classification.

Consequently the result does not produce the missing `COMP.md` clocks from
the endpoint monodromy, nor weaken the input required by the reviewed
periodic two-clock consumer.  It is a correct downstream diagnostic of a
source object whose production is already conjecture-closing.  Under the
literal language of `exports/README.md`, it is a supplied-certificate theorem
whose source hypothesis remains open, not a strict narrowing of the producer
obligation.  It belongs in `Research` or `revisit/` unless it is strengthened
to start from pre-equilibrium monodromy/blocker data.

The blocker/support-entry example in the reviewed note is a valid boundary
test but is not part of this export verdict.  It does not instantiate every
field of the Fin4 hard residual.

## Exact theorem checked

Let `I` be a nonempty finite player set and let `K >= 1` be fixed.  For every
`n`, let

\[
 x^n_k=(q^n_{ki})_{i\in I},\qquad k=0,\ldots,K-1,
\]

be product roots, and let `sigma_n` be the behavioral profile which repeats
this word forever from one fixed initial phase.  Let

\[
 e_n=\max_i\left(B_i(\sigma_n)-U_i(\sigma_n)\right)
\]

where `B_i` is the supremum over all unilateral behavioral strategies,
including every deterministic stopping date and `Never`.  Assume `e_n -> 0`.

After taking a subsequence so that every root coordinate converges, define

\[
 Z=\{i:\exists k,\ \lim_n q^n_{ki}>0\}.
\]

Then:

* if `Z` is empty, either all-Never is an exact terminal Nash profile or the
  normalized singleton matrix has a homogeneous simplex-LCP solution;
* if `|Z| >= 2`, the limiting periodic root word is an exact terminal Nash
  profile against every behavioral deviation; and
* if `Z={i}`, every limiting debt except possibly that of `i` is zero, and

  \[
  d_i=\bigl(-r_i(\{i\})\bigr)_+.
  \]

In particular, the last limiting profile is exact if and only if
`r_i({i}) >= 0`.

For the first arm, the sharper positive-absorption statement is useful.  If
every root tends to all Continue and the period has positive absorption for
all sufficiently large `n`, then the homogeneous conclusion holds.  No rate
assumption comparing `e_n` with the total hazard is needed.

## Independent proof of the vanishing-root arm

Put

\[
 h_n=\sum_{k<K}\sum_{i\in I}q^n_{ki},\qquad
 a_i^n=\sum_{k<K}q^n_{ki}.
\]

If all roots tend to Continue then `h_n -> 0`.  Pass to a subsequence on
which either the period has zero absorption for every `n`, or positive
absorption for every `n`.

In the zero case every root coordinate is zero, so every `sigma_n` is the
same all-Never profile.  Since its fixed exploitability is the limit zero,
all-Never is exact.

In the positive case `h_n>0`.  Pass to a further subsequence with

\[
 q_i=\lim_n\frac{a_i^n}{h_n}.
\]

Then `q` is a probability vector.  The following elementary estimates make
the phase and collision issues explicit.  If `H_n` is the probability of
absorption during one period, then

\[
 h_n-\frac{h_n^2}{2}\le H_n\le h_n.
\tag{1}
\]

This follows by expanding the product of all Continue probabilities, or by
the first two Bonferroni bounds.  If `u_{n,j}` is the probability that `j` is
the unique quitter during one period, including survival through the earlier
phases, then

\[
 |u_{n,j}-a_j^n|\le h_n^2.
\tag{2}
\]

The probability of a nonsingleton terminal coalition during one period is
at most `h_n^2/2`.  Repeating the same period geometrically divides every
one-period terminal mass by `H_n`.  Equations (1)--(2) therefore show that
the eventual terminal law converges to the singleton law `q`; accumulated
collisions have total probability `O(h_n)`, not order one.  The fixed
starting phase changes (2) only by its preceding survival factor, which is
`1+O(h_n)`.

Consequently the prescribed payoffs converge to

\[
 v_i=\sum_j q_jr_i(\{j\}).
\tag{3}
\]

Quitting at the current date is one legal behavioral deviation.  Its payoff
is `r_i({i})+O(h_n)`, because an opponent joins the current root with
probability at most `h_n`.  Since its gain is at most `e_n`, passage to the
limit gives

\[
 v_i\ge r_i(\{i\}),
 \qquad (Mq)_i\ge0,
\tag{4}
\]

where `M_ij=r_i({j})-r_i({i})`.

Now fix `i` with `0<q_i<1` and replace that player's complete strategy by
`Never`.  The opponents' total period hazard is asymptotic to
`(1-q_i)h_n`; the same estimates (1)--(2), applied after deleting `i`, show
that this deviation's payoff converges to

\[
 L_i=\frac{\sum_{j\ne i}q_jr_i(\{j\})}{1-q_i}.
\tag{5}
\]

The global terminal-debt hypothesis gives `v_i >= L_i`.  But (3) is the
convex decomposition

\[
 v_i=q_i r_i(\{i\})+(1-q_i)L_i.
\]

Together with (4), this forces both endpoints to equal `v_i`; hence
`(Mq)_i=0`.  If `q_i=1`, complementarity follows directly from the zero
diagonal: `(Mq)_i=M_ii=0`.  If `q_i=0`, it is vacuous.  Thus

\[
 Mq\ge0,\qquad q_i(Mq)_i=0
\]

for every `i`, exactly `HasHomogeneousSimplexSolution`.

Notice that this proof never divides `e_n` by `h_n`.  A sequence with, for
example, `e_n=sqrt(h_n)` is still covered.  This is the substantive
difference from a local endpoint-regret tangent argument.

## Independent proof of the positive zero-order split

Assume first that `|Z| >= 2`.  For every player `i`, some other member of `Z`
has positive Quit probability in at least one limiting phase.  Hence the
opponents of `i` absorb within one period with probability bounded below by a
positive constant, uniformly for all large `n`.

Payoffs of pure stopping dates more than `m` periods away, and the `Never`
payoff, have a tail bounded uniformly by a reward bound times `(1-delta)^m`.
For the finitely many dates before that cutoff, payoff is continuous in the
finitely many root coordinates.  Pure stopping times plus `Never` already
exhaust the unrestricted behavioral cap in a quitting game.  Therefore both
the prescribed payoff and every player's unrestricted cap are continuous at
the limiting word.  Since `e_n -> 0`, every limiting debt is zero.  This proves
exact terminal Nash against the full behavioral strategy class, not only
against periodic or one-stage deviations.

If `Z={i}`, the same argument applies to every `j != i`, since `i` supplies a
uniformly positive opponent clock.  Thus all those debts vanish.  In the
limiting word, all opponents of `i` play Never and `i` eventually Quits almost
surely.  Its prescribed payoff is `r_i({i})`; every finite pure stopping date
has that same payoff, while `Never` pays zero.  Its cap is therefore
`max(r_i({i}),0)`, proving the displayed debt formula.

## Falsification tests

### Phase bias

Putting one player's hazard in phase zero and another's unequal hazard in a
later phase changes the singleton owner numerator by an earlier-phase survival
factor.  That factor is `1+O(h_n)`, so after division by `H_n~h_n` the limit is
still the normalized aggregate hazard.  No phase-indexed bias survives.

### Collisions over a geometric lifetime

A same-stage collision has one-period probability `O(h_n^2)`.  The expected
number of survived periods is `O(1/h_n)`, so its eventual mass is `O(h_n)`.
This rules out the proposed failure in which negligible one-period collisions
accumulate to a positive limiting terminal law.

### `Never` and a point-mass owner

When `0<q_i<1`, the opponents' deleted period hazard is comparable to
`(1-q_i)h_n`, so the `Never` limit (5) is legitimate.  When `q_i=1` that
denominator vanishes, but no deleted-clock limit is needed: the diagonal
entry already gives complementarity.  This is the only boundary at which a
division by `1-q_i` would have been invalid.

### Genuine one-active singularity

The first review's two-player table is a valid falsifier of any stronger
positive-limit claim.  Let player zero receive `-1` at every nonempty
coalition and player one receive zero.  In the one-period root, let player
zero Quit with probability `1/2` and player one with probability `1/n`.
Every approximating profile is exact: player zero always receives `-1`
because player one eventually absorbs if necessary, and player one is
indifferent.  The limiting word has only player zero active; that player can
switch to `Never` and improve from `-1` to zero.  Thus the sole-active,
negative-singleton branch cannot be deleted.

### Zero period absorption

For a product root word, zero period absorption means every Quit probability
in the word is literally zero.  Hence an infinite zero-absorption subsequence
is the fixed all-Never profile, and convergence of its exploitability forces
exactness.  There is no additional zero-hazard boundary.

## Source and novelty audit

The narrow checked comparison is:

* `hasHomogeneousSimplexSolution_of_vanishing_returnedBlocks` in
  `UniformEquilibrium/Quitting/Stationary/ReturnedBlockTangentObstruction.lean`
  requires aggregate Bellman and probability-weighted endpoint regrets to be
  little-`o` of the block's total hazard.  It allows varying phase counts and
  is stronger in that direction, but it does not imply the theorem reviewed
  here when terminal exploitability merely tends to zero at an arbitrary
  rate.
* `sSup_range_quittingTerminalPayoff_update_cyclicBehaviorProfile` in
  `UniformEquilibrium/Quitting/Cycles/PeriodicRootResponseSystem.lean`
  identifies the exact finite periodic response cap with the supremum over
  all behavioral deviations.  It supplies the strategy-class adapter, not
  the asymptotic LCP classification.
* `QuittingTerminalExploitabilityWitness.exists_periodicCap_gain` in
  `UniformEquilibrium/Quitting/Cycles/TerminalExploitabilityPeriodicProfile.lean`
  exposes every periodic profile at a fixed terminal gap but does not classify
  a vanishing-exploitability sequence.
* `ResidualHardClass.no_homogeneous` in
  `UniformEquilibrium/Quitting/Classification/LCP/Gate.lean` concerns the
  recursive normal-core principal matrix.  For
  `FinFourQuantitativeFullSupportHardResidual`, the separate field
  `normalCore_eq_univ` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`
  identifies that matrix with the full Fin4 normalized singleton matrix, so
  the homogeneous output is genuinely excluded.

The ordinary returned-block precursor in
`notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md` likewise uses relative
Bellman/endpoint error.  The present use of the global `Never` deviation to
remove that relative-rate hypothesis is not a restatement of it.  No original
paper theorem was used in this review, and the narrow source search found no
checked rate-free fixed-period classification.

## Conjecture-facing status and export gate

The input is a literal fixed-period family of behavioral profiles whose full
terminal exploitability tends to zero.  Its outputs have named consumers:

* an exact terminal Nash profile is accepted by the terminal-Nash/uniform-
  payoff bridge;
* all-Never exactness is the same terminal endpoint;
* in the Fin4 full-normal-core hard residual, a homogeneous witness
  contradicts the checked `no_homogeneous` field; and
* the sole singular compactification branch is an actual one-active periodic
  limit with one named exceptional owner and negative own singleton reward.

But the source family has already crossed the semantic waist.  It supplies
terminal approximate Nash profiles for every error, so it directly produces
a uniform-equilibrium payoff.  Under a terminal exploitability witness it is
impossible before any compactification analysis.  The new classification
therefore does not reduce the unresolved implication

\[
\text{literal endpoint monodromy/blocker data}
\Longrightarrow
\text{an executable terminal-approximating chronology}.
\]

In particular, saying that the all-Continue implementation is "unavailable"
inside a hypothetical counterexample reverses the proof logic.  If the hard
residual data produced such an implementation, its impossibility would be the
desired contradiction.  The present theorem does not show that the attempted
producer cannot be proved; it supplies another contradiction after that
producer has already reached the terminal endpoint.

I therefore do **not** judge Theorems A--B export-worthy as a standalone
packet under `exports/README.md`, despite their correctness and usefulness as
a Research theorem.  They could become part of an export if a new adapter
starts from the actual same-stage monodromy or strict-blocker data and reaches
one of their hypotheses by a genuinely weaker argument than the existing
periodic terminal consumer.  Any retained packet or Research file should
still:

1. states the exact terminal exploitability quantity and fixed initial phase;
2. includes the positive-period-absorption/all-Never fork;
3. retains the exact one-active debt formula and does not call every positive
   zero-order limit an equilibrium;
4. states the full-normal-core hypothesis when invoking hard-residual
   `no_homogeneous`;
5. distinguishes this rate-free global-deviation theorem from the checked
   relative-error returned-block theorem; and
6. claim only the compactification boundary, not production or consumption of the
   remaining negative-singleton exceptional owner.

Because exact unrestricted-behavior coverage is claimed, this review is the
second independent mathematical review and explicit falsification attempt.  I
found no unresolved mathematical objection, but the conjecture-facing export
objection remains.

## Lean handoff

A narrow formalization should use the existing cyclic profile and cap API,
not introduce a new strategy class:

* `quittingCyclicBehaviorProfile` and
  `quittingProfileLiveRoot_cyclicBehaviorProfile`;
* `sSup_range_quittingTerminalPayoff_update_cyclicBehaviorProfile` for exact
  behavioral caps;
* finite-product estimates for one-period absorption, singleton ownership,
  and collisions;
* `normalizedSoloMatrix` and `HasHomogeneousSimplexSolution`;
* `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  for the exact branches; and
* `normalCore_eq_univ` plus `ResidualHardClass.no_homogeneous` for the Fin4
  hard-residual corollary.

The most useful theorem shape is a three-arm compactification of a sequence of
fixed-period cyclic profiles: exact periodic limit, one-active negative-solo
exceptional owner, or homogeneous simplex witness (with exact all-Never as an
early solved case).  The theorem should derive, rather than assume, the
limiting owner distribution from the literal repeated product words.
