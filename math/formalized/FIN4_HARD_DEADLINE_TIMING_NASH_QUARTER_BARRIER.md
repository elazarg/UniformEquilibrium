# Normalized Fin4 hard-deadline timing-Nash quarter barrier

Authors: `CODEX_NOETHER` (base recursion and diffuse boundary), `CODEX_MINER`
(normalized Fin4 extraction and architecture theorem)

Independent reviews:

* [`CODEX_EULER`](../feedback/CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING__BY_CODEX_EULER.md);
* [`CODEX_RAMSEY`](../feedback/CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING__BY_CODEX_RAMSEY.md).

Both reviewers independently checked the full timing-game uniqueness proof,
dummy-player elimination, exact recursion and Never products, unrestricted
behavioral debt, and the vanishing `1/L` comparison.

## Exact statement

There is a normalized rational quitting-game reward table `r` on `Fin 4`
with the following properties.

For every integer `N>=1`, form the finite normal-form timing game in which
each player independently selects one planned stopping time from

\[
 \{0,1,\ldots,N-1,\mathsf{Never}\}.
\]

The earliest finite selected time determines the quitting coalition, and all
Never pays zero.  Then:

1. this finite timing game has a unique mixed Nash equilibrium;
2. its literal behavioral-hazard realization has unrestricted terminal
   exploitability

   \[
   D_N={2^{N-1}\over2^{N+1}-1}>{1\over4};             \tag{1}
   \]

3. `D_N` decreases to `1/4`.

Nevertheless, for every `L>=1` the same table has a literal finite-clock
behavioral profile `sigma^L` with the fixed prescribed payoff

\[
 (1,-1,0,0)
\]

and exact unrestricted terminal exploitability

\[
 \operatorname{Expl}_r(\sigma^L)={1\over L}.          \tag{2}
\]

Consequently the true executable terminal exploitability infimum is zero,
and `(1,-1,0,0)` is a uniform-equilibrium payoff.  The table is not a
counterexample to the quitting-game conjecture.

## Conjecture-facing change

This is an exact impossibility theorem for the proposed architecture

\[
 \text{increase a hard finite deadline}
 \;\longrightarrow\;
 \text{select an exact timing-game Nash}
 \;\longrightarrow\;
 \text{seek vanishing unrestricted debt}.
\]

At this table there is no equilibrium-selection freedom, and every deadline
retains debt greater than `1/4`.  Thus no theorem can make exact Nash
equilibria of growing hard-zero-tail timing games into a universally
vanishing terminal-approximation producer.

This also narrows
[`ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md`](../questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md):
the actual finite-clock centers in the escape-aware hierarchy cannot be
replaced by, or restricted to, exact Nash equilibria of the corresponding
hard-deadline timing games while preserving convergence to the true
exploitability infimum.  Equation (2) proves that arbitrary actual
finite-clock profiles remain expressive enough on the same table; exact
Nashification is the incompatible extra field.

The theorem does not rule out a soft terminal state, approximate timing
roots, off-path punishment, or a globally selected non-Nash finite-clock
profile.

## Definitions and reward table

Name the four players

\[
 I=\{k,j,d_1,d_2\}.
\]

For every nonempty quitting coalition `S`, let
`A=S intersection {k,j}`.  Define the two active payoff coordinates by

\[
\begin{array}{c|rrrr}
A & \varnothing & \{k\} & \{j\} & \{k,j\}\\ \hline
r_k(S)&0&1/2&1&0\\
r_j(S)&0&-1&-1&0.
\end{array}                                           \tag{3}
\]

For each dummy `d in {d_1,d_2}`, define

\[
 r_d(S)=\begin{cases}
 -1,&d\in S,\\
 0,&d\notin S.
 \end{cases}                                         \tag{4}
\]

Equations (3)--(4) define all fifteen nonempty terminal rows, including
dummy-only exits and collisions involving dummies.  Every coordinate is
rational and lies in `[-1,1]`.  Infinite all-Continue play pays zero.

A mixed timing profile is a product of the players' private mixed planned
times.  Its literal behavioral realization uses the standard conditional
hazards of those marginal laws along the unique public all-Continue history.
Zero-reach denominators may be assigned arbitrary Continue hazards; they do
not change the stopping law.  No public correlation or observation of a
private planned time is used.

For a behavioral profile `sigma`, write `U_i(sigma)` for prescribed terminal
payoff and

\[
 B_i(\sigma)=\sup_{\tau_i}U_i(\tau_i,\sigma_{-i})
\]

for the supremum over every randomized history-dependent behavioral
deviation.  Put

\[
 \operatorname{Expl}_r(\sigma)=\max_i(B_i(\sigma)-U_i(\sigma)).
\]

## Proof of uniqueness at every deadline

We use backward induction on the number of remaining finite dates.  With zero
finite dates, every player has only the Never action, so the timing profile is
unique and its active continuation payoff is `(0,0)`.  At a
current live date a dummy's current Quit action pays `-1` surely, whereas
Never guarantees zero because a dummy absent from the quitting coalition
always receives zero.  Hence every dummy Continues at the current date.

Let `p` and `q` be the current Quit probabilities of `k` and `j`.
Neither active player can Quit surely.

* If `p=1`, player `j` strictly prefers to collide now, receiving `0` rather
  than `-1`.  Once `q=1`, player `k` strictly prefers Continue, receiving
  `1` rather than `0`, a contradiction.
* If `q=1`, player `k` strictly prefers Continue, hence `p=0`, and player `j`
  receives `-1`.  If `k`'s remaining timing law has positive Never mass,
  player `j` improves by Never.  Otherwise `k` has a positive finite atom,
  and player `j` improves by colliding with one such atom: the tie pays zero
  instead of `-1`.  A dummy-only earlier exit, if present, already pays
  player `j` zero and cannot destroy strict improvement.

Thus `p,q<1`.  Since the dummies Continue, the current all-Continue event has
positive probability.  The conditional timing profile after that public
history must be Nash in the remaining timing game: a strict tail improvement
could otherwise be spliced after the current history, giving a strict global
improvement multiplied by its positive reach probability.  The induction
hypothesis makes that tail unique and forces the dummies to Never at every
later date.  No subgame-perfect refinement has been assumed; tail optimality
is forced by ordinary Nash and positive reach.

Let `(u,v)` be the unique active continuation payoff of that tail.  With the
dummies absent, direct subtraction of Continue from Quit gives

\[
 \Delta_k=(1/2-u)-q(3/2-u),
 \qquad
 \Delta_j=p(2+v)-(1+v).                              \tag{5}
\]

Whenever `u<1/2` and `v>-1`, the first difference strictly decreases through
zero as `q` varies from zero to one, while the second strictly increases
through zero as `p` varies from zero to one.  None of the four pure corners is
Nash, so the unique current root is interior:

\[
 p={1+v\over2+v},
 \qquad
 q={1/2-u\over3/2-u}.                                \tag{6}
\]

Conversely, joining this root to the unique Nash tail is Nash by ordinary
finite backward induction.  Hence the full timing-game equilibrium is unique.

## Exact recursion and Never products

Indifference in (6) gives the predecessor active payoff

\[
 u'={1\over3-2u},
 \qquad
 v'={-1\over2+v}.                                    \tag{7}
\]

Starting from the hard all-Never tail `(u_0,v_0)=(0,0)`, induction yields

\[
 u_n={1\over2}\left(1-{1\over2^{n+1}-1}\right),
 \qquad
 v_n=-1+{1\over n+1}.                                \tag{8}
\]

In particular `u_n<1/2` and `v_n>-1`, so the strict domain used above is
preserved.  The root prepended to an `n`-date tail has

\[
 p_n={1\over n+2},
 \qquad
 q_n={1\over2^{n+2}-1}.                              \tag{9}
\]

The full `N`-date equilibrium therefore has exact active Never masses

\[
 a_k^{(N)}=\prod_{n<N}(1-p_n)={1\over N+1},
\]

\[
 a_j^{(N)}=\prod_{n<N}(1-q_n)
 ={2^N\over2^{N+1}-1}.                               \tag{10}
\]

Both products telescope.  In particular player `k` assigns positive mass to
Never at every finite deadline.

## Exact unrestricted debt

Fix a player `i`.  Finite timing Nash controls every pure date below `N` and
Never.  Because the opponents Continue surely after date `N`, every later
finite pure Quit time has one common value `L_i`.  Relative to Never, it adds
exactly the singleton reward on the event that all opponents chose Never:

\[
 L_i-V_i^{Never}=E_i s_i,                             \tag{11}
\]

where `E_i` is the product of opponents' Never masses and
`s_i=r_i({i})`.  If

\[
 \sigma_i=U_i-V_i^{Never}\ge0
\]

is the prescribed finite-game payoff's advantage over Never, checked
behavioral pure-time extremality gives the exact full debt

\[
 d_i=\max(0,E_i s_i-\sigma_i).                       \tag{12}
\]

For player `k`, Never has positive support, so mixed-Nash indifference gives
`sigma_k=0`.  Both dummies have Never mass one, while `s_k=1/2`; hence

\[
 d_k={1\over2}a_j^{(N)}
 ={2^{N-1}\over2^{N+1}-1}>{1\over4}.                 \tag{13}
\]

Player `j` and both dummies have singleton reward `-1`.  Their after-support
value cannot improve on Never, so their debts are zero.  Equation (13) is
therefore the exact maximum terminal debt against every behavioral
deviation.  Moreover

\[
 {D_{N+1}\over D_N}
 ={2^{N+2}-2\over2^{N+2}-1}<1,
\]

and division of (13) by `2^(N+1)` gives the limit `1/4`.  This proves both
the asserted strict decrease and its limit.

## Vanishing actual finite-clock comparison

Fix `L>=1`.  Prescribe the following behavioral profile `sigma^L`.

* Player `j` Quits surely at date zero.
* Player `k` Continues at date zero.  Conditional on public survival, it uses
  the private behavioral hazards whose stopping law is uniform on
  `{1,...,L}`.
* Both dummies Continue forever.

The prescribed path absorbs at `{j}`, with payoff `(1,-1,0,0)`.

Player `k` cannot improve: Continue receives one, while joining at date zero
receives zero.  A dummy receives zero by Continuing and `-1` by joining.
When player `j` deviates, Quit at date zero still pays `-1`.  Conditional on
refusal, any deterministic time in `{1,...,L}` pays `-1` except on its one
tie atom with `k`, where it pays zero.  Any time after the punishment window,
and Never, lets `k` quit first and pays `-1`.  Therefore player `j`'s best
deviation payoff is exactly

\[
 -1+{1\over L},
\]

and its debt is `1/L`; all other debts are zero.  Behavioral pure-time
extremality again exhausts all randomized history-dependent deviations.
This proves (2), the zero exploitability infimum, and—through the checked
fixed-target terminal acceptance theorem—the uniform-equilibrium payoff
`(1,-1,0,0)`.

The off-path punishment respects unilateral agency.  When `j` deviates, the
prescribed clock of `k` remains; when `k` deviates, the prescribed sure Quit
of `j` remains and the punishment branch is irrelevant.  Public survival at
date one reveals only the public refusal event, not a private planned time.

## Boundary tests

* At `N=1`, the unique root is `(p_0,q_0)=(1/2,1/3)` and the exact debt is
  `D_1=1/3`.
* At `N=2`, the exact debt is `D_2=2/7`; adding one hard date improves this
  table but does not begin a vanishing sequence.
* Every denominator in (6)--(10) is positive on the proved invariant region;
  no zero-support conditioning is hidden.
* Dummies cannot create additional equilibria: current Quit is strictly worse
  than Never at every positively reached live date, and the active sure-Quit
  cases were excluded before tail induction.
* The comparison profile has exact error `1` at `L=1` and error tending to
  zero as `L` grows; no error is claimed to be negative or attained at zero.
* The same table simultaneously supplies the nonvanishing exact-Nash sequence
  and the vanishing non-Nash sequence, ruling out any positive-gap reading.

## Source correspondence and novelty

The unnormalized two-active-player recursion first appeared as Proposition 9
of
[`notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md),
and its diffuse comparison as Proposition 10 there.  Those propositions had
independent ordinary reviews.  The present result positively rescales only
player `k`'s payoff coordinate, pads to literal Fin4, and isolates the exact
normalized architecture theorem.  Positive playerwise scaling preserves all
best-response comparisons; the proof above also recalculates every normalized
formula directly.

Checked correspondence:

* `QuittingFiniteDeadlineNashProfile` and
  `quittingRootSequencePureTimeTerminalValue_late_sub_none_eq` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`
  express the supplied hard-deadline profile and its after-support escape.
  They do not construct finite timing Nash profiles or prove uniqueness.
* `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`
  supplies the unrestricted behavioral cap reduction.
* `KernelGame.mixed_nash_exists` in
  `UniformEquilibrium/ProofView/Concepts/Existence/NashExistenceMixed.lean`
  is the generic finite mixed-Nash producer; it does not contain this timing
  recursion.
* `quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  is the checked fixed-target consumer for the `1/L` family.

A narrow search found no checked declaration, formalized packet, or prior
export with the normalized Fin4 table, every-deadline uniqueness, exact
quarter lower barrier, and zero-infimum comparison.  The independently
reviewed universal upper theorem in
[`notes/CODEX_EULER__FINITE_DEADLINE_NASH_UNIVERSAL_QUARTER_CEILING.md`](../notes/CODEX_EULER__FINITE_DEADLINE_NASH_UNIVERSAL_QUARTER_CEILING.md)
is complementary: it bounds every normalized table from above and, together
with this packet, identifies the asymptotic worst-table value.  This packet
does not rely on that later result.

No external paper is used beyond the standard finite-game Nash existence
theorem already represented by the checked declaration above.

## Adapter and consumer

The adapter is the explicit normalized rational Fin4 reward table
(3)--(4).  For every chosen hard deadline, the unique finite timing Nash law
and its literal independent behavioral hazards are computed by (8)--(10).
Equation (12) and checked pure-time extremality consume that profile into the
exact unrestricted debt (13).

The negative architecture consumer is uniqueness itself: every possible
exact equilibrium selection at this table returns the same nonvanishing
profile.  The positive boundary consumer is the explicit `sigma^L` family,
which proves that arbitrary actual finite-clock centers still converge to
zero error and reaches the checked fixed-target uniform-payoff theorem.

## Lean handoff

The narrowest useful implementation has two layers.

1. Define the table (3)--(4), the active continuations (8), and the explicit
   root sequence (9).  Prove the local root Nash equations, the invariant
   inequalities, the two telescoping products, and the exact semantic debt
   using the checked late-minus-Never and pure-time declarations.  This first
   layer supplies a checked nonvanishing explicit Nash family.
2. Define finite planned-time laws on `Fin N` plus Never and their literal
   hazard realization.  Prove the positive-reach tail-splice lemma and use it
   with the two sure-Quit exclusions to establish uniqueness of every mixed
   timing Nash.  Uniqueness is required before claiming that arbitrary exact
   equilibrium selection is excluded.

Separately define `sigma^L` by a sure date-zero owner and the existing
finite uniform stopping-law hazard for the punisher.  Compute its three
pure-time payoff regimes and invoke behavioral pure-time extremality to show
exact debt `1/L`; then apply the checked fixed-target acceptance theorem.

The formalization must not encode “is the unique equilibrium” or the desired
debt lower bound as a structure field.  Both are conclusions to prove from
the concrete finite timing game and reward table.

## Scope and nonclaims

This packet does not prove a positive all-profile terminal gap, furnish a
counterexample, or challenge the uniform-equilibrium conjecture.  It does not
exclude:

* soft or nonzero terminal continuation values;
* approximate finite timing equilibria;
* changing early hazards while adding later dates;
* off-path diffuse punishment;
* non-Nash finite-clock profiles; or
* another constructive chronology accepted by the uniform-payoff theory.

It proves exactly that fresh exact Nash selection in every growing
hard-all-Continue-tail timing game is not a universally vanishing producer.

## Formalization record

The packet is formalized at its full reviewed scope in three checked modules.

- `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashBarrier.lean`
  defines the normalized rational Fin4 table and canonical hard-deadline
  profiles, proves their exact unrestricted exploitability
  `hardDeadlineDebt`, proves convergence to `1/4`, and constructs the exact
  `1/L` comparison family with target `(1,-1,0,0)`.
- `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashUniqueness.lean`
  proves `existsUnique_finiteDeadlineTimingNash` for every deadline, identifies
  the unique law with the canonical behavioral profile, and proves the exact
  debt and strict quarter lower bound for every positive deadline.
- `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashWorstCase.lean`
  combines the table-specific lower family with the universal finite-deadline
  upper bound and proves
  `tendsto_finiteDeadlineTimingNashWorstExploitability_succ_quarter`.

The same-table comparison theorem
`comparisonTarget_isUniformEquilibriumPayoff` proves that `(1,-1,0,0)` is a
uniform-equilibrium payoff, and `terminalExploitabilityInf_eq_zero` proves the
true executable terminal exploitability infimum is zero.

Evidence seals are `M`, `L`, `A`, and `C`: both independent reviews passed;
Lean checks the concrete table, complete finite-game uniqueness, exact debt,
limit, and comparison family; the laws are literal independent planned-time
laws with exact Never atoms and checked behavioral realizations; and the
comparison family is consumed by the fixed-target uniform-payoff theorem.

No positive all-profile terminal gap or quitting-game counterexample is
claimed.  The result excludes only exact Nash selection in growing hard-zero-
tail timing games; soft tails, approximate timing Nash, changed early hazards,
and non-Nash finite-clock profiles remain outside the no-go.
