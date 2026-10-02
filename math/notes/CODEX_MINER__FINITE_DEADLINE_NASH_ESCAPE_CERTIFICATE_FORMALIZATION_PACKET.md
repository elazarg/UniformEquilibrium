# Finite-deadline Nash production and exact horizon escape

Author/assembler: `CODEX_MINER`

Status: **review-ready export candidate; ordinary mathematics, not checked in
Lean.**  This packet consolidates the stronger result of
[`CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md),
Sections 1 and 3--6, with the concise horizon-escape formulation in
[`CODEX_FERMAT__FINITE_DEADLINE_NASH_HORIZON_ESCAPE.md`](CODEX_FERMAT__FINITE_DEADLINE_NASH_HORIZON_ESCAPE.md).
It does not claim novelty over either conference note.  Its new repository
target is the arbitrary-table producer missing from the checked supplied-object
interface, together with its exact adjusted-debt identity.

Existing independent falsification reviews:

- [`CODEX_CEDAR`](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_CEDAR.md)
  checked the exact adjusted-debt identity, zero masses, negative singleton
  rewards, and unrestricted behavioral deviations.
- [`CODEX_EULER`](../feedback/CODEX_FERMAT__FINITE_DEADLINE_NASH_HORIZON_ESCAPE__BY_CODEX_EULER.md)
  checked the finite Nash producer, hazard realization at zero tails, deadline
  convention, global-gap corollary, and unrestricted behavioral deviations.

The export gate should be decided on this consolidated statement, not on a
claim that the short Fermat presentation is new mathematics.

## 1. Exact statement

Let `I` be a nonempty finite player set and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a quitting-game reward table.  Payoff is zero if nobody ever quits.  For
`N\in\mathbb N`, put

\[
 K_N=\{0,\ldots,N-1\}\sqcup\{\infty\};
\]

when `N=0`, this is the one-element set `\{\infty\}`.  The finite timing game
gives an action profile `a\in K_N^I` the quitting reward determined by its
earliest finite date, and gives the all-`\infty` profile payoff zero.

### Theorem A: arbitrary-table producer

For every `N`, the finite timing game has a mixed Nash equilibrium `q`.  There
is a behavioral quitting profile `\sigma` whose independent stopping-time law
is exactly `q`, which is surely Continue at every live date `t\ge N`, and for
which every player `i` and every `t<N` or `t=\infty` satisfies

\[
 U_i(\sigma[i\leftarrow Q_t])\le U_i(\sigma).       \tag{1.1}
\]

Thus `\sigma` supplies the checked predicate
`QuittingFiniteDeadlineNashProfile reward sigma N`.  This is an actual-data
producer for every finite reward table, not a supplied-certificate verifier.

### Theorem B: exact adjusted-debt identity

The following identity in fact holds for every behavioral `\sigma` carrying a
`QuittingFiniteDeadlineNashProfile reward sigma N` certificate, whether or not
one remembers the finite mixed equilibrium used to produce it.  Write

\[
 \begin{aligned}
 P_i&=U_i(\sigma),\\
 V_i^\infty&=U_i(\sigma[i\leftarrow Q_\infty]),\\
 \kappa_i&=P_i-V_i^\infty\quad(\ge0),\\
 E_i&=\Pr_{\sigma_{-i}}(T_j\ge N\text{ for every }j\ne i),\\
 s_i&=r_i(\{i\}).
 \end{aligned}
\]

Then the full unrestricted behavioral terminal debt of player `i` is

\[
 d_i(\sigma)
   =\sup_{\tau_i}\bigl(U_i(\sigma[i\leftarrow\tau_i])-P_i\bigr)
   =\max\{0,E_i s_i-\kappa_i\}.                       \tag{1.2}
\]

In particular the exact maximum-player exploitability is

\[
 D(\sigma)=\max_i\max\{0,E_i s_i-\kappa_i\}.         \tag{1.3}
\]

This strictly sharpens the checked raw-charge upper bound
`d_i\le E_i\max(0,s_i)`.

### Corollary C: horizon escape under a global terminal gap

Suppose `\gamma>0` and every behavioral profile has unrestricted terminal
exploitability at least `\gamma`.  Then for every `N` and every mixed Nash
equilibrium `q` of the deadline-`N` timing game, its behavioral realization
has some player `i` such that

\[
 E_i s_i-\kappa_i\ge\gamma.                          \tag{1.4}
\]

Equivalently, every declared action `t<N` and `\infty` has gain at most zero,
but the pure deviation `Q_N` has gain at least `\gamma` for some player.
Consequently, for every finite `F\subseteq\mathbb N`, there is an actual
behavioral profile at which every `Q_t`, `t\in F`, and `Q_\infty` has
nonpositive gain while one later pure time has gain at least `\gamma`.

Moreover the player in (1.4) satisfies

\[
 s_i\ge\gamma,\qquad E_i\ge\gamma/s_i>0.             \tag{1.5}
\]

Every opponent's deadline-survival probability is at least `\gamma/s_i`.
If the finite equilibrium gives player `i` positive `\infty` mass, then
`\kappa_i=0`; otherwise `i` is the unique coordinate with zero `\infty` mass.

The corollary is conditional.  It does not construct a positive-gap table.

## 2. Probability, observation, and agency

The finite timing game uses independent private mixed actions.  Its behavioral
realization uses one private randomizer for each player's live-history hazard;
there is no public coin and no observation of another player's sampled stopping
time.  The quitting game has a unique public live history, so the hazards below
are legitimate behavioral strategies.

The debt in (1.2) takes the supremum over **all** unilateral behavioral
strategies.  It is not a bounded-controller or pure-deviation statement.  The
reduction to pure quit times uses the checked quitting-game pure-time
extremality theorem; it does not assume a behavioral best response is attained.

## 3. Proof

### 3.1 Finite Nash production

For `a\in K_N^I`, if a finite coordinate exists let

\[
 m(a)=\min\{a_i:a_i<\infty\},\qquad
 S(a)=\{i:a_i=m(a)\},
\]

and set the payoff to `r(S(a))`; set the all-`\infty` payoff to zero.  This is a
finite normal-form game with nonempty action sets, including when `N=0`.
Finite mixed-Nash existence supplies a product mixed equilibrium
`q=(q_i)_i`.

For player `i` define the tail, for `0\le t<N`, by

\[
 M_i(t)=q_i(\infty)+\sum_{s=t}^{N-1}q_i(s).
\]

At live date `t<N`, prescribe Quit probability

\[
 h_i(t)=
 \begin{cases}
 q_i(t)/M_i(t),&M_i(t)>0,\\
 0,&M_i(t)=0,
 \end{cases}
\]

and prescribe Continue surely from date `N` onward.  Induction gives survival
to date `t` equal to `M_i(t)`.  If `M_i(t)>0`, multiplication by
`1-h_i(t)=M_i(t+1)/M_i(t)` advances the identity.  If `M_i(t)=0`, every later
finite mass and the `\infty` mass are zero and the behavioral live path already
has probability zero, so the chosen zero hazards on that unreachable tail are
harmless.  Therefore the induced stopping law has mass `q_i(t)` at each
`t<N` and mass `q_i(\infty)` at Never.

Coordinatewise private realization preserves the independent product law.
Hence the behavioral terminal payoff and every unilateral pure-time payoff
equal the corresponding finite timing-game payoffs.  Mixed Nash optimality
gives (1.1), and the all-Continue tail gives the other field of
`QuittingFiniteDeadlineNashProfile`.  This proves Theorem A.

### 3.2 The permitted maximum equals the prescribed payoff

Now let `\sigma` be any profile carrying the checked finite-deadline
certificate.  The all-Continue suffix implies that each player's stopping law
is supported on `K_N`.  Against fixed opponents, `P_i` is the expectation of
the pure-time payoff under player `i`'s own stopping law.  Every pure time in
`K_N` has payoff at most `P_i` by the certificate.  Therefore their maximum is
exactly `P_i`: their average cannot be strictly larger or smaller than a common
upper bound equal to that average.  In particular `V_i^\infty\le P_i`, so
`\kappa_i\ge0`.  No support-indifference assertion is needed here.

### 3.3 Every late time has one exact value

Fix `t\ge N`.  If some opponent stops before `N`, player `i` choosing `t` or
Never leaves the already determined terminal outcome unchanged.  On the event
that all opponents survive to `N`, they Continue forever, so choosing Never
produces no later quit while choosing `t` makes `i` the singleton quitter.
The event has probability `E_i`.  Hence

\[
 U_i(\sigma[i\leftarrow Q_t])=V_i^\infty+E_i s_i.    \tag{3.1}
\]

This value is independent of `t\ge N`, including `t=N`.

### 3.4 Upgrade to unrestricted behavioral deviations

All pure-time values consist of the finite permitted family, whose maximum is
`P_i`, and the common late value in (3.1).  Checked pure-time extremality says
the supremum over unrestricted behavioral deviations is exactly the supremum
of these deterministic-time and Never values.  Thus the best-response envelope
is

\[
 \max\{P_i,V_i^\infty+E_i s_i\}.
\]

Subtracting `P_i` proves (1.2) and (1.3).

### 3.5 Global-gap consequences

Apply the assumed gap to a profile produced from any deadline equilibrium.
Equation (1.3) selects `i` with (1.4); (3.1) says `Q_N` realizes that gain.
Since `0\le E_i\le1` and `\kappa_i\ge0`, (1.4) implies (1.5).  Writing
`E_i` as the product of the opponents' `\infty` masses, every factor is at
least the product and therefore at least `\gamma/s_i`.

If `q_i(\infty)>0`, finite mixed-Nash support indifference makes Never's payoff
equal `P_i`, hence `\kappa_i=0`.  Since every opponent has positive Never mass,
if `q_i(\infty)=0` then `i` is the unique zero-Never coordinate.

For nonempty finite `F`, choose `N>\max F`; for empty `F`, take `N=0`.  The
certificate controls all times in `F` and Never while `Q_N` realizes the gap.
This proves Corollary C.

## 4. Exact boundary tests

1. **Deadline zero.**  `K_0={\infty}` and the producer is the all-Never
   profile.  Here `P_i=V_i^\infty=0`, `E_i=1`, and (1.2) reads
   `d_i=\max(0,s_i)`, exactly the payoff from quitting immediately.

2. **Zero opponent survival.**  If one opponent has zero Never mass, then
   `E_i=0`; late quitting and Never have the same value and (1.2) gives zero
   debt because `\kappa_i\ge0`.

3. **Negative singleton.**  When `s_i<0`, late quitting is worse than Never;
   the positive part in (1.2) gives zero without a sign assumption.

4. **Raw charge can overestimate by one.**  For two players let
   `r({1})=(1,0)`, `r({2})=(0,-1)`, and `r({1,2})=(0,-1)`.  Player 1 quitting
   at date zero while player 2 chooses Never is a finite-deadline Nash profile.
   For player 1, `E_1=s_1=\kappa_1=1`; the raw charge is one but exact debt is
   zero.

5. **Finite-deadline Nash need not be unrestricted Nash.**  Let
   `r({1})=(1,0)`, `r({2})=(0,1)`, and `r({1,2})=(-1,-1)`.  At deadline one,
   each player mixes equally between date zero and Never.  Both permitted
   actions pay zero, so this is a finite timing Nash equilibrium, but
   `E_i=1/2`, `s_i=1`, `\kappa_i=0`, and exact unrestricted debt is `1/2`,
   attained by quitting at date one.

These tests show both why the checked raw escape bill is not exact and why the
producer alone does not settle the conjecture.

## 5. Source correspondence and named boundary change

Checked source inspected:

- `QuittingFiniteDeadlineNashProfile`,
  `quittingRootSequencePureTimeTerminalValue_late_sub_none_eq`,
  `QuittingFiniteDeadlineNashProfile.bestResponseValue_le_add_escapeCharge`,
  `QuittingFiniteDeadlineNashProfile.semanticDebt_le_escapeCharge`, and the
  terminal/uniform consumers in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`.
  The module explicitly says its predicate is a consumer interface and does
  not construct the finite timing equilibrium or behavioral realization.
- `GameTheory.exists_isNash_mixed` in `GameTheory/Analysis/Nash.lean` is the
  checked generic finite-game Nash theorem.
- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean` supplies the
  checked one-player mixture identity.
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` supplies
  unrestricted behavioral pure-time extremality.
- `HasTerminalExploitabilityGap` and
  `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap` in
  `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean` supply the
  checked negative semantic endpoint.

The narrow search found no checked declaration producing
`QuittingFiniteDeadlineNashProfile` and no checked adjusted-slack equality.
The current module has only the raw-charge inequality.  No paper theorem is
invoked; the relevant tracked literature search found no finite-deadline
planned-time producer corresponding to Theorems A--C.

This packet makes two named boundary changes:

1. it fills the explicitly missing arbitrary-game producer of the checked
   finite-deadline consumer; and
2. it supplies the exact mandatory **horizon escape** regression in
   [`ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md`](../questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md):
   no relaxation whose deviation objective sees only one fixed finite set of
   pure times plus Never can retain a positive fraction of a hypothetical
   all-profile gap on every actual profile.

The result does not itself satisfy any positive certificate-search progress
gate.  It makes the regression checkable and forces an escape-aware system to
represent late-time information rather than hide it in a fixed truncation.

## 6. Adapter and consumers

Theorem A is the arbitrary-data adapter from every finite reward table and
deadline to the checked `QuittingFiniteDeadlineNashProfile` interface.
Existing checked consumers then give the raw escape-charge debt bound and, for
families with vanishing raw charges, terminal approximate Nash and a uniform
equilibrium payoff.

Theorem B is a sharper proposed consumer theorem for the same checked
interface.  It replaces the raw bill with exact adjusted debt.  A family of
produced profiles whose maximum adjusted deficit tends to zero enters the
checked terminal-Nash-all-errors semantic endpoint directly.  Corollary C is
the negative consumer: a checked `HasTerminalExploitabilityGap` forces the
late-time witness at every deadline.

## 7. Lean handoff

The narrowest implementation can be split into three declarations.

1. A finite-law hazard realization, including zero tails, whose stopping law
   is exactly the input probability mass function on `Fin N \sqcup Unit`.
2. An arbitrary-table producer

   ```lean
   theorem exists_quittingFiniteDeadlineNashProfile
       [Nonempty ι]
       (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
       (deadline : ℕ) :
       ∃ profile,
         QuittingFiniteDeadlineNashProfile reward profile deadline
   ```

   using `GameTheory.exists_isNash_mixed` and the realization theorem.
3. For any supplied certificate, an exact equality between
   `quittingTerminalSemanticDebt` and the positive part of
   `deadlineSurvival * singletonReward - NeverSlack`, followed by the
   `HasTerminalExploitabilityGap` horizon-escape corollary.

The deadline convention is exact: permitted finite dates satisfy
`time < deadline`, the live tail is all-Continue from `deadline`, and the
first untested pure date is `deadline`.  Do not reindex this as an inclusive
deadline.  The zero deadline should use the one-action timing game or be proved
directly by the all-Never profile; it should not be discarded as an impossible
`Fin 0` game.

Useful exact regression instances are Boundary Tests 4 and 5.  They distinguish
the proposed equality from both the current raw upper bound and the false claim
that every finite-deadline Nash profile is already unrestricted Nash.

## 8. Scope and nonclaims

The packet does not produce a positive-gap reward table, a chronological
return, a Bellman path, a positive escape-aware certificate, or a uniform
equilibrium payoff for an arbitrary quitting game.  It does not localize gap
witnesses at a profile-dependent bounded time.  It rules out only a fixed
finite deviation menu under the global gap and formalizes the exact residual
left by the finite-deadline producer.

