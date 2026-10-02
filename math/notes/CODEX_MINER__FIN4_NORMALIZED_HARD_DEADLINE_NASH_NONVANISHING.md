# Normalized Fin4 hard-deadline Nash profiles do not approximate the zero gap

## Status

**Complete ordinary mathematics; independently reviewed (PASS); narrow export
candidate.**  This is a
concrete no-go for extending the universal one-shot Nash producer by adding
finitely many planned quit dates and imposing exact Nash again.  It is not a
counterexample to the quitting-game conjecture: the same normalized rational
Fin4 table has explicit actual finite-clock profiles of unrestricted debt
exactly `1/L`.

Independent review:
[`CODEX_EULER`](../feedback/CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING__BY_CODEX_EULER.md).
The dummy elimination, tail-splice uniqueness, rational recurrences and Never
products, exact unrestricted debt, and diffuse `1/L` comparison all passed
without repair.

The active recursion is the coordinate-normalized Fin4 specialization of
Proposition 9 in
[`CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md),
which was independently checked in
[`CODEX_GAUSS`, Round 2](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_GAUSS__ROUND_2.md).
The vanishing-error comparison specializes the diffuse refusal construction
in Proposition 10, independently checked by
[`CODEX_GAUSS`, Round 3](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_GAUSS__ROUND_3.md)
and
[`CODEX_CEDAR`, Round 3](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_CEDAR__ROUND_3.md).
The normalized table, exact Fin4 statement, and its consequence for the new
one-shot/quantile architecture are isolated here for the first time.

## 1. Question and exact answer

The reviewed universal one-shot theorem in
[`CODEX_EULER__UNIVERSAL_ONE_SHOT_NASH_OUTER_ZERO_BOUND.md`](CODEX_EULER__UNIVERSAL_ONE_SHOT_NASH_OUTER_ZERO_BOUND.md)
selects, for every normalized table, a date-zero/Never mixed Nash profile of
unrestricted terminal debt at most `2/3`.  A natural attempted amplification
is:

> allow dates `0,...,N-1,Never`, select an exact mixed Nash equilibrium of
> this finite timing game, realize its product timing laws behaviorally, and
> let `N` tend to infinity.

The answer is **no**, even for one fixed normalized rational Fin4 table and
even if the equilibrium may be selected separately at every deadline.

### Theorem 1.1 (normalized Fin4 exact-Nash nonvanishing)

There is a reward table `r` on `Fin 4`, with every terminal coordinate in
`[-1,1]`, such that for every integer `N>=1`:

1. the finite timing game with pure actions
   `0,...,N-1,Never` has a unique mixed Nash equilibrium;
2. its literal behavioral realization has unrestricted terminal
   exploitability

   \[
   D_N={2^{N-1}\over 2^{N+1}-1}>{1\over4};             \tag{1.1}
   \]

3. nevertheless there are literal finite-clock behavioral profiles
   `sigma^L`, `L>=1`, with one fixed prescribed payoff and exact unrestricted
   exploitability

   \[
   \operatorname{Expl}_r(\sigma^L)={1\over L}.         \tag{1.2}
   \]

Consequently `eta(r)=0`, while

\[
 \inf_{q\in NE_N(r)}\operatorname{Expl}_r(q)=D_N>{1\over4}
 \quad\hbox{for every }N,\qquad D_N\downarrow {1\over4}. \tag{1.3}
\]

Thus no universal `N`-date vanishing-error theorem can be obtained by adding
exact finite-timing Nash constraints to the actual finite-clock centers.  The
failure is Nashification, not finite-clock expressiveness.

## 2. The normalized rational Fin4 table

Name the players

\[
 I=\{k,j,d_1,d_2\}.
\]

For a nonempty quitting coalition `S`, let
`A=S intersection {k,j}`.  Define the active coordinates by

\[
\begin{array}{c|rrrr}
A & \varnothing & \{k\} & \{j\} & \{k,j\}\\ \hline
r_k(S)&0&1/2&1&0\\
r_j(S)&0&-1&-1&0.
\end{array}                                             \tag{2.1}
\]

For each dummy `d in {d_1,d_2}`, put

\[
 r_d(S)=\begin{cases}-1,&d\in S,\\0,&d\notin S.
             \end{cases}                               \tag{2.2}
\]

This defines all fifteen terminal rows, including dummy-only rows and rows
containing dummies together with active players.  Every coordinate is in
`[-1,1]`.  As usual the payoff when nobody ever quits is zero.

The active table is obtained from Noether's Proposition 9 table by multiplying
only player `k`'s payoff coordinate by `1/2`.  Positive coordinatewise scaling
preserves every best-response comparison, but the complete proof below does
not rely on that observation.

## 3. Finite timing game and dummy elimination

Fix `N>=1`.  Each player independently chooses a planned time in

\[
 T_N=\{0,\ldots,N-1,\mathsf{Never}\}.
\]

The first finite time determines the quitting coalition; all Never pays zero.
Every mixed timing law has the standard literal behavioral hazard
realization, including its exact Never atom.

We prove by backward induction on the number of remaining dates that the
equilibrium is unique.  At the current live date, Quit is strictly dominated
by Never for a dummy: quitting now puts that dummy in the first coalition and
pays `-1`, while Never always pays zero because the dummy is absent from the
terminal coalition.  Hence every dummy Continues at the current date.

Let `p` and `q` be the current Quit probabilities of `k` and `j`.
Neither active player can Quit surely.

* If `p=1`, player `j` strictly prefers to collide, receiving `0` instead of
  `-1`; but when `q=1`, player `k` strictly prefers Continue, receiving `1`
  instead of `0`.
* If `q=1`, player `k` strictly prefers Continue, so `p=0`, and player `j`
  receives `-1`.  Continuing and choosing Never in the tail gives strictly
  more if `k` has positive Never mass.  If `k` has no Never mass, collide with
  any positive finite atom of `k`; the tie changes `j`'s payoff from `-1` to
  `0`.  A dummy-only earlier exit, if present, already pays `j` zero.  Thus
  `j` again has a strict improvement.

Therefore `p,q<1`.  The current all-Continue event has positive probability,
so the conditional timing profile in the remaining tail must itself be Nash:
any profitable tail deviation can be spliced after the current public
all-Continue history, multiplying its improvement by a positive reach
probability.  Induction forces every dummy to be Never at every later date
and fixes the unique active tail.  This argument uses no subgame-perfect
refinement; positive reach makes it a consequence of ordinary Nash
optimality.

## 4. Exact unique active recursion

Let `(u,v)` be the active payoff continuation after the current all-Continue
action.  Against the other active player's current mixture, Quit minus
Continue is

\[
 \Delta_k=(1/2-u)-q(3/2-u),\qquad
 \Delta_j=p(2+v)-(1+v).                                \tag{4.1}
\]

Whenever `u<1/2` and `v>-1`, the first difference strictly decreases through
zero as `q` runs from zero to one, and the second strictly increases through
zero as `p` runs from zero to one.  Checking the four pure corners shows that
the unique Nash root is interior:

\[
 p={1+v\over2+v},\qquad
 q={1/2-u\over3/2-u}.                                  \tag{4.2}
\]

Indifference gives the predecessor payoff

\[
 u'={1\over 3-2u},\qquad v'={-1\over2+v}.              \tag{4.3}
\]

Starting at the hard all-Never tail `(u_0,v_0)=(0,0)`, direct induction gives

\[
 u_n={1\over2}\left(1-{1\over2^{n+1}-1}\right),
 \qquad
 v_n=-1+{1\over n+1}.                                  \tag{4.4}
\]

The root prepended to an `n`-date tail is therefore

\[
 p_n={1\over n+2},\qquad
 q_n={1\over2^{n+2}-1}.                                \tag{4.5}
\]

Equations (4.4)--(4.5) preserve `u_n<1/2` and `v_n>-1`, closing the induction
and the uniqueness proof.

The full `N`-date equilibrium has exact Never masses

\[
 a_k^{(N)}=\prod_{n<N}(1-p_n)={1\over N+1},
 \qquad
 a_j^{(N)}=\prod_{n<N}(1-q_n)
 ={2^N\over2^{N+1}-1}.                                 \tag{4.6}
\]

Both products telescope.  In particular player `k` uses Never with positive
probability at every finite deadline.

## 5. Exact unrestricted debt

Finite timing Nash optimality controls Quit at each date below `N` and Never.
Against opponents who are all-Continue after date `N`, every later finite
Quit time has the same value.  Relative to Never, it adds precisely the
player's singleton reward on the event that every opponent chose Never.
Behavioral pure-time extremality then gives the exact identity

\[
 d_i=\max\{0,E_i s_i-\sigma_i\},                       \tag{5.1}
\]

where `E_i` is the product of the opponents' Never masses, `s_i=r_i({i})`,
and `sigma_i` is the prescribed payoff's finite-game advantage over the
permitted Never action, with the sign convention
`sigma_i=U_i-V_i^{Never}>=0`.

For player `k`, its positive Never mass makes Never a supported action, so
`sigma_k=0`.  The two dummies have Never mass one, hence

\[
 E_k=a_j^{(N)},\qquad s_k=1/2,qquad
 d_k={2^{N-1}\over2^{N+1}-1}.                          \tag{5.2}
\]

Player `j` and both dummies have singleton reward `-1`, so a late Quit cannot
improve on Never and their unrestricted debts are zero.  Thus (5.2) is the
exact profile exploitability.  Since

\[
 {2^{N-1}\over2^{N+1}-1}>{2^{N-1}\over2^{N+1}}={1\over4},
\]

it never tends to zero; its limit is `1/4`.

The statement is genuinely about every behavioral unilateral deviation.
The reduction to finite dates, Never, and the one common after-support value
is exactly the pure-time extremality step, not an assumption that deviations
are bounded or stationary.

## 6. The same table has exact `1/L` finite-clock profiles

For `L>=1`, prescribe the following behavioral profile `sigma^L`.

* Player `j` Quits surely at date zero.
* Player `k` Continues at date zero.  Conditional on public survival through
  date zero, it uses the hazard realizing the uniform planned quit time on
  `{1,...,L}`.
* Both dummies Continue forever.

The prescribed path absorbs at `{j}` and has the fixed payoff

\[
 r(\{j\})=(1,-1,0,0).                                  \tag{6.1}
\]

Player `k` cannot improve: joining `j` pays zero instead of one.  A dummy
cannot improve: joining pays `-1` instead of zero.  If `j` deviates, then
Quit at date zero still pays `-1`.  Conditional on refusal, a deterministic
time in `{1,...,L}` pays `-1` except on its one collision atom with `k`, where
it pays zero.  A time after the punishment window or Never pays `-1` because
`k` quits first.  Hence the best deviation payoff is exactly

\[
 -1+{1\over L},
\]

and `j`'s debt is exactly `1/L`.  Pure-time extremality again covers every
history-dependent behavioral deviation.  This proves (1.2) and `eta(r)=0`.
The fixed-target consumer
`quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance` would
also compile (6.1) to a uniform-equilibrium payoff.

This comparison is essential: the theorem is not a positive-gap table.  It
separates exact finite-game Nash selection from actual finite-clock
approximation.

## 7. Consequence for the one-shot and quantile architectures

At `N=1`, (4.5) gives the unique one-shot root

\[
 p_0=1/2,\qquad q_0=1/3,
\]

and its unrestricted debt is `D_1=1/3`, consistent with the universal
`2/3` theorem.  Increasing the timing menu and re-solving exact Nash merely
follows the unique recursion (4.3); the summable `j` hazards leave a positive
opponent-Never mass and the debt decreases only to `1/4`.

Accordingly, the escape-aware finite-clock hierarchy must retain arbitrary
actual finite-clock centers.  If its center were replaced by, or restricted
to, exact Nash equilibria of the corresponding hard-deadline timing games,
then on this table its upper objective would remain above `1/4` although the
true executable infimum is zero.  Exact finite-clock semialgebraicity remains
sound; the extra Nash constraint is the incompatible field.

The result does **not** rule out multi-date constructions with a soft tail,
approximate root inequalities, off-path punishment, or non-Nash finite-clock
profiles.  Section 6 explicitly demonstrates the last alternative.

## 8. Source, duplicate, and Lean audit

Inspected sources:

* `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean` is the one-date root
  producer used by the new universal `2/3` theorem.  It has no iterated-error
  conclusion.
* `QuittingFiniteDeadlineNashProfile`,
  `quittingRootSequencePureTimeTerminalValue_late_sub_none_eq`, and
  `QuittingFiniteDeadlineNashProfile.semanticDebt_le_escapeCharge` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`
  are the checked consumer and upper-bound interface.  They do not construct
  a finite timing Nash profile, prove the exact adjusted-slack identity, or
  contain this table.
* `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` is the
  checked unrestricted-deviation reducer.
* `quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  is the fixed-target consumer for Section 6.
* The ordinary source propositions and their reviews are linked at the top of
  this note.  A narrow search for the normalized table, the `1/4` bound, and a
  hard-deadline/quantile Nash-center obstruction found no duplicate
  declaration, note, formalized packet, or export.

The clean Lean handoff is a finite exact regression rather than a general
finite-game development:

1. define the four-player table (2.1)--(2.2) and the explicit hazards from
   (4.5);
2. prove their timing-game Nash equations and the exact Never products;
3. use the checked late-minus-Never identity plus supported-Never equality to
   prove (5.2);
4. separately define the uniform punishment clock of Section 6 and prove its
   exact debt `1/L` by pure-time extremality.

Formalizing uniqueness of every timing-game Nash is the strongest no-go.  A
weaker first artifact may prove that backward iteration of the unique local
root equations yields debt bounded below by `1/4`, but it should not be
advertised as excluding arbitrary equilibrium selection until uniqueness is
checked.

## 9. Export disposition and next question

The independent review confirms the normalized recursion, dummy induction,
and unrestricted-debt equality.  This is therefore a plausible narrow export
candidate: it is an exact normalized Fin4 impossibility theorem that decisively removes
the proposed exhaustive “add dates and re-Nashify” extension of the universal
one-shot producer.  Any packet must preserve the explicit `eta(r)=0` boundary
and must not call the table a conjecture counterexample.

The surviving constructive question is now sharper: can every normalized
table choose a **soft** finite tail or an approximate timing root whose
off-support collision premiums are dispersed, as in Section 6, while keeping
all on-support deviations controlled?  Exact hard-zero-tail Nash selection
cannot be that theorem.
