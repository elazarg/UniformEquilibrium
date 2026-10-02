# Two-date timing Nash gives a sharp terminal-debt half bound

Authors: `CODEX_EULER`

Independent reviews:

- [`CODEX_MINER`](../feedback/CODEX_EULER__TWO_DATE_NASH_UNRESTRICTED_DEBT_HALF_BOUND__BY_CODEX_MINER.md)
- [`CODEX_RAMSEY`](../feedback/CODEX_EULER__TWO_DATE_NASH_UNRESTRICTED_DEBT_HALF_BOUND__BY_CODEX_RAMSEY.md)

Both reviewers independently checked the unrestricted behavioral cap, all
boundary cases, the scalar extremum, and the rational sharpness example.  Two
local proof-writing defects found during review have been repaired below:
signed comparison differences are used only through positive parts, and the
dummy-player uniqueness argument is equilibrium-specific.

## Exact statement

Let `I` be a nonempty finite player set.  Let `r` be a quitting-game reward
table satisfying

\[
 |r_i(S)|\le R
\]

for every player `i` and every nonempty quitting coalition `S`, where
`R >= 0`.  Infinite all-Continue play pays zero.

Form the finite timing game in which every player selects independently from

\[
 \{0,1,\mathsf{Never}\}.
\]

The players selecting the earliest finite time form the absorbing quitting
coalition.  Choose any mixed Nash equilibrium of this finite game and realize
each mixed planned-time law by its literal behavioral hazards, preserving its
exact Never atom.

Then every player `i` has unrestricted terminal semantic debt

\[
 0\le B_i-U_i\le\frac R2.
 \tag{1}
\]

The cap `B_i` is over every randomized history-dependent behavioral
deviation, including Never and every finite quitting time after the prescribed
support.

The constant is sharp for this architecture.  There is a rational normalized
Fin4 table whose `{0,1,Never}` timing game has a unique mixed Nash equilibrium
and whose literal realization has exploitability exactly `1/2`.

For the escape-aware quantile-clock hierarchy, let `A_K(r)` be the set of
terminal-semantic pairs of actual product stopping laws supported on
`{0,...,K-1,Never}`.  Put

\[
 K_m=2|I|m+1,
 \qquad
 \delta_m=\frac{|I|(|I|-1)}m,
\]

\[
 F(U,B)=\max\left\{0,\max_i(B_i-U_i)\right\},
\]

\[
 N_m(r)=\{z:\exists a\in A_{K_m}(r),
                 \|z-a\|_\infty\le\delta_m\},
 \quad
 R_M(r)=\bigcap_{1\le m\le M}N_m(r),
 \quad
 L_M(r)=\min_{z\in R_M(r)}F(z).
\]

For normalized Fin4 rewards,

\[
 L_M(r)=0\qquad(1\le M\le48)
 \tag{2}
\]

for every table `r`.

## Conjecture-facing change

This improves the reviewed universal one-date producer from coordinate debt
`2R/3` to `R/2`, while continuing to control the complete behavioral strategy
class.  By itself it moves the first universally unblocked normalized Fin4
level of the escape-aware hierarchy from `37` to `49`.

The subsequently reviewed
[`general-K` finite-deadline theorem](FINITE_DEADLINE_NASH_QUARTER_CEILING_AND_FIXED_PREFIX_BARRIER.md)
subsumes the universal `K=2` inequality and moves the corresponding cutoff
through level `59`.  The present result remains a useful self-contained base
case because it proves the exact sharp `K=2` constant and unique equality
regression.  A distinct normalized table, agreeing with the sharp table on
every coalition containing an active player but assigning `(1,-1)` rather
than `(0,0)` on dummy-only coalitions, is used by the later fixed-prefix
obstruction.  The sharp table here has the checked unique law
`(1/4,1/4,1/2)` and exact debt `1/2`; this uniqueness does not transport to
the fixed-prefix table.

The result is a strict finite-step improvement, not a vanishing-error theorem.
The independently reviewed hard-deadline no-go
[`CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING.md`](../notes/CODEX_MINER__FIN4_NORMALIZED_HARD_DEADLINE_NASH_NONVANISHING.md)
shows why no recursive conclusion is inferred: one normalized rational Fin4
table has unique exact `N`-date timing equilibria whose unrestricted debt
stays above `1/4`, even though other explicit finite-clock profiles for that
same table have debt tending to zero.

Thus the remaining constructive timing problem is sharply narrowed to soft
tails, approximate timing Nash conditions, or deliberately selected non-Nash
finite-clock profiles.

## Definitions and probability semantics

Fix a player `i` and the opponents' product distribution over planned times.
Let

\[
 a=\Pr(\text{every opponent chooses Never}),
\]

and let `h_0` and `h_1` be the probabilities that the opponents' earliest
finite planned time is respectively zero or one.  Then

\[
 a+h_0+h_1=1.
 \tag{3}
\]

Let `s=r_i({i})`.  Write `V_0,V_1,V_N` for `i`'s payoffs from the three pure
actions of the finite timing game, and let `L` be the payoff from any pure
quitting time `t >= 2`.  Every such late time has the same value because the
opponents have no finite mass after date one.

The behavioral realization uses independent hazards at the two live dates.
A planned-time law `(x_0,x_1,x_N)` is realized by date-zero Quit probability
`x_0` and, conditional on survival, date-one Quit probability
`x_1/(x_1+x_N)` when `x_1+x_N>0`; if that denominator is zero, the reached
date-one hazard may be set arbitrarily because the history has probability
zero.  Conditional on a second Continue, the player Never Quits.  This
realizes the original law exactly, including `x_N=0`, `x_N=1`, and every
zero-tail boundary.
A unilateral deviator may replace its entire stopping law.  The pure-time
extremality theorem is used below to pass from all deterministic stopping
times to this unrestricted behavioral cap.

## Source correspondence

The closest checked declarations are:

- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`, which
  reduces the unrestricted behavioral cap to pure quitting times;
- `QuittingFiniteDeadlineNashProfile` and
  `quittingRootSequencePureTimeTerminalValue_late_sub_none_eq` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`,
  which provide the existing hard-deadline interface and late-time identity;
- `quittingFiniteClockSemanticReachable_eq_range_fold`,
  `quittingFiniteClockSemanticReachable_isCompact`,
  `quittingFiniteClockSemanticReachable_mono`, `quantileClockSupport`, and
  `quantileClockRadius` in
  `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`, which provide
  the actual finite-word centers, support monotonicity, and hierarchy
  constants; and
- the ordinary hierarchy theorem in
  [`ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md`](ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md).

The checked general finite-game Nash producer is
`KernelGame.mixed_nash_exists` in
`UniformEquilibrium/ProofView/Concepts/Existence/NashExistenceMixed.lean`.
After packaging the three planned times as the finite pure actions, it supplies
the required mixed Nash law.  No current checked declaration packages this
specific timing game, its literal two-date realization, or the `R/2`
all-behavior bound.

No external paper is used; the argument is elementary and source-native.

## Proof of the universal bound

At a mixed Nash equilibrium, the prescribed payoff is a convex combination
of the three pure values and every pure value is at most the prescribed
payoff.  Hence

\[
 U_i=\max\{V_0,V_1,V_N\}.
 \tag{4}
\]

Pure-time extremality gives

\[
 B_i=\max\{V_0,V_1,V_N,L\},
 \qquad
 d_i:=B_i-U_i=\max\{0,L-U_i\}.
 \tag{5}
\]

There are three comparisons.

First, late Quit and Never differ only when every opponent chooses Never:

\[
 L-V_N=as.
 \tag{6}
\]

If `s <= 0`, equations (4)--(6) give `d_i=0`.  Assume `s>0` and, when
`R>0`, put `x=s/R`, so `0<x<=1`.

Second, late Quit and Quit at date one differ only when the opponents' first
finite time is one.  On that event the difference is an opponent-only versus
joined terminal reward and is at most `2R`.  Therefore

\[
 d_i\le\max\{0,L-V_1\}\le2Rh_1.
 \tag{7}
\]

Third, compare late Quit with Quit at date zero.  When opponents first quit at
zero, the leave-versus-join difference is at most `2R`.  When they first quit
at one, late Quit receives an opponent-only reward at most `R`, whereas the
date-zero action receives the solo payoff `s`.  Thus

\[
 d_i\le\max\{0,L-V_0\}
      \le2Rh_0+(R-s)h_1.
 \tag{8}
\]

Finally, (6) and `U_i>=V_N` give

\[
 d_i\le as.
 \tag{9}
\]

If `R=0`, the result is immediate.  Otherwise put `delta=d_i/R`.  From
(7)--(9),

\[
 \delta\le ax,
 \qquad
 \delta\le2h_1,
 \qquad
 \delta\le2h_0+(1-x)h_1.
 \tag{10}
\]

If `delta=0`, there is nothing to prove.  Otherwise

\[
 a\ge\frac\delta x,
 \qquad
 h_1\ge\frac\delta2.
\]

Using `h_0=1-a-h_1` in the third inequality of (10),

\[
 \delta
 \le2(1-a-h_1)+(1-x)h_1
 \le2-\frac{2\delta}{x}-\frac{1+x}{2}\delta.
\]

Consequently

\[
 \delta\le\frac{4x}{x^2+3x+4}\le\frac12,
 \tag{11}
\]

where the last inequality is equivalent to
`0 <= (1-x)(4-x)`.  This proves (1).

For (2), the literal two-date profile belongs to every `A_(K_m)`.  Replace
its semantic pair `(U,B)` by the diagonal midpoint

\[
 z_{U_i}=z_{B_i}=\frac{U_i+B_i}{2}.
\]

Then `F(z)=0` and

\[
 \|z-(U,B)\|_\infty
 =\frac12\max_i(B_i-U_i)\le\frac14.
\]

For Fin4, `delta_m=12/m`, which is at least `1/4` for every `m<=48`.
The same actual center therefore witnesses `z in R_M(r)` and proves
`L_M(r)=0` through level `48`.

## Sharp rational Fin4 regression

Take active players `1,2` and dummy players `3,4`.  For a nonempty coalition
`S`, define the active rewards from `S intersection {1,2}` by

\[
\begin{array}{c|rrrr}
S\cap\{1,2\}&\varnothing&\{1\}&\{2\}&\{1,2\}\\ \hline
r_1(S)&0&1&1&-1\\
r_2(S)&0&-1&-1&1.
\end{array}
\tag{12}
\]

For a dummy `d`, put `r_d(S)=-1` when `d in S` and zero otherwise.  Every
reward lies in `[-1,1]`.

We first justify elimination of the dummies in every equilibrium.  A dummy
cannot use time zero: it then belongs to the first quitting coalition surely
and receives `-1`, whereas Never guarantees zero.  Neither active player can
Quit surely at time zero.  If player 1 does so, player 2 uniquely joins,
after which player 1 strictly prefers a later action.  If player 2 is sure at
zero, player 1 strictly chooses later; player 2 then improves either by Never
when player 1 has positive Never mass or by joining player 1 at date one when
player 1 is sure there.  Hence both active players Continue at date zero with
positive probability.  A dummy choosing date one then has positive
probability of belonging to the first coalition and a strictly negative
expected payoff, while Never gives zero.  Thus both dummies uniquely choose
Never.  This is an equilibrium argument; date one is not globally strictly
dominated when it is surely preempted.

Against player 2's actions `(0,1,Never)`, player 1's matrix is

\[
 A=\begin{pmatrix}
 -1&1&1\\
 1&-1&1\\
 1&1&0
 \end{pmatrix},
 \tag{13}
\]

and player 2's payoff is `-A`.  The unique minimax law of each player is

\[
 (1/4,1/4,1/2),
 \tag{14}
\]

with value `1/2`.  Indeed, for a row law `(x_0,x_1,x_N)`, the three pure
column values are

\[
 1-2x_0,
 \qquad
 1-2x_1,
 \qquad
 1-x_N.
\]

Their minimum is at most `1/2`; otherwise the three probabilities would sum
to less than one.  Equality forces (14).  The column argument is identical.

At the literal equilibrium profile, player 1's prescribed payoff is `1/2`.
Quitting at any time `t>=2` pays one on every opponent plan: if player 2 chose
a finite time, it exits alone before `t`; if it chose Never, player 1 exits
alone.  Hence player 1's debt is exactly `1/2`.  Player 2 has no profitable
late deviation and the dummies have zero debt.  This proves sharpness.

## Boundary tests

- The proof uses no division by a stopping probability and covers pure,
  partially mixed, and fully mixed Nash equilibria.
- `a=0`, `a=1`, `h_0=0`, or `h_1=0` cause no conditioning problem.
- If `s<=0`, late Quit cannot beat Never; if `R=0`, all debts vanish.
- Zero-probability terminal cells and exact Never atoms are retained.
- The sharpness proof explicitly handles possible off-path dummy times rather
  than claiming global strict dominance.
- The `R/2` constant is sharp for the exact three-action architecture, but no
  claim is made about approximate timing Nash, soft tails, or non-Nash
  selections.
- The result is consistent with the separate hard-deadline example whose
  exact timing Nash debts converge to `1/4` rather than zero.

## Adapter and consumer

The arbitrary source is any bounded finite reward table.  Finite-game Nash
existence produces the timing law; the standard hazard representation gives
a literal product behavioral profile.  Equations (4)--(5) and the checked
pure-time extremality theorem upgrade the finite Nash inequalities to the
complete behavioral cap.

The immediate semantic output is an actual terminal `(R/2)`-Nash profile.
The escape-aware hierarchy consumes its actual semantic pair and proves the
universal zero lower certificate (2).  This is a finite quantitative producer
and an exact early-level hierarchy obstruction, not a uniform-payoff
consumer.

## Lean handoff

A narrow implementation should:

1. define the finite three-action timing game and select a mixed Nash;
2. realize its product law by a two-date behavioral profile with exact Never;
3. prove the pure-time values `V_0,V_1,V_N,L` and the three positive-part
   inequalities (6)--(9);
4. formalize the scalar inequality (11) and combine it with
   `sSup_range_quittingTerminalPayoff_update_eq_pureTime`;
5. separately formalize the rational Fin4 sharpness table as a regression;
6. package the actual center and its diagonal midpoint for the hierarchy,
   retaining `HasEscapeAwareQuantileClockCompression reward` if required by
   the current checked bracket API.

The theorem may return the selected timing law together with its literal
behavioral profile, rather than introduce a new profile predicate.  The
sharpness table should prove equilibrium uniqueness before eliminating dummy
times.

## Scope and nonclaims

The theorem does not produce arbitrarily small terminal errors, a uniform-
equilibrium payoff, or a positive terminal gap.  It does not justify
induction in the number of hard dates, and it gives no positive hierarchy
lower bound beyond its own level-`48` certificate.  The separately reviewed
general-`K` theorem improves the finite cutoff to `59` but converges only to a
quarter bound.  The independently reviewed hard-deadline example shows that
exact re-Nashification at longer deadlines can remain bounded away from zero;
the constructive route must allow a different tail or selection mechanism.

## Formalization record

The packet is formalized at its full corrected scope in three checked modules.

- `UniformEquilibrium/Diagnostics/Quitting/TwoDateTimingNashDebt.lean`
  constructs a mixed Nash law for the complete `{0,1,Never}` timing game,
  realizes it as a literal behavioral profile, proves the data-sensitive
  all-behavior debt estimate, and proves
  `exists_twoDateTimingNash_terminalDebt_le_half`.
- `UniformEquilibrium/Diagnostics/Quitting/TwoDateTimingNashSharpness.lean`
  defines the normalized rational Fin4 sharp table, proves
  `equilibriumProfile_isUniqueNash`, and proves the exact unrestricted debt
  identity `equilibriumProfile_terminalDeviationDebt_zero_eq_half`.
- `Research/Quitting/FiniteDeadlineTimingNashDebtHierarchy.lean` proves the
  actual-center hierarchy consumer and the normalized Fin4 level-`48`
  theorem
  `escapeAwareQuantileClockLower_finFour_eq_zero_of_le_fortyEight`.

Evidence seals are `M`, `L`, `A`, and `C`: both independent reviews passed;
Lean checks the universal bound and the exact equality regression; the source
is an arbitrary bounded finite reward table together with a selected finite
mixed Nash law; and its literal stopping-law semantic pair is consumed by the
finite-clock hierarchy.

The sharp table is distinct from the fixed-prefix table used by the later
tail barrier.  No vanishing-error family, uniform-equilibrium payoff, positive
hierarchy lower bound, or inductive hard-deadline improvement is claimed.
