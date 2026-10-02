# Four-clock guards renew full screening, but do not create admissible charge

Author: `CODEX_ROOT`

## Status

Audit of a supplied ordinary-mathematics argument.  Research note, not checked
in Lean and not an export claim.

The four-clock guard contains a potentially important producer lemma: on
`Fin 4`, full screening survives an arbitrary complete unilateral strategy
replacement because the other three private guard clocks remain, and every
deleted profile still sees at least two of them.  Combined with the exact
prefix-debt ledger, this renewably produces a fixed-gain *behavioral
better-reply macro-edge*.

The proposed conclusion that compact recurrence yields a positive cumulative
admissible-payoff return is not justified.  A profitable whole-strategy move,
or its stopping-law decomposition into pure-time payoff differences, is not an
exact Nash--Bellman punishment-floor path.  Moreover, the checked cumulative
near-return compiler charges edges by root absorption mass, not by unilateral
payoff gain.  The argument therefore solves a screening/restart problem but
not the chronology consumer.

## 1. Valid guard and seam calculation

Let rewards be bounded in absolute value by `R`.  For `0<eta<1`, use four
successive rows, with player `j` quitting with probability `1-eta` at row `j`
and every other player continuing.  Then

\[
 c(G_\eta)=\eta^4,
 \qquad H_i(G_\eta)=\eta^3.
\]

For a finite prefix word `A` and arbitrary continuations `T,T'`, direct
coupling gives

\[
 |U_j(A*T)-U_j(A*T')|\le 2R c(A),
\]

and, uniformly over the complete behavioral deviation class,

\[
 |B_j(A*T)-B_j(A*T')|\le 2R H_j(A).
\]

The same bounds hold for the ordinary law and the `j`-deleted law in total
variation.  Thus inserting a guard after a prefix with `c(A)->0` and
`H_j(A)->0` for every `j` is a full-semantic null seam.

The globally weighted root-defect contribution of the four guard rows is at
most `32 R c(A)`: each of four rows has total root defect at most `8R`, and
the guard is reached with probability `c(A)`.

## 2. Valid extraction of a complete behavioral better reply

Write the coordinate prefix-debt account as

\[
 d_i(A*T)=C_i(A)+c(A)d_i(T),
\]

where `C_i(A)` is the reached sum of player `i`'s nonnegative root defects
against the actual suffix caps.  For a fully screened family `A_n*T_n`, insert
the guard.  Global minimality and the preceding guard bound give, eventually,

\[
 \sum_i C_i(A_n)\ge D_*/2.
\]

After a subsequence, one fixed player has

\[
 C_i(A_n)\ge D_*/8,
 \qquad d_i(A_n*G_{\eta_n}*T_n)\ge D_*/8.
\]

Against fixed opponents, a behavioral strategy is represented by a
subprobability/probability law on `Nat union {infinity}`, and its payoff is the
expectation of the corresponding pure-time values.  Replacing the prescribed
law by an approximately cap-attaining law therefore gives an actual profile
`Y_n`, differing in only player `i`, such that for large `n`

\[
 U_i(Y_n)-U_i(\bar X_n)\ge D_*/16,
 \qquad B_i(Y_n)=B_i(\bar X_n),
 \qquad d_i(Y_n)\longrightarrow0.
\]

This is a genuine complete-behavioral paid macro-edge.  It does not require a
large individual row defect.

## 3. Valid renewable screening

The replacement may change player `i` everywhere, including inside the
guard.  The other three guard coordinates remain unchanged.  Cutting just
after the guard gives

\[
 c(A_n')\le\eta_n^3,
 \qquad H_i(A_n')\le\eta_n^3,
 \qquad H_j(A_n')\le\eta_n^2\quad(j\ne i).
\]

The final inequality is specifically four-player: after deleting `j`, two
guarded players distinct from `i,j` remain.  Hence the target is fully
screened again and can receive another null guard.  Subject to the routine
subsequence bookkeeping, this yields an indefinitely renewable sequence of
actual one-player better-reply macro-edges with a common positive gain floor.

This is the valuable new content.  It directly attacks the known failure of a
complete best reply to preserve the fully screened class.

## 4. First invalid splice: payoff decomposition is not an admissible path

Moving stopping-law mass from a pure time `s` to an approximately optimal
time `theta` gives the exact payoff contribution

\[
 \mu(s)\bigl(V_i(\theta)-V_i(s)\bigr)>0.
\]

The two pure-time strategies have a literal first-disagreement date.  This
does **not** make the difference an
`IsQuittingNashBellmanEdge`:

* exact Nash--Bellman edges require the whole product root to be exact Nash
  against the declared continuation value;
* the displayed inequality certifies only one player's profitable change;
* it supplies no Nash conditions for the other players;
* it supplies no Bellman state equality or punishment-floor inequalities for
  the intermediate state; and
* a stopping law may move mass at infinitely many dates, whereas the checked
  admissible-path object is finite.

Choosing the continuing strategy's literal off-path continuation does not
repair any of these missing conditions.  Likewise, punishment normality and
singleton separation are table/source facts; they do not imply that the new
whole-profile payoff vectors dominate the punishment floor.

The honest output is therefore a paid behavioral macro-edge, perhaps with a
first-disagreement payoff decomposition, not a finite exact
punishment-floor Nash--Bellman path.

## 5. Second invalid splice: the compiler's charge is absorption, not gain

`QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily` requires a path
in `quittingPunishmentFloorAdmissibleChargedRelation`.  By definition, every
edge is an exact Nash--Bellman predecessor edge between floor-admissible boxed
states, and

\[
 \operatorname{charge}(e)
 =\operatorname{quittingRootAbsorptionMass}(e.root).
\]

Consequently `path.chargeSum` is a sum of literal one-stage absorption masses.
It is not the sum of movers' prescribed-payoff improvements.  A lower bound

\[
 \sum_e\bigl(U_{i_e}(target_e)-U_{i_e}(source_e)\bigr)
 \ge D_*/16
\]

does not establish the positive `chargeFloor` consumed by
`quittingGame_exists_uniformEquilibriumPayoff_of_cumulativePayoffNearReturns`.

Compact recurrence of the full semantic packets therefore gives, at most, a
recurrent finite segment of fixed-gain unilateral better replies.  Such
better-reply cycles are possible in finite games and are not themselves a
contradiction or a uniform-equilibrium compiler.

## 6. Exact surviving research question

The useful reduced target is:

\[
\boxed{
\begin{array}{c}
\text{renewable fully screened fixed-gain behavioral macro-edges}\\
\Longrightarrow\\
\text{an exact punishment-floor Nash--Bellman return with positive}\\
\text{absorption charge, or renewable finite-rank descent.}
\end{array}}
\]

Any successful bridge must manufacture the exact root-Nash, Bellman,
punishment-floor, and absorption-charge fields.  Reinterpreting payoff gain as
edge charge is not sufficient.

## 7. Files and declarations inspected

* `exports/FIN4_SATURATED_OFFMIN_ACTUALIZER_AND_SCREENED_CHARGE_LEDGER.md`:
  the existing fully screened aggregate root-defect ledger and its explicit
  nonclaim that it is an admissible payoff return.
* `UniformEquilibrium/Quitting/Bellman/Finite/
  PunishmentFloorAdmissibleChargedRelation.lean`:
  `QuittingPunishmentFloorAdmissibleEdge` and
  `quittingPunishmentFloorAdmissibleChargedRelation`.
* `UniformEquilibrium/Quitting/Projective/CumulativeChargeNearReturn.lean`:
  `QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily` and its
  uniform-payoff consumer.
* `UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`:
  the current paid-first-disagreement producer interface.

## Concrete next check

Stress-test the renewable-guard lemma itself, especially the exact coordinate
prefix-debt account after guard insertion and the diagonal subsequence needed
for arbitrarily many renewals.  Do not attempt the admissible-return splice
without a new exact-edge constructor.
