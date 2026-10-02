# Adversarial review of the complementary-pair boundary consumer

Reviewer: `ATLAS_FALSIFIER`

## Verdict

The document contains two mathematically different claims.

1. The **generic stationary-block theorem is correct**. A full-support
   stationary family whose genuine all-behavior terminal debts tend to zero
   yields a uniform-equilibrium payoff. The stronger unscaled condition
   `|Quit - Never| -> 0` is sufficient. The advertised finite block followed
   by an arbitrary fixed literal tail also works.
2. The **complementary-pair atlas adapter is not produced by the cited
   screen**. The current empty-base screen uses the denominator-cleared active
   residual

   \[
   H_i=a_i(Q_i-N_i),
   \]

   and supplies neither a sequence with unscaled `|Q_i-N_i| -> 0` nor a
   sequence with terminal debt tending to zero. In fact it does not
   unconditionally supply any vanishing-defect sequence at all. The document's
   normalization warning identifies exactly this problem but the application
   section assumes it away.

Moreover, the independently reviewed Fin4 monodromy impossibility theorem
now makes the proposed atlas parent empty. Thus the displayed implication from
`FinFourComplementaryPairMonodromyProducer` is vacuously true, not a new
consumer of a nonempty atlas leaf.

**Overall: do not export this as a complementary-pair consumer.** The generic
block theorem is valid but largely duplicates the existing terminal-to-uniform
selection mechanism; its only extra feature is the optional literal fixed
tail. It becomes conjecture-facing only if a nonvacuous producer of unscaled
stationary debt is supplied.

## 1. Exact generic statement checked

Fix a full-support stationary root `x` and a player `i`. Put

\[
s_i=\prod_{j\ne i}(1-x_j),\qquad a_i=1-s_i>0.
\]

Let `Q_i` be the value of quitting in the current round and let `N_i` be the
value of continuing forever against the stationary opponents. The latter is
the opponents' one-round absorbing reward divided by `a_i`.

Against an arbitrary behavioral strategy of `i`, the opponents' fresh action
at every live date is independent of the deviator's current private coin and
past live history. Opponent absorption occurs almost surely. Conditional on
the terminal mode in which `i` quits, the terminal reward has expectation
`Q_i`; conditional on the mode in which `i` continues and the opponents quit,
it has expectation `N_i`. Hence every behavioral-deviation value is a convex
combination of these two endpoints. Quit now and Never attain them, so

\[
B_i(x_{-i}^{\infty})=\max\{Q_i,N_i\}.
\]

This verifies the unrestricted-strategy step. It does not rely on stationary
or pure-time completeness by assertion; it follows directly from the
memoryless opponent law.

The prescribed stationary payoff `V_i(x)` is itself a convex combination of
the same two endpoints. Therefore

\[
d_i(x)=\max\{Q_i,N_i\}-V_i(x)
       \le |Q_i-N_i|.
\]

No denominator-cleared version of this implication is valid when `a_i` tends
to zero.

## 2. Fixed-tail finite block bounds

Let `sigma[x,L;tau]` play `x` for `L` live dates and then resume an arbitrary
fixed behavioral tail `tau`. Assume rewards are bounded in absolute value by
`M`.

Couple its prescribed play with the infinite stationary profile. The profiles
are identical unless all players Continue through the block, an event of
probability `s(x)^L`. The finite-horizon stationary payoff differs from the
terminal stationary payoff only by the missing pre-absorption portion. The
stationary absorption clock has mean at most `1/a(x)`. Thus, with the harmless
factor `2M`, the claimed bound

\[
|U_i^N(\sigma[x,L;\tau])-V_i(x)|
\le 2M s(x)^L+\frac{2M}{Na(x)}
\]

is valid for `N >= L`.

For deviations, couple only the opponents. Whether every opponent survives
the first `L` dates is independent of the deviator and has probability
`s_i(x)^L`. Under stationary opponents, the terminal time under any deviation
is stochastically bounded by the opponents' geometric absorption clock with
parameter `a_i(x)`. Taking the supremum over all behavioral deviations gives

\[
B_i^N(\sigma[x,L;\tau]_{-i})
\le \max\{Q_i,N_i\}+2M s_i(x)^L+\frac{2M}{Na_i(x)}.
\]

Combining the two estimates using `s <= s_i` and `a >= a_i` proves the stated
regret estimate. The proof remains valid when `tau` has infinite support,
Never mass, or no absorption. The tail is used only on the exponentially small
survival event.

The diagonal quantifiers are also correct. One first selects a stationary
root for the requested accuracy, then its block length, and only then the
horizon threshold. Therefore no uniform lower bound on `a_i(x^m)` is needed.

## 3. Relation to existing generic consumers

Once `d_i(x^m) -> 0` is known and a subsequence of `V(x^m)` converges, the
stationary profiles themselves form terminal Nash approximants against all
behavioral deviations. The checked declarations in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
and
`UniformEquilibrium/Quitting/Classification/LCP/StationaryEquilibrium.lean`
already consume such a fixed-target stationary family. In particular,
`IsQuittingStationaryUniformEquilibriumPayoff.isUniformEquilibriumPayoff` and
`exists_uniformEquilibriumPayoff_of_stationaryFamily` capture the main
conclusion.

The finite-block argument adds the honest but narrower provenance statement
that one may graft the same arbitrary literal tail after the block. It does
not preserve a prescribed root chronology before that tail, and it does not
produce the stationary roots.

## 4. The current empty-base screen has the wrong normalization

The exact checked active residual is defined in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/EmptyBaseSemanticDispatch.lean`:

```text
quittingEmptyBaseActiveResidual
  = (1 - fixedOpponentsContinueMass) * quitValue
      - fixedOpponentsContinueReward.
```

Since

\[
N_i=\frac{\text{fixedOpponentsContinueReward}}{a_i},
\]

this is exactly

\[
H_i=a_i(Q_i-N_i).
\]

For the complementary-pair empty-base geometry all four players are active,
so `quittingEmptyBaseSimplexDefect` is the maximum of `|H_i|`; there are no
passive rows that improve this normalization. The compact-separation theorem
`exists_uniformPayoff_or_emptyBase_noSolution_with_rhoGaps` says:

- either an exact interior solution exists and is already compiled; or
- no exact interior solution exists and every fixed interior `rho`-box has a
  positive lower bound on the scaled defect.

It does **not** construct roots whose scaled defect tends to zero. The later
theorem
`eventually_exists_active_boundary_of_tendsto_emptyBaseDefect_zero` is only a
conditional statement: *if* a vanishing scaled-defect sequence is supplied,
then some active hazard approaches the boundary.

Even adding that missing sequence would not justify the proposed consumer.
The two-player regression in the document is exact: with `Q_i=1`, `N_i=0`,
and symmetric hazards `t`, one has

\[
a_i|Q_i-N_i|=t\to0,
\qquad
d_i=\frac{1-t}{2-t}\to\frac12.
\]

Thus scaled screen convergence cannot be substituted for (1) or (2).

## 5. Failure of the atlas application

The application section says to “use the full-support vanishing-defect repairs
supplied by the screen.” No current declaration inspected supplies such
repairs with semantic debt or unscaled Quit-versus-Never residual tending to
zero. Nor does complementary-pair label geometry convert the scaled residual
into an unscaled one: the boundary arm is precisely where `a_i` may vanish.

Independently, `FIN4_MONODROMY_PRODUCER_IMPOSSIBLE` proves the stronger source
fact that the current `FinFourMonodromyProducer` is empty, hence both its
common-host and complementary-pair wrappers are empty. Accordingly the final
displayed implication is logically true only through an impossible premise.
It should not be advertised as consuming the atlas leaf.

## 6. What would make the generic theorem useful

A nonvacuous adapter would need to produce, from actual game/source data, a
full-support sequence `x^m` satisfying at least one of

\[
\max_i d_i(x^m)\to0,
\qquad
\max_i|Q_i(x^m_{-i})-N_i(x^m_{-i})|\to0.
\]

Equivalently, a scaled screen would need an additional quantitative lower
bound on every deleted-opponent absorption rate on the rows where its
residual is used. The present boundary alternative supplies the opposite:
escape from every fixed interior box.

### Final classification

- **Generic stationary-block mathematics:** PASS.
- **Claimed complementary-pair atlas adapter:** FAIL (missing producer and
  wrong residual normalization; now also vacuous after monodromy exclusion).
- **Independent export value:** insufficient without a nonvacuous source of
  unscaled stationary debt. Retain as a conditional/internal lemma if the
  literal fixed-tail refinement is wanted.

