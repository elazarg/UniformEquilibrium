# Normal unique-persistent Nash--Bellman spines

Authors: GPT; Math Conference synthesis

Independent reviews:

- [`FIN4_SPINE__BY_CODEX_ADVERSARY.md`](../feedback/FIN4_SPINE__BY_CODEX_ADVERSARY.md)
- [`FIN4_SPINE__BY_CODEX_SOURCE_GATE.md`](../feedback/FIN4_SPINE__BY_CODEX_SOURCE_GATE.md)
- [`FIN4_SPINE__BY_CODEX_STRENGTHEN.md`](../feedback/FIN4_SPINE__BY_CODEX_STRENGTHEN.md)
- [`FIN4_SPINE_EXPORT_FINAL_GATE__BY_CODEX_SOURCE_GATE.md`](../feedback/FIN4_SPINE_EXPORT_FINAL_GATE__BY_CODEX_SOURCE_GATE.md)

## Exact statement

Let \(I\) be a finite player set and let

\[
r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow \mathbb R^I
\]

be a bounded quitting reward table.  Let \(v_t\in\mathbb R^I\) and let
\(x_t\) be product roots, for \(t\in\mathbb N\).  Assume that they form a
bounded exact Nash--Bellman spine:

For a product root \(x\) and continuation vector \(w\), \(F_x(w)\) is the
coordinatewise expectation which pays \(r(S)\) when the root's quitting set
is the nonempty set \(S\), and pays \(w\) when every player Continues.
Saying that \(x\) is exact root Nash against \(w\) means that, for every
player \(i\) and every alternative Quit/Continue distribution \(z_i\),
\[
F_x(w)_i\ge F_{x[i\leftarrow z_i]}(w)_i.
\]

1. there is \(K>0\) such that
   \(\lVert v_t\rVert_\infty\le K\) and
   \(\lVert r(S)\rVert_\infty\le K\) for every \(t,S\);
2. \(v_t=F_{x_t}(v_{t+1})\) for every \(t\); and
3. \(x_t\) is an exact product-root Nash equilibrium against continuation
   payoff \(v_{t+1}\).

Write

\[
q_{t,i}:=\Pr_{x_t}(i\text{ Quits}).
\]

Suppose there is a player \(p\in I\) such that

\[
\sum_{t=0}^{\infty}q_{t,p}=\infty,
\qquad
\sum_{t=0}^{\infty}q_{t,j}<\infty
\quad(j\ne p),                                      \tag{1}
\]

and \(p\) is punishment-normal:

\[
\operatorname{Pun}_p(r)\le r_p(\{p\}),              \tag{2}
\]

where \(\operatorname{Pun}_p(r)\) is the infimum, over all behavioral
opponent profiles, of \(p\)'s unrestricted behavioral best-response value.
Then

\[
\boxed{r(\{p\})\text{ is a uniform-equilibrium payoff}.}       \tag{3}
\]

In repository terminology, (1) says that \(p\)'s marginal Quit-hazard stream
is nonsummable and every other marginal Quit-hazard stream is summable.

### Fin4 consequence

If a four-player quitting game has no uniform-equilibrium payoff, then, on
every bounded exact canonical Nash--Bellman spine, every player's marginal
Quit-hazard stream is summable.

Indeed, the checked four-player hard residual makes every player
punishment-normal.  Exactly one nonsummable marginal is therefore excluded by
the theorem above.  Two or more nonsummable marginals contain two fixed
persistent labels on the same spine; the checked two-label survival and
chronological-shadowing compilers then give a uniform-equilibrium payoff.
Thus a hypothetical Fin4 counterexample permits only the zero-persistent
spine alternative.

## Conjecture-facing change

This strictly narrows
[the exact-spine selection question](../questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md):
the spine-selection problem now asks only for one nonsummable marginal stream,
not two.  Exactly one is consumed by the theorem above, while two or more are
consumed by the checked chronological route.  The zero-persistent
all-Continue phantom remains possible, so this is not a proof of the
four-player conjecture.

## Proof

Put

\[
R:=r(\{p\})\in\mathbb R^I,
\quad
s_t:=\sum_{j\ne p}q_{t,j},
\quad
a_t:=\prod_{j\ne p}(1-q_{t,j}),
\quad
c_t:=1-a_t.
\]

Here \(c_t\) is the probability that at least one player other than \(p\)
Quits at root \(x_t\).  The finite union bound gives

\[
0\le c_t\le s_t.
\]

The outsider assumptions in (1) and finiteness of \(I\) therefore imply

\[
\sum_t c_t<\infty.                                  \tag{4}
\]

### 1. The spine values converge to the singleton row

Split the Bellman expectation at date \(t\) according to whether an outsider
Quits.  On the event that no outsider Quits, player \(p\) either Quits and the
payoff is \(R\), or Continues and the payoff is \(v_{t+1}\).  Consequently
there is an unnormalised outsider-event contribution \(G_t\in\mathbb R^I\)
such that

\[
v_t=a_t\bigl((1-q_{t,p})v_{t+1}+q_{t,p}R\bigr)+G_t,
\qquad
\lVert G_t\rVert_\infty\le Kc_t.                    \tag{5}
\]

For \(d_t:=v_t-R\), equation (5) becomes

\[
d_t=a_t(1-q_{t,p})d_{t+1}+e_t,
\qquad
e_t:=G_t-c_tR,
\qquad
\lVert e_t\rVert_\infty\le2Kc_t.                   \tag{6}
\]

Iterating (6) from \(t\) to \(T\) gives

\[
\begin{aligned}
d_t={}&
 \left(\prod_{u=t}^{T-1}a_u(1-q_{u,p})\right)d_T\\
&+\sum_{s=t}^{T-1}
 \left(\prod_{u=t}^{s-1}a_u(1-q_{u,p})\right)e_s.
                                                               \tag{7}
\end{aligned}
\]

For fixed \(t\), the first coefficient satisfies

\[
0\le\prod_{u=t}^{T-1}a_u(1-q_{u,p})
\le\prod_{u=t}^{T-1}(1-q_{u,p})
\le\exp\!\left(-\sum_{u=t}^{T-1}q_{u,p}\right)
\longrightarrow0,                                             \tag{8}
\]

by the nonsummability of \(p\)'s hazard.  Boundedness kills the first term in
(7).  The remaining products are at most one, so (4), (6), and \(T\to\infty\)
give

\[
\boxed{
\lVert v_t-R\rVert_\infty
\le2K\sum_{s=t}^{\infty}c_s
\le2K\sum_{s=t}^{\infty}s_s.}                       \tag{9}
\]

In particular,

\[
v_t\longrightarrow R.                              \tag{10}
\]

### 2. Late rows give solo roots with vanishing outsider cap error

There are arbitrarily late \(t\) with \(q_{t,p}>0\).  At each such \(t\),
form a solo root \(y_t\) by retaining \(p\)'s marginal from \(x_t\) and making
every other player Continue surely.

Fix \(i\ne p\).  If \(i\) Quits immediately against \(y_t\), its payoff is

\[
A_{t,i}:=(1-q_{t,p})r_i(\{i\})
          +q_{t,p}r_i(\{i,p\}).                     \tag{11}
\]

Exact root Nash at \(x_t\), tested against \(i\)'s pure-Quit deviation, and
the Bellman identity give

\[
U_i(x_t[i\leftarrow Q];v_{t+1})\le v_{t,i}.          \tag{12}
\]

Couple \(x_t[i\leftarrow Q]\) with \(y_t[i\leftarrow Q]\), keeping the
actions of \(p\) and the forced-Quit action of \(i\) identical.  Their
terminal outcomes can differ only when some \(j\notin\{p,i\}\) Quits.  This
event has probability at most \(s_t\), and two terminal rewards differ by at
most \(2K\).  Hence

\[
A_{t,i}\le v_{t,i}+2Ks_t
          \le R_i+\eta_t,
\quad
\eta_t:=\lVert v_t-R\rVert_\infty+2Ks_t\longrightarrow0.       \tag{13}
\]

Repeat \(y_t\) stationarily forever.  Since \(q_{t,p}>0\), \(p\) eventually
Quits almost surely.  Against these stationary opponents, every behavioral
strategy of \(i\) induces a stopping time in
\(\mathbb N\cup\{\infty\}\).  Never gives \(R_i\); quitting at a finite date
gives a convex combination of \(R_i\) and \(A_{t,i}\).  Conversely, Never and
immediate Quit attain those endpoints.  Thus the unrestricted behavioral cap
is exactly

\[
B_i(y_t^\infty)=\max\{R_i,A_{t,i}\}\le R_i+\eta_t.   \tag{14}
\]

This is an all-behavior cap statement, not merely a stationary- or
one-stage-deviation calculation.

Choose a strictly increasing sequence \(t_n\to\infty\) with
\(q_{t_n,p}>0\).  Let \(h_n\) be \(p\)'s hazard at \(t_n\) and set
\(\epsilon_n:=\eta_{t_n}\).  Equations (13)--(14) give positive solo hazards,
nonnegative errors \(\epsilon_n\to0\), and

\[
B_i(\operatorname{Solo}(p,h_n)^\infty)
\le R_i+\epsilon_n
\quad(i\ne p).                                      \tag{15}
\]

### 3. Punishment completion fixes the target \(R\)

For completeness, fix an accuracy \(\varepsilon>0\).  Choose \(n\) so large
that \(\epsilon_n<\varepsilon/3\), and write \(q=h_n(Q)>0\).  By (2) and the
definition of the punishment infimum, for every \(\delta>0\) there is an
actual opponent punishment profile \(\pi\) such that

\[
B_p(\pi)\le\operatorname{Pun}_p(r)+\delta
          \le R_p+\delta.                            \tag{16}
\]

Choose \(0<\delta<\varepsilon/3\), and then choose \(N\) so large that, for
\(\rho:=(1-q)^N\),

\[
4K\rho<\varepsilon/3.                                \tag{17}
\]

Let \(\sigma\) repeat the solo root \(\operatorname{Solo}(p,h_n)\) for \(N\)
live dates and, conditional on survival, switch to \(\pi\).

If \(p\) Quits in the prefix, the terminal coalition is \(\{p\}\).  Only the
event of reaching \(\pi\), of probability \(\rho\), can change the prescribed
payoff.  Therefore

\[
\lVert U(\sigma)-R\rVert_\infty\le2K\rho.            \tag{18}
\]

For an arbitrary behavioral deviation by \(i\ne p\), compare the finite
prefix with the infinite solo profile.  The two environments differ only if
\(p\) survives the prefix, an event of probability \(\rho\) independently of
\(i\)'s behavior.  Equations (15) and (18) imply

\[
U_i(\sigma[i\leftarrow\tau_i])-U_i(\sigma)
\le\epsilon_n+4K\rho<2\varepsilon/3.                 \tag{19}
\]

For an arbitrary behavioral deviation by \(p\), quitting during the prefix
gives \(R_p\), while reaching the tail gives at most \(R_p+\delta\) by (16).
Thus

\[
U_p(\sigma[p\leftarrow\tau_p])-U_p(\sigma)
\le\delta+2K\rho<\varepsilon/2.                      \tag{20}
\]

This includes Never and arbitrarily late randomized stopping.  Equations
(18)--(20) give terminal approximate Nash profiles at every positive error
whose prescribed terminal payoffs converge to the one fixed target \(R\).
The fixed-target terminal-to-uniform theorem proves (3).

## Semantic audit

- A root is an independent product distribution on the players' Quit/Continue
  actions at the unique live public history.  Equations (5), (11), and (12)
  use that product law and no correlated device.
- A unilateral deviation replaces one player's complete behavioral strategy.
  Before absorption, every public history is a string of all-Continue
  outcomes, so such a strategy is equivalently a possibly randomized,
  time-dependent stopping law on \(\mathbb N\cup\{\infty\}\).  The cap in
  (14), the punishment cap in (16), and inequalities (19)--(20) quantify over
  this entire class.
- Terminal payoff is the expected reward of the first nonempty quitting
  coalition, with the repository's zero payoff on nonabsorption.  The
  constructed positive solo hazard absorbs almost surely before infinity in
  the infinite comparison profile.  The finite-prefix profile may reach its
  punishment tail, which is an actual behavioral profile rather than a
  declared continuation vector.
- The coupling in (13) changes only the nonowner root marginals and charges
  the full bounded payoff oscillation on the event that one of those
  marginals Quits.  The coupling in (19) changes only what follows the finite
  solo prefix and charges the event that \(p\) survives that prefix.
- The target \(R=r(\{p\})\) is selected before the requested accuracy.
  The positive-hazard date, punishment slack, prefix length, and behavioral
  profile may depend on the accuracy.  The fixed-target terminal consumer
  converts these terminal statements to one profile for every accuracy that
  works at every sufficiently late finite horizon.

## Source correspondence

The following declarations were checked against the proof.

- `IsCanonicalExactQuittingNashBellmanSpine` in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanClockReduction.lean`
  is the canonical exact bounded spine interface.
- `quittingMarginalQuitHazard`,
  `HasTwoPersistentQuittingMarginals.survival`, and
  `hasTwoPersistentQuittingMarginals_iff_all_suffix_survival_zero` in
  `UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean`
  provide the marginal and two-label vocabulary.
- `quittingStationaryUnilateralCap_solo_other` in
  `UniformEquilibrium/Quitting/Boundary/Exceptional/TailFallback.lean` and
  `quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix` in
  `UniformEquilibrium/Quitting/Stationary/SingletonStationaryRoot.lean`
  are the checked form of (11) and (14).
- `quittingBestReplyValue_stationary` and
  `quittingPunishmentValue_eq_stationaryPunishmentValue` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean` retain the full
  behavioral deviation class.
- `exists_stationaryRoot_cap_lt_punishmentValue_add` in
  `UniformEquilibrium/Quitting/Paths/SupportWitnessIndividualRational.lean`
  supplies an actual punishment at every positive slack.
- `isUniformEquilibriumPayoff_soloReward_of_approximate_caps` in
  `UniformEquilibrium/Quitting/Punishment/ApproximateCompletedCycle.lean`
  is the direct checked fixed-target consumer for (15) and (2).  The weaker
  `quittingStationarilyGeneratedApproximateEquilibria_of_approximate_solo_caps`
  implements the same finite-prefix strategy but forgets the target and must
  not be cited by itself for the boxed payoff identity.
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget`
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean`
  is the alternative direct consumer of (18)--(20).
- `nonempty_quittingChronologicalDebtShadowingCertificate_of_exactSpine` in
  `UniformEquilibrium/Quitting/Debt/Dynamic/NashBellmanChronologicalForcing.lean`
  and
  `quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors`
  in
  `UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean`
  consume the already checked two-persistent branch.
- `FinFourQuantitativeFullSupportHardResidual.all_punishmentNormal` and
  `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`
  provide the same-table Fin4 adapter.

The new mathematical content is the spine-to-singleton estimate (9), the
source-faithful solo cap estimate (13)--(15), and their composition with the
fixed-target punishment consumer.

IsQuittingNormalPlayer is defined in
UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean; after
unfolding quittingSoloSelfPayoff, it is exactly (2).

No result from an external paper is invoked.  This packet was audited against
the project declarations above rather than inferred from a literature claim.
The closest existing positive theorem,
isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits in
UniformEquilibrium/Quitting/Cycles/ConditionedDeletedClockSoloCompletion.lean,
consumes already-supplied vanishing deleted hazards, convergence to a
singleton target, and pure-Quit endpoint control.  It does not derive those
fields from an exact one-persistent Nash--Bellman spine.  Conversely,
IsCanonicalExactQuittingNashBellmanSpine.exists_tendsto_value_of_summableClock
in
UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanValueConvergence.lean
proves coordinatewise value convergence from a summable opponent clock, but
does not identify the limit as \(r(\{p\})\) or supply punishment completion.
The explicit obstruction in
UniformEquilibrium/Quitting/Paths/OneOwnerPersistentLabelObstruction.lean
refutes an unconditional two-label selector on a solved table; it does not
give the normal unique-persistent positive consumer proved here.  These
comparisons rule out a duplicate or weakened restatement.

## Boundary tests

### Normality is necessary

Take the one-player quitting game with

\[
r_p(\{p\})=-1.
\]

Let \(v_t=-1\) and let \(p\) Quit with probability \(1/2\) at every root.
Quit and Continue both have value \(-1\), so this is a bounded exact
one-persistent Nash--Bellman spine.  However, Never gives \(0\), and

\[
\operatorname{Pun}_p(r)=0>-1=r_p(\{p\}).
\]

The target \(-1\) is not a uniform-equilibrium payoff.  This falsifies the
theorem with punishment-normality deleted and shows why an actual punishment
tail is necessary when the singleton payoff is negative.

### The positive one-player boundary

For the one-player game with \(r_p(\{p\})=1\), the same constant spine is
normal, and the theorem returns the exact Quit payoff \(1\).  This checks the
degenerate finite-player boundary without using an outsider.

### Zero persistence is not consumed

The canonical constant all-Continue spine has every marginal hazard equal to
zero in every quitting game.  Its existence is checked by
`canonicalPhantom_isExactQuittingNashBellmanSpine`.  The theorem neither
excludes nor consumes it.

## Lean handoff

The main declaration should specialize to the repository's canonical spine
and use `Summable`/`¬ Summable`, rather than an extended-real series:

```text
theorem isUniformEquilibriumPayoff_soloReward_of_uniquePersistent_exactSpine
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (hpersistent : ¬ Summable (quittingMarginalQuitHazard roots owner))
    (hothers : ∀ other, other ≠ owner →
      Summable (quittingMarginalQuitHazard roots other))
    (hnormal : IsQuittingNormalPlayer reward owner) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner)
```

A second declaration should record the direct hard-residual consequence:

```text
theorem FinFourQuantitativeFullSupportHardResidual.all_marginalHazards_summable
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots) :
    ∀ owner, Summable (quittingMarginalQuitHazard roots owner)
```

The local proof obligations are:

1. the vector Bellman decomposition and tail estimate (9);
2. extraction of an increasing sequence of positive owner-hazard dates;
3. the pure-Quit comparison and coupling estimate (13); and
4. instantiation of
   `isUniformEquilibriumPayoff_soloReward_of_approximate_caps`.

The Fin4 corollary then uses the existing two-persistent survival adapter and
chronological consumer.  No new compact carrier, law, or stopping-time type is
needed.

## Scope and nonclaims

- This does not select a spine with a nonsummable marginal.
- It does not consume the zero-persistent all-Continue phantom.
- It does not prove the four-player conjecture.
- It does not claim that the original one-persistent spine itself is a
  terminal or uniform equilibrium.
- It does not replace unrestricted behavioral caps by stationary deviations;
  stationarity is used only for the constructed solo environment, whose cap
  is proved against all behavioral deviations.
- It does not assert attainment of the punishment infimum.

## Lean formalization record

Pre-formalization packet SHA-256:
`41bf52b26e3e44853ff5636f9bec619f4ed73806efa9ea547ce1edac9955bcef`.
The implementation landed in commit
`a0842d13cbe2c1b2854ef4fb4e671b3970d1f089`.

The generic compiler is in
`UniformEquilibrium/Quitting/Classification/Existence/NormalUniquePersistentNashBellmanSpine.lean`;
the Fin4 hard-residual companion is in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardNashBellmanSpine.lean`.
The principal declarations are
`abs_value_sub_soloReward_le_of_bounded_bellman`,
`IsCanonicalExactQuittingNashBellmanSpine.abs_value_sub_soloReward_le`,
`IsCanonicalExactQuittingNashBellmanSpine.tendsto_value_soloReward`,
`IsCanonicalExactQuittingNashBellmanSpine.isUniformEquilibriumPayoff_soloReward_of_persistent`,
`IsCanonicalExactQuittingNashBellmanSpine.isUniformEquilibriumPayoff_soloReward_of_uniquePersistent`,
`FinFourQuantitativeFullSupportHardResidual.all_marginalQuitHazards_summable`,
and `all_marginalQuitHazards_summable_of_no_uniformPayoff`.

Evidence seals are `M` and `L`, with a conditional `C` for a supplied
canonical exact spine.  There is no source `A` selecting such a spine or its
unique-persistent branch.  The result does not consume the zero-persistent
all-Continue phantom, resolve the hard residual or Fin4 conjecture, weaken
normality, replace unrestricted behavioral caps by stationary deviations, or
assert attainment of the punishment infimum.
