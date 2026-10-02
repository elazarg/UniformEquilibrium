# Fin5 quiet whole-law interpolation connects a frozen atom to the omitted-player paid gap

**Author:** CODEX_EULER  
**Status (2026-08-25):** independently reviewed **PASS** as ordinary
mathematics; internal only because event/paid-row alignment and a maintained
Bellman or rank consumer remain absent.  Review:
[`CODEX_EULER__FIN5_QUIET_WHOLE_LAW_ATOM_PAID_CONNECTOR__BY_CODEX_RAMSEY.md`](../feedback/CODEX_EULER__FIN5_QUIET_WHOLE_LAW_ATOM_PAID_CONNECTOR__BY_CODEX_RAMSEY.md).

## 1. Result

Fix a five-player quitting table with terminal exploitability gap
`Gamma>0`, fix an omitted player `w`, and let the other four players be the
survivors.  Suppose:

- `y` is an actual ambient profile with `w` literal Never;
- the survivor law inherited from `y` has a positive chronological atom of
  mass `m` at some finite date and nonempty survivor coalition;
- `sigma` is a terminal `epsilon`-Nash profile of the four-player deleted
  game, with `0<epsilon<Gamma`; and
- `R=quittingRewardBound reward`.

Mix, independently for each survivor, its complete stopping law in the
restricted profile inherited from `y` with its complete stopping law in
`sigma`.  Give the frozen source law weight

\[
 \delta=\frac{\Gamma-\epsilon}{28R},                \tag{1.1}
\]

and the internally stable law weight `1-delta`, then quietly lift the mixed
four-player profile by keeping `w` Never.  The resulting literal ambient
profile `z_delta` simultaneously satisfies:

1. every survivor has unrestricted terminal-semantic debt at most

   \[
   \epsilon+14R\delta=\frac{\Gamma+\epsilon}{2}<\Gamma; \tag{1.2}
   \]

2. the omitted player has debt at least `Gamma` and has a finite pure-time
   deviation of gain at least `Gamma`;
3. the paid first-disagreement decoder gives a full-gap paid row on the same
   literal profile `z_delta`, with observer exactly `w`; and
4. the frozen chronological atom survives at the same date and coalition
   with mass at least

   \[
   \delta^4m>0.                                     \tag{1.3}
   \]

If the atom at `y` arose from the reviewed Fin5 two-reset/erase construction,
so that

\[
 \tfrac14m_{x_0}(t,T)\le m_y(t,T\setminus\{w\}),
\]

then `z_delta` carries that erased atom with mass at least

\[
 \frac{\delta^4}{4}m_{x_0}(t,T).                    \tag{1.4}
\]

Thus whole-law interpolation defeats the bare source-separation obstruction:
it produces one actual profile carrying both a quantified fraction of the
frozen atom and a source-matched full-gap paid row for the preselected omitted
player.  It does not identify the paid first-disagreement cylinder with the
retained atom or preserve a static toggle sign.

## 2. Sources and precise construction

The checked ingredients inspected are:

- `quittingStoppingLawMixtureBehaviorStrategy` and
  `quittingBehaviorStoppingLaw_stoppingLawMixture` in
  `UniformEquilibrium/Quitting/Paths/StoppingLawMixture.lean`;
- `quittingTerminalPayoff_update_stoppingLawMixture_eq` in the same file;
- the product/live-root payoff representation and pure-time extremality in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`;
- `quittingLiftDeletedProfile`, survivor payoff/cap naturality, and literal
  Never in
  `UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean`;
- `quittingStageCoalitionMass_update_eq_opponentFactor_mul` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawMixture.lean`;
- `one_sub_mul_stageCoalitionMass_le_stoppingLawMixture` in that same file,
  which is the one-coordinate chronological retention inequality iterated in
  Section 5;
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
  and
- `terminalExploitabilityGap_le_two_mul_bound` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/NormalTerminalGapConstrainedStationary.lean`,
  together with the canonical bound in
  `UniformEquilibrium/Quitting/RewardBound.lean`.

Let `Iminus=QuittingDeletedPlayer w`.  As in
[`CODEX_EULER__FIN5_RESTRICTED_EQUILIBRIUM_FROZEN_SOURCE_SEPARATION.md`](CODEX_EULER__FIN5_RESTRICTED_EQUILIBRIUM_FROZEN_SOURCE_SEPARATION.md),
form a reduced profile `eta` from the survivor live roots of `y`.  Its quiet
lift is terminal/live-root equivalent to `y`.

For each survivor `i`, define

```text
xi_delta(i) = quittingStoppingLawMixtureBehaviorStrategy
  rewardMinus i (eta i) (sigma i) (1-delta).
```

The checked mixture-law theorem says that its complete stopping law is

\[
 \mu_i^\delta=\delta\mu_i^\eta+(1-\delta)\mu_i^\sigma. \tag{2.1}
\]

Finally set

```text
z_delta = quittingLiftDeletedProfile reward (fun i => i=w) xi_delta.
```

This construction uses independent behavioral strategies.  Equation (2.1)
may be realized for estimates by an independent private initial selector for
each survivor.  No public correlation is inserted into the game.

The terminal-gap bound `Gamma<=2R` and `epsilon>0` imply `R>0` and

\[
 0<\delta<1/14<1,                                   \tag{2.2}
\]

so every mixture is well typed.

## 3. Uniform coupling lemma

### Lemma 3.1 (payoff and cap Lipschitz bounds)

Let `p` and `q` be two four-player behavioral profiles.  Suppose each
player's complete stopping laws admit a coupling with mismatch probability at
most `theta`.  If every reward coordinate has absolute value at most `R`,
then for each player `i`,

\[
 |U_i(p)-U_i(q)|\le 8R\theta,                       \tag{3.1}
\]

\[
 |B_i(p)-B_i(q)|\le 6R\theta,                       \tag{3.2}
\]

and hence

\[
 d_i(p)\le d_i(q)+14R\theta.                        \tag{3.3}
\]

These bounds remain true after quiet lift to the five-player table for a
surviving coordinate.

#### Proof

Couple the four prescribed stopping laws coordinatewise.  The two terminal
outcomes agree unless at least one coordinate mismatches, an event of
probability at most `4 theta`.  Two bounded terminal payoffs differ by at
most `2R`, so (3.1) follows.

For a fixed arbitrary behavioral deviation of player `i`, its own law is the
same in the two comparisons.  Only the other three survivor laws can
mismatch, with probability at most `3 theta`; hence the deviation payoffs
differ by at most `6R theta`.  The estimate is uniform over all unrestricted
behavioral deviations.  Taking suprema in both directions proves (3.2).
Combining the upper cap bound with the lower prescribed-payoff bound gives
(3.3).  Quiet deletion-lift naturality identifies both quantities exactly
with their ambient surviving coordinates.  QED.

For (2.1), couple `mu_i^delta` to `mu_i^sigma` by choosing the target law
with probability `1-delta` and the source law with probability `delta`.
The mismatch probability is at most `delta`, even if the two component laws
are mutually singular.  Lemma 3.1 therefore applies with `theta=delta`.

## 4. Survivor stability and witness localization

Because `sigma` is terminal `epsilon`-Nash, every survivor debt at `sigma` is
at most `epsilon`.  Equations (3.3) and (1.1) give

\[
 d_i(z_\delta)\le\epsilon+14R\delta
 =\frac{\Gamma+\epsilon}{2}<\Gamma.                 \tag{4.1}
\]

Apply `HasTerminalExploitabilityGap reward Gamma` at the actual profile
`z_delta`.  Its selected behavioral deviation has gain at least `Gamma`, so
the selected player's unrestricted debt is at least `Gamma`.  Bound (4.1)
excludes every survivor.  The only remaining player is `w`; hence

\[
 d_w(z_\delta)\ge\Gamma.                            \tag{4.2}
\]

This is the key point at which witness switching is prevented quantitatively,
rather than assumed away.

The quiet lift makes `w` literal Never.  Disintegrate the selected deviation
over its complete stopping law on `Option Nat`.  Never equals the baseline.
The countable strict-average argument therefore produces a finite pure time
whose gain is at least the full weak gap `Gamma`; otherwise every support atom
would lie strictly below the selected expected gain.  Apply the checked paid
first-disagreement decoder.  Its receiving profile is exactly `z_delta` and
its observer is exactly `w`.

## 5. Atom retention

Let the source reduced profile `eta` have chronological atom `(t,S)` of mass
`m`, where `S` is nonempty.  Expand the four independent affine stopping laws
(2.1).  One nonnegative term is the branch in which all four private selectors
choose their source components.  Its coefficient is `delta^4`, and conditional
on that branch the joint stopping law is exactly the law of `eta`.  Therefore

\[
 m_{\xi_\delta}(t,S)\ge\delta^4m_\eta(t,S).          \tag{5.1}
\]

Quiet lifting leaves every chronological survivor atom unchanged, proving
(1.3).  Composing with the reviewed erase-`w` quarter retention proves
(1.4).

This proof uses a lower bound on one term of a finite multilinear expansion.
It does not assert that the joint outcome law is the convex combination
`delta law(eta)+(1-delta) law(sigma)`; cross-component terms are also present.

## 6. General `k`-survivor form

The same argument with `k` survivors gives

\[
 |U_i(p)-U_i(q)|\le2Rk\theta,
 \qquad
 |B_i(p)-B_i(q)|\le2R(k-1)\theta,                  \tag{6.1}
\]

\[
 d_i(p)\le d_i(q)+2R(2k-1)\theta,                  \tag{6.2}
\]

and retains each source atom with factor `theta^k`.  For `k=4`, (6.2) is the
constant `14R` used above.  The omitted-player witness is localized whenever

\[
 \epsilon+2R(2k-1)\theta<\Gamma.                   \tag{6.3}
\]

The Fin5 choice (1.1) spends half the available margin and is deliberately
coarse rather than sharp.

## 7. Boundary tests

1. **Singular component laws.**  The coupling bounds do not require common
   support.  A mixture law differs from its target component only on the
   source-selector branch, of probability `delta`.
2. **Never and escaping clocks.**  `Option Nat` includes Never.  Total
   variation of the affine complete stopping laws is controlled even when
   mass moves between finite times and Never, avoiding weak-topology
   discontinuity.
3. **Witness switching outside the margin.**  If
   `epsilon+14R delta>=Gamma`, the proof no longer excludes a survivor as the
   ambient gap witness.  No continuity argument alone selects `w` there.
4. **Vanishing source weight.**  As `epsilon` approaches `Gamma`, the retained
   fraction `delta^4` tends to zero.  A uniform positive atom bound requires a
   fixed error margin, for example `epsilon=Gamma/2`.
5. **Fixed quantitative choice.**  With `epsilon=Gamma/2`,

   \[
   \delta=\Gamma/(56R),\qquad
   d_i(z_\delta)\le3\Gamma/4,
   \]

   and a quarter-retained source atom survives with factor
   `Gamma^4/[4(56R)^4]`.
6. **No correlated-profile shortcut.**  Mixing the two entire joint laws with
   a public coin would retain source mass linearly in `delta`, but is not an
   ordinary behavioral profile of the quitting game.  The legal independent
   construction costs the fourth power.

## 8. Conjecture-facing consequence and nonclaims

For a cardinal-minimal Fin5 counterexample, choose `sigma` from the checked
four-player uniform-payoff theorem at any `epsilon<Gamma`, for instance
`epsilon=Gamma/2`.  Starting from any literal Never endpoint with a retained
nonempty survivor atom, the theorem produces one actual same-table profile
with:

- a quantitative copy of that atom;
- all four survivor debts strictly below the ambient gap;
- omitted-player debt at least the full gap;
- a finite paid row with observer equal to the omitted player; and
- entry into the checked actual-profile paid-cap trichotomy after adjoining a
  positive global semantic-debt minimum.

This is a genuine connector across the source separation in the preceding
note.  It does **not** prove:

- that the retained atom carries the old coalition-toggle sign after erasure;
- that the paid first-disagreement cylinder is the retained atom;
- a floor-admissible prescribed-payoff Bellman edge;
- elimination of the paid-cap inert stall;
- preservation of a minimum-fiber rank; or
- a uniform-equilibrium payoff.

The remaining interface is no longer mere source coincidence.  It is the
event-alignment problem between the quantitatively retained atom and the
source-matched paid cylinder, or an additional consumer of their simultaneous
presence.

## 9. Lean handoff and review request

A narrow Lean implementation should first prove a complete-stopping-law
coupling/TV lemma for independently mixed profiles, then the payoff/cap bounds
(6.1).  A separate finite-product lemma should lower-bound a chronological
atom under coordinatewise stopping-law mixtures by `theta^k` times its source
mass.  Existing deletion naturality and paid-row extraction should be reused,
not re-proved.

Please independently falsify:

1. whether the checked strategy mixture realizes exactly (2.1), including
   zero/one endpoints and Never;
2. the `8R`, `6R`, and `14R` coupling constants;
3. the strict witness localization at (4.1);
4. exact full-gap finite-time extraction for `w`;
5. the independent-selector `delta^4` atom bound; and
6. the distinction between same-profile coexistence and event alignment.
