# Independent review of `FIN5_QUIET_WHOLE_LAW_ATOM_PAID_CONNECTOR`

**Reviewer:** CODEX_RAMSEY  
**Date:** 2026-08-25  
**Verdict:** **PASS in the stated same-profile scope; keep internal.**

I checked the complete-stopping-law interpolation, private-product
realization, all three Lipschitz constants, the quantitative witness
localization, exact finite-time paid-row extraction, the `delta^4` atom
retention, and the cardinal-minimal Fin5 adapter.  I found no mathematical
error.  The result genuinely repairs the bare source-coincidence problem: one
actual profile carries both a positive fraction of the frozen chronological
atom and a full-gap paid row for the preselected omitted player.  It still
does not align those two events or enter a checked floor/Bellman/rank
consumer, so it should remain internal.

## 1. Mixture orientation and behavioral legality

The argument uses the checked orientation correctly.  For

```text
quittingStoppingLawMixtureBehaviorStrategy
  rewardMinus i (eta i) (sigma i) (1-delta)
```

`quittingBehaviorStoppingLaw_stoppingLawMixture` gives

\[
\mu_i^\delta
=\delta\mu_i^\eta+(1-\delta)\mu_i^\sigma.
\]

The theorem's parameter is the weight of the second (`target`) law, so using
`1-delta` indeed gives source weight `delta`.

This is an ordinary behavioral strategy.  Its hazards reconstruct the
affine complete stopping law by conditioning mixed stop mass on mixed
survival.  Across players, the quitting profile uses independent private
randomization.  Consequently the induced vector of stopping times has the
product of the four displayed marginal laws.  Referring to an independent
private initial selector is a distributional realization for the estimates,
not an illicit public correlating device.

The terminal-gap bound `Gamma<=2R`, together with `Gamma>epsilon>0`, implies
`R>0` and

\[
0<\delta={\Gamma-\epsilon\over28R}
<{\Gamma\over28R}\le {1\over14}<1.
\]

Thus all mixture parameters and denominators are valid, including the
boundary where component laws are mutually singular or carry Never mass.

## 2. Coupling constants

Couple each mixed survivor stopping law to its `sigma` law so that it differs
only on the source-selector branch.  Each coordinate mismatch probability is
at most `delta`.

For prescribed payoffs, couple all four coordinates independently.  Unless
one of the four couplings mismatches, the complete stopping-time vector—and
hence the terminal coalition or Never outcome—is identical.  The union bound
is `4 delta`; two payoff values in `[-R,R]` differ by at most `2R`.  Therefore

\[
|U_i(\xi_\delta)-U_i(\sigma)|\le 8R\delta.
\]

For a fixed arbitrary behavioral deviation of survivor `i`, use the same
deviation law in both comparisons.  Only the other three survivor stopping
laws can mismatch; the omitted player is Never in both quiet lifts.  The
union bound is `3 delta`, yielding a uniform deviation-payoff difference
`<=6R delta`.  Taking suprema in both directions is legitimate because the
same unrestricted deviation class is used, and gives

\[
|B_i(\xi_\delta)-B_i(\sigma)|\le6R\delta.
\]

Combining the upper cap perturbation with the lower prescribed-payoff
perturbation gives

\[
d_i(\xi_\delta)\le d_i(\sigma)+14R\delta.
\]

Deletion-lift naturality preserves both quantities exactly for survivors, so
the same bounds hold at the ambient profile `z_delta`.  The general
`2Rk`, `2R(k-1)`, and `2R(2k-1)` formulas are the same calculation.

## 3. Gap localization and exact finite paid row

Since `sigma` is terminal `epsilon`-Nash,

\[
d_i(z_\delta)\le\epsilon+14R\delta
=\epsilon+{\Gamma-\epsilon\over2}
={\Gamma+\epsilon\over2}<\Gamma
\]

for every survivor.  Applying the ambient terminal exploitability gap at the
literal profile `z_delta` therefore excludes all four survivors.  The sole
remaining label is the preselected omitted player `w`, proving
`d_w(z_delta)>=Gamma` without a witness-selection assumption.

The quiet lift prescribes `w` to literal Never.  Disintegrating the selected
profitable behavioral deviation with
`quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` is exact on
`Option Nat`.  Never has the baseline value.  If all finite times gained
strictly less than `Gamma`, every support atom would lie below the threshold;
splitting off one positive-mass support atom makes the bounded expectation
strictly smaller, contradicting the weak full-gap gain.  Hence some finite
time retains gain at least `Gamma`, and
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` returns the
claimed row at `z_delta` with observer exactly `w`.

## 4. Chronological atom retention

For a finite atom `(t,S)`, the joint stopping-time law is multilinear in the
four independent marginal stopping laws.  In its nonnegative expansion, the
branch where all four selectors take their `eta` components has coefficient
`delta^4`; conditional on that branch its atom mass is exactly `m_eta(t,S)`.
Therefore

\[
m_{\xi_\delta}(t,S)\ge\delta^4m_\eta(t,S).
\]

This can also be obtained by four successive applications of
`one_sub_mul_stageCoalitionMass_le_stoppingLawMixture`.  It covers players in
`S` through their stop masses and players outside `S` through their survival
past `t`; Never is already part of the complete law.  Quiet lifting `w`
leaves the survivor chronological atom unchanged.

If the frozen source came from the reviewed erase-`w` construction and

\[
\tfrac14m_{x_0}(t,T)\le m_y(t,T\setminus\{w\}),
\]

the erasure premise already includes that the survivor coalition is
nonempty.  Multiplying the two lower bounds gives exactly

\[
m_{z_\delta}(t,T\setminus\{w\})
\ge {\delta^4\over4}m_{x_0}(t,T).
\]

The note correctly does not claim that the full joint outcome law is a
two-term convex mixture: the other `2^4-2` selector branches are present.

## 5. Fin5 adapter and typing

For a cardinal-minimal five-player counterexample, the one-player-deleted
subtype is nonempty and has cardinality four.  The checked smaller-cardinality
uniform-payoff theorem and terminal selection interface supply `sigma` at any
`epsilon>0`, in particular `epsilon=Gamma/2`.  The resulting constants are

\[
\delta={\Gamma\over56R},\qquad
d_i(z_\delta)\le {3\Gamma\over4},
\]

and the quarter-retained atom factor is
`Gamma^4/[4(56R)^4]`, as stated.

As in the preceding frozen-source note, a literal Lean wrapper over
`MinimalFinQuittingCounterexample` must either keep labels in
`Fin minimal.playerCount` with a hypothesis `playerCount=5`, or explicitly
transport to `Fin 5`.  The present ordinary statement starts directly with a
five-player table, so it has no mathematical type ambiguity.

## 6. Scope and consumer assessment

The connector is stronger than the preceding source-separation theorem:
source reselection no longer destroys every trace of the frozen source.  At
one actual profile it co-realizes:

* a quantitatively retained survivor chronological atom;
* survivor debts strictly below the ambient gap; and
* a source-matched full-gap finite paid row for `w`.

The retained atom need not be the paid first-disagreement cylinder, need not
carry the old toggle after erasing `w`, and has no supplied punishment-floor
or Bellman sign.  The checked paid-cap trichotomy can be invoked from this
profile, but its inert arm remains and no current declaration consumes the
simultaneous atom/paid-row fields or turns them into a support/debt-rank
decrease.

Accordingly this is a useful internal actual-source connector, not yet an
export-quality chamber elimination.  Export becomes warranted only after an
event-alignment theorem or a named consumer uses the retained atom while
preserving the source-matched paid row.

