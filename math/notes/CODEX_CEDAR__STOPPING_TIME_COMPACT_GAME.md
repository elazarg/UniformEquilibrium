# CODEX_CEDAR — compact stopping-time normal form and its payoff-graph failure

## Current best attempt

**Status: CLOSED as a direct better-reply-security route.**  Propositions 1--2
give an exact compact stopping-law representation, the finite-pure-time
continuity needed for truncation limits, and the complete late-Quit/Never jump.
Proposition 3 localizes the deviation inequality lost under weak limits to a
negative-solo player with positive opponent-Never mass.  However Proposition
4 gives a two-player positive-solo table at which the closure of the payoff
graph contains payoff `(1,1)` over the non-Nash all-Never profile, while no
player can secure more than `1`.  Thus the compact game is not universally
better-reply secure, even away from the negative-solo seam.  A direct Reny-type
existence theorem cannot be the missing universal producer without a further
time-translation or boundary-state compactification.

**Conjecture-closing thesis tested.**  Identify arbitrary behavioral strategies
with probability laws on the compact quit-time space
`K=N union {infinity}` and obtain terminal approximate Nash profiles from a
general compact discontinuous-game equilibrium theorem.  This is distinct
from Simon finite-orbit necessity and from punishment-floor source matching:
it treats the full all-behavior terminal game in one normal form.

**Universal obligation and kill criterion.**  The required theorem would need
the closure-payoff security implication: at every non-Nash weak limit profile
and every payoff vector in the closure of the terminal payoff graph, some
player has a fixed stopping time that secures strictly more than that closure
payoff against nearby opponents.  Proposition 4 violates this implication
exactly, reaching the kill criterion.  Repairing it requires retaining the
relative scale/order of quit times escaping to infinity; that is a different
compactification and overlaps the existing normalized-motion/Simon program.

**Sections to check.**  Section 2 for named semantic sources, Section 3 for
the exact topology and quantifiers, Section 4 for the late-Quit identity, and
Sections 5--6 for the truncation inequality and two-player falsifier.

All propositions below are ordinary mathematics, not checked in Lean.

## 1. Self-contained question

Fix a nonempty finite player set `I` and a finite quitting reward table

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I.
\]

Before absorption the only public history is a string of joint Continue
actions.  A player's behavioral strategy therefore induces a law on

\[
 K:=\mathbb N\cup\{\infty\},
\]

its first Quit time, and players' private randomizations make these laws
independent.  Give `K` the one-point compactification topology: every finite
date is isolated and `t_n -> infinity` exactly when `t_n -> +infinity` in
`N`.  Give probability laws on `K` the weak topology.

The tested question is whether the resulting compact mixed normal-form game
has enough payoff security to invoke a general discontinuous-game equilibrium
theorem and thereby produce terminal approximate Nash profiles for every
finite quitting table.

## 2. Bounded source audit

The narrow lookup inspected these declarations and their local definitions.

- `quittingBehaviorStoppingLaw`, `quittingHazardStoppingLaw_none_toReal`, and
  `quittingHazardStoppingLaw_some_toReal`
  (`UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`) identify the
  complete finite-date/Never stopping law of one live-spine behavior.
- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime`
  (`UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`) is the
  exact one-player mixture identity.
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime`
  (`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`)
  identifies unrestricted behavioral best response with finite pure Quit
  times plus Never.
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean`)
  is the fixed-target consumer that a successful compact-game argument would
  feed.
- `exists_minimum_quittingTerminalSemanticDebtSum`
  (used in
  `UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean`)
  compactifies the finite-dimensional semantic pair, not the full stopping
  laws or their escaping relative-time order.

A narrow search for `better-reply security`, `payoff security`, and compact
stopping-law Nash existence found no existing project theorem.  No external
discontinuous-game theorem is invoked below; Proposition 4 directly refutes
the premise the proposed route would need.

## 3. Exact stopping-law normal form

### Proposition 1 (proved)

Every probability law `mu` on `K` is induced by a Boolean behavioral hazard,
and the induced law determines all terminal payoffs.  Hence behavior profiles
modulo terminal equivalence are exactly product laws

\[
 \mu=\bigotimes_{i\in I}\mu_i\quad\hbox{on }K^I.
\]

### Proof

Given `mu`, let

\[
 S(t)=\mu(\{t,t+1,\ldots,\infty\}).
\]

If `S(t)>0`, set the date-`t` Quit hazard to `mu({t})/S(t)`; if `S(t)=0`, set
it arbitrarily, say zero.  Induction gives survival through date `t` equal to
`S(t)` and stopping mass at `t` equal to `mu({t})`.  The limiting survival is
`mu({infinity})`.  Conversely the usual survival-times-hazard formula gives a
probability law on `K`.  Private behavioral randomizations are independent
across players on the unique live history.  The first minimum finite time and
its tie set therefore determine the terminal coalition and payoff.

## 4. Continuity of fixed finite times and the unique unilateral boundary jump

For fixed opponents `mu_{-i}`, let `V_i(t;mu_{-i})` be player `i`'s payoff
when it Quits deterministically at `t in N`, and let
`V_i(infinity;mu_{-i})` be its pure-Never payoff.  Write

\[
 s_i=r(\{i\})_i,\qquad
 A_{-i}=\prod_{j\ne i}\mu_j(\{\infty\}).
\]

### Proposition 2 (proved)

For every fixed finite `t`, `V_i(t;.)` is continuous in the opponents' weak
laws.  Moreover

\[
 \lim_{t\to\infty}V_i(t;\mu_{-i})
 =V_i(\infty;\mu_{-i})+s_iA_{-i}.                 \tag{4.1}
\]

### Proof

At a fixed finite `t`, the payoff is a finite sum of products of opponent
probabilities of the clopen events `{0},...,{t}` and `{t+1,t+2,...,infinity}`.
It is therefore weakly continuous.

For (4.1), partition opponent outcomes into: absorption strictly before `t`;
some opponent stopping exactly at `t`; all opponents stopping after `t` but
not all Never; and all opponents Never.  The first term converges to the
Never payoff.  The exact-`t` term tends to zero because every probability
mass function has atoms tending to zero.  The finite-tail term also tends to
zero by continuity from above.  On the all-opponents-Never event, finite Quit
pays `s_i`, whereas Never pays zero.  Its probability is `A_{-i}`, proving
(4.1).  This argument includes atoms and Never exactly.

## 5. What finite truncation limits really preserve

Let `mu^n` be any sequence of product stopping-law profiles, let
`mu^n -> mu` weakly coordinatewise, and suppose their payoff vectors converge
to `u`.  Assume each `mu^n` is exact Nash against every deterministic Quit
time in `{0,...,n}` (finite normal-form Nash profiles are the intended source).

### Proposition 3 (proved)

For every player `i` and fixed finite `t`,

\[
 V_i(t;\mu_{-i})\le u_i.                         \tag{5.1}
\]

Consequently

\[
 V_i(\infty;\mu_{-i})+s_iA_{-i}\le u_i.          \tag{5.2}
\]

Thus Never is also bounded by `u_i` whenever `s_i>=0` or `A_{-i}=0`.  The only
unilateral best-response inequality not forced by fixed-time compactness is

\[
 s_i<0,\quad A_{-i}>0,\quad
 V_i(\infty;\mu_{-i})>u_i.                        \tag{5.3}
\]

Even when (5.3) is absent, the prescribed limit payoff
`U_i(mu)` need not equal the graph-limit payoff `u_i`.

### Proof

For fixed `t`, the Nash inequality is available for every `n>=t`.  Proposition
2 gives convergence of the deviating payoff, while prescribed payoffs converge
to `u_i`, proving (5.1).  Let `t` tend to infinity and use (4.1) to obtain
(5.2).  The sign consequences are immediate.

## 6. Exact failure of better-reply security

### Proposition 4 (proved; two-player falsifier)

There is a two-player quitting table and exact Nash profiles whose stopping
laws converge weakly to a non-Nash profile while their payoffs converge to a
closure payoff that no player can strictly beat.  Let

```text
r({0})   = (1/2,0),
r({1})   = (0,1/2),
r({0,1}) = (1,1).
```

For every `n`, let both players Quit deterministically at date `n`.  This is an
exact terminal Nash profile with payoff `(1,1)`.  The stopping laws converge
to all-Never, whose payoff is `(0,0)` and which is not Nash.  Nevertheless no
player can secure more than its closure payoff `1` against any opponents.

### Proof

At the date-`n` profile the terminal coalition is `{0,1}` and both players get
one.  A unilateral Quit before `n` gets own solo payoff `1/2`; a unilateral
Quit after `n` or Never gets zero because the opponent quits alone at `n`.
Any behavioral deviation is a mixture of those pure times, so the profile is
exact Nash.

As `n -> infinity`, both deterministic laws converge weakly to `delta_infinity`.
The literal limit profile is all-Never and pays zero.  Either player can deviate
to any finite time and get `1/2`, so it is not Nash.  But every terminal reward
coordinate is at most one, hence no strategy can guarantee strictly more than
the graph-limit payoff one.  The closure-payoff security implication fails.

The all-Never profile is not itself an obstruction to equilibrium existence:
Quit-together at date zero is already exact Nash.  The example instead proves
that a generic better-reply-security theorem cannot select that equilibrium
from weak compactness alone.  The lost datum is the relative timing of clocks
escaping together to infinity.  Retaining that datum requires an enlarged
boundary or a common time recentering, not the plain compact mixed normal form.
