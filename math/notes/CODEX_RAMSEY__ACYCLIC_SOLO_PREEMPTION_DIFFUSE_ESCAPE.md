# CODEX_RAMSEY — acyclic solo-preemption graphs have a diffuse singleton escape

Author: `CODEX_RAMSEY`

Status: exported after two independent falsification PASSes and a separate
whole-packet PASS.  The reviews are
[`CODEX_EULER`](../feedback/ACYCLIC_SOLO_PREEMPTION_NOGO__BY_CODEX_EULER.md)
and
[`CODEX_CEDAR`](../feedback/CODEX_RAMSEY__ACYCLIC_SOLO_PREEMPTION_DIFFUSE_ESCAPE__BY_CODEX_CEDAR.md).
The packet gate is
[`CODEX_EULER`](../feedback/ACYCLIC_SOLO_PREEMPTION_GADGET_NOGO__BY_CODEX_EULER__PACKET_GATE.md).
The result rules out one explicit universal incentive-gadget architecture.  It
is ordinary mathematics and is not yet a Lean theorem.

## 1. Self-contained question and answer

Let `I` be a nonempty finite player set and let

```text
r : {S : Finset I // S.Nonempty} -> R^I
```

be a finite quitting reward table.  Put

```text
s_i = r({i})_i.
```

The empty-player game is outside the stated theorem; its empty profile is
vacuously exact.

Adjoin one symbol `bottom` to the player set and define the **augmented strict
solo-preemption digraph** on `I union {bottom}` by the following edges:

```text
bottom -> i   iff  s_i > 0,
i -> bottom   iff  s_i < 0,
i -> j        iff  i != j and r({j})_j > r({i})_j.       (1)
```

The last edge says exactly that `j` strictly prefers quitting alone to waiting
for `i` to quit alone.  In the repository's orientation it is
`QuittingSoloPreempts r gap i j` for some `gap>0`.

> **Theorem 1 (acyclic solo-preemption diffuse escape).**  If the graph `(1)`
> is acyclic, then the quitting game has terminal approximate Nash profiles at
> every positive error.  More precisely, either:
>
> 1. `bottom` is a sink and all Never is an exact terminal Nash profile; or
> 2. some player `p` is a sink.  If `p` Quits at each live date with stationary
>    probability `q in (0,1)` and every other player plays Never, then the
>    profile's terminal exploitability is at most `q J_p`, where
>
>    ```text
>    J_p = max ({0} union
>      {r({p,j})_j-r({p})_j : j != p}),                 (2)
>    ```
>
>    so the finite maximum is singleton-safe and equals zero when `p` is the
>    only player.
>
>    Its prescribed terminal payoff is the literal singleton row `r({p})`.
>
> Consequently, for a rational reward table and every positive error one may
> choose a rational `q` giving a rational stationary terminal approximate Nash
> profile.  The fixed target `r({p})` is a uniform-equilibrium payoff by the
> checked terminal-all-errors fixed-target consumer.

For the four-clock gadget in `questions/INCENTIVE_GADGET.md`, the profile in
either arm has

```text
a=0,  b=0,  ell=1.                                  (3)
```

Indeed, all Never is assigned to `ell`, while the second arm absorbs almost
surely at the singleton `{p}`, also an `ell` outcome.  Thus no reward table
whose augmented graph is acyclic can force the requested positive lower bound
on either designated pair atom from small terminal exploitability.  Any viable
gadget in this architecture must contain a directed cycle in `(1)`.

The statement permits arbitrary rewards on every coalition of size at least
three.  They do not occur under the constructed profile or under a unilateral
deviation from it.

## 2. A finite graph supplies the sink

Every finite acyclic directed graph has a sink.  If `bottom` is a sink, there
is no edge `bottom -> i`; hence

```text
s_i <= 0                                               (4)
```

for every player.  Against opponents who all play Never, a player's finite
quit time pays `s_i` and Never pays zero.  Every behavioral stopping strategy
is a mixture of those possibilities, so `(4)` proves that all Never is exact
terminal Nash.  This arm is exactly the checked zero-solo disjunct.

Now suppose a player `p` is a sink.  Absence of `p -> bottom` and of every
`p -> j` gives

```text
s_p >= 0,
r({j})_j <= r({p})_j        for every j != p.          (5)
```

These are the only sink inequalities used below.

## 3. Exact pure-time formula

Let `G` be `p`'s quit time under stationary hazard `q`, with dates numbered
`0,1,2,...`:

```text
Pr(G=t)=q(1-q)^t.                                      (6)
```

Since `q>0`, `G` is finite almost surely.  If everyone else plays Never, the
terminal coalition is `{p}` almost surely and the prescribed payoff is
`r({p})`.

Player `p` has no profitable deviation.  Its opponents never quit, so every
finite quit time pays `s_p`, Never pays zero, and its prescribed strategy pays
`s_p`.  The first inequality in `(5)` is exactly what is needed.

Fix `j != p`.  Abbreviate

```text
x_j = r({j})_j,
y_j = r({p})_j,
z_j = r({p,j})_j.
```

If `j` Quits at the deterministic date `t`, then `G<t`, `G=t`, and `G>t`
respectively pay `y_j`, `z_j`, and `x_j`.  Subtracting the prescribed payoff
`y_j` gives the exact excess

```text
D_j(t)
 = (1-q)^t * [q*(z_j-y_j)+(1-q)*(x_j-y_j)].           (7)
```

The inclusive time convention is visible here:

```text
Pr(G=t)=q(1-q)^t,
Pr(G>t)=(1-q)^(t+1).
```

By `(5)`, `x_j-y_j<=0`.  Therefore `(2)` and `(7)` imply

```text
D_j(t) <= q J_p                                      (8)
```

for every finite date `t`.  Never gives excess zero.

An arbitrary behavioral deviation by `j` in a one-state quitting game induces
one law `mu` on `N union {infinity}` through its conditional hazards.  It can
equivalently draw that quit time privately at date zero; this draw is
independent of `p`'s private geometric clock.  Terminal payoff is affine in
`mu`, so its excess is

```text
sum_t mu(t) D_j(t) + mu(infinity)*0 <= q J_p.          (9)
```

This covers arbitrary time dependence, private randomization, all finite pure
times, ties, and Never.  Taking the maximum over `j` proves Theorem 1.

If `p` is the only player, there is no outsider cap to check and any
`q in (0,1]` is exact.  Otherwise `J_p` is the finite maximum in `(2)`.  If
`J_p=0`, every `q in (0,1)` is already exact.  If `J_p>0`, `q` can be chosen
arbitrarily small, and in particular with `q J_p` below any prescribed
positive error.  For an arbitrary real table one may choose such a `q`
rational by density.  For a rational table, the explicit choice

```text
q=min(1/2, epsilon/(2*(J_p+1)))
```

is rational whenever the requested `epsilon` is rational.

## 4. Exact strict-sink refinement

The weak sink theorem is generally only approximate because a deviator can
be indifferent between its singleton and `{p}` rows but gain on the tie row.
There is, however, an exact rational refinement.

Call a player sink `p` **strict on the player faces** if

```text
g_p = min_(j != p) (r({p})_j-r({j})_j) > 0.           (10)
```

Assume there is at least one `j != p`; the one-player case is already exact.
For a real table choose

```text
q = g_p / (2*(g_p+J_p)).                              (11)
```

This lies in `(0,1/2]`.  It is rational when the reward table is rational.
For arbitrary real rewards, any positive rational
`q<g_p/(g_p+J_p)` works instead.  For the displayed choice, the bracket in
`(7)` is at most

```text
q J_p-(1-q)g_p
 = q*(J_p+g_p)-g_p
 = -g_p/2 < 0.                                       (12)
```

Thus every finite pure quit time of every `j != p` is strictly worse than the
prescribed Never strategy, while Never is equal.  Player `p` is optimal by
`s_p>=0`.  The stationary singleton profile is therefore an **exact**
terminal Nash profile.  For rational reward data this proves the claimed exact
rational strict-sink arm without placing any bound on pair or
larger-coalition rewards.

## 5. Sharp tests

### 5.1 Weakness really costs exactness

Take two players `p,j` and, in coordinate `j`, put

```text
r({j})_j=r({p})_j=0,
r({p,j})_j=1,
```

with `s_p=1`.  Then `p` is a weak sink, `J_p=1`, and `(7)` at `t=0` gives
gain exactly `q`.  No positive stationary hazard in this construction is
exact, while exploitability tends to zero with `q`.  This shows both the
factor `q` and the need for `(10)` in the exact refinement.

### 5.2 Rational strict sink

Put instead

```text
r({j})_j=0, r({p})_j=1, r({p,j})_j=3, s_p=1.
```

Then `g_p=1`, `J_p=2`, and `(11)` gives `q=1/6`.  Formula `(12)` gives the
strict bracket `-1/2`; hence the displayed rational stationary profile is
exact even though the collision row is strictly attractive relative to
`r({p})_j`.

### 5.3 Cyclic boundary

The conclusion is only an acyclic-architecture theorem.  When `(1)` contains
a directed cycle, no sink argument is available.  This note makes no claim
that a cycle produces the requested gadget, only that one is necessary for
this solo-preemption architecture to survive.

## 6. Source, novelty, and semantic consumer

The narrow source search inspected:

- `QuittingSoloPreempts` in
  `UniformEquilibrium/Quitting/Classification/PreemptionCycle.lean`;
- `normalizedSoloMatrix_eq_soloReward_sub` and
  `quittingSoloPreempts_iff_normalizedSoloMatrix_le_neg` in
  `UniformEquilibrium/Quitting/Classification/PreemptionGateDictionary.lean`;
- `IsQuittingZeroSolo`,
  `isZeroAsymptoticNash_quittingAlwaysContinue_of_zeroSolo`, and
  `quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo` in
  `UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`; and
- `quittingStationarilyGeneratedApproximateEquilibria_of_normal_noHarmSingleton`
  in
  `UniformEquilibrium/Quitting/Classification/Existence/NoHarmSingletonGenerated.lean`,
  together with `quittingPunishmentValue_le_max_solo` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`;
- `isεAsymptoticNash_soloStationary_exact_iff` and
  `isUniformEquilibriumPayoff_soloReward_of_inactive` in
  `UniformEquilibrium/Quitting/Punishment/OwnerSoloCertification.lean`; and
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_fixedTarget`
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean`.

The orientation in `(1)` agrees exactly with the checked preemption
definition: `i -> j` means that `j` preempts `i`.  Existing preemption-cycle
files analyze the cyclic residual once strict preemption edges have been
produced.  The checked zero-solo theorem consumes the `bottom`-sink arm.  The
checked no-harm-singleton and owner-solo declarations are strategically
stronger than the isolated stationary calculation: a player sink supplies
their no-harm singleton inequalities, and the exact affine inactive-player
condition is precisely the bracket in `(7)` at `t=0`.

Accordingly, the new contribution claimed here is the transparent **augmented
graph corollary and gadget no-go**: acyclicity forces one of those checked solo
owner branches, and the explicit diffuse profiles simultaneously have
`a=b=0, ell=1`.  No new general stationary-existence theorem is claimed.

The signed-influence SCC theorem is different.  It assumes coalitionwise
fixed influence signs and constructs a sure-exit set.  The present source uses
only singleton rows plus the pair collision rows in the error constant; every
larger-coalition reward and every background-dependent influence may be
arbitrary.

Because every approximate profile in the player-sink arm has the same
prescribed payoff `r({p})`, the named fixed-target terminal-all-errors theorem
is the downstream unrestricted semantic consumer.  For the incentive-gadget
question, no further consumer is needed: `(3)` directly falsifies the required
pair-mass implication at arbitrarily small terminal error.

## 7. Scope and next question

- This is an ordinary mathematical theorem, not yet checked in Lean.
- It rules out exactly the acyclic augmented solo-preemption architecture.
- It does not assume that the candidate reward table ignores calibrators or
  large coalitions; those rows are simply unreachable under one unilateral
  deviation from the constructed profile.
- It proves no conclusion for a table whose augmented graph has a directed
  cycle.
- It does not construct the positive pair-mass gadget or settle the general
  finite-quitting conjecture.

The next exact question is whether a directed cycle through `bottom` can also
be diffused by a finite stationary chain, or whether every surviving cycle can
be reduced to one of the already solved signed-influence/blocker cores.
