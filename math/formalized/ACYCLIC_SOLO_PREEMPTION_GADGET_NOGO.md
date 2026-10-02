# Acyclic solo-preemption architectures cannot force incompatible pair clocks

Author: `CODEX_RAMSEY`

Independent falsification reviews:

- [`CODEX_EULER`](../feedback/ACYCLIC_SOLO_PREEMPTION_NOGO__BY_CODEX_EULER.md)
- [`CODEX_CEDAR`](../feedback/CODEX_RAMSEY__ACYCLIC_SOLO_PREEMPTION_DIFFUSE_ESCAPE__BY_CODEX_CEDAR.md)

Whole-packet review:

- [`CODEX_EULER`](../feedback/ACYCLIC_SOLO_PREEMPTION_GADGET_NOGO__BY_CODEX_EULER__PACKET_GATE.md)

## Exact statement

Let `I` be a nonempty finite player set and let

```text
r : {S : Finset I // S.Nonempty} -> R^I
```

be a finite quitting reward table.  Write `s_i=r({i})_i`.  Adjoin one symbol
`bottom` and define a directed graph on `I union {bottom}` by

```text
bottom -> i   iff s_i>0,
i -> bottom   iff s_i<0,
i -> j        iff i!=j and r({j})_j>r({i})_j.       (1)
```

Assume this augmented strict solo-preemption graph is acyclic.  Then one of
the following holds.

1. The all-Never profile is exact terminal Nash against every unilateral
   behavioral deviation.
2. There is a player `p` such that, for every `q in (0,1)`, the stationary
   profile in which only `p` Quits, with live-date probability `q`, has
   terminal exploitability at most

   ```text
   q J_p,

   J_p=max ({0} union
     {r({p,j})_j-r({p})_j : j!=p}).                 (2)
   ```

   It absorbs almost surely at the singleton `{p}` and has prescribed payoff
   exactly `r({p})`.

Consequently the game has terminal approximate Nash profiles at every positive
error.  The second arm uses one fixed target payoff `r({p})`, so the checked
fixed-target terminal-all-errors consumer makes it a uniform-equilibrium
payoff.  If the reward table and requested error are rational, the profile can
be chosen with a rational stationary rate.

There is also an exact strict-sink refinement.  If `p` is a player sink and

```text
g_p=min_(j!=p) (r({p})_j-r({j})_j)>0,               (3)
```

then every

```text
0<q<=g_p/(g_p+J_p)                                  (4)
```

makes the singleton stationary profile exact terminal Nash.  For a rational
table, the rational choice

```text
q=g_p/[2(g_p+J_p)]                                  (5)
```

works.  When `p` is the only player, set `J_p=0`; every positive rate is exact
whenever `s_p>=0`, and `(3)--(5)` are unnecessary.  The empty-player game is
outside the statement and is vacuous.

For the four-clock notation of
[`INCENTIVE_GADGET.md`](../questions/INCENTIVE_GADGET.md), every constructed
profile satisfies

```text
a=0, b=0, ell=1.                                    (6)
```

This remains true if `p` is an added calibrator.  Therefore no reward table in
the acyclic architecture `(1)` can derive positive lower bounds on both target
pair atoms from low terminal exploitability.  A directed cycle in the
augmented graph is necessary for any viable gadget in this architecture.

## Conjecture-facing change

The maintained incentive-gadget question requires one finite table for which
every sufficiently accurate terminal Nash profile gives two positive
strict-first pair atoms and a small leftover.  The theorem supplies, for every
table in the precisely defined acyclic solo-preemption class, profiles at
arbitrarily small terminal error with the opposite extreme `(6)`.  It is
therefore a complete negative answer for that universal gadget architecture,
not a failed search in one table.

The surviving boundary is exact: the augmented graph must contain a directed
cycle.  The packet does not assert that such a cycle suffices.

## Probability, information, and deviation semantics

Dates are `0,1,2,...`.  In the player-sink arm, `p` independently Quits at
every live date with probability `q`; every other player uses Never.  Thus
`p`'s quit time `G` obeys

```text
Pr(G=t)=q(1-q)^t,
Pr(G>t)=(1-q)^(t+1),                                (7)
```

and is finite almost surely.

There is no public correlation or mixture over stationary profiles.  A
unilateral deviator may use arbitrary history-dependent behavioral hazards,
private randomization, any pure finite time, or Never.  Before absorption the
only public history is repeated unanimous Continue, so such a deviation
induces one law on `N union {infinity}`.  It is equivalently a private draw of
its first quit time and is independent of `G`.  Terminal expectation is affine
in that law.  The proof below therefore controls the full behavioral deviation
class, not only stationary or finite-controller deviations.

Under one unilateral deviation, the only possible terminal coalitions are
`{p}`, `{j}`, and `{p,j}`.  Rewards on coalitions of cardinality at least three
are genuinely arbitrary and irrelevant to the calculation.

## Proof

### 1. Sink alternatives

A finite acyclic digraph has a sink.  If `bottom` is a sink, no edge
`bottom->i` exists, so `s_i<=0` for every player.  Against opponents who Never,
every finite quit time pays `s_i` and Never pays zero.  Every behavioral
strategy is a mixture of those possibilities; hence all Never is exact.
This is the checked zero-solo branch.

Otherwise take a player sink `p`.  Absence of `p->bottom` and of `p->j` gives

```text
s_p>=0,
r({j})_j<=r({p})_j       for every j!=p.            (8)
```

Player `p` faces opponents who Never.  Its prescribed geometric clock quits
almost surely and pays `s_p`; every finite alternative also pays `s_p`, while
Never pays zero.  The first inequality in `(8)` proves that `p` cannot gain.

### 2. Exact pure-time calculation

Fix `j!=p` and abbreviate

```text
x_j=r({j})_j, y_j=r({p})_j, z_j=r({p,j})_j.
```

If `j` Quits at deterministic date `t`, the events `G<t`, `G=t`, and `G>t`
pay `y_j`, `z_j`, and `x_j`.  Subtracting prescribed payoff `y_j` gives

```text
D_j(t)
 =(1-q)^t [q(z_j-y_j)+(1-q)(x_j-y_j)].              (9)
```

At `t=0`, the singleton `{j}` has probability `1-q` and the tie `{p,j}` has
probability `q`, fixing the time convention.  Never has excess zero because
`p` quits almost surely.

By `(8)`, `x_j-y_j<=0`.  The singleton-safe definition `(2)` therefore gives

```text
D_j(t)<=q(1-q)^t J_p<=qJ_p.                         (10)
```

An arbitrary behavioral deviation is a probability mixture of the values in
`(9)` and the zero Never excess.  Inequality `(10)` proves its gain is at most
`qJ_p`.  Taking the maximum over all players proves the quantitative arm of
the theorem.

If `J_p=0`, the profile is exact at every positive rate.  If `J_p>0`, take,
for example,

```text
q=min(1/2, epsilon/[2(J_p+1)]).                     (11)
```

Then `qJ_p<epsilon`.  For rational data and rational `epsilon`, `(11)` is
rational; for arbitrary real data a smaller positive rational rate may instead
be chosen by density.

### 3. Strict-sink exactness

Under `(3)`, the bracket in `(9)` is at most

```text
qJ_p-(1-q)g_p=-g_p+q(g_p+J_p).                     (12)
```

This is nonpositive under `(4)`.  At the displayed rational rate `(5)`, it is
exactly `-g_p/2<0`.  Every outsider's finite quit time is therefore no better
than Never, while `p` remains optimal by `(8)`.  This proves exact terminal
Nash and the rational refinement.

### 4. Pair masses and uniform payoff

In the `bottom`-sink arm, Never occurs with probability one.  In the
player-sink arm, `{p}` occurs with probability one.  Neither is either
designated two-player target coalition, so `(6)` follows, including when `p`
is a calibrator.

For a fixed player sink, every approximate profile above has prescribed payoff
`r({p})`.  Applying

```text
quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_fixedTarget
```

to the all-error family gives the uniform-payoff conclusion.  The
`bottom`-sink uniform payoff is already supplied by the checked zero-solo
theorem.

## Boundary tests

### Weak sink: the factor `q` is sharp

Take two players `p,j`, set `s_p=1`, and in coordinate `j` put

```text
r({j})_j=r({p})_j=0,
r({p,j})_j=1.
```

Then `p` is a weak sink, `J_p=1`, and quitting at date zero gains exactly `q`.
No positive rate in this singleton construction is exact, while its
exploitability tends to zero.  This tests the equality face and shows why
strictness is required only for the exact refinement.

### Rational strict sink

Set instead

```text
r({j})_j=0, r({p})_j=1, r({p,j})_j=3, s_p=1.
```

Then `g_p=1`, `J_p=2`, and `(5)` gives `q=1/6`; the bracket `(12)` is `-1/2`.
The rational stationary profile is exact despite the attractive collision
row.

### Cyclic boundary

If `(1)` contains a directed cycle, the sink proof no longer applies.  This is
the sharp boundary of the theorem's graph argument, not a counterexample and
not a claim that cyclic tables lack a uniform payoff.

## Source correspondence and novelty

The graph orientation is exactly the repository convention in

```text
QuittingSoloPreempts
normalizedSoloMatrix_eq_soloReward_sub
quittingSoloPreempts_iff_normalizedSoloMatrix_le_neg
```

from
`UniformEquilibrium/Quitting/Classification/PreemptionCycle.lean` and
`PreemptionGateDictionary.lean`: `i->j` means that `j` preempts `i`.

The `bottom`-sink arm is the checked `IsQuittingZeroSolo` theorem in
`UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean`.  The repository
also contains strategically stronger solo-owner results:

```text
quittingStationarilyGeneratedApproximateEquilibria_of_normal_noHarmSingleton
isεAsymptoticNash_soloStationary_exact_iff
isUniformEquilibriumPayoff_soloReward_of_inactive
```

in `NoHarmSingletonGenerated.lean` and `OwnerSoloCertification.lean`.  A player
sink supplies the no-harm singleton inequalities, and the fixed-rate inactive
condition is precisely `(12)`.  This packet does **not** claim a new general
solo-owner equilibrium compiler.

The new result is the exact augmented-graph packaging and its
`INCENTIVE_GADGET` consequence: acyclicity forces a zero-solo or diffuse
singleton escape with the explicit `qJ_p` bound and `(a,b,ell)=(0,0,1)`.
Existing preemption-cycle files start from the cyclic residual; they do not
state this graph-level gadget no-go.  The signed-influence SCC theorem uses
coalitionwise fixed influence signs and is a different class.  Here every
large-coalition reward and background-dependent influence is unrestricted.

## Actual-data adapter and downstream consumer

The adapter is finite and literal:

1. read every singleton own payoff and every off-diagonal singleton payoff;
2. build the graph `(1)` and check acyclicity;
3. select a sink;
4. in a player-sink arm compute the finite number `J_p` from pair rows.

No equilibrium profile, desired target mass, continuation value, or
best-response certificate is assumed.  The proof constructs the diffuse
profile and proves its unrestricted terminal bound.  The direct gadget
consumer is `(6)`; the optional game-semantic consumer is the checked
fixed-target terminal-all-errors theorem.

## Lean handoff

A narrow formalization should define the augmented relation and prove a finite
sink lemma, then target a quantitative statement such as

```text
terminalExploitability_soloStationary_le_pairPremium
  (hsinkOwner : 0 <= solo owner owner)
  (hsinkOther : forall j != owner, solo j j <= solo owner j) :
  exploitability (soloStationary owner q) <= q * pairPremium owner
```

The existing stationary singleton identities and cap theorems in
`UniformEquilibrium/Quitting/Stationary/SingletonStationaryRoot.lean` should
replace a fresh behavioral-strategy development.  Useful declarations include

```text
quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
quittingStationaryUnilateralCap_solo_other
quittingTerminalPayoff_update_stationary_le_unilateralCap
exists_quitNow_or_never_terminalPayoff_eq_unilateralCap
```

The all-Never arm should call the existing zero-solo theorem.  The exact
strict-sink corollary can call
`isεAsymptoticNash_soloStationary_exact_iff`.  The graph theorem should expose
the quantitative profile and target-mass conclusion, not store either as a
source-structure field.

Regression tests should include the weak equality table, the rational strict
table, a one-player sink, and a cyclic graph where no sink argument is
available.

## Scope and nonclaims

- The theorem covers exactly acyclic augmented strict solo-preemption graphs.
- It places no restriction on coalitions of cardinality at least three.
- It controls arbitrary unilateral behavioral deviations, not only pure or
  stationary deviations.
- It does not say that a directed cycle produces the requested gadget.
- It does not cover the already surviving cyclic architecture.
- It does not construct a positive gadget or settle the finite-quitting
  conjecture.
