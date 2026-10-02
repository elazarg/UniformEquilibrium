# Independent audit of the acyclic solo-preemption no-go

Reviewer: `CODEX_EULER`

Verdict: **PASS with two statement-level repairs**.  The acyclic-sink
argument, terminal exploitability bound, and exact strict-sink inequality are
correct.  The displayed exact rate is rational only under rational reward
data, and the no-outsider case needs a convention or separate clause.

## Claim audited

Let the finite directed graph have vertices `I` together with `bottom`, and
edges

```text
bottom -> i  iff r_i({i}) > 0,
i -> bottom  iff r_i({i}) < 0,
i -> j       iff r_j({j}) > r_j({i})       (i != j).
```

The proposed conclusion is that acyclicity prevents a fixed positive
terminal exploitability gap.  A sink `bottom` gives all-Never.  A player sink
`p` gives a solo stationary profile: `p` Quits at each live date with rate
`q>0`, and every other player always Continues.

## Sink orientation

The orientation is correct.

- If `bottom` is a sink, absence of `bottom -> i` gives
  `r_i({i})<=0` for every `i`.  Against all-Never, every finite Quit time pays
  `r_i({i})`, while Never pays zero.  Hence all-Never is exact terminal Nash.
- If `p` is a sink, absence of `p -> bottom` gives `r_p({p})>=0`.  Absence of
  `p -> j` gives

  ```text
  r_j({j}) <= r_j({p})
  ```

  for every `j!=p`.  These are exactly the owner and inactive-player signs
  used below.

A finite acyclic digraph has a sink, so the graph step itself is complete.
Equalities correctly produce no edge and are handled by the weak inequalities
at the sink.

## Pure times and arbitrary behavioral deviations

Put `a=1-q`.  For `j!=p`, if `j` Quits at deterministic live date `t`, with
dates starting at zero, then

```text
V_j(t)-r_j({p})
 = a^t [a (r_j({j})-r_j({p}))
          + q (r_j({p,j})-r_j({p}))].               (1)
```

This includes the endpoint conventions exactly.

- At `t=0`, the owner Continues with probability `a`, producing `{j}`, and
  Quits with probability `q`, producing the tie `{p,j}`.
- At `t=infinity` (Never), `p` exits eventually with probability one because
  `q>0`, and the value is `r_j({p})`; equivalently the gain in (1) is zero.

Before absorption there is only one public live history: every previous
action was Continue.  Thus an arbitrary behavioral deviation by `j` induces
a law on `N union {infinity}`, and its payoff is the expectation of the
corresponding deterministic-time values.  The repository proves this more
generally through pure-time extremality and the stationary Snell cap.  In
particular, the relevant checked declarations are

```text
quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
quittingStationaryUnilateralCap_solo_other
quittingTerminalPayoff_update_stationary_le_unilateralCap
exists_quitNow_or_never_terminalPayoff_eq_unilateralCap
```

in `Quitting/Stationary/SingletonStationaryRoot.lean`,
`Quitting/Boundary/Exceptional/TailFallback.lean`, and
`Quitting/Stationary/BestResponse.lean`.

Under a unilateral deviation the only absorbing coalitions are `{p}`, `{j}`,
and `{p,j}`.  If the deviator is `p`, only `{p}` can absorb.  No coalition of
cardinality at least three can occur; this is not an implicit assumption
about its reward.

## Exploitability constant

Define, with positive part taken before the finite maximum,

```text
J_p = max_{j!=p} (r_j({p,j})-r_j({p}))_+ >= 0.
```

For every `j!=p`, the sink inequality and (1) give

```text
V_j(t)-r_j({p}) <= a^t q J_p <= q J_p.
```

The same bound therefore holds for every behavioral deviation.  Player `p`
faces all-continuing opponents; every finite stopping law pays `r_p({p})` and
Never pays zero.  Since `r_p({p})>=0`, `p` has no positive gain over the
prescribed profile.  The profile exploitability is therefore at most `q J_p`.

For every `epsilon>0`,

```text
q = min(1/2, epsilon / (2(J_p+1)))
```

lies in `(0,1)` and satisfies `q J_p < epsilon`.  Hence no fixed positive
all-profile terminal exploitability gap is possible in the acyclic graph
class.

## Strict sink and exact rate

Assume there is at least one outsider and put

```text
d_p = min_{j!=p} (r_j({p})-r_j({j})) > 0.
```

The immediate-Quit endpoint difference of any outsider is bounded by

```text
(1-q)(r_j({j})-r_j({p}))
  +q(r_j({p,j})-r_j({p}))
 <= -(1-q)d_p + q J_p
  = -d_p + q(d_p+J_p).                              (2)
```

Thus every

```text
0 < q <= d_p/(d_p+J_p)
```

makes the solo stationary profile exact terminal Nash.  The proposed choice

```text
q = d_p/[2(d_p+J_p)]
```

is positive, at most `1/2`, and satisfies (2).  If `J_p=0`, it reduces to
`q=1/2` and remains valid.  The strictness `d_p>0` is essential: when
`d_p=0` and some pair premium is positive, every `q>0` can leave a positive
inactive-player gain.

### Required rationality repair

For an arbitrary real reward table the displayed quotient need not be
rational.  For example, `d_p=sqrt(2)` and `J_p=1` give an irrational displayed
rate.  The claim should say one of the following.

1. The displayed formula is an exact **real** rate.
2. If every reward entry is rational, then `d_p`, `J_p`, and the displayed
   rate are rational.
3. For arbitrary real rewards, choose a positive rational
   `q<d_p/(d_p+J_p)` by density; this gives a rational exact rate, but not the
   displayed closed formula.

If `I\{p}` is empty, the maximum/minimum defining `J_p,d_p` is also empty.
The one-player game should be split off (any `q in (0,1]` is exact when
`r_p({p})>=0`) or explicit empty-extremum conventions should be declared.

## Existing stronger code and novelty

The game-semantic core is already stronger than a pure-time calculation.
The checked theorem

```text
quittingStationarilyGeneratedApproximateEquilibria_of_normal_noHarmSingleton
```

in
`Quitting/Classification/Existence/NoHarmSingletonGenerated.lean` consumes a
no-harm singleton owner and punishment normality to produce the maintained
stationarily generated approximate-equilibrium branch.  A player sink gives
the no-harm inequalities above, and `r_p({p})>=0` plus the general bound
`quittingPunishmentValue_le_max_solo` supplies punishment normality.

At a fixed rate, the still sharper checked declarations

```text
isεAsymptoticNash_soloStationary_exact_iff
isUniformEquilibriumPayoff_soloReward_of_inactive
```

in `Quitting/Punishment/OwnerSoloCertification.lean` give the exact
all-behavior endpoint characterized by (2).

Accordingly the proposed theorem is valid and useful as a transparent graph
corollary and as an `INCENTIVE_GADGET` architecture no-go, but its strategic
content is subsumed by these checked solo-owner results.  It is not a new
general equilibrium theorem and says nothing about tables whose solo-
preemption graph contains a directed cycle.
