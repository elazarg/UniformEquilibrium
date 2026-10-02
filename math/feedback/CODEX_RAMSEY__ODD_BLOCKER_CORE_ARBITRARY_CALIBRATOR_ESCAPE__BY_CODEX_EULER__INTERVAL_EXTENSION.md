# Review of the interval-passive odd-core extension

Reviewer: `CODEX_EULER`

Verdict: **PASS** as ordinary mathematics in the stated universal
all-behavior architecture scope.  This is a fresh review of the appended
interval-sandwich theorem; it does not rely on the reviews of the original
constant-continuation result.  The face persistence, odd alternation,
endogenous endpoint algebra, arbitrary-calibrator limit, unrestricted
stationary compiler, strict-extension example, and likelihood-ratio boundary
all check.  No repair is required.

## Claim audited

For every core player `i`, define the extrema of literal continuation rows,
blocker-absent Quit rows, and blocker-present Quit rows by

```text
C_i^- <= C_i^+,
H_i^-,
L_i^+,
```

and assume

```text
L_i^+ < C_i^- <= C_i^+ < H_i^-.
```

On an odd cyclic core of cardinality at least three, with completely arbitrary
calibrator payoff coordinates, the theorem constructs a stationary exact
terminal Nash profile whose core rates are all strictly interior and whose
stationary payoff is a uniform-equilibrium payoff against unrestricted
behavioral deviations.

## Constrained Kakutani and endpoint formula

On

```text
[epsilon,1]^K x [0,1]^(I\K),
```

every player has a positive-rate core opponent.  Hence every deleted
opponent-absorption probability `delta_i` is positive and the stationary
payoff

```text
F_i(p;q_-i)=[p Q_i+(1-p)A_i]/[delta_i+p beta_i]
```

is continuous.  Its derivative has the constant sign of `Q_i-N_i`, with
`N_i=A_i/delta_i`; therefore the own-rate maximizer is the lower endpoint,
upper endpoint, or whole interval.  The product best-response correspondence
has nonempty compact convex values and closed graph, so Kakutani supplies the
constrained stationary Nash point.  No pure or stationary completeness is
being assumed at this stage.

For a core continuer, `N_i` is the conditional expectation of literal
nonempty opponent coalitions omitting `i`.  Thus it is genuinely a convex
combination and

```text
C_i^- <= N_i <= C_i^+
```

uniformly on every constraint box.

## Face persistence and odd alternation

Condition on the blocker action in the forced-Quit endpoint.  If the blocker
rate tends to zero, the blocker-absent conditional part has value at least
`H_i^-`, while the bounded blocker-present contribution has vanishing weight.
Consequently

```text
liminf Q_i >= H_i^- > C_i^+ >= N_i,
```

so `Q_i>N_i` eventually.  If the blocker rate tends to one, the same argument
gives

```text
limsup Q_i <= L_i^+ < C_i^- <= N_i,
```

so `Q_i<N_i` eventually.  The strict finite-row gaps make these eventual
signs uniform; no convergence of a conditional posterior is assumed.

A limiting zero rate therefore forces its predecessor to equal the upper
endpoint `1`; the next predecessor is forced to the lower endpoint
`epsilon_m`, hence tends to zero.  Backward iteration alternates `0,1` around
the blocker permutation.  Odd cycle length makes the returning value
inconsistent.  A limiting one immediately forces a predecessor to zero and
is excluded by the first argument.  Thus every limiting core rate lies in
`(0,1)`.

For large indices each core coordinate is strictly inside
`[epsilon_m,1]`, so constrained optimality gives `Q_i=N_i`.  Positive limiting
core rates keep all relevant deleted absorption denominators uniformly away
from zero, allowing this equality and every calibrator best-response
inequality to pass to the limit.

## Exact stationary and unrestricted semantics

At the limit, a core player's common endpoint value is `N_i` and

```text
A_i+beta_i N_i=delta_i N_i+beta_i N_i=N_i.
```

For a calibrator, fractional linearity gives the usual exact endpoint
inequalities at rate zero, interior, or one.  The stationary payoff equation
therefore gives both an exact Bellman fixed point and endpoint Nash root.

Every player has a positive-rate core opponent: a core player has at least two
other core labels, while a calibrator has the entire core.  Hence joint and
all player-deleted Continue products are strictly below one.  The named
stationary endpoint compilers consequently cover replacement of an entire
behavioral strategy, including history dependence, randomization, and Never,
and yield the uniform payoff.  Arbitrary calibrator rewards have entered only
through their actual constrained best responses.

## Tests and sharp boundary

The explicit three-core/one-calibrator table has

```text
C_i^-=0, C_i^+=1, H_i^-=2, L_i^+=-1.
```

At core rates `1/3` and calibrator rate `1`, each core Quit endpoint is
`2*(2/3)-1*(1/3)=1`, and its Continue endpoint is also `1`; the calibrator
strictly Quits.  Since a core continuer receives zero without the calibrator
and one with it, no constant passive baseline exists.  This is an exact
strict-extension witness.

The likelihood-ratio regression is also exact.  With blocker rate `epsilon`
and third-core rate `epsilon^2`, its table gives

```text
Q_i=1+8 epsilon,
N_i=10/(1+epsilon-epsilon^2),
```

so `Q_i-N_i -> -9` even though every same-background join comparison has the
desired `+1/-1` toggle sign.  Rare opponent absorption amplifies the blocker
continuation row.  This proves that backgroundwise signs alone do not justify
the liminf/limsup step and that the interval sandwich is substantive.

## Source and scope

The checked `BlockerSwitch` and `ConditionalFaceGap` theorems constrain every
player and therefore do not absorb arbitrary calibrator coordinates.  The
reviewed exported passive-core theorem fixes each core continuation payoff;
it does not imply this interval-valued extension.  The new theorem genuinely
widens that architecture while retaining the exact arbitrary-calibrator and
unrestricted-deviation conclusion.

It does not cover even cores, weak band inequalities, background-dependent
sign reversal, overlap of the three bands, or other negative-cycle
architectures.  It does not construct the pair-mass incentive gadget or prove
that every negative-cycle table has a uniform payoff.  If exported as an
unrestricted strategy-class theorem, it still requires the separate packet
gate and mandatory second independent falsification review.
