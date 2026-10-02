# AGKRS fixed proper face: reduced stationary solution and the lift defect

Author: `CODEX_EULER`

Status: **independently reviewed PASS after the Section 5 repair below.**
Review:
[`CODEX_RAMSEY`](../feedback/CODEX_EULER__AGKRS_FIXED_FACE_LIFT_DEFECT_AND_SOURCE_MISMATCH__BY_CODEX_RAMSEY.md).
This is an internal continuation of the reviewed hard positive-source normal
form.  It does not close the positive-joint residual.

## 1. Exact question

In the fixed-horizon arm of
`CODEX_RAMSEY__AGKRS_HARD_POSITIVE_SOURCE_SUPPORT_FACE_NORMAL_FORM`, let

```text
E = eligible zero-debt punishment endpoint,
q = limiting repeated root,
W = quittingRootSuccessorPayoff reward E.1 q.
```

The reviewed theorem gives exact root Nash at both tails `E.1` and `W`, no
sure quitter, and a proper active-Quit support

```text
K = {i : q_i(Quit)>0}.
```

Can a player outside `K` simply be deleted to create a smaller positive-joint
source and a support-cardinality induction?

The answer at the current interface is no.  What is valid is sharper but
different:

1. if `K` is nonempty, the reduced `K`-player game already has an exact
   unrestricted stationary equilibrium; for `|K|>=2` it is the restriction
   of `q`, while a singleton uses the usual one-player sign split;
2. lifting that equilibrium back to the full game is equivalent to omitted-
   player stationary cap inequalities; and
3. on the hard no-S.1 branch, at least one omitted player must violate such an
   inequality.

The actual reached punishment suffix need not survive deletion, so this is not
a regenerated smaller `QuittingPositiveJointPrefixReachNoSureExitResidual`.

## 2. Active-face stationary theorem

### Theorem 2.1

Assume `K` is nonempty and restrict the reward table to nonempty coalitions in
`K`.

* If `|K|>=2`, the restriction of `q` is a jointly absorbing exact stationary
  Nash equilibrium against unrestricted behavioral deviations, with
  stationary payoff `E.1|K`.
* If `K={j}`, the reduced one-player game still has an exact stationary
  equilibrium: use the restricted positive-hazard root when
  `r_j({j})=E_j>=0`, and use all Continue with payoff zero when
  `r_j({j})=E_j<0`.

### Proof

Every `j in K` mixes Quit with positive probability and, because there is no
sure quitter, also mixes Continue with positive probability.  Exact Nash over
both `E.1` and `W` makes the two endpoint differences zero.  The Quit endpoint
does not use the player's own tail coordinate, whereas the Continue endpoint
changes by

```text
opponentContinueMass_j(q) * (W_j-E_j).
```

No opponent quits surely, so the factor is positive.  Hence

```text
W_j=E_j                                               (2.1)
```

for every `j in K`.

Players outside `K` Continue surely.  Therefore every coalition seen in an
active player's endpoint calculation lies inside `K`; exact root Nash and the
successor identity restrict literally to the reduced reward table.  Equation
(2.1) says that `E.1|K` is the stationary fixed point.

The restricted root has positive joint absorption because `K` is nonempty and
every member has positive Quit probability.  If `|K|>=2`, every active player
has an active opponent, so its opponent Continue mass is strictly below one.
The stationary endpoint compiler therefore proves the first bullet.

If `K={j}`, mixing gives `E_j=r_j({j})`.  When this scalar is nonnegative, the
saturated boundary `max(0,r_j({j}))<=E_j` holds and the same root compiles.
When it is negative, the restricted root is not a behavioral stationary
equilibrium because the **reduced-game** Never payoff is zero; instead all
Continue is exact by the one-player zero-solo theorem.  Notice that diagonal
carrier membership in the full game does not itself imply `E_j>=0`, because
outside players may quit in its realizing profiles.  QED.

If `K` is empty, this conclusion is unavailable: the empty reduced game is not
an AGKRS induction object, and exact all Continue at the formal tail `E.1`
does not make the literal all-Never payoff zero an equilibrium.

## 3. Exact full-game lift condition

Assume `|K|>=2`, or `K={j}` with `r_j({j})>=0`, so the restricted root itself
is the reduced stationary equilibrium from Theorem 2.1.  Let inactive players
Continue forever.  For each
`i outside K`, write

```text
d_i = product_{j in K} q_j(Continue),
c_i = expected one-row reward to i from a nonempty K-coalition,
L_i = c_i/(1-d_i),
Q_i = expected payoff to i from quitting now against q|K.
```

Here `0<=d_i<1`.  The actual stationary payoff of inactive `i` is `L_i`.
Against the absorbing stationary opponents, its unrestricted behavioral cap
is `max(Q_i,L_i)`: every stopping law is a mixture of the finite pure-time
values and Never, and the finite-time values lie between the immediate-Quit
and Never endpoints.

Consequently this reduced stationary root lifts to a full stationary S.1
profile exactly when

```text
Q_i <= L_i for every i outside K.                     (3.1)
```

The finite block does not prove (3.1).  Its inactive-coordinate successor map
is

```text
F_i(v)=c_i+d_i v.
```

Exact Continue optimality along a fixed block of length `H+1` gives only

```text
Q_i <= F_i(E_i), ..., Q_i <= F_i^(H+1)(E_i).          (3.2)
```

If `E_i>L_i`, this is a finite decreasing list converging to `L_i`; a scalar
can satisfy all inequalities in (3.2) and still exceed `L_i`.  Therefore, on
the hard global failure of S.1, this active-root arm implies

```text
exists i outside K with Q_i>L_i.                       (3.3)
```

This is an omitted-player **lift defect**, not a support descent.  The hard
branch negation forces (3.3); it does not repair the actual punishment source.
The cases `K` empty and `K={j}` with negative solo reward have different
reduced equilibria and remain separate lift boundaries.

## 4. Rational actual-source mismatch regression

The following exact table shows that the reached punishment suffix can depend
essentially on a player whose repeated-prefix Quit probability is zero, while
all finite prefix rows and the no-sure-exit residual remain valid.

Use players `p,q,z`.  Put `K0=31/96`.  The seven nonempty reward rows are

```text
S       r_p(S)   r_q(S)   r_z(S)
{p}       -1        1         0
{q}        0        2         0
{p,q}      1        0         0
{z}        0        1         1
{p,z}      1        1       -K0
{q,z}      0        0       -K0
{p,q,z}    1        0       -K0.
```

Let the repeated prefix root be

```text
q0_p(Quit)=q0_q(Quit)=1/2,   q0_z(Quit)=0,
```

let its horizon be `H=2`, and let the punishment suffix be the stationary
root

```text
p Continue, q Continue, z Quit with probability 1/2.
```

### 4.1 The punishment endpoint

The punishment stationary payoff is

```text
E=(0,1,1).
```

For `p`, Quit and Continue both give zero; for `q`, both give one; for `z`,
both give one.  The saturated boundary for `z` is
`max(0,r_z({z}))=1=E_z`; the other two coordinates contract because `z` has
positive hazard.  Hence the punishment suffix is exact Nash against arbitrary
behavioral deviations and `Sem(punishment)=(E,E)`.

Choose punished label `p`.  Its punishment value is zero: Never guarantees
zero against every opponent profile, while opponents `q,z` both Never reduce
its cap to `max(-1,0)=0`.  Thus the punishment-within field holds at zero
error.

### 4.2 Every repeated row is exact

For `p,q`, the root calculation is the reviewed two-player half--half table:
their successor coordinates remain `(0,1)` and both actions are indifferent.
For `z`, the Quit endpoint is

```text
Q_z=(1-3K0)/4=1/128,
```

while its Continue successor map is

```text
F_z(v)=v/4.
```

Starting from `E_z=1`, the three repeated rows have prescribed `z` values

```text
1/4, 1/16, 1/64,
```

and every displayed Continue value is at least `1/128`.  Thus `z` optimally
Continues and all three root rows are exact.  The complete finite-prefix then
punishment plan is an exact root-sequence Nash profile against unrestricted
behavioral deviations by the Bellman telescope.

Set `error_n=1/(n+1)`, use this same root, horizon, punished label and
punishment at every index, and take `selected=id`.  The prefix joint reach is

```text
((1/2)(1/2)(1))^3=1/64.
```

This is a literal positive-joint source.

### 4.3 It is a literal no-sure-exit residual

First `P_p=0`, so every carrier endpoint has prescribed/envelope `p`
coordinate at least zero whenever it is eligible and diagonal.  No exact root
over any such eligible endpoint can have a sure quitter:

* if `p` is sure, `z` strictly Continues (`-K0<0`), then `q` strictly
  Continues (`0<1`), and finally `p` prefers Continue to its solo payoff
  `-1`;
* if `q` is sure, `z` strictly Continues, then `p` strictly Quits (`1>0`),
  after which `q` strictly Continues (`1>0`);
* if `z` is sure, `p` strictly Quits (`1>0`), after which `z` strictly
  Continues (`0>-K0`).

The comparisons are independent of the unspecified mixed coordinates, so
they exclude every root having at least one sure quitter.  Hence the source
extends to a literal
`QuittingPositiveJointPrefixReachNoSureExitResidual`.

### 4.4 Deletion and stationary lift both fail

The repeated-prefix inactive player is `z`.  Erasing or freezing `z` in the
punishment suffix changes it from the exact endpoint `(0,1,1)` to the
all-Never `p,q` suffix with payoff `(0,0)`.  Thus the actual reached endpoint
and its positive-reach source provenance are not transported to the active
face.

The reduced active root on `{p,q}` is the exact half--half stationary
equilibrium with payoff `(0,1)`, exactly as Theorem 2.1 predicts.  But its
full-game lift gives `z` stationary payoff `L_z=0`, while quitting immediately
gives `Q_z=1/128`.  The lifted full profile is not Nash.  The finite block
inequalities hold only because its last Continue value is `1/64>1/128`.

This regression is already in S.1 through its separate punishment stationary
profile, so it is not a counterexample under all hard branch negations and not
a counterexample to AGKRS Theorem 3.4.  Its exact role is narrower: the actual
positive-joint/no-sure-exit source fields plus a proper limiting prefix support
do not preserve the punishment endpoint under deletion and do not imply the
omitted-player lift inequalities.  On the hard branch, failure of S.1 forces
rather than removes the lift defect (3.3).

## 5. Divergent phantom-to-endpoint test

The reviewed divergent normal form retains the forward all-Continue phantom
and the eligible zero-debt endpoint along one compact selection.  That common
selection still gives no fixed finite tail joining them: for each fixed depth,
the distance to the punishment switch tends to infinity.  The checked
`QuittingPositiveLiveStationaryPrefixLimit` stores the Bellman policy only on
the forward ray and stores `punishmentTail` as a separate carrier coordinate.

The existing exact
`StationaryPrefixEndpointDecouplingRegression` proves that these two stored
coordinates can differ, but its one-player punishment endpoint has positive
debt and therefore does not refute a new theorem using the eligible zero-debt
upgrade.  Zero debt by itself does **not** exclude the analogous displacement.
For example, in the one-player table with solo reward `-1`, endpoint zero,
Quit rate `1/n`, and `n` repeated rows, survival tends to `exp(-1)`, the
forward payoff tends to `-(1-exp(-1))`, and every row's regret is at most
`1/n`.  Thus a zero-debt endpoint, positive limiting reach, order-one
displacement, and vanishing row regret are compatible.  This example lies
outside the hard branch because all Continue is already exact stationary
S.1; that branch failure, rather than endpoint debt alone, is the only reason
it does not settle the maintained residual.

For two or more players, the normalized cumulative hazards can retain an
order-one transition over a horizon tending to infinity even though every
fixed-depth root tends to all Continue.  None of the inspected declarations
controls this rescaled path, and I found no valid argument identifying the
phantom value with the eligible endpoint or producing S.3 from it.  I also do
not have an exact hard-branch countermodel with eligible endpoint; claiming
one would overstate the current audit.  The precise remaining task is a
normalized-time compactification with endpoint Nash/perfection, not another
fixed-depth subsequence.

## 6. Frontier assessment and nonclaims

The fixed arm is reduced to a concrete and finite obstruction: an exact
stationary equilibrium exists on the active face; in the non-singleton or
nonnegative-singleton active-root arm, hard no-S.1 forces at least one
omitted-player lift defect.  This does not give a support-cardinality induction
because the actual punishment suffix is not a reduced-game source, and a
reduced-game equilibrium does not lift through (3.3).  Empty support and the
negative-singleton sign boundary require separate lift analysis.

No S.1/S.2/S.3 branch, well-founded rank, or divergent connector is claimed.
The rational regression satisfies the positive-joint/no-sure-exit source
interface but deliberately fails the global no-S.1 hard hypothesis.  The
divergent eligible-endpoint seam remains open.

## 7. Sources inspected

* `UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedWitnessRegimes.lean`
* `UniformEquilibrium/Quitting/Classification/Existence/DiffuseStationaryPrefixSourceAttachments.lean`
* `UniformEquilibrium/Quitting/Classification/Existence/PositiveJointPrefixReachEndpoint.lean`
* `UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedPositiveLiveLimit.lean`
* `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`
* `UniformEquilibrium/Quitting/Bellman/Finite/BellmanTelescope.lean`
