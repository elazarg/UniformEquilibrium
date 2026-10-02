# Predictable single-owner derandomization

Author: `CODEX_CEDAR`

Status: `UNIVERSAL ONE-ACTIVE THESIS CLOSED BY ACTUAL RESIDUAL-HARD TABLE;
PARTIAL COMPILER AND INTERFACE COUNTEREXAMPLE RETAINED`

Conjecture-closing thesis tested here: every finite source-matched sunspot packet in which
at most one player has positive quit hazard in each live row can be converted
to an ordinary deterministic causal branch schedule with shrinking,
nonsummable hazards.  The conversion must approximate the public lottery on
**every continuation suffix**, keep every active owner nearly indifferent,
and cap every deterministic quit-time deviation.  Applied to the Q branch of
Solan--Solan's construction and then to the terminal positive endpoint, this
would prove the finite-quitting uniform-equilibrium-payoff conjecture.

This thesis is distinct from the Simon `F_epsilon` orbit-necessity route and
from finite-depth punishment-floor/source-matching chains.  Its main object is
a deterministic discrepancy/derandomization theorem for a supplied finite
single-owner Bellman packet, followed by an exact semantic adapter to ordinary
private behavioral coins.

Precise universal obligation now under attack: for a finite branch alphabet
`K`, target weights `z in Delta(K)`, bounded branch reward/drift data, and
owner map `o:K->I`, construct one deterministic word `k_0,k_1,...` and hazards
`q_t↓0`, `sum q_t=infinity`, such that for every start time `m` and every end
time or pure quit time `T>=m`:

```text
weighted branch counts on [m,T) = z-weighted total charge + o(total error),
owner-weighted Bellman drift on [m,T) has the required one-sided sign,
collision/deleted-clock error is summable at the construction scale,
and the tail from m lands at the same fixed target up to o(1).
```

The order of quantifiers is essential: the schedule is fixed before the
deviator selects `T`, and the estimate must hold uniformly over every suffix
`m`, not only from time zero or in global frequency.

Kill criterion: abandon this route if one finite source-matched single-owner
packet admits an exact predictable-calendar exploitability gap bounded away
from zero for **every** deterministic schedule and every shrinking
nonsummable hazard choice satisfying the packet frequencies.  A two-owner
counterexample, a global-prefix discrepancy failure, or a schedule without
the source Bellman identities does not kill the thesis.

Current checkpoint: the paper-facing source is only
`theorem2_13_sunspot` (`Literature/SolanAndSolan2020.lean`), contains `sorry`,
and is not imported by production.  The checked semantic tools selected for
this route are
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`
(`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`),
`collisionMass_logarithmicBlock_le_sq`
(`UniformEquilibrium/Quitting/AbsorptionPath/LogarithmicBlockDiscretization.lean`),
and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
No ordinary single-owner packet producer or compiler is currently claimed.
Propositions 1--3 below prove the deterministic compiler for a common-target
packet with a deleted-clock drift sign.  Proposition 4 gives an exact
three-player `BuildingBlock` for which a public one-draw implementation is an
exact sunspot Nash profile but every faithful ordinary schedule using its two
positive-weight owners has a fixed refusal gap near the same target.  This
refutes derandomization from the literal `BuildingBlock` fields alone.
Crucially, that matrix has a homogeneous simplex LCP solution, so it violates
the actual Q-branch hypothesis `hzero`; Proposition 4 alone does **not** refute
the source-matched thesis.

The thesis is nevertheless closed by an earlier, stronger actual-source
falsifier.  The checked declaration `periodTwo_residualHardClass`
(`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`)
places the Solan--Vieille `boundaryReward` table in the full-normal
standard-Q/no-homogeneous residual-hard class.  The independent audit in
`feedback/CLAUDE_HILBERT__SINGLETON_LOTTERY_LIMITS__BY_CODEX_CEDAR__ROUND_2.md`
validates a fixed positive terminal exploitability floor for **every**
ordinary profile with at most one positive hazard at each live date.  The
same table has the checked genuinely two-active endpoint
`periodTwo_isUniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean`).
Thus universal one-active derandomization is false as an architecture, while
the full conjecture remains intact.

Next concrete check for this closed note: none.  Propositions 1--4 remain
useful partial mathematics, but the `hzero` source-adapter question is not a
conjecture-closing next step.

All work in this notebook is ordinary mathematics unless explicitly attached
to a named checked declaration.  No Lean file or export is proposed.

## 1. Source and declaration ledger

Read before starting mathematics:

- `SOURCES.md`, `GOAL.md`, and
  `questions/PREDICTABLE_SINGLE_OWNER_DERANDOMIZATION.md`;
- the exact statement and nearby construction fields of
  `Literature.SolanAndSolan2020.theorem2_13_sunspot` in
  `Literature/SolanAndSolan2020.lean`; and
- the three checked declarations named in the current checkpoint above.

The literature lane is paper-facing, non-built, and uses `sorry`; it is source
evidence, not an `L`, `A`, or `C` seal for the proposed derandomization.

## 2. Periodic discrepancy survives arbitrary decreasing weights

Let `K` be a finite alphabet and let `z` be rational probability weights.
Choose a period word

```text
k_0,...,k_{L-1}
```

which contains each letter `k` exactly `L*z_k` times, and extend it
periodically.  Let `f:K->R^d` have zero `z`-mean.  Define the interval
discrepancy

```text
D_f = sup_{m<=N} ||sum_{t=m}^N f(k_t)||_infinity.
```

This is finite; the crude bound `D_f<=2L*max_k ||f(k)||_infinity` suffices.

**Proposition 1 (ordinary mathematics; weighted every-suffix discrepancy).**
For every start `m` and every nonnegative nonincreasing weight sequence
`w_m>=w_{m+1}>=...` tending to zero,

```text
||sum_{t=m}^infinity w_t*f(k_t)||_infinity <= D_f*w_m.  (2.1)
```

The same bound holds for every finite upper endpoint `N` if the last weight
is set to zero after `N`.

**Proof.**  Work coordinatewise and put

```text
F_n=sum_{t=m}^n f(k_t),  ||F_n||_infinity<=D_f.
```

Finite Abel summation gives

```text
sum_{t=m}^N w_t f(k_t)
 = w_N F_N + sum_{t=m}^{N-1}(w_t-w_{t+1})F_t.
```

Its norm is at most

```text
D_f*(w_N+sum_{t=m}^{N-1}(w_t-w_{t+1}))=D_f*w_m.
```

For the infinite series, let `N` tend to infinity; the displayed estimate is
Cauchy on tails and `w_N F_N` tends to zero.  A finite cutoff is the same
calculation after extending the weights by zero.  QED.

This is stronger than global frequency matching.  The start `m`, endpoint,
and decreasing weight sequence may all be selected after the deterministic
calendar is fixed.  Survival weights therefore fit without a new randomness
argument.

## 3. A rational single-owner Bellman packet lands from every suffix

Here is the smallest exact packet for testing the thesis.  For each branch
`k in K`, fix:

- an owner `o(k)`;
- a coefficient `c_k>=0`;
- an absorbing payoff vector `r^k`; and
- one common candidate continuation target `v`.

Assume

```text
sum_k z_k*c_k*(r^k-v)=0.                              (3.1)
```

Choose rational `theta>0` and an integer `M` so large that

```text
q_t=theta/(M+t),   q_t*c_k<=1 for every t,k.          (3.2)
```

At date `t`, only player `o(k_t)` has positive prescribed quit probability,
namely `q_t*c_(k_t)`.  All other players Continue.

Assume at least one branch with `c_k>0` has positive `z_k`.  Because that
branch recurs once per period and the harmonic sum on its arithmetic
progression diverges,

```text
sum_t q_t*c_(k_t)=infinity.
```

Consequently prescribed absorption occurs almost surely.  For a suffix
starting at `m`, write

```text
S_(m,t)=product_{s=m}^{t-1}(1-q_s*c_(k_s))
```

and let `V_m` be its terminal payoff vector.

**Proposition 2 (ordinary mathematics; every-suffix landing).**  Let

```text
f(k)=c_k*(r^k-v)
```

and let `D_0=D_f` be its interval discrepancy from Proposition 1.  Then

```text
||V_m-v||_infinity <= D_0*q_m                  for every m.  (3.3)
```

**Proof.**  Almost-sure absorption gives

```text
V_m-v
 = sum_{t=m}^infinity S_(m,t)*q_t*c_(k_t)*(r^(k_t)-v)
 = sum_{t=m}^infinity w_t*f(k_t),
```

where `w_t=S_(m,t)*q_t`.  Both factors are nonincreasing in `t`, and `q_t`
tends to zero, so `(w_t)` is nonnegative, nonincreasing, and tends to zero.
Proposition 1 gives norm at most `D_0*w_m=D_0*q_m`.  QED.

Thus the deterministic future being known does not by itself disturb the
target: every continuation suffix lands within `O(q_m)`, uniformly over the
suffix chosen after the word is announced.

## 4. Deleted-clock drift and every pure quit time

Fix a player `i`.  Deleting `i`'s prescribed clock leaves branch coefficient

```text
c_i^-(k)=c_k if o(k)!=i, and 0 if o(k)=i.
```

When an opponent-owned branch absorbs, player `i` receives coordinate
`r^k_i`.  Assume the packet satisfies the deleted-clock mean inequality

```text
bar_f_i := sum_k z_k*c_i^-(k)*(r^k_i-v_i) <= 0.       (4.1)
```

Let

```text
g_i(k)=c_i^-(k)*(r^k_i-v_i)-bar_f_i
```

and denote its interval discrepancy by `D_i`.  Also assume the zero-mesh
quit-now and Never caps

```text
s_i <= v_i+eta,          v_i >= -eta,                 (4.2)
```

where `s_i=r({i})_i` is the solo reward.  Let `B` bound every terminal payoff
in absolute value and put `c_max=max_k c_k`.

**Proposition 3 (ordinary mathematics; unrestricted-deviation compiler for
the common-target packet).**  From every suffix `m`, every unilateral
behavioral deviation of player `i` gains over the prescribed profile by at
most

```text
2*eta + (D_0+D_i+2*B*c_max)*q_m.                     (4.3)
```

If pure Never is treated separately, its bound improves by omitting the
collision term `2*B*c_max*q_m`.

**Proof.**  By
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`
(`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`), it is
enough to bound every deterministic quit time, including Never.

For a finite quit time `T>=m`, use the opponent-only survival

```text
S_i^-(m,t)=product_{s=m}^{t-1}(1-q_s*c_i^-(k_s)).
```

Before `T`, opponent absorption contributes `r^(k_t)_i`.  At `T`, if the
active owner is distinct from `i`, simultaneous collision has probability at
most `q_T*c_max`; replacing the solo payoff by the corresponding joint payoff
changes the conditional quit value by at most `2B*q_T*c_max`.  If `i` is the
active owner, its deviation overwrites its own hazard and there is no opponent
collision.  Hence the conditional date-`T` quit value `Q_i(T)` obeys

```text
Q_i(T) <= v_i+eta+2*B*c_max*q_T.                     (4.4)
```

The exact stopped-payoff decomposition is

```text
D_i(T)-v_i
 = sum_{t=m}^{T-1} S_i^-(m,t)*q_t*c_i^-(k_t)
       *(r^(k_t)_i-v_i)
   + S_i^-(m,T)*(Q_i(T)-v_i).                        (4.5)
```

In the first sum, split the periodic letter function into `bar_f_i+g_i`.
The mean term is nonpositive by `(4.1)`.  The weights
`S_i^-(m,t)*q_t` are nonnegative and nonincreasing, so Proposition 1 bounds
the zero-mean part by `D_i*q_m`.  Equation `(4.4)` bounds the stopped term by
`eta+2B*c_max*q_m`.  Therefore

```text
D_i(T) <= v_i+eta+(D_i+2B*c_max)*q_m.                (4.6)
```

For pure Never, let `T` tend to infinity.  If opponent absorption is not
almost sure, the surviving event pays zero.  The decomposition acquires the
residual `-S_i^-(m,infinity)*v_i`, which is at most `eta` by `(4.2)`; the
weighted drift is still at most `D_i*q_m`.  Thus Never is covered by
`v_i+eta+D_i*q_m`.

Finally the prescribed payoff is at least `v_i-D_0*q_m` by Proposition 2.
Subtracting it from `(4.6)` gives at most

```text
eta+(D_0+D_i+2B*c_max)*q_m
```

for finite `T`, and at most
`eta+(D_0+D_i)*q_m` for Never.  The slightly looser common bound `(4.3)`
allows the same statement when `(4.2)` itself is supplied with `eta` slack in
both clauses.  Pure-time extremality transfers the result to every behavioral
deviation.  QED.

Since `q_m<=q_0`, choosing `M` large makes the error uniform over **all**
suffixes and all pure times.  The harmonic tail remains nonsummable, while

```text
sum_t q_t^2
```

can be made arbitrarily small by increasing `M`.  Thus any additional
collision or mesh estimate controlled by square hazard is compatible with the
same construction.

## 5. Proved, open, and source adapter

Proved above in ordinary mathematics:

- exact bounded discrepancy for every interval of a rational periodic word;
- its survival-weighted Abel transform for every suffix;
- common-target Bellman landing under harmonic single-owner hazards; and
- a full behavioral-deviation bound from deleted-clock mean drift, rowwise
  solo rationality, and the Never cap.

Not proved:

- that `theorem2_13_sunspot` supplies one **common-target** finite packet with
  `(3.1)`, `(4.1)`, and `(4.2)`;
- that its public-signal continuation states can be collapsed to this common
  `v` without changing the deviation ledger;
- a rational approximation theorem retaining all one-sided deleted-clock
  inequalities when the source weights are real; or
- a production Lean adapter/compiler.

The next source check is therefore exact and bounded: identify whether the
Q-branch kiloblock construction has a finite family of branch continuation
values `v^k` rather than one common `v`.  If so, replace `(3.1)` by a
telescoping edge equation and test whether the deterministic balanced word
must respect a directed transition graph.  Arbitrary frequency matching is
then insufficient unless the graph admits a bounded-discrepancy Eulerian
schedule whose every suffix retains the deleted-clock sign.

## 6. The literal `BuildingBlock` fields do not derandomize

This section tests the exact structure
`BuildingBlock` in `Literature/SolanAndSolan2020.lean`, not the full hypotheses
of `theorem2_13_sunspot`.

Take three players and let the singleton columns of `M` be

```text
M^1=(0,1,0),   M^2=(1,0,0),   M^3=(-1,-1,0).
```

Set `y=0`, `epsilon=1/4`, and

```text
wi^1=(0,1/2,0),
wi^2=(1/2,0,0),
wi^3=(-1/4,-1/4,0),
z_0=0, z_1=z_2=1/2, z_3=0,
w=(1/4,1/4,0).
```

**Proposition 4 (ordinary mathematics; exact interface counterexample).**
These data satisfy every field of `BuildingBlock M y (1/4)`.  There is an
exact public one-draw single-owner Nash profile with payoff `w`.  On the other
hand, consider any ordinary behavioral profile in which only players 1 and 2
can quit, their allowed quit dates are disjoint, and the terminal payoff is
zero if nobody quits.  If its payoff is within `delta` coordinatewise of `w`,
then one of players 1 and 2 gains at least

```text
(1/2)*(1/4-delta)^2
```

by deviating to pure Never.  In particular, for `delta<=1/8` its
exploitability is at least `1/128`.

**Verification of the `BuildingBlock`.**  Both `y` and `w` lie in `DZero M`.
Indeed,

```text
y = (1/3)M^1+(1/3)M^2+(1/3)M^3,
w = (5/12)M^1+(5/12)M^2+(1/6)M^3,
```

and both vectors are nonnegative and have third coordinate zero.  The first
two `wi` are the midpoints of the segments from `y` to `M^1,M^2`; the third is
one quarter of `M^3`, hence lies on the segment from `y` to `M^3`.  All their
coordinates are at least `-1/4`, and each differs from `y`.  The balance and
complementarity identities are

```text
w=(1/2)wi^1+(1/2)wi^2,
wi^1_1=wi^2_2=0.
```

Finally `z_1+z_2=1>0`.  This checks `y_boundary`, `w_boundary`, `approach`,
`lower`, `balance`, `complementary`, and `nontrivial` in the literal source
structure.

For the public profile, draw owner 1 or 2 with probability `1/2`.  The drawn
owner quits with probability `1/2` at date zero; after continuation, everyone
plays Never.  Give all nonsingleton coalitions and Never payoff zero.  The
conditional values are `wi^1,wi^2`, and the ex ante payoff is `w`.  A drawn
owner is indifferent because its own singleton and continuation payoffs are
zero.  A passive player weakly loses by joining: a collision pays zero, its
own singleton coordinate is zero, whereas continuing obtains the positive
off-diagonal singleton payoff when the drawn owner quits.  Player 3 obtains
zero under every action.  Thus this is an exact sunspot Nash profile with at
most one prescribed quitter.

For the ordinary profile, let `T_i` be player `i`'s independently randomized
first quit date, and put

```text
F_i=P(T_i<infinity),
p_1=P(T_1<T_2),  p_2=P(T_2<T_1).
```

Disjoint allowed dates rule out finite ties.  The prescribed payoff is
`(p_2,p_1,0)`.  If player 1 switches to Never, its payoff becomes `F_2`, so
its gain is

```text
g_1=F_2-p_2=P(T_1<T_2<infinity).
```

Similarly `g_2=P(T_2<T_1<infinity)`.  Independence and absence of ties give

```text
g_1+g_2=P(T_1<infinity,T_2<infinity)=F_1*F_2>=p_1*p_2.
```

If the payoff is `delta`-close to `w`, then
`p_1,p_2>=1/4-delta`, proving the claim.

**Why this does not kill the source-matched thesis.**  The matrix has the
homogeneous simplex solution with weights `1/3,1/3,1/3`: its residual is
exactly zero.  By
`hasNontrivialZeroProjectiveLCPSolution_iff_homogeneous`
(`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`), it
satisfies `HasNontrivialZeroProjectiveLCPSolution M`.  The Q branch assumes
the negation.  The example also restricts the deterministic implementation to
the positive support of `z`; it does not exclude a construction that uses a
zero-weight branch as a vanishing auxiliary correction.  The rigorous
conclusion is only that the public choice cannot be replaced by deterministic
frequency scheduling from the `BuildingBlock` fields alone.

Conceptually, this example fails `(4.1)`: deleting player 1 leaves the
positive branch-2 drift for coordinate 1, and conversely for player 2.  The
precise surviving question is whether `hzero` plus the actual kiloblock
restart/advance graph supplies a separating correction to these two positive
deleted-clock drifts.
