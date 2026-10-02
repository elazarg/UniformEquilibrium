# Review of `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION`, Propositions 84--85

Reviewer: `CODEX_GAUSS`

Status: independent falsification audit.  Both propositions are **valid
ordinary mathematics** in their stated scope.  I found no counterexample or
missing factor.  Neither result is asserted to be proved in Lean here.

## Claims reviewed

I reviewed Sections 64--65 of
`notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`:

- Proposition 84, the monotone exact-debt/capacity-account mismatch and the
  obstruction to a constant reanchor; and
- Proposition 85, automatic terminal-cap funding by any physical zero-target
  frozen-root lift whose support contains every positive-solo player.

The exact declarations inspected were:

- `QuittingDynamicDebtTail.monotone_debt`,
  `QuittingPositiveDebtSelfLoopLimit.debt_le_soloReward_of_debt_pos`, and
  `QuittingPositiveDebtSelfLoopLimit.soloReward_le_value` in
  `UniformEquilibrium/Quitting/Debt/Dynamic/PositiveDebtSelfLoopLimit.lean`;
- the `debt_tendsto` field of `QuittingPositiveDebtDynamicTailWitness` in
  `UniformEquilibrium/Diagnostics/Quitting/Chronology/PositiveDebtDynamicTailWitness.lean`;
- `killedDebtReference_step` and
  `killedDissipationSum_eq_zero_of_debtBoundary_le` in
  `UniformEquilibrium/Diagnostics/Quitting/Debt/KilledTailPotential.lean`;
- `killedCapacityDebtAccount_nonneg` and
  `killedCapacityDebtAccount_isKilledExcessive` in
  `UniformEquilibrium/Diagnostics/Quitting/Debt/KilledCapacityPotential.lean`;
- `antitone_killedCapacityDebtAccount`,
  `killedCapacityBoundaryMismatch_one`, and the capacity-dissipation
  identities in
  `UniformEquilibrium/Diagnostics/Quitting/Debt/BoundaryMismatchAlternative.lean`;
- `killedBoundaryRemainder`, `IsKilledExcessive`, and
  `killedDissipation` in `MathUE/Probability/KilledTailPotential.lean`;
- `IsQuittingFrozenRootContinuationLift` in
  `UniformEquilibrium/Quitting/Boundary/Analytic/ChargeTangent/SupportLiftFarkas.lean`;
- `quittingRootQuitPayoff_eq_zero_of_zeroTargetLift` in
  `UniformEquilibrium/Quitting/Boundary/Repair/TerminalFunding/SupportNecessity.lean`;
- `quittingRewardBound` and `abs_reward_le_quittingRewardBound` in
  `UniformEquilibrium/Quitting/RewardBound.lean`;
- `quittingRootOpponentAbsorptionMass_le_absorptionMass` in
  `UniformEquilibrium/Quitting/Stationary/LiveMass.lean`; and
- `debt_cutoff_eq_sum_positiveSingletonDebtCap` and
  `debt_zero_le_aggregateCapacityAccount_zero_of_frozenRootLift` in
  `UniformEquilibrium/Quitting/Debt/Dynamic/ReachableCarryTelescope.lean` and
  `UniformEquilibrium/Diagnostics/Quitting/Capacity/TerminalIncomingPathAlternative.lean`.

## Proposition 84: verdict VALID

Write, for one fixed player,

```text
D_t = killedDebtReference(t),
A_t = killedCapacityDebtAccount(t),
m_t = D_t-A_t.
```

### Monotonicity and limit sign

The exact checked directions are the directions used in the note:

```text
D_t <= D_(t+1),          A_(t+1) <= A_t.
```

Consequently

```text
m_(t+1)-m_t
  = (D_(t+1)-D_t) + (A_t-A_(t+1)) >= 0.
```

The witness field `debt_tendsto` gives `D_t -> d_infty`.  The account is
nonnegative and antitone, hence converges to its infimum `A_infty`.  Therefore
`m_t -> d_infty-A_infty`.  In particular, if the limit is nonpositive then
every finite `m_t` is nonpositive, exactly giving `D_t<=A_t` at every date.

If the limiting mismatch is positive, then
`d_infty>A_infty>=0`.  The two named self-loop declarations give

```text
0 < d_infty <= r_i({i}) <= limit.value_i.
```

Thus the positive-solo conclusion has the correct player and direction.

### Signed dissipation recursion and finite telescope

The checked reference recursion and the definition of killed dissipation are

```text
D_t = source_t + c_t D_(t+1),
delta_t = A_t-source_t-c_t A_(t+1).
```

Subtracting gives exactly

```text
c_t m_(t+1)-m_t = delta_t.
```

`killedCapacityDebtAccount_isKilledExcessive` gives `delta_t>=0`.  Iterating
the displayed identity with
`W(t,j)=prod_(k<j)c_(t+k)` gives

```text
W(t,L)m_(t+L)
  = m_t + sum_(j<L) W(t,j)delta_(t+j).
```

I checked the endpoint convention: the `j=0` coefficient is one and the far
coefficient is exactly `W(t,L)`, so there is no one-step shift.

### Constant reanchor

For a fixed start `t` with `m_t>=0`, let `B_u=A_u+m_t`.  From excessivity of
`A`, `0<=c_u<=1`, and `m_t>=0`,

```text
source_u+c_u B_(u+1)
 <= A_u+c_u m_t
 <= A_u+m_t = B_u.
```

Thus the shift really remains excessive and `B_t=D_t`.  The two finite
boundary terms differ by

```text
W(t,L)(D_(t+L)-B_(t+L))
  = W(t,L)(m_(t+L)-m_t) >= 0.
```

The checked boundary consumer needs the reverse weak inequality, reference
boundary at most account boundary.  If `W(t,L)>0`, that reverse inequality
therefore holds exactly when `m_(t+L)=m_t`.  This confirms both the sign and
the strict equivalence in Proposition 84(5).  At `W=0` both boundaries vanish,
which is why the proposition correctly states the equivalence only for
positive prefix survival.

The scalar test `c_0=1/2`, `D_0=d/2`, `A_0=a`, followed by constant `D=d`,
`A=a` also checks.  For `(d,a)=(3,1)`, the shifted far-boundary excess is

```text
(1/2) ((3-1)-(3/2-1)) = 3/4.
```

### Scope

This is an exact adapter among checked scalar accounting declarations.  The
pointwise arm `D_t<=A_t` does not itself construct a co-realized finite
chronology, and the positive-limit arm does not attach or punish the surviving
positive-solo phantom.  I found no existing named consumer which removes
either of those two producer obligations merely from this dichotomy.

## Proposition 85: verdict VALID

Let

```text
P = {i | 0<r_i({i})},
M = quittingRewardBound reward,
Q = quittingRootAbsorptionMass root.
```

Assume the root is interior on support `S`, `P subset S`, and the supplied
continuation is an `IsQuittingFrozenRootContinuationLift` at target zero.

### Active endpoint really is zero

For `i in P subset S`, the lift gives zero Boolean-Mobius coordinate
derivative.  The checked endpoint-difference adapter converts this to equality
of forced Quit and forced Continue.  Their root-coordinate mixture is the
successor payoff, and the lift's Bellman equality makes that successor payoff
zero.  Since the two action probabilities sum to one, both endpoints are
zero.  This is already isolated exactly by
`quittingRootQuitPayoff_eq_zero_of_zeroTargetLift`; no limiting or division
argument is involved.

### Global absolute-sum estimate

Condition on `i` quitting and let `mu_i` be the opponents' product law.  Write
`s_i=r_i({i})>0` and let `h_i` be the probability that at least one opponent
quits.  The zero forced-Quit endpoint is

```text
0 = mu_i(empty)s_i + sum_(T nonempty) mu_i(T)r_i(T union {i}).
```

Using total mass one, this is equivalently

```text
-s_i = sum_(T nonempty) mu_i(T)(r_i(T union {i})-s_i).
```

For nonempty opponent `T`, the terminal coordinate
`(T union {i},i)` is distinct from `({i},i)`.  Because `quittingRewardBound`
is the sum of the absolute values of *all* terminal/player coordinates, those
two distinct summands give

```text
|r_i(T union {i})|+|s_i| <= M.
```

Taking absolute values and summing therefore yields

```text
s_i <= M h_i.
```

This is genuinely the sharper project-specific constant `M`, not the generic
`2M` coordinatewise estimate.  No issue occurs when `h_i=0`; the inequality
would contradict `s_i>0`, so positivity of opponent absorption is a
consequence rather than an extra assumption.  Finally the checked inequality
`h_i<=Q` gives `s_i<=M Q`.

Summing over `P` gives

```text
sum_i max(0,r_i({i}))
  = sum_(i in P) s_i
  <= |P| M Q
  <= card(I) M Q.
```

By `debt_cutoff_eq_sum_positiveSingletonDebtCap`, the left side is the exact
terminal debt of every finite zero-boundary chain.  Hence this is precisely
the `hpays` premise of
`debt_zero_le_aggregateCapacityAccount_zero_of_frozenRootLift` in the stated
nonpositive-punishment lane.

### Boundary tests and exact remaining gap

- For one player with positive solo reward, forced Quit is that positive
  singleton reward and cannot equal target zero, so the lift is impossible.
- For two players with owner payoffs `s` at `{i}` and `-a` at `{i,j}`, taking
  the opponent hazard `s/(s+a)` gives equality
  `(s+a)h_i=s`.  With all other relevant coordinates zero, the second owner's
  endpoint equations are also zero.  This verifies sharpness of the local
  coefficient.

The proposition removes only charge calibration after a suitable physical
root has been supplied.  It does not produce a root, prove simultaneous
support feasibility, eliminate the Farkas certificates, construct a return,
or cover an inadmissible positive punishment floor.  The surviving universal
question is exactly feasibility of one zero-target physical product root with
support containing `P`, or a global use of the family of Farkas obstructions.

## Final disposition

Both propositions survive falsification.  Proposition 84 is a useful exact
diagnosis of why constant reanchoring fails; Proposition 85 materially removes
the separate magnitude gate from the physical-root branch.  They remain
ordinary, unformalized adapters and are not by themselves exportable
uniform-payoff producers.
