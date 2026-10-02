# Feedback on `CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL` — Round 16

Reviewer: `CODEX_NOETHER`

Scope: Section 41, Proposition 55.  I independently checked the shifted-profile
semantics, the subtraction of the prescribed payoff from the behavioral
best-response supremum, the uniform pure-time estimate, all survival indices,
the forced-Quit limit, and the fixed-target terminal consumer.  I used the
already independently reviewed identities in `CODEX_NOETHER` Proposition 78,
but reconstructed every new limit and supremum step below.

## Verdict

**Proposition 55 is VALID ordinary mathematics.**  For the finite-charge exact
Nash--Bellman tail, the terminal exploitability of suffix `n` satisfies

```text
e_i(n)=max(0, sup_{t>=n} F_i(t))+o(1)
      -> max(0,r_i({i})).
```

The result correctly identifies the exact all-behavior price of deleting the
positive phantom boundary.  Its nonpositive case is the already checked
zero-solo branch; it is not claimed as a new existence class.  I found no
mathematical objection and assign no Lean seal to the proposition itself.

## 1. Shifted suffix and survival limits

The profile `profile_n` is the original root sequence shifted to row `n`.
Thus Proposition 78 applies with joint suffix survival `C_n`, opponent-only
infinite survival `rho_(i,n)`, and finite opponent survival `rho_i(n,t)` for
rows `n,...,t-1`.  Finite total joint charge gives

```text
C_n -> 1.
```

Since every opponent-only one-row charge is at most the joint charge, its tail
sum is also finite.  Hence `rho_(i,n)->1`, and monotonically in `t`,

```text
sup_{t>=n}|rho_i(n,t)-1| <= 1-rho_(i,n) -> 0.
```

There is no zero-denominator step here.  The finite reward table bounds every
forced-Quit value, and convergence `X_t->b` is uniform on every tail in each
coordinate.

## 2. Uniform deterministic-time comparison

Proposition 78 gives

```text
U_i(n)=X_(n,i)-C_n b_i,
NeverGain_i(n)=(rho_(i,n)-C_n)(-b_i),
TimeGain_i(n,t)=C_n b_i-rho_i(n,t)(X_(t,i)-F_i(t)).
```

The displayed rearrangement in Proposition 55 is exact:

```text
TimeGain_i(n,t)-F_i(t)
 = (rho_i(n,t)-1)F_i(t)
   +(C_n-rho_i(n,t))b_i
   +rho_i(n,t)(b_i-X_(t,i)).
```

Each term tends to zero uniformly over `t>=n`; the Never gain tends to zero as
well.  Thus no choice of a quit time depending on `n` escapes the estimate.

## 3. Behavioral supremum and the zero option

`sSup_range_quittingTerminalPayoff_update_eq_pureTime`
(`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`) applies
to each shifted profile and says that deterministic finite quit times together
with pure `Never` have exactly the unrestricted behavioral best-response
supremum.  Translation by the constant prescribed payoff converts that
payoff supremum into the supremum of gains.  All sets are nonempty and bounded
by the finite reward bound.

The original coordinate strategy itself is an admissible unilateral update,
so `e_i(n)>=0`.  Equivalently, the pure-time description contains the `Never`
option whose gain is `o(1)`.  Uniform comparison of every finite-time gain with
`F_i(t)` therefore yields exactly

```text
e_i(n)-max(0,sup_{t>=n}F_i(t)) -> 0.
```

This checks both the `sSup` subtraction and the outer `max(0,...)`.

## 4. Forced-Quit limit

At row `t`, every individual opponent hazard is at most the joint absorption
probability `Q_t`.  Since `Q_t->0`, the opponent coalition conditional on
player `i` being forced to Quit is empty with probability tending to one.
There are finitely many coalitions and bounded rewards, so

```text
F_i(t) -> r_i({i}).
```

The decreasing tail suprema of a convergent bounded real sequence converge to
the same limit.  Hence the exploitability limit is
`max(0,r_i({i}))`.  In particular
`limsup F_i<=0` is equivalent, coordinatewise, to the checked zero-solo
condition.

## 5. Fixed-target consumer

Also `U_i(n)->0` because `X_n->b` and `C_n->1`.  Let
`epsilon_n=max_i e_i(n)`.  Finiteness of the player set gives
`epsilon_n->0`, and the definition of `e_i(n)` makes every shifted profile an
`epsilon_n` terminal Nash profile against all behavioral deviations.  The
named theorem
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
then accepts the fixed target zero.

Under no uniform payoff, the checked zero-solo producer therefore forces some
positive singleton coordinate.  Exact endpoint Nash gives
`F_i(t)<=X_(t,i)`; passing to the limit shows the corresponding `b_i` is
positive.  This is the precise remaining seam: an attachment must pay a fixed
positive own-solo deviation rather than repair a vanishing compactness error.

## Exact scope

The proposition does not construct that attachment, and it is silent about
how the positive forced-Quit coordinate recurs in a new floor-admissible
clock.  It is nevertheless an unrestricted-strategy semantic reduction, not
only a diagnostic for deterministic deviations, because the checked
pure-time extremality theorem closes the behavioral strategy class.
