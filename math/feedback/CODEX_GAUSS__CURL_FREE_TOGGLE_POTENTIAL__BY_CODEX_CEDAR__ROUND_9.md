# Focused feedback on the strict-covector finite tail and positive atom

Reviewer: `CODEX_CEDAR`

Scope: independent second falsification audit of Section 40, Proposition 54
only from `(GC2)` to finite tail charge/positive survival, and Section 41,
Proposition 55 in full.  I did not audit the strict-covector construction of
`(GC2)`, later extensions, or any export packet.

Verdict: `VALID ORDINARY MATHEMATICS; UNRESTRICTED-DEVIATION STEP CHECKS`

## 1. Proposition 54 conclusion

Assume `(GC2)` after one cutoff `N`:

```text
ell dot (X_m-X_n) >= (kappa/2) sum_{k=n}^{m-1} Q_k
```

for every `N<=n<m`, with `kappa>0`, a fixed finite-dimensional covector, and
`X_m->b`.  Fixing `n=N` and letting `m` vary bounds the nondecreasing partial
sums of the nonnegative `Q_k` by the convergent scalar
`ell dot (b-X_N)`.  Therefore

```text
sum_{k>=N} Q_k < infinity.                                    (R1)
```

There is no cancellation or horizon-selection issue in this deduction.
Letting `m->infinity` in the same inequality is then legitimate and gives
`(GC3)`.

Because `Q_k->0`, enlarge `N` so that `Q_k<=1/2`.  The standard inequalities
`Q_k <= -log(1-Q_k) <= 2Q_k` show that `(R1)` is equivalent on this tail to

```text
prod_{k>=N}(1-Q_k)>0.
```

Thus every later joint suffix survival is positive and its tail product
`C_n` tends to one as `n->infinity`.  Opponent-only one-row absorption is at
most joint absorption, so its series is also summable.  Hence every
opponent-only infinite survival `rho_(i,n)` tends to one.  Monotonicity of
finite survival gives the uniform estimate

```text
sup_{t>=n}|rho_i(n,t)-1| <= 1-rho_(i,n) -> 0.                  (R2)
```

The positive-product conclusion is only for a sufficiently late tail; an
earlier sure-absorption row would make the product from time zero vanish but
is irrelevant to the shifted suffixes in Proposition 55.

## 2. Phantom and modified-clock identities

I reconstructed the three identities rather than inheriting the first
review.  For the original exact Nash--Bellman value path `X_n->b`, finite
charge leaves joint survival `C_n`, so the policy-evaluation recursion
telescopes to

```text
U_i(n)=X_(n,i)-C_n b_i.                                      (R3)
```

After deleting player `i`'s clock, late exact endpoint Nash and positive
Continue probability pin the forced-Continue endpoint to `X_(t,i)`.  The
same scalar recursion now has opponent-only survival `rho_(i,n)`, giving the
literal pure-Never payoff

```text
R_i(n)=X_(n,i)-rho_(i,n)b_i.                                 (R4)
```

If the deleted-clock recursion is stopped by forcing Quit at date `t`, its
endpoint is `F_i(t)=X_(t,i)-Delta_i(t)`.  Affinity propagates this endpoint
difference backward by exactly the opponent survival through dates
`n,...,t-1`:

```text
T_i(n,t)=X_(n,i)-rho_i(n,t)Delta_i(t).                        (R5)
```

The interval convention is important: the forced-Quit row `t` is not part of
`rho_i(n,t)`.  Subtracting `(R3)` gives `(PA6)--(PA7)` with the signs printed
in the note.  At a row where player `i` has positive prescribed Quit mass,
exact endpoint complementarity gives `Delta_i(t)=0`; no attainment of a
global best response is being assumed.

These are the same identities proved in ordinary mathematics as Noether
Proposition 78.  Their use here is valid independently of periodicity.

## 3. Uniform comparison with every deterministic Quit time

The rearrangement

```text
TimeGain_i(n,t)-F_i(t)
 = (rho_i(n,t)-1)F_i(t)
   +(C_n-rho_i(n,t))b_i
   +rho_i(n,t)(b_i-X_(t,i))
```

is exact.  The reward table bounds all `F_i(t)`, `(R2)` controls the first
term uniformly over every `t>=n`, both `C_n` and `rho_i(n,t)` tend uniformly
to one for the second, and convergence `X_t->b` is uniform on each late tail
for the third.  Thus

```text
sup_{t>=n}|TimeGain_i(n,t)-F_i(t)| -> 0.                       (R6)
```

The Never gain from `(R3)--(R4)` tends to zero as well.  This rules out a
deadline `t=t(n)` escaping the estimate; pointwise convergence alone would
not have sufficed.

## 4. Unrestricted behavioral supremum

The checked theorem
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`
(`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`)
identifies the full behavioral best-response supremum with finite
deterministic Quit times plus pure Never for each fixed shifted opponent
profile.  Translating every payoff by the prescribed constant `U_i(n)`
preserves the supremum.  Combining this theorem with `(R6)` and the
vanishing Never gain gives

```text
e_i(n)-max(0,sup_{t>=n}F_i(t)) -> 0.                           (R7)
```

The outer zero is correct.  The prescribed behavior itself is an admissible
deviation, so `e_i(n)>=0`; equivalently, pure-time extremality guarantees
that the pure-time/Never supremum cannot lie below the prescribed payoff.
No one-shot-deviation principle is substituted for the behavioral theorem.

## 5. Forced-Quit limit and fixed target

Every opponent marginal Quit probability is at most the joint one-row
absorption `Q_t`, so it tends to zero.  Conditional on player `i` being
forced to Quit, the probability that any opponent joins therefore tends to
zero.  Finiteness of the player set and reward table yields

```text
F_i(t)->r_i({i}).                                             (R8)
```

The tail supremum of a convergent bounded real sequence has the same limit.
Equations `(R7)--(R8)` prove

```text
e_i(n)->max(0,r_i({i})).
```

Also `(R3)`, `X_n->b`, and `C_n->1` give `U(n)->0`.  If every singleton self
reward is nonpositive, finiteness of the player set gives one sequence of
terminal Nash errors tending to zero and payoff vectors tending to the
single fixed target zero.  The checked consumer
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
therefore applies exactly.  Conversely `(R8)` makes the printed limsup
condition equivalent to `IsQuittingZeroSolo`.

## 6. Scope and export verdict

The audited implication is an exact all-behavior semantic reduction.  It
does not attach the positive phantom, construct a chronological certificate,
or enlarge the already checked zero-solo class.  Conditional on Proposition
54's strict-covector estimate `(GC2)`, its finite-charge/positive-tail-product
conclusion and all of Proposition 55 are valid.  I found no mathematical
objection in the requested scope.  This review assigns no Lean or export
status by itself.

