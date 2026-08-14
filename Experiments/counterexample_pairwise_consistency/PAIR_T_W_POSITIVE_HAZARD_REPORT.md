# T x W: an exact positive-hazard shared-tail model

Status: **Consistent** for the exposed `T x W` equations; optimized-minimizer
provenance is not established.

Provenance qualification: the tail below is an exact Nash--Bellman and exact
dynamic-debt tail in the canonical bounded boxes, but it is **not known** to
arise as a projective limit of cutoff-wise optimized zero-boundary exact-D
chains for this same table.  Thus the report proves pairwise consistency of
the `T` and `W` constraints stated in the pair program and in the assigned
test, not consistency with every additional provenance property enjoyed by
the specially selected tail in the full counterexample reduction.  Adding
optimized-minimizer provenance is a strictly stronger residual problem.

This report gives one exact rational four-player reward table and one tail
which simultaneously realize the exposed equations of `T` and `W`.  The
canonical periodic windows are formed from that same tail.  In particular,
this is not a construction which attaches a periodic word to an unrelated
prefix.

The example also isolates the normalized window-drift obstruction requested
in the consolidation pass.  Exact debt conservation and the logarithmic
opponent clock do not improve the endpoint drift from `O(m_n)` to `o(m_n)`.
For this witness the normalized drift converges to `2`.

## Exact table and shared tail

Let the players be

```text
I = {o, a, b, c}.
```

Player `o` is both the positive-debt owner and the stabilized periodic-window
witness.  Player `a` supplies the small physical hazard.  For every nonempty
terminal set `S`, put

```text
r_o(S) = 1  if o is in S,
         2  if o is not in S and b is in S,
         0  otherwise,

r_a(S) = r_b(S) = r_c(S) = 0.
```

The unused `b`-terminal makes `M = 2` a sharp reward bound, so all prescribed
coordinates below lie in `[-M,M]`.  It does not occur on the tail or under an
`o`-deviation.  The owner's positive singleton cap is

```text
K_o = max(0,r_o({o})) = 1.
```

Choose `eta = 1/2`.  At date `t >= 0`, only `a` has a positive Quit
probability:

```text
p_t := a_a,t = 1/(t+2)^2,
a_o,t = a_b,t = a_c,t = 0.
```

Set the displayed annotation and exact dynamic debt to

```text
v_t(o) = 2(t+1)/(t+2),       d_t(o) = (t+1)/(t+2),
v_t(j) = d_t(j) = 0          for j != o.
```

All data are rational at every finite date.

## Exact Nash--Bellman and dynamic-debt checks

Write `s_t = 1-p_t`.  Direct cancellation gives

```text
s_t = (t+1)(t+3)/(t+2)^2,
d_t(o) = s_t d_(t+1)(o),
v_t(o) = s_t v_(t+1)(o).                              (1)
```

At the displayed root, `o` surely Continues.  Its pure-Quit endpoint is `1`
whether or not `a` simultaneously Quits.  Its pure-Continue endpoint is

```text
p_t r_o({a}) + s_t v_(t+1)(o) = v_t(o).
```

Since `v_t(o) >= 1`, Continue is optimal (with equality at `t=0`).  Player
`a` has both endpoints equal to zero and may mix with probability `p_t`.
Players `b,c` also have both endpoints zero.  Thus every root is an exact
one-stage Nash action and the Bellman equality is exactly (1).

For `o`, the exact dynamic-debt update is

```text
max(1, v_t(o) + s_t d_(t+1)(o)) - v_t(o)
  = max(1, v_t(o)+d_t(o)) - v_t(o)
  = d_t(o).                                             (2)
```

The other three updates are zero.  Hence these are exact dynamic-debt edges,
not merely vectors satisfying an external conservation equation.  Equation
(1) is also precisely the supplied conservation law because `a_o,t=0` and
joint survival is `s_t`.

## The T conditions

Joint absorption is `q_t=p_t`.  It is positive, tends to zero, and is
summable; for example

```text
1/(t+2)^2 <= 1/((t+1)(t+2)),
```

whose right side telescopes.  Thus this witness is not a zero-absorption
plateau.

Furthermore,

```text
1/2 = eta <= d_t(o) < 1 = K_o,
d_t(o) -> 1,
v_t(o) -> 2 >= eta.                                    (3)
```

Only `a` can absorb on the honest tail, and `r({a})=0` in every coordinate.
The Never event also pays zero.  Consequently the honest suffix payoff is
identically zero, not just asymptotically zero:

```text
U(a^(t)) = 0  for every t,
v_t(o)-U_o(a^(t)) = v_t(o) -> 2.                       (4)
```

The owner's opponent-clock charge is `p_t`.  From (1), for every finite
window `[T,T+L)`,

```text
sum p_t <= sum -log(1-p_t)
          = log(d_(T+L)(o)/d_T(o))
          <= log(1/(1/2)) = log(K_o/eta).              (5)
```

Here `p <= -log(1-p)` for `0 <= p < 1` is the standard scalar logarithm
inequality.  This proves the required clock bound with the exact same debt
owner and tail.

## Exact canonical-window evaluator

For each `n`, the required inclusive canonical word is

```text
W_n = (a_n,a_(n+1),...,a_(2n)),
```

of period `n+1`.  Its one-pass survival and absorption are

```text
1-m_n = product_(t=n)^(2n) (1-1/(t+2)^2)
      = (2n+3)/(2n+4),

m_n = 1/(2n+4) > 0.                                    (6)
```

On periodic repetition, each pass has the same positive absorption
probability.  Absorption therefore occurs almost surely, only `a` Quits, and
the honest periodic delivery is zero.

Now evaluate arbitrary unilateral behavior by the exact periodic-window
taxonomy in `PeriodicWindowEvaluation.lean`.  For player `o`:

```text
refusal/Never value = 0,
phase-0 stop value  = 1.
```

Every later deterministic stop has value at most `1`: before that stop `a`
may already have absorbed for payoff zero, while at the stop every reachable
terminal containing `o` pays exactly `1`.  More explicitly, the value of
phase `ell` in the first pass is

```text
product_(t=n)^(n+ell-1) (1-p_t)
  = (n+1)(n+ell+2)/((n+2)(n+ell+1)) <= 1,
```

where equality holds at `ell=0`; the denominator minus the numerator is
exactly `ell`.  The exact finite evaluator is therefore
therefore

```text
max(refusal, best phase stop) = max(0,1) = 1.           (7)
```

By the behavioral pure-stopping-time reduction, (7) controls arbitrary
behavioral deviations, not just stationary deviations.  Since delivery is
zero,

```text
E(periodic W_n) = 1 > eta/2 = 1/4                     (8)
```

for every `n`.  Thus the infinite selected set can be all natural numbers,
the fixed witness is `o`, and the fixed branch is a concrete finite stopping
phase (phase zero).  The refusal and finite-phase quantifiers are literal.

## The normalized drift does not vanish

The finite-word Bellman identity for `o` is, exactly,

```text
v_n(o) = m_n * delivery_n + (1-m_n) * v_(2n+1)(o),
delivery_n = 0.                                        (9)
```

Using (6),

```text
(v_(2n+1)(o)-v_n(o))/m_n = v_(2n+1)(o) -> 2,

((1-m_n)/m_n) * (v_(2n+1)(o)-v_n(o)) = v_n(o) -> 2.   (10)
```

The debt has the same exact finite-word recurrence,

```text
d_n(o) = (1-m_n)d_(2n+1)(o).
```

Thus summable joint absorption, exact debt conservation, the owner's
logarithmic opponent clock, root complementarity, positive limiting debt,
and convergence of `v_t` all coexist with an `O(m_n)` endpoint change whose
normalized coefficient stays positive.  No `o(m_n)` estimate follows from
the `T x W` data.

This identifies the residual seam sharply: ruling out persistent phase
exploitability needs an additional condition controlling normalized
annotation drift (or co-realizing the endpoint cap), not merely convergence
plus the clock bound.

## Validation and scope

Run

```text
python Experiments/counterexample_pairwise_consistency/pair_t_w_positive_hazard_probe.py
```

The probe has no external dependencies.  Its small rational-function checker
uses `fractions.Fraction` coefficients and verifies identities by polynomial
cross multiplication over `Q[X]`; it performs no floating-point comparisons
or tolerance-based reconstruction.  It checks (1), (6), (9), (10), the debt
recurrence, the evaluator branches, and all stated limits.

The construction survives extension by additional zero-payoff, always-
Continue dummy players.  It already uses four players, as required by the
master problem's ambient setting.  It does not establish cardinal-minimality
of a counterexample and is not a counterexample to the full problem: it only
proves exact pairwise consistency of the exposed `T` and `W` equations.  No
optimized zero-boundary chain is constructed, no minimizing property is
proved, and no projective-limit extraction from optimized cutoffs is claimed.
That provenance requirement remains unresolved for this table and could rule
out this particular tail once added as a third condition.  In particular, no
claim is made that this table satisfies the global terminal gap for every
profile or the universal charged-chain bound.
