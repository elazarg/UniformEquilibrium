# Balanced cap-leakage rigidity

Status: ordinary mathematics independently reviewed and accepted with the
statement repairs below.  It is a supplied-object limit theorem, not a Fin4
consumer and not an export candidate.  The source draft is `../CAP_LEAK.md`;
the independent review is
`feedback/CAP_LEAK__BY_CODEX_BANACH.md`.

## Question

Suppose actual behavioral profiles approach the global minimum of total debt
at a rate negligible relative to a reset scale.  If finitely many unilateral
stopping-law tangent columns balance in every debt coordinate, can switching
of unrestricted behavioral best replies create a new first-order debt term
under the simultaneous product reset?

## Reviewed theorem

Let the finite mover set be `A`.  Let `lambda_n > 0` tend to zero, and let
actual profiles `sigma_n` satisfy

```text
(D(sigma_n) - D_*) / lambda_n -> 0.
```

For every mover `a`, mix only `a`'s original stopping law with a supplied
replacement law at intensity `lambda_n`, obtaining `sigma_n^a`.  Suppose all
coordinate tangent limits exist:

```text
(d_j(sigma_n^a) - d_j(sigma_n)) / lambda_n -> T[j,a].
```

Let nonnegative weights `m_a` sum to one and balance every coordinate:

```text
sum_a m_a T[j,a] = 0  for every j.
```

Let `bar_sigma_n` reset all movers independently, using intensity
`m_a * lambda_n` for mover `a`.  Then, for every player `j`,

```text
(d_j(bar_sigma_n) - d_j(sigma_n)) / lambda_n -> 0.
```

The cap-envelope nonadditivity is also negligible at that scale:

```text
sum_a m_a (B_j(sigma_n^a) - B_j(sigma_n))
  - (B_j(bar_sigma_n) - B_j(sigma_n))
= o(lambda_n).
```

The proof covers the complete behavioral cap, including Never and arbitrarily
late stopping.  Uniform multiaffinity gives an
`O_(reward bound, |A|)(lambda_n^2)` remainder for each fixed deviation.  An
`o(lambda_n)`-optimal deviation at the simultaneous reset gives the cap
upper bound; the base optimality gap cancels because the weights sum to one.
Global minimum provenance upgrades coordinatewise `limsup <= 0` to equality.

Monotonicity of `lambda_n` is unnecessary.  Positivity and convergence to zero
are enough.  The multiaffine remainder constant should record dependence on
the reward bound and the number of movers.

## Sharp boundary

The source excess must be `o(lambda_n)`, not merely `O(lambda_n)`.  A
max-of-two-affine cap switch supplies a balanced pair of unilateral tangent
columns while allowing an order-`lambda_n` simultaneous cap/debt drop when the
base itself lies order `lambda_n` above the minimum.

## What it changes

First-order cap leakage is not an additional obstruction once the behavioral
reset tangents balance at an `o(lambda)`-minimum source.  The simultaneous
behavioral reset is coordinatewise flat to first order.

What remains is a type conversion, not another cap estimate.  The reset is an
operation in behavioral-profile space.  Existing return compilers require an
ordered exact Nash--Bellman/punishment-floor chronology whose charge is literal
root absorption.  Canonical cap lifting near the minimum supplies only
`o(lambda)` absorption and therefore cannot realize the order-`lambda` reset
charge.

## Concrete next question

Prove or refute a radial collision realization theorem: from a source-attached
balanced reset of scale `h`, displacement `o(h)`, and fixed positive reset
charge, produce either terminal approximants, a renewable exact admissible
block with absorption `Omega(h)` and seam `h * o(1)`, or a source-preserving
strict finite-rank decrease with a backward compiler.

Without that conversion, this theorem should remain a formalizable
intermediate lemma and must not be described as an exact chronology producer.
