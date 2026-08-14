# Stochastic-button compression for quitting paths

## Result

The stochastic-button idea yields a rigorous atom/diffuse compression ledger
without changing the quitting game.

For a root sequence `p(t)`, define the effectiveness of row `t` by

```text
q_t = P(at least one player quits at row t).
```

Fix a threshold `eta > 0`. Retain rows with `q_t > eta` as atomic packets and
call the remaining rows diffuse. For a finite window ending at `N`, let

```text
Q_N = sum_{t < N} q_t,
S_t = product_{s < t} (1 - q_s).
```

The Lean experiment
`QuittingStochasticButtonCompression.lean`
proves:

```text
sum_{t < N} S_t q_t = 1 - S_N,                         (1)

eta * #{t < N : q_t > eta} <= Q_N,                    (2)

sum_{t < N, q_t <= eta} S_t * CollisionMass(p(t))
  <= choose(n,2) * eta * (1 - S_N)
  <= choose(n,2) * eta,                                (3)

S_N <= exp(-Q_N).                                      (4)
```

If `Q_N` lies in `[L,L+1]`, these combine to give

```text
#{large rows} <= (L+1)/eta,
diffuse collision mass <= choose(n,2) * eta,
tail survival <= exp(-L).
```

If `Q_N -> infinity`, a finite first-crossing window with
`Q_N in [L,L+1]` exists for every `L > 0`; that assertion is also checked in
Lean. Thus, at any requested accuracy, the nonlinear part of a divergent
quitting chronology has a quantitatively finite number of rows.

## Why this is the right stochastic-button coordinate

No external noise is added. The scalar effectiveness is already determined
by the original independent behavioral buttons. On a row with `q > 0`, define

```text
d_i = p_i / q.
```

Lean proves

```text
p_i = q * d_i,
0 <= d_i <= 1,
1 <= sum_i d_i <= n.
```

The direction does not generally lie on the simplex: simultaneous quits are
counted in several marginals. This is not a defect in the coordinate. It
locates exactly the nonlinear collision content. As `q` becomes small,
one-stage collision mass is quadratic:

```text
CollisionMass(p) <= choose(n,2) * q^2.
```

After multiplication by live survival and summation, one factor of `q`
telescopes by (1), leaving the horizon-independent `O(eta)` bound (3).

This is stronger than the naive estimate `O(eta * N)`. Arbitrarily many tiny
rows are harmless for terminal collision mass because they must share one
unit of survival-weighted absorption.

## Interpretation as a finite nonlinear reduction

Choose

```text
L  >= log(2M / epsilon),
eta <= epsilon / (2M * choose(n,2))
```

for reward bound `M`, ignoring harmless adjustments when the binomial
coefficient vanishes. Then:

- the unprocessed tail carries at most `epsilon/(2M)` probability;
- all diffuse simultaneous-coalition outcomes carry at most
  `epsilon/(2M)` probability; and
- at most `(L+1)/eta` large-effectiveness rows retain genuine nonlinear
  coalition geometry.

The diffuse residue is therefore first-order singleton flow plus a controlled
error. Existing logarithmic singleton meshes handle exactly this first-order
geometry. The rows that cannot be subdivided without changing their coalition
law are precisely the finitely many retained atoms.

This does **not** say that the original chronology has finitely many calendar
dates. It says that, at fixed accuracy, only finitely many dates carry
non-negligible nonlinear coalition information. The remaining calendar can in
principle be consumed by a singleton-flow telescope rather than iterated row
by row.

## Relation to landed results

The experiment combines, rather than replaces, four existing ingredients:

1. one-row product collisions are quadratic in absorption;
2. survival-weighted absorption telescopes;
3. divergent absorption charge gives exponential tail contraction; and
4. singleton arcs admit exact logarithmic subdivision.

The new content is the arbitrary-path atom/diffuse assembly and its finite
first-crossing certificate. It formalizes the proposed stochastic-button
normal form:

```text
arbitrary quitting chronology
  = finitely many coalition atoms
    + diffuse singleton flow with O(eta) collision bill
    + exp(-L) terminal tail.
```

## What is not yet equivalent strategically

Equations (1)--(4) concern the prescribed product-root chronology and its
terminal coalition law. Uniform equilibrium requires more.

1. **Continuation motion.** Removing diffuse collisions changes which
   continuation value follows a no-quit row. A terminal total-variation bound
   alone does not preserve the Nash--Bellman recursion.

2. **Unilateral counterfactuals.** A deviator can replace its own marginal by
   a large or sure quit. The atomic/diffuse partition for the prescribed path
   is not automatically the partition for every updated path. The correct
   strategic clock is player-deleted opponent survival.

3. **Punishment floors.** An `O(eta)` payoff change can cross a tight
   punishment face. Slack pays for this, but tight coordinates require an
   exact or one-sided transport theorem.

4. **Direction variation.** The diffuse button direction can oscillate at
   arbitrarily many dates. Its collision nonlinearity is small, but a finite
   compression of the singleton flow still has to preserve the relevant
   continuation moments or telescope them without compression.

Accordingly, adding literal independent button failures is unnecessary and
would not be equivalent. The useful object is the effectiveness coordinate
already latent in the original game.

## Strategic upgrade now landed

The player-deleted collision part of the proposed strategic upgrade has now
landed in
`QuittingStochasticButtonUnilateralCompression.lean`,
with its mathematical report in
[`QUITTING_STOCHASTIC_BUTTON_UNILATERAL_COMPRESSION.md`](QUITTING_STOCHASTIC_BUTTON_UNILATERAL_COMPRESSION.md).

For each player `i`, use the opponent effectiveness

```text
q^(-i)_t = P(at least one opponent of i quits at row t)
```

and its survival weight `S^(-i)_t`. The new Lean theorem chooses a finite
window and the large packets from this clock before the deviation, then proves
uniformly over every behavioral hazard that the literal diffuse collision
mass is at most

```text
(choose(n,2) + 1) * eta.
```

The remaining target is to replace the diffuse singleton flow while
preserving the same continuation endpoint and every stated punishment-floor
inequality up to an explicit one-sided budget.

If that theorem lands, the standard pure-time-law reduction should extend the
bound to arbitrary behavioral deviations. Together with the finite terminal
compiler, this would make the full UE problem accuracy-by-accuracy equivalent
to:

- finitely many nonlinear coalition packets;
- a singleton-flow segment handled by telescope/mesh; and
- one explicit terminal boundary account.

The two experiments now establish quantitative finiteness and collision
control, including unilateral counterfactuals. They do not yet establish the
continuation/punishment transport needed for the full strategic replacement
theorem.
