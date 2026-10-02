# Positive-minimum attainment: singleton-escape exclusion and the cap-surcharge screen

Author: `CODEX_RAMSEY`

Status: **complete bounded ordinary-mathematics screen; the attempted
attainment route does not close a maintained conjecture-facing arm.  Internal
negative result.**

The reviewed two-player positive-debt nonattainment mechanism cannot occur
literally on the punishment-normal `Fin 4` positive minimum fiber: the checked
uniform singleton gap forces a fixed amount of every nearby actual terminal
law away from each owner's singleton.  This does **not** imply attainment.
The exact completion ledger below shows the remaining obstruction: a weak
stopping-law completion may raise the unrestricted best-response caps enough
to preserve global minimality.  Current paid-port and terminal-witness data do
not control that surcharge on the same completing profile.

Consequently this note does not regenerate a paid/reset source after descent,
eliminate an inert minimum endpoint, or produce terminal approximate Nash
profiles.  It records why this compactification attempt must stop rather than
quietly assuming that the attained semantic set is closed.

## 1. Setting

Let `reward` be a quitting reward table on `Fin 4`, let

```text
z = (U,B) ∈ quittingTerminalSemanticCarrier reward
```

minimize total semantic debt

```text
D(U,B) = sum_i (B_i-U_i),
```

and assume `D(z)>0` and punishment normality.  Write

```text
M = quittingRewardBound reward,
s_i = reward({i})_i.
```

The checked theorem

```text
exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal
```

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`
supplies `delta>0` such that every point `(V,C)` of the minimum fiber obeys

```text
V_i - s_i >= delta                         (1.1)
```

for every player `i`.

Choose any actual behavioral profiles `sigma_n` whose full semantic pairs
converge to `z`.  Let `mu_n` be the probability vector on the finite terminal
outcome type

```text
Option {S : Finset (Fin 4) // S.Nonempty};
```

`none` denotes nonabsorption.

## 2. Uniform exclusion of the one-singleton escape

### Proposition 2.1

For every player `i`, eventually

```text
mu_n(none) + sum_{S != {i}} mu_n(some S) >= delta/(4*M).       (2.1)
```

In particular, among `none` and the fourteen nonempty coalitions other than
`{i}`, one outcome has mass at least

```text
delta/(60*M).                                                (2.2)
```

After a subsequence that outcome can be fixed.

### Proof

Positivity of `delta` implies `M>0`.  Prescribed-coordinate convergence and
(1.1) give, eventually,

```text
U(sigma_n)_i - s_i >= delta/2.                               (2.3)
```

The terminal reward of outcome `none` is zero.  Every reward coordinate and
`s_i` lie in `[-M,M]`; hence every outcome other than `{i}` contributes at
most `2*M` above `s_i`, while `{i}` contributes exactly zero.  The exact
terminal-outcome moment identity therefore gives

```text
U(sigma_n)_i - s_i
  <= 2*M * [1-mu_n(some {i})].                               (2.4)
```

Combining (2.3) and (2.4) proves (2.1).  The bracket in (2.4) is the sum of
exactly fifteen nonnegative outcome masses, proving (2.2) by the finite
pigeonhole principle.  Finiteness also fixes one outcome on a subsequence.

### What this proves and does not prove

The counterexample in
[`CODEX_FERMAT__POSITIVE_DEBT_SEMANTIC_NONATTAINMENT.md`](CODEX_FERMAT__POSITIVE_DEBT_SEMANTIC_NONATTAINMENT.md)
has prescribed mass one on a single clock owner's singleton.  At that owner
the prescribed coordinate equals its own singleton reward, so it is excluded
by (1.1), quantitatively by (2.1).

But (2.1) allows:

- a lottery over two or more singleton labels;
- a fixed nonsingleton terminal coalition; or
- fixed nonabsorption mass.

The persistent outcome may also depend on `i`.  It is not a paid row, an
exact Bellman root, a reset incidence, or a terminal approximate-Nash
certificate.  Thus it supplies no source-matched regeneration after a paid
port descends to the minimum fiber.

## 3. Exact weak-completion debt ledger

The algebra behind every proposed compactification is independent of how the
weak stopping-law limit is constructed.

### Proposition 3.1

Let

```text
z   = (U,B)
tau = (U',B')
```

be any two terminal-semantic carrier points, with `z` a global minimizer of
total debt.  Define the total prescribed loss and total cap surcharge of the
move from `z` to `tau` by

```text
L = sum_i (U_i-U'_i),
C = sum_i (B'_i-B_i).
```

Then

```text
D(tau)-D(z) = L+C,                                  (3.1)
L+C >= 0.                                           (3.2)
```

If the only prescribed discontinuity is vanished mass `m_S>=0` on terminal
coalitions, so that

```text
U-U' = sum_S m_S reward(S),                         (3.3)
```

then

```text
sum_i (B'_i-B_i)
  >= - sum_S m_S * sum_i reward(S)_i.               (3.4)
```

In the one-coalition case `U=U'+m reward(S)`, (3.4) is

```text
C >= -m * sum_i reward(S)_i.                        (3.5)
```

### Proof

Expand the definitions:

```text
D(tau)-D(z)
 = sum_i [(B'_i-U'_i)-(B_i-U_i)]
 = sum_i(B'_i-B_i) + sum_i(U_i-U'_i)
 = C+L.
```

Global minimality of `z` gives (3.2).  Substitute (3.3) to obtain (3.4).

### Corollary 3.2: exact Fermat-type completion is impossible at a minimum

Suppose a weak-law completion removes positive mass only from coalitions with
negative total reward and does not increase the aggregate unrestricted cap:

```text
sum_S m_S * sum_i reward(S)_i < 0,
sum_i B'_i <= sum_i B_i.
```

Then `D(tau)<D(z)`, contradicting global minimality.

For the checked two-player regression, the vanished clock singleton has total
reward `-1` and the all-Never completion has the same cap vector.  The ledger
therefore explains exactly why that table's global minimum is zero and why
its positive-debt phantom cannot be a positive global minimizer.

## 4. The precise surviving obstruction

Stopping-law marginals live on `Nat union {infinity}` and have weakly
convergent subsequences.  Their product weak limit is again an executable
behavioral profile after the usual hazard realization.  Terminal payoffs are
not continuous at the joint all-infinite boundary, however, and the full
best-response envelope need not converge to the cap of that completed
profile.

Proposition 3.1 says that a nonattained positive minimum can survive this
completion in either of two ways:

1. the disappeared terminal mass has nonnegative aggregate prescribed
   reward; or
2. the completing actual profile has a sufficiently large upward cap jump
   `C`.

The second alternative is an all-behavior phenomenon.  Neither the uniform
singleton gap nor the currently checked paid-cap port controls
`B(tau)-B(z)` for this weak completion.  Finite stopping-law capping controls
payoffs and caps only when its explicit splice error tends to zero; that is
the cap-tight datum isolated in
`TerminalSemanticStoppingLawFiniteSpliceNashification.lean`, not a consequence
of positive minimum debt.

This is the exact point at which the attempted attainment proof stops.  Any
conjecture-facing continuation must co-realize one of the following on the
completion:

- a cap-nonincreasing weak completion, making a negative-total-reward escape
  contradict minimality;
- a terminal approximate-Nash certificate for a finite splice, which would
  give the terminal approximants requested by the main question; or
- source-matched paid/reset provenance carried through the cap surcharge,
  producing a maintained debt/support-rank descent.

The current fields provide none of these.  Therefore the present screen does
not eliminate the inert minimum endpoint and should not be exported as a
conjecture-closing result.

## 5. Source audit and boundaries

Declarations inspected:

- `exists_minimum_quittingTerminalSemanticDebtSum` and
  `exists_profile_sequence_tendsto_minimumTerminalSemanticDebt` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean`;
- `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`;
- `quittingTerminalRewardMoment_outcomeMass` and the finite terminal-outcome
  law declarations used throughout
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauTimeDisintegration.lean`;
- the checked counterexample in
  `UniformEquilibrium/Diagnostics/Quitting/PositiveDebtTerminalSemanticNonattainment.lean`;
- `isεAsymptoticNash_finiteCap` and the cap-tight diagonal consumer in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawFiniteSpliceNashification.lean`;
- the current hard residual and minimum-fiber boundaries in
  [`../questions/FIN4_HARD_RESIDUAL_SEMANTIC_CLOSURE.md`](../questions/FIN4_HARD_RESIDUAL_SEMANTIC_CLOSURE.md).

The ledger is elementary and apparently not separately named, but its only
new content is the exact sign screen (3.4).  It is not an attainment theorem.
No claim is made that the attained semantic set is compact, that a weak-law
completion preserves the cap, or that a persistent terminal outcome is a
Bellman/paid/reset consumer.
