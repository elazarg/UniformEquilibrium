# Sharpness of the two-seed finite-cap threshold

## Result

The two-zero-Never threshold is necessary as well as sufficient for a
reward-uniform all-player finite-cap reduction of the complete terminal
semantics.

The positive theorem in
`QuittingStoppingLawFiniteCapConvergence.lean`
says that two distinct zero-Never players suffice to cap the whole profile
while approximating prescribed payoff, the unrestricted behavioral
best-response envelope, and semantic debt.

The sharpness experiment
`QuittingFiniteCapSeedSharpness.lean`
proves that neither remaining zero-pattern class admits such a theorem.

## 1. The separating reward table

Use the same payoff for every absorbing coalition and every player:

```text
absorbing payoff = -1,
Never payoff     =  0.
```

For this table, certain absorption gives terminal payoff exactly `-1`.
Continuing forever gives `0`. The contrast isolates the cemetery branch
without relying on coalition incidence or chronology.

Lean proves the general facts used by both regressions:

- a sure quitter at any finite live date forces terminal live mass to zero;
- under the constant `-1` table, zero terminal live mass implies payoff
  exactly `-1`; and
- if every player is a literal finite cap, then every observer faces a
  distinct sure-quitting opponent under every behavioral deviation.

Consequently every behavioral deviation against an all-player capped profile
pays exactly `-1`, and its full best-response envelope is exactly `-1`.

## 2. Zero seeds

Let every player Continue forever. Every stopping law has Never mass one, so
the profile is in the zero-seed class. Its prescribed payoff and behavioral
envelope are both zero.

After coordinatewise finite capping, absorption is certain. For every player:

```text
source payoff   =  0,
capped payoff   = -1,
source envelope =  0,
capped envelope = -1.
```

Lean proves both absolute differences are exactly one, for every choice of
finite cap dates. Sending the dates to infinity does not help.

## 3. Exactly one seed

Choose a designated player `s`. Let `s` quit immediately and let every other
player Continue forever. Lean proves literally:

```text
NeverMass(s) = 0,
NeverMass(j) = 1  for every j != s.
```

Thus the source is genuinely in the one-seed class. At `s`:

```text
prescribed payoff = -1,
behavioral envelope = 0,
semantic debt = 1.
```

The envelope is zero because `s` can deviate to Continue forever, producing
Never and payoff zero. No deviation can obtain a positive terminal atom.

In every coordinatewise all-player finite cap:

```text
prescribed payoff = -1,
behavioral envelope = -1,
semantic debt = 0.
```

Indeed, after `s` deviates to Continue, a finitely capped opponent still quits
surely. Lean therefore proves, independently of all cap dates,

```text
|source envelope - capped envelope| = 1,
|source debt     - capped debt|     = 1.
```

This is an obstruction in exactly the semantic coordinates needed by the UE
reduction, not merely a total-variation difference in terminal laws.

## 4. Complete zero-pattern picture

Combining the positive and negative experiments gives the following sharp
reward-uniform classification for literal all-player finite capping:

| Number of zero-Never coordinates | Universal behavior |
|---:|---|
| `0` | impossible: payoff and envelope can stay unit-separated |
| `1` | impossible: envelope and debt can stay unit-separated |
| `>= 2` | possible at every accuracy; the whole profile can be capped |

The positive class additionally admits:

- arbitrary preservation of a prescribed finite entry prefix;
- one common finite horizon for all behavioral deviations; and
- transport of terminal `epsilon`-Nash to
  `(epsilon + 2 delta)`-Nash.

The classification is reward-uniform. Particular reward tables can collapse
the cemetery distinction—for example when the relevant absorbing rewards
equal the Never payoff—and may permit capping in a lower stratum.

## 5. Why stochastic smoothing does not cross the boundary cheaply

Under complete stopping-law mixtures, Never mass is affine:

```text
N((1-lambda) law0 + lambda law1)
  = (1-lambda) N(law0) + lambda N(law1).
```

Starting with positive Never mass and mixing with a zero-Never law leaves
positive Never mass for every `lambda < 1`. Reaching the zero face therefore
requires moving all the way to the zero-Never endpoint. The sharpness example
shows that the full behavioral envelope can detect precisely this support
transition: a player either retains a genuine Never deviation or every
deviation is forced to absorb.

So there is useful smooth affine geometry *inside* a fixed cemetery-support
stratum, but no reward-uniform smooth chart across the zero-Never boundary in
the complete payoff/envelope/debt semantics. Log-survival coordinates can
quantify approach rates when Never mass is already zero; they cannot erase a
positive cemetery atom.

## 6. What remains possible—and what is now proved

The regression rules out only the intended reward-uniform literal finite-cap
reduction. It does not rule out:

- payoff-sensitive reductions exploiting equality or cancellation between
  Never and absorbing rewards;
- weaker semantics which do not retain unrestricted behavioral envelopes;
- retaining an explicit cemetery state in the finite representative rather
  than forcing sure absorption; or
- a finite-state stochastic representation with a genuine Never branch,
  instead of a finite-horizon quitting word.

The last option is the necessary form of any reward-uniform reduction on the
lower strata: the finite object must preserve cemetery support explicitly. A
finite-horizon sure-absorption compiler cannot be equivalent there.

That last option has now been carried out for the complete terminal semantics.
Every profile is approximated by a finite live-root prefix followed by one of
the exact elementary boundaries `Never`, `sureJoint`, or `sureSolo(owner)`.
Payoff, unrestricted behavioral envelope, and debt are all controlled, and
the representative is evaluated by a literal finite backward recursion from
an explicit cemetery-aware boundary pair. See
[`QUITTING_ELEMENTARY_TAIL_SEMANTIC_REDUCTION.md`](QUITTING_ELEMENTARY_TAIL_SEMANTIC_REDUCTION.md).

Thus the no-go result remains sharp specifically for **literal all-player
finite-horizon capping**. It is not an obstruction to finite computation once
the Never state is retained honestly.

## Lean status

Both sharpness capstones compile without `sorry` or `admit`. Their printed
axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`.
