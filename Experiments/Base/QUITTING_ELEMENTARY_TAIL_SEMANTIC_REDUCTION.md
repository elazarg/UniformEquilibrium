# Cemetery-aware finite semantic reduction

## Result

There is an unconditional finite-iteration reduction for the terminal
semantics of a quitting profile, but it is not always a literal
finite-horizon reduction.

For every bounded quitting reward table, behavior profile, and `delta > 0`,
one can retain a finite prefix of the profile's canonical live-root word and
replace its entire remaining tail by exactly one of:

```text
Never:              everyone Continues forever;
sureJoint:          everyone Quits at the first suffix row, then Continue;
sureSolo(owner):    owner alone Quits at the first suffix row, then Continue.
```

The resulting profile simultaneously approximates, for every player:

```text
prescribed terminal payoff,
unrestricted behavioral best-response envelope,
terminal semantic debt = envelope - payoff.
```

The experiment
[`Research/Quitting/ElementaryTailSemanticReduction.lean`](../../Research/Quitting/ElementaryTailSemanticReduction.lean)
also proves that the compressed profile's complete semantic pair is evaluated
*exactly* by finitely many backward operations. If the retained prefix has
length `K`, start from the explicit semantic pair of the chosen elementary
boundary and apply the ordinary one-root semantic-prefix map exactly `K`
times. There is no limiting operation left in this evaluation.

Consequently, an arbitrary terminal `epsilon`-Nash profile has an elementary
compressed representative which is terminal `(epsilon + 2 delta)`-Nash.
Unlike coordinatewise finite capping, this statement needs no zero-Never
seeds.

## 1. The finite quotient

The correct global axis is not the number of playerwise zero-Never buttons.
It is the joint and one-player-deleted survival geometry of the whole live
root word. Exactly one of the following strata occurs:

| Stratum | Survival condition | Suffix |
|---|---|---|
| `N` | joint survival has positive limit | `Never` |
| `J` | joint survival tends to zero and every player-deleted survival tends to zero | `sureJoint` |
| `S_i` | joint survival tends to zero and player `i` is the unique deletion with positive survival limit | `sureSolo(i)` |

For `n` players this gives `n + 2` labeled strata. Lean formalizes the
predicate `QuittingElementaryCapMatchesSurvivalStratum`, proves that a close
elementary representative can be selected in the matching stratum, and
proves that the owner in `S_i` is unique.

This quotient is exhaustive because two distinct positive deleted-player
survival limits would force positive joint survival. It is finer than the
earlier `0 / 1 / at least 2` zero-Never quotient, and it answers a different
question:

- the zero-Never quotient classifies when every player can be given a literal
  finite sure-Quit cap;
- the elementary quotient classifies which single global boundary condition
  accurately replaces the whole tail.

The cap shape depends only on survival geometry. The selected cutoff still
depends on the source profile, accuracy, and convergence rate.

## 2. Exact finite boundary values

The apparently infinite `Never` suffix has the explicit terminal semantic
pair

```text
prescribed_i = 0,
envelope_i   = max(0, q_i),
```

where `q_i` is player `i`'s payoff when it quits alone. The two alternatives
are also finite-dimensional:

```text
Boundary(Never)           = (0, max(0, q_i))_i,
Boundary(sureJoint)       = T_sureJoint(Boundary(Never)),
Boundary(sureSolo(owner)) = T_sureSolo(owner)(Boundary(Never)).
```

Here `T_r` is the exact semantic-prefix action of one product root `r`. Its
first coordinate is the usual prescribed Bellman expectation. Its second
coordinate is the maximum of quitting now and continuing into the supplied
payoff/envelope pair, so it already represents the supremum over all
behavioral deviations.

For retained roots `r_0, ..., r_(K-1)`, define

```text
P_K = Boundary(cap),
P_t = T_(r_t)(P_(t+1))       for t = K-1, ..., 0.
```

Lean proves literally:

```text
P_0 = terminal semantic pair of the compressed behavior profile.
```

Thus “finite number of iterations” is valid for the complete terminal
payoff/envelope/debt calculation at every fixed accuracy. In the `Never` and
`sureSolo(owner)` strata it is important to call this a finite-boundary or
finite-semantic reduction, not sure absorption: an owner can still deviate
into the cemetery branch.

## 3. Why this does not contradict two-seed sharpness

The two-seed theorem and its sharpness regression concern **all-player
coordinatewise sure-Quit caps**. Such a cap removes Never from every prescribed
button and forces every unilateral deviator to meet a sure-quitting opponent
by a common finite horizon. The constant negative reward regression proves
that this is impossible, reward-uniformly, with zero or one zero-Never seed.

The elementary reduction does not remove the cemetery atom in those lower
strata. It retains it as the explicit `Never` boundary pair. In the one-seed
obstruction, the unique sure quitter becomes the owner of `sureSolo(owner)`;
if that owner deviates, the continuation is Never and its envelope remains
zero exactly as it should. The unit semantic gap therefore disappears without
falsifying the sharpness theorem.

The combined classification is:

| Goal | Hypothesis | Result |
|---|---|---|
| literal finite horizon for every deviation | at least two zero-Never buttons | all-player sure-Quit cap |
| finite exact evaluation of an approximate terminal representative | none | finite prefix plus one elementary boundary |

This is the sharp distinction the earlier “make the buttons stochastic” idea
was reaching for. Randomizing a sure cap is not the essential operation.
The essential operation is to retain the cemetery support as a genuine
boundary state whenever survival geometry says it is visible.

## 4. What is and is not equivalent

The theorem is an accuracy-by-accuracy semantic equivalence:

```text
for each source profile and delta > 0,
there exists a finite prefix length K and one elementary boundary.
```

It is not:

- one horizon uniform over all source profiles;
- exact equality with the original terminal law;
- a coordinatewise approximation of every player's stopping law;
- a finite-horizon absorption theorem in the `Never` or sure-solo owner
  branch; or
- a projection to a rowwise exact Nash--Bellman chain.

The output does preserve the original canonical live roots literally at every
date before its selected cutoff. Lean proves the stronger stratified form:
for every requested entrance length `L`, the cutoff can be selected with
`K >= L`, the complete live-root word is then literally unchanged at every
date `< L`, and payoff, envelope, and debt retain the same error bound. This
closes the entry-port timing issue, but not an exact exit anchor.

## 5. Consequence for the UE program

This removes the “infinite terminal optimization” objection for every
survival stratum. At fixed accuracy, the terminal payoff, unrestricted
behavioral envelope, and debt of the representative are finite data produced
by a finite backward recursion. Terminal approximate Nash also transports
with the transparent `2 delta` loss.

It does **not** yet solve the exact-chain compiler problem. The retained roots
need not satisfy the required rowwise Nash--Bellman equations against the
backward semantic values. Nor does tail compression fix an exact exit anchor,
zero-slack Nash face, marked chronology, or a prescribed exact-`D` seam.

The sharpened remaining question is therefore:

```text
Given a finite root word and one of the n+2 exact elementary boundary pairs,
can its finite semantic recursion be repaired/projected to the required
exact Nash--Bellman chain while controlling both external ports?
```

This is materially smaller than the previous question. The infinite tail has
been reduced to finitely many boundary types. The remaining obstruction is
finite exact local compatibility, not infinite behavioral semantics.

## 6. Marked causal atoms: the precise actionable corollary

The compression theorem does **not** supply Nash--Bellman compatibility of
the retained prefix. Its present atom-to-strategy role is narrower, but
useful.

Suppose a signed terminal atom has already been localized at a finite causal
date `m`. Apply elementary compression to the shifted continuation beginning
at `m`, and require it to retain at least the marked row. Lean now proves that
one can choose an absolute cutoff `K > m` such that:

```text
every live root at every date t < K is literally unchanged;
the unconditional mass of every terminal-coalition atom at date m is exact;
the continuation payoff/envelope/debt pair at date m changes by < delta;
the new continuation at m is exactly a finite backward semantic recursion.
```

The second statement is stronger than preservation of a support label. The
survival probability reaching `m` and the complete product root at `m` are
both unchanged, so the chronological atom has exactly the same unconditional
probability.

Two robust consequences are formalized separately:

- if a local scalar has sign `x <= -margin` and the semantic perturbation is
  smaller than `margin`, its compressed value remains strictly negative;
- if a source semantic debt is exactly zero, its compressed debt is less than
  the chosen error tolerance.

The second conclusion is deliberately approximate. Exact zero debt, a
zero-slack Nash face, and rowwise Nash--Bellman compatibility do not follow
from closeness. Likewise, compression does not create a missing signed atom
or a missing local sign. It only ensures that an already localized atom/root
history is retained while its continuation becomes finite-dimensional.

This yields the following honest compiler split:

```text
atom localization and signed estimate          -- still required upstream
marked-date elementary continuation compression -- now proved
finite Nash--Bellman/seam repair                 -- still required downstream
```

## 7. Geometry and Fourier ideas

The useful geometry here is survival/deletion geometry:

```text
joint survival,
one-player-deleted survival,
which deleted clocks retain positive limiting mass.
```

These coordinates determine the finite stratum exactly. Fourier series do
not create this quotient for arbitrary time-varying hazards, because no
periodicity or translation invariance is assumed. Fourier or generating
function methods may still be valuable inside periodic or spectrally
controlled subclasses, especially for explicit convergence rates and hence
effective bounds on `K`. They are rate tools, not the source of the finite
boundary classification.

## Lean status

The experiment compiles without `sorry` or `admit`. Its capstones formalize:

- dependence of the full behavioral envelope only on canonical live roots;
- the `n + 2` survival-stratum selector and uniqueness of a sure-solo owner;
- unconditional simultaneous approximation of payoff, full envelope, and
  debt by an elementary compressed profile;
- arbitrarily late cutoff selection with exact preservation of any requested
  finite canonical live-root entrance block;
- unconditional transport of terminal approximate Nash;
- the explicit Never boundary pair;
- exact finite-dimensional boundary semantics of all three cap forms; and
- exact equality between the compressed profile's semantic pair and the
  `K`-step finite backward evaluator;
- marked-date compression with exact preservation of every preceding root;
- exact preservation of every chronological terminal-coalition mass at the
  marked date;
- approximation of the continuation semantic pair specifically at that
  marked date; and
- elementary strict-sign and zero-to-small-debt stability rules.

All printed capstones use only `propext`, `Classical.choice`, and
`Quot.sound`.
