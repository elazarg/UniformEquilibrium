# Finite capping of stochastic quitting buttons

## Result

A stochastic quitting button can be reduced to finitely many effective dates,
with simultaneous control of terminal payoff, behavioral envelope, and debt,
under a sharp and interpretable tail condition.

Given one player's live hazard `h` and a cutoff `K`, the finite cap:

```text
keeps h(t) for t < K,
Quits surely at t = K,
Continues surely for t > K.
```

Thus the modified button has no effective decisions after `K`. The production
finite-splice estimates isolate the dimensionless error

```text
E(K) = lateFiniteMass(K)
     + NeverMass * maxPairDeletedSurvival(K).
```

The experiment
`QuittingStoppingLawFiniteCapConvergence.lean`
proves:

```text
lateFiniteMass(K) -> 0.
```

Consequently `E(K) -> 0` under either of two conditions:

1. the button has zero `Never` mass; or
2. the maximal pair-deleted survival clock tends to zero.

The experiment now identifies condition 2 exactly: it holds iff two distinct
other players have zero Never mass. Thus these alternatives are a complete
classification of when the explicit universal splice error vanishes.

For every `delta > 0`, one finite cutoff then works simultaneously for every
player `i`:

```text
|payoff_i(original) - payoff_i(capped)| < delta,
|BR_i(original)     - BR_i(capped)|     < delta,
|debt_i(original)   - debt_i(capped)|   < delta.
```

Here `BR_i` is the unrestricted supremum over all behavioral deviations, not
a pure-time or finite-deviation proxy.

There is now a substantially stronger all-player theorem. It is enough that
**two distinct original buttons** have zero Never mass. Cap those two first;
they become permanent finite sure-Quit sentinels. Every remaining button can
then be capped in turn, with no restriction at all on its Never mass, while
the same three semantic coordinates remain uniformly within `delta` for every
player. Every unilateral deviator then faces a distinct finitely capped
opponent, so the capped profile's behavioral deviation problems are genuinely
finite-horizon.

Thus positive Never mass is not a global obstruction. It is only a bootstrap
obstruction: two initially cappable coordinates unlock the entire finite
player set.

There is also a direct approximate-equilibrium corollary. If the original
profile is terminal `epsilon`-Nash, then the capped profile can be chosen
terminal `(epsilon + 2 delta)`-Nash while remaining within `delta` in the full
terminal semantics. The factor two is the transparent cost of perturbing both
the best-response envelope and prescribed payoff by at most `delta`.

## 1. Why late finite mass always disappears

Every Boolean hazard induces a subprobability distribution of finite stopping
dates plus a possible cemetery atom `Never`. Its finite stopping masses form a
summable nonnegative sequence. The mass strictly after `K` is a tail sum:

```text
lateFiniteMass(K) = sum_{t > K} P(stop exactly at t).
```

Tail sums tend to zero without any game-theoretic assumption. This closes the
finite-date part of the problem completely. All persistent difficulty is in
the cemetery atom.

## 2. Why the deleted clock multiplies Never

Moving finite stopping mass from after `K` to `K` changes chronology whenever
that mass is reached, so it is charged absolutely.

The `Never` atom is different. It matters to observer `i` only on histories
which survive to the cap after deleting both:

- the moved player, whose button is being reset; and
- observer `i`, whose arbitrary behavioral deviation must be controlled
  uniformly.

This gives the pair-deleted clock. Taking the maximum over observers produces
one error valid for every payoff coordinate and every behavioral envelope.

The decomposition is therefore:

```text
finite tail       -> always vanishes,
Never cemetery    -> harmless if the relevant deleted clocks die,
persistent Never × deleted survival -> unresolved tail obstruction.
```

The last expression is the obstruction exposed by this estimate. It is not
claimed to be logically necessary in games where payoff cancellations could
make the actual error smaller.

## 3. What “finite reduction” means here

The theorem is accuracy-by-accuracy:

```text
for each profile and delta, there exists a finite K(profile, delta).
```

It is not yet a uniform horizon depending only on the number of players and
`delta`. With two zero-Never seeds the one-player caps can be telescoped over
the finite player set, but the selected playerwise dates still depend on the
profile. A uniform finite-iteration theorem for a class of profiles would need
a uniform rate for:

```text
lateFiniteMass(K) -> 0
```

and, when `NeverMass > 0`, for:

```text
maxPairDeletedSurvival(K) -> 0.
```

Without such rates, compactness may select finite representatives but does not
give an effective common cutoff.

## 4. An exact finite zero-pattern classification

The deleted-clock geometry can now be computed exactly. Write `N_j` for
player `j`'s Never mass. For mover `m` and observer `i`, Lean proves the
finite pair-deleted clock is the product of the individual survival curves
after forcing `m` and `i` to Continue. Passing to the limit gives, equivalently,

```text
pairDeletedLimit(m, i) = product of N_j over j outside {m, i}.
```

In particular:

```text
maxPairDeletedLimit(m) = 0
iff at least two distinct players other than m have zero Never mass.
```

The production error has the exact limit

```text
finiteSpliceError(m, K)
    -> N_m * maxPairDeletedLimit(m).
```

Therefore the universal cap criterion itself has the finite equivalence

```text
finiteSpliceError(m, K) -> 0
iff N_m = 0
    or two distinct other players have zero Never mass.
```

This is stronger than the earlier sufficient-condition split: it is an exact
classification of the explicit payoff-independent splice bound. It is still
not a necessity theorem for the actual payoff error, because a particular
reward table may create cancellations which the universal bound ignores.

For a whole profile, let `Z = {j : N_j = 0}`. The zero pattern collapses to
three global bootstrap classes:

```text
|Z| = 0:  no coordinate satisfies the universal cap criterion;
|Z| = 1:  only the unique zero-Never coordinate is initially cappable;
|Z| >= 2: every coordinate is cappable, and the whole profile can be capped.
```

This is a genuinely finite quotient in a useful axis: only the zero support
of the Never-mass vector matters, and globally even its exact support reduces
to cardinality truncated at two. It does not make the strategy space finite;
inside a class, stopping dates, hazard values, convergence rates, and selected
cutoffs remain continuous data.

The lower two classes are now known to be genuinely different in the full
semantics, not merely failures of this estimate. Under the constant `-1`
absorbing reward table, an all-Continue zero-seed source stays exactly unit
distance in payoff and envelope from every all-player finite cap. A source
with exactly one zero-Never player stays exactly unit distance in envelope and
semantic debt from every all-player finite cap. See
[`QUITTING_FINITE_CAP_SEED_SHARPNESS.md`](QUITTING_FINITE_CAP_SEED_SHARPNESS.md).

There is nevertheless an unconditional **finite-semantic** reduction in all
three classes: retain one finite global root prefix and attach a cemetery-aware
elementary boundary (`Never`, `sureJoint`, or `sureSolo(owner)`). Its full
payoff/envelope/debt pair is then computed exactly by finitely many backward
semantic-prefix steps. This does not force finite-horizon absorption and so
does not contradict the sharpness result. See
[`QUITTING_ELEMENTARY_TAIL_SEMANTIC_REDUCTION.md`](QUITTING_ELEMENTARY_TAIL_SEMANTIC_REDUCTION.md).

### The geometry behind the quotient

The player-varying occupation geometry here is multiplicative. At horizon
`K`, each player's survival curve is

```text
S_j(K) = product over t < K of ContinueProbability(j, t).
```

The pair-deleted clock is a monomial in the `S_j(K)` outside the two deleted
coordinates. At infinity the same monomial is evaluated on the Never-mass
vector `(N_j)`. Thus its zero locus is a union of coordinate faces. Taking the
maximum over the deleted observer asks whether the zero support hits every
such face; since one observer can delete at most one zero coordinate, the
minimal hitting set has size two.

This suggests the right general abstraction. If a semantic envelope required
uniform control after deleting a mover and up to `r` additional coordinates,
then the corresponding payoff-independent occupation mechanism should need
`r+1` zero-Never seeds. The present theorem is the `r=1` case. Whether the
relevant coalition-deviation or multi-controller semantics really factor in
this way is a standalone question; it is not proved here.

There is a useful linearization for rates:

```text
-log S_j(K) = sum over t < K of -log ContinueProbability(j, t),
```

whenever the factors are positive. Pair-deleted products then become sums of
playerwise log-survival occupations. This may be the right coordinate system
for uniform-rate estimates and compactness. Fourier series or generating
functions could still help on periodic, eventually periodic, or spectrally
controlled hazard families. For arbitrary time-varying buttons, however,
there is no translation-invariant or periodic structure to exploit, and the
exact finite quotient above comes from support/deletion geometry rather than
frequency modes.

After capping, the same threshold has an exact sentinel form:

```text
0 sentinels: each new cap needs its own tail condition;
1 sentinel:  still insufficient for uniform behavioral envelopes;
2 sentinels: every remaining coordinate is automatically cappable.
```

The threshold two is exactly the rank of the deletion in the semantic
estimate. A best-response coordinate deletes the moved player and one
observer. Two sentinels ensure that at least one survives that deletion and
kills the clock. Lean proves eventual exact vanishing, not merely convergence:
after both sentinel rows have occurred, every relevant maximum pair-deleted
clock is literally zero.

Before capping, if a player survives both deletions, the pair-deleted clock is
bounded above by that player's own survival curve. Hence two distinct
zero-Never opponents already force the mover's maximal clock to tend to zero.
An arbitrary third button, including one with positive Never mass, is directly
cappable. Converting the two seeds to finite sentinels upgrades asymptotic
decay to eventual exact zero and makes the subsequent induction stable.

The same argument also shows why one sentinel is not enough for this estimate.
Choose that sentinel as the observer. It is then deleted together with the
mover; if all remaining players Continue surely, the corresponding clock is
exactly one at every horizon. Lean formalizes both the one-sentinel equality
and the two-sentinel zero theorem. This is sharpness of the current uniform
clock mechanism, not a no-go theorem for every possible payoff-sensitive
repair.

## 5. Relation to exact dynamic debt

One finite cap makes one player's prescribed button Continue forever after
its sure-Quit cap row. It does **not** by itself make the entire profile a
finite operational root word: the other players may retain infinite tails,
and a deviation by the capped mover can bypass its prescribed sure-Quit row
and see those tails.

The all-player telescope now closes this issue under the weaker two-seed
hypothesis. First cap two distinct zero-Never buttons. These two caps survive
all later coordinate updates. For any third mover and any observer, deleting
the mover and observer leaves at least one of the two capped sentinels; its
sure-Quit row makes the deleted survival clock eventually exactly zero. The
one-button cap theorem therefore applies to the third mover even if it has
positive Never mass. Repeating this over the finite player set and applying
triangle inequalities gives the global theorem.

The induction maintains four literal invariants:

1. both seed coordinates remain their original finite caps;
2. every processed coordinate is a finite cap of its original law;
3. every unprocessed nonseed coordinate still equals its original law; and
4. payoff, envelope, and debt errors grow by at most one budget unit per cap.

In a nontrivial player set, any unilateral deviator then faces at least one
distinct capped opponent. That opponent quits surely at its finite cap date,
so every deviating problem absorbs by a finite date. Lean formalizes the
existence of this deviation-independent finite sure quitter. Taking the
maximum of one selected cap date per player gives a single profile-dependent
horizon `H`: for every observer and every behavioral deviation, some opponent
quits surely at a row `< H`. This is a uniform finite iteration bound across
the entire (infinite-dimensional) deviation space, although `H` is not uniform
over source profiles or accuracies.

Once an all-player capped word is also represented by an exact zero-boundary
Nash--Bellman chain, the dynamic-debt bridge says each stored exact-`D`
coordinate is its literal behavioral semantic debt.

What finite capping does not guarantee is local exact-chain validity. Capping
one button can disturb:

- the prescribed Bellman value recursion chosen for a production chain;
- zero-slack root Nash faces; and
- the required two-ended exact seam anchors.

The entry-root issue itself is now closed. The cutoff selector accepts an
arbitrary lower bound `L`, and the two-seed all-player induction threads the
same `L` through every cap. Since a cap leaves the original hazard unchanged
strictly before its cutoff, the complete prescribed live-root word is
literally unchanged at every time `< L`. Taking `L=1` fixes the time-zero root;
larger `L` fixes any prescribed finite entrance block. This is exact prefix
preservation, not approximate root control. It still does not fix an exit
anchor or restore rowwise Nash--Bellman equations after the preserved prefix.

Thus the two results fit together as follows:

```text
one stochastic button
        |
        | finite cap, small terminal-semantic error
        v
one finite-support button
        |
        | cap all remaining players and telescope errors
        v
finite behavioral profile
        |
        | exact-chain projection/repair
        v
production exact-D chain
        |
        | exact semantic bridge
        v
literal payoff/root/behavioral-debt port
```

Under the two-zero-Never-seed hypothesis, the all-player arrow is now proved,
including profiles whose other buttons have arbitrary positive Never mass.
Moreover terminal approximate Nash is transported directly to the capped
profile with only twice the semantic tolerance. The remaining nontrivial
arrow is not terminal Nashification; it is projection to a rowwise exact
Nash--Bellman chain while controlling both external ports.

## 6. Relation to time-decaying effectiveness

A button whose effectiveness decreases with time is useful only insofar as it
forces one of the two tail quantities to decay.

- If decreasing effectiveness still gives eventual stopping probability one,
  then `NeverMass=0` and finite capping converges.
- If it leaves positive Never mass, decay of the player's own hazard is not
  enough. The other players' pair-deleted survival clocks must also die, or a
  cemetery branch remains visible to deviations.

So “make each button less effective over time” is not by itself the right
condition. The correct invariant is stopping-law cemetery mass multiplied by
the appropriate player-deleted survival geometry.

## 7. Revised next question

There are now two complete but distinct reductions:

```text
two zero-Never seeds -> literal finite horizon for every deviation;
arbitrary profile    -> finite prefix plus one cemetery-aware boundary pair.
```

The next compiler-facing question is:

```text
Can a finite root word with one of the finitely many exact elementary boundary
pairs be projected to an exact finite Nash--Bellman chain while fixing the
prescribed entry and exit exact-D ports?
```

A positive answer with a uniform tail rate would reduce the relevant UE
problem to an effective number of iterations at each accuracy. Without a
uniform tail rate, the number of retained rows remains profile-dependent.
Without preserving the elementary boundary, literal sure-absorption remains
false in the persistent cemetery regimes.

## 8. Lean inventory

The experiment formalizes:

- convergence of late finite stopping mass to zero for every hazard;
- convergence of the explicit splice error when `NeverMass=0`;
- convergence when the maximal pair-deleted clock tends to zero;
- exact factorization of terminal pair-deleted survival into individual Never
  masses, the iff characterization by a surviving zero-Never coordinate, and
  the resulting exact `0 / 1 / at least 2` zero-pattern classification;
- the iff classification of splice-error convergence: zero Never mass at the
  mover or two zero-Never opponents;
- an abstract one-cutoff theorem simultaneously controlling all players'
  prescribed payoff, full behavioral envelope, and semantic debt;
- the no-Never finite-cap specialization;
- the dying-deleted-clock specialization;
- exact zeroing of the maximal deleted clock by two finite sentinels;
- asymptotic zeroing by two uncapped zero-Never opponents, and the resulting
  direct cap theorem for an arbitrary third button;
- a sharp one-sentinel counter-geometry in which that maximal clock stays
  exactly one;
- the local two-sentinel extension step for an arbitrary positive-Never
  button;
- the finite-player telescope which caps every button from only two
  zero-Never seeds, within one common semantic error budget;
- arbitrary-late cap selection and exact preservation of any prescribed
  finite live-root prefix through the global telescope;
- transport of terminal `epsilon`-Nash to terminal
  `(epsilon + 2 delta)`-Nash under that global cap; and
- a common finite horizon before which every unilateral deviation encounters
  a sure-quitting opponent in the all-player capped profile.

The file compiles without `sorry` or `admit`. All printed capstones use only
`propext`, `Classical.choice`, and `Quot.sound`.
