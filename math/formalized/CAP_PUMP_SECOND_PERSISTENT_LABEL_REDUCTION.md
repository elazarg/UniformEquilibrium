# Bounded cap pumps force a second persistent quitting label

Author: `CODEX_NOETHER`

Independent reviews:
[Gauss, cap-pump telescope](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_GAUSS__ROUND_50.md),
[Gauss, known-mover excess](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_GAUSS__ROUND_51.md),
and
[Gauss, sharp one-label obstruction](../feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_GAUSS__ROUND_52.md).

## Exact statement

Let `I` be a nonempty finite player set.  Time is partitioned into finite
nonempty blocks.  In block `k`, at local dates `0 <= t < N_k`, players use a
product mixed Quit/Continue row with marginal Quit probabilities

```text
p(k,t,j) in [0,1],        j in I.
```

Fix a player `i`.  Put

```text
O(k,t,i) = product_(j != i) (1-p(k,t,j)),
```

the probability that every opponent of `i` Continues.  Suppose terminal
reward coordinates have absolute value at most `M`, where `M>=0`.

Attach a real candidate cap `b(k,t,i)` at every block state
`0 <= t <= N_k`.  Assume `|b(k,t,i)|<=K` for one `K>=0` and exact within-block
cap recursion

```text
b(k,t,i)=max(Q(k,t,i), C(k,t,i)+O(k,t,i)b(k,t+1,i)).    (1)
```

Here `Q(k,t,i)` is the successor-independent value of forcing player `i` to
Quit at that row, while `C(k,t,i)` is the unnormalized reward contribution
when `i` Continues and at least one opponent Quits.  Thus

```text
|C(k,t,i)| <= M(1-O(k,t,i)).                            (2)
```

Define the favorable cap drop and reverse violation at seam `k` by

```text
R(k,i) = (b(k,N_k,i)-b(k+1,0,i))_+,
V(k,i) = (b(k+1,0,i)-b(k,N_k,i))_+,                    (3)
```

and the rowwise opponent-absorption budget of block `k` by

```text
A(k,i)=sum_(t<N_k)(1-O(k,t,i)).                         (4)
```

Then, for every natural number `n`,

```text
sum_(k<n) R(k,i)
 <= sum_(k<n) V(k,i)
    +(K+M)sum_(k<n)A(k,i)+2K.                           (5)
```

Consequently, if

```text
sum_k R(k,i)=infinity,
sum_k V(k,i)<infinity,                                  (6)
```

then

```text
sum_(k,t)(1-O(k,t,i))=infinity.                         (7)
```

Some fixed opponent `j!=i` therefore has divergent marginal Quit hazard:

```text
sum_(k,t)p(k,t,j)=infinity.                             (8)
```

If player `i` also has divergent marginal Quit hazard, `i,j` are two distinct
persistent labels.  Hence joint survival and every one-player-deleted
survival of the same literal root chronology vanish from every suffix.

There is a sharp form when the already persistent label is a known mover
`a!=i`.  Define

```text
P_a(n)=sum_(k<n)sum_(t<N_k)p(k,t,a).
```

For every `n`,

```text
sum_(k<n)R(k,i)-sum_(k<n)V(k,i)-2K-(K+M)P_a(n)
 <= (K+M)sum_(k<n)sum_(t<N_k)sum_(j!=i,a)p(k,t,j).      (9)
```

If the left side of (9) is unbounded above, some fixed
`j` outside `{i,a}` has divergent marginal Quit hazard.  Thus `a,j` are the
required two persistent labels.  Merely having divergent favorable observer-
cap drops is insufficient: those drops can be funded entirely by mover `a`.

## Conjecture-facing change

This strictly narrows the live obligation
[`questions/PERSISTENT_TWO_LABEL_HAZARDS.md`](../questions/PERSISTENT_TWO_LABEL_HAZARDS.md).
That obligation asks a source-matched chronology to retain two preselected
divergent labels on the same roots used by the Bellman or chronological
construction.  The present reduction removes the need to select the second
label whenever the same bounded construction supplies either:

1. divergent favorable cap drops for a cap owner whose own hazard is already
   persistent, with summable reverse rises; or
2. for a distinct known mover `a`, cap-drop excess unbounded after subtracting
   the mover hazard account in (9).

The conclusion is on the original literal roots.  No root or hazard is
reprojected, and the second label is recovered by finite pigeonhole rather
than chosen block by block.

The distinction between cases 1 and 2 is necessary.  The sharp example below
has every analytic one-sided seam field, divergent favorable observer-cap
drops, and one persistent mover, yet the mover-deleted clock stays equal to
one.  Thus the prior open phrase “obtain a second label from a cap pump” is
replaced by the exact quantitative requirement (9).

What remains open is source production: current atom/reset data have not been
shown to orient a bounded cap pump satisfying (6) in the cap owner's own
coordinate, or to make the excess in (9) unbounded.

## Definitions and assumptions

At each live date, players randomize independently within the product row.
Across dates, the root may depend on the unique public all-Continue history;
no stationarity or independence across dates is assumed.  Marginal hazards
and survival products are the literal conditional probabilities along that
history.

When `b` is the literal semantic best-response cap of an executable tail,
(1) is the ordinary unrestricted behavioral best-response recursion.  At the
displayed row a deviator may choose Quit or Continue.  The Quit branch is
successor-independent.  In the Continue branch, any opponent Quit absorbs
immediately, while the all-opponents-Continue event reaches the successor
unrestricted cap with coefficient `O(k,t,i)`.  Taking a supremum over all
behavioral continuations therefore gives the maximum in (1), even when the
supremum is not attained.  No bounded-controller or pure-time restriction is
used.  For possibly artificial candidate caps, the theorem does not derive
this semantic identity: exact scalar recursion (1) is an explicit assumption.

The theorem itself is a scalar consequence of (1).  Candidate caps need not
already be semantic caps of one complete profile; this permits its use in the
conditioned block/seam construction.  When they are generated from actual
terminal semantic prefixes or an exact Nash--Bellman spine, (1) is the literal
cap identity.

“Persistent” means divergence of the nonnegative marginal hazard series.
Removing any finite prefix preserves divergence.  A persistent pair need not
Quit simultaneously or be active in the same block.

## Source correspondence

The checked theorem
`hasTwoPersistentQuittingMarginals_iff_all_suffix_survival_zero`
(`UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean`)
identifies two divergent marginal labels with the required joint and every-
deleted suffix survivals.  Its robust consumers
`QuittingChronologicalDebtShadowingSurvivalFields.of_twoPersistent`,
`.of_consecutiveBlock_summableError`, and
`.of_consecutiveBlock_fixedFraction` provide the survival fields used by
chronological debt shadowing.

The cap-prefix object `quittingTerminalSemanticPrefix` is defined in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.  The theorem
`exists_quittingTerminalSemanticPrefix_secant`
(`UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean`)
records that its cap coordinate is monotone and has secant at most the
opponent Continue mass.  The unrestricted successor cap is
`quittingContinuationBestResponseValue`
(`UniformEquilibrium/Quitting/Root/FirstBranch.lean`).

The packet
[`formalized/PERSISTENT_DELETED_CLOCK_TWO_LABEL_REDUCTION.md`](../formalized/PERSISTENT_DELETED_CLOCK_TWO_LABEL_REDUCTION.md)
starts with two persistent labels; it does not generate one from cap motion.
Cedar Proposition 4 in
[`notes/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION.md`](../notes/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION.md)
identifies the favorable sign of a donated-to-next cap drop, but does not
prove that bounded Bellman motion replenishing repeated drops forces an
opponent clock.  Equations (5) and (9), together with the sharp obstruction,
are the new ordinary mathematics.

Gauss Proposition 60 gives a later reached-path analogue and explicitly
derives it from this result; it is not a prior source.  No paper theorem is
used.

## Proof

### One-row cap replenishment

The maximum in (1) dominates its Continue branch.  Therefore

```text
b(k,t+1,i)-b(k,t,i)
 <= (1-O(k,t,i))b(k,t+1,i)-C(k,t,i).
```

Taking positive parts and using (2) and `|b(k,t+1,i)|<=K` gives

```text
(b(k,t+1,i)-b(k,t,i))_+
 <= (K+M)(1-O(k,t,i)).                                 (10)
```

This calculation is valid across a switch between the forced-Quit and
Continue branches because it uses only that the maximum dominates the
Continue branch.

Summing (10) inside block `k` bounds the signed net rise by its positive
variation:

```text
b(k,N_k,i)-b(k,0,i) <= (K+M)A(k,i).                    (11)
```

### Seam telescope

For real `x,y`, `(x-y)_+-(y-x)_+=x-y`.  Thus

```text
R(k,i)-V(k,i)=b(k,N_k,i)-b(k+1,0,i).
```

Insert and subtract `b(k,0,i)` and sum over `k<n`:

```text
sum_(k<n)(R(k,i)-V(k,i))
 =sum_(k<n)(b(k,N_k,i)-b(k,0,i))
   +b(0,0,i)-b(n,0,i).                                 (12)
```

Use (11) on the first term and the uniform bound `|b|<=K` on the boundary
term.  Rearranging proves (5).

If the opponent-absorption sum in (7) were finite, (5), summability of `V`,
and the fixed boundary `2K` would uniformly bound the partial sums of `R`,
contradicting (6).  This proves (7).

### Fixed-label extraction

At every product row, the event that some opponent of `i` Quits is contained
in the union of the individual opponent Quit events.  Hence

```text
1-O(k,t,i) <= sum_(j!=i)p(k,t,j).                       (13)
```

By (7), the sum of the finitely many opponent marginal series diverges.
At least one fixed `j!=i` therefore has divergent series, proving (8).  If
`i` is persistent, the two labels are distinct.  The checked two-label
criterion then gives every required suffix survival.

For the known-mover refinement, separate `a` in (13):

```text
1-O(k,t,i)
 <= p(k,t,a)+sum_(j!=i,a)p(k,t,j).
```

Substitute this in (5), subtract `(K+M)P_a(n)`, and rearrange.  This is (9).
If its left side is unbounded, the finite sum of all remaining marginal
series is unbounded, so one fixed remaining label is persistent.

## Boundary tests

### Positive excess test

Take three players `{a,i,j}` and zero terminal rewards.  At every row let
`a` Quit with fixed probability `alpha in (0,1)`, let `j` Quit with fixed
probability `beta in (0,1)`, and let `i` Continue.  Put

```text
O_i=(1-alpha)(1-beta).
```

Use one-row blocks with donated endpoint cap `1` for `i`, source and next
candidate cap `O_i`, and zero for all other candidate coordinates.  Since
`H_i(z)=O_i z`, the within-block recursion is exact.  Every seam has

```text
R=1-O_i,       V=0.
```

With `K=1,M=0`, subtracting the known mover account `alpha` leaves linear
per-row excess

```text
(1-O_i)-alpha=(1-alpha)beta>0.
```

Thus (9) is unbounded and recovers a fixed label outside `{i,a}`, necessarily
`j`.  Both `a` and `j` are persistent, so all required clocks vanish.

### Sharp one-label obstruction

Take two players `{a,i}` and again set every terminal reward coordinate to
zero.  Fix `0<h<1`.  At every date let mover `a` Quit with probability `1-h`
and observer `i` Continue surely.  Use one-row blocks.  Give the donated
endpoint candidate pair zero prescribed value and caps

```text
b^-(a)=0,       b^-(i)=1,
```

while the block source and next global candidate source have zero prescribed
value and caps

```text
b^+(a)=0,       b^+(i)=h.
```

For player `i`, `H_i(z)=hz`.  Hence the donated endpoint prefixes to source
cap `h`, while prefixing the actual next candidate cap gives `h^2`.  The
global direct-debt defect is therefore

```text
E_i=h-h^2>0,
```

so every adverse forcing sum is nonpositive.  The generated cap secant
against the actual zero semantic cap is exactly `h`; prescribed defects are
zero; candidate debts are nonnegative and bounded.  Choosing
`h=min(eta/2,1/2)` makes the only initial candidate debt at most any requested
`eta>0`.

At every seam,

```text
R=1-h=p_a,       V=0.
```

Thus favorable drops diverge, but for the minimal bounds `K=1,M=0` the
mover-subtracted left side of (9) is the bounded constant `-2`, not an
unbounded excess.  Joint survival and survival after deleting `i` are `h^n`;
after deleting `a`, the sure-Continue observer leaves survival identically
one.  Exactly one deleted clock fails.

This all-zero game has a trivial equilibrium.  It is an interface-sharpness
example, not a counterexample to uniform equilibrium.

### Other boundaries

- If `O=1`, then `C=0` and the Continue branch equals the successor cap, so a
  prefix cannot lie below its successor.  The right side of (10) is zero.
- If `O=0`, (10) permits a full bounded reset at cost at most `K+M`.
- Summability of reverse violations is essential: arbitrary alternating seam
  rises can fund divergent later drops with no internal opponent absorption.
- Uniform boundedness is essential: unbounded endpoint caps can fund the
  seam account through the terminal boundary rather than literal absorption.
- With one player, there are no opponents.  Inequality (5) prevents its
  divergence hypotheses from holding, as required.

## Adapter and consumer

The adapter input is one supplied literal-root chronology with bounded
candidate annotations satisfying the assumed exact within-block scalar cap
recursion.  This is the data shape sought when finite donated Bellman blocks
are concatenated and their endpoint mismatch is localized at seams; the
packet does not claim that arbitrary semantic source data produces it.  No
root may be changed after applying the theorem: all hazards in the conclusion
are the actual hazards of the supplied roots.

If the cap owner is already persistent, (5)--(8) produce the second fixed
label.  If a distinct mover is the known persistent label, (9) produces a
second label from the stated excess.  The checked
`QuittingChronologicalDebtShadowingSurvivalFields.of_twoPersistent` then
supplies the joint and every-deleted survival fields for those same roots.

If the roots and payoffs form an exact bounded Nash--Bellman spine, the
checked
`nonempty_quittingChronologicalDebtShadowingCertificate_of_exactSpine`
(`UniformEquilibrium/Quitting/Debt/Dynamic/NashBellmanChronologicalForcing.lean`)
combines those survival fields with zero non-survival defects.  For a more
general one-sided candidate construction, the other discrepancy, forcing,
boundedness, and initial-debt certificate fields remain separate.

Thus this packet is a strict reduction of second-label production, not an
arbitrary-game producer and not a semantic equilibrium theorem.

## Lean handoff

A narrow formalization should reuse the existing finite-player root hazards,
opponent Continue mass, and two-persistent-label theorem.  Natural theorem
shapes are:

1. a one-row lemma bounding positive cap rise by
   `(K+M)*(1-opponentContinueMass)` under the scalar cap recursion;
2. a finite block/seam telescope proving (5);
3. a divergence corollary producing one persistent opponent;
4. the known-label excess corollary (9); and
5. the exact `Fin 2` obstruction with zero rewards and `h in (0,1)`.

Likely reusable definitions are `quittingTerminalSemanticPrefix`,
`quittingRootOpponentContinueMass`, and the marginal Quit probability used by
`hasTwoPersistentQuittingMarginals_iff_all_suffix_survival_zero`.  The proof
uses only finite sums, positive parts, the finite union bound, and ordinary
series nonsummability.  The `Fin 2` test at `h=1/2` and the `Fin 3` positive
test at `alpha=beta=1/2` are exact rational regressions.

The narrowest checks are the new single-file Lean check and the project trust
scan.  No new structure should assume persistent labels or the desired clock
limits as fields of the cap-pump input.

## Scope and nonclaims

- The packet does not orient favorable seams from arbitrary quitting-game,
  atom, reset, or paid-row data.
- It does not prove divergent cap drops, summable reverse rises, persistent
  own hazard, or the known-mover excess.
- It does not construct an exact Nash--Bellman spine, small initial debt, or
  the remaining chronological certificate fields.
- It does not restrict unilateral deviations to pure times or bounded
  controllers; it makes no equilibrium claim at all.
- It does not prove a uniform-equilibrium payoff or a counterexample.
- The sharp two-player table is not a game counterexample.  It proves only
  that a favorable observer-cap pump can be monopolized by the existing
  mover and therefore cannot replace the excess condition in (9).
