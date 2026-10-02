# Round 11 Feedback on Aggregate Charged Near-Returns

Reviewer: `CODEX_GAUSS`

Reviewed note: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: Section 40, Proposition 37 only.  Production of the charged
near-return paths is outside this review.

Status: `VALID_ORDINARY_MATHEMATICS`

## Claim reconstructed

Let a nonempty finite exact path in
`quittingPunishmentFloorAdmissibleChargedRelation reward` have edge
absorption charges `q_0,...,q_(K-1)`, whole-block absorption

```text
A = 1-product_(t<K)(1-q_t),
```

and raw path charge `Cpath=sum_(t<K)q_t`.  Proposition 37 asserts that
arbitrarily close endpoint **payoff** coordinates imply a uniform-equilibrium
payoff if either `A` has one fixed positive lower bound or `Cpath` has one
fixed positive lower bound.  Roots, supports, path lengths, and individual
edge charges may vary and no individual charge must stay positive.

I find both implications correct.

## Whole-block absorption and reversal

Every edge charge is `quittingRootAbsorptionMass root`, hence lies in
`[0,1]`.  The exact identity
`quittingCyclicWeightedAbsorption_reversedForwardCycle`
(`UniformEquilibrium/Quitting/Projective/ForwardBlockSingleSeam.lean`) says
that reversing the path changes neither the product nor its absorption
deficit.  Thus the lasso constructor sees exactly `A`, not a bound assembled
from an incorrectly oriented sequence.

For desired error `delta>0`, replace a possibly oversized lower bound by
`c=min(c,1)` and choose endpoint error `delta*c`.  The split

```text
supportError=delta*(1-c),
seamError=delta*c
```

is nonnegative and sums to `delta`.  Endpoint closeness pays the raw closing
seam, while

```text
seamError=delta*c <= delta*A
```

is exactly the weighted closing-ratio field of
`quittingFiniteSingleSeamProjectiveLasso_of_reversedForwardBlock`
(`UniformEquilibrium/Quitting/Projective/ForwardBlockSingleSeam.lean`).
The same indexing, exact-support, and punishment-floor arguments checked in
Round 10 for Proposition 35 apply verbatim.

Because the path is finite and `A>0`, not all factors can equal one, so some
`q_t>0`.  Reversing its index supplies the constructor's literal positive
absorbing phase.  No fixed lower bound on that individual phase is required.
The downstream theorem
`quittingGame_exists_uniformEquilibriumPayoff_of_singleSeamProjectiveLassos`
(`UniformEquilibrium/Quitting/Projective/SingleSeamProjectiveLasso.lean`)
therefore gives the claimed unrestricted-behavior conclusion.

## Raw charge implies block absorption

For a finite list `q_t in [0,1]`, the note uses

```text
product_t(1-q_t) * (1+sum_t q_t) <= 1.                 (CS)
```

The induction is sound.  If the preceding sum is `S`, adjoining `q` changes
the scalar factor by

```text
(1-q)(1+S+q)-(1+S) = -q*S-q^2 <= 0.
```

This exact inequality is already proved in Lean as
`Math.prod_one_sub_mul_one_add_sum_range_le_one`
(`MathUE/DivergentChargeRecurrence.lean`).  Nonnegativity of the survival
product permits division by `1+Cpath>0`, giving

```text
A >= Cpath/(1+Cpath) >= C/(1+C)
```

whenever `Cpath>=C>0`; the last orientation uses monotonicity of
`x/(1+x)` on nonnegative reals.  Part 1 applies with
`c=C/(1+C)`.

## Relation to checked packages and exact scope

The recently checked
`quittingGame_exists_uniformEquilibriumPayoff_of_admissiblePath_payoffNearReturns`
(`UniformEquilibrium/Quitting/Projective/PunishmentFloorNearReturn.lean`)
packages Proposition 35's fixed **edge** threshold, not Proposition 37's
aggregate block threshold.  The more primitive reversed-forward constructor
already accepts the whole-block weighted absorption and therefore is the
correct checked consumer for the new ordinary-mathematics adapter.

`exists_singleSeamProjectiveLasso_of_finiteForwardPackets`
(`UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`)
derives a close block with aggregate charge from arbitrarily large charge in
one fixed compact packet.  Proposition 37 neither reproves that compactness
selection nor requires its common-carrier/arbitrarily-large-charge producer;
it states the weaker direct endpoint condition after such a block has been
found.  This novelty comparison is accurate.

The proposition remains a conditional boundary weakening.  It does not show
that arbitrary games generate the same-path macroscopic charge and payoff
near-return.

## Verdict

Proposition 37 is valid ordinary mathematics.  The reversal orientation,
whole-block absorption identity, error split, positive-phase extraction,
support/floor fields, elementary charge-to-absorption estimate, and relation
to the existing checked packages all survive falsification.  I found no
mathematical objection.
