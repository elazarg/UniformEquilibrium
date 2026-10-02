# Review of all-suffix clock characterization by `CODEX_NOETHER`

Reviewed note:
[`CHATGPT_EXTERNAL__ALL_SUFFIX_CLOCK_CHARACTERIZATION.md`](../notes/CHATGPT_EXTERNAL__ALL_SUFFIX_CLOCK_CHARACTERIZATION.md).

## Verdict

The scalar criterion, arbitrary-deleted-set rule, four-player calculation,
and packet-boundary equivalence are valid ordinary mathematics.  The two
suggested Lean closures use real API names and correct summability orientation,
but they are already present in a stronger checked form in
`UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean`.

The general deleted-set form adds no currently needed consumer adapter: the
chronological certificate asks only for one-player-deleted clocks.  The
packet-boundary form is the one modest useful increment.  It converts lower
bounds on **actual executed packet** opponent-absorption probabilities into
the existing suffix-survival fields, without extracting two persistent
labels.  It is worth retaining as an internal lemma shape if a conditioned
packet producer naturally outputs those block probabilities.  In the absence
of such a producer, it does not justify extending the existing formalized
packet or creating a new export.

The four-player example is a correct source-matched regression for the clock
semantics, not a source adapter, equilibrium, or small-debt construction.

I did not run Lean and claim no new `L`, `A`, or `C` seal.

## 1. Existing checked API subsumes Section 5

The exact current declarations in
`UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean` are:

- `all_opponentClocks_iff_all_suffix_survival_zero`;
- `hasTwoPersistentQuittingMarginals_iff_all_suffix_survival_zero`;
- `tendsto_jointSurvival_zero_of_opponentSurvival_zero`;
- `HasTwoPersistentQuittingMarginals.survival`; and
- `QuittingChronologicalDebtShadowingSurvivalFields.of_twoPersistent`.

Thus the proposed
`allTail_opponentSurvival_iff_not_summable_charge` is only the fixed-player
specialization of the first theorem.  Its proof body is mathematically and
API-wise oriented correctly:

- `exists_suffix_half_le_quittingOpponentSurvivalWeight_of_summable` and
  `ge_of_tendsto'` prove the reverse implication;
- `tendsto_zero_quittingOpponentSurvivalWeight_of_not_summable_charge`
  consumes the shifted nonsummability statement; and
- `(summable_nat_add_iff start).1` has the displayed direction after rewriting
  `start+offset` as `offset+start`.

This is exactly the argument already used in the checked file's private
`not_summable_nat_add_of_not_summable` and public equivalence.

The proposed joint theorem is likewise already checked as
`tendsto_jointSurvival_zero_of_opponentSurvival_zero`.  Its displayed squeeze
uses the genuine declarations
`quittingJointSurvivalWeight_nonneg` and
`quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight`, the latter in
`UniformEquilibrium/Quitting/Boundary/Repair/JointComplementarity.lean`.
The production theorem is slightly better aligned with the chronological
consumer because it concludes directly about the `Math.survivalProduct`
appearing in `joint_survival`.

Accordingly Section 5 should be read as a correct implementation sketch for
already checked declarations, not an unclosed Lean obligation.  The note's
link to `exports/PERSISTENT_DELETED_CLOCK_TWO_LABEL_REDUCTION.md` is stale in
the refreshed tree; folder placement now records the packet under
`formalized/PERSISTENT_DELETED_CLOCK_TWO_LABEL_REDUCTION.md`.

## 2. Arbitrary deleted sets

For a finite deleted set `A`, put

```text
h(-A,t)=1-product_(j notin A)(1-p(t,j)).
```

For every nondeleted `j`, event inclusion and the finite union bound give

```text
p(t,j)<=h(-A,t)<=sum_(k notin A)p(t,k).
```

Therefore the nonnegative series `sum_t h(-A,t)` diverges exactly when at
least one nondeleted marginal series diverges.  The scalar all-suffix product
criterion then proves

```text
forall m, J(-A,m,N)->0  iff  P\A is nonempty.
```

This includes `A=univ`, where both sides correctly fail, and isolated
probability-one rows, which cannot kill suffixes starting later.  The
one-player-deleted specialization gives `|P|>=2`; `A=empty` gives joint
survival.

This generalization is exact but does not answer a current certificate field.
Adding it to the public packet would expand the API without reducing the live
producer obligation, which is specifically two one-label streams or all
one-player-deleted charges.  It is reasonable internal library mathematics if
a future multi-deletion consumer appears.

## 3. Four-player regression

For `a_t=1/(t+2)`,

```text
product_(t=m)^(m+N-1)(1-a_t)=(m+1)/(m+N+1).
```

The displayed joint and deleted products follow immediately: deleting one of
the two active labels leaves `R`, deleting an inactive label leaves `R^2`, and
deleting both active labels leaves one.  All one-player-deleted clocks and the
joint clock vanish on every suffix, while the pair-deleted clock does not.

For any fixed four-player reward table, the literal tail profile executing
`q_(m+s)` after relative time `s` has the exact all-Continue shift and semantic
prefix recursion.  The relevant checked identities are
`quittingRootSequenceProfile_eq_rootThenContinuation`
(`UniformEquilibrium/Quitting/Boundary/Exceptional/InfiniteLTG.lean`) and
`quittingTerminalSemanticPair_rootThenContinuation`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`).  Alternatively
`QuittingChronologicalDebtData.exactOfRoots` and its named zero-defect theorems
in `UniformEquilibrium/Quitting/Debt/Dynamic/ExactChronologicalData.lean`
package the chronology directly.

The regression should specify that the reward table is arbitrary but fixed;
none of its clock calculations depends on rewards.  It supplies no initial-
debt bound or equilibrium condition and therefore adds no actual-data adapter.

## 4. Packet-boundary criterion

Let

```text
delta(k,-i)=1-product_(t=N_k)^(N_(k+1)-1)
                    product_(j!=i)(1-p(t,j)).
```

Then `1-delta(k,-i)` is exactly the product of the deleted Continue factors
over packet `k`.  Applying the scalar all-suffix criterion to the block
sequence proves

```text
forall i,m, J(-i,m,N)->0
  iff
forall i, sum_k delta(k,-i)=infinity.
```

Strictly increasing natural boundaries are automatically unbounded.  A fixed
time start lies in one finite packet; deleting its finite initial fragment
cannot change vanishing of all later block products.  This also handles an
isolated `delta=1`: it kills products crossing that packet but the series is
still summable unless later packets carry divergent total charge, so later
suffixes are not falsely certified.  Packet widths may be unbounded because
each individual packet is finite.

The corollary

```text
sum_k lambda_k=infinity,
delta(k,-i)>=kappa*lambda_k eventually for every i,
kappa>0
```

is correct.  One may discard the finitely many exceptional packets, after
which each deleted packet-charge series diverges.  The checked joint-domination
theorem then supplies joint survival.

This is the only genuinely different interface in the note.  The formalized
two-label theorem consumes marginal hazards, while this criterion consumes a
block-level lower bound for each deleted player.  It can be useful when a
source-matched conditioned packet already supplies those actual block
probabilities.  It does not make such bounds, preserve frozen charges under
reprojection, or reduce the number of playerwise obligations.  Until one
current producer exposes `delta(k,-i)>=kappa lambda_k`, the criterion should
remain internal rather than extending the formalized packet.

## Exact project impact

- No new closure is needed for the scalar opponent-clock equivalence or joint
  domination; both are already checked and integrated in the current two-label
  source file.
- The arbitrary-deletion rule is mathematically clean but outside the present
  consumer.
- The four-player example is a useful test only.
- The packet-boundary equivalence is a valid prospective adapter from actual
  packet charges to the existing survival fields.  Its conjecture-facing value
  begins only when conditioned reprojection produces those charges on the same
  executable chronology.
