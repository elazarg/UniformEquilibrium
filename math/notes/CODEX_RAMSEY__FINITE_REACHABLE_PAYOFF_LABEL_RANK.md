# Finite reachable-payoff-label rank for charged regeneration

Author: `CODEX_RAMSEY`

Status: **internal only; mathematical PASS; generic closing content is already
covered by stronger checked finite-return theorems; no new paid-source
producer**

Independent review:
[`CODEX_EULER`](../feedback/CODEX_RAMSEY__FINITE_REACHABLE_PAYOFF_LABEL_RANK__BY_CODEX_EULER.md)

## 1. Exact question and verdict

This note audits the externally proposed finite reachable-label argument for
[`../questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`](../questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md).
The combinatorial theorem is valid, and it gives a genuine finite-valued
well-founded rank for any *supplied* marked charged-regeneration rule.  It does
not by itself construct that rule from a paid first-disagreement row.

One logical correction is mandatory.  A same-label charged return is an
`eta`-payoff near-return, so failure of the latter excludes the former.  The
converse need not hold: distinct cells of a deterministic partition can have
arbitrarily close points on opposite sides of their common boundary.

## 2. Sources inspected

- `ChargedRelation.Path`, `Path.append`, and `Path.highChargeCount` in
  `MathUE/ChargedPathBudget.lean`;
- `exists_same_label_with_large_clock_gap`,
  `exists_same_label_with_large_charge_gap`, and
  `exists_close_pair_with_large_charge_gap_of_finite_labels` in
  `MathUE/FiniteChargedReturn.lean`;
- `exists_charge_threshold_for_close_pair_of_compact` and
  `exists_close_pair_of_arbitrarily_large_finite_charge` in
  `MathUE/CompactFiniteChargedReturn.lean`;
- `QuittingPunishmentFloorAdmissibleState` and
  `quittingPunishmentFloorAdmissibleChargedRelation` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`;
- `QuittingPositiveAdmissiblePayoffNearReturnFamily` and
  `highChargeCount_pos_iff_decodedPathHasChargeAtLeast` in
  `UniformEquilibrium/Quitting/Projective/PunishmentFloorNearReturn.lean`;
- `quittingBestReplyValue`, `quittingPunishmentValue_le`,
  `neg_quittingRewardBound_le_quittingBestReplyValue`, and
  `quittingBestReplyValue_le` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`;
- `quittingAllContinueSimplexRoot` in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanFactory.lean`; and
- the earlier finite-packing draft
  [`CHATGPT_EXTERNAL__PAID_BLOCK_HAZARD_PACKING_REDUCTION.md`](CHATGPT_EXTERNAL__PAID_BLOCK_HAZARD_PACKING_REDUCTION.md).

No declaration for this exact *reachable-set rank presentation* was found.
However, its generic closing consequence is already covered in stronger
checked form by the two finite-return files above: a finite label sequence
with sufficiently large monotone unit-step clock has a same-label interval
with fixed clock gain, and compactness supplies the deterministic finite
metric labelling.  The argument below is ordinary mathematics and should not
be presented as a new closing theorem.

## 3. Abstract theorem

Let `R` be a charged relation on a state set `X`, let `c > 0`, and let `L` be
a finite label set.  Fix a single-valued map

```text
ell : X -> L.
```

Thus the cells `C_l={x : ell(x)=l}` are pairwise disjoint and cover `X`.
This is a partition, not merely a finite cover.

For `x in X`, define

```text
Lambda(x) = {l in L : there are y and an R-path x -> y with ell(y)=l},
rho(x)    = |Lambda(x)|.
```

The empty path is allowed, so `ell(x) in Lambda(x)` and `rho(x)>=1`.
Call an `R`-path `p:x->y` a same-label `c`-return if

```text
ell(x)=ell(y)  and  highChargeCount_c(p)>0.
```

### Theorem 3.1 (reachable-label descent)

Assume that no same-label `c`-return exists.  Then:

1. every edge `e:x->y` satisfies `Lambda(y) subseteq Lambda(x)`;
2. if `charge(e)>=c`, then
   `ell(x) notin Lambda(y)`, hence `Lambda(y) properSubset Lambda(x)` and
   `rho(y)<rho(x)`;
3. every finite path `p:x->y` satisfies

   ```text
   rho(y) + highChargeCount_c(p) <= rho(x);
   ```

In particular

```text
highChargeCount_c(p) + 1 <= |L|.
```

#### Proof

If `l in Lambda(y)`, append the edge `x->y` to a path witnessing reachability
of `l` from `y`.  This proves (1).

Suppose `charge(e)>=c` and `ell(x) in Lambda(y)`.  A witnessing path from `y`
to a state `z` with `ell(z)=ell(x)`, preceded by `e`, is a same-label path
from `x` to `z` containing the `c`-charged edge `e`, contrary to the
hypothesis.  Since `ell(x) in Lambda(x)`, inclusion is strict.  This proves
(2).

For (3), induct on the path.  The empty path is equality.  After removing the
first edge, use weak cardinal decrease when its charge is below `c`, and use
strict cardinal decrease (at least one for finite sets) when its charge is at
least `c`.  Finally `rho(y)>=1` and `rho(x)<=|L|`.  QED.

The strict step is attached to the **source label of the charged edge**.  It
does not assert that every edge crossing two displayed cells is strict; a
low-charge edge may decrease the rank or preserve it, and a high-charge edge
may connect states carrying the same or different displayed labels.

## 4. Marked-regeneration corollary

Let `Marked subseteq X`.  Suppose that for every marked `x` one can produce a
marked `y` and a finite path

```text
p_x : x -> y,       highChargeCount_c(p_x)>0.
```

Starting from any marked state and choosing successors repeatedly gives
blocks `p_0,p_1,...`.  If no same-label `c`-return existed, Theorem 3.1 would
give

```text
rho(x_(n+1)) < rho(x_n)
```

at every block.  This is impossible for `|L|` consecutive blocks.  Hence the
marked successor closure produces a same-label `c`-return after finitely many
regenerations.

Equivalently in constructive finite form, it is enough to supply `|L|`
composable marked blocks; their concatenation has at least `|L|` high edges,
contradicting `highChargeCount+1<=|L|` under the no-return assumption.  No
infinite-choice principle is needed for this finite conclusion.

This is a legitimate well-founded reduction: under failure of the desired
return, each completed regeneration strictly decreases the explicit natural
rank `rho`.  It is nevertheless conditional on an endpoint-preserving marked
regeneration producer.

## 5. Payoff cells and the one-way near-return implication

Let `P:X->R^I` be the payoff projection and fix `eta>0`.  Since the relevant
quitting payoff vectors lie in the finite-dimensional compact cube
`[-M,M]^I`, choose a finite `eta/2`-ball cover and assign every point to the
first covering ball in a fixed ordering.  Pulling this assignment back by
`P` gives a deterministic finite label map `ell`.  Every resulting cell has
`l-infinity` diameter at most `eta`; empty labels may be discarded.

Therefore a same-label `c`-return `p:x->y` satisfies

```text
forall i, |P(y)_i-P(x)_i| <= eta,
highChargeCount_c(p)>0,
```

which is exactly one instance of the maintained payoff-near-return output.
The checked equivalence
`highChargeCount_pos_iff_decodedPathHasChargeAtLeast` confirms that this is a
literal charged Bellman stage, not an aggregate behavioral hazard.

The correct logical implications are

```text
same-cell c-return  ->  eta-near-return,
not eta-near-return ->  no same-cell c-return.
```

There is no reverse implication in general.  Adjacent deterministic cells
can contain distinct-labelled payoff vectors at distance much smaller than
`eta`.

## 6. Exact behavioral-cap state embedding

For a behavior profile `sigma`, write

```text
B_sigma(i) = quittingBestReplyValue reward sigma i.
```

The point

```text
A(sigma) = ((B_sigma, quittingAllContinueSimplexRoot), box proofs)
```

is a `QuittingPunishmentFloorAdmissibleState reward`:

- `quittingPunishmentValue_le reward i sigma` gives
  `P_i<=B_sigma(i)`;
- `neg_quittingRewardBound_le_quittingBestReplyValue` gives the lower box
  bound;
- `quittingBestReplyValue_le`, applied to
  `abs_quittingTerminalPayoff_le`, gives the upper box bound; and
- the all-Continue simplex coordinate is harmless stored data.

This check is exact even for unrestricted history-dependent behavioral
deviations, because `B_sigma` is defined using their full supremum.

However, `A(sigma)` is only a valid state embedding.  It does **not** prove:

- that the actual prescribed payoff `U(sigma)` equals `B_sigma`;
- that the profile's first row is an exact Nash root at tail `B_sigma`;
- that a paid row gives a `c`-charged outgoing admissible path from
  `A(sigma)`;
- that the endpoint of such a path is `A(tau)` for another paid profile; or
- that the paid/atom/debtor labels survive this re-anchoring.

The full floor-admissible relation does give abstract exact predecessors of
boxed tails by the compact Nash--Bellman factory, but their charges may be
zero and their endpoints need not lie in the marked paid class.  Consequently
the behavioral-cap embedding is not yet the marked successor closure required
by Section 4.

## 7. Comparison with existing checked bounds

The finite-packing lemma in
`CHATGPT_EXTERNAL__PAID_BLOCK_HAZARD_PACKING_REDUCTION.md` already proves that
more payoff-cell labels' worth of high edges on one supplied path force two
close charged positions.  Theorem 3.1 is its local rank form: it allows a
regeneration proof to proceed one block at a time and exposes the exact
well-founded invariant.  Once the blocks are concatenated, it is not a
stronger packing theorem.

More decisively, `MathUE/FiniteChargedReturn.lean` already checks the generic
finite-label theorem for an arbitrary nondecreasing unit-step clock, and
`MathUE/CompactFiniteChargedReturn.lean` already turns it into a close charged
return on a compact metric carrier.  Taking the clock to be the cumulative
high-edge count recovers the relevant closing implication.  The present rank
has a sharper local count (`|L|-1`) for thresholded edges and is convenient
proof organization, but it supplies no new conjecture-facing consumer beyond
those checked results.

`ChargedPathBudget` supplies the real-valued bound
`highChargeCount*c <= chargeSum`; under a terminal exploitability witness the
common prefix budget therefore also bounds the number of high edges.  That
bound does not use payoff cells and does not turn regeneration into payoff
closure.  Conversely, the finite label rank uses no terminal witness or
finite charge budget.  The two potentials are distinct but compatible.

## 8. Conjecture-facing status and next exact target

The theorem changes the desired paid proof architecture to a finite local
obligation:

> For every marked paid-cap anchor reached by the construction, produce a
> marked successor anchor connected by an exact floor-admissible path
> containing one edge of charge at least the same fixed `c`.

If this closure holds, finite rank terminates in the maintained payoff
near-return and the checked all-behavior consumer applies.  If it fails, the
failure state is a finite exit only when an existing solved-game or strict
support/debt descent consumer handles it.  The current paid source results
supply isolated charged rows and stationary handoffs, not this closure.

Thus the graph theorem is a sound internal reformulation, but it is **not a
new paid-branch producer or an export candidate**.  The checked generic
finite-return declarations already perform the closing step once long charged
blocks exist.  The actual unresolved step remains exactly the one not touched
by the cap embedding: construct a charge-preserving, provenance-preserving
exact successor from paid data and regenerate it at the reached endpoint (or
dispatch failure to a named solved/decreasing branch).

## 9. Review disposition

Euler's independent review passed:

1. the removal of the source label at a `c`-charged edge and the quantitative
   high-edge-count inequality;
2. the marked-block concatenation/termination statement;
3. the deterministic partition versus cover distinction and the one-way
   near-return logic; and
4. the behavioral-cap/all-Continue state embedding, especially the stated
   absence of any exact charged successor or paid-label provenance.

A subsequent source audit found the stronger checked generic results named in
Section 7.  That is not a mathematical objection to Theorem 3.1; it removes
the novelty/export case.  This note therefore remains a closed internal record
and no packet is requested.
