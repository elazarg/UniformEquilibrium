# Formalization coverage for the renewable minimum-source descent packet

Formalizer: external Lean formalization agent
Target: [`CANONICAL_FIN4_RENEWABLE_MINIMUM_SOURCE_SUPPORT_DESCENT.md`](../exports/CANONICAL_FIN4_RENEWABLE_MINIMUM_SOURCE_SUPPORT_DESCENT.md)

Verdict: **Two pieces are checked: the joint semantic/law lift of Section 1
and the exact horizontal debt ledger of Section 6, the latter at arbitrary
player cardinality and under strictly weaker hypotheses than the packet
assumes.  The source-reconstruction machinery, the renewable rank transition
system, the exhaustive dispatch and the three residual exits are unchecked, so
the export is not claimed as accepted.**

## The joint-law lift

`exists_retainedProfile_terminalSemanticLawCluster`
(`Research/Quitting/MinimumFiberDebtTransfer.lean`) is Section 1.  A sequence
of executable profiles whose terminal semantic pairs converge has a strictly
increasing subsequence along which the joint terminal semantic/law points
converge inside `quittingTerminalSemanticLawCarrier`, and the semantic
coordinate of that joint limit is the supplied semantic limit.

The point the packet makes about retention is in the statement, not only in
the proof: the supplied profile sequence appears in the conclusion, composed
with the selected subsequence.  The theorem therefore lifts those realizers
and cannot silently substitute another sequence with the same semantic limit.

## The horizontal debt ledger, at arbitrary cardinality

`QuittingPositiveMinimumDebtTangentFamily.FullReplacementCluster.minimumFiber_debtTransfer`
is Section 6's ledger.  At a full-replacement endpoint cluster whose total
debt equals the base total debt, the active mover's debt is zero at the
cluster and positive at the base (`base_moverDebt_pos`), and the aggregate
debt change over the other players is exactly the mover's base debt
(`nonmover_debtChange_sum_eq_moverDebt`).

`exists_nonmover_debtChange_moverDebt_div_card_le` then selects a nonmover
absorbing at least

```text
d_m(b) / (Fintype.card ι - 1)
```

and proves that share strictly positive.  The packet states only the
four-player form with denominator `3`, arguing from "there are three
nonmovers".  That form is now the corollary
`exists_nonmover_debtChange_moverDebt_div_three_le`, which derives the
denominator from a supplied `Fintype.card ι = 4`.  The general statement rests
on `nonmover_nonempty` and `two_le_card` instead of on the count of Fin4
players.

The consequences the packet draws are checked as stated.
`not_forall_debt_le_base` refutes coordinatewise debt nonincrease across the
seam, and `moverDebt_le_sum_positivePart_nonmover_debtChange` bounds the total
positive part of the change below by the mover's base debt, so the transfer is
not uniformly small either.  Any cross-seam compiler must carry, centre,
cancel, or pay it, exactly as the packet's intrinsic negative boundary says.

## The ledger needs less than the packet assumes

This is the part most useful to the conference.

The packet states the debt-transfer law for "every recursive minimum-fibre
replacement", that is, for dispatch case 4 of a node that has already been
excluded from cases 1--3.  Reaching case 4 means the tangent column is flat
and does not enter a coordinate with zero debt at the base.  Section 6 then
adds "in the flat branch, the checked coordinate theorem further identifies
each change with the corresponding tangent entry".

The checked ledger assumes neither.  Its hypotheses are a
`FullReplacementCluster` for the given frontier and mover, together with
equality of the cluster and base total debts.  There is no flatness
hypothesis, no hypothesis about entry into the inactive debt support, and no
tangent-column hypothesis of any kind; the module records this explicitly.

So the seam charge does not depend on which dispatch branch produced the
replacement, and it is available before the exhaustive dispatch is proved.
The tangent-entry identification remains a genuine extra in the flat branch,
but nothing in the ledger or its consequences needs it.

## One scope limit that must travel with the result

The packet states it and the module repeats it, so it should not be dropped in
any restatement.  Debt is the gap between the best-response envelope and the
prescribed payoff, so a lower bound on debt change bounds no envelope
coordinate on its own.  Nothing here asserts that the raw envelope vectors at
the base and at the cluster are close: the prescribed payoff may move together
with the envelope.

## What remains unchecked

```text
Section 2  initial endpoint source reconstruction
Section 3  recursive source reconstruction
Section 4  the exhaustive four-way node dispatch
Section 5  the well-founded rank and its strict decrease
           the three nonrecursive residual exits
```

A narrow search found no declaration named or implementing
`CanonicalPairEndpointMinimumSourceRegeneration`,
`nonempty_endpointMinimumSourceRegeneration`,
`FinFourMinimumSourceTangentNode`, `FinFourMinimumFiberSourceDescent`,
`nonempty_minimumSourceRenewalDispatch`,
`CanonicalPairRenewableSourceRankState`, `canonicalPairRenewableSourceRank`,
or `CanonicalPairRenewableSourceRankCertificate`.

Nothing in the checked part orients repeated regeneration.  The ledger is a
statement about one seam; it neither produces a child source nor decreases any
rank, and the joint-law lift selects a subsequence without reconstructing a
source from it.  The packet's own claim to prove "renewable source
reconstruction and strict finite support descent" is therefore not covered.

The packet's remaining nonclaims are unaffected: no terminal approximate Nash
profile, no uniform-equilibrium payoff, no positive admissible near-return, no
cap or response compiler across full replacement, and no resolution of the
four-player conjecture follows from the checked part.

## Seals

The two checked pieces have `M` and `L`.  Neither earns `A` or `C` here: no
adapter supplies a `FullReplacementCluster` on the minimum fibre from actual
source data through these declarations, and no downstream declaration consumes
the ledger.  The export packet itself remains at most `M`.
