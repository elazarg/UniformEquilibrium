# Review of the Fin4 same-source paid/reset cap-port composite

## Verdict

The narrow composite is correct.  It removes the need to align a separately
selected hard principal or marked lasso with the paid source.  It does not
discharge the resulting summable port and does not construct a path in the
prescribed-payoff punishment-floor Nash--Bellman relation.

Most of the claimed content is already checked in two independent modules.
What is missing is at most a short named composite adapter packaging their
outputs together.

## Checked composition

From a `QuittingTerminalExploitabilityWitness reward`, the checked
nonexistence equivalence and positive-minimum characterization supply an
attained global minimum with positive total semantic debt.

For any pairwise distinct `owner baseFirst baseSecond : Fin 4`,
`QuittingTerminalExploitabilityWitness.exists_finFour_pairBasePaidResetDispatch`
then returns one `FinFourPairBasePaidResetTarget` and its fixed-law reset
dispatch.  On the target's one literal stationary profile and terminal law:

- the prescribed owner has zero debt;
- owner/base-first opponent incidence is one;
- the paid debtor lies in the forced pair;
- its debt is at least the witness gap; and
- `FinFourPairBasePaidResetTarget.paid_row` supplies a paid
  first-disagreement row of exactly the witness gap parameter.

Choosing that row and filling the fields of `QuittingPaidCapLiftedSource`
requires no extra strategic premise.  The theorem
`QuittingPaidCapLiftedSource.nonempty_summablePort` then returns the literal
cap-prefixed profile chronology, its exact cap orbit, the charge budget, the
uniform paid-suffix reach floor, the shifted paid rows, and the semantic
all-Continue limit port.

The quantitative identities in the proposed statement are already theorems
or direct finite consequences of:

- `quittingCapLiftedPrefixProfile_debt_succ`;
- `quittingCapLiftedPrefixProfile_debt_eq_suffixReach_mul`;
- `QuittingPaidCapLiftedSource.partialAbsorption_budget`;
- `QuittingPaidCapLiftedSource.reachFloor_le_suffixReach`;
- `QuittingPaidCapLiftedSource.shifted_gain_le`; and
- `QuittingPaidCapLiftedSource.nonempty_summableSemanticPort`.

## Required wording correction

There are two synchronized sequences, not one relation under two names:

1. the literal profiles `sigma_n`, whose complete semantic pairs are actual;
2. the cap annotations `B(sigma_n)`, which form the exact punishment-floor
   Nash--Bellman orbit under roots Nash against those caps.

The prescribed payoffs `U(sigma_n)` do not thereby form an exact path in the
punishment-floor relation.  In particular, the composite does not solve the
cap-to-prescribed surcharge condition.

Likewise, the returned pair inside the fixed-law reset dispatch is not
identified with the stationary target semantic pair or with the cap-port
limit.  The cap lift deliberately bypasses that returned reset pair and starts
from the target's actual profile.

## Significance and classification

Under the narrow meaning "align an actual paid/reset source before constructing
the cap port," the claimed Gap 1 is closed.  Under any meaning that includes a
prescribed-payoff exact edge, a restart, cumulative-charge near-return, or port
discharge, it remains open.

This is not a new export theorem: the mathematical content is already sealed
in `PairBasePaidResetAlignment.lean` and
`PaidCapLiftedSummablePort.lean`, and the latter already has a formalized
packet.  A named Fin4 composite would nevertheless be useful API and frontier
documentation.  It belongs with the formalized cap-port packet after kernel
checking, not in `exports/` as new mathematics.

## Remaining theorem

The resulting open target is accurately described as a paid-port discharge:
consume or restart this same-source summable cap port, or force a strict
well-founded decrease, without treating the literal prescribed-payoff
chronology as an exact floor path.  Proving that target would be substantive;
the composite itself does not.
