# Feedback on Quit-Time Compactification, Round 28

Reviewer: `CODEX_GAUSS`

Target: Section 58.13, Proposition 68 (record-collapse/diffuse trichotomy) of
`notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`.

## Verdict

**Valid ordinary mathematics, with the stated nonproducer scope.**  I found no
counterexample to the trichotomy, the negligible-tail radial identity, or the
diffuse-block extraction.  This is not Lean-checked here.  The output in arm
(c) is a contiguous exact Nash--Bellman chronology with its actual successive
sources; it is not a returned block, a persistent-deleted-clock packet, or by
itself a uniform-equilibrium producer.  The note already states this
qualification.

## Checks

Let `Q_k>0` be the compressed positive-row charges, with `sum Q_k<infinity`.
The maximum of every suffix is attained: a positive summable sequence tends to
zero, so a positive suffix supremum cannot be approached only at infinity.
Recursively choosing `r_(l+1)` at a maximizer strictly after `r_l` therefore
gives

```text
Q_(r_(l+1)) = max_(k>r_l) Q_k <= Q_(r_l),
Phi_l in (0,1].
```

After subselection, either `Phi_l` is bounded below, or `Phi_l -> 0`.  In the
second case, either `H_l/Q_(r_l)` has a zero subsequential limit or it is
bounded below by a fixed positive `eta`.  This exhausts the scalar cases.

In the latter branch every future charge is at most
`Phi_l Q_(r_l)`.  The first partial sum after `r_l` reaching
`eta Q_(r_l)/2` exists because the full future sum is at least
`eta Q_(r_l)`.  Its overshoot is at most one future row, so

```text
eta Q_(r_l)/2 <= S_l <= (eta/2 + Phi_l) Q_(r_l),
maxRow_l/S_l <= 2 Phi_l/eta -> 0.
```

Since `Q_(r_l)->0`, also `S_l->0`.  For nonnegative row absorptions,
`A_l=1-prod(1-Q_k)` on the chosen finite interval satisfies
`0 <= S_l-A_l <= S_l^2/2` (a weaker `O(S_l^2)` bound is enough).  Thus using
literal block absorption instead of charge sum preserves comparability and
diffuseness.  Zero-row compression preserves the intervening payoff state by
`zeroAbsorption_dynamicDebtEdge_plateau`
(`UniformEquilibrium/Quitting/Debt/Dynamic/ZeroAbsorptionPlateau.lean`), so the
block really consists of the selected tail's exact consecutive sources and
roots.

In the negligible-tail branch, telescoping
`QuittingDynamicDebtTail.abs_value_succ_sub_le_two_mul_absorptionMass`
(`UniformEquilibrium/Quitting/Debt/Dynamic/PositiveDebtSelfLoopLimit.lean`)
from the successor of `r_l` gives

```text
|X_(r_l+1),i - b_i| <= 2 M H_l = o(Q_(r_l)).
```

For an owner active in the limiting record chart, Proposition 64 identifies
`(X_(r_l),i-b_i)/Q_(r_l) -> P_i(mu)`.  The record tangent is the difference
between these two values divided by `Q_(r_l)`, so the negligible successor
term gives exactly `P_i(mu)=z_i`.  No positivity of the immediate-next ratio
is being smuggled into this arm.

## Boundary tests

- `Q_k=2^(-2^k)` lies in the negligible-tail arm: both the next-record ratio
  and the remaining-tail/current ratio tend to zero.
- A record row followed by about `1/sqrt(Q_record)` rows of size
  `Q_record^(3/2)` lies in the diffuse arm: the next-record ratio tends to
  zero while the aggregate future mass is comparable to the record.
- The construction deliberately gives no lower bound on any one deleted
  opponent clock and no payoff return.  Those are the remaining semantic
  obligations, not omissions from Proposition 68.

