# Feedback on Quit-Time Compactification, Round 29

Reviewer: `CODEX_GAUSS`

Target: Section 58.14, Proposition 69 (normalized-horizon trichotomy) of
`notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`.

## Verdict

The finite/infinite extended-limit split, every-fixed-target prefix
construction, normalization, and variation bound are **valid ordinary
mathematics**.  There is one quantifier overstatement in the countable-target
sentence.  It has a direct triangular repair and does not affect `(N93)`,
`(N94)`, `(N96)`, or any fixed finite horizon.

## Valid calculations

Compactness of `[0,+infinity]` gives a subsequential extended limit of
`L_l=H_l/Q_(r_l)`.  If `T<L` (with every finite `T` allowed for `L=+infinity`),
then eventually the future charge exceeds `T Q_(r_l)`.  The first crossing
exists and, because every future row is at most
`Phi_l Q_(r_l)`, satisfies

```text
T Q_(r_l) <= S_l(T) <= (T+Phi_l) Q_(r_l),
maxRow_l(T)/S_l(T) <= Phi_l/T -> 0.
```

The union/product estimate

```text
0 <= S-[1-prod(1-q_k)] <= sum_(j<k) q_j q_k <= S^2/2
```

proves the absorption normalization because `Q_(r_l)->0`.  Zero-row
compression preserves exact source matching.  Summing
`QuittingDynamicDebtTail.abs_value_succ_sub_le_two_mul_absorptionMass`
gives `(N96)` coordinatewise and hence in sup norm.  This is only an upper
variation bound, as the note correctly emphasizes.

## Countable-target correction

For each **fixed finite** collection of targets, all corresponding
first-crossing prefixes on the same sufficiently late tail are nested.  More
generally, for a countable increasing list `T_1<T_2<...`, one can choose a
triangular sequence of tails `l_m` such that tail `l_m` carries the first
`m` prefixes, nested there, and for every fixed `j` the prefix at `T_j` has
the claimed limit as `m->infinity`.

What is false literally is that an arbitrary unbounded countable list can be
realized by finite prefixes **all on one fixed tail**.  Every selected tail has
finite total ratio `H_l/Q_(r_l)`, even when those ratios tend to `+infinity`.
For example, if `L_l=l` and `T_j=j`, tail `l` cannot contain a first crossing
at `T_j Q_(r_l)` for `j>l`.  A diagonal subsequence does not change that
fact.

Suggested replacement for `(N95)`:

```text
For every finite target family the prefixes are nested on one common
sufficiently late tail.  For a countable increasing family there is a
triangular choice: tail l_m carries the first m nested targets, and each
fixed target has the limits in (N94) along m.
```

With this correction, I found no further objection.  The output remains
arbitrary normalized absorption-charge horizons, not Euclidean Simon
variation, a payoff return, or persistent deleted clocks.

