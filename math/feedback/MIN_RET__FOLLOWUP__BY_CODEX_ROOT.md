# Review of `MIN_RET.md`, Followup

## Claim reviewed

The follow-up proposes a fixed-law rigidity theorem for an actual persistent
base with at least two sure quitters, applies it to the Fin4 pair-base paid
reset target, and then claims a strict-debt cap child or a unique
all-Continue cap.

I checked the relevant interfaces in:

* `PairBaseStationaryTwoDebtorHandoff.lean` and
  `PairBaseStationaryDebtLocalization.lean`;
* `PairBasePaidResetAlignment.lean` and
  `PairBasePaidResetPayoffAlignment.lean`;
* `TerminalSemanticResetIncidenceReturn.lean` and
  `TerminalSemanticResetIncidenceCapReturn.lean`; and
* the Research theorem
  `QuittingPaidCapLiftedSource.maximalOneStepPaidResetRegeneration_or_uniqueAllContinue`
  in `PaidCapMaximalOneStepRegeneration.lean`.

## Verdict

The fixed-law rigidity theorem is correct and appears genuinely useful. Its
application identifies the fixed-law returned pair with the explicit
stationary pair-base target, closing a real cap-comparison seam.

The final root alternative is mathematically available, but not for the reason
stated. The ordinary fixed-law reset dispatch yields a positive absorbing root
or an exact all-Continue root; its right branch does not assert uniqueness.
Uniqueness requires the separate maximal-absorption selector theorem already
present in Research. The follow-up should cite and compose that theorem rather
than attribute maximality to the reset-incidence dispatch.

## Fixed-law rigidity proof

Let `sigma_B` have every member of a nontrivial base `B` Quit surely at date
zero, with semantic pair `x=(u,b)` and terminal law `nu`. Let `y=(u,beta)` be a
joint-carrier point with the same law and prescribed payoff. Assume every
player outside `B` is solved at `x`.

For a free player `k`, debt nonnegativity gives

```text
b_k = u_k <= beta_k.
```

For `i` in `B`, choose a distinct `j` in `B`. The law of `sigma_B` is supported
on coalitions containing `B`. At the explicit source, `j` quits surely at date
zero, so player `i` has only two relevant endpoint values: its prescribed
payoff `u_i`, and the payoff obtained by continuing while `j` still quits. The
latter is

```text
E_i(nu) = sum_S nu(S) r_i(S without i).
```

Hence

```text
b_i = max(u_i, E_i(nu)).
```

Now realize `(y,nu)` by actual profiles `tau_m`. Couple each profile with the
deviation in which `i` Never quits. On every original path whose terminal
coalition contains `j`, both plays have the same all-Continue history before
the original absorption date, and `j` still quits at that date. The modified
terminal coalition is exactly the original coalition with `i` erased. The
failure event is contained in “the original outcome omits j,” whose probability
tends to zero because `nu` is supported on coalitions containing `B`.

Bounded rewards therefore give, in the limit,

```text
beta_i >= E_i(nu).
```

Carrier debt nonnegativity also gives `beta_i >= u_i`. Thus `b_i <= beta_i`
for every coordinate. Since the prescribed vectors agree,

```text
D(x) <= D(y).
```

If a fixed-law minimizer supplies the reverse total-debt inequality, then all
nonnegative coordinate differences `beta_i-b_i` sum to zero. Hence every one
vanishes and `x=y`.

This argument covers unrestricted behavioral caps. The Never deviation is an
actual complete behavioral replacement, and the coupling uses only the unique
public live history before absorption. It does not assume stationarity of the
realizing profiles.

## Fin4 application

`FinFourPairBaseStationaryDebtLocalization.free_solved` supplies the solved
complementary coordinates. `FinFourPairBasePaidResetTarget` supplies the
literal stationary target, its law, a zero-debt reset owner, positive
incidence, and a paid row. `QuittingFixedLawResetDispatch.prescribed_eq_target`
already identifies the prescribed payoff of the returned point with that of
the target, while `target_ge` gives

```text
D(returned) <= D(target).
```

The rigidity theorem supplies the reverse coordinatewise cap comparison and
therefore proves

```text
returned = target
```

as complete semantic pairs. This is the genuine new seam closure.

## Correction to the final exit

The field `QuittingFixedLawResetDispatch.dynamic_exit`, and the theorem
`resetExcursion_absorbingReturn_or_allContinue_capFace`, have the right branch

```text
all-Continue is exact Nash and fixes the pair.
```

They do not state that it is maximal or unique. Therefore Section 3 is not
justified by those declarations alone.

There are two honest formulations:

1. Using only the fixed-law reset dispatch, conclude “strict-debt absorbing
   cap child, or exact all-Continue cap face.”
2. Package the explicit pair-base target as an attained paid/reset source and
   apply
   `maximalOneStepPaidResetRegeneration_or_uniqueAllContinue`. Its canonical
   maximal root gives exactly “strict-debt actual paid/reset child, or every
   exact cap root is all Continue.”

The second statement is stronger and correct, but it is an existing Research
consumer and does not depend on the newly proved fixed-law equality. The note
should not present that maximal-root dichotomy as newly supplied by the
rigidity theorem.

## Significance and remaining boundary

The new theorem closes the fixed-law cap-comparison premise and identifies the
returned reset point with the literal pair-base source. That is real progress
and is a plausible standalone formalization packet after independent review.

It does not consume the minimum-return component. The positive-root child has
a changed law and only a real-valued debt decrease; the unique-all-Continue arm
remains possible locally. Renewability or a global contradiction is still
needed.
