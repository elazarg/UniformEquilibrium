# Adversarial review of weighted cap coercivity

Reviewer: CODEX_CAP_ADVERSARY_28.

Reviewed manuscript:
[CODEX_COORDINATOR__WEIGHTED_CAP_ABSORPTION_COERCIVITY](../notes/CODEX_COORDINATOR__WEIGHTED_CAP_ABSORPTION_COERCIVITY.md),
SHA-256 `df6021424eab5f56f653b78471feaee5a99fd61bcdd52942f843097e4e9b39a3`.
The reviewer supplied a separate matrix countercondition analysis, but did
not construct this coercivity proof. This review concerns the exact version
above. No Lean command was run.

## Mathematical verdict

PASS. No unresolved mathematical objection was found. The two stated raw
tests imply the displayed bound for every actual complete-law profile and
its stated semantic closures, including sparse nonnegative weights.

The attempted failure points were:

- Sampling a full root coalition before forcing one player to Quit gives
  exactly the weighted forced-Quit identity. Its own coin is immaterial.
  Negative individual caps are allowed: their weighted negative part is
  bounded by `M*a`, which is sufficient for the absolute-value estimates.
- The next-cap upper bound remains valid when `B_i-P_i` or `b_i` is
  negative. The proof uses absolute values before dividing by `H_i` and
  applies the weighted negative-part estimate afresh to the conditional
  tail. No division by a possibly zero weight occurs.
- The passive-coalition identity in Step 3 is exact. Singleton terms are
  the stated column drifts; the collision error is at most `M*n^2*a^2`.
  The subsequent subtraction of `(1-H_i)b_i` is bounded in the correct
  direction even for negative tail caps.
- The collar argument never conditions on an event of probability zero:
  every iterated root has activity at most one half. Since `D>=n^2>=4`,
  its activity sum is at most one quarter when `w<=delta`. This justifies
  the strict bound for actual absorbing profiles and the weak bound for
  their closure.
- The final cap estimate is uniform over every complete replacement.
  If all opponents choose Never, every native own replacement pays zero.
  Hence escape of finite clock mass cannot create a nonzero cap at a
  carrier point whose ORIGINAL Never product is one.

Exact rational checks reproduced both displayed column-drift vectors and
the signed-participant example's minimum `K_A=1/20`. Both hypothesis-deletion
controls also check: the two-player uniform clocks have cap `1/T` and
payoff `-1/2+3/(2T)`; the three-player sure date-one profile has cap zero
and payoff minus one. Thus neither raw positivity condition was silently
used only as a convenient sufficient estimate.

Static source inspection checked
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`, the named
semantic pair/prefix/debt definitions in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`, and the
independent outcome and intervention definitions in
`UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`.
These establish the intended semantics, not a Lean implementation of the
new quantitative theorem.

## Significance and export gate

The cap-face consumer is valid and useful: the existing boundary reduction
already supplies membership in `K_abs`, and the new raw tests exclude the
specified zero-cap faces there without requiring actual tail realization
or global minimality of the tail. Sparse weights exclude more than the
single all-zero-cap configuration. There is no unproduced strategic input
once the finite reward tests hold.

I recommend retaining this as an internal proved result at present.
Mathematical soundness alone does not establish the export coverage gate:
the tests are not supplied for every counterexample, a full UE class is
not proved, and the manuscript does not yet certify a surviving reward
family outside the relevant accepted existence criteria on which this
conditional boundary exclusion changes the unresolved source alternatives.
This is not an objection to the theorem or its stated application. It is
a limit on claiming a new exported counterexample-class exclusion.
