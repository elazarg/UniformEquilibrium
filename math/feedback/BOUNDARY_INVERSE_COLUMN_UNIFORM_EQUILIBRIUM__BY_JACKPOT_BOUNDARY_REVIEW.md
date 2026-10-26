# Independent review of boundary inverse-column uniform equilibria

Reviewer: CODEX_JACKPOT_BOUNDARY_REVIEW.

Reviewed the complete artifact
`BOUNDARY_INVERSE_COLUMN_UNIFORM_EQUILIBRIUM.md`, SHA256
`bf0f1118db106024b6db237f9ceeeccf0ef14679a38f22c35a7ba57ab7ff2e38`.
This review covers the general finite-player theorem, its scale-thick and
open-singleton-neighborhood extensions, the complete behavioral consumer,
and the exact four-player coverage family. It is ordinary mathematical
review; I ran no Lean compilation and confer no new formalization seal.

**Verdict: PASS. No unresolved mathematical objection in this scope.**

## Main proof checked independently

I derived the divided endpoint field directly from the product probabilities.
The selected containing-coalition reward contributes only to the recipient's
Quit endpoint. Cancellation gives the claimed homogeneous pole and linear
term -Gamma z; no finite-terminal native shift is applied on an improper
profile. Euler's identity and the rank-one inverse formula give the stated
Jacobian and its inverse. In particular its omitted principal inverse block
is exactly minus the corresponding block of Gamma inverse.

Invertibility of that block really does imply invertibility of the active
Jacobian block. It also forces the selected recipient into the positive
support and forces that support to have at least three members. Thus the
four-player boundary has exactly one omitted label and the positive inverse
diagonal condition is the correct scalar sign.

I separately derived the reduced complementarity field and the clamp-cube
argument. Strict semimonotonicity gives a strictly positive compact minimum
eta. A clamp fixed point on the upper boundary would contradict the resulting
quadratic lower bound. Removing that boundary yields the required signs and
complementarity, and the same estimate gives the O(t) omitted scaled hazards.
This proves existence without assuming continuity or uniqueness of the
selected complementary root. The P-matrix sufficient test is proved correctly.

The nonsingleton substitution e=t b leaves a polynomial field. Treating raw
singleton perturbations as additional parameters likewise preserves the local
IFT and the strict cube-boundary estimate. The uniform scale-thick and open
singleton-neighborhood conclusions therefore follow. The proof correctly
restricts its O(t^2) omitted-hazard estimate to bounded residuals at the base
singleton table. I verified the mixed-sign perturbation formula exactly.

## Behavioral and fixed-target audit

At least three positive hazards give every deviator a proper opponent.
Active endpoint equalities and inactive endpoint inequalities imply complete
terminal Nash, including Never and arbitrary private behavioral replacements.
Opponent survival is geometrically bounded independently of the deviator.
The finite-average comparison is consequently uniform over deviations. Each
fixed table has one actual terminal payoff target and one stationary profile
working at every accuracy; no accuracy-dependent target or cross-table target
is substituted. All strategic inputs are produced from raw reward data.

## Explicit falsification attempts and exact checks

I recomputed the positive/negative boundary-control coefficients from coalition
enumeration, obtaining E=(25/24,25/576,0,-25b/48-25/24), the active correction
(25/64,25/64,25/192), and the reduced forcing -25b/48. The fourth-hazard
coefficient is -5b/24 when the interior correction is physical. Thus both
quiet and active omitted-label cases are genuinely needed. Reversing the
fourth singleton column changes the reduced sign and gives the stated local
nonexistence control. That control is correctly not called a UE counterexample.

I checked the exact finite calibration q=(1/10,1/10,1/4,0), a=200/39, b=1,
including its actual target (0,15/13,0,9/157). I also recomputed every principal
determinant and every candidate in the eleven-support LCP census. All entries
match; the only standard-LCP root is the empty support and the R0 degree is1.

## Coverage and source audit

The selected inverse column in the exact four-player family has a zero entry.
Only a different recipient has a strict positive column, and that recipient's
rewards stay bounded along the displayed ray. Thus the previous strict-column
large-reward producer does not supply this ray's threshold. The new theorem
also includes nearby mixed-sign selected columns. This is a new raw producer,
not merely a supplied stationary-root verifier.

The whole sure-owner exclusion is valid against every continuation value.
Both nonsuccessors of a sure owner must Continue, its successor must Quit,
and the owner then strictly prefers Continue. For every proper child, the
single-owner child equilibrium and absent-successor gain are exact; they
exclude the stated full child-debt certificate selection. The directed-cycle
argument excludes every first anchor block and every positive weight vector.
The singleton weighted sums, all pair partitions, crossed-face partner choices,
and signed-cycle sign screens give the claimed failures. The only inverse-
positive child has mixed outside inverse weights, so its raw passive-row
criterion also fails. These are complete tests for the named producers;
the packet correctly does not claim exclusion from all possible UE theorems.

I inspected the named stationary endpoint compiler declarations and the R0
support-index declaration. I also inspected
`PassiveRowInverseCriterion.exists_quiet_smallHazard_terminalNash_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/WeakInversePassiveRowSmallHazard.lean`
to verify the relevant nonnegative outside-weight requirement. The proof's
source-to-target adapter is complete. Its mathematical coverage increment
passes the stated export gate, with the explicit limits retained: no arbitrary
Fin4 closure, no negative central-wedge closure, no actual-minimum resolution,
and no numerical large-reward threshold are claimed.
