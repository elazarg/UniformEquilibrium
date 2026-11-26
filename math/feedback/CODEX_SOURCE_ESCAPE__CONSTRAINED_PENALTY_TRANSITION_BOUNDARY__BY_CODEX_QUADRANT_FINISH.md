# Focused review of reward transport and the singleton boundary

Reviewer: CODEX_QUADRANT_FINISH.

Reviewed source:
[CODEX_SOURCE_ESCAPE__CONSTRAINED_PENALTY_TRANSITION_BOUNDARY](../notes/CODEX_SOURCE_ESCAPE__CONSTRAINED_PENALTY_TRANSITION_BOUNDARY.md),
SHA-256
`d969a6a344a8ae08af51e4bbe78e7f555e54ce4eb95b708eec53aaf2fc42fd6d`.

Status: ordinary-mathematical PASS for Sections 4, 5 and 7, subject to
the authorship exception for (8b) below. This includes the vanishing-weight
estimate (8a), the explicit negative-offset limit (8c), and the source's
explicit carrier-coordinate identification in (10). No export or new
Lean result is claimed.

## Review scope and authorship

Section 6's universal-monotonicity equivalence was contributed by this
reviewer. It is therefore excluded from this independent review. The
author's independent check of that section is a separate record.

The row-affine formulas and constrained scaling identities in Section 4
were independently derived by both participants before comparison.
Section 5's maximality lemma and Section 7's singleton-only boundary
were proposed by CODEX_SOURCE_ESCAPE and independently checked here.
The mixed-sign row-offset observation (8b) was also contributed by this
reviewer. It is excluded from this independent review; the source author
independently checked it. The explicit profile in (8c) is independently
reviewed below.

## Section 4: complete caps, offsets and positive weights

For native own zero, finite deterministic Quit-date payoffs converge to
the pure-Never response. Hence their supremum is the complete cap, even
when no finite date attains it. A finite response absorbs surely and
therefore gains the entire constant absorbing-row offset. Never gains
only its opponents' absorption probability times that constant.
These facts prove the exact signed-offset maximum in (5).

The prescribed payoff gains `c_i(1-nu)`. Consequently (6)--(7) hold on
every actual profile, with all complete responses included. In
particular, negative offsets need not preserve individual absorbing debts;
they can increase them. Nonnegative offsets preserve them exactly.

Positive recipient scaling multiplies every prescribed payoff, complete
cap and debt coordinate by that recipient's scale. The same independent
profile class is used before and after transformation. Taking infima
gives (8), and multiplying the singleton matrix on the left by the
positive diagonal gives (9).

The numerical carriers in (10) are explicitly identified by

```text
(U,B,N,e) -> (aU,aB,N,ae).
```

The scaled observer-zero set is the image under this map, and the
displayed argmin identity uses that image as well. This resolves the
coordinate-identification clarification in the earlier reviewed draft.

After that identification, observer debts vanish at exactly the same
points, and the pivot objective is exactly
`a_h[d_h+(r/a_h)nu]`. Thus the minimum, minimizers and axis envelope
transform as stated. The other observer weights have no effect on this
constrained optimization.

## Section 5: universal coordinatewise additive transport

Fix a nonempty opponent coalition T, all quitting surely at date 1.
The owner's complete response menu has exactly the three payoff classes
`0,a,b`; every mixture of dates or Never is an average of these values.
The fixed correction adds `w0,wT,wJ` respectively.

Prescribing date 0 and taking `(a,b)=(K,-K)` or `(-K,K)`, with K
sufficiently large relative to the fixed correction, forces
`wT>=w0` and `wJ>=w0`. Taking `a=b=-K` and prescribing Never or
date 1 forces the reverse inequalities. Each prescribed profile
absorbs because the opponents T quit surely.

Varying T covers every nonempty coalition, so only absorbing row
constants meet the universal coordinatewise inequality. Formula (7)
proves their sufficiency for either sign. The sole-quitter zero-table
control proves that universal equality excludes negative constants.
The affine version follows by dividing the fixed correction by the
positive row scale.

The source correctly distinguishes this result from SUM-only transport,
different-profile constructions, and source-dependent deformations.
Those stronger exclusions are not consequences of this lemma.

## Section 7: rank-one singleton perturbation

Changing only the carrying owner's singleton reward and then restoring
native own zero subtracts lambda from every other nonempty entry of
that row. Both entries in each nonempty joining difference change
equally, so all such contacts are fixed.

With `u=1-e_h`, the singleton matrix changes by
`-lambda e_h u^T`. Since `u^T Gamma^(-1)e_h=k`, the determinant lemma
gives the factor `1-lambda k`. Sherman--Morrison gives the carrying
column `v/(1-lambda k)` before the singular boundary. These formulas
require no assumption about the other inverse columns.

The positive native absorbing-gap premise forces positive determinant:
adding a positive constant to every absorbing row gives positive
unrestricted SUM gap by the exact offset identity and absorbing
properification; the original-game determinant necessity then applies
to the unchanged singleton matrix. Thus singularity and negative
determinant imply zero native absorbing gap.

The inverse-axis construction scales its three quantities v, S and k
by the common factor `1/(1-lambda k)`. Its ceiling therefore becomes
`c_h(1-lambda k)`. The same-law reward increments lie in an interval
of length lambda, so the row's debt changes by at most lambda.
Restoring own-zero normalization preserves absorbing debts because the
own reward is nonnegative on both sides of that normalization.
This proves the stated sharp row-oscillation bound.

Finally `c_h=(v_h/S)/k<1/k`, because every entry of v is positive.
The guaranteed positivity interval cannot reach the determinant
boundary. Positive recipient weights scale the carrying boundary and
its axis ceiling by the same factor, so they do not remove this
separation. All conclusions are conditional on the original source;
the source does not exhibit a positive-gap game.

## Vanishing-weight bound (8a)

The claim

```text
A min_i a_i <= A_abs(aZ) <= 2M min_i a_i
```

is valid. For each owner h, fix its first-date action to Quit surely.
Choose a mixed Nash equilibrium of the finite three-observer game
at that date. Under every observer deviation, h still absorbs
immediately, so the observer's entire behavioral response reduces
to that finite first-date action comparison. All three observer
debts are exactly zero.

The pivot's prescribed payoff and complete response cap both lie in
`[-M,M]`, including later dates and Never after a deviation. Its debt
is therefore at most `2M`. Under positive row scaling only that debt
can remain, and it is at most `2M a_h`. Choose h of minimum weight.
The lower bound is the pointwise weighted-debt inequality (8).
Hence every approach to a zero-weight face loses a uniform positive
absorbing-gap margin, regardless of the other weights.

## Explicit negative-offset limit (8c)

For the proposed profile, an observer's Never payoff is
`e_i=(1-x)Gamma_ih`. Its other finite response classes are the early
payoff zero, the simultaneous payoff `(1-x)Z_i({i,h})`, and the late
payoff e_i. Thus its native cap rent is exactly

```text
B_i-e_i=(1-x)max(0,-Gamma_ih,Z_i({i,h})-Gamma_ih).
```

Its opponents' joint Never probability is x. Since
`(1-x)kappa=Kx`, the offset formula (5), with offset -K, shows that
its shifted Never response attains the entire cap. All three observer
debts vanish, including against mixed finite dates and Never.

All of the pivot's opponents Never, so its own native cap and prescribed
payoff are zero. Its positive offset a gives debt exactly ax. These
are actual independent stopping laws, so their total debt proves the
displayed upper bound on the unrestricted infimum.

If kappa were zero, the same three-class comparison at x=0 would give
an exact native absorbing Nash profile, contrary to A>0. Hence kappa
is positive under the source assumption, and the upper bound tends
to zero as K tends to infinity. Strict positivity at every finite K
is the independently author-reviewed implication (8b), rather than
an inference from the positive debt of this particular profile.
The construction therefore exhibits loss of a uniform gap in the
unbounded offset limit without changing the native reward table.

## Sources and checks

Static source inspection included:

- `quittingTerminalPayoff_update_finiteTime_tendsto_of_profile`
  (`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`);
- the reward continuity and scale identities in
  `UniformEquilibrium/Quitting/Terminal/TerminalDebtSumRewardGeometry.lean`;
- `ownShiftReward` and
  `quittingRootEndpointDifference_ownShiftReward`
  (`UniformEquilibrium/Quitting/Root/EndpointBackwardStability.lean`);
- Sections BA2--BA5 of
  [the global-obstruction note](../notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md);
- the finite-deadline and properification arguments in
  fresh small-own properification, now archived at Git path
  `b8d49627:math/exports/FRESH_SMALL_OWN_FINITE_HAZARD_SOURCE_PROPERIFICATION.md`;
- the complete necessity theorem in
  the positive-determinant reduction, now archived at Git path
  `b8d49627:math/exports/FIN4_POSITIVE_DETERMINANT_AND_INVERSE_COLUMN_REDUCTION.md`;
- the inverse-axis construction in
  [the constrained repair note](../notes/CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_REPAIR_AND_CONE_GRAFT_OBSTRUCTION.md).

Curation reference: the finite-response raise and properification facts are
available in [the retained strict inverse-column packet](../exports/FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md),
Part II Section 2; its Part IV contains the complete singleton necessity
theorem. The inspection list above records the original sources read, not
a new review of that packet or its stronger conclusions.

No Lean or Lake command was run. The documentation checker passed.
The review does not turn these internal deformation limits into a
new counterexample exclusion.
