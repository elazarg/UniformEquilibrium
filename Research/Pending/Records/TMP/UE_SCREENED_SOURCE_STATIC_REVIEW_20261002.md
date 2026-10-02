Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Independent screened-source algebra and quantifier review

Verdict: PASS for the ten frozen algebra patches, with both explicit repair
patches applied after their baselines. No mathematical or source-quantifier
defect was found. This is a static review, not a Lean/build/axiom/integration
seal and emphatically not a finding that the three source packets are complete.

## Scope and evidence

Read all three source exports completely (1109, 499, and 471 lines), the entire
534-line `DEPENDENCY_AND_THEOREM_SPECS.txt`, and all ten frozen patches. Checked
their hashes against the dependency audit. Read the relevant current canonical
owners and searched production/Research for overlapping interfaces.

No Lean, Lake, Git, compiler, shared edit, cache creation, worktree, snapshot,
or child agent was used. The only write is this new report under `/tmp`.
All existing-declaration observations below are static: not checked here.

Sources:

- `math/exports/GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR.md`
- `math/exports/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md`
- `math/exports/THREE_SURE_MINIMA_REQUIRE_OPPOSED_MEMBERSHIP_REVERSALS.md`

The dependency audit's proposed D/P/S/C/G/A/R/H identifiers are retained below
for an exact remaining-work map. They are specifications, not existing theorem
declarations or proof seals.

## Frozen algebra coverage

### Direct coordinate chart

`quittingOwnSingletonReward` inserts four independently supplied own-singleton
values and leaves every other recipient/terminal coordinate unchanged.
Reconstruction and joint/fiber continuity concern the same literal table.
Never is unchanged at zero. The existing Fin4 coordinate chart is refactored
to delegate to this generic owner, preserving its canonical singleton vector.
`fin4OriginalReward` remains a recipient-row translation and must not be used
as the new direct fiber. Cardinality 56 remains the existing
`card_fin4FreeRewardCoordinate` in
`UniformEquilibrium/Quitting/Cycles/PairedCycleFin4Chart.lean`.

This covers most of D1. The direct chart's sup-distance, unit-cube, and
strict-interior adapters and compact eta extrema are not in these drafts.
Because this patch changes an existing chart, its old consumers need the root
agent's compiler/integration checks; the downstream unfolding edit is included.

### Complete debts and literal coefficient rows

`quittingTerminalDeviationDebt_oneDateThenNever_eq_rootNashDefect_of_sureOpponent`
delegates full behavioral screening to
`oneDateProductQuittingContinuationBestResponseValue_oneDateThenNever_sureQuitter`
(`UniformEquilibrium/Diagnostics/Quitting/OneDateProductRootCaps.lean`). The tail
is actual root-then-Never, with no padding or excluded late response. A distinct
sure opponent remains after the observed player's replacement.

The optional debt identity is max((1-q) Delta, -q Delta), with Delta the actual
Quit-minus-Continue gap. At a sure owner the debt is max(0,-Delta). Equal
strictly positive debts force the sure owners' untruncated branch values to
equal that debt. `exists_screenedRootDebtBranches_eq_of_positive_equal_debts`
constructs optional labels internally using the maximum's alternatives; it
does not assume best-action signs, a supplied cap, a selected coefficient
matrix, or interior optional probabilities.

The generic expectation theorem interpolates two independent Boolean
marginals at four corners. The actual adapter evaluates literal nonempty
terminal coalitions at those corners and their unilateral updates. Every
corner retains a different original sure player, so neither terminal entry
can be the recipient's own singleton. Full payoff, endpoint gap, full debt,
corner gain, coefficient row, and branch-vector invariance therefore hold
under every own-singleton reselection.

`screenedRootDebtBranches_eq_coefficientRow` returns the exact coefficient
order (1,x,y,xy) and the source corner formula
(f00, f10-f00, f01-f00, f11-f10-f01+f00). This is P1 with its actual source
adapter, not a theorem about arbitrary supplied bilinear rows.

### Six pairs and four labels, including all boundaries

The six orderings are exactly:

| Sure pair | Optional pair | Full order |
| --- | --- | --- |
| 01 | 23 | 0,1,2,3 |
| 02 | 13 | 0,2,1,3 |
| 03 | 12 | 0,3,1,2 |
| 12 | 03 | 1,2,0,3 |
| 13 | 02 | 1,3,0,2 |
| 23 | 01 | 2,3,0,1 |

`ScreenedRootFactorIndex = Fin 6 × (Fin 2 → Bool)` includes QQ, QC, CQ, CC
for each pair, and its cardinality theorem is 24. True means Q and false C.
`isScreenedQuittingRoot_iff_exists_pair` covers any two distinct sure players,
including roots with three or four sure players. Optional probabilities may
equal zero or one throughout; duplicate descriptions of boundary roots cause
no exclusion. Positive debt handles the sure-player zero branch correctly.
There is no strict-complementarity, nonzero optional gap, or open-square premise.

### Cofactors, deficient rank, and actual polynomial evaluation

The signed maximal minors use ordered column deletion and sign (-1)^j.
The kernel and coordinate-cross identities are over a commutative ring and
make no rank assumption. The field lemma selects a nonzero cofactor coordinate
internally only after a nonzero cofactor vector has been supplied. The repaired
scalar-span proof has the required multiplication orientation.

For the game-facing Segre exclusion, nonzero w0*w3-w1*w2 itself implies a
nonzero cofactor vector. The monomial vector has first coordinate one and
Segre quadratic zero. A nonzero scalar multiple of the cofactor vector would
contradict that quadratic. Thus a bilinear kernel point forces the obstruction
to vanish, including deficient-rank matrices. No rank-three or invertible-minor
premise enters the game theorem. This covers P2.

The integer polynomial variables are the literal 56 free coordinates. The
matrix consists of branch1-branch0, branch2-branch0, branch3-branch0 in the same
corner order. Ring-map compatibility identifies polynomial evaluation with the
actual reward matrix, minors, and obstruction. The fixed product contains all
24 factors. Positive equal actual debts select a pair and labels, force that
factor to vanish, and hence force the same product to vanish.

The final facade
`not_positive_equal_screened_debts_of_actual_reward_polynomial_ne_zero`
reconstructs the original reward table from its own coordinate restriction.
It does not change the game. The nonvanishing premise is appropriate for this
genericity consumer, but is not a completed counterexample-to-generic-fiber
producer. This covers the construction part of P3 and P5.

### Every factor's actual rational witness and exact degree

For each of the 24 indices the witness is a complete rational table on all
15 nonempty coalitions and four recipients. No coefficient array is accepted
as substitute input. The first core row pays +/-1/8, the second pays
+/-(1/4 + 1/8 when both optional players belong), and each optional recipient
pays +/-1/8 according to membership and its selected label when the core pair
belongs. Unused entries are zero. These recipient blocks cannot conflict.
Each own singleton is zero and every one of the 60 entries is bounded by 3/8.
The same free-coordinate witness can subsequently be paired with any singleton
vector by the independently proved fiber invariance.

The actual branch functions are 1/4, 1/2+xy/4, Lc(x)/4, Ld(y)/4, where
LQ(t)=1-t and LC(t)=t. To independently check all four labels, multiply the
three equality rows by four. With xi = 1 for C and 0 for Q, and similarly
upsilon, the rows are

```text
[ 1,      0,      0, 1 ]
[ -xi,    ec,     0, 0 ]
[ -upsilon,0,     ed,0 ]
```

where ec,ed are -1 for Q and +1 for C. Their signed-minor vector is
ec*ed*(1,xi,upsilon,-1). Each actual minor is divided by 4^3=64, so the
actual obstruction is -(1+xi*upsilon)/4096. It is -1/2048 for CC and
-1/4096 for QQ, QC, CQ. Player permutation changes no row calculation, so
this check covers every one of the six pairs, with its own literal witness.

The drafts then correctly infer each factor's polynomial nonvanishing from
its own evaluation, and product nonvanishing from the integral domain.
They do NOT infer that one displayed table makes every factor nonzero.
Homogeneity alone is used only for degree upper bounds. The nonvanishing
theorems discharge the extra hypothesis for exact factor degree 6 and product
degree 144. The injective integer-to-real map retains product nonvanishing
and exact degree. This covers P4 and the remaining exact-degree part of P3.

No source weakening or additional favorable-object hypothesis is recommended.
The two explicit repair patches remain required. Compiler elaboration and
warnings still need checking; mathematical PASS does not certify their scripts.

## Current canonical owners and important exclusions

The production full-cap screening, reward robustness/common positive scaling,
MAX carrier minimum/moat/all-player ties, joint semantic-law carrier, and
strict-margin unpadded product-base realization remain the correct dependencies.
The draft branch layer reuses the full-cap theorem and does not duplicate its
unrestricted-response proof. Existing membership stretch, coherent exclusion,
supported saturation, and first three-sure reversal should also be reused.

In particular:

- `minimumTerminalSemantic_exploitabilitySingletonMargin`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`)
  is the MAX objective moat. `minimumTerminalSemantic_maximumDebt_allPlayersTie`
  and the actual-attainment bridge in `PositiveMaximumDebtMinimum.lean` supply
  the required ties only at actual/carrier global MAX minima.
- `exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin`
  (`UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`)
  preserves the SAME full pair and law as an UNPADDED root-then-Never. It still
  needs zero Never, zero coordinate singleton masses, at least two players,
  and strict cap-singleton margins. Its padded nonstrict sibling is unsuitable.
- `exists_sureOwner_strictOptionalReversal_of_membershipStretch_positiveMinimum_finFour`
  (`UniformEquilibrium/Diagnostics/Quitting/ThreeSureMembershipReversal.lean`)
  already derives optional interiority and ONE sure-owner reversal, with signs
  at both tables. It does not give two opposed owners. Its existing telescope
  uses infimum ordering, not a supplied full-cube maximizer.
- `exists_offMinimum_collar_on_completeCap_singletonSlab`
  (`UniformEquilibrium/Diagnostics/Quitting/CompleteCapSingletonSlabCollar.lean`)
  and `exists_eventual_offMinimum_collar_of_completeCap_tendsto_singleton`
  (`UniformEquilibrium/Diagnostics/Quitting/CompleteCapSingletonLimitCollar.lean`)
  concern `quittingTerminalSemanticDebtSum` and a cap near a singleton payoff.
  They are NOT the new positive-total-singleton-law collar at MAX minima and
  do not discharge C1–C5.
- `escapeAwareQuantileClock_fin4_normalized_quantitative_bracket`,
  `quantileClockSupport_fin4`, and the finite-clock minimizing-pair theorem
  remain in `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`, importing
  Research transport. The normalized theorem supplies compression internally;
  its support is 8k+1 and full-objective bracket gap 24/k. It is not yet a
  production import. Promote the coherent required slice before consumption.
- Production `FiniteCalendarRawPayoff.lean` and `FiniteCalendarRawPolynomial.lean`
  already give actual independent date/Never coordinates and polynomial
  terminal masses/payoffs. Reuse them; payoff-only closure is insufficient
  for full-cap approximation. `SingletonJointNeverDebt.lean` gives a different
  joint-Never-times-positive-singleton debt bound, not C1's required
  zero-singleton limiting-law implication.

No current production owner of the full softmax/common-calendar selector,
new MAX singleton-mass collar, or two-opposed-reversal consumer was located
in the scoped searches. This is discovery evidence, not a global absence proof.

## Remaining source construction dependency map

The precise remaining known-source obligations are as follows. None is supplied
by proving the 24 polynomial factors, and none may be replaced by a certificate
field that assumes the sought output.

1. D1 metric/box glue; D2–D3 compact extrema. Derive direct reward bounds and
   distance identities, continuous eta and attained full-cube/fiber maxima,
   attained screened score on six CLOSED squares, singleton independence,
   and the eleven-coalition Gamma. Obtain 0 <= eta <= 1 via actual all Never.
   Keep the whole-cube Omega distinct from each Omega_b.

2. S1–S3 ancestry-preserving membership source. Adapt canonical pure-set full
   caps to the max-over-players symmetric-difference formula for all eleven
   nonsingleton coalitions. Prove the common stretch identities for eS and
   Gamma without fixing a maximizing owner. Starting from arbitrary real
   no-UE, choose a unit-cube maximizer r*, retain any 0<alpha<Omega/8, its
   literal stretch and agreement, then maximize the four singletons. Output
   Omega/2<eta(final)=Omega_b<=Omega, alpha<eta(final)/4, and Gamma>=Omega_b+gamma
   for EVERY singleton vector. The literal stretch displacement bound must
   not be asserted after arbitrary singleton remaximization. This supplies
   packet 2 and packet 3 ancestry; no generic perturbation can replace it.

3. P6–P8 generic source. Combine actual screened attainability and MAX ties
   with P5 to prove theta>Omega_b when Omega_b>0. Prove/reuse open dense
   polynomial nonvanishing and rational intersection of every suitable open
   box; exact degree alone does not supply this topological theorem. Scale
   an arbitrary real positive-eta table strictly inside the cube, perturb its
   56 coordinates to rational nonvanishing b while retaining positive eta,
   maximize s, and choose rational positive gamma below theta-Omega_b.
   Quantify over EVERY singleton vector and EVERY screened root. The selected
   maximizing s need not be rational. This may discard stretch ancestry.

4. C1–C5 new MAX singleton-law collar. On ONE joint approximating sequence,
   prove singleton_i >= (1-a_i)*product(other Never atoms) >= p*(1-a_i).
   Zero limiting singleton masses and positive Never force all Never atoms
   to one, hence prescribed payoff zero; the MAX moat then makes all singletons
   nonpositive, contradicting positive minimum by actual all Never. Thus Never
   is zero. Derive coordinate singleton zeros from total zero, strict margins
   from the MAX moat, and invoke the existing SAME-pair/SAME-law unpadded
   product-base theorem; P5 and ties contradict it. Compactness gives the
   fixed-table collar. For uniformity across eta>=a>0 in one fiber, prove the
   varying-reward closed joint-carrier graph by transporting SAME approximating
   profiles/laws and reward robustness. Separate fixed-table compactness is
   insufficient. Retain nonempty positive-threshold fiber portions.

5. Promote the complete finite-clock Research slice and implement G1–G4.
   Needed generic work is finite log-sum-exp/entropy and derivative identities,
   compact smooth-envelope directional derivatives over ALL inner minimizers,
   finite gradient-convex-hull/outward-normal separation for tuples, chord
   curvature and same-weight all-competitor derivative estimates, and finite
   weighted discarding/selection. No supplied favorable minimizer or selected
   profile normal replaces the envelope/separation proof.

6. A1–A10 common-calendar actual source. Use actual independent polynomial
   gains with coefficient vectors equal to response law minus source law in
   ONE recipient row; optimize only the four singleton coordinates. Retain
   zero tester, all finite responses in the common pool, and distinct Never.
   Show that the pool controls unrestricted full caps, not clock-capped caps.
   Use reward-uniform complete approximation for EVERY calendar minimizer at
   the SAME outer maximizing table. Telescope fN-f(N+1) at that same table.
   Obtain tuple-averaged singleton normal signs from the MAX moat, not normality
   of a chosen profile and not a 60-coordinate norm identity.

7. The remaining A6–A10 steps must keep their quantitative joins: shift only
   finite dates and recompute softmax weights; prove partition ratio 1-ell+a
   and pressure transport; discard the last two calendars; preserve the entire
   tester family on X_(N+3); derive the SAME-weight all-competitor residual and
   solo-Quit0 inequality giving EVERY owner mass >=Omega_b/4 eventually.
   Select one actual tuple/calendar entry after controlling discarded mass.
   Transport those SAME laws and weights to fixed r_infty with reward errors
   2delta for E, 4delta for inactivity, 16delta for weighted derivative.

8. A11 attaches C5 BEFORE tuple/calendar selection for packet 1. Its selected
   sources retain total singleton mass >=kappa and a fixed-owner subsequence
   with mass >=kappa/4. Packet 2 instead retains Gamma's pure-coalition gap;
   it has no unproduced singleton collar. In both final APIs fixed b, gamma,
   Omega_b, r_infty (and kappa for packet 1) precede all epsilon/depth requests.
   One actual independent silent profile and ONE tester PMF must simultaneously
   satisfy full-regret approximation, inactivity, all-owner mass, ONE summed
   pressure upper bound, and the derivative bound for EVERY competitor in
   X_(N+3). Never remains distinct; no tuple mixture is played as a strategy.

9. R1–R2 opposed-reversal consumer. The missing generic affine comparison
   retains 0<m<1/2, 0<alpha<m/4, 0<p<1, actual signed endpoints and optional
   zero-positive row. For v>m the chosen p' gives all old debts strictly below
   m. For v<m or v=m it only gives <=m with one strict-slack row. The actual
   adapter must FIRST establish old global attainment by
   eta(old)<=E_old<=m<=eta(old), THEN apply old all-player ties. Reuse the
   existing coherent exclusion and one-reversal/interiority producer. Return
   TWO DISTINCT sure owners with opposite strict signs at both tables.
   S3 supplies ancestry and the parameter relation. No three-sure minimum
   existence follows, and this consumer does not eliminate opposed reversals.

10. H1–H3 and source regressions remain separate useful claims: simultaneous
    hazards t/L_i at a MAX minimum, actual Continue-cap first derivative,
    harmonic sum m/L_i<=1, strict margins/positive denominators, strict Fin4
    bound eta<1/3, and attained uniform cube bound. Reuse prefix/carrier and
    small-hazard owners, not Research sum-debt reservoir results. Also formalize
    the stated tied screened boundary fixtures, AdaptiveChildCenter's exact
    screened minimum/robust solved neighborhood, and the opposed-affine-row
    sharpness fixture as needed. None of these examples is a counterexample.

The largest remaining common source unit is compact envelope/separation plus
the common-calendar construction. It is supplied known mathematics awaiting
formalization, not authority to undertake unrelated frontier research.

## Nonclaims

The algebra chain implements the content of packet 1's explicit polynomial
construction/nonvanishing and tied-positive-screened-debt exclusion, Theorem
A(1)–(2), not its strict fiber gap A(3), selection B, collar C, harmonic bound,
or common-calendar source. These theorem item numbers are distinct from the
dependency audit's A1–A11 calendar adapters.

It does not complete packets 2 or 3. Generic Pi nonvanishing or theta>0 does
not imply eta>0; individual factor witnesses are solved algebra fixtures.
No equilibrium, counterexample, renewed descent, fixed stopping date,
cap-attaining response, or post-response cap control follows. No selected
source has four separate pressure inequalities or a full reward normal.

## Frozen hashes

All source and patch hashes match the dependency audit at the time of review.

```text
GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR.md
c3004d986acc316a20b7c29a7cdc9c764235f843e4b006a7fc99e0cbe0e0f5d7
MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md
24537ca80ba0c3ac610c73259ca44977acda1d985527fedba524de98589ac2b6
THREE_SURE_MINIMA_REQUIRE_OPPOSED_MEMBERSHIP_REVERSALS.md
83ee0a42c89aa0f37a29b74bee059fc6dca8cbda309f9e6806f84bf410bb8297
/tmp/three-source-packets-dependency-audit.xEpZYgxQ/DEPENDENCY_AND_THEOREM_SPECS.txt
0f4412a92546f7036c1d850e96141275526cf18e9aa000bc48c1c079d8509a59
/tmp/own-singleton-reward-chart.fIa1qX/OWN_SINGLETON_REWARD_CHART.patch
6cf88b0275721e0e933301951eab49a015316f75a3717df01e6e0f2a25c4ee06
/tmp/screened-root-source.xNVVKd/SCREENED_ROOT_DEBT_BRANCHES.patch
46d69174893acfbcea517076790e9408007249e030f0dbe2ad0db131ba937e2a
/tmp/own-singleton-reward-chart.fIa1qX/SCREENED_ROOT_BRANCH_LABELS.patch
ebaa9d7113b14e79bc3c12491f580a18c734ef76b9a68d8df21a1d28da25a7c2
/tmp/screened-root-four-corners.cIBcxx/SCREENED_ROOT_FOUR_CORNERS.patch
47813f600a0ff663cf7b9ddbb16f958d55cc589a60f7844ac351a2f50a2a5a5a
/tmp/screened-root-four-corners.cIBcxx/SCREENED_ROOT_FOUR_CORNERS_REPAIR.patch
bfdc3b0bc8706f0b3e3e56fcc7f3487af43a4d3e546b7ec8d6fa5c71abc3a22c
/tmp/rectangular-cofactor-kernel.akNW24/RECTANGULAR_COFACTOR_SEGRE.patch
b07ca5fb697d2c34992ad6d96c593fa1f3447c7cfcd16a5099ac41231bcf0c29
/tmp/rectangular-cofactor-kernel.akNW24/RECTANGULAR_COFACTOR_SEGRE_REPAIR.patch
fdecf5890b7892f339d0fb71f1285942b1fe7d98ec6e4c42cb1a543eb607904e
/tmp/screened-root-polynomial.qdx5Fg/SCREENED_ROOT_POLYNOMIAL.patch
e3ddc227b55d3f48518ed5d60af28620026e95710bf31687e069dda4252e2440
/tmp/screened-polynomial-witness.4kdar9/SCREENED_POLYNOMIAL_DEGREES.patch
9572c041d806a5fbfa8c293f85ca7c5b188492e141eb229a0c3fb91df753af3b
/tmp/screened-polynomial-witness.4kdar9/SCREENED_POLYNOMIAL_WITNESSES.patch
dab5f8e14dc55cd8ef8d005a7d25948767b0060e773aac6542ecbc02b85acbdb
```
