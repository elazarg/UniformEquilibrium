Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Reflection packet: actual bounded single-pivot normalization staging

## Source and status

Fully read math/exports/REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS.md.
Source SHA256:
a28b23b400cfef2fce48d0dfd33027b344e00d45a015de549c328dce4f397e69.
The relevant obligation is the decision reduction in Conjecture-facing change,
Strategic inputs, and Adapter and semantic consumer, plus handoff item6 and
the signed-normality boundary warning.

The smallest dependency-complete frozen chain remains15→16→17→17A.
Current checked14 is its certificate/minimum prerequisite, not a future draft.
No new proof or additional source hypothesis is needed. All three future files
are currently absent; neither originals nor this staging/harness were compiled
here. Root owns shared application and tests. Full gate1205 remains pending
at this audit; it is not replaced by source inspection.

Full original HANDOFF and independent static review were read and hashed:
 /tmp/ue-bounded-normalization-Y0cMlfQG/HANDOFF.md
 9a3dfc2120d1cfc5797703e293773d0e7a1cdcf0346d07a6c69efaed62a61461;
 /tmp/bounded-normalization-static-review.gN3fEM1P/REVIEW.txt
 93615880edcdb4febd9f3458b2c54805322d2fe3cc9446b79e259d33bee08ca5.
That review gives mathematical/source PASS, not a compiler or consumer seal.
The newly refreshed independent review is owned by Astra, separately.

## Literal claim and canonical owner map

15: GameTheory.quittingGame_scale_eq_affinePayoff
(UniformEquilibrium/Quitting/Transform/PositivePayoffScaling.lean) equates the
ENTIRE quitting game of the common product table with the original stochastic
game's zero-shift affinePayoff. The proof inspects only the canonical structures.
State, action sets, observations/history carriers, transition and discount data
are unchanged. Live payoff stays0; consequently Never still pays0.
The structural equality does not require a positive scale.

15: GameTheory.quittingGame_exists_uniformPayoff_scale_iff requires scale>0
and delegates both directions to
GameTheory.StochasticGame.isUniformEquilibriumPayoff_affinePayoff_iff and
GameTheory.StochasticGame.isUniformEquilibriumPayoff_of_affinePayoff in
UniformEquilibrium/ProofView/Concepts/Stochastic/Transform/Payoff/AffinePayoff.lean.
No finite-average, horizon, delivery, behavior or deviation proof is copied.
The canonical API has target fixed before accuracy, all sufficiently long
expected finite-horizon averages and every unilateral behavioral replacement.
Its positive-horizon rescaling is sufficient for UE, using max(threshold,1).
No horizon-zero or strategy-class restriction is added to the source notion.

Canonical discovery also located scaleQuittingReward,
quittingTerminalPayoff_scaleQuittingReward and
quittingContinuationBestResponseValue_scaleQuittingReward in
UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean.
The table lambda in15 is definitionally that same common product formula.
Those terminal/cap homogeneity declarations are not a whole-game UE transport;
15 does not duplicate them and does not import a larger terminal chain merely
to name an already literal multiplication lambda.

16: GameTheory.exists_finFourBoundedSinglePivotNormalization_of_no_uniformPayoff
(UniformEquilibrium/Diagnostics/Quitting/FinFourBoundedSinglePivotNormalization.lean)
takes ONLY an arbitrary REAL Fin4 table and bare no-UE from none.
It internally invokes
GameTheory.nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff
in UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean.
This checked producer outputs the actual pivot and actual no-UE for the literal
quittingSinglePivotNormalizedReward reward pivot. Its no-UE is a semantic output
proved through the existing actual source/gap consumer, not assumed in a supplied
record and not inferred from terminal-only affine invariance.

Canonical quittingRewardBound and abs_reward_le_quittingRewardBound bound that
SAME normalized finite table. exists_nat_ge gives base, divisor=base+1 gives
N≥1, and scale=1/N is positive. Each of the actual normalized coordinates is
bounded by N. The output table is LITERALLY (1/N)*normalized, with every absolute
coordinate≤1 and own-singleton vector (1/N)e_p. The same table has no-UE by15.
There is no all-singletons-positive conclusion: the three nonpivot own
singletons are exactly0. This says nothing false about the off-diagonal entries
of singleton reward columns. Common scaling does not repair a signed original
own-singleton vector; the actual single-pivot producer is used FIRST.

17: GameTheory.exists_finFourBoundedSinglePivotPolynomialObstruction_of_no_uniformPayoff
(UniformEquilibrium/Diagnostics/Quitting/FinFourBoundedSinglePivotPolynomialObstruction.lean)
retains the SAME original reward, internally selected pivot and natural divisor.
It invokes current
GameTheory.quittingGame_noUniformPayoff_iff_noSureRoot_and_restricted_rationalPotential
in UniformEquilibrium/Quitting/Projective/RestrictedPolynomialForwardCharacterization.lean
AFRESH on the literal scaled table. Own-singleton nonnegativity and the positive
pivot are derived internally. Current14 itself derives normality and calls the
original characterization with bound1 and normalizes its dependent box to
EXACT3. No previous polynomial or old fixed-box certificate is transported.

ONE rational tolerance and ONE rational expression are shared by the all-edge
robust certificate on box3, canceled totalDegree≥3, failure of coordinatewise
degree≤1 and QuittingRationalPolynomialAdaptiveMinimumConditions.
Current14's strengthened predicate literally quantifies EVERY global box
minimum, with ONE positive gap, ONE adaptive lower-boundary minimizing point,
boxed reflection, whole closed[0,2] segment and quantitative directional third
derivative at an internally selected time. Upper-face global minima are allowed.
Unit17 consumes that predicate unchanged: no repair to its public statement is
needed after14's strengthening.

GameTheory.IsQuittingBoundedSinglePivotPolynomialObstruction.no_uniformPayoff
forgets extra restrictions and calls14's unchanged semantic reverse for the
SAME certified table. The final
GameTheory.exists_finFour_no_uniformPayoff_iff_exists_boundedSinglePivotPolynomialObstruction
has existential reward tables on BOTH sides. It is an existence-of-counterexample
decision equivalence, NOT per-table UE equivalence of the original and its
terminal-only normalized table. The per-table equivalence asserted separately
by15 is only for common positive whole-game scaling with zero shift.

No rationality of the source or normalized/scaled reward table is required.
A positive reciprocal integer is a rational-real scalar, but does not make
arbitrary real coordinates rational. Rationality of the newly produced
polynomial/tolerance comes from the characterization. No supplied candidate,
minimum, strategy, favorable counterexample, denominator bound, UE solution,
or all-polynomial exclusion is added.

## Exact application and pinned API context

Use ORDERED_APPLICATION_MANIFEST.json for immutable originals, source hashes,
current prerequisite hashes, contexts and planned umbrella transports.

1. Original15.
2. Original16, reusing current actual single-pivot normalization and RewardBound.
3. Original17, reusing current14's checked closure.
4. Existing17A:
   /tmp/ue-future-pinned-name-overlays-iBO2Hj/001_UNIT17_PINNED_ITE_NAMES.patch
   SHA d3d4dc16cf920cf5100fe00ca9266d885b5f80fb7a42fc054d0c96ff99aefcba.
   Exact SOURCE base b06b995f274c4d395801dc30231a739bf6b3a33f514da3494d36c6838ab140c0
   →result baffd10885b9bc26ad9252755fd03be5995d5feb97a7677f599f878bac72d8f8.
5. NORMALIZATION_GROUP_IMPORTS.patch, then root-owned audit regeneration/gates.

17A replaces ONLY the two if_pos rfl proof sites by ite_eq_left rfl.
Pinned Init/Core.lean explicitly deprecates the old alias. Both contexts match
uniquely and the reconstructed result is exactly that literal substitution.
No public declaration, hypothesis, predicate, branch choice or warning policy
changes. No other definite pinned-name/import/API defect was found in15–17.
The inspected exists_nat_ge and one_div_mul_cancel APIs match16's calls.

The narrow umbrella overlay puts15 in UniformEquilibrium.lean and16/17 in the
authoritative UniformEquilibrium/Diagnostics.lean inventory beside their
existing normalization owner. This retains the frozen lane choices and avoids
any Quitting→Diagnostics edge, forbidden by scripts/check_import_graph.py.
The secondary diagnostics umbrella is an integration inventory, not Research.
No production proof promotion/refactor is needed for this chain.

The shared main umbrella will change when the earlier SHAPE imports apply.
The manifest records BOTH its current-base transport and the predicted
post-SHAPE transport: d5573bdc368cd66f8d3be79fd3ba0f5d8668d319ae6b5c7c2b150e8d60d1ce13
→480a1701248dac73dd2a6f13b9f1fb75c24c6d39f168abe3f586ba5b231b4dcd.
These are in-memory reconstructions, not applied results. Root must verify
actual current hashes; unrelated intervening changes require recording the
actual new result, not claiming a stale complete-file hash.

## Narrow consumers and checks

SOURCE_SCOPE_HARNESS.lean imports ONLY final17 and contains unnamed consumers
for whole-game equality, literal live-zero payoff, positive-scaling UE
existence equivalence,16's actual integer bound/table/no-UE,17's fully expanded
SAME-table/SAME-expression output, and the final existential decision iff.
There is no caller-supplied minimizer or certificate in its forward examples.

GROUP_AXIOM_HARNESS.lean imports ONLY17 and audits all seven new declarations,
including the output predicate. Current14 and semantic foundations are covered
transitively; root's regenerated exhaustive AxiomAudit is authoritative.

Root should serialize named checks15,16,17 AFTER17A, then the scope harness
and narrow axiom harness, then umbrella/audit/trust/import/docs/full gates.
Expected axioms are only propext, Quot.sound and Classical.choice; no harness
was executed here. Literal structural congruence and dependent initial-state
rewriting in15, and reducible let/conjunction packaging in16/17, remain ordinary
compiler uncertainties rather than asserted successful checks.

This is one required Reflection decision-reduction branch, not whole Reflection
retirement. The separate approximate rational-rejection/search and exact
integral/paired/signed boundary fixture branches remain separate existing DAGs.
No optional43/60, screened-root, tilted calendar or new research is required here.

No shared edits, Lean/Lake, Git, cache/worktree, child agent, warning suppression,
trust-policy change or project math-note write was performed. All originals
remain immutable.
