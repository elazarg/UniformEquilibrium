Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Sorin Remark 4 critical-rate constructors: independent static review

## Verdict

PASS for the supplied known-source mathematics, actual-profile quantifiers, and static dependency/packaging audit of ordered patches 001 → 002 → 003 → 004 → 005 in `/tmp/sorin-asymmetric-critical-constructors.MzUuFU68`.

No definite additional proof/API repair was identified. This is NOT a Lean, warning-policy, transitive-axiom, integration, or full-build seal. No compiler, Lake, Git, shared edit, cache, worktree, snapshot, or child agent was used. The existing above-critical comparison/uniqueness conjunct remains unproved, and the unchanged whole `concluding_remark_4` retains its `sorry`. The new constructor declarations do not depend on that theorem.

Read the entire five patches, entire source/dependency record and harness, the original printed Remark (4), page 160, and the exact relevant current paper/production owners. Reconstructed the post-P4 paper and this complete chain in memory only; every context was unique and all recorded intermediate hashes matched.

## 1. Original source and literal parameters

The source is `literature/SORIN_1986__ON_REPEATED_GAMES_WITH_COMPLETE_INFORMATION.pdf`, concluding Remark (4), printed page 160. Its matrix is exactly the current `asymmetricGeneralizedDilemma` in `Literature/Sorin1986.lean`:

| Joint action | Payoff |
| --- | --- |
| CC | (β − y, β − y) |
| CD | (α − x, β) |
| DC | (β, α − x) |
| DD | (α, α) |

The assumptions remain α < β − y, x > 0, y > 0. The original `asymmetricCriticalDiscount` remains max(β − α − x, β − α − y)/(β − α). Paper λ is the current-stage weight; repository continuation is 1 − λ. The constructors and Nash statements consistently preserve that translation.

The rate is derived internally to lie strictly between zero and one. The denominator is positive from α < β − y and y > 0. The maximum numerator is positive because its second term is positive; each term is smaller than the denominator because x and y are positive. No additional hypothesis α > 0, β > 0, or x < β − α is introduced.

The source prints stationary cooperation for x > y. The already-owned literal paper statement uses the closed branch x ≥ y; the new proof correctly covers its equality boundary as well. At x = y both expressions for the critical rate agree. This harmless closed boundary is established by the displayed non-strict incentive inequality, not assumed by a favorable producer field.

## 2. Shared actual trigger extraction

Patch001 factors three existing-proof ingredients inside the same Literature file:

- `FiniteStageGame.triggerBehaviorProfile_other_on_support` identifies a nondeviator's actual mixed action on support of the history law of `Function.update actualProfile who arbitraryDeviation`.
- `FiniteStageGame.triggerBehaviorProfile_discountedPayoff` proves actual delivery from a bounded on-path affine recurrence.
- `binaryGrimProfile_discounted_deviation_cap` lifts actionwise source bounds to the entire arbitrary behavioral replacement payoff.

The first helper uses the existing `FiniteStageGame.firstMismatch_of_mem_support_trigger_update`, `publicTriggerStatus_eq_some_of_first`, and monitored-to-stochastic realized-action adapter. It makes no assertion that an arbitrary unreachable trigger status names the actual deviator. At time zero, the on-path condition is vacuous. After a supported first mismatch, only the nonculprit's punishment action is used; the culprit's default action is overwritten by the unilateral replacement.

The cap helper's history potential is the bounded calendar value while on path, and the punishment baseline after any mismatch. The successor test uses the existing `triggerOnPath_snoc_iff` on the SAME actual history and action. It splits exact calendar action from changed action, and it never reconstructs an independently chosen favorable successor profile. The source action bounds are assumptions only of this private generic helper; both actual final constructors derive all of them from the original matrix.

On support of the actual mixed action law, the other player is forced to the calendar action or to defection. `Math.PMFProduct.eq_of_mem_support_pmfPi_update_pure` supplies this fact without assuming the deviator is pure. The actionwise inequality is averaged with `Math.ProbabilityMassFunction.expect_le_of_le_on_support`; exact stage and continuation expectations are those of the current stochastic profile. Stage absolute bounds are obtained internally by finite boundedness.

The final telescope is the production `StochasticGame.discountedPayoff_le_of_history_bellman_ge_on_support` in `UniformEquilibrium/ProofView/Concepts/Stochastic/Strategy/Potential/Adaptive.lean`. It permits an arbitrary history-dependent profile and requires its Bellman inequality only on the actual history-law support. The private helper supplies bounded potential values directly; no global subgame-perfect or unreachable-history cap premise is imposed. Its discount substitution gives 0 ≤ 1 − λ < 1 for every 0 < λ ≤ 1, including λ = 1. No strict positive continuation coefficient is used.

Delivery uses the existing realized-action expected-stage identity and `FiniteStageGame.stageEU_triggerMonitoredProfile`, then the unchanged interface of `discounted_sum_eq_of_affine_recurrence`. In the expected post-P4 base, that private scalar interface delegates to the promoted generic geometric telescope. No second summability/interchange proof or independent continuation oracle is introduced.

## 3. Stationary constructor

`asymmetricStationaryProfile` is an actual behavioral trigger profile with calendar CC forever and actual nonculprit defection after a supported mismatch. Its target is literally `pair (β − y) (β − y)`.

`asymmetricStationaryProfile_discountedPayoff` establishes delivery under just the original three parameter assumptions, because the constant on-path payoff does not depend on the branch ordering. The deviation-cap, Nash and equilibrium-payoff membership theorems additionally require exactly y ≤ x.

On this branch λ = (β − α − y)/(β − α), and the proof establishes the exact changed-action identity λβ + (1 − λ)α = β − y. A player facing cooperation receives either β − y or β. Continuing cooperation followed hypothetically by baseline α remains below the source value because α < β − y. Against punishment defection, either action pays at most α because x > 0. All signs are valid even when α and β are negative.

`asymmetricStationaryProfile_discounted_deviation_cap` quantifies over EVERY player and EVERY full `BehaviorStrategy who`. `asymmetricStationaryProfile_isDiscountedNash` rewrites the bound with the actual profile's own delivered payoff; `asymmetricStationary_mem_discountedEquilibriumPayoffs` supplies the actual profile internally. No cap, Nash witness, maximizer, or reply is a final input.

The harness explicitly covers x = y and the negative-payoff/large-loss case α = −10, β = −5, x = 7, y = 2. Here x > β − α; that case remains inside the public theorem, as required.

## 4. Alternating constructor

`asymmetricAlternatingPath` starts at DC: at time zero the false player chooses true and the true player chooses false. Odd times are CD. This is the source order (β, α − x), then (α − x, β); it is not the swapped calendar.

For x < y, the rate is λ = (β − α − x)/(β − α). The constructed phase values are (β − x, α), then (α, β − x). The two literal recurrence identities are proved exactly:

- λβ + (1 − λ)α = β − x;
- λ(α − x) + (1 − λ)(β − x) = α.

The second identity is an equality at a zero-surplus phase. No strictly positive punishment margin is required. The parity recurrence switches these exact values at each calendar date.

`asymmetricAlternatingDiscountedPayoff_eq` identifies the source's original two-period expression with `pair (β − x) α`, using internally nonzero denominators. The public `asymmetricAlternatingProfile_discountedPayoff` nevertheless prints the full original `alternatingDiscountedPayoff` expression with the original rate and starting order, so this useful literal source claim is not hidden in a proof.

For a changed action at a low-value phase, the opponent defects, so the stage payoff is at most α and the punished continuation is α. At a high-value phase, every stage payoff is at most β, so the exact first recurrence identity gives the cap. These are literal table case splits, not supplied best-response values. Absolute phase bounds use max(|β − x|, |α|), so no payoff positivity is silently assumed.

`asymmetricAlternatingProfile_discounted_deviation_cap`, `asymmetricAlternatingProfile_isDiscountedNash`, and `asymmetricAlternating_mem_discountedEquilibriumPayoffs` preserve the full unilateral behavioral quantifier and internally produced same-profile payoff/Nash conjunction. They do not claim unsupported child profiles are Nash or impose unused off-path subgame perfection.

## 5. P15 regressions, overlays, ownership, and limits

Patch001 preserves the public signatures of `prisonerVertexProfile_discountedPayoff` and `prisonerVertexProfile_discounted_deviation_cap`. Their proofs now delegate to the factored owners using the existing literal P15 recurrences, changed-action bound and punishment bound. The original actual profiles and `prisonerVertexProfile_isDiscountedNash` are unchanged. The private nondeviator support wrapper retains its statement and delegates too.

Patch004 only fixes pinned additive-order API use and combines a redundant Boolean simplification. `add_le_add` receives explicit left/right inequalities in the correct order. Patch005 explicitly normalizes 1 − 3/4 to 1/4 in the three P15 applications, including multiplication by baseline one in the changed-action cap. These repairs change neither public assumptions nor conclusions.

The new private helpers are source-specific adapters over the Literature-owned `FiniteStageGame`; retaining them in `Literature/Sorin1986.lean` does not create a production-to-Literature dependency. Existing production Bellman, probability, monitoring, and telescope foundations are reused. No import or module-inventory change is introduced by this packet. No added forbidden trust primitive was found.

The manual harness contains 18 axiom queries: both public actual profiles; delivery/cap/Nash/membership for each; three public P15 declarations plus literal P15; and four actual consumer fixtures. The support helper is covered transitively through the cap proofs. This is appropriate, but the harness has not been run in this lane. Root must compile the chain and recheck P15 after factoring, permitting only `propext`, `Quot.sound`, and `Classical.choice`.

Whole Remark4 remains open specifically at its above-critical comparison/uniqueness conjunct. The new declarations prove its two critical-rate constructor branches only. No equilibrium monotonicity under parameter decreases, finite-horizon Nash, uniform equilibrium, or new endpoint statement outside the source assumptions is claimed.

## 6. Verified immutable hashes and application contexts

All files below are under `/tmp/sorin-asymmetric-critical-constructors.MzUuFU68` unless otherwise indicated.

| File | SHA256 |
| --- | --- |
| `001_GENERALIZED_ACTUAL_GRIM_ADAPTER.patch` | `9f02f8cb615dc33118ac0d4c6ccf21cbd62f29ce90d8a5f115fc271534e6787c` |
| `002_STATIONARY_CRITICAL_CONSTRUCTION.patch` | `77beaabd1180a74ed9b715b41a27d0f3bc294ab126326e62732d5e0614c7b01e` |
| `003_ALTERNATING_CRITICAL_CONSTRUCTION.patch` | `1cee8d388cc38c65011082e0c99ef776995ac0945ef36043cced3a4a7f4cde46` |
| `004_PINNED_ADDITIVE_ORDER_NORMALIZATION.patch` | `9c8525d33e5f5e4892dd1e54ec8bfe8cb82909c1e2e736546ddef17a342dc709` |
| `005_P15_EXACT_CONTINUATION_COEFFICIENT.patch` | `9ba54e4a11c37c7d6bf8a7d02c4ab18ca1aab0669ab34c5ca809fea1d38974ea` |
| `SOURCE_AND_DEPENDENCIES.txt` | `acb7c37a477c310806e23a21e50d97822d90ef0378746b3285f0c67e3408fa42` |
| `AXIOMS_AND_ACTUAL_CONSUMERS_AFTER_CHECKS.lean` | `08f18d9636a98ff177c7f8486aa7f75ed4b22f9a877af9535a30088a9aef8932` |

Independently recomputed in-memory source chain:

| State | SHA256 |
| --- | --- |
| Current `Literature/Sorin1986.lean` | `fba6f32df9e627384edd4e5e21fec63a5e6d14e5eef83e9b07d462b1439bdfa5` |
| After existing P4 paper/delegation patch | `2c88f34cbf93c047d5d42efbba92016a86ab5b33686c5c054a7fbe9cc6722156` |
| After P4 doc overlay: exact required base | `bfaac016cff33d49bb67f174ed79860bd0fe0ff94b7cad3549f9edc511c3456a` |
| After001 | `481c4dbfa904ffb6d2835255b7f8ac56bf543b144fc33ab0771d7e1245f6d8a4` |
| After002 | `2d09aa9c53e452e4959caa14cdf5d0e4543d9249475b6a50a96068eb082edf06` |
| After003 | `e11821d2b1bb629fcc518c10c264e897d346fb8e0e712af4af09ccf74befb9ae` |
| After004 | `919a46e65eb9d875caebb765b17b40eac9b7812269d6b99942c7ae135c219755` |
| After005 | `5ecfd7f0b986f91d00272832825a321ee8e475d828bb867578e28d6604bba773` |

Source PDF SHA256: `d09a8e78f37f9863ff40e969a90f03799967d05eb70ba28a93afab84ddfce56c`.

Current `UniformEquilibrium/ProofView/Concepts/Stochastic/Strategy/Potential/Adaptive.lean`: `4852b8219663f80320452a982cc8446728d25e637c820838e063f3800944abff`.

Current `UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Discounted.lean`: `cf8690ce05062e9efed94c48ad14fe44c5e9a394244601696f61703bcdfb231d`.

Apply only after the exact P4 predecessor chain, then001→002→003→004→005. Unique contexts and resulting byte equality were checked in memory, not by a shared patch application. No additional overlay is recommended on static evidence.
