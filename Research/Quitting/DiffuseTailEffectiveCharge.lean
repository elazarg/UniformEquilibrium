/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.DivergentChargeRecurrence
import Research.Quitting.DiffuseTailSoloStructure

/-!
# Effective charge budget and the extraction split for diffuse quitting tails

`Research/Quitting/DiffuseTailSoloStructure.lean` proves a quantitative bound
for one fenced solo window and derives `quittingTailPersistentlySolo_of_zeroFree`
*conditionally* on a single bundled hypothesis `QuittingSoloWindowExtraction`.
This module does two things with that material.

## Effective charge versus mesh

`survivalGap_mul_abs_normalizedSoloMatrix_le_of_soloWindow` is an inequality
between a window's charge, the two fence meshes, and the normalized solo
matrix entry.  On a table with a *margin*, `margin ≤ |M spectator owner|`, and
at fence meshes below `1/2`, it rearranges into a genuine budget:

  `quittingSoloWindowCharge ≤ 8 * M / margin * quittingSoloWindowMesh`

(`quittingSoloWindowCharge_le_of_margin`), where the window mesh is the sum of
the fence mesh and the return mesh.  The constant `8 * M / margin` comes from
the landed inequality's factor `4 * M * fenceMesh + 2 * M * returnMesh` on the
right and the factor `1 - fenceMesh ≥ 1/2` on the left, so the worst case is
`8 * M * fenceMesh + 4 * M * returnMesh ≤ 8 * M * (fenceMesh + returnMesh)`.

Summing over a family of windows gives `sum_quittingSoloWindowCharge_le_of_margin`
(finite sums), `summable_quittingSoloWindowCharge_of_margin`, and
`tsum_quittingSoloWindowCharge_le_of_margin`: on a margin table, a family of
fenced solo windows with a summable window-mesh series has finite total
conditioned charge, bounded by `8 * M / margin` times the mesh series.  That
is the currency consumed by `MathUE/SparseVanishingSchedule.lean`, whose
selection lemma produces dates with a summable mesh series.

Summability of the window-mesh series is a sparseness condition on the family,
not a global hypothesis in disguise:
`not_summable_quittingTailConditionedAbsorptionWeight` shows that the global
conditioned mesh series always diverges in an exact tail, because the
conditioned chain absorbs almost surely
(`tendsto_quittingTailConditionedSurvivalProduct_zero`).  A window family can
still have a summable mesh series, since its fence and closing dates are sparse
among all dates; separation of consecutive windows (`window_separated`) is what
makes those dates distinct.

The contrapositive `not_tendsto_quittingSoloWindowMesh_of_fencedSoloWindows`
records the consequence in its strongest form: on a margin table, the
window-mesh series of a fenced solo window family carrying a uniform positive
charge does not even tend to zero.  Since the window mesh is a sum of two
conditioned weights at dates escaping to infinity, that contradicts a vanishing
global conditioned mesh, which gives
`isEmpty_quittingFencedSoloWindows_of_soloMatrixMargin`: a second route to the
coexistence obstruction, carrying the explicit constant `8 * M / margin` and
not passing through the vanishing of the normalized solo entry.

## The charge floor is an additive condition

`quittingSoloWindowInsideHazard` is the total conditioned hazard strictly
inside a window.  The union bound and the survival estimate of
`MathUE/DivergentChargeRecurrence.lean` pin a window's conditioned charge
between `inside / (1 + inside)` and `inside`
(`quittingSoloWindowCharge_le_insideHazard`,
`one_sub_quittingSoloWindowCharge_mul_insideHazard_le`), so the multiplicative
charge floor and the additive inside-hazard floor are the same condition on a
family (`quittingUniformSoloWindowChargeFloor_iff_insideHazardFloor`).  With the
effective charge bound this also caps the inside hazard of a late window by a
fixed multiple of its fence mesh
(`quittingSoloWindowInsideHazard_le_of_margin`), and caps the conditioned mesh
at every date inside a window by the window's charge.

## Splitting the extraction hypothesis

`QuittingSoloWindowExtraction` is decomposed into three named pieces.

* **(i), proved.**  `nonempty_quittingFencedSoloWindowFamily_of_lateSoloAlternating`:
  late *strict* alternation (eventually every root is an active solo root of
  one of the two players) plus persistence of both yields an infinite family of
  fenced solo windows of positive length — everything the extraction needs
  except the charge.
* **(ii), proved, with a stated currency caveat.**
  `not_quittingTailRawChargeFloor_of_tendsto` routes the co-active branch to a
  vanishing one-stage absorption budget, consuming only one of the two players'
  rates, and
  `QuittingCounterexampleSeamWitness.not_coactiveChargeFloor` discharges that
  budget from the seam field `jointAbsorption_summable`.  The budget is in
  *raw* one-stage absorption mass, which is the currency the seam supplies; it
  therefore kills only a co-activity floor stated in raw quit probability.  A
  co-activity floor in the *conditioned* currency of the window bound is not
  addressed by this route.
* **(iii), open.**  `QuittingUniformSoloWindowChargeFloor` is a proposition
  definition, not a theorem: it says a fenced solo window family always has a
  subfamily with a uniform positive conditioned charge.  Nothing here proves
  it.  `QuittingUniformSoloWindowInsideHazardFloor` is its additive form.

  On a margin table with vanishing conditioned mesh the charge floor is
  refutable as soon as one fenced solo window family exists
  (`not_quittingUniformSoloWindowChargeFloor_of_family`), because a floored
  subfamily would be a `QuittingFencedSoloWindows` and
  `isEmpty_quittingFencedSoloWindows_of_soloMatrixMargin` excludes those.  The
  assembly below can therefore discharge (iii) only vacuously, when no family
  exists; the quantitative target that remains is ruling out a family carrying
  no floor at all, for which the effective charge bound gives `charge ≤
  constant * mesh` with both sides vanishing.

The assembly `quittingSoloWindowExtraction_of_dichotomy_of_chargeFloor` shows
(i) + (ii) + (iii) ⟹ `QuittingSoloWindowExtraction`, modulo one further
isolated hypothesis `QuittingTailPairSoloDichotomy` — "each distinct pair of
persistently active players either alternates strictly and late, or collides at
a uniform positive raw rate".  That hypothesis is *not* a tautology: it rules
out idle dates, third-player activity, and collisions whose raw rate vanishes.
It is stated separately so that the split's remaining hypotheses are named
rather than bundled.

The extraction hypothesis is moreover *equivalent* to the conclusion it is
used to prove: at most one persistently active player makes it vacuous
(`quittingSoloWindowExtraction_of_persistentlySolo`), so on a zero-free table
with vanishing conditioned mesh the two are interchangeable
(`quittingSoloWindowExtraction_iff_persistentlySolo`).  The residual that is
not of that shape is `QuittingNoFencedSoloWindowFamily`, which asks no uniform
charge of any window and yields the conclusion through
`quittingTailPersistentlySolo_of_noFencedSoloWindowFamily`.

`quittingTailPersistentlySolo_of_zeroFree_of_soloDichotomy` records
`quittingTailPersistentlySolo_of_zeroFree` with its conditionality expressed in
these terms.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Charge and mesh of a single fenced window -/

/-- The conditioned charge absorbed inside the window of `length` solo dates
opened at `fence`: one minus the window's survival product. -/
def quittingSoloWindowCharge
    (roots : ℕ → ι → PMF Bool) (fence length : ℕ) : ℝ :=
  1 - quittingTailConditionedSurvivalProduct roots (fence + 1) length

/-- The window's mesh budget: the conditioned mesh at the left fence plus the
conditioned mesh at the date closing the window. -/
def quittingSoloWindowMesh
    (roots : ℕ → ι → PMF Bool) (fence length : ℕ) : ℝ :=
  quittingTailConditionedAbsorptionWeight roots fence +
    quittingTailConditionedAbsorptionWeight roots (fence + 1 + length)

omit [DecidableEq ι] in
/-- The window charge is nonnegative in an exact tail. -/
theorem quittingSoloWindowCharge_nonneg
    (roots : ℕ → ι → PMF Bool)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (fence length : ℕ) :
    0 ≤ quittingSoloWindowCharge roots fence length := by
  have hle := (quittingTailConditionedSurvivalProduct_mem_unitInterval roots
    hpositive (fence + 1) length).2
  unfold quittingSoloWindowCharge
  linarith

omit [DecidableEq ι] in
/-- Each of the two mesh contributions is nonnegative in an exact tail. -/
theorem quittingTailConditionedAbsorptionWeight_nonneg_of_positive
    (roots : ℕ → ι → PMF Bool)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (time : ℕ) :
    0 ≤ quittingTailConditionedAbsorptionWeight roots time :=
  (quittingTailConditionedWeights_mem_unitInterval roots time
    (hpositive (time + 1)).le (hpositive time)).1.1

omit [DecidableEq ι] in
/-- The window mesh is nonnegative in an exact tail. -/
theorem quittingSoloWindowMesh_nonneg
    (roots : ℕ → ι → PMF Bool)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (fence length : ℕ) :
    0 ≤ quittingSoloWindowMesh roots fence length :=
  add_nonneg
    (quittingTailConditionedAbsorptionWeight_nonneg_of_positive roots hpositive
      fence)
    (quittingTailConditionedAbsorptionWeight_nonneg_of_positive roots hpositive
      (fence + 1 + length))

/-- The scalar rearrangement behind the effective charge bound. -/
private theorem charge_le_of_window_inequality {fenceMesh returnMesh charge
    entry margin bound : ℝ} (hfence : fenceMesh ≤ 1 / 2) (hcharge : 0 ≤ charge)
    (hbound : 0 ≤ bound) (hreturn : 0 ≤ returnMesh) (hmargin : 0 < margin)
    (hentry : margin ≤ entry)
    (hmain : (1 - fenceMesh) * (charge * entry) ≤
      4 * bound * fenceMesh + 2 * bound * returnMesh) :
    charge ≤ 8 * bound / margin * (fenceMesh + returnMesh) := by
  have hscaled : 0 ≤ charge * margin := mul_nonneg hcharge hmargin.le
  have hentryScaled : charge * margin ≤ charge * entry :=
    mul_le_mul_of_nonneg_left hentry hcharge
  have hshrink : (1 - fenceMesh) * (charge * margin) ≤
      (1 - fenceMesh) * (charge * entry) :=
    mul_le_mul_of_nonneg_left hentryScaled (by linarith)
  have hhalf : 1 / 2 * (charge * margin) ≤ (1 - fenceMesh) * (charge * margin) :=
    mul_le_mul_of_nonneg_right (by linarith) hscaled
  have hraw : charge * margin ≤ 8 * bound * fenceMesh + 4 * bound * returnMesh := by
    linarith
  have hslack : 0 ≤ 4 * bound * returnMesh :=
    mul_nonneg (by linarith) hreturn
  have hexpand : 8 * bound * (fenceMesh + returnMesh) =
      8 * bound * fenceMesh + 8 * bound * returnMesh := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hmargin]
  linarith

/-- **One window.**  On a table whose normalized solo entry
`M spectator owner` has absolute value at least `margin`, and at a fence whose
conditioned mesh is at most `1/2`, the conditioned charge absorbed inside a
fenced solo window is at most `8 * bound / margin` times the window mesh, where
`bound` is a uniform bound on the reward table.

This is the effective (rearranged) form of the quantitative inequality
`survivalGap_mul_abs_normalizedSoloMatrix_le_of_soloWindow`. -/
theorem quittingSoloWindowCharge_le_of_margin
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (spectator owner : ι)
    (htight : boundary spectator = quittingSoloReward reward spectator spectator)
    {margin : ℝ} (hmargin : 0 < margin)
    (hentry : margin ≤ |normalizedSoloMatrix reward spectator owner|)
    (fence length : ℕ)
    (hhalf : quittingTailConditionedAbsorptionWeight roots fence ≤ 1 / 2)
    (hfence : 0 < (roots fence spectator true).toReal)
    (hreturn : 0 < (roots (fence + 1 + length) spectator true).toReal)
    (hsolo : ∀ offset, offset < length →
      IsQuittingSoloRoot (roots (fence + 1 + offset)) owner)
    (hactive : ∀ offset, offset < length →
      0 < (roots (fence + 1 + offset) owner true).toReal) :
    quittingSoloWindowCharge roots fence length ≤
      8 * bound / margin * quittingSoloWindowMesh roots fence length := by
  have hmain := survivalGap_mul_abs_normalizedSoloMatrix_le_of_soloWindow roots
    value boundary hpolicy hnash hreward hpositive spectator owner htight fence
    length hfence hreturn hsolo hactive
  have hboundNonneg : (0 : ℝ) ≤ bound :=
    (abs_nonneg _).trans (hreward (quittingSingletonTerminal spectator) spectator)
  have hreturnNonneg :=
    quittingTailConditionedAbsorptionWeight_nonneg_of_positive roots hpositive
      (fence + 1 + length)
  have hchargeNonneg :=
    quittingSoloWindowCharge_nonneg roots hpositive fence length
  simp only [quittingSoloWindowCharge, quittingSoloWindowMesh] at hchargeNonneg ⊢
  exact charge_le_of_window_inequality hhalf hchargeNonneg hboundNonneg
    hreturnNonneg hmargin hentry hmain

/-! ## Families of fenced solo windows without a charge floor -/

/-- Recurrent windows on which only `owner` may quit, each of positive length
and fenced on both sides by a date at which `spectator` is active.  This is
`QuittingFencedSoloWindows` with the uniform charge floor removed: it is what
persistence and alternation actually produce. -/
structure QuittingFencedSoloWindowFamily
    (roots : ℕ → ι → PMF Bool) (spectator owner : ι) where
  /-- Left fence date of window `index`. -/
  fence : ℕ → ℕ
  /-- Number of solo dates in window `index`. -/
  length : ℕ → ℕ
  /-- The fence dates are strictly increasing, hence escape to infinity. -/
  fence_strictMono : StrictMono fence
  /-- Each window closes strictly before the next one opens, so distinct
  windows occupy disjoint blocks of dates. -/
  window_separated : ∀ index, fence index + 1 + length index < fence (index + 1)
  /-- Every window has at least one solo date. -/
  length_pos : ∀ index, 0 < length index
  /-- `spectator` is active at every left fence. -/
  fence_active : ∀ index, 0 < (roots (fence index) spectator true).toReal
  /-- `spectator` is active again at the date closing each window. -/
  return_active : ∀ index,
    0 < (roots (fence index + 1 + length index) spectator true).toReal
  /-- Only `owner` may quit inside each window. -/
  window_solo : ∀ index offset, offset < length index →
    IsQuittingSoloRoot (roots (fence index + 1 + offset)) owner
  /-- `owner` really is active inside each window. -/
  window_active : ∀ index offset, offset < length index →
    0 < (roots (fence index + 1 + offset) owner true).toReal

namespace QuittingFencedSoloWindowFamily

/-- A subfamily carrying a uniform positive conditioned charge is a
`QuittingFencedSoloWindows`. -/
def windows {roots : ℕ → ι → PMF Bool} {spectator owner : ι}
    (family : QuittingFencedSoloWindowFamily roots spectator owner)
    {select : ℕ → ℕ} (hselect : StrictMono select) {charge : ℝ}
    (hpos : 0 < charge)
    (hcharge : ∀ index, charge ≤ quittingSoloWindowCharge roots
      (family.fence (select index)) (family.length (select index))) :
    QuittingFencedSoloWindows roots spectator owner where
  fence index := family.fence (select index)
  length index := family.length (select index)
  charge := charge
  fence_tendsto :=
    (family.fence_strictMono.tendsto_atTop).comp hselect.tendsto_atTop
  charge_pos := hpos
  fence_active index := family.fence_active (select index)
  return_active index := family.return_active (select index)
  window_solo index := family.window_solo (select index)
  window_active index := family.window_active (select index)
  charge_le index := hcharge index

end QuittingFencedSoloWindowFamily

/-! ## The summed charge budget -/

section Budget

variable {roots : ℕ → ι → PMF Bool} {value : ℕ → Payoff ι} {boundary : Payoff ι}
variable {bound margin : ℝ} {spectator owner : ι}

/-- Every window of a family obeys the effective charge bound, once its fence
mesh is below `1/2`. -/
theorem quittingSoloWindowCharge_le_of_margin_of_family
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (htight : boundary spectator = quittingSoloReward reward spectator spectator)
    (hmargin : 0 < margin)
    (hentry : margin ≤ |normalizedSoloMatrix reward spectator owner|)
    (family : QuittingFencedSoloWindowFamily roots spectator owner)
    (index : ℕ)
    (hhalf : quittingTailConditionedAbsorptionWeight roots (family.fence index) ≤
      1 / 2) :
    quittingSoloWindowCharge roots (family.fence index) (family.length index) ≤
      8 * bound / margin *
        quittingSoloWindowMesh roots (family.fence index) (family.length index) :=
  quittingSoloWindowCharge_le_of_margin roots value boundary hpolicy hnash
    hreward hpositive spectator owner htight hmargin hentry (family.fence index)
    (family.length index) hhalf (family.fence_active index)
    (family.return_active index) (family.window_solo index)
    (family.window_active index)

/-- **Summed.**  The total conditioned charge of any finite set of windows
of a family is at most `8 * bound / margin` times their total mesh. -/
theorem sum_quittingSoloWindowCharge_le_of_margin
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (htight : boundary spectator = quittingSoloReward reward spectator spectator)
    (hmargin : 0 < margin)
    (hentry : margin ≤ |normalizedSoloMatrix reward spectator owner|)
    (family : QuittingFencedSoloWindowFamily roots spectator owner)
    (hhalf : ∀ index,
      quittingTailConditionedAbsorptionWeight roots (family.fence index) ≤ 1 / 2)
    (indices : Finset ℕ) :
    ∑ index ∈ indices,
        quittingSoloWindowCharge roots (family.fence index)
          (family.length index) ≤
      8 * bound / margin * ∑ index ∈ indices,
        quittingSoloWindowMesh roots (family.fence index)
          (family.length index) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun index _ =>
    quittingSoloWindowCharge_le_of_margin_of_family hpolicy hnash hreward
      hpositive htight hmargin hentry family index (hhalf index)

/-- **Summable form.**  A summable window-mesh series forces a summable
window-charge series. -/
theorem summable_quittingSoloWindowCharge_of_margin
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (htight : boundary spectator = quittingSoloReward reward spectator spectator)
    (hmargin : 0 < margin)
    (hentry : margin ≤ |normalizedSoloMatrix reward spectator owner|)
    (family : QuittingFencedSoloWindowFamily roots spectator owner)
    (hhalf : ∀ index,
      quittingTailConditionedAbsorptionWeight roots (family.fence index) ≤ 1 / 2)
    (hmesh : Summable fun index =>
      quittingSoloWindowMesh roots (family.fence index) (family.length index)) :
    Summable fun index =>
      quittingSoloWindowCharge roots (family.fence index)
        (family.length index) :=
  Summable.of_nonneg_of_le
    (fun _ => quittingSoloWindowCharge_nonneg roots hpositive _ _)
    (fun index => quittingSoloWindowCharge_le_of_margin_of_family hpolicy hnash
      hreward hpositive htight hmargin hentry family index (hhalf index))
    (hmesh.mul_left _)

/-- **Total charge.**  On a margin table, the total conditioned charge of a
fenced solo window family is at most `8 * bound / margin` times its total mesh.
This is the statement whose right-hand side is the summable mesh-weighted cost
produced by `Math.exists_sparse_vanishing_nonsummable_schedule`. -/
theorem tsum_quittingSoloWindowCharge_le_of_margin
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (htight : boundary spectator = quittingSoloReward reward spectator spectator)
    (hmargin : 0 < margin)
    (hentry : margin ≤ |normalizedSoloMatrix reward spectator owner|)
    (family : QuittingFencedSoloWindowFamily roots spectator owner)
    (hhalf : ∀ index,
      quittingTailConditionedAbsorptionWeight roots (family.fence index) ≤ 1 / 2)
    (hmesh : Summable fun index =>
      quittingSoloWindowMesh roots (family.fence index) (family.length index)) :
    ∑' index, quittingSoloWindowCharge roots (family.fence index)
        (family.length index) ≤
      8 * bound / margin * ∑' index,
        quittingSoloWindowMesh roots (family.fence index)
          (family.length index) := by
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum
    (fun index => quittingSoloWindowCharge_le_of_margin_of_family hpolicy hnash
      hreward hpositive htight hmargin hentry family index (hhalf index))
    (summable_quittingSoloWindowCharge_of_margin hpolicy hnash hreward hpositive
      htight hmargin hentry family hhalf hmesh)
    (hmesh.mul_left _)

/-- **Contrapositive.**  On a margin table, the window-mesh series of a
fenced solo window family carrying a uniform positive conditioned charge does
not tend to zero.  No global mesh hypothesis is used, and nothing about the
series beyond its termwise limit is consumed. -/
theorem not_tendsto_quittingSoloWindowMesh_of_fencedSoloWindows
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (htight : boundary spectator = quittingSoloReward reward spectator spectator)
    (hmargin : 0 < margin)
    (hentry : margin ≤ |normalizedSoloMatrix reward spectator owner|)
    (windows : QuittingFencedSoloWindows roots spectator owner) :
    ¬Tendsto (fun index =>
      quittingSoloWindowMesh roots (windows.fence index)
        (windows.length index)) atTop (nhds 0) := by
  intro hzero
  have hscaled : Tendsto (fun index => 8 * bound / margin *
      quittingSoloWindowMesh roots (windows.fence index)
        (windows.length index)) atTop (nhds 0) := by
    simpa using hzero.const_mul (8 * bound / margin)
  have hfloor : ∀ᶠ index in atTop, windows.charge ≤ 8 * bound / margin *
      quittingSoloWindowMesh roots (windows.fence index)
        (windows.length index) := by
    filter_upwards [(tendsto_order.1 hzero).2 (1 / 2) (by norm_num)] with
      index hindex
    have hreturnNonneg :=
      quittingTailConditionedAbsorptionWeight_nonneg_of_positive roots hpositive
        (windows.fence index + 1 + windows.length index)
    have hhalf :
        quittingTailConditionedAbsorptionWeight roots (windows.fence index) ≤
          1 / 2 := by
      unfold quittingSoloWindowMesh at hindex
      linarith
    have hstep := quittingSoloWindowCharge_le_of_margin roots value boundary
      hpolicy hnash hreward hpositive spectator owner htight hmargin hentry
      (windows.fence index) (windows.length index) hhalf
      (windows.fence_active index) (windows.return_active index)
      (windows.window_solo index) (windows.window_active index)
    exact le_trans (windows.charge_le index) hstep
  exact absurd (ge_of_tendsto hscaled hfloor) (not_le.2 windows.charge_pos)

/-- Summable form of the contrapositive: a summable window-mesh series has a
vanishing general term, which the uniform charge already forbids. -/
theorem not_summable_quittingSoloWindowMesh_of_fencedSoloWindows
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (htight : boundary spectator = quittingSoloReward reward spectator spectator)
    (hmargin : 0 < margin)
    (hentry : margin ≤ |normalizedSoloMatrix reward spectator owner|)
    (windows : QuittingFencedSoloWindows roots spectator owner) :
    ¬Summable fun index =>
      quittingSoloWindowMesh roots (windows.fence index)
        (windows.length index) := fun hmesh =>
  not_tendsto_quittingSoloWindowMesh_of_fencedSoloWindows hpolicy hnash hreward
    hpositive htight hmargin hentry windows hmesh.tendsto_atTop_zero

/-- **Quantitative coexistence obstruction.**  On a margin table a vanishing
global conditioned mesh already excludes a fenced solo window family carrying a
uniform positive conditioned charge: the window mesh is a sum of two
conditioned weights at dates escaping to infinity, so it vanishes along the
family, while the effective charge bound keeps it bounded below by the charge
divided by the bound's constant.

This route does not pass through the vanishing of the normalized solo entry,
and it carries the explicit constant `8 * bound / margin`. -/
theorem isEmpty_quittingFencedSoloWindows_of_soloMatrixMargin
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (htight : boundary spectator = quittingSoloReward reward spectator spectator)
    (hmargin : 0 < margin)
    (hentry : margin ≤ |normalizedSoloMatrix reward spectator owner|)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight roots) atTop
      (nhds 0)) :
    IsEmpty (QuittingFencedSoloWindows roots spectator owner) := by
  refine ⟨fun windows => ?_⟩
  have hclose : Tendsto
      (fun index => windows.fence index + 1 + windows.length index) atTop atTop :=
    tendsto_atTop_mono (fun index => by omega) windows.fence_tendsto
  have hwindowMesh : Tendsto (fun index =>
      quittingSoloWindowMesh roots (windows.fence index)
        (windows.length index)) atTop (nhds 0) := by
    simpa [quittingSoloWindowMesh] using
      (hmesh.comp windows.fence_tendsto).add (hmesh.comp hclose)
  exact not_tendsto_quittingSoloWindowMesh_of_fencedSoloWindows hpolicy hnash
    hreward hpositive htight hmargin hentry windows hwindowMesh

end Budget

/-! ## (i) Late strict alternation produces fenced solo windows -/

omit [Fintype ι] [DecidableEq ι] in
/-- At a solo root every other player has zero Quit probability. -/
theorem quitProbability_eq_zero_of_isQuittingSoloRoot
    {root : ι → PMF Bool} {owner other : ι}
    (hsolo : IsQuittingSoloRoot root owner) (hne : other ≠ owner) :
    (root other true).toReal = 0 := by
  rw [hsolo other hne]
  simp

/-- **Late strict alternation.**  From some date on, every root is an active
solo root of `first` or an active solo root of `second`.  This forbids idle
dates, third-player activity, and simultaneous activity of the pair. -/
def QuittingTailLateSoloAlternating
    (roots : ℕ → ι → PMF Bool) (first second : ι) : Prop :=
  ∃ start, ∀ time, start ≤ time →
    (IsQuittingSoloRoot (roots time) first ∧
        0 < (roots time first true).toReal) ∨
      (IsQuittingSoloRoot (roots time) second ∧
        0 < (roots time second true).toReal)

/-- A cofinal supply of window data can be threaded into a *separated*
sequence of windows: each window closes strictly before the next one opens.
Restarting the search past the chosen window's own closing date, rather than
past its fence, is what buys the separation, and separation is what makes the
per-window fence and closing dates injective. -/
private theorem exists_escaping_separated_of_cofinal {Q : ℕ → ℕ → Prop}
    (hcofinal : ∀ start, ∃ fence length, start ≤ fence ∧ Q fence length) :
    ∃ fence length : ℕ → ℕ,
      StrictMono fence ∧
        (∀ index, fence index + 1 + length index < fence (index + 1)) ∧
          ∀ index, Q (fence index) (length index) := by
  classical
  choose pick size hle hQ using hcofinal
  let starts : ℕ → ℕ :=
    fun index => Nat.rec 0 (fun _ prev => pick prev + size prev + 2) index
  have hseparated : ∀ index,
      pick (starts index) + 1 + size (starts index) <
        pick (starts (index + 1)) := by
    intro index
    have hstep : starts (index + 1) =
      pick (starts index) + size (starts index) + 2 := rfl
    have hbound := hle (starts (index + 1))
    omega
  refine ⟨fun index => pick (starts index), fun index => size (starts index),
    strictMono_nat_of_lt_succ fun index => ?_, hseparated,
    fun index => hQ (starts index)⟩
  have := hseparated index
  omega

omit [Fintype ι] [DecidableEq ι] in
/-- One fenced solo window with `second` inside and `first` on both fences,
opened arbitrarily late.  This is the mechanical half of the extraction
hypothesis. -/
theorem exists_quittingFencedSoloWindow_of_lateSoloAlternating
    {roots : ℕ → ι → PMF Bool} {first second : ι} (hne : first ≠ second)
    (halternating : QuittingTailLateSoloAlternating roots first second)
    (hfirst : QuittingTailPersistentlyActive roots first)
    (hsecond : QuittingTailPersistentlyActive roots second) (start : ℕ) :
    ∃ fence length, start ≤ fence ∧ 0 < length ∧
      0 < (roots fence first true).toReal ∧
      0 < (roots (fence + 1 + length) first true).toReal ∧
      (∀ offset, offset < length →
        IsQuittingSoloRoot (roots (fence + 1 + offset)) second) ∧
      (∀ offset, offset < length →
        0 < (roots (fence + 1 + offset) second true).toReal) := by
  classical
  obtain ⟨base, hbase⟩ := halternating
  obtain ⟨anchor, hanchor, hanchorActive⟩ := hfirst (max start base)
  have hstartAnchor : start ≤ anchor := le_trans (le_max_left _ _) hanchor
  have hbaseAnchor : base ≤ anchor := le_trans (le_max_right _ _) hanchor
  have hsecondExists : ∃ step,
      0 < (roots (anchor + 1 + step) second true).toReal := by
    obtain ⟨date, hdate, hactive⟩ := hsecond (anchor + 1)
    exact ⟨date - (anchor + 1), by
      rwa [show anchor + 1 + (date - (anchor + 1)) = date from by omega]⟩
  have hsecondSpec := Nat.find_spec hsecondExists
  set step := Nat.find hsecondExists with hstep
  refine ?_
  have hfenceEq : anchor + step + 1 = anchor + 1 + step := by omega
  have hfenceActive : 0 < (roots (anchor + step) first true).toReal := by
    rcases Nat.eq_zero_or_pos step with hzero | hpos
    · simpa [hzero] using hanchorActive
    · have hmin : ¬0 < (roots (anchor + 1 + (step - 1)) second true).toReal :=
        Nat.find_min hsecondExists (by omega)
      rw [show anchor + 1 + (step - 1) = anchor + step from by omega] at hmin
      rcases hbase (anchor + step) (by omega) with ⟨_, hactive⟩ | ⟨_, hactive⟩
      · exact hactive
      · exact absurd hactive hmin
  have hopen : 0 < (roots (anchor + step + 1) second true).toReal := by
    rw [hfenceEq]; exact hsecondSpec
  have hfirstExists : ∃ span,
      0 < (roots (anchor + step + 1 + span) first true).toReal := by
    obtain ⟨date, hdate, hactive⟩ := hfirst (anchor + step + 1)
    exact ⟨date - (anchor + step + 1), by
      rwa [show anchor + step + 1 + (date - (anchor + step + 1)) = date from
        by omega]⟩
  have hspanSpec := Nat.find_spec hfirstExists
  set span := Nat.find hfirstExists with hspan
  have hinside : ∀ offset, offset < span →
      IsQuittingSoloRoot (roots (anchor + step + 1 + offset)) second ∧
        0 < (roots (anchor + step + 1 + offset) second true).toReal := by
    intro offset hoffset
    have hmin : ¬0 < (roots (anchor + step + 1 + offset) first true).toReal :=
      Nat.find_min hfirstExists hoffset
    rcases hbase (anchor + step + 1 + offset) (by omega) with
      ⟨_, hactive⟩ | hright
    · exact absurd hactive hmin
    · exact hright
  have hspanPos : 0 < span := by
    rcases Nat.eq_zero_or_pos span with hzero | hpos
    · exfalso
      rw [hzero] at hspanSpec
      simp only [Nat.add_zero] at hspanSpec
      rcases hbase (anchor + step + 1) (by omega) with ⟨hsolo, _⟩ | ⟨hsolo, _⟩
      · rw [quitProbability_eq_zero_of_isQuittingSoloRoot hsolo
          (Ne.symm hne)] at hopen
        exact absurd hopen (lt_irrefl 0)
      · rw [quitProbability_eq_zero_of_isQuittingSoloRoot hsolo hne] at hspanSpec
        exact absurd hspanSpec (lt_irrefl 0)
    · exact hpos
  exact ⟨anchor + step, span, by omega, hspanPos, hfenceActive, hspanSpec,
    fun offset hoffset => (hinside offset hoffset).1,
    fun offset hoffset => (hinside offset hoffset).2⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **(i), proved.**  Late strict alternation of two persistently active
players yields an infinite family of fenced solo windows of positive length:
everything the extraction hypothesis asks for except the uniform charge. -/
theorem nonempty_quittingFencedSoloWindowFamily_of_lateSoloAlternating
    {roots : ℕ → ι → PMF Bool} {first second : ι} (hne : first ≠ second)
    (halternating : QuittingTailLateSoloAlternating roots first second)
    (hfirst : QuittingTailPersistentlyActive roots first)
    (hsecond : QuittingTailPersistentlyActive roots second) :
    Nonempty (QuittingFencedSoloWindowFamily roots first second) := by
  obtain ⟨fence, length, hmono, hseparated, hwindow⟩ :=
    exists_escaping_separated_of_cofinal
      (exists_quittingFencedSoloWindow_of_lateSoloAlternating hne halternating
        hfirst hsecond)
  exact ⟨{ fence := fence
           length := length
           fence_strictMono := hmono
           window_separated := hseparated
           length_pos := fun index => (hwindow index).1
           fence_active := fun index => (hwindow index).2.1
           return_active := fun index => (hwindow index).2.2.1
           window_solo := fun index => (hwindow index).2.2.2.1
           window_active := fun index => (hwindow index).2.2.2.2 }⟩

/-! ## (ii) The co-active branch and the raw collision budget -/

/-- **Co-activity at a uniform raw rate.**  The pair quits simultaneously at
arbitrarily late dates, each with probability at least a fixed positive
`charge`.  This is the raw-probability currency supplied by the seam's
absorption budget, not the conditioned currency of the window bound. -/
def QuittingTailCoactiveChargeFloor
    (roots : ℕ → ι → PMF Bool) (first second : ι) : Prop :=
  ∃ charge : ℝ, 0 < charge ∧ ∀ start, ∃ time, start ≤ time ∧
    charge ≤ (roots time first true).toReal ∧
      charge ≤ (roots time second true).toReal

/-- **A raw charge floor for one player.**  `who` quits at arbitrarily late
dates, each time with probability at least a fixed positive `charge`.  This is
the single-player content of a co-activity floor. -/
def QuittingTailRawChargeFloor (roots : ℕ → ι → PMF Bool) (who : ι) : Prop :=
  ∃ charge : ℝ, 0 < charge ∧ ∀ start, ∃ time, start ≤ time ∧
    charge ≤ (roots time who true).toReal

omit [Fintype ι] [DecidableEq ι] in
/-- A co-activity floor contains a raw charge floor for the first player. -/
theorem QuittingTailCoactiveChargeFloor.rawChargeFloor_left
    {roots : ℕ → ι → PMF Bool} {first second : ι}
    (hcoactive : QuittingTailCoactiveChargeFloor roots first second) :
    QuittingTailRawChargeFloor roots first := by
  obtain ⟨charge, hpos, hrecurrent⟩ := hcoactive
  refine ⟨charge, hpos, fun start => ?_⟩
  obtain ⟨time, htime, hfirst, -⟩ := hrecurrent start
  exact ⟨time, htime, hfirst⟩

omit [DecidableEq ι] in
/-- **(ii), proved, in the weakest currency.**  A *vanishing* one-stage
absorption mass already excludes a raw charge floor for a single player: the
player's own quit probability never exceeds the one-stage absorption mass, so a
recurrent positive floor contradicts the limit. -/
theorem not_quittingTailRawChargeFloor_of_tendsto
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hvanishing : Tendsto (fun time => quittingRootAbsorptionMass (roots time))
      atTop (nhds 0)) :
    ¬QuittingTailRawChargeFloor roots who := by
  rintro ⟨charge, hpos, hrecurrent⟩
  obtain ⟨start, hstart⟩ := eventually_atTop.1
    ((tendsto_order.1 hvanishing).2 charge hpos)
  obtain ⟨time, htime, hcharge⟩ := hrecurrent start
  exact absurd (hstart time htime)
    (not_lt.2 (hcharge.trans
      (quitProbability_le_quittingRootAbsorptionMass (roots time) who)))

omit [DecidableEq ι] in
/-- **(ii), proved.**  A vanishing one-stage absorption mass excludes a
co-activity floor at a uniform positive raw rate.  Only one of the two players'
rates is consumed; the co-active framing records where the branch arises, not
the strength of the argument. -/
theorem not_quittingTailCoactiveChargeFloor_of_tendsto
    (roots : ℕ → ι → PMF Bool) (first second : ι)
    (hvanishing : Tendsto (fun time => quittingRootAbsorptionMass (roots time))
      atTop (nhds 0)) :
    ¬QuittingTailCoactiveChargeFloor roots first second := fun hcoactive =>
  not_quittingTailRawChargeFloor_of_tendsto roots first hvanishing
    hcoactive.rawChargeFloor_left

omit [DecidableEq ι] in
/-- Summable form: a summable one-stage absorption series has a vanishing
general term, which is already enough. -/
theorem not_quittingTailCoactiveChargeFloor_of_summable
    (roots : ℕ → ι → PMF Bool) (first second : ι)
    (hsummable : Summable fun time => quittingRootAbsorptionMass (roots time)) :
    ¬QuittingTailCoactiveChargeFloor roots first second :=
  not_quittingTailCoactiveChargeFloor_of_tendsto roots first second
    hsummable.tendsto_atTop_zero

namespace QuittingCounterexampleSeamWitness

variable {regime : QuittingCounterexampleRegime reward}

/-- **(ii), routed to the seam.**  The seam's joint-absorption budget excludes
a raw co-activity floor along its canonical tail roots. -/
theorem not_coactiveChargeFloor
    (seam : QuittingCounterexampleSeamWitness regime) (first second : ι) :
    ¬QuittingTailCoactiveChargeFloor
      (quittingDynamicDebtTailRoots seam.tail) first second :=
  not_quittingTailCoactiveChargeFloor_of_summable _ first second
    seam.jointAbsorption_summable

/-- The seam's joint-absorption budget also excludes a single-player raw charge
floor along its canonical tail roots. -/
theorem not_rawChargeFloor
    (seam : QuittingCounterexampleSeamWitness regime) (who : ι) :
    ¬QuittingTailRawChargeFloor
      (quittingDynamicDebtTailRoots seam.tail) who :=
  not_quittingTailRawChargeFloor_of_tendsto _ who
    seam.jointAbsorption_summable.tendsto_atTop_zero

end QuittingCounterexampleSeamWitness

/-! ## (iii) The uniform charge floor, and the assembly -/

/-- **(iii), open proposition.**  Every fenced solo window family has a
subfamily whose windows all absorb at least one fixed positive share of the
conditioned scale.

This is the only genuinely quantitative open content of the extraction
hypothesis of `quittingTailPersistentlySolo_of_zeroFree`: pieces (i) and (ii)
are proved above.  Nothing forces a fixed positive conditioned charge per
window, and nothing in this file proves this proposition; it is stated as a
`Prop` definition. -/
def QuittingUniformSoloWindowChargeFloor (roots : ℕ → ι → PMF Bool) : Prop :=
  ∀ spectator owner : ι,
    ∀ family : QuittingFencedSoloWindowFamily roots spectator owner,
      ∃ select : ℕ → ℕ, ∃ charge : ℝ, StrictMono select ∧ 0 < charge ∧
        ∀ index, charge ≤ quittingSoloWindowCharge roots
          (family.fence (select index)) (family.length (select index))

/-- **The uniform charge floor is refutable, not merely unproved.**  On a
margin table with vanishing conditioned mesh, a single fenced solo window
family for a distinct boundary-tight pair already witnesses the failure of the
uniform charge floor: a floored subfamily of it would be a
`QuittingFencedSoloWindows`, and the quantitative obstruction excludes those.

So the charge-floor hypothesis of the extraction assembly can hold only when no
fenced solo window family exists at all, in which case it is discharged
vacuously.  Ruling out families themselves, rather than floored families, is
what the effective charge bound leaves open: it gives `charge ≤ constant *
mesh`, and both sides vanish along a family with no floor. -/
theorem not_quittingUniformSoloWindowChargeFloor_of_family
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    {spectator owner : ι}
    (htight : boundary spectator = quittingSoloReward reward spectator spectator)
    {margin : ℝ} (hmargin : 0 < margin)
    (hentry : margin ≤ |normalizedSoloMatrix reward spectator owner|)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight roots) atTop
      (nhds 0))
    (family : QuittingFencedSoloWindowFamily roots spectator owner) :
    ¬QuittingUniformSoloWindowChargeFloor roots := by
  intro hfloor
  obtain ⟨select, charge, hselect, hpos, hcharge⟩ := hfloor spectator owner
    family
  exact (isEmpty_quittingFencedSoloWindows_of_soloMatrixMargin hpolicy hnash
    hreward hpositive htight hmargin hentry hmesh).false
    (family.windows hselect hpos hcharge)

/-- **The one further hypothesis the split needs.**  Every distinct pair of
persistently active players either alternates strictly and late, or collides at
a uniform positive raw rate.

This is *not* a tautology.  The negation of recurrent co-activity leaves dates
at which neither player of the pair is active, dates at which a third player is
active, and collisions whose raw rate vanishes; a window family cannot be built
across any of those, because the landed window-transport lemma needs the owner
active at every date inside the window.  Isolating this hypothesis is what lets
the remaining open content be exactly the charge floor. -/
def QuittingTailPairSoloDichotomy (roots : ℕ → ι → PMF Bool) : Prop :=
  ∀ first second : ι, first ≠ second →
    QuittingTailPersistentlyActive roots first →
      QuittingTailPersistentlyActive roots second →
        QuittingTailLateSoloAlternating roots first second ∨
          QuittingTailCoactiveChargeFloor roots first second

omit [DecidableEq ι] in
/-- **Assembly.**  The bundled extraction hypothesis of
`Research/Quitting/DiffuseTailSoloStructure.lean` follows from the mechanical
alternation construction (i), the raw collision budget (ii), and the uniform
charge floor (iii), given the isolated pair dichotomy.  Only (iii) and the
dichotomy remain unproved. -/
theorem quittingSoloWindowExtraction_of_dichotomy_of_chargeFloor
    (roots : ℕ → ι → PMF Bool)
    (hvanishing : Tendsto (fun time => quittingRootAbsorptionMass (roots time))
      atTop (nhds 0))
    (hdichotomy : QuittingTailPairSoloDichotomy roots)
    (hfloor : QuittingUniformSoloWindowChargeFloor roots) :
    QuittingSoloWindowExtraction roots := by
  intro first second hne hfirst hsecond
  rcases hdichotomy first second hne hfirst hsecond with halternating | hcoactive
  · obtain ⟨family⟩ :=
      nonempty_quittingFencedSoloWindowFamily_of_lateSoloAlternating hne
        halternating hfirst hsecond
    obtain ⟨select, charge, hselect, hpos, hcharge⟩ := hfloor first second family
    exact Or.inl ⟨family.windows hselect hpos hcharge⟩
  · exact absurd hcoactive
      (not_quittingTailCoactiveChargeFloor_of_tendsto roots first second
        hvanishing)

omit [DecidableEq ι] in
/-- **The extraction hypothesis is implied by the conclusion it is used to
prove.**  If at most one player is persistently active, the extraction
requirement is vacuous: it only ever speaks about distinct persistently active
pairs. -/
theorem quittingSoloWindowExtraction_of_persistentlySolo
    (roots : ℕ → ι → PMF Bool) (hsolo : QuittingTailPersistentlySolo roots) :
    QuittingSoloWindowExtraction roots := fun first second hne hfirst hsecond =>
  absurd (hsolo first second hfirst hsecond) hne

/-- **The extraction hypothesis is equivalent to the eventually-solo
conclusion.**  On a zero-free table with vanishing conditioned mesh both
implications hold, so assuming extraction assumes the conclusion: the
hypothesis carries no content beyond the coexistence obstruction itself. -/
theorem quittingSoloWindowExtraction_iff_persistentlySolo
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight roots) atTop
      (nhds 0))
    (htight : ∀ who, QuittingTailPersistentlyActive roots who →
      boundary who = quittingSoloReward reward who who)
    (hzeroFree : QuittingZeroFreeSoloMatrix reward) :
    QuittingSoloWindowExtraction roots ↔ QuittingTailPersistentlySolo roots :=
  ⟨quittingTailPersistentlySolo_of_zeroFree roots value boundary hpolicy hnash
      hreward hpositive hmesh htight hzeroFree,
    quittingSoloWindowExtraction_of_persistentlySolo roots⟩

/-- **The non-degenerate residual.**  No distinct pair of coordinates carries a
fenced solo window family at all -- with no uniform charge asked of it.

Unlike the uniform charge floor, this is not refuted by the effective charge
budget: that budget bounds a window's charge by a multiple of its mesh, and
along a family with no floor both sides vanish. -/
def QuittingNoFencedSoloWindowFamily (roots : ℕ → ι → PMF Bool) : Prop :=
  ∀ spectator owner : ι, spectator ≠ owner →
    IsEmpty (QuittingFencedSoloWindowFamily roots spectator owner)

omit [DecidableEq ι] in
/-- **The eventually-solo conclusion without the charge floor.**  Late strict
alternation produces a fenced solo window family and the raw collision budget
kills the co-active branch, so the pair dichotomy together with the absence of
families gives the conclusion outright.  No uniform charge is asked of any
window, and no zero-freeness of the table is used. -/
theorem quittingTailPersistentlySolo_of_noFencedSoloWindowFamily
    (roots : ℕ → ι → PMF Bool)
    (hvanishing : Tendsto (fun time => quittingRootAbsorptionMass (roots time))
      atTop (nhds 0))
    (hdichotomy : QuittingTailPairSoloDichotomy roots)
    (hnofamily : QuittingNoFencedSoloWindowFamily roots) :
    QuittingTailPersistentlySolo roots := by
  intro first second hfirst hsecond
  by_contra hne
  rcases hdichotomy first second hne hfirst hsecond with
    halternating | hcoactive
  · obtain ⟨family⟩ :=
      nonempty_quittingFencedSoloWindowFamily_of_lateSoloAlternating hne
        halternating hfirst hsecond
    exact (hnofamily first second hne).false family
  · exact absurd hcoactive
      (not_quittingTailCoactiveChargeFloor_of_tendsto roots first second
        hvanishing)

/-- **Conditionality split.**  On a zero-free table, an exact
diffuse tail with a vanishing one-stage absorption mass has at most one
persistently active player — conditional on the pair dichotomy and on the
uniform charge floor, and on nothing else beyond the landed hypotheses of
`quittingTailPersistentlySolo_of_zeroFree`. -/
theorem quittingTailPersistentlySolo_of_zeroFree_of_soloDichotomy
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    {bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight roots) atTop
      (nhds 0))
    (htight : ∀ who, QuittingTailPersistentlyActive roots who →
      boundary who = quittingSoloReward reward who who)
    (hzeroFree : QuittingZeroFreeSoloMatrix reward)
    (hvanishing : Tendsto (fun time => quittingRootAbsorptionMass (roots time))
      atTop (nhds 0))
    (hdichotomy : QuittingTailPairSoloDichotomy roots)
    (hfloor : QuittingUniformSoloWindowChargeFloor roots) :
    QuittingTailPersistentlySolo roots :=
  quittingTailPersistentlySolo_of_zeroFree roots value boundary hpolicy hnash
    hreward hpositive hmesh htight hzeroFree
    (quittingSoloWindowExtraction_of_dichotomy_of_chargeFloor roots hvanishing
      hdichotomy hfloor)

/-! ## The charge floor in additive form -/

/-- Total conditioned hazard strictly inside the window of `length` solo dates
opened at `fence`.  This is the additive shadow of the window's multiplicative
conditioned charge. -/
def quittingSoloWindowInsideHazard
    (roots : ℕ → ι → PMF Bool) (fence length : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range length,
    quittingTailConditionedAbsorptionWeight roots (fence + 1 + offset)

omit [DecidableEq ι] in
/-- Each conditioned absorption weight is at most one in an exact tail. -/
theorem quittingTailConditionedAbsorptionWeight_le_one_of_positive
    (roots : ℕ → ι → PMF Bool)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (time : ℕ) :
    quittingTailConditionedAbsorptionWeight roots time ≤ 1 :=
  (quittingTailConditionedWeights_mem_unitInterval roots time
    (hpositive (time + 1)).le (hpositive time)).1.2

omit [DecidableEq ι] in
/-- The inside hazard of a window is nonnegative in an exact tail. -/
theorem quittingSoloWindowInsideHazard_nonneg
    (roots : ℕ → ι → PMF Bool)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (fence length : ℕ) :
    0 ≤ quittingSoloWindowInsideHazard roots fence length :=
  Finset.sum_nonneg fun offset _ =>
    quittingTailConditionedAbsorptionWeight_nonneg_of_positive roots hpositive
      (fence + 1 + offset)

omit [DecidableEq ι] in
/-- A window's conditioned charge is at most one. -/
theorem quittingSoloWindowCharge_le_one
    (roots : ℕ → ι → PMF Bool)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (fence length : ℕ) :
    quittingSoloWindowCharge roots fence length ≤ 1 := by
  have hsurvival := (quittingTailConditionedSurvivalProduct_mem_unitInterval
    roots hpositive (fence + 1) length).1
  unfold quittingSoloWindowCharge
  linarith

omit [DecidableEq ι] in
/-- **Union bound.**  A window's conditioned charge is at most its total inside
hazard. -/
theorem quittingSoloWindowCharge_le_insideHazard
    (roots : ℕ → ι → PMF Bool)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (fence length : ℕ) :
    quittingSoloWindowCharge roots fence length ≤
      quittingSoloWindowInsideHazard roots fence length := by
  have hbound := Math.one_sub_sum_range_le_prod_one_sub
    (quittingTailConditionedAbsorptionWeight roots)
    (quittingTailConditionedAbsorptionWeight_nonneg_of_positive roots hpositive)
    (quittingTailConditionedAbsorptionWeight_le_one_of_positive roots hpositive)
    (fence + 1) length
  unfold quittingSoloWindowCharge quittingSoloWindowInsideHazard
    quittingTailConditionedSurvivalProduct
  linarith

omit [DecidableEq ι] in
/-- **Sharper lower bound.**  Survival times one plus the inside hazard is at
most one, so the surviving share of a window's inside hazard is at most its
conditioned charge.  Together with the union bound this pins the charge between
`inside / (1 + inside)` and `inside`. -/
theorem one_sub_quittingSoloWindowCharge_mul_insideHazard_le
    (roots : ℕ → ι → PMF Bool)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (fence length : ℕ) :
    (1 - quittingSoloWindowCharge roots fence length) *
        quittingSoloWindowInsideHazard roots fence length ≤
      quittingSoloWindowCharge roots fence length := by
  have hbound := Math.prod_one_sub_mul_one_add_sum_range_le_one
    (quittingTailConditionedAbsorptionWeight roots)
    (quittingTailConditionedAbsorptionWeight_nonneg_of_positive roots hpositive)
    (quittingTailConditionedAbsorptionWeight_le_one_of_positive roots hpositive)
    (fence + 1) length
  have hexpand :
      (∏ offset ∈ Finset.range length,
          (1 - quittingTailConditionedAbsorptionWeight roots
            (fence + 1 + offset))) *
        (1 + ∑ offset ∈ Finset.range length,
          quittingTailConditionedAbsorptionWeight roots (fence + 1 + offset)) =
      (∏ offset ∈ Finset.range length,
          (1 - quittingTailConditionedAbsorptionWeight roots
            (fence + 1 + offset))) +
        (∏ offset ∈ Finset.range length,
            (1 - quittingTailConditionedAbsorptionWeight roots
              (fence + 1 + offset))) *
          ∑ offset ∈ Finset.range length,
            quittingTailConditionedAbsorptionWeight roots
              (fence + 1 + offset) := by ring
  rw [hexpand] at hbound
  unfold quittingSoloWindowCharge quittingSoloWindowInsideHazard
    quittingTailConditionedSurvivalProduct
  linarith

omit [DecidableEq ι] in
/-- The conditioned mesh at any date strictly inside a window is at most the
window's conditioned charge. -/
theorem quittingTailConditionedAbsorptionWeight_le_quittingSoloWindowCharge
    (roots : ℕ → ι → PMF Bool)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    {fence length offset : ℕ} (hoffset : offset < length) :
    quittingTailConditionedAbsorptionWeight roots (fence + 1 + offset) ≤
      quittingSoloWindowCharge roots fence length := by
  have hmem : offset ∈ Finset.range length := Finset.mem_range.2 hoffset
  have hsplit := Finset.mul_prod_erase (Finset.range length)
    (fun o => 1 - quittingTailConditionedAbsorptionWeight roots (fence + 1 + o))
    hmem
  have hrest : (∏ o ∈ (Finset.range length).erase offset,
      (1 - quittingTailConditionedAbsorptionWeight roots (fence + 1 + o))) ≤ 1 :=
    Finset.prod_le_one
      (fun o _ => by
        linarith [quittingTailConditionedAbsorptionWeight_le_one_of_positive
          roots hpositive (fence + 1 + o)])
      (fun o _ => by
        linarith [quittingTailConditionedAbsorptionWeight_nonneg_of_positive
          roots hpositive (fence + 1 + o)])
  have hrest0 : 0 ≤ (∏ o ∈ (Finset.range length).erase offset,
      (1 - quittingTailConditionedAbsorptionWeight roots (fence + 1 + o))) :=
    Finset.prod_nonneg fun o _ => by
      linarith [quittingTailConditionedAbsorptionWeight_le_one_of_positive
        roots hpositive (fence + 1 + o)]
  have hfactor : 0 ≤ 1 - quittingTailConditionedAbsorptionWeight roots
      (fence + 1 + offset) := by
    linarith [quittingTailConditionedAbsorptionWeight_le_one_of_positive roots
      hpositive (fence + 1 + offset)]
  unfold quittingSoloWindowCharge quittingTailConditionedSurvivalProduct
  nlinarith [hsplit, hrest, hrest0, hfactor]

section InsideBudget

variable {roots : ℕ → ι → PMF Bool} {value : ℕ → Payoff ι} {boundary : Payoff ι}
variable {bound margin : ℝ} {spectator owner : ι}

/-- **Inside-hazard budget.**  On a margin table, once the effective charge
bound puts a window's conditioned charge at or below one half, the total
conditioned hazard strictly inside the window is at most twice that bound.  A
late fenced solo window therefore accumulates no more hazard inside it than a
fixed multiple of the conditioned mesh at its two fences. -/
theorem quittingSoloWindowInsideHazard_le_of_margin
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (htight : boundary spectator = quittingSoloReward reward spectator spectator)
    (hmargin : 0 < margin)
    (hentry : margin ≤ |normalizedSoloMatrix reward spectator owner|)
    (fence length : ℕ)
    (hhalf : quittingTailConditionedAbsorptionWeight roots fence ≤ 1 / 2)
    (hsmall : 8 * bound / margin *
      quittingSoloWindowMesh roots fence length ≤ 1 / 2)
    (hfence : 0 < (roots fence spectator true).toReal)
    (hreturn : 0 < (roots (fence + 1 + length) spectator true).toReal)
    (hsolo : ∀ offset, offset < length →
      IsQuittingSoloRoot (roots (fence + 1 + offset)) owner)
    (hactive : ∀ offset, offset < length →
      0 < (roots (fence + 1 + offset) owner true).toReal) :
    quittingSoloWindowInsideHazard roots fence length ≤
      2 * (8 * bound / margin) * quittingSoloWindowMesh roots fence length := by
  have hcharge := quittingSoloWindowCharge_le_of_margin roots value boundary
    hpolicy hnash hreward hpositive spectator owner htight hmargin hentry fence
    length hhalf hfence hreturn hsolo hactive
  have hkey := one_sub_quittingSoloWindowCharge_mul_insideHazard_le roots
    hpositive fence length
  have hinside := quittingSoloWindowInsideHazard_nonneg roots hpositive fence
    length
  nlinarith [hcharge, hkey, hinside, hsmall]

end InsideBudget

/-- **(iii), additive form.**  Every fenced solo window family has a subfamily
whose windows all carry at least one fixed positive total conditioned hazard
strictly inside them.

This is a proposition definition, exactly like the multiplicative charge floor
it mirrors. -/
def QuittingUniformSoloWindowInsideHazardFloor
    (roots : ℕ → ι → PMF Bool) : Prop :=
  ∀ spectator owner : ι,
    ∀ family : QuittingFencedSoloWindowFamily roots spectator owner,
      ∃ select : ℕ → ℕ, ∃ floor : ℝ, StrictMono select ∧ 0 < floor ∧
        ∀ index, floor ≤ quittingSoloWindowInsideHazard roots
          (family.fence (select index)) (family.length (select index))

omit [DecidableEq ι] in
/-- **The charge floor is an additive statement.**  In an exact tail the
multiplicative conditioned charge floor and the additive inside-hazard floor
are the same condition on a window family: the union bound gives one direction
and the survival estimate the other, with the constant `floor / (1 + floor)`.

The additive form is the one that composes with a hazard series, so this
identifies the remaining quantitative content of the extraction hypothesis as a
statement about summed conditioned hazard rather than about a product. -/
theorem quittingUniformSoloWindowChargeFloor_iff_insideHazardFloor
    (roots : ℕ → ι → PMF Bool)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time) :
    QuittingUniformSoloWindowChargeFloor roots ↔
      QuittingUniformSoloWindowInsideHazardFloor roots := by
  constructor
  · intro hfloor spectator owner family
    obtain ⟨select, charge, hselect, hpos, hcharge⟩ := hfloor spectator owner
      family
    refine ⟨select, charge, hselect, hpos, fun index => (hcharge index).trans ?_⟩
    exact quittingSoloWindowCharge_le_insideHazard roots hpositive _ _
  · intro hfloor spectator owner family
    obtain ⟨select, floor, hselect, hpos, hinside⟩ := hfloor spectator owner
      family
    refine ⟨select, floor / (1 + floor), hselect,
      div_pos hpos (by linarith), fun index => ?_⟩
    set fence := family.fence (select index) with hfence
    set length := family.length (select index) with hlength
    have hkey := one_sub_quittingSoloWindowCharge_mul_insideHazard_le roots
      hpositive fence length
    have hchargeLe := quittingSoloWindowCharge_le_one roots hpositive fence
      length
    have hfloorLe := hinside index
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + floor)]
    nlinarith [hkey, hchargeLe, hfloorLe]

/-! ## The conditioned mesh series always diverges -/

omit [DecidableEq ι] in
/-- The joint survival limit factors through any finite prefix. -/
theorem quittingJointSurvivalLimit_eq_weight_mul
    (roots : ℕ → ι → PMF Bool) (start length : ℕ) :
    quittingJointSurvivalLimit roots start =
      quittingJointSurvivalWeight roots start length *
        quittingJointSurvivalLimit roots (start + length) := by
  induction length with
  | zero => simp
  | succ length ih =>
      rw [quittingJointSurvivalWeight_succ,
        show start + (length + 1) = start + length + 1 from by omega,
        mul_assoc, ← quittingJointSurvivalLimit_eq_continue_mul_succ]
      exact ih

omit [DecidableEq ι] in
/-- **Conditioned survival is a survival ratio.**  The conditioned survival
product over a window, scaled by the remaining eventual absorption at its
start, is the raw joint survival weight scaled by the remaining eventual
absorption at its end. -/
theorem quittingTailConditionedSurvivalProduct_mul_eventualAbsorption
    (roots : ℕ → ι → PMF Bool)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (start length : ℕ) :
    quittingTailConditionedSurvivalProduct roots start length *
        quittingTailEventualAbsorption roots start =
      quittingJointSurvivalWeight roots start length *
        quittingTailEventualAbsorption roots (start + length) := by
  induction length with
  | zero => simp
  | succ length ih =>
      have hstep : quittingTailConditionedSurvivalProduct roots start
          (length + 1) =
            quittingTailConditionedSurvivalProduct roots start length *
              (1 - quittingTailConditionedAbsorptionWeight roots
                (start + length)) := by
        unfold quittingTailConditionedSurvivalProduct
        rw [Finset.prod_range_succ]
      have hweights := quittingTailConditionedWeights_add roots (start + length)
        (hpositive (start + length))
      have hcontinuation :
          1 - quittingTailConditionedAbsorptionWeight roots (start + length) =
            quittingStationaryContinueMass (roots (start + length)) *
                quittingTailEventualAbsorption roots (start + length + 1) /
              quittingTailEventualAbsorption roots (start + length) := by
        rw [show (1 : ℝ) -
            quittingTailConditionedAbsorptionWeight roots (start + length) =
          quittingTailConditionedContinuationWeight roots (start + length) from
            by linarith]
        rfl
      have hne := (hpositive (start + length)).ne'
      rw [hstep, mul_right_comm, ih, hcontinuation,
        quittingJointSurvivalWeight_succ,
        show start + (length + 1) = start + length + 1 from by omega]
      field_simp

omit [DecidableEq ι] in
/-- Conditioned survival across a window, in the form that exhibits its limit:
the raw survival weight minus the joint survival limit, scaled down by the
remaining eventual absorption at the window's start. -/
theorem quittingTailConditionedSurvivalProduct_mul_eventualAbsorption_eq_sub
    (roots : ℕ → ι → PMF Bool)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (start length : ℕ) :
    quittingTailConditionedSurvivalProduct roots start length *
        quittingTailEventualAbsorption roots start =
      quittingJointSurvivalWeight roots start length -
        quittingJointSurvivalLimit roots start := by
  rw [quittingTailConditionedSurvivalProduct_mul_eventualAbsorption roots
    hpositive start length, quittingTailEventualAbsorption,
    quittingJointSurvivalLimit_eq_weight_mul roots start length]
  ring

omit [DecidableEq ι] in
/-- **The conditioned chain absorbs almost surely.**  Every shifted conditioned
survival product tends to zero: the raw survival weight converges to the joint
survival limit, which is exactly the quantity the conditioning divides out. -/
theorem tendsto_quittingTailConditionedSurvivalProduct_zero
    (roots : ℕ → ι → PMF Bool)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time)
    (start : ℕ) :
    Tendsto (quittingTailConditionedSurvivalProduct roots start) atTop
      (nhds 0) := by
  have hscaled : Tendsto (fun length =>
      quittingTailConditionedSurvivalProduct roots start length *
        quittingTailEventualAbsorption roots start) atTop (nhds 0) := by
    have hsub : Tendsto (fun length =>
        quittingJointSurvivalWeight roots start length -
          quittingJointSurvivalLimit roots start) atTop (nhds 0) := by
      simpa using (tendsto_quittingJointSurvivalLimit roots start).sub
        (tendsto_const_nhds
          (x := quittingJointSurvivalLimit roots start) (f := atTop (α := ℕ)))
    refine hsub.congr fun length => ?_
    exact (quittingTailConditionedSurvivalProduct_mul_eventualAbsorption_eq_sub
      roots hpositive start length).symm
  have hcancel := hscaled.div_const (quittingTailEventualAbsorption roots start)
  simp only [zero_div] at hcancel
  have hne := (hpositive start).ne'
  refine hcancel.congr fun length => ?_
  field_simp

omit [DecidableEq ι] in
/-- **The conditioned mesh series always diverges.**  In an exact tail with
positive remaining eventual absorption at every date, the conditioned
absorption weights are the hazards of a chain that absorbs almost surely, so
they are never summable.

Consequently a budget stated against the conditioned mesh cannot be discharged
from a global summability hypothesis; it has to be discharged along a sparse
family of dates, which is what a window family's fence and closing dates
supply. -/
theorem not_summable_quittingTailConditionedAbsorptionWeight
    (roots : ℕ → ι → PMF Bool)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption roots time) :
    ¬Summable (quittingTailConditionedAbsorptionWeight roots) :=
  Math.not_summable_of_tendsto_prod_one_sub_zero
    (quittingTailConditionedAbsorptionWeight roots)
    (quittingTailConditionedAbsorptionWeight_nonneg_of_positive roots hpositive)
    (quittingTailConditionedAbsorptionWeight_le_one_of_positive roots hpositive)
    (tendsto_quittingTailConditionedSurvivalProduct_zero roots hpositive)

end GameTheory
