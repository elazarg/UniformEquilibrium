/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.DiffuseTailSoloStructure

/-!
# Effective charge budget and the extraction split for diffuse quitting tails

`Research/Quitting/DiffuseTailSoloStructure.lean` proves a quantitative form
of T2 for one fenced solo window and derives T3 *conditionally* on a single
bundled hypothesis `QuittingSoloWindowExtraction`.  This module does two
things with that material.

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
selection lemma produces dates with a summable mesh series.  It is *not* an
automatic match: the schedule lemma controls the mesh only at the dates it
selects, while a window family's return dates are determined by the windows,
so the summability of the combined window-mesh series is a hypothesis here and
not a consequence of a vanishing global mesh.

The contrapositive `not_summable_quittingSoloWindowMesh_of_fencedSoloWindows`
records the consequence: on a margin table, a fenced solo window family
carrying a uniform positive charge has a *non-summable* window-mesh series.
This is a companion to, not a corollary of, T2: T2 assumes the global
conditioned mesh vanishes, which neither implies nor is implied by summability
along the family.

## Splitting the extraction hypothesis

`QuittingSoloWindowExtraction` is decomposed into three named pieces.

* **(i), proved.**  `nonempty_quittingFencedSoloWindowFamily_of_lateSoloAlternating`:
  late *strict* alternation (eventually every root is an active solo root of
  one of the two players) plus persistence of both yields an infinite family of
  fenced solo windows of positive length — everything the extraction needs
  except the charge.
* **(ii), proved, with a stated currency caveat.**
  `not_quittingTailCoactiveChargeFloor_of_summable` routes the co-active branch
  to a summable one-stage absorption budget, and
  `QuittingCounterexampleSeamWitness.not_coactiveChargeFloor` discharges that
  budget from the seam field `jointAbsorption_summable`.  The budget is in
  *raw* one-stage absorption mass, which is the currency the seam supplies; it
  therefore kills only a co-activity floor stated in raw quit probability.  A
  co-activity floor in the *conditioned* currency of the window bound is not
  addressed by this route.
* **(iii), open.**  `QuittingUniformSoloWindowChargeFloor` is a proposition
  definition, not a theorem: it says a fenced solo window family always has a
  subfamily with a uniform positive conditioned charge.  Nothing here proves
  it.

The assembly `quittingSoloWindowExtraction_of_dichotomy_of_chargeFloor` shows
(i) + (ii) + (iii) ⟹ `QuittingSoloWindowExtraction`, modulo one further
isolated hypothesis `QuittingTailPairSoloDichotomy` — "each distinct pair of
persistently active players either alternates strictly and late, or collides at
a uniform positive raw rate".  That hypothesis is *not* a tautology: it rules
out idle dates, third-player activity, and collisions whose raw rate vanishes.
It is stated separately precisely so that the remaining genuinely quantitative
open content is exactly (iii).

`quittingTailPersistentlySolo_of_zeroFree_of_soloDichotomy` records T3 with its
conditionality expressed in these terms.
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

/-- **M6, one window.**  On a table whose normalized solo entry
`M spectator owner` has absolute value at least `margin`, and at a fence whose
conditioned mesh is at most `1/2`, the conditioned charge absorbed inside a
fenced solo window is at most `8 * bound / margin` times the window mesh, where
`bound` is a uniform bound on the reward table.

This is the effective (rearranged) form of the quantitative T2 inequality
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
  /-- The fence dates escape to infinity. -/
  fence_tendsto : Tendsto fence atTop atTop
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
  fence_tendsto := family.fence_tendsto.comp hselect.tendsto_atTop
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

/-- **M6, summed.**  The total conditioned charge of any finite set of windows
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

/-- **M6, summable form.**  A summable window-mesh series forces a summable
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

/-- **M6, total charge.**  On a margin table, the total conditioned charge of a
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

/-- **M6, contrapositive.**  On a margin table, a fenced solo window family
carrying a uniform positive conditioned charge has a non-summable window-mesh
series.  No global mesh hypothesis is used. -/
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
        (windows.length index) := by
  intro hmesh
  have hzero := hmesh.tendsto_atTop_zero
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

/-- A cofinal supply of window data can be threaded into an escaping
sequence of windows. -/
private theorem exists_escaping_of_cofinal {Q : ℕ → ℕ → Prop}
    (hcofinal : ∀ start, ∃ fence length, start ≤ fence ∧ Q fence length) :
    ∃ fence length : ℕ → ℕ,
      Tendsto fence atTop atTop ∧ ∀ index, Q (fence index) (length index) := by
  classical
  choose pick size hle hQ using hcofinal
  let starts : ℕ → ℕ := fun index => Nat.rec 0 (fun _ prev => pick prev + 1) index
  have hmono : StrictMono fun index => pick (starts index) := by
    refine strictMono_nat_of_lt_succ fun index => ?_
    have hstep : starts (index + 1) = pick (starts index) + 1 := rfl
    have hbound := hle (starts (index + 1))
    omega
  exact ⟨fun index => pick (starts index), fun index => size (starts index),
    hmono.tendsto_atTop, fun index => hQ (starts index)⟩

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
  obtain ⟨fence, length, htendsto, hwindow⟩ :=
    exists_escaping_of_cofinal
      (exists_quittingFencedSoloWindow_of_lateSoloAlternating hne halternating
        hfirst hsecond)
  exact ⟨{ fence := fence
           length := length
           fence_tendsto := htendsto
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

omit [DecidableEq ι] in
/-- **(ii), proved.**  A summable one-stage absorption series excludes a
co-activity floor at a uniform positive raw rate.  Only one of the two players'
rates is consumed, so the same budget already excludes a single-player raw
charge floor; the co-active framing records where the branch arises, not the
strength of the argument. -/
theorem not_quittingTailCoactiveChargeFloor_of_summable
    (roots : ℕ → ι → PMF Bool) (first second : ι)
    (hsummable : Summable fun time => quittingRootAbsorptionMass (roots time)) :
    ¬QuittingTailCoactiveChargeFloor roots first second := by
  rintro ⟨charge, hpos, hrecurrent⟩
  obtain ⟨start, hstart⟩ := eventually_atTop.1
    ((tendsto_order.1 hsummable.tendsto_atTop_zero).2 charge hpos)
  obtain ⟨time, htime, hfirstCharge, -⟩ := hrecurrent start
  exact absurd (hstart time htime)
    (not_lt.2 (hfirstCharge.trans
      (quitProbability_le_quittingRootAbsorptionMass (roots time) first)))

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

end QuittingCounterexampleSeamWitness

/-! ## (iii) The uniform charge floor, and the assembly -/

/-- **(iii), open proposition.**  Every fenced solo window family has a
subfamily whose windows all absorb at least one fixed positive share of the
conditioned scale.

This is the *only* genuinely quantitative open content of T3's extraction
hypothesis: pieces (i) and (ii) are proved above.  Nothing forces a fixed
positive conditioned charge per window, and nothing in this file proves this
proposition; it is stated as a `Prop` definition. -/
def QuittingUniformSoloWindowChargeFloor (roots : ℕ → ι → PMF Bool) : Prop :=
  ∀ spectator owner : ι,
    ∀ family : QuittingFencedSoloWindowFamily roots spectator owner,
      ∃ select : ℕ → ℕ, ∃ charge : ℝ, StrictMono select ∧ 0 < charge ∧
        ∀ index, charge ≤ quittingSoloWindowCharge roots
          (family.fence (select index)) (family.length (select index))

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
/-- **M11, assembly.**  The bundled extraction hypothesis of
`Research/Quitting/DiffuseTailSoloStructure.lean` follows from the mechanical
alternation construction (i), the raw collision budget (ii), and the uniform
charge floor (iii), given the isolated pair dichotomy.  Only (iii) and the
dichotomy remain unproved. -/
theorem quittingSoloWindowExtraction_of_dichotomy_of_chargeFloor
    (roots : ℕ → ι → PMF Bool)
    (hsummable : Summable fun time => quittingRootAbsorptionMass (roots time))
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
      (not_quittingTailCoactiveChargeFloor_of_summable roots first second
        hsummable)

/-- **T3 with its conditionality split.**  On a zero-free table, an exact
diffuse tail with a summable one-stage absorption series has at most one
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
    (hsummable : Summable fun time => quittingRootAbsorptionMass (roots time))
    (hdichotomy : QuittingTailPairSoloDichotomy roots)
    (hfloor : QuittingUniformSoloWindowChargeFloor roots) :
    QuittingTailPersistentlySolo roots :=
  quittingTailPersistentlySolo_of_zeroFree roots value boundary hpolicy hnash
    hreward hpositive hmesh htight hzeroFree
    (quittingSoloWindowExtraction_of_dichotomy_of_chargeFloor roots hsummable
      hdichotomy hfloor)

end GameTheory
