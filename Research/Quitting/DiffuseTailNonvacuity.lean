/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.DiffuseTailEffectiveCharge
import Research.Quitting.SourceMatchedSnellPurificationCollapse
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundarySoloMatrixCalibration

/-!
# A satisfied instance of the diffuse-tail hypothesis bundle

`Research/Quitting/DiffuseTailSoloStructure.lean` and
`Research/Quitting/DiffuseTailEffectiveCharge.lean` quantify over exact
diffuse tails satisfying several hypotheses at once: the exact policy
recursion, exact endpoint Nash at accuracy zero at every date, positive
remaining eventual absorption, a vanishing conditioned mesh, and boundary
tightness at every persistently active player.  This module discharges all of
them simultaneously for the explicit solo-hazard tail `svRoots` of
`Research/Quitting/SourceMatchedSnellPurificationCollapse.lean` over the
Solan--Vieille boundary table, whose zero-free margin `1` is
`SolanVieilleBoundary.one_le_abs_normalizedSoloMatrix_boundaryReward`.

Two things follow.

* `svQuittingTailPersistentlySolo` is `quittingTailPersistentlySolo_of_zeroFree`
  with every hypothesis supplied, including the window-extraction hypothesis:
  on this tail only `quitter` is ever active, so extraction holds vacuously.
* `svSoloWindowCharge_le` instantiates the effective charge budget
  `quittingSoloWindowCharge_le_of_margin` at `margin = 1`, and
  `svQuittingSoloWindowCharge` / `svQuittingSoloWindowMesh` evaluate both of
  its sides in closed rational form.

The tail is solo by construction, so the conclusions it certifies are
degenerate: `svIsEmpty_quittingFencedSoloWindowFamily` shows no fenced solo
window family for a distinct pair exists over it, and the only windows to
which the charge budget applies are those of length zero.  What this module
records is therefore the joint consistency of the hypotheses, not the
sharpness of the conclusions.  `svExists_charge_gt_mul_mesh` separates the two
readings: the closed-form charge of a long window exceeds any fixed multiple
of its mesh, so the budget is not an arithmetic identity satisfied by the
tail's window statistics at large.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability QuittingLCPClassification
open SolanVieilleBoundary SourceMatchedSnellCollapse

namespace DiffuseTailNonvacuity

/-! ## Only the designated quitter is ever active -/

/-- A date at which `who` quits with positive probability identifies `who` as
the tail's designated quitter. -/
theorem eq_quitter_of_svRoots_active {time : ℕ} {who : Player}
    (hactive : 0 < (svRoots time who true).toReal) : who = quitter := by
  by_contra hne
  rw [svRoots_of_ne time hne] at hactive
  simp at hactive

/-- The designated quitter is active at every date. -/
theorem svRoots_quitter_active (time : ℕ) :
    0 < (svRoots time quitter true).toReal := by
  have hvalue : (svRoots time quitter true).toReal = svHazard time :=
    hazardOfRoot_svRoots_quitter time
  have htime : (0 : ℝ) ≤ (time : ℝ) := Nat.cast_nonneg time
  rw [hvalue, svHazard]
  positivity

/-- Persistent activity on this tail singles out the designated quitter. -/
theorem svQuittingTailPersistentlyActive_iff (who : Player) :
    QuittingTailPersistentlyActive svRoots who ↔ who = quitter := by
  constructor
  · intro hactive
    obtain ⟨time, -, hquit⟩ := hactive 0
    exact eq_quitter_of_svRoots_active hquit
  · rintro rfl
    exact fun start => ⟨start, le_refl start, svRoots_quitter_active start⟩

/-! ## The hypothesis bundle -/

/-- Boundary tightness at every persistently active player: the phantom
boundary's quitter coordinate is the quitter's own singleton reward. -/
theorem svBoundary_eq_soloReward_of_persistentlyActive (who : Player)
    (hactive : QuittingTailPersistentlyActive svRoots who) :
    svBoundary who = quittingSoloReward boundaryReward who who := by
  rw [(svQuittingTailPersistentlyActive_iff who).1 hactive, soloReward_self]
  rfl

/-- The window-extraction hypothesis holds vacuously: no two distinct players
are both persistently active on this tail. -/
theorem svQuittingSoloWindowExtraction : QuittingSoloWindowExtraction svRoots := by
  intro first second hne hfirst hsecond
  exact absurd (((svQuittingTailPersistentlyActive_iff first).1 hfirst).trans
    ((svQuittingTailPersistentlyActive_iff second).1 hsecond).symm) hne

/-- **The bundle is satisfiable.**  Every hypothesis of the conditional
eventually-solo theorem `quittingTailPersistentlySolo_of_zeroFree` is met by
the solo-hazard tail over the Solan--Vieille boundary table, so its conclusion
holds there unconditionally. -/
theorem svQuittingTailPersistentlySolo : QuittingTailPersistentlySolo svRoots :=
  quittingTailPersistentlySolo_of_zeroFree svRoots svValue svBoundary svPolicy
    svEndpointNash (abs_reward_le_quittingRewardBound boundaryReward)
    svEventualAbsorption_pos svConditionedAbsorptionWeight_tendsto
    svBoundary_eq_soloReward_of_persistentlyActive
    quittingZeroFreeSoloMatrix_boundaryReward
    svQuittingSoloWindowExtraction

/-! ## Closed forms for the window statistics -/

/-- The conditioned survival product of the tail telescopes. -/
theorem svConditionedSurvivalProduct (start length : ℕ) :
    quittingTailConditionedSurvivalProduct svRoots start length =
      ((start : ℝ) + 1) / ((start : ℝ) + length + 1) := by
  have hstart : (0 : ℝ) ≤ (start : ℝ) := Nat.cast_nonneg start
  induction length with
  | zero =>
      have h1 : (start : ℝ) + 1 ≠ 0 := by positivity
      simp only [quittingTailConditionedSurvivalProduct, Finset.range_zero,
        Finset.prod_empty, Nat.cast_zero, add_zero]
      field_simp
  | succ length ih =>
      have hlength : (0 : ℝ) ≤ (length : ℝ) := Nat.cast_nonneg length
      have hweight : quittingTailConditionedAbsorptionWeight svRoots
          (start + length) = 1 / ((start : ℝ) + length + 2) := by
        rw [svConditionedAbsorptionWeight]
        push_cast
        ring_nf
      have h1 : (start : ℝ) + length + 1 ≠ 0 := by positivity
      have h2 : (start : ℝ) + length + 2 ≠ 0 := by positivity
      simp only [quittingTailConditionedSurvivalProduct,
        Finset.prod_range_succ] at ih ⊢
      rw [ih, hweight]
      push_cast
      field_simp
      ring

/-- Closed form of the window charge: a window of `length` solo dates opened
at `fence` absorbs the conditioned share `length / (fence + length + 2)`. -/
theorem svQuittingSoloWindowCharge (fence length : ℕ) :
    quittingSoloWindowCharge svRoots fence length =
      (length : ℝ) / ((fence : ℝ) + length + 2) := by
  have hfence : (0 : ℝ) ≤ (fence : ℝ) := Nat.cast_nonneg fence
  have hlength : (0 : ℝ) ≤ (length : ℝ) := Nat.cast_nonneg length
  have h2 : (fence : ℝ) + length + 2 ≠ 0 := by positivity
  rw [quittingSoloWindowCharge, svConditionedSurvivalProduct]
  push_cast
  field_simp
  ring

/-- Closed form of the window mesh: the fence mesh plus the return mesh. -/
theorem svQuittingSoloWindowMesh (fence length : ℕ) :
    quittingSoloWindowMesh svRoots fence length =
      1 / ((fence : ℝ) + 2) + 1 / ((fence : ℝ) + length + 3) := by
  rw [quittingSoloWindowMesh, svConditionedAbsorptionWeight,
    svConditionedAbsorptionWeight]
  push_cast
  ring_nf

/-! ## The instantiated charge budget at margin one -/

/-- No fenced solo window family for a distinct pair exists over this tail:
its fences force the spectator to be the designated quitter and its interiors
force the owner to be the designated quitter as well. -/
theorem svIsEmpty_quittingFencedSoloWindowFamily {spectator owner : Player}
    (hne : spectator ≠ owner) :
    IsEmpty (QuittingFencedSoloWindowFamily svRoots spectator owner) := by
  refine ⟨fun family => hne ?_⟩
  have hspectator : spectator = quitter :=
    eq_quitter_of_svRoots_active (family.fence_active 0)
  have howner : owner = quitter :=
    eq_quitter_of_svRoots_active (family.window_active 0 0 (family.length_pos 0))
  rw [hspectator, howner]

/-- **The charge budget at `margin = 1`.**  Over the Solan--Vieille boundary
table the designated quitter fences a window of length zero at every date, and
the effective charge bound of `quittingSoloWindowCharge_le_of_margin` applies
there with the table's zero-free margin `1`. -/
theorem svSoloWindowCharge_le {owner : Player} (hne : owner ≠ quitter)
    (fence : ℕ) :
    quittingSoloWindowCharge svRoots fence 0 ≤
      8 * quittingRewardBound boundaryReward *
        quittingSoloWindowMesh svRoots fence 0 := by
  have hfence : (0 : ℝ) ≤ (fence : ℝ) := Nat.cast_nonneg fence
  have hhalf : quittingTailConditionedAbsorptionWeight svRoots fence ≤ 1 / 2 := by
    rw [svConditionedAbsorptionWeight]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  rw [show 8 * quittingRewardBound boundaryReward =
    8 * quittingRewardBound boundaryReward / 1 from (div_one _).symm]
  exact quittingSoloWindowCharge_le_of_margin svRoots svValue svBoundary svPolicy
    svEndpointNash (abs_reward_le_quittingRewardBound boundaryReward)
    svEventualAbsorption_pos quitter owner
    (svBoundary_eq_soloReward_of_persistentlyActive quitter
      ((svQuittingTailPersistentlyActive_iff quitter).2 rfl))
    one_pos (one_le_abs_normalizedSoloMatrix_boundaryReward (Ne.symm hne))
    fence 0 hhalf
    (svRoots_quitter_active fence) (svRoots_quitter_active (fence + 1 + 0))
    (fun offset hoffset => absurd hoffset (Nat.not_lt_zero offset))
    (fun offset hoffset => absurd hoffset (Nat.not_lt_zero offset))

/-- The budget is not an arithmetic identity of the tail's window statistics:
for every constant, some window of the closed-form family absorbs more charge
than that constant times its mesh.  So the charge bound constrains which
windows a tail can carry rather than holding for the closed-form pair at
large. -/
theorem svExists_charge_gt_mul_mesh (constant : ℝ) :
    ∃ fence length : ℕ, constant * quittingSoloWindowMesh svRoots fence length <
      quittingSoloWindowCharge svRoots fence length := by
  obtain ⟨fence, hfence⟩ := exists_nat_gt (4 * constant)
  refine ⟨fence, fence + 2, ?_⟩
  have hcast : (0 : ℝ) ≤ (fence : ℝ) := Nat.cast_nonneg fence
  have hpos2 : (0 : ℝ) < (fence : ℝ) + 2 := by positivity
  have hpos5 : (0 : ℝ) < 2 * (fence : ℝ) + 5 := by positivity
  have hcharge : quittingSoloWindowCharge svRoots fence (fence + 2) = 1 / 2 := by
    rw [svQuittingSoloWindowCharge]
    push_cast
    rw [div_eq_div_iff (by positivity) (by norm_num)]
    ring
  have hmesh : quittingSoloWindowMesh svRoots fence (fence + 2) =
      1 / ((fence : ℝ) + 2) + 1 / (2 * (fence : ℝ) + 5) := by
    rw [svQuittingSoloWindowMesh]
    push_cast
    ring_nf
  have hsmall : 1 / (2 * (fence : ℝ) + 5) ≤ 1 / ((fence : ℝ) + 2) :=
    one_div_le_one_div_of_le hpos2 (by linarith)
  have hbound : quittingSoloWindowMesh svRoots fence (fence + 2) ≤
      2 / ((fence : ℝ) + 2) := by
    rw [hmesh]
    have hhalf : (2 : ℝ) / ((fence : ℝ) + 2) =
        1 / ((fence : ℝ) + 2) + 1 / ((fence : ℝ) + 2) := by ring
    rw [hhalf]
    linarith
  rw [hcharge]
  rcases le_or_gt constant 0 with hconstant | hconstant
  · have hmeshNonneg : 0 ≤ quittingSoloWindowMesh svRoots fence (fence + 2) :=
      quittingSoloWindowMesh_nonneg svRoots svEventualAbsorption_pos fence
        (fence + 2)
    nlinarith
  · have hscaled : constant * quittingSoloWindowMesh svRoots fence (fence + 2) ≤
        constant * (2 / ((fence : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_left hbound hconstant.le
    have hstrict : constant * (2 / ((fence : ℝ) + 2)) < 1 / 2 := by
      rw [show constant * (2 / ((fence : ℝ) + 2)) =
        2 * constant / ((fence : ℝ) + 2) from by ring, div_lt_iff₀ hpos2]
      linarith
    linarith

end DiffuseTailNonvacuity

end GameTheory
