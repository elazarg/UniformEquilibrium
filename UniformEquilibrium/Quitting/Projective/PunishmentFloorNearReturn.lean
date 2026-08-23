/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.CollisionMass
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorAdmissibleChargedRelation
import UniformEquilibrium.Quitting.Projective.ForwardBlockSingleSeam

/-!
# Payoff near-returns in the punishment-floor relation

An exact path in the full punishment-floor admissible relation can be read
backwards as a chronological lasso.  Equality, or even closeness, of the
stored root coordinates at the two endpoints is unnecessary: only the payoff
vectors enter the unique closing Bellman seam.

If one path edge has absorption charge at least a fixed `c > 0`, then the
whole reversed block has weighted absorption at least `c`.  Endpoint payoff
closeness at scale `error * c` therefore pays for the closing seam at scale
`error`.  Exact Nash along the path supplies the remaining support slack, and
floor admissibility supplies rationality.

This file is a consumer of exact payoff near-return paths.  It does not
construct such paths.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget Math.Probability Math.PMFProduct
open QuittingPunishmentFloorAdmissibleChargedRelation

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

private abbrev AdmissibleRelation :=
  quittingPunishmentFloorAdmissibleChargedRelation reward

namespace QuittingPunishmentFloorBoxPath

private abbrev BoxRelation :=
  quittingPunishmentFloorBoxChargedRelation reward

/-- The final decoded payoff is the payoff component of the path target. -/
@[simp] theorem value_length
    {source target : QuittingPunishmentFloorBoxState reward}
    (path : BoxRelation.Path source target) :
    value path path.length = target.1.1 := by
  induction path with
  | nil state => rfl
  | cons edge rest ih =>
      simpa only [ChargedRelation.Path.length_cons, value] using ih

end QuittingPunishmentFloorBoxPath

namespace QuittingPunishmentFloorAdmissibleChargedRelation

/-- Forgetting floor proofs preserves the number of edges. -/
@[simp] theorem length_pathToBoxPath
    {source target : QuittingPunishmentFloorAdmissibleState reward}
    (path : AdmissibleRelation.Path source target) :
    (pathToBoxPath path).length = path.length := by
  induction path with
  | nil state => rfl
  | cons edge rest ih =>
      change (pathToBoxPath rest).length + 1 = rest.length + 1
      rw [ih]

/-- The decoded prefix has exactly one stage per charged-relation edge. -/
@[simp] theorem pathToFinitePrefix_horizon
    {source target : QuittingPunishmentFloorAdmissibleState reward}
    (path : AdmissibleRelation.Path source target) :
    (pathToFinitePrefix path).horizon = path.length := by
  exact length_pathToBoxPath path

/-- The first decoded stage of a nonempty path is the charge-carrying root of
its first relation edge. -/
@[simp] theorem pathToFinitePrefix_roots_cons_zero
    (edge : QuittingPunishmentFloorAdmissibleEdge reward)
    {target : QuittingPunishmentFloorAdmissibleState reward}
    (rest : AdmissibleRelation.Path
      ((quittingPunishmentFloorAdmissibleChargedRelation reward).tgt edge)
      target) :
    (pathToFinitePrefix (ChargedRelation.Path.cons edge rest)).roots 0 =
      edge.toBoxEdge.root := rfl

/-- Removing the first decoded stage exposes the decoded roots of the
remaining path. -/
@[simp] theorem pathToFinitePrefix_roots_cons_succ
    (edge : QuittingPunishmentFloorAdmissibleEdge reward)
    {target : QuittingPunishmentFloorAdmissibleState reward}
    (rest : AdmissibleRelation.Path
      ((quittingPunishmentFloorAdmissibleChargedRelation reward).tgt edge)
      target)
    (time : ℕ) :
    (pathToFinitePrefix (ChargedRelation.Path.cons edge rest)).roots (time + 1) =
      (pathToFinitePrefix rest).roots time := rfl

/-- Decoding an admissible path preserves its final payoff exactly. -/
@[simp] theorem pathToFinitePrefix_value_horizon
    {source target : QuittingPunishmentFloorAdmissibleState reward}
    (path : AdmissibleRelation.Path source target) :
    (pathToFinitePrefix path).value (pathToFinitePrefix path).horizon =
      target.1.1.1 := by
  exact QuittingPunishmentFloorBoxPath.value_length (pathToBoxPath path)

/-- The decoder-side form of a high-charge edge: one displayed Bellman stage
has at least the given absorption mass. -/
def DecodedPathHasChargeAtLeast
    {source target : QuittingPunishmentFloorAdmissibleState reward}
    (path : AdmissibleRelation.Path source target) (threshold : ℝ) : Prop :=
    ∃ time, time < (pathToFinitePrefix path).horizon ∧
      threshold ≤ quittingRootAbsorptionMass
        ((pathToFinitePrefix path).roots time)

/-- A positive relation-level high-charge count is exactly the assertion that
some charged edge reaches the threshold.  Decoding exposes that edge as a
Bellman stage with the same literal absorption charge. -/
theorem decodedPathHasChargeAtLeast_of_highChargeCount_pos
    {source target : QuittingPunishmentFloorAdmissibleState reward}
    (path : AdmissibleRelation.Path source target) (threshold : ℝ)
    (hcount : 0 < path.highChargeCount threshold) :
    DecodedPathHasChargeAtLeast path threshold := by
  induction path with
  | nil state => simp at hcount
  | cons edge rest ih =>
      by_cases hedge : threshold ≤
          (quittingPunishmentFloorAdmissibleChargedRelation reward).charge edge
      · refine ⟨0, ?_, ?_⟩
        · rw [pathToFinitePrefix_horizon,
            ChargedRelation.Path.length_cons]
          omega
        · rw [pathToFinitePrefix_roots_cons_zero]
          exact hedge
      · have hrest : 0 < rest.highChargeCount threshold := by
          simpa [ChargedRelation.Path.highChargeCount_cons, hedge] using hcount
        obtain ⟨time, htime, hcharge⟩ := ih hrest
        refine ⟨time + 1, ?_, ?_⟩
        · rw [pathToFinitePrefix_horizon,
            ChargedRelation.Path.length_cons]
          rw [pathToFinitePrefix_horizon] at htime
          omega
        · rw [pathToFinitePrefix_roots_cons_succ]
          exact hcharge

/-- The decoded-stage condition also detects a high relation edge. -/
theorem highChargeCount_pos_of_decodedPathHasChargeAtLeast
    {source target : QuittingPunishmentFloorAdmissibleState reward}
    (path : AdmissibleRelation.Path source target) (threshold : ℝ)
    (hstage : DecodedPathHasChargeAtLeast path threshold) :
    0 < path.highChargeCount threshold := by
  induction path with
  | nil state =>
      obtain ⟨time, htime, _⟩ := hstage
      rw [pathToFinitePrefix_horizon] at htime
      simp at htime
  | cons edge rest ih =>
      obtain ⟨time, htime, hcharge⟩ := hstage
      cases time with
      | zero =>
          have hedge : threshold ≤
              (quittingPunishmentFloorAdmissibleChargedRelation reward).charge
                edge := by
            rw [pathToFinitePrefix_roots_cons_zero] at hcharge
            exact hcharge
          simp [ChargedRelation.Path.highChargeCount_cons, hedge]
      | succ time =>
          have hrest : DecodedPathHasChargeAtLeast rest threshold := by
            refine ⟨time, ?_, ?_⟩
            · rw [pathToFinitePrefix_horizon]
              rw [pathToFinitePrefix_horizon,
                ChargedRelation.Path.length_cons] at htime
              omega
            · rw [pathToFinitePrefix_roots_cons_succ] at hcharge
              exact hcharge
          have ihigh := ih hrest
          by_cases hedge : threshold ≤
              (quittingPunishmentFloorAdmissibleChargedRelation reward).charge
                edge
          · simp [ChargedRelation.Path.highChargeCount_cons, hedge]
          · simpa [ChargedRelation.Path.highChargeCount_cons, hedge] using ihigh

/-- Relation-level high-edge counts and decoded high-charge stages are exact
equivalent views of the same path event. -/
theorem highChargeCount_pos_iff_decodedPathHasChargeAtLeast
    {source target : QuittingPunishmentFloorAdmissibleState reward}
    (path : AdmissibleRelation.Path source target) (threshold : ℝ) :
    0 < path.highChargeCount threshold ↔
      DecodedPathHasChargeAtLeast path threshold :=
  ⟨decodedPathHasChargeAtLeast_of_highChargeCount_pos path threshold,
    highChargeCount_pos_of_decodedPathHasChargeAtLeast path threshold⟩

end QuittingPunishmentFloorAdmissibleChargedRelation

omit [DecidableEq ι] in
/-- One stage's absorption is bounded by the aggregate weighted absorption of
the entire finite block. -/
theorem quittingRootAbsorptionMass_le_reversedForwardWeightedAbsorption
    (roots : ℕ → ι → PMF Bool) (horizon time : ℕ)
    (htime : time < horizon) :
    quittingRootAbsorptionMass (roots time) ≤
      quittingCyclicWeightedAbsorption
        (quittingReversedForwardCycle roots 0 (horizon - 1)) := by
  let q : Fin horizon → ℝ := fun phase =>
    quittingRootAbsorptionMass (roots phase)
  have hq0 : ∀ phase ∈ (Finset.univ : Finset (Fin horizon)), 0 ≤ q phase := by
    intro phase _
    exact quittingRootAbsorptionMass_nonneg _
  have hq1 : ∀ phase ∈ (Finset.univ : Finset (Fin horizon)), q phase ≤ 1 := by
    intro phase _
    unfold q quittingRootAbsorptionMass
    linarith [quittingStationaryContinueMass_nonneg (roots phase)]
  have hcoordinate := coordinate_le_one_sub_prod_one_sub q Finset.univ
    hq0 hq1 (Finset.mem_univ ⟨time, htime⟩)
  have hlength : horizon - 1 + 1 = horizon := by omega
  rw [quittingCyclicWeightedAbsorption_reversedForwardCycle, hlength]
  simp only [zero_add]
  rw [← Fin.prod_univ_eq_prod_range
    (fun offset => 1 - quittingRootAbsorptionMass (roots offset)) horizon]
  exact hcoordinate

/-- **One exact punishment-floor prefix with a charged payoff near-return
gives a single-seam lasso.** -/
theorem exists_singleSeamProjectiveLasso_of_floorPrefix_payoffNearReturn
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (chargeThreshold seamError error : ℝ)
    (hchargeThreshold : 0 < chargeThreshold)
    (hseamError : 0 ≤ seamError)
    (hseamScale : seamError ≤ error * chargeThreshold)
    (hclose : ∀ who,
      |cert.value 0 who - cert.value cert.horizon who| ≤ seamError)
    (hhigh : ∃ stage, stage < cert.horizon ∧
      chargeThreshold ≤ quittingRootAbsorptionMass (cert.roots stage)) :
    ∃ K : ℕ,
      Nonempty (QuittingFiniteSingleSeamProjectiveLasso reward K error) := by
  obtain ⟨stage, hstage, hstageCharge⟩ := hhigh
  have hthresholdLeOne : chargeThreshold ≤ 1 := by
    calc
      chargeThreshold ≤ quittingRootAbsorptionMass (cert.roots stage) :=
        hstageCharge
      _ ≤ 1 := by
        unfold quittingRootAbsorptionMass
        linarith [quittingStationaryContinueMass_nonneg (cert.roots stage)]
  have herror : 0 ≤ error := by
    by_contra herror
    have hproductNeg : error * chargeThreshold < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge herror) hchargeThreshold
    linarith
  let supportError := error - seamError
  have hsupportError : 0 ≤ supportError := by
    dsimp only [supportError]
    have hseamLeError : seamError ≤ error := by
      calc
        seamError ≤ error * chargeThreshold := hseamScale
        _ ≤ error * 1 := mul_le_mul_of_nonneg_left hthresholdLeOne herror
        _ = error := mul_one _
    linarith
  let n := cert.horizon - 1
  have hlength : n + 1 = cert.horizon := by
    dsimp only [n]
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le stage) hstage)))
  have hpolicy : ∀ time,
      0 ≤ time → time < 0 + n + 1 →
      cert.value (time + 1) = quittingRootSuccessorPayoff reward
        (cert.value time) (cert.roots time) := by
    intro time _ htime
    exact cert.policy time (by simpa only [zero_add, hlength] using htime)
  have hsupport : ∀ time,
      0 ≤ time → time < 0 + n + 1 →
      IsQuittingRootSupportApproxNash reward
        (cert.value time) supportError (cert.roots time) := by
    intro time _ htime
    have hexact := isQuittingRootSupportApproxNash_zero_of_isZeroNash
      reward (cert.value time) (cert.roots time)
      (cert.exactNash time (by simpa only [zero_add, hlength] using htime))
    intro who
    constructor
    · intro hquit
      linarith [((hexact who).1 hquit)]
    · intro hcontinue
      linarith [((hexact who).2 hcontinue)]
  have hdecodedClose : ∀ who,
      |cert.value 0 who - cert.value (0 + n + 1) who| ≤ seamError := by
    intro who
    rw [zero_add, hlength]
    exact hclose who
  have hweighted : chargeThreshold ≤
      quittingCyclicWeightedAbsorption
        (quittingReversedForwardCycle cert.roots 0 n) := by
    calc
      chargeThreshold ≤ quittingRootAbsorptionMass (cert.roots stage) :=
        hstageCharge
      _ ≤ quittingCyclicWeightedAbsorption
          (quittingReversedForwardCycle cert.roots 0 (cert.horizon - 1)) :=
        quittingRootAbsorptionMass_le_reversedForwardWeightedAbsorption
          cert.roots cert.horizon stage hstage
      _ = quittingCyclicWeightedAbsorption
          (quittingReversedForwardCycle cert.roots 0 n) := rfl
  have hclosingRatio : seamError ≤
      (supportError + seamError) *
        quittingCyclicWeightedAbsorption
          (quittingReversedForwardCycle cert.roots 0 n) := by
    have htotal : supportError + seamError = error := by
      dsimp only [supportError]
      ring
    rw [htotal]
    exact hseamScale.trans (mul_le_mul_of_nonneg_left hweighted herror)
  have hrational : ∀ targetWho time,
      0 < time → time ≤ 0 + n + 1 →
      quittingPunishmentValue reward targetWho -
          (supportError + seamError) ≤ cert.value time targetWho := by
    intro targetWho time _ htime
    have hfloor := quittingPunishmentValue_le_finitePrefixValue
      cert time (by simpa only [zero_add, hlength] using htime) targetWho
    linarith [hfloor, herror]
  let rawPhase : Fin (n + 1) :=
    ⟨stage, by simpa only [hlength] using hstage⟩
  let absorbingPhase : Fin (n + 1) := rawPhase.rev
  have habsorbing : 0 < quittingRootAbsorptionMass
      (quittingReversedForwardCycle cert.roots 0 n absorbingPhase) := by
    have hstagePositive : 0 < quittingRootAbsorptionMass (cert.roots stage) :=
      hchargeThreshold.trans_le hstageCharge
    simpa [quittingReversedForwardCycle, absorbingPhase, rawPhase] using
      hstagePositive
  let lasso :=
    quittingFiniteSingleSeamProjectiveLasso_of_reversedForwardBlock
      reward cert.roots cert.value 0 n
      (supportError := supportError) (seamError := seamError)
      hsupportError hseamError hpolicy hsupport hdecodedClose hclosingRatio
      hrational absorbingPhase habsorbing
  refine ⟨n + 1, ?_⟩
  have htotal : supportError + seamError = error := by
    dsimp only [supportError]
    ring
  rw [← htotal]
  exact ⟨lasso⟩

/-- **One exact charged payoff near-return gives a single-seam lasso.**

The endpoint assumption concerns payoff vectors only.  In particular, the
stored root coordinates of `source` and `target` need not agree or be close. -/
theorem exists_singleSeamProjectiveLasso_of_admissiblePath_payoffNearReturn
    (source target : QuittingPunishmentFloorAdmissibleState reward)
    (path : AdmissibleRelation.Path source target)
    (chargeThreshold seamError error : ℝ)
    (hchargeThreshold : 0 < chargeThreshold)
    (hseamError : 0 ≤ seamError)
    (hseamScale : seamError ≤ error * chargeThreshold)
    (hclose : ∀ who,
      |source.1.1.1 who - target.1.1.1 who| ≤ seamError)
    (hhigh : 0 < path.highChargeCount chargeThreshold) :
    ∃ K : ℕ,
      Nonempty (QuittingFiniteSingleSeamProjectiveLasso reward K error) := by
  let cert := pathToFinitePrefix path
  apply exists_singleSeamProjectiveLasso_of_floorPrefix_payoffNearReturn
    cert chargeThreshold seamError error hchargeThreshold hseamError hseamScale
  · intro who
    have hzero : cert.value 0 = source.1.1.1 := by
      exact QuittingPunishmentFloorBoxPath.value_zero (pathToBoxPath path)
    have hfinal : cert.value cert.horizon = target.1.1.1 :=
      pathToFinitePrefix_value_horizon path
    rw [hzero, hfinal]
    exact hclose who
  · exact decodedPathHasChargeAtLeast_of_highChargeCount_pos
      path chargeThreshold hhigh

/-- A fixed positive charge scale together with exact floor-admissible payoff
near-returns at every endpoint tolerance.  The source, target, path, and
charged edge may all vary with the tolerance. -/
structure QuittingPositiveAdmissiblePayoffNearReturnFamily
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  chargeThreshold : ℝ
  charge_pos : 0 < chargeThreshold
  nearReturn : ∀ endpointError : ℝ, 0 < endpointError →
    ∃ (source target : QuittingPunishmentFloorAdmissibleState reward)
      (path : (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
        source target),
      (∀ who, |source.1.1.1 who - target.1.1.1 who| ≤ endpointError) ∧
      0 < path.highChargeCount chargeThreshold

/-- **Fixed charged payoff near-returns at every scale imply a uniform
equilibrium payoff.**

The producer may return different paths and endpoint states at different
scales.  It is only asked to keep one positive edge-charge threshold and make
the endpoint payoff vectors arbitrarily close. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_admissiblePath_payoffNearReturns
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (chargeThreshold : ℝ) (hchargeThreshold : 0 < chargeThreshold)
    (hproducer : ∀ endpointError : ℝ, 0 < endpointError →
      ∃ (source target : QuittingPunishmentFloorAdmissibleState reward)
        (path : (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
          source target),
        (∀ who, |source.1.1.1 who - target.1.1.1 who| ≤ endpointError) ∧
        0 < path.highChargeCount chargeThreshold) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have hsampleError : 0 < chargeThreshold := hchargeThreshold
  obtain ⟨sampleSource, sampleTarget, samplePath, _hsampleClose,
      hsampleHigh⟩ := hproducer chargeThreshold hsampleError
  letI : Nonempty ι := by
    rcases isEmpty_or_nonempty ι with hempty | hnonempty
    · letI : IsEmpty ι := hempty
      obtain ⟨stage, _hstage, hstageCharge⟩ :=
        decodedPathHasChargeAtLeast_of_highChargeCount_pos
          samplePath chargeThreshold hsampleHigh
      have hroot :
          (pathToFinitePrefix samplePath).roots stage =
            quittingAllContinueRoot := by
        funext who
        exact isEmptyElim who
      rw [hroot, quittingRootAbsorptionMass_allContinueRoot] at hstageCharge
      linarith
    · exact hnonempty
  apply quittingGame_exists_uniformEquilibriumPayoff_of_singleSeamProjectiveLassos
    reward
  intro error herror
  have hendpointError : 0 < error * chargeThreshold :=
    mul_pos herror hchargeThreshold
  obtain ⟨source, target, path, hclose, hhigh⟩ :=
    hproducer (error * chargeThreshold) hendpointError
  exact exists_singleSeamProjectiveLasso_of_admissiblePath_payoffNearReturn
    source target path chargeThreshold (error * chargeThreshold) error
    hchargeThreshold (mul_nonneg herror.le hchargeThreshold.le) le_rfl hclose
    hhigh

namespace QuittingPositiveAdmissiblePayoffNearReturnFamily

/-- The packaged varying-edge payoff-near-return family is a direct uniform
payoff certificate. -/
theorem exists_uniformEquilibriumPayoff
    (result : QuittingPositiveAdmissiblePayoffNearReturnFamily reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_admissiblePath_payoffNearReturns
    reward result.chargeThreshold result.charge_pos result.nearReturn

/-- A fixed positive edge with payoff closure is a special case of the
varying-edge payoff-near-return family. -/
def ofPositiveEdgePayoffClosure
    (edge : QuittingPunishmentFloorAdmissibleEdge reward)
    (hcharge : 0 < edge.toBoxEdge.absorptionCharge)
    (hclosure : ∀ endpointError : ℝ, 0 < endpointError →
      ∃ (target : QuittingPunishmentFloorAdmissibleState reward)
        (_path : (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
          edge.current target),
        ∀ who,
          |edge.tail.1.1.1 who - target.1.1.1 who| ≤ endpointError) :
    QuittingPositiveAdmissiblePayoffNearReturnFamily reward where
  chargeThreshold := edge.toBoxEdge.absorptionCharge
  charge_pos := hcharge
  nearReturn := by
    intro endpointError hendpointError
    obtain ⟨target, path, hclose⟩ := hclosure endpointError hendpointError
    let relation := quittingPunishmentFloorAdmissibleChargedRelation reward
    let rest : relation.Path (relation.tgt edge) target :=
      path.castSrc (by rfl)
    let fullPath : relation.Path edge.tail target :=
      ChargedRelation.Path.cons edge rest
    refine ⟨edge.tail, target, fullPath, hclose, ?_⟩
    have hedge : edge.toBoxEdge.absorptionCharge ≤ relation.charge edge :=
      le_rfl
    apply highChargeCount_pos_of_decodedPathHasChargeAtLeast
    refine ⟨0, ?_, ?_⟩
    · rw [pathToFinitePrefix_horizon]
      change 0 < (ChargedRelation.Path.cons edge rest).length
      simp only [ChargedRelation.Path.length_cons]
      omega
    · change edge.toBoxEdge.absorptionCharge ≤
        quittingRootAbsorptionMass
          ((pathToFinitePrefix (ChargedRelation.Path.cons edge rest)).roots 0)
      rw [pathToFinitePrefix_roots_cons_zero]
      exact hedge

end QuittingPositiveAdmissiblePayoffNearReturnFamily

/-- **Fixed positive edge with payoff closure.**

It is enough that the payoff of `edge.tail` be approximated arbitrarily well
by payoff projections of states reachable from `edge.current`.  Prepending
the fixed edge supplies the common positive charge required by the payoff
near-return theorem.  No stored root coordinate is required to recur. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_positiveEdge_payoffClosure
    (edge : QuittingPunishmentFloorAdmissibleEdge reward)
    (hcharge : 0 < edge.toBoxEdge.absorptionCharge)
    (hclosure : ∀ endpointError : ℝ, 0 < endpointError →
      ∃ (target : QuittingPunishmentFloorAdmissibleState reward)
        (_path : (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
          edge.current target),
        ∀ who,
          |edge.tail.1.1.1 who - target.1.1.1 who| ≤ endpointError) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  exact
    (QuittingPositiveAdmissiblePayoffNearReturnFamily.ofPositiveEdgePayoffClosure
      edge hcharge hclosure).exists_uniformEquilibriumPayoff

end GameTheory
