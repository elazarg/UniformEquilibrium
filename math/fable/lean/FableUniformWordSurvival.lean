/-
Table-uniform survival through every finite exact punishment-floor prefix.

This file formalizes the quantitative core (sections 2 and 3) of the note
`CODEX_DESCENDANT__UNIFORM_EXACT_PORT_REACH_AND_POSTMARK_ORIENTATION`, in the
scope confirmed by its `SOCIAL_WEIGHT_REVIEW` review.

Fix a finite quitting reward table carrying a terminal exploitability witness
of gap `γ`.  Write `M` for the canonical reward bound `quittingRewardBound`.
The checked root estimate caps every marginal Quit probability of an exact
punishment-floor root by `1 - γ / (4 * M)`, so every coordinate's Continue
probability is at least the margin `h = γ / (4 * M)`, and the joint
all-Continue mass of one root is at least `r = h ^ card ι`.

The charge of a finite prefix certificate is the sum of its per-stage
absorption masses `1 - c`, and the witness bounds that sum by the canonical
`C = quittingPunishmentFloorPrefixChargeBound`.  Converting each stage by
`-log c ≤ (1 - c) / r`, valid on `[r, 1]`, gives the table-uniform floor

  `∏_{t < N} c (roots t) ≥ exp (-(C / r))`

for every compatible `QuittingPunishmentFloorFinitePrefix` of every depth.

Quantifier discipline.  The floor is stated only over prefix certificates:
the word must carry the certificate's box, anchor-floor, Bellman, and exact
root Nash fields.  Nothing here licenses attaching an unrelated exact root
word to an arbitrary suffix, and nothing here concerns the section 4
composition with the actual-reach paid row.

Everything is stated for a general finite player type; the estimates used do
not specialize to `Fin 4`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.TerminalGapExactRootMarginalCap
import UniformEquilibrium.Quitting.Boundary.Repair.JointComplementarity
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityWitness

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## An elementary charge-to-log conversion -/

/-- On `[floor, 1]` with `0 < floor`, the logarithm is bounded below by the
absorption charge scaled by the floor.  This is the exact form of the note's
inequality `-log c ≤ (1 - c) / r`. -/
theorem fable_neg_charge_div_le_log {floor mass : ℝ}
    (hfloor : 0 < floor) (hle : floor ≤ mass) (hmass : mass ≤ 1) :
    -((1 - mass) / floor) ≤ Real.log mass := by
  have hmassPos : 0 < mass := hfloor.trans_le hle
  have hlog : 1 - mass⁻¹ ≤ Real.log mass :=
    Real.one_sub_inv_le_log_of_pos hmassPos
  have hinv : (mass - 1) / mass = 1 - mass⁻¹ := by
    field_simp
  have hgap : (mass - 1) / floor ≤ (mass - 1) / mass := by
    have hdiff : (mass - 1) / mass - (mass - 1) / floor =
        (1 - mass) * (mass - floor) / (mass * floor) := by
      field_simp
      ring
    have hnonneg : 0 ≤ (1 - mass) * (mass - floor) / (mass * floor) := by
      apply div_nonneg
      · exact mul_nonneg (by linarith) (by linarith)
      · positivity
    linarith
  have hrewrite : -((1 - mass) / floor) = (mass - 1) / floor := by ring
  rw [hrewrite]
  linarith [hgap, hinv ▸ hlog]

namespace QuittingPunishmentFloorFinitePrefix

/-- Every annotated value of a finite exact prefix lies in the canonical
reward box.  This is the certificate's stored `value_mem` field read
coordinatewise. -/
theorem fable_abs_value_le_quittingRewardBound
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (time : ℕ) (htime : time ≤ cert.horizon) (player : ι) :
    |cert.value time player| ≤ quittingRewardBound reward := by
  have hmem : cert.value time ∈ Set.Icc
      (fun _ : ι => -quittingRewardBound reward)
      (fun _ : ι => quittingRewardBound reward) := cert.value_mem time htime
  exact abs_le.mpr ⟨hmem.1 player, hmem.2 player⟩

end QuittingPunishmentFloorFinitePrefix

namespace QuittingTerminalExploitabilityWitness

/-! ## The table-uniform one-root constants -/

/-- The per-coordinate Continue margin `h = γ / (4 * M)` of the note's (2.2),
at the canonical reward bound. -/
def fableRootContinueMargin
    (witness : QuittingTerminalExploitabilityWitness reward) : ℝ :=
  witness.terminalGap / (4 * quittingRewardBound reward)

/-- The joint one-root survival floor `r = h ^ card ι` of the note's (2.2). -/
def fableRootSurvivalFloor
    (witness : QuittingTerminalExploitabilityWitness reward) : ℝ :=
  witness.fableRootContinueMargin ^ Fintype.card ι

/-- The table-uniform word survival floor `λ = exp (-(C / r))` of the note's
(3.3). -/
def fableUniformSurvivalFloor
    (witness : QuittingTerminalExploitabilityWitness reward) : ℝ :=
  Real.exp (-(quittingPunishmentFloorPrefixChargeBound reward /
    witness.fableRootSurvivalFloor))

/-- A positive terminal gap forces a positive canonical reward bound. -/
theorem fable_quittingRewardBound_pos
    (witness : QuittingTerminalExploitabilityWitness reward) :
    0 < quittingRewardBound reward := by
  have hgapBound := terminalExploitabilityGap_le_two_mul_bound
    reward (abs_reward_le_quittingRewardBound reward)
      witness.terminalExploitability
  linarith [witness.terminalGap_pos]

theorem fableRootContinueMargin_pos
    (witness : QuittingTerminalExploitabilityWitness reward) :
    0 < witness.fableRootContinueMargin := by
  unfold fableRootContinueMargin
  exact div_pos witness.terminalGap_pos
    (by linarith [witness.fable_quittingRewardBound_pos])

theorem fableRootSurvivalFloor_pos
    (witness : QuittingTerminalExploitabilityWitness reward) :
    0 < witness.fableRootSurvivalFloor :=
  pow_pos witness.fableRootContinueMargin_pos _

theorem fableUniformSurvivalFloor_pos
    (witness : QuittingTerminalExploitabilityWitness reward) :
    0 < witness.fableUniformSurvivalFloor :=
  Real.exp_pos _

/-! ## One root -/

/-- **Per-root Continue-product floor.**  Under the hypotheses of the checked
root margin -- reward box for the tail, domination of the behavioral
punishment floor, and exact root Nash against that tail -- the joint
all-Continue mass of the root is at least `r`. -/
theorem fableRootSurvivalFloor_le_stationaryContinueMass
    (witness : QuittingTerminalExploitabilityWitness reward)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (htail : ∀ player, |tail player| ≤ quittingRewardBound reward)
    (hfloor : ∀ player, quittingPunishmentValue reward player ≤ tail player)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    witness.fableRootSurvivalFloor ≤ quittingStationaryContinueMass root := by
  have hmargin : ∀ player : ι,
      witness.fableRootContinueMargin ≤ (root player false).toReal := by
    intro player
    exact terminalGap_div_four_mul_le_exactFloorRoot_continueProbability
      reward tail root player witness.terminalGap_pos
      (abs_reward_le_quittingRewardBound reward) htail hfloor
      witness.terminalExploitability hnash
  have hconst : witness.fableRootSurvivalFloor =
      ∏ _player : ι, witness.fableRootContinueMargin := by
    rw [fableRootSurvivalFloor, Finset.prod_const, Finset.card_univ]
  rw [hconst, quittingStationaryContinueMass_eq_prod_continueProbability]
  refine Finset.prod_le_prod (fun player _ => ?_) (fun player _ => ?_)
  · exact witness.fableRootContinueMargin_pos.le
  · exact hmargin player

/-! ## Every finite exact prefix certificate -/

/-- Every stage of a compatible finite exact prefix certificate has joint
Continue mass at least `r`. -/
theorem fableRootSurvivalFloor_le_prefixStationaryContinueMass
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (time : ℕ) (htime : time < cert.horizon) :
    witness.fableRootSurvivalFloor ≤
      quittingStationaryContinueMass (cert.roots time) :=
  witness.fableRootSurvivalFloor_le_stationaryContinueMass
    (cert.value time) (cert.roots time)
    (fun player => cert.fable_abs_value_le_quittingRewardBound time
      htime.le player)
    (fun player => quittingPunishmentValue_le_finitePrefixValue cert time
      htime.le player)
    (cert.exactNash time htime)

/-- **The table-uniform survival floor.**  Every compatible finite exact
punishment-floor prefix certificate, of every depth, survives jointly through
its whole root word with probability at least `λ = exp (-(C / r))`.  The
constant depends only on the reward table and the terminal-gap witness. -/
theorem fableUniformSurvivalFloor_le_prefixContinueProduct
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cert : QuittingPunishmentFloorFinitePrefix reward) :
    witness.fableUniformSurvivalFloor ≤
      ∏ time ∈ Finset.range cert.horizon,
        quittingStationaryContinueMass (cert.roots time) := by
  have hfloorPos := witness.fableRootSurvivalFloor_pos
  have hmass : ∀ time ∈ Finset.range cert.horizon,
      witness.fableRootSurvivalFloor ≤
        quittingStationaryContinueMass (cert.roots time) := by
    intro time htime
    exact witness.fableRootSurvivalFloor_le_prefixStationaryContinueMass cert
      time (Finset.mem_range.mp htime)
  have hpos : ∀ time ∈ Finset.range cert.horizon,
      0 < quittingStationaryContinueMass (cert.roots time) :=
    fun time htime => hfloorPos.trans_le (hmass time htime)
  have hlog : ∀ time ∈ Finset.range cert.horizon,
      -(quittingRootAbsorptionMass (cert.roots time) /
          witness.fableRootSurvivalFloor) ≤
        Real.log (quittingStationaryContinueMass (cert.roots time)) := by
    intro time htime
    have hstage := fable_neg_charge_div_le_log hfloorPos (hmass time htime)
      (quittingStationaryContinueMass_le_one (cert.roots time))
    simpa [quittingRootAbsorptionMass] using hstage
  have hchargeSum : ∑ time ∈ Finset.range cert.horizon,
      -(quittingRootAbsorptionMass (cert.roots time) /
        witness.fableRootSurvivalFloor) =
      -(cert.charge / witness.fableRootSurvivalFloor) := by
    rw [QuittingPunishmentFloorFinitePrefix.charge, Finset.sum_div]
    simp
  have hsum : -(quittingPunishmentFloorPrefixChargeBound reward /
      witness.fableRootSurvivalFloor) ≤
      ∑ time ∈ Finset.range cert.horizon,
        Real.log (quittingStationaryContinueMass (cert.roots time)) := by
    have hlower := Finset.sum_le_sum hlog
    rw [hchargeSum] at hlower
    have hbudget := witness.prefixCharge_le cert
    have hscaled : cert.charge / witness.fableRootSurvivalFloor ≤
        quittingPunishmentFloorPrefixChargeBound reward /
          witness.fableRootSurvivalFloor :=
      div_le_div_of_nonneg_right hbudget hfloorPos.le
    linarith
  calc witness.fableUniformSurvivalFloor
      = Real.exp (-(quittingPunishmentFloorPrefixChargeBound reward /
          witness.fableRootSurvivalFloor)) := rfl
    _ ≤ Real.exp (∑ time ∈ Finset.range cert.horizon,
          Real.log (quittingStationaryContinueMass (cert.roots time))) :=
        Real.exp_le_exp.mpr hsum
    _ = ∏ time ∈ Finset.range cert.horizon,
          Real.exp (Real.log (quittingStationaryContinueMass
            (cert.roots time))) := Real.exp_sum _ _
    _ = ∏ time ∈ Finset.range cert.horizon,
          quittingStationaryContinueMass (cert.roots time) :=
        Finset.prod_congr rfl (fun time htime => Real.exp_log (hpos time htime))

/-- The same floor in the checked joint-survival-weight vocabulary of the
certificate's root sequence. -/
theorem fableUniformSurvivalFloor_le_jointSurvivalWeight
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cert : QuittingPunishmentFloorFinitePrefix reward) :
    witness.fableUniformSurvivalFloor ≤
      quittingJointSurvivalWeight cert.roots 0 cert.horizon := by
  rw [quittingJointSurvivalWeight_eq_prod]
  simpa using witness.fableUniformSurvivalFloor_le_prefixContinueProduct cert

end QuittingTerminalExploitabilityWitness

end GameTheory
