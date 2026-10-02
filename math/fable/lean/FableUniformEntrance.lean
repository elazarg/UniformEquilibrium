/-
Uniform prefix-survival lower bound for exact punishment-floor prefixes.

A terminal exploitability gap caps every marginal Quit probability of an exact
punishment-rational root, so each certified prefix stage keeps a fixed positive
share of the live mass.  The canonical prefix-charge bound then controls the
total absorption of the whole prefix, and an elementary product-versus-sum
estimate turns those two facts into one horizon-free lower bound on the joint
survival product of the prefix.
-/
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityWitness
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.TerminalGapExactRootMarginalCap

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Elementary product-versus-sum estimate.  Factors that are bounded away
from `1` by a fixed margin `η` and whose total mass is at most `B` leave a
survival product at least `exp (-(B / η))`, uniformly in the number of
factors. -/
theorem prod_one_sub_ge_exp_neg_div
    (a : ℕ → ℝ) (H : ℕ) (η B : ℝ) (hη : 0 < η)
    (ha : ∀ t, t < H → 0 ≤ a t ∧ a t ≤ 1 - η)
    (hsum : (∑ t ∈ Finset.range H, a t) ≤ B) :
    Real.exp (-(B / η)) ≤ ∏ t ∈ Finset.range H, (1 - a t) := by
  have hterm : ∀ t ∈ Finset.range H, Real.exp (-(a t / η)) ≤ 1 - a t := by
    intro t ht
    obtain ⟨hnonneg, hcap⟩ := ha t (Finset.mem_range.mp ht)
    have hpos : 0 < 1 - a t := by linarith
    have hne : (1 : ℝ) - a t ≠ 0 := ne_of_gt hpos
    have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at hlog
    have hsplit : (1 - a t)⁻¹ - 1 = a t / (1 - a t) := by
      field_simp
      ring
    have hratio : (1 - a t)⁻¹ - 1 ≤ a t / η := by
      rw [hsplit, div_le_div_iff₀ hpos hη]
      nlinarith [mul_nonneg hnonneg (by linarith : (0 : ℝ) ≤ 1 - a t - η)]
    have hbound : -(a t / η) ≤ Real.log (1 - a t) := by linarith
    calc Real.exp (-(a t / η)) ≤ Real.exp (Real.log (1 - a t)) :=
          Real.exp_le_exp.mpr hbound
      _ = 1 - a t := Real.exp_log hpos
  have hsumNeg : (∑ t ∈ Finset.range H, -(a t / η))
      = -((∑ t ∈ Finset.range H, a t) / η) := by
    rw [Finset.sum_div]
    simp
  have hdiv : (∑ t ∈ Finset.range H, a t) / η ≤ B / η :=
    (div_le_div_iff_of_pos_right hη).2 hsum
  calc Real.exp (-(B / η))
      ≤ Real.exp (-((∑ t ∈ Finset.range H, a t) / η)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = ∏ t ∈ Finset.range H, Real.exp (-(a t / η)) := by
        rw [← hsumNeg, Real.exp_sum]
    _ ≤ ∏ t ∈ Finset.range H, (1 - a t) :=
        Finset.prod_le_prod (fun t _ => (Real.exp_pos _).le) hterm

/-- **Uniform entrance bound.**  Under a terminal exploitability witness, the
joint survival product of an exact punishment-floor finite prefix has a
positive lower bound that depends only on the reward bound, the terminal gap,
the number of players, and the canonical prefix-charge bound.  In particular it
is independent of the prefix horizon.

The punishment floor at every certified date is derived from the certificate's
anchor floor and exact edges, so no floor hypothesis is imposed here. -/
theorem QuittingTerminalExploitabilityWitness.uniform_prefixSurvival_lowerBound
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    {M : ℝ} (hM : 0 < M) (hreward : ∀ S player, |reward S player| ≤ M)
    (cert : QuittingPunishmentFloorFinitePrefix reward)
    (hbox : ∀ time, time ≤ cert.horizon → ∀ player,
      |cert.value time player| ≤ M) :
    Real.exp (-(quittingPunishmentFloorPrefixChargeBound reward /
        (witness.terminalGap / (4 * M)) ^ (Fintype.card ι))) ≤
      ∏ time ∈ Finset.range cert.horizon,
        quittingStationaryContinueMass (cert.roots time) := by
  have hqpos : 0 < witness.terminalGap / (4 * M) :=
    div_pos witness.terminalGap_pos (by linarith)
  have hetapos : 0 < (witness.terminalGap / (4 * M)) ^ Fintype.card ι :=
    pow_pos hqpos _
  have hpow : (witness.terminalGap / (4 * M)) ^ Fintype.card ι
      = ∏ _player : ι, witness.terminalGap / (4 * M) := by
    rw [Finset.prod_const, Finset.card_univ]
  have hcontinue : ∀ time, time < cert.horizon →
      (witness.terminalGap / (4 * M)) ^ Fintype.card ι ≤
        quittingStationaryContinueMass (cert.roots time) := by
    intro time htime
    rw [quittingStationaryContinueMass_eq_prod_continueProbability, hpow]
    refine Finset.prod_le_prod (fun player _ => hqpos.le) ?_
    intro player _
    exact terminalGap_div_four_mul_le_exactFloorRoot_continueProbability
      reward (cert.value time) (cert.roots time) player
      witness.terminalGap_pos hreward (hbox time htime.le)
      (fun who => quittingPunishmentValue_le_finitePrefixValue cert time
        htime.le who)
      witness.terminalExploitability (cert.exactNash time htime)
  have hstage : ∀ time, time < cert.horizon →
      0 ≤ quittingRootAbsorptionMass (cert.roots time) ∧
        quittingRootAbsorptionMass (cert.roots time) ≤
          1 - (witness.terminalGap / (4 * M)) ^ Fintype.card ι := by
    intro time htime
    refine ⟨quittingRootAbsorptionMass_nonneg _, ?_⟩
    have habs : quittingRootAbsorptionMass (cert.roots time)
        = 1 - quittingStationaryContinueMass (cert.roots time) := rfl
    rw [habs]
    linarith [hcontinue time htime]
  have hcharge : (∑ time ∈ Finset.range cert.horizon,
      quittingRootAbsorptionMass (cert.roots time)) ≤
        quittingPunishmentFloorPrefixChargeBound reward :=
    witness.prefixCharge_le cert
  have hmain := prod_one_sub_ge_exp_neg_div
    (fun time => quittingRootAbsorptionMass (cert.roots time))
    cert.horizon ((witness.terminalGap / (4 * M)) ^ Fintype.card ι)
    (quittingPunishmentFloorPrefixChargeBound reward) hetapos hstage hcharge
  refine hmain.trans_eq (Finset.prod_congr rfl fun time _ => ?_)
  simp [quittingRootAbsorptionMass]

end GameTheory
