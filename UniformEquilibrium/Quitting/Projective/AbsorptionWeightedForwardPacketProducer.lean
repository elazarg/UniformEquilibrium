import UniformEquilibrium.Quitting.Projective.AbsorptionWeightedForwardPacketRepair

/-! # Weighted and exact finite forward-packet producers -/

noncomputable section

namespace GameTheory

/-- Exact forward packets of every positive accuracy and nonnegative charge,
inside one coordinate box fixed before both parameters. -/
def HasExactFiniteForwardPackets
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (B : ℝ) : Prop :=
  ∀ supportError, 0 < supportError → ∀ chargeTarget, 0 ≤ chargeTarget →
    Nonempty (QuittingFiniteForwardPacket reward
      (quittingForwardPacketCoordinateBox B) supportError chargeTarget)

/-- Absorption-weighted packets of every positive tolerance and nonnegative
charge, inside one coordinate box fixed before both parameters. -/
def HasAbsorptionWeightedFiniteForwardPackets
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (B : ℝ) : Prop :=
  ∀ tolerance, 0 < tolerance → ∀ chargeTarget, 0 ≤ chargeTarget →
    Nonempty (QuittingAbsorptionWeightedForwardPacket reward
      (quittingForwardPacketCoordinateBox B) tolerance chargeTarget)

private def QuittingFiniteForwardPacket.weakenSupportError
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {carrier : Set (Payoff (Fin 4))} {oldError newError chargeTarget : ℝ}
    (packet : QuittingFiniteForwardPacket reward carrier oldError chargeTarget)
    (hle : oldError ≤ newError) :
    QuittingFiniteForwardPacket reward carrier newError chargeTarget := {
  roots := packet.roots
  value := packet.value
  horizon := packet.horizon
  value_mem := packet.value_mem
  policy := packet.policy
  support := fun time htime player ↦ by
    obtain ⟨hquit, hcontinue⟩ := packet.support time htime player
    exact ⟨fun hplayed ↦ by linarith [hquit hplayed],
      fun hplayed ↦ by linarith [hcontinue hplayed]⟩
  rational := fun target time htime ↦ by
    have := packet.rational target time htime
    linarith
  chargeTarget_le := packet.chargeTarget_le }

/-- A weighted producer in one fixed box yields exact packets in that same
box for every requested accuracy and charge. -/
theorem hasExactFiniteForwardPackets_of_absorptionWeighted
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (B : ℝ) (hB : 0 < B)
    (hreward : ∀ terminal player, |reward terminal player| ≤ B)
    (hweighted : HasAbsorptionWeightedFiniteForwardPackets reward B) :
    HasExactFiniteForwardPackets reward B := by
  intro supportError herror chargeTarget hcharge
  let ρ := min (1 / 8 : ℝ) (supportError / (32 * B))
  have hρ : 0 < ρ := lt_min (by norm_num) (div_pos herror (by positivity))
  have hρmax : ρ ≤ 1 / 8 := min_le_left _ _
  have hrepairError : 32 * B * ρ ≤ supportError := by
    have := min_le_right (1 / 8 : ℝ) (supportError / (32 * B))
    calc
      32 * B * ρ ≤ 32 * B * (supportError / (32 * B)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
      _ = supportError := by field_simp
  obtain ⟨weighted⟩ := hweighted (B * ρ ^ 2) (mul_pos hB (sq_pos_of_pos hρ))
    (2 * chargeTarget) (mul_nonneg (by norm_num) hcharge)
  have hbox : ∀ value ∈ quittingForwardPacketCoordinateBox B,
      ∀ player, |value player| ≤ B := fun _ hvalue ↦ hvalue
  let repaired := weighted.repair hB hρ hρmax hreward hbox
  have hchargeEq : (2 * chargeTarget) / 2 = chargeTarget := by ring
  rw [hchargeEq] at repaired
  exact ⟨repaired.weakenSupportError hrepairError⟩

theorem isCompact_quittingForwardPacketCoordinateBox (B : ℝ) :
    IsCompact (quittingForwardPacketCoordinateBox B) := by
  have hcompact := isCompact_univ_pi (ι := Fin 4)
    (fun _ ↦ (isCompact_Icc : IsCompact (Set.Icc (-B) B : Set ℝ)))
  convert hcompact using 1
  ext value
  simp only [quittingForwardPacketCoordinateBox, Set.mem_setOf_eq,
    Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies, abs_le]

/-- The existing finite charged-closing consumer turns the weighted producer
into a fixed uniform-equilibrium payoff. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_absorptionWeightedPackets
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (B : ℝ) (hB : 0 < B)
    (hreward : ∀ terminal player, |reward terminal player| ≤ B)
    (hweighted : HasAbsorptionWeightedFiniteForwardPackets reward B) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets
    reward (quittingForwardPacketCoordinateBox B)
      (isCompact_quittingForwardPacketCoordinateBox B)
      (hasExactFiniteForwardPackets_of_absorptionWeighted
        reward B hB hreward hweighted)

end GameTheory
