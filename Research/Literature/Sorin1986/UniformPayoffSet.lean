import Literature.Papers.Sorin1986
import UniformEquilibrium.Certificates.Adaptive.Certificate

/-!
# Research reduction for Sorin's uniform-payoff segment

The paper's Theorem 2 identifies the uniform-equilibrium payoff set with a
bounded segment.  This module states the exact semantic claim through the
paper module and proves the inclusion supplied by the two security
certificates.  The converse inclusion is not claimed here.
-/

namespace Research.Literature.Sorin1986

open GameTheory StochasticGame
open Literature.Papers.Sorin1986

theorem uniformPayoff_mem_sorinSegment_of_source_claim
    (hclaim : Literature.Papers.Sorin1986.UniformEquilibriumPayoffSetClaim)
    (payoff : Payoff SorinAbsorbingGame.Player)
    (hpayoff : SorinAbsorbingGame.game.IsUniformEquilibriumPayoff
      SorinAbsorbingGame.State.live payoff) :
    ∃ a : ℝ, 1 / 2 ≤ a ∧ a ≤ 2 / 3 ∧
      payoff = SorinAbsorbingGame.pair a (2 * (1 - a)) :=
  (hclaim payoff).mp hpayoff

theorem uniformPayoff_mem_sorinSegment
    (payoff : Payoff SorinAbsorbingGame.Player)
    (hpayoff : SorinAbsorbingGame.game.IsUniformEquilibriumPayoff
      SorinAbsorbingGame.State.live payoff) :
    ∃ a : ℝ, 1 / 2 ≤ a ∧ a ≤ 2 / 3 ∧
      payoff = SorinAbsorbingGame.pair a (2 * (1 - a)) := by
  have hplayerOne :=
    uniformEquilibriumPayoff_coordinate_ge_of_isOneSidedGuaranteeCertificate
      SorinAbsorbingGame.game SorinAbsorbingGame.State.live false (1 / 2)
    SorinAbsorbingGame.isOneSidedGuaranteeCertificate_playerOne hpayoff
  have hplayerTwo :=
    uniformEquilibriumPayoff_coordinate_ge_of_isOneSidedGuaranteeCertificate
      SorinAbsorbingGame.game SorinAbsorbingGame.State.live true (2 / 3)
    SorinAbsorbingGame.isOneSidedGuaranteeCertificate_playerTwo hpayoff
  have hline := SorinAbsorbingGame.uniformEquilibriumPayoff_weighted_eq_two
    payoff hpayoff
  refine ⟨payoff false, hplayerOne, ?_, ?_⟩
  · linarith
  · funext who
    cases who
    · simp [SorinAbsorbingGame.pair]
    · simp [SorinAbsorbingGame.pair]
      nlinarith [hline]

end Research.Literature.Sorin1986
