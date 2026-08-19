import Literature.Sorin1986
import UniformEquilibrium.ProofView.Concepts.Existence.CompactNash

noncomputable section

namespace Literature.Sorin1986

open GameTheory Set
open scoped BigOperators Topology

/-- Temporary adapter used to validate the compact Nash application before
folding the data into `CompactContinuousGame`. -/
structure CompactNashData (G : CompactContinuousGame) where
  barycenter : ∀ who (n : ℕ),
    stdSimplex ℝ (Fin n) → (Fin n → G.Strategy who) → G.Strategy who
  barycenterContinuous : ∀ who (n : ℕ)
    (points : Fin n → G.Strategy who),
    Continuous fun weights : stdSimplex ℝ (Fin n) =>
      barycenter who n weights points
  payoffBarycentric : ∀ profile who (n : ℕ)
    (weights : stdSimplex ℝ (Fin n))
    (points : Fin n → G.Strategy who),
    G.payoff (Function.update profile who
        (barycenter who n weights points)) who =
      ∑ a, weights a *
        G.payoff (Function.update profile who (points a)) who

noncomputable def CompactNashData.toGame {G : CompactContinuousGame}
    (data : CompactNashData G) : GameTheory.CompactBarycentricGame where
  Player := G.Player
  Strategy := G.Strategy
  payoff := G.payoff
  payoffContinuous := G.payoffContinuous
  barycenter := data.barycenter
  barycenterContinuous := data.barycenterContinuous
  payoffBarycentric := data.payoffBarycentric

theorem CompactContinuousGame.continuous_update_const_test
    (G : CompactContinuousGame) (who : G.Player)
    (deviation : G.Strategy who) :
    Continuous (fun profile : G.Profile =>
      Function.update profile who deviation) := by
  apply continuous_pi
  intro i
  by_cases hi : i = who
  · subst i
    simpa using (continuous_const :
      Continuous (fun _profile : G.Profile => deviation))
  · simpa [Function.update, hi] using
      (continuous_apply i : Continuous (fun profile : G.Profile => profile i))

theorem CompactContinuousGame.isClosed_nashProfiles_test
    (G : CompactContinuousGame) :
    IsClosed {profile : G.Profile | G.IsNash profile} := by
  rw [show {profile : G.Profile | G.IsNash profile} =
      ⋂ who, ⋂ deviation : G.Strategy who,
        {profile : G.Profile |
          G.payoff (Function.update profile who deviation) who ≤
            G.payoff profile who} by
    ext profile
    simp [CompactContinuousGame.IsNash]]
  apply isClosed_iInter
  intro who
  apply isClosed_iInter
  intro deviation
  exact isClosed_le
    ((G.payoffContinuous who).comp
      (G.continuous_update_const_test who deviation))
    (G.payoffContinuous who)

theorem paper_property_2_test (G : CompactContinuousGame)
    (data : CompactNashData G) :
    G.equilibriumPayoffs.Nonempty ∧ IsCompact G.equilibriumPayoffs := by
  have hnash : ∃ profile : G.Profile, G.IsNash profile := by
    obtain ⟨profile, hprofile⟩ := data.toGame.exists_nash
    refine ⟨profile, ?_⟩
    simpa [CompactContinuousGame.IsNash,
      GameTheory.CompactBarycentricGame.IsNash,
      CompactNashData.toGame] using hprofile
  constructor
  · obtain ⟨profile, hprofile⟩ := hnash
    exact ⟨G.payoff profile, profile, hprofile, rfl⟩
  · have hpayoff : Continuous G.payoff :=
      continuous_pi G.payoffContinuous
    have hcompactProfiles :
        IsCompact {profile : G.Profile | G.IsNash profile} :=
      G.isClosed_nashProfiles_test.isCompact
    have heq : G.equilibriumPayoffs =
        G.payoff '' {profile : G.Profile | G.IsNash profile} := by
      ext value
      constructor
      · rintro ⟨profile, hprofile, rfl⟩
        exact ⟨profile, hprofile, rfl⟩
      · rintro ⟨profile, hprofile, rfl⟩
        exact ⟨profile, hprofile, rfl⟩
    rw [heq]
    exact hcompactProfiles.image_of_continuousOn hpayoff.continuousOn

end Literature.Sorin1986
