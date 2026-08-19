import Sorin1986

noncomputable section

namespace Literature.Sorin1986

open GameTheory Set Filter
open scoped BigOperators Topology

/-- Property (1), proved directly from compactness, convex mixing, and
continuity of the payoff map. -/
theorem paper_property_1_proved (G : CompactContinuousGame) :
    G.feasiblePayoffs.Nonempty ∧
      PathConnectedSet G.feasiblePayoffs ∧ IsCompact G.feasiblePayoffs := by
  have hpayoff : Continuous G.payoff :=
    continuous_pi G.payoffContinuous
  constructor
  · exact Set.range_nonempty G.payoff
  constructor
  · constructor
    · exact Set.range_nonempty G.payoff
    · rintro _ ⟨profileX, rfl⟩ _ ⟨profileY, rfl⟩
      let path : ℝ → Payoff G.Player := fun t =>
        G.payoff (fun i => G.mix i t (profileY i) (profileX i))
      have hprofile : Continuous fun t : ℝ =>
          (fun i => G.mix i t (profileY i) (profileX i)) := by
        apply continuous_pi
        intro i
        exact (G.mixContinuous i).comp
          (continuous_id.prodMk (continuous_const.prodMk continuous_const))
      refine ⟨path, hpayoff.comp hprofile, ?_, ?_, ?_⟩
      · change G.payoff (fun i => G.mix i 0 (profileY i) (profileX i)) =
          G.payoff profileX
        congr 1
        funext i
        exact G.mix_zero i (profileY i) (profileX i)
      · change G.payoff (fun i => G.mix i 1 (profileY i) (profileX i)) =
          G.payoff profileY
        congr 1
        funext i
        exact G.mix_one i (profileY i) (profileX i)
      · intro t _
        exact ⟨fun i => G.mix i t (profileY i) (profileX i), rfl⟩
  · simpa [CompactContinuousGame.feasiblePayoffs] using
      isCompact_univ.image_of_continuousOn hpayoff.continuousOn

end Literature.Sorin1986
