#!/usr/bin/env python3
from pathlib import Path

path = Path("Literature/Sorin1986.lean")
s = path.read_text(encoding="utf-8")


def replace_once(old: str, new: str) -> None:
    global s
    count = s.count(old)
    if count != 1:
        raise SystemExit(
            f"expected one occurrence, found {count}: {old[:120]!r}"
        )
    s = s.replace(old, new)


replace_once(
    "import UniformEquilibrium.ProofView.Concepts.Welfare.FolkTheorem.Feasible\n",
    "import UniformEquilibrium.ProofView.Concepts.Welfare.FolkTheorem.Feasible\n"
    "import UniformEquilibrium.ProofView.Concepts.Existence.CompactNash\n",
)

replace_once(
    "observed realized action profiles.  Its behavior profiles give a behavioral presentation that is outcome-equivalent\n"
    "to the paper's mixed strategies under perfect recall and standard\n"
    "signalling.\n",
    "observed realized action profiles.  Its behavior profiles give a behavioral\n"
    "presentation that is outcome-equivalent to the paper's mixed strategies under\n"
    "perfect recall and standard signalling.\n",
)

replace_once(
    """  payoffAffine : ∀ profile i x y t who, 0 ≤ t → t ≤ 1 →
    payoff (Function.update profile i (mix i t x y)) who =
      t * payoff (Function.update profile i x) who +
        (1 - t) * payoff (Function.update profile i y) who

attribute [instance] CompactContinuousGame.finitePlayer
""",
    """  payoffAffine : ∀ profile i x y t who, 0 ≤ t → t ≤ 1 →
    payoff (Function.update profile i (mix i t x y)) who =
      t * payoff (Function.update profile i x) who +
        (1 - t) * payoff (Function.update profile i y) who
  barycenter : ∀ i (n : ℕ),
    stdSimplex ℝ (Fin n) → (Fin n → Strategy i) → Strategy i
  barycenterContinuous : ∀ i (n : ℕ) (points : Fin n → Strategy i),
    Continuous fun weights : stdSimplex ℝ (Fin n) =>
      barycenter i n weights points
  payoffBarycentric : ∀ profile who (n : ℕ)
    (weights : stdSimplex ℝ (Fin n)) (points : Fin n → Strategy who),
    payoff (Function.update profile who
        (barycenter who n weights points)) who =
      ∑ a, weights a * payoff (Function.update profile who (points a)) who

attribute [instance] CompactContinuousGame.finitePlayer
""",
)

replace_once(
    """attribute [instance] CompactContinuousGame.nonemptyStrategy

/-- A mixed-profile carrier for a compact continuous game. -/
abbrev CompactContinuousGame.Profile (G : CompactContinuousGame) :=
  ∀ i, G.Strategy i

/-- Feasible payoff set of a compact continuous game. -/
""",
    """attribute [instance] CompactContinuousGame.nonemptyStrategy

/-- Forget the paper-facing binary mixing operation and retain the finite
barycentres used by the compact Nash theorem. -/
noncomputable def CompactContinuousGame.toCompactBarycentricGame
    (G : CompactContinuousGame) : GameTheory.CompactBarycentricGame where
  Player := G.Player
  Strategy := G.Strategy
  payoff := G.payoff
  payoffContinuous := G.payoffContinuous
  barycenter := G.barycenter
  barycenterContinuous := G.barycenterContinuous
  payoffBarycentric := G.payoffBarycentric

/-- A mixed-profile carrier for a compact continuous game. -/
abbrev CompactContinuousGame.Profile (G : CompactContinuousGame) :=
  ∀ i, G.Strategy i

/-- Replacing one coordinate by a fixed strategy is continuous. -/
theorem CompactContinuousGame.continuous_update_const
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

/-- Feasible payoff set of a compact continuous game. -/
""",
)

replace_once(
    """  compactPayoffAffine : ∀ profile who x y t observer, 0 ≤ t → t ≤ 1 →
    compactPayoff (Function.update profile who (mix who t x y)) observer =
      t * compactPayoff (Function.update profile who x) observer +
        (1 - t) * compactPayoff (Function.update profile who y) observer
  toBehavior : (∀ who, Strategy who) → G.BehaviorProfile
""",
    """  compactPayoffAffine : ∀ profile who x y t observer, 0 ≤ t → t ≤ 1 →
    compactPayoff (Function.update profile who (mix who t x y)) observer =
      t * compactPayoff (Function.update profile who x) observer +
        (1 - t) * compactPayoff (Function.update profile who y) observer
  barycenter : ∀ who (n : ℕ),
    stdSimplex ℝ (Fin n) → (Fin n → Strategy who) → Strategy who
  barycenterContinuous : ∀ who (n : ℕ) (points : Fin n → Strategy who),
    Continuous fun weights : stdSimplex ℝ (Fin n) =>
      barycenter who n weights points
  compactPayoffBarycentric : ∀ profile who (n : ℕ)
    (weights : stdSimplex ℝ (Fin n)) (points : Fin n → Strategy who),
    compactPayoff (Function.update profile who
        (barycenter who n weights points)) who =
      ∑ a, weights a *
        compactPayoff (Function.update profile who (points a)) who
  toBehavior : (∀ who, Strategy who) → G.BehaviorProfile
""",
)

replace_once(
    """  payoffContinuous := presentation.compactPayoffContinuous
  payoffAffine := presentation.compactPayoffAffine
""",
    """  payoffContinuous := presentation.compactPayoffContinuous
  payoffAffine := presentation.compactPayoffAffine
  barycenter := presentation.barycenter
  barycenterContinuous := presentation.barycenterContinuous
  payoffBarycentric := presentation.compactPayoffBarycentric
""",
)

replace_once(
    """/-! Property (1) is an application of compactness and continuity of the
product mixed-strategy space.  Its general topological proof is not present in
the repository. -/
theorem paper_property_1 (G : CompactContinuousGame) :
    G.feasiblePayoffs.Nonempty ∧
      PathConnectedSet G.feasiblePayoffs ∧ IsCompact G.feasiblePayoffs := by
  sorry

/-! Property (2) is the compact-strategy Nash existence theorem together with
closedness of the equilibrium relation.  The repository has finite mixed Nash
existence, but not this compact continuous version. -/
theorem paper_property_2 (G : CompactContinuousGame) :
    G.equilibriumPayoffs.Nonempty ∧ IsCompact G.equilibriumPayoffs := by
  sorry
""",
    """/-- Property (1): the continuous payoff image of the compact product
strategy space is nonempty and compact; binary mixing supplies paths. -/
theorem paper_property_1 (G : CompactContinuousGame) :
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

/-- The Nash-profile set is closed: it is the intersection, over every
player and every unilateral deviation, of one closed payoff inequality. -/
theorem CompactContinuousGame.isClosed_nashProfiles
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
      (G.continuous_update_const who deviation))
    (G.payoffContinuous who)

/-- Property (2): Nash profiles exist, and their payoff image is compact. -/
theorem paper_property_2 (G : CompactContinuousGame) :
    G.equilibriumPayoffs.Nonempty ∧ IsCompact G.equilibriumPayoffs := by
  have hnash : ∃ profile : G.Profile, G.IsNash profile := by
    obtain ⟨profile, hprofile⟩ :=
      G.toCompactBarycentricGame.exists_nash
    refine ⟨profile, ?_⟩
    intro who deviation
    exact hprofile who deviation
  constructor
  · obtain ⟨profile, hprofile⟩ := hnash
    exact ⟨G.payoff profile, profile, hprofile, rfl⟩
  · have hpayoff : Continuous G.payoff :=
      continuous_pi G.payoffContinuous
    have hcompactProfiles :
        IsCompact {profile : G.Profile | G.IsNash profile} :=
      G.isClosed_nashProfiles.isCompact
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
""",
)

replace_once(
    """/-! Remark 2 says the analogue of Proposition 15 holds under the printed
sufficient condition.  The proof is only announced in the paper. -/
theorem concluding_remark_2 (α β x : ℝ)
    (hgap : α < β - x) (hx : 0 < x)
    (hβ : max (1 + α) (1 + 2 * x) < β) :
""",
    """/-! Remark 2 says the analogue of Proposition 15 holds under the printed
sufficient condition `β ≥ max{1 + α, 1 + 2x}`.  The proof is only announced
in the paper, and the explicit critical set is not printed there: the set
below is the Proposition 15 analogue extrapolated to the parameter family,
agreeing with Figure 1 at `α = 1`, `β = 5`, `x = 1`. -/
theorem concluding_remark_2 (α β x : ℝ)
    (hgap : α < β - x) (hx : 0 < x)
    (hβ : max (1 + α) (1 + 2 * x) ≤ β) :
""",
)

path.write_text(s, encoding="utf-8")
print(f"patched {path}: {len(s)} bytes, {s.count(chr(10)) + 1} lines")
