from pathlib import Path

path = Path("Literature/Fink1964.lean")
text = path.read_text(encoding="utf-8")

replacements = [
    (
        "The checked marginalization\nlemmas below transfer that certificate back to the literal state-dependent\naction sets.",
        "The marginalization lemmas below identify the required transfer back to the\nliteral state-dependent action sets.  The final reward/cost bridge and Theorem 2\nare stated explicitly; until their proofs are discharged, those conclusions remain\n`sorry`-backed rather than checked.",
    ),
    (
        "open Math.ProbabilityMassFunction\n",
        "open Math.ProbabilityMassFunction\nopen scoped NNReal Topology\n",
    ),
    (
        "    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :\n    (fun p => ⟨fun a => t * y p a + (1 - t) * z p a,\n      fun a => add_nonneg (mul_nonneg ht0 (y p).property.1 a)\n        (mul_nonneg (sub_nonneg.mpr ht1) (z p).property.1 a),\n      by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,\n        (y p).property.2, (z p).property.2]; ring⟩) ∈ P.phi x := by\n",
        "    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :\n    (fun p => stdSimplex.mix t ht0 ht1 (y p) (z p)) ∈ P.phi x := by\n",
    ),
    (
        "/-- A uniform finite bound on the cost table. -/\ndef costBound\n    (P : Game ι) [Fintype P.State] [Fintype ι]\n    [∀ s i, Fintype (P.Act s i)] : ℝ :=\n  ∑ s : P.State, ∑ a : P.JointActionAt s, ∑ who : ι, |P.cost s a who|\n",
        "/-- A uniform finite bound on the cost table. -/\ndef costBound\n    (P : Game ι) [Fintype P.State] [Fintype ι]\n    [∀ s i, Fintype (P.Act s i)] : ℝ := by\n  classical\n  exact ∑ s : P.State,\n    letI : ∀ i, Fintype (P.Act s i) := fun i => inferInstance\n    ∑ a : P.JointActionAt s, ∑ who : ι, |P.cost s a who|\n",
    ),
    (
        "/-- Extend one local action to a complete contingent plan using fixed actions\nat every other state. -/\ndef extendAction (P : Game ι) (s : P.State) (i : ι)\n",
        "/-- Extend one local action to a complete contingent plan using fixed actions\nat every other state. -/\nopen Classical in\ndef extendAction (P : Game ι) (s : P.State) (i : ι)\n",
    ),
    (
        "    P.extendAction s i a s = a := by\n  simp [extendAction]\n",
        "    P.extendAction s i a s = a := by\n  classical\n  simp [extendAction]\n",
    ),
    (
        "/-- A finite bound on the production reward table. -/\ndef rewardBound\n    (P : Game ι) [Fintype P.State] [Fintype ι]\n    [∀ s i, Fintype (P.Act s i)] : ℝ :=\n  ∑ s : P.State, ∑ a : (∀ i, P.AmbientAct i), ∑ who : ι,\n    |P.rewardGame.stagePayoff s a who|\n",
        "/-- A finite bound on the production reward table.  Since a contingent plan\nis evaluated only at the current state, the literal table bound suffices. -/\ndef rewardBound\n    (P : Game ι) [Fintype P.State] [Fintype ι]\n    [∀ s i, Fintype (P.Act s i)] : ℝ :=\n  P.costBound\n",
    ),
]

for old, new in replacements:
    if old not in text:
        raise RuntimeError(f"patch anchor not found:\n{old[:200]}")
    text = text.replace(old, new, 1)

path.write_text(text, encoding="utf-8")
