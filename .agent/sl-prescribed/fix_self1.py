from pathlib import Path

path = Path('UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/SelfOrientedAtomSequence.lean')
text = path.read_text(encoding='utf-8')

replacements = [
("""  by_contra hnone
  push_neg at hnone
  have hmono :
      expect (quittingBehaviorStoppingLaw reward strategy)
          (fun _ : Option ℕ => source + ε) ≤
        expect (quittingBehaviorStoppingLaw reward strategy) value := by
    apply expect_mono
    intro quitTime
    exact (hnone quitTime).le
""",
"""  by_contra hnone
  simp only [not_exists, not_le] at hnone
  have hmono :
      expect (quittingBehaviorStoppingLaw reward strategy)
          (fun _ : Option ℕ => source + ε) ≤
        expect (quittingBehaviorStoppingLaw reward strategy) value := by
    apply FinDist.expect_mono
    intro quitTime _
    exact (hnone quitTime).le
"""),
("""  have htargetDebt : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who targetTime))) who ≤ ε := by
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
    rw [quittingContinuationBestResponseValue_update_self]
    linarith
  refine ⟨sourceTime, targetTime, ?_, htargetDebt⟩
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  linarith
""",
"""  have htargetDebt : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who targetTime))) who ≤ ε := by
    change quittingContinuationBestResponseValue reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who targetTime)) who -
      quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who targetTime)) who ≤ ε
    rw [quittingContinuationBestResponseValue_update_self]
    linarith
  refine ⟨sourceTime, targetTime, ?_, htargetDebt⟩
  change quittingContinuationBestResponseValue reward profile who -
      quittingTerminalPayoff reward profile who - 2 * ε ≤
    quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who targetTime)) who -
      quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who sourceTime)) who
  linarith
"""),
("""    nlinarith [hsourceDebt n]
""",
"""    linarith [hsourceDebt n, hgain, herrorLe]
"""),
]

for old, new in replacements:
    if old not in text:
        raise SystemExit(f'missing replacement block:\n{old[:160]}')
    text = text.replace(old, new, 1)

path.write_text(text, encoding='utf-8')
