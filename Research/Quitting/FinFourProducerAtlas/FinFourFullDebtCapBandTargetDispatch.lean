import Research.Quitting.FinFourProducerAtlas.FinFourFullDebtFixedWeightChordCompactification
import Research.Quitting.FinFourProducerAtlas.FinFourFullDebtOffMinimumActualReachPaidPort

/-!
# Full-debt compact-target dispatch

For a supplied four-player full-debt minimum source, cap-band redistribution
has two exact compact-limit branches.  A target strictly above the source
minimum yields one literal actual-reach paid port selected from the retained
target family.  A target on the minimum fibre yields one actual fixed-weight
chord compactification and its strict positive-debt support child.

No classifier produces the supplied source here.  Neither branch gives a
renewal, terminal conclusion, Nash profile, or uniform equilibrium.
-/

noncomputable section

namespace GameTheory

/-- Exhaustive branch-local output for a supplied full-debt minimum source. -/
inductive FinFourFullDebtCapBandTargetDispatch
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    (M : ℝ)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1) : Type
  | offMinimum
      (base : FinFourFullDebtCapBandTargetCompactification source M)
      (port : FinFourFullDebtOffMinimumActualReachPaidPort base) :
      FinFourFullDebtCapBandTargetDispatch source M weight hweight0 hweight1
  | minimumChord
      (base : FinFourFullDebtCapBandTargetCompactification source M)
      (minimumTarget : FinFourFullDebtCapBandMinimumTarget base)
      (chord : FinFourFullDebtFixedWeightChordCompactification
        base minimumTarget weight hweight0 hweight1) :
      FinFourFullDebtCapBandTargetDispatch source M weight hweight0 hweight1

/-- A supplied full-debt minimum-atom producer enters exactly the strict
actual-reach paid-port branch or the minimum fixed-weight chord branch. -/
theorem nonempty_finFourFullDebtCapBandTargetDispatch
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound)
    (hfullDebt : ∀ who, 0 < quittingTerminalSemanticDebt source.point.1 who)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1) :
    Nonempty (FinFourFullDebtCapBandTargetDispatch
      source M weight hweight0 hweight1) := by
  obtain ⟨⟨base, alternative⟩⟩ :=
    nonempty_finFourFullDebtCapBandTargetCompactification_and_alternative
      source hfullDebt M hM hreward
  cases alternative with
  | offMinimum margin hmargin htargetDebt heventually =>
      obtain ⟨port⟩ :=
        nonempty_finFourFullDebtOffMinimumActualReachPaidPort
          base margin hmargin htargetDebt heventually hreward
      exact ⟨.offMinimum base port⟩
  | minimum htargetDebt =>
      let minimumTarget :=
        FinFourFullDebtCapBandTargetAlternative.minimumTarget_of_minimum
          htargetDebt
      obtain ⟨chord⟩ :=
        nonempty_finFourFullDebtFixedWeightChordCompactification
          base minimumTarget weight hweight0 hweight1
      exact ⟨.minimumChord base minimumTarget chord⟩

end GameTheory
