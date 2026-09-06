import UniformEquilibrium.Quitting.Classification.SupportwiseQuittingPremiumBalanceAt
import UniformEquilibrium.Quitting.Classification.SupportwiseQuittingPremiumProductLow
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-! # Product-low and supportwise balance coincide for two players -/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

/-- On two players, product-low premiums imply a supportwise certificate on
every nonempty support. -/
theorem supportwiseBalance_of_productLow_finTwo
    (reward : {S : Finset (Fin 2) // S.Nonempty} → Payoff (Fin 2))
    (hlow : HasProductLowQuittingPremium reward) :
    IsSupportwiseBalancedQuittingPremiumTable reward := by
  let fullRoot : Fin 2 → PMF Bool := quittingPureSetRoot Finset.univ
  have habsorption : 0 < quittingRootAbsorptionMass fullRoot := by
    rw [quittingRootAbsorptionMass_pureSetRoot_of_nonempty
      (by simp : (Finset.univ : Finset (Fin 2)).Nonempty)]
    norm_num
  obtain ⟨lowPlayer, _hactive, hlowPlayer⟩ := hlow fullRoot habsorption
  have hfullLow : reward ⟨Finset.univ, Finset.univ_nonempty⟩ lowPlayer ≤
      reward (quittingSingletonTerminal lowPlayer) lowPlayer := by
    rw [show quittingRootQuitPayoff reward 0 fullRoot lowPlayer =
      reward ⟨Finset.univ, Finset.univ_nonempty⟩ lowPlayer by
        unfold fullRoot
        rw [quittingRootQuitPayoff_pureSetRoot_eq_insert]
        simp [quittingSetReward]] at hlowPlayer
    exact hlowPlayer
  intro active hactive
  by_cases hfull : active = Finset.univ
  · subst active
    obtain ⟨weight, hweight, hsupport, hsum, hpremium⟩ :=
      hasSupportwiseQuittingPremiumBalanceAt_of_point reward Finset.univ
        lowPlayer (Finset.mem_univ lowPlayer) (by
          intro terminal _hsubset hmem
          by_cases hsingleton : terminal.val = {lowPlayer}
          · rw [show terminal = quittingSingletonTerminal lowPlayer by
              exact Subtype.ext hsingleton]
          · have hterminalFull : terminal.val = Finset.univ := by
              ext player
              fin_cases lowPlayer <;> fin_cases player <;> simp_all
              all_goals
                by_contra hnot
                apply hsingleton
                ext candidate
                fin_cases candidate <;> simp_all
            rw [show terminal = ⟨Finset.univ, Finset.univ_nonempty⟩ by
              exact Subtype.ext hterminalFull]
            exact hfullLow)
    exact ⟨weight, hweight, hsupport, hsum, fun terminal hterminal hsubset =>
      hpremium ⟨terminal, hterminal⟩ hsubset⟩
  · obtain ⟨chosen, hchosen⟩ := hactive
    have hactiveSingleton : active = {chosen} := by
      fin_cases chosen
      · have hnot : (1 : Fin 2) ∉ active := by
          intro hone
          apply hfull
          ext player
          fin_cases player <;> simp_all
        ext player
        fin_cases player <;> simp_all
      · have hnot : (0 : Fin 2) ∉ active := by
          intro hzero
          apply hfull
          ext player
          fin_cases player <;> simp_all
        ext player
        fin_cases player <;> simp_all
    subst active
    obtain ⟨weight, hweight, hsupport, hsum, hpremium⟩ :=
      hasSupportwiseQuittingPremiumBalanceAt_of_point reward {chosen}
        chosen (by simp) (by
          intro terminal hsubset hmem
          have hterminalSingleton : terminal.val = {chosen} := by
            apply Finset.Subset.antisymm hsubset
            simpa using hmem
          rw [show terminal = quittingSingletonTerminal chosen by
            exact Subtype.ext hterminalSingleton]
        )
    exact ⟨weight, hweight, hsupport, hsum, fun terminal hterminal hsubset =>
      hpremium ⟨terminal, hterminal⟩ hsubset⟩

/-- Thus the two raw table conditions are equivalent for two players. -/
theorem productLow_iff_supportwiseBalance_finTwo
    (reward : {S : Finset (Fin 2) // S.Nonempty} → Payoff (Fin 2)) :
    HasProductLowQuittingPremium reward ↔
      IsSupportwiseBalancedQuittingPremiumTable reward := by
  constructor
  · exact supportwiseBalance_of_productLow_finTwo reward
  · exact hasProductLowQuittingPremium_of_supportwiseBalance reward

end GameTheory
