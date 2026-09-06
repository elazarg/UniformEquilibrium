import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremium
import UniformEquilibrium.Quitting.Classification.SupportwiseQuittingPremium

/-! # Supportwise premium balance implies product-low premiums -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The supportwise weighted product identity supplies the product-low
active endpoint at every absorbing root. -/
theorem hasProductLowQuittingPremium_of_supportwiseBalance
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hbalanced : IsSupportwiseBalancedQuittingPremiumTable reward) :
    HasProductLowQuittingPremium reward := by
  intro root habsorption
  exact exists_active_quitPayoff_le_singleton_of_supportwiseBalance
    reward hbalanced root habsorption

end GameTheory
