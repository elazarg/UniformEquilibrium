import UniformEquilibrium.Quitting.Stationary.LiveMass
import UniformEquilibrium.Quitting.Paths.ProfileNeverMass

/-! # Actual joint-Never mass of an absorbing stationary profile -/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The actual live-mass limit of an absorbing stationary source is zero. -/
theorem quittingLiveMassLimit_stationary_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (habsorbs : quittingStationaryContinueMass root < 1) :
    quittingLiveMassLimit reward (quittingStationaryProfile reward root) = 0 :=
  tendsto_nhds_unique
    (tendsto_quittingLiveMass reward (quittingStationaryProfile reward root))
    (tendsto_quittingLiveMass_stationary_zero reward root habsorbs)

/-- Absorption kills the product of actual marginal Never atoms, without
requiring each individual player or each deleted opponent clock to absorb. -/
theorem prod_stoppingLaw_none_stationary_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (habsorbs : quittingStationaryContinueMass root < 1) :
    (∏ who, (quittingBehaviorStoppingLaw reward
      (quittingStationaryProfile reward root who) none).toReal) = 0 := by
  rw [← quittingTerminalOutcomeMass_none_eq_prod_stoppingLaw_none]
  exact quittingLiveMassLimit_stationary_eq_zero reward root habsorbs

end GameTheory
