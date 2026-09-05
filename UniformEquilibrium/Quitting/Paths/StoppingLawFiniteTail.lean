import MathUE.ProbabilityMassFunction.StoppingLawFiniteTail

/-! # Stopping-law finite tails: game-semantic namespace access -/

namespace GameTheory

export Math.Probability
  (stoppingLawFinitePrefix
    none_mem_stoppingLawFinitePrefix
    some_mem_stoppingLawFinitePrefix
    stoppingLawFiniteHeadMass
    stoppingLawLateFiniteMass
    stoppingLawLateFiniteMass_eq_tsum_compl
    stoppingLawFinitePrefix_compl_is_late_finite
    stoppingLawLateFiniteMass_eq_one_sub_none_sub_finiteHead
    stoppingLaw_atom_le_lateFiniteMass)

end GameTheory
