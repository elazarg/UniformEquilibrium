import UniformEquilibrium.Quitting.Bellman.Finite.EndpointNashClosed
import Mathlib.Topology.Maps.Proper.Basic

/-! # Closed actual exact-root singleton-sublevel return sources

Compactness of the full Boolean root simplex closes the existential return
relation. No root selection continuity or premium sign is assumed.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isClosed_setOf_exists_exactRoot_singletonSublevel
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsClosed {tail : Payoff ι | ∃ root, IsεQuittingRootNash reward tail 0 root ∧
      ∃ player, quittingRootSuccessorPayoff reward tail root player ≤
        reward (quittingSingletonTerminal player) player} := by
  let relation : Set (Payoff ι × QuittingRootSimplex ι) :=
    {point | IsεQuittingRootEndpointNash reward point.1 0
      (quittingRootOfSimplex point.2) ∧ ∃ player,
        quittingRootSuccessorPayoff reward point.1 (quittingRootOfSimplex point.2) player ≤
          reward (quittingSingletonTerminal player) player}
  have hnashClosed : IsClosed {point : Payoff ι × QuittingRootSimplex ι |
      IsεQuittingRootEndpointNash reward point.1 0 (quittingRootOfSimplex point.2)} :=
    (isClosed_isεQuittingRootEndpointNash_simplex reward).preimage
      (continuous_const.prodMk continuous_id)
  have hlowClosed : IsClosed (⋃ player : ι,
      {point : Payoff ι × QuittingRootSimplex ι |
        quittingRootSuccessorPayoff reward point.1 (quittingRootOfSimplex point.2) player ≤
          reward (quittingSingletonTerminal player) player}) :=
    isClosed_iUnion_of_finite fun player : ι =>
    isClosed_le ((continuous_apply player).comp
      (continuous_quittingRootSuccessorPayoff_simplex reward))
      (continuous_const (y := reward (quittingSingletonTerminal player) player))
  have hlowSet : {point : Payoff ι × QuittingRootSimplex ι | ∃ player,
      quittingRootSuccessorPayoff reward point.1 (quittingRootOfSimplex point.2) player ≤
        reward (quittingSingletonTerminal player) player} =
      ⋃ player : ι, {point : Payoff ι × QuittingRootSimplex ι |
        quittingRootSuccessorPayoff reward point.1 (quittingRootOfSimplex point.2) player ≤
          reward (quittingSingletonTerminal player) player} := by
    ext point
    simp
  rw [← hlowSet] at hlowClosed
  have hrelation : IsClosed relation := hnashClosed.inter hlowClosed
  have hprojection := isClosedMap_fst_of_compactSpace relation hrelation
  have heq : Prod.fst '' relation = {tail : Payoff ι |
      ∃ root, IsεQuittingRootNash reward tail 0 root ∧ ∃ player,
        quittingRootSuccessorPayoff reward tail root player ≤
          reward (quittingSingletonTerminal player) player} := by
    ext tail
    constructor
    · rintro ⟨⟨source, simplex⟩, ⟨hnash, hlow⟩, rfl⟩
      exact ⟨quittingRootOfSimplex simplex,
        (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward source _).mp hnash,
        hlow⟩
    · rintro ⟨root, hnash, hlow⟩
      refine ⟨(tail, quittingSimplexOfRoot root), ?_, rfl⟩
      change IsεQuittingRootEndpointNash reward tail 0
        (quittingRootOfSimplex (quittingSimplexOfRoot root)) ∧ _
      simpa only [quittingRootOfSimplex_simplexOfRoot] using
        And.intro ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
          reward tail root).mpr hnash) hlow
  exact heq ▸ hprojection

end GameTheory
