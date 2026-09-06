import MathUE.FiniteCoalitionSupportPeelingOrder
import UniformEquilibrium.Quitting.Classification.SupportwiseQuittingPremiumNormalization

/-! # Weak quitting-premium support peeling and player rankings -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A player receives a strictly positive own-quitting premium at a finite
coalition.  Nonemptiness is carried here so the coalition indexes a quitting
reward entry. -/
def HasPositiveOwnQuittingPremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (player : ι) (coalition : Finset ι) : Prop :=
  ∃ hcoalition : coalition.Nonempty,
    reward (quittingSingletonTerminal player) player <
      reward ⟨coalition, hcoalition⟩ player

/-- Weak support peeling for the positive-own-premium coalition relation. -/
def HasWeakQuittingPremiumSupportPeeling
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  MathUE.HasFiniteCoalitionSupportPeeling
    (HasPositiveOwnQuittingPremium reward)

/-- A full player-label rank in which every positive own-premium coalition
contains a strictly earlier-ranked member. -/
def HasPositiveQuittingPremiumPlayerRanking
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  MathUE.HasFiniteCoalitionPlayerRanking
    (HasPositiveOwnQuittingPremium reward)

omit [Fintype ι] [DecidableEq ι] in
/-- The named peeling predicate has exactly the support-by-support
payoff formulation. -/
theorem hasWeakQuittingPremiumSupportPeeling_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    HasWeakQuittingPremiumSupportPeeling reward ↔
      ∀ active : Finset ι, active.Nonempty →
        ∃ chosen ∈ active, ∀ (terminal : Finset ι)
          (hterminal : terminal.Nonempty), terminal ⊆ active →
          chosen ∈ terminal →
            reward ⟨terminal, hterminal⟩ chosen ≤
              reward (quittingSingletonTerminal chosen) chosen := by
  constructor
  · intro hpeel active hactive
    obtain ⟨chosen, hchosen, hfree⟩ := hpeel active hactive
    refine ⟨chosen, hchosen, ?_⟩
    intro terminal hterminal hsubset hchosenTerminal
    by_contra hnot
    exact hfree terminal hsubset hchosenTerminal
      ⟨hterminal, lt_of_not_ge hnot⟩
  · intro hpeel active hactive
    obtain ⟨chosen, hchosen, hchosenPayoff⟩ := hpeel active hactive
    refine ⟨chosen, hchosen, ?_⟩
    rintro terminal hsubset hchosenTerminal ⟨hterminal, hpositive⟩
    exact (not_lt_of_ge
      (hchosenPayoff terminal hterminal hsubset hchosenTerminal)
      hpositive)

omit [DecidableEq ι] in
/-- The ranking predicate exposes an injective rank of every player into the
cardinality-sized initial segment and the literal positive-premium rule. -/
theorem hasPositiveQuittingPremiumPlayerRanking_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    HasPositiveQuittingPremiumPlayerRanking reward ↔
      ∃ rank : ι → ℕ, Function.Injective rank ∧
        (∀ player, rank player < Fintype.card ι) ∧
        ∀ (terminal : Finset ι) (hterminal : terminal.Nonempty)
          (player : ι), player ∈ terminal →
          reward (quittingSingletonTerminal player) player <
              reward ⟨terminal, hterminal⟩ player →
            ∃ earlier ∈ terminal, rank earlier < rank player := by
  constructor
  · rintro ⟨rank, hinjective, hbound, hpositive⟩
    refine ⟨rank, hinjective, hbound, ?_⟩
    intro terminal hterminal player hplayer hpremium
    exact hpositive player terminal hplayer ⟨hterminal, hpremium⟩
  · rintro ⟨rank, hinjective, hbound, hpositive⟩
    refine ⟨rank, hinjective, hbound, ?_⟩
    rintro player terminal hplayer ⟨hterminal, hpremium⟩
    exact hpositive terminal hterminal player hplayer hpremium

/-- Weak premium support peeling is exactly the full finite player-ranking
condition.  This orders player labels, not quitting dates. -/
theorem weakQuittingPremiumSupportPeeling_iff_playerRanking
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    HasWeakQuittingPremiumSupportPeeling reward ↔
      HasPositiveQuittingPremiumPlayerRanking reward :=
  MathUE.finiteCoalitionSupportPeeling_iff_playerRanking
    (HasPositiveOwnQuittingPremium reward)

omit [Fintype ι] in
/-- Weak premium support peeling supplies the supportwise point-mass
witnesses used by the low-root and periodic producers. -/
theorem supportwiseBalance_of_weakQuittingPremiumSupportPeeling
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpeel : HasWeakQuittingPremiumSupportPeeling reward) :
    IsSupportwiseBalancedQuittingPremiumTable reward := by
  apply supportwiseBalance_of_weakPremiumPeeling reward
  exact hasWeakQuittingPremiumSupportPeeling_iff reward |>.mp hpeel

end GameTheory
