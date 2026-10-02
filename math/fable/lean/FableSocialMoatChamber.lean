/-
Social-moat chamber for quitting games.

A reward table is *socially nonpositive* when every terminal coalition pays a
nonpositive total.  Every executable behavior profile then also pays a
nonpositive social total, because its prescribed terminal payoff is an exact
barycentric mixture of the coalition reward vectors and the zero payoff of
Never.  The bound survives the passage to the compact semantic carrier, since
the social total is continuous and the carrier is the closure of the attainable
semantic pairs.

Against this ceiling stands the singleton moat of a debt-minimal semantic pair:
if no uniform equilibrium payoff exists, the total debt infimum is positive and
every player's best-response cap sits at least that far above the player's own
solo quitting reward.  Summing the moat over all players forces the minimizer's
social total to be at least the solo total plus `card - 1` moat widths.  With
nonnegative solo rewards and at least two players this is strictly positive,
contradicting the social ceiling: socially nonpositive tables with nonnegative
solo rewards always have a uniform equilibrium payoff.

The same moat sum, stated without the social hypothesis, is an unconditional
lower bound on the social total of any carrier-minimal semantic pair whenever
no uniform equilibrium payoff exists.
-/
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment

noncomputable section

namespace GameTheory

open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The social ceiling -/

omit [DecidableEq ι] in
/-- If every terminal coalition pays a nonpositive social total, then so does
every executable behavior profile.  The prescribed terminal payoff is the exact
reward moment of the profile's terminal outcome law, whose masses are
nonnegative, and Never pays zero. -/
theorem fable_sum_terminalPayoff_nonpos_of_social_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsocial : ∀ terminal, (∑ player, reward terminal player) ≤ 0)
    (profile : (quittingGame reward).BehaviorProfile) :
    (∑ player, quittingTerminalPayoff reward profile player) ≤ 0 := by
  have hmoment := quittingTerminalRewardMoment_outcomeMass reward profile
  have hmass := (quittingTerminalOutcomeMass_mem_stdSimplex reward profile).1
  have hplayer : ∀ player : ι, quittingTerminalPayoff reward profile player =
      ∑ outcome, quittingTerminalOutcomeMass reward profile outcome *
        quittingTerminalOutcomeReward reward outcome player :=
    fun player => (congrFun hmoment player).symm
  have hout : ∀ outcome : QuittingTerminalOutcome ι,
      (∑ player, quittingTerminalOutcomeReward reward outcome player) ≤ 0 := by
    intro outcome
    cases outcome with
    | none => simp [quittingTerminalOutcomeReward]
    | some terminal => exact hsocial terminal
  calc (∑ player, quittingTerminalPayoff reward profile player)
      = ∑ player, ∑ outcome,
          quittingTerminalOutcomeMass reward profile outcome *
            quittingTerminalOutcomeReward reward outcome player :=
        Finset.sum_congr rfl fun player _ => hplayer player
    _ = ∑ outcome, ∑ player,
          quittingTerminalOutcomeMass reward profile outcome *
            quittingTerminalOutcomeReward reward outcome player :=
        Finset.sum_comm
    _ = ∑ outcome, quittingTerminalOutcomeMass reward profile outcome *
          ∑ player, quittingTerminalOutcomeReward reward outcome player :=
        Finset.sum_congr rfl fun outcome _ => by rw [Finset.mul_sum]
    _ ≤ 0 := by
        apply Finset.sum_nonpos
        intro outcome _
        simpa using mul_le_mul_of_nonneg_left (hout outcome) (hmass outcome)

/-- The social ceiling passes to the compact semantic carrier: the social total
is continuous, so its nonpositivity is a closed condition containing every
attainable semantic pair, hence their closure. -/
theorem fable_sum_carrierPayoff_nonpos_of_social_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsocial : ∀ terminal, (∑ player, reward terminal player) ≤ 0)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    (∑ player, pair.1 player) ≤ 0 := by
  have hcont : Continuous
      (fun candidate : QuittingTerminalSemanticPair ι =>
        ∑ player, candidate.1 player) :=
    continuous_finsetSum Finset.univ fun player _ =>
      (continuous_apply player).comp continuous_fst
  have hclosed : IsClosed
      {candidate : QuittingTerminalSemanticPair ι |
        (∑ player, candidate.1 player) ≤ 0} :=
    isClosed_le hcont continuous_const
  have hsubset : quittingAttainableTerminalSemanticPairs reward ⊆
      {candidate : QuittingTerminalSemanticPair ι |
        (∑ player, candidate.1 player) ≤ 0} := by
    rintro candidate ⟨profile, rfl⟩
    exact fable_sum_terminalPayoff_nonpos_of_social_nonpos reward hsocial profile
  exact (closure_minimal hsubset hclosed) hpair

/-! ## The singleton moat sum -/

/-- Summing the singleton moat of a positive carrier-minimal semantic pair over
all players: the social total of the prescribed coordinate is at least the solo
reward total plus `card - 1` copies of the total debt. -/
private theorem fable_moat_sum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair) :
    (∑ player, reward (quittingSingletonTerminal player) player) +
        ((Fintype.card ι : ℝ) - 1) * quittingTerminalSemanticDebtSum pair ≤
      ∑ player, pair.1 player := by
  have hmoat : ∀ player : ι, quittingTerminalSemanticDebtSum pair ≤
      pair.2 player - reward (quittingSingletonTerminal player) player :=
    fun player => minimumTerminalSemantic_singletonMargin
      (reward := reward) pair hpair hminimum hpositive player
  have hconstant : (Fintype.card ι : ℝ) * quittingTerminalSemanticDebtSum pair =
      ∑ _player : ι, quittingTerminalSemanticDebtSum pair := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hsplit : ∑ player,
      (pair.2 player - reward (quittingSingletonTerminal player) player) =
      (∑ player, pair.2 player) -
        ∑ player, reward (quittingSingletonTerminal player) player :=
    Finset.sum_sub_distrib _ _
  have hsum : (Fintype.card ι : ℝ) * quittingTerminalSemanticDebtSum pair ≤
      (∑ player, pair.2 player) -
        ∑ player, reward (quittingSingletonTerminal player) player := by
    rw [hconstant, ← hsplit]
    exact Finset.sum_le_sum fun player _ => hmoat player
  have hdebt : quittingTerminalSemanticDebtSum pair =
      (∑ player, pair.2 player) - ∑ player, pair.1 player := by
    unfold quittingTerminalSemanticDebtSum quittingTerminalSemanticDebt
    exact Finset.sum_sub_distrib _ _
  linarith

/-! ## The chamber theorem -/

/-- **Social moat chamber.**  A quitting game with at least two players whose
solo quitting rewards are nonnegative and whose every terminal coalition pays a
nonpositive social total has a uniform equilibrium payoff. -/
theorem fable_socialNonpositive_exists_uniformEquilibriumPayoff
    [Nontrivial ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsingleton : ∀ player, 0 ≤ reward (quittingSingletonTerminal player) player)
    (hsocial : ∀ terminal, (∑ player, reward terminal player) ≤ 0) :
    ∃ payoff : Payoff ι, (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  haveI : Nonempty ι := ⟨(exists_pair_ne ι).choose⟩
  have hinf : 0 < quittingTerminalDebtSumInf reward :=
    quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff.mpr hno
  obtain ⟨point, -, hcarrier, hminimum, hvalue⟩ :=
    exists_minimum_terminalSemanticLawCarrier_of_debtSumInf_pos reward hinf
  have hpositive : 0 < quittingTerminalSemanticDebtSum point.1 := by
    rw [hvalue]; exact hinf
  have hmoat := fable_moat_sum reward point.1 hcarrier hminimum hpositive
  have hceiling : (∑ player, point.1.1 player) ≤ 0 :=
    fable_sum_carrierPayoff_nonpos_of_social_nonpos reward hsocial point.1 hcarrier
  have hsolo : 0 ≤ ∑ player, reward (quittingSingletonTerminal player) player :=
    Finset.sum_nonneg fun player _ => hsingleton player
  have hcard : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    have h := Fintype.one_lt_card (α := ι)
    have h2 : 2 ≤ Fintype.card ι := h
    exact_mod_cast h2
  have hscale : 2 * quittingTerminalSemanticDebtSum point.1 ≤
      (Fintype.card ι : ℝ) * quittingTerminalSemanticDebtSum point.1 :=
    mul_le_mul_of_nonneg_right hcard hpositive.le
  linarith

/-! ## The unconditional necessary condition -/

/-- Without any social hypothesis: if no uniform equilibrium payoff exists, the
prescribed social total of every carrier-minimal semantic pair is at least the
solo reward total plus `card - 1` copies of the positive literal total-debt
infimum. -/
theorem fable_counterexample_minimum_socialPayoff_lowerBound
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate) :
    (∑ player, reward (quittingSingletonTerminal player) player) +
        ((Fintype.card ι : ℝ) - 1) * quittingTerminalDebtSumInf reward ≤
      ∑ player, pair.1 player := by
  have hinf : 0 < quittingTerminalDebtSumInf reward :=
    quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff.mpr hno
  have hvalue : quittingTerminalDebtSumInf reward =
      quittingTerminalSemanticDebtSum pair :=
    quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum
      pair hpair hminimum
  have hpositive : 0 < quittingTerminalSemanticDebtSum pair := by
    rw [← hvalue]; exact hinf
  rw [hvalue]
  exact fable_moat_sum reward pair hpair hminimum hpositive

end GameTheory
