import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanDebtMonotonicity

/-!
# E35: monotonicity and non-necessity of the minimum finite quitting debt

Proof-mining probe for the finite quitting Nash--Bellman chain lane.

Three claims are checked here.

1. **Antitone.** `quittingFiniteZeroBoundaryNashBellmanMinDebt` is antitone in
   the cutoff, hence converges to its infimum.  Deleting the first displayed
   stage of an admissible chain is admissible one cutoff lower, and
   reinstating a stage multiplies every playerwise debt by an
   opponent-continuation mass in `[0,1]`; a predecessor always exists, so the
   minimum cannot increase.  Consequently one exhibited chain at a single
   cutoff bounds the minimum debt at every larger cutoff.

2. **Boundary value.** At cutoff zero the debt is path-independent and equals
   the positive-solo mass, so that sum bounds every later minimum debt, and a
   game all of whose solo payoffs are nonpositive has identically zero minimum
   debt.

3. **Non-necessity.** The opponent-survival factor of a player is a product
   over that player's *opponents*.  With a single player it is an empty
   product, so a one-player quitting game with a positive solo payoff has
   minimum debt exactly that payoff at every cutoff, while its uniform
   equilibrium is obvious (quit at stage zero).  Hence vanishing minimum debt
   is sufficient but not necessary, and the residual question concerns
   `2 ≤ card ι` only.  The uniform-equilibrium half of this fence is argued by
   hand in the report, not here.

This is a probe: it checks the theorems it declares and is not imported by
any production module.
-/


noncomputable section

namespace GameTheory.Experiment35

open Filter Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One exhibited chain bounds the minimum debt at every larger cutoff. -/
theorem minDebt_le_of_chain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {cutoff target : ℕ}
    (hcutoff : cutoff ≤ target)
    (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    {ε : ℝ}
    (hdebt : quittingFiniteNashBellmanPathAggregateDebt reward cutoff path
      ≤ ε) :
    quittingFiniteZeroBoundaryNashBellmanMinDebt reward target ≤ ε :=
  (_root_.GameTheory.antitone_quittingFiniteZeroBoundaryNashBellmanMinDebt
    reward hcutoff).trans
    ((quittingFiniteZeroBoundaryNashBellmanMinDebt_le reward cutoff path
      hpath).trans hdebt)

/-! ## The boundary value at cutoff zero -/

/-- At cutoff zero the aggregate debt is path-independent. -/
theorem aggregateDebt_cutoff_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : QuittingFiniteNashBellmanPath ι 0) :
    quittingFiniteNashBellmanPathAggregateDebt reward 0 path =
      ∑ who, max 0 (reward (quittingSingletonTerminal who) who) := by
  unfold quittingFiniteNashBellmanPathAggregateDebt
    quittingFiniteNashBellmanPathPlayerDebt
    quittingFiniteNashBellmanPathOpponentSurvival
  simp

/-- The minimum debt at cutoff zero is the positive-solo mass. -/
theorem minDebt_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingFiniteZeroBoundaryNashBellmanMinDebt reward 0 =
      ∑ who, max 0 (reward (quittingSingletonTerminal who) who) := by
  unfold quittingFiniteZeroBoundaryNashBellmanMinDebt
  exact aggregateDebt_cutoff_zero reward _

/-- The positive-solo mass bounds the minimum debt at every cutoff. -/
theorem minDebt_le_positiveSoloMass
  (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (cutoff : ℕ) :
    quittingFiniteZeroBoundaryNashBellmanMinDebt reward cutoff ≤
      ∑ who, max 0 (reward (quittingSingletonTerminal who) who) := by
  rw [← minDebt_zero reward]
  exact _root_.GameTheory.antitone_quittingFiniteZeroBoundaryNashBellmanMinDebt
    reward (Nat.zero_le cutoff)

/-- Nonpositive solo payoffs make the criterion fire at once: this is the
Never branch seen through the finite-chain interface, and the interface's
nonvacuity probe. -/
theorem minDebt_eq_zero_of_solo_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsolo : ∀ who, reward (quittingSingletonTerminal who) who ≤ 0)
    (cutoff : ℕ) :
    quittingFiniteZeroBoundaryNashBellmanMinDebt reward cutoff = 0 := by
  refine le_antisymm ?_
    (quittingFiniteZeroBoundaryNashBellmanMinDebt_nonneg reward cutoff)
  refine (minDebt_le_positiveSoloMass reward cutoff).trans (le_of_eq ?_)
  exact Finset.sum_eq_zero fun who _ => max_eq_left (hsolo who)

/-! ## Non-necessity: the one-player fence -/

/-- The one-player quitting table with solo payoff `payoff`. -/
def onePlayerReward (payoff : ℝ) :
    {S : Finset (Fin 1) // S.Nonempty} → Payoff (Fin 1) :=
  fun _ _ => payoff

/-- With a single player the opponent-continuation mass is an empty product. -/
theorem onePlayer_opponentContinueMass (cutoff : ℕ)
    (path : QuittingFiniteNashBellmanPath (Fin 1) cutoff) (who : Fin 1)
    (time : ℕ) :
    quittingFiniteNashBellmanPathOpponentContinueMass cutoff path who time
      = 1 := by
  classical
  unfold quittingFiniteNashBellmanPathOpponentContinueMass
  have herase : (Finset.univ.erase who) = (∅ : Finset (Fin 1)) := by
    ext player
    simp [Finset.mem_erase, Subsingleton.elim player who]
  split_ifs
  · rw [herase, Finset.prod_empty]
  · rfl

/-- With a single player the aggregate debt never decays. -/
theorem onePlayer_aggregateDebt (payoff : ℝ) (cutoff : ℕ)
    (path : QuittingFiniteNashBellmanPath (Fin 1) cutoff) :
    quittingFiniteNashBellmanPathAggregateDebt (onePlayerReward payoff) cutoff
        path = max 0 payoff := by
  unfold quittingFiniteNashBellmanPathAggregateDebt
    quittingFiniteNashBellmanPathPlayerDebt
    quittingFiniteNashBellmanPathOpponentSurvival
  rw [Finset.sum_congr rfl (g := fun _ => max 0 payoff) ?_]
  · simp
  · intro who _
    rw [Finset.prod_congr rfl fun time _ =>
      onePlayer_opponentContinueMass cutoff path who time]
    simp [onePlayerReward]

/-- **Mined fence.**  A one-player quitting game with a positive solo payoff
has minimum debt exactly that payoff at every cutoff, although it obviously
has a uniform-equilibrium payoff.  Vanishing minimum debt is therefore
sufficient but not necessary. -/
theorem onePlayer_minDebt (payoff : ℝ) (cutoff : ℕ) :
    quittingFiniteZeroBoundaryNashBellmanMinDebt (onePlayerReward payoff)
      cutoff = max 0 payoff := by
  unfold quittingFiniteZeroBoundaryNashBellmanMinDebt
  exact onePlayer_aggregateDebt payoff cutoff _

theorem onePlayer_iInf_ne_zero {payoff : ℝ} (hpayoff : 0 < payoff) :
    (⨅ cutoff, quittingFiniteZeroBoundaryNashBellmanMinDebt
      (onePlayerReward payoff) cutoff) ≠ 0 := by
  have hconst : (fun cutoff : ℕ =>
      quittingFiniteZeroBoundaryNashBellmanMinDebt (onePlayerReward payoff)
        cutoff) = fun _ => payoff := by
    funext cutoff
    rw [onePlayer_minDebt]
    exact max_eq_right hpayoff.le
  rw [hconst, ciInf_const]
  exact ne_of_gt hpayoff

end GameTheory.Experiment35
