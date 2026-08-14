import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanMinimizer

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

/-! ## Simplex coordinates are at most one -/

omit [DecidableEq ι] in
/-- Every mixed-action simplex coordinate is at most one. -/
theorem simplexCoord_le_one (root : QuittingRootSimplex ι) (who : ι)
    (action : Bool) : (root who : Bool → ℝ) action ≤ 1 := by
  have hsum : (root who).val true + (root who).val false = 1 := by
    have hone := (root who).property.2
    rwa [Fintype.sum_bool] at hone
  have htrue : 0 ≤ (root who).val true := (root who).property.1 true
  have hfalse : 0 ≤ (root who).val false := (root who).property.1 false
  change (root who).val action ≤ 1
  cases action with
  | false => linarith
  | true => linarith

/-- Every displayed opponent-continuation factor is at most one. -/
theorem opponentContinueMass_le_one (cutoff : ℕ)
    (path : QuittingFiniteNashBellmanPath ι cutoff) (who : ι) (time : ℕ) :
    quittingFiniteNashBellmanPathOpponentContinueMass cutoff path who time
      ≤ 1 := by
  classical
  unfold quittingFiniteNashBellmanPathOpponentContinueMass
  split_ifs
  · exact Finset.prod_le_one
      (fun player _ => (path _).2 player |>.property.1 false)
      (fun player _ => simplexCoord_le_one (path _).2 player false)
  · exact le_rfl

/-! ## Deleting and reinstating the first displayed stage -/

/-- Delete the first displayed stage of a chain. -/
def suffixPath (cutoff : ℕ)
    (path : QuittingFiniteNashBellmanPath ι (cutoff + 1)) :
    QuittingFiniteNashBellmanPath ι cutoff :=
  fun time => path time.succ

/-- The suffix of an admissible chain is admissible one cutoff lower. -/
theorem suffixPath_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (cutoff : ℕ)
    (path : QuittingFiniteNashBellmanPath ι (cutoff + 1))
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (cutoff + 1)) :
    suffixPath cutoff path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff := by
  refine ⟨fun time => hpath.1 _, ?_, fun time => ?_⟩
  · change (path (Fin.last cutoff).succ).1 = 0
    rw [Fin.succ_last]
    exact hpath.2.1
  · have hedge := hpath.2.2 time.succ
    rw [← Fin.succ_castSucc] at hedge
    exact hedge

/-- Opponent-continuation factors of the suffix are the shifted factors of the
original chain. -/
theorem opponentContinueMass_suffixPath (cutoff : ℕ)
    (path : QuittingFiniteNashBellmanPath ι (cutoff + 1)) (who : ι)
    {time : ℕ} (htime : time < cutoff) :
    quittingFiniteNashBellmanPathOpponentContinueMass (cutoff + 1) path who
        (time + 1) =
      quittingFiniteNashBellmanPathOpponentContinueMass cutoff
        (suffixPath cutoff path) who time := by
  unfold quittingFiniteNashBellmanPathOpponentContinueMass
  rw [dif_pos (Nat.succ_lt_succ htime), dif_pos htime]
  rfl

/-- Reinstating the first stage multiplies opponent survival by that stage's
opponent-continuation mass. -/
theorem opponentSurvival_succ (cutoff : ℕ)
    (path : QuittingFiniteNashBellmanPath ι (cutoff + 1)) (who : ι) :
    quittingFiniteNashBellmanPathOpponentSurvival (cutoff + 1) path who =
      quittingFiniteNashBellmanPathOpponentSurvival cutoff
          (suffixPath cutoff path) who *
        quittingFiniteNashBellmanPathOpponentContinueMass (cutoff + 1) path
          who 0 := by
  unfold quittingFiniteNashBellmanPathOpponentSurvival
  rw [Finset.prod_range_succ']
  congr 1
  exact Finset.prod_congr rfl fun time htime =>
    opponentContinueMass_suffixPath cutoff path who (Finset.mem_range.mp htime)

/-- Reinstating a stage cannot increase the aggregate surviving debt. -/
theorem aggregateDebt_le_suffixPath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (cutoff : ℕ)
    (path : QuittingFiniteNashBellmanPath ι (cutoff + 1)) :
    quittingFiniteNashBellmanPathAggregateDebt reward (cutoff + 1) path ≤
      quittingFiniteNashBellmanPathAggregateDebt reward cutoff
        (suffixPath cutoff path) := by
  refine Finset.sum_le_sum fun who _ => ?_
  unfold quittingFiniteNashBellmanPathPlayerDebt
  rw [opponentSurvival_succ]
  have hnn : 0 ≤ quittingFiniteNashBellmanPathOpponentSurvival cutoff
      (suffixPath cutoff path) who := by
    unfold quittingFiniteNashBellmanPathOpponentSurvival
    exact Finset.prod_nonneg fun time _ =>
      quittingFiniteNashBellmanPathOpponentContinueMass_nonneg cutoff
        (suffixPath cutoff path) who time
  have hsurv : quittingFiniteNashBellmanPathOpponentSurvival cutoff
        (suffixPath cutoff path) who *
      quittingFiniteNashBellmanPathOpponentContinueMass (cutoff + 1) path
        who 0 ≤
      quittingFiniteNashBellmanPathOpponentSurvival cutoff
        (suffixPath cutoff path) who := by
    calc quittingFiniteNashBellmanPathOpponentSurvival cutoff
            (suffixPath cutoff path) who *
          quittingFiniteNashBellmanPathOpponentContinueMass (cutoff + 1) path
            who 0
        ≤ quittingFiniteNashBellmanPathOpponentSurvival cutoff
            (suffixPath cutoff path) who * 1 :=
          mul_le_mul_of_nonneg_left
            (opponentContinueMass_le_one (cutoff + 1) path who 0) hnn
      _ = quittingFiniteNashBellmanPathOpponentSurvival cutoff
            (suffixPath cutoff path) who := mul_one _
  exact mul_le_mul_of_nonneg_right hsurv
    (le_max_left 0 (reward (quittingSingletonTerminal who) who))

/-- Reinstate a first stage in front of a chain. -/
def prependPath (cutoff : ℕ) (head : QuittingNashBellmanPoint ι)
    (path : QuittingFiniteNashBellmanPath ι cutoff) :
    QuittingFiniteNashBellmanPath ι (cutoff + 1) :=
  Fin.cases head path

omit [DecidableEq ι] in
@[simp] theorem suffixPath_prependPath (cutoff : ℕ)
    (head : QuittingNashBellmanPoint ι)
    (path : QuittingFiniteNashBellmanPath ι cutoff) :
    suffixPath cutoff (prependPath cutoff head path) = path := by
  funext time
  simp [suffixPath, prependPath]

/-- A bounded exact predecessor in front of an admissible chain is again an
admissible chain. -/
theorem prependPath_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (cutoff : ℕ)
    (head : QuittingNashBellmanPoint ι)
    (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hhead : head ∈ quittingNashBellmanBox (quittingRewardBound reward))
    (hedge : IsQuittingNashBellmanEdge reward head (path 0))
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    prependPath cutoff head path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (cutoff + 1) := by
  refine ⟨fun time => ?_, ?_, fun time => ?_⟩
  · refine Fin.cases ?_ ?_ time
    · simpa [prependPath] using hhead
    · intro i
      simpa [prependPath] using hpath.1 i
  · show (prependPath cutoff head path (Fin.last (cutoff + 1))).1 = 0
    unfold prependPath
    rw [← Fin.succ_last, Fin.cases_succ]
    exact hpath.2.1
  · refine Fin.cases ?_ ?_ time
    · unfold prependPath
      rw [Fin.castSucc_zero, Fin.cases_zero, Fin.cases_succ]
      exact hedge
    · intro i
      unfold prependPath
      rw [← Fin.succ_castSucc, Fin.cases_succ, Fin.cases_succ]
      exact hpath.2.2 i

/-! ## The minimum debt is antitone -/

/-- **Mined theorem.**  The attained minimum aggregate surviving debt is
antitone in the cutoff. -/
theorem minDebt_antitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Antitone (quittingFiniteZeroBoundaryNashBellmanMinDebt reward) := by
  refine antitone_nat_of_succ_le fun cutoff => ?_
  have hmem :=
    quittingFiniteZeroBoundaryNashBellmanDebtMinimizer_mem reward cutoff
  obtain ⟨head, hheadBox, hheadEdge⟩ :=
    exists_quittingNashBellmanPredecessor reward
      (abs_reward_le_quittingRewardBound reward)
      (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff 0)
      (hmem.1 0)
  have hprepend := prependPath_mem reward cutoff head
    (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward cutoff)
    hheadBox hheadEdge hmem
  calc quittingFiniteZeroBoundaryNashBellmanMinDebt reward (cutoff + 1)
      ≤ quittingFiniteNashBellmanPathAggregateDebt reward (cutoff + 1)
          (prependPath cutoff head
            (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward
              cutoff)) :=
        quittingFiniteZeroBoundaryNashBellmanMinDebt_le reward (cutoff + 1)
          _ hprepend
    _ ≤ quittingFiniteNashBellmanPathAggregateDebt reward cutoff
          (suffixPath cutoff (prependPath cutoff head
            (quittingFiniteZeroBoundaryNashBellmanDebtMinimizer reward
              cutoff))) :=
        aggregateDebt_le_suffixPath reward cutoff _
    _ = quittingFiniteZeroBoundaryNashBellmanMinDebt reward cutoff := by
        rw [suffixPath_prependPath]
        rfl

/-- The minimum debt converges to its infimum. -/
theorem minDebt_tendsto_iInf
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Tendsto (quittingFiniteZeroBoundaryNashBellmanMinDebt reward) atTop
      (𝓝 (⨅ cutoff, quittingFiniteZeroBoundaryNashBellmanMinDebt reward
        cutoff)) := by
  refine tendsto_atTop_ciInf (minDebt_antitone reward) ⟨0, ?_⟩
  rintro x ⟨cutoff, rfl⟩
  exact quittingFiniteZeroBoundaryNashBellmanMinDebt_nonneg reward cutoff

/-- Vanishing infimum and vanishing limit are the same criterion. -/
theorem minDebt_iInf_eq_zero_iff_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (⨅ cutoff, quittingFiniteZeroBoundaryNashBellmanMinDebt reward cutoff)
        = 0 ↔
      Tendsto (quittingFiniteZeroBoundaryNashBellmanMinDebt reward) atTop
        (𝓝 0) := by
  constructor
  · intro hinf
    have := minDebt_tendsto_iInf reward
    rwa [hinf] at this
  · intro hlimit
    exact tendsto_nhds_unique (minDebt_tendsto_iInf reward) hlimit

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
  (minDebt_antitone reward hcutoff).trans
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
  exact minDebt_antitone reward (Nat.zero_le cutoff)

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
