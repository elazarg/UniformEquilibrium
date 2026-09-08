import UniformEquilibrium.Quitting.Root.RationalFiniteWordSemantics
import UniformEquilibrium.Quitting.Root.TerminalSemanticSoloCapThreshold
import Mathlib.Data.Nat.Find

/-! # Executable rational first-cap-threshold scan

The search predicate and its iterates use only rational arithmetic.  The
existence proof certifying termination is erased; evaluation does not compute
real logarithms or arbitrary behavioral response suprema.
-/

namespace GameTheory

open Math.ProbabilityMassFunction

variable {players : ℕ}

/-- A prescribed-payoff/full-cap pair represented entirely over the rationals. -/
abbrev RationalQuittingSemanticPair (players : ℕ) :=
  (Fin players → ℚ) × (Fin players → ℚ)

/-- Exact rational total debt of a rational semantic pair. -/
def rationalQuittingSemanticDebtSum
    (pair : RationalQuittingSemanticPair players) : ℚ :=
  ∑ who, (pair.2 who - pair.1 who)

/-- One exact rational root-prefix operation on a rational semantic pair. -/
def rationalQuittingSemanticPrefix
    (reward : RationalQuittingReward players)
    (root : RationalQuittingRoot players)
    (pair : RationalQuittingSemanticPair players) :
    RationalQuittingSemanticPair players :=
  (rationalQuittingRootExpectedPayoff reward pair.1 root,
    fun who => max
      (rationalQuittingRootPurePayoff reward pair.1 root who true)
      (rationalQuittingRootPurePayoff reward
        (Function.update pair.1 who (pair.2 who)) root who false))

/-- Cast a rational semantic pair into the real terminal-semantic interface. -/
def RationalQuittingSemanticPair.toReal
    (pair : RationalQuittingSemanticPair players) :
    QuittingTerminalSemanticPair (Fin players) :=
  (fun who => (pair.1 who : ℝ), fun who => (pair.2 who : ℝ))

theorem quittingTerminalSemanticDebtSum_rational_eq_cast
    (pair : RationalQuittingSemanticPair players) :
    quittingTerminalSemanticDebtSum pair.toReal =
      (rationalQuittingSemanticDebtSum pair : ℝ) := by
  rw [quittingTerminalSemanticDebtSum, rationalQuittingSemanticDebtSum]
  push_cast
  rfl

/-- The actual finite source has the rationally computed total debt. -/
theorem quittingTerminalSemanticDebtSum_rationalFiniteWord_eq_cast
    (reward : RationalQuittingReward players)
    (roots : List (RationalQuittingRoot players)) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair (rationalQuittingRewardToReal reward)
          (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
            (roots.map RationalQuittingRoot.toPMF)
            (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward)))) =
      (rationalQuittingSemanticDebtSum
        (rationalQuittingFiniteWordSemanticPair reward roots) : ℝ) := by
  rw [quittingTerminalSemanticPair_rationalFiniteWord_eq_cast]
  simpa [RationalQuittingSemanticPair.toReal] using
    (quittingTerminalSemanticDebtSum_rational_eq_cast
      (rationalQuittingFiniteWordSemanticPair reward roots))

/-- Rational prefixing agrees exactly with the real semantic prefix. -/
theorem quittingTerminalSemanticPrefix_rational_eq_cast
    (reward : RationalQuittingReward players)
    (root : RationalQuittingRoot players)
    (pair : RationalQuittingSemanticPair players) :
    quittingTerminalSemanticPrefix (rationalQuittingRewardToReal reward)
        root.toPMF pair.toReal =
      (rationalQuittingSemanticPrefix reward root pair).toReal := by
  apply Prod.ext
  · funext who
    exact quittingRootExpectedPayoff_rationalQuitting_eq_cast
      reward pair.1 root who
  · funext who
    have hquit := quittingRootPurePayoff_rationalQuitting_eq_cast
      reward pair.1 root who true
    have hcontinue := quittingRootPurePayoff_rationalQuitting_eq_cast
      reward (Function.update pair.1 who (pair.2 who)) root who false
    have hupdate :
        Function.update (fun player => (pair.1 player : ℝ)) who (pair.2 who : ℝ) =
          fun player => ((Function.update pair.1 who (pair.2 who)) player : ℝ) := by
      funext player
      by_cases hplayer : player = who
      · subst player
        simp
      · simp [hplayer]
    simp only [if_true] at hquit
    simp only [Bool.false_eq_true, if_false] at hcontinue
    change max
        (quittingRootQuitPayoff (rationalQuittingRewardToReal reward)
          (fun player => (pair.1 player : ℝ)) root.toPMF who)
        (quittingRootContinuePayoff (rationalQuittingRewardToReal reward)
          (Function.update (fun player => (pair.1 player : ℝ)) who
            (pair.2 who : ℝ)) root.toPMF who) = _
    rw [hupdate, hquit, hcontinue]
    change max
        (rationalQuittingRootPurePayoff reward pair.1 root who true : ℝ)
        (rationalQuittingRootPurePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who false : ℝ) =
      (max
        (rationalQuittingRootPurePayoff reward pair.1 root who true)
        (rationalQuittingRootPurePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who false) : ℚ)
    exact (Rat.cast_max _ _).symm

/-- The rational solo root with the supplied hazard.  Clamping makes this a
total executable definition on arbitrary rational inputs. -/
def rationalQuittingSoloRoot (owner : Fin players) (hazard : ℚ) :
    RationalQuittingRoot players where
  probability := fun who => if who = owner then max 0 (min 1 hazard) else 0
  nonnegative := by
    intro who
    split_ifs
    · exact le_max_left _ _
    · rfl
  le_one := by
    intro who
    split_ifs
    · exact max_le (by norm_num) (min_le_left _ _)
    · norm_num

theorem rationalQuittingSoloRoot_probability_of_mem_Icc
    (owner : Fin players) {hazard : ℚ} (hhazard : hazard ∈ Set.Icc (0 : ℚ) 1)
    (who : Fin players) :
    (rationalQuittingSoloRoot owner hazard).probability who =
      if who = owner then hazard else 0 := by
  change (if who = owner then max 0 (min 1 hazard) else 0) = _
  simp [hhazard.1, hhazard.2]

theorem rationalQuittingSoloRoot_toPMF_eq
    (owner : Fin players) {hazard : ℚ} (hhazard : hazard ∈ Set.Icc (0 : ℚ) 1) :
    (rationalQuittingSoloRoot owner hazard).toPMF =
      quittingSoloStationaryRoot owner
        (quittingHazardCoin (hazard : ℝ)
          (by exact_mod_cast hhazard.1) (by exact_mod_cast hhazard.2)) := by
  funext who
  apply eq_of_forall_toReal_eq
  intro action
  by_cases hwho : who = owner
  · subst who
    cases action <;>
      simp [quittingSoloStationaryRoot,
        rationalQuittingSoloRoot_probability_of_mem_Icc owner hhazard]
  · cases action <;>
      simp [quittingSoloStationaryRoot, hwho,
        rationalQuittingSoloRoot_probability_of_mem_Icc owner hhazard,
        PMF.pure_apply]

/-- Repeated exact rational prefixing by one solo root. -/
def rationalQuittingSoloSemanticIterate
    (reward : RationalQuittingReward players) (owner : Fin players)
    (hazard : ℚ) (source : RationalQuittingSemanticPair players) (steps : ℕ) :
    RationalQuittingSemanticPair players :=
  (rationalQuittingSemanticPrefix reward
    (rationalQuittingSoloRoot owner hazard))^[steps] source

@[simp] theorem rationalQuittingSoloSemanticIterate_zero
    (reward : RationalQuittingReward players) (owner : Fin players)
    (hazard : ℚ) (source : RationalQuittingSemanticPair players) :
    rationalQuittingSoloSemanticIterate reward owner hazard source 0 = source := by
  simp [rationalQuittingSoloSemanticIterate]

theorem rationalQuittingSoloSemanticIterate_succ
    (reward : RationalQuittingReward players) (owner : Fin players)
    (hazard : ℚ) (source : RationalQuittingSemanticPair players) (steps : ℕ) :
    rationalQuittingSoloSemanticIterate reward owner hazard source (steps + 1) =
      rationalQuittingSemanticPrefix reward (rationalQuittingSoloRoot owner hazard)
        (rationalQuittingSoloSemanticIterate reward owner hazard source steps) := by
  simp [rationalQuittingSoloSemanticIterate, Function.iterate_succ_apply']

theorem quittingSoloSemanticIterate_rational_eq_cast
    (reward : RationalQuittingReward players) (owner : Fin players)
    {hazard : ℚ} (hhazard : hazard ∈ Set.Icc (0 : ℚ) 1)
    (source : RationalQuittingSemanticPair players) (steps : ℕ) :
    quittingSoloSemanticIterate (rationalQuittingRewardToReal reward) owner
        (quittingHazardCoin (hazard : ℝ)
          (by exact_mod_cast hhazard.1) (by exact_mod_cast hhazard.2))
        source.toReal steps =
      (rationalQuittingSoloSemanticIterate reward owner hazard source steps).toReal := by
  rcases hhazard with ⟨hhazard0, hhazard1⟩
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [quittingSoloSemanticIterate_succ,
        rationalQuittingSoloSemanticIterate_succ,
        ← rationalQuittingSoloRoot_toPMF_eq owner ⟨hhazard0, hhazard1⟩]
      rw [ih, quittingTerminalSemanticPrefix_rational_eq_cast]

/-- Decidable rational test that some coordinate's cap has reached the
specified singleton-margin threshold after `steps` solo rows. -/
def rationalSoloCapThresholdHit
    (reward : RationalQuittingReward players) (owner : Fin players)
    (hazard threshold : ℚ) (source : RationalQuittingSemanticPair players)
    (steps : ℕ) : Prop :=
  ∃ crossing : Fin players,
    (rationalQuittingSoloSemanticIterate reward owner hazard source steps).2 crossing -
      reward (quittingSingletonTerminal crossing) crossing ≤ threshold

instance rationalSoloCapThresholdHit_decidable
    (reward : RationalQuittingReward players) (owner : Fin players)
    (hazard threshold : ℚ) (source : RationalQuittingSemanticPair players)
    (steps : ℕ) :
    Decidable (rationalSoloCapThresholdHit reward owner hazard threshold source steps) :=
  by
    unfold rationalSoloCapThresholdHit
    infer_instance

/-- The earliest rational first-hit index. `Nat.find` evaluates as a linear
decidable search; its existence proof is only a termination certificate. -/
def rationalFirstSoloCapThresholdIndex
    (reward : RationalQuittingReward players) (owner : Fin players)
    (hazard threshold : ℚ) (source : RationalQuittingSemanticPair players)
    (hexists : ∃ steps,
      rationalSoloCapThresholdHit reward owner hazard threshold source steps) : ℕ :=
  Nat.find hexists

theorem rationalFirstSoloCapThresholdIndex_spec
    (reward : RationalQuittingReward players) (owner : Fin players)
    (hazard threshold : ℚ) (source : RationalQuittingSemanticPair players)
    (hexists : ∃ steps,
      rationalSoloCapThresholdHit reward owner hazard threshold source steps) :
    rationalSoloCapThresholdHit reward owner hazard threshold source
      (rationalFirstSoloCapThresholdIndex reward owner hazard threshold source hexists) :=
  Nat.find_spec hexists

theorem rationalFirstSoloCapThresholdIndex_le
    (reward : RationalQuittingReward players) (owner : Fin players)
    (hazard threshold : ℚ) (source : RationalQuittingSemanticPair players)
    (hexists : ∃ steps,
      rationalSoloCapThresholdHit reward owner hazard threshold source steps)
    {steps : ℕ}
    (hhit : rationalSoloCapThresholdHit reward owner hazard threshold source steps) :
    rationalFirstSoloCapThresholdIndex reward owner hazard threshold source hexists ≤ steps :=
  Nat.find_min' hexists hhit

theorem rationalFirstSoloCapThresholdIndex_before
    (reward : RationalQuittingReward players) (owner : Fin players)
    (hazard threshold : ℚ) (source : RationalQuittingSemanticPair players)
    (hexists : ∃ steps,
      rationalSoloCapThresholdHit reward owner hazard threshold source steps)
    {steps : ℕ}
    (hbefore : steps < rationalFirstSoloCapThresholdIndex
      reward owner hazard threshold source hexists) :
    ¬rationalSoloCapThresholdHit reward owner hazard threshold source steps :=
  Nat.find_min hexists hbefore

/-- One crossing coordinate at the earliest rational hit. `Fin.find` is a
finite executable scan over player indices. -/
def rationalFirstSoloCapThresholdPlayer
    (reward : RationalQuittingReward players) (owner : Fin players)
    (hazard threshold : ℚ) (source : RationalQuittingSemanticPair players)
    (hexists : ∃ steps,
      rationalSoloCapThresholdHit reward owner hazard threshold source steps) :
    Fin players :=
  Fin.find (fun crossing =>
    (rationalQuittingSoloSemanticIterate reward owner hazard source
        (rationalFirstSoloCapThresholdIndex reward owner hazard threshold source hexists)).2
          crossing - reward (quittingSingletonTerminal crossing) crossing ≤ threshold) <|
    rationalFirstSoloCapThresholdIndex_spec
      reward owner hazard threshold source hexists

theorem rationalFirstSoloCapThresholdPlayer_spec
    (reward : RationalQuittingReward players) (owner : Fin players)
    (hazard threshold : ℚ) (source : RationalQuittingSemanticPair players)
    (hexists : ∃ steps,
      rationalSoloCapThresholdHit reward owner hazard threshold source steps) :
    (rationalQuittingSoloSemanticIterate reward owner hazard source
        (rationalFirstSoloCapThresholdIndex reward owner hazard threshold source hexists)).2
          (rationalFirstSoloCapThresholdPlayer
            reward owner hazard threshold source hexists) -
      reward (quittingSingletonTerminal
        (rationalFirstSoloCapThresholdPlayer
          reward owner hazard threshold source hexists))
        (rationalFirstSoloCapThresholdPlayer
          reward owner hazard threshold source hexists) ≤ threshold := by
  unfold rationalFirstSoloCapThresholdPlayer
  exact Fin.find_spec <| rationalFirstSoloCapThresholdIndex_spec
    reward owner hazard threshold source hexists

/-- Strict preemption certifies termination of the executable rational scan.
The proof also places its earliest hit below the sharper real logarithmic
horizon; that logarithm is absent from the search computation itself. -/
theorem exists_rationalFirstSoloCapThresholdIndex_le_logHorizon
    (reward : RationalQuittingReward players)
    (sourceRoots : List (RationalQuittingRoot players))
    (owner blocker : Fin players) (M hazard : ℚ)
    (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hhazard0 : 0 < hazard) (hhazard1 : hazard < 1)
    (hinitial : ∀ player,
      4 * M * hazard <
        (rationalQuittingFiniteWordSemanticPair reward sourceRoots).2 player -
          reward (quittingSingletonTerminal player) player)
    (hpreempted : 0 < reward (quittingSingletonTerminal blocker) blocker -
      reward (quittingSingletonTerminal owner) blocker) :
    let source := rationalQuittingFiniteWordSemanticPair reward sourceRoots
    let threshold := 4 * M * hazard
    ∃ hexists : ∃ steps,
        rationalSoloCapThresholdHit reward owner hazard threshold source steps,
      rationalFirstSoloCapThresholdIndex
          reward owner hazard threshold source hexists ≤
        quittingSoloCapThresholdHorizon (M : ℝ) (hazard : ℝ)
          ((reward (quittingSingletonTerminal blocker) blocker -
            reward (quittingSingletonTerminal owner) blocker : ℚ) : ℝ) := by
  dsimp only
  let source : RationalQuittingSemanticPair players :=
    rationalQuittingFiniteWordSemanticPair reward sourceRoots
  let profile := quittingLiteralRootStackProfile
    (rationalQuittingRewardToReal reward)
    (sourceRoots.map RationalQuittingRoot.toPMF)
    (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))
  have hpair : quittingTerminalSemanticPair
      (rationalQuittingRewardToReal reward) profile = source.toReal := by
    dsimp only [profile, source]
    simpa [RationalQuittingSemanticPair.toReal] using
      (quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward sourceRoots)
  have hsource : source.toReal ∈
      quittingTerminalSemanticCarrier (rationalQuittingRewardToReal reward) := by
    rw [← hpair]
    exact subset_closure (Set.mem_range_self profile)
  have hrewardReal : ∀ terminal player,
      |rationalQuittingRewardToReal reward terminal player| ≤ (M : ℝ) := by
    intro terminal player
    unfold rationalQuittingRewardToReal
    exact_mod_cast hreward terminal player
  have hne : blocker ≠ owner := by
    intro heq
    subst blocker
    simp at hpreempted
  have hinitialReal : ∀ player,
      4 * (M : ℝ) * (hazard : ℝ) < source.toReal.2 player -
        rationalQuittingRewardToReal reward
          (quittingSingletonTerminal player) player := by
    intro player
    change 4 * (M : ℝ) * (hazard : ℝ) <
      ((rationalQuittingFiniteWordSemanticPair reward sourceRoots).2 player : ℝ) -
        (reward (quittingSingletonTerminal player) player : ℝ)
    exact_mod_cast hinitial player
  have hpreemptedReal : 0 <
      rationalQuittingRewardToReal reward
          (quittingSingletonTerminal blocker) blocker -
        rationalQuittingRewardToReal reward
          (quittingSingletonTerminal owner) blocker := by
    unfold rationalQuittingRewardToReal
    exact_mod_cast hpreempted
  obtain ⟨steps, crossing, _, hstepsLe, _, _, hcrossing, _, _, _⟩ :=
    exists_first_solo_capThreshold_hit
      (rationalQuittingRewardToReal reward) source.toReal hne
      (M := (M : ℝ)) (θ := (hazard : ℝ))
      (by exact_mod_cast hM) hrewardReal hsource
      (by exact_mod_cast hhazard0) (by exact_mod_cast hhazard1)
      hinitialReal hpreemptedReal
  have hhit : rationalSoloCapThresholdHit reward owner hazard
      (4 * M * hazard) source steps := by
    refine ⟨crossing, ?_⟩
    have hupper := hcrossing.2
    rw [quittingSoloSemanticIterate_rational_eq_cast
      reward owner ⟨hhazard0.le, hhazard1.le⟩ source steps] at hupper
    simp only [RationalQuittingSemanticPair.toReal,
      rationalQuittingRewardToReal] at hupper
    exact_mod_cast hupper
  let hexists : ∃ index,
      rationalSoloCapThresholdHit reward owner hazard
        (4 * M * hazard) source index := ⟨steps, hhit⟩
  refine ⟨hexists, ?_⟩
  have hstepsLe' : steps ≤
      quittingSoloCapThresholdHorizon (M : ℝ) (hazard : ℝ)
        ((reward (quittingSingletonTerminal blocker) blocker -
          reward (quittingSingletonTerminal owner) blocker : ℚ) : ℝ) := by
    simpa only [rationalQuittingRewardToReal, Rat.cast_sub] using hstepsLe
  exact (rationalFirstSoloCapThresholdIndex_le
    reward owner hazard (4 * M * hazard) source hexists hhit).trans hstepsLe'

end GameTheory
