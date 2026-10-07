import UniformEquilibrium.Quitting.Cycles.CrossedMatchingPhaseSource
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Literal crossed-matching boundary examples

Signed own levels and all unused coordinates remain arbitrary. The balanced
half-hazard construction needs no matching sign or Q assumption. A separate
weak-boundary example has no positive odds solution but does have a pure-pair
uniform payoff. None of these screens is an obstruction to existence of UE.
-/

noncomputable section

namespace GameTheory.PairedCycle.CrossedMatchingBoundaryExamples

open Math.CrossedMatching Math.LinearProgramming Math.PairedAffine
open QuittingSureSetOwnerRepair
open scoped Matrix

abbrev Reward := TwoPairOdds.Reward

/-- The designated singleton increment need not be positive. All unspecified
coordinates are retained literally from the supplied completion. -/
def familyReward (own gap increment K : Payoff (Fin 4)) (unused : Reward) : Reward :=
  fun terminal player =>
    if terminal.val = {player} then own player
    else if terminal.val = {favorite player} then own player + gap player
    else if terminal.val = {scheduled player} then own player - 1
    else if terminal.val = {other player} then own player - 1
    else if terminal.val = {player, scheduled player} then own player + increment player
    else if terminal.val = {favorite player, other player} then own player + K player
    else if terminal.val = {player, favorite player} ∨
        terminal.val = {player, other player} ∨
        terminal.val = {player, favorite player, other player} then own player
    else unused terminal player

theorem family_unused (own gap increment K : Payoff (Fin 4)) (unused : Reward)
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (player : Fin 4)
    (hown : terminal.val ≠ {player}) (hf : terminal.val ≠ {favorite player})
    (ha : terminal.val ≠ {scheduled player}) (ho : terminal.val ≠ {other player})
    (hpair : terminal.val ≠ {player, scheduled player})
    (hpassive : terminal.val ≠ {favorite player, other player})
    (hcapf : terminal.val ≠ {player, favorite player})
    (hcapo : terminal.val ≠ {player, other player})
    (hjoint : terminal.val ≠ {player, favorite player, other player}) :
    familyReward own gap increment K unused terminal player = unused terminal player := by
  simp only [familyReward, hown, hf, ha, ho, hpair, hpassive, hcapf, hcapo, hjoint,
    or_false, ite_false]

theorem family_singletons (own gap increment K : Payoff (Fin 4)) (unused : Reward)
    (player : Fin 4) :
    singleton (familyReward own gap increment K unused) player = own player ∧
    (familyReward own gap increment K unused)
        (quittingSingletonTerminal (favorite player)) player = own player + gap player ∧
    (familyReward own gap increment K unused)
        (quittingSingletonTerminal (scheduled player)) player = own player - 1 ∧
    (familyReward own gap increment K unused)
        (quittingSingletonTerminal (other player)) player = own player - 1 := by
  fin_cases player <;>
    norm_num +decide [familyReward, PairedCycle.singleton, quittingSingletonTerminal,
      favorite, scheduled, other]

theorem family_pairs (own gap increment K : Payoff (Fin 4)) (unused : Reward)
    (player : Fin 4) :
    (familyReward own gap increment K unused)
        ⟨{player, scheduled player}, by simp⟩ player = own player + increment player ∧
    (familyReward own gap increment K unused)
        ⟨{favorite player, other player}, by simp⟩ player = own player + K player := by
  fin_cases player <;>
    norm_num +decide [familyReward, favorite, scheduled, other]

theorem family_caps (own gap increment K : Payoff (Fin 4)) (unused : Reward)
    (player : Fin 4) :
    (familyReward own gap increment K unused)
        ⟨{player, favorite player}, by simp⟩ player = own player ∧
    (familyReward own gap increment K unused)
        ⟨{player, other player}, by simp⟩ player = own player ∧
    (familyReward own gap increment K unused)
        ⟨{player, favorite player, other player}, by simp⟩ player = own player := by
  fin_cases player <;>
    norm_num +decide [familyReward, favorite, scheduled, other]

theorem family_premium (own gap increment K : Payoff (Fin 4)) (unused : Reward) :
    TwoPairOdds.premium (familyReward own gap increment K unused) = increment := by
  funext player
  unfold TwoPairOdds.premium
  rw [(family_pairs own gap increment K unused player).1,
    (family_singletons own gap increment K unused player).1]
  ring

theorem family_passive (own gap increment K : Payoff (Fin 4)) (unused : Reward) :
    TwoPairOdds.passive (familyReward own gap increment K unused) = K := by
  funext player
  unfold TwoPairOdds.passive
  rw [(family_pairs own gap increment K unused player).2,
    (family_singletons own gap increment K unused player).1]
  ring

theorem family_matrix (own gap increment K : Payoff (Fin 4)) (unused : Reward)
    (player : Fin 4) :
    quittingProjectiveLCPMatrix (familyReward own gap increment K unused)
        player (favorite player) = gap player ∧
    quittingProjectiveLCPMatrix (familyReward own gap increment K unused)
        player (scheduled player) = -1 ∧
    quittingProjectiveLCPMatrix (familyReward own gap increment K unused)
        player (other player) = -1 := by
  simp only [TwoPairOdds.matrix_entry]
  obtain ⟨hs, hf, ha, ho⟩ := family_singletons own gap increment K unused player
  rw [hs, hf, ha, ho]
  constructor
  · ring
  · constructor <;> ring

theorem family_rawSource (own gap increment K : Payoff (Fin 4)) (unused : Reward)
    (hgap : ∀ player, 0 < gap player) (hincrement : ∀ player, -1 < increment player) :
    CrossedMatching.RawSource (familyReward own gap increment K unused) := by
  constructor
  · intro player
    obtain ⟨hs, hf, _, _⟩ := family_singletons own gap increment K unused player
    rw [hs, hf]
    linarith [hgap player]
  · intro player
    obtain ⟨hs, _, ha, _⟩ := family_singletons own gap increment K unused player
    rw [hs, ha]
    linarith
  · intro player
    obtain ⟨hs, _, _, ho⟩ := family_singletons own gap increment K unused player
    rw [hs, ho]
    linarith
  · intro player
    rw [(family_singletons own gap increment K unused player).2.2.1,
      (family_pairs own gap increment K unused player).1]
    linarith [hincrement player]
  · intro player
    rw [(family_caps own gap increment K unused player).1,
      (family_singletons own gap increment K unused player).1]
  · intro player
    rw [(family_caps own gap increment K unused player).2.1,
      (family_singletons own gap increment K unused player).1]
  · intro player
    rw [(family_caps own gap increment K unused player).2.2,
      (family_singletons own gap increment K unused player).1]

theorem family_matrix_entry (own gap increment K : Payoff (Fin 4)) (unused : Reward)
    (player owner : Fin 4) :
    quittingProjectiveLCPMatrix (familyReward own gap increment K unused) player owner =
      if owner = player then 0 else if owner = favorite player then gap player else -1 := by
  rw [TwoPairOdds.matrix_entry]
  fin_cases player <;> fin_cases owner <;>
    norm_num +decide [familyReward, PairedCycle.singleton, quittingSingletonTerminal,
      favorite, scheduled, other]

def odds : Fin 4 → ℝ := fun _ => 1
def q : Fin 4 → ℝ := TwoPairOdds.hazard odds

theorem odds_positive (player : Fin 4) : 0 < odds player := by norm_num [odds]
theorem q_proper (player : Fin 4) : q player ∈ Set.Ioo (0 : ℝ) 1 :=
  TwoPairOdds.hazard_proper odds_positive player
theorem q_eq (player : Fin 4) : q player = 1 / 2 := by norm_num [q, odds, TwoPairOdds.hazard]

theorem family_equation (own gap increment K : Payoff (Fin 4)) (unused : Reward)
    (point : Fin 4 → ℝ) (player : Fin 4) :
    passiveEquation (quittingProjectiveLCPMatrix (familyReward own gap increment K unused))
        (TwoPairOdds.premium (familyReward own gap increment K unused))
        (TwoPairOdds.passive (familyReward own gap increment K unused)) point player =
      (increment player + 1) * point (scheduled player) *
          (1 + point (favorite player)) * (1 + point (other player)) -
        gap player * point (favorite player) + point (other player) -
        K player * point (favorite player) * point (other player) -
        increment player * point (scheduled player) / (1 + point (scheduled player)) := by
  unfold passiveEquation
  rw [family_premium, family_passive]
  obtain ⟨hf, ha, ho⟩ := family_matrix own gap increment K unused player
  rw [hf, ha, ho]
  ring

theorem balanced_equations (own gap increment K : Payoff (Fin 4)) (unused : Reward)
    (hbalance : ∀ player, gap player = 7 / 2 * increment player + 5 - K player) :
    ∀ player, passiveEquation
      (quittingProjectiveLCPMatrix (familyReward own gap increment K unused))
      (TwoPairOdds.premium (familyReward own gap increment K unused))
      (TwoPairOdds.passive (familyReward own gap increment K unused)) odds player = 0 := by
  intro player
  rw [family_equation, hbalance player]
  norm_num [odds]
  ring

theorem family_activeValue (own gap increment K : Payoff (Fin 4)) (unused : Reward)
    (player : Fin 4) :
    twoPairActiveValue (familyReward own gap increment K unused) fin4Schedule q player =
      own player + increment player / 2 := by
  change twoPairActiveValue _ fin4Schedule (TwoPairOdds.hazard odds) player = _
  rw [TwoPairOdds.activeValue_eq, family_premium,
    (family_singletons own gap increment K unused player).1]
  norm_num [TwoPairOdds.hazard, odds]
  ring

theorem family_postValue (own gap increment K : Payoff (Fin 4)) (unused : Reward)
    (player : Fin 4) :
    twoPairPostValue (familyReward own gap increment K unused) fin4Schedule q player =
      own player + increment player + 1 := by
  change twoPairPostValue _ fin4Schedule (TwoPairOdds.hazard odds) player = _
  rw [TwoPairOdds.postValue_eq _ odds_positive, family_premium,
    (family_singletons own gap increment K unused player).1,
    (family_matrix own gap increment K unused player).2.1]
  norm_num [odds]
  ring

theorem family_passiveQuit (own gap increment K : Payoff (Fin 4)) (unused : Reward)
    (player : Fin 4) :
    quittingRootQuitPayoff (familyReward own gap increment K unused)
      (twoPairPhaseValue (familyReward own gap increment K unused) fin4Schedule q
        (fin4Schedule.phase player))
      (cycle fin4Schedule q (properUnitBounds q q_proper)
        (finRotate 2 (fin4Schedule.phase player))) player = own player := by
  rw [fin4Schedule_passive_root, rootQuit_eq_bellman]
  · obtain ⟨hf, ho, hj⟩ := family_caps own gap increment K unused player
    rw [hf, ho, hj]
    have hsolo := (family_singletons own gap increment K unused player).1
    unfold PairedCycle.singleton at hsolo
    rw [hsolo]
    unfold bellman contribution
    ring
  · fin_cases player <;> decide

def phaseValue (own increment : Payoff (Fin 4)) (initial : Fin 2) : Payoff (Fin 4) :=
  fun player => if initial = fin4Schedule.phase player then
    own player + increment player / 2 else own player + increment player + 1

theorem family_phaseValue (own gap increment K : Payoff (Fin 4)) (unused : Reward)
    (initial : Fin 2) :
    twoPairPhaseValue (familyReward own gap increment K unused) fin4Schedule q initial =
      phaseValue own increment initial := by
  funext player
  unfold phaseValue twoPairPhaseValue
  split_ifs <;> first | exact family_activeValue _ _ _ _ _ _ | exact family_postValue _ _ _ _ _ _

def profile (table : Reward) (initial : Fin 2) : (quittingGame table).BehaviorProfile :=
  quittingCyclicBehaviorProfile table (cycle fin4Schedule q (properUnitBounds q q_proper)) initial

structure ExactFamily (table : Reward) (target : Fin 2 → Payoff (Fin 4)) : Prop where
  terminal : ∀ initial, quittingTerminalPayoff table (profile table initial) = target initial
  nash : ∀ initial, (quittingGame table).IsεAsymptoticNash (quittingTerminalPayoff table) 0
    (profile table initial)
  horizons : ∀ initial accuracy, 0 < accuracy → ∃ threshold : ℕ,
    ∀ horizon, threshold ≤ horizon →
      (quittingGame table).IsεHorizonNash none horizon accuracy (profile table initial) ∧
      ∀ player, |(quittingGame table).finiteAveragePayoff none horizon
        (profile table initial) player - target initial player| ≤ accuracy
  uniform : ∀ initial, (quittingGame table).IsUniformEquilibriumPayoff none (target initial)

/-- The explicit half-hazard profile needs only the balance and increment floor,
not matching signs, positive designated singleton gaps, or a Q certificate. -/
theorem balanced_exactFamily (own gap increment K : Payoff (Fin 4)) (unused : Reward)
    (hincrement : ∀ player, -1 ≤ increment player)
    (hbalance : ∀ player, gap player = 7 / 2 * increment player + 5 - K player) :
    ExactFamily (familyReward own gap increment K unused) (phaseValue own increment) := by
  have hcontinue := TwoPairOdds.passive_continue
    (familyReward own gap increment K unused) odds_positive
    (balanced_equations own gap increment K unused hbalance)
  have hquit (player : Fin 4) := family_passiveQuit own gap increment K unused player
  have hbounds : ∀ player, quittingRootQuitPayoff (familyReward own gap increment K unused)
      (twoPairPhaseValue (familyReward own gap increment K unused) fin4Schedule q
        (fin4Schedule.phase player))
      (cycle fin4Schedule q (properUnitBounds q q_proper)
        (finRotate 2 (fin4Schedule.phase player))) player ≤
        twoPairPostValue (familyReward own gap increment K unused) fin4Schedule q player := by
    intro player
    rw [hquit player, family_postValue]
    linarith [hincrement player]
  have hcertificate (initial : Fin 2) := twoPair_exact_terminal_and_fixedProfile
    (familyReward own gap increment K unused) fin4Schedule q q_proper hcontinue hbounds initial
  constructor
  · intro initial
    exact (hcertificate initial).1.trans (family_phaseValue _ _ _ _ _ _)
  · intro initial
    exact (hcertificate initial).2.1
  · intro initial accuracy haccuracy
    simpa only [profile, family_phaseValue] using
      (hcertificate initial).2.2.1 accuracy haccuracy
  · intro initial
    simpa only [family_phaseValue] using (hcertificate initial).2.2.2

def negativeIncrement : Payoff (Fin 4) := fun _ => -1 / 2
def mixedPassive : Payoff (Fin 4) := ![1, 1 / 2, -1, -1 / 2]
def mixedGap : Payoff (Fin 4) := ![9 / 4, 11 / 4, 17 / 4, 15 / 4]

theorem signed_zero_passive_example (own : Payoff (Fin 4)) (unused : Reward) :
    ExactFamily (familyReward own (fun _ => 13 / 4) negativeIncrement (fun _ => 0) unused)
      (phaseValue own negativeIncrement) := by
  apply balanced_exactFamily
  · intro player; norm_num [negativeIncrement]
  · intro player; norm_num [negativeIncrement]

theorem signed_negative_passive_example (own : Payoff (Fin 4)) (unused : Reward) :
    ExactFamily (familyReward own (fun _ => 17 / 4) negativeIncrement (fun _ => -1) unused)
      (phaseValue own negativeIncrement) := by
  apply balanced_exactFamily
  · intro player; norm_num [negativeIncrement]
  · intro player; norm_num [negativeIncrement]

theorem signed_mixed_passive_example (own : Payoff (Fin 4)) (unused : Reward) :
    ExactFamily (familyReward own mixedGap negativeIncrement mixedPassive unused)
      (phaseValue own negativeIncrement) := by
  apply balanced_exactFamily
  · intro player; norm_num [negativeIncrement]
  · intro player
    fin_cases player <;> norm_num [negativeIncrement, mixedGap, mixedPassive]

theorem negativeIncrement_values (own : Payoff (Fin 4)) (initial : Fin 2) (player : Fin 4) :
    phaseValue own negativeIncrement initial player =
      if initial = fin4Schedule.phase player then own player - 1 / 4 else own player + 1 / 2 := by
  unfold phaseValue negativeIncrement
  split_ifs <;> ring

theorem printed_strict_rawSources (own : Payoff (Fin 4)) (unused : Reward) :
    CrossedMatching.RawSource
        (familyReward own (fun _ => 13 / 4) negativeIncrement (fun _ => 0) unused) ∧
    CrossedMatching.RawSource
        (familyReward own (fun _ => 17 / 4) negativeIncrement (fun _ => -1) unused) ∧
    CrossedMatching.RawSource
        (familyReward own mixedGap negativeIncrement mixedPassive unused) := by
  refine ⟨family_rawSource _ _ _ _ _ ?_ ?_, family_rawSource _ _ _ _ _ ?_ ?_,
    family_rawSource _ _ _ _ _ ?_ ?_⟩
  · intro player; norm_num
  · intro player; norm_num [negativeIncrement]
  · intro player; norm_num
  · intro player; norm_num [negativeIncrement]
  · intro player; fin_cases player <;> norm_num [mixedGap]
  · intro player; norm_num [negativeIncrement]

theorem mixed_pair_passive_test_fails (phase : Fin 2) :
    ¬ ∀ player, player ∉ fin4Schedule.pair phase → 0 ≤ mixedPassive player := by
  fin_cases phase
  · intro h
    have hbad := h 3 (by decide)
    norm_num [mixedPassive] at hbad
  · intro h
    have hbad := h 2 (by decide)
    norm_num [mixedPassive] at hbad

theorem zero_passive_matrix_equation (own : Payoff (Fin 4)) (unused : Reward) :
    let table := familyReward own (fun _ => 13 / 4) negativeIncrement (fun _ => 0) unused
    variableMatrix (quittingProjectiveLCPMatrix table)
        (TwoPairOdds.premium table) (TwoPairOdds.passive table) odds *ᵥ odds =
      (fun _ => 3 / 2) ∧
    positiveNumerator (quittingProjectiveLCPMatrix table)
        (TwoPairOdds.premium table) (TwoPairOdds.passive table) odds = (fun _ => 3 / 2) := by
  dsimp only
  rw [family_premium, family_passive]
  constructor
  · funext player
    unfold Matrix.mulVec dotProduct variableMatrix
    simp only [family_matrix_entry]
    fin_cases player <;> norm_num [negativeIncrement, odds,
      favorite, scheduled, other, Fin.sum_univ_succ]
  · funext player
    unfold positiveNumerator
    obtain ⟨_, ha, _⟩ := family_matrix own (fun _ => 13 / 4) negativeIncrement
      (fun _ => 0) unused player
    rw [ha]
    fin_cases player <;> norm_num [negativeIncrement, odds]


theorem negative_passive_matrix_equation (own : Payoff (Fin 4)) (unused : Reward) :
    let table := familyReward own (fun _ => 17 / 4) negativeIncrement (fun _ => -1) unused
    variableMatrix (quittingProjectiveLCPMatrix table)
        (TwoPairOdds.premium table) (TwoPairOdds.passive table) odds *ᵥ odds =
      (fun _ => 5 / 2) ∧
    positiveNumerator (quittingProjectiveLCPMatrix table)
        (TwoPairOdds.premium table) (TwoPairOdds.passive table) odds = (fun _ => 5 / 2) := by
  dsimp only
  rw [family_premium, family_passive]
  constructor
  · funext player
    unfold Matrix.mulVec dotProduct variableMatrix
    simp only [family_matrix_entry]
    fin_cases player <;> norm_num [negativeIncrement, odds,
      favorite, scheduled, other, Fin.sum_univ_succ]
  · funext player
    unfold positiveNumerator
    obtain ⟨_, ha, _⟩ := family_matrix own (fun _ => 17 / 4) negativeIncrement
      (fun _ => -1) unused player
    rw [ha]
    fin_cases player <;> norm_num [negativeIncrement, odds]


theorem mixed_passive_matrix_equation (own : Payoff (Fin 4)) (unused : Reward) :
    let table := familyReward own mixedGap negativeIncrement mixedPassive unused
    variableMatrix (quittingProjectiveLCPMatrix table)
        (TwoPairOdds.premium table) (TwoPairOdds.passive table) odds *ᵥ odds =
      ![3 / 2, 3 / 2, 5 / 2, 2] ∧
    positiveNumerator (quittingProjectiveLCPMatrix table)
        (TwoPairOdds.premium table) (TwoPairOdds.passive table) odds =
      ![3 / 2, 3 / 2, 5 / 2, 2] := by
  dsimp only
  rw [family_premium, family_passive]
  constructor
  · funext player
    unfold Matrix.mulVec dotProduct variableMatrix
    simp only [family_matrix_entry]
    fin_cases player <;> norm_num [negativeIncrement, mixedGap, mixedPassive, odds,
      favorite, scheduled, other, Fin.sum_univ_succ]
  · funext player
    unfold positiveNumerator
    obtain ⟨_, ha, _⟩ := family_matrix own mixedGap negativeIncrement mixedPassive unused player
    rw [ha]
    fin_cases player <;> norm_num [negativeIncrement, mixedGap, mixedPassive, odds]

def weakReward (own : Payoff (Fin 4)) (H : ℝ) (unused : Reward) : Reward :=
  familyReward own (fun _ => H) (fun _ => -1) (fun _ => 0) unused

theorem mixed_positive_inverse (own : Payoff (Fin 4)) (unused : Reward) :
    HasStrictlyPositiveInverse (quittingProjectiveLCPMatrix
      (familyReward own mixedGap negativeIncrement mixedPassive unused)) := by
  have hraw := (printed_strict_rawSources own unused).2.2
  refine hasStrictlyPositiveInverse_of_matching_positive_vector _ hraw.matchingSigns
    (fun _ => 1) ?_ ?_
  · intro player
    norm_num
  · intro player
    unfold Matrix.mulVec dotProduct
    simp only [family_matrix_entry]
    fin_cases player <;> norm_num [Fin.sum_univ_succ, favorite, mixedGap]

theorem weak_positive_inverse (own : Payoff (Fin 4)) {H : ℝ} (hH : 2 < H)
    (unused : Reward) :
    HasStrictlyPositiveInverse (quittingProjectiveLCPMatrix (weakReward own H unused)) := by
  refine hasStrictlyPositiveInverse_of_matching_positive_vector _ ?_ (fun _ => 1) ?_ ?_
  · constructor
    · intro player
      simp only [weakReward, family_matrix_entry, ite_true]
    · intro player
      simp only [weakReward, family_matrix_entry]
      fin_cases player <;> norm_num [favorite] <;> linarith
    · intro player
      simp only [weakReward, family_matrix_entry]
      fin_cases player <;> norm_num [favorite, scheduled]
    · intro player
      simp only [weakReward, family_matrix_entry]
      fin_cases player <;> norm_num [favorite, other]
  · intro player
    norm_num
  · intro player
    unfold Matrix.mulVec dotProduct
    simp only [weakReward, family_matrix_entry]
    fin_cases player <;> norm_num [Fin.sum_univ_succ, favorite] <;> linarith

/-- Failure of the proper odds producer at the weak joining boundary is not
failure of the game's uniform-equilibrium existence. -/
theorem weak_no_positive_odds (own : Payoff (Fin 4)) {H : ℝ} (hH : 2 < H)
    (unused : Reward) (point : Fin 4 → ℝ) (hpoint : ∀ player, 0 < point player) :
    ¬ ∀ player, passiveEquation (quittingProjectiveLCPMatrix (weakReward own H unused))
      (TwoPairOdds.premium (weakReward own H unused))
      (TwoPairOdds.passive (weakReward own H unused)) point player = 0 := by
  intro heq
  have hrow (player : Fin 4) := heq player
  simp only [weakReward, family_equation] at hrow
  have hratio (player : Fin 4) : point player / (1 + point player) < point player := by
    apply (div_lt_iff₀ (show 0 < 1 + point player by linarith [hpoint player])).mpr
    nlinarith [sq_pos_of_pos (hpoint player)]
  have h0 := hrow 0
  have h1 := hrow 1
  have h2 := hrow 2
  have h3 := hrow 3
  norm_num [favorite, scheduled, other] at h0 h1 h2 h3
  simp only [neg_div, sub_neg_eq_add] at h0 h1 h2 h3
  have hsum : 0 < point 0 + point 1 + point 2 + point 3 := by
    linarith [hpoint 0, hpoint 1, hpoint 2, hpoint 3]
  nlinarith [hratio 0, hratio 1, hratio 2, hratio 3, mul_pos (sub_pos.mpr hH) hsum]

theorem weak_scheduledPairCapSource (own : Payoff (Fin 4)) (H : ℝ) (unused : Reward) :
    CrossedMatching.ScheduledPairCapSource (weakReward own H unused) := by
  unfold weakReward
  constructor
  · intro player
    rw [(family_singletons own (fun _ => H) (fun _ => -1) (fun _ => 0) unused player).2.2.1,
      (family_pairs own (fun _ => H) (fun _ => -1) (fun _ => 0) unused player).1]
    linarith
  · intro player
    rw [(family_caps own (fun _ => H) (fun _ => -1) (fun _ => 0) unused player).1,
      (family_singletons own (fun _ => H) (fun _ => -1) (fun _ => 0) unused player).1]
  · intro player
    rw [(family_caps own (fun _ => H) (fun _ => -1) (fun _ => 0) unused player).2.1,
      (family_singletons own (fun _ => H) (fun _ => -1) (fun _ => 0) unused player).1]
  · intro player
    rw [(family_caps own (fun _ => H) (fun _ => -1) (fun _ => 0) unused player).2.2,
      (family_singletons own (fun _ => H) (fun _ => -1) (fun _ => 0) unused player).1]

theorem weak_pure_pair_uniformPayoff (own : Payoff (Fin 4)) (H : ℝ) (unused : Reward)
    (phase : Fin 2) :
    (quittingGame (weakReward own H unused)).IsUniformEquilibriumPayoff none
      (quittingSetReward (weakReward own H unused) (fin4Schedule.pair phase)) := by
  have hpassive : ∀ player, player ∉ fin4Schedule.pair phase →
      0 ≤ TwoPairOdds.passive (weakReward own H unused) player := by
    intro player _
    unfold weakReward
    rw [family_passive]
  exact (CrossedMatching.scheduledPair_exact_profile
    (weak_scheduledPairCapSource own H unused) phase hpassive).2.2.2.2

theorem weak_rawSource (own : Payoff (Fin 4)) {H : ℝ} (hH : 0 ≤ H)
    (unused : Reward) : CrossedMatching.WeakRawSource (weakReward own H unused) := by
  have hcaps := weak_scheduledPairCapSource own H unused
  refine ⟨?_, ?_, ?_, hcaps.participant_ge, hcaps.cap_favorite, hcaps.cap_other,
    hcaps.cap_joint⟩
  · intro player
    unfold weakReward
    rw [(family_singletons own (fun _ => H) (fun _ => -1) (fun _ => 0) unused player).1,
      (family_singletons own (fun _ => H) (fun _ => -1) (fun _ => 0) unused player).2.1]
    linarith
  · intro player
    unfold weakReward
    rw [(family_singletons own (fun _ => H) (fun _ => -1) (fun _ => 0) unused player).1,
      (family_singletons own (fun _ => H) (fun _ => -1) (fun _ => 0) unused player).2.2.1]
    linarith
  · intro player
    unfold weakReward
    rw [(family_singletons own (fun _ => H) (fun _ => -1) (fun _ => 0) unused player).1,
      (family_singletons own (fun _ => H) (fun _ => -1) (fun _ => 0) unused player).2.2.2]
    linarith

theorem weak_pure_pair_exact_profile (own : Payoff (Fin 4)) (H : ℝ) (unused : Reward)
    (phase : Fin 2) :
    let pureProfile := quittingOneDateThenNeverProfile (weakReward own H unused)
      (quittingPureSetRoot (fin4Schedule.pair phase))
    quittingTerminalPayoff (weakReward own H unused) pureProfile =
        quittingSetReward (weakReward own H unused) (fin4Schedule.pair phase) ∧
    (quittingGame (weakReward own H unused)).IsεAsymptoticNash
      (quittingTerminalPayoff (weakReward own H unused)) 0 pureProfile ∧
    (∀ horizon, (quittingGame (weakReward own H unused)).IsεHorizonNash none horizon 0
      pureProfile) ∧
    (quittingGame (weakReward own H unused)).IsUniformEquilibriumPayoff none
      (quittingSetReward (weakReward own H unused) (fin4Schedule.pair phase)) := by
  have hpassive : ∀ player, player ∉ fin4Schedule.pair phase →
      0 ≤ TwoPairOdds.passive (weakReward own H unused) player := by
    intro player _
    unfold weakReward
    rw [family_passive]
  have hcert := CrossedMatching.scheduledPair_exact_profile
    (weak_scheduledPairCapSource own H unused) phase hpassive
  exact ⟨hcert.1, hcert.2.1, hcert.2.2.1, hcert.2.2.2.2⟩

/-- The altered coordinate is used only by the outsider's inserted Quit, not
by the original policy. -/
def capViolationReward (unused : Reward) : Reward := fun terminal player =>
  if terminal.val = {0, 1, 3} ∧ player = 0 then 4 else
    familyReward (fun _ => 1) (fun _ => 17 / 4) negativeIncrement (fun _ => -1) unused
      terminal player

theorem capViolation_singleton (unused : Reward) (player : Fin 4) :
    singleton (capViolationReward unused) player = 1 := by
  fin_cases player <;> norm_num +decide [capViolationReward, familyReward,
    PairedCycle.singleton, quittingSingletonTerminal, favorite, scheduled, other]

theorem capViolation_premium (unused : Reward) :
    TwoPairOdds.premium (capViolationReward unused) = negativeIncrement := by
  funext player
  fin_cases player <;> norm_num +decide [TwoPairOdds.premium, capViolationReward,
    familyReward, PairedCycle.singleton, quittingSingletonTerminal,
    favorite, scheduled, other, negativeIncrement]

theorem capViolation_passive (unused : Reward) :
    TwoPairOdds.passive (capViolationReward unused) = (fun _ => -1) := by
  funext player
  fin_cases player <;> norm_num +decide [TwoPairOdds.passive, capViolationReward,
    familyReward, PairedCycle.singleton, quittingSingletonTerminal,
    favorite, scheduled, other]

theorem capViolation_matrix (unused : Reward) :
    quittingProjectiveLCPMatrix (capViolationReward unused) =
      quittingProjectiveLCPMatrix
        (familyReward (fun _ => 1) (fun _ => 17 / 4) negativeIncrement (fun _ => -1) unused) := by
  ext player owner
  rw [TwoPairOdds.matrix_entry, TwoPairOdds.matrix_entry]
  fin_cases player <;> fin_cases owner <;>
    norm_num +decide [capViolationReward, PairedCycle.singleton, quittingSingletonTerminal]

theorem capViolation_equations (unused : Reward) :
    ∀ player, passiveEquation (quittingProjectiveLCPMatrix (capViolationReward unused))
      (TwoPairOdds.premium (capViolationReward unused))
      (TwoPairOdds.passive (capViolationReward unused)) odds player = 0 := by
  rw [capViolation_matrix, capViolation_premium, capViolation_passive]
  have heq := balanced_equations (fun _ => 1) (fun _ => 17 / 4) negativeIncrement
    (fun _ => -1) unused (by intro player; norm_num [negativeIncrement])
  simpa only [family_premium, family_passive] using heq

theorem capViolation_postValue (unused : Reward) (player : Fin 4) :
    twoPairPostValue (capViolationReward unused) fin4Schedule q player = 3 / 2 := by
  change twoPairPostValue _ fin4Schedule (TwoPairOdds.hazard odds) player = _
  rw [TwoPairOdds.postValue_eq _ odds_positive, capViolation_singleton,
    capViolation_premium, capViolation_matrix,
    (family_matrix (fun _ => 1) (fun _ => 17 / 4) negativeIncrement
      (fun _ => -1) unused player).2.1]
  norm_num [negativeIncrement, odds]

theorem capViolation_terminal (unused : Reward) :
    quittingTerminalPayoff (capViolationReward unused) (profile (capViolationReward unused) 1)
      0 = 3 / 2 := by
  unfold profile
  rw [twoPair_terminalPayoff_eq _ fin4Schedule q q_proper
    (TwoPairOdds.passive_continue _ odds_positive (capViolation_equations unused))]
  have hphase : (1 : Fin 2) = finRotate 2 (fin4Schedule.phase 0) := by
    rw [fin4Schedule_phase_zero]
    rfl
  rw [hphase, twoPairPhaseValue_post, capViolation_postValue]

theorem capViolation_passiveQuit (unused : Reward) :
    quittingRootQuitPayoff (capViolationReward unused)
      (twoPairPhaseValue (capViolationReward unused) fin4Schedule q (fin4Schedule.phase 0))
      (cycle fin4Schedule q (properUnitBounds q q_proper)
        (finRotate 2 (fin4Schedule.phase 0))) 0 = 7 / 4 := by
  rw [fin4Schedule_passive_root, rootQuit_eq_bellman]
  · norm_num +decide [capViolationReward, familyReward, negativeIncrement,
      PairedCycle.singleton, quittingSingletonTerminal, favorite, scheduled, other,
      bellman, contribution, quittingHazardCoin_true_toReal, q_eq]
  · decide

theorem capViolation_quitNow_gain (unused : Reward) :
    quittingTerminalPayoff (capViolationReward unused)
        (Function.update (profile (capViolationReward unused) 1) 0
          (quittingPureTimeBehaviorStrategy (capViolationReward unused) 0 (some 0))) 0 -
      quittingTerminalPayoff (capViolationReward unused) (profile (capViolationReward unused) 1)
        0 = 1 / 4 := by
  rw [capViolation_terminal, quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  unfold profile
  rw [quittingProfileLiveRoot_cyclicBehaviorProfile,
    quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents,
    ← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue (capViolationReward unused) _ 0
      (twoPairPhaseValue (capViolationReward unused) fin4Schedule q (fin4Schedule.phase 0)),
    quittingCyclicRootSequence_zero]
  have hphase : (1 : Fin 2) = finRotate 2 (fin4Schedule.phase 0) := by
    rw [fin4Schedule_phase_zero]
    rfl
  rw [hphase, capViolation_passiveQuit]
  norm_num

theorem capViolation_not_terminalNash (unused : Reward) :
    ¬ (quittingGame (capViolationReward unused)).IsεAsymptoticNash
      (quittingTerminalPayoff (capViolationReward unused)) 0
      (profile (capViolationReward unused) 1) := by
  intro hnash
  have hcap := hnash 0
    (quittingPureTimeBehaviorStrategy (capViolationReward unused) 0 (some 0))
  have hgain := capViolation_quitNow_gain unused
  simp only [add_zero] at hcap
  linarith

theorem capViolation_not_rawSource (unused : Reward) :
    ¬ CrossedMatching.RawSource (capViolationReward unused) := by
  intro hraw
  have hcap := hraw.cap_joint 0
  rw [capViolation_singleton] at hcap
  norm_num +decide [capViolationReward, favorite, other] at hcap

end GameTheory.PairedCycle.CrossedMatchingBoundaryExamples
