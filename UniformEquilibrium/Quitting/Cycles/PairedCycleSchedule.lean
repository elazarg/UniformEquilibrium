import MathUE.PairedAffineClearedField
import UniformEquilibrium.Quitting.Root.PairedProductRoot
import UniformEquilibrium.Quitting.Cycles.PeriodicCompiler

/-! # Ordered pair partitions and their literal independent cyclic roots -/

noncomputable section

namespace GameTheory.PairedCycle

variable {ι : Type} {period : ℕ}

/-- An ordered partition of the entire player type into pairs. -/
structure Schedule (ι : Type) (period : ℕ) where
  label : (Fin period × Bool) ≃ ι

def Schedule.first (schedule : Schedule ι period) (phase : Fin period) : ι :=
  schedule.label (phase, false)

def Schedule.second (schedule : Schedule ι period) (phase : Fin period) : ι :=
  schedule.label (phase, true)

def Schedule.phase (schedule : Schedule ι period) (player : ι) : Fin period :=
  (schedule.label.symm player).1

def Schedule.partner (schedule : Schedule ι period) (player : ι) : ι :=
  schedule.label ((schedule.label.symm player).1, !(schedule.label.symm player).2)

theorem Schedule.first_ne_second (schedule : Schedule ι period) (phase : Fin period) :
    schedule.first phase ≠ schedule.second phase := by
  intro h
  have h' := schedule.label.injective h
  have := congrArg Prod.snd h'
  cases this

@[simp] theorem Schedule.phase_first (schedule : Schedule ι period) (phase : Fin period) :
    schedule.phase (schedule.first phase) = phase := by
  simp [Schedule.phase, Schedule.first]

@[simp] theorem Schedule.phase_second (schedule : Schedule ι period) (phase : Fin period) :
    schedule.phase (schedule.second phase) = phase := by
  simp [Schedule.phase, Schedule.second]

@[simp] theorem Schedule.partner_first (schedule : Schedule ι period) (phase : Fin period) :
    schedule.partner (schedule.first phase) = schedule.second phase := by
  simp [Schedule.partner, Schedule.first, Schedule.second]

@[simp] theorem Schedule.partner_second (schedule : Schedule ι period) (phase : Fin period) :
    schedule.partner (schedule.second phase) = schedule.first phase := by
  simp [Schedule.partner, Schedule.first, Schedule.second]

@[simp] theorem Schedule.partner_partner (schedule : Schedule ι period) (player : ι) :
    schedule.partner (schedule.partner player) = player := by
  simp [Schedule.partner]

@[simp] theorem Schedule.phase_partner (schedule : Schedule ι period) (player : ι) :
    schedule.phase (schedule.partner player) = schedule.phase player := by
  simp [Schedule.phase, Schedule.partner]

theorem Schedule.player_eq_first_or_second (schedule : Schedule ι period) (player : ι) :
    player = schedule.first (schedule.phase player) ∨
      player = schedule.second (schedule.phase player) := by
  obtain ⟨⟨phase, side⟩, rfl⟩ := schedule.label.surjective player
  cases side <;> simp [Schedule.phase, Schedule.first, Schedule.second]

theorem Schedule.partner_ne (schedule : Schedule ι period) (player : ι) :
    schedule.partner player ≠ player := by
  obtain ⟨⟨phase, side⟩, rfl⟩ := schedule.label.surjective player
  cases side
  · change schedule.partner (schedule.first phase) ≠ schedule.first phase
    simpa only [Schedule.partner_first] using (schedule.first_ne_second phase).symm
  · change schedule.partner (schedule.second phase) ≠ schedule.second phase
    simpa only [Schedule.partner_second] using schedule.first_ne_second phase

theorem Schedule.player_ne_first_of_phase_ne (schedule : Schedule ι period)
    {player : ι} {phase : Fin period} (hne : phase ≠ schedule.phase player) :
    player ≠ schedule.first phase := by
  intro h
  exact hne (by simpa using (congrArg schedule.phase h).symm)

theorem Schedule.player_ne_second_of_phase_ne (schedule : Schedule ι period)
    {player : ι} {phase : Fin period} (hne : phase ≠ schedule.phase player) :
    player ≠ schedule.second phase := by
  intro h
  exact hne (by simpa using (congrArg schedule.phase h).symm)

theorem orbit_eq_finCycle (phase offset : Fin period) :
    quittingCyclicOrbit phase offset.val = finCycle phase offset := by
  apply Fin.ext
  simp [quittingCyclicOrbit, finCycle_apply, Fin.add_def, Nat.add_comm]

theorem orbit_next (phase : Fin period) (steps : ℕ) :
    quittingCyclicOrbit (finRotate period phase) steps =
      quittingCyclicOrbit phase (steps + 1) := by
  have h := quittingCyclicOrbit_add phase 1 steps
  simpa [quittingCyclicOrbit_succ, Nat.add_comm] using h.symm

theorem orbit_injective_below_period (phase : Fin period) {first second : ℕ}
    (hfirst : first < period) (hsecond : second < period)
    (heq : quittingCyclicOrbit phase first = quittingCyclicOrbit phase second) :
    first = second := by
  have h := (finCycle phase).injective
    (show finCycle phase ⟨first, hfirst⟩ = finCycle phase ⟨second, hsecond⟩ by
      simpa only [← orbit_eq_finCycle] using heq)
  exact congrArg Fin.val h

theorem orbit_ne_start (phase : Fin period) {steps : ℕ}
    (hpositive : 0 < steps) (hsteps : steps < period) :
    quittingCyclicOrbit phase steps ≠ phase := by
  intro h
  have hzero := orbit_injective_below_period phase hsteps phase.pos
    (by simpa using h)
  omega

variable [DecidableEq ι]

def Schedule.pair (schedule : Schedule ι period) (phase : Fin period) : Finset ι :=
  {schedule.first phase, schedule.second phase}

theorem Schedule.pair_nonempty (schedule : Schedule ι period) (phase : Fin period) :
    (schedule.pair phase).Nonempty := by
  simp [Schedule.pair]

theorem Schedule.pair_phase_eq (schedule : Schedule ι period) (player : ι) :
    schedule.pair (schedule.phase player) = {player, schedule.partner player} := by
  obtain ⟨⟨phase, side⟩, rfl⟩ := schedule.label.surjective player
  cases side <;>
    simp [Schedule.pair, Schedule.phase, Schedule.partner, Schedule.first, Schedule.second,
      Finset.pair_comm]

def singleton (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι) : ℝ :=
  reward (quittingSingletonTerminal player) player

def partnerReward (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (player : ι) : ℝ :=
  reward (quittingSingletonTerminal (schedule.partner player)) player

def jointReward (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (player : ι) : ℝ :=
  reward ⟨schedule.pair (schedule.phase player), schedule.pair_nonempty _⟩ player

/-- Own, passive, and joining reward restrictions for an ordered pair cycle. -/
structure RawRegion (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) : Prop where
  own : ∀ player, Math.PairedAffine.OwnBounds (singleton reward player)
    (partnerReward reward schedule player) (jointReward reward schedule player)
  passive : ∀ player phase, phase ≠ schedule.phase player →
    Math.PairedAffine.PassiveBounds
      (reward (quittingSingletonTerminal (schedule.first phase)) player)
      (reward (quittingSingletonTerminal (schedule.second phase)) player)
      (reward ⟨schedule.pair phase, schedule.pair_nonempty phase⟩ player)
  joining : ∀ player phase, phase ≠ schedule.phase player →
    ∀ coalition : Finset ι, coalition.Nonempty → coalition ⊆ schedule.pair phase →
      reward ⟨insert player coalition, Finset.insert_nonempty player coalition⟩ player ≤
        singleton reward player + 1 / 50

def indexedRow (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (player : ι) (phase : Fin period) :
    Math.PairedAffine.IndexedRow ι where
  first := schedule.first phase
  second := schedule.second phase
  left := reward (quittingSingletonTerminal (schedule.first phase)) player
  right := reward (quittingSingletonTerminal (schedule.second phase)) player
  tie := reward ⟨schedule.pair phase, schedule.pair_nonempty phase⟩ player

/-- Quiet phases after the player's active phase and before its next active phase. -/
def quietRows (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (player : ι) : List (Math.PairedAffine.IndexedRow ι) :=
  List.ofFn fun offset : Fin (period - 1) =>
    indexedRow reward schedule player (quittingCyclicOrbit (schedule.phase player) (offset.val + 1))

theorem quietRows_nonempty (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hperiod : 2 ≤ period) (player : ι) :
    quietRows reward schedule player ≠ [] := by
  intro h
  have hlength := congrArg List.length h
  simp [quietRows] at hlength
  omega

theorem quietRows_passive (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι period) (hregion : RawRegion reward schedule) (player : ι)
    (row : Math.PairedAffine.IndexedRow ι) (hrow : row ∈ quietRows reward schedule player) :
    Math.PairedAffine.PassiveBounds row.left row.right row.tie := by
  obtain ⟨offset, rfl⟩ := List.mem_ofFn.mp hrow
  apply hregion.passive
  exact orbit_ne_start (schedule.phase player) (by omega) (by omega)

def cycle (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1) (phase : Fin period) : ι → PMF Bool :=
  root (schedule.first phase) (schedule.second phase)
    (quittingHazardCoin (q (schedule.first phase)) (hq _).1 (hq _).2)
    (quittingHazardCoin (q (schedule.second phase)) (hq _).1 (hq _).2)

@[simp] theorem cycle_active_rate (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1) (player : ι) :
    (cycle schedule q hq (schedule.phase player) player true).toReal = q player := by
  obtain ⟨⟨phase, side⟩, rfl⟩ := schedule.label.surjective player
  cases side
  · change (cycle schedule q hq (schedule.phase (schedule.first phase))
      (schedule.first phase) true).toReal = q (schedule.first phase)
    simp [cycle, root_first (schedule.first_ne_second phase)]
  · change (cycle schedule q hq (schedule.phase (schedule.second phase))
      (schedule.second phase) true).toReal = q (schedule.second phase)
    simp [cycle]

theorem cycle_outside (schedule : Schedule ι period) (q : ι → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1) {player : ι} {phase : Fin period}
    (hne : phase ≠ schedule.phase player) :
    cycle schedule q hq phase player = PMF.pure false := by
  exact root_outside (schedule.player_ne_first_of_phase_ne hne)
    (schedule.player_ne_second_of_phase_ne hne) _ _

variable [Fintype ι]

omit [DecidableEq ι] in
theorem Schedule.card_players (schedule : Schedule ι period) : Fintype.card ι = 2 * period := by
  simpa [Nat.mul_comm] using (Fintype.card_congr schedule.label).symm

theorem exists_hazards_of_rawRegion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (schedule : Schedule ι period)
    (hperiod : 2 ≤ period) (hregion : RawRegion reward schedule) :
    ∃ q : ι → ℝ, (∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2)) ∧
      ∀ player, Math.PairedAffine.playerGap schedule.partner (singleton reward)
        (partnerReward reward schedule) (jointReward reward schedule)
        (quietRows reward schedule) q player = 0 :=
  Math.PairedAffine.exists_interior_hazards_all_playerGap_zero schedule.partner
    schedule.partner_partner (singleton reward) (partnerReward reward schedule)
    (jointReward reward schedule) (quietRows reward schedule) hregion.own
    (quietRows_passive reward schedule hregion) (quietRows_nonempty reward schedule hperiod)

end GameTheory.PairedCycle
