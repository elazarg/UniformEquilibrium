/-
The mixed-background purification iteration.

A deadline-bounded behavior profile need not be canonical: only some of its
coordinates have to be literal pure quit dates, and the rest may randomize.
The finite-clock purification kernel overwrites one coordinate at a time by a
pure plan bounded by one step past the current deadline, so each overwrite
costs one date of deadline slack and buys one syntactically pure coordinate.

Run that overwrite along the coordinates that are not yet pure.  Every
intermediate profile is again deadline bounded, and its terminal-semantic pair
is a carrier point, so a source profile sitting at a global minimum of total
debt forces every intermediate total debt to be at least the minimum.  Each
step therefore either ties the minimum - and the run continues with one more
purified coordinate - or already leaves the minimum fibre, and the run stops
there.

Both exits are recorded.  The tying exit is a canonical pure-time date vector
whose pair is a global minimum at exactly the source's debt value.  The
leaving exit is a deadline-bounded profile strictly above the source's debt
carrying a literal pure-time or Never response whose gain is at least that
profile's average debt.  Composing the tying exit with the anchored-erasure
and deadline-descent capstone collapses both exits to one off-minimum paid
port.

Nothing here selects an equilibrium, claims the exit profile is a minimum, a
Nash point, or an equilibrium payoff, or asserts that purification preserves
the coordinates it does not overwrite: each step overwrites exactly one
coordinate and every other coordinate is carried unchanged.
-/
import FableDeadlineDescentCapstone

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## F1: an average-debt paid response at a deadline-bounded profile -/

/-- Some coordinate of a strictly positive total debt carries at least the
average debt.  Stated for an arbitrary behavior profile. -/
private theorem fable_exists_bounded_averageDebt_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile)) :
    ∃ responder : ι,
      quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) /
          (Fintype.card ι : ℝ) ≤
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) responder := by
  classical
  have hsumEq : ∑ who, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) := rfl
  have hne : (Finset.univ : Finset ι).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset ι) with
      hempty | hne
    · rw [← hsumEq, hempty, Finset.sum_empty] at hpositive
      exact absurd hpositive (lt_irrefl 0)
    · exact hne
  have hcardPos : 0 < Fintype.card ι := by
    rw [← Finset.card_univ]
    exact Finset.card_pos.mpr hne
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hcardPos
  have hfix : (Fintype.card ι : ℝ) *
      (quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) /
        (Fintype.card ι : ℝ)) =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) := by
    field_simp
  have hsumLe : ∑ _who : ι, quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) /
          (Fintype.card ι : ℝ) ≤
      ∑ who, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who := by
    rw [hsumEq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hfix]
  obtain ⟨responder, -, hresponder⟩ := Finset.exists_le_of_sum_le hne hsumLe
  exact ⟨responder, hresponder⟩

/-- **F1.**  At any deadline-bounded profile with strictly positive total
debt, some player has a literal pure-time or Never response whose gain is at
least the average debt. -/
theorem fable_positiveDebt_deadlineBounded_averagePaidResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {deadline : ℕ}
    (hbound : FableDeadlineBounded reward profile deadline)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile)) :
    ∃ (responder : ι) (choice : Option ℕ),
      quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) /
          (Fintype.card ι : ℝ) ≤
        quittingPureTimeDeviationPayoff reward profile responder choice -
          quittingTerminalPayoff reward profile responder := by
  obtain ⟨responder, hresponder⟩ :=
    fable_exists_bounded_averageDebt_le reward profile hpositive
  obtain ⟨choice, hvalue, -⟩ := fable_exists_deadlineBounded_pureTime_eq_cap
    reward profile responder hbound
  refine ⟨responder, choice, ?_⟩
  have hdebt := fable_semanticDebt_profile_eq reward profile responder
  rw [hvalue]
  linarith

/-! ## F2: one purification step -/

/-- Overwriting one coordinate by a pure plan bounded one step past the
deadline leaves a profile deadline bounded one step later. -/
theorem fableDeadlineBounded_update_pureTime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {deadline : ℕ}
    (hbound : FableDeadlineBounded reward profile deadline) (who : ι)
    {choice : Option ℕ}
    (hchoice : choice = none ∨
      ∃ time, time ≤ deadline + 1 ∧ choice = some time) :
    FableDeadlineBounded reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who choice))
      (deadline + 1) := by
  intro player time htime
  simp only [quittingProfileLiveRoot]
  by_cases hcase : player = who
  · subst player
    rw [Function.update_self]
    show quittingPureTimeHazard choice time = PMF.pure false
    rcases hchoice with rfl | ⟨date, hdate, rfl⟩
    · rfl
    · exact quittingPureTimeHazard_some_of_ne (by omega)
  · rw [Function.update_of_ne hcase]
    exact hbound player time (by omega)

/-- **F2.**  One purification step at a deadline-bounded global minimum.  The
overwritten coordinate is literally a pure-time strategy with a date no later
than one step past the deadline, the target is deadline bounded one step
later, and the target's total debt is at least the source's. -/
theorem fable_purification_step
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {deadline : ℕ}
    (hbound : FableDeadlineBounded reward profile deadline) (who : ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ choice : Option ℕ,
      (choice = none ∨ ∃ time, time ≤ deadline + 1 ∧ choice = some time) ∧
        FableDeadlineBounded reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who choice))
          (deadline + 1) ∧
        Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who choice) who =
          quittingPureTimeBehaviorStrategy reward who choice ∧
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) ≤
          quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who choice))) := by
  obtain ⟨choice, hshape, -, -⟩ :=
    fable_deadlineBounded_purification reward profile who hbound
  exact ⟨choice, hshape,
    fableDeadlineBounded_update_pureTime reward profile hbound who hshape,
    Function.update_self _ _ _,
    hminimum _ (quittingTerminalSemanticPair_mem_carrier reward _)⟩

/-! ## F3: the iteration -/

/-- A profile all of whose coordinates are literal pure-time strategies is
canonical, so at a global minimum it exhibits a canonical global minimum at
its own debt value. -/
private theorem fable_purify_left_of_all
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hpure : ∀ player : ι, ∃ choice : Option ℕ,
      profile player = quittingPureTimeBehaviorStrategy reward player choice)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ tau : ι → Option ℕ,
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
          (fableCanonicalProfile reward tau)) =
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ∧
      ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
            (fableCanonicalProfile reward tau)) ≤
          quittingTerminalSemanticDebtSum candidate := by
  classical
  have heq : fableCanonicalProfile reward
      (fun player => Classical.choose (hpure player)) = profile := by
    funext player
    show quittingPureTimeBehaviorStrategy reward player
      (Classical.choose (hpure player)) = profile player
    exact (Classical.choose_spec (hpure player)).symm
  refine ⟨fun player => Classical.choose (hpure player), ?_, ?_⟩
  · rw [heq]
  · simp only [heq]
    exact hminimum

/-- Every player is purified once the unpurified complement is empty. -/
private theorem fable_mem_of_sdiff_card_zero
    {purified : Finset ι}
    (hcard : ((Finset.univ : Finset ι) \ purified).card = 0) :
    ∀ player : ι, player ∈ purified := by
  intro player
  by_contra hcontra
  have hmem : player ∈ (Finset.univ : Finset ι) \ purified :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ player, hcontra⟩
  rw [Finset.card_eq_zero.mp hcard] at hmem
  exact absurd hmem (by simp)

/-- The purification iteration, driven by a fuel bound on the number of
coordinates that are not yet syntactically pure-time. -/
private theorem fable_purify_aux
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∀ (fuel : ℕ) (purified : Finset ι)
      (profile : (quittingGame reward).BehaviorProfile) (deadline : ℕ),
      ((Finset.univ : Finset ι) \ purified).card ≤ fuel →
      (∀ player ∈ purified, ∃ choice : Option ℕ,
        profile player =
          quittingPureTimeBehaviorStrategy reward player choice) →
      FableDeadlineBounded reward profile deadline →
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) ≤
          quittingTerminalSemanticDebtSum candidate) →
      0 < quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) →
      (∃ tau : ι → Option ℕ,
          quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
              (fableCanonicalProfile reward tau)) =
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward profile) ∧
          ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
            quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward
                  (fableCanonicalProfile reward tau)) ≤
              quittingTerminalSemanticDebtSum candidate) ∨
        (∃ (sigma : (quittingGame reward).BehaviorProfile) (bound : ℕ),
          FableDeadlineBounded reward sigma bound ∧
          quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward profile) <
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward sigma) ∧
          ∃ (responder : ι) (choice : Option ℕ),
            quittingTerminalSemanticDebtSum
                  (quittingTerminalSemanticPair reward sigma) /
                (Fintype.card ι : ℝ) ≤
              quittingPureTimeDeviationPayoff reward sigma responder choice -
                quittingTerminalPayoff reward sigma responder) := by
  classical
  intro fuel
  induction fuel with
  | zero =>
      intro purified profile _ hcard hpure _ hminimum _
      exact Or.inl (fable_purify_left_of_all reward profile
        (fun player => hpure player
          (fable_mem_of_sdiff_card_zero (Nat.le_zero.mp hcard) player))
        hminimum)
  | succ fuel ih =>
      intro purified profile deadline hcard hpure hbound hminimum hpositive
      by_cases hstep : ((Finset.univ : Finset ι) \ purified).Nonempty
      · obtain ⟨who, hwho⟩ := hstep
        obtain ⟨choice, hshape, hboundTarget, hcoord, hle⟩ :=
          fable_purification_step reward profile hbound who hminimum
        set target := Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who choice) with htarget
        rcases lt_or_eq_of_le hle with hstrict | hequal
        · exact Or.inr ⟨target, deadline + 1, hboundTarget, hstrict,
            fable_positiveDebt_deadlineBounded_averagePaidResponse reward
              target hboundTarget (by linarith)⟩
        · have hcard' :
              ((Finset.univ : Finset ι) \ insert who purified).card ≤ fuel := by
            rw [Finset.sdiff_insert, Finset.card_erase_of_mem hwho]
            omega
          have hpure' : ∀ player ∈ insert who purified, ∃ c : Option ℕ,
              target player =
                quittingPureTimeBehaviorStrategy reward player c := by
            intro player hplayer
            by_cases hne : player = who
            · subst player
              exact ⟨choice, hcoord⟩
            · obtain ⟨c, hc⟩ := hpure player
                ((Finset.mem_insert.mp hplayer).resolve_left hne)
              refine ⟨c, ?_⟩
              rw [htarget, Function.update_of_ne hne]
              exact hc
          have hminimum' : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
              quittingTerminalSemanticDebtSum
                  (quittingTerminalSemanticPair reward target) ≤
                quittingTerminalSemanticDebtSum candidate := by
            intro candidate hcandidate
            rw [← hequal]
            exact hminimum candidate hcandidate
          have hpositive' : 0 < quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward target) := by
            rw [← hequal]
            exact hpositive
          rcases ih (insert who purified) target (deadline + 1) hcard' hpure'
            hboundTarget hminimum' hpositive' with hleft | hright
          · obtain ⟨tau, hvalue, hmin⟩ := hleft
            exact Or.inl ⟨tau, hvalue.trans hequal.symm, hmin⟩
          · obtain ⟨sigma, bound, hsigmaBound, hlt, hport⟩ := hright
            exact Or.inr ⟨sigma, bound, hsigmaBound, hequal.trans_lt hlt, hport⟩
      · refine Or.inl (fable_purify_left_of_all reward profile
          (fun player => hpure player ?_) hminimum)
        exact fable_mem_of_sdiff_card_zero
          (Finset.card_eq_zero.mpr
            (Finset.not_nonempty_iff_eq_empty.mp hstep)) player

/-- **F3.**  A deadline-bounded profile whose terminal-semantic pair is a
strictly positive global minimum of total debt either purifies to a canonical
pure-time date vector carrying a global minimum at the very same debt value,
or exposes a deadline-bounded profile strictly above that minimum carrying a
literal pure-time or Never response whose gain is at least its own average
debt. -/
theorem fable_deadlineBounded_minimum_purify_or_paidPort
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {deadline : ℕ}
    (hbound : FableDeadlineBounded reward profile deadline)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile)) :
    (∃ tau : ι → Option ℕ,
        quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
            (fableCanonicalProfile reward tau)) =
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) ∧
        ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
          quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (fableCanonicalProfile reward tau)) ≤
            quittingTerminalSemanticDebtSum candidate) ∨
      (∃ (sigma : (quittingGame reward).BehaviorProfile) (bound : ℕ),
        FableDeadlineBounded reward sigma bound ∧
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) <
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward sigma) ∧
        ∃ (responder : ι) (choice : Option ℕ),
          quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward sigma) /
              (Fintype.card ι : ℝ) ≤
            quittingPureTimeDeviationPayoff reward sigma responder choice -
              quittingTerminalPayoff reward sigma responder) :=
  fable_purify_aux reward ((Finset.univ : Finset ι) \ ∅).card ∅ profile
    deadline le_rfl (fun _ hplayer => absurd hplayer (by simp)) hbound
    hminimum hpositive

/-! ## F4: composing with the deadline-descent capstone -/

/-- **F4, shaped form.**  Composing F3's canonical exit with the anchored
erasure and deadline descent capstone.  Either a canonical pure-time profile
strictly above the source's minimum carries a paid pure-time or Never port, or
a deadline-bounded profile strictly above it does. -/
theorem fable_deadlineBounded_minimum_offMinimum_paidPort_shape
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {deadline : ℕ}
    (hbound : FableDeadlineBounded reward profile deadline)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile)) :
    (∃ tau : ι → Option ℕ,
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) <
          quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
            (fableCanonicalProfile reward tau)) ∧
        ∃ (responder : ι) (choice : Option ℕ),
          quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
                (fableCanonicalProfile reward tau)) /
              (Fintype.card ι : ℝ) ≤
            quittingPureTimeDeviationPayoff reward
                (fableCanonicalProfile reward tau) responder choice -
              quittingTerminalPayoff reward
                (fableCanonicalProfile reward tau) responder) ∨
      (∃ (sigma : (quittingGame reward).BehaviorProfile) (bound : ℕ),
        FableDeadlineBounded reward sigma bound ∧
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) <
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward sigma) ∧
        ∃ (responder : ι) (choice : Option ℕ),
          quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward sigma) /
              (Fintype.card ι : ℝ) ≤
            quittingPureTimeDeviationPayoff reward sigma responder choice -
              quittingTerminalPayoff reward sigma responder) := by
  rcases fable_deadlineBounded_minimum_purify_or_paidPort reward profile hbound
    hminimum hpositive with ⟨tau, hvalue, hmin⟩ | hright
  · have hpositiveTau : 0 < quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (fableCanonicalProfile reward tau)) := by
      rw [hvalue]
      exact hpositive
    obtain ⟨target, hlt, hport⟩ :=
      fable_canonicalMinimum_offMinimum_paidPort reward tau hmin hpositiveTau
    refine Or.inl ⟨target, ?_, hport⟩
    rw [← hvalue]
    exact hlt
  · exact Or.inr hright

/-- **F4.**  A deadline-bounded profile whose terminal-semantic pair is a
strictly positive global minimum of total debt exhibits one profile strictly
above that minimum carrying a literal pure-time or Never response whose gain
is at least that profile's average debt. -/
theorem fable_deadlineBounded_minimum_offMinimum_paidPort
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {deadline : ℕ}
    (hbound : FableDeadlineBounded reward profile deadline)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile)) :
    ∃ sigma : (quittingGame reward).BehaviorProfile,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) <
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward sigma) ∧
      ∃ (responder : ι) (choice : Option ℕ),
        quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward sigma) /
            (Fintype.card ι : ℝ) ≤
          quittingPureTimeDeviationPayoff reward sigma responder choice -
            quittingTerminalPayoff reward sigma responder := by
  rcases fable_deadlineBounded_minimum_offMinimum_paidPort_shape reward profile
    hbound hminimum hpositive with ⟨tau, hlt, hport⟩ | ⟨sigma, -, -, hlt, hport⟩
  · exact ⟨fableCanonicalProfile reward tau, hlt, hport⟩
  · exact ⟨sigma, hlt, hport⟩

end GameTheory
