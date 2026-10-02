/-
The exact owner response at a one-sure product realization.

A *one-date-then-Never* profile plays one product root and then continues
forever.  Fix a player `owner` that quits surely at that root.  Its prescribed
payoff is then exactly the zero-tail Quit endpoint, while its behavioral cap is
the maximum of that endpoint and the *augmented continue value*: the zero-tail
Continue endpoint raised by the opponents' all-Continue mass times the positive
part of the solo reward.

This file exhibits one literal complete behavioral response by `owner` that
changes no opponent, and shows that the response attains the augmented continue
value exactly.  Because only `owner`'s own coordinate is overwritten, `owner`'s
cap is unchanged; so whenever `owner` carries strictly positive terminal
semantic debt, the response gains exactly that debt and kills it.  Total debt of
the response target then splits into a strict increase or an exact tie against
any global carrier minimum, and the leakage identity shows the killed owner debt
can only reappear in aggregate across the other coordinates.

Nothing here selects a cap value without an attaining strategy: the response is
a literal deterministic quit plan, and the sign of the solo reward decides
between one late solo quit and Never.
-/
import FableSureCoreSoftening

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The augmented continue value -/

/-- The zero-tail Continue endpoint of a product root raised by the opponents'
all-Continue mass times the positive part of the observer's solo reward.  This
is the exact value of continuing at the root and then optimizing between one
later solo quit and Never. -/
def fableAugmentedContinueValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  fableContinueEndpoint reward root who +
    fableOppContinue root who *
      max 0 (reward (quittingSingletonTerminal who) who)

theorem fableAugmentedContinueValue_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    fableAugmentedContinueValue reward root who =
      fableContinueEndpoint reward root who +
        fableOppContinue root who *
          max 0 (reward (quittingSingletonTerminal who) who) := rfl

/-- The unpadded cap of a one-date-then-Never profile is the maximum of the
zero-tail Quit endpoint and the augmented continue value. -/
theorem fable_oneDateThenNever_cap_eq_max
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingContinuationBestResponseValue reward
        (quittingOneDateThenNeverProfile reward root) who =
      max (fableQuitEndpoint reward root who)
        (fableAugmentedContinueValue reward root who) :=
  fableQuittingContinuationBestResponseValue_oneDateThenNever reward root who

/-! ## The literal owner response -/

/-- The owner's deterministic quit plan: quit one date after the root when the
solo reward is nonnegative, and never quit otherwise. -/
def fableOneSureOwnerChoice
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) : Option ℕ :=
  if 0 ≤ reward (quittingSingletonTerminal owner) owner then some 1 else none

/-- The response target: the one-date-then-Never profile with `owner`'s own
strategy, and only `owner`'s, replaced by the response plan. -/
def fableOneSureOwnerResponseProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) :
    (quittingGame reward).BehaviorProfile :=
  Function.update (quittingOneDateThenNeverProfile reward root) owner
    (quittingPureTimeBehaviorStrategy reward owner
      (fableOneSureOwnerChoice reward owner))

/-- The response target is literally one pure-time unilateral deviation from the
one-date-then-Never profile. -/
theorem fableOneSureOwnerResponseProfile_payoff_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) :
    quittingTerminalPayoff reward
        (fableOneSureOwnerResponseProfile reward root owner) owner =
      quittingPureTimeDeviationPayoff reward
        (quittingOneDateThenNeverProfile reward root) owner
        (fableOneSureOwnerChoice reward owner) := rfl

/-! ## A1: the response attains the augmented continue value -/

/-- **Theorem A1.**  The owner's literal response attains the augmented continue
value exactly.  No hypothesis on the root is needed: the two sign branches of
the solo reward are the late solo quit and Never. -/
theorem fable_oneSure_ownerResponse_payoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) :
    quittingTerminalPayoff reward
        (fableOneSureOwnerResponseProfile reward root owner) owner =
      fableAugmentedContinueValue reward root owner := by
  rw [fableOneSureOwnerResponseProfile_payoff_eq,
    fableAugmentedContinueValue_eq, fableOneSureOwnerChoice]
  by_cases hs : 0 ≤ reward (quittingSingletonTerminal owner) owner
  · rw [if_pos hs, max_eq_right hs]
    have hlate : quittingPureTimeDeviationPayoff reward
          (quittingOneDateThenNeverProfile reward root) owner (some 1) =
        fableContinueEndpoint reward root owner +
          fableOppContinue root owner *
            reward (quittingSingletonTerminal owner) owner :=
      fablePureTimeDeviationPayoff_oneDateThenNever_succ reward root owner 0
    exact hlate
  · rw [if_neg hs, max_eq_left (not_le.mp hs).le, mul_zero, add_zero]
    exact fablePureTimeDeviationPayoff_oneDateThenNever_none reward root owner

/-! ## A2: own-update cap invariance -/

/-- Overwriting a player's own strategy does not move that player's behavioral
cap: the two suprema range over literally the same set of unilateral updates. -/
theorem fable_continuationBestResponseValue_update_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (strategy : (quittingGame reward).BehaviorStrategy who) :
    quittingContinuationBestResponseValue reward
        (Function.update profile who strategy) who =
      quittingContinuationBestResponseValue reward profile who := by
  unfold quittingContinuationBestResponseValue
  refine congrArg sSup (congrArg Set.range (funext fun deviation => ?_))
  rw [Function.update_idem]

/-- **Theorem A2.**  The owner's cap at the response target equals its cap at the
one-date-then-Never profile.  No opponent changed, so the owner's whole
deviation range is unchanged. -/
theorem fable_oneSure_ownerResponse_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι) :
    quittingContinuationBestResponseValue reward
        (fableOneSureOwnerResponseProfile reward root owner) owner =
      quittingContinuationBestResponseValue reward
        (quittingOneDateThenNeverProfile reward root) owner :=
  fable_continuationBestResponseValue_update_self reward
    (quittingOneDateThenNeverProfile reward root) owner
    (quittingPureTimeBehaviorStrategy reward owner
      (fableOneSureOwnerChoice reward owner))

/-! ## A3: the sure owner's prescribed payoff, cap, gain, and killed debt -/

/-- A sure quitter's prescribed payoff at a one-date-then-Never profile is
exactly the zero-tail Quit endpoint. -/
theorem fable_oneSure_prescribed_eq_quitEndpoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (hsure : (root owner true).toReal = 1) :
    quittingTerminalPayoff reward
        (quittingOneDateThenNeverProfile reward root) owner =
      fableQuitEndpoint reward root owner := by
  have hfalse : (root owner false).toReal = 0 := by
    have hsum := quittingRoot_continueProbability_add_quitProbability root owner
    linarith
  rw [fable_terminalPayoff_oneDateThenNever, hsure, hfalse]
  ring

/-- Terminal semantic debt of a realized profile is its cap minus its prescribed
payoff. -/
theorem fable_semanticDebt_profile_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who =
      quittingContinuationBestResponseValue reward profile who -
        quittingTerminalPayoff reward profile who := rfl

/-- With a sure owner, strictly positive owner debt forces the augmented
continue value strictly above the Quit endpoint. -/
theorem fable_oneSure_quitEndpoint_lt_augmentedContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (hsure : (root owner true).toReal = 1)
    (hdebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root)) owner) :
    fableQuitEndpoint reward root owner <
      fableAugmentedContinueValue reward root owner := by
  rw [fable_semanticDebt_profile_eq, fable_oneDateThenNever_cap_eq_max,
    fable_oneSure_prescribed_eq_quitEndpoint reward root owner hsure] at hdebt
  have hlt : fableQuitEndpoint reward root owner <
      max (fableQuitEndpoint reward root owner)
        (fableAugmentedContinueValue reward root owner) := by linarith
  rcases lt_max_iff.mp hlt with hself | hother
  · exact absurd hself (lt_irrefl _)
  · exact hother

/-- With a sure owner and strictly positive owner debt, the owner's cap at the
one-date-then-Never profile is exactly the augmented continue value. -/
theorem fable_oneSure_cap_eq_augmentedContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (hsure : (root owner true).toReal = 1)
    (hdebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root)) owner) :
    quittingContinuationBestResponseValue reward
        (quittingOneDateThenNeverProfile reward root) owner =
      fableAugmentedContinueValue reward root owner := by
  rw [fable_oneDateThenNever_cap_eq_max]
  exact max_eq_right (fable_oneSure_quitEndpoint_lt_augmentedContinue
    reward root owner hsure hdebt).le

/-- The same statement read off the terminal semantic pair's cap coordinate. -/
theorem fable_oneSure_capCoordinate_eq_augmentedContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (hsure : (root owner true).toReal = 1)
    (hdebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root)) owner) :
    (quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root)).2 owner =
      fableAugmentedContinueValue reward root owner :=
  fable_oneSure_cap_eq_augmentedContinue reward root owner hsure hdebt

/-- **Theorem A3, gain.**  The owner's literal response raises its own payoff by
exactly its terminal semantic debt at the source profile. -/
theorem fable_oneSure_ownerResponse_gain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (hsure : (root owner true).toReal = 1)
    (hdebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root)) owner) :
    quittingTerminalPayoff reward
          (fableOneSureOwnerResponseProfile reward root owner) owner -
        quittingTerminalPayoff reward
          (quittingOneDateThenNeverProfile reward root) owner =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingOneDateThenNeverProfile reward root)) owner := by
  rw [fable_oneSure_ownerResponse_payoff, fable_semanticDebt_profile_eq,
    fable_oneSure_cap_eq_augmentedContinue reward root owner hsure hdebt]

/-- **Theorem A3, killed debt.**  The response target's owner coordinate carries
zero terminal semantic debt. -/
theorem fable_oneSure_ownerResponse_debt_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (hsure : (root owner true).toReal = 1)
    (hdebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root)) owner) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (fableOneSureOwnerResponseProfile reward root owner)) owner = 0 := by
  rw [fable_semanticDebt_profile_eq, fable_oneSure_ownerResponse_cap,
    fable_oneSure_ownerResponse_payoff,
    fable_oneSure_cap_eq_augmentedContinue reward root owner hsure hdebt,
    sub_self]

/-- The owner's strictly positive source debt is a strict payoff gain. -/
theorem fable_oneSure_ownerResponse_payoff_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (hsure : (root owner true).toReal = 1)
    (hdebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root)) owner) :
    quittingTerminalPayoff reward
        (quittingOneDateThenNeverProfile reward root) owner <
      quittingTerminalPayoff reward
        (fableOneSureOwnerResponseProfile reward root owner) owner := by
  have hgain := fable_oneSure_ownerResponse_gain reward root owner hsure hdebt
  linarith

/-! ## A4: the total-debt dichotomy and the leakage identity -/

/-- **Theorem A4.**  Against a global carrier minimum of total terminal semantic
debt, the response target's total debt is either strictly larger or exactly
equal.  The split needs only carrier minimality: the response target is an
attainable semantic pair, hence a carrier point. -/
theorem fable_oneSure_ownerResponse_debtSum_dichotomy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingOneDateThenNeverProfile reward root)) ≤
        quittingTerminalSemanticDebtSum candidate) :
    quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingOneDateThenNeverProfile reward root)) <
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (fableOneSureOwnerResponseProfile reward root owner)) ∨
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (fableOneSureOwnerResponseProfile reward root owner)) =
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingOneDateThenNeverProfile reward root)) := by
  have hle := hmin _ (quittingTerminalSemanticPair_mem_carrier reward
    (fableOneSureOwnerResponseProfile reward root owner))
  rcases lt_or_eq_of_le hle with hstrict | heq
  · exact Or.inl hstrict
  · exact Or.inr heq.symm

/-- **Leakage identity.**  The response target's total debt differs from the
source's by exactly minus the killed owner debt plus the aggregate change over
the remaining coordinates.  No coordinatewise preservation is asserted. -/
theorem fable_oneSure_ownerResponse_debtSum_leak
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (owner : ι)
    (hsure : (root owner true).toReal = 1)
    (hdebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root)) owner) :
    quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (fableOneSureOwnerResponseProfile reward root owner)) -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingOneDateThenNeverProfile reward root)) =
      -quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingOneDateThenNeverProfile reward root)) owner +
        ∑ j ∈ Finset.univ.erase owner,
          (quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (fableOneSureOwnerResponseProfile reward root owner)) j -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (quittingOneDateThenNeverProfile reward root)) j) := by
  have hzero :=
    fable_oneSure_ownerResponse_debt_eq_zero reward root owner hsure hdebt
  set target := quittingTerminalSemanticPair reward
    (fableOneSureOwnerResponseProfile reward root owner) with htarget
  set source := quittingTerminalSemanticPair reward
    (quittingOneDateThenNeverProfile reward root) with hsource
  have hT : ∑ j, quittingTerminalSemanticDebt target j =
      quittingTerminalSemanticDebt target owner +
        ∑ j ∈ Finset.univ.erase owner,
          quittingTerminalSemanticDebt target j :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ owner)).symm
  have hS : ∑ j, quittingTerminalSemanticDebt source j =
      quittingTerminalSemanticDebt source owner +
        ∑ j ∈ Finset.univ.erase owner,
          quittingTerminalSemanticDebt source j :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ owner)).symm
  have hsplit : ∑ j ∈ Finset.univ.erase owner,
        (quittingTerminalSemanticDebt target j -
          quittingTerminalSemanticDebt source j) =
      (∑ j ∈ Finset.univ.erase owner, quittingTerminalSemanticDebt target j) -
        ∑ j ∈ Finset.univ.erase owner,
          quittingTerminalSemanticDebt source j :=
    Finset.sum_sub_distrib _ _
  unfold quittingTerminalSemanticDebtSum
  rw [hT, hS, hsplit, hzero]
  ring

end GameTheory
