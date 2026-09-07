import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPolynomial

/-!
# Joint reward-table and finite-calendar payoff polynomials

Reward entries are variables, not coefficients. The calendar block retains every
player/date coordinate, including Never. Evaluation uses the existing literal
coalition masses and prescribed payoffs; no response-cap claim is made.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One independent coordinate for every nonempty-coalition reward entry. -/
abbrev QuittingRewardTableVariable (ι : Type) :=
  {S : Finset ι // S.Nonempty} × ι

/-- Reward coordinates precede the full, uncompressed calendar coordinate block. -/
abbrev QuittingFiniteCalendarJointVariable (ι : Type) (deadline : ℕ) :=
  QuittingRewardTableVariable ι ⊕ QuittingFiniteCalendarVariable ι deadline

/-- An explicit finite layout with the reward and calendar blocks kept separate. -/
def quittingFiniteCalendarJointCoordinates (deadline : ℕ) :
    QuittingFiniteCalendarJointVariable ι deadline ≃
      Fin (Fintype.card (QuittingRewardTableVariable ι) +
        Fintype.card (QuittingFiniteCalendarVariable ι deadline)) :=
  (Equiv.sumCongr (Fintype.equivFin (QuittingRewardTableVariable ι))
    (Fintype.equivFin (QuittingFiniteCalendarVariable ι deadline))).trans finSumFinEquiv

omit [DecidableEq ι] in
theorem quittingFiniteCalendarJointCoordinates_reward (deadline : ℕ)
    (entry : QuittingRewardTableVariable ι) :
    quittingFiniteCalendarJointCoordinates deadline (Sum.inl entry) =
      Fin.castAdd (Fintype.card (QuittingFiniteCalendarVariable ι deadline))
        (Fintype.equivFin (QuittingRewardTableVariable ι) entry) := rfl

omit [DecidableEq ι] in
theorem quittingFiniteCalendarJointCoordinates_calendar (deadline : ℕ)
    (entry : QuittingFiniteCalendarVariable ι deadline) :
    quittingFiniteCalendarJointCoordinates deadline (Sum.inr entry) =
      Fin.natAdd (Fintype.card (QuittingRewardTableVariable ι))
        (Fintype.equivFin (QuittingFiniteCalendarVariable ι deadline) entry) := rfl

/-- Supply the raw reward entries and arbitrary real calendar coordinates. -/
def quittingFiniteCalendarJointValues
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {deadline : ℕ}
    (values : QuittingFiniteCalendarVariable ι deadline → ℝ) :
    QuittingFiniteCalendarJointVariable ι deadline → ℝ :=
  Sum.elim (fun entry => reward entry.1 entry.2) values

/-- The empty-coalition polynomial is exactly the product of Never entries. -/
def quittingFiniteCalendarNeverMassPolynomial (deadline : ℕ) :
    MvPolynomial (QuittingFiniteCalendarVariable ι deadline) ℝ :=
  ∏ who, MvPolynomial.X (who, none)

omit [DecidableEq ι] in
theorem eval_quittingFiniteCalendarNeverMassPolynomial (deadline : ℕ)
    (values : QuittingFiniteCalendarVariable ι deadline → ℝ) :
    MvPolynomial.eval values (quittingFiniteCalendarNeverMassPolynomial deadline) =
      ∏ who, values (who, none) := by
  simp [quittingFiniteCalendarNeverMassPolynomial]

omit [DecidableEq ι] in
theorem eval_quittingFiniteCalendarNeverMassPolynomial_simplex {deadline : ℕ}
    (profile : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline)) :
    MvPolynomial.eval (fun pair => profile pair.1 pair.2)
      (quittingFiniteCalendarNeverMassPolynomial deadline) =
        quittingFiniteCalendarNeverMass profile := by
  exact eval_quittingFiniteCalendarNeverMassPolynomial deadline _

/-- Existing coalition polynomials are renamed into the calendar block only. -/
def quittingFiniteCalendarJointCoalitionMassPolynomial (deadline : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    MvPolynomial (QuittingFiniteCalendarJointVariable ι deadline) ℝ :=
  MvPolynomial.rename Sum.inr (quittingFiniteCalendarCoalitionMassPolynomial deadline terminal)

/-- Never mass in the same joint coordinate type as the nonempty coalition masses. -/
def quittingFiniteCalendarJointNeverMassPolynomial (deadline : ℕ) :
    MvPolynomial (QuittingFiniteCalendarJointVariable ι deadline) ℝ :=
  MvPolynomial.rename Sum.inr (quittingFiniteCalendarNeverMassPolynomial deadline)

omit [DecidableEq ι] in
theorem eval_quittingFiniteCalendarJointNeverMassPolynomial
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (values : QuittingFiniteCalendarVariable ι deadline → ℝ) :
    MvPolynomial.eval (quittingFiniteCalendarJointValues reward values)
      (quittingFiniteCalendarJointNeverMassPolynomial deadline) =
        ∏ who, values (who, none) := by
  rw [quittingFiniteCalendarJointNeverMassPolynomial, MvPolynomial.eval_rename]
  exact eval_quittingFiniteCalendarNeverMassPolynomial deadline values

/-- The payoff is polynomial jointly in rewards and calendar coordinates. -/
def quittingFiniteCalendarJointPayoffPolynomial (deadline : ℕ) (observer : ι) :
    MvPolynomial (QuittingFiniteCalendarJointVariable ι deadline) ℝ :=
  ∑ terminal, MvPolynomial.X (Sum.inl (terminal, observer)) *
    quittingFiniteCalendarJointCoalitionMassPolynomial deadline terminal

/-- Surplus above the observer's own singleton reward, also a joint polynomial. -/
def quittingFiniteCalendarJointSingletonSurplusPolynomial (deadline : ℕ) (observer : ι) :
    MvPolynomial (QuittingFiniteCalendarJointVariable ι deadline) ℝ :=
  quittingFiniteCalendarJointPayoffPolynomial deadline observer -
    MvPolynomial.X (Sum.inl (⟨{observer}, Finset.singleton_nonempty observer⟩, observer))

theorem eval_quittingFiniteCalendarJointCoalitionMassPolynomial
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (values : QuittingFiniteCalendarVariable ι deadline → ℝ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    MvPolynomial.eval (quittingFiniteCalendarJointValues reward values)
      (quittingFiniteCalendarJointCoalitionMassPolynomial deadline terminal) =
        MvPolynomial.eval values
          (quittingFiniteCalendarCoalitionMassPolynomial deadline terminal) := by
  rw [quittingFiniteCalendarJointCoalitionMassPolynomial, MvPolynomial.eval_rename]
  rfl

/-- The joint and fixed-table polynomials agree at every real calendar point. -/
theorem eval_quittingFiniteCalendarJointPayoffPolynomial
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (values : QuittingFiniteCalendarVariable ι deadline → ℝ) (observer : ι) :
    MvPolynomial.eval (quittingFiniteCalendarJointValues reward values)
      (quittingFiniteCalendarJointPayoffPolynomial deadline observer) =
        MvPolynomial.eval values
          (quittingFiniteCalendarRawPayoffPolynomial reward deadline observer) := by
  simp only [quittingFiniteCalendarJointPayoffPolynomial,
    quittingFiniteCalendarRawPayoffPolynomial, map_sum, map_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_C]
  apply Finset.sum_congr rfl
  intro terminal _
  rw [eval_quittingFiniteCalendarJointCoalitionMassPolynomial]
  rfl

theorem eval_quittingFiniteCalendarJointPayoffPolynomial_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {deadline : ℕ}
    (profile : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline))
    (observer : ι) :
    MvPolynomial.eval (quittingFiniteCalendarJointValues reward
      (fun pair => profile pair.1 pair.2))
      (quittingFiniteCalendarJointPayoffPolynomial deadline observer) =
        quittingFiniteCalendarRawPayoff reward deadline profile observer := by
  rw [eval_quittingFiniteCalendarJointPayoffPolynomial]
  exact eval_quittingFiniteCalendarRawPayoffPolynomial reward deadline observer profile

theorem eval_quittingFiniteCalendarJointSingletonSurplusPolynomial
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (values : QuittingFiniteCalendarVariable ι deadline → ℝ) (observer : ι) :
    MvPolynomial.eval (quittingFiniteCalendarJointValues reward values)
      (quittingFiniteCalendarJointSingletonSurplusPolynomial deadline observer) =
        MvPolynomial.eval values
          (quittingFiniteCalendarRawPayoffPolynomial reward deadline observer) -
            reward ⟨{observer}, Finset.singleton_nonempty observer⟩ observer := by
  rw [quittingFiniteCalendarJointSingletonSurplusPolynomial, map_sub,
    eval_quittingFiniteCalendarJointPayoffPolynomial, MvPolynomial.eval_X]
  rfl

theorem eval_quittingFiniteCalendarJointSingletonSurplusPolynomial_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {deadline : ℕ}
    (profile : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline))
    (observer : ι) :
    MvPolynomial.eval (quittingFiniteCalendarJointValues reward
      (fun pair => profile pair.1 pair.2))
      (quittingFiniteCalendarJointSingletonSurplusPolynomial deadline observer) =
        quittingFiniteCalendarRawPayoff reward deadline profile observer -
          reward ⟨{observer}, Finset.singleton_nonempty observer⟩ observer := by
  rw [eval_quittingFiniteCalendarJointSingletonSurplusPolynomial,
    eval_quittingFiniteCalendarRawPayoffPolynomial]

theorem totalDegree_quittingFiniteCalendarJointPayoffPolynomial_le
    (deadline : ℕ) (observer : ι) :
    (quittingFiniteCalendarJointPayoffPolynomial deadline observer).totalDegree ≤
      1 + Fintype.card ι := by
  unfold quittingFiniteCalendarJointPayoffPolynomial
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  apply Finset.sup_le
  intro terminal _
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_X]
  exact Nat.add_le_add_left
    ((MvPolynomial.totalDegree_rename_le Sum.inr _).trans
      (totalDegree_quittingFiniteCalendarCoalitionMassPolynomial_le deadline terminal)) 1

theorem card_quittingRewardTableVariable_fin_four :
    Fintype.card (QuittingRewardTableVariable (Fin 4)) = 60 := by decide

theorem card_quittingFiniteCalendarVariable_fin_four_twenty :
    Fintype.card (QuittingFiniteCalendarVariable (Fin 4) 20) = 84 := by decide

theorem card_quittingFiniteCalendarJointVariable_fin_four_twenty :
    Fintype.card (QuittingFiniteCalendarJointVariable (Fin 4) 20) = 144 := by
  rw [Fintype.card_sum, card_quittingRewardTableVariable_fin_four,
    card_quittingFiniteCalendarVariable_fin_four_twenty]

theorem totalDegree_quittingFiniteCalendarJointSingletonSurplusPolynomial_le
    (deadline : ℕ) (observer : ι) :
    (quittingFiniteCalendarJointSingletonSurplusPolynomial deadline observer).totalDegree ≤
      1 + Fintype.card ι := by
  unfold quittingFiniteCalendarJointSingletonSurplusPolynomial
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact totalDegree_quittingFiniteCalendarJointPayoffPolynomial_le deadline observer
  · rw [MvPolynomial.totalDegree_X]
    exact Nat.le_add_right 1 _

end GameTheory
