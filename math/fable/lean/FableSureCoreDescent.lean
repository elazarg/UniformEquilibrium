/-
Iterating one sure-core softening step down to a terminal outcome.

`fable_sureCore_softening_step` is a one-step dichotomy at a positive full-debt
global minimum whose sure set `K` has at least two members: either the pure
member-leaving target is strictly off-minimum with the exact stated payoff
gain, or one strictly interior softening of a chosen sure coordinate `p` is
again an attained positive full-debt global minimum, whose sure set is exactly
`K.erase p`.

The second arm strictly shrinks the sure set, so it can be taken only finitely
often.  This file records that iteration.  `FableSofteningReaches` is the
length-indexed reflexive-transitive closure of the second arm; its single
non-reflexive constructor carries, for one step, the softened member's
sureness, the strict interiority of the softening, the debt-sum equality, the
positivity of every debt coordinate of the child, the softened player's exact
payoff rise, and the sure-set update.

`fable_sureCore_descent` runs the dichotomy by induction on `K.card` and stops
at whichever terminal outcome comes first: an off-minimum member-leaving target
at the reached vector, or -- when the sure set has shrunk to two members and
the second arm fires once more -- a strictly positive singleton atom on the
remaining sure quitter.  The chain length is at most `K.card - 1`, so on
`Fin 4` at most three, which is `finFour_fable_sureCore_descent`.

Global minimality travels along the chain for free: the constructor's debt-sum
equality means every vector in the chain is compared against the very same
value, so `FableSofteningReaches.globalMin` turns minimality at the root into
minimality at the reached vector, and `FableSofteningReaches.debt_pos` does the
same for full debt.
-/
import FableSureCoreSoftening

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The softening chain -/

/-- **Softening reachability.**  `FableSofteningReaches reward n v w` says that
`w` is obtained from `v` by exactly `n` second-arm sure-core softening steps.

Each step names the softened coordinate `p`, sure at the current vector, and
the softening amount `θ` strictly inside `(0, 1)`, and records the four facts
the one-step dichotomy's second arm supplies about the child
`Function.update u p (1 - θ)`: its total terminal semantic debt equals the
parent's, every one of its debt coordinates is strictly positive, player `p`'s
prescribed payoff rises by exactly `θ` times its own debt at the parent, and
its sure set is the parent's sure set with `p` removed. -/
inductive FableSofteningReaches
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ℕ → (ι → ℝ) → (ι → ℝ) → Prop where
  | refl (u : ι → ℝ) : FableSofteningReaches reward 0 u u
  | step {n : ℕ} {u w : ι → ℝ} (p : ι) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
      (hsure : u p = 1)
      (hsum : quittingTerminalSemanticDebtSum
          (fableSoftPair reward (Function.update u p (1 - θ))) =
        quittingTerminalSemanticDebtSum (fableSoftPair reward u))
      (hdebt : ∀ i, 0 < quittingTerminalSemanticDebt
        (fableSoftPair reward (Function.update u p (1 - θ))) i)
      (hpay : (fableSoftPair reward (Function.update u p (1 - θ))).1 p =
        (fableSoftPair reward u).1 p +
          θ * quittingTerminalSemanticDebt (fableSoftPair reward u) p)
      (hupdate : ∀ j, Function.update u p (1 - θ) j = 1 ↔ j ≠ p ∧ u j = 1)
      (tail : FableSofteningReaches reward n (Function.update u p (1 - θ)) w) :
      FableSofteningReaches reward (n + 1) u w

/-- Every step preserves total terminal semantic debt. -/
theorem FableSofteningReaches.debtSum_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {n : ℕ} {v w : ι → ℝ}
    (h : FableSofteningReaches reward n v w) :
    quittingTerminalSemanticDebtSum (fableSoftPair reward w) =
      quittingTerminalSemanticDebtSum (fableSoftPair reward v) := by
  induction h with
  | refl _ => rfl
  | step _ _ _ _ _ hsum _ _ _ _ ih => exact ih.trans hsum

/-- Softening keeps the quit-rate vector nonnegative. -/
theorem FableSofteningReaches.nonneg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {n : ℕ} {v w : ι → ℝ}
    (h : FableSofteningReaches reward n v w) : (∀ k, 0 ≤ v k) → ∀ k, 0 ≤ w k := by
  induction h with
  | refl _ => exact fun hu => hu
  | step p _ _ hθ1 _ _ _ _ _ _ ih =>
      refine fun hu => ih fun j => ?_
      by_cases hj : j = p
      · subst hj
        rw [Function.update_self]
        linarith
      · rw [Function.update_of_ne hj]
        exact hu j

/-- Softening keeps the quit-rate vector inside the unit box. -/
theorem FableSofteningReaches.le_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {n : ℕ} {v w : ι → ℝ}
    (h : FableSofteningReaches reward n v w) : (∀ k, v k ≤ 1) → ∀ k, w k ≤ 1 := by
  induction h with
  | refl _ => exact fun hu => hu
  | step p _ hθ0 _ _ _ _ _ _ _ ih =>
      refine fun hu => ih fun j => ?_
      by_cases hj : j = p
      · subst hj
        rw [Function.update_self]
        linarith
      · rw [Function.update_of_ne hj]
        exact hu j

/-- Every vector in the chain has all its terminal semantic debt coordinates
strictly positive. -/
theorem FableSofteningReaches.debt_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {n : ℕ} {v w : ι → ℝ}
    (h : FableSofteningReaches reward n v w) :
    (∀ i, 0 < quittingTerminalSemanticDebt (fableSoftPair reward v) i) →
      ∀ i, 0 < quittingTerminalSemanticDebt (fableSoftPair reward w) i := by
  induction h with
  | refl _ => exact fun hu => hu
  | step _ _ _ _ _ _ hdebt _ _ _ ih => exact fun _ => ih hdebt

/-- Every vector in the chain is again a global minimum of total terminal
semantic debt, because every step compares against the very same value. -/
theorem FableSofteningReaches.globalMin
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {n : ℕ} {v w : ι → ℝ}
    (h : FableSofteningReaches reward n v w)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum (fableSoftPair reward v) ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum (fableSoftPair reward w) ≤
        quittingTerminalSemanticDebtSum candidate := by
  intro candidate hcandidate
  rw [h.debtSum_eq]
  exact hmin candidate hcandidate

/-! ## The two terminal outcomes -/

/-- **First terminal outcome.**  Some sure member `p` of `w` leaves the sure set
at a strictly larger total terminal semantic debt, and its own prescribed payoff
rises by exactly its full debt at `w`.  This is the first arm of the one-step
dichotomy, restated at `w`. -/
def FableSofteningOffMinimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (w : ι → ℝ) : Prop :=
  ∃ p : ι, w p = 1 ∧
    quittingTerminalSemanticDebtSum (fableSoftPair reward w) <
        quittingTerminalSemanticDebtSum
          (fableSoftPair reward (Function.update w p 0)) ∧
      fableSoftPair reward (Function.update w p 0) ∈
        quittingTerminalSemanticCarrier reward ∧
      (fableSoftPair reward (Function.update w p 0)).1 p =
        (fableSoftPair reward w).1 p +
          quittingTerminalSemanticDebt (fableSoftPair reward w) p

/-- **Second terminal outcome.**  The one-date-then-Never profile at the clamped
product root of `w` puts strictly positive mass on some singleton terminal
coalition. -/
def FableSofteningPositiveSingleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (w : ι → ℝ) : Prop :=
  ∃ k : ι, 0 < quittingTerminalOutcomeMass reward (fableSoftProfile reward w)
    (some (quittingSingletonTerminal k))

/-! ## The descent -/

/-- The descent, with an explicit budget on the sure set's size to induct on. -/
private theorem fable_sureCore_descent_ofCard
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (b : ℕ) :
    ∀ v : ι → ℝ, (∀ k, 0 ≤ v k) → (∀ k, v k ≤ 1) →
      ∀ K : Finset ι, (∀ k, k ∈ K ↔ v k = 1) → 1 < K.card → K.card ≤ b →
        (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
          quittingTerminalSemanticDebtSum (fableSoftPair reward v) ≤
            quittingTerminalSemanticDebtSum candidate) →
        (∀ i, 0 < quittingTerminalSemanticDebt (fableSoftPair reward v) i) →
        ∃ (n : ℕ) (w : ι → ℝ), n + 1 ≤ K.card ∧
          FableSofteningReaches reward n v w ∧
            (FableSofteningOffMinimum reward w ∨
              FableSofteningPositiveSingleton reward w) := by
  induction b with
  | zero =>
      intro _ _ _ K _ hK2 hcard _ _
      omega
  | succ b ih =>
      intro v hv0 hv1 K hK hK2 hcard hmin hdebt
      obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < K.card by omega)
      have hp1 : v p = 1 := (hK p).mp hp
      have hcarderase : (K.erase p).card = K.card - 1 := Finset.card_erase_of_mem hp
      rcases fable_sureCore_softening_step reward v hv0 hv1 K hK p hp hK2 hmin hdebt with
        ⟨hlt, hmem, hgain⟩ | ⟨θ, hθ0, hθ1, hsum, hchild, hpay, hupd⟩
      · exact ⟨0, v, by omega, FableSofteningReaches.refl v,
          Or.inl ⟨p, hp1, hlt, hmem, hgain⟩⟩
      · have hv'0 : ∀ k, 0 ≤ Function.update v p (1 - θ) k := by
          intro k
          by_cases hk : k = p
          · subst hk
            rw [Function.update_self]
            linarith
          · rw [Function.update_of_ne hk]
            exact hv0 k
        have hv'1 : ∀ k, Function.update v p (1 - θ) k ≤ 1 := by
          intro k
          by_cases hk : k = p
          · subst hk
            rw [Function.update_self]
            linarith
          · rw [Function.update_of_ne hk]
            exact hv1 k
        have hupdate : ∀ j, Function.update v p (1 - θ) j = 1 ↔ j ≠ p ∧ v j = 1 := by
          intro j
          rw [← hupd j, Finset.mem_erase, hK j]
        have hmin' : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
            quittingTerminalSemanticDebtSum
                (fableSoftPair reward (Function.update v p (1 - θ))) ≤
              quittingTerminalSemanticDebtSum candidate := by
          intro candidate hcandidate
          rw [hsum]
          exact hmin candidate hcandidate
        by_cases hbig : 1 < (K.erase p).card
        · obtain ⟨n, w, hnle, hreach, hend⟩ :=
            ih (Function.update v p (1 - θ)) hv'0 hv'1 (K.erase p) hupd hbig
              (by omega) hmin' hchild
          exact ⟨n + 1, w, by omega,
            FableSofteningReaches.step p θ hθ0 hθ1 hp1 hsum hchild hpay hupdate hreach,
            hend⟩
        · obtain ⟨k, hk⟩ := Finset.card_eq_one.mp (show (K.erase p).card = 1 by omega)
          have hmass :=
            fable_sureCore_softening_singletonMass reward v hv0 hv1 K hK p k hp hk hθ0 hθ1
          refine ⟨1, Function.update v p (1 - θ), by omega,
            FableSofteningReaches.step p θ hθ0 hθ1 hp1 hsum hchild hpay hupdate
              (FableSofteningReaches.refl _),
            Or.inr ⟨k, ?_⟩⟩
          rw [hmass.1]
          exact hmass.2

/-- **Sure-core descent.**  Let `v` be a quit-rate vector in the unit box whose
sure set is exactly `K`, with at least two members, and let the
one-date-then-Never target at `v` be a global minimum of total terminal
semantic debt with every debt coordinate strictly positive.

Then finitely many -- at most `K.card - 1` -- single-coordinate softenings, each
one a full-debt attained global-minimum child recorded by
`FableSofteningReaches`, reach a vector `w` at which the descent terminates in
one of exactly two ways: some sure member of `w` leaves the sure set strictly
off-minimum with its exact full-debt payoff gain, or the target at `w` already
puts strictly positive mass on a singleton terminal coalition. -/
theorem fable_sureCore_descent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (v : ι → ℝ) (hv0 : ∀ k, 0 ≤ v k) (hv1 : ∀ k, v k ≤ 1)
    (K : Finset ι) (hK : ∀ k, k ∈ K ↔ v k = 1) (hK2 : 1 < K.card)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum (fableSoftPair reward v) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hdebt : ∀ i, 0 < quittingTerminalSemanticDebt (fableSoftPair reward v) i) :
    ∃ (n : ℕ) (w : ι → ℝ), n + 1 ≤ K.card ∧
      FableSofteningReaches reward n v w ∧
        (FableSofteningOffMinimum reward w ∨
          FableSofteningPositiveSingleton reward w) :=
  fable_sureCore_descent_ofCard reward K.card v hv0 hv1 K hK hK2 le_rfl hmin hdebt

/-- **Four players: at most three softenings.**  On `Fin 4` a sure set has at
most four members, so the sure-core descent terminates after at most three
softening steps. -/
theorem finFour_fable_sureCore_descent
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (v : Fin 4 → ℝ) (hv0 : ∀ k, 0 ≤ v k) (hv1 : ∀ k, v k ≤ 1)
    (K : Finset (Fin 4)) (hK : ∀ k, k ∈ K ↔ v k = 1) (hK2 : 1 < K.card)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum (fableSoftPair reward v) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hdebt : ∀ i, 0 < quittingTerminalSemanticDebt (fableSoftPair reward v) i) :
    ∃ (n : ℕ) (w : Fin 4 → ℝ), n ≤ 3 ∧
      FableSofteningReaches reward n v w ∧
        (FableSofteningOffMinimum reward w ∨
          FableSofteningPositiveSingleton reward w) := by
  obtain ⟨n, w, hnle, hreach, hend⟩ :=
    fable_sureCore_descent reward v hv0 hv1 K hK hK2 hmin hdebt
  have hcard : K.card ≤ 4 := by simpa using Finset.card_le_univ K
  exact ⟨n, w, by omega, hreach, hend⟩

end GameTheory
