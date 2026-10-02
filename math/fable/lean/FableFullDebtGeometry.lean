/-
Punishment-floor safety and full-debt persistence for minimum-debt quitting
semantics.

Two finite-dimensional geometric facts about a minimum-debt terminal semantic
pair all of whose best-response debt coordinates are strictly positive.

The first fact turns the singleton moat of a positive minimum into an eventual
strict punishment-floor margin: literal behavior profiles whose semantic pairs
converge to such a minimum eventually pay *every* player strictly above the
behavioral punishment floor, provided the floor is normal, that is dominated by
the corresponding singleton quitting reward.

The second fact is a persistence statement along one marked exact orbit.  The
orbit's debt coordinates are antitone, and carrier minimality caps their total
loss, so an orbit whose source starts near a full-debt minimum keeps every debt
coordinate above half the full-debt level forever.
-/
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.PaidRowExactPortAlternative

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The complementary debt margin of a semantic pair -/

/-- Removing one player's own debt from the total debt leaves exactly the sum
of the remaining players' debts. -/
private theorem quittingTerminalSemanticDebtSum_sub_debt_eq_sum_erase
    (pair : QuittingTerminalSemanticPair ι) (who : ι) :
    quittingTerminalSemanticDebtSum pair -
        quittingTerminalSemanticDebt pair who =
      ∑ other ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebt pair other :=
  (Finset.sum_erase_eq_sub (Finset.mem_univ who)).symm

/-- With at least two players, a pair whose every debt coordinate is positive
has a strictly positive complementary margin at each player. -/
private theorem quittingTerminalSemanticDebtSum_sub_debt_pos [Nontrivial ι]
    (pair : QuittingTerminalSemanticPair ι)
    (hfull : ∀ who, 0 < quittingTerminalSemanticDebt pair who) (who : ι) :
    0 < quittingTerminalSemanticDebtSum pair -
      quittingTerminalSemanticDebt pair who := by
  rw [quittingTerminalSemanticDebtSum_sub_debt_eq_sum_erase]
  obtain ⟨other, hother⟩ := exists_ne who
  refine Finset.sum_pos (fun player _ => hfull player) ⟨other, ?_⟩
  exact Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩

/-! ## Eventual punishment-floor safety near a full-debt minimum -/

/-- **Eventual punishment-floor safety.**  Let `z` be a carrier point of
minimal total best-response debt, with positive total debt and with strictly
positive debt at every player, and suppose the behavioral punishment floor is
dominated playerwise by the singleton quitting rewards.  Then the literal
prescribed payoffs of any sequence of behavior profiles whose semantic pairs
converge to `z` eventually dominate the punishment floor strictly, uniformly in
the player. -/
theorem fullDebtMinimum_eventually_punishmentFloorSafe_of_semanticTendsto
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} [Nontrivial ι]
    (z : QuittingTerminalSemanticPair ι)
    (hz : z ∈ quittingTerminalSemanticCarrier reward)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum z ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpos : 0 < quittingTerminalSemanticDebtSum z)
    (hfull : ∀ who, 0 < quittingTerminalSemanticDebt z who)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (htendsto : Filter.Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      Filter.atTop (nhds z)) :
    ∀ᶠ n in Filter.atTop, ∀ who,
      quittingPunishmentValue reward who <
        quittingTerminalPayoff reward (profiles n) who := by
  rw [Filter.eventually_all]
  intro who
  have hmargin :=
    minimumTerminalSemantic_singletonMargin (reward := reward) z hz hmin hpos who
  have hgap : 0 < quittingTerminalSemanticDebtSum z -
      quittingTerminalSemanticDebt z who :=
    quittingTerminalSemanticDebtSum_sub_debt_pos z hfull who
  have hdebt : quittingTerminalSemanticDebt z who = z.2 who - z.1 who := rfl
  have hstrict : quittingPunishmentValue reward who < z.1 who := by
    have hfloor := hnormal who
    linarith
  have hevaluate : Continuous
      (fun pair : QuittingTerminalSemanticPair ι => pair.1 who) :=
    (continuous_apply who).comp continuous_fst
  have hcoordinate : Filter.Tendsto
      (fun n => (quittingTerminalSemanticPair reward (profiles n)).1 who)
      Filter.atTop (nhds (z.1 who)) :=
    (hevaluate.tendsto z).comp htendsto
  filter_upwards [hcoordinate.eventually_const_lt hstrict] with n hn
  exact hn

/-! ## Full-debt persistence along a marked exact orbit -/

omit [DecidableEq ι] in
/-- Abstract debt-loss bookkeeping: if every debt coordinate of `current` is
below the corresponding coordinate of `base`, the total debt of `current` is at
least that of a minimum `z`, and the total debt of `base` exceeds that minimum
by at most `δ / 4`, then each coordinate loses at most `δ / 4` and stays above
`δ / 2` whenever `base` starts within `δ / 4` of a full-debt level `δ`. -/
private theorem quittingTerminalSemanticDebt_lowerBound_of_smallTotalLoss
    (base current z : QuittingTerminalSemanticPair ι) {δ : ℝ}
    (hanti : ∀ player, quittingTerminalSemanticDebt current player ≤
      quittingTerminalSemanticDebt base player)
    (hminimum : quittingTerminalSemanticDebtSum z ≤
      quittingTerminalSemanticDebtSum current)
    (hsum : quittingTerminalSemanticDebtSum base ≤
      quittingTerminalSemanticDebtSum z + δ / 4)
    (hnear : ∀ player, quittingTerminalSemanticDebt z player - δ / 4 ≤
      quittingTerminalSemanticDebt base player)
    (hfull : ∀ player, δ ≤ quittingTerminalSemanticDebt z player) (who : ι) :
    δ / 2 ≤ quittingTerminalSemanticDebt current who := by
  have hloss := Finset.single_le_sum
    (f := fun player => quittingTerminalSemanticDebt base player -
      quittingTerminalSemanticDebt current player)
    (fun player _ => sub_nonneg.mpr (hanti player)) (Finset.mem_univ who)
  have htotal : ∑ player, (quittingTerminalSemanticDebt base player -
        quittingTerminalSemanticDebt current player) =
      quittingTerminalSemanticDebtSum base -
        quittingTerminalSemanticDebtSum current := by
    rw [Finset.sum_sub_distrib]
    rfl
  rw [htotal] at hloss
  have hbase := hnear who
  have hlevel := hfull who
  linarith

/-- **Full-debt persistence.**  A marked exact orbit whose source pair is
within `δ / 4` of a full-debt carrier minimum `z`, both coordinatewise and in
total debt, keeps every literal debt coordinate at least `δ / 2` at every
orbit time. -/
theorem nearFullDebtMinimum_markedExactOrbit_debtSupport_lowerBound
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (z : QuittingTerminalSemanticPair ι)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum z ≤
        quittingTerminalSemanticDebtSum candidate)
    {δ : ℝ} (hδ : 0 < δ)
    (hfull : ∀ who, δ ≤ quittingTerminalSemanticDebt z who)
    {source : QuittingPaidRowFloorSafeSource reward}
    (marked : QuittingPaidRowMarkedExactOrbit source)
    (hnear : ∀ who, quittingTerminalSemanticDebt z who - δ / 4 ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward source.profile) who)
    (hsum : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward source.profile) ≤
      quittingTerminalSemanticDebtSum z + δ / 4) :
    ∀ time who, δ / 2 ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (marked.profiles time)) who := by
  have hpositive : (0 : ℝ) < δ := hδ
  intro time who
  have hanti : ∀ player, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (marked.profiles time)) player ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward source.profile) player := by
    intro player
    have hstep := marked.debt_antitone player (Nat.zero_le time)
    simp only [marked.profiles_zero] at hstep
    exact hstep
  have hminimum : quittingTerminalSemanticDebtSum z ≤
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward (marked.profiles time)) :=
    hmin _ (quittingTerminalSemanticPair_mem_carrier reward (marked.profiles time))
  have hbound := quittingTerminalSemanticDebt_lowerBound_of_smallTotalLoss
    (quittingTerminalSemanticPair reward source.profile)
    (quittingTerminalSemanticPair reward (marked.profiles time)) z hanti
    hminimum hsum hnear hfull who
  linarith [hpositive]

end GameTheory
