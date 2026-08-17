/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.PlayerDeletionLift
import UniformEquilibrium.Quitting.Cycles.AnchoredSoloPeriodic
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Paths.SurvivalWindowLanding
import MathUE.PMFProduct.Update

/-!
# Merging indistinguishable twins in a quitting game

Two distinct players `d` and `e` are *indistinguishable twins* when they have
the same reward row and no player's payoff can tell which of them belongs to
a quitting coalition, nor whether both do:
`QuittingIndistinguishableTwins`.

The *token game* of such a pair is the one-player-smaller game obtained by
deleting `e`, namely `quittingDeletePlayerReward reward e`, in which the
surviving twin `d` plays the token.  The producer direction
`exists_uniformEquilibriumPayoff_of_indistinguishableTwins` says that a
uniform-equilibrium payoff of the token game yields one for the original
game, and `not_exists_uniformEquilibriumPayoff_token_of_indistinguishableTwins`
is its contrapositive.

The producer is proved from `QuittingTwinMergeable`, which asks for the
shared row and for the two invisibility clauses only at the twins' own row,
omitting them at every other player's row.  Indistinguishability implies it
through `QuittingIndistinguishableTwins.toMergeable`, so every statement is
available under both hypotheses.

The lift prescribes `Never` for the silent twin `e` and gives `d` the token's
strategy.  Every player other than `e` is handled by the exact transport of
`quittingLiftDeletedProfile` in
`UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean`.  The silent twin is handled by
`quittingBestReplyValue_le_twin`: whatever `e` could gain by quitting at some
date, the token `d` could gain by quitting at the minimum of its own
scheduled date and that date.  The one-stage content is
`quittingRootExpectedPayoff_twin_base`: once one twin quits for sure, the
payoff to either twin is the same number whatever the other twin does.

Both clauses of the definition are used, and neither can be dropped.  If the
transposition of `d` and `e` is merely a symmetry of the table, the numbers
`reward (S ∪ {e}) d` — one twin quits and the other does not — are not
determined by the token game, since a token either quits or does not; those
are exactly the rows on which a twin free-rides on its partner's exit.
Merging also changes the available randomizations: two players can realize
the events "exactly one quits" and "both quit" with a joint law that no
single player can produce.
-/

noncomputable section

namespace GameTheory

namespace QuittingTwinMerging

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Indistinguishable twins -/

/-- Distinct players `d` and `e` are **indistinguishable twins** when they
have the same reward row, and every player's payoff depends on a coalition
only through its trace outside `{d, e}` and whether it meets `{d, e}`. -/
structure QuittingIndistinguishableTwins
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (d e : ι) : Prop where
  /-- The two twins are distinct players. -/
  ne : d ≠ e
  /-- The twins have the same reward row. -/
  row_eq : ∀ S, reward S d = reward S e
  /-- Which twin quits is invisible. -/
  merge_swap : ∀ (i : ι) (S : Finset ι), d ∉ S → e ∉ S →
    reward ⟨insert d S, Finset.insert_nonempty d S⟩ i =
      reward ⟨insert e S, Finset.insert_nonempty e S⟩ i
  /-- Whether both twins quit is invisible. -/
  merge_both : ∀ (i : ι) (S : Finset ι), d ∉ S → e ∉ S →
    reward ⟨insert d S, Finset.insert_nonempty d S⟩ i =
      reward ⟨insert d (insert e S), Finset.insert_nonempty d (insert e S)⟩ i

/-- The clauses of `QuittingIndistinguishableTwins` that the merging producer
consumes: the shared row, and the invisibility of which twin quits and of
whether both quit *as recorded by the twins' own row*.  Nothing is required
of any other player's row, so this is a weaker demand on the table than
`QuittingIndistinguishableTwins`. -/
structure QuittingTwinMergeable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (d e : ι) : Prop where
  /-- The two twins are distinct players. -/
  ne : d ≠ e
  /-- The twins have the same reward row. -/
  row_eq : ∀ S, reward S d = reward S e
  /-- Which twin quits is invisible to the twins' own row. -/
  merge_swap : ∀ S : Finset ι, d ∉ S → e ∉ S →
    reward ⟨insert d S, Finset.insert_nonempty d S⟩ d =
      reward ⟨insert e S, Finset.insert_nonempty e S⟩ d
  /-- Whether both twins quit is invisible to the twins' own row. -/
  merge_both : ∀ S : Finset ι, d ∉ S → e ∉ S →
    reward ⟨insert d S, Finset.insert_nonempty d S⟩ d =
      reward ⟨insert d (insert e S), Finset.insert_nonempty d (insert e S)⟩ d

omit [Fintype ι] in
/-- Indistinguishable twins are mergeable. -/
theorem QuittingIndistinguishableTwins.toMergeable
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {d e : ι}
    (htwin : QuittingIndistinguishableTwins reward d e) :
    QuittingTwinMergeable reward d e where
  ne := htwin.ne
  row_eq := htwin.row_eq
  merge_swap := fun S hd he ↦ htwin.merge_swap d S hd he
  merge_both := fun S hd he ↦ htwin.merge_both d S hd he

/-! ## Actions with the twin coordinates prescribed -/

/-- The action `a` with the twin coordinates overwritten by `bd` at `d` and
`be` at `e`. -/
def setTwins (d e : ι) (a : ι → Bool) (bd be : Bool) : ι → Bool :=
  Function.update (Function.update a e be) d bd

/-- The quitters of `a` outside the twin pair. -/
def twinBase (d e : ι) (a : ι → Bool) : Finset ι :=
  ((quittingQuitters a).erase d).erase e

theorem not_mem_twinBase_left (d e : ι) (hne : d ≠ e) (a : ι → Bool) :
    d ∉ twinBase d e a := by
  simp [twinBase, Finset.mem_erase, hne]

theorem not_mem_twinBase_right (d e : ι) (a : ι → Bool) :
    e ∉ twinBase d e a := by
  simp [twinBase, Finset.mem_erase]

theorem quittingQuitters_setTwins_true_true (d e : ι) (hne : d ≠ e) (a : ι → Bool) :
    quittingQuitters (setTwins d e a true true) =
      insert d (insert e (twinBase d e a)) := by
  ext i
  simp only [quittingQuitters, setTwins, twinBase, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase,
    Function.update_apply]
  by_cases hd : i = d <;> by_cases he : i = e <;> simp_all

theorem quittingQuitters_setTwins_true_false (d e : ι) (hne : d ≠ e) (a : ι → Bool) :
    quittingQuitters (setTwins d e a true false) = insert d (twinBase d e a) := by
  ext i
  simp only [quittingQuitters, setTwins, twinBase, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase,
    Function.update_apply]
  by_cases hd : i = d <;> by_cases he : i = e <;> simp_all

theorem quittingQuitters_setTwins_false_true (d e : ι) (hne : d ≠ e) (a : ι → Bool) :
    quittingQuitters (setTwins d e a false true) = insert e (twinBase d e a) := by
  ext i
  simp only [quittingQuitters, setTwins, twinBase, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase,
    Function.update_apply]
  by_cases hd : i = d <;> by_cases he : i = e <;> simp_all

/-! ## The one-stage twin identities -/

/-- Both twins quitting pays the silent twin exactly what the sole exit of
the other twin pays that other twin. -/
theorem quittingRootPayoff_twin_true_true
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {d e : ι}
    (htwin : QuittingTwinMergeable reward d e)
    (V W : Payoff ι) (a : ι → Bool) :
    quittingRootPayoff reward V (setTwins d e a true true) e =
      quittingRootPayoff reward W (setTwins d e a true false) d := by
  have hbase := not_mem_twinBase_left d e htwin.ne a
  have hbase' := not_mem_twinBase_right d e a
  unfold quittingRootPayoff
  rw [dif_pos (by
      rw [quittingQuitters_setTwins_true_true d e htwin.ne a]
      exact Finset.insert_nonempty _ _),
    dif_pos (by
      rw [quittingQuitters_setTwins_true_false d e htwin.ne a]
      exact Finset.insert_nonempty _ _)]
  have hTT := quittingQuitters_setTwins_true_true d e htwin.ne a
  have hTF := quittingQuitters_setTwins_true_false d e htwin.ne a
  have hrow := htwin.row_eq
    ⟨insert d (insert e (twinBase d e a)),
      Finset.insert_nonempty d (insert e (twinBase d e a))⟩
  have hboth := htwin.merge_both (twinBase d e a) hbase hbase'
  rw [show (⟨quittingQuitters (setTwins d e a true true), _⟩ :
        {S : Finset ι // S.Nonempty}) =
      ⟨insert d (insert e (twinBase d e a)),
        Finset.insert_nonempty d _⟩ from Subtype.ext hTT,
    show (⟨quittingQuitters (setTwins d e a true false), _⟩ :
        {S : Finset ι // S.Nonempty}) =
      ⟨insert d (twinBase d e a), Finset.insert_nonempty d _⟩ from Subtype.ext hTF]
  rw [← hrow, ← hboth]

/-- The silent twin quitting alone pays it exactly what the sole exit of the
other twin pays that other twin. -/
theorem quittingRootPayoff_twin_false_true
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {d e : ι}
    (htwin : QuittingTwinMergeable reward d e)
    (V W : Payoff ι) (a : ι → Bool) :
    quittingRootPayoff reward V (setTwins d e a false true) e =
      quittingRootPayoff reward W (setTwins d e a true false) d := by
  have hbase := not_mem_twinBase_left d e htwin.ne a
  have hbase' := not_mem_twinBase_right d e a
  unfold quittingRootPayoff
  rw [dif_pos (by
      rw [quittingQuitters_setTwins_false_true d e htwin.ne a]
      exact Finset.insert_nonempty _ _),
    dif_pos (by
      rw [quittingQuitters_setTwins_true_false d e htwin.ne a]
      exact Finset.insert_nonempty _ _)]
  have hFT := quittingQuitters_setTwins_false_true d e htwin.ne a
  have hTF := quittingQuitters_setTwins_true_false d e htwin.ne a
  have hrow := htwin.row_eq
    ⟨insert e (twinBase d e a), Finset.insert_nonempty e (twinBase d e a)⟩
  have hswap := htwin.merge_swap (twinBase d e a) hbase hbase'
  rw [show (⟨quittingQuitters (setTwins d e a false true), _⟩ :
        {S : Finset ι // S.Nonempty}) =
      ⟨insert e (twinBase d e a), Finset.insert_nonempty e _⟩ from Subtype.ext hFT,
    show (⟨quittingQuitters (setTwins d e a true false), _⟩ :
        {S : Finset ι // S.Nonempty}) =
      ⟨insert d (twinBase d e a), Finset.insert_nonempty d _⟩ from Subtype.ext hTF]
  rw [← hrow, ← hswap]

/-- Twins have equal one-stage values against a common root, as soon as
their continuation values agree. -/
theorem quittingRootExpectedPayoff_twin_step
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {d e : ι}
    (htwin : QuittingTwinMergeable reward d e)
    (root : ι → PMF Bool) (V W : Payoff ι) (htail : V e = W d) :
    quittingRootExpectedPayoff reward V root e =
      quittingRootExpectedPayoff reward W root d := by
  unfold quittingRootExpectedPayoff
  have hpt : (fun action => quittingRootPayoff reward V action e) =
      fun action => quittingRootPayoff reward W action d := by
    funext a
    unfold quittingRootPayoff
    by_cases h : (quittingQuitters a).Nonempty
    · rw [dif_pos h, dif_pos h, ← htwin.row_eq]
    · rw [dif_neg h, dif_neg h, htail]
  rw [hpt]

/-! ## The base case: one twin quitting for sure -/

/-- A product root with both twin coordinates prescribed integrates against
the original root along `setTwins`. -/
theorem expect_pmfPi_setTwins (d e : ι) (root : ι → PMF Bool) (bd be : Bool)
    (f : (ι → Bool) → ℝ) :
    expect (pmfPi (Function.update (Function.update root e (PMF.pure be)) d
        (PMF.pure bd))) f =
      expect (pmfPi root) (fun a => f (setTwins d e a bd be)) := by
  rw [← pmfPi_bind_update_pure, ← pmfPi_bind_update_pure]
  simp only [expect_bind, expect_pure]
  rfl

/-- **The one-stage coupling.**  Once the silent twin quits for sure, its
value equals the value of the other twin quitting for sure, whatever the
continuations and whatever the other twin's own hazard. -/
theorem quittingRootExpectedPayoff_twin_base
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {d e : ι}
    (htwin : QuittingTwinMergeable reward d e)
    (root : ι → PMF Bool) (he : root e = PMF.pure false) (V W : Payoff ι) :
    quittingRootExpectedPayoff reward V
        (Function.update root e (PMF.pure true)) e =
      quittingRootExpectedPayoff reward W
        (Function.update root d (PMF.pure true)) d := by
  have hfd : (Function.update root e (PMF.pure true)) d = root d :=
    Function.update_of_ne htwin.ne _ _
  have hsplit : Function.update root e (PMF.pure true) =
      Function.update (Function.update root e (PMF.pure true)) d (root d) := by
    rw [← hfd, Function.update_eq_self]
  have hR : Function.update root d (PMF.pure true) =
      Function.update (Function.update root e (PMF.pure false)) d
        (PMF.pure true) := by
    rw [← he, Function.update_eq_self]
  rw [hR]
  conv_lhs => rw [hsplit]
  rw [quittingRootExpectedPayoff_update_eq_moverMix]
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_setTwins, expect_pmfPi_setTwins, expect_pmfPi_setTwins]
  have h1 : (fun a => quittingRootPayoff reward V (setTwins d e a true true) e)
      = fun a => quittingRootPayoff reward W (setTwins d e a true false) d :=
    funext fun a => quittingRootPayoff_twin_true_true htwin V W a
  have h2 : (fun a => quittingRootPayoff reward V (setTwins d e a false true) e)
      = fun a => quittingRootPayoff reward W (setTwins d e a true false) d :=
    funext fun a => quittingRootPayoff_twin_false_true htwin V W a
  rw [h1, h2, ← add_mul]
  have hsum : (root d true).toReal + (root d false).toReal = 1 := by
    simpa [Fintype.sum_bool] using
      Math.Probability.pmf_toReal_sum_one (root d)
  rw [hsum, one_mul]

/-! ## The coupling along a deviation date -/

/-- The root chronology in which `who` quits for sure at `date` and follows
`roots` at every other time. -/
def sureQuitAt (who : ι) (roots : ℕ → ι → PMF Bool) (date : ℕ) :
    ℕ → ι → PMF Bool :=
  fun time =>
    if time = date then Function.update (roots time) who (PMF.pure true)
    else roots time

/-- **The coupling.**  If the silent twin `e` never quits on the chronology
`roots`, then its value from quitting for sure at `date` equals the value of
the other twin `d` from following its own hazard until `date` and quitting
for sure there. -/
theorem quittingRootSequenceTerminalValue_twin_coupling
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {d e : ι}
    (htwin : QuittingTwinMergeable reward d e)
    (roots : ℕ → ι → PMF Bool) (he : ∀ time, roots time e = PMF.pure false)
    (date : ℕ) :
    ∀ (n start : ℕ), start + n = date →
      quittingRootSequenceTerminalValue reward (sureQuitAt e roots date) e start =
        quittingRootSequenceTerminalValue reward (sureQuitAt d roots date) d start := by
  intro n
  induction n with
  | zero =>
    intro start hstart
    have hs : start = date := by omega
    subst hs
    rw [quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector,
      quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector]
    have hE : sureQuitAt e roots start start =
        Function.update (roots start) e (PMF.pure true) := by
      simp [sureQuitAt]
    have hD : sureQuitAt d roots start start =
        Function.update (roots start) d (PMF.pure true) := by
      simp [sureQuitAt]
    rw [hE, hD]
    exact quittingRootExpectedPayoff_twin_base htwin (roots start) (he start) _ _
  | succ n ih =>
    intro start hstart
    have hne : start ≠ date := by omega
    have hE : sureQuitAt e roots date start = roots start := by
      simp [sureQuitAt, hne]
    have hD : sureQuitAt d roots date start = roots start := by
      simp [sureQuitAt, hne]
    rw [quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector,
      quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector, hE, hD]
    exact quittingRootExpectedPayoff_twin_step htwin (roots start) _ _
      (ih (start + 1) (by omega))

/-! ## Transporting the silent twin's deviations to the token -/

/-- The token's deviation coupled to a silent-twin quit date: follow the
scheduled hazard until `date`, then quit for sure. -/
def twinCoupledDeviation (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (d : ι) (roots : ℕ → ι → PMF Bool) (date : ℕ) :
    (quittingGame reward).BehaviorStrategy d :=
  fun time _ => if time = date then PMF.pure true else roots time d

theorem quittingRootSequenceUpdate_twinCoupledDeviation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (d : ι) (roots : ℕ → ι → PMF Bool) (date : ℕ) :
    quittingRootSequenceUpdate roots d
        (quittingBehaviorLiveHazard reward
          (twinCoupledDeviation reward d roots date)) =
      sureQuitAt d roots date := by
  funext time
  unfold quittingRootSequenceUpdate sureQuitAt quittingBehaviorLiveHazard
    twinCoupledDeviation
  by_cases h : time = date
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h, Function.update_eq_self]

omit [Fintype ι] in
theorem quittingRootSequenceUpdate_pureTime_eq_sureQuitAt
    (e : ι) (roots : ℕ → ι → PMF Bool)
    (he : ∀ time, roots time e = PMF.pure false) (date : ℕ) :
    quittingRootSequenceUpdate roots e (quittingPureTimeHazard (some date)) =
      sureQuitAt e roots date := by
  funext time
  have hpt : quittingPureTimeHazard (some date) time =
      if time = date then PMF.pure true else PMF.pure false := rfl
  unfold quittingRootSequenceUpdate sureQuitAt
  rw [hpt]
  by_cases h : time = date
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, ← he time, Function.update_eq_self]

omit [DecidableEq ι] in
/-- Terminal payoffs are equal on equal reward rows. -/
theorem quittingTerminalPayoff_congr_row
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {d e : ι}
    (hrow : ∀ S, reward S d = reward S e)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward profile d =
      quittingTerminalPayoff reward profile e := by
  unfold quittingTerminalPayoff
  exact Finset.sum_congr rfl fun S _ ↦ by rw [hrow]

/-- **The silent twin cannot outgain the token.**  On the lift of any token
profile, the best reply value of the silent twin is at most that of the
token. -/
theorem quittingBestReplyValue_le_twin
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {d e : ι}
    (htwin : QuittingTwinMergeable reward d e)
    (profile :
      (quittingGame (quittingDeletePlayerReward reward e)).BehaviorProfile) :
    quittingBestReplyValue reward
        (quittingLiftDeletedProfile reward e profile) e ≤
      quittingBestReplyValue reward
        (quittingLiftDeletedProfile reward e profile) d := by
  set lifted := quittingLiftDeletedProfile reward e profile with hlifted
  have hroots : ∀ time, quittingProfileLiveRoot reward lifted time e =
      PMF.pure false := by
    intro time
    rw [hlifted, quittingProfileLiveRoot_liftDeletedProfile]
    simp [quittingExtendDeletedRoots]
  have hpure : ∀ quitTime : Option ℕ,
      quittingTerminalPayoff reward
          (Function.update lifted e
            (quittingPureTimeBehaviorStrategy reward e quitTime)) e ≤
        quittingBestReplyValue reward lifted d := by
    intro quitTime
    cases quitTime with
    | none =>
      rw [hlifted, Function.update_liftDeletedProfile_never,
        ← quittingTerminalPayoff_congr_row htwin.row_eq]
      have h := le_quittingBestReplyValue reward
        (quittingLiftDeletedProfile reward e profile) d
        ((quittingLiftDeletedProfile reward e profile) d)
      rwa [Function.update_eq_self] at h
    | some date =>
      rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
        quittingBehaviorLiveHazard_pureTimeBehaviorStrategy]
      unfold quittingRootSequenceHazardTerminalValue
      rw [quittingRootSequenceUpdate_pureTime_eq_sureQuitAt e _ hroots date,
        quittingRootSequenceTerminalValue_twin_coupling htwin _ hroots date
          date 0 (by omega)]
      have h := le_quittingBestReplyValue reward lifted d
        (twinCoupledDeviation reward d (quittingProfileLiveRoot reward lifted) date)
      rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue] at h
      unfold quittingRootSequenceHazardTerminalValue at h
      rwa [quittingRootSequenceUpdate_twinCoupledDeviation] at h
  refine quittingBestReplyValue_le reward lifted e (fun dev ↦ ?_)
  refine le_of_forall_pos_le_add (fun ε hε ↦ ?_)
  obtain ⟨quitTime, hq⟩ :=
    exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
      reward lifted e dev hε
  linarith [hpure quitTime]

/-! ## The producer -/

/-- **Twin merging.**  If two players are indistinguishable twins and the
token game obtained by deleting one of them has a uniform-equilibrium payoff,
then so does the original game. -/
theorem exists_uniformEquilibriumPayoff_of_twinMergeable
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {d e : ι}
    (htwin : QuittingTwinMergeable reward d e)
    (htoken : ∃ payoff : Payoff (QuittingDeletedPlayer e),
      (quittingGame (quittingDeletePlayerReward reward e)).IsUniformEquilibriumPayoff
        none payoff) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  rw [quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors]
    at htoken ⊢
  intro ε hε
  obtain ⟨profile, hprofile⟩ := htoken ε hε
  refine ⟨quittingLiftDeletedProfile reward e profile, fun who dev ↦ ?_⟩
  by_cases hwho : who = e
  · subst hwho
    have hbest := quittingBestReplyValue_le_twin htwin profile
    have hdev := le_quittingBestReplyValue reward
      (quittingLiftDeletedProfile reward who profile) who dev
    have htoken' := hprofile ⟨d, htwin.ne⟩
    have hd : quittingBestReplyValue reward
        (quittingLiftDeletedProfile reward who profile) d ≤
        quittingTerminalPayoff reward
          (quittingLiftDeletedProfile reward who profile) d + ε := by
      rw [quittingBestReplyValue_liftDeletedProfile reward who profile
          ⟨d, htwin.ne⟩,
        quittingTerminalPayoff_liftDeletedProfile reward who profile
          ⟨d, htwin.ne⟩]
      exact quittingBestReplyValue_le _ _ _ fun deviation ↦ by
        have := htoken' deviation
        linarith
    have hrow := quittingTerminalPayoff_congr_row htwin.row_eq
      (quittingLiftDeletedProfile reward who profile)
    linarith
  · have hstep := quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation
      reward e profile ⟨who, hwho⟩ dev
    have hbase := quittingTerminalPayoff_liftDeletedProfile reward e profile
      ⟨who, hwho⟩
    have := hprofile ⟨who, hwho⟩
      (quittingDeletePlayerDeviation reward e ⟨who, hwho⟩ dev)
    simp only at hstep hbase
    rw [hstep, hbase]
    exact this

/-- **The contrapositive.**  If a table has indistinguishable twins and no
uniform-equilibrium payoff, then neither does its token game. -/
theorem not_exists_uniformEquilibriumPayoff_token_of_twinMergeable
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {d e : ι}
    (htwin : QuittingTwinMergeable reward d e)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ¬ ∃ payoff : Payoff (QuittingDeletedPlayer e),
      (quittingGame (quittingDeletePlayerReward reward e)).IsUniformEquilibriumPayoff
        none payoff :=
  fun htoken ↦ hno (exists_uniformEquilibriumPayoff_of_twinMergeable htwin htoken)

/-- **No indistinguishable twins in a minimal counterexample.**  If a table
has no uniform-equilibrium payoff while its token game does, then the pair is
not a pair of indistinguishable twins. -/
theorem not_twinMergeable_of_token_uniformEquilibriumPayoff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {d e : ι}
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (htoken : ∃ payoff : Payoff (QuittingDeletedPlayer e),
      (quittingGame (quittingDeletePlayerReward reward e)).IsUniformEquilibriumPayoff
        none payoff) :
    ¬ QuittingTwinMergeable reward d e :=
  fun htwin ↦
    not_exists_uniformEquilibriumPayoff_token_of_twinMergeable htwin hno htoken

/-- The terminal exploitability gap descends to the token game across an
indistinguishable twin pair. -/
theorem exists_terminalExploitabilityGap_token_of_twinMergeable
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {d e : ι}
    (htwin : QuittingTwinMergeable reward d e)
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap) :
    ∃ gap' : ℝ, 0 < gap' ∧
      HasTerminalExploitabilityGap (quittingDeletePlayerReward reward e) gap' := by
  rw [← not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap]
  exact not_exists_uniformEquilibriumPayoff_token_of_twinMergeable htwin
    (quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
      reward hgap hexploit)

/-! ## Every token game arises from an indistinguishable twin pair -/

/-- Collapse the twin pair onto the surviving twin. -/
def twinCollapse {d e : ι} (hne : d ≠ e) : ι → QuittingDeletedPlayer e :=
  fun i => if h : i = e then ⟨d, hne⟩ else ⟨i, h⟩

omit [Fintype ι] in
@[simp] theorem twinCollapse_left {d e : ι} (hne : d ≠ e) :
    twinCollapse hne d = ⟨d, hne⟩ := by
  simp [twinCollapse, hne]

omit [Fintype ι] in
@[simp] theorem twinCollapse_right {d e : ι} (hne : d ≠ e) :
    twinCollapse hne e = ⟨d, hne⟩ := by
  simp [twinCollapse]

omit [Fintype ι] in
@[simp] theorem twinCollapse_val {d e : ι} (hne : d ≠ e)
    (who : QuittingDeletedPlayer e) : twinCollapse hne who.1 = who := by
  simp [twinCollapse, who.2]

/-- Pull a token table back along the collapse. -/
def twinPullback {d e : ι} (hne : d ≠ e)
    (token : {S : Finset (QuittingDeletedPlayer e) // S.Nonempty} →
      Payoff (QuittingDeletedPlayer e)) :
    {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun S i =>
    token ⟨S.1.image (twinCollapse hne), S.2.image _⟩ (twinCollapse hne i)

omit [Fintype ι] in
/-- A pullback along the collapse always has the twin pair
indistinguishable. -/
theorem indistinguishableTwins_twinPullback {d e : ι} (hne : d ≠ e)
    (token : {S : Finset (QuittingDeletedPlayer e) // S.Nonempty} →
      Payoff (QuittingDeletedPlayer e)) :
    QuittingIndistinguishableTwins (twinPullback hne token) d e where
  ne := hne
  row_eq := fun S ↦ by simp [twinPullback]
  merge_swap := fun i S _ _ ↦ by
    have himg : (insert d S).image (twinCollapse hne) =
        (insert e S).image (twinCollapse hne) := by
      rw [Finset.image_insert, Finset.image_insert, twinCollapse_left,
        twinCollapse_right]
    exact congrFun (congrArg token (Subtype.ext himg)) (twinCollapse hne i)
  merge_both := fun i S _ _ ↦ by
    have himg : (insert d S).image (twinCollapse hne) =
        (insert d (insert e S)).image (twinCollapse hne) := by
      rw [Finset.image_insert, Finset.image_insert, Finset.image_insert,
        twinCollapse_left, twinCollapse_right, Finset.insert_idem]
    exact congrFun (congrArg token (Subtype.ext himg)) (twinCollapse hne i)

omit [Fintype ι] in
/-- The token game of a pullback is the table it was pulled back from, so
every one-player-smaller table is the token game of an indistinguishable twin
pair. -/
theorem quittingDeletePlayerReward_twinPullback {d e : ι} (hne : d ≠ e)
    (token : {S : Finset (QuittingDeletedPlayer e) // S.Nonempty} →
      Payoff (QuittingDeletedPlayer e)) :
    quittingDeletePlayerReward (twinPullback hne token) e = token := by
  funext T who
  have himg : (quittingExtendDeletedCoalition e T).1.image (twinCollapse hne)
      = T.1 := by
    ext j
    simp only [quittingExtendDeletedCoalition, Finset.mem_image, Finset.mem_map,
      Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨i, ⟨k, hk, rfl⟩, rfl⟩
      simpa using hk
    · intro hj
      exact ⟨j.1, ⟨j, hj, rfl⟩, twinCollapse_val hne j⟩
  unfold quittingDeletePlayerReward twinPullback
  rw [twinCollapse_val]
  exact congrFun (congrArg token (Subtype.ext himg)) who

/-! ## The same statements under full indistinguishability -/

/-- **Twin merging.**  If two players are indistinguishable twins and the
token game obtained by deleting one of them has a uniform-equilibrium payoff,
then so does the original game. -/
theorem exists_uniformEquilibriumPayoff_of_indistinguishableTwins
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {d e : ι}
    (htwin : QuittingIndistinguishableTwins reward d e)
    (htoken : ∃ payoff : Payoff (QuittingDeletedPlayer e),
      (quittingGame (quittingDeletePlayerReward reward e)).IsUniformEquilibriumPayoff
        none payoff) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_twinMergeable htwin.toMergeable htoken

theorem not_exists_uniformEquilibriumPayoff_token_of_indistinguishableTwins
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {d e : ι}
    (htwin : QuittingIndistinguishableTwins reward d e)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ¬ ∃ payoff : Payoff (QuittingDeletedPlayer e),
      (quittingGame (quittingDeletePlayerReward reward e)).IsUniformEquilibriumPayoff
        none payoff :=
  not_exists_uniformEquilibriumPayoff_token_of_twinMergeable htwin.toMergeable hno

theorem not_indistinguishableTwins_of_token_uniformEquilibriumPayoff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {d e : ι}
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (htoken : ∃ payoff : Payoff (QuittingDeletedPlayer e),
      (quittingGame (quittingDeletePlayerReward reward e)).IsUniformEquilibriumPayoff
        none payoff) :
    ¬ QuittingIndistinguishableTwins reward d e :=
  fun htwin ↦
    not_twinMergeable_of_token_uniformEquilibriumPayoff hno htoken htwin.toMergeable

theorem exists_terminalExploitabilityGap_token_of_indistinguishableTwins
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {d e : ι}
    (htwin : QuittingIndistinguishableTwins reward d e)
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap) :
    ∃ gap' : ℝ, 0 < gap' ∧
      HasTerminalExploitabilityGap (quittingDeletePlayerReward reward e) gap' :=
  exists_terminalExploitabilityGap_token_of_twinMergeable htwin.toMergeable hgap hexploit

omit [Fintype ι] in
/-- A pullback along the collapse is in particular mergeable. -/
theorem twinMergeable_twinPullback {d e : ι} (hne : d ≠ e)
    (token : {S : Finset (QuittingDeletedPlayer e) // S.Nonempty} →
      Payoff (QuittingDeletedPlayer e)) :
    QuittingTwinMergeable (twinPullback hne token) d e :=
  (indistinguishableTwins_twinPullback hne token).toMergeable

end QuittingTwinMerging

end GameTheory
