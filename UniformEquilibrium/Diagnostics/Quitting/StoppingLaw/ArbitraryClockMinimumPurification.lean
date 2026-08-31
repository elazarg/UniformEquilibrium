import UniformEquilibrium.Quitting.Paths.BehaviorSupportedPureTimeReplacement
import UniformEquilibrium.Diagnostics.Quitting.PureTimeSemanticFiniteRange
import MathUE.Topology.FiniteLabelSubsequence
import UniformEquilibrium.Quitting.Paths.PureTimeDeadlineRank
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum

/-!
# Arbitrary-clock purification at a realized global debt minimum

The induction controls only literal purity and total-debt convergence.  It
does not preserve nonmover caps or individual debt coordinates.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A realizing sequence either purifies to one literal canonical minimum or
has a literal finite-replacement descendant strictly above the minimum. -/
theorem minimumRealizingSequence_purify_or_offMinimum
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimumDebt : ℝ)
    (hlower : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      minimumDebt ≤ quittingTerminalSemanticDebtSum candidate)
    (original : ℕ → (quittingGame reward).BehaviorProfile)
    (hrealizes : Tendsto
      (fun n => quittingTerminalDebtSum reward (original n))
      atTop (𝓝 minimumDebt)) :
    (∃ (sourceIndex : ℕ) (times : QuittingPureTimeProfile ι),
        IsQuittingBehaviorReplacementAncestry (original sourceIndex)
          (quittingPureTimeProfileBehavior reward times) ∧
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingPureTimeProfileBehavior reward times)) = minimumDebt) ∨
      ∃ (sourceIndex : ℕ) (target : (quittingGame reward).BehaviorProfile),
        IsQuittingBehaviorReplacementAncestry (original sourceIndex) target ∧
        minimumDebt < quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward target) := by
  classical
  let PureAt := fun (profile : (quittingGame reward).BehaviorProfile)
      (who : ι) => ∃ choice : Option ℕ,
        profile who = quittingPureTimeBehaviorStrategy reward who choice
  have aux : ∀ (fuel : ℕ) (purified : Finset ι)
      (profiles : ℕ → (quittingGame reward).BehaviorProfile)
      (sourceIndex : ℕ → ℕ),
      ((Finset.univ : Finset ι) \ purified).card ≤ fuel →
      (∀ n who, who ∈ purified → PureAt (profiles n) who) →
      (∀ n, IsQuittingBehaviorReplacementAncestry
        (original (sourceIndex n)) (profiles n)) →
      Tendsto (fun n => quittingTerminalDebtSum reward (profiles n))
        atTop (𝓝 minimumDebt) →
      (∃ (index : ℕ) (times : QuittingPureTimeProfile ι),
          IsQuittingBehaviorReplacementAncestry (original index)
            (quittingPureTimeProfileBehavior reward times) ∧
          quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (quittingPureTimeProfileBehavior reward times)) = minimumDebt) ∨
        ∃ (index : ℕ) (target : (quittingGame reward).BehaviorProfile),
          IsQuittingBehaviorReplacementAncestry (original index) target ∧
          minimumDebt < quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward target) := by
    intro fuel
    induction fuel with
    | zero =>
        intro purified profiles sourceIndex hcard hpure hancestry hdebt
        have hremaining : ((Finset.univ : Finset ι) \ purified) = ∅ :=
          Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
        have hallPure : ∀ n who, PureAt (profiles n) who := by
          intro n who
          apply hpure n who
          by_contra hnot
          have : who ∈ (Finset.univ : Finset ι) \ purified :=
            Finset.mem_sdiff.mpr ⟨Finset.mem_univ who, hnot⟩
          rw [hremaining] at this
          simp at this
        let times : ℕ → QuittingPureTimeProfile ι := fun n who =>
          Classical.choose (hallPure n who)
        have hprofile : ∀ n,
            quittingPureTimeProfileBehavior reward (times n) = profiles n := by
          intro n
          funext who
          exact (Classical.choose_spec (hallPure n who)).symm
        let code : ℕ → QuittingPureClockSemanticCode ι := fun n =>
          Classical.choose (exists_quittingPureClockSemanticCode reward (times n))
        have hcode : ∀ n,
            quittingTerminalSemanticPair reward
                (quittingPureTimeProfileBehavior reward (times n)) =
              (code n).evaluate reward := fun n =>
          Classical.choose_spec
            (exists_quittingPureClockSemanticCode reward (times n))
        obtain ⟨fixed, subsequence, hsubsequence, hfixed⟩ :=
          Math.exists_fixed_label_on_strictMono_subsequence code
        have hdebtSub : Tendsto
            (fun rank => quittingTerminalDebtSum reward
              (profiles (subsequence rank))) atTop (𝓝 minimumDebt) :=
          hdebt.comp hsubsequence.tendsto_atTop
        have hconstant : ∀ rank,
            quittingTerminalDebtSum reward (profiles (subsequence rank)) =
              quittingTerminalSemanticDebtSum (fixed.evaluate reward) := by
          intro rank
          rw [← hprofile (subsequence rank)]
          change quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (quittingPureTimeProfileBehavior reward
                  (times (subsequence rank)))) = _
          rw [hcode, hfixed]
        have hconstantTendsto : Tendsto
            (fun rank => quittingTerminalDebtSum reward
              (profiles (subsequence rank))) atTop
            (𝓝 (quittingTerminalSemanticDebtSum (fixed.evaluate reward))) := by
          simpa only [hconstant] using
            (tendsto_const_nhds : Tendsto
              (fun _ : ℕ => quittingTerminalSemanticDebtSum
                (fixed.evaluate reward)) atTop
              (𝓝 (quittingTerminalSemanticDebtSum (fixed.evaluate reward))))
        have hminimum : quittingTerminalSemanticDebtSum
            (fixed.evaluate reward) = minimumDebt :=
          tendsto_nhds_unique hconstantTendsto hdebtSub
        left
        refine ⟨sourceIndex (subsequence 0), times (subsequence 0), ?_, ?_⟩
        · rw [hprofile]
          exact hancestry (subsequence 0)
        · rw [hcode, hfixed]
          exact hminimum
    | succ fuel ih =>
        intro purified profiles sourceIndex hcard hpure hancestry hdebt
        by_cases hremaining :
            ((Finset.univ : Finset ι) \ purified).Nonempty
        · obtain ⟨who, hwho⟩ := hremaining
          have hwhoNot : who ∉ purified := (Finset.mem_sdiff.mp hwho).2
          let choice : ℕ → Option ℕ := fun n =>
            Classical.choose
              (exists_support_pureTime_payoff_ge_prescribed
                reward (profiles n) who)
          let target : ℕ → (quittingGame reward).BehaviorProfile := fun n =>
            Function.update (profiles n) who
              (quittingPureTimeBehaviorStrategy reward who (choice n))
          have htargetMem : ∀ n,
              quittingTerminalSemanticPair reward (target n) ∈
                quittingTerminalSemanticCarrier reward := fun n =>
            quittingTerminalSemanticPair_mem_carrier reward (target n)
          obtain ⟨cluster, hcluster, subsequence, hsubsequence, htargetTendsto⟩ :=
            (quittingTerminalSemanticCarrier_isCompact reward).tendsto_subseq
              htargetMem
          have htargetDebtTendsto : Tendsto
              (fun rank => quittingTerminalDebtSum reward
                (target (subsequence rank))) atTop
              (𝓝 (quittingTerminalSemanticDebtSum cluster)) := by
            have hcontinuous :=
              continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
                htargetTendsto
            change Tendsto
              (fun rank => quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward
                  (target (subsequence rank)))) atTop
              (𝓝 (quittingTerminalSemanticDebtSum cluster))
            simpa only [Function.comp_def] using hcontinuous
          have hclusterLower : minimumDebt ≤
              quittingTerminalSemanticDebtSum cluster := hlower cluster hcluster
          rcases hclusterLower.lt_or_eq with hstrict | hequal
          · right
            have heventually : ∀ᶠ rank in atTop,
                minimumDebt < quittingTerminalDebtSum reward
                  (target (subsequence rank)) :=
              htargetDebtTendsto.eventually_const_lt hstrict
            obtain ⟨rank, hrank⟩ := heventually.exists
            refine ⟨sourceIndex (subsequence rank), target (subsequence rank), ?_,
              hrank⟩
            exact (hancestry (subsequence rank)).trans
              (isQuittingBehaviorReplacementAncestry_update
                (profiles (subsequence rank)) who _)
          · have hcard' :
                ((Finset.univ : Finset ι) \ insert who purified).card ≤ fuel := by
              rw [Finset.sdiff_insert, Finset.card_erase_of_mem hwho]
              omega
            have hpure' : ∀ rank player,
                player ∈ insert who purified →
                  PureAt (target (subsequence rank)) player := by
              intro rank player hplayer
              by_cases heq : player = who
              · subst player
                exact ⟨choice (subsequence rank), Function.update_self _ _ _⟩
              · obtain ⟨oldChoice, holdChoice⟩ :=
                  hpure (subsequence rank) player
                    ((Finset.mem_insert.mp hplayer).resolve_left heq)
                refine ⟨oldChoice, ?_⟩
                dsimp only [target]
                rw [Function.update_of_ne heq]
                exact holdChoice
            have hancestry' : ∀ rank,
                IsQuittingBehaviorReplacementAncestry
                  (original (sourceIndex (subsequence rank)))
                  (target (subsequence rank)) := by
              intro rank
              exact (hancestry (subsequence rank)).trans
                (isQuittingBehaviorReplacementAncestry_update
                  (profiles (subsequence rank)) who _)
            have hdebt' : Tendsto
                (fun rank => quittingTerminalDebtSum reward
                  (target (subsequence rank))) atTop (𝓝 minimumDebt) := by
              simpa only [hequal] using htargetDebtTendsto
            exact ih (insert who purified) (target ∘ subsequence)
              (sourceIndex ∘ subsequence) hcard'
              (by simpa only [Function.comp_apply] using hpure')
              (by simpa only [Function.comp_apply] using hancestry')
              (by simpa only [Function.comp_apply] using hdebt')
        · have hcardZero :
              ((Finset.univ : Finset ι) \ purified).card = 0 :=
            Finset.card_eq_zero.mpr
              (Finset.not_nonempty_iff_eq_empty.mp hremaining)
          exact ih purified profiles sourceIndex (by omega)
            hpure hancestry hdebt
  simpa only [PureAt] using
    aux (Fintype.card ι) ∅ original id (by simp) (by simp)
      (fun _ => Relation.ReflTransGen.refl) hrealizes

end GameTheory
