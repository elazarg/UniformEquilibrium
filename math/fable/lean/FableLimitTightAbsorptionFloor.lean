/-
Limit tightness prices pre-mark opponent absorption along a whole sequence.

The pre-mark absorption floor is a statement about one profile: a coordinate
that is tight up to `sigma` at the profile, whose post-mark all-Continue spine
tail clears the solo quitting reward by `gamma`, forces the opponents' joint
survival product over the live word to be at most
`(2 * M + sigma) / (2 * M + gamma)`.

A limit-point consumer does not have either hypothesis on the nose.  What it
has instead are two convergences: the prescribed coordinate converges to the
player's solo quitting reward, and the total semantic debt of the post-mark
spine tails converges to the minimum debt over the semantic carrier.  The
near-minimum cap transport converts the second convergence into the spine
margin: at debt within `epsilon` of the minimum `D`, the constant shift
`q = (gamma + D) / 2` is charged at residual width `D - q = (D - gamma) / 2`,
so choosing `epsilon` small compared with that width recovers the full `gamma`
margin.  The first convergence supplies the `sigma` slack directly.

Both hypotheses therefore hold for all large ranks, so the absorption floor
holds eventually.  This is the `Filter.atTop` form the selection argument
consumes.  The choice `epsilon = d ^ 2 / (2 * M + d + 1)` with
`d = (D - gamma) / 2` is one explicit admissible budget; nothing below depends
on it beyond the two inequalities `epsilon < d` and `epsilon * (2 * M + d) ≤ d ^ 2`.
-/
import FablePremarkAbsorptionFloor
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCapNashNearMinimum

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The scalar error budget -/

/-- Scalar core of the eventual margin.  For a residual moat width `d > 0` and
a joining loss bounded by `2 * M`, the explicit near-minimality budget
`epsilon = d ^ 2 / (2 * M + d + 1)` is positive, strictly below `d`, and small
enough that the transported error term `loss * (epsilon / (d - epsilon))` never
exceeds `d`.  Consequently a `q`-shifted floor at `q = gamma + d` degrades to a
floor at `gamma`. -/
private theorem fable_limitTight_error_budget {M loss d epsilon : ℝ}
    (hM : 0 ≤ M) (hloss : loss ≤ 2 * M) (hdpos : 0 < d)
    (hdef : epsilon = d ^ 2 / (2 * M + d + 1)) :
    0 < epsilon ∧ epsilon < d ∧ loss * (epsilon / (d - epsilon)) ≤ d := by
  have hden : (0 : ℝ) < 2 * M + d + 1 := by linarith
  have hepspos : 0 < epsilon := by
    rw [hdef]
    exact div_pos (by positivity) hden
  have hepsd : epsilon < d := by
    rw [hdef, div_lt_iff₀ hden]
    nlinarith [mul_nonneg hM hdpos.le]
  have hgap : 0 < d - epsilon := by linarith
  have hkey : epsilon * (2 * M + d) ≤ d ^ 2 := by
    rw [hdef, div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [sq_nonneg d]
  have hratio : 0 ≤ epsilon / (d - epsilon) := (div_pos hepspos hgap).le
  have hstep : loss * (epsilon / (d - epsilon)) ≤ 2 * M * (epsilon / (d - epsilon)) :=
    mul_le_mul_of_nonneg_right hloss hratio
  have hfinal : 2 * M * (epsilon / (d - epsilon)) ≤ d := by
    rw [← mul_div_assoc, div_le_iff₀ hgap]
    nlinarith
  exact ⟨hepspos, hepsd, hstep.trans hfinal⟩

/-! ## The eventual pre-mark absorption floor -/

/-- **Eventual pre-mark absorption floor under limit tightness.**  Let `source`
attain the minimum total semantic debt `D` over the semantic carrier, and let a
sequence of behavior profiles with marks satisfy: the prescribed coordinate of
`who` converges to `who`'s solo quitting reward, and the total semantic debt of
the post-mark all-Continue spine tails converges to `D`.  Then for every
`0 < gamma < D` and every `sigma > 0`, all sufficiently late ranks obey the
pre-mark absorption floor: the opponents' joint all-Continue survival product
over the live word `0, …, mark n` is at most `(2 * M + sigma) / (2 * M + gamma)`.

The two convergences are used only through their eventual one-sided forms, so
the conclusion is genuinely eventual and carries no rate. -/
theorem fable_limitTight_premark_opponentAbsorption_eventual_floor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (source : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (profile : ℕ → (quittingGame reward).BehaviorProfile) (mark : ℕ → ℕ)
    (who : ι)
    (hcap : Filter.Tendsto
      (fun n => (quittingTerminalSemanticPair reward (profile n)).2 who)
      Filter.atTop (nhds (reward (quittingSingletonTerminal who) who)))
    (htail : Filter.Tendsto
      (fun n => quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward (profile n) (mark n + 1))))
      Filter.atTop (nhds (quittingTerminalSemanticDebtSum source)))
    {gamma sigma : ℝ} (hgamma : 0 < gamma)
    (hgammaD : gamma < quittingTerminalSemanticDebtSum source)
    (hsigma : 0 < sigma) :
    ∀ᶠ n in Filter.atTop,
      (∏ t ∈ Finset.range (mark n + 1),
          quittingStationaryFixedOpponentsContinueMass
            (quittingProfileLiveRoot reward (profile n) t) who) ≤
        (2 * M + sigma) / (2 * M + gamma) := by
  have hM : (0 : ℝ) ≤ M :=
    (abs_nonneg _).trans (hreward (quittingSingletonTerminal who) who)
  have hloss : quittingJoiningLoss reward who ≤ 2 * M :=
    quittingJoiningLoss_le_two_mul who hreward
  set D := quittingTerminalSemanticDebtSum source with hDdef
  set d : ℝ := (D - gamma) / 2 with hddef
  set q : ℝ := (gamma + D) / 2 with hqdef
  set epsilon : ℝ := d ^ 2 / (2 * M + d + 1) with hedef
  have hdpos : 0 < d := by rw [hddef]; linarith
  have hqnonneg : (0 : ℝ) ≤ q := by rw [hqdef]; linarith
  have hDq : D - q = d := by rw [hddef, hqdef]; ring
  have hqd : q - d = gamma := by rw [hddef, hqdef]; ring
  obtain ⟨hepspos, hepsd, hbudget⟩ :=
    fable_limitTight_error_budget hM hloss hdpos hedef
  have htailev : ∀ᶠ n in Filter.atTop,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward (profile n) (mark n + 1))) ≤
        D + epsilon :=
    ((tendsto_order.1 htail).2 (D + epsilon) (by linarith)).mono fun n hn => hn.le
  have hcapev : ∀ᶠ n in Filter.atTop,
      (quittingTerminalSemanticPair reward (profile n)).2 who ≤
        reward (quittingSingletonTerminal who) who + sigma :=
    ((tendsto_order.1 hcap).2 (reward (quittingSingletonTerminal who) who + sigma)
      (by linarith)).mono fun n hn => hn.le
  filter_upwards [htailev, hcapev] with n hnear hclose
  have hpair := quittingTerminalSemanticPair_mem_carrier reward
    (quittingAllContinueProfileSpine reward (profile n) (mark n + 1))
  have hraw := nearMinimumTerminalSemantic_cap_sub_singleton_ge (reward := reward)
    (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward (profile n) (mark n + 1)))
    who D epsilon q hpair hminimum hnear hepspos.le hqnonneg (by rw [hDq]; exact hepsd)
  rw [hDq] at hraw
  have hmargin : reward (quittingSingletonTerminal who) who + gamma ≤
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward (profile n) (mark n + 1))).2 who := by
    linarith
  exact fable_nearTight_coordinate_premark_opponentAbsorption_floor reward hreward
    (profile n) who (mark n) hgamma hclose hmargin

end GameTheory
