/-
Pre-mark opponent absorption caps the Never mass.

The pre-mark absorption floor bounds one *finite* object: the opponents' joint
all-Continue survival product over the live word `0, …, m`.  That product is
also an upper bound for a *limit* object, the mass the profile leaves in the
live state forever.

The bridge is elementary.  Live mass obeys the stopping recurrence
`liveMass (t+1) = liveMass t * jointContinue t`, and the joint all-player
Continue mass of a stage is at most the mass with `who` forced to Continue —
forcing one coordinate to Continue deletes a factor in `[0,1]` from the
product.  So the finite live mass at date `m+1` is already below the live word
product, and the limiting live mass is below every finite live mass.

Since `quittingTerminalOutcomeMass reward profile none` *is* the limiting live
mass, the two absorption floors transfer verbatim into ceilings on the Never
coordinate of the terminal outcome law: one for a coordinate tight up to
`sigma` at a single profile, one holding eventually along a limit-tight
sequence.  This is the form a Never-mass consumer reads.
-/
import FablePremarkAbsorptionFloor
import FableLimitTightAbsorptionFloor
import UniformEquilibrium.Quitting.Bellman.Finite.BellmanTelescope
import UniformEquilibrium.Quitting.Boundary.Exceptional.Hazard
import UniformEquilibrium.Quitting.Paths.LiveMassRecurrence
import UniformEquilibrium.Quitting.Paths.LiveTail
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment
import UniformEquilibrium.Quitting.Stationary.LiveMass

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The per-date Continue-mass comparison -/

/-- The joint all-player Continue mass of a stage is at most the mass of the
same stage with `who` forced to Continue.  Forcing a coordinate to Continue
replaces that player's displayed Continue probability by one, and the deleted
factor lies in `[0, 1]`. -/
private theorem fable_jointContinueMass_le_fixedOpponents
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (time : ℕ) :
    quittingJointContinueMass reward profile time ≤
      quittingStationaryFixedOpponentsContinueMass
        (quittingProfileLiveRoot reward profile time) who := by
  have hjoint : quittingJointContinueMass reward profile time =
      quittingStationaryContinueMass (quittingProfileLiveRoot reward profile time) := by
    rw [quittingJointContinueMass_eq_product,
      quittingStationaryContinueMass_eq_prod_continueProbability]
    rfl
  rw [hjoint]
  exact quittingStationaryContinueMass_le_update_pure_false
    (quittingProfileLiveRoot reward profile time) who

/-! ## The finite live-mass ceiling -/

/-- **Finite live-mass ceiling.**  The probability that play is still live
after `m + 1` completed stages is at most the opponents-of-`who` joint
all-Continue survival product over the live word `0, …, m`.

Induction on `m` through the stopping recurrence: each stage contributes its
joint Continue mass, which the per-date comparison bounds by the corresponding
opponent survival factor. -/
theorem fable_liveMass_le_liveWord_opponentSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (m : ℕ) :
    quittingLiveMass reward profile (m + 1) ≤
      ∏ t ∈ Finset.range (m + 1),
        quittingStationaryFixedOpponentsContinueMass
          (quittingProfileLiveRoot reward profile t) who := by
  induction m with
  | zero =>
      rw [Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
        quittingLiveMass_succ, quittingLiveMass_zero, one_mul]
      exact fable_jointContinueMass_le_fixedOpponents reward profile who 0
  | succ m ih =>
      rw [Finset.prod_range_succ, quittingLiveMass_succ]
      exact mul_le_mul ih
        (fable_jointContinueMass_le_fixedOpponents reward profile who (m + 1))
        (quittingJointContinueMass_nonneg reward profile (m + 1))
        (Finset.prod_nonneg fun _ _ =>
          quittingStationaryFixedOpponentsContinueMass_nonneg _ _)

/-! ## The Never-mass ceiling -/

/-- **Never-mass ceiling.**  The mass the profile leaves in the live state
forever — the `none` coordinate of its terminal outcome law — is at most the
opponents-of-`who` joint all-Continue survival product over any live word
`0, …, m`.

The Never coordinate is by definition the limiting live mass, which is below
every finite live mass; the finite live mass at date `m + 1` is below the live
word product.  No hypothesis on the reward table or on the profile is needed. -/
theorem fable_neverMass_le_liveWord_opponentSurvival
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (m : ℕ) :
    quittingTerminalOutcomeMass reward profile none ≤
      ∏ t ∈ Finset.range (m + 1),
        quittingStationaryFixedOpponentsContinueMass
          (quittingProfileLiveRoot reward profile t) who := by
  have hnone : quittingTerminalOutcomeMass reward profile none =
      quittingLiveMassLimit reward profile := rfl
  rw [hnone]
  exact (quittingLiveMassLimit_le reward profile (m + 1)).trans
    (fable_liveMass_le_liveWord_opponentSurvival reward profile who m)

/-- **Near-tight Never-mass ceiling.**  Under the hypotheses of the pre-mark
absorption floor — `who`'s envelope at the profile exceeds their solo quitting
reward by at most `sigma`, while the `m+1`-fold all-Continue spine shift clears
that solo reward by `gamma > 0` — the profile's Never mass is at most
`(2 * M + sigma) / (2 * M + gamma)`.

A tight coordinate with a clearing tail therefore cannot leave much mass live
forever: the opponents have already absorbed a fixed fraction before the mark,
and the Never mass is capped by what survives it. -/
theorem fable_nearTight_neverMass_ceiling
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {M gamma sigma : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (m : ℕ) (hgamma : 0 < gamma)
    (hclose : (quittingTerminalSemanticPair reward profile).2 who ≤
      reward (quittingSingletonTerminal who) who + sigma)
    (hmargin : reward (quittingSingletonTerminal who) who + gamma ≤
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (m + 1))).2 who) :
    quittingTerminalOutcomeMass reward profile none ≤
      (2 * M + sigma) / (2 * M + gamma) :=
  (fable_neverMass_le_liveWord_opponentSurvival reward profile who m).trans
    (fable_nearTight_coordinate_premark_opponentAbsorption_floor reward hreward
      profile who m hgamma hclose hmargin)

/-- **Eventual Never-mass ceiling under limit tightness.**  Along a sequence of
profiles whose prescribed coordinate converges to `who`'s solo quitting reward
and whose post-mark spine-tail debts converge to the minimum debt `D`, every
sufficiently late profile leaves Never mass at most
`(2 * M + sigma) / (2 * M + gamma)`.

The conclusion is genuinely eventual and carries no rate: it inherits both from
the eventual pre-mark absorption floor, applied at each rank's own mark. -/
theorem fable_limitTight_neverMass_eventual_ceiling
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
      quittingTerminalOutcomeMass reward (profile n) none ≤
        (2 * M + sigma) / (2 * M + gamma) :=
  (fable_limitTight_premark_opponentAbsorption_eventual_floor reward hreward source
    hminimum profile mark who hcap htail hgamma hgammaD hsigma).mono
      fun n hn =>
        (fable_neverMass_le_liveWord_opponentSurvival reward (profile n) who
          (mark n)).trans hn

end GameTheory
