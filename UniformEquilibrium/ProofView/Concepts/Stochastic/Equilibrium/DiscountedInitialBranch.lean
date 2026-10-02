import UniformEquilibrium.ProofView.Concepts.Stochastic.Equilibrium.DiscountedContinuation
import UniformEquilibrium.ProofView.Concepts.Stochastic.Transform.Repeated.InitialActionAffineness

/-!
# Actual initial-action and continuation deviations

One actual unilateral behavior strategy combines an arbitrary initial mixed
action with complete unilateral replies at every first-stage public history.
Its exact discounted payoff supplies the current-plus-continuation matrix
inequality used in Sorin (1986), Proposition 15. Those deviation identities
need no equilibrium or joint-payoff premise at unsupported histories.

Conversely, an initial mixed Nash profile in the actual-child effective game
and discounted Nash at every supplied child imply full behavioral Nash of
their actual dispatcher. This construction includes off-path child Nash.
-/

noncomputable section

namespace GameTheory.KernelGame

open _root_.Math.Probability
open scoped BigOperators

/-- The actual public history after one prescribed joint action. -/
def realizedActionFirstHistory {ι : Type} (G : KernelGame ι) (joint : Profile G) :
    G.realizedActionStochasticGame.Hist 1 :=
  G.realizedActionStochasticGame.consHist (PUnit.unit, joint)
    (G.realizedActionStochasticGame.emptyHist PUnit.unit)

/-- The actual first-history law is the image of the independent first-action
law; the repeated game has one deterministic state. -/
theorem realizedAction_histDist_one_eq_map
    {ι : Type} (G : KernelGame ι) [Fintype ι]
    (profile : G.realizedActionStochasticGame.BehaviorProfile) :
    G.realizedActionStochasticGame.histDist profile PUnit.unit 1 =
      (Math.PMFProduct.pmfPi (G.realizedActionInitialMixedProfile profile)).map
        G.realizedActionFirstHistory := by
  rw [G.realizedActionStochasticGame.histDist_succ_shift profile PUnit.unit 0]
  change (Math.PMFProduct.pmfPi (G.realizedActionInitialMixedProfile profile)).bind
      (fun joint => (PMF.pure PUnit.unit).bind (fun state =>
        (G.realizedActionStochasticGame.histDist
          (G.realizedActionStochasticGame.shiftProfile profile (PUnit.unit, joint))
          state 0).map (G.realizedActionStochasticGame.consHist (PUnit.unit, joint)))) = _
  simp only [G.realizedActionStochasticGame.histDist_zero, PMF.pure_map, PMF.pure_bind]
  rfl

/-- Exact expectation transfer along the actual first-action history map. -/
theorem realizedAction_expect_histDist_one
    {ι : Type} (G : KernelGame ι) [Fintype ι]
    (profile : G.realizedActionStochasticGame.BehaviorProfile)
    (value : G.realizedActionStochasticGame.Hist 1 → ℝ) :
    expect (G.realizedActionStochasticGame.histDist profile PUnit.unit 1) value =
      expect (Math.PMFProduct.pmfPi (G.realizedActionInitialMixedProfile profile))
        (fun joint => value (G.realizedActionFirstHistory joint)) := by
  rw [G.realizedAction_histDist_one_eq_map, expect_map]

/-- On the one-state realized-action carrier, every full child family is
automatically compatible with the canonical dispatcher, including off path. -/
theorem realizedAction_terminalChildFamilyCompatible
    {ι : Type} (G : KernelGame ι) {depth : ℕ}
    (child : G.realizedActionStochasticGame.Hist depth →
      G.realizedActionStochasticGame.BehaviorProfile) :
    G.realizedActionStochasticGame.TerminalChildFamilyCompatible child := by
  intro base who suffixLength suffix
  have hstart := G.realizedActionHist_startsAt base suffix
  have h := G.realizedActionStochasticGame.terminalChildDispatcher_appendHist
    (child base) child base suffix hstart who
  simpa only [StochasticGame.terminalChildDispatcher,
    dite_eq_left (Nat.le_add_right depth suffixLength)] using h

/-- An actual full unilateral deviation with an arbitrary first mixed
action and one complete reply at every first-stage public history. -/
def realizedActionInitialBranchDeviation
    {ι : Type} (G : KernelGame ι) [DecidableEq ι]
    (profile : G.realizedActionStochasticGame.BehaviorProfile) (who : ι)
    (mixed : PMF (G.Strategy who))
    (reply : G.realizedActionStochasticGame.Hist 1 →
      G.realizedActionStochasticGame.BehaviorStrategy who) :
    G.realizedActionStochasticGame.BehaviorStrategy who :=
  G.realizedActionStochasticGame.terminalChildDispatcher 1
    (Function.update profile who (fun _time _history => mixed))
    (fun base => Function.update
      (G.realizedActionStochasticGame.afterHistoryProfile profile base) who (reply base)) who

/-- Only the selected player's actual initial randomization is replaced. -/
theorem realizedActionInitialMixedProfile_update_initialBranchDeviation
    {ι : Type} (G : KernelGame ι) [DecidableEq ι]
    (profile : G.realizedActionStochasticGame.BehaviorProfile) (who : ι)
    (mixed : PMF (G.Strategy who))
    (reply : G.realizedActionStochasticGame.Hist 1 →
      G.realizedActionStochasticGame.BehaviorStrategy who) :
    G.realizedActionInitialMixedProfile
        (Function.update profile who
          (G.realizedActionInitialBranchDeviation profile who mixed reply)) =
      Function.update (G.realizedActionInitialMixedProfile profile) who mixed := by
  funext player
  by_cases hplayer : player = who
  · subst player
    simp only [realizedActionInitialMixedProfile, Function.update_self,
      realizedActionInitialBranchDeviation]
    rw [G.realizedActionStochasticGame.terminalChildDispatcher_before
      _ _ (by omega) who]
    simp only [Function.update_self]
  · simp only [realizedActionInitialMixedProfile, Function.update_of_ne hplayer]

/-- After each actual first-stage history, exactly one player's complete
continuation is changed to its assigned reply; actual opponents are retained. -/
theorem realizedAction_afterHistoryProfile_update_initialBranchDeviation
    {ι : Type} (G : KernelGame ι) [DecidableEq ι]
    (profile : G.realizedActionStochasticGame.BehaviorProfile) (who : ι)
    (mixed : PMF (G.Strategy who))
    (reply : G.realizedActionStochasticGame.Hist 1 →
      G.realizedActionStochasticGame.BehaviorStrategy who)
    (base : G.realizedActionStochasticGame.Hist 1) :
    G.realizedActionStochasticGame.afterHistoryProfile
        (Function.update profile who
          (G.realizedActionInitialBranchDeviation profile who mixed reply)) base =
      Function.update
        (G.realizedActionStochasticGame.afterHistoryProfile profile base) who (reply base) := by
  let selection := Function.update profile who (fun _time _history => mixed)
  let child := fun reached => Function.update
    (G.realizedActionStochasticGame.afterHistoryProfile profile reached) who (reply reached)
  have hdispatcher := G.realizedActionStochasticGame.afterHistoryProfile_terminalChildDispatcher
    1 selection child base (G.realizedAction_terminalChildFamilyCompatible child base)
  have hstrategy := congrFun hdispatcher who
  have hrebase : G.realizedActionStochasticGame.afterHistoryStrategy
      (G.realizedActionInitialBranchDeviation profile who mixed reply) base = reply base := by
    simpa only [realizedActionInitialBranchDeviation, selection, child,
      Function.update_self] using! hstrategy
  rw [G.realizedActionStochasticGame.afterHistoryProfile_update, hrebase]

/-- Exact one-stage actual payoff decomposition indexed by the actual
first joint action, not by a supplied continuation-payoff matrix. -/
theorem realizedAction_discountedPayoff_firstHistory
    {ι : Type} (G : KernelGame ι) [Fintype ι]
    [∀ player, Fintype (G.Strategy player)]
    (profile : G.realizedActionStochasticGame.BehaviorProfile) (who : ι)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    G.realizedActionStochasticGame.discountedPayoff β profile PUnit.unit who =
      expect (Math.PMFProduct.pmfPi (G.realizedActionInitialMixedProfile profile))
        (fun joint => (1 - β) * G.eu joint who +
          β * G.realizedActionStochasticGame.discountedPayoff β
            (G.realizedActionStochasticGame.afterHistoryProfile profile
              (G.realizedActionFirstHistory joint)) PUnit.unit who) := by
  let : Finite G.realizedActionStochasticGame.State :=
    inferInstanceAs (Finite PUnit)
  let (player : ι) : Finite (G.realizedActionStochasticGame.Act player) :=
    @Finite.of_fintype _ (inferInstanceAs (Fintype (G.Strategy player)))
  have h := G.realizedActionStochasticGame.discountedPayoff_prefix_decomposition
    profile PUnit.unit 1 who hβ0 hβ1
  simp only [Finset.sum_range_one, pow_zero, pow_one, one_mul,
    G.realizedActionStochasticGame.expectedStagePayoff_zero] at h
  have hstate : (fun base : G.realizedActionStochasticGame.Hist 1 =>
      G.realizedActionStochasticGame.discountedPayoff β
        (G.realizedActionStochasticGame.afterHistoryProfile profile base) base.2 who) =
      fun base => G.realizedActionStochasticGame.discountedPayoff β
        (G.realizedActionStochasticGame.afterHistoryProfile profile base) PUnit.unit who := by
    funext base
    rw [show base.2 = PUnit.unit from Subsingleton.elim _ _]
  rw [hstate, G.realizedAction_expect_histDist_one] at h
  unfold StochasticGame.stageEUAt at h
  change G.realizedActionStochasticGame.discountedPayoff β profile PUnit.unit who =
    (1 - β) * expect
        (Math.PMFProduct.pmfPi (G.realizedActionInitialMixedProfile profile))
        (fun joint => G.eu joint who) +
      β * expect (Math.PMFProduct.pmfPi (G.realizedActionInitialMixedProfile profile))
        (fun joint => G.realizedActionStochasticGame.discountedPayoff β
          (G.realizedActionStochasticGame.afterHistoryProfile profile
            (G.realizedActionFirstHistory joint)) PUnit.unit who) at h
  rw [expect_add, expect_const_mul, expect_const_mul]
  exact h

/-- Exact payoff of the actually assembled full unilateral initial/child
deviation, including replies on formerly unreachable first histories. -/
theorem realizedAction_discountedPayoff_initialBranchDeviation
    {ι : Type} (G : KernelGame ι) [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Strategy player)]
    (profile : G.realizedActionStochasticGame.BehaviorProfile) (who : ι)
    (mixed : PMF (G.Strategy who))
    (reply : G.realizedActionStochasticGame.Hist 1 →
      G.realizedActionStochasticGame.BehaviorStrategy who)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    G.realizedActionStochasticGame.discountedPayoff β
        (Function.update profile who
          (G.realizedActionInitialBranchDeviation profile who mixed reply)) PUnit.unit who =
      expect (Math.PMFProduct.pmfPi
        (Function.update (G.realizedActionInitialMixedProfile profile) who mixed))
        (fun joint => (1 - β) * G.eu joint who +
          β * G.realizedActionStochasticGame.discountedPayoff β
            (Function.update (G.realizedActionStochasticGame.afterHistoryProfile profile
              (G.realizedActionFirstHistory joint)) who
                (reply (G.realizedActionFirstHistory joint))) PUnit.unit who) := by
  have h := G.realizedAction_discountedPayoff_firstHistory
    (Function.update profile who
      (G.realizedActionInitialBranchDeviation profile who mixed reply)) who hβ0 hβ1
  rw [G.realizedActionInitialMixedProfile_update_initialBranchDeviation] at h
  simp_rw [G.realizedAction_afterHistoryProfile_update_initialBranchDeviation] at h
  exact h

/-- Root Nash caps every actually assembled initial-action/child deviation;
the replies are arbitrary full unilateral behavioral strategies, not Nash
pairs supplied on unsupported histories. -/
theorem realizedAction_discountedNash_initialBranchDeviation_bound
    {ι : Type} (G : KernelGame ι) [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Strategy player)]
    (profile : G.realizedActionStochasticGame.BehaviorProfile)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hnash : G.realizedActionStochasticGame.IsDiscountedεNash β PUnit.unit 0 profile)
    (who : ι) (mixed : PMF (G.Strategy who))
    (reply : G.realizedActionStochasticGame.Hist 1 →
      G.realizedActionStochasticGame.BehaviorStrategy who) :
    expect (Math.PMFProduct.pmfPi
        (Function.update (G.realizedActionInitialMixedProfile profile) who mixed))
        (fun joint => (1 - β) * G.eu joint who +
          β * G.realizedActionStochasticGame.discountedPayoff β
            (Function.update (G.realizedActionStochasticGame.afterHistoryProfile profile
              (G.realizedActionFirstHistory joint)) who
                (reply (G.realizedActionFirstHistory joint))) PUnit.unit who) ≤
      G.realizedActionStochasticGame.discountedPayoff β profile PUnit.unit who := by
  have h := hnash who (G.realizedActionInitialBranchDeviation profile who mixed reply)
  rw [G.realizedAction_discountedPayoff_initialBranchDeviation
    profile who mixed reply hβ0 hβ1] at h
  simpa only [add_zero] using h

/-- One actual profile with the specified independent initial actions and
one complete continuation at every first-stage public history. -/
def realizedActionInitialChildDispatcher
    {ι : Type} (G : KernelGame ι)
    (mixed : ∀ who, PMF (G.Strategy who))
    (child : G.realizedActionStochasticGame.Hist 1 →
      G.realizedActionStochasticGame.BehaviorProfile) :
    G.realizedActionStochasticGame.BehaviorProfile :=
  G.realizedActionStochasticGame.terminalChildDispatcher 1
    (fun who _time _history => mixed who) child

/-- The initial randomization of the actual dispatcher is exactly the
supplied independent mixed profile. -/
theorem realizedActionInitialMixedProfile_initialChildDispatcher
    {ι : Type} (G : KernelGame ι)
    (mixed : ∀ who, PMF (G.Strategy who))
    (child : G.realizedActionStochasticGame.Hist 1 →
      G.realizedActionStochasticGame.BehaviorProfile) :
    G.realizedActionInitialMixedProfile
        (G.realizedActionInitialChildDispatcher mixed child) = mixed := by
  funext who
  exact G.realizedActionStochasticGame.terminalChildDispatcher_before
    (fun player _time _history => mixed player) child (by omega) who
    (G.realizedActionStochasticGame.emptyHist PUnit.unit)

/-- The effective first-stage game uses actual joint child payoffs, not
independently selected individual best-response values. -/
def realizedActionDiscountedChildGame
    {ι : Type} (G : KernelGame ι) [Fintype ι] (β : ℝ)
    (child : G.realizedActionStochasticGame.Hist 1 →
      G.realizedActionStochasticGame.BehaviorProfile) : KernelGame ι :=
  KernelGame.ofPureEU G.Strategy (fun joint who =>
    (1 - β) * G.eu joint who +
      β * G.realizedActionStochasticGame.discountedPayoff β
        (child (G.realizedActionFirstHistory joint)) PUnit.unit who)

/-- Exact mixed evaluation of the actual-child effective game. -/
theorem realizedActionDiscountedChildGame_mixedEU
    {ι : Type} (G : KernelGame ι) [Fintype ι]
    [∀ who, Fintype (G.Strategy who)] (β : ℝ)
    (child : G.realizedActionStochasticGame.Hist 1 →
      G.realizedActionStochasticGame.BehaviorProfile)
    (mixed : ∀ who, PMF (G.Strategy who)) (who : ι) :
    (G.realizedActionDiscountedChildGame β child).mixedExtension.eu mixed who =
      expect (Math.PMFProduct.pmfPi mixed) (fun joint =>
        (1 - β) * G.eu joint who +
          β * G.realizedActionStochasticGame.discountedPayoff β
            (child (G.realizedActionFirstHistory joint)) PUnit.unit who) := by
  let : Finite (G.realizedActionDiscountedChildGame β child).Outcome := by
    classical
    change Finite (∀ player, G.Strategy player)
    exact Finite.of_fintype _
  simpa only [realizedActionDiscountedChildGame, KernelGame.eu_ofPureEU] using!
    (G.realizedActionDiscountedChildGame β child).mixedExtension_eu mixed who

/-- The assembled profile has exactly the payoff of its actual-child
effective game at the chosen independent initial mixed action. -/
theorem realizedAction_discountedPayoff_initialChildDispatcher
    {ι : Type} (G : KernelGame ι) [Fintype ι]
    [∀ who, Fintype (G.Strategy who)]
    (mixed : ∀ who, PMF (G.Strategy who))
    (child : G.realizedActionStochasticGame.Hist 1 →
      G.realizedActionStochasticGame.BehaviorProfile)
    (who : ι) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    G.realizedActionStochasticGame.discountedPayoff β
        (G.realizedActionInitialChildDispatcher mixed child) PUnit.unit who =
      (G.realizedActionDiscountedChildGame β child).mixedExtension.eu mixed who := by
  have hchild : ∀ base,
      G.realizedActionStochasticGame.afterHistoryProfile
          (G.realizedActionInitialChildDispatcher mixed child) base = child base := by
    intro base
    exact G.realizedActionStochasticGame.afterHistoryProfile_terminalChildDispatcher
      1 (fun player _time _history => mixed player) child base
      (G.realizedAction_terminalChildFamilyCompatible child base)
  have h := G.realizedAction_discountedPayoff_firstHistory
    (G.realizedActionInitialChildDispatcher mixed child) who hβ0 hβ1
  rw [G.realizedActionInitialMixedProfile_initialChildDispatcher] at h
  simp_rw [hchild] at h
  rw [G.realizedActionDiscountedChildGame_mixedEU]
  exact h

/-- All actual children being discounted Nash, together with initial mixed
Nash in their effective game, implies full behavioral Nash of the dispatcher.
The child premise includes initially unreachable histories, which a root
deviation may reach. Discount zero is allowed; no tail division is used. -/
theorem realizedAction_initialChildDispatcher_isDiscountedNash
    {ι : Type} (G : KernelGame ι) [Fintype ι] [DecidableEq ι]
    [∀ who, Fintype (G.Strategy who)]
    (mixed : ∀ who, PMF (G.Strategy who))
    (child : G.realizedActionStochasticGame.Hist 1 →
      G.realizedActionStochasticGame.BehaviorProfile)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hchild : ∀ base,
      G.realizedActionStochasticGame.IsDiscountedεNash β PUnit.unit 0 (child base))
    (hinitial : (G.realizedActionDiscountedChildGame β child).mixedExtension.IsNash mixed) :
    G.realizedActionStochasticGame.IsDiscountedεNash β PUnit.unit 0
      (G.realizedActionInitialChildDispatcher mixed child) := by
  intro who deviation
  let first : PMF (G.Strategy who) :=
    deviation 0 (G.realizedActionStochasticGame.emptyHist PUnit.unit)
  have hfirst :
      G.realizedActionInitialMixedProfile
          (Function.update (G.realizedActionInitialChildDispatcher mixed child) who deviation) =
        Function.update mixed who first := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp only [realizedActionInitialMixedProfile, Function.update_self, first]
    · simp only [realizedActionInitialMixedProfile, Function.update_of_ne hplayer]
      exact congrFun (G.realizedActionInitialMixedProfile_initialChildDispatcher mixed child)
        player
  have hrebase : ∀ base,
      G.realizedActionStochasticGame.afterHistoryProfile
          (Function.update (G.realizedActionInitialChildDispatcher mixed child) who deviation)
          base =
        Function.update (child base) who
          (G.realizedActionStochasticGame.afterHistoryStrategy deviation base) := by
    intro base
    exact G.realizedActionStochasticGame.afterHistoryProfile_update_terminalChildDispatcher
      1 (fun player _time _history => mixed player) child base
      (G.realizedAction_terminalChildFamilyCompatible child base) who deviation
  have hpay := G.realizedAction_discountedPayoff_firstHistory
    (Function.update (G.realizedActionInitialChildDispatcher mixed child) who deviation)
    who hβ0 hβ1
  rw [hfirst] at hpay
  simp_rw [hrebase] at hpay
  have hcap :
      G.realizedActionStochasticGame.discountedPayoff β
          (Function.update (G.realizedActionInitialChildDispatcher mixed child) who deviation)
          PUnit.unit who ≤
        G.realizedActionStochasticGame.discountedPayoff β
          (G.realizedActionInitialChildDispatcher mixed child) PUnit.unit who := by
    calc
      _ = expect (Math.PMFProduct.pmfPi (Function.update mixed who first)) (fun joint =>
          (1 - β) * G.eu joint who +
            β * G.realizedActionStochasticGame.discountedPayoff β
              (Function.update (child (G.realizedActionFirstHistory joint)) who
                (G.realizedActionStochasticGame.afterHistoryStrategy deviation
                  (G.realizedActionFirstHistory joint))) PUnit.unit who) := hpay
      _ ≤ expect (Math.PMFProduct.pmfPi (Function.update mixed who first)) (fun joint =>
          (1 - β) * G.eu joint who +
            β * G.realizedActionStochasticGame.discountedPayoff β
              (child (G.realizedActionFirstHistory joint)) PUnit.unit who) := by
        apply expect_mono
        intro joint
        apply add_le_add_right
        apply mul_le_mul_of_nonneg_left _ hβ0
        simpa only [add_zero] using
          hchild (G.realizedActionFirstHistory joint) who
            (G.realizedActionStochasticGame.afterHistoryStrategy deviation
              (G.realizedActionFirstHistory joint))
      _ = (G.realizedActionDiscountedChildGame β child).mixedExtension.eu
          (Function.update mixed who first) who :=
        (G.realizedActionDiscountedChildGame_mixedEU β child
          (Function.update mixed who first) who).symm
      _ ≤ (G.realizedActionDiscountedChildGame β child).mixedExtension.eu mixed who :=
        hinitial who first
      _ = G.realizedActionStochasticGame.discountedPayoff β
          (G.realizedActionInitialChildDispatcher mixed child) PUnit.unit who :=
        (G.realizedAction_discountedPayoff_initialChildDispatcher
          mixed child who hβ0 hβ1).symm
  simpa only [add_zero] using hcap

end GameTheory.KernelGame
