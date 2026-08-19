from pathlib import Path
import re
root=Path(__file__).resolve().parents[1] / 'Literature'
main=(root/'Sorin1986.lean').read_text()

def inner(path):
    s=(root/path).read_text()
    a=s.index('namespace SequenceForm\n')+len('namespace SequenceForm\n')
    b=s.rindex('\nend SequenceForm')
    return s[a:b].strip()+"\n"

compact=inner('Sorin1986CompactScratch.lean')
payoff=inner('Sorin1986CompactPayoffScratch.lean')
game=inner('Sorin1986CompactGameScratch.lean')
eval_=inner('Sorin1986EvaluationScratch.lean')
disc=inner('Sorin1986DiscountedScratch.lean')
# Introduce raw discount evaluator and make typed definitions abbreviations.
disc=disc.replace('''/-- The continuation factor corresponding to the paper's current-stage
weight `λ`. -/
def continuationFactor {G : FiniteStageGame} (lam : G.DiscountRate) : ℝ :=
  1 - lam.1''','''/-- Continuation factor for an arbitrary current-stage weight. -/
def continuationFactorRaw (lam : ℝ) : ℝ := 1 - lam

/-- The continuation factor corresponding to a paper discount rate. -/
abbrev continuationFactor {G : FiniteStageGame} (lam : G.DiscountRate) : ℝ :=
  continuationFactorRaw lam.1''')
disc=disc.replace('''/-- Geometric weights in the paper's convention. -/
def discountWeight {G : FiniteStageGame}
    (lam : G.DiscountRate) (stage : ℕ) : ℝ :=
  lam.1 * continuationFactor lam ^ stage

/-- Discounted payoff of a realization-plan profile. -/
def discountedRealizationPayoff (G : FiniteStageGame)
    (lam : G.DiscountRate) (profile : RealizationProfile G) :
    Payoff G.Player :=
  fun observer => ∑' stage : ℕ,
    discountWeight lam stage * stagePayoff G profile stage observer''','''/-- Geometric weights for an arbitrary current-stage weight. -/
def discountWeightRaw (lam : ℝ) (stage : ℕ) : ℝ :=
  lam * continuationFactorRaw lam ^ stage

/-- Geometric weights in the paper's typed discount domain. -/
abbrev discountWeight {G : FiniteStageGame}
    (lam : G.DiscountRate) (stage : ℕ) : ℝ :=
  discountWeightRaw lam.1 stage

/-- Discounted payoff for an arbitrary real parameter.  Paper-facing theorems
use it only on `0 < λ ≤ 1`; retaining the raw definition is useful for statements
that quantify over a real parameter before imposing those hypotheses. -/
def discountedRealizationPayoffRaw (G : FiniteStageGame)
    (lam : ℝ) (profile : RealizationProfile G) : Payoff G.Player :=
  fun observer => ∑' stage : ℕ,
    discountWeightRaw lam stage * stagePayoff G profile stage observer

/-- Discounted payoff on the paper's typed discount domain. -/
abbrev discountedRealizationPayoff (G : FiniteStageGame)
    (lam : G.DiscountRate) (profile : RealizationProfile G) :
    Payoff G.Player :=
  discountedRealizationPayoffRaw G lam.1 profile''')
disc=disc.replace('unfold discountedRealizationPayoff','unfold discountedRealizationPayoffRaw')
disc=disc.replace('unfold continuationFactor\n','unfold continuationFactorRaw\n')

sequence='''/-! ## Sequence-form repeated strategies

The paper works with mixed contingent plans.  We use their exact realization-plan
normal form: one compact flow polytope for each player, indexed by finite public
histories.  This avoids postulating regular probability measures on an infinite
pure-strategy space and makes the compact reduction computationally explicit. -/

namespace SequenceForm

'''+compact+'\n'+payoff+'\n'+game+'\n'+eval_+'\n'+disc+'''
/-- Nash equilibrium for one realization-plan payoff evaluator. -/
def IsNash {G : FiniteStageGame}
    (payoff : RealizationProfile G → Payoff G.Player)
    (profile : RealizationProfile G) : Prop :=
  ∀ who (deviation : RealizationPlan G who),
    payoff profile who ≥
      payoff (Function.update profile who deviation) who

end SequenceForm
'''

end_rate='''/-- Discount parameters in the paper's domain `0 < λ ≤ 1`. -/
abbrev FiniteStageGame.DiscountRate (G : FiniteStageGame) :=
  {lam : ℝ // 0 < lam ∧ lam ≤ 1}
'''
pos=main.index(end_rate)+len(end_rate)
prefix=main[:pos]
prefix=prefix.replace('''The repeated-game model is not an unconstrained payoff oracle.  A finite stage
game is compiled to the repository's one-state stochastic game with publicly
observed realized action profiles.  Its behavior profiles give a behavioral presentation that is outcome-equivalent
to the paper's mixed strategies under perfect recall and standard
signalling.''','''The repeated-game model is not an unconstrained payoff oracle.  A finite stage
game has the repository's one-state realized-action presentation, while the
paper-facing mixed normal form is implemented below by compact sequence-form
realization plans.  Their flow equations generate the probability of every
finite public history and joint action, so no abstract regular-measure or
perfect-recall transport is assumed.''')

start_model=main.index('/-- Expected one-stage payoff under a mixed profile. -/',pos)
end_model=main.index('/-- A real sequence is bounded. -/',start_model)
model='''/-- A repository behavioral profile, retained for the perfect-public
equilibrium comparison after Lemma 2. -/
abbrev FiniteStageGame.RepositoryBehaviorProfile (G : FiniteStageGame) :=
  G.repeatedGame.BehaviorProfile

/-- One repository behavioral strategy. -/
abbrev FiniteStageGame.RepositoryBehaviorStrategy (G : FiniteStageGame)
    (who : G.Player) :=
  G.repeatedGame.BehaviorStrategy who

/-- The compact mixed repeated-strategy profile used for the paper. -/
abbrev FiniteStageGame.RepeatedProfile (G : FiniteStageGame) :=
  SequenceForm.RealizationProfile G

/-- One player's compact repeated strategy. -/
abbrev FiniteStageGame.RepeatedStrategy (G : FiniteStageGame)
    (who : G.Player) :=
  SequenceForm.RealizationPlan G who

/-- Expected one-stage payoff under a mixed profile. -/
noncomputable def FiniteStageGame.mixedPayoff (G : FiniteStageGame)
    (profile : G.MixedProfile) : Payoff G.Player :=
  G.kernel.mixedExtension.payoffVector profile

/-- Expected average payoff in the `n`-stage sequence-form repetition. -/
noncomputable def FiniteStageGame.finitePayoff (G : FiniteStageGame)
    (n : ℕ) (profile : G.RepeatedProfile) : Payoff G.Player :=
  SequenceForm.finiteRealizationPayoff G n profile

/-- The paper's `λ`-discounted payoff in sequence form. -/
noncomputable def FiniteStageGame.discountedPayoff (G : FiniteStageGame)
    (lam : ℝ) (profile : G.RepeatedProfile) : Payoff G.Player :=
  SequenceForm.discountedRealizationPayoffRaw G lam profile

/-- Repository behavioral discounted payoff.  This separate name prevents the
perfect-public-equilibrium comparison from changing the paper-facing carrier. -/
noncomputable def FiniteStageGame.repositoryDiscountedPayoff
    (G : FiniteStageGame) (lam : ℝ)
    (profile : G.RepositoryBehaviorProfile) : Payoff G.Player :=
  fun who => G.repeatedGame.discountedPayoff (1 - lam) profile PUnit.unit who

/-- Finite payoff with the paper's positive-horizon domain exposed in the type. -/
abbrev FiniteStageGame.finitePayoffOnHorizon (G : FiniteStageGame)
    (n : G.Horizon) : G.RepeatedProfile → Payoff G.Player :=
  G.finitePayoff n.1

/-- Discounted payoff with `0 < λ ≤ 1` exposed in the type. -/
abbrev FiniteStageGame.discountedPayoffOnRate (G : FiniteStageGame)
    (lam : G.DiscountRate) : G.RepeatedProfile → Payoff G.Player :=
  G.discountedPayoff lam.1

/-- Feasible one-stage payoffs, the paper's `D₁`. -/
def FiniteStageGame.oneStageFeasiblePayoffs (G : FiniteStageGame) :
    Set (Payoff G.Player) :=
  Set.range G.mixedPayoff

/-- Nash equilibrium payoffs of the mixed one-stage game, the paper's `E₁`. -/
def FiniteStageGame.oneStageEquilibriumPayoffs (G : FiniteStageGame) :
    Set (Payoff G.Player) :=
  {v | ∃ profile : G.MixedProfile,
      G.kernel.mixedExtension.IsNash profile ∧ G.mixedPayoff profile = v}

/-- Feasible payoffs of the `n`-stage game, the paper's `Dₙ`. -/
def FiniteStageGame.finiteFeasiblePayoffs (G : FiniteStageGame) (n : ℕ) :
    Set (Payoff G.Player) :=
  Set.range (G.finitePayoff n)

/-- Nash equilibrium payoffs of the `n`-stage game, the paper's `Eₙ`. -/
def FiniteStageGame.finiteEquilibriumPayoffs (G : FiniteStageGame) (n : ℕ) :
    Set (Payoff G.Player) :=
  {v | ∃ profile : G.RepeatedProfile,
      SequenceForm.IsNash (G.finitePayoff n) profile ∧
        G.finitePayoff n profile = v}

/-- Feasible payoffs of the `λ`-discounted game, the paper's `D_λ`. -/
def FiniteStageGame.discountedFeasiblePayoffs (G : FiniteStageGame) (lam : ℝ) :
    Set (Payoff G.Player) :=
  Set.range (G.discountedPayoff lam)

/-- Nash equilibrium payoffs of the `λ`-discounted game, the paper's `E_λ`. -/
def FiniteStageGame.discountedEquilibriumPayoffs
    (G : FiniteStageGame) (lam : ℝ) : Set (Payoff G.Player) :=
  {v | ∃ profile : G.RepeatedProfile,
      SequenceForm.IsNash (G.discountedPayoff lam) profile ∧
        G.discountedPayoff lam profile = v}

/-! The paper-facing wrappers below prevent accidental use of horizon zero and
of discounts outside `0 < λ ≤ 1`.  Raw definitions remain for block formulas. -/

abbrev FiniteStageGame.finiteFeasiblePayoffsOnHorizon
    (G : FiniteStageGame) (n : G.Horizon) : Set (Payoff G.Player) :=
  G.finiteFeasiblePayoffs n.1

abbrev FiniteStageGame.finiteEquilibriumPayoffsOnHorizon
    (G : FiniteStageGame) (n : G.Horizon) : Set (Payoff G.Player) :=
  G.finiteEquilibriumPayoffs n.1

abbrev FiniteStageGame.discountedFeasiblePayoffsOnRate
    (G : FiniteStageGame) (lam : G.DiscountRate) : Set (Payoff G.Player) :=
  G.discountedFeasiblePayoffs lam.1

abbrev FiniteStageGame.discountedEquilibriumPayoffsOnRate
    (G : FiniteStageGame) (lam : G.DiscountRate) : Set (Payoff G.Player) :=
  G.discountedEquilibriumPayoffs lam.1

'''

ban_start=end_model
ban_end=main.index('/-- Pure-profile payoff vectors',ban_start)
ban=main[ban_start:ban_end]
ban=ban.replace('G.BehaviorProfile','G.RepeatedProfile').replace('G.BehaviorStrategy','G.RepeatedStrategy')
pure_start=ban_end
compact_start=main.index('/-! The paper first embeds',pure_start)
precompact=main[pure_start:compact_start]
cc_start=compact_start
abstract_start=main.index('/-- A faithful bridge from one repeated-game evaluator',cc_start)
compact_base=main[cc_start:abstract_start]
property3=main.index('/-! The asymptotic feasible-payoff statements',abstract_start)
rest=main[property3:]
rest=rest.replace('''  G.discountedPayoff lam
    (GameTheory.KernelGame.RealizedActionRepeatedAdapter.toBehaviorProfile''','''  G.repositoryDiscountedPayoff lam
    (GameTheory.KernelGame.RealizedActionRepeatedAdapter.toBehaviorProfile''')

bridge='''/-! ## Concrete compact reductions for `Gₙ` and `G_λ` -/

/-- Compact continuous normal form of a positive finite repetition. -/
noncomputable def FiniteStageGame.finiteCompactGame
    (G : FiniteStageGame) (n : G.Horizon) : CompactContinuousGame where
  Player := G.Player
  Strategy := SequenceForm.RealizationPlan G
  mix := fun _ => SequenceForm.RealizationPlan.mix
  mixContinuous := SequenceForm.RealizationPlan.mix_continuous G
  mix_zero := fun _ => SequenceForm.RealizationPlan.mix_zero
  mix_one := fun _ => SequenceForm.RealizationPlan.mix_one
  payoff := G.finitePayoff n.1
  payoffContinuous := SequenceForm.continuous_finiteRealizationPayoff G n.1
  payoffAffine := fun profile who x y t observer ht0 ht1 =>
    SequenceForm.finiteRealizationPayoff_update_mix
      G n.1 profile who x y t observer ht0 ht1

/-- Compact continuous normal form of a discounted repetition. -/
noncomputable def FiniteStageGame.discountedCompactGame
    (G : FiniteStageGame) (lam : G.DiscountRate) : CompactContinuousGame where
  Player := G.Player
  Strategy := SequenceForm.RealizationPlan G
  mix := fun _ => SequenceForm.RealizationPlan.mix
  mixContinuous := SequenceForm.RealizationPlan.mix_continuous G
  mix_zero := fun _ => SequenceForm.RealizationPlan.mix_zero
  mix_one := fun _ => SequenceForm.RealizationPlan.mix_one
  payoff := G.discountedPayoff lam.1
  payoffContinuous :=
    SequenceForm.continuous_discountedRealizationPayoff G lam
  payoffAffine := fun profile who x y t observer ht0 ht1 =>
    SequenceForm.discountedRealizationPayoff_update_mix
      G lam profile who x y t observer ht0 ht1

@[simp] theorem FiniteStageGame.finiteCompactGame_feasiblePayoffs
    (G : FiniteStageGame) (n : G.Horizon) :
    (G.finiteCompactGame n).feasiblePayoffs =
      G.finiteFeasiblePayoffsOnHorizon n := rfl

@[simp] theorem FiniteStageGame.finiteCompactGame_equilibriumPayoffs
    (G : FiniteStageGame) (n : G.Horizon) :
    (G.finiteCompactGame n).equilibriumPayoffs =
      G.finiteEquilibriumPayoffsOnHorizon n := rfl

@[simp] theorem FiniteStageGame.discountedCompactGame_feasiblePayoffs
    (G : FiniteStageGame) (lam : G.DiscountRate) :
    (G.discountedCompactGame lam).feasiblePayoffs =
      G.discountedFeasiblePayoffsOnRate lam := rfl

@[simp] theorem FiniteStageGame.discountedCompactGame_equilibriumPayoffs
    (G : FiniteStageGame) (lam : G.DiscountRate) :
    (G.discountedCompactGame lam).equilibriumPayoffs =
      G.discountedEquilibriumPayoffsOnRate lam := rfl

/-- Property (1), directly from compactness, convex mixing, and continuity. -/
theorem paper_property_1 (G : CompactContinuousGame) :
    G.feasiblePayoffs.Nonempty ∧
      PathConnectedSet G.feasiblePayoffs ∧ IsCompact G.feasiblePayoffs := by
  have hpayoff : Continuous G.payoff := continuous_pi G.payoffContinuous
  constructor
  · exact Set.range_nonempty G.payoff
  constructor
  · constructor
    · exact Set.range_nonempty G.payoff
    · rintro _ ⟨profileX, rfl⟩ _ ⟨profileY, rfl⟩
      let path : ℝ → Payoff G.Player := fun t =>
        G.payoff (fun i => G.mix i t (profileY i) (profileX i))
      have hprofile : Continuous fun t : ℝ =>
          (fun i => G.mix i t (profileY i) (profileX i)) := by
        apply continuous_pi
        intro i
        exact (G.mixContinuous i).comp
          (continuous_id.prodMk (continuous_const.prodMk continuous_const))
      refine ⟨path, hpayoff.comp hprofile, ?_, ?_, ?_⟩
      · change G.payoff (fun i => G.mix i 0 (profileY i) (profileX i)) =
          G.payoff profileX
        congr 1
        funext i
        exact G.mix_zero i (profileY i) (profileX i)
      · change G.payoff (fun i => G.mix i 1 (profileY i) (profileX i)) =
          G.payoff profileY
        congr 1
        funext i
        exact G.mix_one i (profileY i) (profileX i)
      · intro t _
        exact ⟨fun i => G.mix i t (profileY i) (profileX i), rfl⟩
  · simpa [CompactContinuousGame.feasiblePayoffs] using
      isCompact_univ.image_of_continuousOn hpayoff.continuousOn

/-! Property (2) is Glicksberg--Fan Nash existence plus closedness of the
equilibrium relation.  The compact sequence-form games above satisfy its
hypotheses, but the required infinite-dimensional fixed-point theorem is not
yet in the imported library. -/
theorem paper_property_2 (G : CompactContinuousGame) :
    G.equilibriumPayoffs.Nonempty ∧ IsCompact G.equilibriumPayoffs := by
  sorry

theorem paper_property_1_finite (G : FiniteStageGame) (n : G.Horizon) :
    (G.finiteFeasiblePayoffsOnHorizon n).Nonempty ∧
      PathConnectedSet (G.finiteFeasiblePayoffsOnHorizon n) ∧
        IsCompact (G.finiteFeasiblePayoffsOnHorizon n) := by
  simpa using paper_property_1 (G.finiteCompactGame n)

theorem paper_property_1_discounted
    (G : FiniteStageGame) (lam : G.DiscountRate) :
    (G.discountedFeasiblePayoffsOnRate lam).Nonempty ∧
      PathConnectedSet (G.discountedFeasiblePayoffsOnRate lam) ∧
        IsCompact (G.discountedFeasiblePayoffsOnRate lam) := by
  simpa using paper_property_1 (G.discountedCompactGame lam)

theorem paper_property_2_finite (G : FiniteStageGame) (n : G.Horizon) :
    (G.finiteEquilibriumPayoffsOnHorizon n).Nonempty ∧
      IsCompact (G.finiteEquilibriumPayoffsOnHorizon n) := by
  simpa using paper_property_2 (G.finiteCompactGame n)

theorem paper_property_2_discounted
    (G : FiniteStageGame) (lam : G.DiscountRate) :
    (G.discountedEquilibriumPayoffsOnRate lam).Nonempty ∧
      IsCompact (G.discountedEquilibriumPayoffsOnRate lam) := by
  simpa using paper_property_2 (G.discountedCompactGame lam)

'''

candidate=prefix+'\n'+sequence+'\n'+model+ban+precompact+compact_base+bridge+rest
candidate=re.sub(r'''/-- A behavioral profile in the repeated game\. -/
abbrev FiniteStageGame\.BehaviorProfile.*?G\.repeatedGame\.BehaviorProfile

/-- A behavioral strategy of one player in the repeated game\. -/
abbrev FiniteStageGame\.BehaviorStrategy.*?G\.repeatedGame\.BehaviorStrategy who

''','',candidate,flags=re.S)
candidate=candidate.replace('behavioral presentation that is outcome-equivalent','behavioral presentation outcome-equivalent')
(root/'Sorin1986IntegratedScratch.lean').write_text(candidate)
print('lines',candidate.count('\n')+1,'sorries',candidate.count('sorry'))
print('old presentation?', 'CompactRepeatedPresentation' in candidate)
print('BehaviorProfile refs',candidate.count('BehaviorProfile'))
