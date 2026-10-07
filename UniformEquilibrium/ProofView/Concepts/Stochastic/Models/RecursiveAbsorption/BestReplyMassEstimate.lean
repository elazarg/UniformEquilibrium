import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.RecursiveAbsorption.ProperPairApproximation

/-!
# Arbitrary-sequence best-reply mass estimates

Flesch, Thuijsman and Vrieze (1996), Lemma 3.2, concerns arbitrary stationary
sequences, not only proper pairs. Its fixed supported best-reply anchor has
positive absorption against the limiting opponent. The raw probability ratio
of every currently absorbing non-best reply tends to zero. Since those sets
vary with the sequence, the premise below uses the ratio on precisely those
memberships, and zero otherwise. It does not force a formerly good action's
unrestricted probability ratio to vanish.

Best replies here cap every behavioral deviation under the actual infinite-play
law. Their equivalence with pure stationary maximality delegates the checked
unrestricted best-response bound. The finite common ratio bound and actual
mixed absorption mass are derived internally. The payoff estimate reuses the
absorption-weighted repair estimate, including signed and zero best values.
No properness, own-strategy convergence or supplied payoff floor is assumed.
-/

noncomputable section

open _root_.Math.Probability _root_.Math.ProbabilityMassFunction Filter
open scoped BigOperators Topology

namespace GameTheory.RecursiveAbsorption

variable {I J : Type} [Fintype I] [Fintype J]

/-- The pure row strategy caps every behavioral reply against the fixed opponent. -/
def IsRowBestReply (D : Data I J) (y : PMF J) (anchor : I) : Prop :=
  ∀ deviation : (game D).BehaviorStrategy false,
    liminfPayoff D none
        (Function.update (stationaryProfile D (PMF.pure anchor) y) false deviation) false ≤
      liminfPayoff D none (stationaryProfile D (PMF.pure anchor) y) false

/-- The analogous actual all-behavior best-reply predicate for the column player. -/
def IsColumnBestReply (D : Data I J) (x : PMF I) (anchor : J) : Prop :=
  ∀ deviation : (game D).BehaviorStrategy true,
    liminfPayoff D none
        (Function.update (stationaryProfile D x (PMF.pure anchor)) true deviation) true ≤
      liminfPayoff D none (stationaryProfile D x (PMF.pure anchor)) true

theorem isRowBestReply_iff_pure_max (D : Data I J) (y : PMF J) (anchor : I) :
    IsRowBestReply D y anchor ↔ ∀ i,
      stationaryPayoff D (PMF.pure i) y false ≤
        stationaryPayoff D (PMF.pure anchor) y false := by
  constructor
  · intro hbest i
    have hprofile : Function.update (stationaryProfile D (PMF.pure anchor) y)
        false (fun _ _ => PMF.pure i) = stationaryProfile D (PMF.pure i) y := by
      funext who time history
      cases who <;> simp [stationaryProfile, StochasticGame.stationaryBehaviorProfile,
        mixedAction] <;> rfl
    have h := hbest (fun _ _ => PMF.pure i)
    rw [hprofile] at h
    simpa only [liminfPayoff_stationary_none] using h
  · intro hmax deviation
    calc
      _ ≤ stationaryPayoff D (PMF.pure anchor) y false :=
        behavioral_rowPayoff_le_of_pure_cap D (PMF.pure anchor) y _ hmax deviation
      _ = _ := (liminfPayoff_stationary_none D (PMF.pure anchor) y false).symm

theorem isColumnBestReply_iff_pure_max (D : Data I J) (x : PMF I) (anchor : J) :
    IsColumnBestReply D x anchor ↔ ∀ j,
      stationaryPayoff D x (PMF.pure j) true ≤
        stationaryPayoff D x (PMF.pure anchor) true := by
  constructor
  · intro hbest j
    have hprofile : Function.update (stationaryProfile D x (PMF.pure anchor))
        true (fun _ _ => PMF.pure j) = stationaryProfile D x (PMF.pure j) := by
      funext who time history
      cases who <;> simp [stationaryProfile, StochasticGame.stationaryBehaviorProfile,
        mixedAction] <;> rfl
    have h := hbest (fun _ _ => PMF.pure j)
    rw [hprofile] at h
    simpa only [liminfPayoff_stationary_none] using h
  · intro hmax deviation
    calc
      _ ≤ stationaryPayoff D x (PMF.pure anchor) true :=
        behavioral_columnPayoff_le_of_pure_cap D x (PMF.pure anchor) _ hmax deviation
      _ = _ := (liminfPayoff_stationary_none D x (PMF.pure anchor) true).symm

/-- The raw ratio only on the paper's varying absorbing non-best-reply set. -/
def rowBadReplyProbabilityRatio (D : Data I J) (x : PMF I) (y : PMF J)
    (anchor i : I) : ℝ := by
  classical
  exact if 0 < absorptionMass D (PMF.pure i) y ∧ ¬ IsRowBestReply D y i then
    (x i).toReal / (x anchor).toReal else 0

/-- The corresponding conditional raw probability ratio for columns. -/
def columnBadReplyProbabilityRatio (D : Data I J) (x : PMF I) (y : PMF J)
    (anchor j : J) : ℝ := by
  classical
  exact if 0 < absorptionMass D x (PMF.pure j) ∧ ¬ IsColumnBestReply D x j then
    (y j).toReal / (y anchor).toReal else 0

/-- Lemma 3.2's actual row-payoff floor for arbitrary stationary sequences. -/
theorem eventually_rowPayoff_ge_bestReply_of_bad_ratio_tendsto (D : Data I J)
    (xs : ℕ → PMF I) (ys : ℕ → PMF J) (y : PMF J) (anchor : I)
    (hy : Tendsto (fun n => toVector (ys n)) atTop (𝓝 (toVector y)))
    (hsupported : ∀ n, 0 < (xs n anchor).toReal)
    (hbest : ∀ n, IsRowBestReply D (ys n) anchor)
    (hhazard : 0 < absorptionMass D (PMF.pure anchor) y)
    (hbad : ∀ i, Tendsto
      (fun n => rowBadReplyProbabilityRatio D (xs n) (ys n) anchor i) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      liminfPayoff D none (stationaryProfile D (xs n) (ys n)) false ≥
        liminfPayoff D none (stationaryProfile D (PMF.pure anchor) (ys n)) false - ε := by
  classical
  let δ : ℕ → ℝ := fun n => ∑ i, rowBadReplyProbabilityRatio D (xs n) (ys n) anchor i
  have hratio_nonneg : ∀ n i,
      0 ≤ rowBadReplyProbabilityRatio D (xs n) (ys n) anchor i := by
    intro n i
    unfold rowBadReplyProbabilityRatio
    split_ifs
    · exact div_nonneg ENNReal.toReal_nonneg (hsupported n).le
    · exact le_rfl
  have hδnonneg : ∀ n, 0 ≤ δ n := fun n => Finset.sum_nonneg fun i _ => hratio_nonneg n i
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => hbad i)
  have hmass := tendsto_pureRow_absorptionMass D ys y hy anchor
  obtain ⟨bound, hbound⟩ := exists_abs_bound_of_finite
    (fun pair : I × J => D.reward pair.1 pair.2 false)
  have hrate : Tendsto (fun n => (2 * bound) * (Fintype.card I : ℝ) *
      (δ n / absorptionMass D (PMF.pure anchor) (ys n))) atTop (𝓝 0) := by
    simpa only [Pi.div_apply, zero_div, mul_zero] using
      (hδ.div hmass hhazard.ne').const_mul ((2 * bound) * (Fintype.card I : ℝ))
  filter_upwards [hmass.eventually_const_lt hhazard, hrate.eventually_lt_const hε]
    with n hnhazard hnrate
  have hpositive : 0 < absorptionMass D (xs n) (ys n) := by
    have hweight : 0 < rowAbsorptionWeight D (xs n) (ys n) anchor :=
      mul_pos (hsupported n) hnhazard
    exact hweight.trans_le ((Finset.single_le_sum
      (fun i _ => rowAbsorptionWeight_nonneg D (xs n) (ys n) i)
      (Finset.mem_univ anchor)).trans_eq (sum_rowAbsorptionWeight D (xs n) (ys n)))
  have hprob : ∀ i, 0 < absorptionMass D (PMF.pure i) (ys n) →
      stationaryPayoff D (PMF.pure i) (ys n) false ≠
        stationaryPayoff D (PMF.pure anchor) (ys n) false →
      (xs n i).toReal ≤ δ n * (xs n anchor).toReal := by
    intro i hihazard hne
    have hinot : ¬ IsRowBestReply D (ys n) i := by
      intro hi
      exact hne (le_antisymm
        ((isRowBestReply_iff_pure_max D (ys n) anchor).mp (hbest n) i)
        ((isRowBestReply_iff_pure_max D (ys n) i).mp hi anchor))
    have hsingle : rowBadReplyProbabilityRatio D (xs n) (ys n) anchor i ≤ δ n :=
      Finset.single_le_sum (fun i _ => hratio_nonneg n i) (Finset.mem_univ i)
    rw [rowBadReplyProbabilityRatio, ite_eq_left ⟨hihazard, hinot⟩] at hsingle
    exact (div_le_iff₀ (hsupported n)).mp hsingle
  have hgap := abs_rowPayoff_gap_le_of_bad_probabilities D (xs n) (ys n) (δ n) anchor
    bound (hδnonneg n) hpositive hnhazard hprob (fun i j => hbound (i, j))
  have hlower := (abs_le.mp hgap).1
  rw [liminfPayoff_stationary_none, liminfPayoff_stationary_none]
  linarith

end GameTheory.RecursiveAbsorption
