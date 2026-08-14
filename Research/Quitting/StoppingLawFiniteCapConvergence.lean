/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawFiniteSplice

/-!
# Convergence of stochastic-button finite caps

The finite-splice estimates isolate the dimensionless error

`late finite mass + Never mass * maximal pair-deleted survival`.

This experiment turns that bound into an actual finite-iteration reduction.
Late finite stopping mass always tends to zero.  Hence the cap error tends to
zero if either the stopping law has no `Never` atom or the maximal
pair-deleted survival clock tends to zero.  Under either condition, one finite
cap simultaneously approximates every player's prescribed payoff, full
behavioral best-response envelope, and terminal semantic debt.

At profile level, the relevant geometry has deletion rank two.  Two distinct
zero-Never players make every third coordinate cappable; after those two are
capped into finite sure-Quit sentinels, a finite induction caps the entire
profile even when every remaining coordinate has positive Never mass.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

/-! ## Two sharp sufficient conditions -/

/-- Without a `Never` atom, the finite-splice error always vanishes. -/
theorem tendsto_quittingFiniteSpliceError_zero_of_neverMass_zero
    (roots : ℕ → ι → PMF Bool) (mover : ι) (hazard : ℕ → PMF Bool)
    (hnever : quittingHazardNeverMass hazard = 0) :
    Tendsto (fun cutoff =>
      quittingFiniteSpliceError roots mover hazard cutoff)
      atTop (nhds 0) := by
  simpa [quittingFiniteSpliceError, hnever] using
    tendsto_quittingHazardLateFiniteMass_zero hazard

/-- A possibly positive `Never` atom is harmless when the maximal
pair-deleted survival clock vanishes. -/
theorem tendsto_quittingFiniteSpliceError_zero_of_pairDeleted
    (roots : ℕ → ι → PMF Bool) (mover : ι) (hazard : ℕ → PMF Bool)
    (hclock : Tendsto (fun cutoff =>
      quittingMaxPairDeletedSurvivalWeight roots mover 0 cutoff)
      atTop (nhds 0)) :
    Tendsto (fun cutoff =>
      quittingFiniteSpliceError roots mover hazard cutoff)
      atTop (nhds 0) := by
  have hlate := tendsto_quittingHazardLateFiniteMass_zero hazard
  have hconst : Tendsto
      (fun _ : ℕ => quittingHazardNeverMass hazard) atTop
      (nhds (quittingHazardNeverMass hazard)) := tendsto_const_nhds
  have hcemetery : Tendsto (fun cutoff =>
      quittingHazardNeverMass hazard *
        quittingMaxPairDeletedSurvivalWeight roots mover 0 cutoff)
      atTop (nhds 0) := by
    simpa using hconst.mul hclock
  simpa [quittingFiniteSpliceError] using hlate.add hcemetery

/-! ## Finite sentinels kill pair-deleted clocks -/

omit [Nontrivial ι] in
/-- A sure quitter distinct from both deleted coordinates kills the
corresponding pair-deleted survival clock at every horizon containing that
row. -/
theorem quittingPairDeletedSurvivalWeight_eq_zero_of_sure_other
    (roots : ℕ → ι → PMF Bool) (mover observer sentinel : ι)
    (hsentinelMover : sentinel ≠ mover)
    (hsentinelObserver : sentinel ≠ observer)
    (sureTime fuel : ℕ) (hsureTime : sureTime < fuel)
    (hsure : roots sureTime sentinel = PMF.pure true) :
    quittingPairDeletedSurvivalWeight roots mover observer 0 fuel = 0 := by
  unfold quittingPairDeletedSurvivalWeight quittingOpponentSurvivalWeight
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hsureTime)
  simp only [Nat.zero_add]
  unfold quittingFixedOpponentsContinueMass
  let forcedRoot := Function.update
    (quittingRootSequenceUpdate roots observer quittingAlwaysContinueHazard
      sureTime) mover (PMF.pure false)
  have hsureRoot : QuittingRootHasSureQuitter forcedRoot := by
    refine ⟨sentinel, ?_⟩
    dsimp [forcedRoot]
    unfold quittingRootSequenceUpdate quittingAlwaysContinueHazard
    rw [Function.update_of_ne hsentinelMover,
      Function.update_of_ne hsentinelObserver, hsure]
  have hmass :=
    (quittingRootHasSureQuitter_iff_allContinue_mass_zero forcedRoot).mp
      hsureRoot
  unfold quittingStationaryContinueMass
  change ((pmfPi forcedRoot (fun _ => false)).toReal) = 0
  rw [hmass]
  simp

omit [Nontrivial ι] in
/-- The complementary sharpness fact: if everyone outside the deleted
mover/observer pair continues surely, then the pair-deleted clock is exactly
one at every finite horizon.  Actions of the two deleted players themselves
cannot change this clock. -/
theorem quittingPairDeletedSurvivalWeight_eq_one_of_others_continue
    (roots : ℕ → ι → PMF Bool) (mover observer : ι)
    (start fuel : ℕ)
    (hcontinue : ∀ time player, player ≠ mover → player ≠ observer →
      roots time player = PMF.pure false) :
    quittingPairDeletedSurvivalWeight roots mover observer start fuel = 1 := by
  unfold quittingPairDeletedSurvivalWeight quittingOpponentSurvivalWeight
  apply Finset.prod_eq_one
  intro offset _
  unfold quittingFixedOpponentsContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Finset.prod_eq_one
  intro player _
  by_cases hplayerMover : player = mover
  · subst player
    simp
  by_cases hplayerObserver : player = observer
  · subst player
    simp [quittingRootSequenceUpdate, quittingAlwaysContinueHazard,
      hplayerMover]
  · simp [quittingRootSequenceUpdate, quittingAlwaysContinueHazard,
      hplayerMover, hplayerObserver,
      hcontinue (start + offset) player hplayerMover hplayerObserver]

/-- One sentinel is genuinely insufficient for the uniform-over-observers
clock estimate.  If every player outside the mover/sentinel pair continues
surely, choosing the sentinel itself as observer deletes the only possible
absorber, and the maximum pair-deleted clock remains exactly one. -/
theorem quittingMaxPairDeletedSurvivalWeight_eq_one_of_single_sentinel
    (roots : ℕ → ι → PMF Bool) (mover sentinel : ι)
    (hmoverSentinel : mover ≠ sentinel) (start fuel : ℕ)
    (hcontinue : ∀ time player, player ≠ mover → player ≠ sentinel →
      roots time player = PMF.pure false) :
    quittingMaxPairDeletedSurvivalWeight roots mover start fuel = 1 := by
  apply le_antisymm
  · exact quittingMaxPairDeletedSurvivalWeight_le_one
      roots mover start fuel
  · rw [← quittingPairDeletedSurvivalWeight_eq_one_of_others_continue
      roots mover sentinel start fuel hcontinue]
    exact quittingPairDeletedSurvivalWeight_le_max
      roots mover sentinel hmoverSentinel start fuel

omit [Nontrivial ι] in
/-- Any player which survives both deletions bounds the pair-deleted clock by
its own survival curve.  This is the quantitative, nonsure version of the
finite-sentinel zero lemma. -/
theorem quittingPairDeletedSurvivalWeight_le_hazardSurvival_of_other
    (roots : ℕ → ι → PMF Bool) (mover observer sentinel : ι)
    (hsentinelMover : sentinel ≠ mover)
    (hsentinelObserver : sentinel ≠ observer) (fuel : ℕ) :
    quittingPairDeletedSurvivalWeight roots mover observer 0 fuel ≤
      quittingHazardSurvival
        (quittingRootSequenceOwnHazard roots sentinel) fuel := by
  unfold quittingPairDeletedSurvivalWeight
  have h :=
    quittingOpponentSurvivalWeight_le_quittingHazardSurvival_ownHazard
      (quittingRootSequenceUpdate roots observer quittingAlwaysContinueHazard)
      hsentinelMover fuel
  have hhazard : quittingRootSequenceOwnHazard
      (quittingRootSequenceUpdate roots observer quittingAlwaysContinueHazard)
        sentinel = quittingRootSequenceOwnHazard roots sentinel := by
    funext time
    unfold quittingRootSequenceOwnHazard quittingRootSequenceUpdate
    exact Function.update_of_ne hsentinelObserver _ _
  rwa [hhazard] at h

omit [Nontrivial ι] in
/-- Exact product geometry of the deleted clock: after forcing the mover and
observer to Continue, joint survival is the product of the individual
survival curves of that twice-deleted root sequence. -/
theorem quittingPairDeletedSurvivalWeight_eq_prod_hazardSurvival
    (roots : ℕ → ι → PMF Bool) (mover observer : ι) (fuel : ℕ) :
    quittingPairDeletedSurvivalWeight roots mover observer 0 fuel =
      ∏ player, quittingHazardSurvival
        (quittingRootSequenceOwnHazard
          (quittingRootSequenceUpdate
            (quittingRootSequenceUpdate roots observer
              quittingAlwaysContinueHazard)
            mover quittingAlwaysContinueHazard)
          player) fuel := by
  unfold quittingPairDeletedSurvivalWeight
    quittingOpponentSurvivalWeight quittingFixedOpponentsContinueMass
  simp only [Nat.zero_add,
    quittingStationaryContinueMass_eq_prod_continueProbability,
    quittingHazardSurvival_eq_prod, quittingRootSequenceOwnHazard,
    quittingRootSequenceUpdate, quittingAlwaysContinueHazard]
  rw [Finset.prod_comm]

omit [Nontrivial ι] in
/-- Passing the finite product identity to the limit identifies terminal
pair-deleted survival with the product of the individual cemetery masses in
the twice-deleted root sequence. -/
theorem quittingPairDeletedSurvivalLimit_eq_prod_neverMass
    (roots : ℕ → ι → PMF Bool) (mover observer : ι) :
    quittingPairDeletedSurvivalLimit roots mover observer 0 =
      ∏ player, quittingHazardNeverMass
        (quittingRootSequenceOwnHazard
          (quittingRootSequenceUpdate
            (quittingRootSequenceUpdate roots observer
              quittingAlwaysContinueHazard)
            mover quittingAlwaysContinueHazard)
          player) := by
  let deletedRoots :=
    quittingRootSequenceUpdate
      (quittingRootSequenceUpdate roots observer quittingAlwaysContinueHazard)
      mover quittingAlwaysContinueHazard
  have hproduct : Tendsto (fun fuel =>
      ∏ player, quittingHazardSurvival
        (quittingRootSequenceOwnHazard deletedRoots player) fuel)
      atTop (nhds (∏ player, quittingHazardNeverMass
        (quittingRootSequenceOwnHazard deletedRoots player))) := by
    apply tendsto_finsetProd Finset.univ
    intro player _
    exact tendsto_quittingHazardSurvival_neverMass
      (quittingRootSequenceOwnHazard deletedRoots player)
  have hweight : Tendsto (fun fuel =>
      quittingPairDeletedSurvivalWeight roots mover observer 0 fuel)
      atTop (nhds (∏ player, quittingHazardNeverMass
        (quittingRootSequenceOwnHazard deletedRoots player))) := by
    simpa [deletedRoots,
      quittingPairDeletedSurvivalWeight_eq_prod_hazardSurvival] using hproduct
  exact tendsto_nhds_unique
    (tendsto_quittingPairDeletedSurvivalLimit roots mover observer 0)
    hweight

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
@[simp] theorem quittingHazardNeverMass_alwaysContinue :
    quittingHazardNeverMass quittingAlwaysContinueHazard = 1 := by
  have hconstant : ∀ fuel,
      quittingHazardSurvival quittingAlwaysContinueHazard fuel = 1 := by
    intro fuel
    simp [quittingHazardSurvival_eq_prod, quittingAlwaysContinueHazard]
  have htends : Tendsto
      (quittingHazardSurvival quittingAlwaysContinueHazard)
      atTop (nhds 1) := by
    convert (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)) using 1
    funext fuel
    exact hconstant fuel
  exact tendsto_nhds_unique
    (tendsto_quittingHazardSurvival_neverMass quittingAlwaysContinueHazard)
    htends

omit [Nontrivial ι] in
/-- Exact zero-pattern classification for one deleted clock.  Its terminal
survival is zero exactly when some player outside the deleted mover/observer
pair has zero cemetery mass. -/
theorem quittingPairDeletedSurvivalLimit_eq_zero_iff
    (roots : ℕ → ι → PMF Bool) (mover observer : ι)
    (hmoverObserver : mover ≠ observer) :
    quittingPairDeletedSurvivalLimit roots mover observer 0 = 0 ↔
      ∃ sentinel, sentinel ≠ mover ∧ sentinel ≠ observer ∧
        quittingHazardNeverMass
          (quittingRootSequenceOwnHazard roots sentinel) = 0 := by
  let deletedRoots :=
    quittingRootSequenceUpdate
      (quittingRootSequenceUpdate roots observer quittingAlwaysContinueHazard)
      mover quittingAlwaysContinueHazard
  have horiginal : ∀ player, player ≠ mover → player ≠ observer →
      quittingRootSequenceOwnHazard deletedRoots player =
        quittingRootSequenceOwnHazard roots player := by
    intro player hplayerMover hplayerObserver
    funext time
    simp [deletedRoots, quittingRootSequenceOwnHazard,
      quittingRootSequenceUpdate, Function.update_of_ne hplayerMover,
      Function.update_of_ne hplayerObserver]
  have hmoverHazard : quittingRootSequenceOwnHazard deletedRoots mover =
      quittingAlwaysContinueHazard := by
    funext time
    simp [deletedRoots, quittingRootSequenceOwnHazard,
      quittingRootSequenceUpdate]
  have hobserverHazard : quittingRootSequenceOwnHazard deletedRoots observer =
      quittingAlwaysContinueHazard := by
    funext time
    simp [deletedRoots, quittingRootSequenceOwnHazard,
      quittingRootSequenceUpdate, Function.update_of_ne hmoverObserver.symm]
  rw [quittingPairDeletedSurvivalLimit_eq_prod_neverMass]
  change (∏ player ∈ Finset.univ,
    quittingHazardNeverMass
      (quittingRootSequenceOwnHazard deletedRoots player)) = 0 ↔ _
  rw [Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨sentinel, hsentinel⟩
    have hsentinelMover : sentinel ≠ mover := by
      intro heq
      subst sentinel
      rw [hmoverHazard, quittingHazardNeverMass_alwaysContinue] at hsentinel
      norm_num at hsentinel
    have hsentinelObserver : sentinel ≠ observer := by
      intro heq
      subst sentinel
      rw [hobserverHazard, quittingHazardNeverMass_alwaysContinue] at hsentinel
      norm_num at hsentinel
    refine ⟨sentinel, hsentinelMover, hsentinelObserver, ?_⟩
    rwa [horiginal sentinel hsentinelMover hsentinelObserver] at hsentinel
  · rintro ⟨sentinel, hsentinelMover, hsentinelObserver, hsentinel⟩
    refine ⟨sentinel, ?_⟩
    rwa [horiginal sentinel hsentinelMover hsentinelObserver]

omit [Nontrivial ι] in
theorem quittingPairDeletedSurvivalLimit_nonneg
    (roots : ℕ → ι → PMF Bool) (mover observer : ι) :
    0 ≤ quittingPairDeletedSurvivalLimit roots mover observer 0 := by
  unfold quittingPairDeletedSurvivalLimit
  exact quittingOpponentSurvivalLimit_nonneg _ _ _

/-- A specified observer's terminal deleted clock lies below the maximum over
all observers distinct from the mover. -/
theorem quittingPairDeletedSurvivalLimit_le_max
    (roots : ℕ → ι → PMF Bool) (mover observer : ι)
    (hmoverObserver : mover ≠ observer) :
    quittingPairDeletedSurvivalLimit roots mover observer 0 ≤
      quittingMaxPairDeletedSurvivalLimit roots mover 0 := by
  unfold quittingMaxPairDeletedSurvivalLimit
  exact Finset.le_sup'
    (fun who => quittingPairDeletedSurvivalLimit roots mover who 0)
    (Finset.mem_erase.mpr
      ⟨hmoverObserver.symm, Finset.mem_univ observer⟩)

/-- **Exact finite zero-pattern classification.**  A mover's maximal terminal
pair-deleted clock vanishes exactly when at least two distinct *other*
players have zero Never mass.  Thus the useful occupation geometry is a
finite support pattern, and its bootstrap threshold really is two. -/
theorem quittingMaxPairDeletedSurvivalLimit_eq_zero_iff_two_zeroNever
    (roots : ℕ → ι → PMF Bool) (mover : ι) :
    quittingMaxPairDeletedSurvivalLimit roots mover 0 = 0 ↔
      ∃ first second,
        first ≠ second ∧ first ≠ mover ∧ second ≠ mover ∧
        quittingHazardNeverMass
            (quittingRootSequenceOwnHazard roots first) = 0 ∧
          quittingHazardNeverMass
            (quittingRootSequenceOwnHazard roots second) = 0 := by
  constructor
  · intro hmax
    obtain ⟨observer, hobserverMover⟩ : ∃ observer : ι,
        observer ≠ mover := exists_ne mover
    have hobserverClock :
        quittingPairDeletedSurvivalLimit roots mover observer 0 = 0 := by
      apply le_antisymm
      · calc
          quittingPairDeletedSurvivalLimit roots mover observer 0 ≤
              quittingMaxPairDeletedSurvivalLimit roots mover 0 :=
            quittingPairDeletedSurvivalLimit_le_max
              roots mover observer hobserverMover.symm
          _ = 0 := hmax
      · exact quittingPairDeletedSurvivalLimit_nonneg roots mover observer
    obtain ⟨first, hfirstMover, _hfirstObserver, hfirstNever⟩ :=
      (quittingPairDeletedSurvivalLimit_eq_zero_iff
        roots mover observer hobserverMover.symm).mp hobserverClock
    have hfirstClock :
        quittingPairDeletedSurvivalLimit roots mover first 0 = 0 := by
      apply le_antisymm
      · calc
          quittingPairDeletedSurvivalLimit roots mover first 0 ≤
              quittingMaxPairDeletedSurvivalLimit roots mover 0 :=
            quittingPairDeletedSurvivalLimit_le_max
              roots mover first hfirstMover.symm
          _ = 0 := hmax
      · exact quittingPairDeletedSurvivalLimit_nonneg roots mover first
    obtain ⟨second, hsecondMover, hsecondFirst, hsecondNever⟩ :=
      (quittingPairDeletedSurvivalLimit_eq_zero_iff
        roots mover first hfirstMover.symm).mp hfirstClock
    exact ⟨first, second, hsecondFirst.symm, hfirstMover, hsecondMover,
      hfirstNever, hsecondNever⟩
  · rintro ⟨first, second, hfirstSecond, hfirstMover, hsecondMover,
      hfirstNever, hsecondNever⟩
    apply le_antisymm
    · unfold quittingMaxPairDeletedSurvivalLimit
      apply Finset.sup'_le
      intro observer hobserver
      have hobserverMover : observer ≠ mover :=
        (Finset.mem_erase.mp hobserver).1
      by_cases hobserverFirst : observer = first
      · apply le_of_eq
        apply (quittingPairDeletedSurvivalLimit_eq_zero_iff
          roots mover observer hobserverMover.symm).mpr
        refine ⟨second, hsecondMover, ?_, hsecondNever⟩
        exact fun h => hfirstSecond (hobserverFirst.symm.trans h.symm)
      · apply le_of_eq
        apply (quittingPairDeletedSurvivalLimit_eq_zero_iff
          roots mover observer hobserverMover.symm).mpr
        exact ⟨first, hfirstMover, (fun h => hobserverFirst h.symm),
          hfirstNever⟩
    · exact quittingMaxPairDeletedSurvivalLimit_nonneg roots mover 0

/-- Two distinct zero-Never opponents already kill a mover's maximal
pair-deleted clock asymptotically; they need not first be converted to literal
sure-Quit rows. -/
theorem tendsto_quittingMaxPairDeletedSurvivalWeight_zero_of_two_zeroNever
    (roots : ℕ → ι → PMF Bool) (mover first second : ι)
    (hfirstSecond : first ≠ second)
    (hfirstMover : first ≠ mover) (hsecondMover : second ≠ mover)
    (hneverFirst : quittingHazardNeverMass
      (quittingRootSequenceOwnHazard roots first) = 0)
    (hneverSecond : quittingHazardNeverMass
      (quittingRootSequenceOwnHazard roots second) = 0) :
    Tendsto (fun fuel =>
      quittingMaxPairDeletedSurvivalWeight roots mover 0 fuel)
      atTop (nhds 0) := by
  let firstSurvival := fun fuel => quittingHazardSurvival
    (quittingRootSequenceOwnHazard roots first) fuel
  let secondSurvival := fun fuel => quittingHazardSurvival
    (quittingRootSequenceOwnHazard roots second) fuel
  have hfirst : Tendsto firstSurvival atTop (nhds 0) := by
    simpa [firstSurvival, hneverFirst] using
      tendsto_quittingHazardSurvival_neverMass
        (quittingRootSequenceOwnHazard roots first)
  have hsecond : Tendsto secondSurvival atTop (nhds 0) := by
    simpa [secondSurvival, hneverSecond] using
      tendsto_quittingHazardSurvival_neverMass
        (quittingRootSequenceOwnHazard roots second)
  apply squeeze_zero
    (quittingMaxPairDeletedSurvivalWeight_nonneg roots mover 0)
    (fun fuel => ?_)
    (by simpa using hfirst.add hsecond)
  unfold quittingMaxPairDeletedSurvivalWeight
  apply Finset.sup'_le
  intro observer _
  by_cases hobserverFirst : observer = first
  · calc
      quittingPairDeletedSurvivalWeight roots mover observer 0 fuel ≤
          secondSurvival fuel := by
        apply quittingPairDeletedSurvivalWeight_le_hazardSurvival_of_other
          roots mover observer second hsecondMover
        exact fun h => hfirstSecond (hobserverFirst.symm.trans h.symm)
      _ ≤ firstSurvival fuel + secondSurvival fuel := by
        exact le_add_of_nonneg_left
          (quittingHazardSurvival_nonneg _ fuel)
  · calc
      quittingPairDeletedSurvivalWeight roots mover observer 0 fuel ≤
          firstSurvival fuel := by
        apply quittingPairDeletedSurvivalWeight_le_hazardSurvival_of_other
          roots mover observer first hfirstMover
        exact fun h => hobserverFirst h.symm
      _ ≤ firstSurvival fuel + secondSurvival fuel := by
        exact le_add_of_nonneg_right
          (quittingHazardSurvival_nonneg _ fuel)

/-- Equivalent convergence form of the exact two-zero-Never clock
classification. -/
theorem tendsto_quittingMaxPairDeletedSurvivalWeight_zero_iff_two_zeroNever
    (roots : ℕ → ι → PMF Bool) (mover : ι) :
    Tendsto (fun fuel =>
      quittingMaxPairDeletedSurvivalWeight roots mover 0 fuel)
        atTop (nhds 0) ↔
      ∃ first second,
        first ≠ second ∧ first ≠ mover ∧ second ≠ mover ∧
        quittingHazardNeverMass
            (quittingRootSequenceOwnHazard roots first) = 0 ∧
          quittingHazardNeverMass
            (quittingRootSequenceOwnHazard roots second) = 0 := by
  constructor
  · intro hzero
    have hlimit : quittingMaxPairDeletedSurvivalLimit roots mover 0 = 0 :=
      tendsto_nhds_unique
        (tendsto_quittingMaxPairDeletedSurvivalLimit roots mover 0) hzero
    exact
      (quittingMaxPairDeletedSurvivalLimit_eq_zero_iff_two_zeroNever
        roots mover).mp hlimit
  · rintro ⟨first, second, hfirstSecond, hfirstMover, hsecondMover,
      hfirstNever, hsecondNever⟩
    exact
      tendsto_quittingMaxPairDeletedSurvivalWeight_zero_of_two_zeroNever
        roots mover first second hfirstSecond hfirstMover hsecondMover
          hfirstNever hsecondNever

/-- **Exact finite classification of the explicit cap criterion.**  The
finite-splice error tends to zero exactly in one of two zero-pattern regimes:
the moved law has no cemetery atom, or two distinct other coordinates have no
cemetery atom.  This is an exact equivalence for the universal splice bound,
not a necessity claim for payoff-specific cancellations. -/
theorem tendsto_quittingFiniteSpliceError_zero_iff_zeroNever_pattern
    (roots : ℕ → ι → PMF Bool) (mover : ι)
    (hazard : ℕ → PMF Bool) :
    Tendsto (quittingFiniteSpliceError roots mover hazard)
        atTop (nhds 0) ↔
      quittingHazardNeverMass hazard = 0 ∨
        ∃ first second,
          first ≠ second ∧ first ≠ mover ∧ second ≠ mover ∧
          quittingHazardNeverMass
              (quittingRootSequenceOwnHazard roots first) = 0 ∧
            quittingHazardNeverMass
              (quittingRootSequenceOwnHazard roots second) = 0 := by
  constructor
  · intro hzero
    have hterminal :=
      tendsto_quittingFiniteSpliceError_terminal roots mover hazard
    have hproduct : quittingHazardNeverMass hazard *
        quittingMaxPairDeletedSurvivalLimit roots mover 0 = 0 :=
      tendsto_nhds_unique hterminal hzero
    rcases mul_eq_zero.mp hproduct with hnever | hclock
    · exact Or.inl hnever
    · exact Or.inr
        ((quittingMaxPairDeletedSurvivalLimit_eq_zero_iff_two_zeroNever
          roots mover).mp hclock)
  · rintro (hnever | ⟨first, second, hfirstSecond, hfirstMover,
      hsecondMover, hfirstNever, hsecondNever⟩)
    · exact tendsto_quittingFiniteSpliceError_zero_of_neverMass_zero
        roots mover hazard hnever
    · exact tendsto_quittingFiniteSpliceError_zero_of_pairDeleted
        roots mover hazard
          (tendsto_quittingMaxPairDeletedSurvivalWeight_zero_of_two_zeroNever
            roots mover first second hfirstSecond hfirstMover hsecondMover
              hfirstNever hsecondNever)

/-- Globally, every coordinate satisfies the universal finite-cap criterion
exactly when the profile contains at least two distinct zero-Never
coordinates.  This packages the three bootstrap classes `0`, `1`, and `≥ 2`.-/
theorem all_quittingFiniteSpliceError_tendsto_zero_iff_two_zeroNever
    (roots : ℕ → ι → PMF Bool) :
    (∀ mover, Tendsto
      (quittingFiniteSpliceError roots mover
        (quittingRootSequenceOwnHazard roots mover))
      atTop (nhds 0)) ↔
      ∃ first second,
        first ≠ second ∧
        quittingHazardNeverMass
            (quittingRootSequenceOwnHazard roots first) = 0 ∧
          quittingHazardNeverMass
            (quittingRootSequenceOwnHazard roots second) = 0 := by
  constructor
  · intro hall
    let mover : ι := Classical.choice (inferInstance : Nonempty ι)
    obtain ⟨other, hotherMover⟩ : ∃ other : ι, other ≠ mover :=
      exists_ne mover
    rcases (tendsto_quittingFiniteSpliceError_zero_iff_zeroNever_pattern
      roots mover (quittingRootSequenceOwnHazard roots mover)).mp
        (hall mover) with hmoverNever | htwo
    · rcases (tendsto_quittingFiniteSpliceError_zero_iff_zeroNever_pattern
        roots other (quittingRootSequenceOwnHazard roots other)).mp
          (hall other) with hotherNever | htwoOther
      · exact ⟨mover, other, hotherMover.symm, hmoverNever, hotherNever⟩
      · obtain ⟨first, second, hfirstSecond, _hfirstOther,
            _hsecondOther, hfirstNever, hsecondNever⟩ := htwoOther
        exact ⟨first, second, hfirstSecond, hfirstNever, hsecondNever⟩
    · obtain ⟨first, second, hfirstSecond, _hfirstMover,
          _hsecondMover, hfirstNever, hsecondNever⟩ := htwo
      exact ⟨first, second, hfirstSecond, hfirstNever, hsecondNever⟩
  · rintro ⟨first, second, hfirstSecond, hfirstNever, hsecondNever⟩
    intro mover
    apply (tendsto_quittingFiniteSpliceError_zero_iff_zeroNever_pattern
      roots mover (quittingRootSequenceOwnHazard roots mover)).mpr
    by_cases hmoverFirst : mover = first
    · left
      simpa [hmoverFirst] using hfirstNever
    by_cases hmoverSecond : mover = second
    · left
      simpa [hmoverSecond] using hsecondNever
    · right
      exact ⟨first, second, hfirstSecond, Ne.symm hmoverFirst,
        Ne.symm hmoverSecond, hfirstNever, hsecondNever⟩

/-- Two distinct finite sure-quit sentinels, both different from the reset
mover, kill the maximum pair-deleted clock: deleting one observer can erase at
most one sentinel. -/
theorem quittingMaxPairDeletedSurvivalWeight_eq_zero_of_two_sentinels
    (roots : ℕ → ι → PMF Bool) (mover first second : ι)
    (hfirstSecond : first ≠ second)
    (hfirstMover : first ≠ mover) (hsecondMover : second ≠ mover)
    (firstTime secondTime fuel : ℕ)
    (hfirstFuel : firstTime < fuel) (hsecondFuel : secondTime < fuel)
    (hfirst : roots firstTime first = PMF.pure true)
    (hsecond : roots secondTime second = PMF.pure true) :
    quittingMaxPairDeletedSurvivalWeight roots mover 0 fuel = 0 := by
  apply le_antisymm
  · unfold quittingMaxPairDeletedSurvivalWeight
    apply Finset.sup'_le
    intro observer _hobserver
    by_cases hobserverFirst : observer = first
    · apply le_of_eq
      apply quittingPairDeletedSurvivalWeight_eq_zero_of_sure_other
        roots mover observer second hsecondMover
      · exact fun h => hfirstSecond (hobserverFirst.symm.trans h.symm)
      · exact hsecondFuel
      · exact hsecond
    · apply le_of_eq
      apply quittingPairDeletedSurvivalWeight_eq_zero_of_sure_other
        roots mover observer first hfirstMover
      · exact fun h => hobserverFirst h.symm
      · exact hfirstFuel
      · exact hfirst
  · exact quittingMaxPairDeletedSurvivalWeight_nonneg roots mover 0 fuel

/-- The two-sentinel maximum clock is eventually identically zero. -/
theorem tendsto_quittingMaxPairDeletedSurvivalWeight_zero_of_two_sentinels
    (roots : ℕ → ι → PMF Bool) (mover first second : ι)
    (hfirstSecond : first ≠ second)
    (hfirstMover : first ≠ mover) (hsecondMover : second ≠ mover)
    (firstTime secondTime : ℕ)
    (hfirst : roots firstTime first = PMF.pure true)
    (hsecond : roots secondTime second = PMF.pure true) :
    Tendsto (fun fuel =>
      quittingMaxPairDeletedSurvivalWeight roots mover 0 fuel)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨max firstTime secondTime + 1, fun fuel hfuel => ?_⟩
  have hfirstFuel : firstTime < fuel := by omega
  have hsecondFuel : secondTime < fuel := by omega
  rw [quittingMaxPairDeletedSurvivalWeight_eq_zero_of_two_sentinels
    roots mover first second hfirstSecond hfirstMover hsecondMover
      firstTime secondTime fuel hfirstFuel hsecondFuel hfirst hsecond]
  simpa using hε

/-! ## One finite cutoff controls the whole terminal semantic port -/

/-- If the explicit splice error tends to zero, then at every requested
positive accuracy one finite cap simultaneously approximates every player's
prescribed payoff, unrestricted behavioral envelope, and semantic debt. -/
theorem exists_finiteCap_all_terminalSemantics_close_after
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (strategy : (quittingGame reward).BehaviorStrategy mover)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (herror : Tendsto (fun cutoff =>
      quittingFiniteSpliceError (quittingProfileLiveRoot reward profile)
      mover (quittingBehaviorLiveHazard reward strategy) cutoff)
      atTop (nhds 0))
    (lowerBound : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ cutoff, lowerBound ≤ cutoff ∧ ∀ observer,
      |quittingTerminalPayoff reward
            (Function.update profile mover strategy) observer -
          quittingTerminalPayoff reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer| < δ ∧
      |quittingContinuationBestResponseValue reward
            (Function.update profile mover strategy) observer -
          quittingContinuationBestResponseValue reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer| < δ ∧
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover strategy)) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover
                (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                  cutoff))) observer| < δ := by
  let error : ℕ → ℝ := fun cutoff =>
    quittingFiniteSpliceError (quittingProfileLiveRoot reward profile)
      mover (quittingBehaviorLiveHazard reward strategy) cutoff
  have hscaled : Tendsto (fun cutoff => 4 * M * error cutoff)
      atTop (nhds 0) := by
    have := herror.const_mul (4 * M)
    simpa [error] using this
  obtain ⟨threshold, hthreshold⟩ :=
    (Metric.tendsto_atTop.mp hscaled) δ hδ
  let cutoff := max lowerBound threshold
  have hlowerBound : lowerBound ≤ cutoff := le_max_left _ _
  have hthresholdCutoff : threshold ≤ cutoff := le_max_right _ _
  have herror0 : 0 ≤ error cutoff := by
    exact quittingFiniteSpliceError_nonneg
      (quittingProfileLiveRoot reward profile) mover
        (quittingBehaviorLiveHazard reward strategy) cutoff
  have hfourNonneg : 0 ≤ 4 * M * error cutoff := by positivity
  have hfour : 4 * M * error cutoff < δ := by
    have hclose := hthreshold cutoff hthresholdCutoff
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hfourNonneg] at hclose
    exact hclose
  have htwoLe : 2 * M * error cutoff ≤ 4 * M * error cutoff := by
    nlinarith [mul_nonneg hM herror0]
  refine ⟨cutoff, hlowerBound, fun observer => ?_⟩
  have hpay := abs_quittingTerminalPayoff_finiteCap_sub_le
    reward profile mover observer strategy cutoff hM hreward
  have hbest := abs_quittingContinuationBestResponseValue_finiteCap_sub_le
    reward profile mover observer strategy cutoff hM hreward
  have hdebt := abs_quittingTerminalSemanticDebt_finiteCap_sub_le
    reward profile mover observer strategy cutoff hM hreward
  dsimp only [error] at hfour htwoLe
  exact ⟨lt_of_le_of_lt hpay (lt_of_le_of_lt htwoLe hfour),
    lt_of_le_of_lt hbest (lt_of_le_of_lt htwoLe hfour),
    lt_of_le_of_lt hdebt hfour⟩

/-- One finite cutoff controls the terminal semantics; this compatibility
wrapper imposes no lower bound on the selected date. -/
theorem exists_finiteCap_all_terminalSemantics_close
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (strategy : (quittingGame reward).BehaviorStrategy mover)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (herror : Tendsto (fun cutoff =>
      quittingFiniteSpliceError (quittingProfileLiveRoot reward profile)
        mover (quittingBehaviorLiveHazard reward strategy) cutoff)
      atTop (nhds 0))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ cutoff, ∀ observer,
      |quittingTerminalPayoff reward
            (Function.update profile mover strategy) observer -
          quittingTerminalPayoff reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer| < δ ∧
      |quittingContinuationBestResponseValue reward
            (Function.update profile mover strategy) observer -
          quittingContinuationBestResponseValue reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer| < δ ∧
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover strategy)) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover
                (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                  cutoff))) observer| < δ := by
  obtain ⟨cutoff, _hcutoff, hclose⟩ :=
    exists_finiteCap_all_terminalSemantics_close_after
      reward profile mover strategy hM hreward herror 0 hδ
  exact ⟨cutoff, hclose⟩

/-- Finite-iteration reduction for a stochastic button with no `Never` atom. -/
theorem exists_finiteCap_all_terminalSemantics_close_of_neverMass_zero_after
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (strategy : (quittingGame reward).BehaviorStrategy mover)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnever : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward strategy) = 0)
    (lowerBound : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ cutoff, lowerBound ≤ cutoff ∧ ∀ observer,
      |quittingTerminalPayoff reward
            (Function.update profile mover strategy) observer -
          quittingTerminalPayoff reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer| < δ ∧
      |quittingContinuationBestResponseValue reward
            (Function.update profile mover strategy) observer -
          quittingContinuationBestResponseValue reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer| < δ ∧
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover strategy)) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover
                (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                  cutoff))) observer| < δ := by
  apply exists_finiteCap_all_terminalSemantics_close_after
    reward profile mover strategy hM hreward
  · exact tendsto_quittingFiniteSpliceError_zero_of_neverMass_zero
      (quittingProfileLiveRoot reward profile) mover
        (quittingBehaviorLiveHazard reward strategy) hnever
  · exact hδ

/-- Compatibility specialization without a requested prefix length. -/
theorem exists_finiteCap_all_terminalSemantics_close_of_neverMass_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (strategy : (quittingGame reward).BehaviorStrategy mover)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnever : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward strategy) = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ cutoff, ∀ observer,
      |quittingTerminalPayoff reward
            (Function.update profile mover strategy) observer -
          quittingTerminalPayoff reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer| < δ ∧
      |quittingContinuationBestResponseValue reward
            (Function.update profile mover strategy) observer -
          quittingContinuationBestResponseValue reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer| < δ ∧
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover strategy)) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover
                (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                  cutoff))) observer| < δ := by
  apply exists_finiteCap_all_terminalSemantics_close
    reward profile mover strategy hM hreward
  · exact tendsto_quittingFiniteSpliceError_zero_of_neverMass_zero
      (quittingProfileLiveRoot reward profile) mover
        (quittingBehaviorLiveHazard reward strategy) hnever
  · exact hδ

/-- Finite-iteration reduction with a possible `Never` atom when every
relevant pair-deleted survival clock dies uniformly through their finite
maximum. -/
theorem exists_finiteCap_all_terminalSemantics_close_of_pairDeleted_after
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (strategy : (quittingGame reward).BehaviorStrategy mover)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hclock : Tendsto (fun cutoff =>
      quittingMaxPairDeletedSurvivalWeight
        (quittingProfileLiveRoot reward profile) mover 0 cutoff)
      atTop (nhds 0))
    (lowerBound : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ cutoff, lowerBound ≤ cutoff ∧ ∀ observer,
      |quittingTerminalPayoff reward
            (Function.update profile mover strategy) observer -
          quittingTerminalPayoff reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer| < δ ∧
      |quittingContinuationBestResponseValue reward
            (Function.update profile mover strategy) observer -
          quittingContinuationBestResponseValue reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer| < δ ∧
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover strategy)) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover
                (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                  cutoff))) observer| < δ := by
  apply exists_finiteCap_all_terminalSemantics_close_after
    reward profile mover strategy hM hreward
  · exact tendsto_quittingFiniteSpliceError_zero_of_pairDeleted
      (quittingProfileLiveRoot reward profile) mover
        (quittingBehaviorLiveHazard reward strategy) hclock
  · exact hδ

/-- Compatibility specialization without a requested prefix length. -/
theorem exists_finiteCap_all_terminalSemantics_close_of_pairDeleted
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (strategy : (quittingGame reward).BehaviorStrategy mover)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hclock : Tendsto (fun cutoff =>
      quittingMaxPairDeletedSurvivalWeight
        (quittingProfileLiveRoot reward profile) mover 0 cutoff)
      atTop (nhds 0))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ cutoff, ∀ observer,
      |quittingTerminalPayoff reward
            (Function.update profile mover strategy) observer -
          quittingTerminalPayoff reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer| < δ ∧
      |quittingContinuationBestResponseValue reward
            (Function.update profile mover strategy) observer -
          quittingContinuationBestResponseValue reward
            (Function.update profile mover
              (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                cutoff)) observer| < δ ∧
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover strategy)) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (Function.update profile mover
                (quittingStoppingLawFiniteCapBehaviorStrategy reward mover strategy
                  cutoff))) observer| < δ := by
  apply exists_finiteCap_all_terminalSemantics_close
    reward profile mover strategy hM hreward
  · exact tendsto_quittingFiniteSpliceError_zero_of_pairDeleted
      (quittingProfileLiveRoot reward profile) mover
        (quittingBehaviorLiveHazard reward strategy) hclock
  · exact hδ

/-! ## Simultaneous finite capping on the zero-Never class -/

/-- Cap the strategy currently assigned to one player inside a profile. -/
def quittingFiniteCapProfileAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (cutoff : ℕ) : (quittingGame reward).BehaviorProfile :=
  Function.update profile mover
    (quittingStoppingLawFiniteCapBehaviorStrategy reward mover
      (profile mover) cutoff)

/-- Uniform coordinatewise control of the complete terminal semantics: the
prescribed payoff, the full behavioral best-response envelope, and debt. -/
def QuittingTerminalSemanticsWithin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (left right : (quittingGame reward).BehaviorProfile)
    (error : ℝ) : Prop :=
  ∀ observer,
    |(quittingTerminalSemanticPair reward left).1 observer -
        (quittingTerminalSemanticPair reward right).1 observer| ≤ error ∧
    |(quittingTerminalSemanticPair reward left).2 observer -
        (quittingTerminalSemanticPair reward right).2 observer| ≤ error ∧
    |quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward left) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward right) observer| ≤ error

omit [Nontrivial ι] in
/-- Terminal-semantic error budgets compose additively. -/
theorem QuittingTerminalSemanticsWithin.trans
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first middle last : (quittingGame reward).BehaviorProfile}
    {firstError secondError : ℝ}
    (hfirst : QuittingTerminalSemanticsWithin reward first middle firstError)
    (hsecond : QuittingTerminalSemanticsWithin reward middle last secondError) :
    QuittingTerminalSemanticsWithin reward first last
      (firstError + secondError) := by
  intro observer
  have h₁ := hfirst observer
  have h₂ := hsecond observer
  constructor
  · calc
      |(quittingTerminalSemanticPair reward first).1 observer -
          (quittingTerminalSemanticPair reward last).1 observer| =
          |((quittingTerminalSemanticPair reward first).1 observer -
              (quittingTerminalSemanticPair reward middle).1 observer) +
            ((quittingTerminalSemanticPair reward middle).1 observer -
              (quittingTerminalSemanticPair reward last).1 observer)| := by
            congr 1
            ring
      _ ≤ |(quittingTerminalSemanticPair reward first).1 observer -
              (quittingTerminalSemanticPair reward middle).1 observer| +
            |(quittingTerminalSemanticPair reward middle).1 observer -
              (quittingTerminalSemanticPair reward last).1 observer| :=
          abs_add_le _ _
      _ ≤ firstError + secondError := add_le_add h₁.1 h₂.1
  · constructor
    · calc
        |(quittingTerminalSemanticPair reward first).2 observer -
            (quittingTerminalSemanticPair reward last).2 observer| =
            |((quittingTerminalSemanticPair reward first).2 observer -
                (quittingTerminalSemanticPair reward middle).2 observer) +
              ((quittingTerminalSemanticPair reward middle).2 observer -
                (quittingTerminalSemanticPair reward last).2 observer)| := by
              congr 1
              ring
        _ ≤ |(quittingTerminalSemanticPair reward first).2 observer -
                (quittingTerminalSemanticPair reward middle).2 observer| +
              |(quittingTerminalSemanticPair reward middle).2 observer -
                (quittingTerminalSemanticPair reward last).2 observer| :=
            abs_add_le _ _
        _ ≤ firstError + secondError := add_le_add h₁.2.1 h₂.2.1
    · calc
        |quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward first) observer -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward last) observer| =
            |(quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward first) observer -
                quittingTerminalSemanticDebt
                  (quittingTerminalSemanticPair reward middle) observer) +
              (quittingTerminalSemanticDebt
                  (quittingTerminalSemanticPair reward middle) observer -
                quittingTerminalSemanticDebt
                  (quittingTerminalSemanticPair reward last) observer)| := by
              congr 1
              ring
        _ ≤ |quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward first) observer -
              quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward middle) observer| +
            |quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward middle) observer -
              quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward last) observer| :=
          abs_add_le _ _
        _ ≤ firstError + secondError := add_le_add h₁.2.2 h₂.2.2

omit [Nontrivial ι] in
/-- Uniform payoff/envelope control transports a terminal approximate-Nash
certificate.  Debt control is carried by the same semantic relation but is
not needed for this implication. -/
theorem isεAsymptoticNash_of_terminalSemanticsWithin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : (quittingGame reward).BehaviorProfile)
    {ε error M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε source)
    (hclose : QuittingTerminalSemanticsWithin reward source target error) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (ε + 2 * error) target := by
  have hsourceBest : ∀ observer,
      quittingContinuationBestResponseValue reward source observer ≤
        quittingTerminalPayoff reward source observer + ε := by
    intro observer
    unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact ⟨_, ⟨source observer, rfl⟩⟩
    · rintro _ ⟨deviation, rfl⟩
      exact hnash observer deviation
  intro observer deviation
  have hdeviation :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward target observer deviation hM hreward
  have h := hclose observer
  have hpayoff := h.1
  have hbest := h.2.1
  change |quittingTerminalPayoff reward source observer -
      quittingTerminalPayoff reward target observer| ≤ error at hpayoff
  change |quittingContinuationBestResponseValue reward source observer -
      quittingContinuationBestResponseValue reward target observer| ≤ error
    at hbest
  have hbestUpper :
      quittingContinuationBestResponseValue reward target observer ≤
        quittingContinuationBestResponseValue reward source observer + error := by
    linarith [neg_le_abs
      (quittingContinuationBestResponseValue reward source observer -
        quittingContinuationBestResponseValue reward target observer), hbest]
  have hpayoffUpper :
      quittingTerminalPayoff reward source observer ≤
        quittingTerminalPayoff reward target observer + error := by
    linarith [le_abs_self
      (quittingTerminalPayoff reward source observer -
        quittingTerminalPayoff reward target observer), hpayoff]
  linarith [hsourceBest observer]

/-- The no-Never one-button theorem in profile-to-profile form. -/
theorem exists_quittingFiniteCapProfileAt_semantics_close_of_neverMass_zero_after
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnever : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile mover)) = 0)
    (lowerBound : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ cutoff, lowerBound ≤ cutoff ∧ ∀ observer,
      |(quittingTerminalSemanticPair reward profile).1 observer -
          (quittingTerminalSemanticPair reward
            (quittingFiniteCapProfileAt reward profile mover cutoff)).1
              observer| < δ ∧
      |(quittingTerminalSemanticPair reward profile).2 observer -
          (quittingTerminalSemanticPair reward
            (quittingFiniteCapProfileAt reward profile mover cutoff)).2
              observer| < δ ∧
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingFiniteCapProfileAt reward profile mover cutoff))
              observer| < δ := by
  obtain ⟨cutoff, hlower, hcutoff⟩ :=
    exists_finiteCap_all_terminalSemantics_close_of_neverMass_zero_after
      reward profile mover (profile mover) hM hreward hnever lowerBound hδ
  refine ⟨cutoff, hlower, fun observer => ?_⟩
  simpa [quittingFiniteCapProfileAt, quittingTerminalSemanticPair] using
    hcutoff observer

/-- Compatibility profile form without a requested prefix length. -/
theorem exists_quittingFiniteCapProfileAt_semantics_close_of_neverMass_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnever : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile mover)) = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ cutoff, ∀ observer,
      |(quittingTerminalSemanticPair reward profile).1 observer -
          (quittingTerminalSemanticPair reward
            (quittingFiniteCapProfileAt reward profile mover cutoff)).1
              observer| < δ ∧
      |(quittingTerminalSemanticPair reward profile).2 observer -
          (quittingTerminalSemanticPair reward
            (quittingFiniteCapProfileAt reward profile mover cutoff)).2
              observer| < δ ∧
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingFiniteCapProfileAt reward profile mover cutoff))
              observer| < δ := by
  obtain ⟨cutoff, hcutoff⟩ :=
    exists_finiteCap_all_terminalSemantics_close_of_neverMass_zero
      reward profile mover (profile mover) hM hreward hnever hδ
  refine ⟨cutoff, fun observer => ?_⟩
  simpa [quittingFiniteCapProfileAt, quittingTerminalSemanticPair] using
    hcutoff observer

/-- Two distinct zero-Never opponents make an arbitrary mover directly
cappable, even if the mover itself has positive Never mass.  This version
uses their decaying survival curves and does not first replace them by
sure-Quit sentinels. -/
theorem exists_quittingFiniteCapProfileAt_semantics_close_of_two_zeroNeverOpponents
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover first second : ι)
    (hfirstSecond : first ≠ second)
    (hfirstMover : first ≠ mover) (hsecondMover : second ≠ mover)
    (hneverFirst : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile first)) = 0)
    (hneverSecond : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile second)) = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ cutoff, ∀ observer,
      |(quittingTerminalSemanticPair reward profile).1 observer -
          (quittingTerminalSemanticPair reward
            (quittingFiniteCapProfileAt reward profile mover cutoff)).1
              observer| < δ ∧
      |(quittingTerminalSemanticPair reward profile).2 observer -
          (quittingTerminalSemanticPair reward
            (quittingFiniteCapProfileAt reward profile mover cutoff)).2
              observer| < δ ∧
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingFiniteCapProfileAt reward profile mover cutoff))
              observer| < δ := by
  have hneverFirstRoot : quittingHazardNeverMass
      (quittingRootSequenceOwnHazard
        (quittingProfileLiveRoot reward profile) first) = 0 := by
    change quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile first)) = 0
    exact hneverFirst
  have hneverSecondRoot : quittingHazardNeverMass
      (quittingRootSequenceOwnHazard
        (quittingProfileLiveRoot reward profile) second) = 0 := by
    change quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile second)) = 0
    exact hneverSecond
  obtain ⟨cutoff, hcutoff⟩ :=
    exists_finiteCap_all_terminalSemantics_close_of_pairDeleted
      reward profile mover (profile mover) hM hreward
      (tendsto_quittingMaxPairDeletedSurvivalWeight_zero_of_two_zeroNever
        (quittingProfileLiveRoot reward profile) mover first second
          hfirstSecond hfirstMover hsecondMover hneverFirstRoot
          hneverSecondRoot)
      hδ
  refine ⟨cutoff, fun observer => ?_⟩
  simpa [quittingFiniteCapProfileAt, quittingTerminalSemanticPair] using
    hcutoff observer

/-- If every original live-path stopping law has zero `Never` mass, all
players can be capped at finite dates while keeping the complete terminal
semantic pair and every debt coordinate uniformly close.  Every resulting
strategy is literally a finite cap of its corresponding original strategy. -/
theorem exists_allPlayersFiniteCap_terminalSemantics_close_of_neverMass_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnever : ∀ mover, quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile mover)) = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ capped : (quittingGame reward).BehaviorProfile,
      (∀ mover, ∃ cutoff,
        capped mover =
          quittingStoppingLawFiniteCapBehaviorStrategy reward mover
            (profile mover) cutoff) ∧
      (∀ observer,
        |(quittingTerminalSemanticPair reward profile).1 observer -
            (quittingTerminalSemanticPair reward capped).1 observer| < δ ∧
        |(quittingTerminalSemanticPair reward profile).2 observer -
            (quittingTerminalSemanticPair reward capped).2 observer| < δ ∧
        |quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward profile) observer -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward capped) observer| < δ) := by
  classical
  let η : ℝ := δ / ((Fintype.card ι : ℝ) + 1)
  have hdenom : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have hη : 0 < η := div_pos hδ hdenom
  have hfinite : ∀ players : Finset ι,
      ∃ current : (quittingGame reward).BehaviorProfile,
        (∀ mover ∈ players, ∃ cutoff,
          current mover =
            quittingStoppingLawFiniteCapBehaviorStrategy reward mover
              (profile mover) cutoff) ∧
        (∀ mover ∉ players, current mover = profile mover) ∧
        (∀ observer,
          |(quittingTerminalSemanticPair reward profile).1 observer -
              (quittingTerminalSemanticPair reward current).1 observer| ≤
            (players.card : ℝ) * η ∧
          |(quittingTerminalSemanticPair reward profile).2 observer -
              (quittingTerminalSemanticPair reward current).2 observer| ≤
            (players.card : ℝ) * η ∧
          |quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward profile) observer -
              quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward current) observer| ≤
            (players.card : ℝ) * η) := by
    intro players
    induction players using Finset.induction_on with
    | empty =>
        refine ⟨profile, ?_, ?_, ?_⟩
        · simp
        · simp
        · intro observer
          simp
    | @insert mover players hmover ih =>
        obtain ⟨current, hprocessed, hunprocessed, hcurrent⟩ := ih
        have hmoverCurrent : current mover = profile mover :=
          hunprocessed mover hmover
        have hmoverNever : quittingHazardNeverMass
            (quittingBehaviorLiveHazard reward (current mover)) = 0 := by
          rw [hmoverCurrent]
          exact hnever mover
        obtain ⟨cutoff, hstep⟩ :=
          exists_quittingFiniteCapProfileAt_semantics_close_of_neverMass_zero
            reward current mover hM hreward hmoverNever hη
        let next := quittingFiniteCapProfileAt reward current mover cutoff
        refine ⟨next, ?_, ?_, ?_⟩
        · intro player hplayer
          rcases Finset.mem_insert.mp hplayer with rfl | hplayerOld
          · refine ⟨cutoff, ?_⟩
            simp [next, quittingFiniteCapProfileAt, hmoverCurrent]
          · obtain ⟨oldCutoff, hold⟩ := hprocessed player hplayerOld
            refine ⟨oldCutoff, ?_⟩
            have hne : player ≠ mover := by
              intro heq
              subst player
              exact hmover hplayerOld
            simp [next, quittingFiniteCapProfileAt,
              Function.update_of_ne hne, hold]
        · intro player hplayer
          have hnotOld : player ∉ players := by
            exact fun hmem => hplayer (Finset.mem_insert_of_mem hmem)
          have hne : player ≠ mover := by
            intro heq
            subst player
            exact hplayer (Finset.mem_insert_self mover players)
          simp [next, quittingFiniteCapProfileAt,
            Function.update_of_ne hne, hunprocessed player hnotOld]
        · intro observer
          have hold := hcurrent observer
          have hnew := hstep observer
          have hcard : (insert mover players).card = players.card + 1 :=
            Finset.card_insert_of_notMem hmover
          constructor
          · apply le_of_lt
            calc
              |(quittingTerminalSemanticPair reward profile).1 observer -
                  (quittingTerminalSemanticPair reward next).1 observer| =
                  |((quittingTerminalSemanticPair reward profile).1 observer -
                      (quittingTerminalSemanticPair reward current).1 observer) +
                    ((quittingTerminalSemanticPair reward current).1 observer -
                      (quittingTerminalSemanticPair reward next).1 observer)| := by
                    congr 1
                    ring
              _ ≤ |(quittingTerminalSemanticPair reward profile).1 observer -
                    (quittingTerminalSemanticPair reward current).1 observer| +
                  |(quittingTerminalSemanticPair reward current).1 observer -
                    (quittingTerminalSemanticPair reward next).1 observer| :=
                abs_add_le _ _
              _ < (players.card : ℝ) * η + η :=
                add_lt_add_of_le_of_lt hold.1 (by simpa [next] using hnew.1)
              _ = ((insert mover players).card : ℝ) * η := by
                rw [hcard]
                push_cast
                ring
          · constructor
            · apply le_of_lt
              calc
                |(quittingTerminalSemanticPair reward profile).2 observer -
                    (quittingTerminalSemanticPair reward next).2 observer| =
                    |((quittingTerminalSemanticPair reward profile).2 observer -
                        (quittingTerminalSemanticPair reward current).2 observer) +
                      ((quittingTerminalSemanticPair reward current).2 observer -
                        (quittingTerminalSemanticPair reward next).2 observer)| := by
                      congr 1
                      ring
                _ ≤ |(quittingTerminalSemanticPair reward profile).2 observer -
                      (quittingTerminalSemanticPair reward current).2 observer| +
                    |(quittingTerminalSemanticPair reward current).2 observer -
                      (quittingTerminalSemanticPair reward next).2 observer| :=
                  abs_add_le _ _
                _ < (players.card : ℝ) * η + η :=
                  add_lt_add_of_le_of_lt hold.2.1
                    (by simpa [next] using hnew.2.1)
                _ = ((insert mover players).card : ℝ) * η := by
                  rw [hcard]
                  push_cast
                  ring
            · apply le_of_lt
              calc
                |quittingTerminalSemanticDebt
                      (quittingTerminalSemanticPair reward profile) observer -
                    quittingTerminalSemanticDebt
                      (quittingTerminalSemanticPair reward next) observer| =
                    |(quittingTerminalSemanticDebt
                        (quittingTerminalSemanticPair reward profile) observer -
                        quittingTerminalSemanticDebt
                          (quittingTerminalSemanticPair reward current) observer) +
                      (quittingTerminalSemanticDebt
                          (quittingTerminalSemanticPair reward current) observer -
                        quittingTerminalSemanticDebt
                          (quittingTerminalSemanticPair reward next) observer)| := by
                      congr 1
                      ring
                _ ≤ |quittingTerminalSemanticDebt
                        (quittingTerminalSemanticPair reward profile) observer -
                      quittingTerminalSemanticDebt
                        (quittingTerminalSemanticPair reward current) observer| +
                    |quittingTerminalSemanticDebt
                        (quittingTerminalSemanticPair reward current) observer -
                      quittingTerminalSemanticDebt
                        (quittingTerminalSemanticPair reward next) observer| :=
                  abs_add_le _ _
                _ < (players.card : ℝ) * η + η :=
                  add_lt_add_of_le_of_lt hold.2.2
                    (by simpa [next] using hnew.2.2)
                _ = ((insert mover players).card : ℝ) * η := by
                  rw [hcard]
                  push_cast
                  ring
  obtain ⟨capped, hcapped, _hunprocessed, hclose⟩ :=
    hfinite Finset.univ
  have htotal : (Fintype.card ι : ℝ) * η < δ := by
    calc
      (Fintype.card ι : ℝ) * η <
          ((Fintype.card ι : ℝ) + 1) * η := by
        exact mul_lt_mul_of_pos_right (by linarith) hη
      _ = δ := by
        dsimp [η]
        field_simp
  refine ⟨capped, ?_, ?_⟩
  · intro mover
    exact hcapped mover (Finset.mem_univ mover)
  · intro observer
    have h := hclose observer
    simpa using ⟨lt_of_le_of_lt h.1 htotal,
      lt_of_le_of_lt h.2.1 htotal,
      lt_of_le_of_lt h.2.2 htotal⟩

/-- Once every player is finitely capped, every unilateral deviator faces a
distinct opponent who quits surely at one finite live date.  Thus the tail
after that date is behaviorally invisible to that deviation. -/
theorem quittingAllPlayersFiniteCap_deviation_has_finite_sureQuitter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source capped : (quittingGame reward).BehaviorProfile)
    (hcapped : ∀ mover, ∃ cutoff,
      capped mover =
        quittingStoppingLawFiniteCapBehaviorStrategy reward mover
          (source mover) cutoff)
    (observer : ι)
    (deviation : (quittingGame reward).BehaviorStrategy observer) :
    ∃ cutoff, QuittingRootHasSureQuitter
      (quittingProfileLiveRoot reward
        (Function.update capped observer deviation) cutoff) := by
  obtain ⟨opponent, hopponent⟩ : ∃ opponent : ι, opponent ≠ observer :=
    exists_ne observer
  obtain ⟨cutoff, hcap⟩ := hcapped opponent
  refine ⟨cutoff, opponent, ?_⟩
  rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate]
  unfold quittingRootSequenceUpdate
  rw [Function.update_of_ne hopponent]
  change quittingBehaviorLiveHazard reward (capped opponent) cutoff =
    PMF.pure true
  rw [hcap, quittingBehaviorLiveHazard_finiteCap]
  exact quittingHazardCapAt_self _ cutoff

/-- All of the deviation problems share one finite iteration bound.  Before
that horizon, every unilateral deviation encounters a prescribed opponent
who quits surely.  The horizon depends on the capped profile, but not on the
observer or its arbitrary behavioral deviation. -/
theorem quittingAllPlayersFiniteCap_deviation_has_uniform_horizon
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source capped : (quittingGame reward).BehaviorProfile)
    (hcapped : ∀ mover, ∃ cutoff,
      capped mover =
        quittingStoppingLawFiniteCapBehaviorStrategy reward mover
          (source mover) cutoff) :
    ∃ horizon, ∀ observer
        (deviation : (quittingGame reward).BehaviorStrategy observer),
      ∃ cutoff, cutoff < horizon ∧ QuittingRootHasSureQuitter
        (quittingProfileLiveRoot reward
          (Function.update capped observer deviation) cutoff) := by
  classical
  let capTime : ι → ℕ := fun player => Classical.choose (hcapped player)
  have hcapTime : ∀ player, capped player =
      quittingStoppingLawFiniteCapBehaviorStrategy reward player
        (source player) (capTime player) := by
    intro player
    exact Classical.choose_spec (hcapped player)
  let horizon := Finset.univ.sup capTime + 1
  refine ⟨horizon, ?_⟩
  intro observer deviation
  obtain ⟨opponent, hopponent⟩ : ∃ opponent : ι,
      opponent ≠ observer := exists_ne observer
  refine ⟨capTime opponent, ?_, opponent, ?_⟩
  · dsimp [horizon]
    have hle : capTime opponent ≤ Finset.univ.sup capTime :=
      Finset.le_sup (Finset.mem_univ opponent)
    omega
  · rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate]
    unfold quittingRootSequenceUpdate
    rw [Function.update_of_ne hopponent]
    change quittingBehaviorLiveHazard reward (capped opponent)
        (capTime opponent) = PMF.pure true
    rw [hcapTime opponent, quittingBehaviorLiveHazard_finiteCap]
    exact quittingHazardCapAt_self _ (capTime opponent)

omit [DecidableEq ι] [Nontrivial ι] in
/-- If every selected cap date lies after `prefix`, the entire prescribed live
root word is preserved literally before `prefix`.  In particular, choosing a
positive lower bound fixes the time-zero entry root exactly. -/
theorem quittingAllPlayersFiniteCap_liveRoot_eq_before
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source capped : (quittingGame reward).BehaviorProfile)
    (prefixLength : ℕ)
    (hcapped : ∀ mover, ∃ cutoff, prefixLength ≤ cutoff ∧
      capped mover =
        quittingStoppingLawFiniteCapBehaviorStrategy reward mover
          (source mover) cutoff)
    {time : ℕ} (htime : time < prefixLength) :
    quittingProfileLiveRoot reward capped time =
      quittingProfileLiveRoot reward source time := by
  funext player
  obtain ⟨cutoff, hprefixCutoff, hcap⟩ := hcapped player
  change quittingBehaviorLiveHazard reward (capped player) time =
    quittingBehaviorLiveHazard reward (source player) time
  rw [hcap, quittingBehaviorLiveHazard_finiteCap,
    quittingHazardCapAt_of_lt]
  omega

/-! ## Two zero-Never seeds unlock arbitrary later buttons -/

/-- After two distinct players have been finitely capped, every third
player's maximal pair-deleted clock dies. -/
theorem tendsto_quittingMaxPairDeletedSurvivalWeight_zero_of_two_cappedPlayers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source current : (quittingGame reward).BehaviorProfile)
    (mover first second : ι)
    (hfirstSecond : first ≠ second)
    (hfirstMover : first ≠ mover) (hsecondMover : second ≠ mover)
    (firstTime secondTime : ℕ)
    (hfirstCap : current first =
      quittingStoppingLawFiniteCapBehaviorStrategy reward first
        (source first) firstTime)
    (hsecondCap : current second =
      quittingStoppingLawFiniteCapBehaviorStrategy reward second
        (source second) secondTime) :
    Tendsto (fun fuel =>
      quittingMaxPairDeletedSurvivalWeight
        (quittingProfileLiveRoot reward current) mover 0 fuel)
      atTop (nhds 0) := by
  have hfirstSure : quittingProfileLiveRoot reward current firstTime first =
      PMF.pure true := by
    change quittingBehaviorLiveHazard reward (current first) firstTime = _
    rw [hfirstCap, quittingBehaviorLiveHazard_finiteCap]
    exact quittingHazardCapAt_self _ firstTime
  have hsecondSure : quittingProfileLiveRoot reward current secondTime second =
      PMF.pure true := by
    change quittingBehaviorLiveHazard reward (current second) secondTime = _
    rw [hsecondCap, quittingBehaviorLiveHazard_finiteCap]
    exact quittingHazardCapAt_self _ secondTime
  exact tendsto_quittingMaxPairDeletedSurvivalWeight_zero_of_two_sentinels
    (quittingProfileLiveRoot reward current) mover first second
      hfirstSecond hfirstMover hsecondMover firstTime secondTime
      hfirstSure hsecondSure

/-- **Two-sentinel extension step.**  Once two distinct capped players are
present, an arbitrary third player's button can be capped at any requested
terminal-semantic accuracy.  No condition on that third button's Never mass
is needed. -/
theorem exists_quittingFiniteCapProfileAt_semantics_close_of_two_cappedPlayers_after
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source current : (quittingGame reward).BehaviorProfile)
    (mover first second : ι)
    (hfirstSecond : first ≠ second)
    (hfirstMover : first ≠ mover) (hsecondMover : second ≠ mover)
    (firstTime secondTime : ℕ)
    (hfirstCap : current first =
      quittingStoppingLawFiniteCapBehaviorStrategy reward first
        (source first) firstTime)
    (hsecondCap : current second =
      quittingStoppingLawFiniteCapBehaviorStrategy reward second
        (source second) secondTime)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (lowerBound : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ cutoff, lowerBound ≤ cutoff ∧ ∀ observer,
      |(quittingTerminalSemanticPair reward current).1 observer -
          (quittingTerminalSemanticPair reward
            (quittingFiniteCapProfileAt reward current mover cutoff)).1
              observer| < δ ∧
      |(quittingTerminalSemanticPair reward current).2 observer -
          (quittingTerminalSemanticPair reward
            (quittingFiniteCapProfileAt reward current mover cutoff)).2
              observer| < δ ∧
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward current) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingFiniteCapProfileAt reward current mover cutoff))
              observer| < δ := by
  obtain ⟨cutoff, hlower, hcutoff⟩ :=
    exists_finiteCap_all_terminalSemantics_close_of_pairDeleted_after
      reward current mover (current mover) hM hreward
      (tendsto_quittingMaxPairDeletedSurvivalWeight_zero_of_two_cappedPlayers
        reward source current mover first second hfirstSecond hfirstMover
          hsecondMover firstTime secondTime hfirstCap hsecondCap)
      lowerBound hδ
  refine ⟨cutoff, hlower, fun observer => ?_⟩
  simpa [quittingFiniteCapProfileAt, quittingTerminalSemanticPair] using
    hcutoff observer

/-- Compatibility two-sentinel extension without a requested prefix length. -/
theorem exists_quittingFiniteCapProfileAt_semantics_close_of_two_cappedPlayers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source current : (quittingGame reward).BehaviorProfile)
    (mover first second : ι)
    (hfirstSecond : first ≠ second)
    (hfirstMover : first ≠ mover) (hsecondMover : second ≠ mover)
    (firstTime secondTime : ℕ)
    (hfirstCap : current first =
      quittingStoppingLawFiniteCapBehaviorStrategy reward first
        (source first) firstTime)
    (hsecondCap : current second =
      quittingStoppingLawFiniteCapBehaviorStrategy reward second
        (source second) secondTime)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ cutoff, ∀ observer,
      |(quittingTerminalSemanticPair reward current).1 observer -
          (quittingTerminalSemanticPair reward
            (quittingFiniteCapProfileAt reward current mover cutoff)).1
              observer| < δ ∧
      |(quittingTerminalSemanticPair reward current).2 observer -
          (quittingTerminalSemanticPair reward
            (quittingFiniteCapProfileAt reward current mover cutoff)).2
              observer| < δ ∧
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward current) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingFiniteCapProfileAt reward current mover cutoff))
              observer| < δ := by
  obtain ⟨cutoff, hcutoff⟩ :=
    exists_finiteCap_all_terminalSemantics_close_of_pairDeleted
      reward current mover (current mover) hM hreward
      (tendsto_quittingMaxPairDeletedSurvivalWeight_zero_of_two_cappedPlayers
        reward source current mover first second hfirstSecond hfirstMover
          hsecondMover firstTime secondTime hfirstCap hsecondCap)
      hδ
  refine ⟨cutoff, fun observer => ?_⟩
  simpa [quittingFiniteCapProfileAt, quittingTerminalSemanticPair] using
    hcutoff observer

/-- **Two-seed global finite reduction.**  It is enough that two distinct
original players have zero `Never` mass.  Cap those two first.  They then act
as permanent sentinels, so every remaining player can be capped in turn even
when that player's original law has positive `Never` mass.

The final profile is coordinatewise a literal finite cap of the original
profile, while prescribed payoff, the full behavioral best-response envelope,
and every debt coordinate are uniformly as close as requested. -/
theorem exists_allPlayersFiniteCap_terminalSemantics_close_of_two_zeroNever_after
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (first second : ι) (hfirstSecond : first ≠ second)
    (hneverFirst : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile first)) = 0)
    (hneverSecond : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile second)) = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (lowerBound : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ capped : (quittingGame reward).BehaviorProfile,
      (∀ mover, ∃ cutoff,
        lowerBound ≤ cutoff ∧ capped mover =
          quittingStoppingLawFiniteCapBehaviorStrategy reward mover
            (profile mover) cutoff) ∧
      (∀ observer,
        |(quittingTerminalSemanticPair reward profile).1 observer -
            (quittingTerminalSemanticPair reward capped).1 observer| < δ ∧
        |(quittingTerminalSemanticPair reward profile).2 observer -
            (quittingTerminalSemanticPair reward capped).2 observer| < δ ∧
        |quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward profile) observer -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward capped) observer| < δ) := by
  classical
  let η : ℝ := δ / ((Fintype.card ι : ℝ) + 1)
  have hdenom : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have hη : 0 < η := div_pos hδ hdenom

  obtain ⟨firstTime, hfirstLate, hfirstStep⟩ :=
    exists_quittingFiniteCapProfileAt_semantics_close_of_neverMass_zero_after
      reward profile first hM hreward hneverFirst lowerBound hη
  let afterFirst :=
    quittingFiniteCapProfileAt reward profile first firstTime
  have hsecondAfterFirst : afterFirst second = profile second := by
    simp [afterFirst, quittingFiniteCapProfileAt,
      Function.update_of_ne hfirstSecond.symm]
  have hneverSecondAfterFirst : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (afterFirst second)) = 0 := by
    rw [hsecondAfterFirst]
    exact hneverSecond
  obtain ⟨secondTime, hsecondLate, hsecondStep⟩ :=
    exists_quittingFiniteCapProfileAt_semantics_close_of_neverMass_zero_after
      reward afterFirst second hM hreward hneverSecondAfterFirst lowerBound hη
  let seeded :=
    quittingFiniteCapProfileAt reward afterFirst second secondTime

  have hfirstSeeded : seeded first =
      quittingStoppingLawFiniteCapBehaviorStrategy reward first
        (profile first) firstTime := by
    simp [seeded, afterFirst, quittingFiniteCapProfileAt,
      Function.update_of_ne hfirstSecond]
  have hsecondSeeded : seeded second =
      quittingStoppingLawFiniteCapBehaviorStrategy reward second
        (profile second) secondTime := by
    simp [seeded, quittingFiniteCapProfileAt, hsecondAfterFirst]
  have hunseeded : ∀ mover, mover ≠ first → mover ≠ second →
      seeded mover = profile mover := by
    intro mover hmoverFirst hmoverSecond
    simp [seeded, afterFirst, quittingFiniteCapProfileAt,
      Function.update_of_ne hmoverSecond,
      Function.update_of_ne hmoverFirst]

  have hwithinFirst :
      QuittingTerminalSemanticsWithin reward profile afterFirst η := by
    intro observer
    have h := hfirstStep observer
    simpa [afterFirst] using
      ⟨le_of_lt h.1, le_of_lt h.2.1, le_of_lt h.2.2⟩
  have hwithinSecond :
      QuittingTerminalSemanticsWithin reward afterFirst seeded η := by
    intro observer
    have h := hsecondStep observer
    simpa [seeded] using
      ⟨le_of_lt h.1, le_of_lt h.2.1, le_of_lt h.2.2⟩
  have hseededClose :
      QuittingTerminalSemanticsWithin reward profile seeded (2 * η) := by
    simpa [two_mul] using
      QuittingTerminalSemanticsWithin.trans reward hwithinFirst hwithinSecond

  have hfinite : ∀ players : Finset ι,
      first ∉ players → second ∉ players →
      ∃ current : (quittingGame reward).BehaviorProfile,
        current first =
            quittingStoppingLawFiniteCapBehaviorStrategy reward first
              (profile first) firstTime ∧
        current second =
            quittingStoppingLawFiniteCapBehaviorStrategy reward second
              (profile second) secondTime ∧
        (∀ mover ∈ players, ∃ cutoff,
          lowerBound ≤ cutoff ∧ current mover =
            quittingStoppingLawFiniteCapBehaviorStrategy reward mover
              (profile mover) cutoff) ∧
        (∀ mover ∉ players, mover ≠ first → mover ≠ second →
          current mover = profile mover) ∧
        QuittingTerminalSemanticsWithin reward profile current
          (((players.card : ℝ) + 2) * η) := by
    intro players
    induction players using Finset.induction_on with
    | empty =>
        intro _ _
        refine ⟨seeded, hfirstSeeded, hsecondSeeded, ?_, ?_, ?_⟩
        · simp
        · simpa using hunseeded
        · simpa using hseededClose
    | @insert mover players hmover ih =>
        intro hfirstInsert hsecondInsert
        have hfirstOld : first ∉ players := by
          exact fun hmem => hfirstInsert (Finset.mem_insert_of_mem hmem)
        have hsecondOld : second ∉ players := by
          exact fun hmem => hsecondInsert (Finset.mem_insert_of_mem hmem)
        have hfirstMover : first ≠ mover := by
          intro heq
          subst mover
          exact hfirstInsert (Finset.mem_insert_self first players)
        have hsecondMover : second ≠ mover := by
          intro heq
          subst mover
          exact hsecondInsert (Finset.mem_insert_self second players)
        obtain ⟨current, hfirstCurrent, hsecondCurrent,
            hprocessed, hunprocessed, hcurrent⟩ :=
          ih hfirstOld hsecondOld
        have hmoverCurrent : current mover = profile mover :=
          hunprocessed mover hmover hfirstMover.symm hsecondMover.symm
        obtain ⟨cutoff, hcutoffLate, hstep⟩ :=
          exists_quittingFiniteCapProfileAt_semantics_close_of_two_cappedPlayers_after
            reward profile current mover first second hfirstSecond
              hfirstMover hsecondMover firstTime secondTime
              hfirstCurrent hsecondCurrent hM hreward lowerBound hη
        let next :=
          quittingFiniteCapProfileAt reward current mover cutoff
        refine ⟨next, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [next, quittingFiniteCapProfileAt,
            Function.update_of_ne hfirstMover] using hfirstCurrent
        · simpa [next, quittingFiniteCapProfileAt,
            Function.update_of_ne hsecondMover] using hsecondCurrent
        · intro player hplayer
          rcases Finset.mem_insert.mp hplayer with rfl | hplayerOld
          · refine ⟨cutoff, hcutoffLate, ?_⟩
            simp [next, quittingFiniteCapProfileAt, hmoverCurrent]
          · obtain ⟨oldCutoff, holdLate, hold⟩ :=
              hprocessed player hplayerOld
            refine ⟨oldCutoff, holdLate, ?_⟩
            have hplayerMover : player ≠ mover := by
              intro heq
              subst player
              exact hmover hplayerOld
            simpa [next, quittingFiniteCapProfileAt,
              Function.update_of_ne hplayerMover] using hold
        · intro player hplayer hplayerFirst hplayerSecond
          have hplayerOld : player ∉ players := by
            exact fun hmem => hplayer (Finset.mem_insert_of_mem hmem)
          have hplayerMover : player ≠ mover := by
            intro heq
            subst player
            exact hplayer (Finset.mem_insert_self mover players)
          simpa [next, quittingFiniteCapProfileAt,
            Function.update_of_ne hplayerMover] using
              hunprocessed player hplayerOld hplayerFirst hplayerSecond
        · have hstepWithin :
              QuittingTerminalSemanticsWithin reward current next η := by
            intro observer
            have h := hstep observer
            simpa [next] using
              ⟨le_of_lt h.1, le_of_lt h.2.1, le_of_lt h.2.2⟩
          have hcombined :=
            QuittingTerminalSemanticsWithin.trans reward hcurrent hstepWithin
          have hcard : (insert mover players).card = players.card + 1 :=
            Finset.card_insert_of_notMem hmover
          convert hcombined using 1
          rw [hcard]
          push_cast
          ring

  let remaining : Finset ι := (Finset.univ.erase first).erase second
  have hfirstRemaining : first ∉ remaining := by
    simp [remaining]
  have hsecondRemaining : second ∉ remaining := by
    simp [remaining]
  obtain ⟨capped, hfirstCapped, hsecondCapped,
      hprocessed, _hunprocessed, hclose⟩ :=
    hfinite remaining hfirstRemaining hsecondRemaining
  have hsecondMemAfterFirstErase : second ∈ Finset.univ.erase first :=
    Finset.mem_erase.mpr ⟨hfirstSecond.symm, Finset.mem_univ second⟩
  have hremainingCard : remaining.card + 2 = Fintype.card ι := by
    have hsecondErase :=
      Finset.card_erase_add_one hsecondMemAfterFirstErase
    have hfirstErase :=
      Finset.card_erase_add_one (Finset.mem_univ first)
    rw [Finset.card_univ] at hfirstErase
    dsimp [remaining]
    omega
  have htotal : ((remaining.card : ℝ) + 2) * η < δ := by
    have hremainingCardReal : (remaining.card : ℝ) + 2 =
        (Fintype.card ι : ℝ) := by
      exact_mod_cast hremainingCard
    rw [hremainingCardReal]
    calc
      (Fintype.card ι : ℝ) * η <
          ((Fintype.card ι : ℝ) + 1) * η := by
        exact mul_lt_mul_of_pos_right (by linarith) hη
      _ = δ := by
        dsimp [η]
        field_simp
  refine ⟨capped, ?_, ?_⟩
  · intro mover
    by_cases hmoverFirst : mover = first
    · subst mover
      exact ⟨firstTime, hfirstLate, hfirstCapped⟩
    by_cases hmoverSecond : mover = second
    · subst mover
      exact ⟨secondTime, hsecondLate, hsecondCapped⟩
    · exact hprocessed mover (by
        simp [remaining, hmoverFirst, hmoverSecond])
  · intro observer
    have h := hclose observer
    exact ⟨lt_of_le_of_lt h.1 htotal,
      lt_of_le_of_lt h.2.1 htotal,
      lt_of_le_of_lt h.2.2 htotal⟩

/-- Compatibility form of the two-seed global reduction without a requested
preserved prefix. -/
theorem exists_allPlayersFiniteCap_terminalSemantics_close_of_two_zeroNever
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (first second : ι) (hfirstSecond : first ≠ second)
    (hneverFirst : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile first)) = 0)
    (hneverSecond : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile second)) = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ capped : (quittingGame reward).BehaviorProfile,
      (∀ mover, ∃ cutoff,
        capped mover =
          quittingStoppingLawFiniteCapBehaviorStrategy reward mover
            (profile mover) cutoff) ∧
      (∀ observer,
        |(quittingTerminalSemanticPair reward profile).1 observer -
            (quittingTerminalSemanticPair reward capped).1 observer| < δ ∧
        |(quittingTerminalSemanticPair reward profile).2 observer -
            (quittingTerminalSemanticPair reward capped).2 observer| < δ ∧
        |quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward profile) observer -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward capped) observer| < δ) := by
  obtain ⟨capped, hcapped, hclose⟩ :=
    exists_allPlayersFiniteCap_terminalSemantics_close_of_two_zeroNever_after
      reward profile first second hfirstSecond hneverFirst hneverSecond
        hM hreward 0 hδ
  refine ⟨capped, ?_, hclose⟩
  intro mover
  obtain ⟨cutoff, _hlate, hcap⟩ := hcapped mover
  exact ⟨cutoff, hcap⟩

/-- **Finite-horizon approximate-Nash reduction from two seeds.**  Under the
same two-zero-Never hypothesis, every terminal `ε`-Nash profile has a literal
all-player finite cap which is terminal `(epsilon + 2 * δ)`-Nash.  The full
terminal semantics, including debt, remains within `δ`. -/
theorem exists_allPlayersFiniteCap_isεAsymptoticNash_of_two_zeroNever
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (first second : ι) (hfirstSecond : first ≠ second)
    (hneverFirst : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile first)) = 0)
    (hneverSecond : quittingHazardNeverMass
      (quittingBehaviorLiveHazard reward (profile second)) = 0)
    {ε M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ capped : (quittingGame reward).BehaviorProfile,
      (∀ mover, ∃ cutoff,
        capped mover =
          quittingStoppingLawFiniteCapBehaviorStrategy reward mover
            (profile mover) cutoff) ∧
      QuittingTerminalSemanticsWithin reward profile capped δ ∧
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (ε + 2 * δ) capped := by
  obtain ⟨capped, hcapped, hclose⟩ :=
    exists_allPlayersFiniteCap_terminalSemantics_close_of_two_zeroNever
      reward profile first second hfirstSecond hneverFirst hneverSecond
        hM hreward hδ
  have hwithin :
      QuittingTerminalSemanticsWithin reward profile capped δ := by
    intro observer
    have h := hclose observer
    exact ⟨le_of_lt h.1, le_of_lt h.2.1, le_of_lt h.2.2⟩
  exact ⟨capped, hcapped, hwithin,
    isεAsymptoticNash_of_terminalSemanticsWithin
      reward profile capped hM hreward hnash hwithin⟩

end GameTheory
