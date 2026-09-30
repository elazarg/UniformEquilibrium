import UniformEquilibrium.Quitting.Stationary.OneSidedWeakUnitRawGuards
import UniformEquilibrium.Quitting.Stationary.SureOwnerJoiningRoot
import UniformEquilibrium.Quitting.Punishment.InstantPunishment
import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.AmbientCarrierElimination
import UniformEquilibrium.Quitting.Classification.LCP.NormalCorePunishmentNormal

/-! # Matrix-free uniform payoffs from one-sided weak unit-ceiling guards -/

noncomputable section

namespace GameTheory

open QuittingLCPClassification ThreeCoreAmbientCarrierElimination

/-- The owner has a nonnegative quitting displacement on the passive-zero
face with an active outsider; the passive player's displacement is nonpositive
on the owner-one face. -/
structure QuittingOneSidedWeakUnitGuards
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner passive : Fin 4) : Prop where
  lower : ∀ hazard,
    (∀ who, 0 ≤ hazard who ∧ hazard who ≤ 1) → hazard passive = 0 →
    quittingCrossedOutsiderPositive owner passive hazard →
    0 ≤ quittingDiscountedDisplacement reward 0 hazard owner
  upper : ∀ hazard,
    (∀ who, 0 ≤ hazard who ∧ hazard who ≤ 1) → hazard owner = 1 →
    quittingDiscountedDisplacement reward 0 hazard passive ≤ 0

/-- Exactly the twelve weak owner lower comparisons and four weak passive
joining comparisons, for any ordered distinct pair of four players. -/
structure QuittingOneSidedWeakUnitRawGuards
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner passive : Fin 4) : Prop where
  lower : QuittingCrossedWeakLowerRanking reward owner passive
  upper : QuittingWeakUnitJoining reward passive owner

/-- The sixteen finite comparisons supply both original polynomial guards. -/
theorem oneSidedWeakUnitGuards_of_raw
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner passive : Fin 4) (hdistinct : owner ≠ passive)
    (hraw : QuittingOneSidedWeakUnitRawGuards reward owner passive) :
    QuittingOneSidedWeakUnitGuards reward owner passive := by
  constructor
  · intro hazard hbox hzero _
    exact quittingDisplacement_partner_zero_nonneg_of_weakLowerRanking reward hazard
      owner passive hdistinct.symm hzero (fun who _ => hbox who) hraw.lower
  · intro hazard hbox hone
    exact quittingDisplacement_partner_one_nonpos_of_weakUnitJoining reward hazard
      passive owner hdistinct hone (fun who _ => hbox who) hraw.upper

private theorem displacement_sureSolo_eq_collision_sub_solo
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hazard : Fin 4 → ℝ) (owner who : Fin 4) (hwho : who ≠ owner)
    (howner : hazard owner = 1) (hothers : ∀ other, other ≠ owner → hazard other = 0) :
    quittingDiscountedDisplacement reward 0 hazard who =
      quittingSingletonCollisionReward reward owner who - quittingSoloReward reward owner who := by
  have hrow : hazard = hazardOfRoot (quittingInstantRoot owner) := by
    funext coordinate
    by_cases hcoordinate : coordinate = owner
    · subst coordinate
      simp [hazardOfRoot, quittingInstantRoot, quittingSoloStationaryRoot, howner]
    · simp [hazardOfRoot, quittingInstantRoot, quittingSoloStationaryRoot,
        hcoordinate, hothers coordinate hcoordinate]
  have hgain := stationaryGain_rootOfHazard_eq_faceNumerator reward
    (hazardOfRoot (quittingInstantRoot owner))
    (hazardOfRoot_nonneg _) (hazardOfRoot_le_one _) who
  rw [rootOfHazard_hazardOfRoot] at hgain
  have hdisplacement : quittingDiscountedDisplacement reward 0 hazard who =
      quittingStationaryGain reward (quittingInstantRoot owner) who := by
    simpa [hrow, quittingDiscountedDisplacement, quittingFaceNumerator] using hgain.symm
  rw [hdisplacement]
  unfold quittingStationaryGain quittingInstantRoot
  rw [quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix reward hwho,
    quittingStationaryFixedOpponentsContinueReward_solo_other reward hwho,
    quittingStationaryFixedOpponentsContinueMass_solo_other hwho]
  simp

/-- The joining-game root either yields an exact contracting stationary
equilibrium or yields every outsider no-join inequality for the sure owner. -/
theorem stationaryTerminalNash_or_instantNoJoin_of_oneSidedWeakUnitGuards
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner passive : Fin 4) (hdistinct : owner ≠ passive)
    (hguards : QuittingOneSidedWeakUnitGuards reward owner passive) :
    (∃ root : Fin 4 → PMF Bool, ∃ value : Payoff (Fin 4),
      (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (quittingStationaryProfile reward root) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none value) ∨
    IsQuittingInstantNoJoin reward owner := by
  obtain ⟨hazard, hzero, hone, howner, hpassive, houtsiders⟩ :=
    exists_quittingSureOwnerJoiningRoot reward owner passive hdistinct
  have hbox : ∀ who, 0 ≤ hazard who ∧ hazard who ≤ 1 :=
    fun who => ⟨hzero who, hone who⟩
  by_cases hactive : quittingCrossedOutsiderPositive owner passive hazard
  · left
    have hsign : ∀ who,
        (hazard who = 0 → quittingDiscountedDisplacement reward 0 hazard who ≤ 0) ∧
        (0 < hazard who → hazard who < 1 →
          quittingDiscountedDisplacement reward 0 hazard who = 0) ∧
        (hazard who = 1 → 0 ≤ quittingDiscountedDisplacement reward 0 hazard who) := by
      intro who
      by_cases hwhoOwner : who = owner
      · subst who
        refine ⟨?_, ?_, fun _ => hguards.lower hazard hbox hpassive hactive⟩
        · intro h
          rw [howner] at h
          norm_num at h
        · intro _ h
          rw [howner] at h
          norm_num at h
      by_cases hwhoPassive : who = passive
      · subst who
        refine ⟨fun _ => hguards.upper hazard hbox howner, ?_, ?_⟩
        · intro h _
          rw [hpassive] at h
          norm_num at h
        · intro h
          rw [hpassive] at h
          norm_num at h
      exact houtsiders who hwhoOwner hwhoPassive
    have hfixed := (quittingDiscountedClippedMap_eq_self_iff reward 0 hazard hzero hone).mpr
      hsign
    have hnonzero : hazard ≠ 0 := by
      intro heq
      have h := congrFun heq owner
      simp [howner] at h
    obtain ⟨root, value, hrootHazard, habsorption, -, hbellman, hendpoint⟩ :=
      stationaryEndpointCertificate_of_nonzero_clippedMap_fixed
        reward hazard hzero hone hnonzero hfixed
    obtain ⟨outsider, houtOwner, houtPassive, houtPositive⟩ := hactive
    have hownerPositive : 0 < (root owner true).toReal := by
      change 0 < hazardOfRoot root owner
      rw [hrootHazard, howner]
      norm_num
    have houtRate : 0 < (root outsider true).toReal := by
      change 0 < hazardOfRoot root outsider
      rw [hrootHazard]
      exact houtPositive
    have hcontracts : ∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1 := by
      intro who
      by_cases hwho : who = owner
      · subst who
        exact quittingStationaryFixedOpponentsContinueMass_lt_one_of_opponent_quit
          root houtOwner houtRate
      · exact quittingStationaryFixedOpponentsContinueMass_lt_one_of_opponent_quit
          root (Ne.symm hwho) hownerPositive
    have habsorbs : quittingStationaryContinueMass root < 1 := by
      unfold quittingRootAbsorptionMass at habsorption
      linarith
    exact ⟨root, value, hcontracts,
      isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts
        reward root value habsorbs hbellman hendpoint hcontracts,
      isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
        reward root value habsorbs hbellman hendpoint hcontracts⟩
  · right
    have hothers : ∀ who, who ≠ owner → hazard who = 0 := by
      intro who hwho
      by_cases hp : who = passive
      · simpa [hp] using hpassive
      have hnonpositive : hazard who ≤ 0 := by
        by_contra hnot
        exact hactive ⟨who, hwho, hp, lt_of_not_ge hnot⟩
      exact le_antisymm hnonpositive (hzero who)
    intro who hwho
    have hsign : quittingDiscountedDisplacement reward 0 hazard who ≤ 0 := by
      by_cases hp : who = passive
      · subst who
        exact hguards.upper hazard hbox howner
      · exact (houtsiders who hwho hp).1 (hothers who hwho)
    rw [displacement_sureSolo_eq_collision_sub_solo reward hazard owner who
      hwho howner hothers] at hsign
    exact sub_nonpos.mp hsign

/-- In the nonnegative sole-owner branch the sure-solo profile is exact terminal
Nash, and its fixed singleton payoff is a uniform-equilibrium payoff. -/
theorem stationaryTerminalNash_sureSolo_of_nonnegative_noJoin
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (owner : Fin 4)
    (howner : 0 ≤ quittingSoloReward reward owner owner)
    (hnoJoin : IsQuittingInstantNoJoin reward owner) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward (quittingInstantRoot owner)) ∧
    (quittingGame reward).IsUniformEquilibriumPayoff none (quittingSoloReward reward owner) := by
  have hnash := isεAsymptoticNash_soloStationary_exact reward owner (PMF.pure true)
    (by simp) howner (by simpa [IsQuittingInstantNoJoin] using hnoJoin)
  have hpayoff : quittingTerminalPayoff reward
      (quittingStationaryProfile reward (quittingInstantRoot owner)) =
        quittingSoloReward reward owner := by
    funext who
    exact quittingTerminalPayoff_soloStationary reward owner who (PMF.pure true) (by simp)
  refine ⟨hnash, ?_⟩
  rw [← hpayoff]
  exact quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact reward _ hnash

/-- Signed Fin4 no-join completion uses the original no-UE punishment theorem.
It neither assumes a punishment plan nor asserts that the UE target must be solo. -/
theorem exists_uniformPayoff_of_finFour_instantNoJoin
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (owner : Fin 4)
    (hnoJoin : IsQuittingInstantNoJoin reward owner) :
    ∃ value : Payoff (Fin 4), (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  by_contra hnot
  have hcore := normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
    reward (by norm_num) hnot
  have hnormal := all_punishmentNormal_of_normalCore_eq_univ reward hcore owner
  have hIR : IsQuittingInstantPunishmentIR reward owner := by
    exact hnormal
  exact hnot ⟨quittingSoloReward reward owner,
    isUniformEquilibriumPayoff_soloReward_of_instantPunishment reward owner hIR hnoJoin⟩

/-- Literal weak one-sided polynomial guards produce one fixed original-game
uniform payoff without any matrix restriction or supplied strategic witness. -/
theorem exists_uniformPayoff_of_oneSidedWeakUnitGuards
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner passive : Fin 4) (hdistinct : owner ≠ passive)
    (hguards : QuittingOneSidedWeakUnitGuards reward owner passive) :
    ∃ value : Payoff (Fin 4), (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  rcases stationaryTerminalNash_or_instantNoJoin_of_oneSidedWeakUnitGuards
    reward owner passive hdistinct hguards with ⟨root, value, -, -, hUE⟩ | hnoJoin
  · exact ⟨value, hUE⟩
  · exact exists_uniformPayoff_of_finFour_instantNoJoin reward owner hnoJoin

/-- Sixteen weak reward comparisons alone produce an original Fin4 UE payoff.
Singleton rewards may have arbitrary signs; no inverse or degree test appears. -/
theorem exists_uniformPayoff_of_oneSidedWeakUnitRawGuards
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner passive : Fin 4) (hdistinct : owner ≠ passive)
    (hraw : QuittingOneSidedWeakUnitRawGuards reward owner passive) :
    ∃ value : Payoff (Fin 4), (quittingGame reward).IsUniformEquilibriumPayoff none value :=
  exists_uniformPayoff_of_oneSidedWeakUnitGuards reward owner passive hdistinct
    (oneSidedWeakUnitGuards_of_raw reward owner passive hdistinct hraw)

end GameTheory
