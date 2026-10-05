import UniformEquilibrium.Quitting.Classification.CommonQuittingPremiumLeaver

/-! # Support-specific protected leavers with signed rewards

The protected leaver is selected from the actual premium trap, not from the
greatest core alone. Protected successor floors hold at every annotation;
return to a singleton sublevel additionally requires protected source floors.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def HasProtectedParticipantPremiums
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (protectedPlayers : Finset ι) : Prop :=
  ∀ player ∈ protectedPlayers, ∀ terminal, player ∈ terminal.val →
    reward (quittingSingletonTerminal player) player ≤ reward terminal player

/-- The comparison parameter is strict for analytic exclusion and weak for
reward closure. All nonempty opponent coalitions inside the actual trap occur. -/
def HasSupportSpecificQuittingLeavers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (protectedPlayers : Finset ι)
    (compare : ℝ → ℝ → Prop) : Prop :=
  ∀ active, IsQuittingPremiumTrap reward active →
    ∃ player ∈ active, player ∈ protectedPlayers ∧
      ∀ (coalition : Finset ι) (hnonempty : coalition.Nonempty),
        coalition ⊆ active.erase player →
          compare (reward ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player)
            (reward ⟨coalition, hnonempty⟩ player)

/-- The full boxed protected region; unprotected coordinates may be signed. -/
def quittingProtectedSetBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (protectedPlayers : Finset ι) : Set (Payoff ι) :=
  Icc (fun _ => -bound) (fun _ => bound) ∩
    {point | ∀ player ∈ protectedPlayers, quittingSoloReward reward player player ≤ point player}

/-- One fixed return region for all supports and root selections. -/
def quittingProtectedSetSublevelDomain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (protectedPlayers : Finset ι) : Set (Payoff ι) :=
  quittingProtectedSetBox reward bound protectedPlayers ∩
    {point | ∃ player, point player ≤ quittingSoloReward reward player player}

/-- Protected successor floors do not require protected floors at the source. -/
theorem exactRootSuccessor_protectedSet_floor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (protectedPlayers : Finset ι)
    (hpremiums : HasProtectedParticipantPremiums reward protectedPlayers)
    (tail : Payoff ι) (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (player : ι) (hplayer : player ∈ protectedPlayers) :
    reward (quittingSingletonTerminal player) player ≤
      quittingRootSuccessorPayoff reward tail root player :=
  (singleton_le_rootQuitPayoff_of_nonnegativeParticipantPremium
    reward player (hpremiums player hplayer) tail root).trans
      (quittingRootQuitPayoff_le_successor_of_isZeroNash reward tail root player hnash)

theorem not_premiumTrap_support_of_supportSpecific_strictLeave
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (protectedPlayers : Finset ι)
    (hleavers : HasSupportSpecificQuittingLeavers reward protectedPlayers (· < ·))
    (tail : Payoff ι)
    (hfloor : ∀ player ∈ protectedPlayers,
      reward (quittingSingletonTerminal player) player ≤ tail player)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root) :
    ¬IsQuittingPremiumTrap reward (quittingPositiveHazardSupport root) := by
  intro htrap
  obtain ⟨player, hplayer, hprotected, hleave⟩ := hleavers _ htrap
  exact not_isZeroNash_of_premiumTrapSupport_strictLeave reward player tail root
    htrap hplayer hleave (hfloor player hprotected) hnash

/-- Signed support-specific return is protected floors plus some sublevel,
not full singleton floors and not an equality at the sublevel coordinate. -/
theorem exactRootSuccessor_protectedSet_sublevel_of_supportSpecific_strictLeave
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (protectedPlayers : Finset ι)
    (hpremiums : HasProtectedParticipantPremiums reward protectedPlayers)
    (hleavers : HasSupportSpecificQuittingLeavers reward protectedPlayers (· < ·))
    (tail : Payoff ι)
    (hfloor : ∀ player ∈ protectedPlayers,
      reward (quittingSingletonTerminal player) player ≤ tail player)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (hpositive : 0 < quittingRootAbsorptionMass root) :
    (∀ player ∈ protectedPlayers, reward (quittingSingletonTerminal player) player ≤
        quittingRootSuccessorPayoff reward tail root player) ∧
      ∃ player, quittingRootSuccessorPayoff reward tail root player ≤
        reward (quittingSingletonTerminal player) player := by
  refine ⟨fun player hplayer => exactRootSuccessor_protectedSet_floor reward
    protectedPlayers hpremiums tail root hnash player hplayer, ?_⟩
  exact exists_successor_le_singleton_of_exactRoot_nontrap_support reward tail root hnash
    hpositive (not_premiumTrap_support_of_supportSpecific_strictLeave reward
      protectedPlayers hleavers tail hfloor root hnash)

/-- Every boxed source has successor in the protected box, even when its
protected coordinates start below their singleton rewards. -/
theorem exactRootSuccessor_mem_protectedSetBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (protectedPlayers : Finset ι)
    (hpremiums : HasProtectedParticipantPremiums reward protectedPlayers)
    (bound : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (tail : Payoff ι) (hbox : ∀ player, |tail player| ≤ bound)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root) :
    quittingRootSuccessorPayoff reward tail root ∈
      quittingProtectedSetBox reward bound protectedPlayers := by
  refine ⟨⟨fun player => ?_, fun player => ?_⟩, ?_⟩
  · exact (abs_le.mp (abs_quittingRootSuccessorPayoff_le_bound
      reward tail root player hreward hbox)).1
  · exact (abs_le.mp (abs_quittingRootSuccessorPayoff_le_bound
      reward tail root player hreward hbox)).2
  · exact fun player hplayer => exactRootSuccessor_protectedSet_floor
      reward protectedPlayers hpremiums tail root hnash player hplayer

/-- The absorbing return to the sublevel domain requires protected source
floors. It is not asserted at arbitrary boxed protected-floor violations. -/
theorem exactRootSuccessor_mem_protectedSetSublevelDomain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (protectedPlayers : Finset ι)
    (hpremiums : HasProtectedParticipantPremiums reward protectedPlayers)
    (hleavers : HasSupportSpecificQuittingLeavers reward protectedPlayers (· < ·))
    (bound : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (tail : Payoff ι) (htail : tail ∈ quittingProtectedSetBox reward bound protectedPlayers)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (hpositive : 0 < quittingRootAbsorptionMass root) :
    quittingRootSuccessorPayoff reward tail root ∈
      quittingProtectedSetSublevelDomain reward bound protectedPlayers := by
  refine ⟨exactRootSuccessor_mem_protectedSetBox reward protectedPlayers hpremiums bound
    hreward tail (fun player => abs_le.mpr ⟨htail.1.1 player, htail.1.2 player⟩)
    root hnash, ?_⟩
  exact (exactRootSuccessor_protectedSet_sublevel_of_supportSpecific_strictLeave reward
    protectedPlayers hpremiums hleavers tail htail.2 root hnash hpositive).2

/-- The finite maximal protected set depends only on participant rewards. -/
def quittingMaximalProtectedPlayers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun player => ∀ terminal, player ∈ terminal.val →
    reward (quittingSingletonTerminal player) player ≤ reward terminal player

theorem mem_quittingMaximalProtectedPlayers_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι) :
    player ∈ quittingMaximalProtectedPlayers reward ↔
      ∀ terminal, player ∈ terminal.val →
        reward (quittingSingletonTerminal player) player ≤ reward terminal player := by
  classical
  simp [quittingMaximalProtectedPlayers]

theorem hasProtectedParticipantPremiums_iff_subset_maximalProtectedPlayers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (protectedPlayers : Finset ι) :
    HasProtectedParticipantPremiums reward protectedPlayers ↔
      protectedPlayers ⊆ quittingMaximalProtectedPlayers reward := by
  constructor
  · intro hpremiums player hplayer
    exact (mem_quittingMaximalProtectedPlayers_iff reward player).2 (hpremiums player hplayer)
  · intro hsubset player hplayer
    exact (mem_quittingMaximalProtectedPlayers_iff reward player).1 (hsubset hplayer)

omit [Fintype ι] in
theorem HasSupportSpecificQuittingLeavers.mono
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {small large : Finset ι} {compare : ℝ → ℝ → Prop}
    (hleavers : HasSupportSpecificQuittingLeavers reward small compare) (hsubset : small ⊆ large) :
    HasSupportSpecificQuittingLeavers reward large compare := by
  intro active htrap
  obtain ⟨player, hplayer, hprotected, hleave⟩ := hleavers active htrap
  exact ⟨player, hplayer, hsubset hprotected, hleave⟩

/-- Exact finite raw-test packaging. The admissible protected set is explicitly
nonempty, even though the raw return lemmas also permit an empty set. The same
equivalence applies to strict and weak comparisons without an extra order premise. -/
theorem exists_nonempty_protectedSet_iff_maximalProtectedPlayers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (compare : ℝ → ℝ → Prop) :
    (∃ protectedPlayers : Finset ι, protectedPlayers.Nonempty ∧
      HasProtectedParticipantPremiums reward protectedPlayers ∧
      HasSupportSpecificQuittingLeavers reward protectedPlayers compare) ↔
      (quittingMaximalProtectedPlayers reward).Nonempty ∧
        HasSupportSpecificQuittingLeavers reward
          (quittingMaximalProtectedPlayers reward) compare := by
  constructor
  · rintro ⟨protectedPlayers, hnonempty, hpremiums, hleavers⟩
    have hsubset := (hasProtectedParticipantPremiums_iff_subset_maximalProtectedPlayers
      reward protectedPlayers).1 hpremiums
    exact ⟨hnonempty.mono hsubset, hleavers.mono hsubset⟩
  · rintro ⟨hnonempty, hleavers⟩
    exact ⟨quittingMaximalProtectedPlayers reward, hnonempty,
      (hasProtectedParticipantPremiums_iff_subset_maximalProtectedPlayers
        reward (quittingMaximalProtectedPlayers reward)).2 Finset.Subset.rfl, hleavers⟩

end GameTheory
