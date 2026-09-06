import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card

/-!
# Finite coalition support peeling and player rankings

A finite coalition relation can be peeled support by support exactly when the
players admit a full ranking such that every related coalition contains a
strictly earlier player.  The ranking concerns labels, not time.
-/

namespace MathUE

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every nonempty support contains a member unrelated to every coalition
inside that support which contains that member. -/
def HasFiniteCoalitionSupportPeeling
    (positive : ι → Finset ι → Prop) : Prop :=
  ∀ active : Finset ι, active.Nonempty →
    ∃ chosen ∈ active, ∀ coalition : Finset ι,
      coalition ⊆ active → chosen ∈ coalition → ¬positive chosen coalition

/-- A full bounded injective player rank such that every related coalition
contains a strictly earlier-ranked member. -/
def HasFiniteCoalitionPlayerRanking
    (positive : ι → Finset ι → Prop) : Prop :=
  ∃ rank : ι → ℕ, Function.Injective rank ∧
    (∀ player, rank player < Fintype.card ι) ∧
    ∀ player (coalition : Finset ι), player ∈ coalition →
      positive player coalition →
        ∃ earlier ∈ coalition, rank earlier < rank player

/-- Recursive support peeling produces a full bounded injective rank. -/
theorem hasFiniteCoalitionPlayerRanking_of_supportPeeling
    (positive : ι → Finset ι → Prop)
    (hpeel : HasFiniteCoalitionSupportPeeling positive) :
    HasFiniteCoalitionPlayerRanking positive := by
  have build : ∀ active : Finset ι,
      ∃ rank : ι → ℕ,
        (∀ first ∈ active, ∀ second ∈ active,
          rank first = rank second → first = second) ∧
        (∀ player ∈ active, rank player < active.card) ∧
        ∀ player ∈ active, ∀ coalition : Finset ι,
          coalition ⊆ active → player ∈ coalition →
          positive player coalition →
            ∃ earlier ∈ coalition, rank earlier < rank player :=
    Finset.strongInduction fun active ih => by
      by_cases hactive : active.Nonempty
      · obtain ⟨chosen, hchosen, hchosenFree⟩ := hpeel active hactive
        let remaining := active.erase chosen
        have hremaining : remaining ⊂ active := Finset.erase_ssubset hchosen
        obtain ⟨oldRank, holdInjective, holdBound, holdPositive⟩ :=
          ih remaining hremaining
        let rank : ι → ℕ := fun player =>
          if player = chosen then 0 else oldRank player + 1
        refine ⟨rank, ?_, ?_, ?_⟩
        · intro first hfirst second hsecond hrank
          by_cases hfirstChosen : first = chosen
          · subst first
            by_contra hsecondChosen
            have hsecondNe : second ≠ chosen := fun heq =>
              hsecondChosen heq.symm
            simp only [rank, if_pos rfl, if_neg hsecondNe] at hrank
            omega
          · by_cases hsecondChosen : second = chosen
            · subst second
              simp [rank, hfirstChosen] at hrank
            · simp only [rank, if_neg hfirstChosen,
                if_neg hsecondChosen] at hrank
              apply holdInjective first
                (Finset.mem_erase.mpr ⟨hfirstChosen, hfirst⟩) second
                (Finset.mem_erase.mpr ⟨hsecondChosen, hsecond⟩)
              omega
        · intro player hplayer
          by_cases hplayerChosen : player = chosen
          · subst player
            simp only [rank, if_pos]
            exact Finset.card_pos.mpr hactive
          · have hold := holdBound player
              (Finset.mem_erase.mpr ⟨hplayerChosen, hplayer⟩)
            have hcard := Finset.card_erase_of_mem hchosen
            simp only [rank, if_neg hplayerChosen]
            dsimp only [remaining] at hold
            omega
        · intro player hplayer coalition hsubset hplayerCoalition hpositive
          by_cases hplayerChosen : player = chosen
          · subst player
            exact (hchosenFree coalition hsubset hplayerCoalition hpositive).elim
          · by_cases hchosenCoalition : chosen ∈ coalition
            · refine ⟨chosen, hchosenCoalition, ?_⟩
              simp [rank, hplayerChosen]
            · have hcoalitionRemaining : coalition ⊆ remaining := by
                intro member hmember
                exact Finset.mem_erase.mpr
                  ⟨fun heq => hchosenCoalition (heq ▸ hmember),
                    hsubset hmember⟩
              obtain ⟨earlier, hearlier, hearlierRank⟩ :=
                holdPositive player
                  (Finset.mem_erase.mpr ⟨hplayerChosen, hplayer⟩)
                  coalition hcoalitionRemaining hplayerCoalition hpositive
              refine ⟨earlier, hearlier, ?_⟩
              have hearlierChosen : earlier ≠ chosen := fun heq =>
                hchosenCoalition (heq ▸ hearlier)
              simp only [rank, if_neg hearlierChosen,
                if_neg hplayerChosen]
              omega
      · have hempty : active = ∅ := Finset.not_nonempty_iff_eq_empty.mp hactive
        subst active
        exact ⟨fun _ => 0, by simp, by simp, by simp⟩
  obtain ⟨rank, hrankInjective, hrankBound, hrankPositive⟩ :=
    build (Finset.univ : Finset ι)
  refine ⟨rank, ?_, ?_, ?_⟩
  · intro first second hrank
    exact hrankInjective first (Finset.mem_univ first) second
      (Finset.mem_univ second) hrank
  · intro player
    simpa using hrankBound player (Finset.mem_univ player)
  · intro player coalition hplayer hpositive
    exact hrankPositive player (Finset.mem_univ player) coalition
      (Finset.subset_univ coalition) hplayer hpositive

omit [DecidableEq ι] in
/-- The least-ranked member of each support is peelable. -/
theorem hasFiniteCoalitionSupportPeeling_of_playerRanking
    (positive : ι → Finset ι → Prop)
    (hranking : HasFiniteCoalitionPlayerRanking positive) :
    HasFiniteCoalitionSupportPeeling positive := by
  obtain ⟨rank, _hrankInjective, _hrankBound, hpositive⟩ := hranking
  intro active hactive
  obtain ⟨chosen, hchosen, hminimal⟩ :=
    Finset.exists_min_image active rank hactive
  refine ⟨chosen, hchosen, ?_⟩
  intro coalition hsubset hchosenCoalition hrelation
  obtain ⟨earlier, hearlierCoalition, hearlierRank⟩ :=
    hpositive chosen coalition hchosenCoalition hrelation
  have hchosenLe : rank chosen ≤ rank earlier :=
    hminimal earlier (hsubset hearlierCoalition)
  omega

/-- Finite support peeling is equivalent to a full player ranking. -/
theorem finiteCoalitionSupportPeeling_iff_playerRanking
    (positive : ι → Finset ι → Prop) :
    HasFiniteCoalitionSupportPeeling positive ↔
      HasFiniteCoalitionPlayerRanking positive := by
  constructor
  · exact hasFiniteCoalitionPlayerRanking_of_supportPeeling positive
  · exact hasFiniteCoalitionSupportPeeling_of_playerRanking positive

end MathUE
