import Research.Quitting.FinFourProducerAtlas.MovingMarkedPairSupportContractedRenewal

/-!
# One-way reset-rigid producer rank

This is the literal finite phase rank for the reset-rigid escape lane.  Its
constructors describe only the one-way transitions of that lane; it is not a
rank on arbitrary atlas edges.  Terminal exits have no outgoing constructor.
-/

noncomputable section

namespace GameTheory

/-- One state in the one-way reset-rigid producer lane.  Every live state
stores a positive-debt support known to be nonempty. -/
inductive FinFourResetRigidProducerState : Type
  | exit
  | tangentMinimum
      (point : QuittingTerminalSemanticLawPoint (Fin 4))
      (support_nonempty : (quittingPositiveDebtSupport point.1).Nonempty)
  | singletonMinimum
      (point : QuittingTerminalSemanticLawPoint (Fin 4))
      (support_nonempty : (quittingPositiveDebtSupport point.1).Nonempty)
  | productMinimum
      (point : QuittingTerminalSemanticLawPoint (Fin 4))
      (support_nonempty : (quittingPositiveDebtSupport point.1).Nonempty)
  | escapeOrigin
      (point : QuittingTerminalSemanticLawPoint (Fin 4))
      (support_nonempty : (quittingPositiveDebtSupport point.1).Nonempty)

namespace FinFourResetRigidProducerState

/-- The support cardinality attached to a live producer state. -/
def supportCard : FinFourResetRigidProducerState → ℕ
  | .exit => 0
  | .tangentMinimum point _ => (quittingPositiveDebtSupport point.1).card
  | .singletonMinimum point _ => (quittingPositiveDebtSupport point.1).card
  | .productMinimum point _ => (quittingPositiveDebtSupport point.1).card
  | .escapeOrigin point _ => (quittingPositiveDebtSupport point.1).card

/-- The packet's phase offsets use base five, strictly above every Fin4
support cardinality. -/
def rank : FinFourResetRigidProducerState → ℕ
  | .exit => 0
  | .tangentMinimum point _ => (quittingPositiveDebtSupport point.1).card
  | .singletonMinimum point _ => 5 + (quittingPositiveDebtSupport point.1).card
  | .productMinimum point _ => 10 + (quittingPositiveDebtSupport point.1).card
  | .escapeOrigin point _ => 15 + (quittingPositiveDebtSupport point.1).card

theorem supportCard_le_four (state : FinFourResetRigidProducerState) :
    state.supportCard ≤ 4 := by
  cases state with
  | exit => simp [supportCard]
  | tangentMinimum point _ =>
      change (quittingPositiveDebtSupport point.1).card ≤ 4
      simpa using (Finset.card_le_univ (quittingPositiveDebtSupport point.1))
  | singletonMinimum point _ =>
      change (quittingPositiveDebtSupport point.1).card ≤ 4
      simpa using (Finset.card_le_univ (quittingPositiveDebtSupport point.1))
  | productMinimum point _ =>
      change (quittingPositiveDebtSupport point.1).card ≤ 4
      simpa using (Finset.card_le_univ (quittingPositiveDebtSupport point.1))
  | escapeOrigin point _ =>
      change (quittingPositiveDebtSupport point.1).card ≤ 4
      simpa using (Finset.card_le_univ (quittingPositiveDebtSupport point.1))

theorem supportCard_pos
    {state : FinFourResetRigidProducerState} (hne : state ≠ .exit) :
    0 < state.supportCard := by
  cases state with
  | exit => exact (hne rfl).elim
  | tangentMinimum _ hnonempty =>
      simpa [supportCard] using Finset.card_pos.mpr hnonempty
  | singletonMinimum _ hnonempty =>
      simpa [supportCard] using Finset.card_pos.mpr hnonempty
  | productMinimum _ hnonempty =>
      simpa [supportCard] using Finset.card_pos.mpr hnonempty
  | escapeOrigin _ hnonempty =>
      simpa [supportCard] using Finset.card_pos.mpr hnonempty

end FinFourResetRigidProducerState

/-- Exactly the permitted one-way transitions of the reset-rigid producer
lane.  There is no constructor leaving `exit` or returning to an earlier
phase. -/
inductive FinFourResetRigidProducerTransition :
    FinFourResetRigidProducerState → FinFourResetRigidProducerState → Prop
  | escapeToProduct
      (origin product : QuittingTerminalSemanticLawPoint (Fin 4))
      (horigin : (quittingPositiveDebtSupport origin.1).Nonempty)
      (hproduct : (quittingPositiveDebtSupport product.1).Nonempty) :
      FinFourResetRigidProducerTransition
        (.escapeOrigin origin horigin) (.productMinimum product hproduct)
  | escapeToExit
      (origin : QuittingTerminalSemanticLawPoint (Fin 4))
      (horigin : (quittingPositiveDebtSupport origin.1).Nonempty) :
      FinFourResetRigidProducerTransition (.escapeOrigin origin horigin) .exit
  | productToSingleton
      (product singleton : QuittingTerminalSemanticLawPoint (Fin 4))
      (hproduct : (quittingPositiveDebtSupport product.1).Nonempty)
      (hsingleton : (quittingPositiveDebtSupport singleton.1).Nonempty) :
      FinFourResetRigidProducerTransition
        (.productMinimum product hproduct) (.singletonMinimum singleton hsingleton)
  | productToExit
      (product : QuittingTerminalSemanticLawPoint (Fin 4))
      (hproduct : (quittingPositiveDebtSupport product.1).Nonempty) :
      FinFourResetRigidProducerTransition (.productMinimum product hproduct) .exit
  | singletonToTangent
      (singleton tangent : QuittingTerminalSemanticLawPoint (Fin 4))
      (hsingleton : (quittingPositiveDebtSupport singleton.1).Nonempty)
      (htangent : (quittingPositiveDebtSupport tangent.1).Nonempty)
      (hstrict : quittingPositiveDebtSupport tangent.1 ⊂
        quittingPositiveDebtSupport singleton.1) :
      FinFourResetRigidProducerTransition
        (.singletonMinimum singleton hsingleton) (.tangentMinimum tangent htangent)
  | singletonToExit
      (singleton : QuittingTerminalSemanticLawPoint (Fin 4))
      (hsingleton : (quittingPositiveDebtSupport singleton.1).Nonempty) :
      FinFourResetRigidProducerTransition
        (.singletonMinimum singleton hsingleton) .exit
  | tangentToTangent
      (source target : QuittingTerminalSemanticLawPoint (Fin 4))
      (hsource : (quittingPositiveDebtSupport source.1).Nonempty)
      (htarget : (quittingPositiveDebtSupport target.1).Nonempty)
      (hstrict : quittingPositiveDebtSupport target.1 ⊂
        quittingPositiveDebtSupport source.1) :
      FinFourResetRigidProducerTransition
        (.tangentMinimum source hsource) (.tangentMinimum target htarget)
  | tangentToExit
      (source : QuittingTerminalSemanticLawPoint (Fin 4))
      (hsource : (quittingPositiveDebtSupport source.1).Nonempty) :
      FinFourResetRigidProducerTransition (.tangentMinimum source hsource) .exit

namespace FinFourResetRigidProducerTransition

/-- Every permitted reset-rigid producer transition strictly lowers the
literal phase/support rank. -/
theorem rank_lt
    {first second : FinFourResetRigidProducerState}
    (transition : FinFourResetRigidProducerTransition first second) :
    second.rank < first.rank := by
  cases transition with
  | escapeToProduct origin product horigin hproduct =>
      have hcard : (quittingPositiveDebtSupport product.1).card ≤ 4 := by
        simpa using Finset.card_le_univ (quittingPositiveDebtSupport product.1)
      simp only [FinFourResetRigidProducerState.rank]
      simpa using (show 10 + (quittingPositiveDebtSupport product.1).card <
          15 + (quittingPositiveDebtSupport origin.1).card by
        omega)
  | escapeToExit origin horigin =>
      simp only [FinFourResetRigidProducerState.rank]
      omega
  | productToSingleton product singleton hproduct hsingleton =>
      have hcard : (quittingPositiveDebtSupport singleton.1).card ≤ 4 := by
        simpa using Finset.card_le_univ (quittingPositiveDebtSupport singleton.1)
      simp only [FinFourResetRigidProducerState.rank]
      simpa using (show 5 + (quittingPositiveDebtSupport singleton.1).card <
          10 + (quittingPositiveDebtSupport product.1).card by
        omega)
  | productToExit product hproduct =>
      simp only [FinFourResetRigidProducerState.rank]
      omega
  | singletonToTangent singleton tangent hsingleton htangent hstrict =>
      have hcard : (quittingPositiveDebtSupport tangent.1).card ≤ 4 := by
        simpa using Finset.card_le_univ (quittingPositiveDebtSupport tangent.1)
      simp only [FinFourResetRigidProducerState.rank]
      simpa using (show (quittingPositiveDebtSupport tangent.1).card <
          5 + (quittingPositiveDebtSupport singleton.1).card by
        omega)
  | singletonToExit singleton hsingleton =>
      simp only [FinFourResetRigidProducerState.rank]
      omega
  | tangentToTangent source target hsource htarget hstrict =>
      simp only [FinFourResetRigidProducerState.rank]
      exact Finset.card_lt_card hstrict
  | tangentToExit source hsource =>
      simp only [FinFourResetRigidProducerState.rank]
      exact Finset.card_pos.mpr hsource

end FinFourResetRigidProducerTransition

/-- The moving support child delegates to the integrated renewable trace,
which permits at most two later nonempty strict-support descents. -/
theorem resetRigidMovingSupportRenewal_furtherDescentCount_le_two
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    {moving : FinFourMovingMarkedPairMinimumSource source}
    {residual : FinFourMovingMarkedPairVanishingResidual moving}
    {minimum : FinFourMovingMarkedPairMinimumApproach residual}
    {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
    {compactification : FinFourMovingMarkedPairMinimumChordCompactification
      minimum weight hweight0 hweight1}
    {common : FinFourMovingMarkedPairCommonPrefixResponse compactification}
    (renewal : FinFourMovingMarkedPairSupportContractedRenewal common) :
    renewal.renewal.trace.descentCount ≤ 2 :=
  renewal.furtherDescentCount_le_two

end GameTheory
