import UniformEquilibrium.Quitting.Root.TerminalSemanticPair

/-! # Joint simplex-root continuity of the canonical terminal semantic prefix -/

noncomputable section

namespace GameTheory

open Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Simplex-coordinate form of one terminal semantic prefix action. -/
def quittingTerminalSemanticPrefixSimplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (data : QuittingRootSimplex ι × QuittingTerminalSemanticPair ι) :
    QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPrefix reward (quittingRootOfSimplex data.1) data.2

/-- Joint continuity of one semantic prefix in the simplex root and the tail
semantic pair. -/
theorem continuous_quittingTerminalSemanticPrefixSimplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Continuous (quittingTerminalSemanticPrefixSimplex reward) := by
  unfold quittingTerminalSemanticPrefixSimplex
  have hprescribed : Continuous (fun data :
      QuittingRootSimplex ι × QuittingTerminalSemanticPair ι =>
      quittingRootSuccessorPayoff reward data.2.1
        (quittingRootOfSimplex data.1)) := by
    let source : QuittingRootSimplex ι × QuittingTerminalSemanticPair ι →
        Payoff ι × QuittingRootSimplex ι := fun data => (data.2.1, data.1)
    have hsource : Continuous source :=
      (continuous_fst.comp continuous_snd).prodMk continuous_fst
    have h := (continuous_quittingRootSuccessorPayoff_simplex reward).comp hsource
    change Continuous (fun data :
      QuittingRootSimplex ι × QuittingTerminalSemanticPair ι =>
        quittingRootSuccessorPayoff reward data.2.1
          (quittingRootOfSimplex data.1)) at h
    exact h
  have henvelope : Continuous (fun data :
      QuittingRootSimplex ι × QuittingTerminalSemanticPair ι =>
      fun who => max
        (quittingRootQuitPayoff reward data.2.1
          (quittingRootOfSimplex data.1) who)
        (quittingRootContinuePayoff reward
          (Function.update data.2.1 who (data.2.2 who))
          (quittingRootOfSimplex data.1) who)) := by
    apply continuous_pi
    intro who
    have hquit : Continuous (fun data :
        QuittingRootSimplex ι × QuittingTerminalSemanticPair ι =>
        quittingRootQuitPayoff reward data.2.1
          (quittingRootOfSimplex data.1) who) := by
      let source : QuittingRootSimplex ι × QuittingTerminalSemanticPair ι →
          Payoff ι × QuittingRootSimplex ι := fun data => (data.2.1, data.1)
      have hsource : Continuous source :=
        (continuous_fst.comp continuous_snd).prodMk continuous_fst
      have h := (continuous_quittingRootQuitPayoff_simplex reward who).comp hsource
      change Continuous (fun data :
        QuittingRootSimplex ι × QuittingTerminalSemanticPair ι =>
          quittingRootQuitPayoff reward data.2.1
            (quittingRootOfSimplex data.1) who) at h
      exact h
    have htail : Continuous (fun data :
        QuittingRootSimplex ι × QuittingTerminalSemanticPair ι =>
        Function.update data.2.1 who (data.2.2 who)) := by
      apply continuous_pi
      intro player
      by_cases hplayer : player = who
      · subst player
        simpa [Function.update_self] using (show Continuous (fun data :
          QuittingRootSimplex ι × QuittingTerminalSemanticPair ι =>
            data.2.2 who) by fun_prop)
      · simpa [Function.update_of_ne hplayer] using (show Continuous (fun data :
          QuittingRootSimplex ι × QuittingTerminalSemanticPair ι =>
            data.2.1 player) by fun_prop)
    have hcontinue : Continuous (fun data :
        QuittingRootSimplex ι × QuittingTerminalSemanticPair ι =>
        quittingRootContinuePayoff reward
          (Function.update data.2.1 who (data.2.2 who))
          (quittingRootOfSimplex data.1) who) := by
      let source : QuittingRootSimplex ι × QuittingTerminalSemanticPair ι →
          Payoff ι × QuittingRootSimplex ι := fun data =>
        (Function.update data.2.1 who (data.2.2 who), data.1)
      have hsource : Continuous source := htail.prodMk continuous_fst
      have h :=
        (continuous_quittingRootContinuePayoff_simplex reward who).comp hsource
      change Continuous (fun data :
        QuittingRootSimplex ι × QuittingTerminalSemanticPair ι =>
          quittingRootContinuePayoff reward
            (Function.update data.2.1 who (data.2.2 who))
            (quittingRootOfSimplex data.1) who) at h
      exact h
    exact hquit.max hcontinue
  simpa only [quittingTerminalSemanticPrefix] using
    hprescribed.prodMk henvelope

end GameTheory
