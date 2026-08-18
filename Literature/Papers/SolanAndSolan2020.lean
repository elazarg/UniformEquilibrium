import Literature.Catalog
import UniformEquilibrium.Quitting.Classification.LCP.StationaryExistence
import UniformEquilibrium.Quitting.Classification.LCP.StrategicTransport

/-!
# Literature audit

Bibliography label: Solan & Solan 2020

E. Solan and O. N. Solan, *Quitting games and linear complementarity
problems*, Mathematics of Operations Research **45**(2), 626–651 (2020);
preprint arXiv:1707.02598.  Both were read.  All numbering below is the final
manuscript's; the preprint numbers the same results differently, and the two
versions do not define "normal player" the same way.

## Two player sets carry the word "normal"

The paper defines two different distinguished sets, and merging them would
misstate every result below.

* **Section 2.3, Definition 2.5.**  Player `i` is *normal* when its min-max
  value `v_i` is nonpositive, that is, not above the payoff `r^i_i = 0` it
  receives by quitting alone.  `I∗` is the set of normal players and `R̂` is
  the principal matrix of solo-exit payoffs on `I∗`.  This set is defined
  through a strategic quantity.  This development represents the quitting
  min-max as `GameTheory.quittingPunishmentValue` but does not compute `I∗`,
  so no declaration here names it.
* **Section 5.**  The recursion `I₀ = I` and
  `I_{l+1} = {i ∈ I_l : some j ∈ I_l with j ≠ i has r^j_i ≤ 0}`, whose
  intersection `I∗∗` is the set of *α-players*; the remaining players are
  *β-players*.  Every α-player is normal, and the paper states that the
  converse may fail.  This set is purely algebraic.  It is exactly
  `GameTheory.QuittingLCPClassification.normalCore` applied to
  `GameTheory.QuittingLCPClassification.normalizedSoloMatrix`, whose entry
  `normalizedSoloMatrix reward who owner` is the paper's `r^owner_who` after
  Assumption 2.1.

## What changed between the preprint and the final manuscript

In the preprint the recursion is not a Section 5 aside: it is Section 2.3's
*definition* of the normal players, and `R̂` is built on its intersection, so
the preprint's Theorem 2.11 — the final manuscript's Theorem 2.13 — is stated
over the recursive set rather than over the min-max set.  The preprint also
credits Simon 2012 with the one-step condition, writing that a player is
normal in Simon's sense exactly when he lies in `I₁` and that "our definition
of normality is a recursive application of Simon's definition"; the final
manuscript instead credits Simon 2012 with min-max normality and demotes the
recursion to the α-players.

The preprint's Section 2.3 display omits the distinctness condition:
`I_{l+1} := {i ∈ I_l : there exists j ∈ I_l such that r^j_i ≤ 0}`.  Read
literally after Assumption 2.1 that display never removes a player, because
`j = i` always satisfies `r^i_i ≤ 0`, so the preprint's `I∗` would be the whole
player set and `R̂` the whole matrix.  The final manuscript's Section 5 display
carries `j ∈ I_l \ {i}`.  The degeneracy is recorded by
`draftRecursionCore_eq_univ` below, and the development uses the final
distinct-witness form throughout.
-/

namespace Literature.Papers.SolanAndSolan2020

open GameTheory StochasticGame QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Section 2: the standing normalization -/

/-- **Assumption 2.1 is without loss of generality**, in the exact form the
paper gives for it: adding a constant to the payoffs of one player does not
change that player's strategic considerations.  Subtracting each player's own
solo-exit payoff preserves every terminal approximate-Nash inequality, profile
by profile and at the same error. -/
theorem isεAsymptoticNash_soloNormalized_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (ε : ℝ) (profile : (quittingGame reward).BehaviorProfile) :
    (quittingGame reward).IsεAsymptoticNash
        (normalizedQuittingTerminalPayoff reward) ε profile ↔
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile :=
  isεAsymptoticNash_normalized_iff reward ε profile

/-! ## Section 5: the α-player recursion -/

/-- **The Section 5 recursion is decreasing**, which is what makes
`I∗∗ = ⋂_l I_l` well defined. -/
theorem alphaLayer_antitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {n m : ℕ} (hnm : n ≤ m) :
    normalLayer (normalizedSoloMatrix reward) m ⊆
      normalLayer (normalizedSoloMatrix reward) n :=
  normalLayer_antitone (normalizedSoloMatrix reward) hnm

/-- **Equation (19).**  When an α-player quits alone, every β-player receives
a strictly positive payoff.  The inequality is stated on the solo-normalized
matrix, where the paper's `r^alpha_beta` is
`normalizedSoloMatrix reward beta alpha`. -/
theorem betaPlayer_alphaSoloExit_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {alpha beta : ι}
    (halpha : alpha ∈ normalCore (normalizedSoloMatrix reward))
    (hbeta : beta ∉ normalCore (normalizedSoloMatrix reward)) :
    0 < normalizedSoloMatrix reward beta alpha :=
  normalCore_entry_pos_of_notMem (normalizedSoloMatrix reward) hbeta halpha

/-- **The earlier draft's display is degenerate.**  Dropping `j ≠ i` from the
Section 5 recursion, as that draft's display does, leaves a recursion whose
intersection is the whole player set after Assumption 2.1.  The final
manuscript's display carries the distinctness condition and is the one used
here. -/
theorem draftRecursionCore_eq_univ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    printedNormalCore (normalizedSoloMatrix reward) = Finset.univ :=
  printedNormalCore_normalized_eq_univ reward

/-- **The Section 5 homogeneous branch, with a weakened conclusion.**  The
paper states that a nontrivial solution of `LCP(R̂∗∗, 0)` yields a stationary
`ε`-equilibrium for every positive `ε`.  What is checked here is the weaker
conclusion that the game has one fixed uniform-equilibrium payoff; neither
stationarity of the witness nor the accuracy-indexed form is part of this
statement. -/
theorem exists_uniformEquilibriumPayoff_of_alphaHomogeneous
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnonempty : HasNormalPlayers (normalizedSoloMatrix reward))
    (hhomogeneous :
      HasHomogeneousSimplexSolution (normalizedNormalPlayerMatrix reward)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_homogeneousMatrixBranch reward
    { normal_nonempty := hnonempty
      homogeneous := hhomogeneous }

/-! ## Section 5: the stationary branch -/

/-- **The Section 5 empty-α-player claim.**  The paper states, without proof,
that a stationary `ε`-equilibrium exists for every positive `ε` when there are
no α-players.  The deviation class checked here is all behavior strategies,
not only stationary ones.

This is the α-player statement of Section 5, not Lemma 2.7, which concerns the
min-max normal players `I∗` and is not implied by it. -/
theorem hasStationaryApproximateEquilibria_of_noAlphaPlayers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hempty : AllPlayersAbnormal (normalizedSoloMatrix reward)) :
    HasQuittingStationaryApproximateEquilibria reward := by
  obtain ⟨_, hvalue⟩ :=
    exists_stationaryUniformEquilibriumPayoff_of_allPlayersAbnormal
      reward hempty
  exact hvalue.hasApproximateEquilibria

/-- **The Section 5 homogeneous claim.**  The paper states, without proof,
that a nontrivial solution of `LCP(R̂∗∗, ~0)` yields a stationary
`ε`-equilibrium for every positive `ε`.  The deviation class checked here is
all behavior strategies, not only stationary ones. -/
theorem hasStationaryApproximateEquilibria_of_alphaHomogeneous
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnonempty : HasNormalPlayers (normalizedSoloMatrix reward))
    (hhomogeneous :
      HasHomogeneousSimplexSolution (normalizedNormalPlayerMatrix reward)) :
    HasQuittingStationaryApproximateEquilibria reward := by
  obtain ⟨_, hvalue⟩ :=
    exists_stationaryUniformEquilibriumPayoff_of_homogeneousMatrixBranch reward
      { normal_nonempty := hnonempty
        homogeneous := hhomogeneous }
  exact hvalue.hasApproximateEquilibria

/-- **Theorem 5.1(1).**  Suppose the α-player set is nonempty, the homogeneous
problem `LCP(R̂∗∗, ~0)` has only the trivial solution, and `R̂∗∗` is not a
Q-matrix in the sense of Definition 2.10.  Then the quitting game has a
stationary `ε`-equilibrium for every positive `ε`.

The deviation class checked here is all behavior strategies, not only
stationary ones, so this is the strong reading of the source's conclusion. -/
theorem hasStationaryApproximateEquilibria_of_alphaNonQ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnonempty : HasNormalPlayers (normalizedSoloMatrix reward))
    (hhomogeneous :
      ¬HasHomogeneousSimplexSolution (normalizedNormalPlayerMatrix reward))
    (hnotQ : ¬IsStandardQMatrix (normalizedNormalPlayerMatrix reward)) :
    HasQuittingStationaryApproximateEquilibria reward :=
  hasQuittingStationaryApproximateEquilibria_of_ordinaryNonQMatrixBranch reward
    { normal_nonempty := hnonempty
      no_homogeneous := hhomogeneous
      normal_not_standardQ := hnotQ }

/-- **Theorem 5.1(1), with a pinned limit payoff.**  Under the hypotheses of
Theorem 5.1(1) the stationary `ε`-equilibria can be chosen to approach one
fixed payoff vector, which is therefore a uniform-equilibrium payoff of the
game.  This conclusion is not in the source. -/
theorem exists_stationaryUniformEquilibriumPayoff_of_alphaNonQ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnonempty : HasNormalPlayers (normalizedSoloMatrix reward))
    (hhomogeneous :
      ¬HasHomogeneousSimplexSolution (normalizedNormalPlayerMatrix reward))
    (hnotQ : ¬IsStandardQMatrix (normalizedNormalPlayerMatrix reward)) :
    ∃ value : Payoff ι,
      IsQuittingStationaryUniformEquilibriumPayoff reward value ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none value := by
  obtain ⟨value, hvalue⟩ :=
    exists_stationaryUniformEquilibriumPayoff_of_ordinaryNonQMatrixBranch reward
      { normal_nonempty := hnonempty
        no_homogeneous := hhomogeneous
        normal_not_standardQ := hnotQ }
  exact ⟨value, hvalue, hvalue.isUniformEquilibriumPayoff⟩

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_and_solan_2020"
  bibliographyLabel := "Solan & Solan 2020"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Solan & Solan 2020"
  role := .recentNonzeroSum
  sourceEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "solo_exit_normalization_without_loss_of_generality"
        sourceLocator := "Assumption 2.1 and Remark 2.2"
        summary :=
          "Normalizing each player's solo-exit payoff to zero is without " ++
          "loss of generality, because adding a constant to one player's " ++
          "payoffs preserves that player's strategic comparisons."
        status := .provedInLean
          "Literature.Papers.SolanAndSolan2020.isεAsymptoticNash_soloNormalized_iff"
          "GameTheory.QuittingLCPClassification.isεAsymptoticNash_normalized_iff" },
      { claimId := "sunspot_epsilon_equilibrium_exists"
        sourceLocator := "Theorem 2.4"
        summary :=
          "Every multiplayer quitting game admits a sunspot " ++
          "epsilon-equilibrium for every positive epsilon."
        status := .sourceOnly },
      { claimId := "abnormal_player_receives_positive_solo_payoffs"
        sourceLocator := "Lemma 2.6"
        summary :=
          "If player i has positive min-max value then every other player " ++
          "quitting alone pays i strictly more than i's own solo exit."
        status := .sourceOnly },
      { claimId := "no_normal_players_gives_stationary_equilibrium"
        sourceLocator := "Lemma 2.7"
        summary :=
          "If no player has nonpositive min-max value then a stationary " ++
          "epsilon-equilibrium exists for every positive epsilon."
        status := .sourceOnly },
      { claimId := "homogeneous_lcp_gives_stationary_equilibrium"
        sourceLocator := "Lemma 2.12"
        summary :=
          "A nontrivial solution of the homogeneous linear complementarity " ++
          "problem on the min-max normal players yields a stationary " ++
          "epsilon-equilibrium for every positive epsilon."
        status := .sourceOnly },
      { claimId := "non_q_matrix_gives_epsilon_equilibrium"
        sourceLocator := "Theorem 2.13(1)"
        summary :=
          "If the normal-player solo matrix is not a Q-matrix, and the " ++
          "homogeneous problem has only the trivial solution, then an " ++
          "epsilon-equilibrium exists for every positive epsilon."
        status := .sourceOnly },
      { claimId := "q_matrix_gives_single_quitter_sunspot_equilibrium"
        sourceLocator := "Theorem 2.13(2)"
        summary :=
          "If that matrix is a Q-matrix, a sunspot epsilon-equilibrium " ++
          "exists in which at most one player quits with positive " ++
          "probability at each stage."
        status := .sourceOnly },
      { claimId := "alpha_player_recursion_is_decreasing"
        sourceLocator := "Section 5, recursion display defining I_l"
        summary :=
          "The layers I_0 = I and I_{l+1} = {i in I_l : some j in I_l " ++
          "distinct from i has r^j_i at most zero} decrease, so the " ++
          "alpha-player set is their well-defined intersection."
        status := .provedInLean
          "Literature.Papers.SolanAndSolan2020.alphaLayer_antitone"
          "GameTheory.QuittingLCPClassification.normalLayer_antitone" },
      { claimId := "alpha_solo_exit_pays_beta_players_positively"
        sourceLocator := "Equation (19)"
        summary :=
          "If i is an alpha-player and j is not, then j receives a strictly " ++
          "positive payoff when i quits alone."
        status := .provedInLean
          "Literature.Papers.SolanAndSolan2020.betaPlayer_alphaSoloExit_pos"
          "GameTheory.QuittingLCPClassification.normalCore_entry_pos_of_notMem" },
      { claimId := "draft_recursion_display_omits_distinctness"
        sourceLocator :=
          "Section 2.3 recursion display in the arXiv:1707.02598 preprint"
        summary :=
          "In the preprint the recursion is the definition of the normal " ++
          "players, and its display omits the condition that the witness j " ++
          "differ from i. Read literally under Assumption 2.1 it removes no " ++
          "player, so the preprint's normal set would be every player and " ++
          "its derived matrix the whole matrix. The final manuscript's " ++
          "Section 5 display carries the distinctness condition, and that " ++
          "final form is the one used throughout this development."
        status := .provedInLean
          "Literature.Papers.SolanAndSolan2020.draftRecursionCore_eq_univ"
          "GameTheory.QuittingLCPClassification.printedNormalCore_normalized_eq_univ" },
      { claimId := "normality_definition_differs_between_versions"
        sourceLocator :=
          "Section 2.3 of the arXiv:1707.02598 preprint against Definition " ++
          "2.5 and Section 5 of the final manuscript"
        summary :=
          "The preprint defines the normal players as the intersection of " ++
          "the recursion and calls that a recursive application of Simon " ++
          "2012's one-step condition, building its derived matrix on that " ++
          "set. The final manuscript defines normal players by nonpositive " ++
          "min-max value, credits that notion to Simon 2012, and keeps the " ++
          "recursion only as the alpha-players of Section 5. A theorem " ++
          "quoted from one version must not be restated with the other " ++
          "version's index set."
        status := .sourceOnly },
      { claimId := "alpha_homogeneous_lcp_gives_stationary_equilibrium"
        sourceLocator := "Section 5, Lemma 2.12 analogue for the alpha-players"
        summary :=
          "A nontrivial solution of the homogeneous linear complementarity " ++
          "problem on the alpha-player matrix yields a stationary " ++
          "epsilon-equilibrium for every positive epsilon. The checked " ++
          "statement caps deviations by all behavior strategies, not only " ++
          "stationary ones."
        status := .provedInLean
          "Literature.Papers.SolanAndSolan2020.\
hasStationaryApproximateEquilibria_of_alphaHomogeneous"
          "GameTheory.QuittingLCPClassification.\
exists_stationaryUniformEquilibriumPayoff_of_homogeneousMatrixBranch" },
      { claimId := "no_alpha_players_gives_stationary_equilibrium"
        sourceLocator := "Section 5, sentence after Equation (19)"
        summary :=
          "If there are no alpha-players then a stationary " ++
          "epsilon-equilibrium exists for every positive epsilon. This is " ++
          "the alpha-player statement of Section 5, distinct from Lemma " ++
          "2.7, which concerns the min-max normal players."
        status := .provedInLean
          "Literature.Papers.SolanAndSolan2020.\
hasStationaryApproximateEquilibria_of_noAlphaPlayers"
          "GameTheory.QuittingLCPClassification.\
exists_stationaryUniformEquilibriumPayoff_of_allPlayersAbnormal" },
      { claimId := "alpha_homogeneous_lcp_gives_uniform_equilibrium_payoff"
        sourceLocator := "Section 5, Lemma 2.12 analogue for the alpha-players"
        summary :=
          "The weakened conclusion of the preceding claim: on a nonempty " ++
          "alpha-player core with a homogeneous simplex solution the game " ++
          "has one fixed uniform-equilibrium payoff. Stationarity of the " ++
          "witness is not part of the checked statement."
        status := .provedInLean
          "Literature.Papers.SolanAndSolan2020.exists_uniformEquilibriumPayoff_of_alphaHomogeneous"
          "GameTheory.QuittingLCPClassification.\
exists_uniformEquilibriumPayoff_of_homogeneousMatrixBranch" },
      { claimId := "alpha_non_q_matrix_gives_stationary_equilibrium"
        sourceLocator := "Theorem 5.1(1)"
        summary :=
          "If the alpha-player set is nonempty, its homogeneous problem has " ++
          "only the trivial solution, and its matrix is not a Q-matrix, " ++
          "then a stationary epsilon-equilibrium exists for every positive " ++
          "epsilon. The checked statement caps deviations by all behavior " ++
          "strategies, not only stationary ones."
        status := .provedInLean
          "Literature.Papers.SolanAndSolan2020.\
hasStationaryApproximateEquilibria_of_alphaNonQ"
          "GameTheory.QuittingLCPClassification.\
hasQuittingStationaryApproximateEquilibria_of_ordinaryNonQMatrixBranch" },
      { claimId := "alpha_non_q_matrix_gives_one_limit_stationary_payoff"
        sourceLocator := "Theorem 5.1(1)"
        summary :=
          "Strengthening of the preceding claim that is not in the source: " ++
          "under the same hypotheses the stationary epsilon-equilibria can " ++
          "be chosen to approach one fixed payoff vector, which is " ++
          "therefore a uniform-equilibrium payoff of the game."
        status := .provedInLean
          "Literature.Papers.SolanAndSolan2020.\
exists_stationaryUniformEquilibriumPayoff_of_alphaNonQ"
          "GameTheory.QuittingLCPClassification.\
exists_stationaryUniformEquilibriumPayoff_of_ordinaryNonQMatrixBranch" },
      { claimId := "alpha_q_matrix_gives_single_quitter_sunspot_equilibrium"
        sourceLocator := "Theorem 5.1(2)"
        summary :=
          "Under the same hypotheses with a Q-matrix, a sunspot " ++
          "epsilon-equilibrium exists in which at most one player quits " ++
          "with positive probability at each stage."
        status := .sourceOnly } ]

end Literature.Papers.SolanAndSolan2020
