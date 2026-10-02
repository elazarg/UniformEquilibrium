# Independent adversarial audit of ordered own-quitting premiums

Author: CODEX_TARSKI_PREMIUM.

Status: PASS after independent reconstruction, exact falsification tests,
and full final-draft review. The bound final feedback is
[here](../feedback/ORDERED_QUITTING_PREMIUMS_UNIFORM_EQUILIBRIUM__FINAL_BY_CODEX_TARSKI_PREMIUM.md),
for draft SHA-256
`a42680e45fe7a8a373337a624808eefee1fc5a3b53507eda32cb5a7e5e7f3b6e`.
This is ordinary mathematics and static source inspection; no Lean
compilation or self-export was performed. I derived the steps below without
reading another reviewer's verdict.

## Exact question

Let I be finite and nonempty. A nonempty first quitting coalition S pays
r(S) in real coordinate space indexed by I; never quitting pays zero.
Players simultaneously choose Continue or Quit using independent behavioral
randomization. Before absorption the unique public history at each date is
all previous actions Continue. A deviator may replace its entire behavioral
strategy, including Never and every finite quitting date. Put s_i=r_i({i})
and assume s_i is nonnegative. Assume the following finite table condition:

    For every nonempty A⊆I, some i∈A satisfies
        r_i(S)≤s_i for every i∈S⊆A.                         (P)

Does this raw table condition produce a periodic terminal approximate Nash
profile, against all behavioral deviations in every suffix, at every positive
accuracy, and consequently one fixed uniform-equilibrium payoff?

The answer from the reconstructed argument is yes. Neither a lower bound on
own joint-quitting payoffs nor a restriction on passive rewards is used.
This is sufficiency for a table class, not necessity, full arbitrary-table
existence, or completeness of periodic profiles for all equilibrium payoffs.

## Independently reconstructed steps

1. The finite condition (P) is equivalent to an ordering i₁,…,i_n such that
   r_(i_m)(S)>s_(i_m), with i_m∈S, implies some i_ℓ∈S with ℓ<m. Repeatedly
   peel a player supplied by (P) from the remaining set. Conversely use the
   earliest member of any nonempty A. Strict positive premiums are the only
   forbidden entries at a peel; negative premiums need not vanish.

2. First normalize to s_i=1 and choose R≥1 bounding all terminal absolute
   payoffs. The compact carrier is

       W={v∈[−R,R]^I : some v_i≤1}.

   For a product root q, let F(q,v) be its payoff with continuation v,
   a(q)=1−∏(1−q_i), and Q_i,C_i its pure Quit/Continue endpoints. Exact
   finite-game Nash existence supplies q at every v∈W. If its active set
   A={i:q_i>0} is nonempty, peel i from A. Every coalition possible when i
   chooses Quit lies in A and contains i, whence Q_i≤1. Positive Quit
   support gives F_i=Q_i≤1. If q is all-Continue, Nash implies v_j≥1 for
   every j; some coordinate in W therefore equals 1, giving an indifferent
   player to activate. This needs no common lower orthant.

3. Replace the selected marginal q_i by q_i+δ(1−q_i), with 0<δ≤1. The new
   row absorbs with probability at least δ. Its selected player's endpoints
   are unchanged. A mixed selected player is indifferent, a sure quitter is
   unchanged, and the newly activated all-Continue player is indifferent.
   Its payoff consequently stays at most 1, so the successor stays in W.
   Other players' pure endpoints each move by at most 2Rδ; their support
   does not change. Thus every supported action is within 4Rδ of every
   pure action. The assertion is SUPPORT regret, not average regret.

4. Given row tolerance τ>0, take δ=min(1/2,τ/(8R)) and ζ=δτ/4. A finite
   ζ-net in W and a chosen row at every representative define a finite map
   from a continuation representative to a representative near its current
   successor. A directed cycle exists. Reverse its order to obtain

       ‖v_ℓ−F(q_ℓ,v_(ℓ+1))‖∞≤ζ,       a(q_ℓ)≥δ.

   The root q_ℓ is the row selected AT the representative v_(ℓ+1), not at
   v_ℓ. This is the required chronological orientation. Repeat the roots
   periodically. Every suffix absorbs almost surely, since n-step survival
   is at most (1−δ)^n. Its actual terminal tail values U_ℓ satisfy exact
   Bellman recursion, are bounded by R, and are periodic. Maximizing over
   one period yields D≤ζ+(1−δ)D, hence D≤ζ/δ. Each pure endpoint is
   1-Lipschitz in the continuation coordinate. The support error against
   actual tails is at most 4Rδ+2ζ/δ≤τ. No continuous selection, public
   correlation, or realization of an annotation by assumption occurs here.

5. The existing unit-singleton perfect-sequence extraction theorem consumes
   precisely these actual-tail rows, their positive common absorption bound,
   and periodicity. At any desired terminal error it first chooses τ>0.
   It returns either the periodic input sequence with all-suffix full
   behavioral Nash guarantees, or a stationary profile, representable by a
   period-one sequence, with the same guarantees. The theorem has no capped
   joint-payoff hypothesis. The implication cannot be replaced with a direct
   summation of row errors; an exact counterexample appears below.

6. For original nonnegative solos, choose t>0, add t to each NONEMPTY
   terminal payoff coordinate, keep Never at zero, and divide coordinate i
   by d_i=s_i+t>0. The result has unit solos and its premiums have the same
   signs as before. For target original error ε>0 use t=ε/4 and unit-game
   terminal error ε/(2 max_i d_i). Undoing positive scaling gives error
   ε/2 in the shifted game. For any profile or deviation π,

       U_i^(r+t)(π)−U_i^r(π)=t Pr_π(absorption)∈[0,t].

   Hence the original deviation gain is at most ε/2+2t=ε. The inequality
   holds for nonabsorbing deviations too, suffix by suffix. All games share
   the same action and coalition-history tree, so strategies transfer by
   its identity. This is perturbation, not a false additive equivalence
   leaving Never fixed.

7. Apply terminal all-errors selection to the ORIGINAL bounded table.
   Its terminal payoffs lie in one compact cube regardless of t or the
   normalized reward bounds. A convergent payoff subsequence supplies one
   target before the accuracy, with profiles and horizon thresholds allowed
   to depend on accuracy. No fixed normalized table or accuracy-independent
   period is required.

## Exact attempted falsifiers

### Signed peeling does not preserve the singleton lower orthant

With two players, set

    r({1})=(1,0),    r({2})=(−2,1),    r({1,2})=(−1,2).

Order 1 before 2. Player 1 has a negative pair premium, and player 2 has a
positive pair premium requiring its earlier player. At q=(1,1), player 1's
Quit/Continue endpoints are −1 and −2; player 2's are 2 and 0. Thus this
is an exact root Nash for every annotation, with successor (−1,2). It
violates the singleton lower orthant [1,∞)² but remains in W. This falsifies
any attempted signed extension of the separate nonnegative-premium
common-boundary or C¹-drift result. It does not falsify the present theorem.

### Peeling failure need not obstruct equilibrium

Set r({1})=(1,0), r({2})=(0,1), r({1,2})=(2,2). Condition (P) fails on
{1,2}. Both Quit surely is nevertheless an exact terminal equilibrium. At
v=(−2,−2), Quit is strictly dominant in the root game and the only Nash
successor is (2,2), so the low-coordinate root-choice mechanism itself
fails. The class hypothesis is a sufficient condition with a real residual.

### Small support errors and positive absorption do not sum to Nash

Set r({1})=(1,1), r({2})=(5,1), r({1,2})=(1,1). This table even has
constant own-quitting rewards. For 0<t<1 use the stationary product row
q₁=t, q₂=t². Its actual value for player 1 is

    U₁=(1+5t(1−t))/(1+t(1−t)).

Its two player-1 endpoints against its actual continuation are Q₁=1 and
C₁=1+4t/(1+t(1−t)). Player 2 is indifferent at 1. Thus the row is
support-(4t)-Nash and has positive per-row absorption. But player 1's Never
deviation earns 5, a gain 4/(1+t(1−t)) tending to 4. At t=1/10, the
exact values are U₁=145/109, C₁−Q₁=40/109, and Never gain 400/109.
Exact rational arithmetic confirms these identities. This directly attacks
and excludes the tempting incorrect shortcut in step 5. A stationary
repair with only player 1 quitting is exact Nash here, as extraction allows.

### Pairwise graph cycles need not violate ordered hyperedges

With three unit-solo players, let every terminal coordinate be 1 except
r₂({1,2,3})=2 and r₃({2,3})=2. Order 1,2,3 satisfies (P). A graph that
joins a premium recipient to EVERY other coalition member has both 2→3
and 3→2, falsely suggesting an obstruction. The raw coalition condition
requires at least one earlier participant, not all participants earlier.

## Source audit

The bounded navigation route was terminal selection in docs/TOOLKIT.md,
followed by the named perfect-row and extraction files. Original source
read directly: Solan and Vieille, “Quitting Games,” Mathematics of Operations
Research 26(2), 265–285 (2001), DOI 10.1287/moor.26.2.265.10549; local
literature/SOLAN_VIEILLE_2001__QUITTING_GAMES__JSTOR.pdf, printed pp.265–274.
Definition 2.1 is support perfection; Proposition 2.2 is the weaker selected
low-payoff-quitter hypothesis, explicitly distinguished from A.2; Proposition
2.3 reverses a finite cycle and proves actual-tail approximation; Proposition
2.4, restated as 2.6, supplies the nonlocal extraction. The paper uses
Continue probabilities; this notebook uses Quit probabilities. Never is zero
in both models. The paper's terminal equilibrium is not itself the project's
one-fixed-target statement; the separate terminal-selection consumer supplies
that quantifier.

Named declarations and files inspected statically:

- `quittingUniformEquilibriumPayoffConjecture`,
  UniformEquilibrium/Quitting/Conjecture/Basic.lean: an open Prop definition.
- `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
  and `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`,
  UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean.
- `exists_isZeroQuittingRootNash`,
  UniformEquilibrium/Quitting/Root/NashExistence.lean.
- `QuittingUnitSoloExit`, `QuittingCappedJointExit`, and
  `QuittingWeakSoloExitPreference`,
  UniformEquilibrium/Quitting/Classification/SoloExitPreference.lean.
- `QuittingPlayerRowεPerfect` and `QuittingRowεPerfect`,
  UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean. The
  stronger supported-action versus pure-action inequalities above imply all
  four production clauses by averaging over supported actions.
- `exists_quittingPerfectAbsorbingRow_of_soloExitPreference`,
  UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRow.lean:
  its signature requires both unit solos and capped joint rewards.
- `exists_periodic_quittingPerfectAbsorbingRootSequence_of_soloExitPreference`,
  UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRootSequence.lean:
  its signature still requires those two table hypotheses.
- `QuittingPerfectSequenceExtraction`,
  UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtractionReduction.lean.
- `quittingPerfectSequenceSubgameDichotomy_of_soloExitPreference` and
  `quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`,
  UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean:
  these signatures require unit solos ONLY and conclude terminal approximate
  Nash against the game's complete behavioral deviation class.
- `isεAsymptoticNash_soloStationary_of_quietWindow`,
  UniformEquilibrium/Quitting/Classification/Existence/QuietWindowStationaryRepair.lean:
  its unit-solo assumption handles the Never clause; no joint cap is present.
- `quittingRootSequenceHazardTerminalValue_le_sSup_pureTime`,
  UniformEquilibrium/Quitting/Cycles/InfinitePureTimeExtremality.lean: the
  deterministic response set explicitly includes every finite date and Never.
- `proposition2_2`, `proposition2_3`, `proposition2_4`, and
  `oneShotPerfectEpsilonEquilibrium`, Literature/SolanAndVieille2001.lean:
  faithful statements under an unbuilt literature lane, not production status.

The mathematical new attachment is finite table condition (P) into the old
conditional root-choice mechanism, together with the explicit zero-singleton
perturbation. Narrow searches of the named producer subtree did not locate
the ordered-premium condition. This is not a literature-priority assertion.
No theorem in the unbuilt literature lane is needed as an unproved premise:
steps 1–4 are reconstructed above, step 5 has the inspected production
consumer, and step 7 has the inspected terminal-selection consumer.

## Remaining requested check

The assembled final draft and all its auxiliary claims have now passed the
hash-bound review linked above. A concrete next formalization check is to
expose the selected active-low-payoff hypothesis in the existing charged-row
generator without assuming capped joint rewards or a supplied sequence. Keep
the signed/nonnegative boundary distinction; the result does not cover
arbitrary tables, arbitrary equilibrium payoffs, or a period bounded
independently of accuracy.
