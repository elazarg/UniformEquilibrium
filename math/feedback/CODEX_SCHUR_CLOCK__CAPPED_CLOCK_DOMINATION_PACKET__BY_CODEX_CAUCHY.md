# Capped-clock domination: independent final-text review

Reviewer: CODEX_CAUCHY.

Mathematical and admission verdict: pass for the stated theorems and scope.
The raw conditions produce unrestricted behavioral regret domination and a
fixed-target quiet extension; the four-player class has no unproduced
strategic input. The auxiliary inverse-row sharpness theorem is valid for
its exact balanced-spine hypotheses. No unresolved mathematical objection
was found. This is ordinary mathematical review, not new Lean compilation.

Reviewed in full:
[CAPPED_CLOCK_DOMINATION_PACKET](../notes/CODEX_SCHUR_CLOCK__CAPPED_CLOCK_DOMINATION_PACKET.md).
The exact reviewed SHA-256 is

```text
7da238a2e58da9c29237921cc9bd10890765982561ab006f6c352066b93d98ce
```

The admission verdict also approves the final packaged SHA-256

```text
9cb9dc87dc36b46d38c33b80ea134edbfbfa2be4856ba0271e7d5324ae032d4b
```

Removing only its three added final-review header lines reconstructs the
exact reviewed hash above. The mathematical text is unchanged.

The review applies the export criteria in [exports/README.md](../exports/README.md):
the relevant increment is a missing project capability, not publication
novelty. The frozen draft was not edited. Its companion verification script
was not used as the universal proof.

## Claim, probability mode, and legal responses

There is a finite child S in an independently randomized finite quitting
game with signed rewards and zero live/Never payoff. For each outside player
k, fixed nonnegative weights λ_ki satisfy the displayed Never, future-first-
coalition, and joining inequalities N,F,J on raw rewards. The claimed
comparison pairs an arbitrary outside first-quit law ν with the legal child
replacement law min(T_i,Z), where T_i is the original private child clock
and Z is an independent ν-clock. Each child summand is a separate unilateral
experiment. This does not correlate players' actual prescribed behavior.

The five deterministic cases exhaust all tuples, including simultaneous
child quitting, outside Never, and joint child Never. In the only case with
two different finite evaluation dates, the residual is

    [f(t)−f(τ)]α + f(τ)[α−ψ(A)].

Both bracketed quantities are nonpositive under N and F; the coefficients
are nonnegative because f is nonincreasing. This proves the weighted
evaluation claim even for signed rewards. With row violations at most η,
the coefficients sum to f(t)≤1, so the additive error is η. There is no
extra factor two or dependence on the number of calendar dates.

The min-clock law is independent of all other child clocks and has the
product-survival formula stated in the packet. Thus it is an admissible
private behavioral replacement. Integrating the pointwise inequality over
the common proof coupling gives the gain comparison. Bounding each separate
child experiment by its own full response supremum before taking the outside
supremum is valid. No supremum/expectation interchange or cap attainment is
assumed. Child-player caps in the quiet lift are exactly unchanged.

Necessity is exact for this prescribed comparison rule: all-Never tuples
recover N, a later deterministic coalition recovers F, and an immediate
coalition recovers J. It is not necessity for arbitrary quiet-extension
theorems or for uniform equilibrium existence.

## Never correction and fixed target

When N is removed, the sole uncontrolled deterministic case is finite outside
quitting against joint child Never. Its excess is at most
a_k=max(s_k−Σ_iλ_ki s_i,0), giving a_k p∞ after integration. The late cap
of a child clock has limiting gain s_j p∞: its gain tends to zero on every
finite original first outcome, equals s_j on joint Never, and is bounded
in absolute value by 2M. Bounded convergence therefore proves
s_j p∞≤d_j without any best-response attainment. A positive s_j absorbs
the correction into a child debt exactly as claimed.

For a specified child uniform payoff, passing each fixed profile and each
fixed deviation to terminal payoffs yields vanishing terminal regret and
delivery of that same child target. The regret estimate has a constant
amplification factor independent of accuracy. Compact selection is used only
for the additional outside payoff coordinates. The parent terminal vectors
therefore converge to one vector whose restriction is the specified child
target, and the terminal sequence consumer has exactly the required
fixed-target, all-large-horizons conclusion. In the fourteen-row case it is
correct to obtain the parent horizon threshold from terminal uniformization;
the packet does not transfer an arbitrary original child threshold directly.

The four-player theorem supplies the child payoff by unconditional
three-player existence. The weights and admission tests are finite reward
data. No child equilibrium, continuation floor, absorption schedule, or
recursive compatibility witness is an unexplained admission hypothesis.

## Consecutive finite menus and exact production

The sparse-calendar counterexample is valid: with an opponent quitting at
0 or 2 equally likely, the querying player's reply values at 0,1,2,3,Never
are 0,1/2,−1/2,0,0. A scan of supported atoms alone misses a profitable gap.

The repaired search uses every date 0 through H, plus Never, when prescribed
support is 0 through H−1 plus Never. Every later finite deadline has the
same terminal outcome distribution as H. Mixtures cannot improve on the
pure-date supremum, so this is the full cap, including H=0. Finite-profile
approximation gives a real profile with a strict regret margin; continuity
of the finite maximum of reply polynomials and rational density preserve
that margin. Exact enumeration therefore terminates for rational data.
This proves existence of the finite-law producer, with no efficiency or
uniform calendar-size assertion.

The finite LP alternative also has a complete proof: feasibility is cone
membership, the finite generated cone is closed by reduction to independent
generators, and nearest-point separation gives y≥0, Vᵀy≤0, b·y>0 with
the stated signs. Rational elimination supplies rational primal or dual
witnesses. None of these numerical certificates is mistaken for a strategy.

## Exact balanced-spine sharpness and partial blocks

For the strict triple, actual singleton absorption laws μ give
z=Tμ≥0 and h·z=1, where h_j is the j-th column sum of T⁻¹. Owner ties
place every positive owner-i row on z_i=0 at both ends. Removing zero
hazards and merging equal successive owners is legitimate. There cannot
be a final infinite owner block: its actual singleton outcome would violate
one of the strict negative cross-payoff floors.

At an owner change i→j, two coordinates of z vanish. The endpoint is a
simplex vertex; the two adjacent arcs force T_ji≥0 and T_ij≤0. The strict
sign pattern therefore forces cyclic owner order. This proves actual visits
to all three vertices and the floor equivalence gT⁻¹≥0 for every such
spine, without assuming a periodic schedule.

At a complete owner-i block, the two nonzero arc coordinates give precisely

    p_i = 1/(a_{i+1}h_{i+1}),
    c_i = b_{i−1}h_{i−1}/(a_{i+1}h_{i+1}).

The identity hT=1 makes p_i+c_i=1, and multiplication gives the displayed
three-block survival C. An arbitrary initial point is on the owner-i
simplex edge. If its entry-vertex coefficient is θ, its remaining block
absorption is θp_i and survival is at least c_i. A chosen vertex is reached
after at most that partial block and two complete blocks, with survival
at least C. This proof does not require bounded block lengths or bounded
zero-hazard gaps.

At a most negative outside vertex, joining loses at most 2Mδ relative to
the solo reward. The conditional gain is at least Δ−2Mδ. Multiplying by
the survival lower bound is used only when this quantity is positive;
otherwise nonnegative response regret suffices. Hence
d_k≥C max(Δ−2Mδ,0) is valid. The chosen response is one deterministic
deadline determined by the schedule, not by unrevealed clocks. No
approximate-balance stability theorem is inferred.

## Exact tests and class significance

An independent rational calculation reproduced the positive fixture's F
slacks (1,1,1,3,1,1,1), J slacks (2,2,1,2,3,4,1), and all complete
pure-date caps at its displayed one-date profile:

    U=B=(13/9,2,2/3,4/3).

The paired singleton matrix has no escort edge because every reciprocal
pair has equal strict signs. The existing arbitrary-period escort theorem
therefore excludes balanced singleton cycles on the parent and every
principal child, regardless of repeated owners. The fixture's strict raw
slacks and the all-Never/future/join cases give an actual enlargement of
the exact deletion capability. The parameterized completion family produces
the remaining eleven outside entries independently after the other
thirty-three nonsingleton entries are fixed.

The all-Never example with child singleton zero and outsider singleton one
correctly refutes dropping N without its stated protection. The table with
one-row dual witnesses for every deletion remains solved by its displayed
sure-anchor profile. These are useful failures of stronger claims, not
counterexamples to equilibrium existence.

## Inspected semantic declarations

The bounded source route uses `docs/TOOLKIT.md` and the declarations below,
read under their displayed imports. No fresh build or transitive trust audit
is represented by this list.

- `quittingBehaviorStoppingLaws_update`,
  `quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws`, and
  `quittingBehaviorDeviationPayoffCap_eq_pureTime`
  (`UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`).
- `prod_stoppingLaw_none_mul_singleton_le_terminalDebt`
  (`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`).
- `quittingGame_exists_uniformEquilibriumPayoff_threePlayer`
  (`UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`).
- `exists_finiteDeadlineTimingProfile_approximation` and
  `isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation`
  (`UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`).
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
- `QuittingBlockJoinAntitone`, `quittingBlockContinueFloor`, and
  `QuittingBlockDispensable`
  (`UniformEquilibrium/Quitting/Classification/BlockDeletion.lean`).
- `IsQuittingSingletonEscortEdge`,
  `BalancedSingletonCycleCertificate.escortEdge_of_coarse_bridge`, and
  `BalancedSingletonCycleCertificate.exists_escortCycle`
  (`UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean`).

The frozen text supplies a complete special-case source-to-UE chain, exact
admission tests, and useful missing compiler capability. Its auxiliary
balanced-spine theorem has explicitly supplied hypotheses and is used for
sharpness, not to hide an input of the raw existence class. The mathematical
and scope requirements for that contribution pass this independent review;
the conclusion remains a sufficient class, with unrestricted deviations
but no universal strategy-class or game-class completeness claim.
