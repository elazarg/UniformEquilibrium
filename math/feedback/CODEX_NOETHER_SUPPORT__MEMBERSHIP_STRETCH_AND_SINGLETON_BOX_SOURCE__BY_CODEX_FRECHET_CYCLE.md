# Independent review: membership stretching and singleton-box source

Reviewer: CODEX_FRECHET_CYCLE.

Reviewed source:
[CODEX_NOETHER_SUPPORT__MEMBERSHIP_STRETCH_AND_SINGLETON_BOX_SOURCE.md](../notes/CODEX_NOETHER_SUPPORT__MEMBERSHIP_STRETCH_AND_SINGLETON_BOX_SOURCE.md).
Exact reviewed SHA256:
`7063965c31fa04fb0c5755f298a329a466f9e0054cb8abb84a423169c67e4a54`.
All 348 lines were read after the author froze this version. I reconstructed
the main argument independently before reading the candidate; I did not
read another review of it.

**Verdict: PASS as ordinary mathematics. No mathematical repair requested.**
This is not a Lean-check, an unconditional positive-gap example, a low-regret
producer, or a resolution of the uniform-equilibrium conjecture. The source
restriction and the advertised same-source fields are proved at their stated
scope. Full sixty-coordinate cube normality is deliberately not among them.

Final mathematical-name packet also accepted, SHA256
`1fdefe4acb70e12b789e045885bc8711cea707daa059a70daab197623afbaa70`:
[MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md](../notes/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md).
The exact final-byte check is recorded in Section 8 below.

## 1. Exact claim checked

Write η(r) for the infimum of full behavioral exploitability over all actual
independent four-player stopping laws, with rewards in [−1,1]^60 and Never
payoff zero. Suppose its maximum Ω over the whole reward cube is positive.

The candidate constructs 56 fixed non-own-singleton reward coordinates b
such that, on the remaining four-coordinate singleton cube:

    Ω_b=max_s η(r(s))>0,
    Γ_b=min_(|S|≥2) E_(r(s))(pure Quit0 on S)>Ω_b.

The second expression is constant throughout that cube. At one fixed
maximizing table r_∞ it then constructs actual silent finite-calendar
near-minimizers, together with one tester distribution at each source,
simultaneously retaining:

- full exploitability tending to Ω_b;
- uniform approximate stationarity on the displayed enlarged calendar;
- vanishing weighted inactivity and positive mass for every owner; and
- nonpositive limiting total weighted own-singleton pressure.

The point of the reduction is that these fields now coexist with strict
separation from ALL eleven pure nonsingleton profiles. It does not assert
that the original cube maximizer or an arbitrarily supplied pure minimizer
has the new separation.

## 2. Full-cap and stretch reconstruction

For |S|≥2, deleting any one player leaves a sure quitter at date zero.
Thus every unilateral law is a mixture of the membership join and leave
endpoints, even when the declared tails are Never. There is no earlier
finite date. Consequently

    E_r(p^S)=max_i (r_i(S△{i})−r_i(S))_+.

This is the actual unrestricted cap formula, not a binary-menu substitute.
It agrees with
`quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card`
in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.

Every displayed endpoint lies on exactly one owner-membership edge
B↔B∪{i}, where B is a nonempty subset of the other three players. None
is an own-singleton reward coordinate. In particular, deleting i from a
pair leaves a singleton of a DIFFERENT player. There are seven disjoint
edges per owner, covering precisely the other fourteen coordinates.

For each strict edge, moving the higher endpoint toward +1 and the lower
toward −1 changes a positive directed gap c to (1−α)c+2α. Negative gaps
remain negative, and equal gaps stay zero. The map on positive gaps is
increasing. Therefore, whenever E_r(p^S)>0,

    E_(r_α)(p^S)=(1−α)E_r(p^S)+2α.

This holds simultaneously for all six pairs, four triples, and the grand
coalition. It needs neither uniqueness of the maximizing owner nor the
ordinary all-player-ties theorem. It also requires no regularity of the
edge-stretch map as a function of r: the base table is fixed before its
one-dimensional segment is used.

## 3. Strict separation on the whole restricted cube

The reward-distance bound gives |η(r)−η(r′)|≤2||r−r′||∞. Hence Ω is
attained. The all-Never profile gives Ω≤1. At a maximizer r*, every actual
pure nonsingleton profile has regret at least Ω>0, so the stretch identity
applies to each of the eleven profiles, not only to an active subcollection.

For 0<α<Ω/8 the candidate correctly obtains

    η(r*_α)>Ω/2,
    Γ(r*_α)≥Ω+α(2−Ω).

The restricted family contains this positive-gap table and remains inside
the original reward cube. Its maximum Ω_b therefore lies in (Ω/2,Ω].
All the pure-profile regrets are independent of the four variable
coordinates, so their strict margin above the ORIGINAL Ω persists over
the ENTIRE singleton cube and hence above Ω_b.

There is no normalization to nonnegative own singletons. Such a
normalization would not preserve the original cube-maximizing property.
The candidate leaves all four singleton parameters free in [−1,1], which
is exactly what the later pressure sign needs.

## 4. Restricted normal: precisely what survives

The common finite tester pool is fixed before minimizing on each calendar.
The reward-uniform quantile estimate implies, uniformly over the restricted
family, that each smoothed calendar minimum lies between η(r) and
η(r)+ρ_m+ε_m. Maximizing their calendar average over the singleton cube
therefore yields η(r_m)→Ω_b. EVERY inner minimizer in the window has full
exploitability within ρ_m+ε_m of η(r_m); this is not a selected favorable
profile premise.

For the smooth objective, the one-sided derivative of the inner minimum
is the minimum of the own-singleton gradient over its actual argmin set.
Compactness and uniform differentiability justify this formula. The finite
sum of these minima is the minimum over source tuples. Separating the
convex hull of their FOUR-coordinate gradients from the cube normal cone
would give a feasible direction with strictly positive derivative for
every tuple, contradicting the outer maximum. Thus the required projected
normal exists, with the SAME softmax weights that differentiate the profile
objective at each source.

The remaining 56 gradient coordinates are not constrained by full-cube
normal signs. The full-gradient entropy pairing r_m·G_m remains valid,
but r_m·G_m=||G_m||₁ need not hold. The source explicitly drops that
identity and does not need it in any subsequent estimate. A singleton
projection equal to zero is allowed and suffices for the mean sign.

## 5. Uniform caps, calendar errors and one actual source

I checked the following points against both this candidate and its frozen
coupled/silent dependencies.

1. The same selected table and same tester pool are used in every adjacent
   calendar difference. The Δ_N telescope is therefore legitimate.
   Chord gains have |g′|≤16 and |g″|≤96, so the Hessian bound
   H=96+256/τ gives the claimed square-root comparison with f_(N+1).
   The multiplier is the original softmax derivative, not a new witness.
2. At the fixed limit table r_∞, the checked MAX-minimum margin gives
   B_i−s_i≥Ω_b. Together with B_i≤1 this excludes the upper singleton
   faces. The projected normal therefore has each singleton component
   nonpositive, giving exactly the mean scalar pressure sign.
3. The stronger finite-source margin B_i−s_(m,i)≥Ω_b/2 holds uniformly
   over ALL inner minimizers in ALL retained calendars. A violating
   sequence, reused literally at r_∞, has a compact semantic subsequence
   tending to a global MAX minimum and contradicts the checked margin.
   No actual attainment of that limiting semantic point is required.
4. Shifting the clocks by one preserves payoffs and gives cap max(s_i,B_i).
   The proved strict margin makes this equal to B_i, including for signed
   s_i. The lost late labels and added initial labels give exactly
   Ẑ/Z=1−ℓ_N+a_N. The bound ℓ_N≤1/d_N is on the SUM over owners,
   while a_N≤4exp(−σ/τ). The new initial labels are exponentially small,
   not merely an O(ε) error that could survive the Hessian scaling.
5. The row reindexing transports actual terminal-law vectors. It therefore
   controls the singleton-indicator account itself. Equality of gain
   values alone would not prove this step.
6. Dropping the final two calendars makes N+3≤L. The shifted profile uses
   finite dates 1,...,N, while competitors range through finite date N+2.
   The response at N+3 remains present and distinct from N+2 on that
   entire domain. Never is a separate response. No after-menu branch is
   identified merely because its source value was duplicated.
7. The same new λ̂ gives the enlarged-direction inequality and all-owner
   bound by the literal Quit0 screen. This step does not use an unrelated
   all-owner multiplier or the all-ties theorem.
8. The three-adjacent-gap average, discarded-mass bound, and scalar
   averaging select ONE actual source together with its own λ̂. Positive
   all-owner weights, small directional error, small inactivity and the
   pressure upper bound all remain true at that same source.
9. When passing to r_∞ the old λ̂(r_m,p_m) is retained. The 2δ_m, 4δ_m
   and 16δ_m error bounds respectively suffice for regret, inactivity and
   all simultaneous derivatives. No uncontrolled re-softmaxing at a
   possibly much smaller temperature is performed.

These checks reconstruct the complete transfer, rather than assuming that
restricting the reward parameters leaves an unspecified source unchanged.

## 6. Falsification attempts and dependencies inspected

An exact rational script tested 30 signed reward tables, α=1/13 and all
eleven nonsingleton coalitions: all 330 stretch identities and invariance
checks under arbitrary changes of the four own singletons passed. The tests
included tied endpoints, negative directed gaps and saturated cube faces.
They test identities, not the unknown premise Ω>0.

The potentially fatal alternatives were explicitly checked:

- A singleton pure profile cannot be included in the conclusion by the
  same reasoning: deleting its only quitter exposes the tail and its own
  singleton reward enters its cap. The source restricts to |S|≥2.
- A positive gap of some pure profiles alone would not permit stretching
  all minima uniformly; here EVERY pure profile has gap at least Ω.
- Freezing the own singletons instead of freeing them would lose the
  desired normal signs. The candidate freezes the other 56 coordinates.
- Reusing the original full-cube normal after changing the family would
  be false. The candidate reconstructs the projected normal from the
  new optimization.
- A projected normal at one table does not make any retained source
  individually normal. The candidate extracts only its total scalar
  pressure sign and expressly disclaims individual normality.
- The strict pure-profile separation is not a low-regret producer or an
  upper bound on non-pair mass. The final nonclaims are accurate.

Exact declarations inspected in their source files, without a new build:

- `quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card`
  in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`;
- `abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close` in
  `Research/Quitting/TerminalExploitabilityRewardRobustness.lean`;
- `escapeAwareQuantileClock_fin4_normalized_quantitative_bracket` and
  `quantileClockSupport_fin4` in
  `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`, together with
  the actual finite-clock realization interface already checked in the
  linked primary audit;
- `minimumTerminalSemantic_exploitabilitySingletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`.

The original coupled certificate remains frozen at SHA
`fade3cb825778caf0c76a1a4d6b9820e43bd6f430abf6f8af64b5c95973dd854`, and
the silent-source bridge at
`0e60914311f2ce46855e87a518400543607d0e2f233bce97f9fd70993b6754db`.
Their needed proofs were rechecked during this review. No external paper
or new semialgebraic theorem is needed.

## 7. Useful frontier delta and remaining test

The reduction genuinely removes the pure-pair equality branch from the
singleton-pressure SOURCE PROGRAM: one may restart that program at the
new singleton-box maximizer with a strict margin for all nonsingleton
pure profiles. It does not show that equality was impossible at the
original full-cube maximizer.

In particular, my independently derived near-pair full-cap estimate can now
use a genuine strict regret margin at these actual near-minimizers, rather
than assume it. This supplies a positive pair-spread floor. Consuming that
floor, or deriving an improving law from the non-pure source that remains,
is still a separate task. Any proposed use of a frozen-coordinate reward
normal or a transferred arbitrary-source mixed sign remains outside this
reviewed theorem.

## 8. Final-byte acceptance

**PASS on the final 515-line mathematical-name packet**, SHA256
`1fdefe4acb70e12b789e045885bc8711cea707daa059a70daab197623afbaa70`,
at the final link near the top of this review. No mathematical objection
remains. No author or export file was edited by this reviewer.

I read all bytes of the preceding mathematical-name version
`af7ed43da3c11c83a346ce6c686a99376d0233b6a7205f7073b1a9b8d9fe3bcb`
and its complete diff from the originally reviewed `7063965c…` candidate.
The last revision adds only the 21-line definition block at the beginning
of Section 4. Removing precisely that block reproduces the full af7ed43…
hash, so there are no unexamined changes elsewhere. The new definitions of
the complete terminal laws, owner-supported signed coefficient vector,
gain, separate zero label, and simultaneous independent marginal chord
match the objects used in the proof. In particular the chord is not a
public lottery over two product profiles.

The additions did create a few explicit handoff obligations beyond prose
cleanup, all of which check:

- The equivalence η>0 with a fixed all-behavior gap uses an actual response
  strictly exceeding η/2, not an assumed cap attainer at gain η. I inspected
  `HasTerminalExploitabilityGap` and
  `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`, and
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
  Their quantifiers are exactly the claimed endpoint.
- Positive COMMON reward scaling normalizes an arbitrary finite table
  without changing zero versus positive η. I inspected
  `quittingTerminalExploitabilityInf_scaleQuittingReward` in
  `Research/Quitting/TerminalExploitabilityRewardRobustness.lean`.
  No affine shift or normalization to nonnegative singletons is used.
- The finite pure-response interface agrees with
  `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.
- The new accuracy/depth formulation follows from N_m→∞, convergence of
  all errors, the limsup pressure bound, and the eventual uniform owner
  floor. Thus b, γ, Ω_b and r_∞ remain fixed before ANY accuracy/depth
  request; no table reselection was hidden in that reformulation.
- The explicit edge, equality, saturation, signed-singleton and Never
  boundary tests are exact. The implementation outline preserves the
  restricted normal and the distinct new tester and does not describe a
  conjectural consumer as an implemented or proved result.

The core proof, all actual-profile source quantifiers, signed reward scope,
and partial-normal tradeoff are unchanged and remain accepted.
