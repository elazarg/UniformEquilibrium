# Independent audit of the weak-inverse extension

Reviewer: CODEX_RADO_BOUNDARY.

Verdict: PASS for the weak-inverse extension, as ordinary mathematics using
the separately audited strict-inverse Fin4 theorem as an input. No unresolved
mathematical objection was found. This is not a new audit of that strict
theorem, an acceptance of an unseen final export, or a Lean check.

Reviewed source:
[CODEX_NOETHER_SUPPORT__NONNEGATIVE_INVERSE_APPROXIMATION_ON_ZERO_DIAGONAL_TABLES.md](../notes/CODEX_NOETHER_SUPPORT__NONNEGATIVE_INVERSE_APPROXIMATION_ON_ZERO_DIAGONAL_TABLES.md).

Frozen source SHA-256:
`cd4f3064d224e570e8b9c221578af6b96edc10370d01a80a9f44ddaf9547a501`.

The hash was checked before and after the substantive audit. I formed this
verdict without reading any other review or obtaining another reviewer's
verdict. I read the statement of the strict input at
[CODEX_FRECHET_CYCLE__INVERSE_POSITIVE_DISCOUNTED_INDEX_ESCAPE.md](../notes/CODEX_FRECHET_CYCLE__INVERSE_POSITIVE_DISCOUNTED_INDEX_ESCAPE.md),
whose SHA-256 is
`0d1a77885542d00559e3a146abc9e40bd1f47884b81be73c571a062d7419702a`.
Its unrestricted, signed, raw-table Fin4 conclusion is the only substantive
external mathematical input assumed here. No paper theorem is independently
invoked by this review.

## Exact claim checked

There are four players. At each live date each independently chooses Continue
or Quit, observing the public history; the first nonempty quitting coalition
S absorbs at reward vector r(S). Rewards are arbitrary real numbers and Never
pays zero. A behavior strategy assigns a probability distribution on the two
actions at every finite history. A unilateral deviation may replace that
entire strategy.

Put s_i = r_i({i}) and Γ_ij = r_i({j}) − s_i, with recipients indexing rows
and quitters indexing columns. The claim is:

    det Γ < 0 and Γ⁻¹ ≥ 0 entrywise
      imply existence of one uniform-equilibrium payoff v.

Here v is chosen before the accuracy. For every η > 0 there must be a behavior
profile p and one horizon threshold N such that every horizon T ≥ N gives
expected average payoffs within η of v and caps the gain from every complete
unilateral behavioral replacement by η. The profile and N may depend on η.

The strict theorem being used has the same conclusion and raw-table scope,
with Γ⁻¹ strictly positive entrywise. The present review checks removal of
that strictness through actual reward perturbations and existence closedness.

## Matrix density: proof and falsification attempts

Write B = Γ⁻¹, K = J − I and T = BK. Since B and K are entrywise nonnegative,
T is nonnegative. The factorization is in the correct order:

    Γ − εK = Γ(I − εBK),
    (Γ − εK)⁻¹ = (I − εBK)⁻¹B
                = B + εBKB + ε²BKBKB + ···.

For ε‖BK‖∞ < 1, the series converges in the submultiplicative maximum row-sum
norm. Multiplication of finite geometric sums leaves a remainder tending to
zero, so it supplies a genuine inverse. All displayed and subsequent terms
are nonnegative. There is no cancellation being ignored.

Fix an entry (i,j). Positivity of B_ij or (BKB)_ij proves strict positivity
of the inverse entry. In the remaining case, the equality

    (BKB)_ij = Σ_(k≠l) B_ik B_lj = 0

forces the support of row i and the support of column j to be the same
singleton {k}. To check that step, choose any positive entry in that row and
any positive entry in that column; their indices must coincide. Pairing
either chosen entry with every other entry of the opposite support then
forces both supports to contain only that index. Invertibility ensures both
supports were nonempty.

There must be u,v outside {k} with B_uv > 0. Otherwise every row outside k
would be a multiple of the row vector supported at k. When n ≥ 3 there are
at least two such rows, contradicting invertibility. Thus

    B_ik K_ku B_uv K_vk B_kj > 0

is one term of (BKBKB)_ij. The fact that u and v may coincide is harmless:
the two K factors only require u ≠ k and v ≠ k. This completes the missing
entry check without assuming irreducibility, a positive diagonal, or a
positive first-order correction.

The diagonal is unchanged because K has zero diagonal. The same series
argument proves invertibility for every t in [0,ε], not just at the final
endpoint. Consequently det(Γ − tK), a continuous nonzero real-valued
function on that interval, keeps the sign of det Γ. This verifies the
negative determinant hypothesis needed by the strict theorem.

I attempted the following exact falsifiers.

- For the four-cycle permutation Γ in the note, B and BKB both vanish at
  (0,2), (1,3), (2,0), and (3,1). Thus first-order positivity really fails.
  The second-order argument covers these entries.
- Exact rational computation reproduces the note's entire inverse at
  ε = 1/20 and gives det(Γ − εK) = −129523/160000. More generally its
  determinant is (1 − 3ε)(ε − 1)(ε² + 1). This also illustrates why
  sufficiently small ε is essential: a determinant zero is reached at 1/3.
- I independently enumerated all 150 permutation matrices in dimensions
  3, 4, and 5 and checked entrywise positivity of B + BKB + BKBKB with
  exact integer arithmetic. These finite checks support, but do not replace,
  the proof above.
- In dimension two, Γ = [0 1; 1 0] has negative determinant and nonnegative
  inverse. Every invertible zero-diagonal 2-by-2 matrix has inverse with
  zero diagonal, so no perturbation confined to that slice can have a
  strictly positive inverse. The stated dimensional restriction survives
  this falsification attempt. It is a density obstruction, not a UE
  obstruction.
- On four players, two disjoint transposition blocks have determinant +1
  and nonnegative inverse. The same perturbation retains positive determinant
  near zero. Thus the density lemma does not silently manufacture the
  negative sign or justify removing it from the strict-theorem invocation.

The general density lemma is valid for n ≥ 3. The game conclusion checked
here remains specifically Fin4 because that is the scope of the assumed
strict-inverse existence theorem.

## Literal table adapter

For i ≠ j set r_i^ε({j}) = r_i({j}) − ε; keep r_i^ε({i}) = s_i and keep
every reward coordinate at every coalition of size at least two. Then the
new gap matrix is exactly Γ − εK and the sup-norm table distance is ε.
There are precisely twelve changed coordinates. All four own singleton
coordinates and all 44 nonsingleton coordinates remain fixed.

This is a legal table for every ε because the input class allows arbitrary
signed real rewards. The player set, actions, states, transition, and Never
reward are identical. The strict input therefore applies to each sufficiently
small positive perturbation without any hidden normality, sign, or reward
translation condition. Its resulting targets, profiles, and punishment
values may vary. The adapter needs no assertion that those objects are
preserved.

## Reward continuity for every behavioral deviation

The same behavior strategy is available in the original and perturbed games.
At every public history it makes exactly the same random choice; changing
the reward table does not change any transition. Hence all finite-history
laws and all absorption-coalition probabilities are equal for a fixed
profile. This statement also holds after replacing any player's entire
behavior strategy by any other strategy.

More explicitly, if r and r′ are at sup-norm distance at most d, for each
profile p let π_p(S) be its probability of eventually absorbing at coalition
S. These numbers are table-independent, nonnegative, and sum to at most one.
For every i,

    |U_i^r(p) − U_i^r′(p)|
      = |Σ_S π_p(S)(r_i(S) − r′_i(S))|
      ≤ d Σ_S π_p(S) ≤ d.

The same calculation holds for p[i←τ_i], for every complete behavioral τ_i.
Never contributes zero to both tables. No interchange of a limit and a
response supremum, no uniform convergence of terminal laws, and no
cap-attaining strategy is being assumed.

In particular, every α-terminal-Nash profile p for r′ satisfies, for every
i and τ_i,

    U_i^r(p[i←τ_i])
      ≤ U_i^r′(p[i←τ_i]) + d
      ≤ U_i^r′(p) + α + d
      ≤ U_i^r(p) + α + 2d.

This direct inequality proves the needed full-deviation statement even
without introducing response caps. The note's cap inequalities are also
valid: each response family is nonempty and bounded by the finite reward
bound, and the pointwise d estimate transfers to its supremum in both
directions. Taking the maximum of cap-minus-prescribed-payoff over the four
players gives the stated 2d exploitability estimate.

Stopping-law language does not introduce additional information or public
randomization here. Until absorption the only possible public history is
the live all-Continue history at its date. The inspected behavioral adapter
and replacement lemmas justify the same conclusion for the actual strategy
class. In fact the direct history-law proof already suffices.

## Fixed target and the actual terminal consumer

For any requested η > 0 choose a sufficiently small perturbation with
table distance d < η/4. Its UE existence, through the actual reverse terminal
consumer, gives a terminal η/2-Nash profile. The displayed estimate makes
the same profile terminal η-Nash for the original table. This establishes
terminal approximate Nash existence at every positive error for that one
original game.

I read both directions and the proof of
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
In particular:

- `quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff`
  accepts a fixed UE target and supplies a behavior profile at every
  terminal error.
- `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
  accepts exactly the target-free all-errors conclusion obtained above.
- Its reward-cube proof chooses terminal equilibria at errors 1/(n+1),
  extracts a convergent subsequence of their finite-dimensional bounded
  payoff vectors, and invokes the fixed-target convergence consumer. The
  resulting target is fixed before the final UE accuracy is chosen.
- The imported
  `quittingGame_isUniformεEquilibrium_of_terminalNash`
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformization.lean`
  accepts arbitrary signed finite reward tables and allows every behavioral
  deviation. It needs a strictly larger uniform error, which the compact
  selection proof supplies. No restriction to stationary deviations is
  present.

Thus the note is correct to avoid assigning a common target to the
approximating games. Compact selection is performed for terminal profiles
in the original game, where the target-free consumer applies exactly.

## Source correspondence and handoff observation

In addition to the terminal declarations above, the following actual sources
were inspected to check the semantic steps rather than inheriting them from
the candidate.

- `quittingGame`, in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Game.lean`:
  reward-independent states, Boolean actions and transitions; zero live
  payoff and absorbing coalition rewards.
- `StochasticGame.Hist`, `StochasticGame.BehaviorStrategy`,
  `StochasticGame.BehaviorProfile`, and `StochasticGame.stageActionDist`, in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Core/Basic.lean`:
  complete public histories and independent behavioral action laws.
- `StochasticGame.IsεAsymptoticNash`, in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Asymptotic.lean`:
  quantification over every whole behavioral replacement.
- `StochasticGame.IsUniformEquilibriumPayoff`, in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Uniform.lean`:
  one target, one profile and threshold per accuracy, all later horizons.
- `quittingTerminalPayoff` and
  `tendsto_finiteAveragePayoff_quittingGame`, in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Asymptotic.lean`:
  absorption-mass expectation and its finite-average interpretation.
- `quittingBehaviorStoppingLaws_update`,
  `quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws`, and
  `quittingBehaviorDeviationPayoffCap_eq_pureTime`, in
  `UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`:
  actual replacement semantics, with the directly imported
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean` also inspected.
- `normalizedSoloMatrix_eq_soloReward_sub`, in
  `UniformEquilibrium/Quitting/Classification/PreemptionGateDictionary.lean`:
  the recipient-row, quitter-column orientation agrees exactly.
- `quittingUniformEquilibriumPayoffConjecture`, in
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean`:
  the intended fixed-payoff target and the larger still-open quantification.

A useful existing formalization route was also found in the same
`UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Uniform.lean`:
`StochasticGame.histDist_withStagePayoff`,
`StochasticGame.abs_finiteAveragePayoff_withStagePayoff_sub_le`, and
`StochasticGame.IsεHorizonNash.of_withStagePayoff` already express the shared
history law, payoff error d, and Nash error 2d for arbitrary behavior.
`StochasticGame.isUniformEquilibriumPayoff_of_uniform_stagePayoff_limit`
proves closedness when the targets also converge. Its target-convergence
hypothesis must be supplied if that alternate route is used. The note's
terminal selection route supplies its own valid target-free argument.
These declarations are an opportunity to reuse existing machinery, not a
mathematical objection or a claim that the new density composition is
already formalized.

This was a source-level audit plus exact matrix computations; no Lean build
was run. No author file, Lean file, shared index, or export was edited.

## Accepted scope and remaining check

The accepted conclusion is existence of an unrestricted behavioral uniform
equilibrium payoff for the stated Fin4 weak-inverse class. It does not give
a stationary equilibrium, an exact terminal Nash profile, a prescribed
payoff target, continuity of equilibrium strategies, or arbitrary-player
coverage. The matrix-density argument is broader than the strategic input;
that distinction must remain explicit.

No repair is required for the frozen candidate. A final packet must retain
the exact raw-table strict theorem as an independently supported input and
include this density, literal-table adapter, and fixed-target closure
argument. Acceptance here attaches to the recorded source hash and to this
bounded extension; the separate final-packet gate remains to be checked.

## Final-byte integration acceptance

Final packet checked:
[INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE.md](../notes/INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE.md).

Exact final packet SHA-256:
`d9bdaba02feaaab171c943c1aeb1f19cec3dcb3fa9c326817a071eeb01d474eb`.

Verdict: PASS for integration of the independently accepted weak-inverse
extension into these final bytes. No mathematical correction is required in
the material covered by this review. This addendum checks the final statement,
Sections 7.5 and 8, the extension's source correspondence in Section 9, its
handoff and scope in Section 10, and related strict-versus-weak distinctions.
It does not reopen the strict core, which retains its separate reviews. No
other feedback was read in making this integration check.

Section 1 states exactly the accepted Fin4 class: arbitrary real reward
coordinates, zero Never payoff, det Γ < 0, and entrywise nonnegative inverse.
It explicitly fixes one payoff target before all accuracies and quantifies
over complete behavioral deviations at every sufficiently large horizon.
The opening of Section 2 correctly limits the discounted localization
argument to the strictly positive inverse case. It does not claim that
the unperturbed weak boundary satisfies that localization or its strict
cone implication.

Section 7.5 retains the exact four-cycle matrix, rational inverse, vanishing
first-order entries, and two-dimensional density obstruction checked above.
Section 8.1 preserves the correct factorization, the convergent nonnegative
inverse series, the shared-singleton support argument, the n ≥ 3 rank
contradiction, the strictly positive second-order term, and invertibility
along the entire determinant-sign-preserving segment. Its actual table
adapter changes exactly the twelve off-own singleton coordinates and keeps
Never zero. The invocation of the strict core is expressly its raw-table
UE conclusion; preservation of auxiliary normality or selected targets is
not being assumed.

Section 8.2 defines full behavioral response caps and regret explicitly.
Its reward error bound holds for every prescribed and deviated profile,
using the same outcome law, and its passage to suprema and the finite
maximum is justified by boundedness. Choosing ε < η/4 and a terminal
η/2-Nash profile gives strict original-game regret below η. The passage
to one fixed target uses exactly the two actual terminal consumers
independently inspected in this review. No common target or convergent
equilibrium strategy family is presumed for the perturbations.

Section 9's extension-related source claims agree with those declarations.
Section 10 correctly treats the density/composition as ordinary mathematics
awaiting formalization, keeps the strategic conclusion in Fin4, and
separates it from stationary exact equilibrium, prescribed targets, and
the general conjecture. The existing stage-payoff stability helpers noted
above remain available to a formalizer; their omission from the frozen
packet is not an objection and requires no byte change.

This addendum supplies exact-final-hash acceptance for my bounded
extension/closure gate. It supersedes the earlier deferral of that
integration check, while leaving the strict core and unrelated packet
claims to their designated independent reviews.
