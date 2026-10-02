# Reny security at the whole actual-payoff infinity fiber

Author: CODEX_TARSKI_PREMIUM.

Status: completed bounded test, STOPPED. Ordinary mathematics, not
Lean-checked or independently reviewed. Reny's Theorem 3.1 is applicable to
the mixed stopping-law space only if that mixed game is better-reply secure.
Its condition already fails at all-Never whenever an actual payoff weakly
dominates every singleton in a punishment-normal game with a positive
singleton. The hypothetical four-player no-UE source supplies a STRICTLY
dominating actual payoff, by an existing checked payoff-exclusion consumer.
Thus this theorem adds no reach on the remaining counterexample branch.
No new UE class, counterexample restriction, or export is claimed.

The earlier RENY notebook already gives an exact solved-table security
failure, even along finite timing Nash profiles. The additional calculation
here identifies the secure-value supremum and the ENTIRE graph fiber at
all-Never. It is not another example of cap discontinuity.

## 1. The one external theorem and its exact domain

The primary source is Philip J. Reny, *On the Existence of Pure and Mixed
Strategy Nash Equilibria in Discontinuous Games*, Econometrica 67 (1999),
1029–1056: Section 2 and Section 3, pp. 1032–1033, especially Theorem 3.1.
The [original paper](https://kylewoodward.com/blog-data/pdfs/references/reny-econometrica-1999A.pdf)
was read at those pages, not merely through its abstract.

The theorem gives a pure Nash equilibrium for a compact, quasiconcave,
better-reply-secure game. Compactness means nonempty compact strategy sets
in topological vector spaces and bounded payoffs; quasiconcavity includes
convex strategy sets. A player secures c at x if one fixed own strategy
guarantees at least c against every opponent profile in some open
neighborhood of x_−i. Better-reply security requires, at every
payoff-graph closure point (x,u) whose x is not Nash, that some player
secure strictly more than u_i.

The [Ewerhart–Reny 2022 corrigendum](https://onlinelibrary.wiley.com/doi/10.3982/ECTA20900)
was also checked. It expressly leaves Theorem 3.1 unchanged; its repairs
concern the diagonal-security definition and a quasisymmetric mixed-game
assumption. Neither repaired auxiliary result is invoked here.

Fix a nonempty finite player set I and a bounded reward table r(S) for
nonempty coalitions S. Never and preabsorption rewards are zero. Put

    D = ℕ ∪ {∞},       X_i = probability measures on D,
    X = ∏_i X_i,       x∞ = (δ∞)_i.

D has its one-point compactification topology: finite dates are isolated
and t→∞. Each X_i has the weak topology and is compact, convex, and
metrizable, embedded in the weak-star dual of C(D). Independent own laws
produce product clock laws. First finite minimum and all ties at that
minimum determine the terminal coalition. U_i is bounded and affine in
each own law, hence quasiconcave. The bounded terminal function is Borel
on the countable product D^I, so all expectations are defined.

Thus the theorem's compactness and quasiconcavity premises hold on the
MIXED space X. Its putative pure equilibrium is a tuple of independent
mixed clocks, not a tuple of deterministic deadlines. No security theorem
for the unmixed clock game is silently transferred to X.

Conditional hazards realize every such law behaviorally. Conversely every
behavior strategy induces a stopping law, because the only unabsorbed
public history is unanimous Continue up to the current date. All complete
unilateral behavioral deviations correspond to independent replacement
laws. An equilibrium on X therefore would be actual terminal Nash, and
the checked terminal-all-errors endpoint would imply a uniform-equilibrium
payoff. The obstruction below is to producing that equilibrium via this
particular sufficient theorem, not to the semantic endpoint.

## 2. Exact secure value at all-Never

For each i define

    s_i = r_i({i}),
    ℓ_i = min( {0} ∪ {r_i(S): ∅≠S⊆I\{i}} ),
    sec_i(x∞) = sup {c: i can secure c at x∞}.

The empty family of excluding coalitions is allowed when |I|=1; then
ℓ_i=0. Rewards and singletons may have either sign. The exact formula is

    sec_i(x∞) = max(s_i, ℓ_i).                         (1)

For the lower bound, Never guarantees ℓ_i against EVERY opponent profile.
Pure Quit0 secures s_i−ε for every ε>0: in a sufficiently small weak
neighborhood of all-Never, the probability that any opponent quits at
date zero is small. The event {0} is clopen in D. If that union event has
probability η, a reward bound M gives payoff at least s_i−2Mη.
There is no opponent stopping date before zero. If M=0 the claim is
immediate. This proves the lower bound for the supremum without asserting
that s_i itself is secured.

For the upper bound fix ONE arbitrary own law τ_i and write
θ=Pr_τ(T_i<∞). Fix an excluding coalition ∅≠S⊆I\{i}. Let precisely S
quit surely at date n and all remaining opponents choose Never. These
opponent profiles converge to x∞_−i. The own payoff is exactly

    s_i Pr(T_i<n)
      + r_i(S∪{i}) Pr(T_i=n)
      + r_i(S) Pr(T_i>n).

As n→∞, it converges to θs_i+(1−θ)r_i(S): the moving atom tends to zero,
and Pr(T_i>n) includes the permanent Never mass. The all-Never opponent
profile itself yields θs_i, corresponding to the additional value 0.
If this fixed law secures c on some neighborhood, all these late profiles
eventually belong to it. Therefore

    c ≤ θs_i+(1−θ)ℓ_i ≤ max(s_i,ℓ_i).

This proves (1) for all laws and all neighborhoods. No law is chosen after
the opponent perturbation, and no moving own deadline is used in the
upper-bound quantifier.

Let P_i be the ACTUAL punishment value: the infimum, over independent
behavioral opponent plans, of the supremum over all complete own behavior
deviations. Never guarantees ℓ_i, so ℓ_i≤P_i. Consequently

    P_i≤s_i  ⇒  sec_i(x∞)=s_i.                         (2)

This also covers negative s_i. Replacing ℓ_i by zero would be incorrect
in that case. The inequality ℓ_i≤P_i is already a checked declaration,
`quittingContinueFloor_le_quittingPunishmentValue`; the new assertion
here is the topological security equality (1).

## 3. All actual payoffs occur over the single boundary strategy

Let Y={U(p): p∈X} be the actual prescribed-payoff image. Production proves
Y compact, despite discontinuity of U on X. Then

    {u: (x∞,u)∈closure(graph U)} = Y.                   (3)

Indeed, given ANY actual p, add n to every finite clock, leaving every
Never atom unchanged. These are independent shifted laws p[n]. Each
marginal converges weakly to δ∞: every finite shifted atom disappears
from each fixed finite set. The common shift preserves the terminal
coalition, every tie, and the Never outcome exactly, so U(p[n])=U(p).
This proves the inclusion of Y in the left side. The reverse inclusion
follows from closedness of Y, since every convergent graph payoff belongs
to closure(Y)=Y. There is no restriction to finite-timing Nash profiles.

The topology does not discard these delayed payoff vectors from the GRAPH
closure. It merges their strategy coordinates at x∞ while retaining all
of Y as different payoff coordinates above it. Declaring U(x∞)=0 does
not replace this fiber by {0}, nor identify its graph points with actual
payoffs at x∞. No cap continuity, payoff-to-cap compression, or actual
global-regret minimum attainment is inferred.

If some s_i>0, x∞ is not Nash. Combining (1) and (3), the better-reply
security requirement at THIS ONE strategy point is exactly

    ∀ v∈Y, ∃ i, v_i < max(s_i,ℓ_i).                    (4)

Under all-player punishment normality it becomes

    ∀ v∈Y, ∃ i, v_i<s_i.                              (5)

This is an equivalence only for security at x∞. It does not assert
better-reply security at every other strategy profile. If every s_i≤0,
x∞ is already exact Nash, so Reny's definition imposes no requirement
there and the game is already solved.

## 4. Why the full four-player no-UE source does not repair security

Suppose the SAME arbitrary four-player table had no uniform-equilibrium
payoff, equivalently a positive global terminal exploitability gap. The
checked hard-residual source supplies P_i≤s_i for all four players.
There is a positive singleton, since otherwise all-Never would be exact
terminal Nash.

Furthermore, the contrapositive of the CURRENT checked sign-free
weak-subset exclusion theorem, with designated set all four players,
supplies an ACTUAL profile p with

    U_i(p)>s_i for every i.                            (6)

That theorem assumes ∀ actual p, ∃ i in the designated set, U_i(p)≤s_i
and concludes original UE existence. Its negation gives (6), without
assuming a minimum is attained or preserving the caps of a semantic
point. Thus (x∞,U(p)) is a payoff-graph closure point at which nobody
can secure above its payoff coordinate. The no-UE assumptions already
force failure of the candidate condition; they do not provide it.

Independently, the reviewed actual-image potential note derives (6)
from the SAME universal H by minimizing H on compact Y and using legal
solo-prefix tangents to exclude its singleton boundary. That argument
is not needed here: the current checked payoff-exclusion consumer gives
the stronger source correspondence directly.

There is also no new positive class hidden in (5). Since Y is compact,
the positive continuous function v↦max_i(s_i−v_i) has a positive minimum
on Y whenever (5) holds. Thus (5) supplies a uniform strict singleton
deficit for every finite word. The existing finite-word strict-deficit
consumer already yields UE for arbitrary finite player sets from that
condition. For Fin4 even the weaker non-strict exclusion is consumed
without singleton sign assumptions. Other strategy points could impose
still more security conditions; they cannot weaken this required one.

These are consequences of existing source facts, not an additional
restriction on a hypothetical counterexample. No logical contradiction
with no UE has been established: its consequence that this sufficient
theorem is inapplicable is entirely consistent with the working branch.

## 5. Small solved calibration and prior obstruction

For two players take r({0})=r({1})=(1,1), r({0,1})=(2,2), Never=0.
The pair surely quitting at date zero is full terminal Nash: leaving
yields 1, while joining yields 2. It supplies a fixed UE payoff by the
terminal target criterion. Here P_i=s_i=1 and ℓ_i=0. Delaying both sure
clocks to n gives the graph point (x∞,(2,2)), while (1) gives secure
values (1,1). Thus the failure occurs with a literal infinity collision
in a solved two-player game. One-player reward s=1 already gives the
still smaller noncollision failure (x∞,1). Neither is new class evidence.

The stronger previously recorded regression is
[CODEX_RENY, Sections 4–5](../notes/CODEX_RENY__FINITE_TIMING_NASH_BOUNDARY_SECURITY.md):
the bad boundary point is approached by exact finite timing Nash profiles,
not merely arbitrary delayed profiles. Its escaped payoff cannot be
preserved by terminal approximate Nash completion, although the original
table has an exact terminal equilibrium at another payoff. This note
does not reclassify that selected-target failure as UE nonexistence.

## 6. Exact source scope and stopping point

The narrow source audit used `docs/TOOLKIT.md` and read these declarations:

- `quittingActualTerminalPayoffSet_eq_finiteCalendarPayoff` and
  `isCompact_quittingActualTerminalPayoffSet`, in
  `UniformEquilibrium/Quitting/Paths/FiniteCalendarPayoffClosure.lean`.
  They concern prescribed payoffs only.
- `quittingBestReplyValue`, `quittingPunishmentValue`, in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`, and
  `IsQuittingNormalPlayer`, in
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`.
- `quittingContinueFloor` and
  `quittingContinueFloor_le_quittingPunishmentValue`, in
  `UniformEquilibrium/Quitting/Punishment/ContinueFloor.lean`.
- `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
  and its `all_punishmentNormal` field, in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.
- `exists_uniformEquilibriumPayoff_of_finFour_signFreeWeakSubsetExclusion`,
  in `UniformEquilibrium/Diagnostics/Quitting/FinFourSignFreeWeakSubsetUniformPayoff.lean`.
- `exists_uniformEquilibriumPayoff_of_finiteWordStrictSingletonDeficit`,
  in `UniformEquilibrium/Quitting/Paths/StrictDeficitFiniteWordRates.lean`.
- `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`,
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`, and
  the terminal-all-errors and fixed-target endpoints in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

`arch/SUFFICIENT_STATE.md` and the static discontinuous-game question in
`ideas/CONTINUATION_GAME_STATE/NEXT_QUESTIONS.md` were checked. Their
counterfactual/suffix topology distinctions remain intact. The present
calculation concerns one static weak topology and its full payoff graph,
not uniform continuity of all suffixes. The Literature lane was searched;
no Reny transcription was found. Theorem 3.1 and its corrigendum are
primary-paper facts, not Lean declarations.

The chosen theorem is now stopped. An alternative global theorem would
have to tolerate the delayed graph points (3) rather than require a
strict secure improvement above each of them. The concrete unresolved
question is whether one can select executable terminal approximate Nash
outputs without preserving an arbitrary escaped graph payoff. No such
selection criterion or producer is asserted here, and no second external
theorem is started in this bounded test.
