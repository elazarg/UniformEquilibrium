# Direct compact-clock existence and the floor-removal budget

Identity: `CODEX_HILBERT`.

## Status and outcome

Ordinary mathematics, not Lean-checked; no export or conjecture resolution.
This is a bounded mechanism-mining record and one completed first test.

The selected mechanism is classical compact-convex-game existence applied
directly to complete private stopping laws with proper clock floors. It
does not turn horizontal best responses into temporal Nash–Bellman edges.
It genuinely produces actual profiles, and it allows unrelated profiles at
successive accuracies. Nevertheless, its proposed universal removal argument
fails: the relevant cost is an integrated probability of forced preemption,
not the size of an individual hazard. An exact game makes that cost actual
unrestricted regret even as every floor tends to zero.

The surviving conditional conclusion is precise: select restricted
equilibria whose **reward-sensitive loss from forcing an arbitrary complete
response** tends to zero. Compact-game existence alone does not select them.
The failed term is another escaping-clock/Never defect, not a newly identified
strategic obstruction in the positive-singleton hard class.

Only one mechanism is proposed for a fresh test. The bounded inventory below
explains why several mathematically distinct older methods are not relabelled
as untested alternatives. No new constant optimization, stationary-class
separation, local regression portfolio, or source-ancestry requirement is
introduced.

## 1. Scope of the mining and the semantic endpoint

Read the two idea catalogues, then the architecture records
`CONTROLLER_VS_TESTER.md`, `SEMANTIC_BARRIER_DUALITY.md`, and
`RECURRENCE_ARCHITECTURE_OBSTRUCTION.md`. The selected older chains were:

1. `ideas/CONTINUATION_GAME_STATE/README.md`,
   `MATRIX_STATE_REDUCTION.md`, and
   `FIXED_DEADLINE_HORIZONTAL_CONTINUITY.md`, together with
   `notes/CODEX_CEDAR__STOPPING_TIME_COMPACT_GAME.md`;
2. `notes/CODEX_CEDAR__DISCOUNTED_RADIAL_DEBIASING.md` and
   `notes/CODEX_SPINOZA__GROWING_PERIOD_HAZARD_CLOCK_AND_REPLICATOR_BOUNDARY.md`;
3. `ideas/QUESTION_BACKLOG/SIMON_LYAPUNOV_CERTIFICATE.md`,
   `ideas/SOCIAL_WEIGHT_REVIEW__SOURCE_RESPONSE_PORT_GAME.md`, and the
   source-anchored component test in
   `notes/CODEX_SPINOZA__SOURCE_ANCHORED_COMPONENT_AND_LAST_CHARGE_COLLAPSE.md`.

The catalogues are proposals, not necessity theorems. In particular, neither
projective compatibility of different finite approximants nor prior packaging
of chronological source ancestry is necessary for an existence proof.
The declaration
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
was inspected directly. Its positive side permits a different actual
behavioral profile at every positive error. It subsequently selects a fixed
uniform payoff. This is the endpoint used here.

### Already tested methods: do not count a vocabulary change as novelty

* **Discontinuous-game payoff security.** CEDAR's compact-clock note and
  RENY's finite-Nash boundary note give actual positive-singleton failures of
  closure-payoff security. A fixed finite-date response being continuous is
  not enough. This blocks direct application to the unrestricted weak compact
  law game, but not application to a genuinely continuous restricted game.
* **Discount/entropy removal.** CEDAR computes the exact unrestricted
  refusal price after radial debiasing. SPINOZA tests growing-period
  common-temperature soft cycles and identifies the nonvanishing cost on
  the scale needed by that compiler. Neither theorem is a universal no-go
  for player-dependent or whole-law regularization; both require a new
  removal estimate rather than another fixed-point existence assertion.
* **Browder components and Simon variation.** The source-anchoring subsidy
  really produces a component, but its endpoints need not be connected by
  play of the original game. Last-charge collapse only obstructs an exact
  positive block that must return to the specified all-Continue-basin tail.
  It does not obstruct direct selection of an unrelated terminal equilibrium.
  The Simon Lyapunov question still needs either an actual certificate and
  production necessity, or a general exclusion theorem. A potential on an
  arbitrarily selected response graph is not such a certificate.
* **Global duality.** The semantic barrier dual is an exact all-profile
  negative route and does not require chronological best-response edges.
  Its canonical barrier already encodes the unknown value. Producing an
  effective positive barrier is being tested independently; another
  formulation of its soundness is not a new experiment here.

A further narrow check found that the older overlapping-pair conjecture is
already the declaration
`twoOverlappingFirstStoppingMasses_sqrt_sum_le_one` in
`MathUE/Probability/OverlappingFirstStopping.lean`. Its statement was read;
it is not proposed again as a new global clock inequality.

## 2. The classical method and exact new input

The original source is I. L. Glicksberg, *A Further Generalization of the
Kakutani Fixed Point Theorem, with Application to Nash Equilibrium Points*,
Proceedings of the AMS 3 (1952), 170–174. Section 1, page 171 gives the
closed-graph, nonempty-convex-value fixed-point theorem on a compact convex
subset of a locally convex Hausdorff space. Section 2, pages 172–173 applies
it to best-response correspondences. The original text was read through a
[transcription of the paper](https://paperzz.com/doc/7085276/a-further-generalization-of-the-kakutani-fixed-point-theorem);
the [publisher's primary locator](https://www.ams.org/journals/proc/1952-003-01/S0002-9939-1952-0046638-5/S0002-9939-1952-0046638-5.pdf)
returned HTTP 403 on direct retrieval. No secondary theorem statement was
substituted for the paper.

The new input is a **uniform properness restriction on whole private laws**,
not a new root relation and not a private change of terminal rewards. It
makes prescribed payoffs jointly continuous on a compact convex strategy
domain. The cost is that deviations in this auxiliary game must satisfy the
same restriction. The unrestricted comparison is therefore a separate lemma.

### Exact first test

Can vanishing proper hazard floors give restricted Nash equilibria whose
unrestricted terminal regrets vanish, purely through a uniform floor-removal
estimate? Sections 3–6 prove existence, compute that estimate, and refute the
proposed universal vanishing conclusion.

## 3. Data and compact-game existence

Fix m ≥ 2 players and a reward table on nonempty coalitions, with
|rᵢ(S)| ≤ M. Never pays zero. Every player privately and independently draws
a planned stopping time in ℕ ∪ {∞}; the first finite minimum determines the
quitting coalition. These laws realize ordinary behavioral strategies, and
all unrestricted deviations are arbitrary complete stopping laws.

For each player choose floors ℓᵢ(t) with

    0 ≤ ℓᵢ(t) < 1,
    Lᵢ(t) = ∏[s < t] (1 − ℓᵢ(s)),
    Lᵢ(t) → 0.

Let Cᵢ be the independent proper censor clock with mass
cᵢ(t) = Lᵢ(t)ℓᵢ(t). Define Kᵢ(ℓ) to be the complete laws μ whose survival
Sμ(t) = Pμ(T ≥ t) satisfies

    Sμ(t + 1) ≤ (1 − ℓᵢ(t)) Sμ(t)                 (3.1)

at every date. Here {T ≥ t} includes Never. These are precisely the laws
whose conditional Quit probability is at least ℓᵢ(t) at every reached date.

### Proposition 1: an actual restricted equilibrium exists

The game with strategy domains Kᵢ(ℓ) has a Nash equilibrium p. This means

    Uᵢ(p) ≥ Uᵢ(μᵢ, p₋ᵢ) for every μᵢ ∈ Kᵢ(ℓ),

not yet for arbitrary laws μᵢ.

#### Proof

Probability laws on the one-point compactification ℕ ∪ {∞} form a compact
convex weak space. Finite initial cylinders are clopen, so each constraint
(3.1) is a closed linear inequality. Thus Kᵢ is compact and convex; it is
nonempty because it contains the censor law Cᵢ.

Induction gives Sμ(t) ≤ Lᵢ(t) uniformly for μ ∈ Kᵢ. Hence every such law is
proper, with a uniform finite-tail bound. Coordinatewise convergence on
finite atoms therefore implies total-variation convergence: first restrict
to a finite head, then bound the two omitted tails by Lᵢ(t). Consequently
the terminal payoff is jointly continuous on the product of the Kᵢ, by the
finite-product coupling estimate for a bounded observable. Own-law payoff
is affine. The product best-response correspondence has nonempty compact
convex values and a closed graph. Glicksberg's fixed-point theorem applies.

The fixed point is a vector of stopping laws, not a correlated distribution
over vectors of laws. No public lottery is used. ∎

The same compactness argument can be proved by finite-net finite games;
nested finite equilibria are not an input to this proposition.

## 4. Actual unrestricted-response comparison

For an arbitrary complete response τᵢ, draw its planned time Aᵢ independently
of Cᵢ and the opponents, and use

    Aᵢ^ℓ = min(Aᵢ, Cᵢ).

Its survival is Sτ(t)Lᵢ(t), so it belongs to Kᵢ(ℓ). This is a private
whole-strategy modification, with the usual conditional-hazard realization.
The censor has no effect on another player's random seed or actions.

Let Oᵢ = min[j ≠ i] Tⱼ under the actual equilibrium opponents. Put

    κᵢ(p; ℓ) = P(Cᵢ ≤ Oᵢ)
              = ∑[t ≥ 0] cᵢ(t) ∏[j ≠ i] Sₚⱼ(t).          (4.1)

The weak inequality in Cᵢ ≤ Oᵢ is deliberate: forcing a Quit at an
opponent's date can change the terminal coalition.

### Proposition 2: the floor-removal budget

Every restricted equilibrium supplied by Proposition 1 satisfies

    dᵢ(p) ≤ 2M κᵢ(p; ℓ)                                  (4.2)

for the ORIGINAL unrestricted terminal cap.

#### Proof

Couple the response Aᵢ and its censored version against identical opponent
clocks. Their terminal outcomes agree unless Cᵢ < Aᵢ and Cᵢ ≤ Oᵢ. A bounded
payoff changes by at most 2M on this event. Therefore, uniformly in every
complete response τᵢ, including Never,

    Uᵢ(τᵢ, p₋ᵢ) − Uᵢ(τᵢ^ℓ, p₋ᵢ)
      ≤ 2M P(Cᵢ < Aᵢ, Cᵢ ≤ Oᵢ) ≤ 2M κᵢ(p; ℓ).

The middle profile is a permitted unilateral deviation in the restricted
game, so its payoff is at most Uᵢ(p). Take the supremum over τᵢ. No cap
attainment, horizon bound, simultaneous best-response selection, or exchange
of limits with a supremum has been used. ∎

One must not replace (4.1) by a sum weighted by **prescribed joint survival**.
The deviator can remove its own prescribed stopping hazard. Its complete
response comparison retains opponent survival and its own censor survival,
not the source's own survival.

### What would be a direct positive consumer?

If a selection pⁿ of these restricted equilibria had κᵢ(pⁿ; ℓⁿ) → 0 for
every player, (4.2) would directly give actual terminal approximate Nash
profiles. The checked all-errors equivalence would then supply one uniform
payoff. The profiles need not have common ancestry or compatible prefixes.

This is a sufficient selection condition, not a producer of that condition.

## 5. The unremovable term in the uniform estimate

The opponents' floor constraints imply Sₚⱼ(t) ≤ Lⱼ(t), so

    κᵢ(p; ℓ) ≤ Kᵢ(ℓ)
      := ∑[t ≥ 0] cᵢ(t) ∏[j ≠ i] Lⱼ(t)
       = P(Cᵢ = minⱼ Cⱼ).                                (5.1)

All censors are proper. Their finite minimum exists almost surely; ties
may have more than one owner. Therefore

    ∑ᵢ Kᵢ(ℓ) = E |argminⱼ Cⱼ| ≥ 1.                     (5.2)

In particular these uniform removal bounds cannot tend to zero for every
player, for ANY choice of proper heterogeneous schedules. The issue is not
an avoidable factor in an estimate: somebody owns the first forced exit.

This alone does not refute the reward-dependent selection condition in
Section 4. Actual equilibrium opponents can absorb substantially before their
censors. The next test shows why the uniform conclusion really fails.

## 6. Exact falsifier: failure is actual regret, not merely a loose bound

Use the reward table

    rᵢ(S) = −1 if i ∈ S, and 0 otherwise.                 (6.1)

The all-Never profile is an exact terminal Nash equilibrium, and is an exact
uniform equilibrium as well: every deviation has nonpositive payoff. Thus
the game is solved; it is not a positive-singleton or no-UE example.

### Proposition 3: the censor profile is restricted Nash

For arbitrary proper floors as above, let each player use its censor Cᵢ.
This is a restricted Nash profile, and its unrestricted debts are exactly

    dᵢ(C) = Kᵢ(ℓ),  hence  maxᵢ dᵢ(C) ≥ 1/m.           (6.2)

#### Proof

Any permitted own law μ satisfies Sμ(t) ≤ Lᵢ(t), so it is stochastically no
later than Cᵢ. Against fixed opponents, the probability of being a first
quitter is nonincreasing as one's planned time becomes later. Thus the
censor law minimizes this probability among permitted laws and maximizes
payoff (6.1). More explicitly, quantile coupling makes a permitted own time
at most Cᵢ; the event {Cᵢ ≤ Oᵢ} is then contained in the event that the
modified own time is at most Oᵢ. This proves restricted optimality for every
player. Its payoff is −Kᵢ. Pure Never has payoff zero and every payoff is
nonpositive, so the unrestricted cap is zero. Use (5.2). ∎

This table gives a stronger explanation: **every** all-proper profile has
sum of unrestricted debts at least one, since absorption occurs surely and
at least one player is a first quitter. Thus no selection within the
all-proper strategy class can make the regret vanish in this game.

For a literal vanishing-floor sequence, take ℓᵢⁿ(t) = 1/n, n ≥ 2. Every
floor tends to zero at every fixed date and each censor remains proper. Its
debt is

    Kᵢ(ℓⁿ) = (1/n) / (1 − (1 − 1/n)^m) → 1/m.

No constant is being optimized: the positive limiting cost is the point of
the test. The unconstrained desirable deviation is Never; its constrained
replacement must eventually Quit and pay when it wins the forced clock race.

## 7. Relation to known obstructions and the new low-reach consumer

This is not CEDAR's payoff-security failure. The restricted game here really
is jointly continuous, so the compact fixed-point step succeeds. Nor is it
GIBBS's near-minimum one-row leakage obstruction: no positive global debt
minimum, cap–Nash root, or source-preserving splice is assumed. The failure
occurs when the restricted equilibrium is tested against an omitted
**complete strategy**, here Never.

The underlying noncompactness is nevertheless familiar. For each fixed n
there is no Never atom, while the stopping mass can escape completely as n
increases. Fixed-date smallness does not control the integrated counterfactual
exposure (4.1). This is a distributed proper-clock version of the cutoff/Never
boundary, not evidence for a new positive-gap mechanism.

The newly reviewed ordinary-mathematics ingredient
`notes/CODEX_ROOT__FINITE_MENU_PUNISHMENT_COMPLETION.md` is accepted here as
reported by its independent review, not re-reviewed. Its supplied small
JOINT reach completion changes the possible direct endpoint: an argument may
instead produce finite-menu approximate equilibria with sufficiently small
reach and invoke that completion. No exact spine or nested ancestry is needed.

Proper clock floors guarantee that each selected prescribed profile
eventually has small joint reach. They do **not** guarantee small
unrestricted finite-menu error after removing those floors. In (6.1), even
the deviation Never is already in every ordinary finite timing menu. Thus
the missing premise is strategic error, not low prescribed reach. One cannot
attach the completion to Proposition 1 merely because the induced clocks
are proper.

## 8. Source-facing boundary and the one remaining question

Additional narrowly inspected declarations and nearby definitions were:

* `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`: the exact
  whole-law, own-payoff affine identity;
* the compact-law and deleted-survival definitions in
  `UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`:
  uniform proper opponent tails control unrestricted caps; this is a
  supplied-sequence realization theorem, not the floor-removal selection;
* `IsProperQuittingBehaviorStrategy` and the scope of
  `StrategicallyPrecompactWatchdogProperBoundary.lean`: properness and
  proper strategic approximation are not universal restricted-game
  completeness assertions;
* the local ledger and minimum compensation statements in
  `notes/CODEX_GIBBS__CONSTRAINED_ROOT_NORMAL_WORK_AND_LEAKAGE_LEDGER.md`:
  whole-profile compact equilibrium is different from an arbitrary-u
  constrained one-row Nash prefix, although both can incur binding costs.

The fresh whole-law budget test is complete. The negative-membership
falsifier does not answer whether all-normal positive-singleton tables admit
a special selection with negligible reward-sensitive removal loss. No such
selection is asserted, and the race budget gives no reason to expect it.

The exact remaining question, if this mechanism is revisited, is:

> Can one use the ORIGINAL reward table to choose proper floors and a
> restricted Nash equilibrium p so that
> sup[τᵢ] (Uᵢ(τᵢ,p₋ᵢ) − Uᵢ(min(τᵢ,Cᵢ),p₋ᵢ)) tends to zero for all players,
> or directly control its ordinary finite-menu counterpart at a small-reach
> cut?

This is a reward-sensitive selection problem. It is not implied by shrinking
floors, existence, properness, or compactness, and is not retained here as a
new obligation of the existing chronological atlas.
