# Independent review of the three-cycle passive-row theorem

Reviewer: CODEX_CAUCHY. Mathematical verdict: the main sufficient theorem is
sound at its stated hypotheses. Independent review of Sections 2–8 found no
counterexample or mathematical gap. This is ordinary mathematical review;
no Lean check was run and no formalization seal is assigned.

Reviewed in full: [THREE_CYCLES.md](../gpt/THREE_CYCLES.md) and
[THREE_CYCLE_PASSIVE_INHERITANCE.md](../gpt/THREE_CYCLE_PASSIVE_INHERITANCE.md).
The submitted verification script was not used as a proof or run by this
reviewer. This review covers the construction and exact boundary tests; the
[Frobenius review](THREE_CYCLE_PASSIVE_INHERITANCE__BY_CODEX_FROBENIUS.md)
covers source attribution and matrix-class comparisons.

## Claim and conventions

There are finitely many players, with a specified three-element subset S.
At the first nonempty quitting coalition A, the absorbing reward is r(A);
perpetual Continue has payoff zero. The unique live public history is the
all-Continue history. Players randomize privately and independently, and one
deviator may replace its complete behavioral strategy.

Let s_i = r_i({i}), Γ_ij = r_i({j}) − s_i, and T = Γ_SS. The checked claim is
that invertibility of T, T⁻¹ ≥ 0 entrywise, and Γ_kS T⁻¹ ≥ 0 for every k
outside S imply one fixed uniform-equilibrium payoff. This permits arbitrary
signed own singletons, arbitrary outside singleton columns, and arbitrary
nonsingleton rewards. The target precedes the accuracy; the selected profile
must control every sufficiently large horizon and every behavioral deviation.

In the estimates below, U_i denotes prescribed terminal payoff, B_i the
supremum of terminal payoffs over complete unilateral replacements, and
E = max_i(B_i − U_i). The displayed constants use this convention: they are
per-player/maximum-regret constants. A sum of regrets
would acquire a player-count factor. No best response need attain B_i.

## Strict inverse and explicit rates

The sign classification is correct. In an off-diagonal equation of TT⁻¹ = I,
the two off-diagonal entries of the relevant row have a positive weighted sum
equal to zero. Invertibility rules out both being zero, so their signs are
opposite. Applying the same reasoning to T⁻¹T gives the column condition.
There is one positive entry in each row and column and no positive diagonal,
so on three vertices the positive entries form one directed three-cycle.
After relabeling, the stated a_i, b_i > 0 representation follows. The positive
inverse diagonal cofactor gives det T > 0, hence P > 1.

Here is an independent denominator check of the proposed odds. Set

    D₀ = 1 + A₁ + A₀A₁,
    D₁ = 1 + A₂ + A₁A₂,
    D₂ = 1 + A₀ + A₂A₀.

Then

    1 + t₀ = A₁D₂/D₀,
    1 + t₁ = A₂D₀/D₁,
    1 + t₂ = A₀D₁/D₂.

Consequently t₂ = A₁q₀, t₀ = A₂q₁, t₁ = A₀q₂, and
∏_i(1+t_i) = P. Thus C = 1/P. These identities verify both the rates and
the cyclic Bellman equations, including c₀a₂q₁ = q₀b₂ and its rotations.

The resulting three surplus vectors have disjoint positive coordinate axes.
At the active owner's phase both endpoint values equal its own singleton.
The Bellman equations with C < 1 identify the annotated vectors with the
actual infinite-cycle terminal payoffs: the unresolved continuation term after
n cycles is Cⁿ times a bounded vector and tends to zero. This argument does
not normalize or discard a signed singleton level.

## Passive inheritance and every intermediate date

For an outside player, w_k = Γ_kS T⁻¹ gives Γ_kS = w_kT exactly. Multiplying
the active Bellman recursion by w_k, then adding s_k, gives the actual
singleton-reward recursion for that player. Since w_k ≥ 0 and every phase
surplus is nonnegative, its phase payoffs lie above s_k. The entries of w_k
need not sum to one; the separate addition of s_k is why this is harmless.

The interpolation assertion can be made explicit. In a phase of total quit
probability q, split into N dates, put

    d_l = 1 − lq/N,
    f_l = (N−l)q/(N−lq),       0 ≤ l ≤ N.

Conditional on reaching local date l, f_l is the probability of a quit in the
remaining phase. If R is the owner's singleton reward vector and W the next
phase value, the value is f_l R + (1−f_l)W. Because 0 ≤ f_l ≤ q, this lies
on the segment between qR+(1−q)W and W. It therefore preserves every
singleton floor, and preserves the active owner's equality to its singleton.
Also h_l = q/(N−lq), and the continuation product telescopes to 1−q.
The claimed h_l ≤ t/N ≤ δ bound is valid.

Thus the passive argument supplies the required property at every live date,
not merely at cycle starts or in an unconditional average.

## Full behavioral deviations and absence of error accumulation

Fix player i and delete that player's hazards. The proposed V_i satisfies

    V_i(t) = H_i(t) + β_i(t)V_i(t+1)

for its Continue action. For a quiet player this is the prescribed recursion;
for the active owner, β_i = 1, H_i = 0 and both adjacent values equal s_i.
The opponents' survival probability per cycle is C/c_i for an active owner
and C for an outside player, strictly below one in either case.

If i quits at date t and had Continued earlier, finite iteration gives

    payoff_i(t) − V_i(0) = b_i(t)(Q_i(t) − V_i(t)).

Never yields V_i(0), because the bounded continuation remainder vanishes under
opponent survival. If another owner j is active at t, then

    Q_i(t) = (1−h)s_i + h r_i({i,j}) ≤ V_i(t) + 2Mδ.

If i is active, Q_i(t) = V_i(t). These are bounds on complete stopping-date
deviations, with a single endpoint error, rather than stage errors being
summed over an arbitrary waiting time.

The behavioral-to-stopping-law passage is valid in this model. Along the
unique live history a behavioral strategy specifies one hazard at each date.
Its first-quit law is a probability measure on finite dates plus Never,
independent of the opponents' private randomness. Off-live behavior cannot
change the terminal reward. Integration against this law establishes the
same bound for every behavioral replacement, including horizon-dependent
choices. No observation of an opponent's current randomization is used.

## Censoring and signed finite-horizon comparison

After K full cycles, censor each player's private first-quit law to Never.
Renewal gives U_i^K = (1−C^K)v_i, even when v_i is negative. For a fixed
deviation, couple each opponent's censored and infinite clock. A different
outcome requires that all opponents' clocks exceed the cutoff, an event of
probability ρ_i^K. This event is determined by the opponents alone. Therefore
the response change is bounded by 2Mρ_i^K uniformly over all deviations.
Taking the supremum and subtracting the censored prescribed payoff gives

    B_i^K − U_i^K ≤ 2Mδ + 2Mρ_i^K + MC^K,

so the displayed bound E^K ≤ 2Mδ + 3Mρ^K is correct. It includes Never and
all deadlines beyond the retained dates. The asserted date count and rational
law construction follow from N_i ≤ 1+t_i/δ and geometric decay of ρ^K.

The signed finite-horizon argument is also correct. Write a path's average
absorbing reward as a_H(t)r, where 0 ≤ a_H(t) ≤ 1 and, for a retained date,
|1−a_H(t)| ≤ (N+1)/H. The extra one permits the repository's live-stage
convention. Prescribed payoff thus changes by at most M(N+1)/H.

For a pure deviating deadline, there are three cases:

1. The deadline is retained: every absorption is early, so compare with that
   deadline's terminal payoff.
2. The deadline is later and s_i ≥ 0: early opponent rewards incur at most
   M(N+1)/H error, and multiplying the late singleton by a factor in [0,1]
   cannot increase it above its terminal contribution.
3. The deadline is later and s_i < 0: compare with the Never deviation.
   The early opponent outcomes agree, while the late own-singleton average
   contribution is nonpositive and can be omitted in an upper bound.

Never itself has only early opponent absorption. Mixtures give a uniform
upper bound B_i^K + M(N+1)/H and hence regret at most
E^K + 2M(N+1)/H. Directly comparing a late negative singleton with its own
negative terminal payoff would be false; the note explicitly uses the valid
Never comparison. Choosing terminal tolerance below the final requested
tolerance leaves room for this horizon error and yields the stated fixed
target quantifiers.

## The nonnegative-inverse boundary

The Neumann argument is sound. Let B = T⁻¹ ≥ 0 and K₀ = J−I. For sufficiently
small e > 0,

    (T−eK₀)⁻¹ = B + eBK₀B + e²BK₀BK₀B + ⋯.

Every term is nonnegative. If B_ij = (BK₀B)_ij = 0, the nonempty support of
row i and the nonempty support of column j must both equal one singleton
{k}: every pair of distinct support indices would contribute positively to
BK₀B. In dimension three, invertibility ensures a positive B_uv with u,v
different from k; otherwise the two rows outside k would both be supported
in column k. Hence

    B_ik (K₀)_ku B_uv (K₀)_vk B_kj > 0,

which is a term of BK₀BK₀B. Thus every inverse entry becomes strictly
positive. The approximation preserves zero diagonal and invertibility.

Keeping w_k fixed and setting Γ_kS^e = w_k(T−eK₀) preserves its nonnegative
multiplier exactly. This is a legitimate perturbation of the original table:
own singletons, outside singleton columns, and nonsingletons remain fixed,
and all changed coordinates converge to their original values.

If the reward sup norm changes by at most η, prescribed payoffs and every
fixed deviating payoff change by at most η, so B_i changes by at most η and
maximum regret by at most 2η. For each accuracy, a sufficiently close strict
table and one sufficiently accurate finite profile therefore supply a terminal
approximate equilibrium of the original game. Compact payoff selection gives
one fixed target. No common mesh bound, convergence rate for targets, or
continuous target selector is required. The explicit target/rational-calendar
claims in the note are correctly restricted to the strict-inverse case.

## Exact falsification attempts

- Removing the passive condition fails for this very child schedule. Use
  T = [0,−1,2; 2,0,−1; −1,2,0], s = 0, and an outside row
  Γ_kS = (−2,0,1). Then w_k = (0,−1,0), and the initial outside payoff is
  −1. Set all pair rewards of that player equal to zero. Quitting immediately
  pays zero, giving gain one for every subdivision. Thus child existence
  alone cannot replace the nonnegative factorization.
- Coarse collision incentives can be positive even with w_k = 0. With s_k = 0
  and positive pair rewards, joining a micro-hazard h pays h times that reward,
  while Never pays zero. Subdivision controls exactly this quantity; neither
  a singleton floor nor owner indifference makes it vanish at a fixed mesh.
- Zeros in the inverse are a real boundary. For
  T = [0,0,1; 1,0,0; 0,1,0], T⁻¹ is a permutation matrix. For 0 < e < 1/2,
  put a = 1−e. The proposed perturbation T−e(J−I) is
  [0,−e,a; a,0,−e; −e,a,0], with determinant a³−e³ and inverse
  (a³−e³)⁻¹[ea,a²,e²; e²,ea,a²; a²,e²,ea], strictly positive.
  Multiplication gives (a³−e³)I before division. Its hazards are
  q_i = (1−2e)/(1−e). They approach one as e tends to zero, so a
  strict-case calendar bound cannot be
  silently made uniform over this boundary. The existence argument does not
  make that claim.

## Source checks and conclusion

The source maps are `docs/TOOLKIT.md` (balanced singleton cycles and terminal
selection) and `docs/FRONTIER.md`; neither substitutes for a declaration.
The following declarations and their relevant imports/statements were inspected:

- `quittingUniformEquilibriumPayoffConjecture`
  (`UniformEquilibrium/Quitting/Conjecture/Basic.lean`): the intended target is
  an open proposition, with a fixed payoff and unrestricted behavioral scope.
- `BalancedSingletonCycleCertificate`,
  `BalancedSingletonCycleCertificate.isTerminalNash_and_hasValue`, and
  `BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`
  (`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`):
  the constructed owner map, hazards, Bellman values, owner ties, singleton
  floors, and positive other-owner hazards supply the named fields.
- `normalizedSoloMatrix_eq_singleton_sub` and
  `QuittingAnchoredCyclicPatienceSystem`
  (`UniformEquilibrium/Quitting/Cycles/AnchoredCyclicPatience.lean`): the
  receiver/owner orientation matches Γ; passive singleton floors and exact
  fixed-hazard joining tests are distinct.
- `quittingGame_hasUniformDeviationUpperApproximation`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformization.lean`)
  and `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`):
  the signed terminal-to-uniform and fixed-payoff endpoint has the required
  scope. The latter file's
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` also states
  the direct convergent-target alternative used in the boundary discussion.

`Literature/README.md` and the relevant definitions around Theorem 3.4 in
`Literature/AshkenaziGolanKrasikovRainerAndSolan2024.lean` were inspected for
scope: `HasApproximateEquilibriaAtEveryPositiveError` permits a separate Never
payoff, while this construction uses zero, and the printed reverse implication
is not an available theorem for this proof. No paper theorem or claimed
literature-wide novelty is used in this review.

The core sufficient theorem follows with the maximum-regret convention and
the intermediate interpolation and signed-deadline arguments above. This proof
review establishes a producer for the stated raw-table class and makes no
claim of coverage for arbitrary Fin4 tables. The degree-one example, source
attribution, and comparison with named existing classes are treated in the
[Frobenius source review](THREE_CYCLE_PASSIVE_INHERITANCE__BY_CODEX_FROBENIUS.md).
