# Optional proper censors: complete class, unresolved Nash selection

Identity: `CODEX_HILBERT`.

## Status and mechanism-level conclusion

Ordinary mathematics, not Lean-checked; no export. This bounded test is
complete and the removal programme is paused.

Adding an independently chosen Never option repairs the strategy-class
defect in
`CODEX_HILBERT__DIRECT_COMPACT_CLOCK_FLOOR_REMOVAL.md`. For each fixed proper
censor, the enlarged law domain is compact in total variation, terminal
payoffs are continuous, and restricted Nash exists. Its exact restricted
best-response formula retains Never. As the censors vanish, the domains
approximate every fixed original law in total variation, so their minimum
FULL exploitability converges to the original game's minimum.

However, the all-normal positive-singleton cyclic Fin4 table has an explicit
branch of exact optional-censor Nash profiles with positive limiting full
regret and positive limiting joint Never mass. Thus **every-selector**
vanishing error or arbitrarily low reach is false. No claim excludes a good
equilibrium selection, and there are feasible profiles in these very domains
whose full regret tends to zero for this solved table.

The ideas pass did not identify a new promising producer. It tested a fresh
legal representation of the existing escaping-response/selection obstruction.
Compact-game existence succeeds; the missing result is still a selection
with small ORIGINAL-game error, not another compactness theorem.

## 1. Scope and narrow source check

The question is whether the domains

    K̂ᵢ = conv(Kᵢ ∪ {δ∞})

improve the proper-censor construction enough to produce actual terminal
approximate Nash profiles, or ordinary finite-menu approximate equilibria
with small joint reach for the reviewed punishment-tail completion.

Here Kᵢ is the whole-law proper-censor domain from the preceding note, and
δ∞ is the actual Never strategy. A player privately draws one coin choosing
Never or a law in Kᵢ; players' coins and clocks remain independent. The
payoff table and all ultimate full-cap tests remain those of the original
quitting game. The auxiliary game's unilateral deviations range over K̂ᵢ,
not all original stopping laws.

A narrow phrase search for optional censors, censor/Never mixtures, convex
proper-law/Never domains, and sentinel variants did not locate this exact
domain and selection calculation. It did locate the earlier censored finite
deadline comparisons, proper-watchdog approximation, and fixed-proper-clock
continuity results. This is a bounded novelty check, not a repository-wide
claim.

Definitions and declarations inspected were:

* `CompactStoppingLaw`, `compactStoppingLawBarycenter`, and
  `CompactStoppingLaw.realMass_barycenter` in
  `MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean`;
* `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`;
* `quittingTerminalPayoff_update_sub_le_two_mul_bound_mul_stoppingLawTV`
  in `UniformEquilibrium/Quitting/Paths/StoppingLawExposure.lean`;
* the all-errors endpoint
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

The classical fixed-point theorem is the Glicksberg Section 1 theorem checked
against the original paper in the preceding note. It is applied only after
verifying continuity of this restricted game.

## 2. Optional-censor compactness and exact best responses

Fix m ≥ 2, rewards |rᵢ(S)| ≤ M, and Never payoff zero. Choose floors
0 ≤ ℓᵢ(t) < 1 and define

    Lᵢ(t) = ∏[s < t] (1 − ℓᵢ(s)) → 0,
    cᵢ(t) = Lᵢ(t)ℓᵢ(t).

The proper censor Cᵢ has law cᵢ. A law μ belongs to Kᵢ precisely when

    Sμ(t + 1) ≤ (1 − ℓᵢ(t))Sμ(t),

where Sμ(t) = Pμ(T ≥ t) includes Never. Since Lᵢ(t) > 0, the sequence
Sμ(t)/Lᵢ(t) is nonincreasing from one. It is the survival sequence of a
complete auxiliary clock A. Thus Kᵢ is exactly the set of laws of
min(A,Cᵢ), with A independently drawn and allowed to equal Never.

The auxiliary clock A = ∞ here means **use the proper censor Cᵢ**. It is
not the additional actual Never action δ∞.

### Proposition 1: compactness and existence survive the added Never option

Every point of K̂ᵢ has the form

    a μ + (1 − a)δ∞,  0 ≤ a ≤ 1, μ ∈ Kᵢ.                (2.1)

K̂ᵢ is compact and convex in total variation. Consequently the original
terminal-payoff game restricted to the product of the K̂ᵢ has an actual
independent Nash profile.

#### Proof

Kᵢ is compact in total variation by the uniform proper-tail bound
Sμ(t) ≤ Lᵢ(t), proved in the preceding note. The map (a,μ) ↦ (2.1) is
continuous in total variation on the compact product [0,1] × Kᵢ. Its image
is exactly the convex hull because Kᵢ is already convex. This proves
compactness and convexity without silently taking a larger closure.

Terminal expected payoff is jointly continuous in the product of marginal
total-variation topologies, uniformly for a bounded terminal reward, and
affine in the mover's own law. The best-response correspondence has nonempty
compact convex values and a closed graph, so Glicksberg applies. The fixed
point is a vector of independent laws. It adds no public correlation. ∎

In particular, adding Never does NOT reintroduce the weak-law payoff jump at
a fixed censor. The finite tail excluding Never is uniformly at most Lᵢ(t),
and Never's mixing weight is continuous on this compact domain. The modulus
need not be uniform when the censor itself changes.

### Proposition 2: the exact restricted cap

Fix actual opponents p₋ᵢ. Write Fᵢ(t) for the original payoff of pure finite
date t and Vᵢ for the original payoff of Never. Define

    Hᵢ(t) = ∑[s < t] cᵢ(s)Fᵢ(s) + Lᵢ(t)Fᵢ(t),  t < ∞,
    Hᵢ(∞) = ∑[s ≥ 0] cᵢ(s)Fᵢ(s).                       (2.2)

Then

    B̂ᵢ(p₋ᵢ) = max{Vᵢ, max[t ∈ ℕ ∪ {∞}] Hᵢ(t)}.        (2.3)

The second maximum is attained. This does not assert attainment of the
original unrestricted finite-date supremum.

#### Proof

The law min(t,Cᵢ) has mass cᵢ(s) at s < t and mass Lᵢ(t) at t. The limit
t = ∞ is Cᵢ itself. Every law in Kᵢ is a mixture of these laws by the
representation above. Own payoff is affine, so maximizing over Kᵢ is
equivalent to maximizing (2.2). The laws min(t,Cᵢ) converge in total
variation to Cᵢ as t → ∞. Thus Hᵢ is continuous on the compact deadline
space, and its maximum exists. Affinity and (2.1) then give (2.3). ∎

At any restricted Nash profile, Uᵢ = B̂ᵢ, so Never is already safe. The
remaining omitted response is a finite date whose forced earlier Quit can
be strategically costly. The useful exact identities are

    Hᵢ(t + 1) − Hᵢ(t) = Lᵢ(t + 1)[Fᵢ(t + 1) − Fᵢ(t)],
    Fᵢ(t) − Hᵢ(t) = ∑[s < t] cᵢ(s)[Fᵢ(t) − Fᵢ(s)].     (2.4)

Hence every restricted Nash profile satisfies, uniformly over its endogenous
opponents,

    Fᵢ(t) − Uᵢ ≤ 2M(1 − Lᵢ(t)),  and  Vᵢ ≤ Uᵢ.        (2.5)

If the floors vanish at every fixed date, (2.5) controls every fixed finite
menu of deviations. It does NOT make the profile finitely supported, nor
control all moving dates uniformly: for each proper censor Lᵢ(t) → 0 as
t → ∞.

## 3. The repaired domains are asymptotically complete

Let ℓᵢⁿ(t) → 0 for every fixed i,t, with each censor still proper. For every
fixed original complete law μᵢ, retain its Never atom unchanged and, on its
finite branch, replace its finite time Aᵢ by min(Aᵢ,Cᵢⁿ). The resulting law
μᵢⁿ lies in K̂ᵢⁿ and

    TV(μᵢⁿ,μᵢ)
       ≤ P(Aᵢ < ∞ and Cᵢⁿ < Aᵢ) → 0.                 (3.1)

Indeed, for each finite Aᵢ = t the conditional probability is 1 − Lᵢⁿ(t)
and tends to zero. Bounded convergence over the fixed finite-part law proves
(3.1). The actual Never branch is not forced to Quit.

Let E(p) be full unrestricted maximum regret and η its infimum over all
actual profiles. Then

    inf[p ∈ ∏ᵢ K̂ᵢⁿ] E(p) → η.                         (3.2)

For the proof, approximate one fixed full near-minimizer using (3.1).
Finite-product coupling gives continuity of its prescribed payoffs and,
uniformly over arbitrary own replacements, of its full caps. More explicitly,
if Δ is the sum of marginal TV distances, the prescribed-payoff difference
is at most 2MΔ and every cap difference is at most 2MΔ; thus the maximum
regret difference is at most 4MΔ. This proves the upper limiting bound in
(3.2); the lower bound η is immediate.

No uniform approximation of ALL profiles is claimed. Most importantly,
(3.2) minimizes FULL exploitability, whereas Proposition 1 selects equilibria
for the RESTRICTED cap (2.3). These optimizing sets need not coincide.

## 4. Exact positive-singleton optional-censor Nash branch

Use the solved cyclic table from
`CODEX_HILBERT__BOUNDED_TIMING_INCENTIVE_TEST.md`. Players 0,1,2 are cyclic,
with predecessor i−1; player 3 is an outsider. For nonempty S,

    rᵢ(S) = 1 + 1_{i−1∈S}, if i∈S and i<3;
    rᵢ(S) = 3·1_{i−1∈S},   if i∉S and i<3;
    r₃(S) = 1 if 3∈S, and 2 otherwise.

All own singleton rewards and all punishment values equal one: Quit now
guarantees at least one, and against all-Never opponents no strategy earns
more than one. Thus all players are normal. The prior note supplies an exact
period-three terminal equilibrium for this table, with outsider Never.

Use common geometric censors of hazard λ ∈ (0,1), and put r = 1 − λ.
Set

    A(r) = r/(1+r),
    B(r) = (1−r+r²)/[(1+r)(1+r+r²)].

Let x > 0 be the unique positive root of

    x² − A(r)x − B(r) = 0,

and put a = 1/(1+x), b = x/(1+x). Since

    1 − A(r) − B(r) = 2r/[(1+r)(1+r+r²)] > 0,

we have 0 < x < 1 and 0 < b < 1/2. Prescribe

    pᵢ = a·Law(Cλ) + b·δ∞,  i = 0,1,2;
    p₃ = δ∞.                                             (4.1)

These are literal optional-censor strategies. Their active finite masses
and survivals are

    pᵢ(t) = aλrᵗ,   S(t) = b + arᵗ.

### Proposition 3: (4.1) is exact optional-censor Nash

For an active player, the original Never payoff is

    V = 3ab + 3a²/(1+r).                                  (4.2)

Write z = rᵗ and k = (1−r+r²)/(1+r). Its finite-date payoff satisfies

    F(t) − V = b² − abr z − a²k z².                        (4.3)

It is strictly increasing in t. Thus (2.4) shows that its best proper-censor
response is Cλ itself. Since

    E r^{Cλ} = 1/(1+r),
    E r^{2Cλ} = 1/(1+r+r²),

we obtain

    H(∞) − V
      = b² − ab r/(1+r) − a²k/(1+r+r²) = 0              (4.4)

by the definition of x = b/a. Hence both Cλ and Never are restricted best
responses, validating each active player's mixture.

For completeness, (4.2) counts absorption by the predecessor before the
other active opponent, including same-date predecessor/opponent ties:

    V = 3∑[s ≥ 0] aλrˢ(b+arˢ).

A finite own Quit at t adds, after survival of both opponents to t,
the contribution S(t)² + aλrᵗS(t), and loses the corresponding future
predecessor contribution from V. Expanding gives (4.3). This verifies the
complete pure-time comparison, not just a current root condition.

For the outsider,

    F₃(t) = 2 − S(t)³,  V₃ = 2(1−b³).

Again F₃(t) increases, so its best K₃ response is Cλ, with payoff
2 − E S(Cλ)³. Jensen and E r^{Cλ} ≥ 1/2 give

    E S(Cλ)³ ≥ [b+a/(1+r)]³
               ≥ [(1+b)/2]³ ≥ 27b³/8 > 2b³,

where b ≤ 1/2 was used in 1+b ≥ 3b. Thus Never is strictly better than
every proper-censor response of the outsider. This proves exact restricted
Nash for all four players. ∎

### Proposition 4: actual full regret and joint Never do not vanish

By (4.3), the original full cap of an active player is

    Bfull = V + b²,

the limit of arbitrarily late finite dates; it is larger than Never and is
not attained at any finite date. Its prescribed payoff is V by (4.4), so
its full debt is exactly b². The outsider's full cap is 2−b³, giving debt
b³. Therefore

    E(p) = b²,   Pₚ(all Never) = b³,
    Rₚ(t) = (b+arᵗ)³ ≥ b³ for every t.                    (4.5)

As λ → 0, x converges to the positive root x* of

    x*² − x*/2 − 1/6 = 0.

In particular b → b* = x*/(1+x*) > 0, so both limits in (4.5) are strictly
positive. No quantitative constant is being optimized.

This is an exact failure of uniform safety or low reach for **every**
optional-censor Nash selector, on an all-normal positive-singleton game.
It is not a no-UE counterexample and does not refute existence of a good
selector.

## 5. What survives, and why this tranche stops

The optional-censor repair really differs from the mandatory proper class:
Never is legal, payoff continuity survives, and (3.2) gives asymptotic
completeness for full-regret minimization. The old negative-membership
counterexample is therefore not used against it.

For the cyclic table, approximate the prior exact periodic equilibrium by
(3.1), retaining the outsider's Never law. This gives feasible profiles in
the optional-censor domains with full regret tending to zero. They are not
asserted to be exact restricted Nash. Thus the bad branch (4.1) isolates a
selection problem rather than a lack of expressive strategies.

The finite-menu punishment completion accepts a supplied finite-menu
approximate Nash source and small joint reach. Neither input follows from
the fixed-date bound (2.5): the optional-censor equilibrium can have infinite
support, and its joint reach in (4.5) remains bounded away from zero at every
cut. Passing to a finite truncation needs an actual error comparison; a
finite list of tests at the untruncated payoff is not finite-menu Nash of
the truncated profile.

The remaining error is the finite response's reward-sensitive preemption
loss in (2.4). In this regression the omitted best-response dates move beyond
the censor scale, and retaining Never does not pay for them. This is a fresh
representation of the already known escaping-response obstruction.

**Mining verdict:** no new promising producer was identified by this bounded
ideas pass. A legal compact approximation class and an exact bad selection
were established, but no operation selects full-safe equilibria or generates
the low-reach approximate finite Nash sources needed by the new completion.
No additional censor variants, constants, or general no-go programme are
pursued here.
