# Independent focused check: late-cap-compensated Never selection

Reviewer: CODEX_FRECHET_CYCLE.

Reviewed original surface:
`notes/CODEX_RENY__LATE_CAP_COMPENSATED_NEVER_SELECTOR.md`, 393 lines,
SHA-256 `22a63c4acbe3b67f20bc2c70f675bded8b9a8bfb211e4cc74fb94904cabdeea0`.
I read the complete original before giving a verdict and read no other
review. This is a focused independent correctness/novelty check, not a
combined export gate or review of the remaining λD consumer.

Verdict: PASS for the stated compact fixed-point existence, the bound at
EVERY such point, the qualified boundary actualization, and both exact
VANISH tests. No mathematical correction is required. The theorem is a
genuine new coupled source construction relative to the inspected production
interfaces, but it does not establish vanishing selected value. Sections 6
and 7 below add exact boundary tests showing why both actualization and
selection qualifications matter.

These calculations are also preserved in the owned note
[Compensated Never selector boundary tests](../notes/CODEX_FRECHET_CYCLE__COMPENSATED_NEVER_SELECTOR_BOUNDARY_TESTS.md),
so their mathematical content does not live only in this review.

## 1. The exact claim checked

The table has four independent stopping-law players, zero Never reward,
|r_i(S)|≤M with M≥1, and own singletons (1,0,0,0). For each N≥1 the
three nonpivots use actual laws in F_N={0,…,N−1,Never}. Write z_j for
their Never masses, D=z₁z₂z₃, and D_j for the product of the other two.
The pivot uses the CLOSED mass coordinates

    m=(x,λ,ν,α),       Σx+λ+ν=1,       0≤α≤λ.

Here λ is late FINITE mass, ν is Never mass, and α is the first late
atom. These are not interchangeable. Put a_j=r_j({0}), b_j=r_j({0,j}).

For every fixed β∈[0,η]³, η≥0, the proposed compact source consists of
points where m globally minimizes the ORIGINAL complete repair LP against
the fixed three laws, while each nonpivot maximizes original old-menu
payoff with its Never action subsidized by

    γ_j=β_j+Δ_j,             Δ_j=D_j[b_jα−a_jλ]₊.

The exact conclusion at every closed fixed point is

    L≤max_j(β_jz_j+D[b_jα−a_jλ]₊)≤η+2MλD.

When α>0 or λ=0 the mass point is literally realized and L is actual
unrestricted exploitability. At α=0<λ the note claims only approximants
with E≤L+Mα', α'↓0, retaining the payoff and old-menu comparisons with
the old numerical subsidy. That is the correct actual-versus-closed scope.

## 2. Endogenous compensation and existence

The own-law independence is exact. Every π_j,t replaces j by pure t, and
A_j replaces j by Never. Consequently neither coefficient uses p_j.
Moreover A_j cancels from C_j−W_j. D_j excludes j, and α,λ are pivot
coordinates held fixed throughout j's optimization. Thus γ_j is constant
as the candidate q_j varies. There is no hidden own-law factor inside Δ_j.

This remains true on z_k=0, λ=0, α=0 and α=λ. No conditional hazard
or division by a vanishing coordinate appears in the finite coefficients.
The geometric law map may fail to exist at α=0<λ, but the auxiliary
finite payoffs, Δ_j and the closed LP objective remain continuous there.

For fixed opponents the original L is the finite maximum of affine
functions of m, so its argmin on K_N is nonempty compact convex. For
each nonpivot the adjusted objective is affine in its own simplex law,
with jointly continuous coefficients. Standard compact maximum-theorem
arguments give closed graph/upper hemicontinuity for all four response
correspondences. Their product takes nonempty compact convex values in
the fixed compact convex product domain. Kakutani therefore applies.

This really proves existence for every stated reward table, N≥1 and
fixed bounded bonus vector. It does not require a continuous selection of
one LP optimizer. Allowing β to vary over its compact cube leaves a closed
fixed-point graph, so minima of continuous L or λD on that full set exist.
No convergence, computability, or numerical solver is inferred from this.

## 3. Full-cap bound and exact global inner optimality

At an outer fixed point the adjusted pure maximum equals
U_j+z_jγ_j. It bounds every original finite response and the adjusted
Never value W_j+γ_j. Since

    max(W_j,C_j)=W_j+Δ_j≤W_j+γ_j,

it bounds the two complete late endpoints as well. The limiting late
endpoint equals W_j exactly because the nonpivot singleton is zero.
The geometric formula includes arbitrarily late finite dates and the
possibly unattained limit. Therefore

    d_j≤z_jγ_j=β_jz_j+D[b_jα−a_jλ]₊.

This is unconditional original regret, not regret conditional on reaching
the cutoff. The z_j comes from the own probability of using the subsidized
action, not a replacement for deleted-player survival.

The inner step is also sound. If at a GLOBAL pivot minimizer the pivot
were the unique strictly maximal debtor with positive value L, choose a
pure pivot response attaining its full cap. Such a response exists among
the finite head, Never, and the first late date against finite opponents.
Its mass point is feasible. Mixing toward it multiplies pivot debt by
1−θ. Every other affine constraint starts strictly below L and remains
strictly below L for sufficiently small θ>0. This would strictly decrease
the original objective, contradicting global optimality.

This argument neither assumes that the nonpivot laws are original best
responses nor that the mass point is behaviorally attained. It proves the
needed inequality L≤max(0,d₁,d₂,d₃), not global optimality over all four
original laws. Combining it with the outer bound gives the claimed result.

The subsidy itself need not be small: Δ_j may have order M. Calling the
original menu profile η-Nash would generally be false. The note correctly
pays its effect with z_jΔ_j and bounds this by 2MλD.

## 4. Boundary conversion is correctly qualified

Changing α while keeping x,λ,ν and the three finite nonpivot laws fixed
does not change any original prescribed payoff or old-menu pure response.
The only moving complete constraint is C_j=A_j+D_jb_jα. Thus at
α=0<λ, replacement by 0<α'≤λ gives

    |C_j(α')−C_j(0)|≤M D_jα'≤Mα',
    E(actual α')≤L(closed)+Mα'.

The old numerical γ_j still yields exact old-menu best-response equations,
because all those numerical payoffs are unchanged. Recomputing γ_j instead
changes the deviation gain by
(q_j(Never)−z_j)(Δ_j(α')−Δ_j(0)), whose absolute value is at most
M D_jα'. Hence the claimed approximate adjusted-BR bound is correct
without an unnecessary factor two.

The changed mass need not be an exact global LP optimizer or a fixed point
of the recomputed correspondence. The original proof explicitly disclaims
both conclusions. Subsequent finite censoring uses the existing actual-law
consumer and an additional arbitrarily small error, not an imaginary
realization of α=0<λ.

## 5. Independent check of the VANISH calculations

For the half-last-date opponent laws, direct enumeration gives exactly
the displayed A, U_j and pivot debt, and the unrestricted nonpivot cap
max(0,A). All earlier finite responses are nonpositive, Quit0 gives zero,
and the first late endpoint supplies A. The identity

    d₀+d_j=3/8+y/2+[−A]₊

therefore proves the 3/16 lower bound. The displayed feasible optimizer
attains it. Every optimizer must have y=0, A≥0 and both debts 3/16,
yielding λ=6x−1/2 and 1/12≤x≤3/14. In particular A≥5/28.
The adjusted Never value is A+β_j>0 while all old finite values are zero,
so the entire old half-last-date family is excluded, with all α faces and
all optimizing pivot choices accounted for.

For the good truncated periodic branch I checked every phase formula,
Never value, payoff and full cap. For the global pivot inequality:

- At pivot time 0, d₀+g_(2,1)=1−D≥2D because K≥1 and D≤1/8.
- At 1≤t<N, d₀=2^(−t)−D≥D. The time-1 response pays one; adding
  the pivot cannot increase prescribed player-2 payoff under the literal
  coupling, so g_(2,1)≥D.
- At t≥N, d₀=0 and only the all-nonpivot-Never event changes player-2
  prescribed payoff, giving g_(2,1)=2D.
- At pivot Never both terms equal D.

Both gains are affine in the pivot law and independent of α on the closed
mass domain. Integration proves the inequality for unrestricted pivot laws
and the entire LP, so the claimed inner optimum D is genuinely global.

An independent exact Fraction computation checked 129 equalities or
inequalities: all phase/date values for K=1,2,3, the full good-branch
payoffs/caps, every displayed pure pivot comparison through and beyond its
deadline, and representative old-family mass points at N=1,2,4. These
checks support, rather than replace, the exact arguments above.

## 6. Existing nonattainment survives the new coupling

The production `PivotRepairNonattainedZeroLP.reward` has
r₀(S)=1 if 0∈S and zero otherwise; r₁(S)=1 if 0,1∈S and zero
otherwise; the remaining rewards are zero. It is canonical, with M=1.
Take all three nonpivots Never and the closed point x=0, λ=1,ν=α=0
at N=1 (or any positive deadline).

This point has original L=0, so it is a global pivot optimizer. Every
old finite response and original Never payoff of a nonpivot is zero,
and Δ_j=0. Thus the all-Never laws are adjusted best responses for every
β≥0. This is a genuine point of the new closed correspondence.

No actual pivot law attains L=0 against these opponents. For an arbitrary
pivot law μ, pivot debt is its Never mass, while player 1 can gain each
finite atom by quitting at that atom's date. Zero pivot debt would require
total finite mass one, which has a positive atom on a countable set.
This is the checked theorem
`behavioral_repair_infimum_zero_not_attained` in
`UniformEquilibrium/Diagnostics/Quitting/PivotRepairNonattainedAllLaws.lean`.
At a positive first geometric atom α', actual exploitability is α'.

This is not an objection to the note, which preserves precisely this
boundary distinction. It also shows that λD can equal one when closed
L=0. A universal converse λD≤f(L) with f(0)=0 is therefore false,
even for the new fixed-point set. Selecting another point is not ruled out.

## 7. Different bad VANISH fixed points survive every deadline and bonus

The old half-last-date family is excluded, but there is another exact bad
family in the SAME VANISH table. For every N≥1, let all three nonpivots
choose Never and take

    x=0,        λ=ν=1/2,        any α∈[0,1/2].

Against all-Never nonpivots, for EVERY pivot mass point its original pivot
debt is ν, while every nonpivot's full cap is zero and its prescribed
payoff is −(1−ν). Quit0 realizes that zero cap: it either precedes the
pivot or joins it and earns own-Quit reward zero. Thus

    L(m,p)=max(ν,1−ν),

independently of the head distribution and α. Its global minimum is 1/2,
attained at the displayed mass. At that point W_j=−1/2 and Δ_j=1/2,
so subsidized Never pays β_j≥0. Every old finite action pays zero, since
the pivot has no head before N. Therefore these laws form a compensated
fixed point for EVERY β≥0 and every deadline, with L=1/2.

Choosing α=1/2 makes this an ACTUAL finite-law profile: the pivot quits
at N with probability one half and otherwise Never. No nonattainment
qualification is involved in this bad branch.

This does not contradict the good branch or the proposed minimum-over-all-
fixed-points target. It refutes the stronger all-selector inference that
every compensated fixed point becomes good as N grows or bonuses vanish.
At β=0 the sharp bound is attained: D=1 and
D[b_jα−a_jλ]₊=1/2=L. Thus (R) alone cannot force decay on every branch.

## 8. Novelty, existing declarations, and final scope

The narrow current-production comparison inspected:

- `QuittingPivotRepairLPInput`, `objective`, `exists_objective_minimizer`
  and the affine/first-atom declarations in
  `UniformEquilibrium/Quitting/Terminal/PivotRepairFiniteLP.lean` and
  `PivotRepairFiniteLPBoundary.lean`;
- `exists_objective_minimizer_eq_behavioral_infimum` and boundary
  approximation in `PivotRepairBehavioralInfimum.lean` and
  `PivotRepairBehavioralApproximation.lean`;
- `singlePivot_exactMenuNash_nonpivot_debt_eq_zero` and
  `singlePivot_exactMenuNash_pivot_debt_le_deletedNever` in
  `SinglePivotFiniteMenuSource.lean`;
- `pivot_singleton_mul_jointNever_le_objective` and
  `jointNever_le_objective_div_pivot_singleton` in
  `PivotRepairNeverMassBound.lean`;
- `prod_stoppingLaw_none_mul_singleton_le_terminalExploitability` in
  `SingletonJointNeverDebt.lean`, and the signed actual finite conversion
  in `PivotRepairFiniteMenuConsumer.lean`.

The old exact-menu results already give E≤D for ordinary exact same-menu
Nash laws. They do not require the pivot to minimize ORIGINAL full repair
value, and they do not imply membership in the new compensated outer
correspondence. The new source proves that simultaneous adjusted outer
responses and a GLOBAL original inner optimizer always coexist, and pays
their regret by the sharper event λD rather than D alone. This is genuine
additional source structure, not a new interpretation of ordinary menu NE.

The old positive-singleton LP bound reads νD≤L in THIS notation.
Its probability is all-player Never. The new upper residual λD is the
different event that all nonpivots Never and the pivot eventually quits
late. These are not a two-sided bound on one scalar. I initially used the
wrong symbol before receiving the original variables and corrected that
preliminary comparison with both ROOT and the author before this review.

The maximal-debtor argument itself is existing elementary minimum-MAX
geometry. The geometric compression and small-value-to-UE consumer are
already production results. The genuinely additional theorem here is their
coupling to the endogenous, own-law-independent compensated response rule.
It is ordinary mathematics not newly formalized by this review.

Final conclusion: the claimed source and estimates are valid as written.
Whether selecting among these compact fixed-point sets makes L arbitrarily
small for arbitrary canonical tables remains open. The λD consumer is
not assumed, and Sections 6–7 show why no converse or all-branch decay
should be silently attached. No original file was edited and no export
or implementation is recommended by this focused review alone.
