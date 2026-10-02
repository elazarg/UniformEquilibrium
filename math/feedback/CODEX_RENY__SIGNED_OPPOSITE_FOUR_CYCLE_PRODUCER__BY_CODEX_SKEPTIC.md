# Independent review of the signed-opposite four-cycle producer

Reviewer: CODEX_SKEPTIC. Author: CODEX_RENY.

## Verdict and reviewed bytes

PASS, as ordinary mathematics, for the complete theorem in
`notes/CODEX_RENY__SIGNED_OPPOSITE_FOUR_CYCLE_PRODUCER.md`, SHA-256
`1c63777ff44e26b9e7784de334b15db905f8c0ce09fa649a1317b7394f0ba330`.
I read the entire frozen original before any other review, independently
rederived its algebra and semantic estimates, inspected the named production
interfaces, and checked every displayed exact fixture using Python Fraction
arithmetic. I have not read another review of this packet. No required
mathematical repair was found; the bounded source-novelty qualification below
is part of this verdict. This is not a Lean check or an export authorization.

The result is a raw-table producer: twelve explicitly tested singleton
comparison coefficients produce four positive owner hazards and a balanced
cycle, with no supplied equilibrium/cycle and with all nonsingleton rewards
arbitrary. It gives a fixed uniform-equilibrium payoff and, at every positive
accuracy, actual finite-clock profiles with small FULL terminal regret and
the stated early-absorption quantifiers. It does not solve arbitrary Fin4.

## 1. Signed reconstruction: the small eigenvalue really works

Use the author's notation aᵢ, dᵢ, X, Y, K, λ, A and W. Since Δ>0, the
displayed λ is a real simple eigenvalue. The vector
W₀=−K₀₁, W₁=K₀₀−λ is its eigenvector: the first row is an identity and
the second is exactly det(K−λI)=0. The explicit strict inequalities, not a
Perron argument, give positive W₀,W₁,W₂,W₃ and 0<A<1.

Substitution into W₁=a₀W₂+d₀W₃ yields
W₁=A(XW₀+YW₁), the second eigenvector row. Substituting that relation into
W₀=a₃W₁+d₃W₂ gives the first row. Together with the two definitions of
W₂,W₃, these are all four equations (2.1), with their signs unchanged.
For each i they give

    Σ[j>i]wⱼΓᵢⱼ + A Σ[j<i]wⱼΓᵢⱼ = 0.

For i=3 cancellation of A is legitimate. Since Σw=1−A<1 and every w>0,
all partial-survival denominators tₖ are positive and every qₖ,cₖ lies
strictly between zero and one. No zero-survival or zero-hazard boundary was
silently admitted. Choosing the larger eigenvalue of the circulant fixture
would fail the positive-vector test; the submitted minus branch is essential.

## 2. Actual payoff and every player's floor

The product profile has actual one-cycle absorption weights w and survival
A<1. Thus its actual payoff is the geometric-resolvent value in (3.1),
not an independently assigned Bellman vector. From phase i+1, the rotated
one-cycle weights are wⱼ/tᵢ₊₁ for j>i and Awⱼ/tᵢ₊₁ for j≤i; their sum
is 1−A. The balance equation consequently proves vᶦ⁺¹ᵢ=sᵢ. The owner's
Bellman equation proves vᶦᵢ=sᵢ as well.

The remaining two dates are precisely covered by

    vᶦ⁺²ᵢ−sᵢ = qᵢ₊₁ bᵢ/cᵢ₊₁ > 0,
    vᶦ⁺³ᵢ−sᵢ = qᵢ₊₃ hᵢ > 0.

The first follows from Bellman at the disliked successor phase and the
second from Bellman immediately before i's own phase. These derivations
remain valid when the opposite comparison gᵢ is negative. They exhaust the
four-player floor conditions; no unexplained positivity of a longer tail is
being assumed. Every player has three other owners with positive hazard.

Hence the raw construction supplies every literal field of
`BalancedSingletonCycleCertificate` in
`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`:
`owner`, `hazard`, `coarse`, `initial`, the hazard bounds, `arc`, `active`,
`soloFloor`, and `opponentDivergence`.

## 3. Full deviations, negative levels, and finite-menu padding

The fine mesh uses independent private hazards on a deterministic calendar.
Its within-phase continuation values interpolate the coarse endpoints.
For an active owner, Quit and Continue both give sᵢ; for a passive player,
Continue is its prescribed value, at least sᵢ, whereas Quit has value at
most sᵢ+2Mθ. A sequence of forced Continue decisions therefore preserves
the prescribed value until its final Quit. The improvement at that Quit is
at most 2M max θ multiplied by deleted-opponent reach, at most one.
This is a single final-quit loss, not a sum over all preceding dates.

The Never response is handled separately and correctly. Under that response,
opponents survive a cycle with probability ∏[i≠j]cᵢ<1, so their absorption
is almost sure and the bounded continuation remainder vanishes. Thus Never
has the prescribed payoff even if that payoff or sᵢ is negative. An arbitrary
behavioral deviation on the unique unabsorbed history is a distribution over
finite stopping dates and Never. The resulting cap bound therefore covers
all behavioral deviations, including history-dependent behavioral rules;
there is no bounded-controller or public-correlation assumption.

The checked declarations
`BalancedSingletonCycleCertificate.isTerminalNash_and_hasValue` and
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff` supply exactly
this semantic consumer. The packet does not falsely claim the coarse cycle
is exact Nash for arbitrary collision rewards. Finite reward boundedness
controls those rewards by 2M; no coalition coordinate is dropped.

For the explicit finite profile, after K full mesh cycles player i's tail
mass is exactly cᵢᴷ. Censoring that mass to Never changes each payoff and
each unrestricted pure-response cap by at most 2MΣcᵢᴷ, by the product
coupling bound. The change of exploitability is at most 4MΣcᵢᴷ. Choosing
L and then K as specified gives full regret <e. The joint Never mass is
∏cᵢᴷ=Aᴷ. With T=4LK and N≥max(T+H,N₀), all finite atoms precede N−H,
so the late reach is exactly Aᴷ<ρ. In particular N≥H. Full regret was
controlled before enlargement of the finite menu, so the padding step does
not confuse finite-menu Nash with unrestricted Nash. Real hazards suffice;
no rational-output or effective finite-search claim is made.

## 4. Exact regression and matrix placement

An independent Fraction calculation reconstructed K from each displayed Γ,
checked its two eigenvalues by trace and determinant, reconstructed W,w,q,
checked all four balance equations, all sixteen Bellman entries, all owner
equalities and floors, and both inverse products ΓB=BΓ=I. Results:

| Fixture | det Γ | selected λ | W | q |
| --- | --- | --- | --- | --- |
| Γ* | −1200 | 16 | (78,39,39/2,39/4) | (1/2,1/2,1/2,1/2) |
| Γ† | −2319/2 | 16 | (381/5,381/10,381/20,381/40) | (1/2,1/2,1/2,1/2) |
| Γ‡ | −781 | 12 | (44,44,22,11) | (1/3,1/2,1/2,1/2) |

All displayed inverses and values passed exactly, without floating-point
acceptance. The unequal-hazard example exercises the additional freedom.

If B=Γ⁻¹ is entrywise strictly positive, xᵀBx>0 for nonzero x≥0, without
assuming B symmetric. Thus B is copositive and R₀, and
`isStandardQMatrix_of_copositive_of_isR0Matrix` in
`UniformEquilibrium/Quitting/Classification/LCP/CopositiveQBridge.lean`
gives standard Q. Solving its LCP at −Bq with variable w and residual
z=B(w−q) gives w=q+Γz. Nonnegativity and complementarity are preserved,
so z solves the Γ-LCP at q. This verifies every q, not a finite screen.
For a homogeneous Γ solution, z=Bw and zᵀw=wᵀBw force w=z=0; a simplex
solution is impossible.

The opposite principal has both off-diagonal entries strictly negative.
At projective right-hand side (−1,−1), its two residual inequalities force
cemetery mass and both singleton weights to zero, contradicting total one.
This uses the actual `ProjectiveLCPSolution` definition in `MatrixClasses.lean`.
The distinct-successor negative blocker keeps every recursive `normalLayer`
equal to Fin4 under `NormalCore.lean`; this is not an identification with
punishment-normal players. All strict spectral, inverse and opposite-pair
conditions persist in an open twelve-dimensional comparison neighborhood.
The 4 own levels and 44 nonsingleton coordinates remain free.

## 5. Bounded source-novelty verdict

The claimed distinction from the named cyclic producers survives inspection:

- `CyclicSingletonTailData` in `CyclicSingletonTailProducer.lean` has a single
  offset tail and scalar survival, whose recurrence forces Γᵢⱼ to depend
  only on j−i. `hasQuittingCanonicalEqualHazardTailData_iff` in
  `CyclicSingletonOpenSignProducer.lean` explicitly assumes that invariance.
  Γ* is already covered at survival 1/2; Γ† and Γ‡ are not invariant under
  any relabeling, and positive playerwise scaling does not remove their
  differing within-row ratios. The note correctly does not count Γ* as new.
- `QuittingCyclicSingletonOpenSignData` additionally requires later offsets
  nonnegative. A mutually negative opposite pair fails that class even after
  changing the cyclic order: a four-cycle cannot make both directions of a
  pair the unique negative successor comparison.
- `isUniformEquilibriumPayoff_of_finitePlayerPhaseNashCertificate` in
  `CyclicKofNPlayerPhaseHazards.lean` consumes supplied hazards and exact
  root Nash at every phase. It is not a raw heterogeneous singleton producer,
  and arbitrary collisions do not supply its exact coarse-root hypotheses.
- `FinFourIntegralTournamentBalancedSingleton.target_isUniformEquilibriumPayoff`
  and its raw singleton-row producers require a tournament-skew matrix.
  The mutually negative opposite pair excludes that matrix form. The
  standard-Q/no-homogeneous calculation also excludes the ordinary non-Q and
  homogeneous closure branches of `CounterexampleNecessary.lean`; the
  failed opposite principal excludes whole-matrix projective Q-bar.
- The broader stationary comparisons inspected were `SureExitChambers.lean`,
  `InducedOwnerChambers.lean`, `ConditionalFaceGapRange.lean`, and
  `FiniteOddBlockerCore.lean`. They require literal collision/face signs, an
  actual induced Nash point with owner-floor signs, or a passive-payoff
  identity. None is supplied just by (1.1)–(1.3) with all 44 collision
  coordinates free. In particular the odd-blocker passive identity would
  make a core player's outsider singleton payoffs constant, unlike these
  rows. Positive-minimum alternatives in the induced-owner file are
  counterexample-side alternatives, not raw producers of those signs.

This is a bounded repository comparison, not proof of worldwide priority or
of disjointness from every previously solved completion. Individual chosen
nonsingleton completions may also satisfy an older producer. What survives
is the explicit heterogeneous, collision-unrestricted, open raw singleton
class crossing the full-standard-Q/non-projective-Q-bar matrix region.
The note's express distinction from an actual positive-terminal-gap hard
source is essential and correct. No compatible hard source is asserted.

## 6. Handoff and nonclaims

No substantive or required expository repair was found. A narrow Lean
handoff is to define the signed spectral raw-data conditions, prove the four
balance identities and two nontrivial phase floors, and construct the
existing `BalancedSingletonCycleCertificate`. Reuse its semantic compiler;
do not refactor that consumer. The three rational matrix fixtures and Q
inversion proof can be separate finite algebra lemmas if matrix placement is
to be formalized. The finite-censor claim additionally needs the existing
law-TV full-cap estimate, not finite-menu padding alone.

The result is not an arbitrary-game UE producer, an exact coarse equilibrium
for arbitrary collision rewards, a rational decision procedure, or closure
of the live Fin4 question. Author/coordinator promotion remains separate from
this independent mathematical PASS.
