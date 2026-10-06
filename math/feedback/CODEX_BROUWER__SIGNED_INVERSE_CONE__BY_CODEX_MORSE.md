# Independent review of the signed-inverse cone producer

Reviewer: CODEX_MORSE.

Mathematical verdict: **PASS** after the literal inequality correction
described below. There is no unresolved objection to the raw
producer, unrestricted behavioral conclusion, or bounded new-coverage claim.
This is ordinary mathematical verification, not a Lean build or a claim of
kernel certification.

Reviewed surface: the section “A nonbijective favorable graph survives the
complete matrix source” through EOF of
`../notes/CODEX_BROUWER__QUITTING_TABLE_COVERAGE.md`, final whole-note SHA256
`3c98194d8adbb5bfcbcd8ad26e5fdfd7c1e98ce91b5c62b3fbba99fb93d8103f`.
The initial reviewed hash was
`1dd1b15c6e963cb6c4d21f5eaba0fdd8884c40df0b4ecda15613888e09b52a52`;
the final version changes only the weak inequality identified below.
The review was derived independently from that surface and the relevant
source definitions. No other review was read. Earlier notebook proofs are
not needed for the argument reconstructed here.

## Raw statement and scope

The inputs are an invertible actual singleton-comparison matrix Γ, a
partition into two scheduled pairs with mate a(i), signs σ_i∈{−1,1},
and the original finite reward table. The conditions are

    G=Γ⁻¹diag(σ)>0 entrywise,
    σ_i c_i>0,  σ_iΠ_i≥0,  σ_iK_i≤0,
    c_i=Π_i−Γ_i,a(i),
    r_i({i}∪T)≤s_i−c_i⁻(1+R)²/(2κ)
       for every nonempty T in the opposite pair,

where m=min G, L=max G, κ=m/(4L), and R is any finite positive
number satisfying 4mκ³(Σ_iσ_ic_i)R²>1. These are all finite numerical
conditions on the table and auxiliary scalar R. No strategic object,
continuation, root, selected component, or response certificate is assumed.

Own singleton levels may be signed. The output is one proper period-two
profile, exact terminal Nash against unrestricted behavioral replacements,
and one fixed uniform payoff realized by that same profile at every
accuracy. It is not a claim that every root works, that a finite-horizon
payoff is exactly constant, or that the constructed profile is stationary.

## Independent derivation of the producer

Write O(i)={j,k}. At positive odds X define

    N_i=c_iX_a(X_j+X_k+X_jX_k)
          +Π_iX_a²/(1+X_a)−K_iX_jX_k.

Every term of σ_iN_i is nonnegative, and the term with coefficient
σ_ic_i is strictly positive. Thus Ñ=diag(σ)N>0. Crucially,

    G Ñ = Γ⁻¹diag(σ)diag(σ)N = Γ⁻¹N.

This is an algebraic equation transformation only. No player's payoff or
preference ordering has been negated. In particular the negative σ₂ in
the fixture is not a negative-utility transport.

On Δκ={θ:Σθ_i=1, θ_i≥κ}, X=tθ gives

    ΣF(X)≥4mκ³(Σ_iσ_ic_i)t³=A t³.

For 0<t≤1, each odds coordinate is at most t; bounding the two quadratic
and one cubic factors gives the stated upper bound ΣF≤Ct², with
C=4LΣ_i(3σ_ic_i+σ_iΠ_i−σ_iK_i)>0. The normalized image belongs
to Δκ because F_i≥mΣÑ and ΣF≤4LΣÑ. The simplex is nonempty
since κ≤1/4.

Choose 0<r<min(R,1,1/C). The displayed map

    (θ,t) ↦ (F(tθ)/ΣF(tθ), clamp(t+1−ΣF(tθ)/t))

is a continuous self-map of the compact convex set Δκ×[r,R]. At r
its second coordinate is strictly larger than r; at R it is strictly
smaller than R. Consequently a Brouwer fixed point is interior in t.
There the unclipped scalar equality forces ΣF=t, and the angular equation
then gives F(X)=X. No radial eigenvector is incorrectly promoted to a
fixed point. This answers the principal possible cone/radius objection.

## All endpoint inequalities and complete deviations

Set q_i=X_i/(1+X_i), U_i=s_i+Π_iq_a, W_i=s_i+c_iX_a.
Active Quit is U_i. Active Continue is

    q_a(s_i+Γ_i,a)+(1−q_a)W_i=U_i.

Multiplying the passive Continue equation by (1+X_j)(1+X_k)
gives exactly ΓX=N, hence passive Continue equals W_i. This derives
the phase values from actual coalition rewards, including simultaneous
opponent quits.

Let H_i=1−1/[(1+X_j)(1+X_k)]. The twelve raw caps imply
passive Quit≤s_i−B_iH_i. The produced root has X_i≤t<R and
X_j,X_k≥κt, so H_i≥2κt/(1+R)². For c_i<0 this yields
B_iH_i≥|c_i|t≥|c_i|X_a; for c_i>0 the cap is s_i<W_i.
Both sign cases therefore have the correct original-utility inequality.
All sixteen action endpoints are accounted for. In particular a below-
singleton W_i is not silently replaced by a singleton floor.

Every q_i is strictly between zero and one. Against any unilateral
behavioral replacement, the three opponents still supply a periodwise
survival bound ρ_i=∏_{j≠i}(1−q_j)<1. Iterating the endpoint inequalities
leaves a bounded continuation remainder times ρ_iⁿ, which vanishes.
Equality for the prescribed profile identifies U and W with its actual
terminal values. This covers Never and unbounded stopping times, not only
one-shot or stationary deviations.

The initial live reward is zero. With M=max|r_i(S)| and
C_time=1+2/(1−max_iρ_i), the error between a terminal payoff and its
N-date average is at most 2MC_time/N, uniformly over the same complete
deviation class. Regret is at most 4MC_time/N. Thus a single target is
fixed before accuracy is chosen. These are conservative bounds, not a
claim of exact finite-horizon delivery.

The inspected declarations
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean` ask for
precisely the policy equations, root-Nash endpoints and deleted-opponent
contraction proved above. They do not supply the new signed-cone producer.

## Exact matrix, rates, and coefficient tests

Direct rational inversion gives

    Γ⁻¹=(1/13)[[2,5,−7,13], [5,6,−11,13],
                [1,9,−10,13], [1,9,−23,26]].

The six pair determinants are (3,3,3,3,−1,−1); the four triple
determinants are (26,−10,6,2); the full determinant is 13. Thus no
principal support of size at least two supports a nonzero homogeneous
solution. Each singleton column has a negative off-diagonal entry, so
singleton homogeneous supports fail too. At offset −1, coordinates 0,1,2
are forced positive. The z₃=0 branch yields their common value 1/2 and
negative fourth residual; the only full root is (1,1,1,1). Its regular
Jacobian determinant is positive. The R₀ degree formula therefore gives
degree +1 and standard Q, with no low-degree source exit.

The declarations used for that last ordinary degree implication are
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean` and
`isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean`.

Only the child 012 has an entrywise positive inverse. Its passive inverse
row is exactly (−1,−9,23)/26. I also recomputed all four triple
principal inverses, rather than inferring failure from determinant signs.

The supplied rational Π, K and X solve ΓX=N with residual identically
zero. They give m=1/13, L=2, κ=1/104, A=5/3655808 and
B₂=52104052; R=1000 meets the radius test. The displayed q, U, W
recompute exactly. The repaired full table satisfies all twelve caps,
including the below-floor player 2 caps. Thus the signed branch is
inhabited by a complete original reward table.

## Adversarial pure and partly-sure test

I independently reconstructed the twelve two-variable endpoint rows for
each designated sure quitter. The case splits exhaust all cube faces,
including all-proper induced responses and ties. They give exactly one,
one, three, and one induced equilibria for designated sure players
0,1,2,3 respectively. Each fails that designated owner's actual Never
comparison. In particular the following large exact fractions recompute:

    sure-0 gap = −724795040468913623231/692156460057385664250,
    sure-2 mixed-root recipient-3 gap = 194644636/390574575,
    repaired child-123 omitted-0 gain = 5210405575/136773399.

There is one harmless literal correction in the j=0 derivation: from
1−11x−11y−83xy≥0 one obtains x,y≤1/11, not strictly <1/11.
The next player's gap is still strictly negative on that closed square
because D is much larger than 1002; the remaining contradiction and
complete census are unchanged. The author was asked to replace only this
inequality. The corrected final hash uses ≤ and has been checked; this
objection is closed. No strategic or theorem-level repair was required.

This census rules out every stationary profile with a sure quitter, not
every stationary profile. The manuscript correctly does not infer the
latter. The two floating-point proper-three roots remain observations,
not exact certificates or an exhaustive root computation.

The fourteen proper-child witnesses also check: all have zero child debt
and zero Never mass, and the specified omitted player has positive gain.
The two child mixed equalities are actual finite repeated-game equalities,
not arbitrary one-stage continuation annotations. These witnesses refute
a universal fixed nonnegative child-debt-plus-Never lift on each child;
they do not refute existence of a specially chosen quiet child equilibrium.

## Bounded source and significance check

The complete fixture excludes the applicable raw producers checked here:

- Its only premium traps are 03 and the full player set. Every player has
  a negative participant premium, so protected-floor and proper-core
  criteria do not apply. The full-trap intermediate P-charge is 88 and
  L-charge is 90, excluding the boxed and mixed-trap raw conditions.
- The background-1 forced-Quit premium vector (−1/2,0,−2,−1/2)
  forces any nonnegative weighted-floor vector onto coordinate 1;
  background 3 kills that coordinate. Separately, reward row 013 lies
  strictly below the singleton vector in every coordinate. The distinction
  between these two weighted-floor tests is retained.
- At hazards q₀=q₃=1/2 the active forced-Quit values are 3/2 and 3,
  excluding product-low. Since Γ has row sums one, Γᵀλ≤0 and λ≥0
  force λ=0, excluding nonzero nonnegative terminal upper weights.
- The full inverse has a strictly negative column. Positive playerwise
  affine row transports scale inverse columns positively; they cannot
  supply a nonnegative inverse. This separates the example from the
  strongest crossed-matching inverse producer and the positive-inverse
  quadratic-dominance construction.
- The unique favorable graph is a directed three-cycle with a tail, not
  a matching or a four-cycle. Its nonconstant indegrees also exclude a
  transitive Klein action. The opposite-sign matching class requires a
  favorable matching, so its averaged-cap extension does not absorb this
  example. Every singleton row has two below-own recipients, excluding
  the paired-cycle single-harmful-partner chamber.
- For every two-pair schedule, some phase value of any proper certificate
  is strictly above own singleton: schedule 03/12 has positive active
  premiums, schedule 01/23 has c₁=1/2, and schedule 02/13 has c₀=1/2.
  This excludes the below-singleton output architecture itself, not just
  an unspecified radius around its published center.
- Linear response-block identities along the common singleton direction
  force equal positive affine scales within any receiver block, since all
  Γ row sums are one. At the all-sure profile the four displacement values
  1000,1001,1002,−104 are distinct. Thus all fourteen nondiscrete response
  partitions fail, including after such transports.

I checked the twelve one-sided guard witnesses against
`QuittingOneSidedWeakUnitGuards` and the raw-guard adapter in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.
They are literal polynomial-face failures, not merely failed sufficient
rankings. Every ordered owner/passive pair is covered. Each singleton also
has a profitable join, so the instant no-join alternative fails.

The recipient-2 range obstruction is literal in
`IsQuittingConditionalFaceGapRange`, in
`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`:
Continue upper must be at least 4, whereas the relevant Quit lower bounds
are at most 1 and −1. The two opposite-signed 1→0 influence increments
are −9/2 and −1−K₀>0; they exclude both
`SignConsistentQuittingInfluence` in
`UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean`
and `IsAffineQuittingMembershipGain` in
`UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`.

For canonical cyclic-child predicates the only cyclic child is 012 and the
pivot is 3. The passive inverse row has two negative entries. The only
pivot pair with both participant premiums positive is 03, but its passive
child-2 increment K₂ is strictly positive, contradicting the prescribed
joint-outsider sign. No pivot pair has a zero participant premium. Versions
requiring two nonnegative pivot singleton comparisons fail since row 3
has only one. These checks use the actual raw rows in
`Classification/LCP/ThreeCore/CyclicChildSingletonAdapter.lean`,
`Classification/LCP/ThreeCore/CyclicChildPassiveInverseExit.lean`, and
`Cycles/CyclicChildJointPhaseSource.lean`, all under
`UniformEquilibrium/Quitting/`.

Finally, the inspected
`PairedCubicStationaryExample.exists_local_stationary_branch` in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`
gives an existential neighborhood around a different table, not a raw
membership criterion covering every proper-three root. An assumed root
or unknown neighborhood is not a produced strategic input. Conversely,
this review makes no assertion of nonmembership in every possible open
set witnessing that existential theorem, and no assertion that stationary
equilibria are absent.

Within these explicit boundaries, the signed-column criterion is a genuine
new finite raw-table producer rather than a renamed interface or a subset
of the inspected accepted classes. The general Fin4 conjecture is not
settled, and no strategy-class nonexistence claim is part of this verdict.
