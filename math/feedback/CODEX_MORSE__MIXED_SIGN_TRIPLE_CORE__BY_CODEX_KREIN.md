# Independent review of the mixed-sign triple-core theorem

Reviewer: CODEX_KREIN.

## Verdict and exact scope

**PASS**, ordinary mathematics, on Section 25 through EOF of
`notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`, whole-note SHA256
`ef8e9d12c2c11f8d9606fbd5e7a65654eca9f43933abc677b5632fb0c82d4900`.
No other review was read before this verdict. The corrected pure-exit
horizon statement is included in this seal. No unresolved mathematical
objection remains.

The checked result is a raw reward-to-UE theorem, not just a root inventory.
The greatest premium core is a derived three-player set C={1,2,3}; the
pair joining signs are positive on 12 and negative on 13 and 23 in both
directions; d₁(23)=d₂(13)=0 and d₃(12)<0. Core and exterior participant
premiums may be signed. For Fin4 the own singletons are nonnegative.
Weakening the seven strict signs, while retaining both equalities, gives
original-game UE by reward closure. The target is fixed before accuracy,
and deviations are unrestricted behavioral strategies.

The strict analytic theorem works for any finite ambient player set with
this greatest core, on every box strictly larger than a reward bound.
The Fin4 existence consumer has its own canonical sum-bound hypothesis,
which the author supplies literally. This is an equality-stratum theorem,
not a full reward-space neighborhood or an arbitrary-game solution.
No new Lean implementation has been checked or is claimed here.

## Root classification and the index computation

I re-derived the proof from the raw rewards rather than treating it as a
corollary of the joining-attractive theorem.

At a bad root, every successor coordinate strictly exceeds its singleton.
Each active player therefore has a positive participant-premium witness
within the active support, so that support is a premium trap. It lies in
C. An exterior player k has r_k(T+k)≤s_k for every T⊆C: otherwise C+k
would be a trap. Consequently its inactive gap satisfies
g_k≤s_k−w_k<0. This establishes full-game outsider strictness without
discarding simultaneous coalitions or assuming exterior premiums have a
particular sign globally.

The partly-sure cases are exhaustive:

- q₁=1 forces q₃=0 by d₃(1),d₃(12)<0, then q₂=1 by d₂(1)>0.
  The case q₂=1 is symmetric.
- If q₃=1 and q₂<1, then g₁=(1−q₂)d₁(3)<0, hence q₁=0,
  then q₂=0; a singleton support cannot be bad.
- If q₃=q₂=1, player2's optimality forces q₁=1, contradicting
  d₃(12)<0.

Thus a sure hazard in a bad root gives the pure-12 exit. At that full
root every unilateral deviation still faces a sure opponent, so the
terminal equilibrium is unrestricted. The literal repository game pays
zero in its initial live state: the N-date payoff is
(N−1)r(12)/N, not r(12). It is exact Nash for every N and delivers the
fixed target with error at most M/N. This is now stated correctly.
The self-loop v=w=r(12) also excludes a positively charged full-root
potential directly.

For proper active hazards the odds identity is exact. At a pair root,
the two active derivative factors can both be negative; what is needed
and proved is their positive product. The active determinant of −Dg is
negative for each of the three possible pairs.

At a triple root I obtain

    a_ij=(1−q_k)/(1−q_j) · [d_i(j)+z_k d_i(jk)].

The two imposed equalities give a₁₂,a₂₁>0 and a₁₃,a₂₃<0;
the last row gives a₃₁,a₃₂<0. Both directed three-cycle products are
positive, not merely their sum. Thus det(−Dg) is strictly negative.
The diagonal sign conjugation is only a matrix calculation, not an
exchange of strategic actions.

The map is the ambient polynomial-gap map F(x)=clip(x+g(x)), with no
input clipping inside g. At strict inactive coordinates its derivative
has inactive identity block in Id−DF and arbitrary upper-right entries.
Its full determinant equals the active determinant. Exterior reward
rows are retained in those upper-right entries; the calculation is not
a face index incorrectly substituted for a full index.

For an inactive core member k of a pair {i,j}, the displayed numerator

    d_i d_j(s_k−v_k)+d_i(v_j−s_j)d_k(i)
      +d_j(v_i−s_i)d_k(j)+(v_i−s_i)(v_j−s_j)d_k(ij)

has coefficient −d_i d_j≠0 in v_k. All three tie loci can therefore
be avoided on a dense open set of annotations. Outside-core ties were
already excluded. This does not perturb the rewards or their equalities.

If every root at a generic below-floor source were bad, every full root
would be regular, isolated, and of index −1. Compactness then gives
finitely many roots. The bounded clipped self-map has total degree +1
on the enlarged open cube, contradicting the finite index sum. No support
or sure-root branch has been left out of that count.

At a nongeneric or box-boundary source, generic approximants can be taken
inside the same box while retaining one strict source deficit. Compactness,
closed Nash inequalities, and a constant good-coordinate subsequence
restore a good root at the original source. It cannot become all-Continue
because that strict source deficit persists. Convexity keeps every
successor in the same box.

## Exact falsification attempts

These tests were calculated from the literal coalition table, including
all inactive coordinates. They are ordinary exact rational calculations,
not a numerical search or Lean checks.

### A genuinely bad triple root

For the author's original table, take

    q=(0,1/4,1/2,1/4),       v=(3,5/3,0,−2).
    Q=(9/32,5/8,1/4,1/4),
    C=w=(83/64,5/8,1/4,1/4).

Every successor is above its singleton although v₃<0. The inactive
player0 gap is −65/64. On the active core,

    Dg=[[0,3,−2/3],[1,0,−1],[−2,−5/2,0]].

The two cycle products are 6 and 5/3, so the full determinant of
Id−DF is −23/3. Thus the theorem does not secretly prove that all
roots return: its selected-root and degree argument is genuinely needed.

### A genuine inactive-core clipping tie

On the same table take

    q=(0,1/4,1/2,0),        v=(3,2,1/3,−2).
    Q=(3/8,1/2,3/4,1/4),
    C=w=(2,1/2,3/4,1/4).

Player3 is inactive and exactly tied, while the root is bad and player0
is strictly inactive. Raising only v₃ by δ>0 preserves the pair root
and gives g₃=−3δ/8. Its full regular index is then the sign of
−16/3. This confirms that inactive-core strictness cannot simply be
asserted without the annotation-polynomial step.

### A negative-joining bad pair

Modify only r₃({1}) from −1 to 2 and r₃({1,3}) from −2 to 1.
Every joining difference in the theorem is unchanged; the traps become
12,13,123 and the greatest core remains 123. Take

    q=(0,1/4,0,1/4),        v=(2,−1/3,1,−1/3).
    Q=(9/16,1/4,1/4,1/4),
    C=w=(43/32,1/4,13/16,1/4).

This is a bad full root with strictly inactive players0 and2. Both
active pair derivatives are −4/3; the full determinant is −16/9.
The proof correctly uses the product sign, not individual positivity.
The raw class does not prohibit overlapping pair traps.

These attempted falsifiers did not refute the theorem. They expose three
actual boundary modes which its proof handles, rather than testing only
already-good roots. Dropping an equality or allowing an opposite-sign
pair is outside the checked claim.

## Original-game consumer and weak boundary

I checked the declarations
`HasBoxedSelectedSingletonSublevelReturn` and
`not_isQuittingFullExactRootPotential_of_selectedSingletonSublevelReturn`
in
`UniformEquilibrium/Quitting/Projective/SelectedSingletonSublevelReturnSmoothDrift.lean`,
and
`exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_on_subbox`
in
`UniformEquilibrium/Quitting/Classification/Existence/SelectedSingletonSublevelReturnUniformPayoff.lean`.

The source return predicate matches exactly the producer just proved.
The potential-exclusion argument is signed and uses the same boxed
singleton-sublevel domain; it introduces no participant-premium sign
assumption. The literal Fin4 wrapper requires a bound strictly above
`quittingRewardBound`, the sum of absolute reward entries. Choosing that
M and B=M+1 meets both wrapper inequalities. The conclusion is the
original stochastic game's fixed-target uniform payoff, not an annotated
terminal-game equilibrium. The wrapper supplies the needed unrestricted
strategy semantics; no strategy-class completeness assertion is inferred
from the root inventory alone.

For weak signs the seven listed passive-entry perturbations have the
correct directions. None changes an own singleton, any participant
premium, either equality, or any premium trap. Hence they preserve the
greatest core exactly while making all seven signs strict simultaneously.
Uniform reward robustness bounds prescribed and deviating expected
averages by the same reward sup-distance, for every horizon and strategy.
A subsequence of bounded targets supplies one limiting target before
accuracy is chosen. This is a valid weak UE conclusion and makes no
unsupported weak local-index assertion.

Other checked source interfaces include the literal quitting-game timing
in `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Game.lean`,
the numerator identity
`quittingPairInactiveGapNumerator_eq_mul_endpointDifference` in
`UniformEquilibrium/Quitting/Root/PairInactiveGapNumerator.lean`, and the
named premium-core, coordinate-affine avoidance, ambient-degree, and
reward-robustness files cited by the author. None is being counted as an
already-implemented raw mixed-sign producer.

## Full fixture and actual coverage gain

I checked all fifteen reward rows, the exact trap list {12,123}, every
joining difference, and all fifteen pure-coalition profitable switches.
All-Never fails by player0's positive singleton.

An independent R₀ check is particularly short: all principal minors of
size at least two are nonzero. The pair determinants are
1,1,−3/2,2,2,2; the triple determinants are −1,−7/2,4,7;
the full determinant is 7/2. Each singleton column has a negative
off-diagonal entry, excluding a singleton homogeneous support. Thus no
nonzero homogeneous complementarity solution exists. At offset
(1,−1,−1,−1), exact support enumeration gives the unique solution
(0,1,1,1), inactive pivot residual 3/2 and active determinant 7.
The degree is +1. I also checked the full and triple inverse entries and
the passive row (−3/7,9/14,2/7).

As an additional narrow source check, the principal03 matrix has both
off-diagonal entries negative, is R₀, and has no standard LCP solution
at offset (−1,−1). It is not projectively Q; the full matrix therefore
does not satisfy the all-principal projective-Q hypothesis. This is not
an assertion that the full standard-Q matrix fails Q.

All thirteen singleton-row-sum partition witnesses check. The sole
survivor 0|123 is excluded by the exact displacement coordinates
−25/64,−1/2,35/32 at all hazards 1/2. I used the literal
`quittingSingletonBlockRowSum_eq_of_responseInvariant` and
`quittingDiscountedDisplacement` definitions in their cited stationary
source files, not merely graphical symmetry.

All fourteen proper-child witnesses check. In child012 the first-date
profile (1/3,1,2/3) has endpoints (0,0), (4/9,−7/9), and (2,2).
When player1 continues and both opponents continue, every future stopping
cap is its singleton0, so this is a full behavioral equilibrium rather
than a one-stage best-response calculation. Quiet player3 receives5/3
and can receive16/9 by immediate Quit. The other thirteen child profiles
are also full behavioral equilibria, have zero joint-Never mass and zero
child debts, and have the stated profitable omitted-player switches.
They exclude a universal fixed nonnegative weighted debt-plus-Never
bound for some omitted player of each child. They do not exclude every
child equilibrium or all possible quiet-lift mechanisms.

The following comparisons cover the accepted existence packets relevant
to these raw data, as well as the named implemented source screens:

- Core size3 excludes the at-most-two and signed-pair-core packets;
  the four negative joining differences exclude joining-attractive
  triple-core coverage, including under relabeling.
- At the grand row every participant premium is strictly negative.
  No player is globally protected, and no nonzero nonnegative weight
  vector gives a global weighted singleton floor. This excludes the
  protected-set/common-leaver and weighted-floor hypotheses.
- Sure coalition123 gives every active player premium1. Product-low
  fails, as does supportwise positive-weight nonpositive participant
  balance. These are distinct named conditions: the tracked
  `hasProductLowQuittingPremium_of_supportwiseBalance` proves balance
  implies product-low, not the reverse comparison.
- Trap12 has no leaving member. The boxed no-pair condition fails;
  the mixed-trap larger-support charge condition also fails since
  P₁₂₃({1})=3−2=1>0.
- The all-child witnesses exclude the finite-quiet universal debt
  bounds, including the nonnegative-singleton finite-quiet lifting
  criterion, within their actual universal quantifiers.
- The only positive singleton belongs to player0, but each of its pair
  participant rewards is0<1. Hence the prescribed cyclic-child joint,
  repeated-solo, two-buffer, global two-joint, and zero-premium pivot
  classes cannot match this fixture under relabeling.
- The accepted full-table two-joint neighborhood is explicitly shrunk
  to preserve two disjoint premium pair traps. Its core is full, whereas
  this fixture's core is proper. It therefore cannot consume this table,
  including after relabeling. The implemented paired-cycle raw region
  also forces two disjoint premium pairs through its strict own bounds;
  positive affine reward transport preserves that distinction.
- The exact R₀, degree+1, inverse/passive-row, and all-partition checks
  above exclude their named homogeneous, degree, matrix, and response-
  quotient exits. In the canonical cyclic singleton coordinates the
  pivot parameter is −1/2, neither the resonance value −1 nor the
  passive-inverse outer region beginning at1/4.

For one further bounded stationary comparison, the fixed-label active012
branch with q₃=0 and proper q₀,q₂ has

    Q₁=(1−q₀)q₂≥0,       A₁=−q₀−q₂+q₀q₂<0,

so its displacement (1−(1−q₀)(1−q₂))Q₁−A₁ is positive.
That branch cannot be interior Nash. This checks only that named branch
of the implemented PairedCubic local construction; it is not an exclusion
of every relabeling or every stationary equilibrium.

Thus the fixture provides genuine raw-class coverage beyond the accepted
packets and the compared implemented sufficient conditions. This verdict
does not claim exhaustive failure of all supplied-certificate interfaces,
nonexistence of a stationary equilibrium, or a positive-gap game. The
new mathematical input is the complete mixed-sign raw producer and its
verified UE consumer, not the coverage exclusions by themselves.

## Final standalone artifact check

**PASS** on the complete 618-line standalone
`exports/MIXED_SIGN_TRIPLE_PREMIUM_CORE_UNIFORM_EQUILIBRIUM.md`, SHA256
`e002b9df5d40270c3ab239916bf0c23e485bbf9ceff195c6c471ddc4bd6131fd`.
This is a bounded assembly/delta check against the completed independent
proof review above. The entire artifact was read; no counterpart assembly
addendum was read before this verdict. No repair is required.

The standalone preserves the raw greatest-core and joining hypotheses,
the two equality restrictions, all partly-sure cases, ambient indices,
generic tie removal, same-box limiting roots, original fixed UE target,
and simultaneous weak reward closure. No root or strategic witness has
become a supplied input. The corrected initial-zero-state convention gives
the pure exit's exact finite-horizon Nash property and M/N delivery error.

The newly expanded signed minimum proof is sound. Its collision-adjusted
solo probe stays in the same box, including upper-face coordinates;
the correction cancels in the differentiated drift. A sole binding
coordinate contradicts the probe. With several binding coordinates,
minimum geometry gives nonnegative binding partials, whereas the downward
source and exact root bounds give ε≤(3M+B)a and a strictly negative
binding partial. No participant-premium sign assumption has slipped into
this step. The Fin4 consumer separately uses the canonical sum bound,
choosing B=M+1 rather than assuming a max-entry box fits the wrapper.

The full rational table, all partition and proper-child comparisons, and
the bounded scope of accepted-class exclusions are retained. The packet
does not depend on a conference note or another mathematical packet.
Its source references are the named tracked declarations and ordinary
finite-dimensional degree facts; the handoff does not assert that the
new producer has been implemented.

I independently recalculated both additional displayed triple tests.
The small-hazard bad root has exactly the stated Q,C and derivative
matrix, with full determinant −41/9. After changing only r₁(123) to4,
the equality-relaxation test has exactly the stated Q,C and derivative
matrix, with cycle products 23/2 and −15 and full determinant +7/2.
Its annotation fits B=21>M=20, and the core and other signs are
unchanged. It refutes only the proposed all-bad-negative-index extension,
not selected return itself or UE. The tied pair and negative-joining pair
regressions also agree with the independent calculations above.

No math-directory dependency, review/process narrative, hidden strategy
assumption, or unsupported openness/implementation claim was found.
