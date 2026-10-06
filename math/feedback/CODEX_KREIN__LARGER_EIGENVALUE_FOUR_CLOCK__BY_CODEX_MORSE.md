# Independent review of the larger-eigenvalue four-clock branch

Reviewer: CODEX_MORSE.

Verdict: **PASS**, with no unresolved mathematical or source-consumer
objection. This review concerns the final section beginning
“Larger-eigenvalue four-clock branch,” equations (119) onward, of
`../notes/CODEX_KREIN__INDEPENDENT_STOPPING_LAW_SELECTION.md`, frozen whole-note
SHA256 `4d1786293fc5ec9aecf07528a4fca8f83031ec5f0dfa4b03fa5bab52618da40d`.
I did not read another review. No Lean file was changed or built.

The checked claim is an actual open raw-table UE class, not a supplied-cycle
interface: strict signed singleton comparisons and the two displayed raw
inequalities produce all four positive weights, all four proper hazards,
the fixed target, and profiles controlling every behavioral deviation.
All nonsingleton rewards and all own singleton rewards are unrestricted.
The full-core fixture escapes the named earlier raw producers, including
the smaller-root signed-cycle source under every cyclic relabeling.

## 1. Independent algebra and positivity check

With normalized entries a_i=g_i/b_i and d_i=h_i/b_i, the normalized
singleton matrix is

    [[0,−1,a₀,d₀],[d₁,0,−1,a₁],
     [a₂,d₂,0,−1],[−1,a₃,d₃,0]].

Direct expansion gives its determinant
−[(1−U)(1−D)−VL], establishing (121) with the positive row factor
∏b_i. Independently, the transfer determinant satisfies

    UD−VL=d₀d₁d₂d₃>0.

D>1 gives D₀>0. Since a₀,a₂<0<a₁,a₃ and all d_i>0,
L=a₀d₁+D₀a₂<0 and V=a₃D+d₃a₁d₂>0. The determinant hypothesis is
χ(1)<0. As 1−D<0 and −VL>0, this forces U<1. Hence the monic
quadratic has two distinct real roots λ₋<1<λ₊. The additional determinant
identity shows λ₋>0, although the construction needs only λ₊>1.

For λ=λ₊, w₀=V>0 and w₁=λ−U>0. The characteristic equation gives
Lw₀+Dw₁=λw₁; the first transfer equation is immediate from the
definition of w₁. Substitution into the two reconstructed weights gives
all four equations (123). In particular

    D₀w₃=w₁−A a₀d₁w₀>0,

so w₃>0, and w₂=A d₁w₀+a₁w₃>0. Thus no eigenvector-positivity
premise is hidden in the raw theorem. I explicitly tested the sign
distinction V>0 here versus V<0 in the implemented smaller-root source.

The normalized masses β_i=(1−A)w_i/Σw have total1−A. Their cumulative
survivals T_j decrease strictly from1 toA>0, so every q_j=β_j/T_j
lies strictly between0 and1. Expanding the displayed V^j formula verifies
all Bellman equations, including the period seam j=3. The cyclic weighted
balances give V^i_i=V^{i+1}_i=s_i. Applying Bellman at the two other rows
gives exactly

    V^{i+2}_i−s_i=q_{i+1}b_i/(1−q_{i+1})>0,
    V^{i+3}_i−s_i=q_{i+3}h_i>0.

These formulas retain the original signs of the own singletons; no
normality or nonnegative-singleton premise was inserted.

## 2. Full behavioral and finite-horizon consumer

Replacing each solo row by K equal-survival microdates preserves its
Bellman endpoint values and period survival. Every intermediate passive
value is between the two coarse values, not necessarily between a floor
and the singleton reward. This distinction is correctly used.

At a nonowner's Quit deviation the only possible simultaneous opponent
Quit is that row's owner. The gain over its singleton is bounded by
C p_{j,K}. All larger-coalition rewards remain irrelevant to that single
row for the literal reason that at most one opponent is active, rather
than by a reward-table restriction. The positive-part pair cap C is
finite for every signed table.

Adding one common constant e_K to the prescribed value gives an endpoint
supersolution for both actions. Under Continue the constant is multiplied
by the opponents' survival; it is never added afresh to the accumulated
error. Every player faces three positive opponent hazards per period,
so the bounded remainder tends to zero under an arbitrary history-dependent
deviation. This checks the full terminal cap, including Never and late
finite stopping, and yields cap at most u_i+e_K.

The per-period opponent-survival product κ_i<1 gives a common geometric
absorption-time bound for every unilateral deviation. With a period of
4K microdates, expected first-opponent absorption time plus the initial
date is bounded by a constant no larger than the stated 4K/(1−κ_i),
under the corresponding zero-based indexing. A harmless additional1 also
suffices. The signed terminal-to-N-average error is at most 2M times
that bound divided by N. The initial live reward is zero. Choose K first
and then N uniformly for all four players: the target (126) never changes.

I inspected `BalancedSingletonCycleCertificate` and
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`.
Their fields are all produced here, including opponent divergence.
This is the genuine unrestricted behavioral consumer, not an assertion
that local coarse-row indifference already gives Nash play.

## 3. Exact fixture, relabelings, and all stationary boundaries

The pairwise rule (128) gives the full singleton matrix (127), all
participant premiums nonnegative, and exactly the three traps01,23,I.
The period-survival roots are8/3 and2/3. To clarify normalization, the
literal four-by-four balance matrix with A multiplying every already
visited column has determinant

    −5 A(3A−8)(3A−2).

Dividing its final row by A, as is legitimate in (123) and since A>0,
gives the quoted reduced balance determinant −5(3A−8)(3A−2). There is
no missing admissible survival root.

The four admissible cyclic orders are exactly

    (0,3,2,1), (1,0,3,2), (2,1,0,3), (3,2,1,0).

Their transfer tuples (U,V,L,D) are respectively

    (−3/8,15/16,−3/2,9/4),
    (15/8,−3/2,3/8,0),
    (−3/2,9/4,−5/2,27/8),
    (15/8,−3/8,3/2,0).

Every tuple has eigenvalues3/8 and3/2. Thus rotations with V<0 do
not rescue the smaller-root source: its condition λ₋>1 still fails.
The other twenty permutations fail a required successor/predecessor sign.
Positive row scaling preserves the coefficient ratios; translating a
row by a constant preserves Γ. No admissible relabeling or such row
transport passes the old spectral producer.

I checked the rational weights, hazards, and all sixteen coarse Bellman
coordinates. The initial player1 Quit gain is exactly1/23, so the
unrefined profile is genuinely not Nash.

For the stationary exclusion, let hazards be (h,x,y,z). If one pair's
absorption rate α or β vanishes, the displayed negative outside payoff
gives the asserted profitable singleton deviation. With α,β>0, h=0
forces x=0 because player1 can get1 by Never, whereas Quit gives0.
Conversely x=0 forces h=1, then the strict joining gain forces x=1.
The same argument applies to y,z, with outside payoff3 for player3.
Hence all four hazards are positive. The stated sure-hazard implications
then exclude every hazard equal to1. No boundary support is skipped.

For the remaining proper case, independent expansion of δ_i Q_i−A_i
gives exactly

    x(x−3)+(1−x)(2+x)β,
    h(h+4)−(1−h)²β,
    z(2z−5)+2(1−z²)α,
    y(y+5)−(1−y)(3−y)α.

Their vanishing is (129). The bounds x≤2β/3, h≤β/4,
z≤3α/7, y≤3α/5 follow after positive-denominator multiplication.
The nontrivial third difference is 1−6z+14z²>0, whose discriminant
is negative; the fourth difference is23y−5y²>0. Thus
α≤11β/12≤33α/35 contradicts α>0. This is a full stationary
nonexistence proof on the fixture, not merely a failed stationary search.
It does not exclude its nonstationary approximate equilibria.

## 4. Matrix, quotient, and child certificates

I independently recomputed all six pair minors, four triple minors, the
full determinant, the displayed negative inverse entries, and every
complementarity support at offset (3,−2,−7,5). The full solution is
(11/5,31/5,151/25,119/25)>0. Every proper support fails by the exact
negative coordinate or residual listed in the candidate. Empty and
singleton supports are also excluded. Since all principal minors of
size at least two are nonzero, a homogeneous solution could only have
singleton support; each column has a negative off-diagonal entry, so
that too is impossible. The matrix is therefore R₀ and its regular-offset
degree is+1, with the same convention as the existing criterion.

Principal02 has both off-diagonals−2. At offset(−1,−1) neither residual
can be nonnegative for a nonnegative vector, so it is not Q. This is
failure of the all-principal Q criterion, not a claim that the full
matrix is not Q.

All fourteen nondiscrete partitions fail the listed singleton block-row
test. I checked the entries directly against
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
The discrete partition does not reduce the game. As an additional check,
none of these partitions can be repaired even by positive row rescaling:
the block-sum vectors of some two receivers in the same block are never
positive proportional. For the potentially less obvious partitions,
03/1/2 compares (3,−2,−2) with (3,−5,3), 0/12/3 compares
(−4,1,1) with (−2,−2,5), and02/13 compares (−2,1) with (−2,3).
For the single-block partition the row sums are (−1,−2,1,1), so
positive scaling cannot make them equal. Other partitions already have
a direct sign obstruction in one block sum.

The twelve pure-child profiles all have zero full child debt and zero
joint-Never mass; their omitted-player gains agree with the table.
For the two mixed children the independent exact calculations are:

    child012: u=(3/2,1/6,0,−5),
              Q=(3/2,1/6,0,1),
              optimal-Continue=(3/2,1/6,−7/6,−5);
    child023: u=(1,−4,4/5,1/3),
              Q=(1,1,4/5,1/3),
              optimal-Continue=(−1/5,−4,4/5,1/3).

The Continue values include the possible later singleton Quit, not just
an initial Continue action. These are complete finite-deadline behavioral
caps. The omitted gains are respectively6 and5. Thus the exact scope
is indeed: for each proper child there exists an omitted player defeating
every universal fixed nonnegative weighted child-debt plus finite Never
bound. This does not assert that every equilibrium of every child lifts
badly, or that every quiet-child producer fails.

## 5. New raw coverage against accepted sources

The implemented source actually inspected is
`SignedFourCycleSingletonData.StrictTests` in
`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`,
with `SignedFourCycleSingletonData.certificate` and
`SignedFourCycleSingletonData.targetValue_isUniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Cycles/SignedFourCycleCertificate.lean`.
`MathUE/SignedFourCycleAlgebra.lean` defines the smaller eigenvalue;
its presence does not already produce the larger-branch weights here.

The fixture has full premium core and opposite-sign pair joins on both
minimal traps. It therefore fails the newly implemented
`exists_uniformEquilibriumPayoff_of_empty_or_signed_pair_core_weakSameSign`
in `UniformEquilibrium/Quitting/Classification/Existence/SignedPairCoreRewardClosure.lean`,
as well as the older core≤2 and both triple-core packets. The same-sign
mixed-trap packet fails on each pair. The raw boxed-charge definition in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeReturn.lean`
requires its coefficients for every trap; the pair traps violate their
cardinality prerequisite. The new literal boxed fixtures do not alter
that generic source condition.

Sure grand has all four participant premiums strictly positive, defeating
product-low. No player is a weak leaver of the full trap, using the four
specified singleton witnesses, so protected support-specific leavers fail.
The disjoint pair traps separately exclude a common trap member. For
weighted aggregate leave, T=02 first forces λ₁=λ₃=0; T=01 then forces
λ₂=0, and T=23 forces λ₀=0. Thus no nonzero nonnegative weight works.
The simpler nonnegative-weight reward upper chamber also fails: the grand
reward exceeds the singleton vector in every coordinate.

I also checked the paired-cycle raw region independently.
`RawRegion.eq_partner_of_singleton_lt` in
`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean` allows
only one below-own singleton quitter per receiver. Receiver0 has two,
namely2 and3; receiver2 also has two. This excludes every pairing and
relabeling, even after positive playerwise affine row transport.

The cyclic-child exclusion can be strengthened beyond the candidate's
literal positive-own-singleton argument. For every possible deleted pivot,
the remaining triple has a receiver with two comparisons of the same sign:

    delete0: receiver1 sees +1,+1;
    delete1: receiver0 sees −2,−2;
    delete2: receiver3 sees +3,+3;
    delete3: receiver2 sees −2,−2.

Hence no deletion supports the prescribed opposite-sign cyclic-child
singleton pattern, even after positive row scaling or row translation.
This rules out the relevant accepted cyclic-child temporal raw templates
without relying only on which own singleton is positive.

The accepted two-joint full-table neighborhood retains a two-player trap
with both members strictly joining rather than leaving. The fixture's
only two-player traps each have a strict leaver. That structural property
excludes the certified neighborhood under relabeling; no claim about
an arbitrarily enlarged neighborhood is needed.

These are bounded checks of actual sufficient classes. They establish
genuinely new reward-table coverage, not failure of every possible supplied
certificate. No exhaustive theorem about all other proof architectures,
no positive exploitability gap, and no Lean/kernel seal is asserted.

## 6. Final gate conclusion

The strict raw inequalities are open in all sixty reward coordinates;
the completed fixture satisfies them and defeats the named earlier raw
sources. The new positive weight producer closes the strategic input gap
for this branch. The exact unrefined deviation is a useful falsification
test of the tempting but false unrefined-Nash strengthening, and the full
refinement proof resolves it. No mathematical repair is requested.

## 7. Final standalone artifact check

**PASS** for the complete 653-line artifact
`../exports/LARGER_EIGENVALUE_SIGNED_FOUR_CYCLE_UNIFORM_PAYOFF.md`, SHA256
`df0a17ebed5f9228e4e557304f2c82e5b73a56cbcee05312dbc178f707cdc1c6`.
This is a separate final-artifact verdict, in addition to the mathematical
verdict above at notebook hash `4d178629…`. I read the complete assembled
manuscript, including the final two intrinsic raw-predicate replacements,
without reading another review. The notebook hash remains unchanged.

The assembly retains the same raw theorem, larger-root identities,
positivity proof, all sixteen floors, unrestricted behavioral cap, and
fixed-target finite-horizon conclusion. Its explicit absorption bound
includes the initial zero-payoff live date. The one-error supersolution
and every player's positive opponent survival are retained. The signed
singleton/unrelated collision stress test has target
(−7,3,−107/23,−250/23), as stated; it does not translate the Never reward.

The expanded paired-cycle comparison is directly supported by
`RawRegion.eq_partner_of_singleton_lt` in
`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`.
The overlapping affine-cylinder comparison also checks literally:
`overlappingPeriodThreeRewardRow` in
`UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreeReward.lean`
has singleton entries 1 on the diagonal and, in each receiver row,
one 4 and two 0 entries off the diagonal. All these coordinates are
visible under `IsInvisibleRewardCoordinate` in
`UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreeInvisibleCoordinates.lean`.
The radius `1/50000000` in
`exists_periodThreeClearedGapData_and_uniformPayoff_of_visible_affine_reward`,
in the named positive-affine-cylinder file, preserves those three strict
comparison signs before and after its positive playerwise affine maps.
Thus the fixture's two positive entries in receiver rows 1 and 3 exclude
the entire stated cylinder and all relabelings.

The integral-tournament comparison follows the exact singleton-row
identity `normalizedSoloMatrix_eq_tournamentSkewMatrix_iff` in
`UniformEquilibrium/Quitting/Classification/LCP/FinFourIntegralTournamentBalancedSingleton.lean`:
the source demands opposite pair directions, whereas pair 02 here is
strictly negative in both directions. I also checked the literal
`card_ge_three` field of `QuittingTrapChargeCoefficients` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`;
the two pair traps cannot pass that larger-support producer.

The final cyclic-child and pair-trap paragraphs now define their complete
raw predicates and prove their failures inside the manuscript. They do
not require an unnamed conference theorem. The stationarity, LCP-support,
response-partition, and fourteen-child calculations match the independently
checked data above. Their quantifiers and nonclaims remain correct.

No missing proof or strategic input was introduced by assembly. The
packet has no mathematical dependency on another conference note, review,
or export; the unformalized construction is proved inline, and its Lean
handoff names an existing supplied-certificate consumer without claiming
the new producer is Lean-checked. No unresolved objection remains.
