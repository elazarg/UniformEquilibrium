# Independent review: opposite-sign matching phase producer

Reviewer: CODEX_BROUWER. Ordinary mathematics and read-only source checks;
no Lean build or new Lean verification is asserted.

## Claim, frozen scope, and verdict

I independently read all 360 lines of
[the candidate](../notes/CODEX_NOETHER__OPPOSITE_SIGN_MATCHING_PHASE_PRODUCER.md),
bound to SHA256
`7c418080b8cb05c94120af80005fd73d88ddff772c64efe09444e282149d17ba`.
No counterpart review was read. The claim is a raw four-player producer:
H>2, one scheduled pair's normalized participant increment Π_A<−1,
the other pair's increment Π_B>−1, the stated passive coefficients,
the explicit scalar threshold (T), and twelve collision caps (C) produce
an exact proper periodic terminal Nash profile and one fixed uniform payoff
against every behavioral deviation. All remaining reward entries are arbitrary.

**PASS.** The raw-to-rate and full-strategy proof is valid, and the complete
fixture supplies genuine class separation from the applicable implemented
and accepted raw existence producers checked below. No strategic witness,
favorable root, public randomization, or uniform-limit interchange is hidden.
No unresolved mathematical objection remains. A final standalone artifact,
if assembled, will still need its own bounded byte-specific check.

The author separately supplied an additional favorite-word exclusion after
freezing the note. I verified it independently and give its full proof below.
It changes no theorem input or proof. It completes the architecture comparison
over all three possible scheduled-pair partitions, without presuming a radius
for the accepted below-floor local theorem.

## Independent scalar and collision checks

Set γ=−Π_A−1>0, β=−Π_A, c_B=Π_B+1>0 and h=H−1>1.
For y≥y_L, C(y)=hy−ky²<0. After multiplying equation (A) by1+x,
the quadratic has leading coefficient γ(1+y)²>0 and constant C(y)<0.
Its discriminant is strictly positive and its two roots have opposite signs.
Thus the displayed radical gives exactly one positive root, continuously
on the entire half-line. Division by1+x loses no positive root.

The lower estimate x(y)>y(ky−h)/[γ(1+y)²] is strict. Direct differentiation
gives [(2k+h)y−h]/[γ(1+y)³], positive on the selected half-line. Therefore
x(y)>m>0 uniformly. For the upper estimate, βx/(1+x)<β and
β<(h+2k)y imply
γ(1+y)²x<ky²+2ky<k(1+y)². Hence x<k/γ. This is a genuine global
branch bound; neither monotonicity of x nor a strategically preferred root
is assumed.

Threshold (T) is exactly the strict sign R_B(y_L)<0. Since h,c_B>0,
x>m, and y/(1+y)<1,

    R_B(y)/x² ≥ c_B y−K_B−h/m−max(Π_B,0)/m².

This remains valid when Π_B<0 or K_B<0. The prescribed finite Y makes
R_B(Y)>0. Continuity and the intermediate value theorem supply a root
strictly between the endpoints. The proof requires neither uniqueness of
this second scalar root nor continuity of a selected root in all raw data.
Every root in that interval satisfies the subsequent estimates.

The crucial passive-collision estimate is correct. Dividing equation (A)
by y(y+2) and using βx/(1+x)≤β gives

    γx/[1−(1+y)⁻²]
      ≤ k−[(2k+h)y−β]/[y(y+2)]
      ≤ k−[(2k+h)y_L−β]/[Y(Y+2)]
      ≤ k−2δ < k−δ=C_A.

Both the numerator lower bound and denominator upper bound have the
required signs. The minimum in δ ensures 0<δ≤k/2 and hence
0<C_A<k. This last strict comparison is not cosmetic: the allowed triple
join can exceed the pure-B passive payoff. The theorem does not quietly
encode a safe pure B exit.

## Actual strategic inputs and horizons

I rederived the endpoints from the original rewards. An active player's
Quit endpoint is U_i. Its Continue endpoint equals
q_a(s_i−b_i)+(1−q_a)W_i=U_i. Passive Continue is W_i by the two
selected equations (E). For A players, the Quit deficit is at least
C_A b_i[1−(1+y)⁻²]>γb_i x. For B players, Quit≤s_i<W_i.
These are all sixteen pure-action endpoints, including the two-opponent
simultaneous collision and its actual triple reward. The unused grand
coalition is unreachable under one unilateral replacement, not deleted
from the game.

The policy identities and strict joint survival contraction uniquely realize
the signed phase vectors as actual terminal values. For each player, the
three opponents' period survival is strictly below one independently of
that player's strategy. The endpoint supermartingale/backward-iteration
bound therefore leaves an absolute remainder tending geometrically to zero,
uniformly over complete behavioral deviations. Never and unbounded stopping
times are included. Negative own rewards or negative phase values cause no
exception to this argument.

The expected opponent absorption-time bound gives the stated conservative
terminal-to-average error2M C_time/N and regret4M C_time/N, including the
initial live zero date. The target is the actual phase-A terminal vector,
chosen before accuracy; the same profile works for every sufficiently large
horizon. This is stronger than merely separate finite-horizon equilibria.

The actual inspected consumers are
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.
The manuscript produces their policy equations, root-Nash inequalities,
and playerwise opponent contraction. No additional consumer hypothesis is
missing.

## Adversarial exact signed stress test

I constructed a separate exact test, not used in the existence proof:

    H=3, Π_A=−2, Π_B=−1/2, k=110/27, K_B=79/32,
    y_L=1, Y=13, x=2, y=3,
    m=14/27, δ=22/1053, C_A=4268/1053.

The high-branch quadratic at y_L has negative value at x=1/2, so its
positive root x_L>1/2. At that endpoint
R_B(1)=3/4−x_L−63x_L²/32<−31/128<0.
The upper-threshold slack is exactly39/112>0. Both original equations
hold at x=2,y=3. Thus this tests a strictly negative Π_B, not only the
positive fixture arm.

Choose signed singleton levels (−3,2,−1,4), positive scales(1,2,3,4),
and all twelve caps at equality. Set every other unused coordinate to37.
Direct exact enumeration of all sixteen endpoints gives

    U=(−13/3,5/4,−5,5/2),
    W=(−5,5,−7,10).

At phase A the passive B gaps are3 and6. At phase B the passive A
gaps are2527/1404 and2527/468. All eight active endpoint equalities
hold exactly. Thus signed singleton values, negative active and passive
values, binding caps, negative Π_B, and arbitrary unused rewards all pass
simultaneously. No phasewise singleton-floor assumption was used.

## Fixture, full proper-three exclusion, and new coverage

For the manuscript's complete fixture I independently recomputed
m=272816/43245>6, δ=10039/81600 and ζ=−54133/32640.
The lower sign estimate is −3229/612<0, while the displayed upper sign
bound is59/36>0. Its cap slack and its profitable pure-B outsider join
are both10039/163200. These are exact rational checks, not reliance on
the reported numerical root. All fifteen pure exit cases, all Never,
and the fourteen proper-child zero-debt/zero-Never witnesses check.
The child statements have the correct universal-lift quantifiers; they
do not claim every possible quiet child equilibrium has a profitable lift.

The nonnegative raw J-row exclusions also check. At an A singleton the
other child A joining gain is nonpositive, whereas its omitted B o-partner
gains1/2. At a B singleton all child A joining gains are negative while
its omitted B mate gains2. At a full B coalition or full B-containing
triple every child joining gain is zero while the omitted gain is positive.
These cover all fourteen children and directly violate the actual raw J
inequality, independently of a selected profile.

The proper-three stationary proof is valid. For a support containing full
B, the designated B player's Never payoff is zero and every Quit outcome
is strictly positive. For support012, player2's equation yields the
displayed positive D(x) and player0's equality gives c<a. Then
a+c−ac<a(2−c), so

    Never₁=a(4+7c)/(a+c−ac)>(4+7c)/(2−c)≥2,

whereas Quit₁≤1. The pair swap handles the other full-A support. This
excludes every proper-three stationary profile and hence the actual
output of `PairedCubicStationaryExample.exists_local_stationary_branch`
in `UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`,
including relabelings and positive affine transports. No exclusion of all
full-support or sure-boundary stationary profiles is inferred.

Against the strongest arbitrary-passive crossed-matching theorem, the
favorite singleton signs fix f. Both harmful scheduled matchings have an
A participant reward below its mate's singleton payoff. Against the general
inverse-positive nonnegative-participant test, every pair partition has a
negative A premium. Arbitrary passive rewards do not repair either input.
The internal signed-column cone also cannot apply: this matrix has a positive
inverse, forcing all column signs positive, but Π_A<0.

Against the accepted below-floor family, on word02/13 the B active value
is above its singleton; on word03/12 its passive value is above its singleton.
Here is the additional complete exclusion of the third word,01/23. For
player1 at its active01 phase, U₁=1−q₀/2. At passive23 every absorbing
Continue reward is zero, so W₁=(1−q₂)(1−q₃)U₁. Its forced-Quit gap is

    Q₁−W₁=(1−q₂)(1−q₃)(1−U₁)
            +(1/2)q₂(1−q₃)+2(1−q₂)q₃+100q₂q₃>0.

This holds for every proper choice of all four hazards, independently of
any same-rate ansatz. Thus no relabeling of the accepted proper two-pair
below-floor architecture can supply the fixture. This is an intrinsic
output obstruction, not a guessed neighborhood radius. It should be retained
in a standalone coverage argument.

The remaining finite source tests check as stated. The only traps are B
and I; the full trap prevents the proper-core criteria. At background A
the four forced-Quit premiums are(−11/10,−1/2,−11/10,−1/2), excluding
every nonzero nonnegative global forced-Quit floor weight. The insertion
charge L_I(B)=δ>0 excludes the boxed larger-trap and mixed-trap hypotheses.
Sure B violates product-low. No player has nonnegative participant premiums
everywhere. The matrix has positive inverse, R₀ degree+1, a harmful not-Q
principal pair, and a negative diagonal in every triple inverse. Row sums1
exclude nonnegative terminal upper weights. Those same row sums and four
distinct all-sure responses exclude every nondiscrete response quotient,
even after positive playerwise affine transport.

The singleton signs exclude the stated four-cycle, cyclic-child, tournament
and unique-negative paired patterns; the explicit visible-cylinder ratio
test is invariant under positive affine transport. The crossed lower-face
witnesses, conditional-range contradictions, and opposite-sign influence
increments ζ−5 and43/25 are all literal actual-table comparisons.
Source declarations inspected for these claims include
`RawRegion.eq_partner_of_singleton_lt`
(`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`),
`quittingSingletonBlockRowSum_eq_of_responseInvariant`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`),
`r0Degree_eq_sign_det_of_nonnegative_inverse`
(`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`),
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`),
`QuittingHalfWeakPolynomialGuards`
(`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`),
`QuittingOneSidedWeakUnitGuards`
(`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`),
`IsQuittingConditionalFaceGapRange`
(`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`),
`SignConsistentQuittingInfluence`
(`UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean`),
and `IsAffineQuittingMembershipGain`
(`UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`).

My export-significance verdict is affirmative for the mathematical class,
subject to the separate final-artifact gate. This is a global raw family
with complete unrestricted strategic production and an actual separating
table, not just a second root, a larger constant, or a supplied periodic
certificate. It does not settle arbitrary Fin4. No export was edited or
promoted, and no new Lean theorem is claimed.

## Separate average-cap strengthening: PASS

This paragraph checks a proposed delta beyond the frozen hash, without
re-reading or assuming a counterpart verdict. Let L_i=s_i−C_A b_i for
i∈A and L_i=s_i for i∈B. The two individual pair caps may be replaced by

    r_i({i,f(i)})+r_i({i,o(i)})≤2L_i,
    r_i({i,f(i),o(i)})≤L_i.

At i's passive phase the two opponents have exactly the same probability q.
Consequently its actual forced-Quit value is

    (1−q)²s_i+q(1−q)[r_i({i,f(i)})+r_i({i,o(i)})]
        +q²r_i({i,f(i),o(i)})
      ≤(1−q)²s_i+[1−(1−q)²]L_i.

This is precisely the old bound. The raw scalar equations, root production,
active endpoints, policy values, contraction, and every full behavioral and
finite-horizon argument are unchanged. The equality of the two scheduled
opponent probabilities is produced by this theorem, not a new user-supplied
strategic condition. No averaging of players or correlated action is used.
Thus the stronger raw theorem is **PASS**, including signed levels and cap
equalities. It has eight scalar cap inequalities in place of twelve.

The proposed exact split r₀(01)=ζ+2, r₀(03)=ζ−2 preserves the pair sum
and every endpoint of the selected profile. Its first individual cap fails
by2−δ/2>0, so the delta is a strict raw enlargement. Every other coordinate
may remain the original fixture. The base fixture remains an admitted member
of the stronger theorem and retains its already-checked full source separation;
the significance verdict therefore does not require assuming that every
additional split table has those same source exclusions. A final artifact
should either retain that distinction or prove any extra split-table coverage
claims explicitly.
