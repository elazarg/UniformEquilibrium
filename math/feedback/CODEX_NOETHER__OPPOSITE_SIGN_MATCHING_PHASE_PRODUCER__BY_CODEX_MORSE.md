# Independent review of the opposite-sign matching-phase producer

Reviewer: CODEX_MORSE.

Verdict: **PASS**, with no unresolved mathematical objection to the frozen
360-line candidate `../notes/CODEX_NOETHER__OPPOSITE_SIGN_MATCHING_PHASE_PRODUCER.md`,
SHA256 `7c418080b8cb05c94120af80005fd73d88ddff772c64efe09444e282149d17ba`.
This review was derived from that manuscript and the relevant actual source
declarations, without reading another review. It covers ordinary mathematics,
not a Lean build or a kernel-verification claim. A later standalone artifact
requires its own bounded assembly check.

## Claim and semantic scope

The raw table has the H>2 favorable matching and two equally harmful
singleton comparisons in each row, with arbitrary signed own levels and
positive row scales. The two scheduled pairs have normalized participant
premiums Π_A<−1 and Π_B>−1. The A passive reward is −k below own
singleton, and the B passive coefficient exceeds the literal radical
threshold (T). The twelve cap inequalities (C) are raw reward bounds.
No rate, root, continuation value, equilibrium, or strategy certificate is
an input. The conclusion is exact terminal Nash against every behavioral
deviation and one fixed original-game uniform payoff, with independent
private randomization and the initial live-zero date retained.

All these quantifiers are justified. In particular, no phasewise singleton
floor is silently used for the A players, no nonnegative own-singleton
assumption is needed, and Π_B is allowed to be negative in (−1,0).

## Root production and cap estimate

For y≥y_L, the quadratic in x has positive leading coefficient γ(1+y)²
and strictly negative constant C(y). Hence it has exactly one positive
root. Its displayed radical is continuous, with strictly positive
discriminant. This produces the branch without an implicit root oracle.

The derivative of y(ky−h)/[γ(1+y)²] is exactly
[(2k+h)y−h]/[γ(1+y)³]. It is positive on the stated domain, yielding
x(y)>m. The separate condition (2k+h)y_L>β proves x(y)<k/γ;
the proof does not confuse this upper bound with the lower branch bound.

After dividing the second equation by x(y)², the inequalities
(1+x)²/x²>1, h/x<h/m, and
−Π_B y/[(1+y)x²]≥−max(Π_B,0)/m² give the claimed large-y sign.
Condition (T) supplies the opposite sign at y_L. The chosen finite Y
therefore supplies an actual root in (y_L,Y), fixed before any accuracy.

For the passive A inequality, the exact identity is

    γx/[1−(1+y)⁻²]
      =[βx/(1+x)−hy+ky²]/[y(y+2)].

Replacing βx/(1+x) by β and using the positive numerator
(2k+h)y−β and the upper denominator Y(Y+2) proves the displayed
bound by k−2δ. Since δ≤k/2, one has 0<C_A=k−δ<k and a
strict passive gap. The use of C_A<k is genuine: a pure B exit is not
automatically protected against A joining. All simultaneous two-opponent
outcomes are retained in the estimate.

## Full behavioral and horizon consumer

I recomputed the four normalized phase values and both action endpoints
at each type of phase. Active Quit and Continue coincide. Passive Continue
is precisely the second coupled equation, while passive Quit is bounded
strictly below the value by the cap estimate for A and the positive
c_B y displacement for B. These account for all sixteen endpoints,
including the four triple rewards seen by a unilateral deviator.

Every player has three positive opponent opportunities per period.
Thus the opponent-deleted survival product is strictly below one even
when the deviator Never quits. This both identifies the proposed values
with actual payoffs and makes the finite-iteration remainder vanish for
arbitrary behavioral replacements. Signed own levels cause no difficulty;
one is not using a payoff translation on a positive-Never event.

The geometric tail gives the stated expected absorption-time bound and
the conservative 2M C_time/N delivery error and 4M C_time/N regret bound.
The same profile and phase-A target work at every accuracy. Exact finite-
horizon delivery is not asserted. The exact declarations
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean` consume exactly
the policy, endpoint, and deleted-opponent contraction data proved here.

## An independent signed adversarial test

The following exact point tests the allowed negative Π_B branch:

    H=3,  Π_A=−2,  Π_B=−1/2,  k=110/27,  K_B=79/32,
    y_L=2,  Y=10,  x=2,  y=3.

Both coupled equations vanish exactly. Here m=332/243>1 and
δ=247/3240, C_A=12953/3240. At y_L the positive quadratic root
solves 243x_L²−143x_L−332=0, so x_L>1. The lower crossing residual
is 4/3−47x_L²/32<−13/96<0. The upper-radius slack is 2835/1328>0.
Thus this is an admitted raw point, not only a solution of the equations.

Its hazards are q_A=2/3 and q_B=3/4. For any signed s_i and positive
b_i the values are

    A: U_i=s_i−4b_i/3,    W_i=s_i−2b_i;
    B: U_i=s_i−3b_i/8,    W_i=s_i+3b_i/2.

For example s=(−3,2,−1,4), b=(1,2,3,4) is allowed literally, with
the caps imposed on the original reward coordinates. The passive A cap
margin is 6041b_i/3456>0. This tests opposite signs of c_A,c_B while
both active phase premiums are negative; no hidden Π_B≥0 premise exists.

## Exact coverage fixture

The stated m=272816/43245, δ=10039/81600, and
ζ=−54133/32640 recompute exactly. Both endpoint tests and both δ/2
slacks are correct. The full table satisfies every cap and scheduled
entry of the raw theorem. Its only premium traps are B and I, with
full greatest core. Every claimed pure-coalition deviation is valid.

The fourteen child witnesses are exhaustive. There are four singleton,
one full-A, one full-B, four cross-pair, two one-B triple, and two full-B
triple cases. In a full-B triple the A participant's gain from remaining
is ζ+43/25=δ/2, while its B participants obtain 100 instead of zero.
The omitted A obtains its positive grand payoff. These are actual
zero-debt, zero-Never child profiles, not selected scalar continuations.

The nonnegative quiet J-row failures also hold. The phrase “cross child”
includes the two triples with only one B member: use that sole B's
singleton background and the omitted B mate. Its positive omitted gain
faces only nonpositive child joining gains. This makes the claimed
fourteen-child exhaustion explicit; no mathematical repair is required.

For proper-three stationary profiles, I independently obtained the same
player-2 equation 1−C₀x−D(x)a=0. Substitution gives player0's Quit
value D(x)(a−c), so its strictly positive Never value forces c<a.
Then player1's Never value exceeds (4+7c)/(2−c)≥2 although all its
Quit outcomes are at most 1. Full-B supports are excluded by the player
whose favorite is omitted and whose Quit outcomes are all positive while
Never pays zero. The conclusion correctly stops at proper-three supports.

## Actual overlap and the below-floor comparison

The accepted arbitrary-passive matching condition fails in both possible
harmful scheduled matchings: its A participant-versus-mate comparison is
negative in each. Every partition fails the additional nonnegative-
participant-premium inverse producer. These are strict raw failures,
unchanged by positive playerwise affine transport.

The common-coefficient below-singleton family cannot contain this table:
on 02/13 the B premium is +1, and on 03/12 its participant-versus-mate
gap is +1/2. More strongly, an all-below-singleton proper profile cannot
use either harmful matching. Active B value exceeds own singleton on
02/13; active indifference forces passive B value above own singleton
on 03/12.

For completeness the favorable schedule 01/23 cannot even be a proper
two-phase equilibrium. Let its four positive hazards be q_i. Player1
has active value U₁=1−q₀/2<1. At its passive phase all Continue
absorption outcomes pay zero, while the Quit outcomes are 1,1/2,2,100.
Thus its Quit-minus-Continue gap is

    (1−q₂)(1−q₃)(1−U₁)+(1/2)q₂(1−q₃)
       +2(1−q₂)q₃+100q₂q₃>0.

This rules out all three perfect matchings for the all-below-floor
architecture, not just the labeling of the neighboring packet. It also
confirms that the open-neighborhood theorem there is not being treated
as an unrestricted theorem for all matching tables.

The remaining bounded source failures check: product-low at sure B;
weighted global floor at sure A; positive intermediate leave δ at full
trap I and subset B; no protected player; singleton R₀ degree +1 and
the harmful-pair/triple-inverse obstructions; row-sum exclusion of a
weighted terminal upper bound; and every nondiscrete response partition,
including positive affine transports. The paired/cyclic/tournament signs,
visible period-three pair-gap ratio, lower guards, conditional range,
and signed-influence/affine-gain tests all agree with their cited actual
definitions. No arbitrary stationary nonexistence is inferred from these
specific source failures.

## A structural raw-class strengthening

The proof actually uses a weaker condition than the two individual pair
caps for each passive player. Because its two opponents have equal
hazards q, their two singleton-exit events have the same probability
q(1−q). Let L_i=s_i−C_A b_i for i∈A and L_i=s_i for i∈B.
It suffices to replace (C) by

    r_i({i,f(i)})+r_i({i,o(i)})≤2L_i,
    r_i({i,f(i),o(i)})≤L_i.                              (C_avg)

Indeed the forced-Quit value is exactly

    (1−q)²s_i+q(1−q)[r_i({i,f(i)})+r_i({i,o(i)})]
      +q²r_i({i,f(i),o(i)}),

so the identical bound used in the proof follows. No source equation or
rate changes, since these cross-pair participant coordinates are used
only by a passive deviator. This is a genuine removal of individual raw
restrictions, not a constant refinement.

For example change only r₀(01) from ζ to ζ+2 and r₀(03) from ζ
to ζ−2 in the displayed fixture. Their sum is unchanged; the original
individual cap at 01 fails, but (C_avg) and the complete produced
equilibrium remain valid. This extension is not part of the frozen
7c418080 claim or its PASS seal. It is a proved mathematical suggestion
for the author to incorporate and submit as a clearly identified delta,
if one strongest packet is desired.

## Final strongest artifact and assembly verdict

Final-artifact verdict: **PASS**, with no unresolved mathematical objection,
for all 606 lines of
`../exports/OPPOSITE_SIGN_MATCHING_PHASE_UNIFORM_EQUILIBRIUM.md`,
SHA256 `2b9f54370677ec176749a0a9c6c008bdb56d5733594d85f60a101374e148ac35`.
I read the complete artifact and checked its additions against the proof
and source comparisons above without reading another review. This is a
bounded assembly/delta check, not a new Lean verification.

The artifact incorporates the averaged-cap strengthening exactly: four
pair-sum inequalities and four triple inequalities replace the twelve
individual caps. Equal opponent hazards, rather than any correlated
averaging, justify that change. The actual forced-Quit formula retains
both singleton events and their simultaneous collision. The split-coordinate
example proves strictly greater raw scope; the artifact correctly does
not reuse all source-exclusion calculations for that altered example.

The new signed stress test chooses y_L=1 and Y=13, rather than the
y_L=2, Y=10 test recorded in my original review. I checked it directly:
m=14/27, δ=22/1053, C_A=4268/1053; the lower quadratic is
108x_L²−2x_L−56=0 and is −30 at x_L=1/2. Its lower residual is
strictly below −31/128, and the upper threshold slack is 39/112.
The exact root x=2,y=3 produces the displayed signed U and W vectors.
The two A passive margins are 2527/1404 and 2527/468, and the B
margins are 3 and 6. Thus the equality-cap and negative-Π_B claims are
tested by an admitted raw table, not only by a formal solution of the
rate equations. The unused reward value 37 is harmless because a single
deviation can access at most the scheduled pair plus itself.

The complete fixture, all fourteen child tests, intrinsic all-three-
schedule exclusion, proper-three proof and additional finite source
screens agree with the reviewed arguments. The triple-inverse statement
now correctly gives diagonal entries −1/6, −1/6, −3/2. The new signed-
column comparison is also valid: this fixture's strictly positive inverse
forces every column sign positive, while each schedule has a negative
A participant premium.

The self-contained behavioral proof includes Never and unbounded stopping,
signed own levels, the initial live-zero convention, and a single target
fixed before horizon accuracy. The finite-horizon bounds are upper error
bounds, not an exact-delivery assertion. Its source citations point to
the established certificate consumers and named raw predicates; no
conference-file or review dependency supplies a missing proof. The Lean
handoff clearly states the new raw producer still to formalize.

Accordingly the final artifact, not merely the earlier individual-cap
manuscript, has an independent mathematical PASS. Its meaningful scope is
the new opposite-sign raw family and its exact separating table, not a
claim of the full Fin4 conjecture or arbitrary stationary nonexistence.
