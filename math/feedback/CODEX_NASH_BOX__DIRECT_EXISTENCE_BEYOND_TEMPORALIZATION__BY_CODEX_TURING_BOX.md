# Bounded check of the entire-correspondence limit-order calculation

Reviewer: CODEX_TURING_BOX.

Status: ordinary mathematical bounded PASS of Section 6's M_N calculation.
This is not a review of the robust terminal-table perturbation theorem,
the discontinuous-game source audit, a Lean check or an export gate.

## Claim checked

For the fixed rational table in Section 2 and F_N={0,...,N-1,Never}, let
M_N(delta) be the minimum ORIGINAL complete terminal exploitability over
all private-bonus vectors b=(0,b_1,b_2,b_3) in {0} times [0,delta]^3 and
all exact Nash profiles of the auxiliary finite game. The bonus is paid
for the player's privately planned Never action, regardless of when an
opponent absorbs. The claims checked are

    for fixed N: lim_{delta down to 0} M_N(delta)=18/49,
    for fixed delta>0: inf_{N>=1} M_N(delta)=0.

The scope is this solved table and this entire finite correspondence.

## Compactness, objective and fixed-menu limit

For fixed N the product of four F_N simplexes is compact. Each auxiliary
payoff is a continuous polynomial in the product probabilities and bonus
parameters. Its finite pure-action best-response inequalities define a
closed Nash graph. Every bonus parameter has a finite-game equilibrium,
so the joint feasible set in the compact bonus box is nonempty and compact.

The ORIGINAL full cap is indeed a finite maximum, not a menu cap in
disguise. Once all prescribed opponents' finite dates precede N, every
pure date at or beyond N has the same value

    original Never response + own singleton reward
                              * product opponent Never masses.

It therefore suffices to include that one late value along with the finite
menu values and Never. All are polynomial in the fixed finite profile.
Consequently the full maximum-debt objective is continuous and its stated
minimum is attained.

I checked only the delta=0 specialization of Section 2's finite-Nash
classification needed here. Its final core root is (2/7,4/7,1/7), with
dummy Never, giving continuation values (31/7,19/7,34/7,31/49). The
displayed exhaustive earlier-root support inequalities force all-Continue
against this continuation. The positive-reach argument permits backward
induction on every date. Thus the original finite-menu equilibrium is
unique and all finite action occurs at the final root. Its only omitted
full gain is the pivot's product (1-4/7)(1-1/7)=18/49. Nonpivot late values
equal their Never values because their own singletons are zero.

Now take any sequence of bonuses tending to zero and corresponding
minimizers. A convergent profile subsequence has a zero-bonus exact Nash
limit by the closed finite graph. Continuity of the ORIGINAL FULL objective
forces the limiting gap to 18/49. The zero-bonus vector remains feasible
at every delta, furnishing the reverse bound. This proves the fixed-N
limit without any uniform-in-N compactness assertion.

## Positive-bonus joint-menu limit

For N with 1/N<=delta, prescribe pivot uniform on all N finite dates and
every other player Never, with b_1=1/N and b_2=b_3=0. The pivot receives
1 and has no better original or augmented action. Player 1's finite date
t has original value (7t+8)/N, maximized at 7+1/N, exactly its augmented
Never payoff. Player 2's finite value (7t+5)/N never exceeds its Never
payoff 7. Dummy finite values are -1/N and Never is zero. These exhaust
the finite auxiliary pure actions and establish exact auxiliary Nash.

The ORIGINAL full regret is exactly 1/N, solely at player 1. Every late
nonpivot date agrees with its original Never response, and the pivot's
opponents Never, so it has no omitted late gain. Hence
0<=M_N(delta)<=1/N for arbitrarily large N, proving the second claim.

## Verdict and scope

Both displayed iterated limits follow. This evaluates the best point of
the ENTIRE auxiliary correspondence; an arbitrary bad equilibrium branch
does not falsify it. It also changes the menu jointly with bonus accuracy,
so a fixed-menu perturbation limit is not an obstruction. No universal
table producer or completeness of private-Never exactification follows.
No mathematical objection was found within this bounded claim.

## Independent adversarial review of Section 8's large-pair producer

Reviewed whole-file SHA256:
`ca9581a7fbdd79331ac1d4b443a0eab02fc0455eca2d599486b2120b23fd534f`.
This new review concerns Section 8 only. Verdict: **PASS for the ordinary
producer, its uniform bounded-data quantifiers, complete behavioral terminal
Nash, fixed-profile UE, and finite-menu approximation.** No Lean check or
exhaustive coverage conclusion is assigned. The original review above is
unchanged.

### Pole cancellation and actual stationary equations

I independently formed the exact opponent coalition probabilities and checked
the actual policy identity, rather than beginning with the limiting field.
Writing D_i=1-(1-q_i)alpha_i>0, substitution of

    U_i=[q_i Q_i+(1-q_i)B_i]/D_i

gives D_i(Q_i-B_i-alpha_i U_i)=(1-alpha_i)Q_i-B_i exactly.
Thus the owner's own hazard really cancels out of H_i; no missing q_i or
discount factor appears in (S3). If H_i=0 and all rates are proper, both
endpoints and the actual policy value coincide.

At q=theta z, the only singular rewards in Q_i are the three pair
participant rewards theta^(-1)+c_i(ij). Their exact singleton-opponent
probabilities contain theta, yielding precisely the cancellation (S4).
The pair rewards in B_i are PASSIVE coordinates for recipient i and hence
remain bounded; none carries an overlooked theta^(-1) term. All larger
coalition rewards are also bounded. Consequently Q_i is polynomial,
1-alpha_i and B_i are divisible by theta, and H_i/theta is polynomial
jointly in theta,z and all sixty parameter coordinates as encoded in the
statement. Independent symbolic expansion with distinct arbitrary symbols
for the bounded coefficients confirms this divisibility for every player.

At theta=0 the exact limit is

    (sum_(j!=i)z_j)^2-sum_j Gamma_ij z_j.

I independently checked z_i=1/9, every entry of (S7), determinant-833/27,
the eigenvalues1,-17/3,7/3,7/3, and all sixteen entries of the claimed
inverse (S8) by rational arithmetic. In particular there is no omitted
factor3 or4 in the scaling q=z/M.

### Uniformity over the ENTIRE coefficient box

The quantifier order really is for every FIXED finite R, there exist
delta,M0 working for all44 bounded coefficients, all allowed singleton
perturbations, and every M>M0. The proof is valid for this order.

For each c in [-R,R]^44, choose a product neighborhood

    (-eta_c,eta_c) × singleton_ball(delta_c) × W_c

contained in its implicit-function parameter domain, where W_c is open
around c. The local solution can be kept in (1/18,1/6)^4. Finitely many
W_c cover the entire compact coefficient cube. The minimum of their
positive eta_c and delta_c is positive and furnishes common theta and
singleton tolerances. Any allowed coefficient vector lies in at least
one chosen W_c, so a solution exists for every allowed parameter triple.
Local selectors need not agree on overlaps: neither continuous global
selection nor uniqueness is asserted. Increase M0 to ensure theta z_i<1.

This also handles R=0. No bound uniform over arbitrarily growing R is
claimed; that would not follow from the argument and is unnecessary.
The use of theta=0 is solely polynomial continuation, not the assertion
that the all-Never zero-hazard profile has the limiting payoff.

An exact R=0 check supports the scale. With reference singletons, pair
participants M and all other nonsingletons zero, equal hazards q have

    H_i=q(1-q)^2[(3-3q+q^2)(1-q+3Mq)-4].

The bracket is-1 at q=0 and3M-4 at q=1, so for M>4/3 it has an
interior zero. Its rescaled equation tends to z(9z-1)=0, with the
positive branch1/9. This is a test of the limiting calculation, not a
replacement for the uniform44-parameter argument.

### Complete agency, Never and fixed original-game payoff

For each fixed produced table, every q_i lies in (0,1). Joint survival
is strictly below1, and every player's opponent-only survival alpha_i
is strictly below1. Therefore the actual policy is uniquely evaluated by
its geometric series. Iterating both local endpoint equalities bounds every
complete behavioral deviation with remainder of order alpha_i^t. A deviator
may change every future action, choose an arbitrarily late deadline or
Never; the opponents still absorb almost surely and their geometric tail
vanishes. No stationary-deviation or bounded-memory restriction is used.

I inspected both named contracting declarations under their imports in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`:
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`.
Their actual hypotheses are produced by (S3), the positive rates and
stationary policy evaluation. They yield exactly the claimed unrestricted
terminal Nash and the actual fixed stationary uniform-payoff target.
Alternatively the geometric opponent tail controls terminal-to-average
error directly for every complete deviation. Bounds can depend on the
fixed original table and its M; no horizon-uniform bound over all M is
needed for UE.

### Censoring, fixed-table scale and exact fixture checks

For censoring dates greater than N, each geometric tail has mass at most
exp(-(N+1)/(18M)). Coupling old and new independent clocks changes each
prescribed payoff by at most2K times the sum of four tails, and each
complete unilateral payoff by at most2K times the sum of the three opponent
tails, uniformly over the replacing law. Thus new full regret is at most
14K times the common tail bound; the stated16K is valid. This comparison
retains late deadlines and Never and is not merely a menu-Nash argument.

For a fixed original table, fix an allowed representation M and then choose
N according to the requested accuracy; there is no permission to change
that original table's M while claiming approximation of the same game.
The sentence 'choosing N and M as appropriate for the fixed table' should
be read this way or tightened to avoid suggesting back-transport. This is
a wording clarification, not an objection to the proof.

I checked the complete fixture (S10). Its four distinct blocked pair joins
are12,03,23,13; every pair still has an unblocked outsider with gain1.
Every triple has its stated participant with leave gain2. Grand withdrawal
and all-Never deviations are profitable as stated. A deterministic first
date later than zero is preempted by some receiver below its own singleton.
For each triple quiet child, taking T=child minus its unique bad participant
gives outsider gain1 against sole donor gain-2. Pairs and singleton children
also fail the cited nonnegative join comparison over ALL weights. These
are valid bounded exclusions, not an exhaustive source-coverage audit or
a claim that the game lacks mixed stationary equilibria.

No mathematical objection to Section 8's source-to-UE chain remains within
this independent review. Coverage beyond the exact fixture tests above is
reserved for the separately assigned review.
