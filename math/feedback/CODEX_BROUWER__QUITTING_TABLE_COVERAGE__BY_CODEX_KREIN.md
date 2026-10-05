# Independent review of complete Klein-four coverage

Reviewer: CODEX_KREIN. Ordinary mathematical review, not a Lean build.
Scope: the frozen section **Complete Klein-four coverage: frozen candidate
for independent review** of
`../notes/CODEX_BROUWER__QUITTING_TABLE_COVERAGE.md`, together with its
referenced common-hazard polynomial and reward-coordinate definitions.
No other review was read before this assessment.

Current scope: the proof remains mathematically valid, but the entire
existence class is already supplied by implemented criteria, including
the subgroup response quotient in the formerly proposed new branch.
The retained mathematical packet is now
`../notes/CODEX_BROUWER__KLEIN_FOUR_EQUIVARIANT_QUITTING_GAMES.md`.
This review does not support export as new existence coverage.

## Verdict

The claimed uniform-equilibrium existence theorem for every finite real
Klein-four-equivariant quitting table is proved by the displayed argument.
I found no mathematical gap or counterexample. In particular, the triangle
construction gives the four INDIVIDUAL Nash conditions, and the response
argument covers arbitrary complete behavioral deviations. This review does
not assert Lean verification, external priority, or existence outside the
stated equivariant class.

## Exact claim and reduction checked

The hypothesis is invariance under simultaneous translation of the player
and the quitting coalition by every element of (Z/2Z)^2. All-Never pays
zero. The output is one fixed uniform-payoff target, with profiles allowed
to depend on accuracy and without shared randomization.

Translation makes all own singletons equal to s. For s≤0 the all-Never
profile is exact Nash for both terminal and finite-average payoffs: a lone
deviator can receive only s or zero. For s>0 division of ALL rewards by s
is legitimate, including signed nonsingleton rewards and the zero Never
value. No invalid additive normalization is used.

For normalized singletons, D=Σa_t−3 splits the proposed cases exhaustively.
The data a_t,p_t,f_t,h_t,h0,g are the fourteen free coordinates after fixing
the common own singleton to one. Pair and triple rewards are not being
silently reconstructed from singleton symmetry.

## Independent check of the triangular producer

Fix a_t<1 with D>0. In the paired row (x,x,y,y), translation by t preserves
the row and swaps the two members of each pair. Thus their individual
face numerators coincide. Translation by a complementary group element
swaps the two pairs and gives exactly F1(x,y)=F0(y,x). This uses the full
reward equivariance, not a grouped-player payoff or a correlated action.

With A=1−a_t>0 and B=a_u+a_v−2, one has B−A=D>0. The individual deleted
opponent law contains one same-pair hazard x and two opposite-pair hazards
y, so expansion gives

    F0(x,y)=Ax−By+O((x+y)^2),
    F1(x,y)=Ay−Bx+O((x+y)^2).

In 0≤y≤x, the second linear term is at most −D*x. Since the field is a
fixed polynomial, a sufficiently small common delta gives F1<0 everywhere
in the punctured cutoff triangle, as well as F0(x,0)>0. Arbitrarily large
or badly signed nonsingleton coefficients merely shrink delta; they do
not invalidate these strict signs.

For metric projection onto T={0≤y≤x≤1}, the fixed-point convention is
correct:

    z=P_T(z+v)  iff  v·(w−z)≤0 for every w∈T.

The perturbation adds phi(x)≥0 only to coordinate 0. I checked every
cutoff face separately:

- At the origin, a positive horizontal direction contradicts the VI.
- At 0<y<x≤delta, both vertical signs are feasible, forcing F1=0.
- At y=0 and 0<x≤delta, both horizontal signs are feasible, forcing
  F0+phi=0 although it is positive.
- On x=y>0, if phi>0 the feasible direction (1,−1) has strictly positive
  field product. If phi=0, the feasible direction (−1,−1) has strictly
  positive field product because both field coordinates are negative.

All directions can be scaled to stay in T because delta<1. The line
x=delta is not an extra triangle face, and the same reasoning excludes
it even when phi vanishes there. Hence the selected point satisfies
x>delta, where the field is literally the original reward-table field.

At the remaining faces, ordinary feasible coordinate directions yield
the stated lower/upper complementarity signs. The only places where the
triangle does not provide both individual directions are its diagonal:

- At 0<x=y<1, both diagonal directions give F0+F1=0, and exact symmetry
  gives F0=F1, hence both vanish.
- At (1,1), the inward diagonal gives F0+F1≥0, and symmetry gives each
  coordinate nonnegative.

At (1,0), the independent inward directions give F0≥0 and F1≤0.
Thus every individual hazard satisfies the correct cube condition. The
proof does not infer individual incentives from an equilibrium of teams.
Since both members of the x-pair have x>delta, every player has a
positive-hazard opponent, even if y=0 or x=1.

## Complete deviations and the fixed target

For one individual, write alpha for its opponents' one-date Continue
probability, Q for its Quit endpoint, A for its unconditional absorbing
Continue reward, and b=1−(1−c)alpha. The actual stationary value is

    U=[cQ+(1−c)A]/b.

Direct multiplication verifies

    Q−(A+alpha*U)=[(1−alpha)Q−A]/b=F/b.

Therefore the selected complementarity signs imply BOTH pure-action
payoffs at continuation U are at most U. An arbitrary behavioral deviator
still faces the same independent opponents. Iterating these inequalities
leaves a bounded remainder multiplied by alpha^N, which vanishes because
alpha<1. This proves the full terminal cap, not only stationary optimality.

The same argument controls the terminal-to-finite-average bridge uniformly
over deviations. If |r|≤M and p_i=1−alpha_i>0, unchanged opponents give
an expected absorption-date bound at most 1/p_i up to the harmless indexing
convention. The difference between terminal and H-date average payoff is
bounded by 2M/(H*p_i). One fixed selected profile therefore works for every
sufficiently large H at its single actual payoff U.

The other branches also retain their fixed targets:

- D<0: the common-hazard face polynomial has L(0)=−D>0. If g<h0,
  L(1)=g−h0<0 supplies an interior exact root; otherwise the full sure
  coalition is exact Nash. At sure absorption, all later deviations equal
  the corresponding withdrawal payoff h0, so g≥h0 is sufficient.
- D=0: Q(q)→1 and A(q)/(1−alpha(q))→Σa_t/3=1. The full pure-time cap
  is the maximum of those two endpoints, so both prescribed values and
  all full regrets converge to the fixed all-ones target. Choosing q first
  and the horizon threshold second is permitted; no uniform-in-q duration
  bound is required.
- D>0 and every a_t≥1: with one rare solo owner, the prescribed terminal
  vector is exactly its singleton reward at every q. An outsider's
  Quit-now payoff is 1+q(p−1); its Never payoff is a≥1, so full gain is
  at most q*max(p−1,0). The owner has no positive-hazard opponent, but
  this is handled separately: every finite-average unilateral payoff is
  at most one, while its prescribed average tends to one. The other
  players retain the owner's geometric absorption bound.

Scaling back multiplies the bounds and target by the same positive s.
The target never depends on requested accuracy.

## Attempted falsifiers and precise source boundary

I tested the likely failure points: reversing the projection sign;
counting team deviations instead of individual deviations; a fixed point
on the cutoff seam; escape through either diagonal endpoint; y=0 with a
noncontracting deviator; zero singleton scale; negative reward entries;
the rare owner's lack of opponent absorption; and a horizon bound that
would need to be uniform as q→0. Each is explicitly resolved above. No
additional sign condition on nonsingleton rewards is needed.

The following source declarations were inspected, without rebuilding:

- `quittingFaceNumerator`, `continuous_quittingFaceNumerator`, and
  `quittingFaceNumerator_eq_gainValue`, in
  `UniformEquilibrium/Quitting/Stationary/FaceNumerator.lean`;
- `heterogeneousFaceNumerator_update_self` and
  `heterogeneousFaceNumerator_congr_off_self`, in
  `UniformEquilibrium/Quitting/Stationary/HeterogeneousConstrainedFaceNash.lean`;
- the target-family definitions and semantic endpoint in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

These support the stated semantics but do not themselves implement the new
triangle producer. The ordinary proof needs only finite polynomial algebra,
Euclidean projection, Brouwer, and geometric absorption. Its genuinely
additional hypothesis is full Klein-four reward equivariance; singleton
symmetry alone does not yield the exact diagonal identity used in the VI.

## Corrected implementation-overlap assessment

The earlier bounded source check missed the stronger subgroup response
quotient. I have now read
`responseInvariant_of_reward_subgroup_automorphisms` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientPlayerOrbits.lean`
and `finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`.

In the positive-surplus branch with a_t<1, translation by t gives two
two-element orbits and actual response invariance on their hazard cube.
With A=1−a_t>0 and B=a_u+a_v−2>A, the quotient singleton matrix is

    [[−A,B],[B,−A]].

Its determinant is A²−B²<0 and its inverse is
[[A,B],[B,A]]/(B²−A²), entrywise positive. The named criterion directly
produces original-game UE from these raw data. It requires no preselected
stationary root, supplied R0 proof, or behavioral witness. Combined with
the existing branches already audited for the other parameter regions,
this covers the full Klein-four class.

The independent triangle proof and the full-behavior checks above remain
valid ordinary mathematics. Their correct status is an alternative direct
proof within an implemented existence class. My mathematical PASS is
unchanged; any earlier implication of new existence-class coverage is
withdrawn. No Lean build was performed for this source audit.

## Independent review: a solo-0 bridge pays a positive outsider cap

### Final standalone artifact check

PASS applies to the complete standalone file
`../exports/REPEATED_SOLO_EXIT_WITH_POSITIVE_OUTSIDER_BUFFER.md`, SHA256
`53dbfbccdf06da788bf4f694ff73d48bb63ce1d3843a00a240c2397870f02937`.
I read all 495 lines and verified the exact hash. The assembly retains
the reviewed raw theorem, effective-premium selector including alpha=0,
all four actual phase vectors, all three refinements and complete
behavioral/fixed-target horizon argument. The now-expanded original-table
degree exits and passive-inverse thresholds are complete and invoke
exactly the tracked hypotheses already checked. The full fixture,
thirteen partition witnesses and final nonlinear partition failure,
and all proper-child tests remain intact. In particular, the approximate
123 child proof retains its fixed positive outside gap and vanishing
child debts; its intrinsic fixed-weight statement correctly quantifies
“for every proper child there exists an omitted player,” not every
omitted player. The raw-predicate to all-R UE handoff assumes no new
strategic input. No math-folder dependency, unresolved assembly issue,
or inflated all-source coverage claim was found. This is the requested
artifact/delta check, not a further independent proof review or Lean build.

VERDICT: PASS, with no unresolved mathematical objection. The scope is
the complete final section with that title, including its all-R source
exits and bounded source audit, in
`../notes/CODEX_BROUWER__QUITTING_TABLE_COVERAGE.md`, at whole-note SHA256
`1d54918d7240fd19ad4d510aefa90400178598f548b42a5acbc7354cec3faab0`.
I did not read CODEX_MORSE's review. This is ordinary independent
mathematical and static source review, not a Lean build. It does not
review the preceding unique-root obstruction as a dependency or assert
that these raw classes exhaust the remaining games.

### The raw selector and bridge identity

The raw restrictions are h_i,a,b,c,eta>0, abc>1, u≤1, v<1, and
one possibly positive outsider cap lambda<h3*eta/h1, with every other
listed cap nonpositive and every unused coordinate arbitrary. The
auxiliary theta can indeed be chosen with
0<theta<eta/h1 and lambda≤h3*theta. Thus eta_eff>0; no strategic
witness is hidden in theta.

I independently checked the cleared quadratic in (B2), including both
coefficient signs, endpoint signs, and the case alpha=0. Its positive
linear coefficient follows from aE−y≥1/b; at the cap, w=0 or z=1
makes the unmultiplied balance strictly positive. The first positive
crossing is the only admissible root. The rationalized root expression
extends continuously through alpha=0 and both y endpoints. Its small-y
ratios are 1/nu1, nu2/nu1, nu3/nu1. The pivot selector therefore has
exact endpoints Rlow and Rtop. The displayed positive formula for
nu3*(Rtop−Rlow) also checks at u=1, since v<1 supplies strictness.

The extra stage is not a second-root assumption. Put k=K/(1+theta).
Then 1−rho=(1+k)/(1+K). Therefore its player-1 Bellman equation is

    (1−rho)*eta*x−rho*h1
      =(eta−theta*h1)k/(1+K)
      =eta_eff*K/(1+K).

The stated t2 similarly gives d2=w/(1−w), and t3 gives d3=0.
These are exact identities in the original reward table, not an
equivalence between different games. At A the effective balance gives
V_B1=K(h1+eta_eff)=k(h1+eta). The two outsider averages reduce to
(b*y−h2*k)/(1+k) and h3*theta*x, respectively, exactly the displayed
t2 and t3. All supported endpoints are indifferent, and all pure
Continue comparisons are exact.

The pivot floors are valid even when u=1: V_B0=(1−u*y)/(1−y)≥1,
V_C0=1+(R−1)w>1 because R>Rlow>1, and d0=t0=1. Every other
coordinate is nonnegative. At A, outsider 2 has endpoint at most zero.
Outsider 3 has endpoint at most lambda*x*(1−y), which is at most
h3*theta*x=t3, including equality in the raw cap. This is an actual
positive continuation buffer, with no discarded simultaneous event.

### All deviations, original-game exits, and fixed target

Refining all three solo blocks is necessary, including the pivot bridge.
Their exact endpoint vectors are unchanged, intermediate values are
convex interpolants, and every singleton floor survives. The immediate
Quit error is precisely bounded by Cjoin times the largest microhazard.
One constant added to every continuation value is a Bellman
supersolution; the proof does not sum errors over periods. Each player's
opponents retain positive hazard in every period, including when player
0 removes BOTH its joint and bridge hazards. Consequently the geometric
survival bound is uniform over complete behavioral deviations.

The fixed terminal target t is independent of the subdivision. Coupling
with the opponents' first scheduled Quit proves the expected absorption
time bound and the stated uniform finite-horizon inequalities. The
refinement proof matches the exact Continue/one-Quit-error fields of
`QuittingInfinitePathQuitErrorCertificate` and the declaration
`quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue`
in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`,
which I reread during this review. The target is fixed before accuracy.

The lower singleton-degree argument does not depend on the bridge or
joint rewards. R=Rlow has the nonzero homogeneous vector (1,nu),
and R<Rlow has the same two regular complementarity roots of determinant
signs + and −. The upper inverse thresholds obey T2≥T3>T1 under
u≤1 and v<1, so all three literal weights are nonnegative at and
above Rtop. I reread the exact named singleton-degree and raw passive-
inverse declarations during this session; none adds a nonsingleton
condition. Thus no endpoint or portion of the real R axis is omitted.

### Exact adversarial tests and bounded source comparison

Exact rational enumeration reproduces all sixteen policy identities and
all sixteen Continue identities in the author's full-core fixture. It
also reproduces both positive unrefined gains, 2/15 for player 2 at C
and 1/66 for player 3 at D. Thus its conclusion genuinely uses the
claimed diffusion rather than an unnoticed coarse Nash assertion.

As a separate test, set a=b=c=2, h=(1,5/6,1), u=1, v=0,
eta=3, theta=lambda=1. Then eta_eff=1 and

    nu=(19/21,20/21,41/42),
    Rlow=81/41, Rtop=3,
    y=1/4, K=1/9, z=13/54, w=11/41,
    x=1/19, rho=1/20, R=24/11.

The quadratic has alpha=0, beta=63/8, gamma=−7/8. The values are

    t=(1,3/19,49/114,1/19),
    V_B=(1,2/9,0,13/27),
    V_C=(54/41,25/41,0,0),
    d=(1,1/10,11/30,0).

Take r3(03)=1 and every other cap coordinate zero, and set all remaining
unspecified coordinates to 37. Exact rational enumeration again gives
all sixteen policy/Continue identities. At A the endpoint pairs are
(1,1), (3/19,3/19), (49/114,0), (1/19,3/76). This tests the
zero leading coefficient, u=1 floor equality, binding positive raw cap,
unequal h_i, and genuinely arbitrary unused premiums simultaneously.

For the author's completion I independently enumerated the five traps
03,23,013,023,0123 and all fifteen pure-coalition toggle improvements.
Their only possible common player is 3, whose leave inequality fails
at 03. The full singleton determinant 497/92, inverse entry −744/497,
all four triple inverses, and passive row (186/161,−297/644,25/322)
match. Enumeration of all fifteen partitions leaves only the discrete
partition and 0|123 at first order; the stated three actual residual
polynomials exclude the latter. These are bounded failures of the
precise named criteria, not an exhaustive producer classification.

I checked all thirteen exact proper-child profiles, including 023's
endpoint pairs (1,1), (−245/347,92/1735), (1/5,1/5), and the omitted
player's Continue value −1367/1735. For the fourteenth child, 123,
the former coarse cycle is indeed not exact Nash after introducing
the 23 premiums. The refined cycle instead has full regret at most
alpha_n/2, joint Never zero, and the quiet pivot's fixed gain 297/644.
This is enough: I reread
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
Its weights are fixed by the certificate while the inequality quantifies
over every child profile. Letting n tend to infinity contradicts the
fixed positive outside gain for every proposed finite weight vector.
The approximate-child witness is logically valid and does not claim an
exact equilibrium which the changed table no longer has.

Finally, the class is not subsumed by the reviewed switched-pair class:
its full-core fixture has both relevant passive singleton rewards below
the pivot singleton, whereas that class requires both above or equal.
No relabeling of the nonpivot cycle repairs this, since only player 0
has a positive own singleton. This comparison also applies to the new
two-buffer extension with the same U,V≥1 requirement. The two mechanisms
therefore cover different stated raw regions, not an alleged partition
of all normalized tables.

## Independent review: weighted-floor return without a protected player

Verdict: **PASS**, no unresolved mathematical objection. Scope is
“Weighted-floor return without a protected player” through EOF of
the author's notebook, including the added precise comparison with
implemented weighted-premium producers, at exact whole-file SHA256
`2c97a149d66c039cfa58cb9779fd4dd532381a9f4a39be80eabcfcf96e41f6bb`.
No other independent review was read before this verdict. This is
ordinary mathematics and a bounded static source check, not a Lean build.

The checked output is a finite weighted raw reward criterion, not
just the preceding convex-return interface. For each actual positive-
premium trap A it requires one strictly positive-on-A weight vector,
zero outside A, satisfying global weighted forced-Quit floors (W3)
and strict weighted leave comparisons (W4). These produce both
convex-return premises, exclude C¹ full exact-root drift, and give
Fin4 UE when own singletons are nonnegative. Weak leave is only a
strategic reward-closure conclusion. The signed open fixture is part
of this review.

### The convex-minimum argument

The set D=R∩{some coordinate at or below its singleton} is compact
and contains the singleton lower boundary L, since R contains U.
The two return premises exclude a below-singleton attained minimum,
so the minimum lies in L. The existing singleton-face drift then
rules out a single binding coordinate and gives exactly the stated
signs: nonnegative at binding coordinates, zero at nonbinding interior
coordinates, and nonpositive at upper faces.

I checked the extra normal-cone assertion (W1) independently. If z∈R
has a binding coordinate j with z_j≤x_j=s_j, the entire segment
from x to z remains in D. Its one-sided derivative is therefore
nonnegative. If no such j exists, all binding displacements are
positive, the interior coefficients vanish, and upper-face coefficients
and displacements have the same nonpositive sign. Thus again
g·(z−x)≥0. Convexity and minimum on D, not just on L, are the
essential hypotheses. No individually protected coordinate is required.

Every exact root at the actual minimum has zero absorption by the
return premises. Lowering any binding coordinate forces every root
to absorb. Finite hazard-cube compactness and closed polynomial Nash
inequalities then give a_n→0 for arbitrary chosen roots. Their
successors belong to R even though their sources need not. The
universal signed bound Q_k≥s_k−2M a_n and displacement bound
give epsilon_n≤(3M+B)a_n and the displayed
‖w_n−x‖∞≤(4M+2B)a_n. Both Taylor errors are o(a_n), while
the linear source term and the normal-cone successor term have the
required signs. Unit charge contradicts their difference. There is
no successor singleton floor or continuous root selection hidden here.

### The two weighted identities and sure hazards

For (W6), averaging r_i(S∪{i}) over the FULL coalition law is
exactly player i's forced-Quit expectation: its own independent action
can be summed out. This remains true at zero and sure hazards.
Therefore (W3), Nash w_i≥Q_i and nonnegative weights give every
weighted successor floor at every boxed source.

For (W7), multiplication by (1−q_i) replaces each opponent-law
probability at coalition T not containing i by the full coalition
probability μ(T). Summing over active i leaves exactly the coefficient
L_A(T) at each nonempty proper T⊂A and the coefficient
sum_i lambda_i(s_i−v_i) at the empty coalition. Coalition A has
zero coefficient. This derives the exact identity without dividing
by hazards or suppressing larger simultaneous coalitions.

The left side is nonnegative at an exact root on its active support.
If some active j is not sure, pick a different active k; the event
that k quits and j continues has probability q_k(1−q_j)>0 and
is contained in the nonempty proper-coalition event. This proves the
strict contribution required by (W4), even if other active hazards
are sure and the empty-coalition probability is zero.

If all active hazards are sure, (W7) alone really is silent. The
separate argument correctly uses T=A\{i}, nonempty since no
singleton is a trap, to obtain
lambda_i[r_i(A)−r_i(A\{i})]<0. Positivity of lambda_i gives
a profitable withdrawal for every participant. Thus this root is
not Nash either. No all-sure face is lost in the weighted identity.

The remaining support is not a trap, hence an active player has all
within-support participant rewards at most its singleton. Supported
Quit equality gives the needed low successor coordinate. This completes
both return premises from finite raw inequalities.

### An exact test of the global coalition quantifier in (W3)

The requirement that (W3) hold for EVERY S⊆I, not only S⊆A,
is essential. Starting from the printed four-player fixture, change
only

    r_0(03)=−1,       r_1(13)=−1,       r_2(23)=−1.

The only trap remains A=012. Every (W3) check on S⊆A and every
(W4) comparison remains unchanged and strict, with lambda=(1,1,1,0).
But at source v=(1/10,1/10,1/10,0), which satisfies the weighted
floor, take q=(0,0,0,1). Each core player gets −9/10 by Continue
and −1 by Quit. Player 3 gets singleton 1 by Quit and source 0
by Continue. This is an exact absorbing Nash root, with successor

    w=(−9/10,−9/10,−9/10,1).

Its weighted centered core sum is −3, outside R. In fact
W_A({3})=−33/10. Thus replacing global (W3) by core-only tests
would break the claimed invariant even at a source already in R.
This is a counterexample to that weakened premise, not an objection
to the actual theorem and not a quitting-game nonexistence example.

### Exact signed fixture and strict openness

I independently enumerated the complete fifteen-row table. The only
trap is 012 and P_max is empty: every player has a strictly negative
participant premium somewhere. With lambda=(1,1,1,0), the weighted
floor values are 1/2 on core singletons, 3/5 on core pairs, 3/10
on 012, 7 on 3 and 03, and 6 on the other coalitions containing
3. The leave values are −1/2 on core singletons and −9/10 on
core pairs. All match exactly. I also checked (W6) and the active-
support specialization of (W7) as exact polynomial identities.

All relevant nonsingleton premium signs, own-singleton positivity,
nonempty weighted floors and leave inequalities have strict margins.
The finite list therefore persists in one full sixty-coordinate
neighborhood with the same trap and the same weights. The singleton
tautology W_A(empty)=0 is an identity, not an openness assumption.
This is a genuine open raw-data class. No IFT strategy witness or
generic equilibrium-openness assertion enters the argument.

The singleton matrix, determinant 7, the stated permutation of the
earlier degree-one matrix, and the exact response values
t+3t²,t+2t²,t+2t² check. Every listed pure toggle gain is correct.
All thirteen first-date child profiles have nonpositive child join
gains, and their sole owners cannot improve by delaying beyond their
positive singleton. The omitted gains are 5/2 except at child3,
where the gain is 4.

For child012 the stated solo order 2,0,1 has the three centered
Bellman vectors (1,0,0),(0,1,0),(0,0,1). Refinement retains actual
singleton floors and exact Continue, so the common-error bound
(3/2)alpha_n covers complete behavioral deviations. Opponent tails
contract and Never vanishes. The quiet outsider value is 6/7; its
first-microstage Quit value is 1−alpha_n. The limiting positive
gain 1/7 contradicts every fixed finite weighted-child-debt-plus-
Never bound. This does not assert that the coarse child profile is
exact Nash or that every selected-child method fails.

### Implemented supportwise balance is a different criterion

I read directly
`IsSupportwiseQuittingPremiumWeightCertificate` and
`HasSupportwiseQuittingPremiumBalanceAt` in
`UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumBalanceAt.lean`,
`IsSupportwiseBalancedQuittingPremiumTable` and
`weighted_quittingRootQuitPremium_sum_nonpos_of_certificate` in
`UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremium.lean`,
and `exists_uniformEquilibriumPayoff_of_supportwiseBalance` in
`UniformEquilibrium/Quitting/Classification/Existence/SupportwisePremiumUniformPayoff.lean`.

The old certificate has normalized nonnegative support weights and
requires a NONPOSITIVE weighted participant-premium sum on every
contained coalition. On support and coalition 012, all three premiums
in the new fixture are 1/10. Thus any normalized old weights give
exactly 1/10>0, even when some weights vanish. The implemented
supportwise condition fails, robustly on the same strict-sign region.

The definition `HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`
also fails directly at q=(1,1,1,0): all active Quit values equal
1/5, strictly above the singletons 1/10. This product law is not Nash;
the new proof uses its Nash premise to exclude just such supports.
There is no contradiction with a product-low theorem quantified over
ALL product laws. These are two different weighted identities and
two different raw classes, not renamed versions of one producer.

The new weighted class and protected-set class are incomparable.
The fixture has no protected player at all. Conversely the author's
two-player example with r(0)=(0,0), r(1)=(2,0), r(01)=(1,1)
has a protected strict leaver 0 but cannot satisfy (W4) at T={0},
since lambda_1(1−0)>0 for every allowed positive weight. Its
protected-set certificate does not transfer to the weighted raw test.
The convex analytic lemma does include the protected-set argument as
R=R_P; that does not imply raw-class subsumption.

### Actual Fin4 consumer and weak leave

The same exact declarations reread in my protected-set audit supply
the face drift, finite Nash existence, signed displacement bound,
normality from nonnegative own singletons, rational polynomial
obstruction on the original table, its full-root restriction, and
uniform-payoff reward closure. In particular the relevant files are
`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`,
`UniformEquilibrium/Quitting/Root/NashExistence.lean`,
`UniformEquilibrium/Quitting/Root/BoundedSuccessorDisplacement.lean`,
`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`,
`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`,
`UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`,
and `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.
Their hypotheses have not changed in this application. All-zero
singletons are handled by all Never; otherwise the positive singleton
and normality feed the actual polynomial producer. No unproduced
equilibrium selector or restricted response class is an input.

Increasing every passive reward by delta leaves (W3), participant
premiums, singletons and traps unchanged. For each proper T⊂A it
decreases L_A(T) by delta times the strictly positive weight sum on
A\T. Thus weak leave becomes strict with the same weights; reward
closure selects one fixed target for the original table. This proves
only the stated weak strategic conclusion. No mathematical repair is
requested before independent assembly work.

### Final weighted-floor artifact and delta check

**Assembly PASS** for
`../exports/WEIGHTED_FLOOR_RETURN_UNIFORM_EQUILIBRIUM.md`,
604 lines, exact final SHA256
`98ffaf81955437f97d3d3d8b1315c0e289be410110fed77ba3f1a72dcf2c1654`.
I read the complete assembly and checked the subsequent one-word
removal of “stronger” before “product-low.” The latter is correct:
the tracked supportwise condition implies product-low, not conversely.
No theorem or numerical content changed in that last delta.

The artifact preserves the reviewed raw criterion, global W_A tests,
strict analytic result, weak Fin4 consumer, and full signed open region.
The expanded singleton-face probe is exact and boxed, including at
upper faces; its source need not lie in R because the potential
property concerns every boxed root. The convex minimum proof retains
both normal-cone cases, the closed Nash graph, the signed absorption
charge, and the separate all-sure support argument. No missing
protected-player floor has entered the assembly.

The three exact-root regressions also check directly. In addition to
the global-coalition falsifier already verified above, the source
(-29/10,1,13/5,0) and hazards (1/2,0,1/2,0) give precisely the
four displayed endpoint pairs and a successor violating an individual
floor while respecting R. The source (1/30,1/30,1/30,1) and
hazards (1/10,1/10,1/10,0) give core endpoints 73/500 and
player-3 endpoints 729/1000,1109/1000, so the outside-source
successor really lies strictly above every singleton. Neither is
misrepresented as a forbidden-potential minimum.

The complete source/partition/child tables agree with the exact audit;
the handoff names the actual new raw producer and the existing semantic
consumer without claiming implementation. There are no mathematical
dependencies on conference notes or exports. No correction or further
full proof audit is requested.

## Independent review: boxed Nash charge on a triple

**PASS**, ordinary mathematics, not Lean checked. Scope is the complete
EOF section “The complement of weighted floors: a boxed Nash charge on
a triple,” (N1)–(N8), including its strict-slack constants and outside-box
regression. Whole-note SHA256 inspected:
`458b24978e61c3ba97a6bd5c410cbc619a526a9e2d049fcc239c13c166d63d2d`.
I derived this audit without reading another review. It does not cover
any subsequent higher-cardinality extension.

### All support cases and the quantitative contradiction

The raw inputs are precisely a finite Fin4 reward table with nonnegative
own singletons, all premium traps of cardinality three, and four positive
real bounds satisfying (N2)–(N6). They contain no root, strategy, source,
or favorable continuation selector. Two different triple traps would
have full union, which is again a trap because each member retains its
original witness; hence there is at most one.

For a nontrap absorbing support the actual supported participant has
all within-support rewards at most its singleton, so its exact successor
coordinate is low. For a trap support, (N4) and (N5) make every nonempty
proper coalition's aggregate-leave coefficient negative. If a hazard is
sure and another is not, the empty-coalition term vanishes and some
proper coalition has positive mass; the aggregate Nash identity is then
impossible. If all are sure, (N5) gives an actual profitable withdrawal
for each participant. Thus neither sure-root case is accidentally lost
when the odds are introduced.

In the remaining interior case, dividing each positive Quit premium by
its opponent Continue probability gives its two pair-premium terms and
one triple-premium term. Summing yields exactly the expression preceding
(N7). Its upper bound is −dU+tau V, so all-high endpoints require
dU<tau V. The elementary identity U²−3V being half the sum of the
three squared odds differences gives V≤U²/3 and U>3d/tau.

Support indifference makes the left side of the aggregate-leave identity
zero. After division by the positive empty-coalition probability, each
singleton coefficient is at least g and each pair coefficient at least
l. Therefore

    sum_A(s_i−v_i) ≥ gU+lV
                    > (g+ld/tau)U
                    > (3d/tau)(g+ld/tau).

The source-box upper bound sum_A s_i+3B is literal. Strict (N6) permits
one M<B<M+2 with the required gap. This proves the asserted return
for every absorbing exact root at every source in that box, not just
roots near a proposed minimum.

### Actual no-potential and UE consumer

The previously audited convex-invariant minimum lemma applies with R
equal to the entire box: successor invariance is ordinary convexity of
the source/terminal payoff mixture, and the boxed return just proved is
its second premise. In particular, the minimum on the union of singleton
sublevels forces zero absorption at every root at the minimum; nearby
root compactness and the signed absorption-scale estimate, rather than
a mere local gain, supply the Taylor contradiction. No individual floor
or nonnegative participant-premium assumption is inserted.

I reread `IsQuittingFullExactRootPotential.mono_box` and
`isQuittingFullExactRootPotential_of_robustPotential` in
`UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`.
The restriction retains the same potential and permits any smaller
bound, not only M+1. I also reread
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`.
For nonnegative singletons, the already checked normality declaration
applies; unless all singletons vanish there is a positive singleton and
failure of UE would produce the actual polynomial on M+2. Its same
smooth restriction to B is excluded above. If every singleton vanishes,
all Never is the direct equilibrium. Thus the conclusion is an original-
table, fixed-target uniform payoff against complete behavioral deviations.

The exact source lemma
`exists_successor_le_singleton_of_exactRoot_nontrap_support` in
`UniformEquilibrium/Quitting/Classification/CommonQuittingPremiumLeaver.lean`
was checked as well: signed nonsingleton rewards are allowed, and no
unwritten floor condition is present.

### Exact raw and boundary tests

Recomputing all fifteen rows of (N1), the only trap is 012. The three
values in each family (N2),(N3),(N4),(N5) are respectively

    −1/2, 1/10, −3/2, −9/10.

The reward bound is 31/10. The original constants give charge 90 against
48/5. The slack constants (2/5,1/5,7/5,4/5) give charge 18, still above
48/5, and make every raw bound strict. The singleton positivity and all
signs defining the trap list are strict. Thus a genuine full-coordinate
neighborhood is covered with fixed auxiliary constants.

The three singleton-product weighted-floor inequalities sum to
−(lambda_0+lambda_1+lambda_2)/2−3lambda_3≥0. Nonnegativity forces
every weight to vanish, so this really excludes every nonzero
nonnegative linear forced-Quit floor, including weights on the outsider.
The product laws used in that exclusion need not be Nash; the new
argument explicitly uses the missing Nash premise. Product-low and
implemented supportwise balance still fail on the all-sure core law,
whose three participant premiums remain 1/10. Every player retains a
negative participant premium, so the protected-set criterion cannot apply.
The singleton matrix and literal quotient falsifier are unchanged by
(N1). The thirteen child singleton profiles remain exact, and the refined
core-child bound changes from (3/2)alpha_n to alpha_n/2 while its outsider
gain stays 1/7−alpha_n. These are bounded comparisons, not exhaustive
exclusion of every existing producer.

I independently evaluated the displayed outside-box root: q=(9/10,
9/10,9/10,0), v=(−863/10,−863/10,−863/10,1) give the stated core
endpoints 17/125 and outsider endpoints 1/1000,1981/1000. It is exact
Nash and all four successor coordinates are above their singleton.
An additional exact test uses odds six, namely q=(6/7,6/7,6/7,0) and
v=(−413/10,−413/10,−413/10,1). Its core endpoints both equal 11/98;
the outsider's Quit and Continue values are 1/343 and 673/343. Again
all successor coordinates are high. Thus removing the bounded-source
quantifier would make the return claim false even on the admitted table.
No repair is requested for the stated boxed theorem.

## Unified boxed-charge theorem: strengthening and final artifact review

**PASS**, both for the new mathematical scope and for the self-contained
artifact `../exports/BOXED_NASH_CHARGES_UNIFORM_EQUILIBRIUM.md`, exact SHA256
`16ffd63e3735ad7b00f99e76efb237cb0cf7fdc6de0ae267161b9da9e2977dde`.
I read the complete artifact without reading another review. This
verdict includes the arbitrary finite m≥3 analytic argument, simultaneous
traps of different sizes, the Fin4 semantic consumer, both complete
fixtures, and the bounded source comparisons. It asserts no Lean check.

### New m≥3 proof and one common source box

The two coefficient families P_A(T) and L_A(T) have distinct roles
and are used with their exact quantifiers. For each trap, summing
the positive active Quit premiums after division by the corresponding
opponent Continue probability yields precisely the P polynomial over
all nonempty proper T. The singleton coefficients cost dU; every
intermediate coefficient is nonpositive; the m−1 coefficients are
bounded by tau and sum to tau E. Thus dU<tau E is correct for any
m≥3, not just a formal replacement of the triple variables.

The symmetric bound E≤U^(m−1)/m^(m−2) is sound. For the relevant
U>0, a maximum at fixed sum has at least m−1 positive coordinates.
For any unequal pair of coordinates, the remaining m−2 coordinates
contain at least m−3 positives, so the coefficient e_(m−3) in
the averaging argument is strictly positive. Averaging strictly raises
E, excluding such a maximum. The all-equal value proves the bound;
the zero-sum case is immediate. Hence U>m(d/tau)^(1/(m−2)).

The separate sure-hazard cases remain essential and correct. With
some but not all active hazards sure, choose a nonsure i. Coalition
A\{i} has positive product probability and a strictly negative L
coefficient. All other L terms are nonpositive and the empty term
vanishes, contradicting supported Nash optimality. With all sure,
the same m−1 coefficient gives an actual profitable withdrawal.

For interior hazards, indifference and the exact aggregate-gap identity
give sum_A(s_i−v_i)≥gU+lE>(g+ld/tau)U>C_A. There are finitely
many traps, so the strict gaps C_A−sum_A s_i−mM permit one common
M<B<M+2. This handles different trap cardinalities and different
auxiliary constants in the SAME raw game. No strategy, root, favorable
annotation, or potential is among the raw inputs. The no-trap case is
also correctly vacuous. Universal low-successor return holds at every
boxed source, including sources outside all singleton-floor regions.

### Same-domain minimum and source restriction

The assembly gives a complete independent minimum proof rather than
referring to the earlier convex-invariant packet. Its collision-adjusted
singleton probe is an exact root: corrections are placed only at
binding coordinates below B, all upper faces remain unshifted, and
the explicit Continue-minus-Quit expression has the required sign.
The two first-order correction terms cancel in the derivative inequality.

Minimization on the full union D of singleton sublevels forces the
minimum onto the lower singleton boundary, rules out a single binding
coordinate by the face drift, and gives nonnegative derivatives at
every binding coordinate. The perturbed source and its successor both
remain in that same D. The signed estimate epsilon≤(3M+B)a then
turns unit absorption drift into the impossible one-sided derivative.
No compactness claim about selected roots or protected coordinate is
needed in this version.

The existing normality and rational-polynomial source theorem apply
to the original Fin4 table when some singleton is positive. The exact
restriction and `IsQuittingFullExactRootPotential.mono_box` retain the
same polynomial on the common smaller B. If all singletons are zero,
all Never is the direct exact equilibrium. The artifact correctly
limits its strategic conclusion to Fin4 even though the analytic
theorem is finite-dimensional in arbitrary cardinality. Its target is
fixed before accuracy, and the cited source consumer has complete
behavioral deviations. No missing strategic hypothesis was found.

### Exact full-core table and fourteen child tests

I recomputed the fifteen-row full-core fixture. The only trap is the
grand coalition. The P coefficients by cardinality are exactly −9/2
at each singleton, −4 at each pair, and 1/10 at each triple. The L
singleton coefficients are −3/2,−13/2,−13/2,−9/2; all pair values
are −8 and all triple values −19/10. M=3. Both charge constants,
348 sqrt(45) and the strict-slack 124 sqrt(20), exceed 13. All stated
strict coefficient and trap margins hold. Raising the three zero own
singletons slightly really preserves the criterion, so the analytic
open-neighborhood and strategic nonnegative-singleton boundary are
properly distinguished.

For all fourteen listed (owner,omitted) pairs I checked that the owner
is in the child, the omitted player is outside it, every other child
player's joining gain is nonpositive, and the omitted joining gain is
exactly 1/2. A sole owner's own singleton is nonnegative; after it
prevents absorption, its opponents remain at Never, so no delayed
behavioral action improves on that singleton. Thus these are exact
FULL terminal Nash witnesses, not only static inequalities. Each has
zero joint Never. Every proper-child universal finite weighted-debt-plus-
Never bound is consequently falsified by an exact positive outsider
gain. The fifteen pure-coalition improvements were checked separately.

The four sure-singleton weighted-floor inequalities sum to
−(9/2)sum_i lambda_i≥0, excluding EVERY nonzero nonnegative weight,
not just uniform weights. The all-sure grand law has all participant
premiums 1/10 and falsifies product-low and implemented supportwise
nonpositive participant balance. Negative proper participant premiums
make the protected set empty. These failures are compatible with UE
and do not imply exhaustive failure of other producers.

As an extra four-core boundary check, let every hazard equal 99/100.
At the exact source

    v=(−9808618/5,−9808128/5,−9808128/5,−9808128/5),

all four players are indifferent, and their successor is

    w=s+(47223/1250000)(1,1,1,1)>s.

The raw participant sum calculation is
Q_i−s_i=−(9/2)q(1−q)²−6q²(1−q)+(1/10)q³.
This is an independent exact full-core test showing that an unbounded-
source return claim would fail here too. It is not needed for the
boxed theorem and is not a UE counterexample.

### Assembly and bounded comparisons

The triple fixture, its two outside-box regressions, thirteen exact
child profiles and one diffuse-child sequence retain the previously
audited values and complete-deviation arguments. The full-core singleton
matrix and all four triple inverses were recomputed: only child123 has
a nonnegative inverse, with passive weights (−1/7,5/7,3/7). The full
inverse entry (0,2) is −5/7. The displayed regular LCP offset has
unique root (0,1,1,1), inactive residual 2 and active determinant 7,
so degree +1 is correct. Principal03 is R₀ and its stated negative
offset is infeasible. All thirteen partition row-sum witnesses and
both remaining exact response polynomials check.

I inspected the actual signatures of
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`
and `withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
The latter really quantifies over every child behavioral profile, so
the exact child witnesses refute its claimed universal bound without
pretending to refute all selected-child constructions. The degree,
inverse, normality and exact-root consumers have the already inspected
literal hypotheses named in the artifact. No reference to another
math-folder proof is required, and no assembly correction is requested.
