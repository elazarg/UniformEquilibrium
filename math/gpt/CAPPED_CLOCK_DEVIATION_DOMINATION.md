# Capped-clock deviation domination and exact quiet extension

## Status and mathematical increment

This is ordinary mathematics, not Lean-checked. No repository source, branch,
commit, or PR was changed. The repository snapshot inspected was
`5aac30ad2553dadd5895dc79fbc4f1f5680d7570`.

The existing three-player singleton cycle, explicit rates, and general balanced
singleton consumer are dependencies, not new results here. The earlier
`THREE_CYCLE_PASSIVE_INHERITANCE.md` overstated the increment by including the
rates among the new mathematics. Its actual addition was outside-player row
inheritance and the associated strategy-producing extension.

This note goes beyond continuation-value inheritance: it gives a finite raw-table
criterion that compiles every outside deviation into a weighted sum of legal
unilateral child deviations. The child need not be a balanced cycle, stationary,
absorbing, or approximately Nash at every suffix. There is no change to its laws
in the prescribed parent profile.

The outputs are:

1. An exact pathwise characterization of this capped-clock deviation compiler.
2. An unrestricted regret-transfer theorem valid for terminal, discounted, and
   every finite-horizon evaluation, with fifteen linear reward constraints for a
   three-player child.
3. A fourteen-constraint terminal version when the child has a positive own
   singleton, together with its full Never correction.
4. A raw sufficient class inside the paired positive-degree singleton cylinder,
   where no balanced singleton cycle exists.
5. A sharpness result for the previous strictly inverse-positive three-player
   child route: choosing a longer balanced child word cannot repair a negative
   outside inverse-row coordinate.

These are not a proof of arbitrary Fin4, a claim that the criteria are necessary
for UE, or a worldwide priority claim. The exactness in item 1 concerns the
specified deviation compiler, not all possible equilibrium constructions.

## 1. Model and raw inequalities

Let I be finite, let S be a nonempty proper subset, and let k be outside S.
All outside players will prescribe Never. Only reward coordinates for coalitions
contained in S or in S union {k} enter k's conditions.

A nonempty first quitting coalition A pays r(A). Live and Never pay zero. All
clocks are independent, privately randomized laws on N union {Never}; complete
behavioral replacements are allowed. Put

    s_i = r_i({i}).

Choose nonnegative numbers lambda_i for i in S. Require:

    (N)  s_k <= sum_i lambda_i s_i;

    (F)  r_k(A)-s_k >= sum_i lambda_i [r_i(A)-s_i]
         for every nonempty A subset S;

    (J)  r_k(A union {k})-r_k(A)
           <= sum_i lambda_i [r_i(A union {i})-r_i(A)]
         for every nonempty A subset S.

When i is already in A, its summand in (J) is zero. Thus these inequalities
retain every membership comparison without inventing an empty-coalition reward.

(N) protects the all-Never event. (F) compares early solo quitting with waiting
for an arbitrary later child coalition. (J) compares joining a child coalition
at the same date with child players' own membership changes.

For |S|=3 these are fifteen scalar linear inequalities in three nonnegative
unknowns: one (N), seven (F), and seven (J). The coefficients are literal reward
entries. They are a linear program for a fixed table, not a quantifier over
unknown equilibrium strategies.

All rewards may be signed. The conditions themselves, rather than an implicit
normalization or punishment hypothesis, specify the allowed signs and bounds.

## 2. Pathwise deviation compiler

Fix a deterministic tuple of child clocks T=(T_i) and an outside deadline t.
For each child i construct a SEPARATE unilateral counterfactual by replacing
only its clock with

    T_i^t = min(T_i,t),

where Never is larger than every finite date. This preserves all of i's earlier
quits. It neither discards the old source nor changes any opponent clock.

Write G_k^t(T) for the outside player's gain from replacing Never by Quit t,
and G_i^t(T) for child i's gain from this capped-clock replacement, both for
terminal payoff. Then

    G_k^t(T) <= sum_i lambda_i G_i^t(T).                 (1)

Here is the complete case split. Write tau for the original first child date.

* If tau<t, every counterfactual has the same first outcome as prescribed play;
  all gains are zero.
* If tau=t, let A be the child coalition quitting there. The outside response
  replaces A by A union {k}; child i's counterfactual replaces A by A union {i}.
  Inequality (1) is exactly (J).
* If t<tau<Never, let A be the original later coalition. The outside response
  obtains s_k at t, and child i's counterfactual obtains s_i at t. Inequality
  (1) is precisely (F), rearranged.
* If tau=Never and t is finite, inequality (1) is (N).
* If t=Never, every clock remains unchanged and all gains are zero.

No expectation, equilibrium property, continuation choice, or cap attainment
enters this argument.

### Exactness for this compiler

Conversely, suppose (1) holds for every deterministic child clock tuple and every
deadline, with the same fixed lambda. All children playing Never and t=0 recover
(N). Prescribing A surely at date 1, everyone else Never, and t=0 recovers (F).
Prescribing A surely at date 0, everyone else Never, and t=0 recovers (J).

Thus (N), (F), and (J) are necessary and sufficient for the universal pathwise
terminal gain inequality for these particular capped-clock deviations. They are
also necessary and sufficient if that inequality is formulated in expectation
for every independent child profile, since deterministic profiles are included.
This is NOT a necessity theorem for a comparison of full caps using arbitrary
child responses, or for existence of a parent equilibrium.

## 3. Every nonincreasing absorption evaluation

Let f:N union {Never}->[0,1] be nonincreasing, with f(Never)=0. Evaluate a first
coalition A at date tau by f(tau) r(A). Terminal payoff has f(t)=1 at every
finite date. Discounted payoff has f(t)=d^(t+1), 0<d<1, under the live-stage-zero
convention. H-stage Cesaro payoff has

    f_H(t)=max(H-t-1,0)/H.

With immediate payment at the quitting stage the alternative formula is
max(H-t,0)/H; the same proof applies. More generally any normalized nonnegative
stage evaluation gives a nonincreasing tail weight of this kind.

The pathwise inequality (1) remains valid with evaluated gains. Only the case
t<tau<Never needs more calculation. Put

    d = s_k-sum_i lambda_i s_i,
    psi(A) = r_k(A)-sum_i lambda_i r_i(A).

By (N), d<=0, and by (F), psi(A)>=d. The difference between the left side of
(1) and its right side is

    f(t)d-f(tau)psi(A)
      = [f(t)-f(tau)]d + f(tau)[d-psi(A)] <= 0.         (2)

For tau=t, multiply (J) by f(t). For tau=Never, use f(t)d<=0. The other cases
are unchanged. Thus the theorem includes signed rewards and finite horizons
without passing through an unjustified terminal/average interchange.

### Approximate raw certificates

If every inequality (N), (F), and (J) is allowed additive violation at most eta,
where eta>=0, the same proof gives

    G_k^t(T) <= sum_i lambda_i G_i^t(T) + eta.

In (2), the two nonnegative coefficients add to f(t)<=1. Therefore the error is
eta, not two eta and not a sum over dates. This also gives a quantitative
robustness version of the regret theorem below.

## 4. Arbitrary private laws and complete caps

Let sigma be any actual independent child profile and let nu be any outside
replacement law. For each child i independently sample its original clock T_i
and a fresh clock Z_i with law nu, and use min(T_i,Z_i) as a unilateral
replacement. Denote the resulting marginal by sigma_i wedge nu.

This is a legal private stopping law. Its survival function is the product of
the two survival functions. Equivalently its conditional hazard is

    1-(1-q_i(t))(1-q_nu(t))

whenever the conditioning event has positive probability. Unreachable histories
can be assigned arbitrarily. For a pure deadline, the old hazard is retained
before t and quitting is certain at t.

Integrating the pathwise inequality gives the actual response comparison

    U_k^f(nu,sigma)-U_k^f(Never,sigma)
      <= sum_i lambda_i [U_i^f(sigma_i wedge nu,sigma_-i)
                           -U_i^f(sigma)].             (3)

The integration can use one common Z as a proof coupling. The terms on the
right are distinct unilateral counterfactual experiments, each with its correct
independent marginal law. No common random signal is introduced into the
prescribed parent game or into any one of those experiments.

Let d_i^f be child i's full response cap minus its prescribed payoff. Every
term in brackets is at most d_i^f, even if the cap is unattained. Nonnegativity
of lambda and the supremum over ALL nu yield

    d_k^f(quiet lift sigma) <= sum_i lambda_i d_i^f(sigma).       (4)

Every surviving player's prescribed payoff and complete cap are unchanged by a
quiet lift. Hence, for one outside player and W=sum_i lambda_i,

    E_f(quiet lift sigma) <= max(1,W) E_f(sigma).         (5)

The same statements hold simultaneously for several outsiders, each with its
own certificate against S. Coalitions containing two or more outsiders never
occur under a unilateral deviation and are completely unrestricted. In that
case replace W in (5) by the largest outside row sum, and

    D_parent <= sum_i [1+sum_k lambda_ki] d_i.

Equations (3)-(5) apply to every profile, not merely to an equilibrium or to a
profile with suffix optimality. In particular exact terminal Nash, uniform
finite-horizon error bounds, and suffix error bounds transfer whenever supplied
by the child.

## 5. Removing (N) for terminal equilibrium transfer

Suppose only (F) and (J) hold. Let

    nu_infty = Pr(all child clocks are Never),
    d_plus = max(s_k-sum_i lambda_i s_i,0).

For TERMINAL evaluation, the only unprotected path in Section 2 is all child
clocks Never. Thus, without any singleton-sign assumption,

    d_k(quiet lift sigma)
      <= sum_i lambda_i d_i(sigma) + d_plus nu_infty.    (6)

If some child j has s_j>0, then

    d_j(sigma) >= s_j nu_infty.                         (7)

To prove (7), cap j's own clock at a deterministic deadline L. As L tends to
infinity, the pathwise gain tends to zero whenever the original child play
absorbs at a finite time: eventually capping changes no earlier outcome. When
all clocks are Never, the gain is s_j. Bounded convergence therefore makes the
gain converge to s_j nu_infty. Each finite-L replacement is legal and bounded
by d_j, which proves (7) without attaining a best response.

Combining (6) and (7),

    d_k <= sum_i lambda_i d_i + (d_plus/s_j) d_j.         (8)

Consequently fourteen raw inequalities (F), (J) suffice to lift terminal
approximate equilibria when the child contains a positive own singleton.
The amplification factor in maximum regret is

    max(1, sum_i lambda_i + d_plus/s_j).

This is not asserted as an evaluation-by-evaluation bound without (N): the
term [f(t)-f(tau)]d in (2) can then be positive on finite absorption paths.
The terminal all-errors/finite-law consumer gives uniform existence from (8).

A source with nu_infty=0 also removes (N), regardless of singleton signs.
When all child singletons are nonpositive and the outside singleton is positive,
no general vanishing-Never source or quiet-lift conclusion is supplied here.

## 6. Uniform targets and actual finite selection

Under (N), (F), (J), every child uniform-equilibrium target v_S extends to at
least one parent target having the SAME coordinates on S.

Choose child profiles sigma_m delivering v_S with uniform horizon errors tending
to zero. For a fixed profile, bounded convergence makes its Cesaro payoffs
converge to its terminal payoffs. Thus its terminal child vector is close to
v_S. The outside terminal vectors are bounded; choose a subsequence converging
to v_out. The same profiles, quietly lifted, satisfy the uniform regret bound
(5). For each required accuracy, choose one sufficiently late profile and then
one horizon threshold making that profile's outside Cesaro payoffs close to its
terminal vector. This proves the required target quantifier order.

Alternatively, use child finite-law terminal approximants and (4), then the
existing terminal-to-uniform selection theorem. This also applies under the
fourteen-constraint positive-singleton variant (8). The quiet lift adds NO dates
and leaves every child marginal unchanged.

For a rational table a feasible certificate has rational weights. A completely
specified, though not efficient, finite-law producer is:

1. Solve the finite rational feasibility problem for lambda.
2. Enumerate rational independent child laws on increasingly large finite menus.
   Evaluate their full terminal caps using every displayed deadline, one first
   post-calendar deadline, and Never.
3. Accept a child profile below the parent tolerance divided by the amplification
   factor, and append Never for the outside player.

For a three-player child, unconditional UE, finite-law approximation and
continuity of the finite full-cap objective prove termination. Rational density
is applied only on a fixed finite menu, whose cap is a finite maximum of
polynomials; it is not an approximation theorem for an arbitrary limiting cap.
No efficient date bound, root oracle, or arithmetic-complexity claim is made.

The existing declaration supplying the three-player result is
`quittingGame_exists_uniformEquilibriumPayoff_threePlayer`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`).
It was read at the pinned snapshot; its proof invokes the already established
analytic-germ and three-dimensional dispatch machinery. It is not reproved here.

## 7. Finite dual certificates and noncoverage

Write the raw LP as V lambda >= b, lambda>=0. Its row data are:

    Never:   v=s_S,                       b=s_k;
    future A:v=s_S-r_S(A),                b=s_k-r_k(A);
    join A:  v_i=r_i(A union {i})-r_i(A),  b=r_k(A union {k})-r_k(A).

The exact alternative to feasibility is a finite vector y>=0 with

    V^T y <= 0,                   b dot y > 0.           (9)

Indeed feasibility contradicts (9) by multiplication. Conversely the cone
{V lambda-z:lambda,z>=0} is polyhedral and closed; if it excludes b, separation
from its finitely generated cone supplies y. Its negative-coordinate generators
force y>=0 and its V-column generators force V^T y<=0. This is the finite
Farkas alternative, not a game-theoretic existence argument.

For rational data both primal and dual certificates can be checked exactly.
Drop the Never row for the fourteen-row terminal criterion. A hypothetical
Fin4 counterexample must defeat every applicable deletion LP. This is a new
finite restriction, not a contradiction: the LPs do fail on solved tables.

For example, the complete table from the attached
`ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO.md` is

    r0(A)=1 if 0 in A, otherwise 2*1_{2 in A};
    r1(A)=(2*1_{0 in A}-1)*1_{1 in A};
    r2(A)=(2*1_{1 in A}-1)*1_{2 in A};
    r3(A)=1_{3 in A}.

It has a one-row dual obstruction for every deletion, even with (N) omitted.
For deletion of 0, use the future coalition {3}: v=(-1,-1,0), b=1.
For deletion of 1, 2, or 3, joining the full child coalition has v=0 and b=1.
Thus none admits our compiler, consistently with the attached theorem excluding
EVERY unchanged-child approximate-equilibrium lift near that table. Its parent
nevertheless has an exact equilibrium. These duals are not UE counterexamples.

## 8. An accepted family in the paired singleton cylinder

Fix the singleton rows

    r({0})=(1,4,0,0),    r({1})=(4,1,0,0),
    r({2})=(0,0,1,4),    r({3})=(0,0,4,1).

Their singleton-difference matrix is

    Gamma = [0 3 -1 -1; 3 0 -1 -1; -1 -1 0 3; -1 -1 3 0].

Delete player 3 and take lambda=2 e_2. Conditions (F), (J) become the FOURTEEN
literal inequalities

    r3(A) >= 2 r2(A)-1,
    r3(A union {3})-r3(A)
        <= 2 [r2(A union {2})-r2(A)]

for nonempty A subset {0,1,2}. Condition (N) is 1<=2. Therefore every completion
satisfying these inequalities has UE. No root or equilibrium is supplied as a
premise. The ENTIRE child table can be chosen arbitrarily, subject to the fixed
singletons: then choose the remaining player-3 passive and joining entries to
satisfy these inequalities. All other parent coordinates on coalitions
containing 3 remain unrestricted, apart from the fixed singleton column.

More precisely, 33 of the 44 nonsingleton coordinates are completely free:
the twelve child-player coordinates on child nonsingleton coalitions and the
twenty-one child-player coordinates on nonsingleton coalitions containing 3.
The remaining eleven coordinates belong to player 3: four passive coordinates
satisfy lower bounds and seven joining coordinates satisfy upper bounds. All
eleven can always be selected after the free coordinates have been fixed.

For clarity, the singleton instances of (F) have strict slacks 1,1,3, so this
family is nonempty for every such child table. For each other child coalition A,
choose r3(A) sufficiently large; then choose r3(A union {3}) below its displayed
upper bound. There are no conflicts between these choices.

For EVERY actual child profile the conclusion is the particularly simple bound

    d3(parent quiet lift) <= 2 d2(child),
    d_i(parent)=d_i(child) for i=0,1,2.                  (10)

No small-hazard assumption is made. Simultaneous child quitting is retained.

### A completely specified rational fixture

| Coalition | r0 | r1 | r2 | r3 |
|---|---:|---:|---:|---:|
| 0 | 1 | 4 | 0 | 0 |
| 1 | 4 | 1 | 0 | 0 |
| 2 | 0 | 0 | 1 | 4 |
| 3 | 0 | 0 | 4 | 1 |
| 01 | 2 | 2 | 1 | 2 |
| 02 | 2 | 1 | 2 | 4 |
| 03 | 2 | 0 | 1 | 2 |
| 12 | 0 | 2 | 2 | 4 |
| 13 | 1 | 2 | 0 | 2 |
| 23 | 1 | 1 | 2 | 2 |
| 012 | 1 | 2 | 0 | 0 |
| 013 | 0 | 1 | 0 | -1 |
| 023 | 0 | 0 | 0 | 1 |
| 123 | 0 | 0 | 1 | 0 |
| 0123 | -1 | -1 | -1 | -1 |

All fifteen certificate slacks are at least 1. Entrywise perturbations of size
less than 1/6 preserve them: each (F) or (J) slack changes by at most
2(1+sum lambda) times the perturbation, here six times it. Thus the accepted set
also contains full-dimensional reward neighborhoods, not only an affine cylinder.

There is no pure equilibrium at the fixture. The exact checker verifies a gain
of at least 1 at every nonempty pure coalition; all-Never has gain 1. A later
deterministic first stopping date gives the same coalition-membership comparison.

The fixture happens to have an easy mixed one-date equilibrium:

    q=(1,2/3,2/3,0), then Never,
    U=B=(13/9,2,2/3,4/3).

For player 0 its immediate endpoint is 13/9, its first late endpoint is 1, and
Never gives 8/9. Players 1 and 2 are screened by sure player 0 and their two
endpoints tie at 2 and 2/3. Player 3's Continue payoff is 4/3 and its immediate
Quit endpoint is -2/9. Every later deadline and Never has the Continue payoff.
This checks complete caps, not just the prescribed two-action menu.

The fixture's easy mixed equilibrium is calibration, not the substantive new
existence proof. The family theorem quantifies over arbitrary child completions
and compiles their child equilibria without selecting a common stationary form.

### Bounded comparisons

The paired matrix has determinant 45 and inverse with diagonal 2/15,
within-pair entries 7/15, and cross-pair entries 1/5. Thus its inverse is strictly
positive and its LCP degree is +1, as already established in the supplied index
packet. This is the region not dispatched by a degree-not-one contradiction.

There are NO singleton escort edges: reciprocal within-pair entries are both
positive and reciprocal cross-pair entries both negative. The existing
`BalancedSingletonCycleCertificate.exists_escortCycle`
(`UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean`) therefore rules
out every balanced singleton cycle, of every length and with every active subset.
This applies to the child as well as the parent. Thus (10) is not another
application of the balanced-singleton row extension.

The principal on {0,1,2} has no nonzero homogeneous nonnegative solution, since
its last row is -x0-x1 and then its first row forces x2=0. It cannot have an LCP
solution at right-hand side -1 because that last row cannot reach 1. Hence the
full matrix is not projective Q-bar. The fixture also fails the own-singleton
product-low condition at pure coalition 02, where both active owners receive
2>1. Weak singleton payoff exclusion fails: common stationary hazards tending to
zero have payoff tending to (5/4,5/4,5/4,5/4), regardless of fixed nonsingleton
rewards. None of these comparisons claims exclusion from every known theorem.

The existing exact block-deletion gate does not accept player 3: its singleton
is 1 while its unconditional continue floor is at most 0, and joining coalition
{0} raises its payoff from 0 to 2. Our comparison charges that possible gain to
a CHILD deviation, rather than requiring it to be nonpositive by itself.

For a full reward ball of radius 1/100 around the fixture, the raw certificate,
absence of pure equilibria, escort-sign pattern, positive inverse, and positive
determinant all persist. To check the inverse claim quantitatively, the paired
inverse has infinity norm 1; the singleton-matrix perturbation has norm at most
6/100. The inverse perturbation norm is at most (6/100)/(1-6/100)=3/47<2/15,
so all inverse entries stay positive. Invertibility along the whole segment
preserves the determinant sign. These are bounded class comparisons only.

## 9. The general balanced-child row argument and its precise limit

This section records the reusable generalization noted by the user and then a
sharpness result. It does not rebrand the existing cycle or rates as new.

Let T=Gamma_SS, and let a balanced child singleton cycle have continuation
singleton laws mu^ell, with

    mu^ell>=0,  sum mu^ell=1,  z^ell=T mu^ell>=0.

Actual absorption supplies these laws. If an outside row g=Gamma_kS has a
nonnegative multiplier w with g>=wT entrywise, then

    g mu^ell >= w z^ell >=0

at every phase. Equality g=wT is the earlier factorization. This requires no
inverse and works for any suitable balanced child cycle. The existing mesh and
complete-response consumer then apply to the extended certificate. One must
still retain its opponent-divergence field.

For a fixed supplied cycle, the EXACT safe-row cone is instead

    {g: g mu^ell>=0 for every ell}
      = cone{mu^ell}^*.

It can be larger than the simple nonnegative-row cone. With an invertible T the
condition is g T^(-1) in cone{z^ell}^*. This is a continuation-floor criterion,
not a claim that every failure creates positive full regret before refinement.

### Sharpness for a strict inverse-positive triple

Suppose |S|=3 and B=T^(-1)>0. Relabel so T has the familiar sign pattern

    [0 -b0 a0; a1 0 -b1; -b2 a2 0],       a_i,b_i>0,

with product a_i > product b_i. Put h_j=sum_i B_ij>0. At every continuation,

    h dot z=1.

Delete zero-hazard phases and merge consecutive phases of the same owner.
Every owner change is an escort edge. In this strict three-player sign pattern
there is only the cyclic order 0->1->2->0. At a change from i to j, both
coordinates z_i and z_j are zero: the previous owner's tie persists through its
own arc, and the next owner's tie holds at its start. Thus the change point is
one of the three uniquely determined vertices

    e_0/h_0, e_1/h_1, e_2/h_2.

Opponent divergence forces owner changes and hence visits to ALL three vertices.
The same reasoning applies to a one-owner-at-a-time infinite balanced child
spine with actual continuation payoffs, all-player singleton floors and joint
absorption: a final forever-owner block would have its singleton payoff vector,
contradicting its strictly negative singleton comparison for another child.
All changes therefore occur at finite dates, with the same cyclic order.

If w=gB, outside surpluses at the three forced vertices are w_j/h_j. Consequently

    an outside singleton floor on any such balanced child spine
      <=> g T^(-1)>=0.                                 (11)

The old row condition is thus not merely a convenient sufficient condition for
one selected three-phase word. Longer words, repeated owners, arbitrary splits,
and different starting phases do not weaken it in the strict-triple setting.

There is also an actual-response lower bound after refinement. Let

    Delta=max_j (-w_j/h_j)_+,
    C=(b0 b1 b2)/(a0 a1 a2) in (0,1),

where C is the existing cycle's one-revolution survival probability. The forced
vertices determine the merged hazards uniquely, so this same C applies to every
balanced realization. Suppose each individual row hazard is at most delta and
all parent rewards have magnitude at most M. From any starting phase a vertex
realizing Delta is reached within one revolution, with child survival at least
C. At that date the outside Quit endpoint is at least s_k-2M delta, while its
actual continuation is s_k-Delta. Its legal pure deadline therefore gives

    d_k >= C max(Delta-2M delta,0).                     (12)

The outside player's prescribed law is Never; the gain formula uses its actual
waiting payoff and actual child survival. Thus a negative inverse-row coordinate
cannot be hidden by longer or finer balanced schedules. This is not asserted for
arbitrary approximately balanced spines without a separate error analysis, or
for arbitrary child approximate equilibria.

Finally the new (F) condition, restricted to singleton coalitions, reads

    g>=lambda T.

If B>=0, it implies gB>=lambda>=0. Therefore the capped-clock criterion does not
repair a negative inverse row on that SAME strict triple. Its additional reach
comes from accepting child equilibria outside the balanced-singleton class,
as in the paired cylinder, while imposing collision-sensitive inequalities.
Conversely the old cycle row test permits arbitrary collision rewards, whereas
(J) can fail. The raw sufficient classes are not claimed to be nested.

## 10. Validation, source correspondence, and Lean boundary

`VERIFY_CAPPED_CLOCK_DEVIATION_DOMINATION.py` uses exact `Fraction` arithmetic and
only the Python standard library. Its successful run recorded:

* 25,600 pathwise comparisons on 16 signed tables and five evaluations;
* 80 full-cap transfers and 80 independently constructed randomized-deviation
  comparisons;
* 15 exact pure-clock recoveries of the raw constraints;
* 20 tests of the fourteen-row positive-singleton variant, with (N) deliberately
  violated;
* the full fixture's exact fifteen slacks, pure-coalition gaps, and unrestricted
  one-date caps;
* four one-row dual obstructions at the supplied unchanged-child no-go table.

These are finite regressions, not a replacement for Sections 2-5's proofs.

Read repository dependencies include:

* `BalancedSingletonCycleCertificate` in
  `UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`:
  exact arcs, owner ties, all-player floors and opponent divergence.
* `BalancedSingletonCycleCertificate.exists_escortCycle` in
  `UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean`:
  the existing arbitrary-period escort necessity, including zero-hazard removal.
* `quittingGame_exists_uniformEquilibriumPayoff_threePlayer` in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`:
  the existing unconditional child existence capstone.
* `UniformEquilibrium/Quitting/Classification/BlockDeletionInequality.lean`:
  existing join-cap/continue-floor control. Its bound does not replace the
  child-deviation comparison proved here.

The supplied files establish the general terminal all-errors selection interface,
finite independent-law approximation, the paired degree calibration, and the
arbitrary unchanged-child obstruction. Their results are not credited as new
here. The external APS paper was consulted for comparison of the continuous-time
route, not used as a mathematical premise of this proof.

A narrow Lean implementation should first prove the evaluated FIRST-OUTCOME
inequality with deterministic extended clocks and the four temporal cases. Then
construct the min-pushforward stopping law and integrate to obtain the actual
response inequality. The full cap theorem follows by supremum bounds, followed
by quiet-lift semantic identities and the existing three-player capstone.

The raw certificate should contain only lambda, its nonnegativity, and the
fifteen finite inequalities. The desired deviation bound, a favorable child
profile, suffix floors, cap attainment, or successful equilibrium extension must
NOT be assumed as certificate fields. The positive-singleton variant needs the
separate late-capping/bounded-convergence proof (7).

No compiler, Lean build, axiom audit, or theorem-level formal validation was run.
