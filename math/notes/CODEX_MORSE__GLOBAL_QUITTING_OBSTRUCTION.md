# Global quitting obstructions and cap-order geometry

Owner: CODEX_MORSE.

Status: ordinary mathematics, not checked in Lean. The convex-domain
smooth-potential exclusion in Section 7 has passed independent review by
CODEX_BROUWER, with no unresolved mathematical objection; see
[the review](../feedback/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION__BY_CODEX_BROUWER.md).
The cap-saturation result and the separate Section 8 obstruction have not
been independently reviewed. Section 7 accommodates
terminal endpoints outside the domain and interior parameters whose image is
a boundary diagonal. It does not supply arbitrary quitting-game homotopy data
or prove Simon's extended-orbit conclusion. The cap-saturation theorem shows that the full invariant-set
alternative always admits a contractible certificate whenever it admits any
certificate. It excludes an ordinary homology obstruction to that alternative;
it neither excludes every smooth potential nor constructs a counterexample.
The full game adapter and the nonconvex finite-union case remain open.
Section 10 is a complete actual-table proof that has passed independent
reviews by CODEX_BROUWER and CODEX_KREIN, with no unresolved mathematical
objection: with
nonnegative participant premiums confined to two players, a strict preference
of either core player for the other's singleton over their pair excludes
every smooth full-root potential. It imposes no outsider no-join condition.
Its proposed Fin4 UE consequence uses the existing polynomial obstruction
producer; source non-overlap has only been checked as specified there.
The independently reviewed, frozen standalone packet is
`../exports/TWO_PLAYER_PREMIUM_CORE_STRICT_LEAVE.md`; it contains a
stronger fully specified {0,3}-premium fixture, independently checked here
and by both reviewers. This remains ordinary mathematics, not Lean code.
Section 12 is a complete mutual-strict-join proof, using
the explicitly computed negative index of the only possible core-only
mixed root. Together with the separate reward-closure argument in
Section 11 it gives full four-player coverage when at most two players
have nonconstant participant rewards. Sections 11–13 have passed independent
falsification reviews by CODEX_BROUWER and CODEX_KREIN. The canonical-core
assembly passed its final artifact check and is frozen as
`../exports/PREMIUM_CORE_AT_MOST_TWO.md`, SHA256
`6adeee61351be59759a6ae69759a44fd055b7fd4bb7db1feb28379c124d6558e`.
It is not part of the older frozen strict-leave export.
Section 14 gives a new, unreviewed raw-class theorem allowing premium
cores of size three or four: every premium trap contains one common
player, and that player strictly prefers leaving every nonempty
coalition inside the greatest core. Its three-core rational fixture
passes the new hypotheses while failing the named matrix, peeling, and
response-partition screens. The original three-core unique-root
falsifier does not satisfy this additional leave condition.
Section 15 independently strengthens the new common-leaver criterion:
only the protected player needs nonnegative participant premiums.
The other players' premiums may have either sign. Its proof minimizes
on a different compact domain and uses an unconditional root-charge
bound; it is unreviewed and does not alter the frozen Section 14.
Section 9 shows that the local corner obstruction persists with compact,
contractible local fibers and uniform metric drift. This ends the proposed
local repair by fiber contractibility; it is not a counterexample to the
full homotopy hypotheses. Further work should use the actual four-player
root relation rather than refine that local repair. No export is requested
by this notebook.

## Exact question and semantic data

Let I be a nonempty finite player set, and let r(S) in R^I be the reward at
each nonempty coalition S. Fix R >= 0 with |r_i(S)| <= R. Independent
behavioral stopping laws, with arbitrary finite stopping dates and Never,
are the strategy space. Infinite all-Continue pays zero. A unilateral
deviation replaces a player's entire law. No public correlation is added.

For a behavioral profile p, let U(p) be its terminal expected payoff and
B_i(p) the supremum over every replacement law of player i. Write

    K = closure { (U(p), B(p)) : p is a behavioral product profile },
    Z = [-R,R]^I x [-R,R]^I,
    d(u,b) = max_i (b_i-u_i).

For a root x in [0,1]^I put c(x)=product_i(1-x_i), and let g_i(x) be the
unconditional expected reward from nonempty absorption at that root. Let
Q_i(x) be the payoff from quitting now, A_i(x) the unconditional reward
from nonempty opponent absorption while i continues, and
alpha_i(x)=product_(j!=i)(1-x_j). Exact semantic prefixing is

    T_x(u,b) = (g(x)+c(x)u,
                  (max(Q_i(x), A_i(x)+alpha_i(x)b_i))_i).       (1)

The carrier K is compact, contains the all-Never semantic pair, is preserved
by every T_x, and has nonnegative coordinate debts. The complete negative
alternative asks for a closed C in Z containing the all-Never pair, preserved
by EVERY T_x, with d >= Gamma > 0 everywhere. There is no restriction to
bounded controllers, selected roots, or a particular component.

The question tested here is whether topology of such C can force a diagonal
point b=u. The answer is negative for any proposed obstruction requiring
nontrivial homology or failure of contractibility: a certificate can always
be made contractible while preserving the same strict gap.

## Cap saturation preserves the full negative certificate

For any closed prefix-invariant C in Z, define

    C^up = { (u,b) in Z : there exists beta <= b with (u,beta) in C }.
                                                                  (2)

The comparison is coordinatewise; prescribed payoff u is unchanged.

**Theorem.** The set C^up is compact, contains C, is invariant under every
product-root prefix, and has the same positive gap lower bound as C. If
every point of C has b >= u, then every point of C^up also has b >= u.

**Proof.** Compactness follows by projecting the compact set of triples
(u,beta,b) with (u,beta) in C, beta <= b, and b in the box. Inclusion is
immediate. The first component of T_x is independent of the input cap; its
second component is coordinatewise increasing in that cap because
alpha_i(x) >= 0. Thus

    pi_u T_x(u,beta) = pi_u T_x(u,b),
    pi_b T_x(u,beta) <= pi_b T_x(u,b).

Prefix invariance puts the left pair in C; all coordinates of the right
pair remain in the reward box. Therefore T_x(u,b) belongs to C^up.
Finally b >= beta implies d(u,b) >= d(u,beta), preserving the original
Gamma with no loss. The coordinate-debt assertion has the same proof.

This is not the known debt-saturation operation. Debt saturation translates
payoffs AND caps while keeping b-u fixed and is impossible for positive-gap
certificates. Here only caps increase, and debt can increase. No unsupported
cap is claimed to be the actual cap of an executable profile. Invariant
certificates are allowed to contain supersets of the actual carrier.

## Every saturated certificate is contractible

Let P be the payoff projection of C, which is also the payoff projection of
C^up. Let top=R*1 and full=r(I).

First the continuous homotopy

    (u,b) |-> (u,(1-t)b+t*top),         0 <= t <= 1,             (3)

stays in C^up by cap saturation. It is a strong deformation retraction onto
the section P x {top}: every point of that section is fixed at every t.

Next give each player quit probability t at a single root, denoted x(t).
Define

    f_t(u) = g(x(t))+c(x(t))u.                                  (4)

For u in P choose ANY cap beta with (u,beta) in C. Prefix invariance implies
f_t(u) in P. The definition of f_t is independent of that choice; no
continuous choice of beta is needed. Moreover

    f_0(u)=u,             f_1(u)=full.                          (5)

The latter uses I nonempty, so the full-Quit root absorbs surely at I.
The map (t,u) |-> f_t(u) is polynomial and hence continuous. Consequently
f_t contracts P, and (f_t(u),top) contracts P x {top} inside C^up.
Concatenating (3) and (4) contracts C^up to (full,top).

**Corollary.** If eta(r)>0, the canonical choice C=K gives a closed,
contractible, full-prefix-invariant certificate C^up with the exact same
lower bound eta(r). Conversely, any such certificate is already a valid
certificate in the unrestricted invariant-set alternative. Thus imposing
contractibility on the invariant certificate does not change the sign
problem at all.

The proof does not assert that K itself is contractible. It DOES show that
its payoff projection is contractible, for every table. Upward cap saturation
is essential for the explicit contraction of the pair set.

If a supplied C has a semialgebraic description, (2) has one by real
quantifier elimination, and the displayed contraction is semialgebraic.
This conditional observation supplies no semialgebraic certificate producer.
The topological theorem itself uses no quantifier-elimination input.

## Exact tests and boundaries

1. One player, r({1})=1, R=1. A law that quits with total probability p has
   semantic pair (p,1). Hence K=[0,1] x {1}, already contractible, and
   eta=0. Formula (4) is f_t(p)=t+(1-t)p. This verifies the endpoint and
   the fact that contractibility alone contains no sign information.
2. For two players, let r({1})=(1,-1), r({2})=(-1,1), and
   r({1,2})=(0,0). Immediate simultaneous quitting has pair ((0,0),(0,0)).
   A silent prefix has pair ((0,0),(1,1)), because either player can quit
   alone in the inserted round. Thus T_0 is NOT the identity on the full
   semantic carrier. A purported contraction of K obtained by setting
   x=t*1 and calling t=0 the identity has this exact false step.
   In (4), only the PAYOFF projection is used, on which t=0 is the identity.
3. Caps increased in (3) remain at most R. The invariant-set argument never
   needs an unbounded cap, a change to the reward table, or a changed gap.
4. The synchronized root x(t) means independent Bernoulli(t) choices. It
   does not mean a public lottery between all-Continue and all-Quit; the
   intermediate g(x(t)) retains every collision coalition.
5. The statement is about existence of a topologically simple certificate,
   not about continuous production of its actual strategy witnesses. The
   witness beta used in (4) may vary discontinuously with u without affecting
   the explicitly defined homotopy.

## Exact sources inspected and comparison

The route began with the controller-tester question and the potential section
of `docs/TOOLKIT.md`. Exact source declarations inspected were:

- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`;
- `IsQuittingFloorFreeRobustEdge` and
  `quittingFloorFreeRobustChargedRelation` in
  `UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`;
- `IsQuittingFullExactRootPotential` and
  `isQuittingFullExactRootPotential_of_robustPotential` in
  `UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`;
- `IsQuittingFullExactRootPotential.minimum_exactRoot_absorption_eq_zero`
  and `IsQuittingFullExactRootPotential.minimum_above_singleton` in
  `UniformEquilibrium/Quitting/Projective/FullExactRootPotentialMinimum.lean`;
- `quittingTerminalSemanticPrefix`, `quittingTerminalSemanticCarrier`,
  `continuous_quittingTerminalSemanticPrefix`, and
  `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`; and
- `IsDebtSaturated` and
  `not_positiveDebtFloor_of_never_prefixInvariant_debtSaturated` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticDebtSaturatedBarrierNoGo.lean`.

The polynomial characterization constructs an arbitrary-degree rational
potential from a hypothetical counterexample; it is not an assumed producer.
Its all-Continue escape at global minima and the existing face/reflection
exclusions do not settle the all-degree alternative. The present theorem
does not revisit those polynomial classes.

No Lean command or implementation was run. The topological and saturation
claims here are ordinary mathematics under (1), with no external theorem
beyond compactness, projection of a compact set, and the displayed homotopy.

## 7. Convex-domain exclusion of every smooth strict graph potential

### Exact finite-dimensional statement

Let C be a nonempty compact convex subset of Euclidean R^n, n>=1, with
nonempty interior. A polytope is allowed but not required. Let

    f,g : C -> R^n

be continuous, with f(x)=g(x)=x for every x on the boundary of C. Assume
only the following diagonal-image condition:

    f(z)=g(z)  =>  f(z) belongs to boundary C.                 (14)

In particular, an INTERIOR parameter z may map to a boundary diagonal.
The stronger assertion f(z)!=g(z) throughout the interior is NOT assumed.

Let Omega be an open subset of R^n containing C, f(C), and g(C), and let
H:Omega->R be C^1. Suppose:

1. For every z with f(z)!=g(z), H(g(z))<H(f(z)).
2. For every x in boundary C, there is y_x in C such that

       gradient H(x) dot (y_x-x) < 0.                        (15)

**Theorem candidate.** These data cannot exist.

There is no convexity assumption on H, degree bound, continuous selection of
y_x, or restriction that f(C) and g(C) lie in C. The auxiliary projected map
below is a proof device, not a supplied root selector or strategy.

### A uniform descent perturbation of the boundary

Write P_C for the Euclidean metric projection onto C. Define, for y in Omega,

    W(y)=P_C(y-gradient H(y))-y.

Projection is continuous. At x in C its variational inequality gives

    gradient H(x) dot W(x) <= -||W(x)||^2.                    (16)

Indeed, compare the projecting point P_C(x-gradient H(x)) with the feasible
point x. Moreover W(x)=0 would imply
gradient H(x) dot (y-x)>=0 for EVERY y in C. Thus (15) implies W(x)!=0 at
every boundary point. Compactness of the boundary gives beta>0 with

    gradient H(x) dot W(x) <= -beta  on boundary C.

By continuity choose an open neighborhood U of boundary C with compact
closure in Omega such that gradient H(y) dot W(y)<=-beta/2 throughout U.
Choose a continuous cutoff chi:R^n->[0,1], equal to one on a neighborhood of
boundary C, with compact support K contained in U. On K the vector W is
bounded. The positive distance from K to the complement of U, and uniform
continuity of gradient H on a compact neighborhood of K in U, allow one
constant e in (0,1] such that, for all y in K and 0<=t<=1,

    y+t*e*chi(y)*W(y) belongs to U,
    gradient H(y+t*e*chi(y)*W(y)) dot W(y) <= -beta/4.         (17)

Only this compact neighborhood is used; no values of H outside Omega are
invoked. Define T:Omega->Omega by

    T(y)=y+e*chi(y)*W(y)

on the support neighborhood and T(y)=y elsewhere. The cutoff makes this
continuous across the support boundary. Integrating the directional
derivative along the segment in (17) proves

    H(T(y))<=H(y) for all y in Omega,
    H(T(y))<H(y) whenever chi(y)>0.                           (18)

For x in boundary C, chi(x)=1 and

    T(x)-x=e W(x),       x+W(x) belongs to C.                 (19)

This construction explicitly handles endpoints outside C. Points outside the
cutoff support are unchanged, and all moved segments lie inside U⊂Omega.

### Brouwer contradiction without a degree assertion

Define a continuous vector field on the PARAMETER domain C by

    Z(z)=T(g(z))-f(z).

It is nowhere zero. If f(z)!=g(z), hypothesis 1 and (18) give
H(T(g(z)))<=H(g(z))<H(f(z)). If f(z)=g(z), (14) places their common value on
boundary C, where (18) is strict. Thus the allowed interior diagonal images
are removed by an actual descent perturbation; they are not silently deleted.

The map z -> P_C(z+Z(z)) is a continuous self-map of compact convex C.
Brouwer supplies a fixed point z. Projection's variational inequality then
says

    Z(z) dot (y-z) <= 0  for every y in C.                    (20)

If z is interior, choose y=z+t Z(z) in C for sufficiently small t>0.
Equation (20) contradicts Z(z)!=0. If z is on the boundary, f(z)=g(z)=z
and (19) give Z(z)=e W(z). Choose y=z+W(z) in C. Then (20) says
e||W(z)||^2<=0, again a contradiction. This proves the theorem.

The proof uses only the usual finite-dimensional projection inequalities,
compactness, continuous cutoff functions, and Brouwer's fixed-point theorem.
It does not use a differentiable f or g, a nonzero difference on the interior,
a source projection of degree one, or a claimed repeatable graph orbit.

### Consequence for the one-polytope Simon hypotheses

Take `QuestionOneHypotheses` from
`MathUE/Topology/SimonViabilityQuestion.lean` with pieceCount=1. Then C is
the single full-dimensional compact convex polytope. Put

    (f(z),g(z)) = homotopy(z,1).

The actual source clauses give continuity, f=g=id on boundary C, and precisely
the diagonal-IMAGE implication (14). They do not give an interior-parameter
nonvanishing statement.

Suppose H is C^1 on an open neighborhood of C together with both coordinate
projections of the full graph J, and for some c>0 satisfies

    H(x)-H(y) >= c ||x-y||  for every (x,y) in J.             (21)

Terminal homotopy pairs lie in J, so (21) gives hypothesis 1. At any boundary
x, the local escape clause supplies y at positive distance from x, with
distance(y,C)<=distance(x,C)=0 and the whole segment [x,y] contained in the
local fiber over x. Closedness of C gives y in C. For every t in [0,1], the
pair (x,x+t(y-x)) lies in the local graph and hence J. Applying (21), dividing
by t>0, and letting t decrease to zero yields

    gradient H(x) dot (y-x) <= -c ||y-x|| < 0.

The theorem therefore excludes EVERY C^1 potential satisfying (21) under the
one-polytope Simon hypotheses. In particular it excludes every polynomial,
without a degree cutoff. Compactness and contractibility of graph fibers are
not needed by this exclusion once their displayed boundary escape is present.

This is not an affirmative answer to Simon's orbit question: no necessity
theorem has been supplied turning absence of such a smooth potential into an
unbounded-variation extended orbit. Nor is a merely bounded, discontinuous,
or piecewise potential covered by the C^1 theorem without further work.

### Exact quitting adapter and its unresolved inputs

For rewards bounded by M and a full robust edge (v,q,w) in the box of radius B,
with tolerance delta>=0 and absorption a, the Bellman residual and reward
bound give directly

    ||w-v||_infinity <= (M+B+delta)*a,
    ||w-v||_2 <= sqrt(n)*(M+B+delta)*a.                      (22)

Indeed the exact successor is (1-a)v+a*rbar with each coordinate of rbar
in [-M,M] when a>0; the a=0 case has w=v. Thus a unit-absorption robust
potential has the metric drift (21), with
c=1/[sqrt(n)*(M+B+delta)] when this denominator is positive.

Consequently the shortest sufficient adapter would produce, in the SAME
robust relation and its existing box:

- a full-dimensional compact convex C and continuous terminal maps f,g;
- f=g=id on boundary C and the diagonal-image implication (14);
- a robust root witness for every terminal pair (f(z),g(z)); and
- for every boundary x, a nontrivial segment into C such that every pair
  (x,x+t(y-x)) has a robust root witness.

These four inputs would reject the arbitrary-degree polynomial produced by
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`.
They are NOT currently produced here. In particular:

* `QuestionOneHypotheses` is a definition, not a game producer.
* `QuittingSimonFEdgeAt` in
  `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/SuppliedCorrespondence.lean`
  uses support-local absolute epsilon error, not absorption-relative robust
  error. Its literal graph is not a subgraph of the robust relation. This
  error-mode difference is nevertheless handled by the EXISTING upward
  translation described at the end of Section 9; it is not an additional
  open conversion problem when the translated endpoints fit the box.
* `HasQuittingSimonFiniteCellLyapunovCertificate` in the same file is supplied
  finite-cell data, not an arbitrary-game smooth certificate or a source of
  the convex domain.
* `lemma4_5` in `Literature/Simon2012.lean` constructs the question's data only
  under its explicit Section 4 hypotheses. Its domain is `TruncatedW`, a
  union of one truncated piece per player, not the single convex polytope
  required above. That declaration cannot be invoked as the missing adapter.

The open files `notes/SIMON_RESTARTABILITY_ONE_POLYTOPE.md` and
`notes/SIMON_RESTARTABILITY_GENERAL_SPLIT.md` ask for stronger repeatable
orbits. They are not proofs used here. The exclusion is a new candidate
answer about smooth strict potentials only. The general nonconvex finite-union
case remains a separate mathematical obligation; convex projection must not
be used there as if the union were convex.

## Remaining question

The relevant geometry must retain the LOWER cap boundary or a dynamically
constrained deformation: unconstrained upward caps erase every ordinary
topological obstruction while preserving the negative certificate. Can
full-prefix invariance force a diagonal on that lower boundary through its
cap order and actual witness coupling? Contractibility of the surrounding
certificate alone cannot supply that implication. Section 7's cutoff
perturbation and diagonal-image repair have passed independent review.
Sections 8 and 9 now retire the local inward-descent extension to the
truncated-box union, even after using contractible fibers. A genuinely global
argument or an actual same-robust-relation convex-domain producer remains
necessary; neither has been constructed here.

## 8. A truncated-box corner obstructs the local inward-descent repair

This is an exact counterexample to one proposed EXTENSION of Section 7,
not a full Simon graph satisfying all seven hypotheses and not a quitting
counterexample. In particular no terminal maps f,g or full invariant graph
are supplied here.

Let

    P1=[-1,0] x [-1,1],   P2=[-1,1] x [-1,0],   C=P1 union P2,
    H(x,y)=x^4+y^4+x^2+y^2+4xy-x-y.

This is the two-piece truncated-box geometry, with a missing upper-right
corner. At every boundary point x of C, and in EVERY piece Pj containing x,
there is a feasible direction v with gradient H(x) dot v<0.

For verification, H_x=4x^3+2x+4y-1 and H_y=4y^3+2y+4x-1.
On x=-1, H_x=4y-7<=-3; on the outer edge x=1 (where y<=0),
H_x=5+4y>=1. The symmetric statements hold on the horizontal outer
edges. The inward coordinate directions therefore work, including the outer
corners and every containing piece there. On the inner edge x=0, 0<y<1,
use the appropriate vertical direction unless H_y=0. If H_y=0, then
4y^3+2y=1 forces y>1/4, so H_x=4y-1>0 and the direction to the left is
strict descent inside P1. The horizontal inner edge is symmetric. At (0,0)
the gradient is (-1,-1): upward descent lies in P1 and rightward descent
lies in P2. Thus even the per-piece boundary version of (15) holds.

Now consider the connected inner-boundary cross

    A = { (t,0):0<=t<=1/4 } union { (0,t):0<=t<=1/4 }.

**Exact obstruction.** There is no continuous T:A->C such that

    ||T(z)-z||_infinity < 1/8,       H(T(z))<H(z)   for all z in A.

Indeed H(t,0)=t^4+t^2-t<=0 on this interval, with strict inequality for
t>0; likewise on the other arm. Consequently H(T(z))<0 throughout A.
But H(x,y)>=0 whenever x<=0 and y<=0, since every displayed term is then
nonnegative. Hence T(A) avoids P1 intersection P2. At z=(1/4,0), the
displacement bound gives first coordinate of T(z)>1/8; membership in C
therefore places this image in P2 without P1. At z=(0,1/4), the image lies
in P1 without P2. A connected subset of C avoiding their intersection cannot
meet both disjoint arms. This contradicts continuity of T.

Thus a continuous arbitrarily small inward descent perturbation cannot be
obtained from per-piece feasible gradient descent merely by replacing convex
projection with a projection or retraction onto the union. Convexification
would fill exactly the missing corner through which the descent map wants to
pass, and would change the boundary problem.

The same local obstruction embeds in four coordinates near an intersection
of two inner faces of the union of coordinate-truncated boxes: keep the
remaining coordinates a positive distance above their truncation thresholds,
add nonnegative squared deviations in those coordinates to H, and restrict
the perturbation to be smaller than that distance. Any transition to either
additional piece is then impossible, while crossing the first two pieces
still forces H>=0. This is a local geometry statement only; it does not claim
that this four-dimensional extension satisfies every global Simon hypothesis.

The convex theorem in Section 7 is unaffected. To treat the actual union,
one needs a different global argument using more than this local inward
descent repair, or an independently justified convex-domain game adapter.

## 9. Contractible local fibers do not repair the corner

This is a completed local test and a decision to retire one proof mechanism,
not a new global topological conjecture or a full Simon counterexample. The
reason for testing it is specific: the full source hypotheses include compact,
contractible local fibers, which Section 7 did not use. Those clauses might
have supplied the continuous inward-descent map missing in Section 8. They
do not do so, even with uniform metric drift and long segment escapes.

Keep the two pieces and polynomial H of Section 8. Put rho=1/64 and

    V=[-rho,rho]^2,
    G_x = (x+[0,rho]e1) union (x+[0,rho]e2),   x in V,
    G = { (x,y) : x in V, y in G_x }.

The graph G is compact: it is the union of the two continuous images of
the compact set V times [0,rho]. Every fiber contains its source and is
contractible by the explicit homotopy

    (y,t) |-> x+(1-t)(y-x).

Every fiber is thus a two-arm tree, not a disconnected set of escape
choices. Take J=G; the small-step inclusion into G then holds at every
positive scale.

On the square [-1/32,1/32]^2 both partial derivatives of H are at most

    4(1/32)^3 + 6/32 - 1 < -3/4.

All the displayed fiber segments lie in that square. Integration along
either coordinate segment consequently gives

    H(x)-H(y) >= (3/4)||x-y||_2     for every (x,y) in G.

For every x in V, moving by rho*e2 leaves its distance to P1 unchanged;
moving by rho*e1 leaves its distance to P2 unchanged. Indeed the unconstrained
coordinate remains inside [-1,1], and the other coordinate, which determines
distance to the relevant truncated piece, is unchanged. Both moves have
length rho and their entire segments lie in the fiber. Thus the local
distance-nonincreasing escape clause holds for BOTH pieces at EVERY source
in V, a stronger local assertion than requiring it only at sources within
rho of the relevant boundary piece.

Nevertheless no continuous map T from

    A_rho = ([0,rho] times {0}) union ({0} times [0,rho])

into C can satisfy both

    ||T(z)-z||_infinity < rho/2,      H(T(z))<H(z).

The Section 8 proof applies verbatim at this scale. H is nonpositive on
A_rho and nonnegative on P1 intersection P2. The image must therefore avoid
the intersection. The horizontal endpoint's image has positive first
coordinate and lies only in P2; the vertical endpoint's image has positive
second coordinate and lies only in P1. This contradicts connectedness.

This test supplies all the just-listed LOCAL properties simultaneously.
It deliberately does not supply terminal maps f,g, a neighborhood of the
ENTIRE boundary, or the global homotopy diagonal-image condition. Those are
exactly the remaining possible sources of a global obstruction. Fiber
contractibility alone cannot be invoked to select a short, inward, strictly
decreasing perturbation at a multiple-piece corner. No existence or
nonexistence assertion about quitting equilibria follows from this example.

### Actual-relation boundary for the next attempt

The relevant current source is
`exists_finFour_no_uniformPayoff_iff_exists_boundedSinglePivotPolynomialObstruction`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourBoundedSinglePivotPolynomialObstruction.lean`.
Its right-hand side uses an actual real unit-bounded four-player reward table,
own singleton vector lambda*e_p with lambda>0, no sure-quitter punishment
Nash root, and ONE rational polynomial with full robust drift on box three.
That same polynomial has degree at least three, is not multiaffine, and
satisfies the stated adaptive minimum restrictions. The equivalence neither
assumes nor concludes rational reward entries.

I also inspected the literal definitions `IsQuittingFloorFreeRobustEdge`
and `quittingFloorFreeRobustChargedRelation` in
`UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`, and
`IsQuittingFullExactRootPotential.minimum_exactRoot_absorption_eq_zero`,
`IsQuittingFullExactRootPotential.minimum_singleton_le`, and
`IsQuittingFullExactRootPotential.minimum_above_singleton` in
`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialMinimum.lean`.
The robust constraints are absorption-relative in BOTH Bellman residual and
ordinary coordinate Nash regret. There is no support-rationality condition
that may be substituted for them. All roots at a global potential minimum
are silent, and every such minimum lies strictly above all own singletons.

An existing exact conversion must be retained in this comparison. In
`UniformEquilibrium/Quitting/Root/UpwardTranslation.lean`,
`coordinateNashDefect_upwardTranslate_le_absorption` converts a support-local
epsilon-Nash root at v into ordinary regret at most 3*epsilon*a at
v+2*epsilon*1. The same source's
`quittingPayoffUpwardTranslate_sub_successor_eq` gives residual exactly
2*epsilon*a when its exact successor w is translated by the same vector.
Thus an exact `QuittingSimonFEdgeAt` edge yields an ACTUAL full robust edge
for the unchanged table after that common endpoint translation, whenever
3*epsilon<=delta and both translated endpoints are in the robust box.
This is already consumed for packets by `QuittingFiniteForwardPacket.upwardTranslate`
in `UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketTranslation.lean`.
No new theorem or improved constant is claimed.

For the unit-bounded Fin4 table and its near-feasible Simon carrier,
epsilon<=delta/3 with delta<=1/4 guarantees these endpoints lie in box
three: each untranslated coordinate has absolute value at most 1+epsilon,
and the translation increases that bound to at most 1+3*epsilon.
Consequently the SAME produced robust polynomial P pulls back to

    H_epsilon(v)=P(v+2*epsilon*1)

and obeys `H_epsilon(v)-H_epsilon(w)>=a` on every such Simon edge.
Since `||w-v||_2<=2(2+epsilon)*a`, this is a global positive metric drift
on that carrier. These are direct consequences of the inspected source
inequalities, not a newly discovered game producer. In particular, a
further support-to-relative-error adapter is not the missing global step.
This observation alone does not extend the potential to the artificial
glue in Simon's full topological graph or produce a charged return.

The next concrete question is whether the actual Nash-root relation for this
single-pivot table forces a positive charged return around its silent region.
Any usable answer must preserve the same table, tolerance, box, and potential
and explicitly use joint-coalition incentives. The singleton-face constraints
and the local topological fiber conditions alone have already been shown
insufficient for the proposed mechanisms. No answer or new producer is
claimed here, and no further generic local-repair lemma is proposed.

## 10. A two-player premium core with a strict preference to leave the pair

**Frozen strict theorem, independently reviewed PASS by CODEX_BROUWER and
CODEX_KREIN.** Complete ordinary proof; not Lean-checked. This is an
actual joint-coalition argument, separate from the retired topological repair.
The claimed conclusion is a full-root exclusion and, for four players, a
uniform-equilibrium existence theorem for the stated raw class. No broader
two-core theorem or arbitrary Fin4 theorem is asserted.

### Self-contained raw statement

Let I be a finite set with distinct players i,j. Each nonempty coalition
S has a finite real reward vector r(S). Write s_k=r_k({k}). Assume:

1. Every participant premium is nonnegative:
   `r_k(S)>=s_k` whenever k belongs to S.
2. For every k outside `{i,j}`, its participant reward is constant:
   `r_k(S)=s_k` whenever k belongs to S.
3. One designated core player strictly prefers the other singleton to their
   pair:

       r_i({i,j}) < r_i({j}).                              (40)

All nonparticipant rewards are arbitrary. The two core players may receive
independent, arbitrarily large nonnegative premiums on every coalition
containing them; nothing about triples or the grand coalition is suppressed.
Singletons may have arbitrary signs for the analytic statement below.

Choose M>=0 with every |r_k(S)|<=M and choose B>M. Put K=[-B,B]^I.
For an independent product root q in [0,1]^I define

    c(q)=product_k(1-q_k),       a(q)=1-c(q),
    T_q(v)=sum_(S nonempty) Pr_q(S) r(S)+c(q)v.

Let Q_k(q) and C_k(q,v) be the expected rewards when k respectively Quits
or Continues, with annotation v after all Continue. An exact root Nash
equilibrium at v means

    (T_q(v))_k=max(Q_k(q),C_k(q,v))  for every k.          (41)

This is a finite simultaneous-move Nash condition. An annotation need not
be an attainable terminal payoff or the value of a supplied strategy.

**Analytic theorem.** No C^1 function H on a neighborhood of K satisfies

    H(v)-H(T_q(v)) >= a(q)                               (42)

for every v in K and every exact root Nash q at v. This excludes every
polynomial degree, not merely a chosen ansatz.

**Four-player consequence.** If I has four players and all s_k>=0, the
actual quitting game has a uniform-equilibrium payoff. Its strategies use
independent private randomization and observe the public survival history.
Never pays zero. Every unilateral deviation may replace a player's whole
behavioral strategy, including all stopping dates and Never. There is one
fixed payoff target before accuracy; the approximating profile and common
finite-horizon threshold may depend on accuracy. No public correlation or
stationary-deviation restriction is introduced.

### An exhaustive full-root return property

Let

    C=product_k[s_k,B],
    L={x in C : x_k=s_k for at least one k}.

Every exact root Nash successor w=T_q(v) has w_k>=s_k, because
`Q_k(q)>=s_k` by assumption 1 and (41) dominates that Quit endpoint.
If v is in K, then w is also in K: it is a convex combination of v and
the finite reward vectors. Thus w belongs to C.

Suppose now ONLY that v_i>=s_i and v_j>=s_j; the other annotations may
lie below their singletons. For every exact root q at v with a(q)>0,

    T_q(v) belongs to the SAME set L.                     (43)

Here is the exhaustive check, retaining all other players' hazards.

* If any player k outside `{i,j}` has q_k>0, exact Nash and support of
  Quit give w_k=Q_k(q)=s_k. This uses its constant participant reward on
  EVERY coalition containing k, including triples and the grand coalition.
  Other players' hazards and the two core players' premiums may be arbitrary.
  Since w is already in C, this proves w in L in this entire case.
* Otherwise every outside hazard is exactly zero. Only in THIS case is
  the core player's endpoint gap the two-player expression

      Q_i(q)-C_i(q,v)
        =(1-q_j)(s_i-v_i)+q_j[r_i({i,j})-r_i({j})].      (44)

  If both q_i and q_j were positive, (40) and v_i>=s_i would make (44)
  strictly negative, contradicting player i's supported Quit action.
  Thus at most one core player is active. Positive absorption forces
  exactly one active core player k, whose opponents all Continue. Its
  Quit endpoint and hence its actual successor coordinate equal s_k.
  Again w is in L.

In particular, (44) is NEVER applied after ignoring a positive outsider
hazard. Such a hazard has already closed the first case through its own
exact coordinate equality. Formula (43) is a return to L with its original
singleton floors and common upper bound B, not to a different face or to
the boundary of another box.

Dependency refinement for later work: the return proof itself uses only
the leaving player's floor v_i>=s_i. The other core floor is not used
in (44); retaining both in the stated return lemma and subsequent
minimizer perturbation is harmless. This sharper source dependency does
not by itself enlarge the raw-table class, and the frozen export is
unchanged.

### The singleton-face derivative inequality

Assume for contradiction that H satisfies (42). Whenever x belongs to C
and x_k=s_k,

    gradient H(x) dot (x-r({k})) >= 1.                    (45)

For completeness, first suppose every other coordinate is strictly above
its singleton. Let k alone quit with probability t>0. It is indifferent,
and every nonowner strictly prefers Continue for sufficiently small t:
its endpoint difference at t=0 is s_l-x_l<0. These are the ACTUAL endpoint
comparisons, including r_l({k,l}) when the nonowner deviates. Hence the
root is exact Nash, its absorption is t, and its successor is
`x+t(r({k})-x)`. Apply (42), divide by t, and let t decrease to zero.

For weak nonowner inequalities, replace each nonowner coordinate x_l by
`(1-epsilon)x_l+epsilon B`, retaining x_k=s_k. Because B>M, all nonowner
inequalities become strict. Apply the preceding argument at each perturbed
point and then use continuity of the gradient as epsilon decreases to zero.
The admissible root rate may depend on epsilon; no uniform eligibility at
intersections of singleton faces is assumed. Upper-box coordinates cause
no difficulty because the successor segment remains in K.

This is also the precise conclusion of
`IsQuittingFullExactRootPotential.singletonFace_drift` in
`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`.

### The minimizer must have a constant-payoff binding player

Choose x minimizing H on the nonempty compact set L, and let

    J={k:x_k=s_k},       g=gradient H(x).

If J is a singleton `{k}`, the small sole-owner root in the preceding
argument is exact Nash at x, has positive absorption, and returns to L
by (43). Minimality of H on L contradicts (42). Thus |J|>=2.

Increasing one binding coordinate slightly then keeps another coordinate
pinned at its singleton. Therefore g_k>=0 for every k in J. If k is not
in J and x_k<B, two-sided feasible changes give g_k=0. If x_k=B,
one-sided feasible decrease gives g_k<=0.

Suppose J contained no player outside `{i,j}`. Then J is exactly `{i,j}`.
Apply (45) with owner j. Its owner-coordinate term vanishes. Its i-term is

    g_i(s_i-r_i({j})) <= 0,

because g_i>=0 and
`r_i({j})>r_i({i,j})>=s_i`. Every nonbinding interior coordinate has zero
gradient. Every upper-box coordinate contributes a nonpositive term,
since its gradient is nonpositive and `B-r_k({j})>0`. The entire left side
of (45) is consequently nonpositive, contradicting its lower bound one.

It follows that

    J0=J outside {i,j} is nonempty.                       (46)

This is where the actual strict pair-leave preference changes the
minimizer argument. It is not inferred merely from a positive premium.

### Force positive absorption while preserving the two core annotations

For sufficiently small epsilon>0 put

    v_epsilon=x-epsilon*1_J0.

The point remains in K, and its two core coordinates are unchanged and
remain at least their singleton levels. Differentiability gives

    [H(v_epsilon)-H(x)]/epsilon
          tends to -sum_(k in J0) g_k <= 0.               (47)

Choose ANY exact Nash equilibrium q_epsilon of the finite root game at
v_epsilon. Finite Nash existence supplies it without a continuous selector.
All-Continue is not Nash: any k in J0 would gain epsilon by quitting alone.
Hence a_epsilon>0, and the exhaustive argument (43) puts the actual
successor w_epsilon=T_(q_epsilon)(v_epsilon) in the original set L.

For k in J0, `w_epsilon,k>=s_k=v_epsilon,k+epsilon`. The elementary
absorption motion estimate gives

    epsilon <= w_epsilon,k-v_epsilon,k
            <= (M+B)*a_epsilon.                          (48)

Indeed `T_q(v)-v=a(q)(rbar-v)` for a(q)>0, with every coordinate of the
conditional absorption payoff rbar in [-M,M]. Minimality on L and (42)
now imply

    epsilon/(M+B) <= a_epsilon
        <= H(v_epsilon)-H(w_epsilon)
        <= H(v_epsilon)-H(x).

Divide by epsilon and use (47). The positive constant `1/(M+B)` cannot
be at most a nonpositive limit. This proves the analytic theorem.

The proof quantifies over the FULL finite root game at each perturbed
annotation, permits all simultaneous coalitions, and requires neither a
root branch nor a particular active support. It does not assert that an
arbitrary root can be repeated as a terminal Nash strategy.

### The actual four-player semantic consumer

Assume now I has four players and s>=0. Immediate Quit guarantees at least
s_k against every opponent behavior, by nonnegative participant premiums.
Against all-Never opponents the full response cap is exactly s_k. Therefore
the unrestricted punishment vector is exactly s. This agrees with
`quittingPunishmentValue_eq_singleton_of_nonnegativePremium` in
`UniformEquilibrium/Quitting/Classification/NonnegativePremiumPunishment.lean`.
All players are consequently normal.

If all s_k=0, all-Never is already exact Nash at every finite horizon.
Otherwise some singleton is positive. Were there no uniform-equilibrium
payoff, the inspected declaration
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in
`UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`
would produce a rational polynomial with unit absorption drift on EVERY
full robust edge in box M+2. Every exact Nash/Bellman edge in that box has
zero residual and zero regret, so the same polynomial satisfies (42) with
B=M+2. The analytic theorem excludes it. Thus the original four-player
game admits the stated fixed uniform-equilibrium payoff. No sure-root
alternative is assumed away as an extra raw-table hypothesis: it is part
of the same no-UE implication and the polynomial arm alone is contradicted.

This composition excludes all degrees and uses an actual-table producer
already present in the source. The new mathematical input is the selective
perturbation of binding constant-payoff players, justified by (40)-(46).
Neither a strategy nor a hypothetical good child is supplied to the raw
class theorem.

### Exact tests and bounded source-overlap check

The following fully specified rational table is a useful falsification test.
Let the possible premium recipients be 0 and 1. For every nonempty S let
their reward depend only on its core membership:

| Core membership | r_0(S) | r_1(S) |
| --- | ---: | ---: |
| neither | 0 | 2 |
| only 0 | 1 | -1 |
| only 1 | 3 | 0 |
| both | 2 | 1 |

Set r_2(S)=0 when 2 belongs to S, -1 when 2 does not belong and the core
pattern is only 1, and 3 in all other cases. Set r_3(S)=0 when 3 belongs
to S and 1 otherwise. The own-singleton vector is `(1,0,0,0)` and
`r_0({0,1})=2<3=r_0({1})`. Every participant premium is nonnegative and
only players 0 and 1 have nonconstant participant rewards.

At the product root `(1/2,1/2,0,0)`, both active Quit endpoints strictly
exceed their singletons: they are 3/2 and 1/2. This directly violates
`HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`.
Therefore neither `not_differentiable_absorptionDrift_of_nonnegative_productLow`
in `UniformEquilibrium/Quitting/Classification/NonnegativeProductLowSmoothDrift.lean`
nor `exists_uniformEquilibriumPayoff_of_productLowPremium` in
`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`
applies by its displayed premium hypothesis. Under nonnegative premiums,
the checked equivalence in
`UniformEquilibrium/Quitting/Classification/NonnegativeProductLowSupportPeelingConverse.lean`
also excludes an inference through weak premium support peeling.

More strongly, at annotation `(0,2,3,1)` this table has the unique exact
root `(1/2,1/2,0,0)`. The core endpoint differences are `1-2q_1` and
`4q_0-2`, independent of the outside hazards. Player 3 strictly Continues,
and at the forced core mixture player 2 gets 2 from Continue and zero
from Quit. Its successor is `(3/2,1/2,2,1)`, strictly above every singleton.
Thus the class does NOT satisfy the existing universal boxed-root return
condition: (43) deliberately retains the two core source inequalities.
The source `(0,2,3,1)` violates the pivot's such inequality. This exact
example was independently recomputed here; it is also the table in
`CODEX_HILBERT__TWO_PREMIUM_CORE_STATIONARY_AND_ROOT_CHOICE_BOUNDARY.md`.
That PARTICULAR table already has a UE by a three-player safe-spectator
lift; it is a boundary test, not claimed new coverage of that instance.

The declaration
`weakPeeling_iff_every_boxedExactRoot_singletonLowerBoundary` in
`UniformEquilibrium/Quitting/Classification/NonnegativePremiumBoxBoundary.lean`
accordingly does not contradict the theorem: it concerns all annotations
in the box, while (43) is proved only on the specified core-annotation
region and (46) is what permits the carefully chosen perturbation there.
The exact root existence input is `exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`.

The raw assumptions impose no outsider joining inequalities and no safe
spectator, response symmetry, selected passive inverse, stationary root,
or supplied F/J weights. I have NOT claimed an exhaustive search proving
that no other implemented producer subsumes this entire class. Independent
review must check both the full-root split in (43) and the selective
boundary perturbation, and separately examine source subsumption before
any export or new-coverage assertion. Both proof reviews have now passed;
the stronger rational witness and its bounded overlap checks are included
in the separate standalone assembly, without changing this strict proof.

## 11. Separate weak-leave corollary and the remaining two-core region

**Ordinary proof, not yet independently reviewed.** This section does not
change the frozen strict analytic theorem or its standalone packet.

For four players with nonnegative singletons, keep conditions 1 and 2 of
Section 10 and replace its strict inequality by

    r_i({i,j}) <= r_i({j}).                              (49)

Then a uniform-equilibrium payoff still exists. For each delta>0, change
only the NONPARTICIPANT coordinate r_i({j}) to r_i({j})+delta. No
singleton SELF reward, participant premium, or outsider participant
equality changes. The nearby table satisfies the strict theorem and is
within delta of the original table in every reward coordinate. The checked
declaration
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables` in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`
then gives uniform-payoff existence for the original table. I read its
literal statement and the surrounding reward-distance inequalities.

For completeness, fixed-target closure does not require the nearby targets
to coincide. Choose a sequence delta_n decreasing to zero and uniform
targets V_n for the nearby games. The targets stay in one compact reward
box, so a subsequence tends to V. At requested accuracy epsilon, select
one nearby game with delta_n and ||V_n-V||_infinity sufficiently small,
and use one of its uniform profiles and its one eventual horizon threshold.
For every prescribed or deviating behavioral profile and every finite
horizon, changing the reward table by delta_n changes expected average
payoff by at most delta_n, since the strategies and transition law are
the same. Thus the original game's payoff-delivery error increases by at
most delta_n+||V_n-V||_infinity and its full deviation gain by at most
2delta_n. Choosing all three margins below epsilon proves the same fixed
V works at every accuracy. No profile limit is taken.

This is ONLY a weak-leave UE corollary. It does not assert that every
ordinary C^1 exact-root potential is excluded under (49): reward closure
of the strategic conclusion is not automatically closure of that stronger
analytic property. No new closure theorem is claimed.

The zero-pair-premium case was already covered. More precisely, under
conditions 1 and 2, if either core participant has
`r_i({i,j})=s_i`, then the whole table is product-low. At an absorbing
product root, any active outsider has its constant Quit endpoint s_k.
If there is no such outsider, only the two core hazards can be positive.
If i is active, its endpoint is the mixture of s_i and r_i({i,j})=s_i;
if i is inactive, the only possible active core player j is alone and
has endpoint s_j. This covers every product root, regardless of the
core players' premiums on larger coalitions. The same argument applies
with i and j interchanged. The existing producer
`exists_uniformEquilibriumPayoff_of_productLowPremium` in
`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`
therefore consumes these zero-premium endpoints.

Consequently, within the entire nonnegative-premium/constant-outsider
two-core class, the part not closed by product-low or by the strict theorem
plus reward closure must satisfy ALL FOUR strict inequalities

    r_i({i,j})>s_i,      r_j({i,j})>s_j,
    r_i({i,j})>r_i({j}), r_j({i,j})>r_j({i}).             (50)

This is a raw-table ordering reduction, not a claim that every table in
(50) is otherwise uncovered or lacks an equilibrium. If additionally all
outsider rewards at the pair obey r_k({i,j})>=s_k, the pure pair itself
is an exact terminal equilibrium: both core players prefer joining,
and no outsider improves by joining. Thus a genuinely remaining table
also has a constant-participant outsider harmed below its singleton by
the pair. That concrete joint-pair/outsider conflict is the next question;
it is not addressed by weakening the retired local topological mechanism.

## 12. Mutual strict joining: a negative-index root forces boundary return

**Complete proof, independently reviewed PASS by CODEX_BROUWER and
CODEX_KREIN.** Ordinary
mathematics, not Lean-checked. This section does not change the independently
reviewed strict-leave export. It gives a different actual-root producer and,
combined with Sections 10–11, claims the entire two-variable-participant
class for four players. No greatest-core peeling extension is included in
the statement below.

### Exact statement and the useful root to be produced

Let I be finite and i≠j. Let r(S) be an actual finite real reward table,
and set s_k=r_k({k}). Assume r_k(S)>=s_k for all participants k in S,
and r_k(S)=s_k whenever k is outside {i,j} and belongs to S. Define

    A_i=r_i({i,j}), b_i=r_i({j}), d_i=A_i-b_i,
    A_j=r_j({i,j}), b_j=r_j({i}), d_j=A_j-b_j.

Assume for this analytic theorem that

    d_i>0 and d_j>0.                                    (51)

For any M>=0 bounding the absolute rewards and any B>M, put
K=[-B,B]^I, C=product_k[s_k,B], and
L={x in C: x_k=s_k for some k}. For q in [0,1]^I, let Pr_q(S) be the
independent product probability of coalition S, c(q)=Pr_q(empty),
a(q)=1-c(q), and T_q(v)=sum_(S nonempty)Pr_q(S)r(S)+c(q)v. Exact
root Nash means (T_q(v))_k=max(Q_k(q),C_k(q,v)) for every k, where Q
and C are the two pure-action endpoints at continuation annotation v.

**Claim.** There is no C^1 H on a neighborhood of K with

    H(v)-H(T_q(v))>=a(q)

for every v in K and every exact Nash root at v. The analytic conclusion
permits signed singletons and any finite number of players. The strategic
consequence below is specifically for four players and s>=0.

As before, EVERY exact root successor w belongs to C, even when its source
lies below some singletons: its Nash value dominates the Quit endpoint,
which is at least s, and the successor stays in K by convexity. If any
outside player k is active, its constant participant rewards imply

    w_k=Q_k(q)=s_k,

so w belongs to the SAME set L. All other hazards, including simultaneous
larger coalitions, are allowed. The new task is to produce at least one
such root, not to assert that every absorbing root returns to L.

If r_k({i,j})>=s_k for every outsider k, the pure pair itself is an exact
root at v=r({i,j}). Both core players strictly prefer joining by (51),
and every outsider prefers Continue to its constant Quit endpoint. Here
T_q(v)=v and a(q)=1, contradicting the potential immediately. Hence only
the following case needs work:

    some outsider h has r_h({i,j})<s_h.                 (52)

For this fixed table the pure core pair can NEVER be an exact root with
all outsiders inactive, at ANY continuation annotation: player h's
strict joining gain in (52) is independent of the annotation.

### A concrete fixed-point index fact, including boundary roots

We use the following elementary consequence of finite-dimensional degree.
Let F:R^n->[0,1]^n be continuous. Suppose its only fixed point is p and
F is C^1 near p with det(I-DF(p)) nonzero. Then

    sign det(I-DF(p))=+1.                               (53)

Here p may lie on the boundary of [0,1]^n. To prove (53), use the larger
open cube U=(-1,2)^n and choose z=(1/2,...,1/2). For t in [0,1],

    H_t(q)=q-[(1-t)F(q)+tz]

has no zero on the boundary of U, since the bracket is in [0,1]^n.
Its degree is therefore constant in t. At t=1 it is the translated
identity, of degree +1. Thus q-F(q) has total degree +1 on U.

Let D=I-DF(p). Invertibility gives m>0 with ||Du||>=m||u||.
Differentiability gives, in a sufficiently small ball about p,

    ||(p+u-F(p+u))-Du|| <= (m/2)||u||.

The straight-line homotopy from q-F(q) to D(q-p) therefore has no
zero on the ball's boundary. Its local degree is sign det D. Since p
is the only root, excision identifies this local degree with the total
degree +1. This proves (53). No parity specification, Nash-index axiom,
or root-count assertion is a premise: all maps and isolating homotopies
have just been supplied. Boundary coordinates of p cause no half-index,
because p is an interior point of the larger ambient cube U.

The required degree tools already have source declarations:
`ambientDegree_homotopy` and `ambientDegree_affineRootField_eq_sign_det`
in `MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`,
`ambientDegree_excision` in `MathUE/Topology/AmbientDegreeProperties.lean`,
and `ambientDegree_of_selfMap_eq_one` in
`MathUE/Topology/AmbientDegreeSelfMapNormalization.lean`. Their literal
statements were inspected. The derivative-to-affine comparison above is
given explicitly; no absent nonlinear-index adapter is being invoked as
an established game producer.

### All roots without an active outsider

For a fixed annotation v, define the polynomial endpoint gap

    g_k(q)=Q_k(q)-C_k(q,v)

using the independent coalition formulas, extended polynomially to all
q in R^I. Define the ACTUAL continuous self-map

    F_v(q)_k = min(1,max(0,q_k+g_k(q))).                 (54)

Every fixed point lies in the unit cube, and the coordinate conditions
for a fixed point are exactly the two-action Nash conditions: g_k<=0
at q_k=0, g_k>=0 at q_k=1, and g_k=0 in the interior. Thus the fixed
points of (54) are precisely all full exact Nash roots at v.

On the face where all outsider hazards vanish, the two core gaps are

    g_i(q)=s_i-v_i+(v_i-s_i+d_i)q_j,
    g_j(q)=s_j-v_j+(v_j-s_j+d_j)q_i.                    (55)

These formulas are used only on that face. In the full map, all triple
and larger coalition terms are retained.

If either core annotation, say v_i, is strictly below s_i, then (55)
is positive for every q_j in [0,1]: it is the convex combination of
s_i-v_i>0 and d_i>0. Exact Nash would force q_i=1, and then d_j>0
forces q_j=1. Condition (52) rules this out. Hence in this case EVERY
exact root has an active outsider.

Now suppose v_i>s_i and v_j>s_j. A root supported on the core cannot
have exactly one active player, since that player's gap against the
other's zero hazard is strictly negative. If either core hazard is one,
the other is forced to one by (51), again ruled out by (52). Apart from
all-Continue, the ONLY possible root without an active outsider is

    p_i=(v_j-s_j)/(v_j-s_j+d_j),
    p_j=(v_i-s_i)/(v_i-s_i+d_i),
    p_k=0 for k outside {i,j}.                          (56)

Both core coordinates lie strictly between zero and one. In particular
c(p)=(1-p_i)(1-p_j)>0.

Suppose some source coordinate is below its singleton, so all-Continue
is not Nash, and suppose no outsider has g_k(p)=0. If an outsider has
g_k(p)>0, p is not Nash either; finite Nash existence then already gives
a root with an active outsider. Otherwise all outsider gaps at p are
strictly negative. The map (54) is C^1 near p: its outsider rows are
locally constant zero, and its two core rows are locally q_k+g_k(q).

Order the two core coordinates first. The Jacobian of q-F_v(q) at p
has the block form

    [[0, -alpha_i, *],
     [-alpha_j, 0, *],
     [0,         0, Id]],

where alpha_i=v_i-s_i+d_i>0 and alpha_j=v_j-s_j+d_j>0. Its determinant
is -alpha_i*alpha_j<0. Cross-derivatives in the starred columns may be
arbitrary: the identity outsider block makes them irrelevant to the
determinant. By (53), p cannot be the only full fixed point. Every other
fixed point must have an active outsider, by the exhaustive classification
above. It follows that

    core annotations strictly above solos,
    some annotation strictly below its solo,
    g_k(p) nonzero for all outsiders
        => an exact root with an active outsider exists. (57)

This is a produced root from the full finite game, not a conditional
selection interface. It retains all original rewards and changes no
outsider's action constraints.

### Boundary minimization and exact tie removal

Assume H exists and minimize it at x on L. Let J={k:x_k=s_k}.
The case |J|=1 is impossible without any index argument: the sole
binding player can Quit with sufficiently small positive probability,
while all others strictly prefer Continue. This exact root has its
owner successor coordinate equal to its singleton and hence returns to
L with positive absorption, contradicting minimality.

Thus |J|>=2. Feasible one-sided variations give g^H_k>=0 for k in J,
where g^H=gradient H(x). Nonbinding interior gradients vanish and
upper-box gradients are nonpositive, although only the binding signs
are needed below.

If J meets the core, set v_epsilon=x-epsilon*1_J. At least one core
annotation is below its solo. By (55),(52), every exact root at this
source has an active outsider. Finite Nash existence produces one, and
its successor lies in L.

If J avoids the core, then x_i>s_i and x_j>s_j. Keep those two
coordinates EXACTLY unchanged, so the mixed candidate p in (56) does
not depend on any outsider annotation. For each outsider k choose

    0<eta_k<epsilon^2,
    v_epsilon,k=x_k-epsilon*1_(k in J)-eta_k.            (58)

Choose eta_k so that g_k(p) is not zero. This is always possible:
Q_k(p)=s_k by the constant-participant hypothesis, while

    C_k(p,v)=sum_(nonempty T subset {i,j})p_p(T)r_k(T)
                   +c(p)v_k.

Since c(p)>0, equality g_k(p)=0 forbids at most one eta_k in the whole
interval (0,epsilon^2). The choices are coordinatewise independent.
Every binding outsider is still at least epsilon below its singleton,
so all-Continue is not Nash. Condition (57) supplies a full exact root
with an active outsider. Its successor again lies in L.

In both cases sources remain in K for small epsilon: x>=s>=-M and
B>M leave a fixed lower clearance, and all perturbations decrease
coordinates. The table and the strict pair-blocking inequality (52)
never change. Moreover

    [H(v_epsilon)-H(x)]/epsilon
        -> -sum_(k in J) g^H_k <=0.                     (59)

In the second case the extra perturbation has norm O(epsilon^2), even
though it need not depend continuously on epsilon. This is enough for
(59). Every chosen exact successor w_epsilon belongs to C and, by its
active constant-participant outsider, to the original L.

Take any k in J. The source has v_epsilon,k<=s_k-epsilon while
w_epsilon,k>=s_k. The actual displacement formula therefore gives

    epsilon<=(M+B)a_epsilon.

Potential drift and minimality on the SAME L give

    epsilon/(M+B)<=a_epsilon
       <=H(v_epsilon)-H(w_epsilon)<=H(v_epsilon)-H(x),

contradicting (59). This proves the analytic claim under (51).

### Exact test: the negative-index root really can be present

The following three-player table tests the index step within its claimed
finite-player analytic scope. Its core is {0,1}, and player 2 has constant
participant payoff zero:

    r({0})=(1,-1,3), r({1})=(0,0,3), r({2})=(3,3,0),
    r({0,1})=(2,1,-1), r({0,2})=(1,3,0),
    r({1,2})=(3,0,0), r({0,1,2})=(1,0,0).

Here d_0=d_1=2, and the pure pair harms player 2. At the annotation
v=(2,1,-1/10), the root p=(1/3,1/3,0) is genuinely full exact Nash:
its endpoint gaps are (0,0,-53/45). Its successor is
(4/3,1/3,53/45), strictly above every singleton. The ambient fixed-point
Jacobian in the proof has determinant -9. Thus the bad root cannot be
discarded just by checking outsider incentives or insisting that ALL roots
return to L. The different root (0,0,1) has gaps (-2,-3,1/10), is exact
Nash, and has successor (3,3,0) in L. I independently computed these
identities with exact rational polynomial arithmetic. They confirm the
intended selection rather than universal-return quantifier; the degree
proof, not this fixture, supplies that selection for arbitrary tables.

### Combined four-player theorem and remaining research boundary

**Proposed complete raw-class conclusion.** Every four-player quitting
game with nonnegative own singleton rewards, nonnegative participant
premiums, and at most two players whose participant rewards are
nonconstant has one uniform-equilibrium payoff against every complete
behavioral deviation. No comparison between pair and passive singleton
rewards is an additional hypothesis.

Indeed choose a designated pair containing all possible variable
participant players. If A_i<=b_i or A_j<=b_j, Section 11 applies,
interchanging the core labels when necessary. Otherwise (51) holds,
and the analytic theorem just proved combines with the SAME normal
Fin4 polynomial producer and exact-root restriction as Section 10.
If all s_k=0, all-Never handles the conclusion directly. The target is
fixed before accuracy by those existing semantic consumers.

This statement is broader than the frozen strict-leave theorem and has
passed independent review. Its key new producer is (57), with
the literal map (54), computed local determinant, and explicit ambient
index normalization. The greatest-premium-core peeling mechanism may
later replace the globally constant outsider assumption, but has NOT
been used in this proof. The next requested check is to falsify the
negative-index root production and the O(epsilon^2) tie removal while
retaining the exact target boundary L.

## 13. Transfer to the greatest premium core of size at most two

**Complete composition, independently reviewed PASS by CODEX_BROUWER and
CODEX_KREIN.** This section
uses the new Section 12 proof and the finite support observation developed
by CODEX_BROUWER in the section “Canonical premium-core reduction” of
`CODEX_BROUWER__QUITTING_TABLE_COVERAGE.md`. I checked the finite argument
and its exact source predicates independently. It is not part of either
frozen export and is not a claim about premium cores of size three or four.

### Canonical raw condition

Let a finite table have nonnegative participant premiums, with singletons
s_k=r_k({k}). Call a nonempty A a premium trap if every k in A has some
coalition S contained in A, containing k, with r_k(S)>s_k. Its witnessing
coalition may depend on k. Traps are union-closed: the old witnesses
remain valid in a union. Hence the union C of all traps is either empty
or the greatest trap. A singleton is never a trap.

This C is also the result of repeatedly deleting from the current player
set a player whose participant rewards on its current subtable are all
its singleton. No trap can lose its first member, because that member
would retain a positive witness inside the trap. A nonempty terminal
residual is itself a trap, because every surviving player has a witness.
Thus every deletion order ends at the same C. These are deletions in a
finite reward-relation calculation, NOT deletion of actual game players.

**Proposed four-player theorem.** If s>=0, participant premiums are
nonnegative, and this greatest premium core has at most two players,
the ORIGINAL four-player quitting game has a uniform-equilibrium payoff
against unrestricted behavioral deviations, with its target fixed before
accuracy. Players outside C may have positive premiums on larger
coalitions, so global constant-participant payoffs are not assumed.

### The two exact replacement facts

The empty-core case is existing product-low coverage: every nonempty
active support A has a player k flat on all participant coalitions inside
A. Its supported Quit endpoint is exactly s_k. This proves product-low
on every absorbing product root. The exact equivalence is
`hasProductLowQuittingPremium_iff_weakSupportPeeling_of_nonnegative` in
`UniformEquilibrium/Quitting/Classification/NonnegativeProductLowSupportPeelingConverse.lean`.

Suppose C={i,j}. Both pair participant premiums are strictly positive,
because the pair is the only possible positive witness for either of its
members inside C. Two facts replace the global outsider equalities:

1. At any positively absorbing root whose active support A is not C,
   A is not a trap. If it were a trap it would be contained in C, and
   the only nonempty proper subsets of C are singletons, which are not
   traps. Thus some active k is flat on EVERY participant coalition
   inside A. Conditional on k Quitting, its actual coalition is contained
   in A, so Q_k(q)=s_k. Exact Nash gives successor coordinate s_k.
   The full successor still belongs to the same L by nonnegative
   participant premiums and the box bound. Hence every root with support
   other than C returns to L; no player with a positive hazard is ignored.
2. For every outsider k and every T contained in C,

       r_k(T union {k})=s_k.                            (60)

   Otherwise that positive premium, together with the pair witnesses
   of i and j, would make C union {k} a larger premium trap. Thus on
   every core-only root, every inactive outsider's forced-Quit endpoint
   is exactly s_k. This fact is distinct from global outsider flatness;
   it permits positive premiums requiring another outsider.

The source definitions inspected were `HasWeakQuittingPremiumSupportPeeling`
and `hasWeakQuittingPremiumSupportPeeling_iff` in
`UniformEquilibrium/Quitting/Classification/QuittingPremiumSupportPeelingOrder.lean`,
and `HasFiniteCoalitionSupportPeeling` in
`MathUE/FiniteCoalitionSupportPeelingOrder.lean`. They require a flat
member in every nonempty support, which is exactly the empty-core case.
The residual pair is genuinely beyond that displayed source assumption.

### Proof transfer without a missing root or degree hypothesis

For strict leave, Fact 1 handles every support except C, and the strict
core endpoint gap excludes support C when the leaving annotation is at
least its singleton. Thus the full-root return and selective minimizer
perturbation of Section 10 hold without any further change. This is
BROUWER's proved pair-core strict-leave extension.

For mutual strict joining, use the actual map F_v of Section 12 on ALL
players and the same lower boundary L. Fact 2 shows that the pure pair
is exact Nash when its passive outsider rewards are at least s; otherwise
there is the same table-fixed strict blocker (52). The core-only gap
formulas and their unique mixed candidate are unchanged, since no outsider
has a positive hazard on that face.

In the minimizer case where a binding core coordinate is lowered,
support C is impossible by the strict-join calculation and the pure-pair
blocker. All-Continue is impossible as well, and finite Nash existence
therefore supplies a root whose support differs from C. Fact 1 returns
its full successor to L.

In the case with only outsider bindings, the O(epsilon^2) tie removal
is still legal because Fact 2 gives Q_k(p)=s_k, while the Continue
endpoint retains the positive coefficient c(p) on the outsider annotation.
If the mixed candidate is not Nash, a different root exists. If it is
Nash, all outside gaps are strictly negative; their rows of the clipped
map are locally constant zero even when their derivatives before clipping
involve other outside hazards and positive layered premiums. The same
block-triangular Jacobian has determinant -alpha_i*alpha_j. Its negative
local index and total index +1 force a different full root. All-Continue
and the blocked pure pair are impossible, so Fact 1 again puts the
selected successor in the original L. The directional and absorption
contradiction is literally the one in Section 12.

No core-only equation has been applied to a root with a positive outsider
hazard. Such roots are consumed by Fact 1, retaining every coalition.
No new root-selection hypothesis, degree computation, or conditional
interface remains to be supplied in this transfer.

Finally equality in either pair-leave comparison is handled by increasing
only its passive singleton coordinate by delta. This changes NONE of the
participant premiums, traps, greatest core, or singletons. The nearby
table has strict leave, and the existing reward-closure theorem in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`
gives a fixed-target UE for the original table. Together, strict leave,
equality, and mutual strict joining cover every pair ordering. The exact
Fin4 polynomial consumer and normality argument are unchanged.

Therefore a four-player
counterexample with nonnegative singletons and nonnegative participant
premiums must have greatest premium core of size at least three. This
does not yet address tables with negative participant premiums or the
size-three/four core. BROUWER's independently found size-three example
has a unique interior-successor root of index +1, so that next region
requires a new mechanism rather than another assertion of negative index.

## 14. A common strict leaver in every premium trap

Status: complete ordinary proof, not independently reviewed or Lean-checked.
This is an actual finite reward-table criterion, not an assumed selector
or index interface. It extends the strict-return mechanism to some
three- and four-player premium cores. It does not extend the negative
index claim refuted by the three-core example.

### Raw hypotheses and conclusion

Let I be finite and nonempty. For every nonempty S⊆I let r(S)∈ℝ^I,
put s_i=r_i({i}), and assume r_i(S)≥s_i whenever i∈S. A premium trap is
a nonempty A⊆I such that each i∈A has some S⊆A containing i with
r_i(S)>s_i. Let C be the union of all premium traps, or ∅ if none exist.
Unions of traps are traps, since each member retains its witness.

Suppose there is a player p such that:

1. Every premium trap contains p. Equivalently, the subtable on I\{p}
   has weak premium support peeling: in every nonempty A⊆I\{p} some
   k∈A has r_k(S)=s_k for every S⊆A containing k.
2. For every nonempty T⊆C\{p},

       r_p(T∪{p}) < r_p(T).                            (61)

No condition is imposed on passive rewards at coalitions outside C.
In particular, (61) is not global pointwise domination of p's Quit
strategy, and it supplies no automatic quiet lift of the whole deleted
subgame. C may have any cardinality, and outsiders may have layered
positive participant premiums on supports which are not traps.

For |r_i(S)|≤M and B>M there is no C¹ full exact-root
potential H on [-B,B]^I satisfying

       H(T_q(v)) ≤ H(v)−a(q)                           (62)

for every v in that box and every exact Nash root q at annotation v.
Here a(q)=1−∏_i(1−q_i), and T_q(v) is the actual one-step payoff with
continuation v if all players Continue. Singleton rewards may be signed
in this analytic statement.

For I=Fin 4 and all s_i≥0, the raw hypotheses imply one fixed
uniform-equilibrium payoff against all behavioral deviations. In this
strategic conclusion only, (61) may be weakened to ≤ by reward closure.
No weak-comparison C¹ exclusion is asserted.

### Every exact root returns while one floor is protected

Let q be an absorbing exact Nash root with v_p≥s_p. Nonnegative
participant premiums imply Q_i(q)≥s_i for every forced-Quit endpoint.
Exact Nash therefore gives w_i=T_q(v)_i≥s_i for every i.

Let A={i:q_i>0}. If A is not a premium trap, some active k is flat on
every participant coalition inside A. Conditional on k Quitting, all
realized coalitions lie inside A, even if many other players have
positive hazards. Consequently Q_k(q)=s_k, and active-player Nash
equality gives w_k=s_k. This branch uses the full root, including all
larger coalitions.

If A is a trap, then p∈A⊆C. Conditional on p's action, the other
quitting coalition T is a product draw inside A\{p}. On T=∅, its
Quit-minus-Continue difference is s_p−v_p≤0. On every nonempty T the
difference is strictly negative by (61). A trap cannot be a singleton,
so another player has positive hazard. The nonempty-T event has
positive probability, including when some hazards equal one. Hence
Q_p(q)−Continue_p(q)<0, contradicting q_p>0 at an exact Nash root.

Thus every absorbing exact root whose source satisfies v_p≥s_p has
its successor on the SAME singleton lower boundary

       L={x∈∏_i[s_i,B]: some x_i=s_i}.                 (63)

The upper bound follows because every reward and source coordinate is
at most B. This is a source-restricted full-root statement; it does not
claim universal return at annotations with v_p<s_p.

### Charged minimization contradiction

Assume H as in (62), and minimize H on the compact nonempty L at x.
Write g=∇H(x), and J={i:x_i=s_i}. Small sole-owner exact roots, followed
by a limit from strict other-coordinate floors, give for every j∈J

       g·(x−r({j}))≥1.                                (64)

For completeness, at a point with only j binding a sufficiently small
sole-j hazard is exact Nash: j is indifferent, and every other player's
strict continuation-floor surplus dominates the vanishing collision
term. Its successor is x+t(r({j})−x), and its absorption is t.
Divide (62) by t and let t decrease to zero. A point with several
bindings is approached by raising the other binding coordinates;
continuity of the derivative gives the same face inequality at x, as in the
existing full-root singleton-face drift theorem.

There cannot be only one binding j. In that case all other interior
partials vanish; at an upper face, g_i≤0 and B−r_i({j})>0. The j
component of x−r({j}) is zero. Thus the left side of (64) is ≤0.
Therefore |J|≥2. Every binding partial g_j is nonnegative, since j
can be increased while another coordinate remains binding.

Choose k∈J with k≠p, and set v_ε=x−εe_k. For small ε>0 this is in
[-B,B]^I, with its p floor unchanged. All-Continue is not Nash because
v_{ε,k}<s_k. Finite normal-form Nash existence supplies an absorbing
exact root q_ε; by the preceding proof its successor w_ε lies in L.
Also w_{ε,k}−v_{ε,k}≥ε. One-step averaging gives

       |w_{ε,k}−v_{ε,k}|≤(M+B)a(q_ε).

Minimality and (62) imply

       [H(v_ε)−H(x)]/ε ≥ 1/(M+B)>0.

The left side tends to −g_k≤0, a contradiction. There is no adaptive
root-selection hypothesis: every root at this source has the required
return. No degree argument, genericity, or inactive-gap tie removal is
used.

The source's direct directional face argument also establishes a
version requiring only differentiability at boundary points. The C¹
statement proved here is enough for the polynomial consumer; no
regularity strengthening is needed for the new raw coverage.

### Exact semantic consumer and weak comparison

If all four singleton payoffs vanish, all-Never is exact Nash: against
all-Never, any unilateral stopping law yields that player's zero
singleton or zero perpetual payoff. Otherwise some singleton is
positive. Nonnegative singleton rewards give normality. The existing
no-UE theorem then produces a rational robust polynomial on the full
relation in the box B=M+2. Its exact-root restriction satisfies (62),
contradicting the preceding proof. This gives a payoff target fixed
before the accuracy; deviations are unrestricted behavioral strategies,
not merely the roots used to exclude the obstruction.

For weak (61), increase by δ>0 only the passive coordinate r_p(T),
for nonempty T⊆C\{p}. Participant coordinates, all singleton own
rewards, every trap, and C remain unchanged. The modified tables satisfy
strict (61) and converge uniformly to r. The existing reward-closure
theorem gives a fixed-target UE at r. This is reward closure of the
strategic conclusion, not closure of the analytic potential exclusion.

### A rational three-core fixture outside the named screens

Take I={0,1,2,3}. The complete table is:

| S | r(S) |
|---|---|
| 0 | (1,−1,−1,−1) |
| 1 | (11/10,0,2,−1) |
| 2 | (0,−1,0,2) |
| 3 | (5/2,2,−1,0) |
| 01 | (1,1/2,−1,−1) |
| 02 | (1,−1,0,−1) |
| 03 | (2,−1,−1,1) |
| 12 | (0,0,0,1) |
| 13 | (5/2,0,1,0) |
| 23 | (5/2,1,0,0) |
| 012 | (1,0,0,−1) |
| 013 | (1,0,−1,0) |
| 023 | (1,−1,0,0) |
| 123 | (5/2,0,0,0) |
| 0123 | (1,0,0,0) |

The only positive participant premiums are those of 0 and 3 at 03
and that of 1 at 01. Thus C={0,1,3}; all traps contain p=0, whereas
the table without 0 has no trap. Condition (61) has exactly three
instances: 1<11/10 at T={1}, 2<5/2 at T={3}, and 1<5/2 at
T={1,3}. Player 2 is flat. The full table is not weakly peeling, and
the product root with q_0=q_3=1/2 has strictly positive premiums for
both active players. Hence neither product-low nor core≤2 covers it.

The centered singleton matrix is

       Γ=[[0,1/10,−1,3/2],
          [−1,0,−1,2],
          [−1,2,0,−1],
          [−1,−1,2,0]].                               (65)

Its child A on 123 has determinant 7, A·1=1, and
A⁻¹=(1/7)[[2,4,1],[1,2,4],[4,1,2]]. In any child complementarity
problem Az≥t·1 with t>0, no coordinate can vanish: a zero followed
round the directed three-cycle forces two positive coordinates and
then a negative active row. Therefore z=t·1 uniquely. At t=0 the
same argument excludes any nonzero homogeneous solution.

For a homogeneous full problem, pivot variable h>0 would force
z=h·1, but the pivot residual is (3/5)h>0. For h=0 the child gives
z=0. Thus Γ is R₀. At offset (1,−1,−1,−1), the child equations give
z=(1+h)·1, and the pivot residual is 1+(3/5)(1+h)>0. The only root
is (0,1,1,1), its inactive residual is 8/5, and its active determinant
is 7. Thus the existing degree-sum theorem gives degree 1, not the
singleton-degree exclusion. The principal 02 matrix [[0,−1],[−1,0]]
is R₀: either nonzero axis violates the opposite row, and two positive
coordinates cannot have zero residuals. It is not Q: at offset
(−1,−1), its first inequality requires −x_2≥1. The principal 01
matrix is not an R₀ witness: (0,1) is a nonzero homogeneous solution
with residual (1/10,0).

The only nonnegative-inverse triple is 123. Its passive pivot row is

       (1/10,−1,3/2) A⁻¹=(26/35,−1/70,−9/70),

so the weak passive-inverse hypothesis fails. For the other triples,
explicit negative inverse entries are respectively −20/21 for 012,
−15/13 for 013, and −1/2 for 023. The full inverse has entry
(Γ⁻¹)_{0,1}=−26/21. No pair has two positive off-diagonal entries.

The necessary first-order response-partition test leaves only 0|123.
Here is one unequal block-row sum for each of the other thirteen
nondiscrete partitions; the two displayed rows belong to the same
target block, and the sums are over the indicated source block:

| Partition | Rows | Source block | Sums |
|---|---|---|---|
| 01 / 2 / 3 | 0,1 | 01 | 1/10,−1 |
| 1 / 02 / 3 | 0,2 | 1 | 1/10,2 |
| 1 / 2 / 03 | 0,3 | 1 | 1/10,−1 |
| 0 / 12 / 3 | 1,2 | 12 | −1,2 |
| 012 / 3 | 0,1 | 012 | −9/10,−2 |
| 12 / 03 | 1,2 | 12 | −1,2 |
| 0 / 2 / 13 | 1,3 | 2 | −1,2 |
| 02 / 13 | 0,2 | 13 | 8/5,1 |
| 2 / 013 | 0,1 | 013 | 8/5,1 |
| 0 / 1 / 23 | 2,3 | 1 | 2,−1 |
| 01 / 23 | 0,1 | 01 | 1/10,−1 |
| 1 / 023 | 0,2 | 1 | 1/10,2 |
| 0123 | 0,1 | 0123 | 3/5,0 |

For 0|123, the actual three child response residuals at the root
(t,0,0,0) are t+t²/2, t, and t+t². Thus the full response relation
breaks the remaining partition. Singleton first-order compatibility
alone has not been substituted for response invariance.

No pure quitting coalition is equilibrium. Explicit improving players
for coalitions in the table's displayed order are respectively
1,3,0,2,0,1,0,2,1,3,3,0,0,1,0. The improvement is immediate when
the player joins, or when a nonsingleton participant Continues while
the remaining coalition quits.

Every nonempty proper child also has an exact terminal-Nash profile
whose quiet lift gives an omitted player a positive gain. For children
1,2,3 use their sure singleton. For 12,13,23 use respectively sure
1,3,2. For 01 and 012 use sure 1; for 03 and 013 use sure 3. For 0 use
sure 0; for 02 let both members quit surely. In each case the chosen
participants have no profitable withdrawal or join inside the child,
and an omitted nonpivot with payoff −1 can join to receive at least 0.
For 123 repeat sole hazards 1/2 in the order 1,2,3. Every child's
phase value is nonnegative, each active player and its continuation
have value zero, so the full behavioral Snell comparison is exact.
The lifted initial payoff is (69/70,0,1,0); pivot 0 can quit at the
first phase for payoff 1, gaining 1/70.

For the remaining child 023, use one date with hazards
(q_0,q_2,q_3)=(2/3,1,2/5), then Never. The literal Continue/Quit
endpoint pairs for players 0,2,3 are (1,1), (−4/5,0), and (0,0).
Thus it is exact child Nash and absorbs surely. Omitted player 1 has
Continue value −11/15 and Quit value 0. These are full endpoint
checks, not a restriction to a chosen class of deviations.

The three-core unique-root falsifier remains intact and outside this
new statement: its r_0({1})=0 is below r_0({0,1})=1, violating (61).
Its sole root of index +1 therefore does not contradict the protected
floor return proved here. Conversely, no claim is made that the new
criterion treats every three-core table.

### Named source overlap and next question

The newly present declarations
`exactRootSuccessor_mem_singletonLowerBoundary_of_twoPlayerPremiumCore_strictLeave`
in `UniformEquilibrium/Quitting/Classification/TwoPlayerPremiumCoreExactRootBoundary.lean`,
`not_isQuittingFullExactRootPotential_of_twoPlayerPremiumCore_strictLeave`
in `UniformEquilibrium/Quitting/Classification/TwoPlayerPremiumCoreSmoothDrift.lean`,
and `exists_uniformEquilibriumPayoff_of_twoPlayerPremiumCore_strictLeave`
in `UniformEquilibrium/Quitting/Classification/Existence/TwoPlayerPremiumCoreUniformPayoff.lean`
were read directly. They require globally flat participants outside one
pair, which the fixture does not satisfy. Their strengthened dependency
on only the leaving player's source floor is exactly what the new
trap argument uses; their lower-boundary minimizer proof already lowers
one different binding coordinate. No formalization status is claimed
for the new raw hypotheses or the trap reduction.

`hasWeakQuittingPremiumSupportPeeling_iff` in
`UniformEquilibrium/Quitting/Classification/QuittingPremiumSupportPeelingOrder.lean`
requires a flat player in EVERY full support. Here it holds only after
deleting p. `weakPeeling_iff_every_boxedExactRoot_singletonLowerBoundary`
in `UniformEquilibrium/Quitting/Classification/NonnegativePremiumBoxBoundary.lean`
concerns universal return at every source; the new statement protects
one source floor instead. The exact-root/polynomial/closure consumers
are the same named declarations inspected in Sections 10–13. Matrix
degree, passive inverse, and full response partition computations above
refer to their existing hypotheses, not to a claimed classification of
all possible constructions.

KREIN's separately reviewed one-joint-phase family does not supply this
fixture through either premium pair: for pair 01 its pivot participant
premium is zero and its passive singleton is 11/10>1; for pair 03 its
participant payoff is 2, below the passive singleton 5/2. Both violate
the raw condition that the selected pivot's pair payoff is at least
its passive partner-singleton payoff. This is only a comparison with
that family's stated hypotheses, not with every possible phase law.

Next check: independently falsify the raw trap/support implication and
the protected-floor minimizer, then test the exact three-core fixture
against the named source screens. The larger residual is still the
three-core region where every common trap member has some profitable
join comparison, including the retained unique-root example; finding a
second root at that refuted source is not the proposed mechanism.

## 15. Signed premiums away from the protected player

Status: separate complete ordinary proof, not independently reviewed or
Lean-checked. Section 14 remains unchanged during its review. This
section changes the raw coverage, not only a constant: participant
premiums of every player other than the designated p can now be
negative.

### Exact raw statement

Let I be finite and nonempty, with a real reward vector r(S) for every
nonempty coalition and s_i=r_i({i}). Define a premium trap by the
same strictly positive own-premium witnesses as in Section 14, even
when negative premiums also occur. Let C be the union of all traps.
Assume there is p∈I such that:

1. r_p(S)≥s_p for every S containing p; this assumption is made ONLY
   for p.
2. Every premium trap contains p.
3. r_p(T∪{p})<r_p(T) for every nonempty T⊆C\{p}.

There is no participant-reward restriction for i≠p. In particular,
the failure of A to be a trap means that some k∈A has r_k(S)≤s_k
for all S⊆A containing k, not that these rewards are all equal.

For every |r_i(S)|≤M and B>M, no C¹ full exact-root potential (62)
exists. For I=Fin 4 with all s_i≥0, there is a uniform-equilibrium
payoff with the usual fixed-target and unrestricted behavioral-deviation
quantifiers. For this strategic conclusion, condition 3 can be weak.

### The correct minimization domain and full-root return

Use the compact nonempty domain

       D={v∈[-B,B]^I : v_p≥s_p and some v_i≤s_i}.       (66)

It is important NOT to use only L: with signed premiums an active
player's exact successor can lie strictly below its singleton. L is
contained in D, but a returned root need not lie on L.

For any boxed source v with v_p≥s_p, every absorbing exact root has
its successor w in D. Indeed, Q_p(q)≥s_p by condition 1, and exact
Nash gives w_p≥Q_p(q), regardless of whether p is active. If active
support A is a trap, then p∈A⊆C; averaging condition 3 over every
actual nonempty opponent coalition, and s_p−v_p≤0 on the empty
coalition, makes p strictly prefer Continue. As before, another player
has positive hazard because no singleton is a trap, so the strict
event has positive probability. This contradicts p being active.

Consequently A is not a trap. Choose an active k all of whose
participant rewards inside A are at most s_k. Its forced-Quit endpoint
is at most s_k, and active-player Nash equality gives w_k≤s_k.
Together with w_p≥s_p and the ordinary box bound, this proves w∈D.
All simultaneous outsider hazards and their larger coalitions are
retained in this argument. The witness k need not be fixed across
roots and may itself be p.

### A minimum is first forced back onto L

Assume H satisfies (62), and let x minimize H on D. If x_k<s_k
for any k, all-Continue is not Nash at annotation x. Every exact root
provided by finite Nash existence therefore absorbs positively. Its
successor lies in D by the preceding return theorem, contradicting
H(w)≤H(x)−a(q)<H(x). Hence x_i≥s_i for all i.

Membership in D now forces some equality, so x∈L. Since L⊆D,
x also minimizes H on L. The singleton-face drift theorem is valid
for arbitrary signed reward tables; it requires no nonnegative-premium
hypothesis. Thus (64) holds at every binding coordinate. The same
box-face argument as in Section 14 excludes only one binding, and
every binding partial is nonnegative. Choose a binding k≠p, and put
v_ε=x−εe_k. This preserves p's floor. Every exact root at v_ε
returns to D, not necessarily to L. Minimality on the ORIGINAL D
still gives H(w_ε)≥H(x).

The old inequality w_{ε,k}≥s_k is unavailable and is not used.
Instead, write a=a(q_ε) and let a_{−k} be the probability that at
least one opponent quits. When no opponent quits, k's forced-Quit
reward is s_k; on the remaining event every reward differs from s_k
by at most 2M. Therefore

       Q_k(q_ε)≥s_k−2M a_{−k}≥s_k−2M a.

Exact Nash gives Q_k(q_ε)≤w_{ε,k}. One-step averaging, independently
of all premium signs, gives

       w_{ε,k}≤v_{ε,k}+(M+B)a
                =s_k−ε+(M+B)a.

Combining them yields the quantitative charge

       ε≤(3M+B)a.                                    (67)

The coefficient is positive because B>M≥0. Together with (62) and
minimality on D,

       [H(x−εe_k)−H(x)]/ε ≥ 1/(3M+B)>0.

Its limit is −∂_kH(x)≤0. This is the contradiction. Neither a
nonnegative premium for the perturbed player nor a return to L was
silently restored. The proof uses D twice for distinct purposes:
first to eliminate below-singleton minima, then to compare the possibly
below-singleton successors of the perturbed roots.

### Fin4 consumer, weak comparison, and a signed fixture

The polynomial obstruction producer assumes normality and one positive
singleton, not nonnegative participant premiums. The directly inspected
`isQuittingNormalPlayer_of_singleton_nonneg` in
`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`
supplies normality from s_i≥0 alone. The signatures and proof of
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`
and `isQuittingFullExactRootPotential_of_robustPotential` in
`UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`
were rechecked: neither needs the absent premium assumptions. Thus the
same rational polynomial would contradict the C¹ exclusion above.
If all singletons vanish, all-Never is exact Nash as before. No equality
between punishment values and singleton rewards is needed here.

The directly inspected
`IsQuittingFullExactRootPotential.singletonFace_drift` in
`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`
also has no premium-sign hypothesis. Its actual singleton probe handles
collision rewards and box corners, so no positive-premium face adapter
is being reused outside its assumptions.

Weak condition 3 is handled by adding δ>0 to the passive coordinate
r_p(T) for each nonempty T⊆C\{p}. No participant reward or own
singleton changes, so conditions 1 and 2 and the whole trap collection
are unchanged. Existing uniform-payoff reward closure gives the weak
strategic conclusion; it says nothing about weak C¹ exclusion.

An exact signed-premium example is the complete Section 14 table with
only r_2({0,2}) changed from 0 to −1/10. Its positive premium traps
and C={0,1,3} do not change. Player 0 still satisfies condition 1, and
all three leave inequalities remain strict. This table is outside the
global-nonnegative-premium class as well as the earlier core≤2 class.
Its singleton matrix, degree 1, inverse failures, and response-partition
first-order failures remain unchanged. At (t,0,0,0), the child response
residuals are now t+t²/2, t−t²/10, and t+t², still excluding the sole
first-order partition 0|123. The pure-coalition improving players listed
in Section 14 retain their improvements.

The stated proper-child profiles remain exact, with two changed values:
child 02's sure participant 2 gets −1/10, still above its withdrawal
payoff −1; in child 023 the participant-2 Quit endpoint becomes −1/25,
still above its Continue endpoint −4/5. All other relevant endpoint
comparisons and every omitted-player improving deviation are unchanged.
This does not assert that a negative own payoff is protected by a
singleton floor; the explicit behavioral endpoint comparisons, including
the prescribed sure exit, are what establish these child claims.

Next requested check: independently verify preservation of p's floor,
the exact signed return to D, and the no-premium charge estimate (67).
Section 14 is not modified or presumed reviewed by this extension.
