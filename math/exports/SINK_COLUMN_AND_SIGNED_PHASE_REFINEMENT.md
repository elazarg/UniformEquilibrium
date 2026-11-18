# Finite decision for vanishing-collision equilibria after a column deletion

Consider four players with positive own singleton rewards, bounded finite
rewards, and zero live and Never rewards. In native coordinates set
Γ_ij=r_i({j})−s_i and J_ij=r_i({i,j})−s_i, with Γ_ii=0.
Let e be the largest original terminal unilateral improvement and C the
on-path probability of a multiple first quit. Assume all off-diagonal
Γ_ij are nonzero and each of the full and three-owner principal matrices
has trivial kernel on its nonnegative cone. Define K_ip=min(J_ip,max(0,Γ_ip)).
Include the arc p→j for p≠j exactly when Γ_jp≥K_jp and K_pj≤0. Suppose some o has no outgoing arc. The sufficient column condition Γ_io<K_io for all i≠o is a special case.

Then inf(e+C)=0 exactly when at least one of the following finite tests succeeds.

1. Some column j admits q∈[0,1] with q J_ij≤Γ_ij for all i≠j.
2. A cyclic order on the other three players admits positive summable
   balanced geometric phase lengths, and the convex polygon test below
   accepts each of its three phases.

In both successful cases there is a uniform equilibrium payoff, using a
possibly accuracy-dependent calendar with one player moving per date. In
the other case every sufficiently accurate terminal equilibrium has a
positive simultaneous first-exit atom bounded below in terms of the game.
Indeed, if m is the largest unconditional simultaneous first-exit atom then C≤2√m. At a date with survival S, conditional exit h and conditional joint exit d one has d≤h², since the conditional singleton probability is at least (1−h)h (use the sum of the four hazard odds, or directly treat a sure hazard). Then S d≤√m √S h≤2√m(√S−√(S(1−h))). Sum across dates. No additional coalition rewards enter the decision. The negative conclusion
has no existence assertion about equilibria allowing simultaneous exits.

## Reduction to three labels

Suppose e+C tends to zero. The compactness argument in
[the signed diamond paper](DIAMOND_SOLO_AND_JOINT_UNIFORM_EQUILIBRIUM.md)
has the following reward-independent form. A physical date of survival S
and exit mass m occupies [1−S,1−S+m) on [0,1]. Subdivide its interval
by quitting coalition, giving the singleton subintervals their owner
colors. The simultaneous subintervals have total length C. The unfilled
joint Never mass N tends to zero, since conditional prescribed original
payoffs on a surviving Never tail tend to zero whereas immediate Quit
there tends to s_i>0, giving e≥Ns_i. Write T_i for the tail integral
of native coalition rewards on this interval, minus s_i N. At a date
start T_i is S times the conditional prescribed native payoff V_i.

For completeness take M bounding the absolute native rewards, q_i the
current hazard, H_i rival survival on this date, and Q_i the native
immediate Quit offer. Immediate Quit gives T_i≥S Q_i−e, with
|Q_i|≤M(1−H_i). If D_i is the value of Continue with prescribed
future minus Q_i, then Σ S q_i [D_i]^+≤e: suppress the favorable
hazards through any finite prefix. Survival can only increase and the
finite payoff telescope gains at least this sum over the prefix.
Writing Δ_i=S q_i H_i for the singleton length, we have
Σ Δ_i S |Q_i|≤M C. Using V_i=Q_i+(1−q_i)D_i and the immediate
Quit comparison gives Σ Δ_i |T_i(start)|≤2e+2MC. Interpolation
through i-colored pieces adds at most M Σ Δ_i(m−Δ_i)≤MC, since
m−Δ_i=S(1−H_i). Thus the integral of |T_i| on its own pieces tends
to zero. The cumulative color masses have a uniformly convergent
subsequence by their common Lipschitz bound. Their limiting measures
μ_i sum to Lebesgue measure and the tail functions converge uniformly
to W_i(t)=Σ_j Γ_ij μ_j([t,1]). The integral bound implies W_i=0
on the support of μ_i.

Here is the two-sided endpoint cap for any maximal pure j-run [a,b]
of length L>0. Select j-colored points from inside the run tending to
a, retaining only dominant-j points on physical cells whose lengths
exceed a threshold tending to zero. This is possible, since on a cell
of length at least η a largest hazard is at least η/4, and the sum of
minority singleton lengths over all such cells is at most 12C/η by
independence. Take η=√C+1/n on profile n. A positive-length limiting
cell is pure j, as the other hazards vanish, and its interior lies in
the maximal run. It starts at a, and its length d belongs to [0,L].
For i≠j the unconditional forced offer on this cell tends to J_ij d.
For a cell shrinking to the endpoint a, it tends to zero, since
S|Q_i|≤M m. Hence W_i(a)≥J_ij d≥min(0,J_ij)L. Choosing points
approaching b instead gives a limiting cell [l,b], possibly of zero
length, with W_i(l)≥J_ij(b−l). Since W_i(a)=W_i(l)+Γ_ij(l−a),
this gives W_i(a)≥min(Γ_ij,J_ij)L. The maximum of the two bounds
is K_ij L. At a domain endpoint the same one-sided selections apply.
The length d from the first selection is common to all quiet rows.

The pure runs cover the interval up to a null set. Locally before 1 the full cone kernel excludes one color, and
in a three-color neighborhood at most one point has all three
components zero, by its principal cone kernel. Elsewhere at most two
colors occur locally, and the zero set of each allowed coordinate is
an interval since it is monotone there. Its interior contains only
its own color, and its exterior only the other. A countable cover
gives the almost-everywhere statement.

Two adjacent distinct runs p then j must have the arc p→j: the
new owner j ends the p run at native zero, hence Γ_jp≥K_jp, and the
exiting owner p starts the j run at zero, hence K_pj≤0. No three
adjacent runs may be p,j,p, by the strictly nonzero Γ_pj and zero
values on both ends of the intervening j run.

On a terminal run of color j the opening native tail divided by its
mass L equals Γ_ij in every other coordinate. At its left endpoint take
a sequence of retained j-points from inside the run approaching that
endpoint, as in the proof of the two-sided cap. Its limiting physical
cell is either a single j atom of length qL or has length zero (q=0).
All quiet inequalities on this one common cell hold simultaneously:
q J_ij≤Γ_ij. Conversely if q>0 meets these inequalities, j alone can
quit with fixed hazard q at every date. Quiet players have native value
Γ_ij, their immediate offer is qJ_ij, and the owner's best terminal
payoff is its own positive level. All quiet deviations absorb with
geometric tail. An active-owner deviation can never obtain more than
s_j at any horizon, so the finite-average comparison also holds.
If q=0 works, Γ_ij≥0 and arbitrarily small positive q makes all quiet
violations uniformly small. Each finite deadline has gain at most that
single cap error, by the exact Continue identities. Either case gives
a fixed target.

Suppose test 1 fails. There is no terminal run. No positive run of
the sink o can occur, either. If it ended at b<1 and had an adjacent
successor, it would have an outgoing arc. Otherwise infinitely many
runs accumulate from the right at b. Since W_o(b)=0 and some W_h(b)
is nonzero, h≠o is absent near b. Among the remaining three colors
there is at most one point in this neighborhood where all their values
vanish. On a sufficiently short open right side of b the runs are
therefore locally finite, and those ending strictly inside it have
immediate successors. No such run can be o. This leaves at most two
colors, which cannot support three consecutive switches without the
forbidden p,j,p. Thus no positive run is o; the almost-everywhere
cover implies μ_o=0. Under the stronger strict column condition the
same deletion also follows at once from W_i(b)≥(K_io−Γ_io)(b−a)>0
for all i≠o, contradicting maximality or the terminal value zero.

The three remaining components cannot all vanish before 1 since their
remaining masses have positive sum and their principal matrix has
trivial nonnegative kernel. Consequently the limiting runs are locally
finite everywhere on [0,1). There is no final run. With three labels
and no p,j,p, one cyclic orientation is mandatory. Between consecutive
p runs, the lengths of the two intervening runs j,n satisfy
Γ_pj L_j+Γ_pn L_n=0. Thus the multiplier from phase j to its successor
n is −Γ_pj/Γ_pn, and repeating three phases multiplies lengths by their
product ρ. The tests require all three ratios positive and ρ<1.
The arbitrarily truncated opening run of a limiting sequence need not
have the canonical relative length. Any three complete interior runs
followed by the recursive infinite tail do, which suffices for the test.

## Testing any signed phase

Choose the first length in the geometric tail to be 1. The opening
tail of any complete j-run divided by its length L_j is
A_i=Σ_(m≥j) Γ_(i,m)L_m/L_j. This is a three-term numerator over 1−ρ.
The owner value vanishes by balance. At fraction t of the run the quiet
row i's residual in these units is A_i−Γ_ij t. Define the closed convex
polygon R of pairs 0≤t≤u≤1 satisfying

    J_ij(u−t) ≤ A_i−Γ_ij t       for every quiet row i.

A chain of cuts is 0=t_0<t_1<...<t_n=1. Its maximum excess is the
maximum positive part of the displayed inequalities over consecutive
pairs. Decide whether infimum excess is zero as follows. This test
applies to any finite number of quiet rows with arbitrary real data.

* Accept if (0,1)∈R. Otherwise form D={d:(0,d)∈R} and E={k:(k,1)∈R};
  reject if either is empty. Put d=min D and k=max E. Reject if d>k.
* Put F={f:(f,f)∈R}. If F meets [d,k], accept.
* If F misses [d,k], minimize u−t over (t,u)∈R with t∈[d,k].
  If the slice is empty, it suffices to test exact chains with at
  most two edges. Otherwise its minimum h is strictly positive.
  Test exact weakly increasing chains of at most 2+floor(1/h)
  edges by linear feasibility. Accept if and only if one exists.

Necessity of the endpoint bounds follows by compactness of first and
last cut pairs along arbitrarily accurate partitions, taking out the
one-step case. If f∈F∩[d,k] and 0<d<f, homothetic images of (0,d)
about (f,f) with ratios ((f−d)/f)^n are exact adjacent edges approaching
f from the left. If d=f, one edge reaches it. If d=0 then [0,f]⊂F
by convexity, so a fine mesh has maximum excess tending to zero.
An empty side needs no edges. The same construction backwards uses
(k,1) to approach f on the right. Join the two truncations by one
edge tending to (f,f), whose excess tends to zero. This establishes
sufficiency even when no finite exact chain exists.

When F misses [d,k], the interior start points of any increasingly
accurate partitions lie in [d−o(1),k+o(1)] by the endpoint bounds.
Any edge starting there then has length at least h/2 for all sufficiently
large indices, by compactness (and none exists eventually if the
slice is empty). Thus the numbers of cuts are bounded. A convergent
subsequence gives an exact chain after removal of repeated points.
Every exact chain has at most 2+floor(1/h) edges since all its interior
edges have length at least h. This proves the finite test in both directions.

## Realization and necessity for varying behavioral calendars

For sufficient realization repeat the chosen finite subdivisions each
tour. At each date set the sole active hazard to its mass divided by
total remaining mass. The mover is indifferent between its two actions
by the geometric balance. Every quiet Continue action gives its prescribed
value. Therefore each pure finite deadline's gain is bounded by the
single final conditional cap error, bounded by the maximum raw excess
times L_j divided by the remaining mass. That ratio is bounded uniformly
in subdivisions by the positive next phase mass ratio. Opponent survival
decays geometrically per tour even with any one player removed, and this
handles literal Never, offsets, and the standard terminal-to-uniform
comparison (uniform over deviations at each fixed mesh). The target
is the initial original row offsets plus normalized weighted singleton
columns and is independent of the cuts.

For necessity fix a complete pure limit run [a,b] inside (0,1) and L=b−a.
The physical cells have lengths equal to their unconditional exit masses.
Give each cell the label of a largest hazard, resolving ties consistently.
Keep each j-labeled cell that overlaps [a,b] over at least half its
positive length. Record the lengths of the intersections in chronological
order. These exhaust [a,b] up to o(1) length. Indeed the total joint,
Never and non-j mass there tends to zero by convergence of the color
measures and purity of the limiting run. On a non-j-labeled cell the
j singleton mass is at most that of some non-j singleton, since
q_j(1−q_h)≤q_h(1−q_j) for a largest hazard h. This controls the
mass lost to labels of whole cells inside the run. For the at most
two cells crossing its boundary, a positive-length subsequential
limit has a single dominant color and lies in the closure of a
maximal run of that color by the diamond compactness proof. If it
overlaps (a,b) in positive length, that color is j and the interval
is wholly in [a,b], so the fraction retained tends to one. Otherwise
its clipped length tends to zero. Accordingly every retained cell is
clipped by o(1) length, uniformly.

The retained lengths sum to L+o(1). Their partial sums differ uniformly
from the clipped mass clock by o(1). Normalize the partial sums by
their total to form a finite chain (physical cells meeting a fixed
compact interval before 1 are finite for all sufficiently large indices).
The maximum excess of this chain tends to zero. Otherwise select a bad
edge and pass its cell endpoints to a limit. A positive-length limit
is pure j, the normalized coordinates equal those of the cell in
[a,b], and the forced-quit cap at its left end passes to
W_i≥J_ij times its length. For a zero-length limit the immediate quiet
offer in unconditional units tends to zero, since it is bounded by a
constant times the physical cell length. Thus the limiting W_i at that
point is nonnegative for every quiet i. In either case the affine
inequality holds, a contradiction. This proves necessity for arbitrary
vanishing-regret, vanishing-collision profiles without assuming they
are solo on finite members of the sequence.

## A degree-one four-normal family requiring long calendars

Use the singleton matrix from the project's two-unrestricted-recipient
benchmark, with labels in their original order,

    Γ = [ 0,−1,−1, 5;  −5,0,2,−1;  −2,4,0,−5;  3,−4,2,0 ].

Every column has a negative entry and the principal determinants of sizes
two, three and four are nonzero. Thus Γ is R₀. At unit target its unique
complementary preimage is (41/30,191/60,289/60,9/5) of full support;
the determinant is 60 and the degree is +1. Row 0 is the observer. For an
integer k≥20 take

    J_01=J_02=k,   J_03=41k/8,   J_i0=1 (i=1,2,3);
    J_ij=−64k for distinct i,j∈{1,2,3}, except J_23=−5k.

All 32 unused coalition entries are free. All four players belong to the normal core because all four rows have a
strict negative supplier inside the full set. No terminal column works.
For j=1,2 the observer has Γ_0j<0<J_0j. For j=3 player 2 requires
q≥1/k and the observer q≤40/(41k). For j=0 the negative singleton
in row 1 conflicts with its positive join. There is no arc 0→1 or
0→2 since Γ_i0<K_i0 there, and K_03=5>0 prevents 0→3.

Up to rotation the required orientation after deletion is (1,3,2),
with successive length ratios 4/5,1/2,1/2, hence multiplier 1/5;
reversing this order requires a nonsummable multiplier 5. In this
order the observer opening values per unit phase mass are
A=(13/4,85/16,5/8), and its closing values are B=(17/4,5/16,13/8).
For phase 1 and phase 2 use 2k equal steps (here phase numbers refer
to owner labels). Each observer offer is 1/2, and its affine value
is at least 5/8. The core offers are −32 and all core quiet values
are bounded below by −5. At a phase of 3 the predecessor has value t
and the successor has value −5(1−t). Put

    x=log(17)/[−log(1−40/(41k))],   n=ceil(x),
    c=(1−17^(−1/n))/5.

Use Δ=c(85/16−5t). The residual observer value after each step is
multiplied by 1−5c, hence n steps end precisely at t=1. We have
c≤8/(41k), funding the observer. Also x>28 for k≥20: the bound
−log(1−z)≤z/(1−z) at z=40/(41k) gives x≥log(17)(41k−40)/40>28.
Concavity of 1−(1−40/(41k))^s in s∈[0,1] gives
c≥(x/n)8/(41k)≥(28/29)8/(41k)>16/(85k).
Since 85/16−5t≥(85/16)(1−t), the successor receives a step
of length at least (1−t)/k and its negative quit cap is satisfied.
The predecessor has negative offer and nonnegative value.
These comparisons give exact terminal Nash. Starting at the first phase of 1, the singleton probabilities of 1,3,2 are 5/11,4/11,2/11, so the fixed original uniform payoff is s+(13/11,0,0,−16/11).

Conversely in every complete phase of 3 in every low-regret,
low-collision limit, the observer's cap bounds any physical step
by Δ≤(8/(41k))(85/16−5t). The successor's strict negative value
everywhere before its right endpoint excludes all diffuse physical mass
in its interior. More explicitly on every compact subinterval of [0,1)
the inequality Δ≥(1−t)/k bounds step lengths below, and the physical
cell extraction proves that positive limiting cells cover it.
If the run has N finite steps, multiplication of the observer residual
gives (5/16)≥(85/16)(1−40/(41k))^N and hence N≥ceil(x). The same count
is automatic if infinitely many physical dates occur in that run.
The construction attains this lower bound exactly. Thus the optimal
number of physical dates per complete 3 run grows as (41/40)log(17) k.
In the other two phases the observer and strictly negative core
coordinate also force bounds of order k. Only the complete phase of
3 is needed for the sharp result.

## Comparison with existing results

The singleton matrix and a different joining table already appear in
[the general singleton-path classification](GENERIC_FOUR_PLAYER_SINGLETON_PATH_CLASSIFICATION.md)
and [the sharp simultaneous-activity theorem](SHARP_SIMULTANEOUS_ACTIVITY_UNIFORM_EQUILIBRIUM.md).
Both the matrix and the signed order are prior project observations.
The earlier positive simultaneous-exit conclusion uses its joining
data. On the present data the explicit triangle has zero collisions.

The conventional [subdivided triangle](CYCLIC_TRIPLE_PHASE_SUBDIVISION_UNIFORM_EQUILIBRIUM.md)
requires an oriented triangle for Γ. The sole oriented edge here is
2→3, so that test fails under every labeling. The [finite test for
nonnegative singleton paths](ALL_FOUR_PLAYER_SINGLETON_PATHS_HAVE_A_FINITE_TEST.md)
also fails, by R₀ and the absence of a simple oriented cycle. In the
implemented `BalancedSingletonCycleCertificate`
(`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`),
`soloFloor` requires nonnegative native values at every phase. Here
the quiet successor at the opening of a 3 phase receives −5 times
the phase mass before normalization. The existing diamond requires two
cycling triangles. Thus the classification and necessary number of
physical dates do not follow from these results. Other equilibrium
producers may apply to particular fillings of the 32 free entries.
The complete four-player conjecture remains open. The new decision and
its calibration are ordinary mathematics without a Lean formalization.
