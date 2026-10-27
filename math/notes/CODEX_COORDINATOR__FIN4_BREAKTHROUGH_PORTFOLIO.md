# Fin4: current results and the remaining proof obligations

Owner: CODEX_COORDINATOR.

Fin4 is OPEN. The target is uniform-equilibrium existence for every signed
four-player quitting table, with one payoff target fixed before accuracy
and all unilateral behavioral deviations allowed. The conference has
ordinary mathematical reductions and existence classes; it has not proved
an arbitrary-table producer or exhibited an unrestricted counterexample.

The checked theorem boundary is in `docs/FRONTIER.md` and the named Lean
sources. An exported mathematical proof is not a new Lean theorem.

## An explicit partition of the remaining work

The [residual partition](CODEX_COORDINATOR__FIN4_RESIDUAL_PARTITION.md)
organizes generic singleton matrices into ten pointed observer sign
templates. For fixed observer magnitudes, the remaining tests are affine
inequalities on a two-dimensional outside row. Child counts0/1/2 and
positive full inverse-column counts1/2/3/4 refine those same polygons.
The normalization is matrix algebra; it is not a transformation of the
original game or its collision rewards.

The no-child, one-pivot branch has exactly one sign pattern up to
permutation, four strict polynomial inequalities and four remaining generic
sign subcases. Its entire sign orbit, with any number of pivots, has the
simpler exact criterion R>0 and det Gamma>0; three cofactor signs specify
all additional pivots, and all eight combinations occur. A small exact
matrix has no cyclic positive-inverse child and only one positive full
column, so neither choosing another pivot nor choosing a cyclic child is
a universal exit. The one-pivot branch has exactly ten applicable signed
weighted-dominance tests. Across every generic residual matrix, the same
source argument supplies at least one such positive direction per recipient.

The separate global-source partition has five actual eventual-owner cases
and five inherited endpoint cap patterns. None is universally solved over
arbitrary raw tables; the benchmark reductions below close several cases
under explicit raw conditions. The
two-owner actual case now has explicit necessary interval tests using the
two quiet observers, including a stronger contact-rate test when late
pivot-only atoms are impossible. These can remove that branch for a given
table/pivot; they do not replace the other source obligations. One compact
exact checker verifies the matrix controls and the interval boundary cases.
The matrix and source classifications are distinct axes, with no assumed
incidence exclusions between them.

The [no-child benchmark](CODEX_COORDINATOR__NO_CHILD_FIN4_BENCHMARK.md)
completes the one-pivot matrix by a four-cycle of joining premiums. At M=14,
an exact rational certificate excludes all80 nonzero stationary patterns
and all65 sure-owner root patterns. Complete trap, anchor, ledger, pair and
the audited scalar-circuit selections also fail. This does not prove that
the game lacks UE.

The [open four-owner tail theorem](CODEX_COORDINATOR__FOUR_OWNER_TAIL_REGION.md)
excludes every proper nonempty infinite-owner set throughout M>11 and on
an explicit open region in the singleton and participant-pair entries.
All remaining higher rewards are arbitrary finite. It needs neither a
positive absorbing gap nor genericity: actual ALL-END and zero observer
debts suffice. Only F and I4 survive on the actual side; inherited endpoints
remain separate.

At a benchmark global minimum, direct zero-cap prefix surgery proves cap
positivity without genericity. Its first support is02,012 or0123; a finite
last support is012 or0123. These six endpoint combinations have exact
contact and hazard restrictions. The complete last-root relation reduces
to two one-dimensional algebraic branches, with an exact M14 cap-sign
partition. Actual positive-cap finite and infinite controls show why local
feasibility alone does not eliminate F or I4. The infinite control is full
native Nash; it is neither a global minimum nor an original-game UE.

The [complete finite-mode exclusion](../exports/NO_FINITE_ACTUAL_MINIMA_AT_SMALL_PENALTY_M14.md)
removes F at M14 for every sufficiently small selectable penalty
`0<r<min(m,r0)`. There is no bound on the number of dates. If finite minima
existed as r tends to zero, their last roots would converge to the unique
nonempty native Nash root. Its cap admits no nonempty proper Nash prefix.
Compressing the intervening pivot-only block then excludes a penultimate
observer date; a produced semantic inverse-axis tail excludes the remaining
one-date case. No conditional tail is assumed to minimize the objective.
Together with the four-owner theorem, only I4 remains in the actual branch
at these penalties. The [exact checker](../experiments/CODEX_NO_CHILD__FINITE_SOURCE_CHECK.py)
and the [adversarial](../feedback/NO_FINITE_ACTUAL_MINIMA_AT_SMALL_PENALTY_M14__BY_ADVERSARY.md)
and [fresh](../feedback/NO_FINITE_ACTUAL_MINIMA_AT_SMALL_PENALTY_M14__BY_FRESH_REVIEW.md)
whole reviews cover the complete proof. This is a benchmark source reduction,
not an arbitrary-table existence theorem.

The [fixed-cap controlled-window theorem](../exports/FIXED_CAP_CONTROLLED_WINDOW_MINIMUM_EXCLUSION.md)
adds a different global variation. A finite raw matrix test, including
passive pair rewards, supplies negative constrained curvature for any number
of players. The variation preserves every entrance full cap and thus works
under an arbitrary unchanged earlier head. At the no-child benchmark it
excludes every qualifying fixed window with five strict pivot dates; tied
dates may remain inside the window under the stated rank test. A Fourier
certificate extends this exclusion to every premium M>=14, with all rewards
on larger coalitions arbitrary fixed finite numbers.

Consequently an eventually full-support actual minimum on this ray has a
geometrically decaying remaining finite mass. At M14 the stronger
[eventual native Nash-tail theorem](../exports/EVENTUAL_NATIVE_NASH_TAIL_AT_ACTUAL_M14_MINIMUM.md)
excludes infinitely many strict pivot dates, however sparse they are.
Every eventually full-support actual minimum therefore has a finite head
followed by a fully contact native Nash tail. The benchmark's canonical-tail
classification shows that, after a further finite cut, this tail belongs to
one fixed one-parameter family. Jointly empty dates may first be deleted
without changing the full source tuple. The proof controls normal
multipliers on arbitrarily long windows; the earlier zero-density conclusion
is subsumed at M14. These are restrictions on actual minima, not UE existence
classes or realization theorems. Two final whole-proof reviews of the generic
fixed-window packet are
[here](../feedback/FIXED_CAP_CONTROLLED_WINDOW_MINIMUM_EXCLUSION__BY_ADVERSARY.md)
and [here](../feedback/FIXED_CAP_CONTROLLED_WINDOW_MINIMUM_EXCLUSION__BY_FRESH_REVIEW.md).

The [cyclic joining-cap theorem](CODEX_COORDINATOR__CYCLIC_JOINING_CAP_REGION.md)
also identifies the entire positive-continuation region admitting a nonzero
Nash root. Its raw joining-increment hypotheses work for every n>=3. The
region has a finite polynomial test, is convex after logarithms, and has one
critical Perron boundary on each positive ray. A positive subcritical minimum
must lie strictly outside it. The M14 specialization gives an exact algebraic
boundary and explicit excluded cap inequalities. This constrains the global
minimum without assuming its realization or varying an inherited fixed-cap
fibre; it does not itself produce UE.

At M14 and a sufficiently small selectable penalty, the remaining actual
obligations are calendars with infinitely many nonempty proper-support dates
and finite heads followed by canonical native Nash tails. The latter reduction
does not remove the finite head or the positive Never mass of its tail. The
inherited branch separately requires a replacement preserving the head's full
caps. Its three-zero-observer/positive-pivot case
now satisfies the strict ratio restriction in Section 9.3 of the residual
partition; equality instead produces an actual minimum. No remaining
inherited cap pattern is entirely eliminated. The canonical-tail uniqueness,
fixed-cap amplitude obstruction and exact finite-head transversality have a
[fresh whole review](../feedback/NO_CHILD_FIN4_CANONICAL_TAIL__BY_FRESH_REVIEW.md);
the obstruction makes changing the head's cap requirements essential to that
local continuation method.

Even with changing entrance caps, canonical-tail amplitude need not decrease
Never probability monotonically. The benchmark now contains a continuous
actual native Nash family with41 repaired roots and an interior Never
minimum; every member also lies outside the entire nonempty Nash-prefix
region. Exact rational interval certificates and a
[whole review](../feedback/NO_CHILD_FIN4_CANONICAL_HEAD_TURN__BY_INTERVAL_REVIEW.md)
establish this obstruction. It is not a global source minimum and does not
exclude other head-gap directions or a nonlocal replacement.

## Constructed equilibrium classes

The canonical two-premium family is now covered for **every real p once
K exceeds one finite threshold**. The new
[compact negative-ratio theorem](../exports/COMPACT_NEGATIVE_PREMIUM_RATIOS_UNIFORM_EQUILIBRIUM.md)
proves UE uniformly on every fixed band `0<q_-<=-p/K<=q_+<infinity` for
sufficiently large K. A finite backward core stops at exact entrance value
zero; connected terminal phases, exact deletion and a product-degree
argument produce all required strategic data. Its complete behavioral
consumer fixes the core and target before accuracy. Both fresh whole-proof
reviews are [here](../feedback/COMPACT_NEGATIVE_PREMIUM_RATIOS_UNIFORM_EQUILIBRIUM__BY_BEST_RESPONSE.md)
and [here](../feedback/COMPACT_NEGATIVE_PREMIUM_RATIOS_UNIFORM_EQUILIBRIUM__BY_SECOND_FRESH_REVIEW.md).

Here is the precise combination. Let Cminus>=100 be the constant from the
[central negative theorem](../exports/CENTRAL_NEGATIVE_WEDGE_UNIFORM_EQUILIBRIUM.md)
and set delta=3/Cminus. For K>=2Cminus and 0<=-p/K<=delta,
`Cminus(1+|p|/6)<=Cminus+K/2<=K`. The new theorem covers the compact
band[delta,2]. For -p/K>=2 and K>=100 the
[explicit negative outer cone](../exports/UNBOUNDED_PAIR_PREMIUMS_UNIFORM_EQUILIBRIUM.md)
applies. The [nonnegative theorem](../exports/ALL_NONNEGATIVE_PAIR_PREMIUMS_UNIFORM_EQUILIBRIUM.md)
covers p>=0. Taking the maximum of these finitely many thresholds gives
one Cstar with `K>=Cstar, p in R => UE` for the displayed canonical family.
No numerical Cstar or arbitrary-table conclusion is claimed. The bounded-K
strip and the broader raw-table frontier remain unresolved.

The exact negative-wedge certificate excludes every stationary and sure-root
Nash selection on `K>=100, -K/10<=p<=0`, in1230/369 nodes. The ray p=-K/10
separates the new producer from the explicit central/outer bounds and the
other audited raw selectors. The older general singleton-chamber theorem
does accept its fixed coefficients, but supplies an unspecified central-cone
constant; no claim that its actual producer necessarily fails on this ray
is made. The increment is complete compact-ratio coverage and the resulting
all-real-p conclusion, rather than another unspecified central cone.

The [weighted collision-dominance theorem](../exports/WEIGHTED_COLLISION_DOMINANCE_UNIFORM_EQUILIBRIUM.md)
replaces separate large-reward rays by a uniform region with any number of
favorable coordinates, including different coalition sizes and passive
recipients. Choose signed positive columns of an active principal inverse
whose outside images are positive. With collision coordinate scale
`|Z_i(D)|^(1/(|D|-1))`, let G be the largest favorable scale and B the
largest unfavorable scale. Explicit constants give stationary UE whenever
`G>=L0, B<=cG`. The full behavioral consumer and every strategic witness
are supplied. Constants are uniform on compact sets satisfying the strict
singleton tests; singular singleton limits remain outside this statement.

In Fin4 there are at most43 support/recipient-subset tests. Their successful
regions can be made disjoint by taking the first successful test, leaving
an explicit unresolved complement. Thus a counterexample with G large
must have a competing unfavorable coordinate of comparable weighted scale
for EVERY applicable test. The complete separating family has two growing
coordinates of sizes L^2 and L^3 and lies outside all compared single-pole
boxes. Proper active sets also handle selected mixed columns of the full
inverse. Two final-artifact reviews are
[here](../feedback/WEIGHTED_COLLISION_DOMINANCE_UNIFORM_EQUILIBRIUM__BY_TOPOLOGY.md)
and [here](../feedback/WEIGHTED_COLLISION_DOMINANCE_UNIFORM_EQUILIBRIUM__BY_BEST_RESPONSE.md).
This is a new raw existence class; it does not remove all stationary-free
sources or close either global-minimum obligation.

The [negative-pair outer dichotomy](../exports/NEGATIVE_PAIR_OUTER_DICHOTOMY_UNIFORM_EQUILIBRIUM.md)
closes both signs and the equality boundary of the formerly obstructing
outside inverse weight W2 within its displayed singleton geometry. It
requires Gamma10<0, a positive-inverse child023, positive determinant and
a strict inverse column0. One scalar quadratic produces the new return;
an exact switch joins it to the old return when W2=0. It retains the ten
arbitrary finite core remainders, 21 free joining entries, seven row0 caps
and arbitrary own levels. Every sufficiently large K relative to 1+|p|
is covered on its stated negative-p region. This is a complete geometry
branch, not all matrices with a cyclic child.

The former failed-return control is now inside this theorem. Its complete
completion at p=-1,u=10 has no stationary equilibrium and no sure-owner
root for every K>=100: the retained exact checker verifies1002/359 nodes.
The final reviews are
[here](../feedback/NEGATIVE_PAIR_OUTER_DICHOTOMY_UNIFORM_EQUILIBRIUM__BY_COVERAGE.md)
and [here](../feedback/NEGATIVE_PAIR_OUTER_DICHOTOMY_UNIFORM_EQUILIBRIUM__BY_BEST_RESPONSE.md).
A positive-Gamma10 control still fails both return choices, so changing
that sign is a substantive remaining obligation.

The [explicit singleton-chamber theorem](../exports/EXPLICIT_SINGLETON_CHAMBER_UNIFORM_EQUILIBRIUM.md)
replaces local coefficient restrictions by eight singleton signs and three
explicit rational inequalities. Ten core collision entries are arbitrary
finite numbers. The four remaining core coefficients satisfy
`A>g, c>0, u>=0, v<Gamma32`, with no upper bound on their magnitudes.
For each such fixed table, a finite threshold covers
`p<=-q0, K>=M(1+|p|)`, where `q0>=0` and
`q0>(c/(-Gamma23))Gamma21`. In particular Gamma21 may be positive;
when it is negative, q0=0 covers every nonpositive p. Thresholds are uniform
on compact subsets of the stated raw conditions, not over all unrestricted
core entries at once. The 21 free joining entries and arbitrary own levels
do not affect the threshold.

The new convergence estimate permits a backward contraction slower than the
phase contraction. On its explicit separating ray, `Z3(13)=10` gives ratios
`5/6>3/4`; all stationary equilibria and all actual sure roots are excluded
for every `K>=100,p=0`. The canonical checker verifies the ray with
`--uniform-k 0 10`. Both complete reviews are
[here](../feedback/EXPLICIT_SINGLETON_CHAMBER_UNIFORM_EQUILIBRIUM__BY_GLOBAL_TOPOLOGY.md)
and [here](../feedback/EXPLICIT_SINGLETON_CHAMBER_UNIFORM_EQUILIBRIUM__BY_BEST_RESPONSE.md).
This is additional raw-table coverage, not a new global-minimum reduction.
It does not contain the older neighborhood's negative-u perturbations.
An exact singleton matrix outside that chamber under every admissible
labeling is included in the packet; its outer-return inequality fails.
The complementary return theorem above now handles that matrix with its
stated collision conditions.

The [all-nonnegative-premium theorem](../exports/ALL_NONNEGATIVE_PAIR_PREMIUMS_UNIFORM_EQUILIBRIUM.md)
covers **every `K>=C, p>=0`** in the reference signed family, with one finite
C independent of p. It also proves the explicit region
`K>=0, p>=max(1,2K)`. Four overlapping ratio intervals give complete coverage:
a hybrid core with supports12/23/123 includes p=0 uniformly; a saddle core
handles the intermediate band; a pure3 return and the outer construction
cover the rest. All roots, continuations and the fixed-target behavioral
consumer are produced. No numerical C or coefficient neighborhood is claimed.
The seven row0 caps, 21 free joining entries and arbitrary own levels retain
their scope.

This implies the asymptotic existence statement of the
[central positive-wedge packet](../exports/CENTRAL_POSITIVE_WEDGE_UNIFORM_EQUILIBRIUM.md),
whose frozen proof remains available; its coverage is not counted again.
The separating ray p=K/1000 is beyond the former central spectral mechanism.
On every K>=100, 0<=p<=K/100, exact certificates exclude all80 stationary
patterns and all65 sure-root patterns in1046/371 nodes. Complete compared
raw selectors also fail on the ray. The two fresh whole-artifact reviews are
[here](../feedback/ALL_NONNEGATIVE_PAIR_PREMIUMS_UNIFORM_EQUILIBRIUM__BY_FRESH_REVIEW.md)
and [here](../feedback/ALL_NONNEGATIVE_PAIR_PREMIUMS_UNIFORM_EQUILIBRIUM__BY_SECOND_FRESH_REVIEW.md).
The compact negative-ratio theorem above supplies the complementary sign
and completes the canonical family's sufficiently-large-K parameter plane.
Bounded-K tables outside the explicit cones and both arbitrary-game
global-minimum cases remain open.

The [robust central negative-wedge theorem](../exports/CENTRAL_NEGATIVE_WEDGE_UNIFORM_EQUILIBRIUM.md)
adds one finite constant `C>=100` and one fixed coefficient neighborhood
covering every `p<=0, K>=C(1+|p|/6)`. The other 26 nontrivial displayed
coefficients vary independently in that neighborhood, while the seven row0
upper bounds, 21 free joining entries and arbitrary own levels retain their
scope. The constants are existential. The new mechanism is a uniform
construction of arbitrarily long finite cores and exact joining of consecutive
length branches, with the entire behavioral and fixed-target consumer proved.
Its independent whole-artifact reviews are
[here](../feedback/CENTRAL_NEGATIVE_WEDGE_UNIFORM_EQUILIBRIUM__BY_ORBIT_REVIEW.md)
and [here](../feedback/CENTRAL_NEGATIVE_WEDGE_UNIFORM_EQUILIBRIUM__BY_STATIONARY_GENERAL.md).
The canonical completion has no stationary equilibrium and no actual sure
root for EVERY `K>=100,p=0`; the exact checker now proves this whole ray,
not just isolated values. It therefore separates the class regardless
of the uncomputed threshold. It adds coverage beyond the scalar family and
both cones below; the positive central region now has the separate result
above, while the arbitrary-game minimum cases remain open.

The [boundary inverse-column theorem](../exports/BOUNDARY_INVERSE_COLUMN_UNIFORM_EQUILIBRIUM.md)
extends the large-reward stationary producer beyond strictly positive inverse
columns. For a signed nonnegative column, it solves the positive coordinates
and supplies the remaining complementary hazards when the relevant inverse
block has a strictly semimonotone inverse; a P-matrix is a finite sufficient
test. In Fin4 the new boundary has one zero coordinate and requires a
positive inverse diagonal there. The producer works for arbitrary bounded
completions, a growing box of other rewards, and an open neighborhood of
singleton entries, including mixed-sign selected inverse columns. All
strategic witnesses and the fixed target are produced. Both full reviews are
[here](../feedback/BOUNDARY_INVERSE_COLUMN_UNIFORM_EQUILIBRIUM__BY_COLUMN_REVIEW_ONE.md)
and [here](../feedback/BOUNDARY_INVERSE_COLUMN_UNIFORM_EQUILIBRIUM__BY_JACKPOT_BOUNDARY_REVIEW.md).
Its explicit four-player ray excludes every sure-owner root, every stated
child-debt selection, and the compared complete raw selectors. This supplies
a general stationary existence class; it does not eliminate the remaining
stationary-free arbitrary-table sources. No numerical large-reward threshold
is asserted.

The [two-premium theorem](../exports/UNBOUNDED_PAIR_PREMIUMS_UNIFORM_EQUILIBRIUM.md)
extends the signed collision family to `Z1(12)=-K, Z2(12)=p` in both regions
`K>=100, p>=2K` and `K>=0, p<=-max(200,2K)`. Both coordinates vary
independently subject to these inequalities, with 30 other displayed native
entries fixed and the same seven upper bounds, 21 free joining entries and
arbitrary own-singleton levels. A finite pair approximation handles the
positive region; three exact core roots handle the negative region. Two
compact rational interval checkers certify the entire regions without
stored numerical payloads. The full behavioral proof fixes the target
before accuracy. Independent whole-artifact reviews are
[here](../feedback/UNBOUNDED_PAIR_PREMIUMS_UNIFORM_EQUILIBRIUM__BY_CONE_REVIEW_ONE.md)
and [here](../feedback/UNBOUNDED_PAIR_PREMIUMS_UNIFORM_EQUILIBRIUM__BY_CONE_REVIEW_TWO.md).
Exact completions at `(K,p)=(200,400)` and `(150,-300)` defeat all stationary
supports and all actual sure-root patterns and cannot be relabeled or
positively rescaled into the preceding `K=100` family. The two cones leave
the rest of the parameter plane open; they do not settle either global
minimum case or arbitrary Fin4.

The [signed collision-parameter theorem](../exports/SIGNED_COLLISION_PARAMETER_UNIFORM_EQUILIBRIUM.md)
removes the restriction `Z2(12)=0` completely: that reward may be ANY real
number. It keeps the other31 displayed native entries fixed, requires only
seven row0 upper bounds, and allows all21 other nonsingleton entries involving
player0, plus all four own-singleton levels, to vary independently. Thus the
positive and negative parameter regimes are both closed for this family.

For positive p, a growing pair12 block has an exact limiting entrance and a
single vanishing interface error. For nonpositive p, one, two or three
triple123 roots suffice. Exact insertion at each wash boundary joins those
three regimes. Two polynomial certificates and a deterministic rational
interval certificate cover the entire line; the latter checks2000 cells and
two support switches without stored center tables. The common finite calendar
prices all behavioral deviations and fixes the target before accuracy.
For p<=0 every selected profile delivers its target exactly in terminal
payoff; for p>0 the finite profiles converge to their fixed target.

Two independent whole-proof and export-gate reviews are
[here](../feedback/SIGNED_COLLISION_PARAMETER_UNIFORM_EQUILIBRIUM__BY_CODEX_CLOSURE_ADVERSARY.md)
and [here](../feedback/SIGNED_COLLISION_PARAMETER_UNIFORM_EQUILIBRIUM__BY_CODEX_CLOSURE_STRATEGY.md).
The concrete completions at p=1,-10,-100 defeat every stationary support and
every sure-root pattern, as well as the named full raw selectors checked in
the reviews. Arbitrary four-player reward tables remain open: the theorem
still fixes31 native coordinates.

The earlier fixed-zero packet below retains its specific algebraic target
and its efficient calendar with only one initial joining error. Its UE class
is contained in the parameter theorem and is not counted again as additional
counterexample exclusion.

The [signed collision-bridge theorem](../exports/SIGNED_COLLISION_BRIDGE_UNIFORM_EQUILIBRIUM.md)
covers a class with strongly signed participant rewards and nonadditive
passive rewards on the difficult singleton matrix. It uses a pair12 root,
a triple123 root and a finite44-root repair through negative native values.
An exact quintic identity closes the return. Every profile delivers the
same payoff target; its full terminal debt is exactly
`(0,0,0,max(K,0)delta)`, where K is player3's joining reward at solo0.
The only error is a single initial joining opportunity. All28 unlisted
native coordinates have the packet's explicit independent freedoms, with
arbitrary signed own levels. The equality `Z2(12)=0` is part of this specialized calibration.
The parameter theorem above removes it with a different construction;
neither theorem claims an all60-coordinate neighborhood.

The concrete positive-core completion has target approximately
`(1,1.8616124826,1.6489455273,1)`. Its stationary and actual sure-root
exclusions are proved in the [signed table note](CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_TABLE.md).
The earlier negative-core table was already covered by ordered nonpositive
anchors and is not counted as new coverage. The exported class instead has
core participant vector `(11,2,1)` on123; complete ordered-anchor, trap,
passive-child and other applicable selector comparisons were checked.
Whole-proof reviews are
[here](../feedback/SIGNED_COLLISION_BRIDGE_UNIFORM_EQUILIBRIUM__BY_CODEX_LAST_DATE.md)
and [here](../feedback/SIGNED_COLLISION_BRIDGE_UNIFORM_EQUILIBRIUM__BY_CODEX_SIGNED_BRIDGE_REVIEW.md),
with a separate
[coverage and mathematical audit](../feedback/SIGNED_COLLISION_BRIDGE_UNIFORM_EQUILIBRIUM__BY_CODEX_GLOBAL_SYSTEMATIC.md).

The [contracting-block theorem](../exports/TWO_CONTRACTING_BLOCKS_UNIFORM_EQUILIBRIUM.md)
unifies four actual reward-table producers. It retains an explicit quantitative
box, extends the construction across a signed singleton chamber with arbitrary
finite passive rewards and computed participant thresholds, and supplies a
complementary class with arbitrary nonnegative pair premiums. Every strategy
and return value is produced from the stated reward conditions.

For the fixed reference singleton matrix and additive passive completion,
the fourth theorem allows the common premium of rows1 and3 and the premium
of row2 to be independently small: under its row0 participant caps, one
positive bound works for both. Rows1 and3 share a premium in this theorem.
The proof combines a positive cone, a constructed invariant graph and a
hybrid pair/triple contraction. The target is fixed before accuracy, and
the finite periodic approximations price all behavioral deviations.

The exact calibration family defeats the checked stationary, sure-owner
punishment, protected-player, ledger and universal child-debt criteria.
The two independent artifact reviews are
[here](../feedback/CODEX_PERIODIC_CLOSURE__DEADLOCK_CONTRACTION_BLOCK_UNIFORM_EQUILIBRIUM__BY_CODEX_ZERO_CAP_ADVERSARY.md)
and [here](../feedback/CODEX_PERIODIC_CLOSURE__DEADLOCK_CONTRACTION_BLOCK_UNIFORM_EQUILIBRIUM__BY_CODEX_PERIODIC_ADVERSARY.md).
The [unequal-premium theorem](../exports/UNEQUAL_PREMIUM_CONTRACTION_UNIFORM_EQUILIBRIUM.md)
adds two regions for core premiums `(a beta,beta,c beta)` on the reference
singleton/additive-passive background:

- `a>0`, `0<c<5/9`, `8a<15(1-c)`;
- `1<c<2`, `3c/2<=a<3`, including the neutral boundary `2a=3c`.

Each compact subset has one sufficiently small scale threshold. A strict
cone produces the first region. In the second, a concave physical boundary
and a monotone contraction produce every pair/triple continuation, including
unbounded pair prefixes. One continuous macro slack parameter produces the
return without separate switch cases. The six row0 proper participant entries
remain independent under their upper bounds. The proof and both exact
separating rays include the full behavioral consumer and selector comparisons.
The final independent reviews are
[here](../feedback/UNEQUAL_PREMIUM_CONTRACTION_UNIFORM_EQUILIBRIUM__BY_CODEX_ACTUAL_MINIMUM_AUDIT.md)
and [here](../feedback/UNEQUAL_PREMIUM_CONTRACTION_UNIFORM_EQUILIBRIUM__BY_CODEX_MACRO_ADVERSARY.md).

The [three-diffuse-flow theorem](../exports/THREE_DIFFUSE_FLOWS_UNEQUAL_PREMIUM_UNIFORM_EQUILIBRIUM.md)
produces uniform equilibria whenever

    0<=a<3, 0<c<=1, Delta=21c-6+8a(19c+1)>=0,

at sufficiently small positive beta, uniformly on each compact parameter
subset. In particular one threshold works throughout the closed rectangle
`0<=a<=2, 2/7<=c<=1`. No numerical scale threshold is asserted. Beyond the
fixed singleton matrix, only seven passive entries, nine core participant
entries and seven upper bounds in row0 are required. All other nonsingleton
rewards and the four own-singleton levels are arbitrary finite numbers; the
scale threshold is independent of these free coordinates.

The proof joins a pair return and two triple-return arcs to a constructed
analytic core graph. Three singleton flows, approximated by finite meshes,
close the return. The finite periodic consumer controls every behavioral
deviation and keeps the payoff target fixed before accuracy. The final
independent reviews are
[here](../feedback/THREE_DIFFUSE_FLOWS_UNEQUAL_PREMIUM_UNIFORM_EQUILIBRIUM__BY_CODEX_COLLAR_ADVERSARY.md)
and [here](../feedback/THREE_DIFFUSE_FLOWS_UNEQUAL_PREMIUM_UNIFORM_EQUILIBRIUM__BY_CODEX_LOCAL_COLLAR_REVIEW.md).

For the reference additive calibration, combining this result with the
strict-cone theorem covers EVERY `0<a<3, 0<c<=1` at sufficiently small scale.
Indeed Delta<0 implies c<2/7 and
`a<(6-21c)/(8(19c+1))<=3/4`; hence `8a<6<15(1-c)`, within the older cone.
This union does not transfer the new theorem's free-coordinate scope to
the older cone. The former stress test `(a,c)=(1/10,1)` is now covered.

The [crossed-premium theorem](../exports/CROSSED_PREMIUM_HYBRID_DIFFUSE_FLOW_UNIFORM_EQUILIBRIUM.md)
adds the following regions with the same seven-passive-entry, nine-core-entry
and row0-cap requirements as the three-flow theorem:

    U: 0<a<3, c>1, 2a<3c;
    L: a>3, 0<c<1;
    B: a=3, 0<c<1.

On U, a contracting obstacle operator constructs a continuous switch between
triple and pair roots. On L, an invariant cone for the reversed linear map
orders finitely many physical continuation sheets; normalized forward
equations continue them to positive beta and glue their exact boundaries.
On B, an analytic graph contains an exact solo-player axis. A single
two-dimensional intermediate-value argument consumes all three continuous
cores, with the same finite-flow behavioral estimate. It requires no smooth
axis map or choice of a continuous return-root curve. The final independent
artifact reviews are
[here](../feedback/CROSSED_PREMIUM_HYBRID_DIFFUSE_FLOW_UNIFORM_EQUILIBRIUM__BY_CODEX_COLLAR_ADVERSARY.md)
and [here](../feedback/CROSSED_PREMIUM_HYBRID_DIFFUSE_FLOW_UNIFORM_EQUILIBRIUM__BY_CODEX_LOCAL_COLLAR_REVIEW.md).

The internal [uniform-core theorem](CODEX_UNIFORM_JOINS__PHYSICAL_CORE_UNIFORMITY.md)
now gives the stronger uniform conclusion on the original additive calibration:

    for every compact K contained in (0,infinity)^2 there is beta_K>0
    such that every (a,c) in K and 0<beta<beta_K gives UE
    for core premiums (a beta,beta,c beta).

This uses the fully specified original sixty-entry calibration: singleton
levels1, Gamma as above, all passive rewards additive, all proper
participant rows (beta,a beta,beta,c beta), and native grand vector
(10,-2,-beta,-1). It does not transfer the newer packets' free-coordinate
scope to the older strict-cone theorem used in the cover.

The local results retain the freer seven-passive-entry scope. They give
two-sided bands across a=3 for every compact positive c interval and across
c=1 for every compact positive a interval. A new dynamic graph works
uniformly on compact subsets of

    0<a<=3, c>1.

One producer covers this entire strip, including the neutral wall 2a=3c
and the a=3 boundary. Keeping the same candidate slope in a derivative's
numerator and denominator, then choosing the slope bounds jointly,
removes the earlier parameter restrictions. Retaining each factor 3-a
keeps the proof uniform at a=3. The graph transform has contraction below
4/5 and allows pair/triple switchbacks.
The other joins use exact solo-player axes, scaled finite sheets, and a
cone-order comparison when the number of sheets diverges.

Every positive ratio point consequently has an open neighborhood with a
common threshold. A finite cover proves the compact-ratio theorem, using
the lower diffuse/strict-cone overlap, the full upper strip, L, and the
exact pair quadrant. All strategy and return data are produced;
the finite-flow consumer prices unrestricted behavioral deviations. The
complete internal artifact has independent reviews
[here](../feedback/CODEX_UNIFORM_JOINS__PHYSICAL_CORE_UNIFORMITY__BY_CODEX_COLLAR_ADVERSARY.md)
and [here](../feedback/CODEX_UNIFORM_JOINS__PHYSICAL_CORE_UNIFORMITY__BY_CODEX_LOCAL_COLLAR_REVIEW.md).

Thus a counterexample sequence in that calibration with beta tending to
zero must leave every compact positive ratio set. For any fixed bound on
the ratio of largest to smallest core premium, sufficiently small premiums
are covered uniformly. Degenerating ratios, a uniform threshold for the
entire positive three-premium cube, and arbitrary signed tables remain
open. No explicit numerical threshold or reduction of arbitrary games to
this calibration is asserted.

The [nine-independent-premium theorem](../exports/NINE_INDEPENDENT_CORE_PREMIUMS_UNIFORM_EQUILIBRIUM.md)
removes the equality of a player's three core participant rewards on an
explicit compact class. In native coordinates its nine entries are

    (Z1(12),Z1(13),Z1(123))=beta(a,b,f),
    (Z2(12),Z2(23),Z2(123))=beta(d,e,g),
    (Z3(13),Z3(23),Z3(123))=beta(h,k,l).

All nine normalized coefficients range independently in [1,2], subject
only to d>=h. One beta0>0 works for this entire closed ordered box,
including d=h. In particular it contains a literal nine-dimensional
rectangle with d in [3/2,2], h in [1,3/2], and the other seven entries in
[1,2]. The fixed singleton matrix, seven passive entries and row0 caps
are the same as in the three-flow theorem; the other nonsingleton rewards
and signed singleton levels remain arbitrary finite data. The threshold
is independent of these free entries.

The producer constructs an analytic graph on the whole nonnegative outer
cap quadrant. At d=h an exact solo-player axis gives a parameter factor
that preserves physicality uniformly up to the ordering boundary. A
continuous macro return and finite flow meshes then price every complete
behavioral deviation. Its exact separating table has all proper participant
premiums e except Z1(123)=2e. The packet checks all applicable selector
families, including the full sure-owner punishment-tail and stationary
censuses, rather than inferring separation from unequal rewards alone.
The final independent mathematical and export-gate reviews are
[here](../feedback/NINE_INDEPENDENT_CORE_PREMIUMS_UNIFORM_EQUILIBRIUM__BY_CODEX_COLLAR_ADVERSARY.md)
and [here](../feedback/NINE_INDEPENDENT_CORE_PREMIUMS_UNIFORM_EQUILIBRIUM__BY_CODEX_LOCAL_COLLAR_REVIEW.md).
The full unordered box [1,2]^9 remains open; an exact example in the
packet shows why the pure triple graph alone cannot cover it.

The [unordered-premium theorem](../exports/UNORDERED_NINE_CORE_PREMIUMS_UNIFORM_EQUILIBRIUM.md)
removes the ordering condition on a smaller pair-premium range: all six
pair coefficients vary independently in [1,4/3], and all three triple
coefficients independently in [1,2]. One beta0 works on this entire
nine-dimensional rectangle. Thus the two accepted boxes are not nested:
the ordered theorem permits larger pair premiums, while the unordered
theorem covers new tables with h>d.

On h>=d, a fixed weighted norm bounds the leading continuation map by
71/72. An enlarged derivative class and exact vanishing-axis factors
produce a uniform obstacle graph even at h=d. Its pair region stays legal
under continuation. The ordered analytic graph handles d>=h. Neither
continuity of the selected graphs across that split nor a supplied phase
itinerary is required. A common macro slack closes the return for both
halves, with the full finite-flow behavioral consumer included.

The separating calibration adds Z3(13)=(1+theta)e, 0<theta<=1/3, to the
previous nonhomogeneous table with Z1(123)=2e. It strictly violates the
earlier order condition, and its full selector census still fails. Both
final mathematical and export-gate reviews are
[here](../feedback/UNORDERED_NINE_CORE_PREMIUMS_UNIFORM_EQUILIBRIUM__BY_CODEX_COLLAR_ADVERSARY.md)
and [here](../feedback/UNORDERED_NINE_CORE_PREMIUMS_UNIFORM_EQUILIBRIUM__BY_CODEX_LOCAL_COLLAR_REVIEW.md).
The full factor-two unordered box, arbitrary singleton matrices and the
general source obligations remain open.

The internal [cap-region invariance theorem](CODEX_UNEQUAL_GLOBAL__NONNEGATIVE_CAP_ROOT_ACTIVITY.md)
shows that, on the small-premium calibration, every full Nash root from
nonnegative continuations with player2 cap at most2 stays in that region.
No output-sign assumption is needed. Such a root can activate player0 only
alone at zero cap. Its
exact control also shows why this cannot be applied to the canonical incoming
head: that head prices observer deviations but may pay positive pivot regret.
The stronger internal
[exact-Nash nonattainment theorem](CODEX_NEGATIVE_CAPS__EXACT_NASH_NONATTAINMENT.md)
proves that the original calibration with own singleton levels1 has no
exact terminal Nash profile for all sufficiently small independent positive
premiums, even with arbitrary infinite behavioral laws and Never. It also
proves that every zero-debt point of its original semantic closure has
nonnegative native payoff. The proof rules out negative continuations along
the complete infinite root sequence, rather than assuming nonnegativity at
one end. This explains why an exact-profile search can fail on tables that
do have uniform equilibria. It does not exclude approximate equilibria or
identify observer-Nash incoming heads with full Nash roots.

## Model and the three different minimum problems

Native rewards Z have own-singleton, live and AllNever payoffs zero.
Private stopping laws are independent. U is prescribed payoff, B is the
supremum over all finite deadlines and Never, and d=B-U. Let K_abs be the
closure of actual absorbing payoff/cap pairs. A hypothetical counterexample
supplies a table with g=min_(K_abs) max_i d_i>0. Its native AllNever profile
still has zero debt; the restriction to absorbing profiles matters.

The source reductions use three distinct optimizations:

| Source | Objective and feasible set | Established conclusion |
| --- | --- | --- |
| Canonical low-cap F_p | Minimize d_p over K_abs with d_i=0 for i!=p and min B<=0 | A source exists for every pivot; after a gap-preserving generic perturbation it has a nonzero exact B-root with strictly positive successor caps. |
| Global absorbing C_p | Minimize d_p over K_abs with d_i=0 for i!=p | Every minimum has positive pivot payoff; generically every payoff is positive. AllContinue is the only exact root at U. |
| Never-penalized C_h | Minimize d_h+r nu on the augmented ALL-profile carrier with zero observer debts, 0<r<A | Every minimum has positive original Never mass, all END caps active, and a strict pivot margin. |

Here nu is the product of original Never masses and A is the infimum of
absorbing total debt. The last source uses the strict inverse column h.
Different pivots, weights and perturbations can select different points.
No inequalities are transferred between these three problems without proof.

The complete canonical result is
[Universal canonical pivot exit](../exports/UNIVERSAL_CANONICAL_PIVOT_EXIT_REDUCTION.md).
It supplies its source, finite-law returns and genericity argument without
a ledger assumption. At its positive-cap exit, if the successor debt is
c d_p and r is the first-zero pivot-return survival, minimality gives

    r c d_p+(1-r)W_p >= d_p,     W_p>d_p,
    U'_p >= (1-c)d_p/(1-r)>0.

Consuming this expensive exit remains open. The separate
[absorbing partial-Nash proof](CODEX_EXPENSIVE_EXIT__ABSORBING_PARTIAL_NASH_MINIMUM.md)
supplies C_p and its positivity; it does not identify C_p with F_p.

For the Never-penalized source, use the existing
[strict-margin proof](CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_PARTIAL_NASH_PREFIX_BARRIER.md)
and [constrained-repair proof](CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_REPAIR_AND_CONE_GRAFT_OBSTRUCTION.md).
They already prove vanishing-weight access, all-END activity at EVERY
minimum, a strict pivot Never-mass bound and separation from jointly
repaired pivot deletion. Reconstructing those facts is not a new result.

## The absorbing global-minimum frontier

The [incoming-collision theorem](CODEX_OBSERVER_PATH__GLOBAL_MINIMUM_INCOMING_COLLISION.md)
and [realization reduction](CODEX_PIVOT_REVIEW__SURE_ROOT_AND_PROPER_LIMIT_REALIZATION.md)
leave two concrete branches.

An ACTUAL global C_p minimum may still exist. Its whole-law variations
must preserve the three observers' exact full best responses. The
[fixed-pivot note](CODEX_COLLAPSED_CONSUMER__FIXED_PIVOT_FULL_LAW_TRAP.md)
excludes actual minima whose observers have pure uniformly strict best
replies, but it does not exclude general ties or infinite supports.

The [observer Never-margin theorem](CODEX_GLOBAL_SYSTEMATIC__TERMINAL_OBSERVER_MARGIN.md)
adds a finite raw test and a bound valid on both actual and nonrealized
sources. For S=I\\{p}, set

    A_i=r_i(S)-r_i(S\\{i}), C_i=r_i(I)-r_i(I\\{i}),
    Lambda_p=max_(0<=x<=1) min_(i in S)[(1-x)A_i+x C_i].

Let e_i denote the literal Never response, D the sum of observer debts,
and M bound all terminal rewards. Every actual profile satisfies

    min_(i in S)(B_i-e_i) <= max(0,Lambda_p)+4 sqrt(M D).

The estimate passes to the augmented all-profile and absorbing carriers
that retain e. The zero-error bound is sharp and attained by actual
absorbing observer-Nash profiles. Thus Lambda_p<=0 forces a Never-active
observer at every partial-Nash source for that pivot, including any lift
of a nonrealized global minimum. Lambda_p is computed from at most five
scalar points; failure has a dual certificate supported on at most two
observer rows. The arbitrary counterexample source does not automatically
supply Lambda_p<=0.

The [joint-positive-capacity control](CODEX_GLOBAL_SYSTEMATIC__JOINT_MARGIN_STATIONARY_OBSTRUCTION.md)
rules out the proposed opposite-case shortcut. Its original own singletons
are all1 and its capacities are (1,1/17,1/17,1/17), yet every stationary
profile has regret bounded below by a positive constant and no absorbing
finite-calendar exact Nash profile exists. An explicit period-three profile
is UE. The stationary exclusion has a short exact rational interval checker
and two full independent reviews. This solved control does not exclude a
new counterexample class; it shows that joint capacity positivity still
requires dynamic constructions.

The separate [signed table control](CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_TABLE.md)
keeps the difficult singleton matrix and has capacities
`(2,1/5,3/29,1/7)`. Its exact Bernstein checker excludes all 80 nonzero
stationary support patterns and every root containing a sure quitter
against any actual continuation. Consequently stationary regret has a
positive floor, and an exact terminal Nash profile cannot have even one
bounded proper clock. Two independent full reviews checked the table,
polynomials and finite certificate. No nonnegative payoff weight or
nonnegative participant row supplies the elementary positivity shortcuts.
The signed collision-bridge theorem now supplies its UE. Thus these
strategy-class exclusions coexist with a proved behavioral producer;
they are not evidence of an unrestricted positive gap.

For an ACTUAL native exact-observer profile, ONE strictly positive Never
margin gives a finite-calendar representation of the entire (U,B,e,N)
tuple, retaining the prescribed terminal outcome law. Its bounded proper
clock protects every other player's response menu. The remaining scalar
Never payoff is matched by independent two-atom tail clocks with fixed
Never masses; finitely many weak orders and the intermediate value theorem
produce them. The strict late-response gap protects the remaining cap.
For original signed tables the exact sufficient condition is
`U_i=B_i>max(e_i,e_i+r_i({i}) product_(j!=i)N_j)`; two strict observers
always supply it. An actual native tuple that has no finite-calendar
realization must therefore have ALL three observers Never-active.
With all three margins strict, the observers also share one last support
date and have strict joining comparisons there. A Never best reply need
not have positive prescribed mass. The finite representation preserves
global minimality when present, but does not eliminate finite mixed-support
minima or realize abstract carrier points. The complete independent reviews are
[here](../feedback/CODEX_GLOBAL_SYSTEMATIC__TERMINAL_OBSERVER_MARGIN__BY_CODEX_LAST_DATE.md)
and [here](../feedback/CODEX_GLOBAL_SYSTEMATIC__TERMINAL_OBSERVER_MARGIN__BY_CODEX_UNIFORM_CORE_REVIEW.md).

The [strict-margin local-minimum control](CODEX_LAST_DATE__STRICT_NEVER_FULL_LAW_LOCAL_MINIMUM.md)
shows why finite representation does not complete the argument. All three
observers can be proper, have strict Never margins27/200, and mix on two
dates, while pivot debt6/85 is locally minimal among ALL complete-law
exact-observer profiles. This persists on an open native-table family with
positive determinant, degree1 and a strict positive inverse column. Its
global minimum is zero at a different explicit equilibrium. Thus local
optimality cannot substitute for the source's global comparison property.

Every NONREALIZED minimum now admits the stronger
[zero-observer boundary reduction](CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION.md).
Incoming decomposition continues through higher-debt tails using words of
at most two roots. It reaches, finitely or as a semantic limit, a tail in

    F={Y in C_p: all B_i(Y)>=0, min_(i!=p) B_i(Y)=0},
    d_p(Y)>=m+kappa_F,     kappa_F=min_F d_p-m>0.

An infinite selected head has positive survival and summable hazards;
vanishing survival would actually realize the original minimum. The
boundary tail need not be an actual profile. No continuation is executed
after infinitely many dates. Observers with positive limiting caps become
inactive eventually in this head; only the pivot and zero-cap observers
can keep acting arbitrarily late.

For a boundary with exactly ONE zero-cap observer, Section 5 now replaces
the entire infinite head by a finite prefix followed by at most TWO
diluted geometric clocks, preserving every payoff and full deviation cap
and keeping the same boundary tail. This needs no genericity. A positive
pivot tail cap leaves only a solo-pivot geometric suffix; the two-clock
case has zero pivot and observer tail caps and an explicit rational pivot
debt formula. This is an exact representation reduction, not a boundary
repair. Boundary tails with two or more zero observer caps remain open.

The infinite case supplies an actual nonabsorbing head P and an explicit
limit comparison map. Write s for its joint Never mass, h_i for opponent
Never mass, and e_i for its Never response payoff. Then

    Phi(Z).U_i=U_i(P)+s U_i(Z),
    Phi(Z).B_i=max(B_i(P),e_i+h_i B_i(Z)),
    Phi(Y)=the original global minimum.

The boundary tail minimizes the pulled-back pivot objective on its fixed
observer-cap slice. It does NOT minimize d_p on F. The old strict incoming
tail-gap theorem remains valid, but a tail above m no longer stops
decomposition. Incoming and outgoing budgets still have different cap
annotations, and an unrelated lower-debt tail need not preserve observer
optimality.

If EVERY boundary cap is zero, Section 6 identifies an exact link to the
penalized problem: with lambda=d_p(Y), the actual positive-Never head P
globally minimizes d_p+lambda nu over the augmented partial-Nash carrier.
Its minimum first reaches the absorbing value m at lambda and stays there
for all larger penalties. The left derivative is at least nu(P)>0 and the
right derivative is zero. Thus every such endpoint has the same debt and
forces a finite plateau corner with both positive- and zero-Never minima.
Excluding that coexistence remains open; generic envelope calculus does
not exclude it.

Section 7 now gives a universal alternative without requiring an incoming
all-zero tail. Write C for the augmented exact-observer carrier, C0 for
its zero-Never slice, m>0 for its minimum pivot debt, and M0 for the full
absorbing minimum set. Either M0 contains a point where every observer's
Never option is optimal, or the penalized value
`f(r)=min_C(d_p+r nu)` first reaches m at a finite `lambda_*>m`, attained
by both positive-Never and absorbing minima. In the latter case, all
positive-Never critical minimizers have a common positive Never-mass
lower bound. At EVERY positive penalty and every minimizer,
`B_p>f(r)` and `U_p>r nu`. For a strict inverse-column pivot supplied by
the native positive-gap source, every positive-Never minimum is all-END
and satisfies `N_p<=1/(1+r sum(v))`, where `Gamma v=e_p`, `v>0`.
At such a pivot the absorbing alternative itself strengthens: one can
select an ALL-END absorbing global minimum with
`N_p<1/(1+m sum(v))`, or obtain the finite critical coexistence. If f(r)
approaches m without reaching it at a finite penalty, the selected
absorbing minimum has `N_p=0`. This follows by taking limits of ALL-END
penalty minima, using the mass bound for every positive r. Both independent
reviews cover the complete extension and its source adapters.
Neither alternative is eliminated. A critical carrier point need not
have an actual head representation; that stronger conclusion still
requires Section 6's incoming all-zero boundary.

Section 8 extends incoming decomposition to the positive-Never critical
source while retaining all Never masses and offers. ALL-END activity
propagates to every tail. An all-zero-cap endpoint must be neutral at the
first penalty plateau; repeating that tail then produces an ALL-END
absorbing global minimum with `N_p=0`. Thus, unless that absorbing case
already occurs, a nonrealized critical minimum reaches a mixed boundary:
at least one observer cap is zero and at least one cap is strictly positive.
Actual critical minima and these mixed endpoints remain open. The two
Section 8 reviews check the complete incoming adapter, not only a supplied
head representation.

The reviewed [weighted cap bound](CODEX_COORDINATOR__WEIGHTED_CAP_ABSORPTION_COERCIVITY.md)
excludes specified zero-cap faces under two finite reward-table tests.
If a nonnegative weight vector has strictly positive singleton column
drift and strictly positive weighted forced-Quit rewards on every nonempty
coalition, its weighted full cap bounds absorption probability from below.
This applies to every actual profile and its semantic closure. Sparse
weights exclude the entire face on which their supported caps vanish.
The arbitrary-counterexample source does not supply those reward tests;
the theorem therefore remains internal and does not close the boundary
branch as a whole.

The [local cap-collar theorem](CODEX_GLOBAL_SYSTEMATIC__LOCAL_CAP_COLLAR.md)
replaces the global forced-Quit positivity test with strictly positive
weighted pair columns and an isolated common nonpositive forced-Quit root.
Individual participant pair rewards may have either sign. Together with
strictly positive weighted singleton drift, these raw tests produce
`max_(i in S) B_i >= delta*(1-nu)` for every actual profile and its augmented
semantic closure. On the small-premium calibration, S={0,1,3} passes these
tests although EVERY weight fails the older global forced-Quit test.
Consequently the entire face `B0=B1=B3=0`, including the all-zero endpoint,
is absent from its absorbing native closure. A separate exact signed table
has a negative pair reward in every row, yet a positive weighted pair
column vector and an isolated root. An explicit Farkas identity rejects
every global forced-Quit weight on that table. Strict margins extend the
example to an open family of native tables. The theorem also proves the
translation for arbitrary nonnegative original own-singleton levels.
Its final independent reviews are
[here](../feedback/CODEX_GLOBAL_SYSTEMATIC__LOCAL_CAP_COLLAR__BY_CODEX_COLLAR_ADVERSARY.md)
and [here](../feedback/CODEX_GLOBAL_SYSTEMATIC__LOCAL_CAP_COLLAR__BY_CODEX_LOCAL_COLLAR_REVIEW.md).
Other zero-observer faces,
the actual-minimum branch and arbitrary tables remain open; this restricted
boundary exclusion is retained internally rather than counted as a global
source theorem.

Section 4 gives an exact warning for the new endpoint: even a zero-cap
observer whose Never action is optimal can lose by at least 1-nu-2epsilon
under EVERY epsilon-Nash repair of the other three players with joint
Never mass nu. That control has equilibria elsewhere and lacks the global
minimum ancestry; it refutes the unguarded repair, not Fin4.

Section 9 simplifies the selected source: fix `0<r<m` and minimize
`J_r=d_p+r nu`. Then `0<mu=f(r)<=r<m`, so every minimum has positive
Never mass and is ALL-END. A nonrealized minimum cannot have an all-zero
incoming endpoint: the actual head and arbitrary-head graft comparisons
force a neutral tail, whose iteration would reach absorbing debt `mu<m`.
There are therefore only two selected-source cases: an actual ALL-END
global minimum, or a nonrealized one with an inherited mixed zero-cap
endpoint. The two scoped Section 9 reviews are linked in the canonical
note. This does not exclude absorbing ALL-END minima; this source choice
avoids needing them as an additional case.

The existing zero-face classification in the
[absorbing source proof](CODEX_EXPENSIVE_EXIT__ABSORBING_PARTIAL_NASH_MINIMUM.md),
Sections 4--7, also applies to `J_r`: its observer-only words multiply
both debt and Never mass by the same survival. Thus after the established
generic perturbation of joining determinants, every selected minimum has
strictly positive caps. This is reused mathematics, not a new zero-face
result. The inherited endpoint need not minimize `J_r` and retains its
zero-cap constraints.

The missing global exchange must produce actual profiles whose observer
debts tend to zero and whose `J_r` stays below `mu` by one fixed positive
amount. In the endpoint case it must respect the inherited head comparison.
No such universal exchange is proved.

## Global reductions worth keeping in view

These retained packets concern broad source constraints rather than one
chosen calendar or controller:

- [Strict inverse column and all-END minima](../exports/FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md): the native source and fixed positive weight box; includes the older determinant/inverse-column argument.
- [Three-owner dispersion](../exports/UNIFORM_THREE_OWNER_TAIL_DISPERSION.md): a uniform actual-law mass bound, including limits in the augmented carrier.
- [Collision floor](../exports/NATIVE_COLLISION_FLOOR_AND_GLOBAL_MASS_DICHOTOMY.md): a quantitative actual-law collision/mass dichotomy and its conditional-tail consequences.
- [Every-cut late-tail debt](../exports/GENERAL_LATE_TAIL_DEBT_AND_END_CAP_MINIMUM_REDUCTION.md): bounds without a fixed future-owner count or calendar, with the additional END-active comparison stated separately.
- [Zero-active-payoff renewal](../exports/ZERO_ACTIVE_PAYOFF_SEMANTIC_RENEWAL_AND_SOURCE_INTERSECTION.md): absorbing approximation from the stated zero-debt closure source without assuming actual realization.

The existence-class packets in `math/exports/` have independent raw reward
criteria and complete producers. They are partial classes, not a coverage
proof for arbitrary tables. Earlier review evidence is consolidated in
[the export review record](../feedback/FIN4_EXPORT_REVIEWS.md).

## Proven obstructions to recurring shortcuts

Use these canonical arguments before opening another variation of the same
method. Their exact hypotheses matter.

- [Full-law component and local traps](CODEX_EXPENSIVE_EXIT__FULL_LAW_OBSERVER_COMPONENT_TRAP.md): an entire absorbing observer-equilibrium component can have a positive debt floor; a stronger local control also has negative singleton columns, a positive inverse column and generic joining determinants. Both games have equilibria elsewhere. Local or component minimality cannot replace global minimality.
- [Fixed-pivot pinning](CODEX_COLLAPSED_CONSUMER__FIXED_PIVOT_FULL_LAW_TRAP.md): unrestricted observer-law changes may be globally pinned when the pivot is fixed. This differs from a joint-law global minimum.
- [Full-cap thinning and continuation](CODEX_FIXED_COLUMN_VARIATION__FULL_CAP_THINNING_RENT.md): exact variation formulas and a spanning observer-equilibrium continuum do not select a branch through an arbitrary initial equilibrium.
- [Singleton-graft dual barrier](CODEX_COORDINATOR__SINGLETON_GRAFT_DUAL_BARRIER.md): singleton-only appended tails, including signed/switching drift, cannot bypass the stated global minimum while retaining the old cap menu.
- [Penalty transition boundary](CODEX_SOURCE_ESCAPE__CONSTRAINED_PENALTY_TRANSITION_BOUNDARY.md): scalar penalty and own-containing reward deformations need their real global consumer; a monotonicity assertion can already be conjecture-equivalent.
- [Finite exact-Nash incompleteness](CODEX_GLOBAL_CREATIVE__FINITE_EXACT_NASH_INCOMPLETENESS.md): an exact finite-calendar strategy grammar misses a genuine infinite absorbing equilibrium, even under its displayed generic singleton restrictions.
- [Analytic barrier draft](CODEX_JOINT_CAP_PROBE__GENERIC_ANALYTIC_GLOBAL_BARRIER_NOGO.md): an UNREVIEWED no-go for functions monotone under every root on the FULL annotation box. It does not rule out a potential restricted to the actual source carrier.

The accepted source constructions and these obstructions are the active
research record. New work should change one of the remaining implications,
produce an independent existence class, or give a genuine positive-gap
example. A renamed source, another solved local control, or a repeated
proof of an existing source does not count as an additional advance.
