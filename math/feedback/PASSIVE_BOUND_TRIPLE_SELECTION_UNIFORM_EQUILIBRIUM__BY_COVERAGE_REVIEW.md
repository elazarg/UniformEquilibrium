# Independent coverage review of the selected-index separating table

Reviewer: INVARIANT_GEOMETRY. Ordinary mathematics, not Lean checked.
This report audits the literal table and prior-producer coverage. The new
raw index theorem and semantic consumer have separate mathematical reviews.

Reviewed artifact: `math/exports/PASSIVE_BOUND_TRIPLE_SELECTION_UNIFORM_EQUILIBRIUM.md`,
SHA256 `fb8d0ebe59dd05959f09c03bcd53fc6b6cf147e562305c98abda7a2811112a14`.
I inspected the complete frozen packet, including its scope, literal table,
strict original-reward neighborhood, architecture-boundary controls and
coverage wording. Its Section 7 uses a different full-set crossing from the
exact checker below; its five leading coefficients and its positive-index
pair control agree with direct expansion of the same literal table.

Use the complete canonical native table with

 eta=-3, K=-1/4, p=-1/10000, R=-25, t=987,
 Z0(01)=-1/100 and Z0(123)=-1000,

all other entries unchanged and original own levels all1. Thus Z2(02)=-1,
Z1(12)=1/4 and Z2(12)=-1/10000. The new general mixed-core criterion accepts
this table through its INDEX branch; the pair12 cannot be bad because its
player2 participant reward is strictly negative.

## 1. Independent exact-census audit

I inspected the complete polynomial/Bernstein algorithm and independently
reran it on this exact table. It closes all80 nonzero stationary patterns
in891 nodes and all65 sure-first patterns in256 nodes, with

 L=(-1000,-8,-10,-12).

The canonical reproduction is
`python math/experiments/CODEX_COORDINATOR__PASSIVE_BOUND_SELECTION_CENSUS.py`,
which contains the
complete literal table and algorithm. The independently rerun canonical source SHA256 is
`9f15e9dce7bbed21f56937e508cca6451b9538cd0a558a6022308f7c09d25e19`.
The rerun also verifies all fourteen
withdrawal duals, all return-role and macro-pair selections, the three
universal-weight duals, the safe graph, and principal singleton determinants.
There are no floating-point decisions or unresolved boxes.

The stationary endpoint gap has the sign of
F_i=(1-H_i)Q_i-P_i after multiplication by a positive absorption denominator.
The required signs are quiet<=0, mixed=0, sure>=0. For any actual original
punishment tail, its full cap minus own level1 is at least L_i: its own-Never
response mixes native passive rewards and the native original-Never level-1.
Thus G_i=Q_i-P_i-H_i L_i gives necessary sure-first signs. Every non-sure
owner then has another sure opponent, making H_i=0; only the unique sure
owner's comparison is weakened by replacing its actual cap with L_i. This
covers arbitrary actual tails, not only stationary or all-Never tails.

The tensor degree2 power-to-Bernstein conversion is exact. Integer midpoint
subdivision applies the quadratic de Casteljau formulas with a common
positive factor4. Boxes are rejected only by a forbidden strict polynomial
sign or by the separately proved origin bound. Mixed equations may be
multiplied by Gamma_SS inverse because all are required equalities.
On a no-sure face F_S=-Gamma_SS q+R(q), with all remainder monomials of
total degree>=2. The computed coefficient bound gives
||q||<=D||q||^2; every nonzero solution therefore has ||q||>=1/D. Only boxes
wholly below the smaller exact threshold2^-E<1/D are discarded. No origin
region is dropped without proof.

Both analytic skips are valid for THIS negative-p table. With q0=0 and
mixed2, write y=q1,z=q3. Then

 P2=-2y(1-z)-z, Q2>=p y(1-z),
 F2>=y(1-z)[2+p(1-H2)]+z>0

when y+z>0, since -2<p<0. This excludes the corresponding stationary faces.
On a sole mixed-owner face choose the quiet witness3,2,0,2 for owner0,1,2,3
respectively. Each satisfies Gamma_ij<min(0,Z_i(ij)), so
F_i=q_j[q_j Z_i(ij)-Gamma_ij]>0 throughout the proper interval. Pure
patterns are checked directly; every other box closes by subdivision.

AllNever fails because original own rewards are1. Stationary approximate
equilibria cannot escape at zero hazards either: after normalization, Quit
comparisons give Gamma*x>=0 and Never comparisons give complementarity on
positive support. Every principal support of size>=2 is nonsingular; a
singleton has a negative column entry. This is the stationary-limit argument
of Section6.1 in
`math/exports/THREE_OWNER_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md`, with unchanged singleton
matrix. Thus the census excludes asymptotic stationary-output producers,
not merely one selected exact root. No all-behavior regret gap is claimed.

## 2. All15 marked invariants fail even inside the calendar diagonal

The safe edges j->i satisfy Gamma_ij>0 and Z_i(ij)<=Gamma_ij. They include

 0->1, 1->0, 0->2, 2->1, 2->3, 3->0,

and are strongly connected. For every proper nonempty marked C choose an
entering edge j outside C, i inside C. Put q_j=epsilon, all other hazards0,
v_j=v_i=0, and

 v_k=epsilon[1+|Gamma_kj|+|Z_k(kj)|] for k notin{i,j}.

For sufficiently small epsilon this is exact Nash, min_C v=0, and every
C output is positive. The safe-edge inequality supplies the anchored
receiver's comparison; every other quiet gap and output is strictly positive.
Thus all14 proper marked choices fail arbitrarily near0.

For the full marked set take odds x1=20epsilon,x2=epsilon,x3=epsilon/1000,
q0=0, and

 v=(0,-347epsilon/1000+epsilon^2/500,
       20001epsilon/500+3epsilon^2/50,
       139epsilon+140epsilon^2).

The active equations are exact. Their Quit numerators are

 3epsilon/20+11epsilon^2/1000,
 epsilon/1000+epsilon^2/25,
 100epsilon+20epsilon^2,

all strictly positive. Quiet0 has nonpositive Quit offer but positive
Continue numerator

 59003epsilon/1000-47997epsilon^2/200-20epsilon^3.

The input has v1<0. This excludes the full-set invariant as well.

Let P be the convex hull of the150 deterministic-calendar vectors(U,Never).
This is a correlated convex outer relaxation, not the actual independent
image; none of its mixed-calendar points is asserted independently realizable.
Its diagonal slice contains the entire l1 ball ||v||_1<=1/1000. An exact
nine-calendar simplex certificate uses mask blocks

 (1,2),(1,14),(4,3),(5),(8,6),(8,7),(10),(11),(13).

The9x9 matrix with columns(U,Never,1) is invertible. Its inverse sends each
(±e_i/1000,±e_i/1000,1) to strictly positive weights summing1. Convexity
proves the ball inclusion. `math/experiments/CODEX_COORDINATOR__PASSIVE_BOUND_CALENDAR_CHECK.py` reconstructs
these certificates without retaining large weights and explicitly verifies
all15 root controls at epsilon=1/1000000, including exact diagonal membership.
All checks pass with fractions and symbolic rational inversion. Its SHA256 is
`cc665acf7b42665212688f13218bb0c4ea7ee43c929805711b5abe530bc8edf9`.

Consequently every global, full-box, passive-box and calendar-diagonal marked
coordinate-minimum invariant fails at this table. This is an all-selector
comparison, not failure of one convenient root. It does not exclude selected
GOOD-root criteria; the new theorem supplies precisely that different source.

## 3. Other prior producers and the strict raw neighborhood

I read the complete author audit, retained as
`math/feedback/PASSIVE_BOUND_TRIPLE_SELECTION_UNIFORM_EQUILIBRIUM__BY_COVERAGE_AUDIT.md`,
and inspected the applicable
recipes in Sections6.2–6.6 of the three-owner audit, and reran its updated
finite calculations. The author audit supplies the consumer-scope comparison;
my independent checks confirm that the changed entries are accounted for:

- The complete return-role screen leaves identity, where current owner2
  value is -x<0. The finite-singleton split uses physical alpha=1/K>0,
  excluding K=-1/4. Joint023 has both row2 contributions negative at every
  candidate. None of the six pairs has two positive participant rewards;
  all twelve macro-pair orientations for the quadratic reset fail.
- The fourteen updated child duals have positive left sides and nonpositive
  coefficients over every nonnegative weight. They cover the five named
  withdrawal families and successive lifts from those certificates. The
  poisoned row uses J123 with left side995 and coefficients(-2,-3,-7).
- The universal-weight duals remain strictly negative in every coordinate
  after the negative-p and Z0(01) changes. The matching, inverse, singleton,
  exact-reference-ratio and participant-trap selectors retain their stated
  obstructions. The positive singleton graph forces any ordered-anchor
  marked set to be all4; coalition123 then defeats every ordered block and
  positive weight. The old passive-threshold relabelings and negative-K
  sufficient region also fail.

This strict calibration gives an open existence region in all60 ORIGINAL
reward coordinates. In the general criterion U=10,c21=19999/10000,
X=100000/19999; its computed F,G are positive, 0<Y<1, B>95, and
Delta=164667791429497/13198990000>12000. Alpha is190 and its endpoint
correction is190+58X>0. Every other sign or weak raw guard is strict here,
except native own-zero identities, which hold by definition. In particular
J21=-1/10000<0 strictly excludes bad pair12 throughout a small neighborhood;
all non-singleton player0 participant rewards are strictly negative, and
all original own levels are1>0. The maximum defining U is continuous, and
the remaining expressions are continuous with positive denominators.
Therefore a positive full-dimensional reward neighborhood satisfies the raw
criterion. No quantitative radius or claim that every neighboring point was
outside older producers is needed or asserted.

Verdict: the literal table is an additional UE coverage witness against the
named accepted raw/implemented producer families, conditional only on the
separate mathematical approval of the new theorem. The all15 calendar-domain
comparison is independently verified here. This audit does not exclude
unspecified robustness neighborhoods, hypothetical conditional mechanisms,
or unrestricted strategic child extensions. No Lean verification is claimed.
