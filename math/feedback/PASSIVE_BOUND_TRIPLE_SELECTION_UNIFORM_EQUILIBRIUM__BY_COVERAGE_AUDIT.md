# Coverage audit: passive bounds and selected triple returns

Reviewer: TRIPLE_CROSSINGS. Verdict: **PASS for the stated coverage scope**.
This is ordinary exact mathematics, not a Lean-checked theorem. The reviewed
export is `math/exports/PASSIVE_BOUND_TRIPLE_SELECTION_UNIFORM_EQUILIBRIUM.md`,
SHA-256 `fb8d0ebe59dd05959f09c03bcd53fc6b6cf147e562305c98abda7a2811112a14`.
This report checks the literal example and its separation from the named
accepted producer families. It does not replace the independent mathematical
reviews of the new selection theorem or its semantic consumer.

Reproducible exact checks, from the repository root:

```sh
python math/experiments/CODEX_COORDINATOR__PASSIVE_BOUND_SELECTION_CENSUS.py
python math/experiments/CODEX_COORDINATOR__PASSIVE_BOUND_CALENDAR_CHECK.py
```

Their respective SHA-256 hashes are
`9f15e9dce7bbed21f56937e508cca6451b9538cd0a558a6022308f7c09d25e19` and
`cc665acf7b42665212688f13218bb0c4ea7ee43c929805711b5abe530bc8edf9`.
Both checkers are fixed literal-table certificates; they have no exploratory
parameter flags or floating-point decisions.

## Literal separating table

The literal table is Section 7 of the reviewed export. Equivalently, use the
entire table of Section 7 of
`math/exports/PASSIVE_THRESHOLD_UNIFORM_EQUILIBRIUM.md`, with

 eta=-3, K=-1/4, p=-1/10000, R=-25, t=987,
 Z0(123)=-1000 instead of -8, Z0(01)=-1/100 instead of0,
 original own levels all1.

Thus Z2(02)=-1, Z1(12)=1/4 and Z2(12)=-1/10000. All other entries
are unchanged. Every nonsingleton participant reward of player0 is now
strictly negative, and every pair in123 has a strictly negative participant.
The selection census checker contains all 60 native entries, the exact
arithmetic and the finite algorithms below. The checks pass:80 stationary patterns,65 sure-first
patterns,14 child duals, all return-role and pair selectors, three universal
weight duals, and all proper marked-set safe-edge exclusions.

## 1. Complete stationary and actual-punishment root exclusions

For hazards q define H_i=prod_(j!=i)(1-q_j), P_i as the native passive
coalition expectation, Q_i as the native Quit expectation, and

 F_i=(1-H_i)Q_i-P_i,
 L=(-1000,-8,-10,-12), G_i=Q_i-P_i-H_i L_i.

Stationary Nash requires F_i<=0,=0,>=0 at quiet,mixed,sure owners. Every
actual original continuation cap after subtracting own level1 is at least
L_i: its own-Never alternative is a mixture of native passive rewards and
native original-Never level-1. The L_i above are the exact minima of those
finite sets. A sure-first Nash root with any actual punishment tail therefore
necessarily satisfies the corresponding G signs. For a mixed or quiet owner
there is another sure owner, making H_i=0, so the G comparison is exact.
For the unique sure owner, replacing its cap by L_i weakens its Quit test.

The independent exact implementation follows the finite procedure in
Section 6.1 of
`math/exports/THREE_OWNER_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md`, with no
large-K row relaxation. It constructs every F,G directly from this table.
For each of the80 nonzero stationary patterns and65 sure-first patterns it
substitutes fixed0/1 hazards and converts each remaining polynomial to its
tensor degree2 Bernstein coefficients. All coefficients are exact integers
after clearing positive denominators. Equalities reject a box with strictly
one-signed coefficients; inequalities reject their forbidden strict sign.
De Casteljau subdivision uses integer formulas and a least-subdivided-axis
order, left child first. The transformed mixed equations Gamma_SS^{-1} F_S=0
(or G_S=0) are also included; they are linear combinations of required zeros.

No origin box is silently discarded. On a no-sure mixed set S of size>=2,
write F_S=-Gamma_SS q+R(q), where all R monomials have total degree>=2.
If c_i is the sum of absolute coefficients of R_i and
D=max_i sum_j |(Gamma_SS^{-1})_ij|c_j, a nonzero solution has
||q||_infinity>=1/D. The checker computes D and chooses an integer E with
2^-E<1/D, rejecting only boxes wholly inside [0,2^-E]^S. Every relevant
principal Gamma matrix is exactly nonsingular. Sole mixed-owner faces are
excluded by their negative singleton witnesses, and q0=0 with mixed2 and
q1+q3>0 is excluded as follows. Put p=-1/10000>-2. Since
Q2>=p q1(1-q3) and P2=-2q1(1-q3)-q3,
F2>=q1(1-q3)[2+p(1-H2)]+q3>0. This extends the original p=0 shortcut
with a checked strict inequality; no p=0 sign test is reused incorrectly.

Result: all80 stationary patterns close in891 subdivision nodes; all65
sure-first patterns close in256 nodes. Every pattern is counted, including
those closed analytically or at a pure vertex. There is no unresolved box.
AllNever fails because original own rewards are1. Stationary approximants
cannot escape at vanishing hazards either: the unchanged singleton matrix
has a negative entry in every column and nonsingular principal matrices,
so its normalized zero-hazard complementarity limit has no admissible
support, as proved in the cited source's stationary-limit argument.

This excludes all stationary-output jackpot and weighted-collision producers,
and every sure-first producer with arbitrary actual continuation caps. It is
not an all-behavior positive regret gap.

## 2. All invariant-domain selectors

The safe-positive edges j->i satisfy Gamma_ij>0 and Z_i(ij)<=Gamma_ij.
They include 0->1,1->0,0->2,2->1,2->3,3->0, hence are strongly connected.
For any nonempty proper marked set C choose such an edge entering C. A sole
j root with hazard epsilon, u_j=u_i=0, and all other continuation coordinates
positive of order epsilon is Nash and makes every C output positive. Choose
those other coefficients larger than1+|Gamma_kj|+|Z_k(kj)|. The marked
recipient i has output epsilon Gamma_ij>0 and its Quit offer is no larger.
Thus every proper marked-set invariant fails arbitrarily close to input0.

For the full marked set take odds x1=20epsilon,x2=epsilon,x3=epsilon/1000,
put q_i=x_i/(1+x_i),q0=0,u0=0, and set the active continuations to

 u1=-347epsilon/1000+epsilon²/500,
 u2=20001epsilon/500+3epsilon²/50,
 u3=139epsilon+140epsilon².

These are exactly the active indifference map. The active Quit numerators
(after multiplying positive opponent denominators) are

 3epsilon/20+11epsilon²/1000,
 epsilon/1000+epsilon²/25,
 100epsilon+20epsilon².

All are positive. The passive0 current numerator is
59003epsilon/1000-47997epsilon²/200-20epsilon³, positive for small epsilon.
Its Quit numerator is -8epsilon/25-20021epsilon²/50-epsilon³/10<0.
Thus quiet0 is Nash, u1<0, and every output is positive. These proper roots
have inputs tending to0 and refute the full-set invariant as well.

Every passive reward interval contains0 in its interior on this table.
Consequently all15 marked choices fail on every open neighborhood of0,
including arbitrarily small inflations of full or passive reward boxes and
all positive recipient scalings. This rules out the earlier one-step
Nash-invariance consumers, not only one raw sufficient criterion.
The original passive-threshold criterion also fails on all24 relabelings:
only player0 has no positive participant reward; each prospective row1 in
123 has a strictly positive pair reward to one of the other two owners.
The negative-K extension fails because p=-1/10000>K F(R)=-639/26800.

The calendar checker proves a stronger domain-specific control. Using the nine
ordered deterministic calendars
(1,2), (1,14), (4,3), (5), (8,6), (8,7), (10), (11), (13), where the integers
are coalition bitmasks, it builds their exact paired (payoff, own-Never payoff)
vertices. Their convex hull contains (v,v) whenever ||v||_1<=1/1000: inversion
of the nine-by-nine augmented vertex matrix gives strictly positive barycentric
weights at all eight vertices v=+/-e_i/1000. It then checks the fourteen
proper-marked controls above and the full-marked control at epsilon=10^-6
inside this hull. This excludes every universal marked-set invariant even
on that closed paired-calendar convex outer domain. It makes no claim that
these convex combinations are actual independent stopping profiles.

## 3. All prior return and reset role selectors

The singleton and pair sign screen used by the finite-core, direct-return,
signed-return and joint-return families leaves only the identity role tuple,
as independently enumerated by the checker. For that tuple the joint02
native owner2 value is x Z2(02)=-x<0. This violates the required positive
return value for every physical root, without choosing a particular cubic.
The finite-singleton-split entrance allows Z2(02)<=Gamma20, but its core
producer uses the physical positive variable alpha=1/K; it requires K>0.
Its signed singleton-role alternatives are separately exhausted by the same
sign census. No unspecified existential large-K threshold is evaluated here.

For a joint023 return, P3=Q3=0 uniquely forces
b=319/1066 and x=319/3475. Its two row2 contributions are
Q2=-x<0 and Q2^3=3-103x=-22432/3475<0. Thus the current row2 value is
negative for every positive odds lambda, and every root selector fails.

The positive-continuation pair variant requires both native participant
rewards of its selected pair to be strictly positive. None of the six pairs
has that property. The more recent quadratic two-pair reset requires an
oriented macro pair(i,j) with Z_i(ij)<0, Z_i(ij)>Gamma_ij, Z_j(ij)>0 and
Z_j(ij)>Gamma_ji. The first-side candidates are 02, whose mate reward is now -1, and 21,
whose mate increment is 1/4-1/2=-1/4. The checker exhausts all 12 oriented
pairs; none satisfies both sides. Hence all24
reset role assignments fail before its quadratic selection.

## 4. All14 children and withdrawal weight choices

Use the relaxed F_A,J_A rows and nonnegative lambda,mu from Section 6.6 of
`math/exports/THREE_OWNER_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md`. Singleton withdrawal gains
are replaced by0, future gains by their positive parts, and the Never row
is omitted; these changes enlarge all five actual withdrawal certificate
families. The following exact positive-LHS/nonpositive-RHS combinations
therefore exclude patient,deadline,evaluated-security,terminal-security and
cancellation variants over every nonnegative weight choice.

 C       o   combination        LHS       lambda coefficients    mu coefficients
 0       3   J0                  2         (0)                    (0)
 1       2   J1                  19999/10000 (0)                    (0)
 2       0   J2                  9/10      (0)                    (0)
 3       1   F3                  3         (0)                    (0)
 01      3   J0                  2         (0,-3)                 (0,0)
 02      3   J0                  2         (0,-3)                 (0,0)
 03      1   F3                  3         (-3,0)                 (0,0)
 12      0   F2                  1         (-1/2,0)               (0,0)
 13      2   J3                  4         (-97,0)                (0,0)
 23      0   J2                  9/10      (0,-101)               (0,0)
 012     3   J0                  2         (0,-3,-3)              (0,0,0)
 013     2   J3                  4         (-23,-97,0)            (0,0,0)
 023     1   F0+F2+2F3           7/2       (-5,0,0)               (0,0,0)
 123     0   J123                995       (0,0,0)                (-2,-3,-7)

The checker computes every row from the literal table and verifies all signs.
Thus no sequence of these raw child lifts can start successfully. Arbitrary
strategically selected child extensions beyond these certificates are not
claimed impossible.

## 5. Weight, matrix and finite raw template selectors

With H_A=sum_i w_i Z_i(A), J_A the outside joining increment, and
k(A)_i=Z_i(A+i), the coefficient vectors of three necessary row combinations
are, respectively,

 H12+H1+H3=(-6,-11/4,-30001/10000,-8) dot w,
 4H2+H1-3J02=(-1,-1,-2,-86468/29) dot w,
 k(01)+k(2)=(-11/100,-3/4,-100,-110) dot w.

All are strictly negative for every nonzero nonnegative w. They exclude the
full-proper-payoff, support-filtered, and forced-Quit-floor weighted criteria,
including their finite weight menus. The first combination is deliberately
updated: the earlier H12+H1 combination alone no longer works at K=-1/4.

The first dual also excludes every weight in
`math/exports/MARKED_SUPPORT_ORIENTATION_LEDGER_UNIFORM_EQUILIBRIUM.md`:
its first raw premise requires H_a(S)>=0 for every nonempty proper S.
Negative-index selection in that accepted theorem therefore does not already
cover this literal table.

The singleton matrix and its exact principal determinants/inverse are
unchanged. Thus the matching, signed Hamiltonian, no-negative-pair,
fixed-reference ratio, cyclic-child and passive-inverse screens in Sections6.3
and 6.5 of
`math/exports/THREE_OWNER_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md` remain
excluded over every stated labeling and weight selector. Each matching still has a negative pair joining increment;
only triple023 has nonnegative inverse, with outside row(-7/10,9/10,-1/5).
Only two recipients qualify for the scalar singular circuit, even after
Z1(12) becomes positive, since its singleton mate Gamma12 is positive.
The fixed-matrix reference ratio Gamma12/Gamma10 remains1/4, not1/2.

The unique premium trap is123, with participant vector(11,2,1).
The accepted joining-attractive source in
`UniformEquilibrium/Quitting/Classification/JoiningAttractiveCoreGenericReturn.lean`
requires positive joining gaps. The source in
`UniformEquilibrium/Quitting/Classification/SignedPairCoreBadRoot.lean`
requires a premium core of size two. The source in
`UniformEquilibrium/Quitting/Classification/MixedSignTripleCoreSelectedReturn.lean`
requires positive reciprocal joining products, whereas the core has
c_13*c_31=-97*12 and c_23*c_32=4*(-101). These requirements fail under every
relabeling. Every
marked-block criterion fails: the positive singleton graph forces the marked
set to be all players, and the first block meeting123 has strictly positive
participant sum for every positive weight. The weak joining-attractive core
fails at Z1(12)-Gamma12=-1/4; the triple joining gaps remain(2,3,7), and the
mixed-trap leave comparison still fails at T=12 with gap7. Poisoning the
passive coordinate Z0(123) leaves these participant obstructions unchanged.

These are complete comparisons with the named accepted raw/implemented
producer families. They do not claim to exclude unspecified maximal
neighborhoods of qualitative existence theorems, or arbitrary hypothetical
strategic extensions. Subject to independent validation of the new
index-selected producer, this table supplies an actual new UE coverage
witness beyond the inspected accepted capabilities.

The strict calibration permits an open reward neighborhood in the NEW raw
index class when its explicit coefficient guards are used. This report does
not infer such a neighborhood merely from pointwise absence of old certificates,
and makes no quantitative claim about older qualitative existence radii.
