# Matching joint producer: independent falsification

Identity: CODEX_NOETHER. Ordinary mathematics, not checked in Lean here.

Status: the general inverse-positive producer and strict signed matching
extension are accepted by my independent matrix, fixed-point, payoff,
full-deviation and raw-coverage review, at manuscript SHA256
`c1fab38c7e5c15dc00e7784f8ca0c929cdbd0cc6b489e54c8925f6c7ba242ad0`,
from “An inverse-positive producer with two unequal joint rows” through EOF.
The separate complete 647-line handoff
`notes/CODEX_BROUWER__MATCHING_JOINT_PHASE_UNIFORM_EQUILIBRIUM.md` is also
accepted, at SHA256
`c47039fd1d48eb76e05ee5105021f39485de6003b62dd46c4aef75ddb1f40653`,
including its changed pairwise-constant fixture and weak-boundary extension.
The complete 310-line arbitrary-passive extension
`notes/CODEX_BROUWER__MATCHING_JOINT_PHASE_ARBITRARY_PASSIVE_REWARDS.md`
is separately accepted at SHA256
`c97c1320ef98c0d68fb866ba532effbe1d2c666f99b328ba3d08b4a3fcb5c6c6`.
It removes every passive K sign restriction using a noncircular scaled-point
outer bound; its mixed-sign fixture strictly enlarges the previous raw class.
The strongest consolidated 723-line artifact
`exports/CROSSED_MATCHING_UNIFORM_EQUILIBRIUM.md` has also passed
the complete assembly/delta check at SHA256
`4757f61a3e57ea6f328d1642136d52d4db2b012a160cda487e1ff167050e4a2c`.
The separate constant-inverse theorem correctly retains K≤0.
MORSE's separate below-floor §29 candidate is also independently accepted at
whole-file SHA256
`84cf88f403ed0004abc2c7bf107f0d9b8e5b4b5312a9ef14da9ebdbafedc31d9`,
from “A negative scheduled-premium arm of the matching two-phase producer”
through EOF. Its substantive review is
`feedback/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION__BY_CODEX_NOETHER.md`.
The complete 660-line below-floor standalone is separately accepted at
SHA256 `6b75ada2ad8e675fd32216d0f1d98fbfdfee6ef5a47d0b7ca8aed05eb2d0e3ca`:
`exports/BELOW_SINGLETON_JOINT_PHASE_UNIFORM_EQUILIBRIUM.md`.
This notebook retains the independent boundary calculations and the proved
extension of the raw existence class. The substantive review is in
`feedback/CODEX_BROUWER__MATCHING_JOINT_PRODUCER__BY_CODEX_NOETHER.md`.
No other conference feedback was read.

The complete opposite-participant-sign producer, strengthened average caps
and sixty-coordinate coverage table passed two independent base and final
reviews. The current canonical artifact is
`exports/OPPOSITE_SIGN_MATCHING_PHASE_UNIFORM_EQUILIBRIUM.md`,606lines,
SHA256 `2b9f54370677ec176749a0a9c6c008bdb56d5733594d85f60a101374e148ac35`.
Its original owned candidate and exploratory branch below remain derivation
history. Current independent research is the separate one-shot join-monotone
anchor mechanism at this notebook's end; its whole-family proof and exact
source-separating table are complete ordinary candidates, not independently
reviewed or exported. Its frozen self-contained manuscript is
`notes/CODEX_NOETHER__ONE_SHOT_ANCHOR_NEGATIVE_JOIN_NECESSITY.md`,377lines,
SHA256 `72e18f442d25d6225b96e022b42c573f3542809fc7ce955ce9dfb66b7ad7b331`.

## Question and finite data

There are four players, private independent Continue/Quit randomizations,
public past actions, one live state with zero stage reward, and fifteen finite
terminal reward vectors r(S). Never pays zero. Unilateral replacements are
arbitrary full behavioral strategies. Write s_i=r_i({i}) and
Γ_ij=r_i({j})−s_i. Let f=(01)(23), a=(02)(13), o=f∘a. The schedule
alternates A=02 and B=13. Its participant increments and passive increments are

    Π_i=r_i({i,a(i)})−s_i,
    K_i=r_i({f(i),o(i)})−s_i.

The strict candidate requires Γ_i,f(i)>0, Γ_i,a(i)=−b_i<0,
Γ_i,o(i)<0, Π_i>−b_i, K_i≤0, and all twelve outsider joins bounded
by s_i. It claims a fixed uniform-equilibrium target for every such raw table,
with an internally produced exact proper period-two terminal Nash profile in
the standard-Q branch. The alternative branch uses the existing original-game
no-UE-to-standard-Q theorem. No strategic witness is a hypothesis.

## Bounded exact-source inspection

The source route was selected through `docs/FRONTIER.md` and
`docs/TOOLKIT.md`, followed by narrow declaration searches. I inspected:

- `isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff`
  (`UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`),
  with no own-singleton sign, reward normalization or strategy premise;
- `quittingProjectiveLCPMatrix`
  (`UniformEquilibrium/Quitting/Projective/SingletonLCP.lean`) and
  `quittingSingletonMatrix`
  (`UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`),
  both receiver first, singleton owner second;
- `IsStandardQ`, `IsStandardLCPSolution`, and `lcpResidual_def`
  (`MathUE/LinearProgramming/CopositiveQ.lean`), using q+Γz≥0;
- `isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
  `isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
  (`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`), requiring
  exact policy recursion, exact local root Nash, and every deleted-player
  cycle contraction;
- the literal pure Quit/Continue definitions and
  `quittingRootExpectedPayoff_update_eq_endpointMix`
  (`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`);
- `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
  (`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`),
  with arbitrary signed rewards and no supplied limiting target;
- raw comparison definitions in the supportwise/product-low, signed
  four-cycle, passive-row inverse, conditional face-gap, affine potential,
  signed influence, and nonnegative-weight chamber files cited in the review.

These were read-only source inspections. No Lean command, build, new Lean
file, Git stage, commit or push was performed. This is not a new certification
of any library declaration. No literature result is imported into the new
matrix/fixed-point argument.

## A proved weak-boundary existence extension

Assume instead the weak raw inequalities

    Γ_i,f(i)≥0,       Γ_i,a(i)≤0,       Γ_i,o(i)≤0,
    Π_i≥Γ_i,a(i),    K_i≤0,

with the same twelve caps. Thus the participant comparison means exactly

    r_i({i,a(i)})≥r_i({a(i)}).

Using the accepted strict theorem, every table in this weak class has a fixed
uniform-equilibrium payoff. This assertion is a mathematical consequence,
not a further supplied-strategy interface. Its complete standalone packaging
has passed the separate byte-bound review recorded above.

For δ>0 form r^δ by changing only the twelve off-diagonal singleton
coordinates: increase r_i({f(i)}) by δ, and decrease each of
r_i({a(i)}), r_i({o(i)}) by δ. Preserve own singletons and all
nonsingleton coordinates. Its singleton sign inequalities are strict. If
b_i=−Γ_i,a(i)≥0, then b_i^δ=b_i+δ>0 and

    Π_i≥−b_i>−(b_i+δ)=−b_i^δ.

All passive increments and all twelve caps are unchanged. The strict
theorem therefore gives UE for r^δ, and every coordinate change has absolute
value at most δ. The inspected reward-closure theorem supplies one fixed UE
target for r. The approximating targets may vary; no target convergence is
silently assumed. This removes degenerate raw boundaries from the existence
problem, while making no exact proper-profile claim at those boundaries.

## Exact simultaneous boundary test

Take favorite Γ entries 13/4, both harmful entries −1, and any real
singleton vector s, for example (−4,−1,0,7). Put Π_i=−1/2,
K_i=0 and all twelve caps at equality. Set X_i=1, hence q_i=1/2.
Then

    U_i=s_i−1/4,       W_i=s_i+1/2.

The original ΓX entry is 5/4. The moved negative part changes the
scheduled-mate coefficient to −3/4, giving (BX)_i=3/2, while
N⁺_i=(1/2)(1+1+1)=3/2. Active Quit and Continue equal U_i;
passive Continue equals W_i and passive Quit equals s_i. Thus negative
own singletons, negative participant increments, K=0 and cap equalities
can occur simultaneously. Signed centering has not translated Never.

## Exact failure at the excluded participant boundary

Take Γ's favorite entry H>2 and both harmful entries −1, but set
Π_i=−1 and K_i=0 for every i. Γ has strictly positive inverse, yet
the original odds equations have no positive solution. Indeed

    ∑_i(ΓX)_i=(H−2)∑_i X_i>0,
    ∑_iN_i(X)=−∑_i X_i²/(1+X_i)<0.

This is the minimal failed extension: the exact proper two-phase producer
cannot simply replace Π_i>−b_i by Π_i≥−b_i. It is not a UE
counterexample. If all outsider caps hold, either scheduled pair is an
exact pure terminal Nash coalition: its participants are indifferent to
withdrawal and its outsiders receive s_i and cannot gain by joining.
Reward closure proves the more general weak existence extension above.

## Exact noncoverage calculations for the asymmetric table

For the author's fifteen-row fixture, independent rational substitution gives

    det Γ=7171377/4096,
    ΓX=(37/32,33/40,157/240,211/120),
    U=(549/272,183/104,61/36,61/24),
    W=(183/68,427/208,61/30,305/96).

Every active endpoint equality and every passive Continue equality holds.
The four passive Continue−Quit margins, ordered (A,1),(A,3),(B,0),(B,2), are

    181/104,       275/96,       5419/2380,       34/21.

The premium traps are exactly 02, 13 and I. Pair traps rule out a proper
greatest core and the all-traps-size-at-least-three charge criterion. All
four players have a negative participant premium somewhere, so there is no
protected leaver. Weighted floors fail at the grand coalition, where every
coordinate is below its own singleton. For the full trap and T=02, the
mixed-charge aggregate joining sum is 1>0, so mixed pair/charge coexistence
does not rescue this fixture. Product-low fails at the sure02 law; both
active Quit premiums are strictly positive.

The nonnegative-weight terminal chamber also fails. If λ≥0 satisfies
the weighted singleton upper bound at both scheduled pairs, adding those
two inequalities gives

    ∑_i(Π_i−1)λ_i≤0.

All four Π_i exceed one, so λ=0, contradicting the required positive
weight coordinates.

For each induced triple, its inverse has negative diagonal entries and
negative outside inverse weights. Up to simultaneous row/column order,
the triple inverse is

    [[−53/16,−1/2,−1/2],
     [−1/2,−4/53,4/53],
     [−1/2,4/53,−4/53]],

and its outside weights are (−2681/128,−53/16,−53/16).
The full inverse exit requires negative determinant, which fails here.
The sole-positive singleton graph consists of two 2-cycles; it cannot be
relabeled to a favorable predecessor 4-cycle or a favorable 3-cycle.

Every proper child fails the accepted finite quiet-lift F/J criterion.
If an outsider k has a(k) in the child, take the child singleton
A={a(k)}. Its own join gain is r_k({k,a(k)})−r_k({a(k)})>0,
whereas each child member's joining gain at A is nonpositive: the owner
has gain zero; its favorable partner has gain −69/8; its other partner
has gain −1. No nonnegative weights can satisfy J. If no outsider has
its active mate in the child, the nonempty proper child must be 02 or13.
At its full coalition, both child deficits s_i−r_i(A) are negative,
while every outsider deficit s_k−r_k(A)=1. No nonnegative weights
can satisfy F.

All fifteen pure quitting coalitions have an explicit profitable join or
withdrawal. The scheduled pairs have outsider joining gain 1/2; all other
pairs have a participant withdrawal; every triple has a withdrawal gain
10; the grand coalition has withdrawal gains (11,12,13,14). All Never
fails because every own singleton is one. These exclude pure-exit raw
producers, not arbitrary stationary mixed profiles.

## Arbitrary passive signs: independent outer-radius derivation

Status: the following load-bearing argument was independently derived before
the author's full draft, and the complete stronger handoff has now passed my
separate byte-bound review at SHA256 c97c1320ef98c0d68fb866ba532effbe1d2c666f99b328ba3d08b4a3fcb5c6c6.
Retain the strict matching signs, participant inequalities and twelve caps,
but permit every K_i to be an arbitrary real number. Write

    h_i=Γ_i,f(i)>0,       d_i=Π_i+b_i>0,
    α_i=max(−Π_i,0)<b_i,
    K_i⁺=max(K_i,0),      K_i⁻=max(−K_i,0).

Move the positive passive coefficient to the left, as well as the negative
participant square term. Define

    B(X)_i,a(i)=−b_i+α_i X_a(i)/(1+X_a(i)),
    B(X)_i,f(i)=h_i+K_i⁺ X_o(i),
    B(X)_i,o(i)=Γ_i,o(i),       B(X)_ii=0,

    N⁺_i(X)=d_i X_a(i)(X_f(i)+X_o(i)+X_f(i)X_o(i))
              +max(Π_i,0)X_a(i)²/(1+X_a(i))
              +K_i⁻ X_f(i)X_o(i).

At equality B(X)X=N⁺(X), the two moved terms exactly recover the original
passive equations for arbitrary K. After the favorite column permutation,
the new favorite coefficient is an increased positive diagonal. Off-diagonal
signs and their strongly connected graph remain strict. The original vector
u=M⁻¹1>0 satisfies M(X)u≥1. The Neumann-series proof therefore gives
B(X)⁻¹>0 on every finite closed coordinate cube. Its diagonal D(X) is
now variable; using the actual positive diagonal in the scaling is necessary.

The key point is to select the cube radius before its inverse minimum and
the resulting simplex lower bound. Set F(X)=B(X)⁻¹N⁺(X), and suppose
X>0 and F(X)=ηX with 0<η≤1. Since both other coefficients in row i
of B remain strictly negative,

    d_i X_a(i)(X_f(i)+X_o(i)+X_f(i)X_o(i))
      ≤N⁺_i(X)
      =η(B(X)X)_i
      <η[h_i X_f(i)+K_i⁺ X_f(i)X_o(i)].

Dividing by the strictly positive X_f(i) gives

    d_i X_a(i)
      <η(h_i+K_i⁺X_o(i))/(1+X_o(i)+X_o(i)/X_f(i))
      ≤max(h_i,K_i⁺).

Thus every such eigenpoint obeys

    ∑_i X_i < T:=∑_i max(h_i,K_i⁺)/d_i.

Choose R>T, then take uniform positive inverse bounds on the finite cube
0≤X_i≤R. Set κ=m_R/(4L_R). On Δκ×[r,R] the normalized image is
in Δκ. Compression at a sufficiently small r>0 follows from the same
uniform O(r²) estimate. At a fixed normalized direction on the outer
radius, F(Rx)=ηRx with η=∑F(Rx)/R. If the radial clamp fixed R,
its sign would require η≤1, contradicting the eigenpoint bound R>T.
The inner boundary is excluded by compression, and the interior fixed point
solves the original four equations. Uniform cubic expansion on a cone whose
κ itself depends on R is not needed.

An exact mixed-sign regression takes b_i=1, Π_i=−1/2, X_i=1,

    K=(1,1/2,−1,−1/2),
    h=(9/4,11/4,17/4,15/4).

Both other singleton gaps remain −1, and h_i=13/4−K_i. Every h_i>2,
so ΓP is strictly diagonally dominant with positive diagonal and strictly
negative connected off-diagonal graph; its inverse is strictly positive.
The new moved equation has BX=N⁺=(3/2,3/2,5/2,2). At q_i=1/2,
U_i=s_i−1/4 and W_i=s_i+1/2. All caps may be at equality and the
singletons may be signed. Each scheduled pair has both a positive and a
negative K outsider, so neither pure-pair arm supplies this regression.

This derivation removes the apparent circularity in the arbitrary-K
fixed-point route. The actual phase values and deviation inequalities still
depend only on d_i>0 and the twelve caps; their proof is unchanged. The weak
matching extension also retains arbitrary K under the same twelve-coordinate
reward approximation. These conclusions are accepted ordinary mathematics.
The author's slightly weaker numerator bound gives exactly the same finite
radius and is sufficient.

The complete mixed-K fixture also passes exact independent arithmetic. Its
determinant is33583397/20480 and its inverse is strictly positive. The triple
determinants are257/20 or53/4, with negative inverse diagonal entries. Every
active endpoint and passive Continue equals the claimed phase value; passive
Quit remains17/50 or31/72, with margins398/175 and2249/1152. The changed
favorite gap h₀=249/40 and K₀=1 cancel in the passive equation because
X_o(0)=1/5. The four all-sure-displacement/singleton-row-sum ratios are
−440/169,−96/37,−104/37,−112/37, pairwise distinct; hence the affine
response-quotient exclusion survives the loss of equal row sums. In the
proper-three contradiction, replace the favorite terminal level by289/40
when i=0; Π+289/40>9 still holds. No full-support exclusion is inferred.

Concrete next question: what complete producer can remove a genuinely new
remaining restriction: the matching geometry, participant comparison, or
twelve outsider caps? Their removal is not justified by this proof. The
final assembled artifact has passed its separate byte-bound acceptance.

## Independent below-floor arm and neighborhood check

The exact §29 claim uses favorite singleton gap H b_i, both harmful gaps
−b_i, common participant increment Πb_i with Π<−1, and common passive
increment Kb_i with K<(7Π+10−2H)/2. The stronger twelve collision caps
are s_i−4(−Π−1)b_i/3. Its cubic has a root t∈(1/2,1), giving q=1−t,
U_i=s_i+qΠb_i and W_i=s_i+q(Π+1)b_i/t<s_i. The cap comparison is
positive because t(1+t)>3/4. This independently checks the below-singleton
passive endpoint regime, not a variant of the positive c_i argument above.

For the complete H=3, Π=−11/10, K=−179/60 table I recomputed all sixteen
endpoints at q=1/3: active endpoints19/30, passive Continue19/20, passive
Quit1/3, margin37/60. Its actual four-odds equations vanish at X=(1/2)1.
The displayed Jacobian has eigenvalues79/72,−307/72,−41/72,269/72 and
determinant267486337/26873856. The contraction X↦X−J⁻¹E(X,r) has zero
derivative at the center, so the compact positive ball and nearby reward
ball really produce all four odds from raw data. Every passive gap remains
strict; no cap equality or normalized singleton equality is required nearby.
The endpoint recursion and three-opponent contraction give a fixed target
against arbitrary behavioral deviations, Never included, at every large
horizon. The full neighborhood is a genuine UE region.

The known arbitrary-K matching criterion fails under every relabeling.
Favorite signs force f. Schedule02/13 violates participant comparison
−1/10≥0; schedule03/12 has outsider triple rewards100>1. All pair
participant premiums are negative, excluding the general Π≥0 inverse
criterion. This separation has strict slack and persists in an open ball.

### Additional actual quiet-lift raw exclusion

Every nonempty proper child S fails the accepted nonnegative F/J condition
already at J. Let o=(03)(12). If S cuts an o-pair, choose j∈S with
k=o(j)∉S and use A={j}. The outsider joining gain is1/2. The child's
joining gains are0 for j,−7/2 for f(j), and−1/10 for a(j), hence their
nonnegative weighted sum is at most zero. If S cuts neither o-pair, the
proper nonempty S is03 or12. At A=S any outsider gains100, whereas all
child joining gains are identically zero. Thus no child and no nonnegative
weight family satisfies J. These strict failures persist nearby.

The exact five-kind withdrawal consumer
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`
also charges every actual child profile. For each proper child the author's
exact Nash witness has zero child debts and zero joint Never, but a positive
outside deviation. It therefore excludes these universal certificate
families as well; it does not exclude some separately selected safe child.

### Proper-three exclusion persists on an open reward ball

Suppose the full table is changed by at most δ≤1/1000 in every coordinate,
and a proper stationary support012 has hazards(a,x,c). Player2's Never
payoff changes from zero by at most δ, and its forced Quit changes by at
most δ. Therefore its center-table endpoint

    Q₂*=1−(11/10)a−x/2+(503/5)ax

obeys |Q₂*|≤2δ. If x≥11/1006, its a coefficient is nonnegative and
Q₂*≥1−x/2≥1/2, impossible. Thus x<11/1006. Rearrangement and the
upper bound11/10 on its positive denominator give

    a≥(1−x/2−2δ)/(11/10)
      >(1−11/2012−2/1000)/(11/10)>9/10.

For player1, write D=a+c−ac≤1 and F=D(N₁*−Q₁*). The author's
derivative remains positive already for a≥9/10: it is concave in c and
its endpoints are a+3 and91/60. Hence

    F≥F(9/10,c)=(64c²−512c+621)/200≥173/200.

Consequently the center Never-minus-Quit gap is at least173/200. Changing
the table changes each endpoint by at most δ, leaving a positive gap at
least173/200−2δ. This contradicts proper mixing. The four Klein-related
supports are all excluded on this full reward ball, not merely at its center.
Intersecting this ball with the proved root neighborhood retains new open
UE coverage beyond the actual proper-three local branch.

### Influence and potential screens

Define D_i(T)=r_i(T∪{i})−r_i(T), with empty coalition reward zero.
The influence1→0 equals−9/2 at background∅ and1001/10 at background{2}:
D₀({1})=−7/2, D₀(∅)=1, D₀({1,2})=100, D₀({2})=−1/10.
This falsifies `SignConsistentQuittingInfluence` in
`UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean`
and `IsAffineQuittingMembershipGain` in
`UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`.
Both failures persist nearby. Together with the existing matrix, premium,
guard, range, quotient and visible-cylinder checks, these are actual raw
producer comparisons, not generic absence claims about strategy languages.

The final standalone below-floor packet has passed its separate exact-byte
check, recorded in the status above. No Lean seal is claimed. The next live
question is independent falsification of the complete opposite-sign producer
in the new owned note.

## New independent mechanism: opposite participant signs

Status: this exploratory derivation has been completed and strengthened in
`notes/CODEX_NOETHER__OPPOSITE_SIGN_MATCHING_PHASE_PRODUCER.md`, including
actual raw-source separation. It remains unreviewed and unexported.
The next target is not a new isolated neighborhood. Normalize singleton gaps
to common favorable H>2 and harmful−1, but allow pair A to have Π_A<−1
and pair B to have Π_B>−1. The accepted global matching theorem cannot use
the A participant comparison; the below-floor scalar theorem cannot use mixed
signs of Π+1. Raw K_A,K_B and collision rewards must produce the odds rather
than supplying them.

A failed first mechanism used a four-dimensional rectangle for the case
Π_i<−b_i everywhere. Writing γ_i=−Π_i−b_i>0, β_i=−Π_i, K_i=−k_i,
the scaled equation at a mate-coordinate lower face X_a=1 is positive if
k_i>4γ_i+Γ_if⁺+Γ_io⁺. A large upper face is negative, so a clamp map
really yields positive odds. However the crude uniform cap required to
secure W_i=s_i−γ_iX_a lies below every nonscheduled singleton comparison.
Then every player with s_i≥0 supplies an exact pure-solo equilibrium; if
all s_i<0, all Never is already equilibrium. This mathematically sound
construction therefore does not narrow counterexamples and is not an export
candidate. The failed implication is “a raw rectangle producer necessarily
adds coverage,” not its Brouwer proof.

The promising replacement reduces the opposite-sign family to one global
branch. Put h=H−1>1, β=−Π_A>1, γ=β−1>0, c_B=Π_B+1>0,
and K_A=−k with k>0. For y>X_B lower threshold h/k, the A equation is

    −γx(1+y)²+βx/(1+x)=hy−ky²<0.

It has exactly one positive high-branch root x=x(y), the positive root of

    γ(1+y)²x²+[γ(1+y)²−β+hy−ky²]x+hy−ky²=0.

The negative constant term proves uniqueness and continuity on that interval.
Also x(y)≤(k+β)/γ=:L and x(y)→k/γ as y→∞. The B residual is

    R_B(y)=c_B y(1+x(y))²−h x(y)−K_Bx(y)²−Π_B y/(1+y).

Choose a RAW-data y_L>max(h/k,β/(h+2k)), for example one plus that
maximum, and compute x_L by the explicit quadratic formula. A lower bound
on K_B making R_B(y_L)<0 is fully raw:

    K_B>[c_B y_L(1+x_L)²−h x_L−Π_B y_L/(1+y_L)]/x_L².

The uniform bound x≤L makes R_B(Y)>0 at any

    Y>max(y_L,[hL+K_B⁺L²+Π_B⁺]/c_B).

The intermediate value theorem therefore produces an actual root y∈(y_L,Y)
and x=x(y)>0, with neither odds supplied. The key collision estimate is

    γx/[1−(1+y)⁻²]
      ≤k−[(2k+h)y−β]/[y(y+2)].

The bracket has a raw uniform positive lower bound on[y_L,Y]. Taking
δ_A=(1/2)min(k,[(2k+h)y_L−β]/[Y(Y+2)])>0 gives the strict cap
C_A=k−δ_A<k. A-player outsider joins bounded by s_i−C_A b_i are then
strictly worse than their produced W_i, while still capable of being better
than their passive payoff s_i−k b_i at a pure B exit. B-player caps at s_i
work because c_B>0. This avoids the earlier pure-exit collapse.

The completed note now contains the global parameter theorem, a complete
raw table, all fourteen actual quiet-child exclusions, and an exact
proper-three stationary exclusion. The derivation above records the earlier
coarser upper bound; the final proof uses a stronger uniform lower bound on
x and x<k/γ. Independent falsification of that complete result is the next
required check.

## Separate raw mechanism: a one-shot join-monotone anchor

Status: proved ordinary raw producer; source-coverage comparison unfinished,
not independently reviewed or exported. This line has no pair template.

Choose any player a in a finite quitting game with s_a≥0 and require
r_a(S∪{a})≥r_a(S) for every nonempty S excluding a. Choose a mixed Nash
point of the complementary finite binary game paying r(T∪{a}). Let a
Quit surely at date0, and each other player independently choose Quit0 or
Never at that point. After date0 every surviving nonanchor always Continues,
including on histories caused by an anchor deviation. This is not the
stationary profile with the same first row.

Every nonanchor's full behavioral cap reduces to its date0 binary choice,
since the anchor forces immediate absorption. If p_T is the complement's
date0 law, the anchor's immediate payoff is

    V_a=p_∅s_a+∑_{T≠∅}p_T r_a(T∪{a}).

After first-date Continue, nonempty T has already absorbed at r_a(T). On
T=∅ all opponents Never quit, so the entire later cap is max(s_a,0)=s_a.
Thus the cap after Continue is p_∅s_a+∑_{T≠∅}p_T r_a(T)≤V_a. This
includes Never and every delayed behavioral replacement. At horizon N,
nonempty outcomes have factor(N−1)/N; the empty event's delayed payoff is
at most(N−1)s_a/N, since s_a≥0. The same argument proves exact Nash at
every horizon. One fixed terminal target is delivered with error≤M/N.
No opponent-contraction assumption, reward translation, or supplied root
is needed. Every positive-gap table must consequently have, for each a
with s_a≥0, some nonempty S excluding a with negative anchor joining gain.

The source route selected through docs/FRONTIER.md was
`UniformEquilibrium/Quitting/Stationary/SingleAnchorArbitraryCompletion.lean`.
Its `QuittingSingleAnchorInducedDominance` instead requires immediate Quit
to dominate every excluded terminal reward and zero; its raw
`exists_exactTerminalNash_and_uniformPayoff_of_singleAnchorMembership`
requires the literal membership indicator coordinate. The conditional
`exists_exactTerminalNash_and_uniformPayoff_of_singleAnchor` consumes a
selected complementary Nash point and that stronger screen. The ≥2-anchor
variant is already covered by
`exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe`, and
is not a new claim. The alternate cardinal sign-balance route is already
covered by `quittingGame_exists_uniformPayoff_of_cycleBalancedSignConsistentInfluence`
in `UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean`.
Threshold-monotone polarity would produce only a pure exit, already covered
by the finite sure-set test in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.
Those duplicate routes were discarded for lack of surviving-table coverage.

### Complete exact anchor stress table

Take anchor0. All own levels are1 and the singleton matrix is favorable3
and harmful−1, with favorite matching(01)(23).

| S | r(S) |
|---|---|
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (5,−1,1,0) |
| 02 | (1,0,1,0) |
| 03 | (1,4,0,−1) |
| 12 | (100,−100,−100,1000) |
| 13 | (100,−100,1000,−100) |
| 23 | (−100,1000,−100,−100) |
| 012 | (101,1,0,100) |
| 013 | (101,−1,1,−1) |
| 023 | (−99,0,1,−1) |
| 123 | (1000,−100,−100,1100) |
| 0123 | (1001,100,100,99) |

All anchor joining gains equal1. In the anchored complement, player3's
joining gain is−1 everywhere. With3 absent, player1's joining gains are
−5 if2 Continues and+1 if2 Quits; player2's are+1 if1 Continues and−1
if1 Quits. The unique mixed point is(q_1,q_2,q_3)=(1/2,5/6,0), giving
V=(43,2/3,1/2,125/3). The anchor's first-date Continue cap is505/12<43.
Repeating that same free row forever instead makes its Never payoff504/11>43.
The minimal false implication is that the one-shot row can be made stationary.

No pure exit exists: every nonempty coalition excluding0 is joined by0;
with0 and3 present3 leaves; with0 but not3 the matching-pennies pair has
a profitable toggle. All Never loses to0. Every leave-safe base of size≥2
fails. The six pair bases01,02,03,12,13,23 have respective witnesses
(coalition,member)=(01,1),(012,2),(03,3),(012,2),(013,3),(023,3).
Their joining gains are−5,−1,−1,−1,−1,−1. The four triple bases
012,013,023,123 fail at their own coalitions for members2,3,3,1,
with gains−1,−1,−1,−1100. The full base fails by player3's99<100.

Every stationary single-anchor induced-dominance screen also fails. Anchor0
has unique complementary Nash Quit value43<100=r_0(12). With any other
anchor, free0 has strict join gain1 and must Quit surely at a complementary
Nash point. Anchor1's immediate value is≤100<r_1(23)=1000; anchor2's is
≤100<r_2(13)=1000; anchor3's is≤99<r_3(012)=100. This tests every
actual complementary Nash point, not just a selected supplied root.

### All fourteen actual nonnegative F/J children fail

If child S excludes0, use T=S: omitted0 gains1, every child joining gain
zero. If S contains0 and omits2, use T={0} for S={0} or01, T={0,3}
for03 or013: omitted2 gains1, every child joining gain nonpositive.
If S contains02 but omits1, use T=S: omitted1 gains1 at02 or100 at023,
every child joining gain zero. These exhaust all but child012.

For child012 and outsider3, its J row at T=12 forces λ_30≥100; its
J row at T=01 forces λ_32≤1. Its F row at T=012 gives

    −99≤−100λ_30+λ_32,

contradicting those two bounds. Therefore no nonnegative F/J certificate
works for any child. Some separately selected quiet-child profile is not
ruled out by this raw failure.

### Remaining exact raw-source comparisons

The singleton matrix is the H=3 favorable matching matrix already analyzed
above: positive inverse, R₀ degree+1, harmful principal pairs not Q, and
negative diagonals in each triple inverse. It therefore survives the
negative-determinant, degree-not-one and child-inverse exits. Row sums1
force every nonnegative terminal upper-bound weight to be zero. All-sure
displacements are(1,100,99,−1), distinct, so the same block-row-sum
identity excludes every nondiscrete response quotient, even after positive
affine row transports.

Both harmful pair words fail the strongest crossed matching caps because
player0 has r_0(01)=5>own1. Both also fail the opposite-sign A/B average
caps: player0's two outsider pair entries sum to6>2s_0, regardless of
which pair is assigned the negative or positive type. The signed-column
cone cannot repair this: Γ⁻¹>0 forces every column sign positive; on a
harmful word its player0 zero buffer again requires its two individual
pair caps≤1, violated at01. On the favorite word01/23, player1 has
Π_1=−2 and c_1=−5, violating the positive-column coefficient signs.
The general inverse-positive/nonnegative-participant producer also fails
at its harmful-word cap. These are actual raw failures, not a claim that
all pair-word equilibria are absent.

There is an intrinsic exclusion of every all-below-singleton proper
two-pair architecture. On either harmful word, player0's Π_0=0 and
mate comparison−1 force W_0=1+X_mate>1. On the favorite word, its
participant increment4 forces U_0=1+4q_1>1. This checks all three
partitions without assuming a neighborhood radius.

The only premium trap is I: every proper nonsingleton has some member
with no positive subcoalition participant premium inside it. At I all
premiums are positive. Thus greatest-core proper-pair/triple hypotheses
fail. No player is protected: use023 for0,01 for1,12 for2,03 for3.
At S=23 all four forced-Quit premiums are strictly negative:
(−100,−101,−101,−101), excluding every nonzero nonnegative global
forced-Quit floor. At full trap I and subset12 the outside joining
charge is1+100=101>0, excluding intermediate nonpositive-L criteria.
Sure I violates product-low and supportwise premium balance.

All ordered crossed weak-unit guards fail. Their lower axis condition
forces the selected passive partner to be the favorite, since an external
favorite has positive Γ. For the four remaining owner/favorite choices:
owner0 fails the passive1 upper face at coalition02 (gain1); owner1
fails its lower face at23 (gain−1100); owner2 fails its lower face at01
(gain−1); owner3 likewise fails at01 (gain−1). The exact axis necessity
is `quittingSingletonMatrix_nonpos_of_axis_displacement_nonneg` in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`;
the weak-unit structures and consumer are in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.
The two-owner half guard always includes a nonanchor owner and fails one
of these lower witnesses, including all relabelings.

Every conditional range blocker already fails its upper inequality for
player0. ContinueLower≤r_0(23)=−100, QuitWithoutUpper≥own1 and
QuitWithUpper≥grand1001. Their convex upper mixture is≥1>−100.
This uses `IsQuittingConditionalFaceGapRange` in
`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`.
Influence2→1 equals−101 at∅ but+6 at{0}, contradicting both
`SignConsistentQuittingInfluence` and `IsAffineQuittingMembershipGain`
in the exact stationary files cited above.

The favorable graph is a matching, not a four-cycle or cyclic three-child;
every row has two harmful singleton comparisons, so the unique-negative
paired and integral-tournament patterns fail. No off-diagonal Γ entry
is zero, excluding the owner-risky literal family. The explicit visible
period-three cylinder requires all participant pair gap ratios near zero;
our pair01 ratios4 and−2 violate its radius1/50000000, invariant under
positive affine transports. This does not exclude all unspecified local
proper-three neighborhoods: no membership radius for those existential
sources is supplied, and no absence of arbitrary proper-three stationary
profiles is claimed.

Current result: the one-shot raw family and a complete table outside the
compared actual producers are now proved ordinary mathematics. Its whole
completion scope is one nonnegative-own, join-monotone coordinate and
arbitrary rewards for every other player, not a local root perturbation.
The next required question is independent falsification of significance
and the transient behavioral consumer, before any export is considered.
