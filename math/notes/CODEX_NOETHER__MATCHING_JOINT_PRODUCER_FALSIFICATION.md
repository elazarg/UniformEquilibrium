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
history. The separate one-shot join-monotone anchor mechanism passed both
independent substantive and final-assembly reviews. Its current internal
artifact is `notes/ONE_SHOT_ANCHOR_UNIFORM_EQUILIBRIUM.md`; the original
reviewed447-line version had SHA256
`64cbf15fe912af117ee42d6d32a29806a8c72316cf88d28a7a8f85d06bdb6f02`.
Its frozen historical377-line manuscript is
`notes/CODEX_NOETHER__ONE_SHOT_ANCHOR_NEGATIVE_JOIN_NECESSITY.md`,377lines,
SHA256 `72e18f442d25d6225b96e022b42c573f3542809fc7ce955ce9dfb66b7ad7b331`.
Current independent research: the finite Nash-regret/CCE producer, all-base
extension and exact behavioral/horizon proofs passed two independent reviews.
However their ENTIRE UE class is already consumed by the implemented
punishment-priced `PersistentBaseConcreteGap.lean` alternatives, as proved
at this notebook's end. Their additional-UE-coverage claim is WITHDRAWN.
The early table also has a literal patient-withdrawal certificate. The later
three-response-cycle family genuinely defeats every raw withdrawal kind and
the compared pair tests, but that does not defeat the broader transient
punishment source. The correct mathematical value is an internal finite LP
recognizer and stronger same-profile/all-horizon theorem, not an export-level
new counterexample restriction. No frozen export was changed.

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

## A global finite Nash-regret restriction on every counterexample

Status: complete ordinary producer and necessary-condition proof, not an
export. Whole-class inclusion into an existing punishment-priced source is
proved in the final section; no new UE counterexample exclusion remains.
This is a global finite LP recognizer on arbitrary game data and every
anchor, not a modification of a radius or supplied stopping certificate.
Two exact table tests follow. The early LP-positive table is covered by a
literal patient-withdrawal certificate and is not an increment witness.
The final strict three-response-cycle table instead separates all fourteen
children from every implemented raw withdrawal kind in an explicit full
reward neighborhood; its additional finite source comparisons are recorded
with their actual scopes. Neither table claims absence of all proper-three
stationary roots.

### Finite data and the raw LP

Let I be any nonempty finite player set, r arbitrary signed terminal data,
live payoff zero, and Never zero. Information, private independence and full
behavioral replacements are as in the anchor theorem above. Fix any player
a, without any own-level sign assumption, and put J=I∖{a}.

Define the complete anchored binary game

    u_j(T)=r_j(T∪{a}),              j∈J, T⊆J.

For b∈{Continue,Quit}, write T^{j,b} for the coalition obtained by fixing
player j's action to b. Define the original-game anchor gap and the free
players' pure-action regret margins by

    g_a(∅)=min(s_a,0),
    g_a(T)=r_a(T∪{a})−r_a(T)        when T≠∅,
    R_{j,b}(T)=u_j(T)−u_j(T^{j,b}).                    (L1)

Let C_a be the polytope of laws ν on the finitely many T⊆J satisfying

    ν_T≥0,  ∑_Tν_T=1,
    ∑_Tν_T R_{j,b}(T)≥0             for every j,b.      (L2)

This is the coarse-correlated-equilibrium polytope of the anchored finite
game, with both unconditional pure deviations tested. It is nonempty:
the coalition law of any internally selected mixed Nash point satisfies
(L2). It is compact. Thus the finite raw minimum

    v_a(r)=min_{ν∈C_a} ∑_Tν_T g_a(T)                  (L3)

is attained. All coefficients come from r. Neither ν nor a product Nash
point is an additional input. The test uses correlated laws as a convex
outer relaxation only; the actual original-game profile uses private
independent randomization.

### Original-game producer and all-counterexample restriction

If v_a(r)≥0 for any anchor a, choose any mixed Nash point μ of its anchored
binary game internally. Its product coalition law p belongs to C_a, so
E_p g_a≥0. Prescribe a Quit surely at date0, the free μ coordinates at
date0, and every free player Never after date0, including on histories
created by an anchor replacement. Prescribe the anchor Continue later.

As before, every nonanchor replacement reduces to its date0 binary choice.
The anchor's two full terminal caps are exactly

    V_a=p_∅s_a+∑_{T≠∅}p_T r_a(T∪{a}),
    C_a^wait=p_∅max(s_a,0)+∑_{T≠∅}p_T r_a(T).

Their difference is E_p g_a≥0. The first-date mixture is independent of
the simultaneous opponents; the empty-event cap includes all delayed
randomized stopping and Never. Hence the profile is exact terminal Nash
against every complete behavioral replacement, for arbitrary signed s_a.

For N≥1, immediate absorption multiplies every reward by h_N=(N−1)/N.
An anchor's empty-event future payoff is at most h_N max(s_a,0): if
s_a<0 every delayed quit is nonpositive and Never pays0; if s_a≥0 the
earlier proof applies. Therefore every finite-horizon deviation is bounded
by h_N V_a as well. Nonanchors obey the same h_N finite Nash inequalities.
The profile is exact Nash at every positive horizon and delivers one fixed
target V with error≤M/N. No contraction, payoff translation or public
correlation is used.

Consequently EVERY no-UE table, and every table with a positive unrestricted
terminal-exploitability floor, must satisfy the unavoidable finite condition

    v_a(r)<0                 for every player a.       (L4)

Equivalently, for every a there must exist a law ν obeying all its anchored
finite-game coarse Nash inequalities while having strictly negative anchor
gap. This is stronger than the exported pointwise negative-join restriction:
for s_a≥0, pointwise nonnegative joining makes g_a≥0 and immediately rules
out (L4), but the converse fails as the exact example below proves. There
is no own-level sign restriction in (L4).

A useful sufficient raw inequality is to choose finitely many λ_{j,b}≥0
and β≥0 such that

    g_a(T)≥β+∑_{j,b}λ_{j,b}R_{j,b}(T)      for every T⊆J. (L5)

Then every ν∈C_a has Eνg_a≥β. This is not a supplied-strategy theorem:
(L5) is a finite inequality family in terminal coordinates, and the finite
Nash point is still produced internally. Standard finite LP duality would
also give the converse certificate for v_a≥β; that converse is not needed
for the producer or necessary condition just proved.

The selected source route remains the finite induced game and the actual
one-date/Never consumer. Narrow searches in
`UniformEquilibrium/Quitting/Stationary/SingleAnchorArbitraryCompletion.lean`,
`UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean`, and
`UniformEquilibrium/Quitting/Root/OneDateNeverNashDebt.lean` found no such raw
Nash-regret producer. The finite dependency is
`quittingPersistentBaseNashSet_nonempty`; the existing downstream consumer
is `quittingOneDateThenNeverProfile_exactHorizonNash` in
`UniformEquilibrium/Quitting/Root/OneDateNeverHorizonNash.lean`. Neither
supplies (L3)→original-game terminal Nash. A general correlated law is not
being mistaken for an independent mixed profile.

### Complete LP-positive, non-monotone-anchor test table

Take anchor0 and the following complete60 table. All own levels are1 and
Γ is still the H=3 favorable matching matrix above.

| S | r(S) |
|---|---|
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (0,−1,1,0) |
| 02 | (1,0,1,0) |
| 03 | (1,4,0,−1) |
| 12 | (99,−100,2,1000) |
| 13 | (105,−100,1000,−100) |
| 23 | (−100,1000,−100,−100) |
| 012 | (101,1,0,100) |
| 013 | (101,−1,1,−1) |
| 023 | (−99,0,1,−1) |
| 123 | (900,−100,−100,1100) |
| 0123 | (1001,100,100,99) |

The anchored free game is unchanged from the preceding fixture, so its
unique Nash point is(q₁,q₂,q₃)=(1/2,5/6,0). In order
T=∅,1,2,3,12,13,23,123, the relevant exact vectors are

    g₀=(0,−4,1,1,2,−4,1,101),
    R_{1,C}=(0,−5,0,0,1,−5,0,100),
    R_{2,Q}=(−1,1,0,−1,0,−99,0,0).

The fixed raw certificate

    g₀≥1/4+R_{1,C}+(1/2)R_{2,Q}

has coordinate slacks(1/4,1/4,3/4,5/4,3/4,201/4,3/4,3/4).
Thus v₀≥1/4, without solving for a strategic point. It is strict in all
eight coordinates, so this is not an equality-stratum-only phenomenon.
The internally produced profile has fixed target

    V=(511/12,2/3,1/2,125/3),      C₀^wait=125/3,
    V₀−C₀^wait=11/12.

Every player nevertheless has a negative nonempty joining comparison:
0 at1 gives−4,1 at0 gives−5,2 at01 gives−1,3 at0 gives−1. Thus no
player meets the accepted raw join-monotone anchor class. This tests strict
strengthening of that particular condition, not an increment beyond all
other actual producers: the broader withdrawal certificate below applies.

The initially tempting experiment changed only player0's excluded rewards.
It created the pure exit1, because its negative0-join at1 left all other
outsiders unwilling to join. That experiment was discarded for additional-
coverage purposes. The displayed complete table instead has player2's
join at1 equal2. No pure exit survives: sets excluding0 other than1,13
are joined by0;1 is joined by2;13 is profitably left by1. Sets containing0
have the same player3 withdrawal or matching-pennies toggle as before.

### Exact sure-stationary exclusion

For any positive opponent absorption, player0's first-date Quit-minus-
Continue difference is E g₀; if someone is sure the opponent background
is nonempty. If q₀=1, the unchanged free game forces the unique point
(1/2,5/6,0). Repeating its hazards gives Never₀=499/11>511/12, so the
candidate is not stationary Nash.

If q₂=1, then Δ₀=1+q₁(1+99q₃)>0, forcing q₀=1, which contradicts
the unique complementary point. If q₃=1 and q₀<1, player0's Nash
condition Δ₀≤0 gives q₁>0 and A=−5+105q₂<0. Player1's difference is
q₀A+(1−q₀)(−100−1000q₂)<0, contradicting q₁>0. Thus q₃ cannot be
sure either.

Finally suppose q₁=1 and q₀<1. Put

    A=−5+6q₂+99q₂q₃,
    B=1−101q₂−101q₃−899q₂q₃.

Player0's condition gives A≤−1, whereas player1's sure condition
q₀A+(1−q₀)B≥0 gives B≥0 and hence q₂,q₃≤1/101. Player3's
difference−q₀+(1−q₀)(−100+200q₂) is strictly negative, so q₃=0.
Then q₀≤(1−101q₂)/(6−107q₂)≤1/6. Player2's difference is
2−3q₀≥3/2, forcing q₂=1, contradiction. All weak boundary ties were
retained. No stationary equilibrium with any sure quitter exists.

### Matching-output separation beyond the raw coefficient tests

Both harmful pair words have Π₀=0 and harmful mate gap−1, so any proper
two-phase output has W₀=1+X_mate>1. They cannot be all-below-singleton
outputs. The favorite word01/23 requires a separate check because its
four participant premiums are now negative.

For this favorite word, write the positive odds X₀,…,X₃, Z=(1+X₂)(1+X₃),
S=X₀+X₁ and P=X₀X₁. Its raw coefficients are

    Π=(−1,−2,−101,−101), c=(−4,−5,−104,−104),
    K=(−101,999,0,−1).

The exact active/Continue equations, which every such output must obey,
give

    S=104X₃(1+S+P)−101X₃/(1+X₃)>3X₃,
    S+P=104X₂(1+S+P)−101X₂/(1+X₂),
    101X₂X₃=3X₂−X₃+X₁[4Z−1/(1+X₁)],
    999X₂X₃=X₂+X₃−X₀[5Z−2/(1+X₀)].

The second equation forces X₂<1/104: otherwise its right side exceeds
S+P by a strictly positive amount. The third then gives
3X₂+3X₁<2X₃, because its bracket is>3 and101X₂X₃<X₃.
The fourth gives3X₀<X₂+X₃<5X₃/3. Hence
S<11X₃/9, contradicting S>3X₃. Thus this word has no positive exact
joint-phase root at all. Together these tests exclude every all-below
proper two-pair architecture, including all relabelings, with no guessed
IFT radius.

### Remaining actual-source comparison: proved tests and live obligations

The unchanged Γ retains positive inverse, R₀/degree+1, harmful-pair non-Q
and negative triple inverse diagonals. Positive full inverse forces every
signed-column σ positive. Every scheduled word has a negative participant
premium and negative c, so the positive-column and nonnegative-participant
sources fail. On both harmful words Π₀=0 also fails the negative-premium
source requiring Π<−1. The opposite-sign symmetric participant source fails
because the two members of each relevant pair have unequal increments.

The previous eleven persistent-base countercomparisons are unchanged.
Every stationary sure-anchor producer is excluded by the full sure census,
not merely at a selected root. All fourteen quiet F/J children fail: use
the earlier direct rows except child1 or13, where T=1 and outsider2 have
gain2 and nonpositive child gains. For the exceptional child012 the J row
at12 now forces λ₃₀≥50; the row at01 gives λ₃₂≤1 and F at012 still
gives−99≤−100λ₃₀+λ₃₂. This remains impossible.

The premium trap is still only I, no player is protected, the forced-floor
vector at23 is still strictly negative, and L_I(12)=102>0. Sure I violates
product-low. The all-sure displacement vector is now(101,100,99,−1),
still distinct; row sums1 exclude terminal upper weights and response
quotients even after positive affine transports. The weak-unit faces,
conditional-range obstruction and sign-changing influence2→1 from the
earlier fixture are unchanged except that player0's favorite premium is
now−1, making the nonfavorite lower-face failure still strict.

For the known transient neighborhood output requiring three free hazards
in(1/4,3/4), anchor0 forces free3=0 and anchor2 forces free0=1. With
anchor3 and all free hazards proper, player0's equation gives
−5+105q₂<0, making player1's difference strictly negative, impossible.
With anchor1, free3's equation gives q₂>1/2 and free0's gives
q₂(6+99q₃)=4, hence q₃<2/99<1/4. Thus no label gives the required
three interior hazards. This does not exclude every other transient root.

The early comparison was provisional and is defeated by the literal broader
withdrawal certificate below. A supplied-root verifier, unknown proper-three
neighborhood, or mere finite LP duality is not an export endpoint. The new
mechanism to test is the raw LP minimum producing an unrestricted equilibrium
and forcing an anchored negative-gap coarse law at EVERY player of EVERY
counterexample.

### Exact failure of the early table's additional-coverage claim

The above producer and (L4) proof survive. The complete60 stress table does
NOT establish an increment over all actual raw sources. A narrow lookup
through docs/TOOLKIT.md found the broader omitted-Never patient-withdrawal
family, and exact finite arithmetic supplies a valid child012/outside3
certificate even though the simpler F/J-only certificate fails.

For this child, every patient's restart floor is0. Let advance weights and
withdrawal weights, in member order0,1,2, be

    λ=(1300/1251,32851/31275,7376/1251),
    ω=(0,1225/1251,0).

All are nonnegative. Against the actual `WithdrawalFutureJoinRewardCertificate`
patient rows, the exact F and J slacks at
T=0,1,01,2,02,12,012 are respectively

    F=(54572/31275,1000/1251,220052/31275,159176/31275,
       1576/31275,34254776/31275,0),
    J=(3428/2085,133427/1251,0,0,64126/31275,0,26/1251).

Every slack is nonnegative. I directly substituted the rational weights
into all fourteen raw inequalities; this is not reliance on a solver's
success flag. In particular the simple proof's F contradiction is repaired
by the withdrawal term at01, where player1 can gain5 by withdrawing.
The actual Never-row right side is280376/31275>1, so its omitted residual
is zero as well.

The literal raw structure is in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`.
Its consumer
`quittingGame_exists_uniformEquilibriumPayoff_of_finFour_withdrawalFutureJoinFamily`
in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`
internally produces the child target and a fixed original-game UE. The
positive-singleton pivot premise holds because every child's own level is1.
I read this declaration and its Fin4 witness-producing dependency under the
imports; it is an actual raw-table producer, not a generic supplied-child
interface. Consequently this stress table is already solved by a compared
existing source, and must not be used to justify exporting (L3).

A diagnostic exact-LP routine was used only to suggest weights. Some other
returned candidates failed literal substitution, so no unverified solver
output is mathematical evidence. The certificate recorded above passed
every row exactly. No infeasibility claim about other children rests on that
routine.

The failed implication is “the direct nonnegative F/J census plus sure-
stationary exclusion exhausts actual quiet raw producers.” It does not.
The strongest surviving theorem remains (L3)≥0→an internally produced
unrestricted one-shot equilibrium and the all-sign necessary restriction
(L4). The global claim max_a v_a≥0 for every table is also false: the
modified global-degree fixture reviewed separately has exact anchored Nash
laws with negative g at EVERY a. Thus this LP mechanism is not a universal
consumer of the remaining singleton-Q source.

Concrete next question: does the entire feasible anchor-regret class imply
one of the existing withdrawal raw families, or can its unconstrained
unanchored nonanchor reward coordinates produce a structural separator?
Resolve that implication before choosing another stress table or making an
export claim. The complete original-game proof and true all-sign empty
event remain preserved above.

### Structural separation from all withdrawal families

Question: does the whole anchored CCE-minimum producer necessarily reduce
to an implemented raw withdrawal family? No. A negative-feedback cycle in
the anchored three-player binary game gives a strict full-table separator.
This is an exact ordinary-mathematics result, not a solver experiment or an
independently reviewed export. It is a new table, not a revision of the
already-covered early table above.

Here is every nonempty reward vector; all four own levels are1.

| S | r(S) |
|---|---|
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (0,−1,0,0) |
| 02 | (1,0,1,0) |
| 03 | (1,4,0,−1) |
| 12 | (100,5,5,0) |
| 13 | (100,5,0,5) |
| 23 | (−100,0,5,5) |
| 012 | (102,1,1,98) |
| 013 | (96,−1,101,1) |
| 023 | (−99,99,−1,−1) |
| 123 | (1000,6,6,6) |
| 0123 | (1002,100,100,99) |

For anchor0, the free utility differences at hazards(q₁,q₂,q₃) are

    A₁=−5+6q₂,       A₂=1−2q₃,       A₃=−1+2q₁.       (C1)

These are exactly the table's own-action differences, not an approximation.
Their product Nash point is uniquely(1/2,5/6,1/2). Indeed if any coordinate
is0 or1, successive strict best responses around the odd negative-feedback
cycle force that coordinate to be its opposite. Thus every equilibrium is
proper; setting the three differences zero gives the stated unique point.
The large terms99q₂q₃,101q₁q₃,98q₁q₂ are independent of the respective
recipient's action and do not change these response equations.

In order T=∅,1,2,3,12,13,23,123, the literal raw vectors are

    g₀=(0,−4,1,1,2,−4,1,2),
    R_{1,C}=(0,−5,0,0,1,−5,0,1),
    R_{2,Q}=(−1,−1,0,1,0,1,0,0).

The SAME finite dual form now has eight strict slacks:

    g₀≥1/4+R_{1,C}+(1/2)R_{2,Q},
    slacks=(1/4,5/4,3/4,1/4,3/4,1/4,3/4,3/4).          (C2)

Consequently v₀≥1/4. The raw CCE producer above supplies the original
unrestricted one-shot equilibrium. Its internally selected unique free
product Nash point gives

    V=(641/3,503/12,101/4,245/6),
    E g₀=23/24,       C₀^wait=5105/24.                 (C3)

Every player has a negative nonempty joining difference: use T1,T0,T03,T0
for players0,1,2,3, with values−4,−5,−1,−1. Thus no label satisfies
the accepted join-monotone-anchor condition.

#### All fourteen children: one structural obstruction, all five kinds

For EVERY nonempty proper child S choose the following nonempty sure
coalition T⊆S and omitted k. Players in T Quit at date0; all other child
players Never. The child gap vector gives, in increasing child order,
Quit-minus-withdraw for members of T and Continue-minus-join for nonmembers.

| S | T | k | Child gaps | Omitted joining gain |
|---|---|---|---|---|
| 0 | 0 | 2 | (1) | 1 |
| 1 | 1 | 2 | (1) | 5 |
| 2 | 2 | 3 | (1) | 1 |
| 3 | 3 | 2 | (1) | 1 |
| 01 | 0 | 2 | (1,5) | 1 |
| 02 | 02 | 1 | (1,1) | 1 |
| 03 | 0 | 2 | (1,1) | 1 |
| 12 | 12 | 3 | (5,5) | 6 |
| 13 | 13 | 2 | (5,5) | 6 |
| 23 | 23 | 1 | (1,1) | 6 |
| 012 | 012 | 3 | (2,1,1) | 1 |
| 013 | 0 | 2 | (1,5,1) | 1 |
| 023 | 02 | 1 | (1,1,1) | 1 |
| 123 | 123 | 0 | (6,6,6) | 2 |

Every displayed child profile is exact terminal Nash against complete
behavioral replacements. If T has at least two members, every deviator has
a sure opponent at date0, so its full deviation reduces to its pure date0
choice. If T is a singleton, its owner has positive own reward1 and all
other child players Never: neither a delayed quit nor Never improves it.
All nonmembers have the strictly negative displayed joining comparisons.
Each profile has zero child debt and zero Never mass. Its positive omitted
gain therefore defeats EVERY universal omitted-gain bound by any fixed
nonnegative weighted sum of child debts and Never mass.

There is also a direct literal raw-row proof, not only a semantic inference.
At the displayed T, every advance joining gain is≤0. For a nonsingleton
member the withdrawal gain is r_i(T−i)−r_i(T)<0; a nonmember's withdrawal
gain is0. At a singleton member, every actual restart floor is≤own1:
patient≤max(1,0), deadline and evaluated security≤0, and terminal security
≤1 by the singleton LP row. Cancellation has the deadline floor. Thus
every withdrawal gain is≤0. The actual J row has strictly positive left
side and nonpositive right side, for ALL nonnegative advance and withdrawal
weights and ALL five `WithdrawalFutureJoinKind` values. No F or Never row
can repair it. This also excludes the simpler future/join-only certificates.

The inspected literal source is `WithdrawalFutureJoinRewardCertificate`,
especially `join_row` and `WithdrawalFutureJoinKind.gain`, in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`.
The restart bounds and five-kind source/consumer files were inspected in
the earlier exact falsifier and global-degree review. This result does NOT
exclude a specially selected safe child equilibrium that avoids these
witnesses; it excludes the actual universal raw-weight families.

#### Explicit full sixty-coordinate neighborhood

Let every reward coordinate vary independently by absolute amount<1/40.
Own rewards remain positive. On a nonempty T, g₀ varies by<2δ,
R_{1,C} by<2δ and R_{2,Q} by<2δ, where δ=1/40; the total right-minus-left
variation in(C2) is<5δ=1/8. On T=∅, g₀=0 and R_{1,C}=0 still, and
the remaining variation is smaller. Thus(C2), with β=1/4, remains valid
with strictly positive slacks. The selected Nash point may change; the
raw finite producer does not require an IFT or prescribe its coordinates.

All child and omitted comparisons in the fourteen-row table have margin
at least1 and vary by<2δ. Their exact child Nash, zero Never and positive
omitted-gain obstructions persist. Singleton withdrawal floors are still
bounded by the new positive own rewards. Hence this entire open full-table
box is produced by the CCE criterion while no implemented five-kind raw
withdrawal family can consume it. This disproves structural inclusion of
the global LP class into the union of those raw families.

#### Other exact source and accepted-class comparisons

The singleton matrix is the unchanged H=3 matching matrix with favorable
partners(01)(23), Γ row sums1, strictly positive inverse and degree1.
On word01/23, c₀=−4 and c₁=−5. On03/12, c₃=−1. On02/13,
c=(1,5,1,5)>0, but player0's opposite triple reward r₀(013)=96 exceeds
own1. Thus EVERY pair partition fails the newly accepted weak condition
“all four scheduled c≥0 and all twelve opposite participant rewards≤own”,
and also its stronger matching and all-positive signed-inverse subcriteria.
The positive inverse forces every sign column positive. No harmful pair
contains two below-mate participants: pair02 has Π₀=Π₂=0, pair03 has
Π₀=0, and pairs12,13 have positive participant premiums. This defeats
the accepted opposite-sign arm's raw negative-participant requirement.

Every proper all-below-singleton two-pair output is excluded intrinsically,
not through a guessed persistence radius. On either harmful word, player0
has Π₀=0 and c₀=1, forcing W₀=1+X_mate>1. On the favorite word01/23,
players2,3 have Π=4, forcing their active values>1. These exhaust all
pair partitions and relabelings.

No persistent base E of cardinality≥2 is complement-leave-safe. A failing
recipient and opponent coalition T⊇E−i are:

    E01:(i0,T1), E02:(i2,T03), E03:(i0,T13),
    E12:(i2,T013), E13:(i1,T03), E23:(i2,T03),
    E012:(i2,T013), E013:(i0,T13), E023:(i2,T03),
    E123:(i2,T013), EI:(i2,T013).

Their joining differences are respectively−4,−1,−4,−1,−5,−1,
−1,−4,−1,−1,−1. The exact predicate and strategic consumer are
`QuittingPersistentBaseComplementLeaveSafe` and
`exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseArbitraryCompletionEscape.lean`.

Every one-sided weak-unit guard fails its UPPER face. For(owner,passive),
choose T containing owner and omitting passive with positive passive join:

    (0,1):T02, (0,2):T0, (0,3):T01,
    (1,0):T12, (1,2):T1, (1,3):T1,
    (2,0):T2,  (2,1):T2, (2,3):T2,
    (3,0):T3,  (3,1):T3, (3,2):T3.

At these pure hazards the polynomial displacement IS that positive joining
difference, so this excludes both raw and polynomial guards, not merely a
stronger sufficient ranking. Inspected declarations are
`QuittingOneSidedWeakUnitGuards`, `QuittingOneSidedWeakUnitRawGuards` and
`exists_uniformPayoff_of_oneSidedWeakUnitGuards` in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`, and
`QuittingWeakUnitJoining` in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitRawGuards.lean`.

The two-sided weak HALF-polynomial guards also fail under every relabeling.
Their actual lower face, together with this invertible nonnegative inverse,
forces the selected reciprocal singleton entries positive. Thus the selected
pair must be01 or23; this is the literal
`QuittingHalfWeakPolynomialGuards.reciprocal_pos` necessity in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`.
For selected01, recipient0 with partner1 hazard1/2 and outsiders2,3 sure
has displacement(g₀(23)+g₀(123))/2=3/2>0. For selected23, recipient3
with partner2 hazard1/2 and outsiders0,1 sure has displacement
(r₃(013)−r₃(01)+r₃(I)−r₃(012))/2=(1+1)/2=1>0.
Each is on its required nonpositive upper-half face. This excludes the
broader polynomial guards and hence their finite weak/strict raw subclasses.
The inspected raw and polynomial consumers are
`exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_halfStrictRaw`
in `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseHalfCeilingProducer.lean`
and `exists_stationary_terminalApproximation_of_weakHalfPolynomialGuards`
in `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialProducer.lean`.
The displacement definition is in
`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean` and
depends on opponents only; the displayed sure-outsider rows therefore
equal the averaged literal joining gains just computed.

Global inserted-premium weights must vanish. At T0 the coefficient vector
is(0,−2,0,−2), forcing λ₁=λ₃=0. At T03 it then forces λ₂=0; at T23
it forces λ₀=0. Therefore `HasWeightedQuittingTrapLeavers` in
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`
fails, since the grand coalition is a premium trap and requires positive
weights. Its weak reward-closure consumer is
`exists_uniformEquilibriumPayoff_of_weightedTrap_weakLeave` in
`UniformEquilibrium/Quitting/Classification/Existence/WeightedQuittingTrapLeaversRewardClosure.lean`.
The actual traps are12,13,23,012,013,123,I. None has all its proper-subset
L and J charges nonpositive: witnesses T1,T1,T2,T1,T1,T1,T13 have both
positive charges. In particular L_I(13)=100,J_I(13)=2. No player is protected,
and sure I's four forced-Quit values all exceed own1, defeating product-low.

For conditional ranges, player0 has Continue upper≥r₀(123)=1000.
For every blocker, its Quit-without lower≤own1, and its Quit-with lower≤1
using pair01,02 or03. Thus no convex mixture of those lower bounds strictly
exceeds its Continue upper. This directly defeats
`IsQuittingConditionalFaceGapRange` in
`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`.
Membership influence1→0 changes sign: at empty background the literal
joining gain changes by−5, whereas at background2 it changes by+1.

Γ row sums1 imply all nonnegative terminal upper weights vanish. They also
force equal positive row scales within any response-invariant block after
playerwise positive affine transport. The all-sure displacement vector is
(2,1,−1,1); only the pair{1,3} could share a block. That pair's singleton0
block sums are3 and−1, so it too fails. Thus all fourteen nondiscrete
response-invariant quotient partitions fail even after such transport.
This uses the actual necessity `quittingSingletonBlockRowSum_eq_of_responseInvariant`
in `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.

#### Sure-stationary census and transient-center output

If0 is sure, the unique free Nash point from(C1) applies. Repeating it gives
Never₀=5104/23 and Q₀=641/3, hence Q₀−Never₀=−569/69<0. The one-shot
profile must not be stationary repeated.

If1 is sure, player3's joining difference is strictly positive: when0
Continues it is5+q₂, and when0 Quits it is1. Thus3 is sure. The free0,2
response differences are−4+6q₂ and6−7q₀, giving unique Nash
(q₀,q₂)=(6/7,2/3). Sure1's difference is then−1/21<0.
If2 is sure, player1 is forced sure (its difference is5+q₃ when0 Continues,
and1 when0 Quits); then player0 has difference2 and player3 difference1,
forcing the grand coalition, where player2's difference is−1.

If3 is sure, free0,1,2 differences are

    G₀=1−5q₁+6q₁q₂,
    G₁=(1−q₀)(5+q₂)+q₀(−5+6q₂),
    G₂=(1−q₀)(1+5q₁)−q₀.

At q₀=0 the other two are forced sure, contradicting G₀>0. At q₀=1,
the unique free response is(q₁,q₂)=(0,0). If q₀ is proper, q₁=0 makes
G₀=1; q₁=1 forces(q₀,q₂)=(6/7,2/3) and G₁=−1/21; q₂=0 forces
(q₀,q₁)=(1/2,1/5) and G₂=1/2; q₂=1 makes G₀>0. All boundary cases
fail. At an all-proper point G₀=0 gives−5+6q₂=−1/q₁. The G₁,G₂
equations then respectively give

    q₀/(1−q₀)=q₁(5+q₂),
    q₀/(1−q₀)=1+5q₁,

hence q₁q₂=1, impossible. The only finite Nash completion is therefore
(q₀,q₁,q₂)=(1,0,0), where sure3's difference is−1. No sure-quitter
stationary equilibrium exists. This excludes actual sure-anchor stationary
sources, but does not claim absence of all-proper stationary equilibria.

The implemented nearby transient center with one sure anchor and every
free hazard in(1/4,3/4) cannot output this table. Anchor0 forces q₂=5/6;
anchor1 forces free3 sure; anchor2 forces free1 sure; anchor3 has no
all-proper finite completion by the preceding calculation. This is an
intrinsic output exclusion for `exists_nearby_oneDate_sameProfile_horizon_equilibrium`
in `UniformEquilibrium/Quitting/Examples/AdaptiveChildCenterNearbyHorizons.lean`,
not a claim about an unspecified perturbation radius.

Concrete next question: independently falsify the whole finite-CCE producer
and the structural family(C1)–(C3), including all-sign empty events and all
fourteen-child universal/RAW distinctions. Extend the source census only
where an actual named raw criterion might consume this table. A generic
conditional verifier or unknown all-proper local center is not a competing
arbitrary-table producer. No export or review request is inferred merely
from fixed-point correctness; the substantive increment evidence is the
full open CCE-positive/withdrawal-negative class proved here.

### Decisive whole-class overlap with the concrete persistent-base source

The finite CCE theorem, exact one-shot strategy, all-sign empty row and
full behavioral/finite-horizon proofs survive. The claimed additional UE
counterexample-class narrowing does NOT. This is a whole-class inclusion,
not another coincidental overlap of a selected example. The exact final
587-line standalone remains frozen for historical proof review; it must
not be promoted on the strength of its former coverage claim.

I independently read the complete tracked
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`
and its singleton strategic dependency
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingletonBaseSemanticDispatch.lean`.
The overlooked original-game alternatives are
`exists_uniformPayoff_or_singletonBase_pos_gap` and
`exists_uniformPayoff_or_persistentLargeBase_pos_gap` in the former file.
They are unconditional theorems over the ACTUAL complete induced product
Nash carrier, not stationary-Never screens or supplied-strategy verifiers.

For singleton base a take free=I∖{a}; there are no outsiders. Put
P_a=quittingPunishmentValue reward a. The source's actual owner-floor
excess at an induced product Nash law p is

    floorExcess=C_nonempty+p_∅P_a−V_a
               =−E_p g_a+p_∅[P_a−max(s_a,0)].         (O1)

The literal theorem `quittingPunishmentValue_le_max_solo` in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean` gives
P_a≤max(s_a,0), with no own-sign assumption. I inspected its definition
and proof: the all-Continue pure opponent row caps any unilateral reply by
max(s_a,0). Thus(O1)≤−E_p g_a. Any internally selected product Nash
belongs to C_a; CCE admission gives E_p g_a≥0. Every owner-floor and
outsider screen in the existing source is therefore nonpositive. Its
strictly positive compact-gap branch is contradicted, leaving its existing
UE conclusion. Its fixed-target compiler uses punishment after a quiet
owner deviation, not stationary repetition of the nominal free hazards.

For |E|≥2 the same inclusion is even more direct. With free=I∖E,
`quittingPersistentLargeBaseComponent` is−E_pG_i^E for every base member,
zero for free players, and has no outsider components. The LP inequalities
give every component≤0 at an internally produced free Nash point. Hence
`quittingPersistentLargeBaseExcess`≤0, contradicting that alternative's
positive-gap branch and yielding its already implemented UE conclusion.

At the complete three-response-cycle center, p_∅=1/24 and E_p g₀=23/24.
Therefore floorExcess≤−23/24, and the source's maximum with the free
players' zero components is exactly0. This is an exact negative screen,
not a hypothetical punishment value or guessed local radius. Excluding
all sure-stationary profiles and every withdrawal certificate did not
exclude this different transient punishment architecture.

Moreover the old alternatives imply a STRICTLY STRONGER necessary
condition under no UE. On every singleton induced PRODUCT Nash point,
its floor excess is≥γ>0, so(O1) forces E_p g_a≤−γ. On every large-base
induced PRODUCT Nash point, some member has E_pG_i^E≤−γ. The member
may vary with the point, but the source's γ is uniform on that carrier.
These conditions imply our existential negative coarse-law restriction
by internally choosing any finite Nash point. Consequently neither the
new existence class nor its contrapositive removes a previously surviving
UE counterexample class. A finite LP recognition shortcut and exact same-
profile horizon strengthening remain valid internal results.

Failed implication: “a full fourteen-child withdrawal obstruction plus
all accepted pair tests and sure-stationary absence establishes additional
coverage against implemented arbitrary-completion sources.” The concrete
singleton source prices waiting at P_a, not at stationary Never. Comparing
against its exact semantic screen, rather than only its stationary or
pointwise subclasses, closes the entire alleged gap.

Concrete next question: find a mechanism that consumes tables failing
EVERY concrete induced-Nash punishment/large-base screen, or prove a new
unavoidable restriction on that actual surviving class. A stronger LP
relaxation of these same accepted finite screens alone cannot establish
new UE existence coverage. Do not retune the already-solved separator.
