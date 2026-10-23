# Mixed-sign triple premium cores have uniform equilibria

## Raw statement and exact scope

Let I be a finite player set, r(S)∈ℝᴵ the reward at each nonempty
coalition S, and s_i=r_i({i}). The initial live state and every later
live state pay zero; after the first
nonempty quitting coalition the resulting absorbing reward is paid from the
next state onward. Never pays zero. Each live-date randomization is private
and independent, and strategies and deviations are unrestricted behavioral
strategies. A premium trap is a nonempty A⊆I such that for each i∈A
some coalition S⊆A
containing i satisfies r_i(S)>s_i. Traps are closed under union, so their
union C is the greatest premium core. Assume C={1,2,3}; these labels may
be any three distinct players. For nonempty T⊆C\{i}, define the actual
joining difference

    d_i(T)=r_i(T∪{i})−r_i(T).

The strict raw inequalities are

    d₁({2})>0,             d₂({1})>0,
    d₁({3})<0, d₃({1})<0, d₂({3})<0, d₃({2})<0,
    d₁({2,3})=0,           d₂({1,3})=0,
    d₃({1,2})<0.                                      (1)

There are no premium sign restrictions inside or outside C. In particular
participant rewards involving players outside C remain arbitrary subject
only to the raw greatest-core condition.

**Strict analytic theorem.** Either pure coalition {1,2} is an actual
full-game exact terminal and uniform equilibrium, or at every source v
strictly below some own singleton there exists a full exact root whose
successor w is at most some own singleton. This is true on every box
[−B,B]ᴵ with B>M≥max_{S,i}|r_i(S)|, and the successor remains in that
same box. Including the pure equilibrium exit, no C¹ full exact-root
unit-absorption potential exists on such a box.

**Original-game Fin4 theorem.** If I=Fin4, every s_i≥0, and (1)
holds with all strict inequalities weakened in their stated directions,
then the original quitting game has a uniform-equilibrium payoff.
The two displayed equalities remain equalities. One target u is chosen
before accuracy: for each ε>0 there is a behavioral profile and a horizon
threshold such that every larger expected average payoff is within ε of
u, and every unrestricted unilateral behavioral deviation earns at most
u_i+ε. No root, target, timing law, or degree is an input to this theorem.
The weak statement is a reward-closure conclusion, not a weak index claim.
This is an exact equality-stratum theorem. No full reward-space open
neighborhood of its tables is claimed; weak closure does not remove the
two equalities.

## Support and partly-sure roots

For a product hazard q let c=∏ᵢ(1−q_i), a=1−c, and let μ_q be its
literal product coalition law. At continuation annotation v write

    w=cv+∑_{S≠∅}μ_q(S)r(S),
    Q_i=∑_{T⊆I\{i}}μ_{−i}(T)r_i(T∪{i}),
    C_i=μ_{−i}(∅)v_i+∑_{T≠∅}μ_{−i}(T)r_i(T),
    g_i=Q_i−C_i.

Exact Nash means q_i=0 implies g_i≤0, q_i=1 implies g_i≥0,
and 0<q_i<1 implies g_i=0. Call a root bad when w_i>s_i for
every player. Its positive support A is a trap: otherwise an active
player i has all participant rewards within A at most s_i, and hence
w_i=Q_i≤s_i. Thus any nonempty bad support is a pair inside C or C.

For k∉C and T⊆C, one has r_k(T∪{k})≤s_k. Otherwise C∪{k}
would be a trap, using the existing witnesses inside C for its members.
Consequently every outside-core player at a bad root satisfies

    q_k=0,        g_k=Q_k−C_k≤s_k−w_k<0.              (2)

This is a strict full-game inequality and keeps all outsider reward rows.

Suppose q₁=1 at a bad root. Player3 faces either coalition {1} or
{1,2}; both joining differences are strictly negative by (1).
Thus g₃<0 and q₃=0. Player2 now faces sure player1, so
g₂=d₂({1})>0 and q₂=1. The root is therefore pure {1,2}.
The argument with 1 and2 exchanged is identical.

Suppose instead q₃=1. If q₂<1, then
g₁=(1−q₂)d₁({3})<0, so q₁=0; this forces g₂=d₂({3})<0
and q₂=0. The support is then singleton3, which cannot be bad.
If q₂=1, its own optimality requires
g₂=(1−q₁)d₂({3})≥0, so q₁=1. But with q₁=q₂=1,
g₃=d₃({1,2})<0, contradicting q₃=1. These cases exhaust
every bad root with a sure hazard.

A full exact pure-{1,2} root is independent of the annotation, since
each player still faces a sure quitter after a unilateral deviation.
Prescribing those two sure quits at the initial date is therefore an
actual unrestricted terminal equilibrium, with immediate absorption even
after every unilateral deviation. In the repository's state-payoff timing,
the initial live date pays zero, so for N≥1 its N-date average is
(N−1)r({1,2})/N. The profile is exact Nash at every N, and delivery to
the fixed target r({1,2}) has error at most M/N. It also contradicts a
positive charged potential directly by taking v=w=r({1,2}). Dispatch
this exit first. Every remaining bad
root has only proper positive hazards.

## Full negative indices, including the mixed signs

For proper active hazards put z_i=q_i/(1−q_i), taking z_i=0 at
an inactive core member. The exact odds identity is

    g_i/∏_{j∈C\{i}}(1−q_j)
      =s_i−v_i+∑_{∅≠T⊆C\{i}}d_i(T)∏_{j∈T}z_j.    (3)

At a bad pair A={i,j}, let d_i=d_i({j}), d_j=d_j({i}). Its two
active derivatives are

    α_i=v_i−s_i+d_i=d_i/(1−q_j),
    α_j=v_j−s_j+d_j=d_j/(1−q_i).

Their signs need not be positive. However d_i d_j>0 for ALL three
pairs in C under (1), so the active determinant of −Dg is

    −α_iα_j<0.                                       (4)

At a triple root, differentiating (3) at its zero gives

    a_ij=∂g_i/∂q_j
        =(1−q_k)/(1−q_j)[d_i({j})+z_k d_i({j,k})].   (5)

The two zero two-opponent differences in (1) are essential here.
They give a₁₂,a₂₁>0 and a₁₃,a₂₃<0. The last row satisfies
a₃₁,a₃₂<0 because both its singleton and two-opponent differences
are negative. Thus each directed triangle product is positive:

    det(−Dg|C)=−(a₁₂a₂₃a₃₁+a₁₃a₂₁a₃₂)<0.          (6)

Equivalently, conjugation by diag(1,1,−1) makes the off-diagonal
entries positive, without changing the determinant. This is a matrix
identity, not a strategic relabeling of Quit and Continue.

To identify the full ambient index, extend each gap g_i polynomially to
all of ℝᴵ and use the literal clipped map

    F_v(x)_i=clip_[0,1](x_i+g_i(x)).

There is NO clipping of the inputs inside g. Every fixed point lies in
the unit cube and is exactly a full Nash root. At a bad root with all
inactive gaps strict, the derivative of Id−F_v has active block −Dg,
an unrestricted upper-right block, and lower blocks 0,Id. Hence (4)
or (6) is its full determinant. Arbitrary rewards involving inactive
outsiders remain in the upper-right derivatives; they are not discarded.

An unused core player at a bad pair may be tied, so annotation genericity
is required. Write b_i=v_i−s_i and b_j=v_j−s_j. The pair odds are
z_i=b_j/d_j, z_j=b_i/d_i. For its remaining core member k, the gap
times a nonzero denominator has polynomial numerator

    N_Ak=d_i d_j(s_k−v_k)
         +d_i b_j d_k({i})+d_j b_i d_k({j})
         +b_i b_j d_k({i,j}).                        (7)

The coefficient of v_k is −d_i d_j≠0. Thus the three pair-tie
polynomials are nonzero and can be avoided simultaneously on a dense
open set of annotations. Outside-core ties are already excluded by
(2). No reward perturbation is used in this strict argument.

## Degree, boundary sources, and the semantic consumer

Choose a generic source v with a strict singleton deficit. The all-Continue
root is impossible because that player strictly prefers Quit. Suppose all
roots were bad. After the pure-{1,2} exit, the preceding classification
makes every root proper on its active support, differentiable for F_v,
and regular with local ambient index −1. Such roots are isolated. The
fixed-point set is compact; therefore it contains finitely many roots.

On the enlarged open cube (−1,2)ᴵ the map F_v takes values in [0,1]ᴵ.
Homotopy through bounded maps to the constant vector (1/2,…,1/2) has
no boundary fixed points. The degree of Id−F_v on this cube is +1.
Additivity over all its finitely many zeros gives +1=−N, impossible.
This counts ALL full roots and treats inactive boundary coordinates in
ambient dimension; it is not an index calculation on a support face.

For an arbitrary boxed source v with a strict singleton deficit, choose
generic v⁽ⁿ⁾ in the interior of the SAME box, preserving that deficit
and converging to v. Select a good exact root at each v⁽ⁿ⁾ and take a
convergent hazard subsequence. Nash inequalities are closed. Passing
also to a constant good-coordinate subsequence gives an exact limiting
root with w_i≤s_i. The strict source deficit prevents this root from
being all-Continue. Since rewards and source are in the same box,
w=cv+∑μ(S)r(S) remains there as well.

## Smooth potential exclusion on the same domain

A full exact-root unit-absorption potential on the box would satisfy

    H(w(v,q))+a(q)≤H(v)

at every exact root with boxed source and successor. Suppose H is C¹
on a neighborhood of the box. The pure-12 case gives a self-loop with
absorption one and is already impossible. Otherwise minimize H on the
compact nonempty set

    D={v∈[−B,B]ᴵ : some v_i≤s_i}.

If a minimum x were strictly below some singleton, selected return would
give w∈D and a>0, contradicting H(w)+a≤H(x). Therefore x≥s and at
least one coordinate binds. Write J={j:x_j=s_j} and g=∇H(x).

For each binding j a collision-adjusted solo root gives

    g·(x−r({j}))≥1.                                  (8)

Here is the exact signed probe. Set b_j=0, set
b_i=max(0,r_i({i,j})−r_i({j})) for other binding i, and set b_i=0
for nonbinding i. At hazard q_j=t, q_i=0 for i≠j, use source
v_t=x+t b/(1−t). Player j is indifferent. For an inactive i its gap is

    (1−t)(s_i−x_i)+t[r_i({i,j})−r_i({j})−b_i]≤0

for all sufficiently small t>0: binding players satisfy this by definition,
and every nonbinding player's strict first term dominates the bounded
second term. Thus this is a full exact root, including every possible
outsider join. Its source and successor stay in the box, and

    w_t=x+t[b+r({j})−x].

Differentiating H(v_t)−H(w_t)≥t proves (8); the b terms cancel.

If j were the only binding coordinate, every other interior partial would
be zero by minimum geometry, and every partial at an upper face would be
nonpositive. At those upper faces x_i−r_i({j})≥B−M>0, while the j
component of x−r({j}) is zero. Hence (8) would have left side at most
zero, a contradiction. There are therefore at least two binding coordinates.
Raising any one of them slightly leaves another binding, remains in D,
and implies g_j≥0 for every j∈J.

Fix such a j and let v=x−εe_j for small ε>0. Selected return gives an
exact root with w∈D and a>0. Minimality and charged drift imply

    H(x−εe_j)−H(x)≥a.                                (9)

The literal reward and displacement bounds, valid with signed premiums, are

    Q_j≥s_j−2Ma,       |w_j−v_j|≤(M+B)a.

The first follows because the own singleton occurs whenever the opponents
all continue; the complementary probability is at most a, and all reward
differences have magnitude at most2M. Exact Nash gives w_j≥Q_j, hence

    ε≤(3M+B)a.

Dividing (9) by ε and passing to zero gives
−g_j≥1/(3M+B)>0, contradicting g_j≥0. Thus no such H exists.

This is the ordinary signed proof behind
`not_isQuittingFullExactRootPotential_of_selectedSingletonSublevelReturn`
in
`UniformEquilibrium/Quitting/Projective/SelectedSingletonSublevelReturnSmoothDrift.lean`.
The root construction above supplies its
`HasBoxedSelectedSingletonSublevelReturn` hypothesis for every B>M;
it is not an additional strategic assumption.

## The original Fin4 game and the simultaneous weak boundary

For Fin4 choose M=quittingRewardBound(r), the actual sum-based canonical
bound, and B=M+1. This supplies the bound hypotheses of the declaration
`exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_on_subbox`
in
`UniformEquilibrium/Quitting/Classification/Existence/SelectedSingletonSublevelReturnUniformPayoff.lean`
takes exactly s_i≥0, M<B≤M+2, and that return predicate. It supplies
the original-game fixed-target UE conclusion stated above, not merely
terminal Nash at an annotated one-stage game. Its proof composes the
continuous boundary-differentiable potential exclusion with the existing
full Fin4 polynomial obstruction producer. The pure-{1,2} branch already
has the direct unrestricted finite-horizon proof given above.

For the weak raw theorem, perturb ONLY passive rewards, by a quantity
δ>0: lower r₁({2}) and r₂({1}); raise r₁({3}), r₃({1}),
r₂({3}), r₃({2}), and r₃({1,2}). All changes have magnitude δ.
This makes the seven weakly signed differences strict in the required
directions. The two equalities are untouched. No participant reward or
own singleton changes, so every premium trap and C remain exactly the
same. The strict theorem gives UE for each perturbed table. The standard
uniform-payoff reward-closure argument, implemented in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`,
then gives one UE target in the original table. Changing every reward by
at most δ changes both any prescribed expected average payoff and any
deviation payoff by at most δ, uniformly in strategy and horizon; a
convergent subsequence of the bounded targets fixes the original target.
No weak analytic C¹ exclusion or weak Jacobian assertion is inferred.

## An exact signed coverage fixture

Here is a complete rational Fin4 table. Its own singleton vector is
s=(1,0,0,0).

| S | r(S) |
|---|---|
| 0 | (1,−1,−1,−1) |
| 1 | (2,0,2,−1) |
| 2 | (2,−1,0,2) |
| 3 | (−1/2,2,−1,0) |
| 01 | (0,0,2,−1) |
| 02 | (0,−1,0,2) |
| 03 | (0,2,−1,0) |
| 12 | (−1,1,3,3) |
| 13 | (−1,1,1,−2) |
| 23 | (−1,1,−2,1) |
| 012 | (0,0,0,3) |
| 013 | (0,0,2,20) |
| 023 | (0,2,0,0) |
| 123 | (−1,1,1,1) |
| 0123 | (0,−2,−2,−2) |

Its traps are exactly 12 and123. Player0 can belong to no trap because
all its participant rewards are at most1. Among core pairs, only12 has
both premiums positive; each member has positive premium at123. The
joining data, in the order appearing in (1), are

    d₁(2)=2, d₂(1)=1,
    d₁(3)=d₃(1)=d₂(3)=d₃(2)=−1,
    d₁(23)=d₂(13)=0, d₃(12)=−2.                      (10)

No pure full exit is Nash. The following table gives one strictly
profitable switch at each coalition, with its exact gain:

| S | Deviator and action | Gain |
|---|---|---|
| 0 | 1 joins | 1 |
| 1 | 2 joins | 1 |
| 2 | 1 joins | 2 |
| 3 | 0 joins | 1/2 |
| 01 | 0 leaves | 2 |
| 02 | 0 leaves | 2 |
| 03 | 2 joins | 1 |
| 12 | 0 joins | 1 |
| 13 | 3 leaves | 1 |
| 23 | 2 leaves | 1 |
| 012 | 2 leaves | 2 |
| 013 | 1 leaves | 2 |
| 023 | 3 leaves | 2 |
| 123 | 0 joins | 1 |
| 0123 | 1 leaves | 4 |

All Never fails by player0's positive singleton. The large passive13-to-013
entry20 is deliberate: it defeats a child lift without changing any core
joining difference, singleton matrix, or trap.

Define Γ_ii=0 and Γ_ij=r_i({j})−s_i for i≠j. The
singleton-difference matrix is

    Γ=[[0,1,1,−3/2],[-1,0,-1,2],
       [-1,2,0,-1],[-1,-1,2,0]].

For an offset b, a complementary solution means z≥0, b+Γz≥0, and
z_i(b+Γz)_i=0 for every i. The R₀ condition means that the homogeneous
problem b=0 has only z=0. At a regular offset the degree is the sum of
the signs of active principal determinants over all complementary
solutions, with positive active coordinates and strict inactive residuals.

For its homogeneous LCP, a positive pivot forces all three core
coordinates positive: if one vanished, the cyclic residual inequalities
and complementarity at the next positive coordinate contradict each other.
The core equations then give z₁=z₂=z₃=z₀. The pivot residual is z₀/2,
contradicting complementarity. With zero pivot, the same support argument
gives either all core coordinates zero or all positive; invertibility of
the core matrix excludes the latter. Thus Γ is R₀.

At offset (1,−1,−1,−1), the same cyclic support argument forces all
three core coordinates positive. They equal 1+z₀, and the pivot residual
is 3/2+z₀/2>0. Thus the unique complementary solution is
(0,1,1,1), its inactive pivot residual is3/2, and its active determinant
is7. The degree is therefore1, not a non-degree-one exit.

The core inverse is

    Γ₁₂₃⁻¹=[[2,4,1],[1,2,4],[4,1,2]]/7,

but its literal passive inverse row is (−3/7,9/14,2/7).
The other principal triple inverses have negative entries −2 at00 for012,
−4/7 at00 for013, and −3/4 at01 for023. The full inverse has entry
(0,2)=−9/7. Thus the named nonnegative-inverse/passive-row criteria
do not consume the table, and neither do the homogeneous or degree exits.
The principal03 matrix is [[0,−3/2],[-1,0]]. It is R₀, but its
offset (−1,−1) has both residual coordinates strictly negative for
every nonnegative vector. It is therefore not Q, excluding the
all-principal projective-Q criterion as well. This does not assert
that the full degree-one matrix fails the standard Q property.

A response-invariant nontrivial quotient must equate singleton block-row
sums for every pair of receivers in one block. Thirteen nondiscrete
partitions fail this necessary condition as follows:

| Partition | Receivers | Column block | Sums |
|---|---|---|---|
| 01 / 2 / 3 | 0,1 | 01 | 1,−1 |
| 02 / 1 / 3 | 0,2 | 02 | 1,−1 |
| 03 / 1 / 2 | 0,3 | 1 | 1,−1 |
| 0 / 12 / 3 | 1,2 | 12 | −1,2 |
| 0 / 13 / 2 | 1,3 | 13 | 2,−1 |
| 0 / 1 / 23 | 2,3 | 1 | 2,−1 |
| 012 / 3 | 0,1 | 012 | 2,−2 |
| 013 / 2 | 0,1 | 013 | −1/2,1 |
| 023 / 1 | 0,2 | 023 | −1/2,−2 |
| 01 / 23 | 0,1 | 01 | 1,−1 |
| 02 / 13 | 0,2 | 02 | 1,−1 |
| 03 / 12 | 0,3 | 12 | 2,1 |
| 0123 | 0,1 | 0123 | 1/2,0 |

For the remaining nondiscrete partition 0|123, use the literal
zero-discount displacement F_i=(1−α_i)Q_i−A_i, where now
α_i=∏_{j≠i}(1−q_j) is opponent continuation mass and A_i is the
unnormalized passive absorption contribution. At q=(1/2,1/2,1/2,1/2),

    F₁=−25/64,       F₂=−1/2,       F₃=35/32.

They differ, excluding that block as well. The discrete partition is
not a reduction. These are the exact necessary invariance tests from
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`,
using `quittingDiscountedDisplacement` in
`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`.

The terminal debt of a player is its full behavioral response cap minus
its prescribed terminal payoff. All fourteen proper nonempty children
have explicit exact-Nash
profiles whose quiet lifts admit a profitable omitted-player deviation.
Thirteen are pure first-date exits, followed by Never:

| Child | Prescribed exit | Omitted profitable joiner | Gain |
|---|---|---|---|
| 0 | 0 | 1 | 1 |
| 1 | 1 | 2 | 1 |
| 2 | 2 | 1 | 2 |
| 3 | 3 | 0 | 1/2 |
| 01 | 1 | 2 | 1 |
| 02 | 2 | 1 | 2 |
| 03 | 03 | 2 | 1 |
| 12 | 12 | 0 | 1 |
| 13 | 1 | 2 | 1 |
| 23 | 2 | 1 | 2 |
| 013 | 1 | 2 | 1 |
| 023 | 2 | 1 | 2 |
| 123 | 12 | 0 | 1 |

For child012 prescribe q=(1/3,1,2/3) at the first date and Never
thereafter. Player0's two endpoints are0; player2's are2. Player1's
Quit endpoint is4/9, whereas Continue gives−7/9, including the
possible zero-valued continuation when both opponents continue. Its
full later stopping cap on that continuation is its singleton0. Hence
this is exact Nash against all behavioral deviations, with payoff
(0,4/9,2). The quiet player3 gets5/3. Quitting at the initial date
gives16/9, a gain1/9: the four possible child coalitions 1,01,12,012
have probabilities 2/9,1/9,4/9,2/9, and the joining payoffs are
−2,20,1,−2 respectively.

Every displayed child has joint Never mass zero and all child debts
zero. For EACH proper child there EXISTS an omitted player for which
no universal bound by fixed nonnegative weighted child debts plus any
finite joint-Never coefficient can hold. This directly excludes the
raw universal weighted child-debt lift certificates, not merely one
choice of weights. It does not assert that every child equilibrium
has a bad quiet lift, or exclude all quiet strategic producers.

The other accepted raw classes fail for explicit reasons. The greatest
core has size3, not at most2; the signed same-sign pair-core theorem
therefore does not apply. Joining-attractive core3 fails by four
negative singleton joining differences. Every player has a strictly
negative participant premium at the grand row, so the protected set
is empty. The same row has strictly negative weighted premium for
EVERY nonzero nonnegative weight vector, ruling out a global weighted
singleton floor. At sure coalition123 every participant premium is1,
so product-low and positive-weight nonpositive participant-sum tests
fail. The trap12 is mutually encouraging, so it has no leaving member;
the support-specific and common-leaver tests fail even apart from
protection. The boxed/mixed larger-trap condition fails because

    P₁₂₃({1})=r₂(12)−s₂+r₃(13)−s₃=3−2=1>0.

Finally the only positive own singleton is player0's1, and all its
pair participant rewards are0. Thus the prescribed cyclic-child
joint-phase classes requiring a zero or positive premium at that pivot
cannot match the table under relabeling. The two-joint full-table neighborhood criterion retains two disjoint
positive-premium pair traps and hence a full greatest core. This fixture
has a proper core, so it is outside that certified neighborhood, also
under relabeling.
These are named-source comparisons, not an exhaustive claim
of nonexistence of stationary or chronological equilibria.

## Exact root and equality boundaries

The theorem selects a good root; it does not claim that every root is
good. In the complete displayed table, take

    v=(1,5/9,0,−14/27),       q=(0,1/10,1/4,1/10).

The literal endpoints are

    Q=(243/400,13/40,1/10,1/10),
    C=w=(847/800,13/40,1/10,1/10).

This is full exact Nash, with outside-core gap −361/800. Although v₃<s₃,
every successor coordinate is strictly above its singleton. Its active
derivative and full determinant are

    Dg_C=[[0,12/5,−5/6],[1,0,−1],[−25/18,−22/15,0]],
    det D(Id−F)=−41/9.

The root is a genuine bad triple root with the negative full index used
in the proof. The existence of another good root is supplied by the
total degree, not by ruling out this root.

There can also be a genuine clipping tie. On the same table take

    v=(3,2,1/3,−2),        q=(0,1/4,1/2,0),
    Q=(3/8,1/2,3/4,1/4),
    C=w=(2,1/2,3/4,1/4).

Player3 is inactive and tied, while the root is bad and player0 is
strictly inactive. Raising only v₃ by η>0 preserves the pair root and
gives g₃=−3η/8. The resulting regular full index is the sign of −16/3.
At η=0 it would be incorrect to apply the differentiable clipping
calculation without first removing that tie.

The negative-sign pair branch is not vacuous. Change only r₃({1})
from −1 to2 and r₃({1,3}) from −2 to1. Every joining difference
in (1) is unchanged. The traps become 12,13,123, still with greatest
core123. At

    v=(2,−1/3,1,−1/3),        q=(0,1/4,0,1/4),
    Q=(9/16,1/4,1/4,1/4),
    C=w=(43/32,1/4,13/16,1/4),

one has a full bad root with strictly inactive players0 and2. Both active
pair derivatives are −4/3, and the full determinant is −16/9. Thus the
class can have overlapping pair traps; the proof uses the positive product
of the two derivatives, not individual positivity.

### Changing one equality can produce a positive-index bad root

Return to the original complete table and change ONLY r₁(123) from1
to4. All seven strict inequalities and d₂(13)=0 remain unchanged, but
d₁(23)=3 instead of0. The trap family and own singletons are unchanged.
At

    v=(20,9/2,9/10,−7),       q=(0,1/2,2/3,1/11),

the actual endpoints are

    Q=(5/33,29/33,29/22,1/3),
    C=w=(469/132,29/33,29/22,1/3).

The outside-core gap is −449/132<0, every active gap is zero, and
w>(1,0,0,0), although v₃<0. The active derivative is

    Dg_C=[[0,69/11,11/6],[20/11,0,−11/20],[−10/3,−9/2,0]].

Its directed triangle products are 23/2 and −15. Therefore

    det D(Id−F)=−[23/2−15]=7/2>0.

This is a regular FULL index +1 bad root. The annotation lies in the
box B=21>M=20, so bounding the source does not repair that negative-index
extension. It is a counterexample only to dropping this equality from the
all-bad-negative-index lemma. It is NOT a UE counterexample and does not
assert the absence of another good root.

The proof also does not extend to a full four-player premium core or to
opposite-sign pair joining products. The raw class is confined to its
stated equality stratum; no reward-space neighborhood is inferred.

## Tracked inputs and Lean handoff

The formalization chain is: finite raw trap/core and joining tests; the full bad-root
support and partly-sure classification; proper pair/triple ambient indices
with annotation tie removal; selected singleton-sublevel return; the
canonical-bound Fin4 strict UE consumer; simultaneous passive-entry
perturbation and original-table weak UE. No strategic object is assumed
in that chain.

The generic source components are:

- `quittingGame` in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Game.lean`,
  for the initial zero live-state payoff and subsequent absorbing rewards.
- `MathUE/FiniteCoalitionPremiumCore.lean`, for the raw premium-trap
  predicate, greatest core, and outside insertion bound.
- `quittingPairInactiveGapNumerator_eq_mul_endpointDifference` and
  `dense_iInter_quittingPairInactiveGapNumerator_ne_zero` in
  `UniformEquilibrium/Quitting/Root/PairInactiveGapNumerator.lean`,
  with `MathUE/Topology/CoordinateAffineAvoidance.lean`, for the literal
  tie numerator and dense annotation avoidance.
- `MathUE/Topology/AmbientDegreeProperties.lean`,
  `MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`, and
  `MathUE/Topology/AmbientDegreeSelfMapNormalization.lean`, for local
  determinant degree, additivity, homotopy, and bounded-map total degree.
- `HasBoxedSelectedSingletonSublevelReturn` and
  `not_isQuittingFullExactRootPotential_of_selectedSingletonSublevelReturn`
  in
  `UniformEquilibrium/Quitting/Projective/SelectedSingletonSublevelReturnSmoothDrift.lean`.
- `exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_on_subbox`
  in
  `UniformEquilibrium/Quitting/Classification/Existence/SelectedSingletonSublevelReturnUniformPayoff.lean`.
  Its bound is the canonical sum-based `quittingRewardBound`; the choice
  B=M+1 above supplies its exact hypotheses.
- `exists_uniformEquilibriumPayoff_of_continuous_boundaryDifferentiable_potential_exclusion`
  in
  `UniformEquilibrium/Quitting/Classification/Existence/BoundaryDifferentiablePotentialUniformPayoff.lean`,
  and
  `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential` in
  `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`,
  for the original-game obstruction consumer.
- `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
  in
  `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`,
  for the weak strategic boundary.

The table comparisons use the literal singleton matrix, standard LCP
degree and passive inverse rows, not an unshifted passive reward row.
The response-partition declarations have their exact paths and hypotheses
given in the corresponding calculation above; the finite child witnesses
include their full behavioral response comparisons explicitly.
