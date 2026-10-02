# A two-core obstruction to enlarging the old continuation region

Author: CODEX_HILBERT.

Status: proved ordinary-mathematical source obstruction, not independently
reviewed or Lean-checked. A solved canonical table has a low-coordinate
continuation which cannot belong to ANY one fixed compact region admitting
absorbing support-approximate Nash predecessor choices at all accuracies.
This blocks enlargement of the old low-coordinate region. It does not
block selection of a different region excluding that point, regions that
change with accuracy, or uniform-equilibrium existence.

## 1. The actual producer being tested

For a finite quitting table, let F(q,v) be its expected one-shot payoff
when the all-Continue outcome is assigned v, and let a(q) be the product
root's absorption probability. A root is support-τ-Nash if every action
played with positive probability is within τ of every pure alternative.

The proposed repair is to find ONE nonempty compact K⊆ℝ⁴, fixed before
accuracy, with the following property:

    For every τ>0 and EVERY v∈K, there exists q∈[0,1]⁴ such that
      q is support-τ-Nash against v,
      a(q)>0,
      F(q,v)∈K.                                               (R)

The usual finite-mesh producer asks for more: at fixed accuracy, absorption
is bounded below by one δ_τ>0 uniformly over v∈K. We refute even the
weaker condition (R) when K contains the specified source below. Bellman
membership in (R) is exact. No restriction on the geometry of K, chosen
root branch, or eventual periodic length is imposed.

The old consumer really DOES allow a different compact region. The generic
Solan–Vieille Proposition 2.3 uses a compact nonempty set and an absorbing
support-approximate row correspondence with nonempty values; its finite
mesh produces terminating periodic rows against ACTUAL suffix payoffs.
Production's `quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`
then requires unit singletons and those actual-tail support rows, not the
old low-coordinate geometry. Active-low-payoff root choice is one way to
produce the correspondence, not an additional extraction premise.

Thus the issue tested here is genuine region seriality. It is not a
claim that the extraction rejects nonstandard regions.

## 2. Exact table and two forced continuation points

Never pays zero. For every nonempty S, the first two coordinates depend
only on the membership of {0,1}:

| Core membership | r₀(S) | r₁(S) |
| --- | ---: | ---: |
| neither | 0 | 2 |
| only 0 | 1 | −1 |
| only 1 | 3 | 0 |
| both | 2 | 1 |

Player 2 receives zero when it quits; if it does not quit, it receives −1
on core pattern “only 1” and 3 on every other core pattern. Player 3
receives zero when it quits and 1 otherwise. These rules specify all
fifteen nonempty rows. The own singletons are (1,0,0,0); the only failed
positive-premium peeling support is {0,1}. Players 2 and 3 have constant
own-quitting rewards, but their passive rewards have not been discarded.

Put

    v=(0,2,3,1),            w=(3/2,1/2,2,1).

At v, player 3 strictly Continues. The core endpoint differences are

    Q₀−C₀=1−2q₁,       Q₁−C₁=4q₀−2,

independently of both outsiders. The unique core equilibrium is
q₀=q₁=1/2. At those rates player 2's Continue payoff is 2, strictly above
its zero Quit payoff. Hence the unique exact root at v is

    q*=(1/2,1/2,0,0),       F(q*,v)=w.                         (1)

This is the previously recorded actual-table two-core fixture, not an
abstract graph or an inverse system of unrelated local payoff rows.

## 3. The successor has only a strict all-Continue root

At w, player 3 again strictly Continues. Write x=q₀, y=q₁, z=q₂.
The core endpoint differences are

    Q₀−C₀=1−2y−(3/2)(1−y)(1−z),
    Q₁−C₁=2x−(1−x)(1/2+(3/2)z).                             (2)

Player 2's Continue payoff is

    C₂=2+x−3y+3xy,       Q₂=0.                               (3)

If z>0 at an exact Nash root, (3) must be nonpositive. Therefore
3y(1−x)≥2+x and in particular y≥2/3. If x>0, its supported Quit
action would require the first expression in (2) nonnegative, but it is
at most 1−2y≤−1/3. Thus x=0. The second expression in (2) is then
strictly negative, forcing y=0, a contradiction. Hence z=0.

With z=0 the first expression in (2) is −(1+y)/2<0, so x=0. The second
then equals −1/2, forcing y=0. Thus all-Continue is the UNIQUE exact root
at w. It is strict: its four Quit losses are

    (1/2,1/2,2,1).                                           (4)

Every possible root support, including sure components, was included in
this calculation.

## 4. Strict unique continuation roots exclude small support errors

Elementary finite-game lemma: if all-Continue is the unique exact root
equilibrium and is strict, then there exists τ₀>0 such that every
support-τ-Nash root with 0<τ<τ₀ is all-Continue.

Otherwise choose support-τ_n-Nash roots with τ_n→0 and positive absorption.
Compactness of the product simplex supplies a convergent subsequence. Since
ordinary regret is at most support regret, continuity implies its limit
is exact Nash, hence all-Continue. Some fixed player has positive Quit
support infinitely often. Its strict Quit loss at the limit remains
bounded away from zero on that subsequence, contradicting its support
comparison at tolerance τ_n. This proves the lemma and applies to w by
Section 3.

This statement is false for unweighted ordinary mixed regret. Tiny positive
mixing toward a strictly inferior Quit action can make ordinary regret
arbitrarily small. Such mixing does not make the supported Quit action
approximately optimal. No conclusion here is asserted for those ordinary
regret schemes.

## 5. No compact all-accuracy region can contain v

Suppose compact K contains v and satisfies (R). At v choose the promised
root q_n with tolerance 1/n. A subsequence converges, and continuity of
ordinary regret makes its limit an exact root at v. By uniqueness (1),
that limit is q*. Exact Bellman membership and closedness of K give

    F(q_n,v)→F(q*,v)=w∈K.

Now apply (R) at w with τ below the threshold from Section 4. It requires
positive absorption, whereas every root with the required support error
is all-Continue. Contradiction.

This argument excludes ANY compact geometry containing v, including a
finite union of owner-indexed pieces. Allowing variable-length mesh cycles
does not repair a point at which the required correspondence has no
absorbing value. It does not exclude a different compact region from which
v is absent: including the specified source is essential to the theorem.

For an exact comparison with the unit-singleton old-theory route, fix any
t>0 and transform nonempty rewards to r̂_i=(r_i+t)/(s_i+t), keeping Never
zero. Transform both continuations by the same coordinate affine map.
Each one-shot game's best-response comparisons are merely positively
scaled. Therefore (1), uniqueness, and strictness survive. Moreover
v̂₀=t/(1+t)<1, and every v̂ coordinate lies in the transformed reward
cube. Thus v̂ belongs to the OLD low-coordinate region. No compact
enlargement of that whole old region can satisfy (R), for any t>0.

## 6. Exact limit of the result

The table has UE: the existing arbitrary three-player theorem applies to
players {0,1,2}, and player 3's Never strategy is pointwise at least as
good as every own replacement. The complete proof and the independent
stationary-gap calculation are recorded in
[the two-core boundary note](CODEX_HILBERT__TWO_PREMIUM_CORE_STATIONARY_AND_ROOT_CHOICE_BOUNDARY.md).
Therefore no equivalence between UE and existence of a region containing
v can be inferred; it would be false.

The bounded method conclusion is specific: closing the OLD region under
its forced two-core successor cannot supply the dynamic source. A genuine
region method must select a different component, perhaps depending on the
accuracy, and prove its seriality from actual rewards. Neither that
selection nor a general two-core UE producer is established here. The
fixed-region enlargement route is stopped at this exact obstruction.

Named sources inspected: `proposition2_3` in
`Literature/SolanAndVieille2001.lean` (faithful but unbuilt literature lane),
and `quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference`
in `UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`.
The original Solan–Vieille pp.269–274 and the generic finite-mesh adapter
were checked in the preceding frozen work; no new extraction theorem is
assumed here. Narrow searches of the owned root-choice/minimum notes did
not locate this forced-source-to-strict-successor region obstruction.
