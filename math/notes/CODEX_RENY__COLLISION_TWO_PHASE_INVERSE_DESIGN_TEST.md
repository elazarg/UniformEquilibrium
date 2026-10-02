# Collision-bearing two-phase test with an old stationary source

Author: CODEX_RENY.

## Status

Exact ordinary calculations, not independently reviewed or Lean-checked.
The full reward completion below has an exact two-phase behavioral Nash
profile and forbids every balanced singleton cycle, irrespective of word
length or player permutation. Nevertheless it is NOT new UE coverage: the
same completed table has an explicit stationary singleton-base equilibrium
with a sure owner. Its source is already covered by
`QuittingInducedOwnerChamber`. This inverse-designed fixture is retained
for testing other selectors, not proposed as a new export/class.

The candidate periodic Jacobian is singular as well, so a bare implicit
function assertion at this fixture would be invalid.

## 1. Complete table and canonical version

Players are 0,1,2,3, own singleton rewards all equal 1, and infinite
all-Continue pays zero. The full nonempty-coalition table is:

| Coalition | Reward vector |
| --- | --- |
| {0} | (1,4,0,0) |
| {1} | (4,1,0,0) |
| {2} | (0,0,1,4) |
| {3} | (0,0,4,1) |
| {0,1} | (3,3,0,0) |
| {0,2} | (1,3,1,3) |
| {0,3} | (−1,0,0,−1) |
| {1,2} | (0,−1,−1,0) |
| {1,3} | (3,1,3,1) |
| {2,3} | (0,0,3,3) |
| {0,1,2} | (1,4,−1,0) |
| {0,1,3} | (4,1,0,−1) |
| {0,2,3} | (−1,0,−1,4) |
| {1,2,3} | (0,−1,4,−1) |
| {0,1,2,3} | (−1,−1,−1,−1) |

For a canonical single-pivot test, subtract (0,1,1,1) from EVERY nonempty
row above and keep Never zero. The canonical own singleton vector is
(1,0,0,0), and the singleton comparison matrix is unchanged. Both exact
profiles checked below remain exact Nash for this canonical table, because
under each complete unilateral deviation their opponents absorb almost
surely. Every deviating payoff and the prescribed payoff are shifted by
the same constant in that coordinate. Their payoff vectors are shifted
by (0,1,1,1). This is a direct verification for these actual profiles, not
a general payoff-affine claim on Never-positive laws.

## 2. Matrix region and exclusion of singleton-word certificates

The comparison matrix is

    Γ = [ 0  3 −1 −1 ]
        [ 3  0 −1 −1 ]
        [−1 −1  0  3 ]
        [−1 −1  3  0 ].

Its determinant is 45 and its inverse is

    Γ⁻¹=(1/15) [2 7 3 3]
                [7 2 3 3]
                [3 3 2 7]
                [3 3 7 2].

The positive inverse gives full standard Q and excludes a homogeneous
simplex solution by strict copositivity and the exact LCP inversion
argument. The principal on {0,2} has both off-diagonal entries −1 and
fails projective Q at (−1,−1), including its cemetery-zero branch.
Every player has a strict negative witness, so the recursive normal core
is full. These are matrix facts, not an actual positive terminal gap.

Any balanced singleton cycle can discard its zero-hazard phases. At any
transition from a positive-hazard owner j to a distinct owner i, Bellman,
the active equality at i's phase, and i's passive floor at j's phase force
Γᵢⱼ≥0. The only such edges here are within the two disjoint pairs {0,1}
and {2,3}. Thus one cycle cannot visit both pairs. If it remains in just
one pair, every player in the other pair receives sᵢ−1 on every possible
singleton absorbing outcome; this violates its floor. Consequently there
is no balanced singleton cycle at all, not merely no four-phase ordering.

In particular neither the frozen four-cycle producer under any permutation
nor a longer singleton word accounts for the equilibrium below. That fact
does NOT rule out collision-sensitive stationary production.

## 3. The actual two-phase profile

At phase A, players 0 and 2 independently Quit with probability 1/2, while
players 1 and 3 Continue. At phase B, players 1 and 3 use hazard 1/2 and
players 0 and 2 Continue. Repeat AB forever. The actual values are

    vᴬ=(1,2,1,2),                 vᴮ=(2,1,2,1).

Joint survival per phase is 1/4 and per period 1/16, so these are actual
geometric-resolvent values. Direct Bellman checks each coordinate.

For an active player at either phase, Quit has payoff 1: its own singleton
and its prescribed pair both pay 1. Continue has payoff 1 as well, because
the other active owner pays it zero upon solo absorption and the following
phase value is 2. For a passive player, Continue has its displayed value 2.
Quit has payoff

    (1+3−1+4)/4=7/4<2.

The four terms correspond to no opponent quitting, its friendly opponent,
its other opponent, and both opponents. The triples used in this test are
the JOINER coordinates fixed at 4; the modified owner coordinates in two
triples do not enter these passive gains.

Every local root condition is therefore exact Nash. Every player faces
three positive opponent hazards per period, whose survival product is 1/8.
Iterating the Bellman inequalities caps every finite pure stopping date;
the Never remainder vanishes geometrically. The pure-date mixture
representation caps all complete behavioral deviations. This gives exact
terminal Nash and, by uniform geometric opponent absorption, the fixed
uniform payoff vᴬ. No public correlation or detected deviation is used.

## 4. The old stationary singleton-base source is explicit

The same completed table has the stationary root

    q=(1,1/2,1/2,0).

Player 0 is a sure quitter. Its prescribed terminal payoff vector is

    U=(3/2,7/2,0,3/4).

For player 1, Quit and Continue both give 7/2. For player 2, Quit and
Continue both give zero. Player 3's immediate Quit payoff is 1/4, strictly
below its prescribed 3/4. These computations condition only on the sure
owner and the two independent half-hazards.

For player 0, Never against the two stationary half-hazard opponents gives
4/3, while its prescribed Quit gives 3/2. Every other pure stopping date
lies between these two values, by the geometric recursion with the same
opponent root. Thus this owner also has no profitable full response.
Equivalently its same-root Continue endpoint is

    1+(1/4)(3/2)=11/8<3/2.

All behavioral responses are capped, including Never. The induced finite
Nash point has free players {1,2}. Against all-Never opponents the owner's
cap is s₀=1, so its punishment value P₀≤1. The literal punishment-priced
owner-floor excess is therefore

    1+P₀/4−3/2≤−1/4<0.

Together with the strict outsider no-join inequality 1/4<3/4, these are the existing
`QuittingInducedOwnerChamber` source fields; the profile is not merely a
stationary numerical approximation. Its canonical payoff is
(3/2,5/2,−1,−1/4).

There is no pure sure-coalition Nash profile for this table: singletons are
blocked by a profitable enemy join, friendly pairs by an owner leaving to
its friend's singleton, the prescribed hostile pairs by an outsider joining,
the other hostile pairs by an owner leaving, every triple by one owner with
reward −1 leaving to a pair paying it zero, and the full coalition by an
owner leaving to a triple paying it zero. The explicit mixed stationary
source nevertheless makes absence of a pure equilibrium irrelevant to new
coverage.

## 5. The naive open-neighborhood argument also fails

Let the four variables be the hazards q₀,q₂ at A and q₁,q₃ at B. Eliminate
the actual two-phase values by their geometric resolvent, and let Fᵢ be the
active player's Quit-minus-Continue endpoint at its phase. In coordinate
order (q₀,q₁,q₂,q₃), the exact Jacobian at all hazards 1/2 is

    J = [  0    −8/5   32/15   8/15 ]
        [−8/5    0      8/15  32/15 ]
        [32/15   8/15   0     −8/5  ]
        [ 8/15  32/15  −8/5    0    ].

It annihilates (1,−1,−1,1) and has determinant zero. Therefore an implicit
function assertion from this fixture would need additional work even if
its stationary overlap were absent. This calculation is exact symbolic
differentiation, not a numerical near-zero determinant.

## 6. Source comparison and disposition

The existing `QuittingInducedOwnerChamber` and its methods `certificate`
and `uniformEquilibriumPayoff` are in
`UniformEquilibrium/Diagnostics/Quitting/InducedOwnerChambers.lean`.
Their source fields and owner/outsider signs were inspected directly. The
fixed two-phase semantic object can instead feed
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `Quitting/Cycles/PeriodicCompiler.lean`; it is not a new consumer.
The exact punishment-priced owner-floor definition was checked in
`Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.

`exists_uniformEquilibriumPayoff_of_periodic_rectangular_face_signs` in
`Quitting/Cycles/PeriodicRectangularFaceSign.lean` was also inspected in
full. It consumes a continuous active-gap field with strict rectangular
face signs, an actual hazard map, strict inactive endpoint inequalities,
and opponent contraction. No new theorem supplies its rectangular source
from the present singular Jacobian. The full pure-date/Never semantics are
also explicit in `PeriodicRootResponseSystem.lean`.

The complete fixture is available for selector tests, including its explicit
canonical transformation. It is not a new existence class, a stationary
class obstruction, or evidence of a hard terminal-gap source. The matrix
residual alone did not settle the reward-completion coverage question.
