# Clock observability seminorms and proper-law closure

Author: CODEX_LARCH_DUAL. Round-two hypothesis/interface mining.

Status: ordinary mathematical proof sketch, passed
[independent review by CODEX_LARCH_JOINT](../feedback/CODEX_LARCH_ROUND2_DUAL__STRATEGIC_CLOCK_SEMINORM__BY_CODEX_LARCH_JOINT.md)
with no unresolved mathematical objection; not Lean-checked. The reusable theory is the topology
of random times observed through bounded before/tie/after payoff tests. It
gives an exact seminorm, null directions, distance to proper laws, and a
proper-law closure dichotomy. The watchdog interface is an illustration of
where this theory is currently implicit in code; obtaining a new UE producer
is not an objective of this note.

## 1. The reusable object and the interface mismatch

The native mathematical object needs no game. A random clock takes values
in ℕ∪{∞}. Choose one common before-event reward and, for finitely many event
marks S, mark-dependent rewards on a tie and after the event. Test the clock
against every deterministic event date, and include an event that never
occurs. The supremum of differences of expected test rewards is an integral
probability seminorm on clock laws. The finite coefficients determine what
clock information is visible and whether Never lies in the closure of the
proper clocks. Several payoff observers simply contribute a finite union
of these tests.

In the quitting specialization, marks are opponent coalitions and the
before-event reward is the singleton reward. Every marked deterministic
event is feasible. Independent randomized opponents only average the
same tests, so they do not enlarge the seminorm. This is the mathematical
reason the strategic definition below collapses to a cumulative/atom norm.

`QuittingStrategicallyWithin`
(`UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdog.lean`)
tests the difference of ONE player's own payoffs against every behavioral
opponent profile. The proper-watchdog boundary uses TV approximation as a
sufficient condition and obtains an essential-Never witness abstractly.
It does not characterize that witness directly from the reward table.

The exact stopping-time order payoff has only three cases: stop before the
first opponent event, tie it, or stop after it. This suggests evaluating the
intrinsic strategic distance on cumulative finite mass and individual atoms,
instead of using TV as a proxy.

This differs from the already exported finite operational pseudometric in
[the censored-reshuffling packet](../formalized/CENSORED_RESHUFFLE_NULL_DIRECTION_AND_EFFECT_SENSITIVE_PARTICIPANT_DISPATCH.md).
That object compares two supplied finite profiles and their current response
observables. Here one player's two arbitrary complete laws are tested against
ALL possible opponent profiles, and the coefficients are computed directly
from the reward table.

## 2. Exact reward-dependent formula

Fix a finite nonempty player set I, one player i, and bounded coalition
rewards. Let p,q be probability laws on ℕ∪{∞}; ∞ means Never. All players'
randomizations are independent, and all complete behavioral deviations are
allowed. Define the signed law σ=p−q and

    Fσ(t−)=Σ_(k<t) σ(k),          s=r_i({i}).

For every nonempty opponent coalition S⊆I\{i}, put

    a_S=s−r_i(S),       b_S=r_i(S∪{i})−r_i(S).

Define the strategic distance

    d_i(p,q)=sup_(opponent profiles ρ)
        |U_i(p,ρ)−U_i(q,ρ)|.

**Exact seminorm formula.**

    d_i(p,q)=max {
        |s σ(∞)|,
        sup_(t∈ℕ, nonempty S⊆I\{i})
           |a_S Fσ(t−)+b_S σ(t)|
    }.                                                    (1)

When there are no opponents, omit the second term. Equivalently interpret
the maximum over an empty set of nonnegative tests as zero.

Proof: fix deterministic opponent clocks. If all are Never, the payoff
difference is sΣ_k σ(k)=−sσ(∞). Otherwise their first event has some date t
and nonempty coalition S. The three payoffs for i are respectively
s,r_i(S∪{i}),r_i(S), so the difference is

    s Fσ(t−)+r_i(S∪{i})σ(t)+r_i(S)σ((t,∞])
      = a_S Fσ(t−)+b_S σ(t),

using total signed mass zero. Every displayed (t,S) is realized by actual
deterministic opponent laws: S stops at t and everyone else plays Never.
An arbitrary independent opponent profile averages these deterministic
first-event tests, so its absolute difference cannot exceed their supremum.
Both inequalities in (1) follow. There is no attainment assumption.

The reward test SHAPES are finite, but time still ranges over every integer.
The formula is not a finite universal calendar theorem. It is a seminorm on
zero-total-mass signed laws, restricted here to differences of probabilities.

### The strict-inequality caveat in the current interface

The Lean predicate requires each opponent-profile difference to be strictly
less than an error. This need not mean their supremum is strictly smaller:
the supremum can equal the error without being attained. Correct implications
are

    d_i(p,q)<ε  ⇒ StrategicallyWithin ε,
    StrategicallyWithin ε ⇒ d_i(p,q)≤ε.

Every all-positive-accuracy approximation statement can absorb this boundary
by choosing a smaller error first. An implementation must not claim a false
pointwise equivalence between the present predicate and open metric balls.

## 3. Exact distance from a law to the proper laws

A law is proper when its Never mass is zero. Define the finite table constant

    κ_i=max({|s|} ∪ {|s−r_i(S)|:∅≠S⊆I\{i}}),
    β_i=max({0} ∪ {|b_S|:∅≠S⊆I\{i}}).

**Proper-distance theorem draft.** For every complete stopping law p,

    inf_(q proper) d_i(p,q)=p(∞) κ_i.                    (2)

For the lower bound, put ν=p(∞) and fix any proper q. Then

    σ(∞)=ν,        Fσ(t−)→−ν,        σ(t)→0.

The all-Never test gives ν|s|. Sending the deterministic opponent coalition
date t to infinity in each test of (1) gives ν|a_S|. Thus d_i(p,q)≥νκ_i.
This is a limit of legal finite-date tests, not a newly allowed infinite
coalition arrival.

For the upper bound, let u_L be uniform on any L distinct finite dates and
set

    q_L=p restricted to ℕ + νu_L.

The entire original finite part is retained, even when it has unbounded
support. The new law is proper. The finite signed masses p−q_L are all
nonpositive, with total −ν and largest absolute atom ν/L. Thus

    |Fσ(t−)|≤ν,        |σ(t)|≤ν/L,
    d_i(p,q_L)≤νκ_i+νβ_i/L.                             (3)

Let L tend to infinity. This proves (2), including ν=0 and one-player games.
The infimum need not be attained.

**Exact consequence.** Never is strategically approximable by proper laws
if and only if κ_i=0, equivalently

    r_i({i})=0 and r_i(S)=0 for every nonempty S excluding i.   (4)

Rewards on coalitions that contain i and another player may be arbitrary:
their effect can be diluted by spreading the replacement atom over time.
The absent-coalition and solo terms cannot be diluted, because opponents
may choose arbitrarily late test dates.

For a general law p, failure of proper approximability is exactly
p(∞)>0 and κ_i>0. The reward constant identifies the size of the barrier,
not merely its existence.

In intrinsic-topology language, the closure of the proper laws is therefore
either the proper laws themselves (κ_i>0) or the entire law space (κ_i=0).
There is no intermediate closure. When κ_i>0, formula (1) also gives
κ_i|p(∞)−q(∞)|≤d_i(p,q), so Never mass is a continuous observable with an
explicit Lipschitz constant. When κ_i=0, the diffuse approximations show
exactly why that observable disappears from the topology.

## 4. Direct watchdog consumers

Let D be a family of player-i laws. Proper strategic approximation by finite
proper nets is equivalent to the conjunction of:

1. D is strategically totally bounded;
2. either κ_i=0 or every member of D is proper.             (5)

Necessity of total boundedness follows by replacing each nonempty ball of an
external finite net with a member of D and doubling the radius. Necessity of
the second condition follows from (2). Conversely take a finite strategic
net in D. Under the second condition each center is proper or, when κ_i=0,
admits arbitrarily close proper approximants by (3). Replacing the finitely
many centers and using the triangle inequality proves proper approximation.
Use slack radii for the strict interface caveat above. The empty family has
the usual harmless one-point proper external net.

This sharpens
`exists_nonproper_essentialNeverWitness_of_totallyBounded`
(`UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`):
inside a totally bounded family, the essential-Never obstruction is now
exactly a positive Never atom multiplied by the explicit table constant κ_i.
Every proper comparison is separated by at least that amount.

It also supplies a cheap raw-table test for the “properly approximable
complete reply class” route in the existing watchdog research. If κ_i=0,
the proper-center obligation adds no condition beyond strategic total
boundedness. This does NOT say that all strategies form a totally bounded
family, or produce a complete family. Those are separate hypotheses, and the
proper-sentinel compact-game consumer is not proved by the present note.

### Exact geometry in the tie-only chamber

When κ_i=0, (1) simplifies to

    d_i(p,q)=β_i sup_t |p(t)−q(t)|.                        (6)

If β_i=0, all laws are strategically identical and every family is properly
strategically approximable. If β_i>0, a family D is properly strategically
approximable if and only if

    lim_(N→∞) sup_(p∈D, t≥N) p(t)=0.                     (7)

Proof: each individual finite-atom sequence lies in c₀, since its sum is at
most one. A finite net in the atom supremum norm has uniformly small tails,
and approximation transfers that property to D. Conversely, under (7),
approximate the first N atom coordinates by a finite grid in [0,1]^N and
ignore the uniformly small tail. Choosing a member of D in every nonempty
grid cell gives a finite net with centers in D. Formula (5) then replaces
those centers by proper ones. This argument includes the empty family using
the earlier convention.

The condition controls late ATOMS rather than late total mass or Never
mass. For example, the family of uniform laws on {0,...,L−1}, over all L≥1,
together with Never, satisfies (7), although it is not uniformly finite-time
tight. When κ_i=0 it therefore has proper strategic finite nets.

Consequently, failure of proper strategic approximation in this chamber is
equivalent to a fixed positive atom size appearing at arbitrarily late
dates in the family. This sharpens the general late-or-Never mass boundary
to an actual late-atom obstruction in an explicit reward-table class.

### Full-range limitation

Independent reviewer CODEX_LARCH_JOINT observed a further immediate
classification. The space of ALL stopping laws is strategically totally
bounded if and only if i's reward is constant across all nonempty coalitions.
Indeed, any b_S≠0 separates every pair of distinct pure finite clocks by
at least |b_S|, by testing the earlier date. If all b vanish but some a_S≠0,
testing the later date separates them by |a_S|. If all a and b vanish, (1)
reduces to |s| times the difference of Never masses, whose quotient is a
compact interval. The same statement includes one-player games, where the
reward is automatically constant on their single nonempty coalition.

Combining this with (2), ALL stopping laws are properly strategically
approximable if and only if i's reward is zero on every nonempty coalition.
Thus a nontrivial watchdog application must select a smaller complete reply
family, rather than seek proper precompactness of the entire strategy space.

## 5. What the distance does and does not control

The metric in the source is OWN-PAYOFF distance. It does not automatically
control the effect of changing i's law on another player's payoff or cap.
For example, let every reward of i be zero but give another player h reward
one when i quits alone and zero otherwise. Then d_i is identically zero,
although replacing i's Never law by immediate Quit can change h's payoff.

There is an exact all-observer variant. For each observer h replace s,a_S,b_S
in (1) with

    s_h=r_h({i}),
    a_S,h=r_h({i})−r_h(S),
    b_S,h=r_h(S∪{i})−r_h(S).

This gives d_(i→h), the maximum change in h's prescribed payoff against all
other-player laws. For h≠i, it bounds the change in h's full cap as well,
because the supremum defining d_(i→h) already permits every replacement law
of h. For h=i, replacing its prescribed law does not change its cap at all.
Thus max_h d_(i→h) is the appropriate uniform quantity for a genuine
cross-player repair. Replacing it by d_i alone would erase strategic harm.

The same proof gives the distance to proper laws for this larger maximum,
with κ_i replaced by the maximum of its observer-specific κ constants.
The common diffuse approximation q_L works for every observer simultaneously.
Thus the all-observer version is an elementary corollary of the SAME
finite-feature observability theory: take the union of the test families.
It needs no new strategy class, compactification, or equilibrium machinery.
Its null space is the intersection of the observer null spaces, and its
proper-law closure is governed by their maximum κ. Requiring control of
additional observers refines the topology in this explicit way.

## 6. Small checks and boundaries

**Timing-sensitive example.** For two players, give i singleton reward one,
opponent-only reward zero, and pair reward one. Then a=b=1 and (1) reduces
to the cumulative-mass supremum, including its limit at Never. Distinct pure
dates have distance one, and d_i(Never,q)=1 for every proper q. No finite
fixed collection of opponent dates detects every difference between late
pure clocks: put both clocks beyond the tester menu and distinguish them
with an opponent quitting at the earlier new date.

**Tie-only example.** Set solo and absent rewards to zero and pair reward
one. Then d_i(p,q)=sup_t|p(t)−q(t)|. Never has distance 1/L from the uniform
law on L dates, so (2) gives zero as required. Nevertheless the pure clocks
δ_t are pairwise distance one. Thus κ_i=0 does not make the entire law space
totally bounded.

**Time-invisible but Never-visible example.** Give i reward one at every
nonempty coalition. Then a=b=0 and d_i(p,q)=|p(∞)−q(∞)|. All proper clocks
are strategically identical, including the non-tight family {δ_t:t∈ℕ}.
Its proper strategic approximation is exact although proper TV approximation
fails. This shows why the intrinsic criterion can be strictly sharper than
TV/tightness.

**Null directions.** Formula (1) already gives an exact finite-coefficient
linear test of null directions. If some a_S≠0, the recurrence
a_S Fσ(t−)+b_Sσ(t)=0, starting at Fσ(0−)=0, forces every finite σ(t)=0
(if b_S=0, use the cumulative constraints directly), hence σ(∞)=0. If all
a_S=0 but some b_S≠0, the atom tests likewise force equality. If all a and b
vanish, only the Never-mass term remains; when also s=0 the pseudometric is
identically zero. This classifies separation, not all quantitative norm
equivalences or compact subsets.

## 7. Overlap, provenance, and next bounded step

The original watchdog note
`CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md`, Proposition 6BM.7,
already proves the κ_i=0 sufficient diffuse-Never example. It does not state
necessity, the exact positive distance νκ_i, or the finite reward-test formula
in the section inspected. Thus the new claim is an exact characterization
and intrinsic metric adapter, not rediscovery of its positive example.

The source files inspected under their stated imports were:

- `QuittingStrategicallyWithin` and `IsQuittingStrategicallyTotallyBounded`
  (`UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdog.lean`).
- `IsQuittingProperStrategicallyApproximable`,
  `exists_lateOrNeverMass_escape_of_not_properStrategicallyApproximable`, and
  `exists_nonproper_essentialNeverWitness_of_totallyBounded`
  (`UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`).
- The imports of that boundary include stopping-law reconstruction and the
  generic proper-PMF approximation module. No new Lean compilation was run.

This lead came from a mismatch between a universal hypothesis and its
sufficient approximation proxy, not from nearby duplicate proof text. A
bounded search of the watchdog sources, the Ramsey source note, and the
formalized/exports metric references did not locate (1)–(5). That is not an
exhaustive novelty claim or evidence of independent historical rediscovery.
The watchdog core and proper-boundary modules were added about three hours
apart on August 24, so they count as one development episode. The present
round compares their open metric boundary with later stopping-order
identification, rather than treating those two nearby modules as separate
votes for a missing theory.

The linked independent review checked (1)–(7). The subsequent
[completion and compactness classification](CODEX_LARCH_ROUND2_DUAL__STRATEGIC_CLOCK_COMPLETION.md)
also passed review: it identifies the TV-topology case and the precise diffuse
finite-mass defect when atom size and Never mass remain visible but cumulative
mass does not. Together these form one reusable mathematical package.
Classification of a supplied watchdog range is an illustrative application,
not a further UE proof-search assignment. No Lean, export, commit, or shared
index was created by this investigation.
