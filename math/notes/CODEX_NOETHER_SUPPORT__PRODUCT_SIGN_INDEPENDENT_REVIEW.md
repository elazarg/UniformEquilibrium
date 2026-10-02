# Independent derivation of the product-sign class and LP separation

Identity: CODEX_NOETHER_SUPPORT.

Status: blind derivation completed from the raw statement only, before
opening the author manuscript or the first review. The proposed condition,
Fin4 example, LP separation, and normalization survive this check. Full
manuscript and final-byte review remain pending. Ordinary mathematics and
static source inspection, not a Lean build.

## Exact condition and conclusion to review

There are finitely many nonempty players, independent private behavioral
strategies, terminal rewards r_i(S), and zero Never payoff. Put
s_i=r_i({i})≥0. For every product root q∈[0,1]^I with exact nonempty active
support A={i:q_i>0}, assume there is some i∈A whose pure Quit payoff
Q_i(q) is at most s_i. No root Nash, continuation, payoff target, or
equilibrium strategy is supplied in the premise.

The claimed conclusion is actual periodic terminal ε-Nash profiles at
every positive ε, from every live suffix, against all behavioral
deviations, and consequently one fixed uniform-equilibrium payoff.

## Blind computation of the Fin4 family

For participants i∈S, the proposed own premiums are

d_0(S)=1[1∈S]−1[2∈S],
d_1(S)=1[2∈S]−1[0∈S],
d_2(S)=1[3∉S](1[0∈S]−1[1∈S]),
d_3(S)=1[{0,1,2}⊆S].

They vanish at own singletons, so these specifications are consistent with
arbitrary s_i≥0. Passive rewards do not enter a pure Quit endpoint.
Writing q=(x,y,z,t), independent expectation gives exactly

(Q_0−s_0,Q_1−s_1,Q_2−s_2,Q_3−s_3)
=(y−z,z−x,(1−t)(x−y),xyz).                               (1)

If x,y,z are positive, suppose all first three premiums were positive.
The first two imply y>z>x. The third either vanishes when t=1 or implies
x>y when t<1. Both cases contradict strict positivity of all three.
Thus one of these active core players has a nonpositive premium.

If at least one core coordinate is zero but at least one is positive,
use the following exhaustive boundary tests:

- x>0 and y=0 gives player 0 premium −z≤0.
- y>0 and z=0 gives player 1 premium −x≤0.
- z>0 and x=0 gives player 2 premium −(1−t)y≤0.

Any nonempty proper subset of the three core coordinates has one of these
cyclic positive-to-zero adjacencies. If all three are zero, nonempty
support forces t>0 and player 3 has premium xyz=0. This proves the raw
condition for every product, including all sure-Quit faces. At q=(1,1,1,1)
the premiums are (0,0,0,1), which illustrates why a positive grand-coalition
premium need not destroy the product condition.

## Exact LP contradiction

Suppose a nonnegative normalized full-support LP weight w existed.
Coalitions {0,1}, {1,2}, and {0,2} give respectively

w_0≤w_1,       w_1≤w_2,       w_2≤w_0.

Hence w_0=w_1=w_2. At {1,2,3}, the only positive-weight contribution
that can be nonzero is d_1=1; d_2=d_3=0. Its inequality gives w_1≤0,
so all three core weights vanish. At the full coalition only d_3=1 is
nonzero, giving w_3≤0. Normalization is now impossible. This proves
failure even when zero weights are allowed, for every passive completion
and every chosen nonnegative singleton vector.

Conversely the all-support LP always implies the raw product condition:
at the exact active set A, its one fixed weight vector gives
Σ_{i∈A}w_i q_i(Q_i−s_i)≤0, and at least one w_i q_i is positive.
Thus the proposed family proves strict separation from that sufficient
test, including its ordered and global-positive-weight subclasses.

## Blind normalization and consumer check

For t>0 set h_i=s_i+t and r'_i(S)=(r_i(S)+t)/h_i. Then
Q'_i(q)−1=(Q_i(q)−s_i)/h_i, so the same active witness retains its sign.
In particular this works when s_i=0; no division by s_i occurs.

For target error ε, choose t=ε/4, η=ε/2, H=max_i h_i, and use unit-table
terminal error η/H. Undoing positive scales gives regret at most η for
r+t. For every prescribed or deviated profile, including Never,
U_i(r+t)−U_i(r)=t·P(absorption)∈[0,t]. Original regret is therefore at
most η+2t=ε. Periodicity and every-suffix guarantees survive because the
actual strategies are unchanged. The fixed original-table payoff is
selected only after obtaining all positive terminal accuracies.

The live source files now explicitly contain the generic classical
consumer. I inspected `HasLowActiveQuittingRootQuitPayoff` and
`HasLowActiveQuittingRootQuitPayoff.exists_for_tail`
(`UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRow.lean`).
The predicate uses level one and the zero-tail Quit endpoint; the latter
is continuation independent. I also inspected
`exists_periodic_quittingPerfectAbsorbingRootSequence_of_lowActiveQuitPayoff`
(`UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRootSequence.lean`)
and `exists_cyclic_subgamePerfectTerminalNash_of_lowActiveQuitPayoff` and
`exists_uniformEquilibriumPayoff_of_lowActiveQuitPayoff`
(`UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`).
Their hypotheses are unit singletons and the low-active product-root
predicate. The new family and LP separation must not be presented as a
new proof of that generic consumer. These recently modified declarations
were read under their actual imports; no compilation was run here.

## Initial overlap and falsification boundaries

The family is outside the all-support LP criterion regardless of passive
completion. This does not mean that every completion is outside every
existing equilibrium class. For example, if every passive reward is zero,
all four players quitting at date zero is exact terminal Nash: a player
continuing alone receives zero, while its grand-coalition reward is s_i
for i=0,1,2 and s_3+1 for player 3. All are nonnegative.

The proof of (1) specifically uses product independence for the factor
(1−t)(x−y) and for xyz. It does not apply to arbitrary correlated
coalition laws. It also requires the complete support case distinction:
finding a nonpositive premium at an inactive coordinate is insufficient.
No continuity of a witness selector is needed or asserted.

Next check: receive and read the author's complete manuscript, inspect its
exact scope and source claims, then write the independent review without
consulting the first verdict.
