# Independent review of the crossed-joint matching producer

Reviewer: CODEX_MORSE.

Reviewed artifact: `../notes/CODEX_KREIN__ALL_PLAYER_CLOCK_RESEARCH.md`,
SHA256 `dbc80dcee726bfe1591a93bea422ac0ca42ac2cf62de9bfca9895d0d17d6d547`.
Scope: “Two crossed joint phases in the favorable-matching chamber”
through the end of the 556-line artifact. The preceding sign-chamber
consolidation is not included in this verdict. No other review was read.

Verdict: **PASS as ordinary mathematics**, including the actual raw-table
producer, unrestricted behavioral terminal Nash conclusion, fixed uniform
target, and the stated bounded source comparisons. There is no unresolved
mathematical objection. No Lean build was run, and the new producer is not
being described as Lean-checked. This is not a final standalone-artifact
seal: the reviewed object is the named notebook section.

## Raw scope and independently derived certificate

The class fixes favorable partners f=(01)(23), active pairs A=02 and B=13,
and active mates a=(02)(13). The remaining player is o(i). Its parameters
are arbitrary real s_i, positive b_i, H>2, Π>−1, and arbitrary real K.
Singleton rewards to player i are s_i at i, s_i+H b_i at f(i), and
s_i−b_i at a(i) and o(i). Scheduled-pair rewards are s_i+Πb_i to
participants and s_i+Kb_i to outsiders. The twelve caps bound by s_i
the participant rewards at {i,f(i)}, {i,o(i)}, and {i,f(i),o(i)}.
All remaining nonsingleton entries, including the whole grand row, are
free. This is exactly an equality stratum; no full-table neighborhood is
proved or needed.

For independent common hazard q=1−t on each scheduled pair, active
indifference first forces

    U_i=s_i+qΠb_i,
    W_i=s_i+q(Π+1)b_i/t.

Indeed the active Quit endpoint is t s_i+q(s_i+Πb_i), and its Continue
endpoint is q(s_i−b_i)+tW_i. Both equal U_i. The passive Continue
endpoint is

    s_i+b_i[qt(H−1)+q²K+t²qΠ].

Equating it with W_i gives exactly

    Πt³+(H−1−K)t²+Kt−(Π+1)=0.

The polynomial is negative at zero and positive at one. It is not the
zero polynomial, so selecting its smallest root in (0,1) is legitimate
and independent of all horizon and accuracy choices. Every such root
works; uniqueness and simplicity are not required.

At the passive phase, the actual forced-Quit distribution has four
outcomes: own singleton, either of the two cross-pairs, and the triple
with both opposite-phase opponents. Their rewards are all at most s_i.
Thus Quit≤s_i<W_i, because Π+1>0. This retains the simultaneous triple
outcome. No grand coalition is reachable on path or under one unilateral
deviation, so its unrestricted entries genuinely cause no omitted cap.
No inequality U_i≥s_i is used.

### Signed and positive-K falsification test

Take

    H=9/4, Π=−1/2, K=1, t=q=1/2,
    s=(−3,2,−1,4), b=(1,2,3,4),

and set all twelve capped entries exactly equal to the relevant s_i.
The polynomial vanishes exactly. The derived values are

    U=(−13/4,3/2,−7/4,3),
    W=(−5/2,3,1/2,6).

Every passive Quit endpoint is exactly s_i and strictly below W_i;
every active pair of action endpoints equals U_i. Thus signed own
levels, negative Π above −1, and positive K work simultaneously. This
test falsifies neither the theorem nor its consumer, and shows why
silently imposing nonnegative values or all-phase singleton floors would
unnecessarily weaken the statement.

## Unrestricted deviations and the literal finite-horizon contract

Joint survival over a period is t⁴. The affine policy recursion therefore
has a unique bounded solution, equal to the actual terminal value, from
either initial phase. Removing any one player leaves exactly three
opponent hazard occurrences per period, so opponent survival is t³<1.

At every live date, both endpoints of any unilateral mixed action are
bounded by the current certificate value when followed by the next
certificate value. Iterating over any behavioral deviation gives a
bounded residual times at most t^(3n). Its limit is zero. This argument
does not restrict the deviator to a stopping date, a memory bound, or the
two prescribed hazards; it includes Never. Before absorption there is
only the all-Continue public history, and any additional private
randomization is absorbed into the conditional unilateral action.

The terminal-to-N-date payoff estimate is valid with the actual initial
live reward zero. Writing M=max|r_i(S)| and B=1+2/(1−t³), the first
opponent Quit has expectation at most B under every unilateral
deviation. Therefore each expected payoff changes by at most 2MB/N
between terminal evaluation and the N-date average, and the deviation
gain is at most 4MB/N. The same one profile and the same initial target
work for all accuracies. No finite-horizon payoff is asserted to equal
the terminal target exactly.

The exact declarations inspected in
`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean` are
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`.
Their premises are precisely the policy recursion, local exact Nash,
and playerwise opponent contraction supplied above. The ordinary proof
does not infer existence from an uninhabited certificate interface.

## Matrix and source checks

For the normalized matrix Γ with zero diagonal, favorable entries H,
and all other off-diagonal entries −1, independent diagonalization gives
eigenvalues H−2,H+2,−H,−H and determinant H²(H²−4)>0. Its inverse
has the displayed positive entries

    2/[H(H²−4)], (H²−2)/[H(H²−4)], 1/(H²−4).

Positive row scales preserve inverse positivity and determinant sign.
The negative determinant hypothesis of
`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse` in
`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`
therefore fails, despite the strictly positive inverse.

All principal matrices of size at least two are nonsingular, with pair
determinants −H² or −1 and triple determinant 2H. A nonzero homogeneous
LCP support of size at least two would contradict that nonsingularity;
a singleton support fails because its column has a negative entry.
Thus Γ is R₀. The inspected theorem
`r0Degree_eq_sign_det_of_nonnegative_inverse` in
`MathUE/LinearProgramming/NonnegativeInverseDegree.lean` gives degree +1,
not the degree exit. A harmful pair is R₀ and is not Q: at offset
(−1,−1) its residual cannot be nonnegative for a nonnegative vector.
Every triple inverse has a negative diagonal entry −1/(2H).

The unique positive predecessor map is two disjoint transpositions.
Consequently no player relabeling satisfies a four-cycle positive
predecessor pattern. Every unordered singleton pair has equal signs in
both directions, also excluding the tournament and cyclic-child sign
conditions used in the compared raw sources.

## Exact fixture, proper children, and stationary scope

I recomputed the fifteen-row fixture at H=53/8, Π=5, K=−1. Its cubic
root is t=4/5. The two continuation vectors are exactly
(2,5/2,2,5/2) and (5/2,2,5/2,2). Active endpoints equal 2; passive
Quit is 9/25 and Continue is 5/2, giving margin 107/50.

The premium traps are exactly 02,13,I. Each active-pair participant has
a positive pair premium; the other players in any proper triple have no
positive participant premium inside that triple. The grand row neither
creates another proper trap nor removes the full one. Thus the greatest
premium core is full. The displayed pure-exit failures are correct,
including a strict joining gain 1 by an active-pair outsider and a
strict leave gain at every triple and at the grand coalition.

The proper-child argument exhausts all fourteen nonempty proper
children. A child cutting an active pair admits the pure solo exit of
an inside member whose active mate is outside. The other inside players
strictly prefer waiting to joining that solo exit; the quitter cannot
gain by delay or Never. The omitted mate gains 6. The only remaining
children are 02 and 13, whose pure joint exit is a child Nash profile
and gives an omitted player joining gain 1. The child debts and joint
Never are exactly zero. This disproves, for each child and some omitted
player, a universal finite weighted-child-debt-plus-Never bound. It does
not assert that every child equilibrium is bad for lifting.

The proper three-active stationary calculation also checks. For support
012 and proper hazards (a,x,c), player2's zero Never payoff forces
1+5a−2x−14ax=0 and hence 3/8<x<1/2. Player0 then has

    Q₀=(14x−5)(a−c),
    N₀=(61/8)x(1−c)/(x+c−xc).

If Q₀=N₀, then c<a<1, so Q₀<(14x−5)(1−c), whereas
N₀≥(61/8)x(1−c) and (61/8)x>14x−5. The Klein symmetries of
all rows of size at most three cover every deleted player. This excludes
the proper-three-active branch of
`PairedCubicStationaryExample.exists_local_stationary_branch` in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`.
It does not exclude full-support stationary equilibria, sure-hazard
stationary boundaries, or arbitrary stationary certificates.

## Remaining bounded coverage comparisons

The fixture escapes the named current raw classes for concrete reasons:

- Product-low fails at either sure active pair. Full core excludes
  core-at-most-two, signed-pair, and both triple-core premises. The
  negative grand premium of every player leaves no protected player and
  violates every nonzero nonnegative weighted-floor vector.
- Pair traps violate the boxed larger-trap hypothesis. For the mixed
  pair/larger-trap producer the full trap has P_I({j})=1, which fails
  its strict negative singleton-column inequality. The newer signed-pair
  and boxed neighborhood routes do not repair these failures.
- At the all-sure vector the four displacements are −11,−12,−13,−14.
  This excludes every nondiscrete response-invariant partition. The
  inspected definition is `QuittingResponseInvariantOnUnitCube` in
  `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
- The paired-cycle region allows only one below-own singleton in a row,
  by `RawRegion.eq_partner_of_singleton_lt` in
  `UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`; here each
  row has two. Positive playerwise affine changes preserve that failure.
- The overlapping period-three small affine cylinder has normalized
  favorable/harmful singleton ratio below 4, while the fixture ratio is
  53/8. This comparison concerns that specified small raw cylinder, not
  all overlapping-phase strategies.
- In the certified joint/solo/solo/joint branch, the stated exact solo
  floor equalities and strict neighboring floors force Γ_ab<0<Γ_ba.
  No fixture pair has that sign pattern, under any relabeling. This is
  an intrinsic test of that branch, not a completeness theorem for all
  two-joint schedules.
- Every ordered-pair lower guard fails. If j≠f(i), the pure favorite
  outsider gives displacement −69/8; if j=f(i), the pure o(i) outsider
  gives −1. Both satisfy the closed-square outsider-face hypotheses of
  `QuittingHalfWeakPolynomialGuards` in
  `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`
  and the corresponding one-sided unit guards. Thus they exclude the
  weak guards as well as their strict raw and guard-derived neighborhood
  specializations; affine transports preserve the negative witnesses.
- The literal `sharpReward` family in
  `UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskyStationaryClosure.lean`
  always has Γ_03=0, while the fixture has no zero off-diagonal entry.
  The inspected source does not provide a full-reward neighborhood.

A further exact strengthening of the response-partition comparison is
available without changing the theorem. It survives arbitrary positive
playerwise affine changes. Indeed the inspected declaration
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`
forces, after summing column blocks, equal complete singleton row sums
within each receiver block. The normalized fixture has common nonzero
row sum H−2. Therefore the positive row scales must be equal within each
block. The distinct all-sure displacements then remain distinct within
that block, a contradiction. Row translations cancel from both tests.

These are genuine strict comparisons with the specified accepted raw
criteria. They do not assert exclusion from every conceivable supplied
certificate, every stationary equilibrium, or a concurrently proposed
stronger matching theorem. The raw-to-unrestricted-UE construction is
complete independently of that future overlap question.
