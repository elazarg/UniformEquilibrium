# Independent whole-proof review of the M14 uniform-equilibrium producer

Reviewer: HEAD_CLOSURE_28. Verdict: PASS, including export admission, for the
complete frozen manuscript and checker identified below. No mathematical
objection remains. This is an independent ordinary-mathematical review, not a
Lean verification or a claim to have solved arbitrary Fin4.

Reviewed the complete 619-line manuscript
`math/exports/M14_QUITTING_GAME_UNIFORM_EQUILIBRIUM.md`, SHA256
`bfcdc6f7d701f739fc86f7aa4e7e66441cf72fcbdbea6130c1242fa30a55bf0f`,
and the complete standalone program `math/experiments/M14_UNIFORM_EQUILIBRIUM_CHECK.py`, SHA256
`94390ab21c09ae25ccc0751d277d02df25b63482841e2099a6dbbbeb1efde5b4`.
I verified that its inline reproduction is byte-identical to the standalone
program. I independently ran the default complete ten-tile program; it
finished with exit code zero and passed every prefix, finite-root, quiet-pivot,
cone, and return inclusion assertion. The aggregate returned enclosure lies
inside (0.8495,0.8602), strictly inside the asserted interval [0.8,0.9].

## Claim and scope

The raw data specify every one of the 60 native absorbing rewards. The
original rewards are 4 plus these native rewards, while live play and Never
remain zero. The result constructs actual finite independent private-hazard
profiles followed by Never, with vanishing unrestricted terminal debt and
vanishing joint Never probability. Native augmented closure therefore has an
absorbing full-Nash point, and the pivot-2 absorbing observer-feasible minimum
has debt zero. For the original game a fixed uniform payoff is
4 times the all-one vector plus b_* e2, with b_* in [4/5,9/10].

The constructed actual profiles are approximate equilibria. The absorbing
native full-Nash object is a point of the augmented closure; the proof does
not assert that it is an actual absorbing exact Nash strategy. No strategic
witness, actual positive-gap minimum, or equilibrium continuation is assumed.

## Finite proxy calculus and the infinite-prefix limits

I derived the displayed C, P and Q formulas directly from the coalition
table, including every pair and triple term in the quiet pivot's comparison.
The payoff recursion has continuation coefficient c, the joint survival;
the response recursion has coefficient H_i, the opponent survival. A diagonal
annotation maps to a diagonal annotation exactly under the displayed root
Nash comparisons. The maps are separately nonexpansive in payoff and cap.

The compact carrier H_v is defined from finite proxy words with one fixed
seed. It is invariant under each fixed finite prefix, by continuity and
finite-word approximation. Thus its diagonal limits may be used as inputs
to further prefixes without assuming that an infinite phase finishes at a
finite date. This is the central justification of all phase switches. The
final result is approximated by actual finite words from the original seed;
no execution after infinitely many dates occurs.

I checked all three singleton phases. Their active coordinates remain zero;
the positive target coordinate follows 13z/(14+z) and decreases to zero.
The quiet comparisons hold throughout, and the affine survival identities
give exactly the three displayed endpoints and total survival 1/(1+6b).
At the eight owner-1 atoms, the first quiet-3 inequality is positive by
(4/5)^6 < 9/28; later quiet-0 comparisons are tied, and quiet-3 slack is
(9/2+5c0)(a_*-a). The seventh atom reaches a_*, and the eighth is admissible
with both quiet-0 and quiet-3 tied. The pivot comparison remains safe.
The resulting vector is b/(18+133b) times (-25,0,104,65), with survival
18/(18+133b) at most 45/311. Negative intermediate observer values cause
no omitted constraint: the stated inequalities price those comparisons.

## Exact finite and infinite return certificate

I audited every interval operation and the entire root transport. Outward
80-bit dyadic rounding encloses the exact rational operations. Floating
point computations nominate centers and preconditioners only. For every cap
in the extended input box, the interval residual and derivative tests prove
a strict contraction and self-map of the root box. Its root is positive and
proper. Failure of a nomination or inclusion cannot constitute acceptance.

The inverse bound follows from the Neumann series for I-B DC. Its column
error bound uses the maximum absolute entry of that column of B and the
row-sum bound kappa/(1-kappa), as required. The code extends the transformed
input box to contain the verified cap C(x_c), so the entire segment used in
the mean-value argument lies in a domain with the same verified inverse.
The output is transported from Q(x_c), not from an unverified midpoint
root. The uniqueness and invertibility provide the needed local gluing.

The pivot transport uses both the cap-coordinate derivative and the direct
beta derivative H. Its mean-value segments lie in the same extended cap
box and the complete beta interval. Correlations are discarded only in the
outward direction. Every one of the 305 roots on each of the ten closed
input tiles satisfies beta > C2(x). Their union covers the whole input
interval; no point sampling substitutes for the uniform certificate.

The final odds box corresponds to the last root, whose Q output is the
input to the analytic next root. I checked this indexing explicitly.
The analytic cone uses the exact matrix L0^{-1}J0. The fixed-point box
Bx +/- 12t^2 is invariant because (69/379)(42+20)<12, and its contraction
constant is at most (69/379)20t. All four corner inequalities cover the full
ratio rectangle, including its boundary; they yield positivity, the same
cone, and y1 < 0.99t. The pivot increment is at most (32/5)y1 since the
absolute singleton contribution is at most 3.7y1 and the survival loss is
at most 2.7y1 while |beta|<=1. Hence total subsequent drift is at most 640t.
The certified endpoint margin bootstraps beta inside [0.8,0.9], rather than
assuming this interval throughout. The quiet pivot comparison then follows
uniformly from C2(y)<=14y3<0.7. Thus the observer values converge to zero and
the pivot value converges to one fixed returned b' in the required interval.

## Actualization, fixed target, and unrestricted deviations

For a fixed return orbit, words are selected at their ideal diagonal inputs
and prepended in reverse orbit order. Nonexpansiveness gives the complete
K eta payoff/cap error, including all finite approximations at switches.
Joint survival is at most (theta+eta)^K. This does not require a continuous
return selector or a return fixed point.

I explicitly attempted to falsify the terminal replacement step by separating
joint survival from each opponent's survival. The proof is valid: in the
original game the true postword payoff is zero and full postword cap is four,
whereas the proxy terminal vector 4*1+b0 e2 majorizes that cap. Cap monotonicity
therefore bounds the actual cap with no opponent-survival contraction claim.
Only the prescribed payoff incurs c_total times the terminal vector. This
gives the displayed 2K eta + 4.9(theta+eta)^K debt bound. The corresponding
native tail has both payoff and full cap zero, giving the separate native
bound and the actual absorbing zero-debt limit.

The compactness selection uses one fixed orbit and a subsequence of its
actual profiles. It produces b_* before any requested accuracy. It does not
choose a different target for each accuracy. All deviations are behavioral:
on the unique live history they induce a first-Quit date or Never, and the
full cap recursion prices every such response and its mixtures.

I also checked the direct finite-horizon proof, including negative absorbing
rewards. Prescribed absorption occurs by T or Never, so its terminal/average
error is at most 17(T+1)/H. After T, with all opponents prescribed Never,
a deviator can obtain only the positive own-singleton reward four or zero.
Delaying that payment cannot increase finite averages above terminal payoff.
Thus the all-behavior gain bound is debt+34(T+1)/H. One chosen profile works
for every sufficiently large horizon with the already fixed target.

## Sources, coverage, and admission

I inspected the exact statements of
`quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash` and
`quittingTerminalSemanticPair_rootThenContinuation` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`,
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`, and
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The stopping-law payoff/cap correspondences in
`UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`
match the same unrestricted behavior semantics. The cited files are tracked.
These supply the existing semantics and consumer, not the new producer.

I assessed admission against `math/exports/README.md` and the maintained M14
benchmark coverage audit. The raw table is the same prior surviving M14
table, not a change to an already solved M10 control. Its singleton upper
tests sum to 3 sum(w)>0 for every nonzero nonnegative weight, and its singleton
boxed charge is three. Its joining tests sum to
3w0+2w1+w2+2w3>0. Anchor predecessor closure forces the entire four-cycle
into one block, where multiplying pair caps would require 13^4<=5^4.
Every candidate pair has an endpoint with joining increment at most -4.
The inverse/opposition and protected-row requirements fail as recorded in
the benchmark, and the sole possible scalar-circuit ordering has a negative
required denominator. These are complete selection-set obstructions for
the applicable raw criteria, not merely tests at selected witnesses.

The independent stationary certificate is not used to reject nonstationary
punishment-tail consumers. Nor do the failures of these finite raw criteria
assert impossibility of their broader architectures. No accepted existence
packet added since the benchmark audit covers this table; the subsequent
M14 exports were necessary reductions of hypothetical positive-gap sources.
In particular the finite-head/native-tail and inherited branches remained
unresolved. Here equation (15) unconditionally eliminates the entire named
M14 positive absorbing-gap obligation, while (14) directly proves original
UE. This is a concrete new exclusion, not another conditional interface or
a stronger profile claim on a table already covered by the cited criteria.

All strategic inputs are produced: the diagonal seed is an explicit proxy,
the singleton limits and eight atoms are proved from raw entries, every
observer root is uniformly validated, the return is closed by the analytic
cone, all finite words follow from the specified closure, and all-error
profiles and a fixed target are constructed by the consumer. There are no
remaining unproduced strategic hypotheses and no need for the conditional
export exception. The packet contains the full mathematical checker and
does not depend on a temporary source or external root table. Its handoff
retains the synthetic seed and phase approximation instead of assuming
actual continuation or return witnesses as fields.

I affirm export admission for this complete M14 theorem at the pinned bytes.
The result supersedes narrower M14 positive-gap case exclusions as a research
frontier statement. It does not solve arbitrary reward tables on four players,
prove a neighborhood theorem, or supply a new Lean seal.
