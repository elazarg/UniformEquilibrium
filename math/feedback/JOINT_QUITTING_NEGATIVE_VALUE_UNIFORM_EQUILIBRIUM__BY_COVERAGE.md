# Independent coverage and source review of the joint-return theorem

Reviewer: JOINT_COVERAGE. Ordinary mathematics; no Lean build or new Lean
verification is asserted. No tracked files or git state were changed.

Reviewed artifact: `math/exports/JOINT_QUITTING_NEGATIVE_VALUE_UNIFORM_EQUILIBRIUM.md`, SHA256
`c39fc225b49d09609329364b515ff1a7ba816acf1e72d1a47d6265f961e1f772`.

Verdict: PASS for Section6 in full, its separation claims in Section1,
and the source/production scope in Section7. No unresolved coverage,
raw-selector, source-reference, or mathematical reproduction objection
remains in this scope. Sections1–5's complete existence proof and finite
interval certificate require their separate mathematical review; this
review does not substitute for that review.

## 1. Exact claims and narrowing of the frontier

The packet is an actual reward-data producer. Its class is specified by a
cubic simple-root test and finite rational inequalities on the reward table.
No strategy, continuation payoff, actual tail, favorable Nash selection,
return certificate or vanishing-error family appears among its inputs.
The integer core length, core hazards, finite prefix, wash and closing arc
are constructed in the proof. The quantified threshold is uniform in p
through K>=M(1+|p|); it is not a claim at a guessed numerical threshold.
The separate K1000,eta1/100 rational certificate supplies one fully explicit
original table independently of the asymptotic threshold. The concrete
claim and its sixty-coordinate neighborhood are distinct from the larger
raw family, as the packet states.

For its complete displayed table at original own levels1, K>=1000 and
0<eta<=1/100, the closest earlier singleton-split producer fails strictly:
its required Z2(02)<=Gamma20 is violated by eta>0, and its complete eight-
sign singleton labeling is uniquely the identity. The independently checked
raw seed with rational eta inside this interval yields an intersection of
the new asymptotic class and the audited previously surviving region for
p=0 and all sufficiently large K. The concrete finite certificate removes
any reliance on that unspecified threshold at K1000,eta1/100.
Thus this is new UE coverage, not merely an exact-profile improvement on
a class already supplied by the compared raw producers. Arbitrary Fin4 is
explicitly left open.

The initial phrase about sure roots was clarified during review. The final
bytes correctly concern full-response Nash roots with actual continuation
best-response caps. An arbitrary actual continuation payoff can be below
the pure-Never cap; the proof does not exclude a one-step Nash root based
only on such a low payoff annotation. The final statement respects this
distinction.

## 2. Independent polynomial reconstruction and the full census

I reconstructed Q,P,H from all15 columns of the printed native table, with
Z2(02)=2+t/100 and t ranging over[0,1]. All entries match the stated family,
including Z0(02)=-1/10, Z3(02)=-219/29, the row0 values -20 on
012,03,013,023, and the row2 values -100 on012,023,0123.
The passive-Never lower cap is exactly(-12,-8,-10,-12).
The only eta term is

    (t/100)q0(1-q1)(1-q3)

in Q2; it contributes that term to G2 and(1-H2) times it to F2.
The two K-variation formulas in the packet are exact. Their coefficient
is nonnegative throughout the cube, so replacing a mixed/sure row1 by
baseline>=0 and omitting a quiet row1 gives valid weaker necessary systems.
Where q2=0, q0=1 or q3=1 the coefficient vanishes and the baseline sign is
retained exactly.

The direct q0=0, mixed2 exclusion is valid: Q2=q3(3-q1)>=0 and
P2=-2q1-q3+2q1q3<0. The single-mixed-owner shortcut correctly uses
Gamma_ij<min(0,Z_i(ij)); its four quiet recipients are3,2,0,2, none the
possibly omitted row1. These statements apply to every point in the
corresponding support pattern rather than to a chosen root.

I reproduced both implementations: a direct Fraction polynomial checker,
and a separately built symbolic reward table with independent exact
Bernstein conversion and traversal. Both terminate with exactly

    700 nodes over all80 nonzero stationary patterns;
    205 nodes over all65 sure-root patterns.

No pattern or unresolved box is discarded without a mathematical reason.
The reconstruction uses the complete t interval, not an eta sample. It
also proves the asserted eta=0 endpoint for this census.

All eight origin constants in Section6 were reproduced exactly:

| Mixed set | D | E |
|---|---:|---:|
|01|1/2|1|
|02|201/200|1|
|03|20/3|3|
|13|100/3|6|
|012|137092/25|13|
|013|1695|11|
|023|6853381/7250|10|
|0123|788325063/25375|15|

Every remainder monomial has player degree at least2; the t degree is not
counted toward this bound. The relaxed inverse columns are nonnegative
where used, so q<=VR has the claimed direction. Each listed2^-E is strictly
smaller than1/D. Thus the origin cubes exclude every nonzero solution,
including arbitrarily small hazards, uniformly in the entire parameter
interval. The t coordinate is not wrongly shrunk with the player origin
cube.

The tensor Bernstein formula, positive denominator clearing, strict sign
rejection, and integer-scaled subdivision rule are correct. Choosing the
least-subdivided player axis with player-order ties and left-first traversal
reproduces the stated counts. If no player is mixed, subdivision of t
preserves all its values. The packet supplies the table, polynomial formulas,
origin constants and exact algorithm, so the calculation is self-contained;
the temporary reproduction programs are not proof dependencies.

The sure-root system uses genuine full caps: pure Never gives its lower
bound, and only a unique sure owner's Continue branch has nonzero H.
The substituted lower cap weakens that owner's necessary Quit comparison.
All other H coordinates are zero. This covers the complete sure-first
punishment selection set, not only stationary continuation tails.

## 3. Stationary approximate limits and output-class comparisons

The compactness argument is valid. A nonzero limiting stationary hazard
profile satisfies the excluded exact sign conditions. If hazards tend to
zero, normalize by their sum. Immediate quitting gives Gamma x>=0.
A singleton normalized support violates this by the negative entry in every
column. Otherwise, for every positive normalized own weight, the Never
comparison gives complementarity x_i(Gamma x)_i=0. Every principal matrix
of size at least2 is nonsingular, so there is no normalized solution.
This proves a positive stationary regret floor for each fixed table; it
claims neither a uniform floor over K nor a full-strategy positive gap.

Hence all stationary-output producers are excluded regardless of their
choice of root, weight, bonus, child or asymptotic selector. This includes
the relevant weighted-collision producer. The sure-root census separately
excludes sure-first producers with arbitrary actual continuation caps.
The result leaves general nonstationary strategies available, as required
by the new construction.

## 4. All finite and weighted raw choices in the other comparisons

I independently enumerated the24 singleton labelings. Exactly identity
satisfies the eight-sign outer template; the displayed previous B1=-1/9
and Gamma10=2 failures therefore cannot be repaired by relabeling.
Positive recipient scales preserve their signs and the new positive eta
joining excess. The fixed signed/premium templates fail their required
Gamma12 value after the stated row normalization.

The three weight obstructions hold for EVERY nonnegative weight:

    H12+H1 has coefficients(-9,-K,-2,-8);
    4H2+H1-3J02 has coefficients(-1,-1,-2,2-2619/58);
    k(01)+k(2)=(-1/10,-K-1,-100,-110).

Every vector is strictly negative at the specified parameters. Thus no
number of candidate weights, support filters, or orientation choices can
repair those necessary premises. The last vector also defeats the global
inserted-reward floor needed by weighted trap-leaver criteria.

The pair and triple selector failures were checked against the literal
premises: the unique positive reciprocal pair01 and negative pair13
intersect; no signed Hamiltonian adjacent cycle exists. Each perfect
matching fails a mandatory joining increment. Each triple contains one
of these strict failures. The attached-negative-pair labeling is unique,
and its broader arbitrary-premium variant fails the unused singleton sign.

The principal determinants and full inverse match direct exact inversion.
Only child023 has nonnegative inverse, and its exterior row
(-7/10,9/10,-1/5) fails the passive-child test. The full inverse mixed
column defeats nonnegative or all-positive signed-column criteria.
Every incoming pivot column for the raw cyclic-child templates fails its
required allnegative sign; for the sole inverse-positive child it is
(3,-2,-2).

The premium assertions are literal:123 is a trap with participant vector
(11,2,1), nobody is protected, and the greatest premium core is exactly123.
The joining-attractive premise fails at owner1 joining singleton2. The
three full-triple joining gaps(2,3,7) defeat the weak mixed-sign triple
criterion's two zero equalities under all six orderings. They also defeat
the applicable boxed/mixed-trap charge conditions; the allpositive123
participant vector excludes supportwise balance, product-low and
support-local upper-average weights. Strong connectivity of the positive
singleton graph makes a nonempty predecessor-closed marked set full;
the positive123 trap then excludes every ordered marked-block partition.
For the calendar-polytope theorem with exactly two marked owners, every
such marked set intersects123 and already fails its participant cap.
The scalar circuit requires three distinct recipients with positive pair
premiums at negative singleton mates, and only owners2,3 qualify.

No additional covering raw producer was found in the relevant sign,
matching, inverse, trap, marked, stationary or cyclic-child families.
The packet deliberately excludes claims about unknown maximal neighborhoods
of earlier local theorems, and does not claim a census of every conceivable
nonstationary supplied-object verifier. That scope is appropriate.

## 5. All fourteen children and all five withdrawal operations

The relaxed F/J inequalities match the actual source definitions. For
patient, deadline, evaluated-security, terminal-security and cancellation,
the own-singleton withdrawal gain is at most0 when own reward is1. Patient
floor is at most max(1,0)=1; terminal-security floor is at most own singleton1;
the other relevant floors are nonpositive. On non-singleton coalitions the
withdrawal gain is exactly Z_i(A-i)-Z_i(A) for members and0 for nonmembers.
The future coefficient is either this gain or0. Replacing it by max(W,0),
and singleton gain by0, therefore enlarges all five feasible sets.

I independently reconstructed every one of the14 printed row combinations
from the table with symbolic K and eta. All positive left sides match.
The three longer coefficient checks are exactly

    child012: advance(0,56-10K,0), withdrawal(-603/10,0,-67eta),
              left433/58;
    child023: advance(-5,0,0), withdrawal(0,0,0), left7/2;
    child123: advance(0,0,0), withdrawal(-2,-3,-7), left3.

Every other coefficient is directly nonpositive; the singleton and01
witnesses with left eta are strictly contradictory precisely when eta>0.
Thus all14 children and every nonnegative weight choice fail, even with
the Never row omitted. Advancing-only capped clocks are contained by
setting the withdrawal weights to zero. This is stronger than exhibiting
one unsafe equilibrium per child and meets the complete-selection gate.
An arbitrary child-specific strategic lift is correctly left outside the
claim.

## 6. Source references and formalization scope

All cited source files are tracked. I checked the actual declarations and
hypotheses used, including:

- `HasWeakJoiningAttractivePremiumCore` in
  `UniformEquilibrium/Quitting/Classification/JoiningAttractiveCorePassivePerturbation.lean`;
- `HasWeakMixedSignTripleJoining` in
  `UniformEquilibrium/Quitting/Classification/MixedSignTripleCorePassivePerturbation.lean`;
- `WithdrawalFutureJoinKind.gain`, `.futureWeight`,
  `WithdrawalFutureJoinRewardCertificate.future_row` and `.join_row` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`;
- the four `rawChild_future_*` and `rawChild_joining_*` identities in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockOriginalCoalitionRows.lean`;
- `patientWithdrawalFloor_le_ownNeverAlternative` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/PatientWithdrawalRaw.lean`;
- `deadlineWithdrawalSecurityValue_le_singleton` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/DeadlineWithdrawalSecurityLP.lean`;
- the cited passive-triple inverse, full nonnegative-inverse, and
  supportwise-premium definitions and consumers;
- `quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
  `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`;
- `quittingGame_fixedProfile_uniformPayoffWitnesses_of_terminalNash_exact` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

The last declaration takes an exact terminal Nash profile and delivers the
same profile and actual terminal payoff at every positive uniform accuracy,
matching Section7. No checked raw producer is falsely attributed to it.
The native row shifts are justified through opponents-only absorption,
not through a same-table AllNever affine-invariance claim. The literal
period avoids the singleton-floor and silent-padding premise that the
negative annotation would violate. The packet explicitly distinguishes
ordinary mathematics from Lean verification and makes no arbitrary-Fin4
claim.
