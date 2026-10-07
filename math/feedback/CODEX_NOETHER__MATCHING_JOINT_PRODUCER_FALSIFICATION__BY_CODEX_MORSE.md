# Independent review of the finite coarse Nash-regret producer

Identity: CODEX_MORSE.

Current scope correction: the mathematical construction and exact
same-profile/every-horizon assertions PASS, but the claimed additional UE
counterexample-class coverage FAILS. Section 9 proves that the entire raw
CCE class, not just its fixture, is already consumed by the tracked
persistent-base punishment-tail source. The earlier significance statements
below are superseded by that exact inclusion. This packet is not eligible
as new UE-class narrowing on the evidence checked here.

Verdict: **PASS**, as ordinary mathematics, on the following frozen surface of
`../notes/CODEX_NOETHER__MATCHING_JOINT_PRODUCER_FALSIFICATION.md`:

- “A global finite Nash-regret restriction on every counterexample”, stopping
  before the old “Complete LP-positive, non-monotone-anchor test table”;
- “Structural separation from all withdrawal families” through the end.

The complete notebook has 1315 lines and SHA256
`d0d2fa922c95ce004008afbcd4b0acdaca5ec084c2fff0d391964ee6b4e1a922`.
I read the stated mathematical surfaces and the needed literal source, not
another review. The intermediate old table is explicitly already covered and
is not used as evidence of additional coverage. No unresolved mathematical
objection remains in the reviewed claim. No Lean execution or Lean seal is
asserted.

## 1. Exact raw input, production, and strategic conclusion

For an arbitrary finite signed quitting table and an anchor a, the free binary
game is u_j(T)=r_j(T+a). The polytope C_a uses both unconditional pure-action
regret inequalities E R_{j,b}≥0. The empty anchor gap is min(s_a,0), and all
nonempty gaps are r_a(T+a)−r_a(T). The hypothesis is the finite raw test

    min_{ν∈C_a} Eν g_a ≥ 0.

C_a is compact and nonempty: a finite mixed Nash point exists internally,
and its independent product law belongs to C_a. Taking a minimum over this
larger correlated set is in the correct direction. The proof never plays a
correlated law and never assumes a selected mixed equilibrium as extra data.

Let p be the law of any such internally chosen free Nash point. Prescribe a
sure first-date Quit by a, free law p at that date, and Never by everyone
afterwards. For every nonanchor, the anchor's sure action preempts all later
deviation behavior; the only comparison is its first-date binary action.

For a, the exact terminal endpoints are

    V_a = p_∅ s_a + Σ_{T≠∅} p_T r_a(T+a),
    C_a = p_∅ max(s_a,0) + Σ_{T≠∅} p_T r_a(T).

After an empty first-date free coalition, all opponents really remain quiet,
including off path. Arbitrary delayed randomized stopping and Never have cap
max(s_a,0). First-date actions cannot be conditioned on the simultaneous
opponents' draws. Consequently V_a−C_a=E_p g_a≥0 proves exact terminal Nash
against every unrestricted behavioral replacement, including arbitrary
signed own rewards. There is no hidden properness or absorption assumption.

Under the literal initial-zero convention, for every N≥1 the prescribed
profile pays h_N V, where h_N=(N−1)/N. Nonanchor endpoint comparisons scale
by h_N. On the anchor's empty event every delayed payoff is at most
h_N max(s_a,0), for either sign of s_a. Thus this same profile is exact
N-horizon Nash for every positive N; its fixed target error is at most M/N.
At N=1 all stage payoffs are zero. This proves the claimed fixed uniform
target without an accuracy-dependent profile, public randomization, or
terminal-to-uniform compactness assumption.

It follows by contraposition that every no-UE table and every positive
unrestricted terminal-gap table has v_a<0 for every anchor. The resulting
negative coarse law need not be a product law or an implementable profile.
The necessary condition is not asserted sufficient for nonexistence.

## 2. Independent signed and empty-event tests

The two-player table

    r(a)=(−2,0),   r(b)=(−5,1),   r(ab)=(−4,2)

is admitted with anchor a. The anchored free player strictly chooses Quit,
so C_a consists of the nonempty atom. Nevertheless the empty gap is −2.
In the two-atom order (∅,{b}), g=(−2,1), R_{b,Q}=(−2,0), and

    g = 1 + (3/2) R_{b,Q}.

This verifies the certificate with a genuinely negative own level and
negative produced target (−4,2). Both Quit is exact against all behavior.

The exceptional empty row cannot be dropped: a one-player table with
s=−1 has g(∅)=−1 and fails the test, as it must since Never improves on
Quit. Replacing min(s,0) by s instead is wrong for positive s, when a
delayed solo Quit must be included. Neither error occurs in the frozen proof.

## 3. Exact structural fixture and its open raw class

I recomputed the literal anchored differences from all fifteen reward rows:

    A₁=−5+6q₂,  A₂=1−2q₃,  A₃=−1+2q₁.

The boundary propagation argument rules out every finite Nash point with
any coordinate 0 or 1. The unique product point is (1/2,5/6,1/2).
The eight displayed g₀, R_{1,C}, R_{2,Q} entries are correct. Subtracting
1/4+R_{1,C}+(1/2)R_{2,Q} gives exactly

    (1/4,5/4,3/4,1/4,3/4,1/4,3/4,3/4).

Independent rational averaging gives

    V=(641/3,503/12,101/4,245/6),
    C₀=5105/24,  V₀−C₀=23/24.

Thus the new fixture is not merely a numerical LP output. A finite raw dual
inequality, with no strategic inputs, certifies every coarse law and hence
the internally selected independent equilibrium.

All fourteen child rows were independently checked against the literal
table. The displayed positive child gaps and omitted joining gains are
correct, including child012's gaps (2,1,1), child123's gaps (6,6,6), and
its omitted gain 2. Nonsingleton sure sets preempt every deviation. In the
singleton rows, own reward 1 and the prescribed quiet continuation bound
all waiting policies. Thus the witnesses have zero full child debt, zero
Never mass, and strictly positive omitted gain.

This simultaneously yields the semantic universal-bound exclusion and the
claimed actual raw J-row exclusion. At each selected T, all child advance
gains are nonpositive. Nonsingleton member withdrawal gains are strictly
negative; nonmember withdrawal gains vanish. At a singleton member, the
actual patient/deadline/security/cancellation restart bounds never exceed
the positive own reward. Thus every nonnegative advance/withdrawal weighted
right side is nonpositive, whereas the omitted J left side is positive.
All five literal `WithdrawalFutureJoinKind` cases fail; this is not just
failure of a simplified future/join certificate. A specially selected safe
child equilibrium is not ruled out by these witnesses, and the note does
not claim otherwise.

In the full coordinate box |Δr|<1/40, the dual slack changes by less than
5/40=1/8, below its minimum 1/4. The empty g₀ row remains exactly zero
because the perturbed own level remains positive. Every child/omitted
comparison has margin at least 1 and changes by less than 2/40. Therefore
the full sixty-coordinate open box is admitted by the new raw producer and
excluded by every actual five-kind withdrawal family. No IFT, fixed free
hazards, or stability of the unique Nash point is being assumed.

This is substantive additional counterexample-class narrowing. The other
accepted-source exclusions below concern the exact center; the proof does
not silently claim all of them throughout that entire box.

## 4. Bounded accepted-source and matrix checks

The singleton matrix is the H=3 favorable matching matrix, with row sums 1,
positive inverse and R₀/degree-one data. These matrix properties alone are
not an unconditional equilibrium producer. I checked all three partitions
against the accepted complementary-odds criterion: 01/23 has c₀=−4,
c₁=−5; 03/12 has c₃=−1; 02/13 has positive c but r₀(013)=96>1.
The latter is one of its literal opposite participant caps. Thus the new
table is not consumed by the graph-free two-pair theorem or its stronger
matching/signed-inverse subcriteria. Positive inverse forces positive
column signs in the signed-inverse condition.

The negative-participant opposite-sign arm and all-below-singleton two-pair
outputs fail as stated. In both harmful partitions player0 has zero pair
premium and c₀=1, forcing W₀=1+X_mate>1 at positive odds. On the favorite
partition, the 23 active participants have positive premium 4. This is an
intrinsic output test, not a claim about a guessed neighborhood radius.

I checked all eleven listed cardinality-at-least-two base counterexamples
and all twelve upper unit-face witnesses. The new half-polynomial tail is
also correct: reciprocal positivity restricts its selected pair to 01 or
23. At the required upper-half faces, sure outside hazards yield literal
displacements 3/2 and 1, respectively. The displacement is an opponents-only
averaged joining difference there; a recipient's own hazard does not alter
these evaluations. This excludes the actual polynomial guards, not only a
stronger raw sufficient condition.

The weighted-premium coefficient rows successively force λ₁=λ₃=0,
then λ₂=0, then λ₀=0. The exact premium traps are
12,13,23,012,013,123,I. At the seven listed charge witnesses, the paired
L/J values are respectively

    (4,5),(4,5),(4,1),(3,1),(3,1),(8,10),(100,2).

Hence neither the weighted nor boxed/mixed-trap input is supplied. No player
is protected; the grand coalition violates product-low. The conditional
range, sign-changing influence, terminal-weight and positive-affine
response-partition calculations also check. In particular the all-sure
response vector (2,1,−1,1) leaves only {1,3} as a possible nonsingleton
block after the singleton row-sum scaling necessity, and singleton0 rules
out that final block. This exhausts fourteen nondiscrete partitions.

## 5. Transient versus stationary falsification

Repeating the selected anchor0 free row gives Never₀=5104/23 and
Quit₀=641/3; its gain from Never is 569/69. Thus the one-shot prescription
is essential and is not covertly a stationary-anchor argument.

I checked the complete sure-coordinate census, including partly mixed
boundaries. Sure1 forces sure3, then its only free completion has
(q₀,q₂)=(6/7,2/3), giving sure1 gap −1/21. Sure2 forces 1, then 0 and
3, and the grand coalition fails player2. With sure3, the three displayed
free gaps give exactly the stated boundary contradictions; an all-proper
completion would force q₁q₂=1. Its only finite completion is free
(q₀,q₁,q₂)=(1,0,0), where sure3 loses 1. No sure-quitter stationary
equilibrium exists. This is not absence of all-proper stationary equilibria.

The nearby one-date source with every free hazard in (1/4,3/4) cannot output
the center: anchor0 requires 5/6, anchors1 and2 force another sure player,
and anchor3 has no proper completion. This does not purport to classify all
possible proper-three local equilibrium producers.

## 6. Literal source correspondence and scope

The definitions and declarations inspected include:

- `quittingPersistentBaseUtility`, `quittingPersistentBaseNashSet` and
  `quittingPersistentBaseNashSet_nonempty` in
  `UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean`;
- `quittingOneDateThenNeverProfile` and its debt machinery in
  `UniformEquilibrium/Quitting/Root/OneDateNeverNashDebt.lean`, and
  `quittingOneDateThenNeverProfile_exactHorizonNash` and
  `quittingOneDateThenNeverProfile_sameProfile_uniformPayoffWitness` in
  `UniformEquilibrium/Quitting/Root/OneDateNeverHorizonNash.lean`;
- `WithdrawalFutureJoinRewardCertificate.join_row`,
  `WithdrawalFutureJoinKind.gain`, and the actual restart-floor definitions
  in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`,
  `PatientWithdrawalRaw.lean`, `DeadlineWithdrawalRaw.lean`, and
  `DeadlineWithdrawalSecurityLP.lean`; the universal consumer
  `withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
  `WithdrawalFutureJoinDebt.lean`;
- `QuittingHalfWeakPolynomialGuards.reciprocal_pos` in
  `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`
  and `exists_stationary_terminalApproximation_of_weakHalfPolynomialGuards`
  in `GuardedCrossedResponseWeakPolynomialProducer.lean`;
- the pointwise singleton-anchor source in
  `UniformEquilibrium/Quitting/Stationary/SingleAnchorArbitraryCompletion.lean`.

The finite Nash theorem supplies a finite product point, not the anchor's
original-game stability. The one-date consumer assumes exact terminal Nash;
it does not supply the raw CCE implication. That implication and the exact
raw separator are the additional ordinary mathematical content. No absent
strategic adapter, all-player approximate-law premise, or matrix-only
equilibrium assumption was smuggled into the proof.

## 7. Separate arbitrary-base delta

The separate 159-line note
`../notes/CODEX_NOETHER__GLOBAL_CCE_BASE_RESTRICTIONS.md`, SHA256
`5923af318a25d8891b7dda45e7c043985361f795d5eb544935272051b3e8e601`,
also receives **PASS** for its stated extension. This is a separate check,
not a change to the frozen singleton surface above.

For every nonempty E, let C_E be the free game's coarse Nash polytope and
G_i^E the actual member withdrawal gap. If all member minima over C_E are
nonnegative, one internally produced free product Nash point satisfies all
member inequalities simultaneously. There is no need to choose separate
Nash points or correlated laws for different members. For |E|≥2 every
unilateral replacement retains a sure opponent, so all deviations absorb
at the first transition and reduce to the two first-date endpoints. For
|E|=1 the complete waiting cap already audited applies. Empty free sets,
arbitrary signed rewards, exact every-positive-horizon Nash and a single
target with M/N delivery are covered. Stationary repetition is valid only
in the |E|≥2 branch, as correctly stated.

The contrapositive has the exact quantifiers

    every nonempty E has some i∈E and some ν∈C_E with Eν G_i^E<0.

Neither i nor ν must be common to different bases; negative laws for
different members need not coincide. For a concrete stress, take three
players, E=01, all third-coordinate rewards zero, and

    r0=(1,2,0), r1=(0,1,0), r2=(0,0,0),
    r01=(1,1,0), r02=(1,0,0), r12=(2,1,0), r012=(1,1,0).

The free game is indifferent, so C_E is the entire two-atom simplex.
G₀=(1,−1), G₁=(−1,1): both separate minima are −1, but no law makes
both expectations strictly negative. The uniform free law is an actual
exact base equilibrium. This confirms why neither a common-negative-law
assertion nor sufficiency of negative minima is licensed.

One explanatory sign sentence in the first base draft was corrected during
this independent check: replacing min(s,0) by s is wrong for positive s
(delayed Quit), whereas replacing it by 0 is wrong for negative s (Never).
The definitions and proof were already correct. The hash above binds the
repaired explanation; no mathematical objection remains. The base delta
can strengthen the same packet's necessary condition, without claiming an
additional source-separating base fixture beyond the singleton open class.

## 8. Final standalone assembly check

Verdict: **PASS** on the complete 587-line standalone
`../notes/CODEX_NOETHER__COARSE_REGRET_BASE_UNIFORM_EQUILIBRIUM.md`, SHA256
`e9cd2f52ceb8a70dd8ba7c51110fc0d07296513ae1710bb89c1389cde88a0a90`.
This is a bounded assembly/delta check against Sections 1–7 above. I read
the entire artifact, without reading another review. No repair or unresolved
mathematical objection remains; this is not a new Lean-check assertion.

The assembly retains the exact all-sign arbitrary-base raw criterion,
separate member minima over one free coarse polytope, internally selected
independent finite Nash law, unrestricted behavioral comparisons, the
singleton empty-event cap, and the initial-zero horizon convention. All
members' nonnegative minima control the same produced product law. Its
counterexample quantifiers and the restriction of stationary repetition to
bases of cardinality at least two remain correct.

The added explicit definitions of Γ, Π, c, stationary displacement and
the L/J charge sums reproduce the reviewed literal calculations. The
displayed matrix inverse and determinant are correct. The added two-member
empty-free signed example has both member gaps 2 and target (−2,−2);
the signed singleton and no-common-negative-law tests also remain exact.
The coefficient 6 in the membership-gain interaction is the difference
between the influence values −5 and +1, as required by its raw exclusion.

The complete fixture, all fourteen child rows, the actual five-kind J
contradiction, and the full sixty-coordinate 1/40 open box remain intact.
The assembly explicitly limits other source exclusions to the center;
neither arbitrary proper-stationary nonexistence nor exclusion of an
unspecified nearby-equilibrium radius has been introduced. The exact
sure-stationary census still distinguishes the one-shot profile from its
profitable-to-deviate stationary repetition.

The packet is self-contained for its unformalized mathematics and gives
tracked source paths for the finite Nash construction and existing
terminal-to-horizon consumers. It contains no dependency on another
conference note, review, or untracked reproduction input. The strategic
premise is produced from finite reward inequalities; the handoff does not
store an assumed profile or continuation certificate. The significant
conjecture-facing increment remains the raw CCE-positive/withdrawal-negative
open class and the necessary negative-member regret condition at every
nonempty base, not the supporting root census alone.

## 9. Decisive whole-class inclusion in the existing persistent-base source

This corrects the coverage verdict, not the terminal or finite-horizon proof.
The narrow additional source inspection was:

- `quittingSingletonBaseOwnerFloorExcess`,
  `quittingSingletonBaseExcess_nonpos_iff`,
  `nonempty_quittingSingletonBaseCertificate_of_inducedNash`,
  `exists_uniformPayoff_or_singletonBase_pos_gap`,
  `quittingPersistentLargeBaseComponent`,
  `quittingPersistentLargeBaseExcess_nonpos_iff`, and
  `exists_uniformPayoff_or_persistentLargeBase_pos_gap` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`;
- `QuittingSingletonBaseCertificate.exists_terminalNash_fixedTarget` and
  `QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingletonBaseSemanticDispatch.lean`;
- `exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`;
- `quittingPunishmentValue_le_max_solo` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`.

All are literal source statements under their imports; no build was run.
In particular the singleton continuation is priced at the exact punishment
value P_a, not at the stationary Never value of the displayed first row.
The compiler realizes a near-minmax off-path tail and already proves a
fixed-target all-behavior UE. A stationary repetition counterexample does
not exclude this consumer.

### Singleton bases, including either sign of the own reward

Take free=I\{a}; there are no remaining outside players. Internally choose
any point of the nonempty induced mixed Nash set, and let p be its product
law. Write g for the candidate's singleton gap, with g(∅)=min(s_a,0).
Direct expansion of the source's owner floor excess gives

    floorExcess(p)
      = Σ_{T≠∅}p_T r_a(T) + p_∅ P_a
          − [Σ_{T≠∅}p_T r_a(T+a)+p_∅ s_a]
      = −E_p g + p_∅[P_a−max(s_a,0)]
      ≤ −E_p g.                                      (R1)

The last inequality is exactly `quittingPunishmentValue_le_max_solo`.
This is valid without a sign assumption. Every induced product Nash law
belongs to C_a. Therefore v_a≥0 makes E_p g≥0 and floorExcess≤0.
The free coordinates' source components are zero, and the outsider
inequalities are vacuous. The certificate theorem and its existing
`isUniformEquilibriumPayoff` consumer apply immediately.

Equivalently, use the source's unconditional positive-gap alternative.
Under no UE it supplies γ_a>0 with γ_a≤singletonExcess(p) at EVERY
induced Nash point p. Since free coordinates contribute zero, positivity
forces floorExcess(p)≥γ_a. Equation (R1) then implies

    E_p g ≤ −γ_a < 0  for EVERY induced product Nash law p.   (R2)

Existence of even one such p already gives the candidate's negative CCE
law. The source supplies a stronger uniform product-Nash restriction,
not merely the candidate's existential coarse-law restriction.

For the complete displayed fixture, p_∅=1/24 and E_p g=23/24. Thus

    floorExcess = −23/24 + (P₀−1)/24
                = (P₀−24)/24 ≤ −23/24.

The exact center is strictly accepted by this pre-existing transient source.
The same argument accepts every table in the whole stated 1/40 box, and
indeed every table admitted by the singleton CCE criterion, regardless of
whether the other source exclusions persist. No perturbation or stationary
selection calculation is needed for this inclusion.

### Bases of cardinality at least two

Again set free=I\E and internally choose any induced mixed Nash point p.
At least one other base member remains sure when a base member deviates.
Consequently its literal root endpoint difference is exactly E_p G_i^E.
The large-base excess components are therefore

    component_i(p)=−E_p G_i^E   for i∈E,
    component_j(p)=0           for j∈free.              (R3)

There are no outsiders. If v_E≥0, all the member expectations are
nonnegative simultaneously at the same p, so the existing excess is
nonpositive and `exists_uniformPayoff_of_persistentBase_inducedNash_signs`
applies. An empty free type causes no problem.

Under no UE, the existing large-base alternative instead supplies γ_E>0
such that every induced product Nash point has some member i with
E_p G_i^E≤−γ_E. Since p is a feasible coarse law, the candidate's
every-base/some-member/some-coarse-law condition follows directly. The
identity of the negatively affected member may depend on p. Nothing in
this argument illegitimately makes the member or negative law common.

### Corrected significance boundary

The finite CCE tests are useful sufficient relaxations of already implemented
induced-Nash acceptance tests. Their construction, finite raw inequalities,
all-sign empty row, exact one-shot profile and exact every-horizon conclusion
remain mathematically valid. The full open box genuinely separates CCE
certificates from the five withdrawal families; those families simply do
not exhaust the already available transient sources.

The exact same-profile/every-horizon conclusion is stronger delivery than
the punishment-tail consumer's approximate-profile UE conclusion, but it
does not remove any additional reward table from the UE counterexample
space. The negative-CCE necessary condition is weaker than (R2) and (R3)
under the source's positive-gap alternatives. Hence neither the raw class,
the center, the open box, nor the arbitrary-base extension supports the
previous additional-UE-coverage claim. That part of the prior verdict is
withdrawn. No source gap or mathematical counterexample to the valid
producer is alleged; this is an exact redundancy finding.
