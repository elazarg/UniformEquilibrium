# Bounded independent check of the recovery primitive and finite signal depth

Reviewer: CODEX_EMMY_BOX.

Status: ordinary mathematical review of Sections 3–6 of the current draft.
The displayed recovery estimates and bounded-depth recursion pass this check.
This is not a complete export review, a Lean check, or a producer of relaxed
equilibria. I did not audit a sunspot existence theorem or an adapter from it.

## Claim checked

For a finite nonempty player set of size n and reward bound R>0, let F be a
nonempty prefix-closed family of payoff/full-cap pairs in the reward box,
with nonnegative debts. For a finite convex combination zbar of F and any
finite independent product-root word w, put epsilon=d(T_w zbar) and let S
be the joint prefix survival probability. The claimed bounds are

    inf_F d <= n epsilon/S                         when S>0,
    inf_F d <= epsilon+2R sqrt(S)+2RS              always.

They imply the stated cubic positive-gap bound and zero-gap equivalence for
each fixed finite bound on the number of future public draws per path.

## Valid steps

The finite-prefix formulas retain complete deviation semantics. A pure
deviation either stops at one of the finitely many prefix dates or continues
through the prefix and uses a complete tail deviation. Therefore its cap is
exactly max(M_i,P_i+L_i b_i), including Never and every arbitrarily late
finite response. The latter alternative is a supremum; no attainment is
needed. Conditioning on the player's own first prefix stop gives the stated
formula for the prescribed payoff.

The lower bound D_i(T_w z)>=S D_i(z) has an independent interpretation: the
player may keep its prescribed prefix decisions and change only its tail
strategy. The gain from an approximately optimal tail replacement is S times
the tail debt. This also explains why the joint survival S, rather than the
player-deleted survival L_i, appears in that lower bound.

The large-S extraction uses affine debt under convex averaging. Selecting a
constituent with total debt below its average is legitimate because all debt
coordinates are nonnegative. It deliberately selects the unprefixed child;
requiring the preceding prefix to be retained would change the theorem.

For the small-S extraction, choosing i with maximal L_i gives
L_j^2<=L_i L_j<=S for every j!=i. A constituent satisfying b_i<=bbar_i
therefore decreases the only potentially weakly screened cap. Every other
cap changes by at most 2R sqrt(S), and every prescribed payoff changes by at
most 2RS. The same single constituent is used for all coordinates.

Literal S=0 is sound. If two players have zero own prefix survival, every
L_i vanishes. If exactly one does, only that player's L_i can remain positive,
and the low-cap constituent handles that coordinate exactly. For one player,
the assertions about other players are empty and the selected cap remains
valid. No denominator is introduced in the small-S branch.

The threshold S0=(n epsilon/(4R))^(2/3) gives the advertised h. When S0>1,
the added term exceeds 4R, so the box bound inf_F d<=2R suffices. Epsilon=0
must be treated separately, as the draft already does. The positive-gap
bound follows from the same two branches and has no hidden attainment step.

## Public-signal interpretation and limit order

For a finite publicly revealed child draw, the full cap is the average of the
children's full caps: the player sees the child and can choose a separate
approximately optimal complete response there. This is an observed fresh
draw, not a hidden correlated recommendation, and is essential to the model.
After one constituent is selected, dropping the prefix or retaining it both
remove the first draw and leave a tree with at most one fewer draw per path.
Thus F_(d-1) is the correct extraction target, and repeated extraction gives
h composed d times.

No objection was found in these statements. Their fixed-depth quantifier is
essential: eta_d->0 along d->infinity does not imply eta_0=0 from the displayed
estimates. The iteration's small-error exponent deteriorates to 1/3^d. A
future application needs an actual tree producer with a suitable joint bound
on depth and accuracy, or a different recovery theorem uniform in depth.

## Source cross-check

The prefix formula is consistent with `quittingTerminalSemanticPrefix` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` and its exact
prescribed/envelope meanings. The target-free conclusion agrees with
`isUniformEquilibriumPayoff_iff_diagonal_mem_terminalSemanticCarrier` in
`UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`.
These declarations were inspected statically under their imports; no Lean
command was run for this review.

Concrete next check: obtain a source theorem with the exact finite observed
future-draw semantics above, recording its depth as a function of the full
terminal error. An unrelated public-randomization existence theorem does not
supply this adapter automatically.

## Additional bounded check: Section 9, actual private marginal rebalancing

Status: **PASS of the ordinary proof draft**, including the deterministic
calendar-varying extension and expected-only falsifier. No source adapter,
general-game producer, or novelty audit is claimed by this check.

The crucial relative error is valid for every deleted-player subset J.
Writing `L=sum lambda_j`, union bound gives `mu(empty)>=1-L`, while every
singleton has mass at most `lambda_j`. Hence the only negative coordinates
of `mu-nu` are singletons, and

```text
TV(mu,nu)=sum_j [lambda_j-mu({j})]
 <= E sum_{j!=k} q_j q_k
 <= delta E sum_j q_j = delta L.
```

The same exact sign structure holds for the private product law. It gives
a coupling with the categorical reference in which a reference Continue
forces the actual Continue. The two couplings can share the same reference
draw; conditional coupling kernels give a legitimate joint construction.
At the first categorical Quit, the chance either system fails to match is
at most `(beta+beta')/L<=2 delta`. The assertion treats `L=0` separately.
No hidden lower bound on a rare opponent's hazard is used.

The same argument applies if the deviator quits at any deterministic date:
agreement persists until the earlier of that date and opponent absorption,
including the simultaneous coalitions at the stopping date. Never and the
event of no categorical Quit also agree. Thus the response comparison is
uniform over every pure time and Never. The full private cap is their
supremum, whereas the public cap is at least their supremum, since these
responses may ignore the signal. This proves the cap upper bound in the
needed direction. Together with the prescribed-payoff bound it gives
`E_private<=E_public+8R delta`.

For time-inhomogeneous exogenous kernels, let `T` be the first categorical
Quit date. Conditional on `T=t` the same mismatch bound holds. Summing over
all finite `t` bounds total mismatch by `2 delta P(T<infinity)<=2 delta`.
On `T=infinity`, both actual systems always Continue. Hence summable total
hazards and positive Never mass create no missing case. Independence across
dates is used in identifying the original public coalition process with
these per-date laws; a retained public macrostate is not covered.

The expected-only counterexample is also exact. Under the public rare
grand-coalition signal, every player gets the maximal possible payoff 1, so
the profile is full public Nash. Under independent marginal hazard theta,
the displayed prescribed payoff tends to 1/4. Immediate Quit has payoff
`(1-theta)^3+theta^3`, which tends to 1. Thus unrestricted private regret
has lower limit at least 3/4 despite expected total hazard tending to zero.
This verifies the stated failure of an expected-only hypothesis.

One useful next falsification target is retained *persistent* macrostate
with uniformly small conditional total hazard, rather than a rare signal
with large conditional hazards. The latter is already settled here.

## Additional bounded check: no-memory source obstruction on the boundary table

Status: **PASS of the ordinary composition in Section 10.** This is not
an independent export gate, a new Lean theorem, or a universal no-UE result.

I inspected the exact statement of
`isAsymptoticNash_quittingSerializedRoots` in
`UniformEquilibrium/Quitting/Root/SequentialSerializationEquilibrium.lean`.
It requires four players, unit own singleton exits, reward bound M,
coordinate hazard bound, and full terminal approximate Nash of the supplied
root-sequence profile; it concludes full terminal approximate Nash with
error enlarged by `32*M*hazardBound`. Its proof explicitly treats every
pure finite deadline and Never and then uses behavioral pure-time extremality.
Therefore no missing late-date/deleted-clock assumption is introduced by
using this declaration here.

I inspected `quittingSerializedRoots` in
`UniformEquilibrium/Quitting/Root/SequentialSerialization.lean` and
`Schedule`, `Schedule.roots` in
`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundarySoloHazardLedger.lean`.
The proposed schedule has owner `t mod 4` and hazard equal to the corresponding
original marginal in row `floor(t/4)`. It is literally the serialized root
process, not merely a distributional analogy. Marginals lie in `[0,1]`,
and the uniform conditional total bound implies each marginal is at most
delta. Stationarity or positive/nonsummable total hazard is unnecessary.

Finally I inspected `Schedule.exploitability` and
`Schedule.one_over_sixtyEight_lt_literal_exploitability` in
`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundarySoloHazardSemantic.lean`.
The former is exactly `quittingTerminalExploitability boundaryReward
schedule.profile`; the latter has no extra charge-supply hypothesis.
`boundaryReward_unitSoloExit` supplies the required normalization, the
displayed finite table has absolute rewards at most 4, and
`periodTwo_residualHardClass` in
`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`
has the claimed literal table as its argument.

Thus the additions `8*4 delta + 32*4 delta = 160 delta` are correct,
and the full cap floor indeed yields `epsilon+160 delta>1/68`.
This excludes unconditional diffuse no-memory production even on a solved
full-normal/Q residual example. It does not exclude a producer only for
actual no-UE tables, a disjunction dispatching this solved example first,
or a retained-state source with a genuinely different legal-root recovery.

## Section 13: independent producer/consumer and bounded coverage review

Reviewer: CODEX_EMMY_BOX. This review concerns the Section 13 candidate
whose supplied whole-file hash was
`07e662fac8b04b956282713b0fd373aff495fb5f7f8b016d0a9c572415a67375`.
It is separate from CODEX_NASH_BOX's full derivative reconstruction.

**Verdict: PASS for the ordinary local producer and unrestricted fixed-profile
uniform-payoff conclusion, with the strengthening below.** No mathematical
objection remains in the input-to-output chain checked here. The bounded
source comparisons below do not show containment in an existing named raw
producer. This is not a claim to have surveyed every possible stationary
certificate, every unquantified implicit-function neighborhood, or every
research-only sufficient condition. No Lean implementation is claimed.

### A strictly stronger and simpler raw statement

Let r* be the displayed center, but constrain only the 56 reward coordinates
on proper nonempty coalitions. There is delta>0 such that

    max_(empty != S != I,i) |r_i(S)-r*_i(S)| < delta

implies the exact terminal Nash and same-profile uniform-payoff conclusions,
for EVERY arbitrary finite grand-coalition row r(I). Thus the source class
can be an open cylinder in the full raw reward space, not merely a ball.

Indeed, the prescribed live support has size two. Keeping the other three
players' strategies fixed, an arbitrary unilateral replacement can add at
most one quitter to that support. Therefore no terminal coalition of size
four occurs, on path or under any unilateral replacement. Policy values,
all endpoint inequalities, the eight residuals, their rate Jacobian and
the complete caps are exactly independent of r(I). Take the IFT in the
56 proper-coalition coordinates. The geometric uniformity estimate may use
a common bound on proper-coalition rewards only; no bound on the free grand
row is needed. The author may retain the displayed asymmetric grand row
when demonstrating source separation at ONE center of this cylinder.

### Independent input-to-output check

I independently recomputed the four actual phase values by summing the
geometric policy series, and all eight inactive Continue-minus-Quit gaps.
They are exactly (21) and (22). The eight owner endpoint equalities follow
directly from these actual values. I checked the displayed integer matrix's
determinant independently:

    det K = 16435089066040617600000,
    det(K/255) = 28792380416/31320375 > 0.

For a bounded independent derivative check, the A0 residual has derivatives
0, 504/255 and -256/255 with respect to a0, a1 and b1. For example the
forcing from a1 in the receiver-0 policy equation is 3, which propagates
to U_B,0 as 12/255; hence the a1 derivative of F_A0 is
2-(1/2)(12/255)=504/255. The b1 forcing at B is 2, giving derivative
-(1/2)(512/255). I did not duplicate all 64 entries of Nash's reconstruction.

The producer has finite raw reward inputs only. Formula (23) is the actual
contracting policy solution, not an externally supplied continuation. The
IFT at a nonsingular zero supplies the eight rates; openness makes every
rate lie in (1/4,3/4) and preserves all strict inactive inequalities. These
rates define actual independent private clock laws, each proper because
it is scheduled twice per period. Neither a profile nor a favorable fixed
point is a premise.

For every player, its opponents have six independent scheduled quitting
opportunities per period. Their continuing probability is at most
rho=(3/4)^6, regardless of the deviator's private randomization, memory,
deadline or Never choice. The one-step Bellman upper bounds therefore
iterate with a vanishing remainder. This proves COMPLETE terminal Nash,
not merely Nash within the four-periodic family. The same estimate bounds
expected stopping time by 4/(1-rho), uniformly under every replacement,
so the displayed terminal-to-average and regret estimates give the one
fixed actual target before every accuracy. The selecting date's zero
reward is included in tau+1. No boundary payoff at Never is lost, since
the opponents alone absorb almost surely with this uniform bound.

These premises are precisely the policy, root-Nash and opponent-cycle
contraction inputs of
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`,
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`. The novel
source step is the local eight-rate construction, not that checked consumer.

### Additional exact exclusion: all sure-owner induced Nash rows

I inspected `QuittingInducedOwnerChamber` and
`QuittingInducedOwnerNeverChamber` in
`UniformEquilibrium/Diagnostics/Quitting/InducedOwnerChambers.lean`, and
`quittingSingletonBaseOwnerFloorExcess`, its nonpositivity equivalence and
`nonempty_quittingSingletonBaseCertificate_of_inducedNash` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.
The punishment-tail compiler does NOT cover the asymmetric center.

Fix sure owner 0, and let x,y,z be players 1,2,3's quit probabilities in
the full induced three-player game. Their Quit-minus-Continue differences
are exactly

    d1=(1-y)(1/2+z/4)-98yz,
    d2=(1-z)(-3+4x)-z(5+94x),
    d3=2-15x-2y-85xy.

At a Nash point z>0 would require d3>=0, hence x<=2/15. Then d2<0
forces y=0, and d1>0 forces x=1, a contradiction. Thus z=0. If y<1,
d1>0 forces x=1, then d2>0 forces y=1, again a contradiction. Hence
the entire induced Nash set is

    z=0, y=1, x in [3/4,1].

The sure owner's actual payoff is -3 throughout; its forced Continue
payoff is 2x. The other players' joint Continue probability is zero, so
the punishment-value term in the floor comparison is zero. Every owner
floor excess is 3+2x>0, whatever its punishment value.

For sure owner 1, write x,y,z for players 0,2,3. The differences are

    d0=(1-z)(1-6y)-97yz,
    d2=(1-z)(2-x)-99xz,
    d3=-3-10x+(15/4)y-(363/4)xy.

At z=0, d2>0 forces y=1, then d0<0 forces x=0, and d3>0 contradicts
z=0. If 0<z<1, d3>=0 requires y>=4/5, then d0<0 gives x=0; next
d2>0 gives y=1 and d3>0 gives z=1. Consequently the full induced Nash
set is exactly

    x=0, z=1, y in [4/5,1].

The owner payoff is -3, Continue payoff 10y, and the punishment term is
again zero. Owners 2 and 3 have the same respective conclusions after
the half-turn relabeling; the different grand entries only replace the
large negative coefficients by other sufficiently negative coefficients
and do not change the deductions. Their owner floor excesses are also
strictly positive.

This checks every `free` selection, not only the full three-player one:
a Nash point on a smaller free set, together with the compiler's outsider
no-join signs, extends by fixed Continue outsiders to a full induced Nash
point. All full points have already failed the owner-floor input. The
all-Never-tail variant independently fails its required nonpositive own
singleton, since all four own singletons here equal 1.

### Bounded implemented and accepted source comparison

- The literal singleton matrix is the checked paired matrix. I inspected
  `FourPlayerPairedSingletonLCP.lean` and
  `FourPlayerPairedSingletonResidualHard.lean` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/`. Their algebraic residual
  classification does not by itself solve every completion. The full
  nonnegative-inverse criterion in
  `UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`
  explicitly requires negative determinant; this center has determinant45.
  Every triple inverse has a negative diagonal, so the raw triple criterion
  in `Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean` fails.
- `QuittingResponseInvariantOnUnitCube` in
  `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`
  demands equality at the all-sure point as well as near zero. The four
  all-sure responses (-97,-98,-99,-100) exclude every nondiscrete literal
  quotient. The named singleton block-row identity makes positive row
  rescalings equal within a proposed block (sum over block columns, using
  the common singleton row sum1), so such rescaling does not repair this
  obstruction. This check is about literal response invariance, not every
  possible strategy quotient.
- I checked the nonnegative quiet-child join row against both the accepted
  `NONNEGATIVE_SINGLETON_FINITE_QUIET_LIFTS.md` and actual
  `CappedClockParentRewardCertificate` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`.
  All four triple-child failures in Section13 are correct. Every pair and
  singleton child listed there also has a positive omitted-player join gain
  against nonpositive child join gains. Thus the whole proper-child selection
  set fails this particular nonnegative donor comparison.
- `RawRegion` in `UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`
  requires an ordered PARTITION into pairs, unlike the proposed repeated-owner
  support cycle, and imposes `OwnBounds`, `PassiveBounds` and joining caps.
  In `MathUE/PairedAffineIntervalEstimates.lean`, `OwnBounds` requires partner
  reward in [-1/10,1/10], joint reward in [19/10,21/10]. Favorite partners
  here have passive reward4, and harmful partners have pair reward-3 or the
  wrong joining caps. The center therefore does not meet this named raw class
  under any pair partition. The broader `twoPair_exact_terminal_and_fixedProfile`
  is a supplied-data consumer, not a raw producer claiming all completions.
- All three partitions fail accepted `TWO_PAIR_JOIN_CAP_UNIFORM_EQUILIBRIUM.md`
  by the explicit violations in Section13. The participant and cap hypotheses
  of `OPPOSITE_SIGN_MATCHING_PHASE_UNIFORM_EQUILIBRIUM.md` and
  `BELOW_SINGLETON_JOINT_PHASE_UNIFORM_EQUILIBRIUM.md` do not restore coverage.
  The singleton positive graph is two transpositions, not the favorable
  three- or four-cycle required by the inspected cyclic-child and signed-cycle
  raw families. I compared `GLOBAL_TWO_JOINT_CYCLIC_CHILD_UNIFORM_EQUILIBRIUM.md`,
  `ONE_JOINT_PHASE_WITH_DIFFUSE_SOLO_EXITS.md` and
  `LARGER_EIGENVALUE_SIGNED_FOUR_CYCLE_UNIFORM_PAYOFF.md` on these literal signs.

I also read the existing local raw-table construction
`PairedCubicStationaryExample.exists_local_stationary_branch` in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`
and accepted `TWO_JOINT_PHASES_FULL_TABLE_NEIGHBORHOOD.md`. They are earlier
local producers about different explicit centers. Their existence statements
do not specify a maximal neighborhood, so no honest disjointness claim about
their unspecified neighborhoods follows merely from comparing the centers.
Nor does this review exclude a stationary equilibrium at the new center.

The surviving mathematical conclusion is a direct raw open-cylinder producer
with a concrete asymmetric center failing the named finite source screens
above, not a proof that four phases are necessary. This is stronger evidence
than merely supplying another periodic certificate. The proposed strengthening
removes a genuinely unused assumption and is ready for author incorporation.

## Section 14: exact coordinatewise source strengthening

Reviewer: CODEX_EMMY_BOX. **PASS** for the 32 local /12 upper-only /16
arbitrary-coordinate strengthening. This is a bounded check of the support
partition, pathwise comparison and proxy producer, not another full IFT audit.
There is no unresolved mathematical objection in this scope.

The scheduled support edges are01,12,23,03. On the prescribed profile,
only their four pair rows and the four singleton rows occur, giving exactly
32 on-path recipient coordinates P. Under player0's or2's replacement,
the only extra own-recipient coordinates occur at02,012,023. Under player1's
or3's replacement they occur at13,013,123. This gives exactly the twelve
C-coordinates listed by the author. The two passive recipients of02 and13,
the two other recipients of each triple, and all four grand coordinates
are the remaining sixteen F-coordinates.

I checked every player against every scheduled phase. If the replacing
player is scheduled, its action can produce only one of that phase's
singletons or the scheduled pair. If unscheduled, Quit can add it to one
or both scheduled opponents, giving only its displayed C-coordinates or
already-listed P rows. If it Continues, every coalition is again a P row.
Simultaneous opponent quitting and player-deleted support are retained;
there is no approximation of a product root by a categorical one.

An F-coordinate can affect some OTHER player's payoff when a deviation
occurs, but never the deviating recipient's own payoff or any prescribed
payoff. That distinction is exactly sufficient for unilateral Nash
comparisons. The theorem makes no coalitional-deviation claim.

For the same independent private seeds and one fixed complete replacing
rule, the finite preabsorption histories, stopping date and coalition are
identical in r and the proxy. Hence coordinatewise lowering C while
holding P fixed weakly lowers the deviator's own terminal reward pathwise.
The fraction of finite-horizon dates paid after the selecting date is the
same nonnegative scalar on both paths, so finite-average deviation rewards
also weakly decrease. Never is zero in both. All complete behavioral rules
remain available because no information is changed before absorption.
Taking their full supremum preserves the inequality. Prescribed payoffs
are identical, not merely close.

With delta=delta0/2, the proxy's P coordinates have error<delta, its C
coordinates have error delta<delta0, and its proper F coordinates have
zero error. Its free grand row may be0 by the already-reviewed cylinder
theorem. That theorem therefore produces the rates and actual fixed target
for EVERY allowed original table. Pathwise comparison transfers exact
terminal Nash and same-profile uniform payoff to that original table.
The proxy's cutoff even works unchanged; a reward bound uniform over the
newly unbounded lower or arbitrary coordinates is not required.

This is a genuine removal of unused or monotone source assumptions. It
preserves all sixty finite inputs, full behavioral agency and the fixed-
target-before-accuracy quantifier. It does not claim uniformity of a
recomputed strategy across different P data or arbitrary-game completeness.

## Section 15: bounded independent source and whole-selection check

Reviewer: CODEX_EMMY_BOX. **PASS within the stated bounded scope** for
Section15 of the notebook with SHA256
`797f0737c9b3682d579093625c020691fb0f170ba6a0863cf1011d695666ec84`.
This checks the raw producer chain, its explicit witness and the named
existing source-selection sets; it does not re-audit the generic periodic
consumer or assert that every older existence theorem is excluded.

The statement produces an actual two-variable zero from finite raw data.
The eliminated six owner equations agree with the displayed phase values;
the face-sign coordinate order is correctly (F_B,F_A) on (a,g). The four
strict face signs exclude boundary zeros and give all eight proper rates
above1/6. The negative barrier has coefficient at least1/(24M), whereas
every other reward entering the inactive player's Quit endpoint is at most
L. Its strict upper bound -24ML therefore makes that endpoint negative.
Prescribed rewards are nonnegative, so the inactive Continue value is
nonnegative. No strategic continuation or root is supplied as an input.
The already-reviewed complete-deviation deleted-survival argument and
table-specific finite reward bound then supply the exact terminal and
same-profile fixed uniform conclusions. I found no soundness caveat in
this source-to-consumer chain.

I independently expanded all twelve induced-owner differences of witness
(39), including the asymmetric grand-row corrections. They are precisely
(40), (41), and the listed owner2/3 replacements. For owner0, d3>=0
forces x<=2/(K+3), making BOTH affine z endpoints of d2 negative;
thus z>0 is impossible. Owner2 has the slightly weaker bound2/(K+1),
still sufficient because K>4. For owners1/3 the coefficient of x in
d3 is strictly negative on0<=y<=1, giving y>=K/(K+1) whenever z>0;
then d0<0 and the claimed Nash-set conclusion follows. Therefore the
complete sets really are

    owner0/2: z=0,y=1,x in[K/(K+1),1],
    owner1/3: x=0,z=1,y in[K/(K+1),1].

The owners' current rewards are -K and Continue rewards Vx or Sy; their
opponents' all-Continue mass is zero. Hence punishment values cannot repair
the strictly positive floor excesses K+Vx and K+Sy. This is a whole
induced-Nash-set check, not a pointwise pure-root rejection.

I re-read `quittingSingletonBaseOwnerFloorExcess_nonpos_iff` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`
and both `nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
`exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`.
The latter's accepted free-Nash, base-leave and fixed-outsider-join signs
would give a full zero-tail root with sure quitters. Picking any sure
owner would contradict the complete induced sets above. Consequently
EVERY larger-base/free-set selection of these compilers fails, as claimed.
For a singleton base with a smaller free set, its outsider signs extend
the free Nash inequalities to a full induced Nash point, where the floor
still fails independently of its punishment value.

The quiet-child witness comparisons also hold over all nonnegative donor
weights: every indicated omitted-player join gain is positive while every
available child-donor gain is negative or absent. The paired singleton
matrix is unchanged, so the previously checked singleton-only inverse,
homogeneous and favorable-singleton-cycle screens have unchanged failures.
All-sure responses (-K,-K-1,-K-2,-K-3) are indeed distinct. The three
two-pair partition and guarded-face violations use the same literal signs
as the preceding bounded review, with -K replacing -3. No hidden choice
of a base, omitted player, donor weights or pair partition repairs these
named sources.

The just-exported `FOUR_JOINT_PHASE_UNIFORM_EQUILIBRIUM.md` has a P-coordinate
radius at most1/2 about W=5/4 and V=2. The present source requires W>=48
and V>=10, and these are ON-PATH coordinates, not arbitrary F coordinates.
Thus that literal local source does not cover this unbounded family.
Schedule-preserving relabeling cannot hide the large passive pair reward:
positive participant cycle edges must still map to scheduled edges, and
all their passive center rewards are at most10. The other new scale-family
proposal from Nash requires ALL twelve pair-participant rewards to have
one large common positive base; the four participant rewards -K here
violate that hypothesis.

I also inspected `PairedCollisionReward.reward` in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardTable.lean`
and `PairedCollisionReward.exists_uniformEquilibriumPayoff` in its
`PairedCollisionRewardExistence.lean` companion. The named theorem solves
its literal one-parameter completion, whose member rewards share one
parameter; it does not solve arbitrary completions of the shared singleton
matrix and does not cover(39). The prior local stationary and two-joint
IFT producers have unspecified radii, so no exclusion of every such
neighborhood follows. The author's explicit caveat about that issue,
and about possible stationary equilibria, is necessary and correct.

The accepted conclusion of this bounded review is a nonlocal unbounded
raw source with a concrete unbounded separating family for the NAMED
singleton, quotient, quiet-child, pair-partition and sure-base sources.
It is not a claim that four phases are necessary or a global residual
classification. No unresolved mathematical objection was found here.

### Broader raw withdrawal and F/J-only quiet sources

The preceding quiet-child comparison extends to ALL FIVE implemented
withdrawal kinds, not merely the advancing-only capped-clock subcone.
This applies both to Section13's asymmetric separating center and to
EVERY Section15 witness(39). I inspected the actual definitions
`DeadlineWithdrawalRewardCertificate` in `DeadlineWithdrawalRaw.lean`,
`WithdrawalFutureJoinKind.gain` and `WithdrawalFutureJoinRewardCertificate`
in `WithdrawalFutureJoinRaw.lean`,
`deadlineSecurityGainFloorWithRestart` in
`DeadlineWithdrawalRestartPointwiseCore.lean`,
`patientWithdrawalFloor_le_ownNeverAlternative` in `PatientWithdrawalRaw.lean`,
and `deadlineWithdrawalSecurityValue_le_singleton` and
`deadlineWithdrawalSecurityFloor` in `DeadlineWithdrawalSecurityLP.lean`.
All these files are in
`UniformEquilibrium/Quitting/Classification/QuietExtension/`.

For every kind, a nonmember of the first coalition A has withdrawal gain0.
For nonsingleton A and member i its gain is exactly
r_i(A\{i})-r_i(A), regardless of the singleton restart floor. Thus the
two member withdrawal gains on scheduled pairs are

    A=01 or23: (-1,-1/2),
    A=12 or03: (-2,-2).

All are negative. For singleton A={i}, every kind has withdrawal gain at
most0 here, because s_i=1 and its restart floor is at most1. The patient
bound follows from its displayed own-Never alternative max(1,0)=1.
The untruncated security floor is max(zeroFloor,securityValue)<=1 by
the named singleton bound and zeroFloor<=0. Truncating at0 only lowers
it; ordinary deadline/cancellation use zeroFloor directly.

Here are complete proper-child witnesses. In the two gain columns, the
first number is the Section13 center gain and the second is the Section15
gain. A dash means there is no child nonmember that could advance.

| Child C | First coalition A | Failed outsider e | Outsider join gain | Remaining child advance gain |
|---|---|---|---|---|
| 013 | 01 | 2 | 1 /1 | -13 /(-K-S) |
| 123 | 23 | 0 | 1 /1 | -13 /(-K-S) |
| 012 | 12 | 3 | 3/4 /1 | -5 /(-K-V) |
| 023 | 03 | 1 | 3/4 /1 | -5 /(-K-V) |
| 01 | 01 | 2 | 1 /1 | — |
| 23 | 23 | 0 | 1 /1 | — |
| 12 | 12 | 3 | 3/4 /1 | — |
| 03 | 03 | 1 | 3/4 /1 | — |
| 02 | 2 | 1 | 2 /2 | -3 /(-K) |
| 13 | 3 | 0 | 2 /2 | -3 /(-K) |
| 0,1,2,3 respectively | same singleton | 3,2,1,0 respectively | 2 /2 | — |

Members of A have zero advance gain. Combining the table with the
nonpositive member withdrawals shows that the join row of
`WithdrawalFutureJoinRewardCertificate` has strictly positive left side
and nonpositive right side for EVERY nonnegative pair of weight arrays,
for patient, deadline, evaluatedSecurity, terminalSecurity and cancellation.
Hence none of their F/J-only certificates exists for the selected outsider
of any nonempty proper child. A multiple-outsider family necessarily
contains that outsider and therefore also fails. Omitting the N row,
charging its residual to a positive singleton or making joint Never small
cannot repair this already-failed J row. The stronger full N/F/J raw
certificates fail a fortiori. This is a whole kind/child/weight selection
check, not a claim excluding every conceivable quiet-lift mechanism.

## Independent bounded review of Section19: the whole passive-reward ray

Author snapshot: whole-notebook SHA256
`a74a0df2120eee5b35960c0b40ac6699a779f601f7d5c2e904422481237cf8c4`.
Scope: the raw A,B,K producer, actual four-phase values, ALL unilateral
behavioral/date/Never caps, same-profile uniform payoffs, and the relevant
whole-selection source comparisons. This is an independent ordinary
mathematical check, not a Lean implementation or unrestricted Fin4 theorem.

Verdict: PASS. I found no unresolved mathematical objection in the stated
parameter range. The entire nonnegative K ray is a meaningful explicit
raw-family extension beyond the named sources checked below. The result
does not imply a general compensation architecture or characterize all
equilibria of these games.

### Exact producer and boundary falsification attempts

For T<A<4, D=sqrt((4-A)/(A-1)) lies strictly between0 and
(3-sqrt(5))/2, and J=(A-1)D satisfies0<J<1. Hence C=(1-D)(1-J)>0
and qstar=1-sqrt(D) is strictly between0 and1.

At K=0 the symmetric IVT proof is genuinely valid: f_K(0)=0 and
f'_K(0)=-1 give negative values at positive small q, while
f_K(qstar)=C>0. At K=Kcrit the endpoint qstar solves the equation
exactly. No division by K occurs at either boundary. For K>Kcrit,
x=C/K lies in(0,qstar^2), the discriminant factorization is correct,
and the two positive roots have sum less than2 and Continue-product D>0;
this proves0<b<a<1, not just a nonnegative discriminant. Both roots
approach qstar at the switch.

I independently substituted the symmetric and asymmetric policies into
BOTH active-owner endpoint equations. In the asymmetric case the common
residual reduces to Kx-(1-D)(1-J)=0. The passive recursions are
W=Kx+dL and Z=Kx+dH with the ORIGINAL pair reward K. The four phase
recursions follow by the actual tau=(0 2 1 3) table symmetry. Joint period
survival d^4<1 uniquely determines the displayed finite policy values.

The inactive Quit endpoints include the ORIGINAL triple reward K-1.
Their margins are exactly(62). In particular the potentially delicate
B=J endpoint has second asymmetric margin Jb+x>0 at every finite K;
there is no division by this margin or demand for a uniform positive gap
as K grows. On the symmetric branch both margins are positive independently
of B. The allowed upper B bound is consistent with the entire high-K ray.

For K->infinity, a->1-D and b~(1-J)/K, while Kab=C exactly. Deleting
the small b coin before multiplying its rare collision by K would be
invalid. Deleted-player contraction remains D^3, but the payoff bound M
grows with K; the proof correctly needs no uniform horizon over changing
tables. Literal K=infinity is not a parameter of the theorem.

At A downarrow T with fixed K>0, eventual selection of the asymmetric
branch is justified by Kcrit->0 and gives the golden singleton limit.
At K=0 the symmetric limit is instead qstar=(3-sqrt(5))/2. An additional
algebraic check at A=T shows that (1-q)f_0(q) factors as a positive
constant times

    q*(q-(3-sqrt(5))/2)*(q-(sqrt(5)-1)/2)*(q-(sqrt(5)+1)/2),

so qstar is the only nonzero limiting root at or below that endpoint.
The derivative at zero excludes convergence to zero. Thus the corrected
distinction is real. At A upward to4, B<=J must also shrink toward0;
there is no claimed fixed-B continuation through that excluded endpoint.

### Unrestricted source-to-UE chain

Every player has one a and one b coin per period. After deleting ANY
deviator, the three remaining independent clocks have period survival
d^3<1. The verified endpoint inequalities and actual policy equations
therefore telescope against an arbitrary complete replacement; the
remainder vanishes, including for Never. This is not an inference from
a finite menu or stationary best replies. Prescribed play attains each
displayed value, so the full cap equals that value.

The same deleted-clock bound gives a deviator-independent expected live
time at most4/(1-d^3), with the extra1 in C_hor harmless for indexing.
Thus terminal-versus-N-stage delivery differs by at most M*C_hor/N for
prescribed play and for EVERY deviation. Terminal Nash then gives horizon
regret at most2M*C_hor/N. The selected private profile and each initial
phase's target are fixed before epsilon and N. No supplied strategy,
normalized reward, public lottery or limit strategy is an input.

For the actual source/consumer objects I checked the declarations
`quittingSubBellmanValue_le_superSolution_of_survival_zero` and
`isεAsymptoticNash_quittingCyclicBehaviorProfile_of_quitError_exactContinue`
in `UniformEquilibrium/Quitting/Cycles/CyclicSupersolution.lean`, and
`quittingGame_fixedProfile_uniformPayoffWitnesses_of_terminalNash_exact`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The present raw producer is ordinary mathematics, not already any one of
these Lean declarations.

### Whole selections and a stronger singleton-calendar exclusion

I checked the full sure-owner induced game rather than one chosen point.
Its two noncollider Quit actions have strictly negative gains A-4 or -B
when alone, -1 when one further nonowner quits, and -1-K when both do.
They are strictly dominated for ALL mixtures. The collider kappa(j) then
Quits surely with gain B, and owner j strictly prefers leave by B. Thus
the entire induced-Nash set is the printed unique point, at every K>=0.
Its all-Continue mass is zero, so no punishment coefficient changes the
conclusion. The full-game implication from any larger base/free-set
certificate to a Nash point in this sure-j game excludes ALL those
selections as well. The actual definitions are
`quittingPersistentBaseUtility`, `quittingPersistentBaseNashSet`, and
`quittingPersistentBaseRoot` in
`UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean`.

For every proper child, the escaping kappa edge gives outsider join B>0
at a singleton, whereas every permissible child advancement is0,A-4,
or -B. The five withdrawal restart floors on this singleton are at most1,
so every withdrawal gain is nonpositive. This excludes all nonnegative
weights, children and raw F/J withdrawal kinds, not just the capped-clock
advancement cone. The precise floor definitions inspected in the previous
review subsection apply unchanged because these singleton rows are the
same; K never enters this failed row.

There was one coverage ambiguity worth resolving: the golden singleton
export has not only its explicit A<=T theorem but also an existential IFT
neighborhood. The explicit cap alone does not logically compare the whole
latter source. In fact an elementary uniqueness argument excludes the
ENTIRE positive-hazard singleton calendar at the exact singleton rows.
In chronological word order0,2,1,3 put u_i=1-p_i in(0,1). Active-owner
indifference is equivalent to the four cyclic equations

    E_i=u_i*(4-4u_(i+1)+u_(i+1)*u_(i+2))-1=0.

Put alpha=u0-u2 and beta=u1-u3. Opposite equation differences give

    4*(1-u1)*alpha-u2*(4-u0)*beta=0,
    u3*(4-u1)*alpha+4*(1-u2)*beta=0.

All four coefficients have the displayed strict signs. The determinant
is positive, forcing alpha=beta=0. Write u0=u2=x,u1=u3=y; the remaining
opposite parity difference is (4+xy)(x-y)=0. Hence every u_i=u, and

    (u-1)*(u^2-3u+1)=0.

The unique root in(0,1) is u=(3-sqrt(5))/2. Thus EVERY all-positive
proper singleton-calendar solution has the exact golden hazards, not
merely the IFT-selected branch. Its inactive mate-join cap is A<=T,
contradicting Section19's strict A>T. This covers all relabelings of the
named singleton calendar with these singleton rows and proves exclusion
of both exported producers, without guessing their existential radii.
It does not exclude arbitrary singleton strategies or other owner words.

The other checked whole-source comparisons are also valid: singleton
Gamma is R0 of degree+1; the four listed block-cube H witnesses exclude
the four dangerous response partitions independently of K; the remaining
actual quotients have positive determinant and inverse and degree+1.
I checked that
`finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`
requires determinant<0. Mere nonnegative inverse does not invoke it.

The `cap_favorite` row of `RawSource` and `WeakRawSource` in
`UniformEquilibrium/Quitting/Cycles/CrossedMatchingPhaseSource.lean`
fails A>1 once the singleton favorite is fixed. For `InverseRawSource`,
`scheduled_lt` forces a nonmate scheduled partner, so the mate is one
of the two unscheduled partners and either `cap_favorite` or `cap_other`
fails A>1. The unique-below-singleton
screen excludes the paired affine raw source; one negative cross participant
excludes the relevant below-singleton and positive-common-pair raw sources.
Favorite A<4 is outside the first four-joint export's declared radius at
most1/2 around a participant5, and outside the rectangle export's literal
favorite coordinates5,9/2. These are bounded comparisons to named raw
classes, not an exhaustive classification or a universal nonoverlap claim.

No unresolved soundness or meaningful-coverage objection remains in this
bounded review. The next general issue is global selection of compensation
roots, not further parameter enlargement of this explicit family.

## Independent bounded review of Section30: the entire C_delta source

Claim checked: for EVERY delta in(0,1), EVERY exact independent Nash law
in C_delta on the two-player waiting table(C3) has finite masses
0<m0<=1/2 and m1<=1/2, hence ORIGINAL unrestricted terminal debt D0>=1/4.
This is not a Fin4/nonnegative-own-singleton claim and not a no-go for the
smaller normalized selective-Never source S_delta.

Reviewed Section30-through-EOF SHA256
`8d57e0500712b37fa55fbdc594edbffa2d4a5bff7d638a27b9936630738ff523`.
The observed whole-file SHA is
`30d950bc4225fb3691c0918273415a15110187c154d9228bc4b0a689a4760bd2`;
the former hash identifies the frozen reviewed section, not the whole note.

**Verdict: bounded independent ordinary mathematical PASS.** I found no
unresolved mathematical objection to the complete correspondence theorem,
compact source existence, private-type interpretation, or original-game
bypass. This is not Lean verification and not a new UE exclusion class.

### Exact domain, existence and private types

C_delta bounds the UNCONDITIONAL finite tail at every date by c^t, leaving
Never exempt. Uniform exponential finite tails make this closed convex set
totally bounded in total variation; completeness makes it compact. Joint
terminal-payoff continuity follows directly from bounded rewards and product
TV coupling, including the all-Never atom. Finite epsilon-nets, finite-game
Nash on their convex hulls, and compact limits therefore give exact restricted
Nash without any unsupported weak-topology payoff continuity claim.

The formal order Never<0<1<... correctly identifies the tail inequalities
with stochastic domination by geometric G. Monotone quantile coupling gives
either Never or a finite T<=G. This is a representation using OWN private
randomness, not observation of opponents or a public lottery. Conversely
every such representation obeys every finite-tail inequality.

The cap E max{V,f(0),...,f(G)} is attained by a pointwise maximizing rule,
because G is finite almost surely. An optimal law under ANY legal coupling
must be pointwise optimal: otherwise replacing its strictly inferior choices
on a positive-probability set gives a strictly better legal law. Thus the
strict-record statement gives EXACT finite tail c^tau, not merely an upper
bound. Types G<tau cannot choose dates>=tau, and types G>=tau cannot choose
Never or any earlier date. Types G=tau contribute an atom at least delta*c^tau.

### Full endpoint formulas and every mass case

I independently conditioned on an opponent quitting before, at, or after t,
including its Never mass. This gives

    f0(t)=1+F1(t)-a1(t),       V0=2*m1,
    f1(t)=-1-F0(t)+a0(t),     V1=-2*m0.

The limiting finite deadline for player0 is1+m1, dominates its Never value,
and bounds every finite endpoint. Consequently its ORIGINAL cap is1+m1
even if no finite date attains it. At every prescribed positive atom t,
restricted optimality f0(t)>=V0 yields exactly2*a1(t)+R1(t)<=1-m1.

If m0=0, player1 must choose Never, after which legal Quit0 strictly
improves player0. Hence the first finite positive p0 atom tau exists.
If m0>1/2, then f1(0)>=-1>V1. Moving any Never mass to0 is legal and
strictly beneficial, so m1=1. Player0 has legal Never payoff2, equal to its
full cap; all its positive atoms must earn2. Thus all p1 mass lies STRICTLY
before tau, and tau>=1. All those dates earn player1 exactly-1. The proposed
replacement (1-c^tau)Quit0+c^tau Quit_tau is legal at EVERY deadline budget,
and raises its payoff by c^tau*a0(tau)>0. This excludes m0>1/2.

For m0<1/2, every date before tau earns player1-1<V1, so it has no mass
there. The p0 support inequality at tau gives m1+a1(tau)<=1-m1, hence
m1<=1/2. At the separate boundary m0=1/2, tau is a strict record above
V1 and every earlier endpoint. Therefore p1's finite tail at tau equals
c^tau. Player0's own tail budget gives c^tau>=m0=1/2. Its support inequality
then gives1-m1>=c^tau, proving the same bound. No continuity from the strict
case or implicit conditioning by a potentially tiny reach is used.

Finally A+B+C=1-(1-m0)(1-m1), U0=A+2B, and B<=m1 give

    D0=1+m1-U0 >=(1-m0)(1-m1)>=1/4.

This exhausts the entire correspondence, including unbounded calendars,
arbitrary atoms and Never mass. The auxiliary existence statement is also
easy to calibrate: both players choosing Quit0 with probability1/3 and Never
otherwise is an exact C_delta Nash for EVERY delta, with unrestricted D0=2/3.
This calibration is not substituted for the whole-correspondence proof.

### Bypass and limits of the falsifier

For proper Geom(kappa) versus sure Quit0, independently recomputed original
payoff(2*(1-kappa),-1+kappa), debts(2*kappa,0), and all pure-date/Never
caps. Thus the fixed target(2,-1) is a valid UE limit, even though every
exact C_delta source component stays a fixed distance from terminal Nash.
The cited `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
has precisely the unrestricted terminal-all-errors-to-UE conclusion used.

For delta<=kappa, the bypass laws themselves lie in C_delta; the defect is
exact source equilibration, not lack of legal approximate profiles. In the
good S_delta component(S8), m1=1/(1+2*delta)>1/3, so player0's forced first
finite atom earns1-m1<2*m1=Never. Deleting that atom is legal for C_delta
but need not retain the normalized proper part required by S_delta. Thus
the distinction between the two exact correspondences is genuine; set
inclusion does not transfer the no-go. No broader source exclusion follows.

## Bounded independent review of the strict coarse source and selection

Reviewed Section31 at section SHA256
`45229b1a5263e232db435525bc0b8b4caf678ce409e97a66ac8820be21d12c96`
and Section32 at section SHA256
`7c6cf570fe7b9eb9c2fe6f56f840ab5c9b38bbf182e183f1d83a42e2c6f070bc`.
The section extraction is heading through the next same-level heading,
with trailing whitespace removed and one final newline. Both hashes
were recomputed. Verdict: PASS as bounded ordinary mathematics; no
objection found. No Lean compilation or independence-improvement theorem
was checked or inferred.

### Exact complete-deviation ledger

I independently partitioned the hidden owner/date experiment by T>h,
T<h-1, T=h and T=h-1. The respective expected gains are d_i, g_i,
A0_i and A1_i. In particular, if the replacing player was another owner's
blocker, tying at T contributes the pair term in A0_i, while removing that
blocker never removes the earlier owner. If it was the owner, Never leaves
its distinct blocker finite. These facts establish(CC6) and(CC7), including
both exceptional boundary dates and all h>N.

An independent Fraction enumeration checked all48 recipient/deadline/Never
cases for N=7 on a four-player signed-own example with arbitrary signed
pair/triple/grand rows. Its singleton comparisons were mate3, other-1,
w_i=1/4 and beta=(2,3,0,1). Exact enumeration of the altered first coalition
agreed with(CC6) in every case. This finite test supplements the symbolic
partition, not a universal numerical inference.

There are at most two exceptional owner dates. The stated N bound gives
at least m/2 margin uniformly across every finite deadline and Never.
Every full behavioral replacement without access to the hidden tuple is
an independent mixture of these deadlines: the only nonabsorbed public
history is the all-Continue history. There is no recommendation-dependent
response or public revelation in this argument. Thus the source proves
FULL COARSE obedience exactly as stated, not informed correlated obedience
or obedience of the product of its marginals.

Both finite source clocks remain distinct, so every unilateral replacement
still absorbs by N. The asserted reward-column shift invariance is valid
for these comparisons even when own singletons have arbitrary signs.
The persistent TV example also checks: exactly-two-finite has probability1
under the source and4/9 under its product marginals, yielding TV>=5/9.

### Global LP and nearby-table selection

The dual signs are correct. Averaging c+sum lambda*gain>=h against the
strict source gives c-gamma*sum lambda>=E_sigma h. Since c<=1/2 and
h>=-1/2, sum lambda<=1/gamma. The same source lies in every sufficiently
large finite menu, and deadlines after that menu produce no new endpoint
payoffs. Neither a minimax interchange with the nonconvex product set nor
an independence recovery follows.

Reopened `StandardLCPSolution`, `IsStandardQMatrix` and
`isStandardQMatrix_reindexMatrix` in
`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`;
`StandardQMatrixSide` in
`UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`;
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`;
`exists_core_blocker_of_mem_normalCore` and `normalPlayerMatrix` in
`UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean`;
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`;
and `abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close` in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.
The normalized singleton matrix agrees with the literal comparisons through
`normalizedSoloMatrix_eq_projectiveLCPMatrix` in
`UniformEquilibrium/Quitting/Classification/LCP/Normalization.lean`.

These declarations justify precisely the composition used: perturb only
passive singleton coordinates, keep own singletons and all collisions fixed,
retain a positive full gap by the2Delta bound, make every off-diagonal entry
nonzero, and obtain strict NEGATIVE ROW blockers from the full normal core.
Standard Q at offset-minus-ones gives Gamma*x>=ones; a sufficiently small
positive perturbation of x gives a positive vector with positive image.
No negative-column substitution or original-table strictness assumption is
needed. The table is selected nearby, not strategically identified with
the original table or its fixed payoff target.

The correlation-distance equivalence in32.3 also checks. Mixing an
epsilon-Nash product with the strict source uses theta=epsilon/(gamma+epsilon)
and makes every coarse gain nonpositive. Its correlation distance is at
most(n+1)theta. In the reverse direction, prescribed and replacement payoff
comparisons each cost at most2R times TV, and opponent projection cannot
increase TV, giving full exploitability<=4R*TV. Independent finite-clock
approximation is valid even with positive Never mass: move only the finite
tail beyond the cutoff to Never; its mass tends to0. Thus the iff concerns
vanishing GLOBAL correlation minima, not a false exact attained product
claim. This is a sound selectable auxiliary source and dual bound, not a
new UE class or a contradiction to a positive original gap.

## Independent bounded falsification of Section33: all bounded public boundaries

Reviewed ONLY Section33 through EOF, at exact section SHA256
`3c69996874a8b28ff787f28c5c03cccf5132e91702b879b02e0588d3c9a5dd0c`.
This replaces, rather than endorses separately, the earlier near-own snapshot.
Verdict: PASS as ordinary mathematics. No unresolved mathematical objection
was found to the stated three-player whole-correspondence theorem. This is
not a Lean proof, a Fin4 padding result, or a uniform-equilibrium exclusion.

### Exact claim and agency checked

For the literal seven-row cyclic table with e=1/10, every fixed finite C
admits a positive c(C) such that EVERY exact independent Nash equilibrium
on EVERY finite clock menu with PUBLIC joint-Never payoff P in[-C,C]^3
has original joint-Never mass rho>=c(C). Every player's original full
complete-response debt is at least rho. No Nash-component, menu length,
payment sign, stationary law, symmetry, or subgame-perfect selection is
prescribed. The explicit near-own hazard bound is a corollary.

The suffix reduction does not silently import a zero-terminal theorem.
At a positive joint reach, replacing the player's conditional tail while
retaining its prefix law changes unconditional payoff by that reach times
the conditional-tail difference. The terminal P remains exactly P in the
shorter menu. Root Nash therefore follows from ordinary finite normal-form
Nash. Starting at date0, the sure-coordinate contradiction makes EVERY
subsequent reach positive. For q0=1, player1 strictly Continues, player2
strictly Quits, and player0 strictly Continues; rotation covers all labels.
No arbitrary annotation at a zero-reach history is used.

### Negative-budget and partial-support proof checked

I independently enumerated the actual raw opponent coalitions to recover
Q_i, B_i and Delta_i in(B4), including simultaneous quits. For a full root,
the sum of the three active equations gives sum q<=A(v-ones), despite
signed d=ones-v. Independently inverting the three-by-three circulant
operator gives the displayed positive D*A^-1, with column sums9/19;
the b coefficient has column sums10/19. Taking positive parts before
column summation is valid for SIGNED d. This yields(B7), not an assumed
lower-box invariant.

The scalar comparison is strictly below A except potentially at A=3;
equality there would require sum q=3 and is impossible. The compactness
step legitimately includes boundary supports: Delta=0 for EVERY player
still makes a root Nash when some q coordinates vanish. Its output equals
Q even for inactive indifferent coordinates. On A>=3/100 the denominator
is bounded away from0; at smaller A the explicit factor1/2 applies. Thus
the uniform kappa(B)<1 does not come from a noncompact interior graph.

For pair support01, the raw equations force signs positive at0 and negative
at1. Whatever the third output sign, ONLY the same pair remains eligible;
no single-owner root becomes eligible. The positive coordinate pays for
all b hazards by telescoping. The negative-budget decrease is at least a:
the old coordinate1 defect is3a/(1-a), its new defect is a, and coordinate2
can add at most a. For sole owner0 the own surplus is0, coordinate2 remains
strictly positive, and no other partial support is eligible. Its hazards
telescope against coordinate2's decrease. All-Continue roots may be
discarded because their output and budgets are unchanged. These facts
exclude arbitrary label renewal inside a partial episode; they do not
assume that finite player count alone bounds switches.

I additionally performed15000 independent exact Fraction raw-row tests:
5000 arbitrary interior q with their forced signed continuation vectors,
5000 arbitrary pair hazards and signed third continuations, and5000 sole
owner hazards with the required predecessor surplus. These check the
displayed endpoint identities and budget inequalities directly; the
symbolic and support arguments, not that sample, justify the quantifiers.

### Global composition, positive floor, and all original caps checked

Backward root composition starts at P. Each full root contracts A and
resets L to at most e times its incoming A. Partial negative charges
telescope globally; positive episode charges are bounded by the initial L
or a preceding full-root reset. This proves(B13) uniformly in the number
of dates. The entire root-Nash graph over the bounded actual-continuation
box is closed and compact, and the same sure-coordinate contradiction
excludes every q_i=1. Hence h(B)<1 is valid over ALL supports. The logarithmic
bound then gives a positive rho floor; boundedness of P is genuinely used.

The final original deviation is exact, not a cap-attainment limit: move
only one's private Never atom to dateN. Every prior finite absorption is
unchanged; on joint Never the player quits alone and gains its own1.
The gain is exactly rho, for EACH player, including original Never and
unrestricted complete-response agency. For the near-own corollary,
A0+L0<=3eta and sum full-root A<=2A0 give total hazard at most48eta/5,
so the claimed10eta and resulting original debt lower bounds follow.

Actual source declarations reopened for this check are
`quittingRootPayoff` and `quittingRootExpectedPayoff` in
`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/RootContinuation.lean`,
`timingLawTail_isNash_of_isNash_of_positiveContinue` in
`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineTimingRecursion.lean`,
and `quittingTerminalPayoff_moveNeverToFinite_sub_eq`,
`neverMass_mul_opponentNeverProduct_mul_singleton_le_terminalDebt`, and
`prod_stoppingLaw_none_mul_singleton_le_terminalDebt` in
`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`.
The arbitrary-P suffix transport is the direct proof above, not a claim
that the inspected zero-terminal recursion declaration has broader scope.

The whole bounded-payment exact auxiliary source is therefore retired on
this three-player table. Unbounded boundaries, genuinely approximate joint
profiles, arbitrary independent original clocks, and four-active games
remain outside this verdict. The older componentwise-above result is not
being promoted to a mixed-sign theorem by analogy.

## Independent bounded falsification of Section34

Verdict: PASS, ordinary mathematical review, not Lean checked. This review is
bound to Section34 through EOF, normalized with one trailing newline, SHA256
`ccc9474dcb9de1921349dcad7edacfb922433e491ada4f6fc77df334f2fafcf9`.
It is ONE check of the private-menu positive calibration, not a theorem of
arbitrary-table menu completeness or a new reward-class coverage audit.

### Claim checked

For the literal canonical Fin4 Section27 table, independently chosen finite
player-specific menus, EVERY one containing date0 and Never, admit selected
EXACT original-utility Nash components with original FULL gap bounded by
max(6 log(5/2)/k,12 theta^m). Their payoffs tend to the single fixed vector
(1,3/2,3/2,1), which is a uniform-equilibrium payoff against all complete
behavioral deviations. The simpler Section22 table has a selected component
with full debt(0,1/N,0,0). These are already-solved tables and calibrations of
a different exact-source operation, not new UE existence classes.

### Seed, chronology, and exact menu Nash

I independently recovered the displayed root endpoints from the seven core
rows. The first player1 coin has own singleton0 and own continuation0. At
the next joint02 coin, player0's endpoints are1+b and-b+(1-b)6x; player2's
endpoints are0 and5a-(1-a)2x. The choices of a,b equate both. The forced
player1 output is5b-2a+2ab, and independent symbolic simplification gives
(60x^2+128x-25)/(2(2x+5)(3x+1)); the stated positive root x makes it0.
The final player2 coin b/(2+b) produces exactly(1,v0,0), with v0>0.

For each rotating block I separately verified the three affine updates:
owner0 makes player1's value0; owner1 makes player2's value0; owner2 brings
player0's value back to1. The resulting recurrence is exactly
v'=125v/(39v+8). Inverting it gives the claimed contraction of1/v-1/3.
All scheduled owner coordinates equal their own singleton, and all endpoint
values in these cycles remain coordinatewise above the singleton floor.
Construction order is reversed physical chronology, consistently throughout.

Dilating a one-owner coin into k identical subcoins preserves both its
total survival and every endpoint. It also preserves the scheduled owner's
indifference at EACH subdate. Backward splicing is therefore valid against
every allowed pure deadline, including Never, not just the displayed hazard
choices. Private independent deadline laws realize the same hazards without
observing anyone's seed or using a public lottery.

At the first physical subdate the added date0 actions for ALL players are
actually checked. Player1's immediate Quit gives h, while Continue gives
v_m/2>=v0/2; condition(P7) suffices. Player2's immediate Quit gives0, while
its prescribed value is positive. Dummy3's Quit gives0, and Never gives a
positive probability of finite core absorption. Owner0 remains indifferent.
Thus date0 is not silently unavailable to nonscheduled players. All later
menu holes are genuine private action constraints in the finite source.

### FULL cap, Never, and the maximum ledger

For a root with actual continuation U and full original cap B, the exact
recursion is B'=max(Q, stopping_term+alpha B). Subtracting actual U' gives
d'=max(Q-U',alpha d). For the scheduled owner Q=U'; for any other core
player the exact raw pair values give Q<=s_i+6h and U'>=s_i. This proves
d'<=max(6h,alpha d). Since0<=alpha<=1, composition gives the MAXIMUM of the
common local ceiling and the deleted-survival multiple of the seed debt;
there is no hidden sum over dates. Each core player faces two other owners
per complete cycle, so their deleted-survival product is at most theta^m,
even after dilation. The seed cap/debt is bounded by12 from the raw bound6.
Never is included in the cap tail, whose full original best value is the
maximum of own singleton and0. Dummy3=Never is pointwise weakly dominant
against every complete dummy clock, and therefore has full debt0.

The partial initial block preserves the same ceiling and above-floor
property. Its exact output tends to(1,3/2,3/2), and the core Never probability
tends to0. Hence the dummy payoff tends to1. The target is fixed before
accuracy, rather than selected separately at each requested error.

For each chosen finite calendar, I checked the horizon argument separately
for deviations before its end and arbitrarily late deviations. Nonnegative
own-singleton payoffs are ESSENTIAL to the stated one-sided late-deviation
bound: on the opponents' Never event a truncated late singleton contribution
is no greater than the terminal one. The literal table has own vector
(1,0,0,0), so the hypothesis holds. Uniformity over pure deadlines passes to
their private mixtures and thus all complete behavioral replacements.

The Section22 uniform-clock example also checks directly: date0 is a legal
best reply for the pivot but need not be used; each nonpivot prefers Never
to its only allowed finite date0. Its ORIGINAL deadline payoff is exactly
a_i(t-1)/N+b_i/N for1<=t<=N, giving the claimed full gap at the endpoint.

### Source and scope

I reopened `isUniformEquilibriumPayoff_singletonArc_of_viable_proper` and
`IsProperViableSingletonFlowChain.isUniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/EssentialAPS/ProperSingletonFlowClosure.lean`.
Both require a supplied UE tail; they do not supply this finite private seed
or an arbitrary-table menu producer. The current proof instead discounts
the seed's possibly positive FULL debt by deleted survival. It does not infer
arbitrary-table completeness from this positive calibration, and does not
contradict any whole COMMON-menu tax/bonus obstruction.

No mathematical objection found in the stated scope. The genuinely missing
global step remains production of suitable player-specific menus and selected
components for arbitrary raw tables, or an ENTIRE-private-source falsifier.
