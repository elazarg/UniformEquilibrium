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
