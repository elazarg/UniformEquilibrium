# Independent audit of the pair-member reward disjunction

Reviewer: CODEX_RADO_BOUNDARY.

Verdict: PASS as ordinary mathematics using the existing capped-joint
existence theorem for c ≤ 1. No unresolved mathematical objection was found.
The constructed periodic and stationary profiles are verified against the
full behavioral deviation class, including Never. The finite-law statements
are also valid, including responses after their retained support.

Reviewed source:
[CODEX_NOETHER_SUPPORT__PAIRED_PAIR_REWARD_DISJUNCTION.md](../notes/CODEX_NOETHER_SUPPORT__PAIRED_PAIR_REWARD_DISJUNCTION.md).

Exact SHA-256:
`88bb6dda56b4dd7ffd2a75f65edbcfca757c575d493a8d5e7f02494dab82503d`.

I read all 373 lines and checked the hash before and after the substantive
audit. I did not consult any other review or verdict of this candidate.
This is a source-level mathematical audit and exact symbolic verification;
no Lean build was run and no author, Lean, or export file was edited.

## 1. Exact claim and original table

For each real c, the candidate specifies one four-player quitting table.
Only the twelve reward coordinates paid to members of two-player quitting
coalitions vary with c. Every singleton, every passive pair coordinate,
every triple, and the grand-coalition vector is fixed as displayed. Live
play and Never pay zero. Players randomize independently and can condition
their behavior on the public history; a deviation replaces the player's
entire strategy. The assertion is one fixed uniform-equilibrium payoff for
each fixed table, before the accuracy is chosen.

I compared every displayed row with `SolanVieilleBoundary.boundaryReward`,
in `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`.
At c = 1 the table agrees exactly. For general c, precisely the twelve
pair-member coordinates differ. The singleton-difference matrix, using
recipient rows and quitter columns, is therefore exactly

    [ 0  3 −1 −1 ]
    [ 3  0 −1 −1 ]
    [−1 −1  0  3 ]
    [−1 −1  3  0 ].

The theorem does not quantify over arbitrary passive rewards or arbitrary
nonsingleton completions of that matrix. Its disjunction covers all real
c through the overlapping ranges c ≤ 1, [1,2], [2,4], and c ≥ 4.

## 2. Admissible periodic rates are actually produced

Fix 1 ≤ c ≤ 2. With R(a) = c−(c−1)a, the equation 4a² = R(a) has
its specified root a₀ in [1/2,2/3). On this interval and above it, the
derivative of 4a²−R(a) is positive. The two endpoint signs in the candidate
are correct, including c = 1, where a₀ = 1/2.

On [a₀,1], R lies between 1 and 2 and a is positive, so

    b(a) = (4a²−R)/(a²(4−R))

has no denominator zero. It is continuous, satisfies G = 0 identically,
has b(a₀) = 0, and satisfies 0 < b < 1 for a₀ < a < 1. The latter
upper bound follows from the exact numerator difference −R(1−a²).

The identity relating b−a to g is correct. At a₀, g is negative;
on [a₀,1] its derivative is at least 2. At 9/10,

    g(9/10) = (801−271c)/1000 ≥ 259/1000 > 0.

Thus a₁ is well defined with a₀ < a₁ < 9/10, b(a₁) = a₁, and
0 < b(a) < a on the open interval between them. This step does not
need monotonicity of b itself.

The multiplied residual F is continuous even at b = 0. It equals c > 0
at a₀. At a₁, equality P = R and G = 0 give exactly

    F = −a₁(1−a₁)² < 0.

The intermediate value theorem therefore selects an interior root of F
with G = 0 and 0 < b < a < 9/10. Division by b occurs only after this
selection, so neither b = 0 nor the all-Continue solution is retained.
The displayed inequality 1 ≤ b+4b² excludes b ≤ 1/4. Also a > a₀ ≥ 1/2.
No uniqueness of the selected F root is required.

All rate choices depend only on c. They do not depend on the truncation
length, accuracy, or horizon. This proves the required producer rather
than verifying a supplied solution.

## 3. All sixteen original-table endpoint identities

I independently enumerated each opponent Quit subset for every player in
both phases, using the literal table. Exact symbolic arithmetic verified
all sixteen Quit/Continue endpoints before imposing F = G = 0.

For active primary players the Quit endpoint is
P = b+(1−b)c, and their Continue endpoint is b(P/b) = P.
For active secondary players the corresponding endpoints are
R = a+(1−a)c and a(R/a) = R. There is no missing passive singleton
reward in these active comparisons: the active cross opponent's singleton
pays the queried player zero.

For quiet primary players, continuation gives

    4(1−a)b + (1−a)(1−b) + abP
      = (1−a)(1+3b)+abP.

For quiet secondary players it gives 4a(1−b)+abR. The different passive
pair rewards, respectively 1 and 0, are essential and have been used
correctly. Equations F = G = 0 identify these expressions with P/b and R/a.

The immediate joining endpoints are also correct:

    T_p = c(a+b)+(1−2c)ab,
    T_s = 1+(c−1)(a+b−2ab).

In particular the quiet joining triple pays 0 for each primary player
and 1 for each secondary player. Replacing all those triple rewards by
one common value would invalidate the calculation; the candidate does
not make that replacement.

I checked the secondary slack factorization and the slack difference
symbolically. All denominator factors are positive. If a²+2a−1 is
nonpositive, L < 0 follows immediately from −3a; otherwise c−1 ≤ 1 gives
L ≤ a²−a−1 < 0. Therefore S_s > 0. The identity

    S_p−S_s = c(a−b)/(ab)+(1−a)(1−b) > 0

then gives S_p > 0. Thus every active pair of endpoints ties and all
four quiet Continue endpoints strictly dominate immediate Quit.

## 4. Full behavioral and uniform-horizon conclusions

The prescribed two-phase Bellman recursion has full-cycle continuation
C = a²b² < 1. Iteration makes its bounded remainder vanish and identifies
the candidate's phase vectors with actual terminal payoffs. They were
not merely guessed annotations accepted without payoff delivery.

For any queried primary player, its three opponents survive a full cycle
with probability ab²; for a queried secondary player that probability is
a²b. Each is strictly below ρ = (9/10)³. These survival bounds remain
valid under every behavioral replacement of the queried player, whose
actions cannot delay an opponent's first Quit. The one-stage endpoint
inequalities can therefore be iterated under any such strategy. The
bounded conditional continuation remainder is multiplied by a probability
tending geometrically to zero. This proves the global terminal cap at
the displayed phase value. Prescribed play attains the value.

This argument includes arbitrary dates, history-dependent behavior, and
Never. Against the absorbing opponents, Never generally has a nonzero
payoff; the proof bounds that actual payoff through the same telescope.
It neither inserts a zero Never value after opponents absorb nor assumes
the deviator is periodic.

For the infinite profile, the mean time to the first opponent Quit is at
most 2/(1−ρ), uniformly over the deviator. With reward magnitude at most
4 in this parameter range, the expected difference between terminal reward
and the N-stage average is at most 8/[N(1−ρ)]. The same estimate applies
to prescribed play and to every complete deviation. Combining the two
estimates with exact terminal Nash gives a uniform finite-horizon Nash
bound tending to zero and payoff delivery to the same fixed initial
vector v = V^A. Phase shifts have the same full-cycle contraction, so the
suffix statement is also valid.

## 5. Censored finite laws, including the late response menu

Independent censoring after K complete cycles retains each player's
geometric atoms on its active dates below 2K and puts the remaining
mass at Never. This remains a product of legal individual stopping laws;
it neither conditions jointly on survival nor adds shared randomization.

Renewal at date 2K gives

    U_i^K = (1−C^K)v_i.

The finite-law full-cap proof survives the late-date test. A deterministic
response before 2K has exactly its infinite-opponent payoff, because play
has absorbed by that response's date. For a response at or after 2K,
condition on opponents surviving to the cutoff. The censored opponents
then all Continue forever, so a finite response gives the queried player
its own singleton 1 and Never gives zero. Waiting until that cutoff
against the infinite opponents and resuming prescribed play gives
conditional value v_i ≥ 1 at the same phase A. Before the cutoff the
two experiments coincide. The latter is a legal infinite-game deviation
and has payoff at most v_i by the full cap already proved. Thus every
late finite response and Never is bounded by v_i as well. Mixtures of
pure stopping times, or the equivalent complete behavioral strategies,
preserve the inequality.

Conversely, the first active date is 0 or 1 and is retained for K ≥ 1.
The queried player prescribes Continue before that date, and the active
Quit endpoint is a tie. Quitting exactly then attains the initial value
v_i. This proves the exact equalities

    B_i^K = v_i,       E^K = C^K max_i v_i.

Every phase coordinate is at least 1; P,R ≤ 2, b > 1/4, and a > 1/2
give max_i v_i < 8. Since C < (9/10)⁴, the claimed bound
E^K ≤ 8(9/10)^(4K) follows, together with the same delivery bound
|U_i^K−v_i| ≤ 8(9/10)^(4K).

These finite laws also have the appropriate fixed-target consumer.
`quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance`, in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`,
accepts precisely terminal Nash error and terminal payoff distance tending
to zero at one fixed target. I checked its actual declaration and its
strict-error terminal-to-uniform step. The bounds above supply its
hypotheses with the original v, without selecting a different target.

For clarity, the infinite opponents' geometric absorption estimate should
not be applied after censoring: the finite laws have positive Never mass.
The candidate does not require that false extension. A direct one-sided
finite-horizon check is available as well. Absorption before 2K contributes
at most 8K/N payoff error. On the remaining event a deviator can only
receive its nonnegative singleton reward or Never, so its finite average
does not exceed its terminal payoff there. Consequently finite-law Nash
gain is at most E^K+16K/N, and delivery error to v is at most
C^K max_i v_i+8K/N. Selecting K first and then a horizon threshold proves
the same fixed-payoff conclusion.

## 6. Stationary and pure exits, including boundary parameters

I separately enumerated all eight opponent outcomes for all four players
at a common stationary hazard q. Each Quit menu has singleton reward 1,
three pair rewards c, one triple reward 1, two triple rewards 0, and grand
reward −1. The Continue singleton sum is 4, pair sum is 2, and triple
reward is 0. This verifies all eight owner-specific formulas for Q and H.

Exact calculation gives both signs displayed in the candidate:

    D(1/2) = (21c−41)/64,
    D(1/100) at c = 4 equals −7087044691/10^12.

For 2 ≤ c ≤ 4, the first is at least 1/64. The coefficient of c in
D(q) is strictly positive for 0 < q < 1, so the second test is a valid
negative upper bound for the whole interval. The intermediate value
theorem gives an interior q with H = (1−α)Q.

For every finite deadline t the payoff is
H(1−α^t)/(1−α)+α^tQ; Never gives H/(1−α). At the selected root
these all equal Q. The same Bellman inequality controls every behavioral
replacement. Substitution in the prescribed Bellman recursion gives the
same payoff Q. Opponents contract at α = (1−q)³ < (99/100)³.

The actual declarations
`quittingContinuationBestResponseValue_stationary_eq_max_quitNow_never`, in
`UniformEquilibrium/Quitting/Stationary/CompleteBehavioralCap.lean`, and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`, in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`, have exactly
these full-response and fixed-target meanings. Their hypotheses are
satisfied by this constructed root and value, with no payoff shift or
extra sign assumption.

For c ≥ 4, the pure date-zero pair 01 is also valid. Continuing gives a
member 4 from the other sure quitter, while joining gives either outsider
0 from its triple instead of its prescribed passive payoff 1. Another
sure player screens every possible later response, including Never. The
target is (c,c,1,1).

All interval edges are covered: c = 1 is both the existing boundary-table
case and an admissible periodic construction; c = 2 satisfies both the
periodic and stationary constructions; c = 4 satisfies the stationary
construction and the pure pair with equality in the member's Continue
comparison. Negative c is handled only by the existing capped-joint
consumer, without extrapolating any new formula.

The claim of no deterministic terminal equilibrium for 1 ≤ c < 4 also
survives direct testing. Singletons admit a cross-pair join; within-partner
pairs admit a profitable member leave; each cross pair has an outsider
with passive reward 0 whose joining triple pays 1; triples have a
zero-paid member who obtains at least 1 by leaving; and a grand-coalition
member can leave from −1 to 0. These toggles can be made at the earliest
deterministic stopping date. All Never admits singleton payoff 1.

## 7. Existing-source overlap and remaining scope

The low-c exit is unconditional at its actual declaration.
`QuittingUnitSoloExit` and `QuittingCappedJointExit`, in
`UniformEquilibrium/Quitting/Classification/SoloExitPreference.lean`, require
own singleton 1 and member reward at most 1. Every row of this table has
those properties for c ≤ 1, including arbitrary negative c.
`exists_uniformEquilibriumPayoff_of_soloExitPreference`, in
`UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`,
takes just those table hypotheses. Its body supplies
`quittingCappedJointExitUniformεExistence_holds` internally to the fixed-target
bridge in `SoloExitPreferenceExistence.lean`. The conditional interface in
that latter file is not being mistaken for an unconditional proof on its own.

For c > 1, capped joint exit fails. The broader
`HasLowActiveQuittingRootQuitPayoff`, in
`UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRow.lean`,
also fails: take exactly two active players with positive hazards. Every
active owner's Quit endpoint is strictly above 1; inactive players cannot
witness that predicate. This is an actual counterexample root to its
universal quantifier.

I inspected the c = 1 declarations `periodTwoProfile_isExactTerminalNash`
and `periodTwo_isUniformEquilibriumPayoff`, in
`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean`.
They use the literal fixed boundary table. The candidate reduces to their
active equations at c = 1 but makes no assertion that they already quantify
over c. The general two-phase strategy compiler and finite truncation
method are correctly credited as existing machinery.

The named paired raw region has the opposite singleton sign count from
this table. Its `OwnBounds` and `PassiveBounds`, in
`MathUE/PairedAffineIntervalEstimates.lean`, require one low partner and
two high quiet singleton rewards relative to the own singleton. Here
each recipient has one high partner and two zero cross rewards. The
definitions in `UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`
therefore do not apply under any relabeling; passive pair adjustments
cannot repair those singleton inequalities. The credited asymmetric
paired-region note has those same explicit interval premises.

`SignedFourCycleSingletonData`, in
`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`, needs
a negative successor edge with positive reverse edge. Every edge of the
present singleton matrix has the same sign as its reverse.
`QuittingCyclicSingletonOpenSignData`, in
`UniformEquilibrium/Quitting/Cycles/CyclicSingletonOpenSignProducer.lean`,
requires at most one negative forward comparison in each row, whereas
these rows have two. These bounded source exclusions are valid.

The cited tracked-corpus note explicitly supplies only fixed small reward
balls. Its radius 10^−7 around the normalized c = 1 seed does not cover
the whole new interval. No claim of worldwide novelty or exclusion from
every conceivable derived consumer is justified or made here. The paper
lane was used for bounded source orientation through
`Literature/SolanAndVieille2001.lean`; the low-c proof dependency used in
this review is the actual production theorem, not a paper claim or an
unbuilt transcription.

The accepted contribution is the c-dependent IVT construction and its
verified joining slacks, composed with the stationary and existing exits
to cover this literal one-parameter family. It provides no result for
the arbitrary 44-coordinate collision cylinder. The concrete remaining
check is final-packet integration at its eventual frozen bytes; this
candidate requires no mathematical repair before that check.

## 8. Exact final-byte integration acceptance

Final packet:
[PAIRED_COLLISION_REWARD_EQUILIBRIUM_DISJUNCTION.md](../notes/PAIRED_COLLISION_REWARD_EQUILIBRIUM_DISJUNCTION.md).

Accepted final SHA-256:
`6e3af381416c1831aa9a5e9ca62034827028e1ef965617818831fd12d8503c72`.

Verdict: PASS. I read all 494 final lines and checked them against the
independently reviewed original, whose hash remains
`88bb6dda56b4dd7ffd2a75f65edbcfca757c575d493a8d5e7f02494dab82503d`.
No mathematical repair is required at these final bytes. I did not consult
the other review or its verdict; checking that its link target exists was
only a filesystem integrity check.

The final statement specifies the literal fifteen-row table, independent
private behavioral randomization, complete unilateral replacements, the
actual terminal payoff and full cap, and the fixed-target/all-later-horizon
quantifier order. The only varying data are c and the twelve corresponding
pair-member rewards. The four parameter ranges still cover every real c.
The periodic rates and stationary hazard are produced by the proved IVT
arguments, and the active/quiet incentives and full caps remain conclusions
of the proof. No favorable continuation, supplied equilibrium, or open
strategic producer assumption has been introduced.

The low-c dependency remains the actual unconditional
`exists_uniformEquilibriumPayoff_of_soloExitPreference`, in
`UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`.
As checked above, that theorem internally supplies the existence law to
the conditional interface in `SoloExitPreferenceExistence.lean`. Thus the
assembly does not accidentally export a result conditional on an unproved
extraction law. The other three parameter ranges have complete constructions
and their original-game consumers in the packet.

The new marginal formulas are exactly the independent censored geometric
laws of the periodic profile. For players 0 and 1, the first K active-date
atoms have masses (1−a)a^k and sum to 1−a^K; their offsets are respectively
0 and 1. Players 2 and 3 have the analogous masses (1−b)b^k and the same
respective offsets. The declared Never masses complete each distribution
to one. Equality of atom probabilities between two players does not couple
their random draws, as the text explicitly states. K ≥ 1 retains every
player's first active date, so the exact cap-attainment argument survives.

The added finite-horizon proof is also correct. If absorption is at a
retained date t < 2K, the number of initial zero-reward stages is at most
2K, accounting for the absorbing reward starting at the successor state.
The reward magnitude is at most 4 throughout the periodic interval, so
the pathwise terminal-to-average error is at most 8K/N. Under prescribed
censored play, every other path remains Never with reward zero. Under a
unilateral deviation, absence of retained-date absorption means that all
opponents continue forever thereafter; any later absorption is a singleton
of nonnegative reward 1. Its finite average is at most its terminal reward.
This is exactly the required one-sided estimate, not an unjustified
absolute convergence claim for the censored opponents.

Combining the uniform one-sided deviation bound with prescribed delivery
gives Nash error at most E^K+16K/N. Because the fixed-target terminal
delivery error equals E^K, finite-average delivery error is at most
E^K+8K/N. With E^K ≤ ε/2 and
N ≥ max(1,ceil(32K/ε)), these are respectively at most ε and 3ε/4.
The same K-dependent censored law therefore works for every such N and
every behavioral deviation at the previously fixed v. This directly
establishes the semantic conclusion; the named terminal-target acceptance
consumer provides a second valid route.

The stationary and pure-pair handoff retains its exact table endpoints,
opponent contraction, Never comparison, and overlap at c = 2 and c = 4.
The low-c exit covers arbitrarily negative c without extrapolating the
periodic or stationary formulas. The source comparison remains bounded
to named hypotheses and credits the existing local persistence and
periodic compilation results. The handoff requests proofs of rates,
incentives, and complete caps instead of placing them in assumed fields.
It neither adds an arbitrary 44-coordinate cylinder nor claims a general
strategy-selection procedure.

All five Markdown link targets resolve from both the current notes
location and the intended exports location. The comparison links point
to retained notes, and both feedback targets exist. No content from the
second feedback file was read. The final manuscript distinguishes ordinary
mathematics from Lean verification and needs no conditional-export exception:
it proves raw c-table input to actual rates and profiles to full fixed UE.
This is final-hash acceptance of that unconditional one-parameter theorem.
No author, export, or Lean file was edited during this gate.
