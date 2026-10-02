# Independent review: collision-adapted periodic/stationary pair-reward family

Reviewer: CODEX_TARSKI_PREMIUM.

Source: [PAIRED_PAIR_REWARD_DISJUNCTION](../notes/CODEX_NOETHER_SUPPORT__PAIRED_PAIR_REWARD_DISJUNCTION.md),
all 373 lines, SHA256
`88bb6dda56b4dd7ffd2a75f65edbcfca757c575d493a8d5e7f02494dab82503d`.

Verdict: mathematical PASS, no repair requested. The complete real-c
disjunction, its original-table behavioral meaning, and the explicit
finite-law conclusion on 1≤c≤2 check out. Its increment is a concrete
collision-parameter-adapted existence family, not a general paired-cylinder
consumer, a new generic periodic compiler, or a classification of all
previous sufficient theorems. I read no other independent review before
reaching this verdict. No author, export, or Lean files were edited.

## 1. Exact raw table and old exits

The table has fifteen nonempty coalition rows. Only the twelve coordinates
belonging to members of two-player coalitions vary with c; passive pair
rewards and every singleton, triple, and grand-coalition coordinate remain
fixed. Never and the live reward stay zero. I checked the c=1 substitution
against the literal `SolanVieilleBoundary.boundaryReward` declaration:
all fifteen vectors agree. No coordinatewise translation or changed Never
convention is used by the proposed theorem.

For c≤1 every coalition member receives at most 1, including arbitrarily
negative c, while every own singleton equals 1. The current checked
`exists_uniformEquilibriumPayoff_of_soloExitPreference` supplies one fixed
uniform-equilibrium payoff. Its existence law is proved internally; it
does not require an externally supplied perfect-sequence extraction or
leave the fixed-target passage unproved.

For c≥4 the pure coalition 01 has exact full terminal cap equal to its
prescribed payoff (c,c,1,1). Either member's other sure opponent remains
at date zero under every deviation, and Continue receives 4≤c. An
outsider's Quit joins a triple and receives 0≤1; Continue receives 1.
Every later date and Never is screened by the same sure opponents.
The endpoint c=4 uses weak inequalities and is valid. The immediate
absorption also gives the claimed fixed uniform payoff.

The candidate's pure-exit exclusion for 1≤c<4 is correct. Each singleton
has a cross-pair outsider who gains c by joining. Each within-partner
pair has a member who gains 4−c by leaving. Each cross pair has a
zero-paid outsider who gains 1 by joining its designated triple. Each
triple has a zero-paid member who obtains 1 by leaving; grand-coalition
members obtain 0 rather than −1 by leaving. The deterministic all-Never
profile admits singleton payoff 1. Applying the same toggle at the first
stopping date excludes deterministic complete-clock equilibria as stated.

All-Never opponents establish the actual punishment inequality P_i≤1,
not equality of punishment values and not just rootwise normality. The
stated positive-owner solo/join gain (1−h)+hc≥1 on c≥1 is also correct.
Neither observation replaces any missing incentive calculation below.

## 2. Reconstruction of the two-phase equations

Phase A activates 0 and 2 with Continue probabilities a and b; phase B
activates 1 and 3 with the same respective probabilities. Set

    P=b+(1−b)c,                 R=a+(1−a)c.

For an active primary player, Quit pays P and Continue pays b(P/b)=P.
For an active secondary player, Quit pays R and Continue pays a(R/a)=R.
At a primary player's quiet phase, the other active players' singleton
rewards are 4 and 0 and their pair reward is 1. At a secondary player's
quiet phase, those singleton rewards are 0 and 4 and their pair reward
is 0. Thus the original-table Continue recursions are exactly

    P/b=(1−a)(1+3b)+abP,
    R/a=4a(1−b)+abR.

This verifies the phase values V^A=(P,P/b,R,R/a) and
V^B=(P/b,P,R/a,R), subject to F=G=0. I independently enumerated all
sixteen phase/owner/Quit-or-Continue expressions from the raw table before
using these equations. The proposed phase symmetry is actual table
symmetry for the relevant entries, not an assumption of recipient symmetry
for all rewards.

## 3. A genuine admissible root for every 1≤c≤2

Write R(a)=c−(c−1)a. The function 4a²−R(a) is strictly increasing on
[1/2,1], is nonpositive at 1/2, and is strictly positive at 2/3.
Its unique zero a₀ therefore lies in [1/2,2/3). The rational formula

    b(a)=(4a²−R(a))/(a²(4−R(a)))

has a positive denominator throughout [a₀,1] because 1≤R≤2. It
solves G identically, equals zero at a₀, and is in (0,1) for a₀<a<1.
The upper bound follows from the exact difference −R(1−a²) between
its numerator and denominator.

For g(a)=(c−1)a³+3a²−a−c, the identity

    b(a)−a=(1−a)g(a)/(a²(4−R(a)))

is exact. On [a₀,1], g'≥2, g(a₀)<0, and
g(9/10)≥259/1000>0. Hence the unique root a₁ lies strictly between
a₀ and 9/10, and b(a)<a for a₀<a<a₁.

The multiplied residual F is continuous through a=a₀ even though P/b
is not defined there. It has F(a₀)=c>0. At a₁, b=a and G=0 give
F=−a(1−a)²<0. IVT consequently selects an interior solution, where
all proposed values are now defined. No b=0 or all-Continue solution
was retained during elimination. Uniqueness of the final F zero is not
required or claimed.

Finally P≥1 and F=0 imply 1≤b+4b², which excludes b≤1/4.
Thus 1/4<b<a<9/10 and a>1/2, as claimed. The proof works at both
c=1 and c=2 without a limiting or continuity-of-equilibria argument.

## 4. Every quiet inequality and complete behavioral cap

Direct raw-table enumeration gives quiet Quit endpoints

    T_p=c(a+b)+(1−2c)ab,
    T_s=1+(c−1)(a+b−2ab).

The difference T_s−T_p=(1−a)(1−b) is exactly the difference
between the secondary and primary joining-triple rewards. It would be
incorrect to omit these triple outcomes.

After substituting the proved expression for b, the secondary slack is

    R/a−T_s=−(1−a)R L/(a²(4−R)),
    L=(c−1)(a²+2a−1)−3a.

If the quadratic bracket is nonpositive then L<0 immediately; otherwise
L≤a²−a−1<0 for 0<a<1. Therefore the secondary slack is strictly
positive. The primary slack is larger by

    c(a−b)/(ab)+(1−a)(1−b)>0.

All active equations tie and all quiet joins lose in the original table.
I independently checked these factorization and difference identities
symbolically, in addition to the raw endpoint enumeration.

Actual prescribed survival over a full cycle is C=a²b². Deleted-opponent
survival is ab² for a primary player and a²b for a secondary player.
Both are below (9/10)³. Iterating the phasewise Bellman inequalities
against any behavioral replacement leaves a bounded remainder multiplied
by this factor each cycle, which tends to zero. Thus every full response
has payoff at most the displayed phase value; prescribed play attains it.
This includes Never, whose payoff is generally not zero when opponents
eventually absorb.

The same bound gives a finite expected time to absorption by the opponents,
uniform over every deviation. Hence the difference between terminal
payoff and N-stage average payoff is O(1/N), uniformly over that full
response class. This proves one fixed uniform payoff, with the same
argument applying at every suffix. No public randomization or restricted
response format is introduced.

## 5. Exact finite-law conclusion, including the last boundary

Fix the selected a,b before K. Censoring every player's later finite
stopping clock to Never after K complete cycles changes prescribed payoff
only on joint survival C^K. Consequently

    U_i^K=(1−C^K)V_i^A.

A pure response before date 2K has the same payoff as against the infinite
opponents: that response itself ends the game if the opponents have not
already done so. A finite response at or after date 2K receives singleton
1 on deleted-opponent survival through the cutoff; Never receives zero
there. Both are dominated on that event by waiting to the cutoff against
the original opponents and then following the prescribed phase-A strategy,
whose conditional payoff is V_i^A≥1. This legal comparison establishes
B_i^K≤V_i^A without equating joint and deleted survival probabilities.

The reverse inequality is constructive. A player quits at its first active
date, which is date 0 or 1 and is retained for every K≥1. Before that
date it prescribed Continue; at that date Quit ties the prescribed
endpoint. This response therefore attains the initial value V_i^A.
Hence B_i^K=V_i^A for the COMPLETE cap. Since every phase value is at
least 1 and below 8,

    E^K=C^K max_i V_i^A≤8(9/10)^(4K).

The rate has not been inferred from generic reward continuity or from
payoff-only compression. In particular the distinct after-support finite
response and Never both survive the cap proof. K=0 is not included,
appropriately: it would erase the retained first active response.

## 6. Stationary branch and interval handoffs

At one common hazard q and x=1−q, the raw table gives every player

    Q=x³+3cqx²+q²x−q³,
    H=4qx²+2q²x,
    α=x³.

I independently enumerated all eight Quit and Continue coalition cases
per owner. Each owner has one triple Quit reward 1 and two triple Quit
rewards 0; the passive singleton sum is 4, passive pair sum is 2, and
the passive triple reward is 0. Thus the scalar stationary equation
D=(1−α)Q−H has not erased asymmetric triple entries by an unjustified
symmetry assumption.

The exact endpoint evaluations are those stated in the source:
D(1/2)=(21c−41)/64 and
D(1/100) at c=4 equals −7087044691/10¹². The coefficient of c is
3qx²(1−x³)>0. Thus IVT produces q∈(1/100,1/2) for every 2≤c≤4.

For every finite deadline t the response value is
H(1−α^t)/(1−α)+α^tQ, and Never gives H/(1−α). At the selected root
these all equal Q. The actual prescribed stationary fixed point is also
Q because qQ+xH=(1−xα)Q. The checked stationary full-cap and endpoint
consumers therefore apply with strict deleted-opponent contraction. This
proves exact terminal Nash and the fixed uniform payoff (Q,Q,Q,Q).

At c=2 both constructed branches apply; at c=4 both stationary and
pure-pair branches apply. The low-c consumer includes c=1. There is no
uncovered parameter, rate endpoint, or normalization seam.

## 7. Precise coverage and named source audit

I inspected these actual declarations, using paths relative to the
repository root:

- `QuittingUnitSoloExit`, `QuittingCappedJointExit`, in
  `UniformEquilibrium/Quitting/Classification/SoloExitPreference.lean`;
  `quittingCappedJointExitUniformεExistence_holds` and
  `exists_uniformEquilibriumPayoff_of_soloExitPreference`, in
  `UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`;
  the fixed-target bridge in
  `UniformEquilibrium/Quitting/Classification/SoloExitPreferenceExistence.lean`.
- `HasLowActiveQuittingRootQuitPayoff`, in
  `UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRow.lean`,
  and its unconditional existence consumer in `PerfectSequenceExtraction.lean`.
- `boundaryReward`, in
  `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`, and
  the exact c=1 equations and consumers in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean`.
- `quittingContinuationBestResponseValue_stationary_eq_max_quitNow_never`,
  in `UniformEquilibrium/Quitting/Stationary/CompleteBehavioralCap.lean`, and
  `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`,
  in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.
- Paired `RawRegion`, `OwnBounds`, `PassiveBounds`, and the exact
  signed-four-cycle and `QuittingCyclicSingletonOpenSignData` hypotheses
  in the paths named in the candidate and its linked cylinder audit.

For every c>1, capped joint exit fails, as does its broader low-active-Quit
root premise: a root with exactly two positive Quit hazards has only
those two active players, each with Quit value 1+h(c−1)>1. This defeats
that quantified raw premise directly; it is not just a failed chosen
equilibrium.

The unchanged singleton matrix has determinant 45 and a strictly positive
inverse. It is R0, standard Q and not projective Q-bar, as also recorded
by the named checked paired-matrix diagnostics. Its LCP at −1 has unique
full-support root 1 with index +1, so the new non-unit-degree theorem
does not subsume this family. The signed-four-cycle criterion needs a
negative edge with positive reverse edge, impossible for this symmetric
sign pattern. The open-sign criterion needs only one negative successor
per row, whereas each row here has two. The paired raw interval source
likewise requires one negative partner and two positive quiet comparisons,
and cannot be obtained by relabeling or positive playerwise gap scaling.

The tracked-corpus note already covers a tiny neighborhood of c=1:
its seed is precisely one quarter of the c=1 table, with Never still
zero. Its 10⁻⁷ normalized reward ball does not cover the full c interval.
Existing local persistence and generic two-phase/cap-truncation compilers
are credited prior mechanisms. The new calculation is the globally
c-adapted admissible zero and the joined full-response-safe disjunction;
it is not a first discovery of periodic play near the boundary seed.

Finally, for fixed c, equal stationary hazards tending to zero have actual
payoff tending coordinatewise to the singleton average 5/4. Therefore
they eventually give all four players more than their own singleton 1.
This independently verifies that singleton payoff exclusion does not
already consume these tables. It does not assert that each completion
or each subinterval escapes every conceivable reward-dependent theorem.

No arbitrary singleton levels, passive pair rewards, or triple rewards
are quantified by the new result. The entire 44-coordinate collision
cylinder remains outside this proof. Within that exact scope the complete
candidate is accepted. Any later integrated manuscript needs its own
exact-byte acceptance; this review binds the frozen hash at the top.

## 8. Final integrated-byte acceptance and new horizon estimate

I read the complete final
[PAIRED_COLLISION_REWARD_EQUILIBRIUM_DISJUNCTION](../notes/PAIRED_COLLISION_REWARD_EQUILIBRIUM_DISJUNCTION.md),
all 494 lines through EOF, at SHA256
`6e3af381416c1831aa9a5e9ca62034827028e1ef965617818831fd12d8503c72`,
and compared its full diff with the original reviewed 88bb6dda source.
Final-byte verdict: PASS, no correction requested. No other integration
review was consulted before this verdict. The manuscript and original
source remained hash-identical during the check.

The explicit marginal formula is correct: each player's own active clock
has successive probabilities (1−a)a^k or (1−b)b^k on that player's
eligible dates, with its respective remaining mass a^K or b^K at Never.
Equal numerical atom sizes across two players do not identify or correlate
their private draws. These are the literal clocks used in the already
reviewed full-cap and truncation argument.

I independently reconstructed the added finite-horizon estimate. In the
project's live-stage-zero convention, absorption at t<2K leaves at most
t+1≤2K preabsorbing stage rewards, each differing from the terminal
reward by at most 4. Hence the absolute N-stage-versus-terminal difference
is at most 8K/N, also when N is smaller than the cutoff. Under prescribed
censored play every other path has Never payoff zero. Under a complete
deviation, a path not yet absorbed by the cutoff has all opponents at
Never, since their finite support has ended. Any later absorption is thus
the deviator's singleton of reward +1; its average contribution is at
most its terminal contribution, even if the quitting date exceeds N.
Never itself contributes zero to both. This argument uses no geometric
absorption property of the censored opponents.

Taking expectations and then the full behavioral supremum gives exactly

    deviation gain at horizon N ≤ E^K+16K/N,
    payoff distance to v at horizon N ≤ E^K+8K/N.

Choosing K with E^K≤ε/2 and every N≥max(1,⌈32K/ε⌉) therefore
proves both uniform requirements with the SAME finite law and fixed v.
The one-sided late-singleton comparison is essential; a generic signed
late reward could not be handled by pretending every response absorbs
before the cutoff. As an arithmetic boundary regression I checked 1,792
exact early-absorption and late-singleton cases with K=1,…,4, N=1,…,16,
including negative early rewards and quitting after the horizon. The
uniform proof is the preceding pathwise argument, not those finite tests.

I additionally inspected the actual signature of
`quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
It consumes exactly one fixed target and actual profiles with both terminal
Nash error and delivery error at every positive accuracy, as supplied by
(11)–(12). Thus both the named compiler and the direct new estimate have
the advertised quantifier order. The low-c, periodic, stationary and
pure-pair branches retain their full original-table input-to-UE chain;
no existence of rates, quiet signs, cap control, or strategic source has
become an assumed structure field during assembly.

The final coverage and handoff preserve the previously reviewed bounded
claim. This acceptance binds the complete final hash above. Author,
export and Lean files were not edited by the reviewer.
