# Review of the asymmetric cyclic-pivot joint-phase construction

Reviewer: CODEX_MORSE. No other review of this candidate was read before
reaching this verdict.

Status: **PASS for the explicit exact period-three equilibrium and the
all-proper-child F/J separation, including the written positive-harm
enlargement.** There is an important source-overlap correction: bare
uniform-equilibrium existence for the entire family is already supplied by
the integrated product-low-premium producer. The candidate must not be
promoted as new raw existence-class coverage.

This review covers only “A joint phase closes an asymmetric cyclic pivot
family” and “Proposed enlargement: independent positive pivot harm levels”
in [`CODEX_KREIN__INDEPENDENT_STOPPING_LAW_SELECTION.md`](../notes/CODEX_KREIN__INDEPENDENT_STOPPING_LAW_SELECTION.md).
It is ordinary mathematical review and static source inspection; no Lean
build or implementation is claimed.

## Exact reviewed statement

The enlarged statement includes the original one by taking all h_j equal
to one. Its raw parameters are positive a,b,c,h_1,h_2,h_3, with abc>1.
The coalition table is exactly the author's displayed table: a nonpivot
gets zero whenever it quits, gets negative h_j when the pivot quits without
it, and otherwise gets its cyclic passive combination. The pivot gets one
whenever it quits and otherwise gets R exactly when player 3 quits.
Nonabsorption pays zero.

For R strictly between the displayed R_low(h) and R_high, the construction
selects four actual hazards from these finite table data. Repeating the
three independent product rows yields exact terminal Nash against every
unilateral behavioral deviation, and the one displayed phase-A value is
a uniform-equilibrium payoff. Finite censoring gives actual finite laws
of vanishing full exploitability and hence arbitrarily small pivot-repair
values. Every nonempty proper child set fails a complete family of the
five specified F/J withdrawal certificates.

No correlation, prescribed root solution, bounded-deviation restriction,
or target varying with accuracy is hidden in that claim. It does not say
that all quiet approximate profiles fail or that all other existing
producer classes fail.

## Scalar selection: independent checks

The inverse vector v satisfies the three exact equations

    -v_2+a v_3=h_1,
    b v_1-v_3=h_2,
    -v_1+c v_2=h_3.

Its displayed positive-coordinate formula is correct. These equations give
directly

    R_high-R_low(h)=[(c+1)h_1+h_3]/v_3 > 0.

Thus the enlarged interval is genuinely nonempty for all allowed harm
levels, including very unequal ones; no extra balancing condition is needed.

The selector (21) is valid on its entire proposed interval. The denominator
of w is `1+k+(by-h_2 k)>0`, and at an interior point w and z lie strictly
between zero and one. Differentiating there gives

    G_k = h_1 + z_k(1+a w) - a w_k(1-z) > 0,

because z_k>0 and the displayed w_k is strictly negative. At k=0 the sign
is the stated negative quadratic in y. At the upper endpoint either w=0
or z=1, and G is strictly positive. This proves one unique interior root
without assuming any favorable leading coefficient after denominator
clearing. In particular, the argument remains valid when h_2 exceeds one.

The root's continuity and the limits k(0)=k(Y)=0 are justified. At zero,
`k<=by/h_2` suffices. At Y, the admissible interval still has positive
length, the endpoint function is strictly increasing, and its unique root
is zero; compact subsequence extraction therefore proves the limit. Local
strict monotonicity gives continuity at every interior y.

The expansion `A(y,z,w)=h k+O(y^2)` follows from the actual three equations,
not an assumed infinitesimal equilibrium. All four rates are O(y) near
zero. Since A is invertible, the claimed ratios to y follow. They give
the correct continuous endpoint value R_low(h). The k=0 endpoint at Y
gives the three unchanged positive rates below one, and substitution
gives R_high. The intermediate value theorem then produces an interior
y for every strict intermediate R. Monotonicity of R(y) is unnecessary.

The original concave-quadratic proof for h_j=1 also checks: its leading
coefficient is negative a, its value at zero is negative, and it is
positive at both displayed comparison endpoints. It has exactly one root
below their minimum. The general monotone proof supplies an independent
check of that special case.

## Full vector recurrence and complete deviations

I checked all three vector Bellman recurrences, including the actual
simultaneous coalition {0,1}. In the enlarged table its reward is
`(1,0,-h_2,-h_3)`, which is retained by the calculation.

At phase A the nonpivot-1 recurrence has a common factor `1-y`; after
dividing by that positive factor its equality is exactly
`-h_1 x+(1-x)V_B,1=0`. This explains the abbreviated identity in the
enlargement and is not a gap. The other two A coordinates reduce to

    (by-h_2 k)/(1+k)=w/(1-w),
    -h_3 k-y+c z(1-y)=0.

Phase B gives `V_B,1=-z+a w(1-z)=h_1 k`; phase C gives the displayed
nonpivot continuation values. The pivot recurrence is unchanged and its
phase-B value is exactly `1/(1-y)`. Thus its values are one at its mixing
phase and greater than one when it surely continues. Every nonpivot's
value is zero at its mixing phase and nonnegative otherwise.

Own-Quit payoffs are identically zero for nonpivots and one for the pivot,
including ties. The value comparisons therefore give both individual
pure-action inequalities at every phase, not merely equilibrium within
the proposed periodic strategy class.

For each deviator the unchanged opponents have positive independent
hazards in every three-date period. Their survival probability decays
geometrically, uniformly over the deviator's behavior. Iterated Bellman
inequalities hence bound every complete deviation after its tail remainder
vanishes. The same contraction identifies the displayed recurrence with
the actual profile payoff. This justifies exact terminal Nash and, by
the uniform opponent-absorption bound, the fixed finite-average target.

The censoring bound is also correct. Each original marginal has zero Never
mass, and the mass moved to Never after K periods is respectively
`(1-x)^K`, `(1-y)^K`, `(1-z)^K`, `(1-w)^K`. Their sum tends to zero.
Coupling bounds both prescribed and fixed-deviation payoffs uniformly,
giving the stated `4M tau_K` regret bound. The censored pivot law is a
legal competitor in the inner minimization, so the optimal repair value
cannot exceed that exploitability. This last comparison does not assert
that optimizing the pivot preserves the displayed target.

The source consumers inspected are
`isUniformEquilibriumPayoff_of_isQuittingBlockCertificate` in
`UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean`,
`quittingTerminalExploitability_censored_le` in
`UniformEquilibrium/Quitting/Paths/LateFiniteStoppingLawCensor.lean`, and
`quittingGame_uniformPayoffWitnesses_of_terminalNash_tendsto` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
Their scopes match these conclusions.

## Every proper child: attempted falsification

All five cases in the note are necessary to the claimed separation, and
they exhaust the nonempty proper child sets. They check as stated.

For children containing no pivot and at most two nonpivots, a suitable
sure solo owner gives the other retained child a positive payoff and a
missing nonpivot negative one. This is exact child Nash, but the missing
player can join for zero. For all three nonpivots, the k=0 endpoint cycle
is exact child Nash. Its probability of player-3 absorption is exactly
`1/R_high`, obtained from the three-phase geometric sum, so the quiet
pivot's value is `R/R_high<1` and it can quit for one.

If the child contains the pivot but not player 3, the all-sure-Quit row
is child Nash. A missing nonpivot has payoff negative h_j and joins for
zero. If the child contains 0 and 3 but not 2, player 3 alone surely
quitting is child Nash: the pivot prefers R>1 and any retained player 1
receives positive a. Missing player 2 receives negative one and can join.

For the remaining child {0,2,3}, use the actual one-date independent hazards
specified in the enlargement. Player 3's Continue payoff is

    -h_3*c/(c+h_3)+c*h_3/(c+h_3)=0;

the pivot's Continue payoff is R times `1/R`, hence one. Player 2's
Continue payoff is strictly negative, whereas it quits surely for zero.
Later deviations do not improve these comparisons: any surviving branch
has only Never opponents and the nonpivot's own singleton is zero.
The missing player's displayed payoff is the correct expectation and is
strictly negative. The algebraic inequality using v in the note proves
its strict sign for the entire enlarged interval.

Each child has zero full debt and zero joint-Never mass. The exact source
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`
quantifies over every actual child profile and arbitrary
`WithdrawalFutureJoinKind`. Thus a single such positive-debt outsider
refutes every weight choice for every one of the five kinds at that
child. For smaller child sets one applies the source after deleting the
other absent outsiders. This establishes the full F/J-family separation,
not just failure of one numerical candidate certificate.

## Material overlap correction: existence is already known here

For every table in BOTH reviewed sections and every product root,

    quittingRootQuitPayoff_i = ownSingleton_i.

Indeed a nonpivot's reward is zero on every coalition containing it,
and the pivot's reward is one on every coalition containing it. This is
stronger than the predicate `HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`:
any active player witnesses its required inequality. Own singletons are
nonnegative.

The exact declaration `exists_uniformEquilibriumPayoff_of_productLowPremium`
in
`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`
therefore already supplies a uniform-equilibrium payoff for the whole raw
family, even outside the proposed R interval. Its companion
`exists_periodic_allSuffix_terminalNash_of_productLowPremium` supplies
actual periodic approximate equilibria in the original table. Together
with finite censoring, this also already yields finite laws of vanishing
exploitability and hence small pivot-repair values. No limiting unit-solo
normalization argument needs to be invented; the checked nonnegative-solo
producer explicitly handles the zero child singletons.

The note's existing narrow comparisons are otherwise accurate. The
strict-inverse/passive-row producer is not directly applicable at the
three-child deletion: the pivot's normalized passive row is
`q=(-1,-1,R-1)`, and the second coefficient of `q A^(-1)` is
`(R-R_high)/D<0`. The deadlock joint-block modules retain their different
literal singleton matrix. But failure of these two methods and of every
proper-child F/J family does not remove the full-game product-low method.

## Verdict and appropriate use

No mathematical defect was found in the exact selected equilibrium,
the positive-harm enlargement, its fixed target, or the complete F/J
separation. The concrete new content is a fixed-period exact producer with
internally selected hazards and explicit target, together with an exact
separation from every proper-child five-kind quiet-lift certificate family.

The claim that this closes previously uncovered raw uniform-equilibrium
existence would be false: the product-low-premium theorem already consumes
all these tables. I recommend **against a new existence-class export**.
The exact periodic structure and separation should remain internal unless
a genuinely important independent use is identified. Any later export
decision must be made on the stronger explicit
construction/separation content, not on new existence coverage or resolution
of the surviving arbitrary-game obstruction. The author should incorporate
this material overlap before a packet is promoted.

## Independent falsification review of the pivot-first generalization

**PASS as ordinary mathematics, with no unresolved mathematical objection.**
This addendum reviews ONLY the final section “Proposed generalization:
select the pivot equation first” in the same notebook. I did not read the
other reviewer's addendum before completing this check. The earlier overlap
objection above applies to the older constant-participant-payoff family; it
does not apply to this changed raw table.

The checked claim has positive a,b,c,h_1,h_2,h_3, abc>1, u,v<1,
xi,eta>0, and q_2,q_3<=0; eta has no upper bound. It prescribes the four
singleton rows and the literal pair row `(1+xi,eta,q_2,q_3)`, caps each
participant's reward at its own singleton on every other nonsingleton
coalition, and leaves their nonparticipant rewards arbitrary. For the
stated strict interval in R, the output is a selected exact period-three
terminal Nash profile against every behavioral deviation, a fixed uniform
payoff target, and finite censored laws with vanishing full exploitability
and optimal pivot-repair value. No supplied strategy or root is an input.

### Raw overlap and the genuinely changed coalition

At the product root `(1/2,1/2,0,0)`, player 0's forced-Quit payoff is
`1+xi/2` and player 1's is `eta/2`. Their own singletons are one and zero,
respectively, and these are the only active players. Absorption is `3/4`.
Thus EVERY table in the new raw class violates the exact
`HasProductLowQuittingPremium` predicate in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`.
The integrated producer
`exists_uniformEquilibriumPayoff_of_productLowPremium` in
`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`
therefore cannot be invoked with its displayed hypothesis for this class.
Both participant premiums are essential to this particular falsification.

The generalization carefully scopes the old all-child F/J and matrix-screen
separations to the retained ORIGINAL completion: u=v=0, q_j=-h_j, and the
other coalition rows prescribed in that earlier family. It does not claim
those separations for arbitrary new passive completions. Increasing eta
introduces no upper-bound dependence into the original F/J falsifiers. In
particular child `{0,1}` remains exact sure-exit child Nash, now with even
higher participant payoffs, while missing nonpivots still gain by joining.
The all-nonpivot quiet cycle is unchanged and the pivot's immediate joining
payoff only rises. The `{0,2,3}` witness and the missing player's joining
payoff never realize `{0,1}`, because player 2 quits surely. The remaining
witnesses are unchanged. The named singleton-matrix screens likewise do not
depend on eta or xi, since neither changes a singleton. No assertion of
exhaustive exclusion of all implemented producers is warranted or made.

### Pivot branch, including both endpoints

I independently derived the three identities

    a*nu_3-nu_2=h_1,
    b*nu_1-nu_3=h_2,
    c*nu_2-nu_1=h_3.

They prove the asserted positive interval width and the comparison
`P_0(0)<R_low`. The denominator identity
`d=1+k+(by-H_2 k)` proves positivity directly, even when H_2>1.
The two strict bounds defining K(y) give `0<z,w<1`. Both H_j are strictly
positive because y<=Y<1 and q_j<=0.

For fixed positive y, z strictly increases and w strictly decreases in k.
The numerator in P is positive and increasing, while `(1-z)w` is positive
and strictly decreasing. Hence P strictly increases and diverges at the
upper endpoint, whether w vanishes, z reaches one, or both occur together.
At k=0 the rational expression P_0 has a continuous value at zero and is
strictly increasing. Substitution at Y gives exactly
`R_high+xi*Y*L`. These facts produce unique y_star and unique k_R(y).

For interior y, fixed strict brackets around k_R(y) remain feasible and
remain brackets for nearby y; this proves continuity without differentiating
the minimum in K. At y_star, any sufficiently small fixed positive upper
bracket remains feasible, so k_R tends to zero. At zero the inequality
`0<=k_R(y)<=by/H_2(y)` proves continuous extension. The statement does not
assume a globally continuous choice from a possibly multivalued final
equation.

The ratio k_R(y)/y is bounded. Multiplication of the defining equation by
`(1-z)w/y` gives, for every convergent ratio subsequence,

    (R-1)(b-h_2*t)=s_1+s_2*(1+h_3*t)/c.

Its right side is positive. This excludes the possible endpoint t=b/h_2,
and its unique solution is the displayed positive tau. Thus all convergent
subsequences have the same limit. The comparison
`F(1/nu_1)=R_low` is exact, and F is strictly increasing, yielding
`tau>1/nu_1`.

In G the eta term is O(y^2), since k,z,w are O(y). This statement is for
each fixed finite eta; it does not require a neighborhood uniform over all
eta. The remaining first-order coefficient is exactly
`(D/c)(nu_1*tau-1)>0`. At y_star, clearing the positive denominator leaves
`y_star*(bL*y_star-D)<0`. Therefore a zero of G exists strictly between
zero and y_star, with all four hazards strictly between zero and one.
No monotonicity or uniqueness of G is needed. This is the substantive
repair that allows arbitrary positive eta.

### Actual vector recurrences and attempted deviation falsifiers

To avoid ambiguous comma subscripts, the B-vector in equation (38) is
unambiguously

    V_B = (v*z+(1-z)*(V_C)_0, (1-z)*(V_C)_1-z, 0, c*z),

where the first two entries mean `v*z+(1-z)*(V_C)_0` and
`(1-z)*(V_C)_1-z`. The prose immediately after (38) already specifies this
interpretation; it should be typeset with explicit coordinate parentheses
in a standalone packet.

Re-expanding the independent A-row probabilities gives the actual player-2
numerator `by-H_2(y)k` and player-3 numerator
`-H_3(y)k-y+c*z*(1-y)`. Thus q_2 and q_3 are consumed as the actual collision
rewards, rather than silently replaced by the older -h_j. The equations
P=R and G=0 respectively give pivot and player-1 indifference at A. The
B/C recurrences and the definition of w give player-2 and player-3
indifference at their solo phases. All prescribed nonpivot values are
nonnegative, and both pivot values outside A exceed one because u,v<1.

I tried to exploit the arbitrary nonparticipant entries. They cannot be
realized on prescribed play, whose only absorption coalitions are the
four singletons and `{0,1}`. When a single deviator quits, every new
coalition contains that deviator, so its own coordinate is covered by the
participant cap (29), except precisely the already computed exceptional
pair. Continuing cannot change the opponents' prescribed coalition.
Thus none of the free passive entries creates an omitted response.

The phase inequalities hold against both pure actions at every live phase.
Every deleted opponent profile retains positive hazards in each period.
The geometric survival bound therefore removes the tail term when the
inequalities are iterated against an arbitrary complete behavioral
deviation, including Never and history-dependent stopping. It also
identifies the displayed vectors with the actual prescribed payoff. This
is full terminal Nash, not periodic-deviation Nash.

### Finite laws, fixed target, and exact tests

The marginal censoring masses are exactly the four displayed geometric
tails. Product coupling gives prescribed-payoff error at most `2M*tau_K`
and full regret at most `4M*tau_K`. The censored pivot is a feasible
competitor in the inner finite optimization, so the optimum is no larger;
this comparison does not claim that an optimized pivot preserves the
selected target. The displayed prescribed laws themselves converge to
the single target V_A. I reread
`quittingTerminalExploitability_censored_le` in
`UniformEquilibrium/Quitting/Paths/LateFiniteStoppingLawCensor.lean` and
`quittingGame_uniformPayoffWitnesses_of_terminalNash_tendsto` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
their exact scopes match these consequences. The supplied-block consumer
`isUniformEquilibriumPayoff_of_isQuittingBlockCertificate` in
`UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean` remains a
consumer, not the new raw-parameter selector.

As an adversarial exact test, I independently enumerated all coalition
probabilities for the second rational example, assigning 37 to every free
passive entry and the allowed cap to every other participant entry. All
12 vector Bellman equalities and all 24 pure-action inequalities hold
over the rationals, and V_A is exactly
`(5/4,62786/81709,195/404,0)`. Both rational examples also independently
satisfy the displayed z/w identities, P=R, and G=0, with eta above two.
The proof, rather than those tests, covers the arbitrary real parameters.

This supplies the requested second independent falsification review for
the changed mechanism and exact raw class. I recommend the mathematical
export gate for this precise theorem, retaining its stated overlap limits
and full behavioral scope. No Lean build, formal implementation, arbitrary
four-player theorem, or global polynomial exclusion is claimed.

## Independent assembled-packet review: diffuse solo exits

**PASS as ordinary mathematics.** This scoped second falsification review
checks `exports/ONE_JOINT_PHASE_WITH_DIFFUSE_SOLO_EXITS.md`,
including the new refinement and the final response-partition audit. I did
not read BROUWER's diffusion review before reaching this verdict. The
pivot-first selection already reviewed above is retained with the same
equations and quantifiers; the materially enlarged assumption is that only
the six outsider participant coordinates in (2) remain capped.

The new theorem is an actual raw-table producer of arbitrarily accurate
terminal equilibria and one fixed uniform payoff target. It does not claim
exact Nash for the uncapped coarse profile, a uniform refinement count over
different tables, or completeness for arbitrary four-player games.

### Exhaustive coalitions and exact Continue

At the undiffused A row, the two prescribed hazards are those of 0 and 1.
A deviating player 2 can Quit into exactly `{2}`, `{0,2}`, `{1,2}`,
or `{0,1,2}`. Its singleton coordinate is zero and the other three are
precisely the first three caps in (2). Player 3 has exactly the analogous
four possibilities and consumes the other three caps. Neither deviator can
cause the other outside player to Quit, so `{2,3}` and the four-player
coalition are impossible here. The two active players have the literal
indifferences already checked in the pivot-first review.

At a solo j row, a distinct deviator i encounters only `{i}` or `{i,j}`
on choosing Quit. The forced-Quit endpoint is exactly
`s_i+delta*(r_i({i,j})-s_i)`. Thus the maximum in (12) exhausts every new
positive error; no triple premium or free passive coordinate was omitted.
The original table is not modified during this argument.

The remaining aggregate hazard within the player-2 block ranges from z
down to zero. Its values are exactly on the segment from V_B to V_C;
similarly the player-3 block runs from V_C to V_A. Both endpoints of
each segment are above the singleton floor. Coordinate 2 is zero on the
first whole segment and coordinate 3 is zero on the second. Consequently
the solo owner is indifferent even after subdivision. For every nonowner,
policy evaluation is the pure-Continue equation, since that nonowner is
prescribed Continue. This proves every player's exact Continue transport,
not only the coarse Bellman recurrence. The aggregate survival identities
preserve the terminal coalition law, so the initial payoff V_A is genuinely
independent of the refinement count n.

### One-error bound against unrestricted deviations

Writing e=e_n, the constant shift V+e is a valid supersolution because an
exact Continue step transports e with coefficient q in [0,1], whereas
Quit is capped by V+e. This is the required nonaccumulating mechanism:
there is no repeated additive error at Continue stages. Each opponent
survival product over a full refined period is exactly the corresponding
coarse product and is strictly below one after deleting any player.
Bounded remainders therefore vanish against every behavioral strategy,
including Never and arbitrary history-dependent hazards. No assumption
that the deviator uses the public clock is needed.

I inspected the literal certificate and consumer in
`UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`:
`QuittingInfinitePathQuitErrorCertificate` requires precisely policy,
Continue, Quit-error, bounded-value, and every-start opponent-survival
fields. The construction supplies every field. In particular a finite
prefix before the next period gives the every-start survival statement.
The declaration
`QuittingInfinitePathQuitErrorCertificate.isεAsymptoticNash_and_delivers`
has the claimed complete-behavioral and exact-delivery conclusion.
`exists_uniform_quittingMeshScale` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/InfiniteSingletonMesh.lean`
is an existing supplied-path subdivision tool, not a selector from this
table class; no new coverage is attributed to subdivision alone.

### Censoring, target, and pivot repair

Each refined period has the same marginal tail masses as one coarse
period, giving (13) independently of n. For a fixed full deviator, couple
the original and censored opponent laws; they differ with probability at
most tau_K. Identical deviator randomness gives identical play until such
a discrepancy, so payoff error is at most 2M*tau_K even for behavioral
deviations. Combining that bound with the prescribed-profile coupling
gives e_n+4M*tau_K full exploitability. Choosing n and then K proves the
joint regret/delivery statement at the unchanged V_A.

The constructed censored pivot is a feasible competitor for the full
exploitability minimization. The optimum is consequently small; the proof
does not claim that an optimizing replacement pivot preserves V_A.
`exists_objective_minimizer_eq_behavioral_infimum` in
`UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean`
has exactly this unrestricted-repair interpretation.
`quittingGame_uniformPayoffWitnesses_of_terminalTargetAcceptance_family`
in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
retains a member of the actual censored family and gives one threshold for
all larger finite horizons. The theorem's fixed-target quantifier is
therefore justified, not merely subsequential payoff selection.

### Assembled boundary and source checks

The class-wide product-low falsifier remains the same two positive
participant premiums at the actual pair `{0,1}`. The theorem correctly
confines F/J and singleton-matrix separations to its fully specified
completion. As a fresh exact test, I enumerated over rational arithmetic
all 12 coarse Bellman identities, all 12 exact Continue identities, and
all 12 Quit caps for the first fixture. All hold. I also enumerated the
13 one-date proper-child witnesses and their pure responses; each is
exact child Nash and each has a missing player with strictly positive
joining gain. The remaining three-child witness has the stated cyclic
values, absorbs almost surely, and gives the quiet pivot R/7<1 while
immediate joining pays 3/2. Together these cover all 14 children. The
five-kind implication matches
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.

I independently enumerated all 14 nondiscrete partitions against the
displayed singleton matrix. Only `{0}|{1,2,3}` passes block-row-sum
equality. For that partition, at hazard `(x,0,0,0)`, player 1's forced-Quit
payoff is eta*x and its absorbing Continue contribution is -x. The exact
zero-discount formula is therefore `x+eta*x^2`, whereas players 2 and 3
both give x. This breaks the last partition for every x>0. The necessary
row-sum declaration
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`
and the literal definition `quittingDiscountedDisplacement` in
`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`
were read in place. This is a full check of these response partitions,
not an exhaustive classification of all repository producers.

Finally, changing only r_2({2,3}) to beta>0 makes the coarse C-row gain
exactly beta*w at value zero. After subdivision the only positive error
for that completion is beta*w_n, exactly as stated. This falsifies the
stronger exact-coarse claim while validating the advertised approximate
enlargement. No unresolved mathematical objection was found in the new
mechanism or its assembled source claims. No Lean build was run.

The reviewed draft had SHA-256
`876304669f258edbffc0b8f1217edf7f465781f32377de1f1680d288e04f92ad`.
The final frozen artifact above has SHA-256
`5277985708567c67486e991e9a44ba8edf8f867e22d53a02f3015b203e65d2a8`;
the coordinator reports only removal of its draft-status preface, with
no mathematical change. The review record remains outside the packet.

## Independent review: quadratic selector and the complete R axis

**PASS as ordinary mathematics, with no unresolved mathematical objection.**
This review checks the complete final section “Quadratic nonpivot selection
and the complete R axis” in the original owned notebook. I did not read
another review of that section before reaching this verdict. The two frozen
exports are unchanged and are not amended by this review.

The claim keeps the five literal reward vectors, positive a,b,c,h_j,xi,eta,
abc>1, q_2,q_3≤0, and the six outsider caps. It allows v<1,
u≤1+xi, and EVERY real R, with arbitrary remaining finite reward entries.
The middle branch constructs a fixed-target joint/solo approximate
equilibrium; source degree, homogeneous, and passive-inverse criteria
cover the other R regions. The broad six-cap class is not subsumed by a
constant-outsider/nonnegative-participant theorem: its unspecified
participant coordinates may have additional positive or negative premiums.

### Literal quadratic and unique admissible root

I independently expanded C*d*G before applying any sign assumptions.
The identity 1−w=(1+k)/d cancels the apparent extra denominator 1+k.
The resulting quadratic coefficients are exactly (53), including all
eta terms and the term H_2*(a*E−y) in beta. A symbolic rational-function
check returned the identically zero difference between the expanded
expression and alpha*k²+beta*k+gamma.

At 0<y<Y, H_2,H_3 are strictly positive. The definition of K ensures
0≤z,w≤1 throughout [0,K], and d≥1+k>0. At k=K either w=0 or z=1,
so the only negative term in G vanishes; h_1*k+z>0 and the eta term is
nonnegative. Thus Q(K)>0 while Q(0)=gamma<0. The claimed quadratic
one-crossing argument is valid: two roots strictly inside the interval
would force the same signs at its endpoints, and a double root cannot
change sign. The actual interior root is simple.

Every term in the displayed beta is nonnegative, and in fact several are
strictly positive. In particular a*E−y=ac−L*y≥1/b>0. This holds on
the whole closed interval [0,Y]. The discriminant is positive in the
interior because a simple real crossing exists, and at both endpoints
it equals beta²>0. Therefore beta+sqrt(Delta) never vanishes.

The formula −2gamma/(beta+sqrt(Delta)) is the admissible root. If alpha
is positive it is the unique positive quadratic root; if alpha is negative
it is the smaller positive root, with the other lying beyond K; if alpha
is zero it is exactly −gamma/beta. It gives k=0 at y=0,Y and a
continuous branch on the full closed interval, without dividing by alpha
or asserting global monotonicity of G.

### Endpoint limits and the entire constructive interval

At zero, beta(0)=c*h_1+h_3+ac*h_2=D*nu_1. Dividing the root formula
by y gives k/y→1/nu_1. Substitution into z,w gives the claimed limits
nu_2/nu_1 and nu_3/nu_1, using the exact nu identities. In particular
the denominator in the pivot ratio has positive first-order coefficient.
At Y, z and w are both strictly between zero and one, while k=0.

The pivot equation P is used only as a continuous function along this
branch. Its numerator may be negative and p−u may be negative; neither
affects the argument. The order-y limit is exactly R_low. Its other
endpoint is T_2+xi*D/b. Hence every strict intermediate R is attained
at an interior y, with all four selected rates strictly between zero and
one. No unproved monotonicity or unique selection for R(y) is needed.

The passive threshold calculation is exact. The three inverse weights
are (50), T_3−T_1=D*s_2/(bc)>0, and T_2−T_3=D*s_1/b.
Thus T_pass=max(T_2,T_3) is precisely the weak nonnegative-weight
threshold. If s_1≥0, T_2−R_low is strictly positive by the stated
identity. If s_1<0, T_3−R_low=(s_2*h_1−s_1*h_2/b)/nu_3>0.
Finally R_top−T_pass is positive in the first case and equals
D*(1+xi−u)/b≥0 in the second. This proves
R_low<T_pass≤R_top even when c*s_1+s_2≤0 or R_low is negative.

### Floors, free coordinates, and complete behavioral deviations

All vector recurrences and pure-Continue identities are algebraic and
are unchanged by the new scalar selection. The pivot floor at B is
exactly

    (V_B)_0−1=(1+xi−u)y/(1−y)≥0.

Using v<1 and z>0 then makes (V_C)_0>1, regardless of the sign of R.
The nonpivot values remain nonnegative. Therefore the refined segments
retain every singleton floor, including the equality u=1+xi. No hidden
R>1 or strict B-floor premise is used.

At the joint row, the six caps still exhaust the two outsiders' possible
new participant coalitions; the two active players are indifferent. At
each refined solo row, a deviation can realize only the deviator's
singleton or its pair with that solo owner. Thus C_join controls every
uncapped participant coordinate actually reachable by a unilateral Quit.
The other free coordinates do not appear. Exact Continue lets the single
shift V+e_n serve as a supersolution over the whole path. Vanishing
opponent survival after deleting any player removes the remainder, so
the bound covers arbitrary complete behavior, not just clock-dependent
deviations. These are exactly the fields of the already inspected
`QuittingInfinitePathQuitErrorCertificate` in
`UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`.

The target is selected with the coarse rates before choosing n or K.
Refinement preserves it exactly; censoring incurs at most 2M*tau_K
delivery error and 4M*tau_K additional full regret. The same fixed-target
terminal consumer therefore applies. It is not necessary for the source
exit branches to share this branch's target, since each actual table has
one fixed R and is handled by one valid existence branch.

### Exact source stitching, including both equality boundaries

For R≠R_low the homogeneous proof really gives full R0. A positive
pivot variable makes all child variables positive by the cyclic residual
inequalities, then z=t*nu and the pivot residual cannot vanish. At zero
pivot, a nonzero child variable cyclically forces every child positive;
the invertible child block then rules it out.

For R<R_low, at offset (q_0,−h_1,−h_2,−h_3) with q_0>delta,
feasibility itself forces all child variables positive, so z=(1+t)*nu.
The two and only pivot solutions are t=0 and t=q_0/delta−1. The first
has strict inactive residual q_0−delta and active determinant D>0;
the second is fully positive with determinant −D*delta<0. These meet
the precise hypotheses of `exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean`, whose statement I inspected.
Its signs sum to zero. The declaration
`exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`
consumes full R0 and degree different from one for the actual original
reward table, with no extra nonsingleton hypotheses.

At R=R_low, (1,nu) is a genuinely positive homogeneous solution. The
inspected
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`
has unconditional original-table noUE as its only strategic hypothesis
and yields full R0. Its contrapositive therefore closes this equality;
no punishment-normality or limiting-target premise is missing.

For R≥T_pass, the literal receiver-first outside difference row times
A⁻¹ is componentwise nonnegative. I checked `inverseWeight`,
`factorization`, and
`exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
The outside-weight inequalities are weak, so equality R=T_pass is
included. The theorem has no hidden restrictions on unused absorbing
coordinates. Thus R≤R_low, R_low<R<T_pass, and R≥T_pass cover the
whole real axis, including when T_pass=R_top. No endpoint was silently
discarded from the open IVT interval.

### Additional exact falsification tests

I independently verified both displayed rational examples. The first
has negative alpha and the second has alpha=0; their rates satisfy G=0
and P=R, and all 12 Bellman and all 12 exact Continue identities hold.
For a stronger completion test I assigned 37 to all unused coordinates,
then imposed zero at the six required outsider caps. Every joint-row
Quit cap holds exactly; every solo-row Quit excess obeys the stated
C_join bound. Thus uncapped positive participant premiums are genuinely
permitted in the checked inequalities rather than accidentally omitted.

As a separate boundary/sign test, take a=b=c=2, h_j=1, xi=1,
eta=17/11, q_2=q_3=−1, u=2=1+xi, and v=9/10. The rates
(1/11,1/4,7/30,4/15) give

    R=157/368<1,       R_low=1/10,       T_pass=R_top=7/10,
    V_A=(5/4,17/121,4/11,0),
    (V_B)_0=1,        (V_C)_0=237/230>1.

All the same exact vector/Continue/error-cap tests pass. This tests the
weak u bound, equality of the two upper thresholds, a pivot R below one,
and a binding B-floor simultaneously. The proof covers all real
parameters; these computations are adversarial evidence, not its basis.

The final shared-condition parameter-plane statement is also valid as
written: its six caps follow from constant zero participation for 2 and
3, and u>1+xi enters the already reviewed strict-leave theorem with no
R restriction. That subfamily may receive additional coverage from newer
two-core results, but it does not subsume the broader six-cap theorem
reviewed here. No Lean build or arbitrary-table completeness claim is made.

## Independent review: switched joint pair with a positive outsider buffer

Verdict: PASS on the final section titled “Switched joint pair: two
passive rewards above the pivot singleton.” This is an independent
check of the changed joint support, raw quadratic producer, weighted
outside cap, complete deviations, all-R source cases, and stated
full-core completion. No other review of this section was read first.
The preceding architecture positive-gap theorem is not a dependency of
this existence proof and is not given a separate full audit here.

### Raw data and genuine change of scope

The five prescribed reward vectors use U,V≥1, arbitrary real R,
a,b,c,h_i>0, and abc>1. The selected pair is 03 with zero premiums
for BOTH actual participants. The three player-2 caps are exactly the
possible nontrivial forced-Quit coalitions at that joint row. Player 1
instead has a weighted raw cap J+ν_3 Q≤ν_2, where
J=max(0,r_1(01),r_1(013)) and Q=r_1(13), which may have either sign.
This does not silently assume zero or nonpositive player-1 premiums.
Unspecified coordinates are arbitrary and enter the solo refinement
bound when they can be reached by a unilateral deviation.

The beta=0 algebraic fixture is already covered by the two-core
weak-leave theorem, as the author says. It is not itself new existence
coverage. The full-core completion is a different matter: raising the
two participant rewards at 12 to 1/2 creates trap 12, while trap 01
persists. Raising participant 3 at 13 to 1/2 gives the fourth member a
premium witness, without changing any new raw cap. Every trap must
contain 1, but their intersection is only {1}; that sole common player
has r_1(01)=1>−1=r_1(0). Thus even the weak common-leaver criterion in
MORSE Section 15 fails. The comparison establishes a genuine complement
to that class, not merely to its nonnegative-premium restriction.

### Independent quadratic derivation

Set C=b(1−y), E=b−(b+1)y, d_0=1+a y, d_1=1−h_1,
and d=d_0+d_1 k. On the admissible interval

    0≤k≤K=min(a y/h_1,E/h_2),

we have d≥1+k>0. Clearing the literal balance
G=h_3 k+z−c w(1−z), with z=(h_2 k+y)/C and
w=(a y−h_1 k)/d, gives C d G=αk²+βk+γ, where

    α=(h_3 C+h_2)d_1−c h_1 h_2,
    β=h_3 C d_0+h_2(d_0+c a y)+y+h_1(cE−y),
    γ=y[a(bc+c+1)y−D].

For 0≤y≤Y'=D/[a(bc+c+1)], cE−y≥1/a, so β>0.
For interior y, γ<0. At K either w=0 or z=1, making G>0.
Thus there is exactly one root in (0,K): opposite endpoint signs
exclude two quadratic crossings within the interval, including every
sign of α. Its derivative is nonzero. The expression

    k=−2γ/[β+sqrt(β²−4αγ)]

is continuous on the closed y interval, has both endpoint values zero,
and is valid at α=0. This proves the selector directly from the raw
data; the old theorem's passive-reward assumptions are not being
reimported through an “eta=0” assertion.

At zero, β(0)=bc h_1+h_2+b h_3=Dν_3, so k/y→1/ν_3.
The identities bν_1−ν_3=h_2 and aν_3−ν_2=h_1 give exactly the two
other limits in (66). At the upper endpoint, the zero-k relation gives

    (1−Y')z/Y'=1/b,
    (1−Y')(1−z)w/Y'=1/(bc).

Substitution into the pivot equation yields R(Y')=T with no monotonicity
assumption. The zero endpoint is R_low. Formula (64) is positive if
either U or V is strictly above one and vanishes only when both are
one, so the stated IVT interval is exactly the residual interval.

### Buffer estimate and actual Bellman equations

Testing at k_0=y/ν_3 gives the displayed z_0 and w_0 exactly. If the
test point is outside the admissible interval, its ordering already
proves k<k_0. Otherwise z_0>ν_1 y/ν_3 and
w_0<ν_2 y/ν_3, so G(k_0)>0 by h_3+ν_1−cν_2=0.
Uniqueness of the admissible root gives the strict bound (68).
No derivative sign of G was assumed.

The literal outsider-1 forced-Quit numerator is
k(1−y)r_1(01)+yQ+ky r_1(013). Its upper bound kJ+yQ is valid even
when Q is negative. The weighted cap gives
a−Q≥(h_1+J)/ν_3; since h_1+J>0, (68) proves the strict buffer.
For outsider 2, the complete list of forced-Quit coalitions is 2,02,23,023.
Thus no larger collision or participating deviator has been omitted.

All twelve policy equations and all twelve Continue comparisons for
(70) hold. In particular B's player-3 value is
−z+c w(1−z)=h_3 k, and C's player-1 value is
−w+(1−w)w/(1−w)=0. At A, the active endpoints are exactly 1 and 0;
the two inactive endpoint comparisons are precisely the three caps and
the strict buffer. U,V≥1 give both pivot continuation floors, including
equality at either U=1 or V=1.

Refining B and C preserves their full endpoint vectors and gives
intermediate vectors on the corresponding line segments, hence every
singleton floor. At a solo-j microhazard t, an outsider's forced-Quit
endpoint is s_i+t[r_i(ij)−s_i], so the claimed C_join t error is exact.
The undiffused A row retains its exact comparisons. Adding one constant
ε to every phase value is a Bellman supersolution: an opponent
survival coefficient multiplies the added continuation ε, so it is at
most ε again. Local errors are not summed across phases or periods.

All four aggregate hazards are strictly positive. After removing any
one player's actions, at least one prescribed opponent still has a
positive hazard in every period. This gives a geometric survival bound
uniform over every complete behavioral deviation, not only deviations
with the same memory. It justifies the terminal Snell limit, finite-law
censoring, and the all-large-horizon conclusion. Refinement depends on
accuracy but keeps the same full vector V_A; no target-selection limit
is hidden in the constructive branch.

### Source exits and endpoint scope

The three inverse thresholds obey T_2≤T_3≤T_1=T because the old
shortfalls are now s_1=−(U−1), s_2=−(V−1). Hence R≥T has weak
nonnegative passive inverse weights, including equality. The previously
inspected `exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`
requires no restrictions on the unused nonsingleton rewards.

For R<R_low, put δ=ν_3(R_low−R)>0. The same actual child LCP forces
z=(1+t)ν at offset (q_0,−h), q_0>δ. There are exactly the two full
roots t=0 and t=q_0/δ−1, with determinant signs + and −. Thus the
full R₀ degree is zero. This computation has no sign hypothesis on
U−1 or V−1. At R=R_low, (1,ν) is a nonzero homogeneous solution.
The checked hypotheses of the named singleton-degree source and its
noUE-implies-R₀ converse remain exactly as in my prior review. Thus
R≤R_low, the open IVT interval, and R≥T cover every real R. When
U=V=1 there is no constructive interval and the two source cases meet
at R=1, as asserted.

### Adversarial exact tests

Besides checking the golden-ratio fixture and all its raw unrefined
Quit inequalities, I tested an asymmetric example with a negative Q
and binding weighted cap. Set a=b=c=2, h_1=h_2=1, h_3=79/45,
U=3/2, V=5/4, y=1/4, k=1/10, x=1/11, z=7/30, w=4/15.
Then

    ν=(349,451,383)/315,
    R=149/300, R_low=1/4, T=11/16,
    J=2, Q=−179/383,
    V_A=(1,4/11,0,0),
    V_B=(1051/900,0,7/15,79/450),
    V_C=(16/15,0,0,8/15).

Take r_1(01)=r_1(013)=2 and set every other unspecified coordinate
to 37, except the three required player-2 caps, set to zero. Exact
arithmetic gives zero residuals in all policy and Continue identities.
At A, outsider 1's Quit payoff is 637/8426, below its value by
2427/8426; every other A comparison is exact. Several unrefined solo
Quit inequalities fail, as they should with this completion, and each
is bounded by C_join times its hazard. Thus the proof genuinely needs
and correctly uses refinement rather than accidentally assuming all
unused premiums harmless.

As a separate α=0 test, retain y=1/4,k=1/10,h_2=1 but use
h_1=2/3,h_3=2. Then z=7/30,w=13/46, ν=(22,32,23)/21,
and the same U,V give R=39/80 strictly between R_low=4/23 and
T=11/16. At this y the quadratic coefficient is exactly zero. The
binding cap choice J=1,Q=11/23 is now positive, giving an independent
sign test for Q. The selector and all displayed continuation identities
remain valid. These computations supplement the proof; they do not
replace its quantifiers. No Lean implementation or general Fin4
completeness claim is made by this verdict.

## Independent review: two outsider buffers and the zero-phase inclusion

Verdict: PASS on the final “Two outsider buffers from a repeated solo
exit” section, including the direct θ=0,ξ=0 inclusion. Reviewed
notebook SHA256:
`e550c92c806d934b2f2e94d4cbe79d47cdc81210a045a231525a644c73c133be`.
No other agent's review of this section was read. This audit targets
the new producer, simultaneous positive caps, endpoint, pivot floor,
full deviations, and zero-phase boundary. The unchanged outer
singleton-source proofs are not given another full audit.

The θ premise is a finite scalar raw-table feasibility condition: its
bounds and the two inequalities (72) are explicit affine inequalities
in θ once the reward data and ν are fixed. It is not an assumed Nash
selector or missing strategic continuation. U,V≥1 imply R_low≤1,
so the ξ bound really does imply ξ≥0.

### Strict monotone selection from the raw data

On the cap interval, z increases strictly with k, while

    ∂A_1/∂k=−(h_1+ay)/(1+k)²<0.

The final rate t depends only on y. Hence d_1 and w decrease strictly.
Since 0≤z≤1 and w≥0,

    ∂G/∂k=h_3+(1+cw)∂z/∂k−c(1−z)∂w/∂k>h_3.

Thus the monotonicity statement holds on the whole admissible interval,
not only at a presumed solution. The identity ensuring positivity of
the second cap is correct, including θ=0. At k=0 the sign is exactly
that of −D+L_θy. If z=1 at the upper cap, positivity of G is immediate.
At the other upper cap k=ay/h_1, the displayed lower bound follows
from w≤aθy and z≥(1+θ+a h_2/h_1)y/b; its coefficient simplifies to

    D(ν_2−h_1θ)/(b h_1)>0.

There is therefore one interior root. Compactness and strict increase
justify continuity at Y_θ and force its limit to zero there; the first
cap bounds k/y at zero. Every subsequential limit of k/y solves the
same linear equation, with coefficient Dν_3/b>0. Its unique solution
is (1+θ)/ν_3. The other two limits in (74) then follow from Aν=h.
No derivative of a root branch or polynomial-root convention is needed.

### The global rate bound pays both caps

At k_0=(1+θ)y/ν_3 I independently obtained the displayed numerator
and denominator of w_0. The critical coefficient after comparison with
(1+θ)ν_2y/ν_3 is

    ν_2(ν_2+1)+θ(ν_2ν_3+ν_2²−h_1).

Subtracting ν_2² leaves
ν_2−θh_1+θν_2ν_3+θν_2²>0. The remaining quadratic coefficient
is nonnegative, and is zero at θ=0; this does not affect the strict
comparison. Also z_0>(1+θ)ν_1y/ν_3. If k_0 is admissible, these
give G(k_0)>0; if not, its location above the upper cap already gives
the desired ordering. Strict monotonicity proves (75) globally.

For outsider 1, (72) gives

    a−Q_1≥(1+θ)(h_1+J_1)/ν_3.

Since h_1+J_1>0, (75) makes its actual Quit payoff strictly below
A_1. For outsider 2, the same bound gives an upper numerator θy.
After division by 1+k this is strictly below θy when θ>0, even
if J_2=0. At θ=0 it is merely ≤0, which is sufficient. The
estimates permit Q_1 and Q_2 of either sign and do not require any
individual zero cap. At the joint row the four possible forced-Quit
coalitions are i,0i,i3,0i3 for each outsider i. Thus all six nontrivial
collision coordinates, including the triples, are included.

### Pivot endpoint and the indispensable last-block floor

Expansion at zero shows the numerator and denominator of (76) have
leading coefficients (1+θ)R_low and 1+θ, respectively. Thus the
zero endpoint is R_low even when ξ>0. At k=0,y=Y_θ, I substituted
the exact rational formulas for z,w,t and verified the identity

    R(Y_θ)−T=D[ξ−θ(1−T)]/(abc+θ).

This also follows by direct clearing of positive denominators. Its
right side is nonnegative under the raw ξ condition; for θ>0 it is
strictly positive whenever the residual interval is nonempty. Together
with continuity, this reaches every R_low<R<T at an interior y.
No unique or monotone pivot selection is assumed.

The last pivot continuation is

    P_D=1+y[ξ+θ(R−1)]/(1+θy).

Its bracket is at least θ(R−R_low), and therefore nonnegative at
the selected R, including equality in the raw ξ bound. The later
convex averages with U,V≥1 retain the pivot floor. This calculation
does not incorrectly infer the floor from R≥1: selected R may be
negative. All other phase coordinates have their displayed nonnegative
values.

I checked all sixteen policy and sixteen Continue identities in (78).
At D, in particular, −t+(1−t)θy=0 is the second outsider's reset;
at C, −w+(1−w)d_1=0 is the first's reset. The A active endpoints
are exactly p and zero. The remaining A comparisons are exactly the
two caps proved above, so there is no omitted behavioral action.

### Full deviations and literal zero-phase specialization

Refining all three solo blocks preserves their complete endpoint
vectors. Their intermediate values are convex interpolants, the solo
owner retains its singleton, and Continue is exact at every microstage.
The positive pivot premium ξ at the final solo-3 block must be included
in C_join; the note does so. The constant-error Bellman supersolution
therefore controls all unilateral actions with one error, without
summing errors across periods.

For every possible deviator, x,y,z,w>0 leave positive prescribed
opponent hazard in each period, regardless of whether t is zero.
Their period survival remains below one after refinement and does not
depend on the deviator's complete behavioral strategy. The terminal
supersolution limit and uniform expected absorption-time bound follow.
Choosing refinement first and a horizon threshold second gives one
profile valid for all larger horizons and the same target V_A at
every accuracy. No public coin or bounded deviation controller is used.

At θ=0, t=0 and V_D=V_A exactly, coordinate by coordinate. Deleting
the final all-Continue block therefore preserves the actual game law
and values, not just a limiting formula. The cap interval and strict
rate bound remain valid. At θ=0,ξ=0, equations (73),(76) reduce
literally to the switched-pair selector, R(Y)=T, and the original
three player-2 zero caps imply the new second weighted cap. Equality
in the first weighted cap remains safe; the second comparison is weak
as allowed. The old theorem is thus included directly, with no reward
closure or assumed openness of UE existence.

The unchanged outer source cases retain the same singleton data. When
U=V=1 the residual interval is empty and those cases alone cover R;
the new construction is not being evaluated on a nonexistent interval.

### Exact adversarial tests

I independently verified every number in the displayed two-buffer
example, including both binding raw caps, all sixteen policy/Continue
identities, and the A safety margins 52581/245036 and 97953/4900720.
Assigning 37 to all still-unspecified coordinates leaves these checks
unchanged and creates real positive solo Quit errors, which require
the proved refinement bound.

A separate test saturates the ξ floor and has a negative selected R.
Take a=b=c=2, h_1=h_2=1 and

    θ=1, h_3=2989/2592,
    ν=(18541/18144,4933/4536,9469/9072), U=V=2,
    ξ=38273/18938=θ(1−R_low),
    R_low=−19335/18938,
    R=−58011473/139554122<T=1/4.

The rates x=3/28,y=1/10,z=83/450,w=19/96,t=1/11 solve the
actual equations. Here ν_2−h_1θ=397/4536>0. Both raw caps bind
with all six outsider collision coordinates positive by setting

    J_1=397/18144, Q_1=397/9469,
    J_2=9469/36288, Q_2=1/2,

and giving each of the two corresponding max entries the value J_i.
All other unspecified coordinates may again be 37. Exact evaluation
gives zero in every policy/Continue residual, strict A safety margins
104775191/1603518336 and 46399/1693440, and
P_D−1=3839461/69777061>0. The unrefined final solo-3 row has
a positive pivot Quit gain, confirming that this last block cannot be
silently left coarse.

As a distinct zero-phase test, take the prior asymmetric switched
example with θ=ξ=0, h=(1,1,79/45), a=b=c=2, U=3/2,V=5/4,
and rates x=1/11,y=1/4,z=7/30,w=4/15,t=0. Keep
J_1=2,Q_1=−179/383, but set J_2=1,Q_2=−315/383. The second
weighted cap binds despite positive J_2, while V_A,2=0. Its exact
Quit payoff is −809/8426, so the boundary comparison is safe without
an implicit individual zero cap. This tests the stronger new θ=0
class as well as literal inclusion of the old one.

The full completion's traps 01,02,13 have empty intersection and
their union is all four players. It is therefore genuinely outside the
common-trap-leaver criterion. I also inspected
`SignedFourCycleSingletonData` in
`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`:
its strictly positive predecessor in each singleton column cannot be
met by a relabeling when the pivot singleton harms every other player.
No claim of failure of every other source is inferred from this check.

No unresolved mathematical objection remains. This is ordinary
mathematical PASS, not a Lean implementation or arbitrary Fin4 result.

## Final artifact check: two buffers with a repeated solo exit

**PASS.** I read all 632 lines of
`exports/TWO_OUTSIDER_BUFFERS_WITH_A_REPEATED_SOLO_EXIT.md`,
SHA256 `93a87ad51034af3d1adae77c44cc17a71e1f96bbd13aee7b2a5fd677f735d62e`.
This is a bounded assembly/delta check against the independently reviewed
final two-buffer mechanism, not a fresh audit of unchanged outer exits.

The assembled raw hypothesis is unchanged: θ is a finite feasibility
parameter, ξ≥θ(1−R_low), and the two weighted inequalities retain
all six actual outsider collision coordinates. Negative Q_i and R
remain allowed. The strict θ>0 conclusions and weak θ=0 comparison
are distinguished correctly. There is no added strategic witness or
hidden individual zero cap in the theorem statement.

The expanded singleton exits are self-contained up to precisely named
existing semantic theorems. The positive-right-hand-side child problem
has its unique solution tν; its homogeneous problem has only zero.
Consequently the full homogeneous equality is exactly R=R_low. At
R<R_low the selected offset has exactly two nondegenerate roots,
with determinant signs + and −. At R≥T the explicitly ordered
thresholds yield all nonnegative passive weights. Both equality seams
are included, and U=V=1 is correctly discharged by those two exits.
The new handoff describes the raw predicate, admissible root, selected
phase law, refined fixed target, and existing consumer without treating
an interface as a producer.

The displayed monotone selector, ratio limit, cap estimate, pivot
endpoint identity, and all four vectors are the reviewed ones. The
full consumer keeps all three solo subdivisions. It bounds terminal
deviations with one common supersolution error and finite-horizon error
through opponent-only geometric tails, uniformly over complete behavior.
Thus the target is fixed before accuracy, not merely a selected limit
of target-dependent profiles.

At θ=0 the block D is literally all Continue and V_D=V_A. Deleting
it requires no limiting argument. At θ=ξ=0 the former zero-cap
switched-pair theorem is included directly, including the exact upper
endpoint R(Y)=T; positive J₂ offset by negative Q₂ is correctly
retained as a larger zero-phase case. I checked the assembled quadratic
coefficients and its rationalized root formula at α=0.

The six-positive-cap full-core completion preserves all five prescribed
rows and all six specified entries; the three exhibited traps have
empty intersection. The final zero-phase completion also preserves the
raw hypotheses and its exact algebraic rates, while player 1 fails the
only possible common-leaver test. These are only the bounded source
separations explicitly claimed in the packet.

For the added boundary fixtures, I independently recomputed the
α=0 test: ν=(55,59,47)/63, k=7/50, α=0, β=25/4,
γ=−7/8, z=13/50, w=10/37, and both scalar/pivot residuals zero.
I also recomputed the signed two-buffer test with θ=1/3 and
h₃=2320/873: ν=(7558,11899,9005)/6111, both weighted-cap
residuals zero, every displayed phase coordinate exact, and outsider
Quit payoffs −1147/176540 and −28307/397215. The binding-pivot-floor
negative-R test and the stronger zero-phase test are the independently
verified adversarial examples in my preceding review; their fractions
are unchanged in the assembly.

No mathematical delta, missing dependency, or strengthened coverage claim
was introduced. No unresolved artifact objection remains. This verdict
is ordinary mathematical validation, not a Lean compilation claim.

## Independent review: two genuine joint phases on a full-table neighborhood

**Verdict: PASS for the open-neighborhood theorem and its precisely
scoped source exclusions.** I independently checked “Two genuine joint
phases give an open full-table neighborhood,” equations (79)–(86),
and the appended “Exact exclusion of the fixed-label stationary
neighborhood.” The full notebook SHA at this check is
`71f306ad1a57b691b34ad7d575e3a55f8e9320a80b7c7445133665d05395b6f5`.
I did not read BROUWER's review before deriving this verdict.

The assertion is a uniform-equilibrium payoff for EVERY table in one
open neighborhood of the complete rational center in ℝ⁶⁰. All sixty
coordinates, including singleton levels and the four joint03 entries,
are independently perturbable. The target depends on the table, then
is fixed before accuracy. The theorem does not assert a common target
across different tables, a numerical neighborhood radius, or general
openness of equilibrium existence.

### Arbitrary-table elimination and the exact center

The use of c_i(S)=r_i(S)−s_i is only algebraic centering of the
original Bellman equations V=s+v. Every one-step outcome, including
the source continuation, has the same subtracted s_i, with total
probability one. The Never reward is not translated. Eventual
absorption, proved separately, validates the original terminal values.

The definitions of e and f in (83) enforce exactly the two supported
Continue equalities at D. The two equations F₃=F₀=0 enforce the
supported Continue equalities at A. The four corresponding Quit
endpoints are ξy, ηx, ξf, ηe in centered coordinates. No equation
requires the perturbed joint03 reward to equal a singleton coordinate.

For player 1, v_B,1=0 makes the A equation a₁=B₁(x,y); the D
equation defines d₁, and w enforces
w c₁(2)+(1−w)d₁=0. This gives BOTH v_C,1=v_B,1=0 and the
solo-1 indifference. For player 2, the definition of a₂ gives the
exact D equation with v_D,2=0, and the z formula gives its A
equation via v_B,2=z c₂(1). The solo-2 indifference follows from
v_C,2=v_D,2=0. The four remaining B/C coordinates are their literal
solo averages. Thus all sixteen policy and all sixteen Continue
identities really follow for arbitrary nearby reward data, not only
on the center's affine parameter slice.

I independently reconstructed all fifteen center reward vectors from
(79)–(80), substituted the six exact hazards, and recomputed every
policy and Continue residual as zero. The four vectors (81) and the
four strict joint-row gaps (82) agree exactly. The four rows of
Continue-minus-Quit gaps, in player order, are

    A: (0, 604439/832400, 105797/416200, 0),
    B: (252/281, 0, 1/2, 823/2958),
    C: (572/843, −1/6, 0, 1480/1479),
    D: (0, 11179/20000, 171/5000, 0).

In particular the coarse C row is NOT Nash: player 1 can gain 1/6.
This is safely handled by refinement rather than silently omitted.

### Independent derivative calculation and all sixty directions

I differentiated the literal rational functions (83)–(84), independently
of the displayed derivative, obtaining exactly

    [−34669831/8430300, −21674311817/23083492500]
    [ 445211/800850,    −7722150539/6578561250]

and determinant 1561445159256653/291890762662500>0. All denominator
values are nonzero at the center. The finite-dimensional implicit-function
theorem therefore applies with the ENTIRE reward vector as its
parameter and (x,y) as its two unknowns. The fact that the equations
ignore some reward entries does not constrain those directions: the
branch simply remains unchanged when only an unused equation entry
varies. Those entries still occur in the subsequent strict inequalities
or in the finite refinement constant.

All six center rates are interior, so the formulas preserve that after
one neighborhood restriction. Exactly the four listed floor occurrences
are identities: V_B,1=V_C,1=s₁ and V_C,2=V_D,2=s₂. The other
twelve phase-coordinate floors are strictly separated at the center,
including the small positive player-3 floor at D. Their continuity
therefore preserves them. The four joint-row outsider gaps are strict;
their formulas retain empty, 0, 3, and 03 opponent events and vary
continuously in every actual collision reward. This justifies one
open neighborhood in all sixty coordinates. No hidden equality or
nonnegative-singleton premise is reintroduced.

### Complete deviations, no accumulated error, and fixed target

Only solo phases B,C are subdivided. Their endpoint vectors are
unchanged and every intermediate vector is on the corresponding
entry/exit segment. The owner coordinate is identically its actual
singleton, even when that singleton becomes negative under perturbation.
Consequently prescribed policy and pure Continue remain exact, all
floors survive, and every microstage Quit payoff is at most current
value plus the same e_n. The two original joint rows retain error zero.

Adding this one e_n to all values gives a Bellman supersolution:
Continue transports only a survival fraction of the added constant,
and Quit has the stated cap. No sum of stage or period errors appears.
For every deviator, its opponents have positive aggregate hazard in
the period; removing its entire behavioral strategy cannot change
that prescribed opponent-only survival probability. The geometric
bound therefore removes the bounded remainder uniformly over complete
history-dependent deviations, including Never.

The same contraction evaluates the prescribed policy exactly at
V_A(r). The refined period has 2+2n dates. Opponent-only first-Quit
time bounds the absorption time under every deviation by expectation
(2+2n)/(1−ρ_i). Thus the stated finite-horizon O(1/N) bound is
uniform over deviations and all larger horizons. Choosing n and then
one horizon threshold leaves V_A(r) fixed. This is the literal
hypothesis of the re-inspected
`quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue`
and `isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError`
in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`.
Neither theorem needs nonnegative singletons for this direct construction.

### Exact scope checks, including the stationary appendix

The disjoint traps03 and12, all four of their positive participant
premiums, and all fifteen listed pure-coalition improvements check
exactly. These strict gaps persist nearby. There is therefore no
common trap player and no pure equilibrium throughout a sufficiently
small neighborhood. Moreover trap03 has NO weak leaver: both its
participants strictly prefer their pair payoff to the other's singleton.
These two gaps also persist, so even the new support-specific protected-
set criterion in my Section 17 cannot apply on this neighborhood.

The appended stationary exclusion is correct in its stated fixed labels.
With q₃=0, put A=q₁+q₂−q₁q₂ and T=q₁+q₂−2q₁q₂. Direct
evaluation gives Q₀=1−A, B₀=2T and E₀≤−T. The inequality
uses A²≥q₁q₂; T=0 occurs only at (0,0) and (1,1).
The (1,1) corner gives E₂=−3/2+q₀/2<0 against active player 2.
At the (0,0) corner, q₀>0 gives E₃=h₃q₀+ηq₀²>0 against
quiet player 3; all hazards zero is blocked by singleton0=1.
Otherwise q₀=0. If q₁>0, E₂=q₁²/2−2q₁<0 forces q₂=0,
then E₃=q₁−q₁²/2>0. The final q₁=0,q₂>0 case gives
E₁=q₂+q₂²/2>0. All boundary hazards are included.

I inspected `PairedCubicStationaryExample.activeHazard` in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicActiveJacobian.lean`
and `PairedCubicStationaryExample.exists_local_stationary_branch` in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`.
Their branch has literal hazard3=0, so that asserted fixed-label
neighborhood cannot contain this center. This does NOT exclude its
relabelings, stationary profiles with other support, or every other
raw producer. I make no all-stationary exclusion claim, and no floating
root search was used to establish the stated source separation.

No unresolved objection remains to the complete open-neighborhood
producer, its exact behavioral consumer, or its explicitly bounded
overlap statements. This is ordinary mathematical PASS, not a Lean
implementation or an unrestricted Fin4 theorem.

## Final artifact check: two joint phases and a full-table neighborhood

Checked the complete 472-line standalone artifact
`../exports/TWO_JOINT_PHASES_FULL_TABLE_NEIGHBORHOOD.md`,
SHA256 `243a79c240d97d8920602503c6b2074e607e2bc00a7d6506e9c67d368b10c2e6`.
Verdict: **PASS**. This is an assembly/delta check against the independently
reviewed theorem above, not a second full proof audit or a Lean-check claim.

The assembled complete rational table, elimination equations, derivative,
six rates, four value vectors, strict margins, and forced floor equalities
agree with the reviewed calculations. The expanded opponent-survival
products correctly omit each deviator's hazards while retaining every
opponent phase. The period length, geometric expected-absorption estimate,
and finite-horizon error retain the same fixed target and unrestricted
behavioral deviations. There is no assumed openness of uniform equilibria.

The added explicit trap03 leave gaps are respectively 475/281 and 495/493,
so the support-specific-leaver exclusion is strict and persists locally.
The stationary appendix retains exactly the reviewed fixed-label q₃=0
claim, including boundary hazards; it expressly does not claim exclusion
of all relabelings or all stationary equilibria. The raw definitions,
center data, analytic producer, refinement, and strategic consumer are
self-contained. No dependency on another conference note or export has
been introduced.

All four named source files in the handoff are tracked. The exact-Continue
certificate and consumer and the literal q₃=0 stationary branch match the
previously inspected declarations. I additionally checked the cited
`PairedCubicLocalPersistence.lean` parameterized setup and its import into
the strategic branch file. The handoff identifies actual missing raw-data
and analytic formalization work, without claiming it is already checked.
No unresolved assembly objection remains at the stated artifact hash.

## Independent review: global two-joint selection on the complete R axis

Checked **Global two-joint selection across the complete R axis** through
its final eta-localization addendum in
`notes/CODEX_KREIN__INDEPENDENT_STOPPING_LAW_SELECTION.md`, full-note
SHA256 `ff030f90240591aef25c3ef361297366e4a000dab98928bb6c95bba4410ff3cb`.
Verdict: **PASS**, ordinary mathematics, not Lean certification. I did
not read another review. This check includes arbitrary ξ,η>0, the six
raw caps, both equality exits, and the complete behavioral consumer.
It does not include any subsequent change to the prescribed reward
vectors or caps.

### Exact scope and the interior interval

The claim is for every actual completion of the five vectors (87)
and six inequalities (88), with a,b,c,h₁,h₂,H>0, abc>1, U,V≥1,
arbitrary ξ,η>0, and every real R. Unused entries may be arbitrarily
large or signed; their finite size affects the accuracy mesh, not
the raw existence hypothesis. No strategic witness is supplied.

The displayed inverse of A is correct and strictly positive. Its
equations give

    bν₁−ν₃=h₂,   aν₃−ν₂=h₁,   cν₂−ν₁=H.

These yield the exact expression for ν₃(T−R_low). It is positive
unless U=V=1. In that exceptional case both thresholds equal one
and the two outer exits cover the entire axis. Otherwise the only
constructive interval is R_low<R<T≤1, which makes t∈(0,1).

### The genuine global selector, including arbitrary eta

I independently expanded d₁ and z from (91), obtaining exactly (92).
For fixed y, d₁ strictly decreases and z strictly increases. The
derivative numerator for z is the stated
h₂(1+κ)+h₂κty+ty>0. The zero of d₁ is positive and O(y);
the z=1 root is positive and below one, since z tends to infinity
at x=1 and z(0,y)<1. Their minimum X(y) is continuous, lies
in (0,1), and retains all denominator signs. The comparison
Y<b/(b+1+t) has precisely the stated positive cross-product
difference (1+t)(ab+b+1).

The player-3 residual at x=0 has the sign of
D−[abc+a(c+1)(1+t)+t]y, after positive factors are removed.
At the endpoint X(y), either z=1 or w=0; both give a strictly
negative residual. These signs do not need η≤c.

For arbitrary η>0, the final localization is valid and is essential
to the stated scope. Write G=ηe. If G≥c then

    Φ≤G−x(H+η)/(1−x)<0.

This uses 0≤w<1 and 0<z≤1 on the admissible interval. Since
G starts at zero and is strictly increasing, its G<c region is an
initial interval. There the derivative's w_x term is nonpositive,
the z_x term is strictly negative, and the positive term involving
G_x is strictly smaller than (H+η)/(1−x)². Thus Φ_x<0 at
every possible zero. A unique zero exists before both the hazard
cap and any G=c barrier; the proof never assumes Φ decreases on
the part where G≥c.

This gives a continuous x(y). At zero, the explicit d₁ cap gives
x=O(y). At Y, any positive accumulation value contradicts either
the G≥c bound or strict decrease from Φ(0,Y)=0 inside G<c.
Therefore x tends to zero at both endpoints. No denominator can
approach zero near Y because X(Y)<1.

I independently differentiated at (0,0), obtaining

    Φ_x=−(1+κ)(H+ch₁+h₂/b),
    Φ_y=(1+t)(abc−1)/b.

Together with x=O(y), these give all three ratios (94). This is
an endpoint calculation after global interval selection, not an
assumed continuation of one local implicit branch.

### Pivot crossing and literal phase equations

Using the above ratios, the first endpoint expression is exactly
(1+t)(R−R_low)>0. At the other endpoint I independently obtained

    z(Y)=D/[b(ac+a+1)],
    w(Y)=D/[c(ab+b+1)].

Substitution into F(Y), with ξ(t−1)=t(R−1), gives exactly
(1+t)(R−T)−tξD/(abc)<0. Thus the intermediate value theorem
selects an interior y and all six hazards are proper. No monotonicity
of F itself or uniqueness of this second crossing is required.

The specialized elimination indeed enforces all sixteen policy and
Continue equations. The two rational formulas e,f give the D-joint
owner equalities; Φ=0 and F=0 give the A-joint owner equalities.
The w formula gives the player-1 zero at C and the z formula gives
the player-2 A value. All these use the SAME original table and
successive phase values, not independently chosen continuations.

Every B,C,D coordinate is at least its own singleton. The possibly
negative a₁ at A is handled directly, not discarded. Its immediate
Quit payoff is at most

    −h₁(x+y−xy)≤−h₁x≤a₁.

At D, player 1's Quit payoff is nonpositive while d₁>0. Player 2's
Quit payoff is nonpositive at both joint rows, with values a₂>0 and
zero. The six stated caps include all three nonempty opponent events
at each retained joint row, including simultaneous 03.

### Complete deviations, a negative A value, and one fixed target

Only B and C are refined, and both their endpoint segments have
singleton floors. Their owner values are identically their own
singleton. Hence every microdate has exact Continue, exact policy,
and immediate Quit at most its value plus the stated common δ_n.
The arbitrary unused reward entries merely enlarge the finite
collision constant. δ_n tends to zero for each fixed actual table.

Adding the SAME δ_n to all values gives a Bellman supersolution
even when A has a negative coordinate: Continue transports at most
one copy of the constant, and Quit has no future value. There is
no accumulation over dates. For each possible deviator, its opponents
retain positive total hazard in every period, including both joint
rows. Geometric opponent survival removes the bounded remainder
uniformly over complete history-dependent deviations and Never.

Refinement does not alter the prescribed macro terminal law. The
target V_A is fixed before n and before accuracy. A common value
bound works for all n because the extra values interpolate fixed
endpoints. Expected absorption under any deviation is at most
(2+2n)/(1−ρ_i), yielding the asserted uniform terminal-to-average
bound. One chooses n first and then one threshold for every larger
horizon.

I re-read `QuittingInfinitePathQuitErrorCertificate`,
`quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue`,
`QuittingInfinitePathQuitErrorCertificate.isεAsymptoticNash_and_delivers`,
and `isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError`
in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`.
Their fields require bounded values and exact Continue, not all-phase
singleton floors. The negative A value is fully compatible with the
actual tracked consumer.

### Original-table outer exits and both equality cases

At R=R_low, the positive vector (1,ν) is a homogeneous LCP solution,
contradicting the R₀ consequence of no UE. For R<R_low, every positive
pivot forces the child solution pν in the homogeneous problem and
leaves a negative pivot residual, so the full matrix is R₀. At the
specified offset, the child is (1+p)ν and the pivot residual is
q₀−d(1+p). The two roots and their strict inactive/active conditions
are exactly as stated; their active determinants are D and −Dd.
Their signed sum is zero. This is the degree-not-one exit for the
original reward table, independent of unused nonsingleton rewards.

At R=T the passive inverse weights simplify exactly to
0, [c(U−1)+(V−1)]/(bc), and (V−1)/c. They remain nonnegative
for R≥T. The tracked passive-inverse theorem allows zero weights,
so this equality boundary is included directly, without an openness
or limiting-strategy argument. I re-inspected
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`,
`exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`,
and `PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
The named regular root-sum formula in
`MathUE/LinearProgramming/R0DegreeSum.lean` is the previously checked
degree input. No extra strategic data is required by this composition.

### Both exact stress tables and bounded scope

I constructed both complete tables exactly, setting every unused
coordinate to 37 as specified, and checked all sixteen policy and
Continue equalities in rational arithmetic. Both scalar residuals
are zero, both R values lie in their strict claimed intervals, and
all displayed rates and scalar values match.

For the first table, a₁=−1/25000. Its joint outsider gaps
(value minus Quit), for players 1,2, are

    A: (1497/12500, 50509/5500000),
    D: (593780/5550509, 0).

For the η>c table they are

    A: (297/2000, 523/16000),
    D: (64/403, 0),

and ηe=278385126/1623503635<c, confirming localization rather
than a hidden η bound. These calculations include the allowed
equality at D for player 2 and all actual joint collision entries.

In the constructive interval, trap03 has positive participant
premiums and both participants strictly prefer joining to leaving.
It therefore fails every support-specific-leaver test and the
positive-weight aggregate-leave test at that trap; product-low fails
at its pure product law. Arbitrary completions may create further
traps, including a full greatest core, so the theorem is not limited
to a pair-core class. These are the claimed bounded input distinctions,
not exclusion of every possible old chronology or stationary producer.
No unresolved mathematical objection remains to the consolidated
arbitrary-positive-eta, complete-R-axis theorem at the stated hash.

## Independent delta review: two joint-outsider halfspaces

Verdict: PASS for the final section **Independent joint-outsider rewards
in two raw halfspaces** of the author's notebook, full-note SHA256
`87b5618b037105f3ef0e6721ae6ce68dbada55d232c58088f2c549edc722fe76`.
This is an independent check of the changed producer and comparisons,
not another review of the unchanged outer singleton exits. No other
review of this delta was read. It is ordinary mathematics, not a Lean
build or an unrestricted strategy-class completeness result.

The actual joint outsider entries are now independent parameters
p₁≤a−h₁ and p₂≤0. The first three collision caps must indeed become
min(−h₁,p₁); retaining only their old −h₁ bounds would not justify
the A comparison when p₁<−h₁. The remaining three caps stay zero.
Substitution p₁=−h₁,p₂=−h₂ literally recovers the reviewed base.

I rederived both rational expressions (103) from the actual phase
equations. After multiplying the negative x derivative of d₁ by
its positive denominator, its numerator at the maximal permitted
p₁=a−h₁ is exactly

    h₁(1+κ)+κ(a+t h₁)y>0.

Smaller p₁ only increases it. The derivative of z has positive
numerator h₂(1+κ−y)+ty−(1+κt)p₂y. Thus both required monotonicities
hold on the full admissible region, including both halfspace equalities.
The revised cap does not assume a positive zero of d₁. Its definition
through Z and A_y/B_y is continuous across B_y=0, because the latter
ratio tends to positive infinity from B_y>0. At either type of cap,
the residual is strictly negative. X(y)=O(y) uses only the strictly
positive limiting B_y, so it is unaffected by a later sign change.

Here is an exact test of the new cap case, distinct from the author's
coverage fixture. Take a=100,b=c=2,h₁=h₂=H=1,η=3,ξ=1,U=V=2,R=0,
p₁=99,p₂=−1. Then κ=3/4,t=1/2,Y=266/567 and the constructive
interval contains R. At y=14/297, B_y=0 and Z=545/1077. At y=1/10,

    B_y=−157/80,  X=Z=44/93,  d₁(X,y)=29627/2646>0.

Thus discarding the B_y≤0 branch would genuinely discard allowed
parameters. The z cap handles it without a singularity or a missing
endpoint sign. The ηe<c localization applies unchanged: all zeros
lie in that initial interval, where the derivative is strictly
negative. Compactness at y=Y gives the zero endpoint x=0. All changes
in (103) are quadratic xy terms, and at x=0 they vanish identically;
both the zero-end ratios and the exact other-end pivot sign therefore
remain the already reviewed ones. No continuation of an earlier
selected root is assumed.

For the behavioral delta, the three actual passive A rewards faced
by player 1 are −h₁,a,p₁. Every corresponding forced-Quit collision
entry is bounded above by its passive reward. At D the same caps are
nonpositive, while d₁>0. Player 2 has Q≤0 at both joint rows and
values a₂>0 and zero. These are the only changed comparison steps.
The revised a₂ is strictly positive because p₂≤0. B,C,D retain all
singleton floors; A need not. Exact Continue, subdivision only along
B→C and C→D, and one common supersolution error therefore still
control all behavioral deviations around the same target. I
reinspected `QuittingInfinitePathQuitErrorCertificate`,
`quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue`,
and `isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError`
in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`:
none inserts an all-phase singleton-floor assumption.

I constructed the author's full 15-row rational fixture and checked
all sixteen policy identities and sixteen Continue identities exactly.
The outsider value-minus-Quit gaps at the retained rows are

    A: (199/1000, 1043/32000),
    D: (2943/16523, 0).

The macro C row has player-1 gain 2123/37292 before subdivision,
so the fixture is not silently an exact four-date equilibrium.
The solo subdivision removes precisely this kind of error. The rates,
displayed a₁,a₂,d₁, and both scalar residuals check exactly. Exhaustive
finite subset tests give exactly the traps 03,12,0123, and a strictly
profitable pure deviation at each of the fifteen nonempty coalitions.
All Never also fails. This verifies the claimed disjoint-trap/full-core
and no-pure-exit scope, without claiming exclusion of every stationary
or chronological producer. At p₂=0, the stated pure03 exit is valid
in the constructive interval, including the permitted outsider ties.
No mathematical repair is required.

## Final global two-joint artifact check

Verdict: PASS on the complete standalone
`exports/GLOBAL_TWO_JOINT_CYCLIC_CHILD_UNIFORM_EQUILIBRIUM.md`, 581 lines,
SHA256 `e957a5d04b9a1b1d88b80004521d124350c37b7904eee8e0caa1ba1590c33ff5`.
I read the entire artifact, not only the halfspace addendum. This is
a bounded assembly/delta check against my independent base and
halfspace reviews above. No counterpart artifact review was read.

The assembled raw class is exactly the strongest reviewed one, with
independent joint outsider halfspaces, all six caps, arbitrary positive
η, and every real R. Both singleton-matrix equality exits remain
direct. The revised cap, ηe<c localization, two endpoint computations,
and actual phase equations are all present; no dependency on the
author's notebook or another conference packet remains.

The expanded behavioral proof preserves the decisive restrictions:
only the two solo arcs are refined, their entire value segments retain
the singleton floors, and the two retained joint rows use actual Quit
comparisons. The common error is not summed over time. The displayed
opponent-survival products are correct for all four deviators and
independent of the refinement. The geometric bound controls every
behavioral replacement and gives one sufficiently long-horizon
threshold for the same profile and fixed target. The finite-law
censoring corollary changes only marginal tail masses and uses the
correct opponent-only coupling for any fixed full deviation.

All three assembled tests have the claimed scope. The nontrivial
full-core fixture is the one independently evaluated in the delta
review above. The negative-A test is explicitly an algebra/regret
test with a pure grand-coalition exit, not a noncoverage witness.
The additional negative-B test is exact: its parameters give
B_y=−169/2000, Z=52/113 at y=1/5, with R_low=−799/304 and Y=2/5.
Thus the assembled proof really retains the nonvanishing-d₁ cap case.
The p₂=0 boundary is honestly identified as permitting a pure03 exit.

Every full Lean source path in Section 9 is tracked and belongs to
the previously inspected source chain. The handoff asks for the new
raw selector and its cap, not an assumed equilibrium, favorable root,
or new semantic compiler. No new formalization status is asserted.
No assembly correction or unresolved mathematical objection remains
at the exact 581-line artifact and hash above.

## Independent review: mixed pair traps and boxed larger supports

Verdict: PASS on **Several negative-index pair traps with boxed larger
supports**, notebook SHA256
`6744da5f4981bdee9ed89beb1637944a8bd7ebf2187e73167891682836acff7d`.
I checked the complete raw criterion, producer, analytic proof, weak
strategic boundary and coverage fixture without reading BROUWER's
review. The corrected standalone assembly is bound separately below.

### Full root relation, genericity and every local index

The larger-support charge uses one common box for every larger trap.
Both sure-hazard cases are handled before odds division. The sum of
active premium equations retains every intermediate product with its
explicit nonpositive coefficient. The symmetric-mean bound and strict
charge then exclude an all-high root on every larger support. Nontrap
support gives a low active endpoint with no global sign condition.

I independently expanded the outsider gap at a pair candidate. Its
four product masses have numerators dᵢdⱼ, dᵢ(vⱼ−sⱼ),
dⱼ(vᵢ−sᵢ), (vᵢ−sᵢ)(vⱼ−sⱼ) over αᵢαⱼ, exactly as in
(108)–(109). The last coefficient is the ACTUAL joining difference
at A∪{k}; it cannot be dropped. The nonzero coefficient −dᵢdⱼ
of v_k proves each tie polynomial is genuinely nonzero, regardless
of its other reward coefficients. Finite simultaneous exclusion is
open dense before roots are chosen. It is source perturbation, not
reward perturbation or a strategic realization assumption.

At a generic bad root, semi-sure pair support is impossible by the
nonzero joining gap, and a fully sure pair was separately discharged.
There is at most one remaining root per pair support. Outsider Nash
gaps are strictly negative, so the clipped outside rows are constant
zero in an ambient neighborhood. The full derivative has its identity
outside block and the two-by-two block with determinant −αᵢαⱼ<0.
No larger-coalition derivative is assumed to vanish in the starred
entries. The affine comparison therefore gives local degree −1,
including roots on coordinate faces of the unit cube.

The enlarged box contains those faces in its INTERIOR. The homotopy
to a constant cube center gives degree +1 on that enlarged domain.
Under the all-bad assumption the root set is finite and nonempty,
so excision and finite additivity really yield −K, not an informal
parity assertion. I inspected `ambientDegree_additive` and
`ambientDegree_excision` in
`MathUE/Topology/AmbientDegreeProperties.lean`, together with the
named homotopy and affine normalization in
`MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`.
These are actual degree statements, not supplied parity interfaces.

Generic sources can approximate any boxed source with a strict
singleton deficit from the box interior while keeping that deficit.
Closed Nash inequalities and compact hazards pass to an exact limit;
the finite union of low successor sublevels is closed. Absorption
cannot disappear at the limit, because all Continue is not Nash at
the limiting source. Thus the stated selected return, and not an
all-root return claim, survives every tie and box boundary.

### Minimum, weak gaps, and semantic endpoint

The selected successors lie in precisely the same D on which H is
minimized. The singleton probe stays boxed even at upper faces;
the binding corrections cancel on differentiation. A unique binding
coordinate contradicts that probe, while two bindings give the needed
nonnegative one-sided derivatives. The signed displacement and Quit
bound give ε≤(3M+B)a without a protected floor. The resulting
backward derivative contradiction is valid.

The actual Fin4 no-UE polynomial is restricted to the exact relation
and then to the SAME smaller box. Nonnegative own singletons imply
normality without participant-premium assumptions; all-zero singletons
are handled directly. The proof has the fixed-target/full-behavior
uniform conclusion, not only a stationary or terminal verifier.

For weak products, each ordered passive singleton entry changes only
its own pair gap. Participant rewards and own singletons stay fixed,
so the ENTIRE trap list and all P coefficients stay fixed. Every
larger trap's singleton-layer L sum changes by at most (m−1)δ;
no other L layer changes. Reducing G by this amount loses precisely
K(m−1)δ in the charge, while the reward bound increases by at most
δ. Both strict inequalities in the stated perturbation budget are
therefore sufficient simultaneously. The reward-closure declaration
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
in `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`
allows varying nearby targets and selects one limiting target before
accuracy. No singular-root index is used. The asserted weak result
remains strategic; the packet does not claim weak analytic exclusion.

### Independent falsification tests and structural clarification

I independently derived the matching restriction while checking the
notebook: overlapping pair traps ij and ik create trap ijk, whose
singleton P coefficient at i is the sum of two strictly positive
premiums. This contradicts its larger-trap bound. Thus the raw class
does not permit an arbitrary overlapping pair graph; pair traps are
disjoint, and Fin4 has at most two. The corrected standalone already
contains this proof and exact scope.

Here is a separate exact stress table where TWO bad pair roots really
coexist at the same below-floor source. It tests the finite count,
rather than merely repeating a unique-bad-root calculation. All own
singletons are zero. Set

    r(0)=(0,2,20,20), r(1)=(2,0,20,20),
    r(2)=(20,20,0,0), r(3)=(20,20,0,0).

At every nonsingleton proper coalition, set participant coordinates
to −10 and passive coordinates to 20, except that participants of
01 and 23 receive 1, and r₀(23)=−11. Let every grand coordinate
be 1/100. These rules specify the full table. The only traps are
01,23,I. Their pair gap vectors are (−1,−1) and (1,1).
For I, singleton P coefficients are −19, pair coefficients −20,
and triple coefficients 1/100. Singleton L coefficients are
−61,−61,−59,−59; pair L is −29 at23 and −60 elsewhere;
triple L is −1999/100. Thus D=10,τ=1,G=10,Lstar=10 give
charge 440√10>80 with M=20. Pair01 cannot be pure Nash because
both owners leave; pair23 is blocked by player 0's gain 1.

At v=(−1,−1,1,1), the following full exact Nash roots both have
successors strictly above all four singletons:

    q=(1/2,1/2,0,0),
    Q=(1/2,1/2,−15/2,−15/2),
    C=w=(1/2,1/2,61/4,61/4);

    q=(0,0,1/2,1/2),
    Q=(−15/2,−15/2,1/2,1/2),
    C=w=(7,59/4,1/2,1/2).

All outsider gaps are strict, all candidate denominators nonzero,
and both full local determinants are −4. This source is generic
for both pair traps. A good root also exists explicitly: q=(1,0,0,0)
has successor (0,2,20,20), and its four Quit and Continue endpoints
are (0,1,−10,−10) and (−1,2,20,20). This example validates the
need to count multiple possible bad roots, while expressly refuting
any strengthening to return by every root. Its zero singletons make
it an analytic/counting regression, not a new strategic-coverage claim.

### Coverage fixture and final artifact

I reconstructed the author's 15-row fixture exactly. Its traps are
03,12,I, pair gaps (4,4) and (4,1), and the three P layers and
all listed L coefficients match. The raw charge is 400√10>45.
Every listed pure improvement is valid. All fourteen sure-coalition
child witnesses were checked with exact rational arithmetic; the
complete-deviation justification follows because either another
quitter absorbs immediately or a sole deviating owner faces Never
and cannot beat its nonnegative singleton. The omitted gains and
zero Never masses are exact.

The matrix, passive-inverse and response expressions check. The
nonnegative-floor test sum is exactly −17∑λᵢ. The greatest core
is full while pair traps are present, so this fixture lies outside
BOTH separate raw classes: the theorem is genuinely more than their
union. The bounds concerning protected floors, product-low, the
specified two-joint template and universal child-debt certificates
retain their stated scope. There is no claim that every stationary
or selected chronological construction has been excluded.

Final entire-artifact verdict: PASS on
`exports/MIXED_PREMIUM_TRAPS_UNIFORM_EQUILIBRIUM.md`, 596 lines,
SHA256 `ba041078646ba8fc865eda2d959ac4018f0ea6ec95b3a310f93a368f81cbee0f`.
I read the complete standalone in addition to the notebook proof.
The matching clarification is correct; all mathematical hypotheses
and proof mechanisms are the reviewed ones. The expanded degree,
minimum, reward-closure and coverage arguments are self-contained.
Its three-zero-singleton fixture is correctly distinguished from a
nearby positive-singleton interior point. The Lean handoff specifies
the actual raw producer chain, with no supplied root or equilibrium
hidden among the inputs. No conference-note dependency or new Lean
certification claim has been introduced. No mathematical repair remains.

## Independent review: joining-attractive triple cores

Verdict: PASS on the complete notebook section **Joining-attractive triple
cores: negative index without a charge box**, at whole-notebook SHA256
`ca96e6bdb54f476e8a50f4d61747be18af1b0f7cacb2c76984cdb36002119fee`.
No counterpart review was read. This is a full mathematical, raw-source
and semantic audit, not a Lean build or a strategic completeness claim.

The claim checked is the literal Fin4 fixed-target uniform-equilibrium
conclusion for nonnegative own singletons, greatest premium core of size
three, and nonnegative insertion differences on every nonempty coalition
inside that core. Participant premiums, including those of core members,
may be negative. Strict insertion differences first give analytic full-root
potential exclusion; weak differences use reward closure only.

### Raw support, sure hazards and the full local index

The signed nontrap argument is valid. A nontrap active support has an
active member with every participant reward on that support at most its
singleton; exact Nash therefore gives a low successor coordinate. Every
bad support must be a pair or the greatest triple core. For an outsider
k, a participant reward above its singleton against any subset of C would
make C∪{k} a trap. Thus at a bad root its actual forced-Quit endpoint
is at most its singleton and its full inactive gap is strictly negative.
No floor on the outsider's continuation or equality of its participant
rewards is being assumed.

The sure-hazard cascade is exhaustive. A sure core member makes every
other core member face a nonempty core coalition with probability one;
strict insertion then forces each to be sure. Pure C, if full Nash, is
source-independent and yields an immediate actual equilibrium. Otherwise
every active hazard at every bad root is interior. This rules out the
partly-sure cases before differentiating.

I derived the odds identity and triple derivative directly from the full
endpoint sum. At a root the derivative of the survival prefactor multiplies
zero, leaving exactly (113), with six strictly positive off-diagonal entries
and zero diagonal. Hence det(−Dg|C) is the negative sum of the two directed
three-cycle products. This is the full determinant after adjoining the
strictly clipped outsider rows: their blocks are 0,Id, while the unrestricted
upper-right block retains all simultaneous outsider interactions. The proof
does not replace those interactions by a two-player subgame.

For a pair the active determinant is −α_iα_j<0. The unused core member
is not covered by the outsider bound and really can be tied. Formula (115)
is the full gap after multiplication by α_iα_j, including the actual triple
reward. Its coefficient of v_k is −d_i d_j≠0. A finite product of the
corresponding nonzero polynomials gives simultaneous dense-open tie avoidance
without a supplied genericity theorem or a reward perturbation.

At a generic below-floor annotation every root absorbs. Under the proposed
no-return contradiction, EVERY root is bad, so every root has a nonsingular
full derivative and local index −1. Compactness plus isolation really makes
this entire root set finite; it is not an assumption about one selected
branch. On the enlarged ambient cube the clipped map always has image in
the unit cube. The homotopy to its center is boundary-fixed-point-free,
giving total index +1. Excision and finite additivity then contradict −K.
There is no half-index issue at zero outsider hazards.

The subsequent limit restores every original boxed source with a strict
singleton deficit. The deficit excludes an all-Continue limit, the Nash
inequalities and low-coordinate union are closed, and the reward/source
convex combination stays in the identical box. No continuity of a selector
or behavioral realizability of the annotation is required.

### Minimum, weak boundary and actual semantic consumer

The same-D minimum proof is complete. The collision-adjusted singleton
probe is exact even with signed premiums; its source correction cancels
in the first-order difference. Upper-box faces cause no missing term or
source escape. A unique binding singleton is excluded by the face inequality;
with at least two bindings the relevant inward partial derivatives are
nonnegative. The signed bounds Q_j≥s_j−2Ma and displacement≤(M+B)a
give ε≤(3M+B)a. The returned successor belongs to the SAME D, so the
minimum and drift contradict the nonnegative partial derivative.

For weak insertion comparisons, each changed coordinate is passive to
its own receiver. None of the participant rewards or own singletons
changes, so every strict premium witness, every trap, and the greatest
core remain exactly the same. Each of the nine compared gaps increases
by δ; no participant endpoint is accidentally changed by another edit.
Reward closure gives one fixed uniform target, not a target depending
on the requested accuracy. This establishes weak strategic coverage,
not an unproved weak local determinant statement.

The exact inspected source composition is valid. In
`MathUE/FiniteCoalitionPremiumCore.lean`, the trap union, subset-core and
`not_positive_on_core_insert` statements have the needed signed scope.
`exists_successor_le_singleton_of_exactRoot_nontrap_support` in
`UniformEquilibrium/Quitting/Classification/CommonQuittingPremiumLeaver.lean`
adds no nonnegative-premium assumption. The topological inputs are actual
`ambientDegree_homotopy`, `ambientDegree_affineRootField_eq_sign_det`,
`ambientDegree_excision`, `ambientDegree_additive`, and
`ambientDegree_of_selfMap_eq_one` in the three named AmbientDegree modules;
the new full Jacobian and tie avoidance are proved in the manuscript.

`isQuittingNormalPlayer_of_singleton_nonneg` in
`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean` supplies
normality. The declaration
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`
produces the actual polynomial under no UE and a positive singleton.
`isQuittingFullExactRootPotential_of_robustPotential` and `.mono_box`
in `UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`
retain the SAME function on M+1. The signed face input is
`IsQuittingFullExactRootPotential.singletonFace_drift` in
`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`.
The closure declaration is
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables` in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.
No supplied root, equilibrium, regularity hypothesis or unimplemented parity
interface has entered the final raw-data implication. Finite-player analytic
scope and Fin4 strategic scope are correctly separated.

### Exact falsification attempts and stronger inventory

I recomputed the complete fixture with rational arithmetic. Its sole trap
is123, its insertion gaps are (1,1,4) for each core player, and every listed
pure deviation is profitable. The signed and weak variants have gaps
(1/2,1,4) and (0,1,4), up to cyclic order, without a new trap. Raising
the specified three participant entries to1 gives exactly the overlapping
traps12,13,23,123 and gaps (1,2,4), again up to order. No disjointness
assumption has leaked in from the earlier boxed theorem.

The matrix and all inverse entries agree. For the degree calculation,
at offset (1,−1,−1,−1) any vanishing child coordinate forces a negative
residual in the next child row. Thus all three child coordinates are
1+p_0; the pivot residual is2+p_0, forcing p_0=0. The unique regular
root is therefore the one displayed. The same argument at homogeneous
offset makes a positive pivot impossible and then forces the child zero.
The R₀/degree-one claim and the negative passive inverse coordinate check.
All thirteen block-row witnesses and the remaining full response polynomial
were independently recomputed; F_3−F_1=−t³ exactly. The other source
exclusions keep their bounded stated scope. In particular the manuscript
does not claim failure of every proper-child universal debt certificate.

The assembled actual triple-root test is also exact: at its stated v and q,
Q_0=171/320, C_0=3559/3200, all three active endpoints equal the displayed
successor coordinates, and the full determinant is −2254/171. It directly
refutes an all-roots-return strengthening within the admitted class.

An additional independent tied-pair regression is recorded self-contained
in Section 23 of `../notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`.
Use the overlapping variant and

    v=(9/10,2/3,1/3,13/9), q=(0,1/4,1/4,0).
    Q=(9/16,1/4,3/4,1), C=w=(191/160,1/4,3/4,1).

It is bad, has a strict outside-core gap −101/160, and has an EXACT
inactive-core tie. The active determinant is −32/9 but the full clipped
map is nondifferentiable; increasing v_3 by η makes the latter gap
−9η/16 and validates the full negative determinant. This tests the
specific place where genericity is needed, rather than merely asserting
that a tie polynomial might vanish.

Section 23 also proves an optional strengthening: after excluding pure C,
there is AT MOST ONE bad root at a fixed source, even across different pair
and triple supports and without genericity. In odds, each core equation
is a function f_i of the other two coordinates with all positive coefficients.
Two distinct triple solutions contradict strict coordinate monotonicity;
a pair and a triple would violate the unused player's Nash inequality;
two distinct pairs give reciprocal strict inequalities b_k>c b_j and
b_j>b_k/c. The manuscript's existing finite-isolation proof is already
sufficient; this stronger inventory is not a required repair or a raw-class
extension and must not be read as extending the sign argument to full cores.

### Bounded entire-artifact check

Final artifact verdict: PASS on all 475 lines of
`exports/JOINING_ATTRACTIVE_TRIPLE_CORE_UNIFORM_EQUILIBRIUM.md`, SHA256
`2e9876294d6ee948c3dcfdd1472c6553951e22f4a027c15c668151ae2d6b2c94`.
I read the entire standalone after the notebook argument. Its substantive
assembly additions are the full endpoint definitions, explicit partition
table, actual boxed bad triple root, exact strategic quantifiers and Lean
handoff. All check. The mathematical packet is self-contained and cites
tracked source inputs, not another conference note or a frozen export.
The weak boundary, source-independence of the pure exit, and finite-player
versus Fin4 scopes remain unchanged. No mathematical repair is requested;
the optional uniqueness observation above is outside the frozen artifact.
