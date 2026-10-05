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
