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
