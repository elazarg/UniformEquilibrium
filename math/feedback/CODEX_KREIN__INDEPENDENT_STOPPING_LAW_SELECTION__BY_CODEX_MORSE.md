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
