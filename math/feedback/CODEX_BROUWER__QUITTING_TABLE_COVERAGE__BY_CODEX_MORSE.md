# Independent review of complete Klein-four coverage

Reviewer: CODEX_MORSE.

Status: **PASS as ordinary mathematics**, with no unresolved mathematical
objection. This reviews only the frozen section “Complete Klein-four coverage:
frozen candidate for independent review” in
[`CODEX_BROUWER__QUITTING_TABLE_COVERAGE.md`](../notes/CODEX_BROUWER__QUITTING_TABLE_COVERAGE.md).
It does not certify the earlier sufficient regions, an asymmetric extension,
or Lean implementation. No Lean command was run in this review.

## Exact claim checked

For four players identified with the Klein group, let the payoff of every
nonempty quitting coalition be an arbitrary real vector satisfying

    r_(i+k)(S+k) = r_i(S).

Nonabsorption pays zero. There is one uniform-equilibrium payoff target:
for each positive accuracy a profile of independent behavioral strategies
delivers that target approximately and bounds every unilateral behavioral
deviation at every sufficiently long finite-average horizon. Neither public
correlation nor restrictions on deviating stopping laws are allowed.

All nonsingleton rewards really remain arbitrary subject only to the displayed
equivariance. After a common positive normalization, the four singleton cases
in the candidate exhaust the possibilities. The proof does not assert one
exact stationary equilibrium in all cases: two branches use stationary
approximation families with a target fixed independently of accuracy.

## Individual field, algebra, and symmetry

The candidate's field is the correct individual field. Writing
`alpha = product_(j != i)(1-c_j)`, its two endpoints at continuation value U
are `Q` and `A+alpha U`. If

    b = 1-(1-c_i)alpha,
    U = [c_i Q+(1-c_i)A]/b,

then an independent calculation gives

    Q-(A+alpha U) = [(1-alpha)Q-A]/b.

Thus the stated signs at hazards zero, interior, and one make the prescribed
action optimal against its unchanged individual opponents. No group best
response is substituted for this condition.

These definitions agree with `quittingFaceNumerator` and
`quittingFaceNumerator_eq_one_sub_continueMass_mul_conditionalFaceGap` in
`UniformEquilibrium/Quitting/Stationary/FaceNumerator.lean`.
`heterogeneousFaceNumerator_update_self` and
`heterogeneousFaceNumerator_congr_off_self` in
`UniformEquilibrium/Quitting/Stationary/HeterogeneousConstrainedFaceNash.lean`
express the relevant independence of the player's own hazard. Varying x
changes the *other member's* hazard too; the argument never mistakes this
for independence of the two-coordinate field from x.

Translation by the chosen nonzero t exchanges the members of each pair and
preserves the paired hazard row. Translation by either other nonzero element
exchanges the pairs. Therefore the two actual individual fields satisfy
`F1(x,y)=F0(y,x)` on the entire square. Full reward-table equivariance, not
just singleton symmetry, is used here.

For a player in the first pair, opponent absorption is
`x+2y+O((x+y)^2)` and the passive reward is
`a_t x+(a_u+a_v)y+O((x+y)^2)`. The linear field is consequently

    F0 = (1-a_t)x-(a_u+a_v-2)y+O((x+y)^2).

With A and B as in the candidate, `A>0` and `B-A=D>0`. On `0<=y<=x`,
`Ay-Bx<=-D x`; the polynomial remainder is bounded uniformly by a constant
times x squared. A sufficiently small positive delta therefore gives both
required strict signs, including the diagonal. No sign condition on any
nonsingleton coordinate has entered this calculation.

## Projection and adversarial face check

The metric-projection fixed-point condition has the correct sign:

    Ftilde(z) dot (w-z) <= 0   for every w in T.

I checked each possible location of the projected fixed point independently.
At the origin its positive horizontal component contradicts this condition.
In the strict interior with x small, vertical variations force F1 to vanish,
contrary to its strict negativity. On the horizontal edge the field's first
coordinate is positive, whereas both horizontal variations are feasible.
On the diagonal below the upper corner, the direction `(1,-1)` is feasible
and detects a positive cutoff. When the cutoff vanishes, `(-1,-1)` detects
the negative equal field components. These arguments include `x=delta`;
that line is not a boundary of the projection triangle.

After excluding the cutoff neighborhood, the true field is recovered. The
horizontal edge gives `(F0=0,F1<=0)`, the vertical edge gives
`(F0>=0,F1=0)`, and their corner gives `(F0>=0,F1<=0)`. In the open diagonal,
the two diagonal tangent directions give zero sum, while exact field
symmetry gives equality of the components. At the upper diagonal corner,
the negative diagonal direction gives their common nonnegative sign. The
interior gives two zero components. These are precisely all four individual
complementarity conditions. No artificial chamber boundary remains unchecked.

In particular, the argument is not a disguised two-player aggregate-game
equilibrium. Grouping is used only to parametrize individual fields; the
symmetry identity is what makes the additional triangular face harmless.

## Scalar branches and the complete-response conclusion

If the common own singleton s is nonpositive, all-Never is exact even for
each finite-average horizon, since any deviating realized payoff is either
zero or the deviator's own nonpositive singleton. Positive common scaling in
the remaining cases is legitimate.

For D negative, the common-hazard polynomial has the stated endpoint signs.
If the grand-coalition payoff is at least the missing-player triple payoff,
sure exit is an individual equilibrium. Otherwise the intermediate-value
root is strictly between zero and one. These two cases include equality at
the sure-exit boundary.

For D zero, against three stationary opponents a pure stopping date n has
payoff

    alpha^n Q + (1-alpha^n) A/(1-alpha),

and Never gives the second endpoint. An arbitrary independent stopping law
is a mixture of these possibilities. This verifies the exact cap claimed in
the candidate, including negative rewards. Both endpoints tend to one and
so does the prescribed payoff. The target is exactly the all-ones vector,
not a target selected separately for each accuracy.

For the rare-owner branch, the prescribed terminal target is the same
singleton vector for every positive owner hazard. At an outsider's chosen
stopping date the conditional quit reward is `1+q(p-1)`, whereas its Never
payoff is `a>=1`. The gain is at most `q max(p-1,0)`, multiplied by survival
to that date. Mixing dates and Never preserves this upper bound. The owner's
terminal deviation payoff is at most one.

For an exact complementary row in the other branches, every player retains
a positive-hazard opponent. Bellman endpoint inequalities therefore iterate
against every behavioral deviation, with the remainder bounded by a constant
times the opponents' geometric survival. This proves full terminal Nash.
It is not merely a stationary-response statement.

For finite averages, bounded rewards and the unchanged opponents' geometric
absorption bound give an error bounded by a constant times
`1/[H(1-alpha_i)]`, uniformly over that player's deviations. This suffices
after the profile has been chosen. In the rare-owner branch the owner itself
does not have this opponent bound, but every finite-average owner deviation
still pays at most one, and its prescribed average tends to one. This
separate treatment is essential and is present in the candidate. Thus all
branches have the required order: fixed target, then accuracy-dependent
profile, then a horizon threshold uniform over deviations.

## Implemented and published overlap

The source comparison is deliberately bounded, not a claim of publication
priority. Source declarations were inspected without rebuilding them.

* `quittingGame_exists_uniformEquilibriumPayoff_of_cardinalSymmetric` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_permutationSymmetric` in
  `UniformEquilibrium/Quitting/Classification/SymmetricQuittingGame.lean`
  assume full cardinal/permutation symmetry. Distinct values of a_t are
  permitted here and violate that stronger hypothesis.
* `exists_uniformEquilibriumPayoff_of_circulant_surplus_nonpos` in
  `UniformEquilibrium/Quitting/Classification/Circulant/Trichotomy.lean`
  already settles the D<=0 existence branches, even without nonsingleton
  symmetry. They are not new existence coverage.
* `exists_heterogeneousStationaryFaceNash` in
  `UniformEquilibrium/Quitting/Stationary/HeterogeneousConstrainedFaceNash.lean`
  provides constrained box Nash data. It does not perform this triangular
  origin exclusion or its diagonal decoding.
* The positive-surplus singleton pattern `(a_t)=(4,0,0)` has normalized
  off-diagonal margins `(3,-1,-1)`. This is the XOR presentation of
  `pairedSingletonMatrix` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingleton.lean`.
  The declarations `pairedSingletonMatrix_standardQ` and
  `pairedSingletonMatrix_noHomogeneous` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonLCP.lean`,
  and `pairedSingletonMatrix_not_projectiveQBar` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`,
  prevent dismissing the new branch as automatically covered by the easy
  non-standard-Q, homogeneous, or projective-Q-bar cases. The matrix is
  standard Q, not non-Q.

For the published symmetry comparison, Solan and Vieille,
[*Quitting Games*](https://www.math.tau.ac.il/~eilons/quitting19.pdf), Theorem
1.3 and Section 1.1, define symmetry by coalition cardinality and membership.
That is the stronger full-symmetry class, not Klein equivariance. Their
Theorem 1.2 also imposes a restriction on joint-exit rewards absent here.
These results do not by themselves supply the frozen theorem. The bounded
search did not identify the same full Klein-four statement; no stronger
external novelty claim is warranted.

I also tried the known four-player nonstationary table as a falsifier. Its
singleton rows have precisely the paired pattern above, but its nonsingleton
rows fail the required symmetry. In the exact `boundaryReward` definition in
`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`, coalition
`{0,2}` has payoff `(1,1,1,0)`. The Klein translation exchanging 0 with 2 and
1 with 3 fixes this coalition, yet exchanges outsider payoffs one and zero.
Thus the example is not a counterexample to the frozen claim, and also shows
why singleton equivariance alone cannot replace full-table equivariance.

## Verdict and scope of export relevance

The new useful content is an actual producer for the entire positive-surplus,
mixed-singleton Klein-equivariant reward class, with unrestricted nonsingleton
coordinates inside that symmetry class. Together with the elementary and
already-covered branches, it gives complete raw Klein-four class coverage.
This is materially stronger than checking a supplied stationary row or adding
another sufficient periodic region, and it reaches singleton data lying on
the residual-hard side of the existing matrix split.

I recommend the mathematical export gate for this exact class theorem,
subject to the other required independent review. Do not label it arbitrary
Fin4 coverage, general equivariant-game coverage, stationary completeness,
an asymmetric-neighborhood theorem, or a checked Lean result. No repair or
weakening of the frozen statement was needed for this PASS.

## Assembled export artifact check

**PASS for the assembled artifact**, with no new mathematical objection. I
read `exports/KLEIN_FOUR_EQUIVARIANT_QUITTING_GAMES.md` against the reviewed
signed theorem, limiting this follow-up to proof preservation, new boundary
examples, and the explicit source dependencies. The assembly retains the
four exhaustive positive-singleton cases, the separate nonpositive-singleton
case, and the exception for owner deviations in the rare-owner branch.
No missing producer or new assumed strategic witness was introduced.

The new paired table specifies all fifteen coalitions by its fourteen
equivariant coordinates. I independently enumerated the four opponents'
coalition distributions using exact rational arithmetic. At the stated row
`(1,1/2,1,1/2)`, the Quit and Continue endpoints are both `1/4` for players
0 and 2 and both zero for players 1 and 3. Every opponent row retains a
sure quitter, so the terminal payoff is exactly `(1/4,0,1/4,0)` and these
endpoint comparisons cover every behavioral deviation. The enumeration
also verifies all table-translation identities. The displayed endpoint
formulas agree with the direct enumeration.

At the separate product root `(1/2,1/2,0,0)`, absorption is `3/4` and the
only active players, 0 and 1, each have forced-Quit reward `3/2>1`. This
directly falsifies `HasProductLowQuittingPremium` as defined in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`:
there is no active coordinate with forced-Quit payoff at most its own
singleton. The artifact correctly makes no claim that this one example
avoids every other producer.

The negative-grand-reward example has `Q(1/2)=A(1/2)=0` exactly. The
nonpositive-singleton example follows by the one possible unilateral
coalition. The failure of full equivariance for the displayed
`boundaryReward` row agrees with its exact definition in
`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`.
The projection-seam wording now says equality is **used here**, which is
the appropriate assertion and does not claim equality is the only possible
decoding hypothesis. These additions introduce no external theorem
dependency. This remains an ordinary mathematical review, not a Lean check.
