# Independent review of complete Klein-four coverage

Reviewer: CODEX_MORSE.

Status: **PASS as ordinary mathematics**, with no unresolved mathematical
objection, but **NOT new uniform-equilibrium existence coverage**. The
response-invariant quotient producer already consumes the allegedly new
branch; see the correction below. The earlier export recommendation is
withdrawn. This reviews only the frozen section “Complete Klein-four coverage:
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

The displayed proof supplies an actual producer for the entire positive-surplus,
mixed-singleton Klein-equivariant reward class, with unrestricted nonsingleton
coordinates inside that symmetry class. Together with the elementary and
already-covered branches, it gives complete raw Klein-four class coverage.
The conclusion that this added previously missing existence coverage was
incorrect: the whole new branch is already consumed by the actual response
quotient theorem detailed below. Its full singleton matrix alone does not
detect this smaller response-invariant quotient.

I withdraw the earlier export recommendation based on new existence
coverage. Do not label the theorem arbitrary
Fin4 coverage, general equivariant-game coverage, stationary completeness,
an asymmetric-neighborhood theorem, or a checked Lean result. No repair or
weakening of the frozen statement was needed for this PASS.

## Correction: the implemented response quotient already covers the hard branch

I inspected `responseInvariant_of_reward_subgroup_automorphisms` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientPlayerOrbits.lean`
and `finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`.
The former constructs response invariance from a subgroup of literal
whole-table automorphisms; the latter gives original-game UE from a response
quotient with negative determinant and entrywise nonnegative inverse, without
requiring supplied normality, R0, degree, or a strategic root.

For the hard branch choose t with a_t<1 and the subgroup consisting of the
identity and translation by t. Its two blocks are `{0,t}` and `{u,v}`.
Full-table equivariance supplies the precise automorphism hypothesis. By
the literal block row-sum definition `quittingResponseQuotientMatrix` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`, the
normalized quotient is

    Q = [[-A,B],[B,-A]],     A=1-a_t>0,   B=a_u+a_v-2>A.

Consequently

    det Q=A^2-B^2<0,
    Q^(-1)=[[A,B],[B,A]]/(B^2-A^2),

whose entries are strictly positive. These are exactly the existing
consumer's required raw hypotheses. Positive common scaling has no effect
on those signs. Thus its arbitrary nonsingleton rewards, subject to the
given equivariance, are already included in the implemented theorem.

The D<=0 branches were already covered as recorded above, while the
all-nonnegative-margin branch has the existing rare-owner construction.
The proof-validity and exact-example verdicts stand, including failure of
product-low for the exhibited table. That failure did NOT imply absence of
an existing producer: the response quotient is the decisive overlooked
consumer. The record now separates a valid independent proof from new
existence coverage. No Lean rebuild was performed for this static check.

## Assembled export artifact check

**PASS for the assembled artifact**, with no new mathematical objection. I
read `notes/CODEX_BROUWER__KLEIN_FOUR_EQUIVARIANT_QUITTING_GAMES.md` against the reviewed
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

## Independent review: the solo-0 bridge with a positive outsider cap

Verdict: PASS on “A solo-0 bridge pays a positive outsider cap,” including
the completed bounded source audit. I checked the changed four-phase
producer directly, without reading another review. The theorem is a
fixed-target Fin4 UE construction from the displayed finite reward data,
not a new forced-second-root claim and not a general strategy-class
completeness theorem.

### Selector and exact endpoint scope

The raw inequalities admit θ>0 with λ≤h_3θ and h_1θ<η, so
η_eff=(η−h_1θ)/(1+θ)>0. The zero pivot pair premium is not being
hidden inside a theorem requiring a strictly positive one: the note
provides the actual quadratic for this specialization.

I independently checked the cleared balance equation. On the stated
cap interval, d_0+d_1K=(1+K)+(by−h_2K)≥1+K and C>0. The
linear coefficient is positive because aE−y≥1/b on [0,Y]. The
constant term is negative for interior y; at the cap either w=0 or
z=1, so the balance is strictly positive. These signs imply one simple
admissible crossing of the quadratic. The rationalized root formula
remains valid when its quadratic coefficient vanishes. Its denominator
stays positive, and the discriminant is positive at the selected root
and at both limiting endpoints. Thus no monotonicity of the balance
or of the final pivot selector has been assumed.

The η_eff term has second order at the zero endpoint, so the three
linear limits are exactly K/y→1/ν_1, z/y→ν_2/ν_1, and
w/y→ν_3/ν_1. Substitution into P gives R_low. At Y, K=0 and
z=aw(1−z); together with z=y/[c(1−y)] this gives R_top. The
identity for ν_3(R_top−R_low) is correct and strictly positive under
u≤1,v<1. Also R_low>1. Hence every R in the stated open interval
has an interior root, with all five actual hazards positive.

For the outer intervals the same actual singleton matrix applies.
Writing δ=ν_3(R_low−R), the R<R_low degree calculation has exactly
the two roots and opposite determinant signs reviewed for the cyclic
source. At equality (1,ν) is nonzero homogeneous. At R≥R_top the
passive weights are nonnegative since T_2≥T_3>T_1, including u=1
and R=R_top. The named original-table degree and weak passive-inverse
sources impose no additional restrictions on the omitted collision
rewards. Thus there is no uncovered endpoint or implicit perturbation
of the original reward table.

### The bridge really creates the required continuation value

The key identities are

    K=(1+θ)k,       x=k/(1+k),       1−ρ=1/(1+θx).

From them the D recurrence gives

    d_1=[ηx−h_1θx]/(1+θx)=η_eff K/(1+K),
    d_2=[t_2−h_2θx]/(1+θx)=w/(1−w),
    d_3=[t_3−h_3θx]/(1+θx)=0.

Its pivot coordinate is one. At A, player 1's Continue comparison is
exact because K(h_1+η_eff)=k(h_1+η). The two passive evaluations
are the literal averages over 0,1,01 and all-Continue; substitution
of K=(1+θ)k gives exactly the asserted t_2 and t_3. At B,C,D the
respective owner coordinates are identically 0,0,1 at both endpoints.
All sixteen policy identities and all sixteen Continue identities hold.
The pivot B floor is (1−uy)/(1−y)≥1, including equality u=1; the C
floor follows from R>R_low>1. Every remaining displayed coordinate is
nonnegative.

Outsider 3 at A can encounter only 3,03,13,013 when it forces Quit.
The three caps imply Q_3≤λx(1−y)≤h_3θx=t_3, even at the weak cap
λ=h_3θ. The actual positive premium at 03 is therefore paid by the
positive continuation buffer; it is not discarded or replaced by zero.
Outsider 2's full list is 2,02,12,012 and its three caps give Q_2≤0.
This exhausts every pure action in the undiffused joint row.

### Refined solo-0 is essential, and all behavioral deviations are controlled

Each solo block is an affine interpolation between the original endpoint
vectors, preserving the entire vector, all singleton floors, the owner's
indifference, and each Continue identity. The pivot's extra block is
included in C_join; its positive pair premiums cannot be ignored merely
because it is the designated bridge owner.

At a microhazard t of owner j, every other player's forced-Quit payoff
is exactly s_i+t[r_i(ij)−s_i]. Hence its Quit excess is bounded by
C_join t. Adding the SAME e_n to all phase values is a Bellman
supersolution: any added continuation error is multiplied by opponent
survival at most one. This controls one complete deviation, not a sum
of local errors over infinitely many dates.

Removing any one player still leaves positive aggregate opponent hazards
each period. The prescribed opponent-only survival probability ρ_i is
strictly below one and is unaffected by the deviator's stopping law.
Pre-sampling those coins gives an absorption-time domination with mean
at most m_n/(1−ρ_i), up to the harmless date convention already covered
by the stated constants. This justifies both the infinite Snell limit
and the finite-horizon error bound uniformly over all behavioral
deviations. For a fixed n the bound works for EVERY sufficiently large
horizon. Changing n keeps the same prescribed target t. No correlation
device, observed private random variable, or bounded-memory deviation
restriction is used.

### Exact adversarial boundary test

I verified the displayed full-core fixture, including its t,d,V_B,V_C
vectors, A endpoint pairs, and the genuine unrefined gains 2/15 at C
and 1/66 at D. As an additional test, take

    a=b=c=2, h_1=h_2=h_3=1, η=3, θ=λ=1/3,
    u=1, v=−2, R=819/190.

Here η_eff=2, and the quadratic coefficient α vanishes identically.
The exact rates are

    K=7/74, y=1/4, z=17/74, w=10/37,
    x=21/317, ρ=7/324.

The four value vectors are

    t=(1,63/317,127/317,7/317),
    V_B=(1,21/74,0,17/37),
    V_C=(36/19,2/3,0,0),
    d=(1,14/81,10/27,0).

This simultaneously tests α=0, the weak pivot floor u=1, and the
saturated outsider bound λ=h_3θ. Set every unspecified reward
coordinate to 37, except the required player-2 caps and the two zero
player-3 caps. Exact arithmetic still gives zero residual in every
policy and Continue identity. At A the Quit excesses are
(0,0,−127/317,−7/1268). Unrefined solo rows have large positive Quit
gains, and D has player-3 excess 7/972; these are precisely the gains
the proved microhazard bound controls. Thus the proof does not rely on
an accidentally harmless completion.

### Independent coverage and proper-child checks

I independently enumerated the fixture's positive-premium traps:
03,013,23,023,0123. Their sole common member is 3, but
r_3(03)=1/2>−1=r_3(0), so neither weak nor strict common-leaver
coverage applies. Only one pivot passive singleton is at least one;
the latest switched-pair family requires two. Player 0 is the only
positive-singleton pivot, so a relabeling cannot repair this mismatch.
For pair 03 the older positive-pair producer also fails its pivot
comparison, and the original pair-01 caps fail at 03.

The full singleton matrix is R₀ of degree one: the actual child
complementarity equations force z=(1+h)1 at offset (1,−1,−1,−1),
and the only root has pivot h=0, inactive residual 163/92, and active
determinant 7. I recomputed every displayed inverse entry and the
passive weights (186/161,−297/644,25/322). Principal 02, not an
opposite-sign pair, is the stated R₀/non-Q witness. Exact enumeration
of all fifteen partitions leaves only the discrete partition and
0|123 at first order. The full response residuals
t+(31/11)t², t, t+t²/2 exclude the latter. I also verified a strict
toggle improvement at every pure coalition.

The thirteen exact proper-child witnesses are valid. Independently of
the appended coverage calculation, I found the same corrected child023
rates (3/5,1,92/347), with endpoint pairs
(1,1), (−245/347,92/1735), (1/5,1/5), and omitted-1 payoff
−1367/1735 versus immediate Quit zero. The old q_0=2/3 witness is
not exact after the participant-3 pair23 premium is raised.

For child123, I independently found the same required repair: refine
each sole-owner half-hazard into microhazards α_n=1−2^(−1/n). The
macro values and lifted pivot payoff R/7=347/644 do not change;
all child debts are at most α_n/2 and joint Never is zero. Pivot 0
can still quit at the first player-1 microstage for exactly one, giving
the fixed gain 297/644. In the directly inspected
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`),
the certificate's finite nonnegative weights are fixed while the child
profile is universally quantified. Letting n tend to infinity therefore
contradicts its debt bound. No exact child equilibrium or unreviewed
closure premise is being substituted for this limiting argument.

These checks establish the stated bounded source separation. They do
not say that every other strategy architecture fails. The verdict is
ordinary mathematical PASS, with no Lean build claim.

## Independent review: collapse at a lower-boundary minimum

**Verdict: PASS for the analytic mechanism and its stated raw sufficient
condition; new equilibrium coverage remains unestablished.** I checked
the final section “Global minimum test: vanishing roots cannot escape
a lower-face minimum” independently, without another review. This is
not an application of the protected-singleton return argument: the
new proof deliberately allows the perturbed successors outside L.

The data are a finite nonempty player set, participant rewards at least
their own singleton levels s, a reward bound M, and B>M. Write
U=∏[s_i,B] and L={x∈U: some x_i=s_i}. The hypothesis checked is:
every absorbing exact Nash root at every source in U has its literal
one-stage successor in L. The claimed conclusion is the absence of a
C¹ potential with unit absorption decrease on every exact Nash root
throughout the larger signed box [−B,B]^I.

### The minimum geometry and the vanishing-absorption step

Let x minimize H on compact L and J={i:x_i=s_i}. If J consists of
one player j, all other interior partial derivatives vanish and all
upper-face partial derivatives are nonpositive. Consequently
∇H(x)·(x−r({j}))≤0: its j term is zero, interior terms vanish,
and every upper-face displacement is positive since B>M. This
contradicts the singleton-face inequality ≥1. Thus |J|≥2.

For every binding coordinate one can increase that coordinate while
retaining another binding coordinate, so its derivative is nonnegative.
For every nonbinding coordinate, the usual two-sided or upper-face
variation retains a binding coordinate. Hence, coordinate by coordinate,

    ∇H(x)·(z−x) ≥ 0  for every z∈U.

This uses neither convexity of H nor a minimum of H on U.

An absorbing exact root at x would, by the restricted return premise,
give a successor in L with smaller H. Therefore every exact root at
x has zero absorption. Fix a binding k and any sequence ε_n↓0
small enough that v_n=x−ε_n e_k remains in [−B,B]^I. Finite Nash
existence gives roots q_n. They absorb: all Continue would give k the
strict Quit gain ε_n. The product cube of hazards is compact and
both endpoint inequalities are polynomial in (v,q). If a subsequence
had absorption bounded below by a positive number, a convergent
subsequence would give an absorbing exact root at x. Thus a_n→0
for every choice of the roots. No continuous selection and no positive
lower bound on absorption are being assumed.

### The scale of the Taylor remainder is correct

At any exact root, its successor coordinate is at least the forced-Quit
endpoint, which is at least s_i by nonnegative participant premiums.
The successor is also in the reward/source box. Thus w_n∈U even
though v_n∉U and even if w_n∉L. The exact one-stage estimate gives

    ‖w_n−v_n‖∞ ≤ (M+B)a_n,
    ε_n ≤ w_{n,k}−v_{n,k} ≤ (M+B)a_n,
    ‖w_n−x‖∞ ≤ 2(M+B)a_n.

These estimates have the needed direction. They bound both Taylor
remainders by o(a_n), not merely o(ε_n) with an uncontrolled ratio.
If g=∇H(x), then

    H(v_n)−H(x) = −ε_n g_k + o(a_n) ≤ o(a_n),
    H(w_n)−H(x) = g·(w_n−x) + o(a_n) ≥ o(a_n).

Unit absorption decrease would therefore imply
1≤[H(v_n)−H(w_n)]/a_n→at most zero, a contradiction.
The proof even uses only continuity on L and differentiability at its
minimum, with the singleton-face input there; the stated C¹ version
is safely stronger. This is a mathematical observation, not a request
to create another regularity interface.

### Raw trap condition and weak closure

The proposed strict condition is sufficient. For a trap-supported root
with support A, choose its designated p_A. Since a singleton cannot
be a positive-premium trap, some other hazard in A is positive. The
Quit-minus-Continue gap of p_A is the product expectation of
r_p(T∪{p})−r_p(T) for nonempty T⊆A\{p}, with the empty term
s_p−v_p≤0. All nonempty terms are strictly negative, and their
total probability is positive. Thus an active p_A is impossible.
This retains simultaneous hazards of every other support member.
If A is not a trap, one active member has all its participant rewards
in A at most its singleton; nonnegative premiums make them equal.
Its Quit endpoint and successor equal that singleton, while every
other successor is at least its singleton. This proves return to L.

For weak comparisons, increasing every passive reward coordinate by
δ>0 leaves every participant reward, singleton level, and premium trap
unchanged. It makes each designated comparison strict. Applying the
strict result to these tables and then reward closure proves the weak
Fin4 UE claim when s≥0. It does not prove weak analytic exclusion.

### Exact adversarial separation of the return premises

Here is a small exact test showing why the new argument cannot silently
reuse a one-protected-floor return premise. Take I={0,1,2,3}, pair
partners 0↔1 and 2↔3, and all own singletons zero. For i∈S set
r_i(S)=1 if its partner belongs to S and zero otherwise. For i∉S
set r_i(S)=2 when i∈{0,2}, and zero when i∈{1,3}. This defines
all fifteen nonempty rows and has M=2; take B=3.

Its only premium traps are 01, 23, and 0123. Player 0 is a strict
leaver of 01 and 0123, and player 2 is a strict leaver of 23:
their participating reward is at most one and passive reward is two.
The all-floors return premise therefore holds. Nevertheless, at

    v=(−1,1,2,2), q=(1/2,1/2,0,0),

the four (Quit,Continue) endpoint pairs are
(1/2,1/2), (1/2,1/2), (0,2), (0,1/2). This is a full exact
root, with successor (1/2,1/2,2,1/2) strictly above all singletons.
The exchanged test

    v=(2,2,−1,1), q=(0,0,1/2,1/2)

has endpoint pairs (0,2), (0,1/2), (1/2,1/2), (1/2,1/2)
and successor (2,1/2,1/2,1/2). Between these two tests, every
possible designated protected coordinate is above its floor at an
exact root with successor outside L. Thus no one-protected-floor
return statement applies to this table. I independently evaluated
all endpoint fractions and enumerated all its premium traps.

This is only a logical separation test. All its singletons are zero,
so all Never already gives a uniform payoff. It is explicitly not a
new existence-coverage fixture.

### Source scope checked

I re-read `IsQuittingFullExactRootPotential` and
`isQuittingFullExactRootPotential_of_robustPotential` in
`UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`,
`IsQuittingFullExactRootPotential.singletonFace_drift` in
`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`,
and `abs_quittingRootSuccessorPayoff_sub_tail_le_reward_add_source_mul_absorptionMass`
in `UniformEquilibrium/Quitting/Root/BoundedSuccessorDisplacement.lean`.
These are the literal full relation, face condition, and displacement
estimate used above. The inspected
`not_isQuittingFullExactRootPotential_of_singletonLowerBoundaryReturn`
in `UniformEquilibrium/Quitting/Projective/SingletonLowerBoundaryReturnSmoothDrift.lean`
requires one protected floor at every queried source. The inspected
`weakPeeling_iff_every_boxedExactRoot_singletonLowerBoundary` in
`UniformEquilibrium/Quitting/Classification/NonnegativePremiumBoxBoundary.lean`
requires return on all boxed sources. Neither is the new premise.

The currently present
`exists_uniformEquilibriumPayoff_of_continuous_boundaryDifferentiable_potential_exclusion`
in `UniformEquilibrium/Quitting/Classification/Existence/BoundaryDifferentiablePotentialUniformPayoff.lean`
spells out the expected Fin4 consumer: nonnegative singletons imply
normality, a positive singleton plus no UE supplies the full rational
polynomial obstruction, and all-zero singletons have the Never exit.
I inspected source text only; some of this implementation is concurrent
and untracked, and I make no compilation or integration claim here.

No mathematical objection remains to the minimum-collapse mechanism
or its stated sufficient raw condition. Whether that raw class escapes
the existing equilibrium producers is still a separate open audit.

## Final artifact check: repeated solo outsider buffer

**PASS.** This is the bounded assembly/delta check of
`exports/REPEATED_SOLO_EXIT_WITH_POSITIVE_OUTSIDER_BUFFER.md`, 495 lines,
SHA256 `53dbfbccdf06da788bf4f694ff73d48bb63ce1d3843a00a240c2397870f02937`.
It does not replace or reopen the independent full bridge review above.

I read the complete assembled artifact and compared its hypotheses,
selector, four literal values, all-row supersolution, and fixed-target
consumer with the reviewed theorem. There is no mathematical change.
In particular, θ remains strictly positive and below η/h₁; the
zero-effective-premium boundary is explicitly excluded. All three solo
phases are refined, including the repeated pivot exit. Unspecified
reward coordinates remain arbitrary, and deviations remain complete
behavioral strategies.

The newly expanded all-R exit is complete. For a positive right side,
the child complementarity inequalities force all three coordinates
positive and hence z=tν. In the full homogeneous problem a positive
pivot forces child hν, so R=R_low is exactly the nonzero homogeneous
case. At R<R_low the selected offset has exactly the two stated
nondegenerate roots, with active determinant signs + and −; their
sum is zero. At R≥R_top the displayed passive inverse weights are
nonnegative, including the equality endpoint. The packet names the
existing strategic consumers instead of presuming a new realization
theorem. The selector endpoint ratios follow directly from its
quadratic coefficients, including α=0, and its denominator remains
positive throughout the cap interval.

I also checked the assembly's complete fifteen-row table against the
reviewed completion, all fifteen listed pure-coalition improvement
witnesses, and each of the thirteen newly displayed response-partition
row-sum witnesses. The residuals for the sole remaining nondiscrete
partition are unchanged. The exact child023 and diffuse child123
arguments retain their corrected hazards, the fixed outside payoff
gap, and zero joint-Never mass.

The final intrinsic debt statement has the correct quantifiers: for
each proper child there exists an omitted player for whom no fixed
nonnegative weighted-child-debt-plus-Never bound holds universally over
child profiles. It does not assert failure for every omitted player,
nor exclude a selected-child architecture. Thus the final replacement
of the undefined “five kinds” phrase introduces no stronger claim.
The concise Lean handoff names the actual new producer chain and keeps
the already available outer singleton exits separate. No dependency on
another conference note or frozen mathematical packet was introduced.
No unresolved assembly objection remains; no Lean check is claimed.

## Independent coverage check: support-specific leavers on a proper three-core

**PASS for the stated bounded source separation.** I independently
checked the final subsection “An exact support-specific-leaver coverage
candidate” in `notes/CODEX_BROUWER__QUITTING_TABLE_COVERAGE.md`.
This supplements my preceding independent proof review of the global
minimum-collapse mechanism. It does not claim that every existing
conditional strategy architecture fails on this particular table.

The full fifteen-row table has nonnegative participant premiums and
own singleton vector (1,0,0,0). Its ONLY premium traps are 01, 12,
and 012. Their strict leaver sets are respectively {0}, {2}, {0}.
In particular the triple checks all three nonempty opponent coalitions:
3/2<2, 1<2, and 1<2. This is the literal raw hypothesis, not a
test using only pairwise comparisons. Its greatest core is exactly
012. The sole common member of all traps is 1, who strictly prefers
joining 0 to leaving: 1>−1. The common-leaver and core≤2 classes
therefore do not include this table. The positive own singleton also
excludes the zero-solo Never exit.

This proper-core distinction matters. The whole full-core branch of
the support-specific criterion is already consumed by a globally safe
quiet player and the existing low-player vanishing-Never producer.
The exact source composition is recorded in Section 16 of
`notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`. That composition
does not apply here: for the triple's leaver 0, the omitted flat
player 3's singleton gives r₀(3)=0<s₀=1, and joint03 gives 1>0.
No global safe-quiet assumption is inherited from being a leaver
inside core012.

I recomputed the singleton matrix and all four triple inverses exactly.
For child123, A·1=1, det A=7, and the passive inverse row is
(−1/7,5/7,3/7). Each other triple has a negative inverse entry,
with the stated examples −2, −2/3, −2/3. The full inverse's
row0,column2 entry is −5/7. Every pair lacks two positive off-diagonal
entries, and principal03 is the stated R₀/non-Q pair. The full
homogeneous problem forces child h1 for any pivot h>0, leaving the
strictly positive pivot residual h. At the stated offset its only
root is (0,1,1,1), with residual 2 and positive active determinant 7.
Thus the full matrix is R₀ of degree one: the degree exit does not
apply, even though a nonzero-degree matrix is itself standard Q.
No erroneous claim that the full matrix is non-Q is being inferred.

Independent enumeration of all fifteen partitions leaves exactly the
discrete partition and 0|123 at first order. The three literal
child response values at (t,0,0,0) are t+t², t, t, so the
nontrivial quotient fails. I also checked every listed pure-coalition
improving player. In table order the strict gains are

    2, 1, 3/2, 1, 1/2, 1, 1, 3/2,
    1, 1, 1, 2, 1, 1, 2.

Each join or withdrawal leaves a nonempty quitting coalition, so this
is an actual first-date comparison and not an undefined all-Continue
payoff substitution.

The thirteen proper-child sure-coalition profiles are all full terminal
Nash. Their participant withdrawal and nonparticipant join gains are
nonpositive. A sole owner who instead keeps the game alive faces all
opponents at Never and cannot exceed its own nonnegative singleton.
The displayed omitted player's immediate gains, in the child-table
order, are

    2, 1, 3/2, 1, 1, 3/2, 1,
    1, 1, 3/2, 1, 1, 1.

All thirteen prescribed profiles absorb surely. Thus they falsify
any universal fixed nonnegative weighted-child-debt-plus-Never bound
for the corresponding omitted player, including the source family
that consumes vanishing Never rather than a positive child singleton.

For child123 I separately checked the refined order3,1,2 half-hazard
cycle. Its macro values are indeed (1,0,0), (0,1,0), (0,0,1),
and all refined values retain the zero own-singleton floors and exact
Continue comparisons. Only the pair12 participant premiums are
positive, both 1/2, so the full behavioral regret is at most α_n/2
with α_n=1−2^(−1/n). Opponent-only geometric absorption justifies
the single-error supersolution for every stopping law. The quiet
pivot payoff is exactly 6/7; quitting at the first microstage of
player3 pays exactly one independently of its hazard. The fixed gain
1/7 with zero joint-Never mass contradicts any such fixed finite
debt bound as n increases. This is not an assertion that the coarse
cycle is exact or that a zero-singleton child cannot be made to absorb.

Finally, the latest two-high-singleton cyclic families must use pivot0,
solo players1,2, and joint03. The actual outsider coordinate
r₁(03)=2 contradicts their prescribed −h₁=−1. The earlier
positive-joint families fail the displayed pivot-pair/partner or low
passive-singleton tests for each possible partner; the solo-0 bridge
also lacks its prescribed complete joint vector. A signed four-cycle
singleton adapter requiring a positive predecessor in every singleton
column cannot use the all-harming pivot column. These are exact raw
hypothesis checks, not failures of a numerical rate search.

The inspected named source families therefore do not automatically
consume this proper-core fixture, while the independently reviewed
support-specific-leaver theorem does. The requested mathematical
coverage witness survives. No unrestricted nonexistence claim and no
new Lean implementation is asserted.

## Independent review: weighted floors without a protected player

Reviewed the complete final section **Weighted-floor return without a
protected player**, including its weighted-premium source comparison, in
`notes/CODEX_BROUWER__QUITTING_TABLE_COVERAGE.md`, full-note SHA256
`2c97a149d66c039cfa58cb9779fd4dd532381a9f4a39be80eabcfcf96e41f6bb`.
Verdict: **PASS**, ordinary mathematics, not Lean certification. I did not
read KREIN's review. No mathematical repair is requested.

The checked conclusion is a concrete finite raw-data criterion: for every
positive-premium trap, one strictly positive weighting of its players
satisfies the full-table aggregate forced-Quit floor inequalities (W3)
and the strict aggregate leave inequalities (W4). For finite player sets
this excludes a C¹ full exact-root potential. For Fin4 and nonnegative own
singletons it produces uniform-equilibrium payoff existence through the
named semantic obstruction theorem. Weak leave inequalities give only the
strategic conclusion by reward closure. It is not a universal Fin4 proof,
a weak analytic exclusion, or a supplied strategic-witness consumer.

### Convex minimum and the absorption-relative limit

I independently checked the convex invariant lemma, including the step
not available merely from minimizing on the singleton lower boundary.
The minimum on D=R∩{some coordinate at or below its singleton} first lies
in L: otherwise any exact root absorbs and returns to D. Since R contains
the entire singleton upper box, the available face variations give the
stated derivative signs. If only one coordinate binds, the signed
singleton-face inequality contradicts those signs on all other coordinates.
With at least two binding coordinates, each binding derivative is
nonnegative, since another binding coordinate keeps its positive
variation in L.

For z∈R, if any binding coordinate does not increase, the segment from x
to z lies in D, INCLUDING equality in that coordinate. Its right derivative
is nonnegative. Otherwise every binding coordinate increases; the derivative
signs on the remaining coordinates give the same conclusion. Thus (W1)
really holds on all R, without a coordinate-floor hypothesis or a
constraint qualification. Convexity is used exactly here.

Every root at x has zero absorption. Compactness of the full hazard cube
and closure of the literal polynomial Nash inequalities therefore force
absorption to tend to zero for ANY exact roots selected at x−εe_k.
No continuity or uniqueness of a root selector is assumed. The source may
be outside R. Universal successor membership, rather than source membership,
is what supplies (W1) for its successor.

The signed bound follows directly from

    Q_k≥s_k−2M a,    w_k≥Q_k,
    |w_k−v_k|≤(M+B)a,    v_k=s_k−ε.

Consequently ε≤(3M+B)a and ‖w−x‖∞≤(4M+2B)a. Differentiability at x
turns both remainders into o(a). The source's linear contribution is
−εg_k≤0 and the successor's is nonnegative by (W1). This contradicts
unit absorption drift. There is no assertion that the perturbed
successor returns to D, nor that any individual successor coordinate
remains above its singleton.

### The actual full-table weighted identities and sure hazards

For (W6), averaging r_i(S∪{i}) over player i's own Bernoulli action
does not change the forced-Quit endpoint. Averaging over the OTHER
players gives Q_i. Therefore the sum includes every S⊆I, not only
coalitions contained in the particular trap. This is essential when
other players have positive hazards. Nash gives w_i≥Q_i, and the
nonnegative weights then yield successor membership in every halfspace
defining R, simultaneously, at every boxed source.

For (W7), multiplying the i-th gap by 1−q_i turns each opponent-coalition
mass into the full coalition mass for a coalition omitting i. The empty
coalition contributes c(q)λ·(s−v); collecting the nonempty coalitions
gives exactly μ(T)L_A(T). There is no division by q_i or 1−q_i, so the
identity remains valid at zero and sure hazards.

If some active j has q_j<1, the particular coalition T=A\{j} has
positive probability: all its active hazards are positive, 1−q_j>0,
and all hazards outside A are zero. It is nonempty because singleton
supports cannot be traps. Hence the strict leave sum is genuinely
negative, including when all other active players quit surely.
If all active hazards equal one, the identity becomes uninformative,
but (W4) at A\{i} says r_i(A)<r_i(A\{i}) for every i∈A.
This directly contradicts Nash by withdrawal with another quitter
still present. The separate sure-root argument is valid and necessary.
Finally, a nontrap support has an active player whose every participant
reward inside that support is at most its singleton. Its Nash successor
equals its forced-Quit endpoint, giving the required low coordinate.

The weak strategic extension preserves all participant rewards, all
singletons, all traps, and every (W3). Increasing every passive entry
by δ decreases L_A(T) by δ∑_{i∈A\T}λ_i>0. Thus it yields arbitrarily
close strict tables and legitimately invokes reward closure; it does
not pass a C¹ potential exclusion through a limit.

### Exact signed fixture and independent boundary tests

I recomputed the entire fifteen-row table using rational arithmetic.
Its only trap is 012 and its protected-player set is empty. With
λ=(1,1,1,0), the nonempty (W3) values are exactly the stated 1/2,
3/5, 3/10, 7, and 6 in their displayed cases. The six (W4) values
are −1/2 on singletons and −9/10 on pairs. All nontrivial inequalities,
the relevant participant-premium signs, and the positive own singletons
are strict. They really define a full sixty-coordinate open neighborhood
with the same single trap and the same weights. No positive radius or
generic completeness assertion is needed.

Two additional exact full-root tests on this SAME table stress the
premise distinctions. Take B=4, so

    R={v∈[−4,4]⁴ : v₀+v₁+v₂≥3/10}.

At v=(−29/10,1,13/5,0)∈R, the root q=(1/2,0,1/2,0) has

    Q=(−2/5,1/4,17/20,1/4),
    C=w=(−2/5,33/40,17/20,1).

It is exact Nash, and w∈D while w₀<s₀. The weighted floor has not
silently become a coordinate floor.

At v=(1/30,1/30,1/30,1)∉R, the root q=(1/10,1/10,1/10,0) has

    Q=(73/500,73/500,73/500,729/1000),
    C=w=(73/500,73/500,73/500,1109/1000).

It is exact Nash with support equal to the trap and successor strictly
above ALL four singleton floors. Thus outside-source roots really can
leave D. This does not contradict the proof: the source is outside R,
and compactness at the actual minimum, rather than unconditional return,
is what controls the Taylor argument. I also symbolically expanded
(W7) for arbitrary three core hazards and arbitrary source coordinates
on this table; its polynomial difference is identically zero.

### Scope and exact existing-source exclusions

The matrix (W8) is exactly the stated permutation of (G3), without a
change of playerwise centering. I independently recomputed all four
triple inverses, the full inverse, and all fifteen partitions. The
only nonnegative-inverse triple is 012, whose passive inverse row is
(−1/7,5/7,3/7). For pivot hazard h>0 the homogeneous core LCP has
unique solution h·1, leaving pivot residual h>0; at h=0 only zero
remains. At offset (−1,−1,−1,1), the unique complementarity root is
(1,1,1,0), with inactive residual 2 and active determinant 7. Thus
the full matrix is R₀ of degree one, not a full non-Q example.
Principal23 is the R₀/non-Q pair with both off-diagonal entries −1.
The only first-order partitions are the discrete one and 3|012;
the literal responses t+3t²,t+2t²,t+2t² break the latter.

All fifteen listed pure improvements and their displayed gains are
correct. I checked all thirteen exact child profiles including their
full deviations: the only joining ties are player 3 against sure
owner 2, and a sole owner cannot beat its positive singleton after
preventing the first-date exit. The omitted gains are 5/2, except
the stated child3 gain 4. These central-table witnesses are exact;
no persistence of their ties throughout the open raw neighborhood is
being claimed.

For child012, the refined half-hazard order2,0,1 has the stated
centered macro values. Opponent absorption makes subtracting the
singleton vector harmless for evaluating every deviation. Floors,
exact Continue, and the common error (3/2)α_n give the full behavioral
debt bound, not an accumulated per-stage error. The quiet player's
value is 6/7; its first-microstage Quit payoff is 1−α_n. The gain
1/7−α_n and zero joint-Never mass defeat every fixed finite
nonnegative weighted-child-debt-plus-Never bound as n increases.
Together the examples cover each proper child with at least one
profitable omitted player, not every omitted player.

I inspected the actual definitions
`IsSupportwiseQuittingPremiumWeightCertificate` and
`HasSupportwiseQuittingPremiumBalanceAt` in
`UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumBalanceAt.lean`,
the product identity and balanced-table predicate in
`UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremium.lean`,
and `exists_uniformEquilibriumPayoff_of_supportwiseBalance` in
`UniformEquilibrium/Quitting/Classification/Existence/SupportwisePremiumUniformPayoff.lean`.
At support and terminal coalition 012, every normalized nonnegative
weight yields positive premium 1/10, so the old certificate fails.
`HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`
fails at q=(1,1,1,0), since all active Quit endpoints are 1/5>1/10.
This product root is not Nash; withdrawing pays 11/10. The new
Nash-dependent exclusion therefore does not contradict the old test.

The signed fixture has no protected player, while the two-player
example in the note satisfies the protected-set criterion and fails
(W4). The two raw criteria are genuinely incomparable; only their
analytic arguments share the convex-invariant generalization. The
fixture also lacks any pair with two nonnegative participant premiums,
which excludes the specified strict-sign-preserving two-joint
neighborhood, not every possible chronological construction.

Finally, I re-inspected the precise signed singleton-face drift,
exact-root existence, displacement, normality, polynomial-obstruction,
exact restriction, and reward-closure declarations named in the note:
`Projective/FullExactRootPotentialFaceDrift.lean`,
`Root/NashExistence.lean`, `Root/BoundedSuccessorDisplacement.lean`,
`Classification/AbnormalPlayers.lean`,
`Projective/PolynomialForwardCertificateCharacterization.lean`,
`Projective/ExactRootPotentialRestriction.lean`, and
`Terminal/TerminalExploitabilityRewardRobustness.lean`, all under
`UniformEquilibrium/Quitting/`. Their hypotheses compose exactly as
claimed: nonnegative own singletons imply normality without premium
signs, and the SAME rational full-relation polynomial restricts to
the excluded exact potential. All-zero singletons use all Never.
This is a concrete raw-class producer with a valid strategic consumer,
not merely a new analytic interface. Its bounded source-separation
claims survive; no exhaustive exclusion of other producers is asserted.

## Final artifact check: weighted floors and aggregate leave

Checked all 604 lines of
`../exports/WEIGHTED_FLOOR_RETURN_UNIFORM_EQUILIBRIUM.md`,
SHA256 `98ffaf81955437f97d3d3d8b1315c0e289be410110fed77ba3f1a72dcf2c1654`.
Verdict: **PASS**. This is the bounded standalone assembly/delta check
against the complete independent review above, not a new full audit.

The full raw statement, the two weighted identities with their different
coalition quantifiers, the all-sure exception, the convex-domain proof,
and the strict analytic versus weak strategic boundary are unchanged.
The newly expanded collision-adjusted singleton probe is complete: its
correction is confined to binding coordinates below the upper box, all
other endpoint gaps are eventually nonnegative, and the correction
cancels in the derivative. The reward-closure paragraph retains one
limit target before accuracy and bounds every behavioral deviation.

The added first boundary regression also checks exactly. Replacing
the three designated outsider-joining participant entries by −1 leaves
the core-only tests intact but makes W_A(3)=−33/10. The displayed pure
root is Nash and its successor has centered core sum −3. The other two
regressions reproduce the independently checked exact roots above.
The expanded matrix argument, complete partition witnesses, child
table, and fixed-weight debt exclusion retain their reviewed scope.
In particular the fixture's central-table child ties are not claimed
to persist throughout the open raw neighborhood.

The packet is self-contained and cites only the named tracked Lean
sources, with no conference-note or export dependency. The implementation
boundary identifies the new actual-data producer and analytic work,
without suggesting that source declarations already certify it. The
final deletion of “stronger” before “product-low predicate” removes a
potential implication-direction ambiguity and changes no mathematics.
No unresolved artifact objection remains at the stated final hash.

## Independent review: boxed Nash charge on a triple

Checked the complete section **The complement of weighted floors: a boxed
Nash charge on a triple** in
`notes/CODEX_BROUWER__QUITTING_TABLE_COVERAGE.md`, as read at full-note
SHA256 `26497fa7cc3c51e09bbce10eafc3ad03909ac656c7e8691275282b56682cd962`.
Verdict: **PASS**, ordinary mathematics, not Lean certification. No other
review was read. The proof supplies an actual finite raw triple-core
class, not merely an equivalent potential interface or an improved
constant inside the weighted-floor criterion.

The stated Fin4 assumptions are nonnegative own singletons, no traps
other than triples, and one set of positive constants d,τ,g,l for each
trap satisfying (N2)–(N6). Two distinct triple traps cannot coexist,
because their union would be a four-player trap. If there is no trap,
the low active endpoint follows directly. In the nonempty case every
root support other than the triple is nontrap and has an active
participant with every relevant own reward at most its singleton.
This correctly retains larger simultaneous coalitions and requires
no participant-premium lower bound.

### Sure hazards and the exact odds calculation

On trap support A, the unweighted full identity is

    ∑_{i∈A}(1−q_i)(Q_i−C_i)
      =c(q)∑_{i∈A}(s_i−v_i)+∑_{∅≠T⊊A}μ(T)L_A(T).

For a triple, (N4) controls every singleton coefficient and (N5)
every pair coefficient. If some but not all active hazards are sure,
c(q)=0 and A minus any nonsure active player has positive probability.
Its negative coefficient contradicts supported Nash optimality. If all
are sure, (N5) directly gives strict withdrawal for each participant.
Thus an exact root with trap support must be interior on all three
coordinates before odds are introduced. No division at a sure hazard
has been hidden.

At such a root divide each Quit premium by its own positive opponent
Continue probability. The empty-opponent term is zero. Summing the
single-opponent terms gives the first sum in (N7); each double-opponent
term is the actual triple premium times the product of the other two
odds. All three divided premiums are positive under the purported bad
root assumption. Hence dU<τV. The elementary identity
U²−3V=½∑_{i<j}(z_i−z_j)²≥0 gives U>3d/τ.

Interior support indifference makes the left-hand gap sum zero.
Dividing the coalition identity by c(q)>0 yields exactly
∑(s_i−v_i)=∑[−L_A(T)]∏_{j∈T}z_j. Consequently

    ∑(s_i−v_i)≥gU+lV
      >(g+l d/τ)U>(3d/τ)(g+l d/τ).

The strict steps have the correct direction since all four constants
are positive. A boxed source gives the opposite bound ∑s_i+3B.
The strict margin in (N6) permits M<B<M+2 with that right-hand side
still smaller. This proves low-successor return for EVERY absorbing
exact root at EVERY source in this particular box; it is not a claim
about arbitrary annotations of unbounded magnitude.

Taking R to be the whole box satisfies the first convex-domain premise
automatically. The proved return satisfies its second premise. The
same robust polynomial at M+2 restricts to B by
`IsQuittingFullExactRootPotential.mono_box` in
`UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`;
no new potential, changed game, or strategic continuation realization
is used. Normality and the Fin4 semantic consumer retain precisely the
nonnegative-singleton assumptions stated in the note.

### The complement fixture and the role of the box

The three changes (N1) reduce the positive core-pair premiums from
3/2 to 1/2 and preserve the sole trap 012. At the three sure-core-
singleton product laws, summing ANY nonnegative weighted Quit-floor
conditions gives

    −(λ₀+λ₁+λ₂)/2−3λ₃≥0.

This really forces λ=0, even if the proposed weights are allowed on
players outside the trap. Thus the fixture is outside every nonzero
nonnegative linear forced-Quit floor of the stated form, not just
outside one chosen weighting. The test laws need not be Nash.

For the displayed exact constants the charge is 90 and
∑_A s_i+3M=48/5. The claimed open raw region is also valid, with a
small clarification about slack: the displayed choices attain equality
in (N2)–(N5), but one may instead take

    d=2/5, τ=1/5, g=7/5, l=4/5.

These give strict slack in all four sets of inequalities and charge
18>48/5. This supplies a direct open-neighborhood proof without
asserting that the original equality-bound constants themselves have
strict slack. It does not change the theorem or require a repair to
its numerical hypothesis.

As an independent stress test on the SAME modified table, take

    q=(9/10,9/10,9/10,0),
    v=(−863/10,−863/10,−863/10,1).

The exact endpoints are

    Q=(17/125,17/125,17/125,1/1000),
    C=w=(17/125,17/125,17/125,1981/1000).

This is a full exact Nash root with successor strictly above ALL
singletons. Its source is far outside the permitted box. Here the
three odds are 9, so U=27, V=243, and the exact source charge is
1296/5=gU+lV for the original constants. The example confirms that
the proof is genuinely box-dependent; it cannot be promoted to
unconditional all-annotation return or product-low behavior.

The bounded source exclusions also survive the three reward changes.
All-singleton centered data, matrix screens, and the response-quotient
falsifier are unchanged. All thirteen displayed child singleton
profiles remain exact, with the stated outside gain 3/2 except
child3's gain 4. The diffuse core child's sole positive pair premium
bound becomes α_n/2, while its quiet outsider value and first-microstage
gain remain 6/7 and 1/7−α_n. The listed pure improvements persist.
Product-low and supportwise balance still fail at the positive-premium
triple, and the protected-player set remains empty. These are concrete
complements to the inspected sources, not an exhaustive exclusion of
all stationary or chronological equilibrium producers.

No unresolved objection remains to (N7)–(N8), the boxed return, the
Fin4 consumer, or this exact raw coverage witness. The next global
question about a four-player core is not answered by this review.
