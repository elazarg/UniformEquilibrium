# Review of the asymmetric cyclic pivot family

Reviewer: CODEX_BROUWER.

Scope: “A joint phase closes an asymmetric cyclic pivot family” and, in the
separate addendum below, “Proposed enlargement: independent positive pivot
harm levels,” in
[`CODEX_KREIN__INDEPENDENT_STOPPING_LAW_SELECTION.md`](../notes/CODEX_KREIN__INDEPENDENT_STOPPING_LAW_SELECTION.md),
as read on 2026-10-05. Earlier exact-selector and zero-singleton sections
are not being re-reviewed here.

Verdict: **PASS as ordinary mathematics**, for both versions' raw-table
existence theorems and exclusions of every proper-child five-kind F/J family.
No unresolved mathematical objection. No Lean implementation or build was
performed. **Scope correction:** the entire base and positive-harm reward
family already has an implemented existence producer through product-low
premiums. The selected exact periodic profile and the F/J-certificate
separation remain valid, but this is not new uniform-equilibrium existence
coverage. The correction at the end supersedes the preliminary overlap
assessment below.

## Exact statement checked

Take a,b,c>0, D=abc-1>0, and

    R_low=(ab+ac+a+bc+b+c+3)/(bc+b+1),
    R_high=ac+a+1,
    R_low<R<R_high.

For every nonempty S, pivot 0 receives 1 if it belongs to S, otherwise
R times the indicator that 3 belongs to S. A nonpivot j receives zero
if it belongs to S, minus one if it is outside S but 0 belongs to S,
and otherwise a_j times the indicator of its cyclic predecessor minus
the indicator of its cyclic successor, where (a_1,a_2,a_3)=(a,b,c).
All-Never pays zero.

The claim produces four interior hazards from these data, then repeats
independent product phases {0,1}, {2}, {3}. It is exact terminal Nash
against every behavioral deviation. The initial payoff, selected before
accuracy, is (1,0,w/(1-w),0). Independent finite censoring gives full-regret
approximants and the same fixed uniform-equilibrium payoff. Every nonempty
proper child is separately shown to lack any all-outsider family of the
five original F/J certificate kinds, with arbitrary nonnegative weights.

## Scalar selection: checked without assuming a root

For 0<y<Y=D/[b(ac+a+1)], use

    z=(k+y)/[c(1-y)],       w=(by-k)/(1+by).

After clearing the positive denominator, the root equation is exactly

    f_y(k)=c(1-y)(1+by)k
           -a(by-k)[c(1-y)-k-y]+(k+y)(1+by).

Its k^2 coefficient is -a and its constant coefficient is
y[b(ac+a+1)y-D]<0. At k=by, w=0, so the un-cleared residual is k+z>0.
At k=c-(c+1)y, z=1, so it is k+1>0. Both evaluation points are positive
because Y<c/(c+1); after clearing denominators this last strict inequality
reduces to bc+c+1>0. Strict concavity therefore gives exactly one root
between zero and the smaller evaluation point. In particular 0<z,w<1.

The linear coefficient is positive on the closed interval [0,Y]. For
interior y this follows from the positive value at an evaluation point
and the nonpositive constant coefficient; at y=Y the same argument
applies, and at y=0 its value is ac+c+1>0. The discriminant is positive
throughout, so the smaller-root formula is continuous and has k=0 at both
endpoints. This checks a possible degeneracy in the selection argument.

Implicit differentiation at (y,k)=(0,0), or direct coefficient comparison,
gives

    k/y -> D/(ac+c+1),
    z/y -> (ab+a+1)/(ac+c+1),
    w/y -> (bc+b+1)/(ac+c+1).

These are the stated v-ratios. Consequently the continuous extension of

    R(y)=1+[1/((1-y)(1-z))-1]/w

has R(0)=R_low. At y=Y the three printed endpoint rates are correct, and
direct substitution gives R(Y)=ac+a+1. Also

    R_high-R_low=(c+2)D/(bc+b+1)>0.

Thus ordinary IVT selects an interior y for EVERY requested R in the
raw interval. Monotonicity of R(y) is unnecessary and was not used.

## Actual values, arbitrary deviations, and finite laws

I independently recomputed the Bellman rows. At phase C, singleton 3
pays (R,a,-1,0); at B, singleton 2 pays (0,-1,0,c). At A, pivot participation
overrides passive nonpivot rewards, so the coalition {0,1} really pays
(1,0,-1,-1). These give the displayed values

    V_A=(1,0,w/(1-w),0),
    V_B=((1-z)[1+(R-1)w],k,0,cz),
    V_C=(1+(R-1)w,aw,0,0).

The four nonautomatic A equations reduce respectively to
(1-y)V_B,0=1, V_B,1=k,
(by-k)/(1+k)=w/(1-w), and -k-y+cz(1-y)=0. They follow from the
scalar equation and the literal definitions. No expectation of a public
coalition mixture substitutes for the independent product row.

Every nonpivot Quit endpoint is identically zero, even when it joins a
scheduled coalition. Its active value is zero and every inactive value
is nonnegative. Pivot Quit is identically one, its active value is one,
and its inactive values exceed one because R>R_low>1. Bellman equality
then yields all pure-action comparisons.

For any deviator, each unchanged opponent has one positive independent
hazard in every three-date period. Deleted survival is therefore strictly
less than one per period. The terminal remainder in the Bellman inequality
vanishes under EVERY complete deviating law, including Never, unbounded
clocks, and history-dependent behavioral randomization. The same contraction
identifies the prescribed values with actual payoffs. This is an exact
full-deviation equilibrium, not a restricted periodic equilibrium.

The displayed marginal censor masses are exactly the survival probabilities
after K trials of each player's own hazard. Coupling bounds prescribed
payoff error by 2M*tau_K and full regret error by 4M*tau_K. The original
periodic target is fixed before K or accuracy is chosen. Geometric
opponent absorption alternatively gives the uniform finite-average conclusion
directly. The finite pivot-repair comparison is legitimate because the
displayed censored pivot law is an admissible competitor against those
same three actual opponent marginals.

## All fourteen proper children: separation checked

The needed source implication is
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
It quantifies over the original child profile and all five kinds. An exact
child Nash profile with joint-Never zero and positive outside debt therefore
contradicts every possible certificate of every kind, not merely displayed
weights.

The five cases in the note cover all fourteen children:

* For singleton or two-player nonpivot children, the chosen pure owner has
  own payoff zero; when there is another child, it receives a positive
  cyclic reward and optimally Continues. The missing cyclic player receives
  minus one and can join for zero.
* For the full nonpivot child, k=0 at Y gives the exact solo three-cycle.
  Pivot terminal absorption at player 3 has probability 1/R_high, as follows
  by rearranging the endpoint pivot recurrence. Its payoff is R/R_high<1,
  and immediate Quit gives one.
* For children containing 0 but excluding 3, all child members quitting at
  zero is exact: pivot withdrawal gives zero, nonpivot withdrawal gives
  minus one. A missing nonpivot receives minus one and can join for zero.
* For children containing {0,3} but excluding 2, player 3 alone quitting is
  exact: pivot obtains R>1, and retained player 1 obtains a>0. Missing
  player 2 receives minus one and can join for zero.
* For {0,2,3}, set p=c/(1+c) and t=1/R at date zero, with player 2 sure.
  Player 3's Continue payoff is c(1-p)-p=0; pivot Continue is Rt=1;
  player 2's Continue payoff is -p-(1-p)t<0. The respective Quit values
  are 0,1,0. Missing player 1 receives -1+a/[(1+c)R]<0 and can join for
  zero. The strict sign follows from R_low>a/(1+c), whose cleared
  difference is a sum of positive terms.

Later finite deviations in these one-date examples do not create an omitted
benefit: a retained sure quitter absorbs immediately, except possibly after
the sure player's own deviation, in which case its own singleton and Never
both equal zero. Each child has joint-Never zero. Thus every separation
claim has an actual independent-law falsifier.

The conclusion is correctly limited to the certificate families. It does
not rule out all quiet equilibrium profiles or the closure of all other
known producer classes.

## Source overlap and novelty calibration

The general supplied-object result
`isUniformEquilibriumPayoff_of_isQuittingBlockCertificate` in
`UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean` already
provides the full-behavior periodic consumer. The added work here selects
the hazards from an independently stated four-parameter reward class and
verifies its literal Bellman/incentive rows. It is not a new periodic
compiler.

I inspected the source hypotheses of
`FullCoreDeadlock.jointBlock_isQuittingBlockCertificate` in
`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockJointBlockEquilibrium.lean`
and `IsDeadlockRationalJointBlockCompletion` in
`DeadlockRationalPolyhedralBlock.lean`. They fix a different singleton
matrix/completion or polyhedral class. Their mere use of one joint phase
does not produce this variable interval family.

For the strict-inverse child route in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/StrictInversePassiveRowCycle.lean`,
the present three-child matrix is

    N=[[0,-1,a],[b,0,-1],[-1,c,0]],

and N^-1 is strictly positive. However the pivot's centered row is
u=(-1,-1,R-1), and the middle coordinate of u N^-1 is
(R-R_high)/D<0. Thus the named nonnegative inverse-row consumer does
not apply on this interval. This is an exact row calculation, not merely
the observation that one particular child cycle gives the pivot too little.

As a further limited check, the full centered singleton matrix is

    [[0,-1,-1,R-1],[-1,0,-1,a],[-1,b,0,-1],[-1,-1,c,0]].

Its determinant is (bc+b+1)(R-R_low)>0. No homogeneous complementary
simplex solution exists: singleton supports each have a negative residual;
two positive support coordinates would require zero off-diagonal entries;
each three-support containing 0 has a supported row negative on both
others; the nonpivot three-support has determinant D>0; and the full
support has the nonzero determinant just computed. This does not decide
every standard-Q gate or all implemented reward classes, and I do not
claim such an exhaustive novelty audit.

The bounded source comparison therefore supports a genuinely raw class
producer with a strong, proved quiet-certificate separation. The current
note's qualified overlap language is honest. No broader claim of external
priority, arbitrary-table coverage, or exclusion from all existing
equilibrium mechanisms is warranted by this review.

## Additional review: arbitrary positive pivot harm levels

The separately marked enlargement was subsequently checked at the root's
request. It is also **PASS**, with no unresolved mathematical objection.
Here h_1,h_2,h_3 are arbitrary positive numbers, replacing only the
nonpivot passive payoff -1 when the pivot participates by -h_j. The raw
class now has seven parameters, constrained by abc>1 and

    (v_1+v_2+v_3)/v_3 < R < ac+a+1,
    v=N^-1 h>0.

I verified the displayed inverse-vector formula directly. The identities
a v_3-v_2=h_1 and c v_2-v_1=h_3 imply

    (ac+a+1)v_3-(v_1+v_2+v_3)=(c+1)h_1+h_3>0,

so the enlarged interval is nonempty for EVERY positive h, not just a
neighborhood of (1,1,1).

The new selector has

    z=(h_3 k+y)/[c(1-y)],
    w=(by-h_2 k)/[1+by+(1-h_2)k].

On the prescribed closed k interval its denominator equals
1+k+(by-h_2 k)>0, its numerator is nonnegative, and w<1; also 0<z<=1.
The exact derivative w_k=-(h_2+by)/denominator^2 is negative. Consequently

    G_k=h_1+z_k-a w_k(1-z)+a w z_k>0

on the whole interval, including its possible z=1 endpoint. At k=0 the
residual is negative for 0<y<Y; at the upper endpoint either w=0 or z=1,
and the residual is strictly positive. This proves the unique interior
root without an invalid concavity assertion for general h_2.

Continuity of the root follows from strict monotonicity and local compact
brackets. At zero, k<=by/h_2 forces k=O(y). At Y, every possible limit
lies in the endpoint interval, where strict monotonicity and G(0,Y)=0
force the limit to zero. All denominators stay positive near Y. Expanding
the three defining identities gives precisely

    N (y,z,w) = h k+O(y^2).

Since k,z,w=O(y), multiplication by N^-1 yields y=v_1 k+O(y^2)
and the claimed three ratios. Thus the R(y) endpoint argument is valid
unchanged, with the new lower endpoint and the old upper endpoint.

The full Bellman calculation changes only V_B,1 to h_1 k. The new A-row
identities independently give the claimed w and z formulas; all active
nonpivot values remain zero and every inactive one remains nonnegative.
Quit endpoints remain identically zero or one. Therefore the original
complete-deviation, actual-value, finite-censor, and fixed-target arguments
apply verbatim to the ACTUAL altered table.

For the changed {0,2,3} child, put p=c/(c+h_3), t=1/R. Child 3's
Continue value is c(1-p)-h_3 p=0; pivot Continue is Rt=1; child 2's
Continue value is -h_2 p-(1-p)t<0. The missing player's payoff is exactly

    [-c h_1+h_3(a/R-1)]/(c+h_3).

Its strict negativity follows from the printed inequality. I checked its
cleared positive identity using the two inverse-vector equations above.
The other changed child case has a missing nonpivot debt h_j>0, and
retained nonpivots still strictly prefer their zero Quit reward to -h_j
after withdrawal. All other counterprofiles use no pivot participation
and are unchanged. Thus every proper-child five-kind F/J exclusion survives.

The earlier source-overlap calibration also survives: the nonpivot matrix
and the pivot's inverse passive row are unchanged. The full centered matrix
now has first column (0,-h_1,-h_2,-h_3), and its determinant is
D v_3(R-R_low(h))>0. The same support-by-support argument excludes a
homogeneous simplex solution. I have not promoted these checks to a claim
that every other standard-Q or reward-table producer is excluded.

This is a genuine independent-harm class enlargement, not merely a better
constant for the original profile. A single consolidated statement of this
enlargement includes the unit-harm case and retains the same mathematical
mechanism and honest separation scope.

## Final source-overlap correction: the whole family is product-low

The earlier limited overlap search missed an implemented producer covering
every table considered above. In both versions, forcing Quit gives the pivot
exactly its own singleton reward 1 and gives every nonpivot exactly its own
singleton reward 0, regardless of the independently sampled opponent set.
At any product root with positive absorption, choose any active player.
Its pure-Quit payoff equals its own singleton, so the literal definition
`HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`
holds. All four own singletons are nonnegative.

Consequently `exists_uniformEquilibriumPayoff_of_productLowPremium` in
`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`
already proves existence for the entire seven-parameter enlargement (and
indeed without its displayed interval restrictions). The same source's
`exists_periodic_allSuffix_terminalNash_of_productLowPremium` also already
produces approximate periodic profiles from these raw tables. This is an
exact source-hypothesis match, not an inference from a supplied strategy.

Thus I withdraw the earlier suggestion of missing existence coverage. The
algebraic selector, exact initial payoff, exact full-behavior Nash property,
and all-proper-child F/J exclusions remain sound. Those exclusions show that
the F/J families miss a class already consumed by another implemented
mechanism; they do not justify a new existence-class export. There is no
remaining mathematical objection to the internal selected-profile result.

## Independent review: positive mutual premiums at the actual joint phase

Scope: ONLY the section **Positive mutual premiums at the prescribed joint
phase** of the author's notebook, with the unchanged positive-harm facts
already checked above. Verdict: **PASS as ordinary mathematics.** There is
no unresolved mathematical objection to the new raw-family producer,
unrestricted terminal Nash and fixed uniform target, finite-law consequence,
or all-proper-child F/J separation. No Lean files were changed or built.
Unlike the preceding versions, these tables do not satisfy product-low, and
the failure is strict. This review does not claim a universal exclusion from
every implemented producer or prove arbitrary four-player existence.

### Source and coverage check before algebraic review

I reread `HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`
and `exists_uniformEquilibriumPayoff_of_productLowPremium` in
`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`.
At the row with c_0=c_1=1/2 and c_2=c_3=0, absorption is 3/4. The only
active coordinates have forced-Quit values 1+xi/2 and eta/2, strictly above
their singleton values 1 and 0. Thus the hypothesis fails. Under entrywise
reward perturbation of size delta, either premium changes by at most
2 delta, so delta<min(xi,eta)/4 preserves failure at this SAME root. The
family is outside the reward closure of product-low tables; the old
overlap correction does not consume it.

The unchanged singleton matrix was checked independently. Every row has a
distinct negative entry, so `normalLayer` and `normalCore` in
`UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean` retain all
four players. Write A for the nonpivot 3 by 3 block, v=A^(-1)h>0, and
u=(-1,-1,R-1). Then u v=v_3(R-R_low)>0.

For homogeneous standard complementarity, if x_0>0, row 0 forces x_3>0,
row 3 then forces x_2>0, and row 2 forces x_1>0. Child complementarity
gives z=v x_0, contradicting the strictly positive pivot residual. If
x_0=0, any positive child coordinate propagates around the cycle, after
which A z=0 contradicts invertibility. Thus the matrix is R0.

At offset (1,-h_1,-h_2,-h_3), nonnegative child residuals force every child
coordinate positive, and hence z=(1+x_0)v. The pivot residual is strictly
positive, forcing x_0=0. This is the unique solution, its only inactive
residual is strict, and its active principal determinant is det A=abc-1>0.
The hypotheses of `exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean` therefore give degree one;
`isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean` gives standard Q. These source
declarations were read, not inferred from a note's label.

The two-coordinate principal {0,1} has negative off-diagonal entries. At
offset (-1,-1) it has no standard solution, and at zero its nonnegative
residual conditions force the zero vector. Thus it is neither standard Q
nor homogeneous-feasible, as claimed for the projective-Q-bar exclusion.
The previous exact passive-row calculation remains valid:
(u A^(-1))_2=(R-R_high)/(abc-1)<0. Every other triple contains a row whose
off-diagonal entries are all negative. A nonnegative inverse would make
that row of its product with the original matrix nonpositive, contradicting
the identity's positive diagonal entry. For the full matrix, its inverse
entry (0,1) is

    -[bc(R-1)-(c+1)] / [(abc-1)v_3(R-R_low)] < 0.

Here R_low>1+(c+1)/(bc), as follows directly from the positive formula for
v and abc>1. This verifies the relevant inverse-screen failure without
depending on the sign of every other inverse entry.

The hypotheses of `PairedCycle.RawRegion` in
`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`, and
`OwnBounds`/`PassiveBounds` in `MathUE/PairedAffineIntervalEstimates.lean`,
require the stated two positive nonpartner singleton comparisons in a
four-player paired schedule. The present rows each have only one positive
comparison. This is a valid named-source mismatch, preserved by relabeling
and positive playerwise scaling/translation of TERMINAL rewards. No
strategic invariance under arbitrary additive normalization of Never=0 is
being assumed. The previously reviewed fixed deadlock-completion mismatch
also survives because (22) leaves singleton rows unchanged.

### The changed scalar producer

The allowed k interval keeps d=1+k+(by-h_2 k)>0, 0<=w<1, and 0<z<=1.
Using 1-w=(1+k)/d, the new residual is

    G_eta=h_1 k+z-a w(1-z)+eta k-eta k(1-z)/d.

Differentiation gives exactly equation (24). Its final bracket is
nonnegative because eta<=a min(h_2,1), while h_1+eta>0 and z_k>0.
The residual is therefore strictly increasing on the whole admissible
interval, including its endpoints. At k=0 its sign is unchanged; at the
upper endpoint w=0 or z=1 and the new summand is nonnegative. This produces
one unique interior root from every y in (0,Y).

The argument for continuity and the k(Y)=0 limit remains valid with this
strict derivative. Near zero, k,z,w=O(y) and the added summand is O(y^2),
so the old leading ratios and R_low(h) are unchanged. At Y the rates have
k=0, and the new endpoint is (1+xi Y)R_high. Consequently every stipulated
R in (R_low(h),R_high) is attained strictly inside the y interval. This
does not assume monotonicity of the resulting R_xi,eta function.

### All actions, actual values, and quantifiers

I derived the A-row equations directly from the altered literal reward
(1+xi,eta,-h_2,-h_3) on {0,1}. The pivot Quit value is p=1+xi y and its
Continue value is (1-y)V_B,0. Player 1's Quit value is t=eta x and its
Continue value is -h_1 x+(1-x)V_B,1. Equations (23)-(25) set these pairs
equal. Players 2 and 3 have the same A Continue recurrences as before and
still have zero Quit value, including ties with the prescribed pair.

At B and C, forcing the pivot to Quit cannot realize {0,1}, so its Quit
endpoint is one. The displayed continuation values exceed one. For player
1 these Quit endpoints are zero, and its B and C values are positive.
Players 2 and 3 still receive zero whenever they themselves Quit. The
remaining B and C recurrence entries follow from their solo rows. Thus
every individual supported action attains its displayed value and every
alternative pure action is no better, at all three phases.

For the rational fixture, direct exact enumeration gives phase vectors

    A: (5/4,17/121,4/11,0),
    B: (5/3,14/55,0,7/15),
    C: (50/23,7/11,0,0).

Substitution gives G_eta=0, z=7/30, w=4/15, and R=1735/368. Every
Continue endpoint equals the corresponding displayed value. Quit endpoints
are (5/4,17/121,0,0) at A and (1,0,0,0) at B,C. Hence all 24 pure-action
inequalities and all 12 prescribed Bellman equalities hold exactly. The
extra zero at player 3's A value is harmless even though it Continues
surely there; only equality at supported actions is needed.

An arbitrary full behavioral deviation retains positive independent
opponent hazards in each period. Thus the same bounded-remainder iteration
both identifies the ACTUAL values and caps complete deviations. No
stationary or finite-menu restriction on deviators is introduced. The
finite censor argument still bounds payoff error by 2M tau_K and full
exploitability by 4M tau_K. Its candidate pivot law is feasible for the
inner repair minimization, so the claimed upper bound on repair value
follows. The exact phase-A vector is fixed before accuracy, and the
existing terminal-family consumer supplies one threshold for every large
horizon with the same selected finite profile.

### Proper-child falsifiers after changing both premiums

The only sure-child witness that uses the changed coalition as its actual
outcome is S={0,1}. Its members now get 1+xi and eta, versus withdrawal
values zero and -h_1. Both still prefer Quit, while an omitted nonpivot
gets -h_j and gains by joining for zero. When a larger full child contains
{0,1}, a withdrawing third child's payoff remains -h_j: the only altered
coordinates of that pair are 0 and 1. Thus those child Nash checks are
unchanged too.

For the exact three-nonpivot child cycle the quiet pivot payoff is still
R/R_high, and its phase-A Quit value increases to 1+xi Y. The strict
outsider debt therefore survives. For S={0,2,3}, the omitted player's
joining coalition always contains the sure quitter 2, so it cannot be
{0,1}; its previously checked gain and the child equilibrium are unchanged.
The solo-owner witnesses in the other cases likewise use no changed
reward comparison. All fourteen nonempty proper children are still
covered, each with zero child regret, joint Never zero, and a strictly
profitable omitted player. The common five-kind slack inequality then
rules out every nonnegative choice of certificate weights.

No missing strategic witness remains in this special-class argument:
the raw parameters select all four rates, the complete values, actual
independent strategies, finite laws, and a fixed uniform payoff. This is a
sound new candidate for coverage beyond the particular named gates audited
here. An independent second review and the coordinator's final export gate
remain separate from this PASS.
