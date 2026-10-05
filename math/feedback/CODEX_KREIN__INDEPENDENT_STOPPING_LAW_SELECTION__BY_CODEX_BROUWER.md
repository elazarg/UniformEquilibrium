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

## Independent review: consolidated pivot-first raw family

Scope: **Proposed generalization: select the pivot equation first**, with
equations (28)-(39), in the same author's notebook. Verdict: **PASS as
ordinary mathematics**, with no unresolved mathematical objection. This
assessment reuses the preceding checks only for unchanged complete-deviation,
censoring, consumer, and original-completion F/J arguments. The pivot-first
selector and the newly freed reward entries were checked separately.

The actual inputs are the raw singleton and exceptional-pair rows (28),
the participant caps (29), positive a,b,c,h_j, abc>1, u,v<1, xi,eta>0,
q_2,q_3<=0, and the stated open R interval. No strategic witness is an
input. The conclusion quantifies over every completion satisfying the
literal participant caps, and over all complete behavioral deviations.

### Implementation overlap and scope

The same explicit absorbing product row on {0,1} witnesses strict failure
of `HasProductLowQuittingPremium` for every new completion. The earlier
perturbation margin still applies. Both new freedom and arbitrary eta
include the previously checked original completion, so no general
product-low theorem covers this enlarged class. The supplied-object
consumer `isUniformEquilibriumPayoff_of_isQuittingBlockCertificate` in
`UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean` assumes the
whole hazard/value certificate, including row recurrences and individual
endpoint inequalities. It does not produce the pivot branch proved here.
Its literal certificate hypotheses were inspected.

The broader class is not claimed to avoid every other producer at every
completion. In particular the all-child F/J exclusion is now restricted
to the old completion; arbitrary unused passive rewards may create other
quiet-lift mechanisms. This is the correct scope, and the proof does not
silently reuse an old-completion separation for all newly allowed tables.
The source comparisons already checked above continue to witness that
the retained old-completion subfamily escapes the named singleton/paired
and product-low gates.

### Pivot branch: existence, endpoints, and continuity

Since q_j<=0 and 0<=y<=Y<1, H_j(y)>0. On the entire admissible interval,
d=1+k+(by-H_2 k)>0. For y>0 and k<K(y), both z and w lie in (0,1).
The derivatives of z and w in (31) have the stated strict signs. The
numerator defining P is strictly positive, increases as z increases,
and its denominator (1-z)w strictly decreases. Hence P increases
strictly and tends to infinity at K(y). This remains true if both
endpoint events w=0 and z=1 coincide.

Equation (32) is the correct k=0 simplification. Its positive bracket
is c(p-u)+(p-v), so it and the rational factor increase strictly.
The endpoint identities (33) are exact. The inverse-vector identities
give nu_1/nu_3>1/b and nu_2/nu_3>1/(bc), which prove the strict lower
endpoint comparison. Thus there is a unique y_star in (0,Y), and one
unique positive k_R(y) for every y in (0,y_star).

The continuity argument uses fixed local brackets strictly inside K(y),
which stay admissible under a small y perturbation. At y_star choose
zero as the lower endpoint and an arbitrarily small fixed positive upper
bracket; strict monotonicity makes the root tend to zero. At zero,
k_R(y)<=by/H_2(y)=O(y) is sufficient. No unproved global implicit-function
or branch-selection hypothesis is needed.

To obtain the ratio limit, multiply P=R by (1-z)w/y, as in the note.
Every subsequential limit t satisfies

    (R-1)(b-h_2 t)=s_1+s_2(1+h_3 t)/c.

The right side is strictly positive, ruling out t=b/h_2. The coefficient
of t is h_2(R-1)+s_2 h_3/c>0, so the equation has exactly the displayed
solution tau, and all subsequential limits agree. Its positivity follows
from R>P_0(0). The function F is strictly increasing, and the identities
b nu_1-nu_3=h_2 and c nu_2-nu_1=h_3 give F(1/nu_1)=R_low. Therefore
tau>1/nu_1 follows from the actual prescribed R>R_low.

### Closing the remaining equation for arbitrary positive eta

Along that branch, the eta summand is O(y^2) for every fixed finite eta,
because k,z,w=O(y) and its bracket is O(y). The linear coefficient of G is

    h_1 tau+(1+h_3 tau)/c-a(b-h_2 tau)
      =[(ac h_2+c h_1+h_3)tau-(abc-1)]/c
      =(D/c)(nu_1 tau-1)>0.

At y_star, k=0, so G has the same strictly negative sign as the old
zero-k expression with y_star<Y. Continuity supplies an interior zero.
This uses a sign change in y and requires no monotonicity of G in k or y.
The former eta upper bound is consequently unnecessary, rather than
being hidden in the new endpoint calculation. Identity (30) follows
directly from a nu_3-nu_2=h_1 and c nu_2-nu_1=h_3 and guarantees a
nonempty R interval for every stipulated raw parameter tuple.

### Freed rewards and complete-vector safety

At phase A, the actual only terminal coalitions are {0},{1},{0,1}.
Their prescribed rewards are exactly (28). For players 2 and 3, averaging
their singleton and collision rewards gives H_j=h_j(1-y)-q_j y,
which yields the two printed A-row expressions. The pivot's Continue
reward is u y+(1-y)V_B,0; player 1's is
-h_1 x+(1-x)V_B,1. The selected equations give equality with p and t.
The B and C recurrences use only their prescribed singleton rows.

The unused nonparticipant rewards cannot affect either the prescribed
profile or its unilateral-deviation inequality. Whenever a deviator joins
a nonsingleton coalition, it is a participant and its OWN reward is bounded
by (29). At A, a deviation by 2 or 3 may create a pair or a triple, but
its coordinate still has the required cap zero. A deviation by 0 or 1
at A uses the explicitly treated exceptional pair. At B and C, no unilateral
deviation can form {0,1}, so pivot Quit values are at most one and every
nonpivot Quit value is at most zero. Thus arbitrary nonparticipant entries
in unused rows are truly irrelevant to each tested player's own payoff.

All displayed nonpivot values are nonnegative; the pivot values at B,C
strictly exceed one by u,v<1 and equation (39). Every action in the
prescribed support attains its value. The geometric opponent contraction
therefore proves ACTUAL terminal values and unrestricted behavioral Nash,
including history-dependent and Never choices. It also puts the displayed
values in the reward box required by the supplied periodic consumer.
The exact fixed target and finite-censor bounds follow as in the earlier
review; finite hazards are selected once from the table before accuracy.

I independently enumerated both rational examples over every opponent
subset at each phase. Each has P=R, G=0, all 24 pure-action inequalities,
and all 12 prescribed Bellman equalities exactly. Their phase-A vectors are

    first:  (5/4,8027/10201,49/101,0),
    second: (5/4,62786/81709,195/404,0).

The second calculation used participant caps and every otherwise unused
nonparticipant coordinate equal to 37, as stipulated. It confirms actual
independent collision payoffs q_2=-2 and q_3=-3, unequal pivot singleton
payoffs u=1/2 and v=-1/2, and eta>2. These are exact boundary checks of
the real-parameter proof, not a substitute for its selection argument.

No additional strategic input remains unproduced. This consolidated
statement is a sound candidate for one final raw-class packet after its
independent second review and coordinator gate. The general arbitrary
canonical table remains outside its proved scope.

## Focused response-quotient check on an exact admitted table

This additional check is motivated by a later source-overlap correction
to my own symmetry route. It concerns the original positive-premium
fixture a=b=c=2, h_1=h_2=h_3=1, xi=1, eta=17/11,
R=1735/368. It does not assert partition exclusion for every parameter
or arbitrary completion in the consolidated class.

`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`
requires that rows in a common block have equal sums over EVERY block.
For the fixture, the centered singleton matrix is

    [[0,-1,-1,R-1],[-1,0,-1,2],[-1,2,0,-1],[-1,-1,2,0]].

All fourteen nondiscrete partitions can be checked directly:

- For a single merged pair, {0,1} requires R=3 from the singleton
  column 3, which is false. Each other merged pair has a retained
  singleton column comparing -1 with 2. Thus all six fail.
- For two pairs, {0,1}|{2,3} has unequal within-{2,3} row sums -1
  and 2; {0,2}|{1,3} has unequal within-{1,3} row sums 2 and -1;
  {0,3}|{1,2} has unequal within-{0,3} sums R-1 and -1.
- Every triple containing 0 has its remaining singleton column contain
  both -1 and 2. The sole first-order survivor is {0}|{1,2,3}.
- A single full block would require equal total row sums R-3=0,
  hence R=3, again false.

For the surviving partition, give player 0 any hazard x in (0,1] and
all nonpivots hazard zero. At the three-player block's common zero
coordinate, direct exact field evaluation yields

    F_1=x+eta*x^2,              F_2=F_3=x.

Indeed every child's passive singleton at owner 0 is -1; forcing player
1 to Quit has value eta*x, whereas forcing either other child to Quit
has value zero. Since eta>0, the actual individual residuals differ.
The definition `quittingDiscountedDisplacement` in
`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean` at
discount zero is precisely this field. Thus actual response invariance
fails for the sole remaining candidate as well.

The fixture therefore has no nontrivial response-invariant partition,
including partitions not generated by automorphisms. Its discrete
partition is the ambient matrix, whose R0 degree +1 was checked above.
Consequently the existing response-quotient nonunit-degree producer does
not consume this exact admitted table. This is a concrete named-source
separation, not an assertion about every possible equilibrium producer.

## Independent review: diffuse only the solo phases

Scope: the notebook section **Further producer: diffuse only the solo
phases**, equations (40)-(43), using the already reviewed pivot-first
selector for its unchanged five prescribed reward vectors. Verdict:
**PASS as ordinary mathematics**, with no unresolved mathematical
objection. The weakened raw criterion produces approximate terminal
equilibria with ONE fixed target, finite common-menu laws, and uniform
equilibrium against all behavioral deviations. It does not assert exact
equilibrium of each refined periodic row schedule.

### Exactly which reward caps remain

At the undiffused row, prescribed opponent sets for outsider 2 are
empty, {0}, {1}, and {0,1}. If it Quits, these become {2}, {0,2},
{1,2}, and {0,1,2}. Its singleton reward is already zero, leaving
precisely the first three inequalities of (40). The same enumeration
for outsider 3 gives the other three inequalities. No fourth-player
coalition can be reached by one deviator at this row. The two prescribed
participants use only their singletons and the exceptional pair, whose
literal rewards are unchanged.

During a solo row owned by j=2 or 3, a unilateral deviator i distinct
from j can produce only its singleton or {i,j}. Thus the six premiums
in (42) are exhaustive for the diffuse rows. They are finite because
the original table is finite. No triple participant cap, passive reward
on an unused coalition, or grand-coalition cap is silently needed there.

The auxiliary capped table is legitimate: it agrees with all five
prescribed vectors and replaces only otherwise unspecified participant
entries by capped values. Its previously proved source selects x,y,z,w.
The argument transfers its actual prescribed payoff recurrences to the
original table, and then proves original-table incentives anew. It does
not transfer exact Nash merely by matching prescribed outcomes.

### Actual payoff and exact Continue at every refined date

The n-fold solo block has exactly the original product survival. Conditional
on entering it, its only possible absorbing coalition is the same singleton.
Hence replacing both blocks preserves the distribution of the first
absorbing coalition, period by period, including every component of the
unchanged joint row. The actual initial payoff is therefore precisely (41)
for every n.

For a player-2 block with m microstages remaining, let
rho=1-(1-z_n)^m. Its actual value is

    W_m=rho*r({2})+(1-rho)*V_C.

The scalar recurrence rho=z_n+(1-z_n)rho_next gives the exact vector
policy recursion. Since 0<=rho<=z and
V_B=z*r({2})+(1-z)*V_C, this vector lies on the closed segment from
V_B to V_C. Both endpoints have every coordinate at least its own
singleton s_i. In the owner coordinate both endpoints are zero, so the
owner value is zero at EVERY microstage. The analogous formula for the
player-3 block lies on the segment from V_C to V_A, whose player-3
coordinate is zero throughout.

For a nonowner, the prescribed action is pure Continue, so policy
recursion IS pure-Continue transport. For a solo owner, its current and
next values are zero and all opponents Continue, so pure-Continue
transport is also exact, as is its supported Quit payoff. At the joint
row, the endpoint equalities of players 0 and 1 persist from the selected
source, and the two outsiders Continue surely. Thus the stronger exact
Continue condition holds for all four players at every refined date;
it has not been inferred merely from a generic mixed policy equation.

These segments also give a common finite value bound independent of n.
One can take the maximum absolute coordinate of V_A,V_B,V_C together
with a bound on the original rewards. Thus the fixed-bound hypotheses
of the intended source consumer are supplied uniformly in accuracy.

### The error is incurred once, even over infinitely many periods

At a solo j-row, outsider i's Quit endpoint is exactly
s_i+delta*(r_i({i,j})-s_i), hence at most its CURRENT displayed value
plus C*delta. At the joint row both prescribed players' Quit endpoints
are exact, and (40) bounds each outsider's Quit endpoint by zero.
The bound e_n=C*max(z_n,w_n) therefore applies at every date and player.

For a fixed player set S_t=V_t+e_n. If a_t is its absorbing Continue
contribution and q_t its opponents' survival probability, the exact
Continue identity gives

    a_t+q_t*S_(t+1)=V_t+q_t*e_n<=S_t.

Quit is also bounded by S_t. Consequently EVERY behavioral mixture at
every surviving history is bounded by this same supersolution. After
iteration the only extra term is a bounded survival remainder; there
is no sum of e_n over dates. For every fixed n, each full refined period
has unchanged positive opponent absorption, so the remainder tends to
zero under every deviator. For a suffix starting in the middle of a
period, its finite initial fragment does not affect this convergence.
Never and arbitrarily delayed finite deviations are included.

This is the exact scope of
`quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue`
and `QuittingInfinitePathQuitErrorCertificate.isεAsymptoticNash_and_delivers`
in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`.
I read both statements and their literal certificate fields: bounded
values, policy evaluation, exact Continue, uniform Quit error, and
playerwise opponent survival at every start. All are constructed here.
The same file's
`isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError`
then consumes the accuracy-indexed source. These are existing supplied-path
consumers; none assumes that arbitrary raw data (28),(30),(40) supply this
mixed joint/solo source.

### Finite laws, fixed target, and claimed enlargement

The unchanged per-period marginal survival probabilities are 1-x, 1-y,
1-z, and 1-w. Censoring after K refined periods therefore changes total
marginal mass by at most the stated tau_K, independent of n. The original
table's bound M gives payoff error at most 2M*tau_K and full-regret error
at most 4M*tau_K by the same uniform coupling used earlier. Combining
with e_n is legitimate for arbitrary replacements of any single law.
Choosing n first and K second yields actual finite laws on the common
menu of (2n+1)K dates and Never. The inner pivot repair can use the
displayed pivot marginal, so its infimum has the same upper bound.

The target V_A depends only on the selected raw table; it does not vary
with n, K, accuracy, or the final horizon. The named retained-family
terminal consumer supplies one profile and one horizon threshold for
each accuracy. No unjustified threshold uniformity in n is used.

The source enlargement is real relative to the prior raw criterion:
arbitrary finite positive participant rewards at diffuse-only pairs and
all remaining unused coordinates are admitted. The earlier theorem (29)
does not apply to them, while the new construction explicitly bounds
their original-game deviation effects. The inspected
`singletonArcCycle_isTerminalNash_and_hasValue` in
`UniformEquilibrium/Quitting/Cycles/SingletonArcCycle.lean` assembles
supplied singleton arcs; it does not select this raw joint/solo path.
The note correctly attributes refinement and the one-error method as
existing mathematics, with the new work being the actual source.

For the beta modification, only player 2's join into a player-3 row
creates a new premium, giving the sharper e_n=beta*w_n. Its value at
the FIRST player-3 microstage is zero, so that row still has positive
local Quit gain beta*w_n for every finite n. Later values in that block
increase along the preserved segment; the supersolution bound remains
uniform. This checks the distinction between the failed exact grammar
and valid vanishing-error construction. The new class still strictly
fails product-low at the unchanged {0,1} product root. No all-child F/J
exclusion or exclusion from every other producer is inferred for its
arbitrary completions.

## Independent review: quadratic nonpivot selection and the complete R axis

**PASS as ordinary mathematics**, with no unresolved mathematical
objection to the section bearing this title in the author's notebook.
I conducted this review without reading MORSE's review of the new section,
using my previous checks only for unchanged joint/solo mechanics and the
one-error refinement. No Lean build or implementation was performed.
The frozen export is not modified here.

The exact raw class has the five vectors (28), positive a,b,c,h,xi,eta,
abc>1, q_2,q_3<=0, v<1, u<=1+xi, arbitrary real R, and exactly the six
outsider participation caps (49). All remaining coalition coordinates
are arbitrary finite numbers. The conclusion concerns the original game,
complete behavioral deviations, and one fixed target before accuracy.

### Quadratic identity, unique branch, and the linear degeneracy

I independently expanded C*d*G. Its apparent 1+k denominator cancels
because `1-w=(1+k)/d`. The coefficients are exactly (53), including
the eta terms; no cubic term has been dropped. On 0<y<Y both bounds
defining K are strictly positive. On the closed k interval,
`d=1+k+[by-H_2*k]>=1+k>0`, z is in [0,1], and w is in [0,1).
At K either z=1 or w=0, eliminating the sole negative term of G;
h_1*K is strictly positive and the eta term is nonnegative. Thus
Q(K)>0 while Q(0)=gamma<0.

Beta is strictly positive on the entire CLOSED y interval:
`a*E-y=ac-L*y>=1/b`, and the other displayed summands are nonnegative,
with several strictly positive. Negative d_1 or large eta can affect
alpha but not this beta argument. A polynomial of degree at most two
with the stated strict endpoint signs has exactly one interior root.
Two quadratic roots inside would force equal endpoint signs; a double
root cannot give the sign change. The actual root is simple.

The discriminant is therefore positive. The selected expression

    k=-2*gamma/(beta+sqrt(beta*beta-4*alpha*gamma))

has a positive denominator. If alpha=0 it is exactly -gamma/beta. If
alpha<0 and two positive roots exist, it is the smaller one, which the
endpoint signs place before K. At y=0,Y, gamma=0 and beta>0, so this
same expression extends continuously to zero. It remains continuous
when alpha changes sign. No monotonicity of G or division by alpha is
being assumed.

### Both limits and the actual covered interval

The identities beta(0)=D*nu_1 and gamma(y)/y tending to -D give
k/y tending to 1/nu_1. Substitution yields z/y tending to nu_2/nu_1
and w/y tending to nu_3/nu_1>0. Cancelling the common order-y factor
in P gives precisely R_low, without a sign requirement on the numerator.
At Y, k=0 and the exact P_0 identity gives R_top=T_2+xi*D/b. The
denominator `(1-z)*w` is positive for 0<y<=Y. Consequently the
intermediate value theorem supplies every strict intermediate R, with
all four hazards strictly interior, even if R(y) is not monotone or
the selected y is not unique.

The passive thresholds check algebraically with the receiver-first row
convention. Formula (50) is the literal outside row times A inverse.
Since T_3>T_1, all weights are nonnegative exactly when
R>=T_pass=max(T_2,T_3). For s_1>=0 the first identity comparing R_low
is strictly positive; for s_1<0 the alternate identity (51) is strictly
positive. Finally R_top>T_pass in the first case and
`R_top-T_pass=D*(1+xi-u)/b>=0` in the second. At u=1+xi the possible
equality R_top=T_pass creates no gap: the constructive open interval
reaches every R below T_pass, and exact equality uses the weak passive
inverse theorem.

### Floors and all behavioral deviations

The selected equations give the displayed four-coordinate values. In
particular `(V_B)_1=k(h_1+eta)>0`, all nonpivot values are nonnegative,
and `(V_B)_0-1=(1+xi-u)y/(1-y)>=0`. Equality is harmless. Rearranging
the B recurrence and using v<1,z>0 gives `(V_C)_0>1`; A has pivot
value p>1. None of these facts requires R>1, c*s_1+s_2>0, or p-u>0.

The six caps list every outsider joining coalition at the undiffused
joint row, apart from its zero singleton. At a solo row, one deviator
can create only the appropriate pair, whose finite premium enters
C_join. Refined values lie on the original phase segments and retain
the singleton floors. Owners stay zero throughout their own solo blocks.
Both policy evaluation and EVERY player's pure-Continue identity remain
exact at every refined date, including the joint row.

Adding e_n to each continuation value yields one Bellman supersolution:
Continue carries q*e_n<=e_n and Quit is bounded directly. The loss is
therefore incurred once, not summed over the unbounded number of dates.
Each deviator's opponents retain a strictly subunit period survival
factor, eliminating the bounded remainder against arbitrary complete
behavioral replacements, including delayed and Never deviations.

I reread the literal fields and consumers
`quittingRootSequenceHazardTerminalValue_le_add_of_quitError_exactContinue`,
`QuittingInfinitePathQuitErrorCertificate.isεAsymptoticNash_and_delivers`,
and `isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError`
in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`.
The exact policy/Continue transport, bounded values, Quit cap, target
identity, and playerwise survival hypotheses are all produced here.
A common value bound follows from the fixed compact phase segments.
Censoring retains the ORIGINAL reward bound M, with target error at
most 2M*tau_K and full regret at most e_n+4M*tau_K. Choosing n and
then K keeps V_A fixed before every accuracy and eventual horizon.

### Exact original-table source exits, including both equalities

For positive pivot coordinate in a homogeneous LCP solution, the child
inequalities force every child coordinate positive; their equalities
then give z=t*nu. For zero pivot, a positive child propagates positivity
cyclically and contradicts invertibility of A. Thus M_full is R0 for
R different from R_low.

Below R_low the test offset forces z=(1+t)*nu. The two displayed pivot
solutions are exhaustive, with a strictly positive inactive residual
at t=0 and active determinant signs + and -. I inspected
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean`: strict-inactive and
nonsingular hypotheses hold for EVERY root, giving degree exactly zero.

The complete source statements
`exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`
and `finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`
were inspected. The former adds no normality or premium assumptions on
unused coalition entries; the latter supplies full original-table R0
under noUE. Thus (1,nu) gives the stated homogeneous contradiction at
exact equality R=R_low, without a limiting strategy argument.

I also inspected `inverseWeight`, `factorization`, and
`exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
They require NONNEGATIVE outside weights, not strictly positive ones,
and impose no condition on the unused nonsingleton completion. Hence
R>=T_pass, including equality, is consumed for the SAME original table.
Together the three source cases and the constructive case cover every
real R with no endpoint gap.

### Exact falsification tests and actual-source enlargement

The fixture u=7/4,v=0,eta=17/11,R=685/368 checks exactly. The old
interval is empty, c*s_1+s_2=-1/2, and the quadratic coefficients are
(-5/11,387/44,-7/8). Substitution of k=1/10 gives zero. I independently
recomputed all displayed phase values, twelve policy equations, twelve
pure-Continue identities, and the passive weights
`(363/644,685/2576,-281/1288)`. The last negative weight genuinely
excludes the selected child-inverse exit.

The alpha=0 fixture also checks: eta=2 gives (beta,gamma)=(37/4,-7/8),
k=7/74, rates (7/81,1/4,17/74,10/37), and R=12509/6840. I obtained

    V_A=(5/4,14/81,10/27,0),
    V_B=(13/12,21/74,0,17/37),
    V_C=(481/342,2/3,0,0),

which satisfy every policy and pure-Continue identity. These are exact
rational checks, not floating-point evidence for branch continuity.

Allowed positive premiums at {2,3} create genuine immediate-Quit gains
in the unrefined profile while preserving all policy and Continue
identities, exactly as the refinement argument predicts. For instance,
set both participant rewards at {2,3} to 1/2 in the original cyclic
completion of the first fixture. The premium traps {0,1} and {2,3}
have full-player union. Thus the admitted class is NOT automatically
subsumed by either the two-variable-participant theorem or its
canonical-core-at-most-two extension. This exact completion has no pure
absorbing coalition equilibrium: the cyclic joining/leaving obstructions
persist, and player 3 still prefers reward 2 from player 2 quitting alone
to the new pair reward 1/2. I make no class-wide claim excluding every
proper-child family or every conditional strategy producer.

This is an actual raw-data construction across the previously missing
interval, with existing exact source exits elsewhere. It retains genuine
four-player premium cores, arbitrary finite unused rewards, and the same
six undiffused caps. It is not merely an improved endpoint constant.

## Final artifact check, including the direct uniform-horizon estimate

**PASS** for the complete standalone assembly
[`CYCLIC_CHILD_WITH_ONE_JOINT_PHASE.md`](../exports/CYCLIC_CHILD_WITH_ONE_JOINT_PHASE.md), SHA256
`3ef4adde01e7f72c8f5b57fbf575c50ab1862811c76b6518d34908fd398fd61d`.
I read the full 561-line artifact and checked its hash. The mathematical
scope, quadratic proof, equality cases, source exits, and exact fixtures
are preserved from the reviewed theorem. The scalar shortfalls sigma_1
and sigma_2 are consistently distinguished from the own-singleton vector.
The complete fifteen-row fixture agrees with the admitted cyclic
completion having both {2,3} participant rewards 1/2; C_join=1/2 and
the full-premium-core assertion are correct. No mathematical repair is
needed. This remains ordinary mathematics, not a Lean check.

The new direct horizon argument was checked substantively, not accepted
as a presentation-only delta. Fix the refinement n, period length
m=1+2n, and a deviator i. Pre-sample the opponents' independent live-date
action coins. Their first prescribed Quit date T_opp has

    Pr(T_opp>km)=rho_i^k,
    E[T_opp]<=m*sum_(k>=0)rho_i^k=m/(1-rho_i).

This representation is valid because the opponents use only the public
clock and survival, with fresh independent action randomization. Before
absorption, a deviator cannot alter their scheduled hazards. Under ANY
complete behavioral replacement of i, the actual absorption time is at
most T_opp, pathwise in this coupling: the deviator can only cause earlier
absorption. This includes arbitrary private randomization, stopping based
on the observed survival history, delayed Quit, and Never. Therefore
the expected absorption bound is genuinely uniform over the deviator's
entire strategy, not merely over stationary or fixed-date responses.
The prescribed profile obeys the same bound. Taking the maximum over
players gives exactly the stated finite C_time.

On any absorbed path, the terminal reward has magnitude at most M and
the payoff stream is zero before absorption and constant afterward.
At horizon N the pathwise average/terminal discrepancy is bounded by
M*min(T,N)/N, with T counted to include the absorbing date; allowing
2M*T/N, as the artifact does, is therefore safely conservative and
covers either immediate- or next-stage absorption indexing. The same
bound covers T>N, where the horizon has ended before the terminal
reward is paid. Absorption is almost sure because E[T] is finite.
Taking expectations yields the claimed uniform bound

    |expected N-date average - expected terminal payoff|
        <=2M*C_time/N.

Comparing the deviating average to its terminal payoff, using the proved
terminal regret e_n, and comparing the prescribed terminal payoff to
its average gives

    finite-horizon regret <=e_n+4M*C_time/N.

The prescribed terminal target is exactly V_A, so delivery error is at
most 2M*C_time/N. One first fixes n to make e_n small, then fixes one
horizon threshold. C_time may depend on this n, but not on the deviator
or the eventual horizon. Every larger horizon satisfies the same bounds
for that SAME profile and target. This proves the required uniform
quantifiers directly and does not rely on the censored profile retaining
the uncensored geometric survival bound.

The finite-law route remains separately valid, with opponent-marginal
coupling for a fixed arbitrary deviation and a second comparison for
the prescribed payoff. The assembly keeps those two horizon routes
distinct. The source correspondences are self-contained named inputs,
with no dependency on a conference notebook or review record inside the
packet. My PASS covers the new direct estimate as well as the preserved
theorem and fixtures.

## Independent review: switched joint pair and two high passive rewards

**Verdict: PASS as ordinary mathematics, not Lean-checked.** I independently
checked the complete section “Switched joint pair: two passive rewards
above the pivot singleton,” without reading MORSE's review. The preceding
restricted-architecture positive-gap proof, including its reversed-solo-
order extension, is OUTSIDE this review and is not used by this theorem.

The claim checked prescribes the four singleton vectors and
r(03)=(1,-h1,-h2,0), with a,b,c,h1,h2,h3>0, abc>1, U,V>=1,
and arbitrary real R. Its extra hypotheses are the three player2 caps
at 02,23,023 and J+nu3*Q<=nu2, where
J=max(0,r1(01),r1(013)) and Q=r1(13). All omitted coordinates
remain arbitrary finite numbers. The conclusion is an original-table
fixed-target UE against complete behavioral deviations.

### All-real-R source exits and equality

Writing d1=U-1,d2=V-1, the threshold order is T2<=T3<=T1,
so the maximal passive threshold is T=T1. The literal outside inverse
weights are the same three threshold differences already checked.
Thus R>=T, including equality, satisfies the raw weak inverse source.
I re-read `exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`;
no additional nonsingleton or premium-sign premise is needed.

For R<Rlow put delta=nu3*(Rlow-R)>0 and use offset
(q0,-h1,-h2,-h3) with q0>delta. A pivot variable t forces the
unique child solution (1+t)*nu. The two roots have t=0 and
t=q0/delta-1, with active determinants D and -D*delta respectively.
The first has positive inactive residual q0-delta. The full matrix is
R0 whenever R differs from Rlow: a positive homogeneous pivot forces
child t*nu and zero pivot residual only at equality. Thus the degree
is zero below Rlow. At R=Rlow, (1,nu) is a nonzero homogeneous
solution, invoking the separate Fin4 R0 requirement. This calculation
does not require the old signs of the two passive shortfalls.

The relevant previously inspected declarations are
`exists_uniformEquilibriumPayoff_of_r0Degree_ne_one`,
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff`, and
`exists_finset_r0Degree_eq_sum_sign_det`, in their cited singleton-
degree and R0-degree-sum files. They consume the actual original table.
The identity

    T-Rlow=[h2*(c*d1+d2)+b*d2*h3]/(bc*nu3)

is correct and positive unless U=V=1. In that case the outer exits
meet at R=1 and cover everything; no degenerate selector is needed.

### Zero-premium quadratic and positive outsider buffer

The cyclic relabeling (3,1,2) is correct. The cleared quadratic
calculation is algebraic at eta=0: its linear coefficient stays
strictly positive, its constant coefficient is negative inside the
y interval, and its cap endpoint value is positive. There is precisely
one simple admissible crossing. The rationalized root formula remains
valid at alpha=0, is continuous, and tends to zero at both endpoints.
No strictly positive joint premium is silently reused.

The alternate pivot equation is exactly the indifference equation of
the actual joint03 row. Both intermediate pivot values are at least
one by U,V>=1, independently of R's sign. At the upper endpoint
z=c*w*(1-z) and z=y/[b*(1-y)], giving
R(Y')=1-d1/b-d2/(bc)=T. The small-y ratios give R(0)=Rlow.
Continuity therefore covers the missing interval without a monotonicity
or uniqueness assumption for y.

For the strict estimate k<y/nu3, a test point outside the admissible
cap is immediate. Inside the cap, substitution gives

    z0=nu1*y/[nu3*(1-y)],
    w0=nu2*y/[nu3+(nu2+1)*y].

The first strictly exceeds, and the second is strictly below, its
linear approximation. Hence the balance is positive at that test point
using h3+nu1-c*nu2=0. The unique admissible crossing lies below it;
no monotonicity of the balance away from its root is being asserted.

The sign of Q is retained. The actual outsider1 Quit endpoint is at
most (k*J+y*Q)/(1+k). Since a*nu3-h1=nu2, the raw condition
is exactly a-Q>=(h1+J)/nu3. Combining it with k<y/nu3 and
h1+J>0 proves strict safety, even for Q<0 and equality in the raw
cap. The player2 singleton and its three capped coalitions exhaust
that outsider's possible Quit outcomes at the joint row.

### Full values, refinement, and uniform horizons

All coordinates of the three phase vectors check in original player
order. At A both supported players are indifferent, outsider1's
prescribed value is w/(1-w), and outsider2's is zero. The B and C
equations are exact singleton recurrences. Every pure-Continue endpoint
equals the displayed value, and every value dominates its singleton.

Solo refinement interpolates between the endpoint vectors, holds each
owner at its singleton, and preserves the SAME V_A for all accuracies.
All arbitrary omitted pair surpluses enter the finite C_join. The
common error e_n tends to zero; adding e_n to every value gives a
supersolution for both unilateral actions, so it is charged once,
not once per date or period. Larger omitted coalitions cannot occur
under one deviator at a solo row; the joint-row tests already cover
all coalitions a single outsider can create there.

Every player's prescribed opponents have positive absorption probability
per period. Pre-sampling their independent clock-based coins couples
actual absorption under ANY complete behavioral deviation below their
first quit date. The geometric tail kills the bounded supersolution
remainder and gives a deviation-uniform expected-time bound Ctime.
The prior direct proof therefore gives terminal error e_n, delivery
error at most 2*M*Ctime/N, and finite-horizon regret at most
e_n+4*M*Ctime/N. Fix refinement first, then one threshold for all
larger N. The target is fixed before accuracy, and no bounded-memory,
fixed-date, or finite-period deviation restriction appears.

### Independent exact adversarial fixtures

I constructed a rational test combining signed Q, raw-cap equality,
and a vanishing leading quadratic coefficient. Take

    a=b=c=2, (h1,h2,h3)=(5/9,1,1), U=V=2,
    y=1/4, Q=-2, J=17/7.

Then nu=(55,59,47)/63 and J+nu3*Q=nu2. The quadratic has
alpha=0, beta=25/4, gamma=-7/8. Its rates and values are

    k=7/50, x=7/57, z=13/50, w=10/37, R=-19/50,
    Rlow=-67/47 < R < T=1/4,
    V_A=(1,10/27,0,0),
    V_B=(73/50,0,13/25,7/50),
    V_C=(47/37,0,0,20/37).

Set r1(01)=r1(013)=17/7, r1(13)=-2 and the player2 caps
to zero. Exact rational arithmetic checks all twelve policy and all
twelve Continue identities. The joint-row outsider1 Quit payoff is
-8/57, below 10/27; outsider2 is indifferent. Assigning large positive
omitted pair rewards, including pivot join rewards 10 and 11 and
player2's pair12 reward 8, produces large unrefined solo-stage gains.
The advertised C_join bound includes them: unspecified entries were
not silently assumed nonpositive.

For the author's beta=0 example, I independently checked the square-root
identities and all twelve endpoint comparisons in its complete table.
Every unrefined Quit excess is nonpositive. This verifies the alternative-
pair exact Nash profile without using the separate architecture theorem.

After the specified full-core additions, the complete trap list is
01,12,012,013,123,0123. The greatest core is all four players;
traps01 and12 force common player1, who strictly joins0 because
r1(01)=1>r1(0)=-1. Thus the signed common-leaver theorem does
not cover this fixture. The old positive-joint-pair raw class fails
its low-passive-reward condition and the raised outsider caps. Among
singleton triples, only 123 has nonnegative inverse, and its outside
weights are (-1/7,5/7,3/7); every other triple has a negative
inverse entry. These are bounded named-source comparisons, not a
claim that every possible conditional consumer has been excluded.

No unresolved mathematical objection remains within this scope. The
raw weighted buffer and changed pivot equation are actual production
steps, not supplied solution objects. The preceding architecture
positive-gap result remains outside this PASS.

## Independent review: two outsider buffers and the literal zero boundary

**Verdict: PASS as ordinary mathematics, not Lean-checked.** I checked
the final section “Two outsider buffers from a repeated solo exit” at
whole-notebook SHA256
`e550c92c806d934b2f2e94d4cbe79d47cdc81210a045a231525a644c73c133be`.
This is a delta audit of the new four-phase producer, its widened raw
caps, and its direct inclusion of the reviewed switched-pair theorem.
Unchanged original-table degree and inverse exits and the full behavioral
compiler are covered by my preceding review. No other review of this
extension was read first. The separate architecture-gap claim is still
outside this verdict.

The hypotheses checked include the existence of a finite auxiliary raw
parameter theta with 0<=theta<nu2/h1, the literal bound
xi>=theta*(1-Rlow), and BOTH weighted inequalities (72), allowing
signed Q1 and Q2. Theta is selected through finite inequalities in
the reward entries; no rate, continuation value, or solution branch is
being supplied as an extra assumption.

### Monotone balance and endpoint control

On the stated cap interval, z strictly increases with k, A1 strictly
decreases, and therefore d1 and w strictly decrease. Since 0<=z<=1,

    partial_k G=h3+(1+c*w)*partial_k z
                   -c*(1-z)*partial_k w > h3.

The upper cap is positive throughout the closed y interval except
for its intended zero at y=0. The exact clearance identity
b*Ltheta-D*(b+1+theta)=(1+theta)*(ab+b+1) checks. Clearing
the k=0 denominators gives the sign of -D+Ltheta*y as claimed.
At the A1=0 cap, w<=a*theta*y and
z>=[1+theta+a*h2/h1]*y/b imply precisely

    G >= y*D*(nu2-h1*theta)/(b*h1) > 0.

At the other cap z=1, G>0 is immediate. Thus the admissible root is
unique and strictly interior. Strict monotonicity and joint continuity
give interior continuity and the zero endpoint at Ytheta. At zero,
k/y is bounded by a/h1. Every subsequential limit solves the same
linear equation with coefficient h3+h2/b+c*h1=D*nu3/b>0,
so the three ratio limits (74) are justified without differentiating
the root branch.

The global test k0=(1+theta)*y/nu3 is valid both outside and
inside the cap. Inside, the displayed rational numerator and denominator
of w0 are exact. Its first-order comparison coefficient, multiplied by
nu3, is

    nu2*(nu2+1)+theta*(nu2*nu3+nu2^2-h1) > nu2^2,

using theta*h1<nu2. The remaining quadratic coefficient is
nonnegative, not necessarily positive; it vanishes at theta=0.
This is enough for the strict w0 upper bound. The z0 lower bound
is also strict, giving G(k0)>0 and hence the global estimate (75).
No unproved quadratic branch convention or monotonicity of the pivot
selector is needed.

### Both signed weighted caps and the pivot floor

For outsider1, the first raw cap is exactly

    a-Q1 >= (1+theta)*(h1+J1)/nu3.

Combining it with (75) proves strict safety because h1+J1>0.
For outsider2, J2>=0 gives
k*J2+y*Q2<=theta*y; division by 1+k yields the advertised
bound theta*y/(1+k)<=theta*y. It is strict when theta>0,
including the case J2=0. At theta=0 the weak zero bound is the
correct conclusion. Both arguments retain negative Q_i exactly and
do not replace them by positive parts. The endpoints exhaust all
possible unilateral outsiders at the joint03 row.

I independently expanded the upper-endpoint selector and obtained
zero residual for the exact identity

    R(Ytheta)-T=D*[xi-theta*(1-T)]/(abc+theta).

The small-y ratios give R(0)=Rlow. Since the nonempty middle
interval has Rlow<T, the raw xi bound gives R(Ytheta)>=T,
strictly so for theta>0. Thus the intermediate value theorem covers
the full missing R interval; the previously checked original-matrix
exits cover both equalities and all exterior R.

The final-phase pivot value is exactly

    P_D=1+y*[xi+theta*(R-1)]/(1+theta*y)>=1.

This uses the selected R>Rlow and the stated RAW lower bound on xi;
it does not assume R>=1. The U,V>=1 averages then give the other
pivot floors. All nonpivot coordinates in (78) are nonnegative.

### Complete rows, the third refinement, and theta=0

I checked all four phase recurrences and supported-action equalities.
At A the actual two outsider passive averages are A1 and theta*y.
At C, player1's value is -w+(1-w)*d1=0. At D, player2's is
-t+(1-t)*theta*y=0. At B, player3's value is h3*k by G=0.
The pivot's Continue equation is exactly (76), not an independent
assertion. Every pure-Continue endpoint equals its phase value.

Refining ALL THREE solo blocks is required and is correctly done.
In particular the final solo3 block can expose the pivot's xi premium
and outsider2's Q2 premium. Its intermediate values interpolate
between V_D and V_A, whose owner3 coordinates are both zero.
Thus it preserves the singleton floors and exact Continue identities
just like the other two blocks. The new C_join includes every relevant
pair surplus for owners1,2,3. Its common error tends to zero and is
charged once by the Bellman supersolution, not repeatedly over the
unbounded number of periods.

The same opponent-clock coupling proves uniform absorption tails and
full behavioral safety. All x,y,z,w are positive even when t=0;
removing any one player's hazards still leaves positive opponent
absorption in every period. The stated m_n=1+3n is a valid upper
period length even if the empty final block is retained as all-Continue
dates. Fixing n first then the finite expected-time horizon threshold
gives the same fixed V_A at all sufficiently large horizons.

The theta=0,xi=0 inclusion is LITERAL. The old three zero caps give
J2=0 and Q2<=0, satisfying the new second inequality; the first
weighted cap and the full joint reward become exactly the old ones.
Then t=0, V_D=V_A, and deleting D recovers the old three Bellman
rows. The balance, Y, and pivot selector specialize to the old formulas.
The cap-endpoint positivity and strict k<y/nu3 estimate remain valid,
while the second outsider comparison is weak, as allowed. The upper
endpoint is exactly T and still covers every interior R. This does
not appeal to openness, a limiting UE target, or reward closure.

### Independent rational and coverage stress tests

Besides recomputing the author's exact fixture and all sixteen policy
and sixteen Continue identities, I constructed a different signed-Q
test with both raw caps binding. Take

    a=b=c=2, h1=h2=1, h3=2320/873,
    U=2, V=3, theta=1/3, xi=2,
    y=1/5, k=1/12, x=1/13, z=2/9, w=83/291, t=1/16.

It has

    nu=(7558,11899,9005)/6111,
    Rlow=-22351/9005 < R=-939/2983 < T=0,
    theta*(1-Rlow)=10452/9005 < xi,
    Q1=Q2=-1, J1=6289/2716, J2=9005/6111,
    V_A=(7/5,19/65,1/15,0),
    V_B=(5455/2983,0,4/9,580/2619),
    V_C=(5309/2983,0,0,166/291),
    V_D=(7713/5966,83/208,0,0).

Setting the appropriate two entries equal to each J_i and their third
entry to Q_i, exact arithmetic verifies all sixteen policy and all
sixteen Continue identities. The two A outsider Quit payoffs are
-1147/176540 and -28307/397215, below their positive buffers.
Large arbitrary positive unused rewards create genuine unrefined
solo-stage gains, which the expanded C_join controls.

For the author's positive-six-collision fixture, both weighted caps
bind exactly. Its two A safety margins are exactly
52581/245036 and 97953/4900720 as stated. The completed table's
trap list is 01,02,012,13,013,123,0123, with empty intersection.
Thus no designated common trap player exists, while their union is
the full four-player core. The explicit completion really does retain
all six positive collision entries. It is outside the signed common-
leaver criterion and directly extends the reviewed switched family.
No exhaustive exclusion of all other producers is inferred.

No unresolved mathematical objection remains for the reviewed extension.
The monotone selector, two raw buffer inequalities, final pivot-floor
control, and direct zero-parameter specialization all survive this audit.

## Final artifact check: two buffers with a repeated solo exit

**Artifact PASS.** The preceding mathematical PASS applies to the full
632-line standalone
[`TWO_OUTSIDER_BUFFERS_WITH_A_REPEATED_SOLO_EXIT.md`](../exports/TWO_OUTSIDER_BUFFERS_WITH_A_REPEATED_SOLO_EXIT.md),
SHA256 `93a87ad51034af3d1adae77c44cc17a71e1f96bbd13aee7b2a5fd677f735d62e`.
I read the complete artifact and recomputed its hash. This is a narrow
assembly/delta check, not another full theorem audit or a Lean check.

The strongest raw hypotheses (including auxiliary theta, signed Q_i,
and both weak weighted caps) are preserved. The complete original-table
degree-zero, homogeneous, and weak passive-inverse exits retain all
their exact hypotheses and both endpoint equalities. The monotone
selector, strict global k/y estimate, selected pivot floor, four
phase vectors, all-three-block refinement, and direct all-horizon
deviation bound are unchanged. The standalone explicitly fixes y
before accuracy and uses the same V_A throughout refinement.

The added theta=0 quadratic subsection has the correct relabeled
coefficients, simple admissible branch, and alpha=0 formula. The
direct theta=xi=0 inclusion needs neither reward closure nor openness.
The refined full-core example correctly avoids asserting exact Nash
for its coarse profile after the pair12 and pair13 rewards are raised.

I independently checked the additional binding-pivot-floor fixture:
its nu, Rlow, xi=theta*(1-Rlow), balance equation, pivot equation,
and both binding raw caps hold exactly. The two displayed joint
safety margins are correct, and

    P_D-1=3839461/69777061,
    final coarse pivot Quit gain=197565595/1535095342>0.

Thus that example genuinely needs the final solo3 refinement. The
new zero-phase signed second-cap test also checks exactly:
J2=1,Q2=-315/383 gives joint Quit endpoint -809/8426<0.
The other assembled rational tests match the preceding independently
checked fixtures and preserve arbitrary-unused-reward scope.

All strategic input dependencies are named repository declarations;
there are no notebook, feedback, or math-directory dependencies and
no embedded review history. The concise Lean handoff supplies the
raw predicate, continuous selector, exact phase data, refined profiles,
and original-table outer exits, rather than hiding any of them as
extra hypotheses. No unresolved mathematical assembly objection
remains for these exact bytes.
