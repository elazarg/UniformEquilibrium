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
