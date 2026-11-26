# Independent whole-proof review of opposed-pair repair

Reviewer: NEVER_DOMAIN_REVIEW.

**Verdict: PASS, with no unresolved mathematical objection.** I read and
independently checked the entire 666-line packet, including the raw producer,
repair path, other support cases, closed-domain consumer, examples, and
fixed original-payoff conclusion. This is ordinary mathematical review,
not Lean certification and not a proof of arbitrary Fin4.

Reviewed export:
`math/exports/QUIET_FACE_OPPOSED_PAIR_UNIFORM_EQUILIBRIUM.md`, SHA-256

    8fc808db2c7a6e06439719b0d36d71a1002c30d12c2244a78a0d7486c2c7966c

Reviewed retained checker:
`math/experiments/CODEX_COORDINATOR__QUIET_FACE_COVERAGE_CHECK.py`, SHA-256

    0bfda0fb7355c124e40a30484efb733ce37a59a0af7af252383b174a63298c59

Approval is limited to those exact bytes. Replacement raw hypotheses or
repair sections require further review; they do not inherit this approval.

## 1. Raw hypotheses really produce the root repair

Conditioning on owner 0's first action and the other active owner's action
gives the two exact variable-increment identities and the quiet-owner upper
bound in (J-gap). Only the stated increments with q3=0 enter. No equality
between d0,d1 or between e0,e1 is assumed, and no additional joining
conditions for owners 1 and 2 when owner 3 quits are needed. The four
increments, L1, and W are computed from finite raw data. For fixed table
data, the four quiet bounds and eight convexity tests are affine in f;
the positive-part endpoint condition is exactly the conjunction of its
two affine inequalities at v2=0,W. Thus the asserted fourteen closed
half-line tests, including constant and degenerate cases, are correct.
They introduce no strategic feasibility premise.

A bad pair12 forces v1<0 and v2>0. Its odds are exactly v2/c and -v1/s.
Consequently the displayed rational path begins at that same pair. Both
denominators are affine in alpha. Their endpoint values are strictly
positive: D1(tau)=d0*tau-v1>0 even when d0=0, and
D2(tau)>=v2+e0*tau>0. The hazards are positive, and the exact formulas
for 1-b and 1-y keep them proper before tau. Owner 2 becomes sure at tau;
owner 1 is at most sure there by e1*tau<=c. Substitution into the two
full gaps makes both identically zero, including the endpoint.

I independently expanded the cubic quiet-owner numerator. Its half second
derivative is exactly the expression in Section 3. The potentially
unbounded v3 is handled correctly: at the initial pair, the quiet threshold
is 12x1+(-101+7x1)x2<60 because x1<=5 and x2>0. Both v3 and 60 lie above
that threshold. Thus replacing v3 by min(v3,60) preserves the initial weak
comparison. On the whole path the coefficient multiplying -v3 is
nonnegative, so the clipped numerator bounds the actual one from above.
The difference between its half second derivative and the displayed raw
corner expression is (60-v3hat)*e1*d1>=0. That raw expression is jointly
affine in v1,v2,alpha, so its eight corner inequalities imply nonnegativity
on the entire required box. The cubic is therefore convex. This covers
zero e increments, weak corners, arbitrary signs of the increment
differences and f, and arbitrarily large finite passive row3 rewards.

At tau, the continuation term vanishes. The remaining factorization is
exactly (End), with positive factor d0*tau-v1 and the additional term
f*tau^2*Delta_e included. Using 0<v2<=W and the positive-part bound on
7-f*tau gives a nonpositive endpoint exactly from (E). Convexity then
preserves the quiet comparison throughout, including all equality cases.
Only the auxiliary estimate is clipped; every actual root comparison uses v.

Owner 0's gap starts strictly negative. At tau, owner 2 is sure, so the
continuation term disappears and the gap is the stated convex combination
of the two raw joining gains. It is nonnegative. Continuity supplies a
zero at a strictly positive path parameter, possibly tau itself. The two
other active comparisons remain equalities and owner 3 remains quiet.
The repaired root is thus whole-game Nash, and owner 0's output is its
nonpositive Quit offer. Neither actual realizability of v nor full cap
information was assumed in this construction.

## 2. Support exhaustion and the whole cylinder

The participant caps rule out active owner 0 at a bad proper root. Native
own rewards rule out singleton supports; the core pair rewards rule out
pairs13 and23. A bad pair12 is handled by the preceding repair, so only
a bad triple can remain if one assumes there is no good root.

For that triple, I checked the odds equations, the bound x1<W/c<=5, and
the strict inequality v3>x1(190+58x1)/(100-x1)>0. The estimates
x2<10/11, B>95, C>=2, F>66, D<19 and E<19 imply the claimed positive
determinant. Solving two equations leaves a single feasible interval;
the first equation has derivative det(Dphi)/(D*F)>0 there. Thus at most
one bad triple exists. Inactive owner 0 is strictly quiet, giving the
negative ambient index. Total clipped-map degree is +1 on the stated
ambient box. This contradicts the all-bad alternative without requiring
genericity or inactive strictness for the repaired pair.

For the whole-cylinder corollary, W<=10 and p>=0 imply W/c<=5. When a<=0,
neither pair12 nor the triple can have positive owner1 output. When a>=1/2,
the triple determinant only improves. At a>1/2 a bad pair is unique with
negative index after avoiding its single inactive3 tie; at a=1/2 it is
removed by perturbing v1 off zero. The fixed singleton signs permit the
required relative perturbations inside the closed passive intervals,
even at boundary inputs, while retaining a strictly negative minimum.
Closedness of the Nash and good-root graphs removes the perturbation.
The constant-increment specialization gives eight identical expressions
36de>=0, and its endpoint test is the stated scalar test. The unit-gap
endpoint estimate in the opposed strip is also correct.
Together these arguments cover every real a and every p>=0, under the
corollary's explicit completion restrictions.

## 3. Full behavioral consumer and the fixed target

The first-Quit-law representation includes every complete behavioral
replacement, all finite deadlines, and literal Never. The max recurrence
for B is therefore a complete response cap, not a restricted response
menu. I checked the residual identity in (C); all three residual terms
are nonnegative. At positive joint survival, zero debt forces U=B=e in
the literal passive box. Intermediate prescribed payoffs need only the
full finite reward bound, which is what the proof uses.

The local induction relies on closedness of the good-root correspondence,
not smallness of every nearby root. In the kernel case, the core linear
passive drift vanishes, leaving O(epsilon^2) drift per prefix and O(epsilon)
full cap errors over the fixed total hazard. Positive outsiders keep their
Continue buffers. In the separator case, the solo-column seed lies in the
closed domain and has a zero coordinate. Its initialized cap is explicitly
virtual; no actual solo-prefix cap equality is asserted.

The survival budget and displacement constants provide the strict slack
needed to prefix a good root at a minimizing fiber. If only AllContinue
remains good, the positive signed value forces a strictly smaller zero set.
The recursive words preserve the original signed inequality because their
supports remain inside the original zero set. Continuity and the strict
survival slack place their limiting endpoint in the original minimizing
closure. Original Never masses are retained; they are not reset at a
conditional tail. Length-independent cap nonexpansiveness removes the seed.

The actual carrier is used through its compact closure, which is preserved
by finite prefixes. Moving a smallest Never mass changes four prescribed
payoffs and three other caps by at most 2M times that mass each, while the
moved owner's cap is unchanged. This proves the 14M repair bound on the
carrier and its closure. A positive absorbing debt infimum would force a
positive minimum of the original Never product on the zero-debt marked
fiber. Both a nonzero good root and the local escape contradict that same
minimum. No finite-calendar realization of the caps is used.

For nonnegative original own levels, absorption gives the prescribed profile
the full own shift, whereas a complete deviation receives at most that shift.
Original regret is therefore bounded by native regret. I inspected the
declarations of `quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
and `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in the source files named in Section 8. Their scopes agree with the stated
cap update and fixed-target handoff. Terminal approximate equilibrium at
every error suffices for one original payoff target fixed before accuracy.
The packet does not claim the new adapter or producer has been checked in Lean.

**Unproduced strategic inputs: none.** In particular no root, continuation,
strategy, public correlation device, punishment, finite calendar, or
equilibrium appears as a premise of the raw theorem.

## 4. Exact examples, weak boundaries, and coverage scope

I independently parsed all sixty table entries from the packet and checked
their equality with the retained checker's literal table. The values
W=5, d0=d1=e0=e1=f=1, eight corner values 36, the two owner0 gains
9/10 and 11, and endpoint value -243 are correct. I also recomputed the full-marked output and both quiet Quit
offers as polynomials in epsilon. The listed safe-edge graph is strongly
connected and supports the fourteen proper-marked controls. These inputs
lie in the passive box for sufficiently small positive epsilon; they
refute universal marked invariance rather than selected return.

For the one-entry perturbation Z1(012)=601/100, I independently checked
d1=101/100, tau=25/101, and the two pairs of corner/endpoint values:
3531/100 and -24568/101 at f=1; 7059/200 and -24468/101 at f=1/2.
At f=1/2 every nontrivial raw guard is strict. Finite minima/maxima are
continuous and d1 remains positive, so the claimed neighborhood in the
independent completion coordinates is justified. The numerical core stays
fixed; this is not an unrestricted sixty-coordinate neighborhood claim.

The e0=e1=0,f=-1 modification retains W=5, has passive row3 maximum 1000,
and has endpoint value -266. All four modified owner3 increments and the
two relevant owner2 increments have the required values. The weak variant
has e0=e1=12,f=28, zero owner0 joining gains, e1*tau=c, endpoint value zero,
and eight corner values 432.
As an additional exact boundary check, q=(1/5,1,1,0) has all four gaps
zero in that variant and output (-12,7/5,-18/5,-5), confirming that a sure
endpoint is fully legitimate.

The separate census review covers all 80 absorbing stationary support
patterns and all 65 sure-first patterns with arbitrary punishment tails
for the literal original own levels one. It also covers the checker's
constant and unequal-increment symbolic repair identities. The final
267-line checker retains the previous census as an exact byte prefix,
does not mutate its literal table in the perturbation test, and was rerun
successfully through its final assertion.
This whole-proof review does not independently recertify every appended
legacy selector's interpretation against its separate producer theorem;
that broader coverage requires its own coverage audit. None of those
exclusions is needed for the UE proof. They must not be read as an
unrestricted behavioral exploitability gap or as arbitrary Fin4 closure.
