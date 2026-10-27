# A raw observer orthant attractor with arbitrary higher rewards

Owner: CODEX_COORDINATOR. Ordinary mathematics. This is a local observer
producer, not a four-player uniform-equilibrium theorem. The final corollary
prices an arbitrary fourth player in a sufficiently thin neighborhood of a
positive pivot axis. Producing such an entry and a recurrent return family
remains a separate obligation.

There are three observers, ordered (0,1,3), with independent private
Continue/Quit choices and native own-singleton and Never rewards zero.
Their passive singleton matrix and participant-pair joining matrix are

 G=[0,-g,h; -i,0,j; k,-l,0],
 L=[0,-A,-B; C,0,-D; -E,F,0],

where all twelve displayed lowercase/uppercase parameters are positive.
The participant-pair matrix is J=L+G. The passive reward of observer r
when both other observers quit is p_r, and the reward when all three quit
is K_r. All six numbers p_r,K_r are arbitrary finite real numbers. Put
r_r=p_r-K_r; these joining-penalty coefficients may have either sign.

Assume the strict raw inequalities

 J03=h-B<0, J10=C-i>0, J13=j-D<0,
 J30=k-E<0, J31=F-l>0,
 eta1=j*C-i*D>0, eta3=k*F-l*E>0.

Assume G is invertible and d=-1^T G^-1 has signs(-,+,+). These hypotheses
concern only singleton and participant-pair rewards. They impose no sign or
magnitude condition on the six higher rewards p_r,K_r.

The inverse-sign condition is exactly the raw singleton inequality

    D0=h*i*l-g*j*k>0.

Indeed det G=D0 and, writing d=(-alpha,beta,gamma), direct multiplication gives

    gamma=(g*i+h*i+g*j)/D0,
    alpha=(l*gamma-1)/g, beta=(1+k*gamma)/i.

If D0>0, gamma and beta are positive. The numerator of alpha before
cancelling g is g*(i*l+j*l+j*k)>0. Conversely gamma>0 forces D0>0.
Thus this condition covers the entire displayed strict singleton sign
chamber with positive determinant. The joining inequalities remain
additional raw restrictions.

**Theorem.** There is a produced epsilon>0 such that, for every diagonal
observer annotation v=(-S,u,w) with S>0, u,w>=0 and

 V=d*v=(-d0)S+d1*u+d3*w<=epsilon,

one can prepend a sequence of proper observer Nash roots supported on01
or013 whose total odds are summable and whose diagonal observer annotations
tend to zero. Every selected root is produced by a monotone scalar equation
or an explicit face formula. Every output belongs to the closure of finite
proxy words with the fixed initial seed. The result does not assert that
the seed is an actual continuation or execute anything after an infinite
number of dates.

## Explicit smallness choices

Set m=min(-d0,d1,d3)>0 and

 mu=(l/F+k/E)/2,
 b_t=mu*F-l=eta3/(2E)>0,
 b_a=k-mu*E=eta3/(2F)>0.

The pair assumptions imply 0<mu<1. Choose delta in(0,1] satisfying

 |r0|*delta<=B/2,
 |r1|*delta<=min(C,D)/2,
 |r3|*delta<=E/2,
 |K0|*delta<=min(-J01,-J03),
 |K1|*delta<=J10/2,
 |D*p1-j*r1|*delta<=eta1/2,
 |p3-mu*r3|*delta<=min(b_t,b_a),
 delta*sum_r |d_r*p_r|<=1.

Here J01=-A-g<0. Every right side is strictly positive, so these finitely
many upper bounds produce such a delta even when some left coefficient
vanishes. For example take the minimum of1 and all positive right-side
bounds divided by1 plus the corresponding absolute coefficient.

Choose

 epsilon=(m*delta/2)*min(A,B/2,A*E/(2F),C)>0.

All choices depend only on the finite raw rewards, before the seed is given.

## Root formulas and selection

For odds x=(a,t,z), opponent survival H_r=prod_(s!=r)(1+x_s)^-1, and
joining offers are

 Ccap0=-A*t-B*z-r0*t*z,
 Ccap1=(C-r1*z)*a-D*z,
 Ccap3=F*t-(E+r3*t)*a.

A root is Nash against diagonal v when Ccap_r<=v_r for every observer,
with equality at positive odds. Its diagonal output is

 v'_r=H_r[v_r+G_r*x+p_r*prod_(s!=r)x_s].             (1)

Put t0=S/A and a0=u/C. If

 F*t0-(E+r3*t0)*a0<=w,

choose the face root(a0,t0,0). Its first two comparisons are equalities,
and the third is the displayed quiet comparison. Allow a0=0 when u=0.

Otherwise the strict reverse inequality implies w/F<t0, since
E+r3*t0>=E/2>0. For t in[w/F,S/A], put

 z(t)=(S-A*t)/(B+r0*t),
 a(t)=(F*t-w)/(E+r3*t),
 f(t)=(C-r1*z(t))*a(t)-D*z(t)-u.

The smallness choices give, throughout this entire interval,

 0<=t<=epsilon/(m*A)<=delta,
 0<=z<=2epsilon/(m*B)<=delta,
 0<=a<=2F*epsilon/(m*A*E)<=delta.

The denominators are positive. Since S<=A*delta and w<=F*delta,

 z'(t)=-(A*B+r0*S)/(B+r0*t)^2<0,
 a'(t)=(F*E+r3*w)/(E+r3*t)^2>0.

Indeed their signed numerators are bounded below by AB/2 and FE/2.
Also C-r1*z>=C/2 and D+r1*a>=D/2. Therefore

 f'=(C-r1*z)*a'-(D+r1*a)*z'>0.

At the left endpoint f=-D*z-u<0, because z>0 there. At the right
endpoint f>0 is precisely the failed face test. There is one interior zero,
which produces a,t,z>0 and all three active equalities Ccap=v. The face
root also has all odds at most delta, since a0<=epsilon/(m*C).
Thus every selected root is proper and satisfies the full observer Nash
comparisons; no strategic root is assumed as input.

## Exact preservation of the cap signs

Write N_r=v_r+G_r*x+p_r*prod_(s!=r)x_s for the numerator in(1).
For coordinate0, substitution of Ccap0=-S gives

 N0=J01*t+J03*z+K0*t*z
    <=(J01*t+J03*z)/2<0.

We used tz<=delta(t+z)/2 and the chosen bound on |K0|. The strict
inequality holds because t>0, including on the face z=0.

For coordinate1, Ccap1=u holds for both selected supports. Consequently

 N1=[J10+K1*z]/[C-r1*z]*u
       +[eta1+(D*p1-j*r1)*z]/[C-r1*z]*z>=0.

Both numerator coefficients are strictly positive by the delta bounds.
This identity also covers u=0 or z=0, with no hidden division by either.

For coordinate3, w>=Ccap3 and w>=0 imply w>=mu*Ccap3, because
0<mu<1. Hence

 N3=w+k*a-l*t+p3*a*t
   >=b_t*t+b_a*a+(p3-mu*r3)*a*t
   >=(b_t*t+b_a*a)/2>0.

Again at<=delta(a+t)/2 and the chosen coefficient bound give the last
line. This covers the boundary a=0 and the quiet third observer on01.
Thus v0'<0, v1'>=0 and v3'>0 at every step.

## Lyapunov descent and summability

The vector d satisfies dG=-1^T. Formula(1) gives the exact identity

 V'-V=-sum_s x_s+sum_r d_r*p_r*prod_(s!=r)x_s
                   -sum_r d_r(1-H_r)N_r.

The last sum is nonnegative because the just-proved signs give d_r*N_r>=0.
For the middle sum, each opponent product is at most delta times half the
sum of its two factors. Thus it is bounded above by

 (delta/2)*sum_r|d_r*p_r|*sum_s x_s<=sum_s x_s/2.

It follows that

 0<=V'<=V-(a+t+z)/2.                                  (2)

Therefore all future states remain within the same smallness domain, the
root selection iterates indefinitely, and the sum of all selected odds is
at most2V_initial. In particular a_n,t_n,z_n tend to zero.

## Zero endpoint and finite-word interpretation

The first two active equalities give

 S_n=A*t_n+B*z_n+r0*t_n*z_n ->0,
 u_n=(C-r1*z_n)*a_n-D*z_n ->0.

The third observer update is

 w'=[w+k*a-l*t+p3*a*t]/[(1+a)(1+t)].

Since w<=epsilon/d3 and all odds are bounded by delta, its increment in
absolute value is at most

 [max(k,l)+|p3|*delta+epsilon/d3]*(a+t).

Summability proves that w_n converges. If its limit were positive,
eventually w_n>F*S_n/A. Since E+r3*S_n/A>0, this forces every later
selection to be the face01. There z=0, t=S/A, and the exact first-coordinate
update is

 S'=(A+g)*S/(A+S).

For every S in(0,g) this strictly increases S, contradicting a positive
sequence converging to zero. Therefore w_n->0 as well.

All marginal survivals converge to positive limits because the odds are
summable. Every finite selected word is a diagonal Nash proxy word from
the fixed seed, so its convergent payoff/cap/survival tuple belongs to the
closure of those finite words. This supplies the claimed endpoint directly.

## Local repair with an arbitrary fourth player

Extend the native table to four players with own singleton and Never rewards
zero. Keep the three-observer rewards above and let all remaining rewards be
arbitrary finite numbers. Fix 0<bmin<=bmax. Choose K>=1 bounding both the
absolute passive rewards Z_p(D) and the absolute joining increments
Z_p(D union{p})-Z_p(D), for every nonempty D contained in the observer set.
Put B=max(bmax,K). Further reduce the preceding smallness constants so that

    delta<=bmin/(48K), epsilon<=bmin/[8(K+B)].

For every diagonal four-player seed with observer part (-S,u,w) as above
and pivot coordinate beta0 in[bmin,bmax], the produced observer roots,
with the pivot always quiet, are full four-player Nash roots. Their values
converge to b'e_p, with b' in[3bmin/4,B]. This is a local repair theorem,
not a producer of the input seed or an invariant family of such entries.

To prove it, define the pivot updates passively along the already produced
observer roots, initially without assuming their pivot comparisons. Write
D=(1+a)(1+t)(1+z), H=1/D, and let P_p be its passive absorption reward.
The update beta'=H*beta+P_p is a convex combination of beta and the pivot's
passive rewards, so |beta_n|<=B throughout. Moreover

    |beta'-beta|<=(K+B)(1-H)<=(K+B)(a+t+z).

The observer theorem gives sum(a+t+z)<=2V_initial. Hence every partial
pivot drift is at most2(K+B)epsilon<=bmin/4, and beta_n>=3bmin/4.
Its full joining offer has one coefficient for each nonempty observer
coalition, each bounded in absolute value by K. Thus

    |C_p(a,t,z)|<=K(D-1)<=12K*delta<=bmin/4,

where delta<=1 and each odds coordinate is at most delta. Every pivot
comparison is therefore strict: C_p<beta_n. All four root comparisons hold,
and summability gives convergence of beta. The finite-word closure argument
now retains the complete four-player payoff/cap/survival tuple. No actual
continuation is assumed at the synthetic seed.

## Source correspondence and the remaining producer problem

The proxy identity and continuity are
quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash and
continuous_quittingTerminalSemanticPrefix in
UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean. Full response
recursion is quittingContinuationBestResponseValue_rootThenContinuation_eq_max
in UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean. These are existing
semantic interfaces; this raw construction has not been formalized in Lean.

The concrete next question is to produce a small entry from a nonnegative
four-player proxy seed and return its pivot value to a bounded admissible
family. Local repair alone does not produce a recurrent entry, a uniform
survival reduction over such a family, or uniform equilibrium.
