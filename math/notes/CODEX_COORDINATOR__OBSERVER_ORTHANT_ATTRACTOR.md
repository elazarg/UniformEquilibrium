# The sharp joining region for a local observer orthant attractor

Owner: CODEX_COORDINATOR. Ordinary mathematics. This is a local observer
producer, not a four-player uniform-equilibrium theorem. The final corollary
prices an arbitrary fourth player in a sufficiently thin neighborhood of a
positive pivot axis. The five joining inequalities below are sharp at first
order within the displayed joining sign pattern. Producing an entry and a
recurrent return family remains a separate obligation; returns confined near zero with uniformly small hazards
cannot supply vanishing survival, as shown in the
[global entry analysis](CODEX_COORDINATOR__GLOBAL_ENTRY_AND_EXCURSIONS.md).

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

 C>i, F>l,
 eta1=j*C-i*D>0, eta3=k*F-l*E>0,
 (A+g)*D*E>(h-B)*C*F.

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

 mu=(l/F+min(1,k/E))/2,
 b_t=mu*F-l>0, b_a=k-mu*E>0,
 H0=max(h-B,0), m0=A+g-H0*C*F/(D*E)>0,
 Rbar=2*F*(C+abs(r1))/(D*E),
 Q=2*F*(E*abs(r1)+C*abs(r3))/(D*E^2).

The assumptions F>l and eta3>0 imply 0<mu<1 and both b coefficients
are positive. The final joining inequality is equivalent to m0>0.
Choose delta in(0,1] satisfying

 |r0|*delta<=B/2,
 |r1|*delta<=min(C,D)/2,
 |r3|*delta<=E/2,
 |K1|*delta<=(C-i)/2,
 |D*p1-j*r1|*delta<=eta1/2,
 |p3-mu*r3|*delta<=min(b_t,b_a),
 delta*(H0*Q+abs(K0)*Rbar)<=m0/2,
 delta*sum_r |d_r*p_r|<=1.

Every right side is strictly positive, so these finitely
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

 N0=-(A+g)*t+(h-B)*z+K0*t*z.

The face has z=0. On full support, u,w>=0 imply

 D*z<=(C+abs(r1)*delta)*a,
 (E-abs(r3)*delta)*a<=F*t.

Consequently z/t<=R_delta, where

 R_delta=F*(C+abs(r1)*delta)/[D*(E-abs(r3)*delta)],
 R_delta<=Rbar, R_delta-C*F/(D*E)<=Q*delta.

The last bound follows by subtracting the two fractions and using
E-abs(r3)*delta>=E/2. For either support,

 N0/t<=-(A+g)+H0*R_delta+abs(K0)*delta*R_delta
      <=-m0+delta*(H0*Q+abs(K0)*Rbar)<=-m0/2<0.

Thus coordinate0 stays strictly negative, even when its participant reward
J03=h-B is positive.

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

## Maximal first-order region and exact failures

Within the fixed six joining-increment signs, the closed first-order
orthant-invariance region is exactly

 C>=i, F>=l, j*C>=i*D, k*F>=l*E,
 (A+g)*D*E>=(h-B)*C*F.

The strict hypotheses used above are its interior. If any weak inequality
is strictly violated, there are interior seeds (-S,u,w), S,u,w>0,
arbitrarily close to zero, whose unique sufficiently small proper Nash root
leaves the orthant. This persists for every fixed finite choice of the higher
rewards. Equality cases are not claimed robust under arbitrary higher rewards.

The former sufficient restrictions J03<0,J13<0,J30<0 are unnecessary.
For example, take

 (g,h,i,j,k,l)=(1,2,1,1,1,1),
 (A,B,C,D,E,F)=(16,1,2,1/2,1/2,2).

All five strict inequalities hold while J03,J13,J30 are all positive.
This is an open enlargement of the local producer, not a new UE class.

For an INTERIOR seed u,w>0, every sufficiently small proper Nash root must
have a>0: if a=0, positive t would require C1=-D*z=u>0, impossible;
therefore t=0, and positive z would require C3=0=w, also impossible.
All odds zero fail C0<=-S. Next t>0: if t=0 and z>0, active3 requires
C3=-E*a=w>0, impossible; if also z=0, C0=0 fails. Thus the only possible
supports are01 and013. On01 the active equalities determine a0,t0. On013
the monotone scalar equation determines the unique root, and it exists
exactly when the face test fails. Hence the selected small root is the only
small proper Nash root at an interior seed.

This uniqueness claim is deliberately not made on boundary seeds u*w=0;
other supports can occur there. For example u=w=0 allows a solo3 root.

### Proof of first-order necessity and sufficiency

Set all higher rewards p_r=K_r=0. The root equations are now linear.
On a full root u,w>=0 are precisely

 a<=F*t/E, z<=C*a/D, a,t,z>=0.

This cone has the three generating rays, in odds order(a,t,z),

 R1=(0,1,0), R2=(F/E,1,0), R3=(F/E,1,C*F/(D*E)).

The numerators on a full root are

 N0=-(A+g)*t+(h-B)*z,
 N1=(C-i)*a+(j-D)*z,
 N3=(F-l)*t+(k-E)*a.

On R1, N3=F-l. On R2, N1=(C-i)F/E and N3=(kF-lE)/E.
On R3, N1=(jC-iD)F/(DE) and
N0=-(A+g)+(h-B)CF/(DE). Thus the five weak inequalities are necessary and sufficient on
this cone. Face01 permits a/t beyond F/E, with w>=0, and its output has
N1=(C-i)a and N3>=max(0,Ft-Ea)+ka-lt. Splitting at a/t=F/E shows that
exactly the same three tests C>=i,F>=l,kF>=lE suffice; N0 is strictly
negative there. Hence the five weak inequalities characterize the entire selected first-order map.

A strict violation at a generating ray persists after perturbing to a,t>0,
u,w>0, keeping the relevant face or full-root formulas. Scale such a seed
and its odds by tau>0. The zero-higher reward equations remain exact, and
the failed numerator is tau times a fixed strictly wrong-signed number.
The small proper root is unique by the argument above.

For arbitrary fixed higher rewards, choose the same scaled interior seed.
The exact selected odds divided by tau converge to that unique linear root:
C0=-tau*S bounds t+z=O(tau), C1=tau*u bounds a=O(tau), and every limit
solves the unique linear complementarity equations. The quadratic higher
terms are O(tau^2), so the output divided by tau converges to the same
strictly wrong-signed numerator. This proves the sharp local obstruction.

### Five exact separating examples

Fix (g,h,i,j,k,l)=(1,2,1,1,1,1), so det G=1, and set p=K=0.
In the following rows all five strict inequalities except the named one hold strictly.
Each listed seed and odds may be multiplied by any tau>0; the same wrong
output sign remains. The seeds have S,u,w>0, so the proper root is unique.

| Failed test | (A,B,C,D,E,F) | seed(-S,u,w) | odds(a,t,z) | failed numerator |
|---|---|---|---|---|
| C>i | (1,2,1/2,1/4,1,2) | (-1,1/2,3) | (1,1,0) | N1=-1/2 |
| jC>iD | (1,2,2,3,1,2) | (-17/5,1/5,1/10) | (19/10,1,6/5) | N1=-1/2 |
| F>l | (1,2,2,1,1/4,1/2) | (-1,1/5,1/2) | (1/10,1,0) | N3=-2/5 |
| kF>lE | (1,2,2,1,3,2) | (-1,6/5,1/4) | (3/5,1,0) | N3=-3/20 |
| last inequality | (1,1/2,2,1,1,2) | (-9/4,1/2,1/2) | (3/2,1,5/2) | N0=7/4 |

These are obstructions to the local whole-orthant method, not to UE or to
all proper roots at larger annotations, and not to sure-root methods.

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
