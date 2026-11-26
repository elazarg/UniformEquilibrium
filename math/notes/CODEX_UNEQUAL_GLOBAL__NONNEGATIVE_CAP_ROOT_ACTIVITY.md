# A nonnegative cap region invariant under every exact Nash root

**Owner: CODEX_UNEQUAL_GLOBAL. Proved ordinary mathematics; independently
[reviewed](../feedback/CODEX_UNEQUAL_GLOBAL__NONNEGATIVE_CAP_ROOT_ACTIVITY__BY_CODEX_ACTUAL_MINIMUM_ATTACK.md).**
Not Lean checked. This is a full exact-Nash-root classification and
invariance theorem for one raw family, not a Fin4 closure.

Use the calibration singleton matrix

    Gamma=[0,3,-1,3;2,0,1,-3;2,-2,0,-1;-1,-2,1,0],

Native own singletons satisfy Z_i({i})=0. Every passive native reward
Z_i(A), i not in A, equals sum_(j in A) Gamma_ij. Every proper nonsingleton participant reward in
rows0,1,2,3 is respectively e,h1,e,h3. The grand native row is
(10,-2,-e,-1). These rules specify all sixty rewards. Original nonempty
rewards are1+Z, and
original live/Never reward is zero. All annotations C,W below are native:
root Nash for Z against C means root Nash for1+Z against1+C.

**Theorem.** There is epsilon0>0 such that for every independent choice
0<e,h1,h3<epsilon0, every full exact Nash root against

    C_i>=0 for all i, C2<=2                         (D)

has nonnegative output W with W2<=2. If player0 acts, its support is
exactly{0} and C0=W0=0. No output nonnegativity is assumed.

Write q=(x,y,z,w), H_i=product_(j!=i)(1-q_j), D_i=1-H_i. Quit and
Continue endpoints are

    Q0=eD0+(10-e)yzw,
    Q1=h1D1-(2+h1)xzw,
    Q2=eD2-2exyw,
    Q3=h3D3-(1+h3)xyz,
    K_i=(Gamma q)_i+H_i C_i.

An active owner has Q_i>=K_i, and equality holds if its hazard is below1.

## A polynomial certificate for the limiting mixed branch

Suppose a sequence of fully mixed roots has premiums tending to zero.
After a subsequence the hazards converge to q in[0,1]^4. Input
nonnegativity and the mixed player2 equation with C2<=2 imply

    z+2x(1+zw)<=3w,
    z<=x+2y,
    2y+w-2x<=2(1-x)(1-y)(1-w),
    F=10yzw-3y+z-3w>=0.                            (1)

The second inequality only uses the weaker Q3<=0, and no output sign
has been used. These inequalities force q=0, as follows.

Put

    U=(3w-z)/(2(1+zw)),
    A=-3w^2 z+3w^2+wz-3w+2,
    D=-2w^2 z+3w^2+3wz-5w+z+4,
    B=3z-3w+2z^2 w, L=10zw-3.

The first inequality in(1) gives x<=U and z<=3w. Both the second
inequality's slack x+2y-z and the third inequality's slack increase in x.
Replacing x by U therefore gives

    y>=B/[4(1+zw)], y<=A/D.                        (2)

Here D>0: its z-independent part is
3(w-5/6)^2+23/12, and its z coefficient is1+w(3-2w)>=1.

If L<=0, then F=yL+z-3w>=0 forces z=3w and yL=0; also x=0.
If w=0, the other inequalities force y=z=0. If w>0, then y>=3w/2>0,
so L=0. But the third inequality gives 9w-3w^2<=2, hence w<1/4,
whereas L=0 and z=3w require w^2=1/10. This is impossible.

Thus any nonzero solution would have L>0. Define

    R=L A-(3w-z)D,
    S=4(1+zw)A-B D.

Equations(1),(2) imply R>=0 and S>=0. There is, however, the exact
polynomial certificate

    P=-R-S/3>=5/9 on[0,1]^2.                       (3)

Here is reproducible rational arithmetic for(3). P has bidegree(3,3).
On the four squares [i/2,(i+1)/2] times[j/2,(j+1)/2], its minimum
Bernstein coefficients, in order(i,j)=(0,0),(0,1),(1,0),(1,1), are

    313/144, 5/9, 2, 55/36.

To check them, substitute w=(i+s)/2,z=(j+t)/2, expand as
sum a_pq s^p t^q, and form the sixteen coefficients

    b_kl=sum_(p<=k,q<=l) a_pq
       *binom(k,p)/binom(3,p)*binom(l,q)/binom(3,q).

Bernstein basis weights are nonnegative and sum to one, so these minima
prove(3). For an expanded polynomial check, 3P equals

    -4w^3z^3+108w^3z^2-114w^3z+18w^3
     +6w^2z^3-44w^2z^2+105w^2z-15w^2
     +2wz^3+8wz^2-57wz+9w+10.

This contradicts R,S>=0. Hence every limiting hazard vector is zero.

For small roots use k=(9,7,0,8), with k Gamma=(6,11,6,6).
Since Gamma q<=Q, putting s=x+y+z+w gives

    6s<=kQ<=(9e+7h1+8h3)s+90yzw
       <=24 max(e,h1,h3)s+(10/3)s^3.

This is impossible for nonzero s<=1/2 and max(e,h1,h3)<=1/8.
Compactness therefore supplies one positive threshold excluding every
fully mixed root against(D), uniformly over independent premium ratios.

## Sure hazards also disappear uniformly

This section treats the remaining FULL-SUPPORT roots with at least one
sure hazard. All four hazards are positive; proper supports are handled
separately below. The check uses no output sign and no additional upper
bound on C. Terms involving a sure
opponent have H_i=0. Write g_i=Q_i-(Gamma q)_i.

If x=1, then g3>=y+h3(1-y)>0, so w=1. The case z=1 is rejected by
g1=-2. Otherwise player2 is mixed and g2=(1-e)(2y-1)=0, giving y=1/2.
Then z=(1+h1)/(3+h1), and owner0's gap is at most
e-9/2+(6-e/2)z<0 for small premiums. Thus x=1 is impossible.

If y=1, then
g2=2(1-x)+e+w(1-2ex)>0 for e<1/2, forcing z=1. Next
g3=1+h3(1-x)>0 forces w=1 and g0=5 forces x=1, already excluded.

It remains to take x,y<1. If z=w=1, the two free equations give
x=(2+h1)/(4+h1), y=(2-e)/(7-e). As premiums vanish, the sure owner's
gap g3 tends to -1/14, hence is negative for sufficiently small premiums.

If z=1 alone, owners0,1,3 are mixed. Their free equations give

    w=(2x+1-h1)/(3-(2+h1)x),
    y=(1-h3-x)/(2-(1+h3)x),

and w<1 implies x<(2+h1)/(4+h1). Along any sequence with premiums
tending to zero, the limiting x lies in[0,1/2], and the limiting g0,
after multiplication by the positive denominator(3-2x)(2-x), equals

    -18x^2+9x+1>=1.

It cannot vanish. Compactness makes this a uniform exclusion.

If w=1 alone, the free equations give

    y=(2x-1-e)/(2(1-ex)),
    z=(3+h1-2x)/(1+(2+h1)x).

The limiting x belongs to[1/2,1]. The limiting g0, multiplied by
1+2x, equals -(52x^2-64x+27)/2<0; its quadratic has negative
discriminant. This is again a uniform contradiction. All sure faces
have now been exhausted.

## Proper supports and output invariance

The proper-support check needs only premiums<=1/10. Supports01,02,03
force respectively h1>=2,e>=2,e>=3. Support012 has
2x+z<=h1(x+z), impossible. Support013 has
3y+3w<=e(y+w-yw), impossible. For023 the active inequalities imply

    z>=(29/11)w, w>=(19/11)x, x>=(9/11)z,

whose product is greater than1. Hence every proper support containing0
is{0}. That support forces C0=W0=0.

When q0=0, every forced-Quit endpoint is nonnegative: the negative
grand terms of Q1,Q2,Q3 vanish, and Q0 is also nonnegative. A full Nash
root therefore has W_i=max(Q_i,K_i)>=0. The solo0 case has the same
property because all queried participant rewards are nonnegative.
Player2's every terminal native reward is at most2, and C2<=2, so both
its Quit and Continue endpoints are at most2. Consequently W2<=2.
This proves invariance of(D) and the activity theorem.

## Source compatibility and limits

Every native absorbing reward of player2 is at most2; its original Never
payoff minus own level is -1. Actual native full caps, and their limits,
therefore satisfy C2<=2. The theorem applies to any full exact Nash prefix
whose input annotations are nonnegative. It proves their output remains
in the same region and supplies the stated restriction on player0.

The [canonical boundary-head reduction](CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION.md)
DOES NOT supply full root Nash: it supplies exact observer optimality,
while the pivot may have positive root regret R0. Its finite intermediate
caps can also be negative. Even eventual input nonnegativity would not
repair the missing pivot optimality. In particular the present theorem
does not show that0 has finite support in a canonical incoming head, and
does not exclude an all-zero boundary endpoint or a Never-penalty plateau.
Those would require a new source argument. The result is a restriction
on full exact-Nash-root architectures; it does not narrow the surviving
arbitrary-behavior counterexamples or close the actual-minimum branch.

There is an exact control showing why pivot optimality matters. For
0<e,h1,h3<1/10, take q=(1/10,0,0,1/10) and continuation
C=(0,1,1,(1+h3)/9). Owners1,2 Continue strictly and owner3 is indifferent.
The full cap output and prescribed output are

    B=(3/10,71/100,91/100,h3/10),
    U=(27/100+e/100,71/100,91/100,h3/10).

All input and output caps are nonnegative and C2<=2, but0 and3 both act.
The pivot's root regret is3/100-e/100>0. This exactly falsifies extension
of the activity theorem to observer-Nash roots. No actual ancestral-tail
realization of this displayed C is claimed. This control was supplied and
independently checked by CODEX_ACTUAL_MINIMUM_ATTACK.

The upper cap bound C2<=2 is also substantive. For every nonnegative
choice of premiums, q=(2/5,9/10,9/10,9/10) has strictly positive endpoint
gaps Q-Gamma q, so it is a mixed Nash root against the positive
continuation C_i=(Q_i-(Gamma q)_i)/H_i. Its C2=(950+173e)/3 is outside
the stated domain. Thus nonnegative input alone would not imply the theorem.

The current hard test is e=beta,h1=beta/10,h3=beta. A useful next question
is to consume the actual global source's debt-paying partial-Nash roots,
rather than assume they satisfy the full optimality used here.

Relevant Lean sources inspected: `quittingUniformEquilibriumPayoffConjecture`
(`UniformEquilibrium/Quitting/Conjecture/Basic.lean`),
`quittingRoot_activeHazards_lt_one_of_leave_sums`
(`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`),
and `exactRootSuccessor_active_eq_singleton_of_support_not_premiumTrap`
(`UniformEquilibrium/Quitting/Classification/QuittingPremiumCoreExactRoot.lean`).
The generic hypotheses of the latter two are not asserted for this family.
