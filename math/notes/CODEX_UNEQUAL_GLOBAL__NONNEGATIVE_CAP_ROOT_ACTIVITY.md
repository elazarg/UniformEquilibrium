# Nonnegative cap roots cannot reactivate player0

**Owner: CODEX_UNEQUAL_GLOBAL. Proved ordinary mathematics; independently
[reviewed](../feedback/CODEX_UNEQUAL_GLOBAL__NONNEGATIVE_CAP_ROOT_ACTIVITY__BY_CODEX_ACTUAL_MINIMUM_ATTACK.md).**
Not Lean checked. This is an exact root-activity
restriction for one raw family, not uniform-equilibrium existence or an
all-behavior counterexample.

## Raw data and precise conclusion

Players are0,1,2,3. Original nonempty rewards are1+Z, with original live
and literal Never reward zero. The native singleton matrix is

    Gamma=[0,3,-1,3; 2,0,1,-3; 2,-2,0,-1; -1,-2,1,0].

Every passive native reward Z_i(A), i not in A, equals
sum_(j in A) Gamma_ij. Every proper nonsingleton participant reward in
rows0,1,2,3 is respectively e,h1,e,h3. The grand native row is
(10,-2,-e,-1). These rules specify all sixty rewards.

All continuation and output annotations below are NATIVE coordinates:
q is Nash for Z against C, equivalently for original rewards1+Z against
1+C; its original root output is1+W.

**Theorem.** There is epsilon0>0 such that, whenever
0<e,h1,h3<epsilon0, the following holds. Let q be any product exact
Nash root against a continuation C satisfying

    C_i>=0 for every i, and C_2<=2.                 (R1)

Assume also that its output annotation W is coordinatewise nonnegative.
If q0>0, then every other hazard is zero, and C0=W0=0.

Input nonnegativity does NOT imply output nonnegativity. Both are
hypotheses. The proof only needs W1,W3>=0 in the full-support branch;
retaining all W>=0 matches the intended source carrier. The conclusion
is uniform in the three premium scales, with no ratio restriction.

Write q=(x,y,z,w), H_i=product_(j!=i)(1-q_j), D_i=1-H_i. The forced
Quit endpoints and Continue endpoints are respectively

    Q0=eD0+(10-e)yzw,
    Q1=h1D1-(2+h1)xzw,
    Q2=eD2-2exyw,
    Q3=h3D3-(1+h3)xyz,                             (R2)
    K_i=(Gamma q)_i+H_i C_i.

An active owner has Q_i>=K_i and W_i=Q_i. If that owner's hazard is
also less than1, its Continue action is used and Q_i=K_i.

## Every proper support containing0

Take epsilon0<=1/10. For support01, owner1's endpoint inequality
requires h1*x>=2x, impossible. For02, owner2 requires e*x>=2x.
For03, owner0 requires e*w>=3w. Nonnegative C was used to drop its
Continue contribution.

For012, owner1 requires

    2x+z<=h1(x+z-xz)<=h1(x+z),

which is impossible. For013, owner0 requires
3y+3w<=e(y+w-yw), also impossible.

For023 the three active endpoint inequalities imply

    z>=(3-e)w/(1+e)>=(29/11)w,
    w>=(2-e)x/(1+e)>=(19/11)x,
    x>=(1-h3)z/(1+h3)>=(9/11)z.

Their product exceeds1, contradicting positive x,z,w. These arguments
permit sure hazards and require no output hypothesis.

The remaining proper support is{0}. Its Quit value is0 and its Continue
value is C0>=0. Activity forces C0=0; its output coordinate is W0=0.

## Full support: first exclude a nonzero limiting hazard vector

Suppose full-support counterexamples exist with e,h1,h3 tending to zero.
Take a convergent subsequence of q in[0,1]^4. All unadorned hazards in
this section denote its limit. Since W1=Q1>=0 and W3=Q3>=0,

    xzw=xyz=0.                                    (R3)

Active endpoint inequalities and C>=0 give Gamma q<=Q in the limit.
If x>0 and z>0, (R3) forces y=w=0, contradicting the row2 inequality
2x-2y-w<=0. If x>0 and z=0, row0 gives3y+3w<=0, then row2 again
contradicts x>0. Therefore x=0.

Pass to a further subsequence on which either z_n<1 throughout or
z_n=1 throughout. This distinguishes use of player2's Continue action.

### Case z_n<1

Player2 is indifferent. By C2<=2, its equation gives at the limit

    2y+w<=2(1-y)(1-w),
    equivalently 4y+3w-2yw<=2.                    (R4)

Rows1,3 and nonnegative C also give z<=3w and z<=2y. Row0 requires

    F=10yzw-3y+z-3w>=0.                           (R5)

For fixed y,w, F increases in z. If 2y<=3w, replace z by2y. From(R4)
and w>=2y/3 one obtains 6y-4y^2/3<=2. Since(R4) also gives y<=1/2,
this implies y<3/8. Hence

    F<=w(20y^2-3)-y<=-3w/16-y.

If 3w<=2y, replace z by3w. Equation(R4) and y>=3w/2 give
9w-3w^2<=2, while w<=2/3. Therefore w<1/4 and

    F<=3y(10w^2-1)<=-9y/8.

Thus(R5) forces y=w=0 in both cases; z=0 follows. The limit is zero.

### Case z_n=1

Here z=1 and x=0. For all sufficiently large n, 0<x_n<1, so owner0
is indifferent. Its H0 is zero. The limiting equation is

    10yw=3y-1+3w.                                 (R6)

For each of owners1,3, take a further subsequence on which it is always
sure or always mixed. A mixed owner1 has H1=0 and indifference forces
w=1/3. A mixed owner3 has H3=0 and forces y=1/2. If both are mixed,
(R6) equates5/3 with3/2, impossible. If owner1 is sure, y=1, so
owner3 cannot be mixed and is also sure. If owner3 is sure, the symmetric
argument using the mixed-owner1 equation forces owner1 sure. When both
are sure, (R6) equates10 with5, again impossible.

This excludes every possible sure-hazard boundary directly. No separate
stationary or sure-owner existence theorem is being assumed.

## Small full-support roots are excluded uniformly

The preceding compactness argument proves that every such root approaches
zero as max(e,h1,h3) approaches zero. The input coordinates other than C2
need not be bounded: only their nonnegativity was used, and C2 is bounded
by(R1).

Use the nonnegative weight vector k=(9,7,0,8), for which

    k Gamma=(6,11,6,6).

Since each active endpoint satisfies Gamma q<=Q, (R2) gives, with
s=x+y+z+w,

    6s<=k Q<=(9e+7h1+8h3)s+90yzw
       <=24 max(e,h1,h3)s+(10/3)s^3.               (R7)

For max(e,h1,h3)<=1/8 and s<=1/2, the right side is at most
(3+5/6)s<6s. Full support has s>0, a contradiction. Compactness
provides a positive uniform threshold below which s<=1/2, so combining
it with the fixed small-premium bounds proves the claimed epsilon0.

## Source compatibility and limits of the result

In this original calibration, every native absorbing reward of player2
is at most2, and its original Never payoff minus own level is -1.
Consequently actual native full caps, and limits of such caps, satisfy
C2<=2. A FULL exact Nash prefix between nonnegative cap annotations supplies
(R1) and the output hypothesis. Any root at which0 acts must then be solo0
and must have zero input and output cap for0. A positive-cap state cannot
reactivate0 at its next full Nash root.

The [canonical boundary-head reduction](CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION.md)
DOES NOT supply full root Nash: it supplies exact observer optimality,
while the pivot may have positive root regret R0. Its finite intermediate
caps can also be negative. Even eventual endpoint nonnegativity would not
repair the missing pivot optimality. In particular the present lemma does
not show that0 has finite support in a canonical incoming head, and does
not exclude an all-zero boundary endpoint or a Never-penalty plateau.
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
of the activity lemma to observer-Nash roots. No actual ancestral-tail
realization of this displayed C is claimed. This control was supplied and
independently checked by CODEX_ACTUAL_MINIMUM_ATTACK.

The current hard test is the ray e=beta,h1=beta/10,h3=beta. The activity
restriction applies for small beta but supplies neither an equilibrium
nor a positive exploitability gap. A useful next question is whether it
can be combined with the inherited boundary comparison map to produce
an admissible tail repair, rather than another root-only architecture.

Relevant Lean sources inspected: `quittingUniformEquilibriumPayoffConjecture`
(`UniformEquilibrium/Quitting/Conjecture/Basic.lean`),
`quittingRoot_activeHazards_lt_one_of_leave_sums`
(`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`),
and `exactRootSuccessor_active_eq_singleton_of_support_not_premiumTrap`
(`UniformEquilibrium/Quitting/Classification/QuittingPremiumCoreExactRoot.lean`).
The generic hypotheses of the latter two are not asserted for this family.
