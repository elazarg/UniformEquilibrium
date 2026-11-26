# Cyclic favorite-pair games: interval closure and remaining source geometry

Owner: CODEX_ROOT. Ordinary mathematics, not new Lean verification.

## Current closure

[Uniform equilibrium for cyclic favorite-pair games](../exports/CYCLIC_FAVORITE_PAIRS_UNIFORM_EQUILIBRIUM.md)
proves absorbing native debt zero and original uniform equilibrium for every
0<=T<=1/4. It supplies every strategic input through explicit root
replacements and the actual compact-payoff-domain consumer. The fixed
uniform target is chosen before accuracy; deviations replace complete
behavioral laws. This is not arbitrary Fin4 closure.

For the remaining family let T>=0, keep private independent choices and
zero live/Never rewards, and use cyclic singleton and participant-pair rows

    Gamma_0=(0,-1,3,-1), J_0=(0,-3/2,2,1/4).

Every nonparticipant in a pair or triple gets T+1; every participant in a
triple and every grand-coalition recipient gets T. These rules specify all60
native rewards Z. Original rewards of interest are Z+one. The two favorite
pairs are02,13. The linked proof gives the full details and the following
boundary results for EVERY fixed T>=0: a strict gap over all original
stationary profiles, and necessity of a triple phase in every nontrivial
exact finite-period equilibrium. Their proofs are not duplicated here.
Neither result excludes approximate or nonperiodic equilibria.

The interval theorem leaves T>1/4. No unrestricted exploitability gap is
known there. The exact old-admission census concerns T=0; membership of
each larger T in other old classes is not asserted absent its own check.

## Why the whole payoff hull alone cannot settle every larger T

For every T>=6 the native reward hull contains

    v=(-1/2,3/4,-1/2,3/4)
      =(1/4)Gamma[:,1]+(1/4)Gamma[:,3]+(1/2)*0.

Its auxiliary root game has exactly THREE Nash roots, all proper and with
every successor payoff strictly positive. Thus no good-root theorem on
the entire hull can cover this whole remaining family.

The favorite02 root has odds(1/2,0,1/2,0). Active outputs are2/3, and both
quiet outputs are T/9. The other roots have supports012 and023 and are
cyclic rotations of one another. For012, write

    27y^2+5y-10=0,  1/2<y<1,
    x=(2+5y)/[4(1+y)], z=(1-y)/[2(1+y)].

The quadratic has exactly one positive root, giving positive odds. At T=6,

    R0=(4y-2)/[3(1+y)]>0,
    R1=(14+43y-43y^2)/[16(1+y)^2]>0,
    R2=2x+y/4+6xy>0.

The quiet-owner output is positive too. Its passive numerator is
-x+3y-z+7(xy+xz+yz+xyz)>0: already -x+3y-z>0 using y>1/2,
x<7/8 and z<1/6. Increasing T only increases these output numerators;
the indifference map is independent of T.

For completeness, the pair root's quiet thresholds are1/8<3/4. On012 the
two anchor equations give exactly the displayed x(y),z(y), with0<y<1;
the free equation reduces to the displayed quadratic. Its sole outsider
is strict Nash-quiet because the sum of all four joining annotations is
negative while sum v=1/2. Rotation handles023. On013 the active owner's
Phi3=-x/2-y-xy is negative, incompatible with v3=3/4;123 is symmetric.
Adjacent01 has odds(x,y)=(3/5,1), but quiet owner2 has Phi2=1/20>-1/2;
23 is symmetric. The other adjacent pairs have the wrong active signs,
and favorite13 cannot have positive active source coordinates. Singletons
require a zero source coordinate; full support would require sum v<0.
The universal sure-root exclusion is in the linked proof. This exhausts
all roots, rather than showing merely one bad root.

This is a limitation of whole-hull selection, not a counterexample to UE
or a payoff/cap-matched source. In fact first-action feasibility already
excludes the displayed v, as the next calculation shows.

## Exact coupled negative-cap restrictions

Let C_i be the actual full behavioral caps of ANY profile for this family.
Never gives at least-1, so C_i>=-1 without any equilibrium hypothesis.
The only negative participant reward in row0 is -3/2 on01, and in row2
it is -3/2 on23. For first-date hazards q, immediate Quit therefore gives

    C0>=Q0>=-(3/2)q1(1-q2)(1-q3),
    C2>=Q2>=-(3/2)q3(1-q0)(1-q1).

If C0=-A<0 and C2=-B<0, then A,B<=1; multiplying yields

    A B<=(9/4)q1(1-q1)q3(1-q3)<=9/64.             (N)

This remains true in actual-data closure and holds for every T>=0.
Rotation gives the analogous restriction for opposite caps1,3. At the
displayed hull source A=B=1/2, their product1/4 violates(N). Equivalently,
Q0,Q2<=-1/2 would require both q1(1-q3),q3(1-q1)>=1/3; their product
would be at least1/9 but at most1/16. Thus the source is outside N1.

Here N1 is the first-action outer set of the
[payoff-domain producer](../exports/PAYOFF_DOMAIN_ORIENTATION_UNIFORM_EQUILIBRIUM.md):
u in H admits product q with Q_i<=u_i, q_i(u_i-Q_i)=0 and
P_i+m_i H_i<=u_i. P_i is the nonempty-opponent passive average,
H_i the opponents' Continue probability, and m_i the minimum of0 and
all row-i rewards. Its actual zero-debt containment is proved there;
the contradiction above needs only its forced-Quit inequalities.

For T>=1/4 there is a stronger parameter-dependent restriction. Put
c=T+5/4. Adding opponent2 to row0 increases forced-Quit payoff by

    (1-q3)(2-q1/4)+(T-1/4)(q1+q3-2q1q3)>=0.

The rotated statement holds for row2. Removing both anchor hazards from
the two forced-Quit inequalities therefore gives a NECESSARY relaxed
witness r=q1,s=q3 satisfying

    (3/2)r-s/4-c rs>=A,
    (3/2)s-r/4-c rs>=B.                            (R)

It is not asserted that this modified head still meets every other N1
inequality. From(R), r,s<3/(2c), whence

    A,B<9/(4c).

Moreover the increasing maps
f(s)=(A+s/4)/(3/2-cs), g(r)=(B+r/4)/(3/2-cr)
have an equality fixed point below any feasible witness: iterate both
from0 inside the witness rectangle. The denominators stay strictly
positive and continuity gives equality in(R) at the limit. Subtraction
then gives r-s=4(A-B)/7. Setting S=r+s gives

    cS^2-(5/2)S+2(A+B)-(16c/49)(A-B)^2=0.

Its discriminant imposes the coupled necessary condition

    2c(A+B)-(16c^2/49)(A-B)^2<=25/16.              (D)

The restrictions(N),(R),(D) concern actual caps, not arbitrary prescribed
payoffs in the hull. They are consequences of first-action feasibility,
not additional raw equilibrium existence theorems.

## The remaining global task

Under a hypothetical positive absorbing gap, actual zero-debt closure
states have positive original Never. For actual approximants let e_i be
the Never-response value and p_i the owner's Never probability. Averaging
finite deadlines and Never gives

    d_i>=p_i(C_i-e_i)>=nu(C_i-e_i)>=0.

If their debts tend to0 and nu tends to a positive limit, their Never
responses converge to the matched payoff/cap coordinates. No law realizing
the closure point is asserted. These coordinates are at least-1, and their
sum is nonnegative by hull membership.

The relevant source must also satisfy joint first-action and extracted
continuation constraints, including the coupled negative-cap bounds
above. A bad hull annotation alone is therefore insufficient. The next
target is to prove good-root selection near these ACTUAL source sets, or
find a compatible global replacement of an earlier head. For larger T,
all bad-root support cases must be retained; the two-negative-favorite
branch is only one case. No claim is made that a finite kernel refinement
already supplies a complete actual-carrier characterization.
