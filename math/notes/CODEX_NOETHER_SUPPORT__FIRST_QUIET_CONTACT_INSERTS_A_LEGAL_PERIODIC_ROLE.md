# A first quiet contact inserts a legal periodic role

Author: CODEX_NOETHER_SUPPORT.

Status: proved local boundary transition in ordinary mathematics, not
independently reviewed or Lean-checked. This is a constructive continuation
across ONE explicitly identified first loss on a specified original-table
path. It is not a generic contact theorem or a complete[1,2]-box selector.
No export or new parameter-rectangle gate is requested.

## 1. The actual path and its first loss

Take the literal table of
[the independent cross-reward rectangle](../notes/CODEX_NOETHER_SUPPORT__INDEPENDENT_CROSS_REWARD_BOX_PERIOD_TWO_SOURCE.md),
but fix c_i=1, w_i=2, u_0=u_1=u_3=1 and vary only u_2=u∈[1,2].
Thus the ONLY changing coordinate is r_2({1,2})=u. All singleton,
passive, triple, grand, live and Never rewards remain fixed. Players use
independent private randomization and deviations are unrestricted complete
behavioral replacements. This paragraph specifies all60 reward coordinates
by an existing explicit table, not by a supplied strategic certificate.

Let a be the unique root in(37/50,3/4) of

    K(a)=44a⁴−7a³−26a²+a+3,
    b=(4a²−1)/(3a²).

The exact old two-phase profile has active roles02,13, primary Continue
a, secondary Continue b, and phase values

    V_A=(1,1/b,1,1/a),      V_B=(1/b,1,1/a,1).          (1)

Only player2's quiet phase-B Quit endpoint changes along the raw path:

    Q_2^B=1+(u−1)(1−a)b+a(1−b).

Its Continue value is1/a. The first equality is therefore at

    u*=1+[1/a−1−a(1−b)]/[(1−a)b]
       =(a+1)(3a−1)/(4a²−1)∈(1,2).                    (2)

Indeed u*>1 follows from a(2−a)>0, and u*<2 from
5a²−2a−1>0 on37/50<a<3/4. All other raw payoff coordinates and
all other response values are unchanged. Their quiet inequalities are
strict: a primary's margin is1/b−a−2b+2ab>0, while player3's is

    1/a−1−a(1−b)=(1−a)(2−a)/(3a)>0.

The primary sign also follows directly from the rectangle's full quiet
bound with u_i=1. Consequently the old profile is exact terminal Nash
for every u∈[1,u*], and fails for every u>u* through this one literal
quiet response. This is an actual first loss, not a failed interval box.

## 2. The new independent strategy and all five equalities

In phase A keep active players0,2, now with Continue probabilities A,y.
In phase B keep active players1,3, with Continue probabilities B,z,
and ADD player2 with Quit probability t. Player0 Continues in phase B;
players1,3 Continue in phase A. Repeat these two rows independently.
The added coin is private; there is no conditioning on opponents' clocks.

Define the phase-B active Quit endpoints for players1,3 and the two
phase-A quiet Continue values by

    q_1=1−t(1−z),             q_3=1+t(2B−1),
    W_1=(1−A)(1+3y)+Ayq_1,
    W_3=4A(1−y)+Ayq_3.

The proposed phase vectors are

    V_A=(1,W_1,1,W_3),      V_B=(1/y,q_1,1/A,q_3).     (3)

Every original-table active tie and prescribed recursion is equivalent
to the following FIVE equations:

    F_0=1−y[(1−t)(1−B)(1+3z)+Bt(1−z)+B(1−t)z]=0,
    F_1=q_1−t(1−z)−(1−t)zW_1=0,
    F_2=1−AB(4−3z)=0,
    F_3=q_3−t(1+3B)−B(1−t)W_3=0,
    F_4=1+(u−1)(1−B)z+B(1−z)−1/A=0.                 (4)

For example, player2 has phase-A Quit value1 and Continue value A·V_2^B.
Its phase-B Continue value is B(4−3z), while its Quit value is the first
three terms of F_4. Thus F_2,F_4 account for BOTH of its active dates.
The terms t(1−z) and t(1+3B) in the other owners' equalities are the
literal new collision outcomes. They cannot be omitted as an unchanged
continuation or an infinitesimal tail correction.

At (A,B,y,z,t,u)=(a,a,b,b,0,u*) all five equations hold. The old
identities used here are a²(4−3b)=1 and
b(1−a+3b−2ab)=1, verified by K(a)=0.

## 3. Regularity and the direction of entry are proved exactly

Let J_4 be the derivative of (F_0,…,F_3) in(A,B,y,z) at the base
point. With c=b(1+2b), d=b(3−2a), e=1/b it is

    J_4=[ 0     c     −e     −d
          c     0     −d     −e
         −1/a  −1/a    0      3a²
         −1/a  −1/a   3a²      0 ].                   (5)

The derivative of the first four equations in t is

    f=[1−ab(1−b),
       2b−1+ab²(1−b),
       0,
       −a−1−a²b(2a−1)]ᵀ.

The final row of the five-variable Jacobian J_5, whose coordinate order
is(A,B,y,z,t), is

    [1/a², 1−(u*)b, 0, (u*−1)(1−a)−a, 0].

Thus J_5 is the bordered matrix with upper blocks J_4,f. Exact
determinant expansion, substituting b=(4a²−1)/(3a²) and reducing by
K(a)=0, gives

    det J_4=−D_4(a)/729,
    D_4(a)=68596a³−18314a²−17596a+2759,

    det J_5=−D_5(a)/19683,
    D_5(a)=4642862a³−214972a²−2010071a−355409.          (6)

These are identities AT the exact quartic root, not polynomial identities
for an arbitrary a. Their signs need only the already known isolating
interval; termwise rational bounds give

    D_4(a)>882140063/125000>0,
    D_5(a)<−37456019/20000<0.                          (7)

For the first bound use a≥37/50 in its positive cubic and a≤3/4 in
its negative quadratic/linear terms. For the second use a≤3/4 in its
positive cubic and a≥37/50 in its negative terms. Thus
det J_4<0 and det J_5>0; regularity is verified, not assumed generic.

The implicit-function theorem now produces a locally unique smooth root
(A(u),B(u),y(u),z(u),t(u)) of (4) near u*. Its derivative satisfies
J_5 x'(u*)=−∂_u F, with ∂_u F=(0,0,0,0,(1−a)b)ᵀ. Cramer's rule yields

    t'(u*)=−(1−a)b · det J_4/det J_5>0.               (8)

There is therefore δ>0, with u*+δ<2, such that for EVERY
u∈(u*,u*+δ), the root has0<t(u)<1 and all four old continuation
probabilities lie strictly between0 and1. Negative t on the analytic
extension is not used as a strategy. No solvability assumption has been
added to the raw input u in this right-hand interval.

Equivalently, reselecting the four old equalities first gives a derivative
of the new player's gain with respect to t equal to det J_5/det J_4<0.
The new gain increases with u, so the actual inserted hazard compensates
for that increase. This is the boundary orientation that an arbitrary
contact point need not have.

## 4. All remaining caps, including new grand-coalition interventions

Only three owner/phase pairs remain quiet. Their exact original Quit
endpoints are

    Q_1^A=A+2y−2Ay,
    Q_3^A=1+A(1−y),
    Q_0^B=B(1−t)+2(1−B)(1−t)z+tz−(1−B)t(1−z).        (9)

The final negative term retains the GRAND-coalition reward−1 when the
quiet player0 joins all three active opponents. Its conditional law is
not discarded because that coalition is absent from prescribed play.
The corresponding Continue values are W_1,W_3,1/y. At the base point
all three margins are strict by Section1. Their expressions are continuous,
so, after reducing δ, all three remain strict along the new actual branch.

Together (4),(9) verify both pure action endpoints at every live row for
every player. Joint cycle survival is

    C=A y B(1−t)z<1.

Deleted-opponent cycle survivals are respectively
yB(1−t)z, Ay(1−t)z, ABz, and AyB(1−t), all strictly below1.
Thus bounded Bellman iteration makes the remainder vanish against every
complete behavioral replacement, including Never. It proves that (3)
are the actual prescribed payoff vectors and full caps. This is not a
claim only about five supported mixed actions.

There is also a literal finite-law output. At phase A, coordinates0,2
stay exactly1; W_1,W_3 remain greater than1 by continuity from1/b,1/a.
Cut after K whole cycles and independently censor later clocks to Never.
The cutoff phase-A values dominate both late singleton1 and Never0.
Consequently the same finite Bellman bound and first-active-date response
give, for v=V_A,

    U_i^K=(1−C^K)v_i,       B_i^K=v_i,       E^K≤4C^K.   (10)

This argument specifically uses the phase-A cutoff. The phase-B active
value q_1=1−t(1−z) is below1 when t>0, so a blanket assertion that
every phase value dominates the late singleton would be false.

As all rewards are bounded by4 and all prescribed finite absorption is
before2K, the direct finite-horizon bounds are E^K+16K/N for gains
and E^K+8K/N for target delivery. Beyond the cutoff only the deviator
may quit, for nonnegative singleton1. Thus each fixed u in this right-hand
interval has one fixed ORIGINAL uniform-equilibrium payoff selected before
accuracy. No cap-preserving retiming or new observation is used.

## 5. Sources, verification, and what has not been continued

The exact baseline source inspected is
`existsUnique_periodTwoParameter`,
`periodTwoParameter_mem_isolatingInterval`, and the two
`periodTwo_active_identity_*` declarations in
`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean`.
They supply this actual a,b, not an arbitrary selected equilibrium branch.

The ordinary implicit-function theorem used in Section3 is reflected by
`ContDiffAt.eventually_apply_implicitFunction`,
`ContDiffAt.eventually_apply_eq_iff_implicitFunction`, and
`ContDiffAt.hasStrictFDerivAt_implicitFunction` in
`Mathlib/Analysis/Calculus/ImplicitContDiff.lean`. These declarations and
their underlying `ImplicitFunctionData` interface were inspected in the
current local Mathlib source. Here the input is the smooth rational map
(4), and the required partial invertibility is exactly det J_5≠0 from
(6),(7). The repository does not thereby contain a Lean proof of this
new reward-specific determinant calculation.

Exact symbolic calculations checked all raw endpoint formulas (4),(9),
the determinant reductions modulo K, and the rational signs (7). Floating
values a≈0.746097, b≈0.734525 and u*≈1.762676 were only diagnostics;
neither existence nor entry direction is inferred from them.

The produced rectangle starts this path, unchanged rates carry it to its
actual FIRST quiet contact, and the new private role continues it to the
right. This consumes that specific boundary event. It does not show the
new branch reaches u=2, describe the next loss, or say that every first
contact on every path in the twelve-parameter box has these determinant
signs. The next unsupplied step is a global continuation/alternate-exit
argument past subsequent contacts, retaining every full quiet response.
