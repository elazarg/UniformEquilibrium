# Three-sure minima require opposed membership reversals

This theorem constrains the THREE-sure branch of an actual worst-table
source. It is not a new equilibrium-existence class or a proof of Fin4 UE. The conclusion
requires two distinct sure owners with opposite strict membership
reversals; that remaining case is not consumed here.

## 1. Exact source and actual comparison

There are four players I={0,1,2,3}, terminal rewards r_i(S)∈[−1,1] for
each nonempty coalition S, and zero Never payoff. The first nonempty
simultaneous Quit coalition absorbs. Profiles are independent private
stopping laws, and every unilateral behavioral response enters the full
cap B_i. At the table under consideration put s_i=r_i({i}). Write U_i for
prescribed payoff, d_i=B_i−U_i, E=max_i d_i, and η(r)=inf_p E_r(p), where the infimum
ranges over ALL actual independent profiles, not a fixed calendar.

Retain the following fixed table data; Section 1.2 proves that they can be
selected whenever a four-player positive-gap table exists:

    η(r*)=Ω=max_(r in the whole unit cube) η(r)>0,
    0<α<Ω/8,
    Ω/2<m=η(r)≤Ω.

The 56 non-own-singleton coordinates of r are the common α-stretch of
those of the ORIGINAL r*. Explicitly, for each owner i and nonempty
opponent coalition S⊆I∖{i}, pair r*_i(S) and r*_i(S∪{i}). If they are
unequal, replace the larger value u by (1−α)u+α and the smaller value l
by (1−α)l−α. Leave equal pairs unchanged. These seven disjoint pairs
per owner account for exactly the 56 coordinates. The four own-singleton
coordinates of r may have been freely reselected.

These are fixed tables and parameters before the root comparison; no
perturbation is selected separately for an owner or response. In particular,

    0<α<m/4.                                             (1)

Suppose an actual UNPADDED date-zero root with Quit probabilities
q∈[0,1]^I, followed by Never, has exactly three sure quitters K and one
genuinely mixed optional player o, and

    E_r(q)=m.

The pointwise-coherence case is proved in Section 4. The two global facts
needed below are proved in Section 1.1: all four full debts at this actual
minimum equal m, and 0<m<1/2. The all-player-tie
proof applies at r* too whenever an actual old-table profile is first
identified as a global minimum.

For each i∈K, the positive debt m means Continue is its source-best action.
Call its Continue-minus-Quit gaps at the two optional actions its directed
core endpoints. A reversing core has a strictly positive gap at one action
and a strictly negative gap at the other; positive mean excludes two
nonpositive endpoints.

Explicitly, at the final table define

    G_i(0)=r_i(K∖{i})−r_i(K),
    G_i(1)=r_i((K∖{i})∪{o})−r_i(K∪{o}),       i∈K.

**Theorem.** In this actual source there must be TWO distinct sure owners
whose directed core gaps reverse in OPPOSITE orientations. In particular,
it is impossible that all negative core endpoints occur at one common
optional action. Equivalently, after naming the two owners i,j,

    G_i(0)<0<G_i(1),       G_j(1)<0<G_j(0).

The same signs hold at r* because the signed stretch preserves them.

The finite operation tested is exact: keep all three original sure laws
at date zero and reselect only the optional player's probability of its
two root actions, at the ORIGINAL table r*. No date is inserted, no source
clock is conditioned on another player's private choice, and no profile
mixture is played. We will produce an old-table full-regret comparison
inconsistent with η(r*)=Ω≥m.

### 1.1 Complete prerequisite proofs at global MAX minima

The MAX singleton moat gives B_i−s_i≥e at a positive global
minimum of value e. An attained actual infimum is a minimum on the
semantic carrier as well: its pair belongs to that carrier, and the
lower bound extends to its closure by continuity of maximum debt.
Since d_i≤e, the moat implies U_i≥s_i.

If d_k<e, prepend one private solo-k hazard h, shifting the entire old
profile by one date on survival. The owner's cap is max(s_k,B_k)=B_k,
and the exact FULL debts are

    d'_k=d_k+h(U_k−s_k),
    d'_j=max((1−h)(s_j−U_j)+h[r_j({k,j})−r_j({k})],
             (1−h)d_j),                     j≠k.

The second coordinate formula retains the initial Quit branch and the
entire old response branch, including Never. Unit bounds give an owner
increase at most 2h and an initial nonowner branch at most 2h. Choosing

    0<h<min(1,(e−d_k)/2,e/2)

makes every displayed debt strictly below e, a contradiction. Thus ALL
owners' debts equal e. This argument uses an actual independent prefix,
not cap attainment or a publicly selected mixture.

Also s_i≤B_i−e≤1−e. At all Never the full regret is
a=max_i(s_i)_+≥e. Equality a=e>0 would make all Never a global minimum,
yet a maximizing positive-singleton owner has B_i=s_i there, contradicting
its moat. Therefore e<a≤1−e and e<1/2. This applies at either table
once actual global attainment has been established. The moat declaration
is named in Section 6.

### 1.2 Construction of the fixed tables from a positive gap

Suppose a real four-player reward table has η>0. A common positive scale
puts all terminal rewards in [−1,1] and scales η by the same factor; Never
remains zero. For two tables at uniform distance δ, every prescribed and
deviated payoff changes by at most δ. Taking the full deviation supremum,
the maximum over players, and the infimum over actual profiles gives

    |η(r)−η(r')|≤2δ.

Thus η is continuous on the compact sixty-coordinate reward cube.
Its maximum Ω is attained at a table r*, and Ω>0. All Never has regret
max(0,max_i r_i({i}))≤1, so Ω≤1.

For each coalition S with |S|≥2, let p^S have its members Quit0 and all
others Never. Another sure quitter remains after every unilateral
replacement, so its full regret is

    e_S(r)=max_i [r_i(S△{i})−r_i(S)]_+.

All coalitions on the right are nonempty. No own-singleton coordinate
occurs, even when deletion leaves a singleton, because its owner differs
from the deviator. Set Γ(r)=min_(|S|≥2)e_S(r). Every p^S is actual, so
Γ(r*)≥Ω>0.

Choose 0<α<Ω/8 and perform the paired stretch defined in Section 1,
initially leaving own singletons unchanged. Its displacement is at most
2α. For an old directed membership gap c, the new gap is T(c) from (2).
For c>0 this increases affinely to (1−α)c+2α; c=0 remains zero and c<0
remains negative. Consequently every positive e_S satisfies

    e_S(r*_α)=(1−α)e_S(r*)+2α.

Therefore

    η(r*_α)≥Ω−4α>Ω/2,
    Γ(r*_α)≥Ω+α(2−Ω)>Ω.

Freeze the 56 non-own-singleton coordinates of r*_α and maximize η over
the remaining four-coordinate cube. Let r be any maximizing table and
m=η(r). This fiber contains r*_α and is contained in the whole reward
cube, giving Ω/2<m≤Ω. Its own-singleton choice does not change the
paired non-own-singleton stretch or Γ. In particular α<m/4, as required.

This proves the table-selection part of the source. It does not assert
that its minimum has a zero-singleton law or a three-sure realization;
those are the explicit branch hypotheses of the theorem.

## 2. Complete caps reduce to four signed affine rows

At least two of K remain sure at date zero after any single core deviates;
all three remain after o deviates. Hence a unilateral complete response
is a mixture of its date-zero Quit and Continue endpoints. Every later
finite date and Never has the Continue payoff. There is no earlier date.
Every relevant reward coordinate is a non-own singleton or a larger
coalition, so the singleton reselection is harmless at BOTH tables.

Suppose at least one core reverses and all negative core endpoints occur
at the same optional action A. Label the other optional action B, and put

    p=Pr_q(optional action A),       β=1−p,       s=1−α.

Then 0<p<1. For each core i let (a_i,b_i) be its OLD directed endpoints
at A,B. Every pair is either

    a_i<0<b_i                       (a reversing core),
    a_i≥0 and b_i≥0                 (a coherent core).

For a signed edge c∈[−2,2], the stretch is

    T(c)=s c+2α sign(c),     with sign(0)=0.               (2)

The four source debts can be represented by endpoint pairs (a_i,b_i)
satisfying the exact common contact equations

    p T(a_i)+β T(b_i)=m.                                 (3)

For a core this follows from its positive Continue-minus-Quit mean. Its
full OLD debt at any reselected probability t of A is

    d_i^*(t)=max(0, t a_i+(1−t)b_i).                      (4)

For the optional owner its source-best action is fixed across both tables:
its opponents are deterministic K and the stretch preserves the sign of
that single membership edge. Let c>0 be its old best-minus-other gap.
Its debt row is (0,c) if A is its best action, and (c,0) otherwise. This is
a coherent row, (3) is its source debt identity, and its full old debt is
the corresponding nonnegative affine expression in (4). The zero endpoint
here represents zero regret when taking its best action; it is not a new
terminal reward coordinate. Applying T(0)=0 is exactly consistent with
this representation.

Thus all four full caps, including every finite late response and Never,
are accounted for by (4). The new operation keeps this screening valid.

## 3. A common reselected hazard when old reversing rows are too high

Every reversing row has the SAME old value at the original probability p:

    v=p a_i+β b_i=[m+2α(2p−1)]/s.                       (5)

The numerator is positive because 2α<m/2. First suppose v>m. Define

    p'=1−β m/v.                                         (6)

Then p<p'<1. For each reversing row, a_i<0 gives the exact improvement

    p'a_i+(1−p')b_i
      =a_i+(m/v)(v−a_i)
      =m+(1−m/v)a_i < m.                                (7)

It remains to check EVERY coherent row, including the optional debt row.
Fix such a row (a,b). If a=0 then b>0 by (3). Since T(b)≥b,

    (1−p')b < βb ≤ m.                                   (8)

If a>0, put x=pa+βb. Equation (3) retains at least the positive stretch
contribution from state A, so

    x≤(m−2αp)/s.

Also b≥0 implies a≤x/p. With p'>p,

    p'a+(1−p')b
       =x+(p'−p)(a−b)
       ≤(p'/p)x
       ≤(p'/p)(m−2αp)/s.                               (9)

The last bound is STRICTLY below m. Here is the complete signed rational
calculation, so no cap endpoint is discarded. Set

    D=m+2α(2p−1),
    R=m[2−m−6p(1−p)]
         +2αp[(4−3m)p+2m−2].                            (10)

The relevant denominators p,s,D are positive. Substituting
p'=(D−βms)/D yields the exact factorization

    m p s D − (D−βms)(m−2αp) = α R.                     (11)

We prove R>0 for EVERY 0<p<1, 0<m<1/2 and 0<α<m/4, not only the subset
where v>m. The first bracket in (10) is positive because

    2−m−6p(1−p) ≥ 1/2−m > 0.

If C=(4−3m)p+2m−2≥0, this proves R>0. If C<0 then p<1/2, since at p=1/2
the expression C is m/2>0 and its slope is positive. Put d=1/2−p>0.
Using 2α/m<1/2 on the NEGATIVE term pC gives

    R/m > 1/2−m+6d² +(1/2)(1/2−d)[m/2−(4−3m)d]
        = 1/2−7m/8 +(m/2−1)d +(8−3m/2)d²
        > 1/16−d+4d²
        = (2d−1/4)² ≥ 0.                                (12)

The second strict inequality uses m<1/2 and d>0; no approximation or
asymptotic source relation enters it. Equations (11)–(12) prove the strict
upper bound in (9).

Combining (7)–(9) with m>0 and the positive-part cap in (4), ALL FOUR
old full debts at the actual reselected root are strictly below m. Hence

    Ω=η(r*)≤E_(r*)(q(p'))<m≤Ω,

a contradiction. This case gives a literal independent strategy at the
old table, not just a necessary directional condition.

## 4. The remaining same-root case v≤m

Keep the original p. Every reversing old row equals v≤m. Every coherent
old row is at most its new value m because T(c)≥c for c≥0. Therefore

    E_(r*)(q)≤m.

If v<m, at least one reversing core has old debt strictly below m. The
chain Ω≤E_(r*)(q)≤m≤Ω either already contradicts a strict inequality, or
identifies q as an actual old global minimum of value m. The latter is
impossible by the all-player-tie theorem at r*, because that core has
strict slack. This does not apply the old moat at an arbitrary source:
old globality is first established by the displayed chain.

If v=m, equation (5) forces

    p=(2−m)/4,       β=(2+m)/4.

Both p and β exceed m/2 when 0<m<1/2. Let w∈{p,β} be the optional owner's
probability of its non-best action. Its contact equation is wT(c)=m,
with c>0. Hence T(c)=m/w<2. The old edge is not saturated, and T(c)>c.
Its old debt wc is therefore strictly below m. The same old-globality
and all-player-tie argument gives the contradiction in this last case.

All denominators and equality cases in the one-orientation case have now
been covered.

For completeness, if no core reverses, each source-best membership
direction is nonnegative pointwise; the optional direction is automatically
so against its deterministic opponents. Let c_i(z)∈[0,2] be an owner's old
directed gap toward that best action at supported opponent configuration z,
and let β_i>0 be its source probability of using the other action.
Independence and screening give

    d_i^old=β_i E[c_i],       d_i^new=β_i E[T(c_i)]=m.

Since T(c)≥c on [0,2], the original global chain gives
Ω≤E_old(q)≤m≤Ω. Old all-player ties force equality in every coordinate.
The nonnegative stretch loss therefore vanishes at every supported
configuration, so all relevant directed gaps are 0 or 2.

For a product-supported pure vertex, owner i's full regret is twice the
indicator that it uses the non-best action on a gap-2 edge. Each such
event has probability m/2. The expected number of losing owners is 2m<1,
so some supported vertex has none. It retains all three sure quitters
and is an actual pure zero-regret profile at both tables, a contradiction.
The product distribution is only a counting device; the implemented
competitor is one deterministic vertex.

Thus all cases without opposed reversals have been excluded. Positive
source mean prevents any core from having negative endpoints at both
optional actions. The required oppositely reversing owners are therefore
DISTINCT, proving the theorem.

## 5. Exact checks and the boundary of this operation

The expression in (6) is used as a probability only when v>m. In that
branch (9)–(12) prove 0<p<p'<1 and the strict full-regret comparison.
At v=m the exact same-root argument of Section 4 applies; outside v>m
the expression (6) need not belong to [0,1].

The zero rule T(0)=0 is retained separately throughout. In (8), an
optional or core row with first endpoint zero is not silently treated
as having a positive stretch contribution there. A positive saturated
edge c=2 stays unchanged; Section 4 excludes precisely that saturation
for the optional edge in the v=m case. The strict inequalities α>0,
α<m/4 and m<1/2 are source hypotheses, not consequences of the finite
affine contact equations.

The operation does NOT automatically handle opposite orientations. For
an exact algebra test take m=1/4, α=1/100, p=1/2 and new affine rows

    (1,−1/2),   (−1/2,1),   (1/4,1/4),   (0,1/2).

Every new row has value m at p. The two reversing old rows are
(98/99,−48/99) and its reversal; the coherent rows are (23/99,23/99) and
(0,48/99). The minimum over the ENTIRE old optional-hazard interval of
the maximum of their positive parts is exactly 25/99>1/4, attained at
p=1/2. Thus the old one-variable envelope can obstruct this comparison
when both orientations occur. These endpoint data fit disjoint owner
membership pairs in the unit cube; taking all own singletons zero makes
all Never exact, so they are explicitly NOT a positive global-source
counterexample. No conclusion about the actual remaining source follows
from this local endpoint test.

The source comparison uses two different global facts, kept separate:

- At the FINAL table, actual global minimality supplies all four contact
  equalities and the strict bound m<1/2.
- At the ORIGINAL table, η(r*)=Ω≥m excludes the reselected full profile,
  or identifies the unchanged profile as an old global minimum before
  invoking its all-player-tie property.

No sixty-coordinate or four-coordinate normal is used. No same-labelled
multiplier, cap-minimizing tail completion, payoff-only compression,
finite-menu Nash selection, or temporal compiler is imported. The strict
pure-coalition margin is unnecessary for this consumer. The sole extra
parameter relation α<m/4 follows from Section 1.2's Ω/2<m and α<Ω/8;
it is not inferred from arbitrary final contact fields.

## 6. Source correspondence and actual consumer

The production entrance is
`exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin`
in
`UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`.
At a joint semantic/law carrier minimum with zero Never and zero singleton
masses, strict cap-singleton margins give ONE unpadded product root
realizing the entire prescribed-payoff/full-cap pair and terminal law.
This theorem takes the additional branch in which the resulting root has
exactly three sure players and a genuinely mixed remaining player. It
does not assert that every source has the required zero masses or that
every reconstruction has three sure players.

The checked MAX moat used in Section 1.1 is
`minimumTerminalSemantic_exploitabilitySingletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`.
It concerns maximum debt over the full semantic carrier, not minimum
total debt or a fixed-calendar optimum. The all-player-tie and strict-half
consequences are proved in Section 1.1. The corresponding tracked
declarations are `minimumTerminalSemantic_maximumDebt_allPlayersTie`
and `minimumTerminalSemantic_maximumDebt_lt_half` in
`UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`.

The pure screening declaration is
`quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card`
in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.
The mixed-root screening needed in this packet is proved directly in
Section 2. Cap preservation is not inferred from prescribed-payoff
equality, and no calendar-labelled multiplier is transported through the
root realization.

Section 1.2 supplies the literal initial maximizer r*, common stretch,
and Ω/2<m≤Ω. This existential construction may change the counterexample
table. The comparison retains those exact relations: it constructs an
actual independent root at r*. That root need not be Nash in a finite
auxiliary game.

The argument permits strictly negative core endpoints of one orientation
and reselects the optional hazard to protect all four complete debts. The resulting
necessary condition is opposed strict reversals in two core owners,
not merely one sign-changing owner.

## 7. Narrow Lean handoff

These are proposed theorem shapes, not existing checked declarations.

1. **Signed affine-row comparison.** Inputs are 0<m<1/2,
   0<α<m/4, 0<p<1, a finite set of gap rows in [−2,2]² satisfying
   pT(a)+(1−p)T(b)=m, each row either a<0<b or a,b≥0, with at
   least one reversing row. Include the optional zero-positive row
   (0,c) or (c,0), c>0. Prove the all-case comparison:
   if v>m, (6) is a legal probability and every old positive-part
   row is strictly below m; if v<m, at p all rows are at most m
   and a reversing row is strict; if v=m, the optional row is strict.
   Keep the zero sign case and every positive denominator explicit.

2. **Actual screened-root adapter.** With three fixed sure Quit0 laws,
   identify each core's unrestricted debt with the positive part of
   its affine Continue-minus-Quit gap. Identify the optional debt
   with its non-best-action probability times the deterministic
   best-minus-other gap. This must include every late finite deadline
   and Never, not just the two prescribed root actions.

3. **Original-table contradiction.** Inputs retain the exact reward
   stretch and arbitrary own-singleton reselection, the original
   global value Ω, final global value m, and actual root attainment.
   Use (1) and the ordinary prerequisites in Section 1.1, then the
   affine-row comparison. In the weak same-root cases, FIRST derive
   old global attainment from Ω≤E_old≤m≤Ω, and only then apply
   all-player ties. In the strict case use the actual reselected root.

4. **Opposed-reversal output.** If no core reverses, the complete
   pointwise-coherence argument in Section 4 applies. Otherwise exclude the common-orientation alternatives
   and return two distinct sure owners with opposite strict signs
   at the optional player's two supported actions.

No structure in this handoff should assume successful hazard selection,
the all-player-tie conclusion, old global attainment, or the sought
opposed pair as an input. The supplied-object verification and the actual
source-to-contradiction steps are separate.

## 8. Scope

The theorem narrows a particular actual source branch. It does not
produce arbitrary low-regret laws, consume opposed reversing cores,
handle the two-sure case, or establish a new raw-table UE class. The
opposed-row regression in Section 5 explicitly prevents asserting that
another optional hazard always suffices.

The construction keeps every full deviation and never opens an earlier
singleton-access date during the old-table root comparison. The only
prefix used is the fully accounted ordinary all-player-tie proof after
its own global hypotheses have been supplied. No reward normal, selected
payoff-only law, cap-attaining deviation, public correlation, stationary
repetition, or finite-menu exactification is assumed.
