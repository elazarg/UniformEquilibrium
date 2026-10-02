# Old-table hazard reselection forces opposed core reversals

Identity: CODEX_NOETHER_SUPPORT.

Status: complete ordinary-mathematics proof draft with an exact arithmetic
falsification pass; not independently reviewed or Lean-checked. This is a
further consumer of one THREE-sure branch of the actual worst-table source.
It does not consume the remaining opposed reversals or prove Fin4 UE.

## 1. Exact source and proposed actual comparison

There are four players, terminal rewards in [−1,1], and zero Never payoff.
Profiles are independent private stopping laws, and every unilateral
behavioral response enters the full cap B_i. Write U_i for prescribed
payoff, d_i=B_i−U_i, E=max_i d_i, and η(r)=inf_p E_r(p), where the infimum
ranges over ALL actual independent profiles, not a fixed calendar.

Retain the literal construction of
[membership stretching and singleton-fiber selection](../exports/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md):

    η(r*)=Ω=max_(r in the whole unit cube) η(r)>0,
    0<α<Ω/8,
    Ω/2<m=η(r)≤Ω.

The 56 non-own-singleton coordinates of r are the common α-stretch of
those of the ORIGINAL r*. The four own-singleton coordinates of r may
have been freely reselected. These are fixed tables and parameters before
the comparison. In particular,

    0<α<m/4.                                             (1)

Suppose an actual UNPADDED date-zero root q, followed by Never, has exactly
three sure quitters K and one genuinely mixed optional player o, and

    E_r(q)=m.

The reviewed
[inverse-stretch source consumer](../exports/INVERSE_MEMBERSHIP_STRETCH_SURE_CORE_SIGN_REVERSAL.md)
supplies two global facts used here: all four full debts at this actual
minimum equal m, and 0<m<1/2. Its all-player-tie proof applies at r* too
whenever an actual old-table profile is identified as a global minimum.
That consumer also excludes the case in which all three core membership
directions are pointwise nonnegative. The present proof handles an
additional case with genuine sign reversal.

For each i∈K, the positive debt m means Continue is its source-best action.
Call its Continue-minus-Quit gaps at the two optional actions its directed
core endpoints. A reversing core has a strictly positive gap at one action
and a strictly negative gap at the other; positive mean excludes two
nonpositive endpoints.

**Claim.** In this actual source there must be TWO distinct sure owners
whose directed core gaps reverse in OPPOSITE orientations. In particular,
it is impossible that all negative core endpoints occur at one common
optional action.

The finite operation tested is exact: keep all three original sure laws
at date zero and reselect only the optional player's probability of its
two root actions, at the ORIGINAL table r*. No date is inserted, no source
clock is conditioned on another player's private choice, and no profile
mixture is played. We will produce an old-table full-regret comparison
inconsistent with η(r*)=Ω≥m.

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

All denominators and equality cases have now been covered. If there was
no reversing core at all, the already reviewed pointwise-coherence
consumer applies. Otherwise the hypothesis that all reversals have one
orientation is impossible by Sections3–4. Since each core has positive
source mean, an owner cannot have negative gaps at both optional actions.
Thus two DIFFERENT sure owners must reverse in opposite orientations,
proving the claim.

## 5. Exact checks and the boundary of this operation

The first falsification test concerned the signed interval, not a new
solved-table trap. An exact rational implementation checked (10)–(11),
positivity of R, 0<p'<1, p'>p, and the bound in (9) for

    m=j/20, j=1,…,9;
    α=(m/4)(k/5), k=1,…,4;
    p=l/20, l=1,…,19.

All 684 cases passed, including 384 with v>m. These finite checks are
regressions only; (11)–(12) are the proof. An initial floating-point check
misclassified the exact equality v=m in one case; the rational check and
the separate Section4 equality treatment avoid that numerical artifact.

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
parameter relation α<m/4 is genuinely retained by the upstream source's
Ω/2<m and α<Ω/8, not inferred from arbitrary final contact fields.

## 6. Narrow source correspondence and next question

The current task uses the same named production entrance as the reviewed
inverse-stretch packet:
`exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin` in
`UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`,
and the MAX singleton moat
`minimumTerminalSemantic_exploitabilitySingletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`.
The complete pure screening declaration is
`quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card`
in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`; the mixed-root
two-endpoint formula is proved directly in Section2. These declarations
were read during the preceding independent review; no fresh Lean build
or new declaration is claimed here.

A narrow search for inverse stretch and sign-coherent sure-core consumers
identified TARSKI's preceding theorem, now linked above. This note keeps
that proof and export unchanged. The hazard-reselection calculation is
new ordinary mathematics, not a claim that the original table or all its
other minimizers are represented by this one-row family.

Concrete next question: in the actual source, can two opposed reversing
cores be jointly changed so as to defeat the two-sided old affine envelope
while retaining every owner's full response cap? The endpoint example
above prevents simply asserting that another optional hazard suffices.
