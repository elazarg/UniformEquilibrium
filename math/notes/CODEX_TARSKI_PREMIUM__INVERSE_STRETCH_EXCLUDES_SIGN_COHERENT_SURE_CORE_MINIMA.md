# Inverse stretching excludes sign-coherent sure-core minima

Author: CODEX_TARSKI_PREMIUM.

Status: complete ordinary-mathematics proof, awaiting independent review.
This consumes a limited branch of the actual singleton-fiber worst-table
source. It is not a new equilibrium-existence class or a proof of the full
Fin4 conjecture. The comparison uses the ORIGINAL maximizing table and an
UNPADDED actual root; no frozen-coordinate reward normal is assumed.

## 1. Exact source, table correspondence, and question

There are four players I. A reward table gives a number in [−1,1] to each
owner i at every nonempty coalition S. Never pays zero. Profiles use
independent complete stopping laws and admit every unilateral behavioral
response. Write U_i, B_i, d_i=B_i−U_i, E=max_i d_i, and

    η(r)=inf_(all actual independent profiles p) E_r(p),
    Ω=max_(r∈[−1,1]^60) η(r).

Use the actual construction of
[the singleton-fiber source reduction](../notes/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md),
not merely an arbitrary tuple with its listed contact inequalities:

1. r* is an ORIGINAL full-cube maximizing table with η(r*)=Ω>0.
2. Fix the construction's 0<α<Ω/8. In each owner's pair of reward
   coordinates (B,B∪{i}), ∅≠B⊆I\{i}, move the larger toward1 and the
   smaller toward−1 by fraction α. Leave equal pairs unchanged.
3. Freeze these56 stretched coordinates. The resulting table r has freely
   reselected own singletons, possibly different from those of r*.
   It is the fixed maximizing limit in that fiber, with

       η(r)=m>0,       m≤Ω.

The same α and ORIGINAL r* belong to the source construction. They are
retained here as provenance, not reconstructed from arbitrary final contact
fields. The source also has strict pure nonsingleton regret separation;
the proof below does not need an additional use of that separation.

Suppose the zero-singleton/zero-Never source arm is realized by a product
root q at DATE ZERO, followed by Never, with at least two sure quitters.
Its complete semantic pair is a global minimum at r:

    E_r(q)=m.

This is an UNPADDED actual profile. The product-base strict-margin theorem
supplies this realization. A silently padded source cannot simply be
evaluated at r*, because its new early singleton caps could change when
the four singleton parameters change. No such padded comparison is used.

Let K={i:q_i=1}, so |K|≥2. A root draw X∈{0,1}^I is sampled independently
under q. Its support is a finite product set; coordinates with probability
zero or one have just their actually supported action. At every unilateral
intervention, at least one member of K other than the deviator remains
sure at date zero. Therefore EVERY full response payoff is one of the
two membership endpoints at that date. Later dates and Never have the
same Continue endpoint. There is no earlier date.

## 2. The sign-coherence hypothesis and conclusion

For each i choose its source-best membership action b_i∈{0,1}, where1
means Quit. Define, for every opponent configuration z of positive
q_−i-probability, the directed endpoint difference

    c_i(z)=r*_i(S(z,b_i))−r*_i(S(z,1−b_i)),             (1)

where S(z,a) is the coalition of Quit players after inserting action a
for i. Both coalitions are nonempty because an unchanged sure opponent
remains. Hence (1) only uses the56 stretched coordinates, never an own
singleton. The same is true at r.

The branch hypothesis is

    c_i(z)≥0 for EVERY i and EVERY supported z.           (2)

Thus the source-best action is weakly better pointwise on the optional
players' supported configurations, rather than only after averaging them.
Equivalently, one may test (2) at r: the stretch preserves the sign of
every directed edge. Zero edges are allowed.

**Theorem.** The actual source of Section1 cannot satisfy (2). More
precisely, assuming (2) produces one supported pure root whose full
terminal regret at r is zero, contradicting η(r)=m>0.

For a THREE-sure root there is only one optional player. Its own opponent
configuration is deterministic, so its best-action direction is
automatically coherent. The hypothesis therefore reduces to the following
particularly concrete test: every sure player's Continue-minus-Quit
payoff difference is nonnegative at BOTH supported actions of the optional
player. The conclusion says that at least one sure owner must instead
have a strictly negative difference at one action and a strictly positive
difference at the other. Its average remains the positive minimum debt.

For a TWO-sure root, (2) also imposes coherence on the two optional players'
source-best actions. That stronger hypothesis is explicit; no such
condition follows merely from averaged best-response optimality.

## 3. Two global-minimum facts used in the proof

These facts concern MAXIMUM debt, not minimum total debt.

First, every coordinate of a positive global MAX minimum equals its
maximum. We include the complete ordinary-mathematics argument from
[HILBERT's note](../notes/CODEX_HILBERT__GLOBAL_MAXIMUM_MINIMUM_ALL_PLAYER_TIES.md).
At an actual minimum with value m>0, the checked MAX singleton margin
B_i−s_i≥m and d_i≤m imply U_i≥s_i for every i. To apply that declaration,
the actual semantic pair belongs to the semantic carrier; its lower bound
against all actual pairs extends to their closure by continuity of maximum
debt. Thus an attained actual infimum is a carrier minimum as required.
Suppose d_k<m. Add one
initial date at which only k Quits, with probability h; on survival use
the entire original independent profile shifted by one date. This is an
actual independent-law operation, not a mixture of publicly selected
profiles. Its complete response caps give

    d'_k=d_k+h(U_k−s_k),
    d'_j=max((1−h)(s_j−U_j)
                 +h(r_j({k,j})−r_j({k})), (1−h)d_j),  j≠k.

For k the full cap is max(s_k,B_k)=B_k. For j≠k the two cap branches
are Quit at the new date or Continue then use any complete old response;
the latter includes Never. Thus these formulas retain EVERY behavioral
tester and do not require a best-response maximizer. Unit reward bounds
give d'_k≤d_k+2h and the first branch for j≠k is at most2h. Choose

    0<h<min(1, (m−d_k)/2, m/2).

Every displayed branch is then strictly below m, contradicting the
global infimum. Consequently d_i=m for all four owners. The argument
applies separately to r and r*. Its all-player-tie conclusion is ordinary
mathematics, not a claimed checked Lean declaration.

Second, at a positive global minimum for a four-player unit-cube table,

    m<1/2.                                               (3)

The same checked margin and B_i≤1 give s_i≤1−m for all i. At the
actual all-Never profile the full cap is max(0,s_i), its prescribed payoff
is zero, and therefore its full regret is

    a=max_i (s_i)_+ ≥ m.

If a=m, all-Never is itself an actual global minimum. Since a=m>0 and
there are finitely many owners, some i has s_i=a>0 and full cap B_i=s_i
there. This contradicts that minimum's checked moat B_i−s_i≥m>0.
Hence

    m<a≤1−m,

which proves (3). This argument, independently observed by
CODEX_NOETHER_SUPPORT, requires neither a fresh gradient certificate nor
transported multipliers, and works at either table once its actual global
minimum has been identified. No quantitative refinement is needed.

## 4. Undoing the stretch at the SAME actual root

For c≥0 the directed edge transform is

    T_α(c)=0                         if c=0;
           (1−α)c+2α                if c>0.              (5)

On [0,2], T_α(c)≥c, with equality precisely when c=0 or c=2.
Both endpoint facts are important: equal reward pairs remain equal, while
the pair (−1,1) is already saturated.

Put β_i=Pr_q(X_i≠b_i). All-player ties at r give d_i(r,q)=m>0, so
β_i>0. Because (2) holds pointwise, b_i is a best action at BOTH tables.
Independence and the complete two-endpoint response formula give

    d_i(r*,q)=β_i E_(q_−i)[c_i],
    d_i(r,q) =β_i E_(q_−i)[T_α(c_i)]=m.                 (6)

Thus EVERY original debt is at most m. This calculation genuinely covers
the old full caps: the SAME root q at date zero has at least two sure
quitters, so old own-singleton coordinates and every declared post-root
tail are irrelevant to every unilateral response.

Using the ORIGINAL worst table and the fiber's upper bound now yields

    Ω=η(r*)≤E_(r*)(q)≤m≤Ω.                              (7)

All values in (7) are equal. In particular q is an actual positive global
minimum at r*, and the old all-player-tie theorem forces

    d_i(r*,q)=d_i(r,q)=m       for every i.                (8)

This is the genuinely global step. No local/contact-only fixture and no
normality in the56 frozen reward coordinates can replace (7).

## 5. Equality produces an actual pure exact equilibrium

In (6), β_i>0 and every supported opponent configuration has positive
probability. The losses T_α(c_i)−c_i are nonnegative term by term.
Equation (8) therefore forces, for every supported configuration,

    c_i(z)∈{0,2}.                                        (9)

The same directed values occur at r, since both0 and2 are unchanged by
stretching. Define the event

    A_i={X_i≠b_i and c_i(X_−i)=2}.

For each pure draw X in the source's product support, every full response
still meets another sure quitter. Its exact owner-i regret is therefore
2·1_(A_i)(X). A player currently using its better action has zero debt;
a player using the other action has debt equal to its endpoint gap0 or2.
No new test after the root can produce a third endpoint.

Equation (6) now says Pr_q(A_i)=m/2 for every i. Consequently

    E_q[Σ_i 1_(A_i)] = 2m < 1.                          (10)

The random variable inside this expectation is a nonnegative INTEGER on
a finite support. If every supported root draw belonged to at least one
A_i, its expectation would be at least1. Hence some supported pure draw
x satisfies x∉A_i for all four owners. At its actual date-zero pure root,
followed by Never, EVERY full regret is zero. At least two members of K
still quit surely, so its terminal coalition is nonempty and the full
response calculation remains valid at this pure endpoint.

This is an actual strict competitor at BOTH r and r*, not a played mixture
over source profiles: the two tables have the same relevant directed gaps
0 or2 at this supported vertex. It contradicts either η(r)=m>0 or
η(r*)=Ω>0. Thus the source's strict pure nonsingleton floor is entrance
context, not a necessary hypothesis of this consumer. It is exact terminal
Nash; its prescribed play and every unilateral response absorb at date zero
because a sure opponent
remains. The argument requires only the terminal contradiction, not a new
uniform-payoff compiler.

## 6. Boundaries, source audit, and remaining question

- The original r* and the common α are fixed before the singleton-fiber
  maximization. The four final own singletons may differ arbitrarily.
  The UNPADDED sure-core profile is what makes that difference harmless.
- A pure optional hazard causes no division by zero: only positive-
  probability configurations enter (1)–(2). If the profile were wholly
  pure, the same argument would apply. In the three-sure mixed branch,
  the one optional hazard is strictly between zero and one by definition.
- Zero directed edges are allowed and contribute no loss under inverse
  stretch. Saturated positive gaps2 are retained, not falsely treated as
  strictly improved. Equation (10) handles their only possible equality
  pattern and excludes the half-half obstruction using (3).
- Raw sign coherence is additional branch data. Global minimality and a
  positive averaged membership gain do not imply it. No statement here
  converts a sign reversal into a descent.

The named production sources inspected for this comparison are
`exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin`
in `UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`,
`quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card`
in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`, and
`minimumTerminalSemantic_exploitabilitySingletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`.
The two-endpoint formula above also follows directly from an unchanged sure
opponent's date-zero absorption. The inverse-stretch construction is ordinary
mathematics in the reviewed source packet, not a new Lean declaration.

This limited positive result arose while testing full normal-core blockers.
Those blockers are not hypotheses secretly used in the proof. The stronger
same-table source now inspected is
`exists_singletonColumnBlockerCertificate_of_fourPlayer_noUniform` in
`UniformEquilibrium/Quitting/Classification/LCP/FourPlayerSingletonColumnBlockers.lean`:
it supplies full homogeneous infeasibility and a strict blocker in every
COLUMN, unlike bare full normal core's nonpositive blocker in every ROW.
The all-rates solo/join source inspected is
`QuittingTerminalExploitabilityWitness.exists_soloRate_joiningGain` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/PreemptionCycle.lean`,
with its literal viable-owner hypothesis. Neither is needed to manufacture
another contact-only calibration.

Concrete remaining question: consume a sure owner's membership preference
that reverses across the optional support, using these genuine singleton-
column and all-rates source constraints while retaining all four full caps.
The proof above closes the sign-coherent branch only; it supplies no global
consumer of the remaining sign-reversing mixed sure-core minima.
