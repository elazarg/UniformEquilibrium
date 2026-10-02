# Positive maximum-debt minima and a prescribed-singleton collar

Identity: CODEX_PORTMANTEAU_SCREEN.

Status: independent ordinary-mathematical review of the strategic realization,
compactness, common-calendar attachment, and harmonic parts of
[GENERIC_SCREEN.md](../gpt/GENERIC_SCREEN.md) and its
[full proof](../gpt/GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR.md).
These parts pass. The polynomial exclusion is a supplied premise for this
bounded review and has a separate independent audit. No fresh Lean compilation or
axiom audit was performed. This notebook is not an export or an assertion of
unconditional equilibrium existence.

The accompanying review is
[GENERIC_SCREEN__BY_CODEX_PORTMANTEAU_SCREEN.md](../feedback/GENERIC_SCREEN__BY_CODEX_PORTMANTEAU_SCREEN.md).

## 1. Exact question and scope

There are four players and fifteen nonempty quitting coalitions. Rewards
r_i(S) lie in [−1,1]; live play and Never pay zero. A profile consists of
independent private complete stopping laws on the nonnegative integers and
Never, equivalently unrestricted behavioral strategies in this quitting game.
A unilateral deviation may replace one player's entire behavioral strategy.
No public correlation, cap attainment, finite-memory restriction, or fixed
finite response menu is assumed.

For an actual profile p let U(p) be its prescribed terminal payoff vector,
B_i(p) the supremum of terminal payoff over all unilateral behavioral
replacements of i, and μ_p its complete first-coalition law, including Never.
Let d_i=B_i−U_i, E=max_i d_i, and η(r)=inf_p E_r(p). Let K_r be the closure
of the actual (U,B) pairs and L_r the closure of the actual ((U,B),μ) points.
These are finite-dimensional semantic carriers, not compactifications that
assert realization by one limiting strategy.

Write s_i=r_i({i}), and b for the other 56 reward coordinates. The supplied
algebraic premise is that Π(b)≠0 excludes every date-zero product root with
at least two sure quitters whose four complete debts are equal and positive.

Questions checked here:

1. Does every joint-carrier minimum at η(r)>0 then have positive total
   prescribed singleton mass?
2. Does this imply one positive mass bound for every sufficiently accurate
   actual near-minimizer, uniformly over s with η(r_b(s))≥a>0?
3. Can the reviewed membership-fiber common-calendar source retain that bound
   without an extra ancestry or strategy assumption?
4. Is the proposed harmonic inequality at positive MAX minima correct, and
   does it imply a worst unit-cube gap strictly below 1/3?

All four answers are affirmative in the stated scope.

## 2. Bounded source route and exact declarations

The route was selected through the zero-Never/zero-singleton product-base row
of `docs/TOOLKIT.md` and the matching paragraph of `docs/FRONTIER.md`. The
following definitions and declarations, together with their actual imports,
were inspected. No global Lean-tree survey was used.

- `quittingContinuationBestResponseValue`,
  `UniformEquilibrium/Quitting/Root/FirstBranch.lean`: its definition is the
  real supremum of terminal payoff over all `BehaviorStrategy who`
  replacements. Thus the semantic cap is the unrestricted behavioral cap.
- `QuittingTerminalSemanticPair`, `quittingTerminalSemanticPair`,
  `quittingTerminalSemanticPrefix`, `quittingTerminalSemanticCarrier`,
  `quittingTerminalSemanticCarrier_isCompact`,
  `continuous_quittingTerminalSemanticPrefix`, and
  `quittingTerminalSemanticPrefix_mem_carrier`,
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`: the pair is
  prescribed payoff and the preceding unrestricted cap; prefixing is the
  continuous max-of-Quit-and-Continue map and preserves the carrier.
- `quittingTerminalSemanticDebt_nonneg_of_mem_carrier`,
  `UniformEquilibrium/Quitting/Root/TerminalSemanticDebt.lean`: debts remain
  nonnegative on the entire carrier.
- `minimumTerminalSemantic_exploitabilitySingletonMargin` and
  `minimumTerminalSemantic_exploitabilityAuxiliaryNash_eq_allContinue`,
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`:
  the objective in their hypotheses is maximum semantic exploitability.
  The former concludes E(U,B)≤B_i−s_i at the same positive global MAX minimum.
- `minimumTerminalSemantic_maximumDebt_allPlayersTie`,
  `terminalSemantic_minimum_of_actualMinimum`,
  `quittingTerminalDeviationDebt_eq_exploitability_of_attained_positive_minimum`,
  and `not_allNever_positiveMinimumTerminalSemanticExploitability`,
  `UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`:
  these are MAX statements, and the all-player tie theorem assumes the unit
  reward bound. This file imports the MAX singleton moat and the literal solo
  cap-threshold machinery; it does not switch to a total-debt minimizer.
- `QuittingTerminalSemanticLawPoint`, `quittingTerminalSemanticLawCarrier`,
  `quittingTerminalSemanticLawCarrier_isCompact`,
  `exists_terminalSemanticLawCarrier_lift`,
  `terminalSemanticLawCarrier_rewardMoment`, and
  `terminalSemanticLawCarrier_fst_mem_carrier`,
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`:
  the law is retained jointly with the same semantic pair. Other declarations
  in this file minimize total debt; those are not used here.
- `exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin`,
  `UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`:
  the exact realization theorem used below. Its direct import is
  `ProductRootLawSupport.lean`, which imports `TwoSureProductRootTailScreen.lean`.
- `exists_twoSureProductRootThenNever_realizing_semantics_of_strictSingletonMargin`,
  `UniformEquilibrium/Diagnostics/Quitting/ProductRootLimitCapSandwich.lean`:
  the underlying realization proof was inspected to check why strictness
  removes the early singleton cap branch.

Nearby symbol searches covered the cited maximum-debt, strict-margin, and
product-base files. They did not reveal a hidden stronger premise or an
already stated harmonic bound in those files. This is not an exhaustive
novelty search. No literature-derived theorem is asserted; the supplied
finite-game Nash theorem and elementary finite-dimensional compactness are
the mathematical dependencies of the reproduced arguments.

## 3. Exact realization theorem: hypothesis-by-hypothesis audit

The exported strict-margin declaration has these mathematical inputs:

| Input | What the manuscript supplies |
| --- | --- |
| A finite decidable player type, with cardinality greater than one | Four players |
| A finite reward table | The normalized table r |
| One point in the joint semantic/law carrier | The same minimizing ((U,B),μ) |
| μ(Never)=0 | Derived in Section 4 below |
| μ({i})=0 for every i | Nonnegative singleton coordinates summing to zero |
| s_i<B_i for every i | B_i−s_i≥m>0 from the MAX moat |

The conclusion supplies one product root, two distinct sure quitters, and
both identities

    semanticPair(root-then-Never)=(U,B),
    outcomeLaw(root-then-Never)=μ.

It also supplies the same two identities for stationary repetition of that
root. The latter output is unused. The theorem does not assume a minimum,
Nash ancestry, a finite-calendar source, a cap-attaining response, an extra
source bound, or a previously selected product base. Finiteness provides the
reward bound internally through `exists_quittingRewardBound`.

The proof route gives, at the same reconstructed root, the cap sandwich

    M_i≤B_i≤max(s_i,M_i),

where M_i is the maximum of the two date-zero action endpoint payoffs. If
B_i>s_i and M_i<B_i, the upper inequality is impossible. Hence B_i=M_i.
Two sure quitters ensure that at least one opponent still absorbs at zero
after any single player's deviation, so this endpoint maximum is exactly
the cap of the unpadded root. The strict-margin theorem therefore does the
full work claimed in the manuscript; the weaker-margin padded theorem is
not being substituted.

## 4. Zero singleton mass forces zero Never mass at a positive minimum

Choose one actual sequence converging jointly to ((U,B),μ). For its nth
profile write a_ni for player i's marginal Never probability and
p_n=∏_i a_ni. Independence makes p_n the joint Never probability. If u_ni is
the prescribed singleton-i probability, then

    u_ni≥(1−a_ni)∏_{j≠i}a_nj≥p_n(1−a_ni).

The first event says only i ever quits, and therefore its first coalition
is {i}. The second inequality uses a_ni≤1. It remains valid when a_ni=0.

If μ(Never)>0 and every μ({i})=0, joint convergence bounds p_n away from
zero and makes every u_ni tend to zero. Thus every a_ni tends to one and
μ(Never)=1. The retained reward-moment identity gives U=0. At a positive
MAX minimum the moat and d_i≤m imply

    U_i−s_i=(B_i−s_i)−d_i≥m−d_i≥0.

Consequently all s_i≤0. Against all Never, the full cap of i is max(0,s_i)
and its prescribed payoff is zero. All Never would therefore have E=0,
contradicting η(r)=m>0. This proves μ(Never)=0.

The product-base theorem now produces an actual screened root with exactly
the minimizing pair. The MAX tie theorem makes its four debts equal to
m>0. The supplied algebraic exclusion rules it out. This establishes
positive total singleton mass at every minimizing law.

Exact boundary tests clarify the scope. The zero reward table and all Never
have zero singleton mass and Never mass one, so positivity/minimality cannot
be deleted from the final Never-zero conclusion. A correlated lottery that
plays all Never with probability 1/2 and a fixed sure pair with probability
1/2 has zero singleton mass and Never mass 1/2; independence is indispensable
for the dichotomy. Such public correlation is not supplied by the game's
independent private clocks. Two players quitting surely at date n for each n
also show why one must retain the outcome law jointly: their first coalition
remains the pair although a naive clock limit at infinity would be Never.

## 5. Compactness and quantifier audit

The projection of L_r to semantic pairs is K_r. The forward inclusion is
continuity; for the reverse, take any actual sequence approaching a point of
K_r and a convergent subsequence of its laws in the finite simplex.
Consequently L_r contains minimizing points. Its minimum level set is
compact, and S(μ)=Σ_i μ({i}) is continuous and strictly positive there.
Let its minimum be κ_*>0.

If every ε>0 admitted an actual p with E_r(p)≤η(r)+ε and S(μ_p)<κ_*/2,
choose ε=1/n and a joint convergent subsequence. Its limit minimizes E but
has S≤κ_*/2, impossible. Thus one ε_0>0 and κ=κ_*/2 work for every actual
near-minimizer. There is no choice of a special favorable approximation
sequence in this quantifier.

For the fiber version fix b with Π(b)≠0 and a>0. The parameter set

    D_a={s∈[−1,1]^4:η(r_b(s))≥a}

is compact because η is 2-Lipschitz in the reward sup norm. To verify the
varying-table carrier graph, let r_n→r and z_n∈L_(r_n) with z_n→z.
Approximate z_n by an actual triple to error 1/n and evaluate those same
clock laws at r. Their prescribed payoffs and each full cap change by at
most ||r_n−r||∞; the outcome law is unchanged. These actual triples converge
to z, so z∈L_r. A supremum over unrestricted responses causes no failure of
this estimate because the payoff bound is uniform over every response.

The pairs (s,z) with s∈D_a, z∈L_(r_b(s)), and E(z)=η(r_b(s)) form a
compact set in the common bounded ambient space. Section 4 gives S>0 on
it. Minimize S on this set and repeat the same sequence contradiction to
obtain κ,ε_0 uniformly in every s∈D_a and every actual profile at that
table. A positive lower gap threshold is used; no uniform collar as a→0,
or over varying generic b approaching Π=0, is established.

## 6. Common-calendar attachment and ancestry boundary

The actual predecessor inspected was
[MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md](../exports/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md),
especially Sections 4–6. Its later construction takes a fixed b, a positive
fiber maximum Ω_b, and a pure nonsingleton sure-coalition floor above Ω_b.
The original endpoint stretch establishes these fields in Sections 2–3,
but its formula and its original full-cube maximizing table do not occur in
the common-calendar proof.

The new generic fiber provides these exact inputs, with the stronger floor
for all screened roots. It leaves all four own singletons free in [−1,1].
That freedom is needed for the four-coordinate normal-cone sign; no normal
in the other 56 directions is claimed.

For every inner minimizer used there, the complete tester pool gives

    E≤F≤E+ε_m,
    η(r_m)≤E_(r_m)(p)≤η(r_m)+ρ_m+ε_m,

uniformly over the calendar window and over all selected tuples. Since
η(r_m)→Ω_b>0, the fiber collar applies with a=Ω_b/2 to every sufficiently
late inner minimizer before the tuple/calendar selection. No tuple averaging
or dependence of its weights on p can remove a pointwise fact valid for
every candidate p.

The silent shift preserves the prescribed outcome law. The predecessor's
own cap moat ensures that the shift also preserves its full cap and E.
Recomputing or transporting tester weights changes no prescribed singleton
mass. Finally, evaluating the selected laws at the fixed limiting table
r_∞ preserves their entire outcome law. Thus the same actual profile and
same final weights retain activity, the enlarged-calendar directional
inequality, all-owner weights, total singleton pressure, and S(μ_p)≥κ.
An infinite subsequence has one fixed owner with μ_p({i})≥κ/4.

This last quantity is total prescribed singleton mass, summed over all
dates. It supplies neither a fixed-date atom nor a singleton atom after a
selected response. It gives no new cap-attainment, post-response debt
control, individual reward normal, or exact old-table inverse-stretch
identity. The manuscript explicitly relinquishes that identity. Reusing
Sections 4–6 is valid; claiming literal preservation of every predecessor
field would not be.

## 7. Independent harmonic calculation

At any positive global MAX minimum in the unit reward box, the existing
lemmas give d_i=m and L_i=B_i−s_i≥m>0. Prefix one product root with
q_i(t)=tλ_i for fixed positive λ_i. At t=0 the Quit endpoint is s_i and
the Continue cap endpoint is B_i>s_i. Finitely many continuous endpoint
gaps therefore keep the Continue cap branch active on one common small
positive interval.

Let β_i=∏_{j≠i}(1−q_j), Q_i be the Quit payoff, and H_i the absorbing
opponent contribution when i Continues. On that interval the exact full
prefix identity is

    d'_i=β_i d_i+q_i(H_i+β_i U_i−Q_i).

At zero, H_i=0, β_i=1, Q_i=s_i, and
β_i'(0)=−Σ_{j≠i}λ_j. Differentiating gives

    (d'_i)'(0)=λ_i(U_i−s_i)−mΣ_{j≠i}λ_j
             =λ_i L_i−mΣ_jλ_j.

This derives the manuscript's first-order ledger directly from the complete
cap identity. The endpoint functions are finite polynomials; collisions are
included and contribute only to the higher-order remainder in this formula.
The sign argument needs one sufficiently small t, which exists for all
coordinates simultaneously by finiteness. Prefixing is an actual legal
operation, and its continuous semantic map preserves K_r for unattained
carrier minima too.

Choose λ_i=1/L_i. If Σ_i m/L_i>1, all four first derivatives are equal and
strictly negative. All debts would then be below m for small positive t,
contradicting minimum E=m. Hence

    Σ_i m/(B_i−s_i)≤1.

For any finite number n≥2 of players, every summand is positive, so no L_i
can equal m. Also L_j≤2 gives

    L_i≥m/[1−(n−1)m/2],
    U_i−s_i≥(n−1)m²/[2−(n−1)m].

The denominators are positive because m/L_i>0 and the harmonic inequality
imply 1−(n−1)m/2>0. These are MAX-minimum conclusions; no TOTAL-minimum
collar is imported.

For four players let a=max_i s_i. All Never has E=max(0,a). Global minimality
gives max(0,a)≥m, and equality would make all Never a positive minimum,
excluded by the existing all-Never lemma. Thus m<a≤1. For an owner k
attaining a, L_k≤1−a<1−m; the other margins are at most two. Therefore

    m/(1−m)+3m/2 < Σ_i m/L_i ≤1.

Multiplication by 2(1−m)>0 gives (3m−1)(m−2)>0. Since m<1, it follows
that m<1/3. The zero-gap case satisfies the same strict upper bound.
Continuity of η and compactness of the full unit reward cube give an
attained worst value, which is also strictly below 1/3. This is an
existential universal numerical bound, with no effective uniform slack
asserted and no vanishing-gap conclusion.

## 8. Current limits and next check

There is no unresolved mathematical objection in the assigned strategic,
compactness, attachment, or harmonic portions. The separate algebraic review
checks that all 24 factors cover the complete-debt branches and form a
nonzero polynomial in the permitted reward coordinates; those calculations
are not independently repeated here. No part of this review certifies new
Lean implementation or the archive's regression execution.

The concrete next question is whether the resulting positive prescribed
singleton mass can produce a full-regret improvement while controlling
every player's post-response cap. Its singleton owner may quit at varying
dates, and its selected response need not retain that singleton mass. A
consumer must handle those distinctions explicitly; it is not supplied by
the reviewed reduction.
