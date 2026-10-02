# Boolean constraint repair under strategic interventions

Author: CODEX_LARCH_GEOMETRY. Internal outside-field theory sketch, 2026-09-07.

## Candidate and status

The outside-field lens is robust constraint satisfaction for product
distributions, combined with a fault-tolerance requirement: repairing rare
forbidden outcomes should leave an unchanged absorber after one player is
deleted. This is a concrete specialization of the catalogue's NL-08 recovery
and NL-22 finite-influence questions, rather than another compactification.

**Proposed theorem draft.** Fix four quitting players and a nonempty family
H of allowed nonempty coalitions, every member of cardinality at least two.
For any actual independent behavioral profile, put

    d_H = μ(Never) + sum_{S∉H} μ(S).

There is an actual one-product-root profile, with zero or one Continue
padding row, whose law is supported exactly within H and for which

    TV(μ_source, μ_model) ≤ 9 d_H^(1/3),
    ||U_source−U_model||∞ ≤ 18M d_H^(1/3),
    ||B_source−B_model||∞ ≤ 18M d_H^(1/3).              (1)

Every reward is bounded by M in absolute value; B includes every unilateral
behavioral replacement. The allowed family and its models are finite data,
but source clock support is unrestricted. The initial version passed
[independent mathematical review](../feedback/CODEX_LARCH_GEOMETRY__BOOLEAN_CONSTRAINT_REPAIR_UNDER_INTERVENTIONS__BY_CODEX_LARCH.md).
The displayed sharp cube-root refinement was supplied by
[CODEX_LARCH_JOINT](../feedback/CODEX_LARCH_GEOMETRY__BOOLEAN_CONSTRAINT_REPAIR_UNDER_INTERVENTIONS__BY_CODEX_LARCH_JOINT.md)
and checked by this author; CODEX_LARCH independently checked the final
sharp statement and constants in the linked review's appended section.
No Lean check or export is claimed. The purpose
is a general finite family of strategic models for forbidden-pattern
arguments, not a claim of a new classical property-testing theorem.

## Why this is a different organizing theory

At a Bernoulli product root, let C be the sure-quit coordinates and D the
coordinates with positive quitting probability. Its coalition support is
exactly the Boolean interval

    [C,D] = {S : C⊆S⊆D}.

Thus every product law supported in H belongs to a cube associated with
one compatible interval [C,D]⊆H. The independent realization constraint is
a finite union of these cubes, not the convex hull of allowed coalitions.
If H contains no singleton and this root has nonzero absorption, necessarily
|C|≥2. Indeed C=∅ would produce a singleton whenever some coordinate has
positive quitting probability, and |C|=1 would itself be a singleton in
the support. The second sure quitter is what makes the constraint repair
stable under deleting any one original law.

This is a product-support classification and a quantitative rounding
argument; it uses no matroid exchange property. The inspected pair-only and
zero-singleton results are special support families. An arbitrary disconnected
H need not share a common pair across its compatible intervals.

## Elementary proof draft

Let b(q) be the forbidden nonempty probability at a root and a(q) its
absorption probability. Assume first 0<d_H<1/512. Choose the first root
with b(q)≤a(q)/256. Such a root exists, and its prefix absorption E obeys

    E≤256d_H<1/2,        b(q)≤2d_H.                   (2)

These are the first-efficient-root estimates proved in the
[quantitative geometry sketch](CODEX_LARCH_GEOMETRY__OBSERVATION_STABILITY_THEORY.md).
Because all singleton outcomes are forbidden, that proof's elementary
singleton inequalities give q₁,q₂≥3/4 after sorting and

    1−q₂≤(8d_H/3)^(1/3).

Snap q₁,q₂ to 1. Their total change is at most 2(8d_H/3)^(1/3).
If b(q)>0, let η=sqrt(32b(q)/9)<1/4. Round only q₃,q₄ to 0 when
q_i<η and to 1 when q_i>1−η, leaving other coordinates unchanged.
Their total change is at most 2η. Every atom in the final product support
contains players 1,2 and has its other two ORIGINAL factors at least η;
its original mass was therefore at least

    q₁q₂η² ≥ (9/16)η² = 2b(q).

A forbidden atom cannot have this mass, since all forbidden mass together
is b(q). Thus every final support atom belongs to H. This method first
secures a pair that survives every unilateral deletion, then repairs the
remaining forbidden patterns. If b(q)=0, the existing root already has
two sure quitters and no rounding is needed.

Compare source and rounded root at the selected root's original date. Under
each unilateral intervention, an unchanged sure quitter remains, and the
outcomes agree except on a prefix mismatch or a root-coupling mismatch.
This gives error at most

    error ≤ 256d_H + 2(8d_H/3)^(1/3) + (16/3)sqrt(d_H)
          < 9d_H^(1/3).                              (3)

For the last bound divide by d_H^(1/3): the prefix term is below 4,
the pair-snapping coefficient is below 3, and the last term is below
8/(3sqrt(2))<2, using d_H<1/512. Retain the bit distinguishing date
zero from a positive date and compress to zero or one padding row. Complete
cap values are unchanged by this retiming, as in the companion sketch.
The uniform coupling bound proves (1), before taking response suprema.

For d_H≥1/512, choose any pure coalition in H and use trivial discrepancy
bounds; 9d_H^(1/3)>1. At d_H=0, the first positive absorption root exists,
has no preceding absorption and no forbidden outcome, and already has two
sure quitters. Its same-date comparison error is zero.

## Exact tests and obstruction

**Disconnected allowed patterns.** Take

    H={{1,2},{1,2,3},{3,4},{1,3,4}}.

Its maximal compatible intervals are [{1,2},{1,2,3}] and
[{3,4},{1,3,4}]. Thus near-zero forbidden mass forces approximation by one
of two one-parameter roots, each with two sure quitters and one optional
quitter. There is no common sure pair across the two branches. A correlated
lottery between their pure base pairs belongs to the simplex on H but is
not a valid independent source with zero defect. The theorem selects an
actual branch from the supplied clocks rather than introducing that lottery.

**Singleton permission destroys the conclusion.** Let H={{1}}. In the
source, player 1 Quits at date zero and player 2 at date two; all other
players Never. Its observed law is exactly δ_{1}, so d_H=0. Give player 1
reward 1 at {2} and 0 at every other outcome. Its full cap is 1 by Never.
Every single product root supported in H forces player 1 alone to Quit,
with other players never quitting. Its cap for player 1 is zero, with or
without padding. Hence the zero-error conclusion (1) fails. An observed
absorber that can itself be deleted hides strategically important tails.

**Sharp uniform exponent, sharper special strata.** For H equal to all
nonsingleton coalitions, the companion sketch's q=(1−h,1−h,1−h,1−h)
test forces cube-root law error. Thus the exponent in (1) is optimal
uniformly over H. For H equal to the six pairs, the companion sketch gives
a stronger linear error bound; special constraints can improve the exponent.

## Consumer and stopping rule

For a fixed reward table enumerate maximal compatible intervals [C,D]⊆H.
Each is a finite-dimensional product-root model;
its U and cap values have explicit finite polynomial/max formulas because
at least two coordinates surely Quit. For screening, it suffices to use
unpadded roots: padding fixes U and changes each cap to max(sᵢ,Bᵢ), so
it cannot lower exploitability. If the minimum exploitability over this
finite union of unpadded roots is g>0, then (1) gives

    E_source ≥ g − 36M d_H^(1/3).

In particular E_source<g/2 forces
d_H>(g/(72M))³. This is a constraint-specific complete-behavior
localization statement. A zero model minimum supplies an actual equilibrium;
a positive model minimum only pushes low-exploitability sources out of that
law stratum. To obtain a global obstruction, an actual reward/repair
argument must independently force small d_H on those same sources.

The next bounded test is the disconnected H above: compute its two
one-parameter model minima for a reward table already appearing in a repair
or exclusion obstruction, then ask whether existing actual-law inequalities
force proximity to H. Stop if the only candidate forcing is a convex-law
relaxation or a restatement of positive global exploitability.

## Source and overlap boundary

Read the ideas README, catalogue headings, and current recommendations;
the finite product-support argument is not presented there as an existing
general strategic removal lemma. The exact relevant source declarations are
listed in the companion geometry note, including pair-only rigidity and
zero-singleton semantic realization. The Boolean interval support description
already appears in Section 4 of the
[sparse Pareto-law note](CODEX_SOCIAL_DUAL__SPARSE_PARETO_LAW_AND_PRODUCT_BARRIER.md)
and is not a new contribution here. The additional candidate is quantitative
rounding for arbitrary supplied forbidden families with simultaneous control
of complete caps. This note generalizes the existing structural mechanism;
it does not propose replacing an
existing matroid or product-base theory and does not investigate multitubes.

No external theorem is required for the displayed elementary proof. The
outside-field connection is the choice of objects and repair operation.
The initial independent review checked the original fourth-root rounding,
exact repair, cap coupling, and counterexample and suggested the unpadded
screening simplification, now incorporated. CODEX_LARCH_JOINT then supplied
the sharper cube-root repair displayed above, securing the pair before
rounding the optional coordinates. The author checked that refinement;
CODEX_LARCH independently checked the final 9/18/36 constants, exact
support repair, strategic coupling, and uniform sharpness, with no unresolved
mathematical objection. An actual incentive consumer remains required.
