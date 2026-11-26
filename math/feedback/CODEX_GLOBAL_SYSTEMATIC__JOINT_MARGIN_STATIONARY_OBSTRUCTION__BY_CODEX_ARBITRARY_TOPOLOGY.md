# Review of the joint-margin stationary obstruction

Reviewer: CODEX_ARBITRARY_TOPOLOGY.

**Mathematical verdict: PASS.** No unresolved objection. This is an internal
ordinary-mathematics review, including an exact rational computation, not a
Lean check or export-gate approval.

Complete artifact reviewed:
[CODEX_GLOBAL_SYSTEMATIC__JOINT_MARGIN_STATIONARY_OBSTRUCTION.md](../notes/CODEX_GLOBAL_SYSTEMATIC__JOINT_MARGIN_STATIONARY_OBSTRUCTION.md),
SHA256:

    fb707a2927478e418f567ae8b817e2ed747854a712719e6fe660b7cd8b1f8855

Exact checker reviewed and executed:
[CODEX_GLOBAL_SYSTEMATIC__JOINT_MARGIN_STATIONARY_CHECK.py](../experiments/CODEX_GLOBAL_SYSTEMATIC__JOINT_MARGIN_STATIONARY_CHECK.py),
SHA256:

    e8b81ccf9b6073bbbe09b1067547f72fc09cb4fabef2af5d0ff6c2af661969a3

## Accepted conclusion and scope

The explicitly specified original game has every own singleton equal to1,
all four observer capacities strictly positive, no absorbing exact
finite-calendar equilibrium, and a positive full-regret floor on the entire
stationary class. It nevertheless has the stated period-three exact
terminal Nash profile and fixed uniform-equilibrium payoff(2,1,17,1).

This disproves the proposed implication from joint margin positivity to
stationary approximate existence. It does not exclude approximate
finite-calendar equilibria, refute Fin4, or claim to meet all arbitrary
counterexample-source conditions. The normal-form and limiting-profile
distinctions are preserved throughout.

## Raw table, capacities and boundary roots

I independently rebuilt all sixty native entries from the coalition rules.
Symbolic expansion reproduces every displayed Delta_i, passive P_i and
stationary numerator, including the row0 product threshold4/9. I also
recomputed the determinant, inverse column, positive image and core block
determinant. The R0 argument covers pivot-only, one-core, two-core and
three-core supports; the positive row0 sum removes pivot mass whenever a
core coordinate is positive.

The grand joining signs are exactly(5/4,-1,-1,-1). The affine capacity
calculations give Lambda0=1 and the three remaining values1/17, with
intersection8/17. Row-wise addition of1 preserves these differences.

I checked the entire sure-root census. For x=1, the three listed core
types are exhaustive and each gives a strictly negative pivot gap. The
negative pivot conclusion needs only v0>=0. Every actual original cap
has B0>=1, so the original-to-native continuation substitution supplies
this condition even after an unreachable all-Continue branch.

With a sure core owner and 0<x<1, pivot mixing imposes ab=4/9. The two
unit cases have the stated negative gap -5/18. With both remaining core
hazards interior, elimination gives36a^2-51a+20=0, whose discriminant is
-279. Unknown continuation coordinates disappear because an opponent is
sure. At x=0, cyclic forcing makes all three core hazards sure and then
the quiet pivot has positive gap.

An absorbing finite-calendar profile must reach a sure root. Exact
full-law Nash makes that root Nash with its actual continuation caps:
when an all-Continue branch is impossible, either its coefficient is zero
or the sure owner must still price a unilateral continuation deviation.
Thus the root census legitimately excludes this entire exact class.

## Stationary exclusion and exact computation

Solo hazards were checked for every positive size, not only sure quitting.
A core solo owner exposes the predecessor's gap16-15q>=1; a pivot solo
owner exposes a core observer's gap1/100+(99/100)q>0. The observer faces a
proper opponent, so adding1 to its absorbing rewards shifts both offers
equally. Original AllNever is itself exploitable by quitting for1.

At x=0 with all core hazards interior, the function T in(7) is symmetric
and strictly increasing. I checked both cyclic order cases in the note;
each really forces equality of all three hazards. The common root exceeds
4/5, so pivot Quit strictly improves on its Never payoff. An independent
rational interval check of the same boundary also found no root with
product at most4/9; this redundant scratch check is not a theorem input.

For the remaining fully mixed case, I independently expanded the original
formula(9) into C+vB-v^2D. The product constraint puts every core hazard
in[4/9,1], so the checker domain includes every candidate. Interval
addition, multiplication, squaring and reciprocal bounds are sound;
all denominators stay positive. Clipping the derived c interval at1
removes only infeasible values. Closed bisections cover their parents,
and every discarded feasible box has a gain interval excluding zero.

The unchanged checker completed with9589 boxes and the advertised PASS.
As a falsification test, changing only the product constant to1 introduces
the exact zero(v,a,b,c)=(1/2,1,1,1). The checker then raises its unresolved
box error rather than reporting exclusion. No floating output or numerical
search is relied upon in the accepted proof.

## Positive stationary regret floor and periodic equilibrium

I independently derived the compactness/R0 strengthening now included in
the note. At a nonzero limit with two active owners, all response endpoints
are continuous. A solo limit is excluded by the explicit outsider gap,
without assuming continuity of the solo owner's Never response. At zero,
the normalized hazard vector lies in the simplex; forced Quit gives
Gamma alpha>=0 and Never gives complementarity for alpha_i<1. When
alpha_i=1, the required equality follows from the zero diagonal. This
produces a forbidden nonzero R0 solution. The row shifts are used only
where prescribed play or the relevant opponents absorb surely.

For the period-three profile I checked each Bellman identity and each
Quit inequality directly at the three rotated continuation vectors. The
unrestricted-deviation argument is valid because any deviator faces at
least two hazard1/2 opportunities every three dates. The bounded residual
vanishes uniformly, all response payoffs shift by1, and finite-horizon
errors vanish uniformly over complete behavioral replacements. The fixed
profile and fixed payoff target therefore satisfy the stated UE contract.

The semantic target and terminal endpoint were checked against
`quittingUniformEquilibriumPayoffConjecture` in
`UniformEquilibrium/Quitting/Conjecture/Basic.lean` and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
No Lean source was edited or built.
