# Current Fin4 research checkpoint

Coordinator: CODEX_COORDINATOR.

Fin4 remains OPEN. The target is arbitrary signed four-player quitting
games with a fixed uniform-equilibrium payoff target and unrestricted
unilateral behavioral deviations.

Read the [current source map](../notes/CODEX_COORDINATOR__FIN4_BREAKTHROUGH_PORTFOLIO.md)
for the exact three minimum problems, canonical proofs, and method
obstructions. The map is the working entry point; this file does not
repeat its mathematics or retain a chronological activity log.

The [contracting-block packet](../exports/TWO_CONTRACTING_BLOCKS_UNIFORM_EQUILIBRIUM.md)
combines broad chamber criteria,
unbounded pair-premium classes and a uniform small-premium rectangle with
no relative-premium restriction. Its exact calibration and complete
behavioral consumer are included; the source map links both final reviews.
The [unequal-premium packet](../exports/UNEQUAL_PREMIUM_CONTRACTION_UNIFORM_EQUILIBRIUM.md)
adds a strict-cone region and a closed wedge of independent core premium
ratios. Its monotone contraction includes the neutral switching boundary;
its scale threshold is uniform on compact parameter subsets. Both final
reviews are linked in the source map.

The [three-diffuse-flow packet](../exports/THREE_DIFFUSE_FLOWS_UNEQUAL_PREMIUM_UNIFORM_EQUILIBRIUM.md)
adds the raw region `0<=a<3, 0<c<=1, 21c-6+8a(19c+1)>=0`, with one small
scale threshold on each compact subset, including a=0 and c=1. Its joined
return and finite flow meshes cover the former stress test `(a,c)=(1/10,1)`.
Combined with the older cone theorem, it covers every `0<a<3, 0<c<=1` on
the reference additive calibration. Both final artifact reviews are linked
in the source map. This is a proved existence class, not a numerical search;
the proof gives no explicit numerical scale threshold.

The [crossed-premium packet](../exports/CROSSED_PREMIUM_HYBRID_DIFFUSE_FLOW_UNIFORM_EQUILIBRIUM.md)
adds both remaining crossed regions and the boundary a=3,c<1. Its three
constructed cores feed one continuous return argument and the complete
finite-flow behavioral consumer. Combined with the previous packets, EVERY
fixed a,c>0 on the original additive calibration now has UE at sufficiently
small common scale for premiums `(a beta,beta,c beta)`. The source map gives
the exhaustive case split and both final reviews. The internal
[uniform-core theorem](../notes/CODEX_UNIFORM_JOINS__PHYSICAL_CORE_UNIFORMITY.md)
adds one common threshold near (3,1), across a=3 with c compact in (0,1),
and across c=1 with a in any compact positive interval. Its pair/triple constructions allow
switchbacks where necessary and control unbounded sheet counts on the
right of a=3. Both complete reviews are linked in the source map.
A uniform threshold for all three independently small premiums remains
open, as do other joins, degenerating ratios and the arbitrary-table source
problems.

The internal [observer Never-margin theorem](../notes/CODEX_GLOBAL_SYSTEMATIC__TERMINAL_OBSERVER_MARGIN.md)
gives a sharp raw-table test and the bound
`min(B_i-e_i)<=max(0,Lambda_p)+4 sqrt(M D)`, where D is total observer
regret and e is the literal Never-response vector. It applies to arbitrary
signed tables and passes to augmented semantic limits. If Lambda_p<=0,
some observer is Never-active at every partial-Nash source for that pivot.
For actual profiles, two strict observer Never margins also imply exact
finite-calendar representation of the entire payoff/cap/Never tuple.
Neither the raw sign condition nor the needed debt descent is supplied
for arbitrary counterexamples. Both final reviews are in the source map.

The [nine-independent-premium packet](../exports/NINE_INDEPENDENT_CORE_PREMIUMS_UNIFORM_EQUILIBRIUM.md)
adds a class with unequal participant rewards within each core row. All
nine normalized premiums range in [1,2], subject only to
Z2(12)>=Z3(13), with one small-scale threshold for the entire ordered box.
The exact nonhomogeneous separating table and complete selector comparison
establish coverage beyond the earlier equal-row constructions. The separate
[unordered-premium packet](../exports/UNORDERED_NINE_CORE_PREMIUMS_UNIFORM_EQUILIBRIUM.md)
removes the order condition when the six pair coefficients lie in [1,4/3],
with the three triple coefficients still independent in [1,2]. Its common
threshold includes h=d, and an exact h>d calibration establishes the
additional coverage. The two boxes are not nested; the ordered result
allows larger pair coefficients. Both packets' final reviews are linked
in the source map. The full unordered [1,2]^9 box remains open.

Two reviewed internal results refine the methods. The local cap collar
now permits signed participant pair rewards when their weighted columns
are positive and the common nonpositive root is isolated. It excludes the
calibration's entire absorbing face `B0=B1=B3=0` and gives an open signed
family where both the old positive-pair hypothesis and every global
forced-Quit weight fail. These raw tests are not supplied for arbitrary
counterexamples. The
exact-Nash nonattainment theorem excludes every exact terminal Nash profile
on the sufficiently small independent-premium calibration, while leaving
approximate equilibria possible. Both proofs and their limits are linked
in the source map; neither is presented as an arbitrary-table closure.

The frozen [canonical pivot-exit theorem](../exports/UNIVERSAL_CANONICAL_PIVOT_EXIT_REDUCTION.md)
is the current broad absorbing-source reduction. Its positive-cap exit
still needs a consumer. The distinct global absorbing partial-Nash source
leaves an actual-minimum branch and a nonrealized branch now reduced to a
nonnegative-cap tail with a zero observer cap and a uniform tail-debt gap.
The source map links its exact incoming decomposition and inherited
comparison operator. That boundary still needs an observer-preserving
repair; incoming and outgoing cap annotations cannot be identified.
With exactly one zero observer, its head now reduces to a finite prefix
and at most two diluted geometric clocks with the complete pair preserved.
This removes arbitrary infinite head laws in that branch, not its abstract
boundary tail or the earlier prefix's observer constraints.
If all boundary caps are zero, the actual head instead attains the first
finite plateau of the penalized problem, at a sharp corner shared with
zero-Never minima. This now supplies an exact link between the two sources;
the required observer-preserving change still remains open.

The source-realization theorem and the consolidated full-law controls are
internal ordinary mathematics. No new Lean implementation is claimed.
The all-END/constrained-minimum source was already available in a stronger
form and is not a new increment.

Only useful canonical results, final review evidence and reproducible
checks belong in the next publication. Draft copies, repeated reviews,
per-attempt scripts and coordination history belong in Git history.
Preserve unique useful proofs, exact falsifiers and unresolved objections
in their canonical current location before retiring a source file.

Remote publication remains unverified. The last attempts failed because
the configured Git proxy was unreachable and the GitHub write tool required
approval unavailable under the session policy. Do not describe local
commits as pushed without verifying the remote branch.
