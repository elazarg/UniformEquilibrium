# Exact one-jump and proper singleton-flow closure

Authors: `CODEX_BLINDSPOT`

Independent reviews:
[CODEX_HAHN](../feedback/CODEX_BLINDSPOT__ONE_JUMP_TWO_SORTED_ESSENTIAL_APS__BY_CODEX_HAHN.md),
[CODEX_SPINOZA](../feedback/CODEX_BLINDSPOT__ONE_JUMP_TWO_SORTED_ESSENTIAL_APS__BY_CODEX_SPINOZA.md)

## Exact statement

Fix a finite nonempty player set `I`.  A quitting game is given by terminal
rewards

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I.
\]

The terminal payoff of Never is zero.  For player `k` and owner `i`, write

\[
 s_k:=r_k(\{k\}),\qquad R_i:=r(\{i\}).
\]

Let `UE(r)` be the set of uniform-equilibrium payoff vectors.  Given a product
root `x` and an all-Continue continuation vector `y`, define

\[
 F_r(x,y)_k=
 \mathbb E_x\left[
  \mathbf 1_{\{Q\ne\varnothing\}}r_k(Q)
  +\mathbf 1_{\{Q=\varnothing\}}y_k
 \right].                                             \tag{1}
\]

Say that `x` is exact root Nash at `y` if, for every player `k` and every
replacement Bernoulli marginal `z_k`,

\[
 F_r(x,y)_k\ge F_r(x[k\leftarrow z_k],y)_k.            \tag{2}
\]

The following two closure statements hold against unrestricted complete
behavioral deviations.

**Exact product-root closure.** If `y\in UE(r)`, `x` satisfies (2), and
`v=F_r(x,y)`, then

\[
                         v\in UE(r).                    \tag{3}
\]

No positive-absorption or sure-quitter condition is imposed on `x`.

**Proper viable singleton-flow closure.** Fix an owner `i`, a mass
`0<p<1`, and vectors `y,z` such that

\[
 z=pR_i+(1-p)y,qquad z_i=s_i,                          \tag{4}
\]

and

\[
 z_k\ge s_k,qquad y_k\ge s_k\quad(k\in I).            \tag{5}
\]

If `y\in UE(r)`, then

\[
                         z\in UE(r).                    \tag{6}
\]

Consequently, if an exact root jump lands in a supplied compiled
singleton-flow/essential-APS component, the jump source is a uniform payoff;
and if one proper viable singleton-flow segment precedes that jump, its source
is also a uniform payoff.

## Conjecture-facing change

The existing essential-APS capstone compiles points of a supplied compact,
convex, terminal-free, unique-live singleton-flow component.  Its discrete
mesh excludes full jumps.  The exact product-root theorem above closes the
local semantic seam from any such compiled continuation payoff through one
arbitrary product-root Bellman jump.  The proper-segment theorem closes the
reverse finite order: one singleton-flow segment may lead into that jump.

This strictly replaces a proposed one-jump verifier by an actual
unrestricted-behavior compiler with a fixed target.  It does not produce the
base essential-APS component for an arbitrary game, and it does not prove
soundness or nonemptiness of an unrestricted alternating jump--flow greatest
fixed point.  Those producer and infinite-closure obligations remain open.

## Definitions and assumptions

A behavior deviation replaces one player's entire behavioral strategy.  It
may choose a different root marginal, a history- and time-dependent quitting
rule, and a different tail behavior.  All payoffs in the proof are terminal
expected payoffs.  Fixed-target terminal acceptance converts profiles whose
terminal exploitability and terminal-payoff error tend to zero into the
uniform finite-horizon equilibrium notion.

A terminal semantic pair `(u,b)` consists of the prescribed terminal payoff
`u` of one actual profile and its coordinatewise all-behavior best-response
cap `b`.  Its debt is `b-u`.  Prefixing by one product root acts on the full
pair, not only on `u`.

For the flow proof choose `M` with

\[
                         |r_k(S)|\le M                  \tag{7}
\]

for all players and nonempty terminal coalitions.  Conditions (5) are the
baseline-invariant version of the paper's nonnegative viability condition.
The strict inequality `p<1` ensures that the supplied continuation remains
reachable with positive probability.

No public correlation device is assumed.  Root actions are independent
product marginals.  Before absorption in the singleton mesh, the only public
history is a string of all-Continue actions.

## Source correspondence

The paper source is G. Ashkenazi-Golan, I. Krasikov, E. Rainer, and E. Solan,
*The APS approach for undiscounted quitting games*, International Journal of
Game Theory 55 (2026), article 19,
<https://doi.org/10.1007/s00182-026-00982-6>.

- Definition 2.4 restricts Flesch absorption paths to one active quitter at
  each continuous absorption-time point.
- Definition 2.9 gives sequential perfection through nonnegative
  continuation payoffs and an active-owner equality, in normalized
  coordinates.
- Lemma 3.2 and display (3) define the singleton-flow predecessor
  `T_i(E)=co({R_i}\cup E)\cap H_i\cap R_+^I`.
- Lemma 4.5 and display (6) give the owner-indexed essential APS operator.
- Theorem 4.10 characterizes its singleton-flow payoff class under the stated
  simple-circuit face-avoidance condition.

The paper has no macroscopic simultaneous/product-root jump clause and leaves
more general strategy families for future work.  The exact jump theorem here
is therefore new relative to that statement, while the proper segment uses
the paper's singleton-flow geometry with an arbitrary uniform-payoff tail.

The exact project interfaces are:

- `quittingRootSuccessorPayoff`, `quittingRootQuitPayoff`, and
  `quittingRootContinuePayoff` in
  `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`;
- `IsεQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/FirstBranch.lean`;
- `quittingTerminalSemanticPrefix`,
  `quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash`,
  `quittingTerminalSemanticPair_rootThenContinuation`, and
  `continuous_quittingTerminalSemanticPrefix` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff`
  and
  `quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- `quittingSegmentEssentialAPSPrefix` in
  `UniformEquilibrium/Quitting/EssentialAPS/Basic.lean`; and
- `quittingEssentialAPSPrefix_subset_segment_of_convex` in
  `UniformEquilibrium/Quitting/EssentialAPS/ConvexProgress.lean`.

The new content is the target-preserving exact-root closure argument, the
unrestricted proper-segment stopping calculation, and the exact demonstration
that jump images need not satisfy the convexity hypothesis of the existing
progress adapter.

## Proof

### Exact product-root closure

Fix `y\in UE(r)`, a product root `x` satisfying (2), and
`v=F_r(x,y)`.  Choose `eta_n\downarrow0`.  The checked tail-selection theorem
supplies actual tail profiles with semantic pairs `(u_n,b_n)` satisfying

\[
 \|u_n-y\|_\infty\le\eta_n,qquad
 0\le b_{n,k}-u_{n,k}\le\eta_n                         \tag{8}
\]

for every player.  Hence

\[
                         (u_n,b_n)\longrightarrow(y,y). \tag{9}
\]

Prefix each profile by the fixed root `x`.  Literal profile splicing has
semantic pair `T_x(u_n,b_n)`, where `T_x` is the checked semantic prefix map.
That map is continuous.  Exact root Nash gives the exact diagonal identity

\[
                         T_x(y,y)=(v,v).                \tag{10}
\]

Therefore

\[
                         T_x(u_n,b_n)\longrightarrow(v,v). \tag{11}
\]

The first coordinate of (11) gives terminal payoff convergence to the fixed
target `v`.  The difference of the two coordinates gives unrestricted
terminal exploitability tending to zero.  Fixed-target terminal acceptance
proves (3).

The diagonal cap in (10) is essential.  If only a tail payoff `y` is known
while the tail cap is strictly larger, root Nash checked at `y` does not
control the continuation deviation.  An all-Continue prefix, for instance,
retains the old continuation debt.

### Proper viable singleton-flow closure

Take a tail semantic pair `(u,b)` satisfying

\[
 \|u-y\|_\infty\le\eta,qquad
 0\le b_k-u_k\le\eta.                                  \tag{12}
\]

For an integer `N\ge1`, set

\[
 q=(1-p)^{1/N},\qquad h=1-q.                           \tag{13}
\]

Play `N` identical rows in which only owner `i` Quits, with probability `h`,
then play the tail.  Since `q^N=1-p`, the prescribed terminal payoff is

\[
                         U=pR_i+(1-p)u,                 \tag{14}
\]

and hence

\[
                         \|U-z\|_\infty\le\eta.         \tag{15}
\]

Since `p<1`, (4) implies `y_i=s_i`.  During the prefix the owner can obtain
only `s_i` by quitting, or at most `b_i` by reaching and deviating in the
tail.  Its terminal debt is at most `3 eta`.

Fix an outsider `k\ne i` and abbreviate

\[
 A=r_k(\{i\}),\qquad S=r_k(\{k\}),\qquad C=r_k(\{i,k\}). \tag{16}
\]

At row `t\in\{0,\ldots,N-1\}`, conditional on survival to that row, the ideal
prescribed continuation is

\[
 Y_t=(1-q^{N-t})A+q^{N-t}y_k.                          \tag{17}
\]

The remaining absorption mass lies in `[0,p]`, so `Y_t` lies on the segment
between `y_k` and `z_k`.  By viability, `Y_t\ge S`.  Replacing `y_k` by `u_k`
lowers the value by at most `eta`.  If `k` Quits at that row, its conditional
payoff is exactly `qS+hC`.  Its conditional gain is therefore at most

\[
 qS+hC-(S-\eta)=h(C-S)+\eta\le2Mh+\eta.                \tag{18}
\]

An arbitrary behavioral quitting rule induces a probability distribution
over its first quitting row and the event of reaching the tail.  Its payoff
is a convex combination of the pure-row values and a tail response, not a sum
of rowwise errors.  Reaching the tail adds at most `(1-p)eta`.  Thus every
outsider's terminal debt is bounded by

\[
                              2Mh+\eta.                 \tag{19}
\]

Let `N\to\infty` and `eta\to0`.  Then `h\to0`;
(15), (18), and (19) give terminal payoff convergence to `z` and unrestricted
terminal exploitability tending to zero.  Fixed-target terminal acceptance
proves (6).

Applying the exact-root theorem first and the proper-segment theorem second
proves the stated flow-before-jump corollary.  Finite induction also allows
any finite list of proper viable singleton segments before the single jump.

## Boundary tests

### Exact nonconvexity regression

Take two players, continuation `y=(0,0)`, and rewards

\[
 r(\{1\})=(-1,-1),\qquad
 r(\{2\})=(-1,-1),\qquad
 r(\{1,2\})=(1,1).                                    \tag{20}
\]

All-Never is an exact equilibrium, so `y\in UE(r)`, and `y` is viable relative
to the singleton baselines `(-1,-1)`.  If `p_i` is player `i`'s root Quit
probability, player 1's pure Quit-minus-Continue difference is `-1+3p_2`, and
symmetrically for player 2.  Mutual best response gives exactly

\[
                    (p_1,p_2)\in
   \{(0,0),(1/3,1/3),(1,1)\}.                          \tag{21}
\]

The corresponding Bellman payoffs are

\[
                    (0,0),\quad(-1/3,-1/3),\quad(1,1). \tag{22}
\]

All three are viable uniform payoffs by the exact-root theorem, but their set
is nonconvex: `(1/2,1/2)` lies between two of them and is absent.  This does
not prove that a convexified point is not a uniform payoff.  It proves that
convexification loses the selected exact root/continuation witness and that
the current convex-progress adapter cannot be applied to the jump image.

### Endpoint and order boundaries

- All-Continue is covered by the root theorem when its endpoint inequalities
  make it exact; it reduces to the identity.
- Sure first-stage absorption is also covered.  The semantic-pair proof never
  divides by root survival.
- The flow theorem requires `p<1`.  At `p=1`, a negative singleton owner may
  deviate to Never and obtain zero, so a viable algebraic terminal endpoint
  needs an additional implementation condition.
- A jump after a complete terminal-free unique-live component is not a second
  live phase: that component has divergent absorption mass and zero survival.
  The jump is unreachable and payoff-invisible.  Reverse order is meaningful
  at a finite cut, as proved above, or requires a new positive-survival limit
  semantics.

## Adapter and consumer

**Adapter.** The exact-root adapter takes a supplied continuation payoff `y`,
an explicit product root `x`, Bellman equality `v=F_r(x,y)`, exact root Nash
at that same `y`, and terminal approximating profiles for `y`.  It constructs
the actual profiles with `quittingRootThenContinuationProfile`.  The proper-
segment adapter takes an explicit owner, mass, viable endpoints, active
equality, and tail approximating profiles, and constructs the `N`-row
solo-owner mesh (13).

When `y` comes from the checked unique-live essential-APS capstone, these are
actual-data adapters from the component point to the new jump or segment
source.  No source theorem produces the component or the exact jump for an
arbitrary reward table.

**Consumer.** The checked downstream consumer is
`quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance`.  The
adapter outputs actual behavior profiles whose unrestricted terminal Nash
error tends to zero and whose terminal payoff tends to the fixed displayed
source target.  The consumer yields exactly `IsUniformEquilibriumPayoff none`
at that target.

**Two-sorted boundary.** A jump has no canonical active singleton owner.  A
faithful later carrier must distinguish `Flow(i,z)`, retaining one selected
segment continuation, from `Jump(v;x,y)`, retaining the product root, tail,
Bellman equality, and root Nash witness.  Flow-to-flow edges may use the
existing Flesch successor rule.  Flow-to-jump edges must retain the proper
segment witness instead of convexifying the jump payoff set.

## Lean handoff

The narrow suggested theorem shapes are:

1. `isUniformEquilibriumPayoff_rootSuccessor_of_isZeroRootNash`:
   from `y` uniform, `IsεQuittingRootNash reward y 0 root`, and the displayed
   `quittingRootSuccessorPayoff`, conclude that exact successor payoff is
   uniform.  Prove it using terminal tail selection, semantic-pair literal
   splicing, continuity, diagonal prefix equality, and target acceptance.
2. `isUniformEquilibriumPayoff_singletonArc_of_viable_proper`:
   from `y` uniform, `p\in Ioo 0 1`, the singleton arc equality, active-owner
   equality, and viability of both endpoints, conclude that the arc source is
   uniform.  The new internal lemma should identify the all-behavior cap of
   the finite solo-owner mesh with the maximum of the pure first-quitting-row
   values and the reached tail cap; (18)--(19) then give the estimate.
3. Add the two-player table (20) as a regression showing that exact jump
   payoff images do not preserve convexity.

Likely dependencies are the exact declarations named in Source
correspondence plus the existing pure-time/extremality infrastructure if it
simplifies the finite-mesh cap proof.  The implementation must construct
actual profiles; neither theorem should take its desired uniform-payoff
conclusion as a certificate field.

## Scope and nonclaims

- This packet proves supplied-object soundness, not an arbitrary-game
  producer.
- It proves one arbitrary product-root jump and finitely many proper viable
  singleton segments before it.  It does not prove unbounded alternation.
- It does not prove nonemptiness or executability of a greatest jump--flow
  fixed point.
- It does not provide public correlation or infer that convex combinations of
  jump payoffs are executable.
- It does not implement a jump after a positive-survival Zeno limit.
- It does not claim that every algebraic essential-APS terminal endpoint is
  executable when singleton baselines are negative.
- It does not decide the Fin4 conjecture.  The current arbitrary-game
  component/jump production and infinite semantic-closure problems remain.
