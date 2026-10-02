# One-jump, two-sorted essential APS

Author: `CODEX_BLINDSPOT`

## Status

Mathematical supplied-object result, 2026-09-03.  Nothing in this note is
Lean-checked, and no arbitrary-game producer is claimed.

The bounded splice problem has a positive answer.  There is a natural exact
product-root predecessor operation `J`, and:

1. an exact `J`-jump in front of any supplied uniform-equilibrium payoff is
   again a uniform-equilibrium payoff;
2. a proper viable singleton-flow segment in front of such a jump is again a
   uniform-equilibrium payoff; and
3. therefore one jump followed by a currently compiled unique-live essential
   APS component, and one finite singleton-flow segment followed by such a
   jump, both compile against unrestricted behavioral deviations.

The proof of (1) uses the payoff/cap semantic pair and works for an arbitrary
product root, with no sure-absorption hypothesis.  The proof of (2) contains
an exact stopping calculation.  Its collision error is the **maximum**
one-row error `2 M h`, not a sum of `N` such errors.

There is also an exact obstruction to treating the resulting construction as
the old one-sorted compact-convex APS fixed point.  Even when the continuation
is a viable uniform-equilibrium payoff, the set of exact product-root jump
payoffs can be nonconvex.  A two-player three-terminal table below gives the
exact jump image

\[
 \{(0,0),(-1/3,-1/3),(1,1)\}.
\]

Consequently, the convex-progress theorem used by the current essential APS
compiler cannot simply be reapplied after adjoining jumps.  A sound combined
operator must retain a jump tag/witness and use a segment relation on edges
entering the jump stratum.  Moreover, putting a jump "after" a complete
terminal-free unique-live component is not a genuine second order: the
component has divergent absorption mass and zero surviving probability.  A
reverse-order jump must occur at a finite cut (or at a new transfinite/Zeno
boundary not represented by the present natural-number execution).

Thus this note supplies a formalization-ready **one-jump compiler**, not a
soundness theorem for the greatest fixed point of the unrestricted
jump--flow operator.  The remaining high-value question is whether a
jump-budgeted compact carrier admits coherent selection without convexifying
the jump witnesses.

## 1. Exact question

Fix a finite nonempty player set `I`.  A quitting game is given by terminal
rewards

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow \mathbb R^I.
\]

The terminal payoff of Never is zero.  For player `k` write

\[
 s_k:=r_k(\{k\}),\qquad R_i:=r(\{i\}).
\]

For a product root `x=(x_k)_{k\in I}`, let `x_k` be a Bernoulli law on
`{Continue,Quit}`.  Given an all-Continue continuation vector `y`, define

\[
 F_r(x,y)_k
 =\mathbb E_x\!
  \left[
   \mathbf 1_{\{Q\ne\varnothing\}}r_k(Q)
    +\mathbf 1_{\{Q=\varnothing\}}y_k
  \right].                                      \tag{1.1}
\]

The exact root condition is

\[
 F_r(x,y)_k\ge
 F_r(x[k\leftarrow z_k],y)_k
 \quad\text{for every player }k
 \text{ and every Bernoulli law }z_k.           \tag{1.2}
\]

This is `IsεQuittingRootNash reward y 0 x`.  It is important that (1.2) is
tested at the same continuation coordinate as (1.1).

The two requested splice tests are:

- **jump then flow component:** `v=F_r(x,y)`, (1.2) holds, and `y` is a payoff
  compiled by a supplied unique-live essential APS component;
- **flow then jump:** for an owner `i` and `0<p<1`,

  \[
    z=pR_i+(1-p)v,                               \tag{1.3}
  \]

  where `v` is the source payoff of a sound jump, `z_i=s_i`, and both `z`
  and `v` dominate the singleton baselines coordinatewise.

The conclusion in each case is that the displayed source vector is one fixed
uniform-equilibrium payoff.  The approximating behavior profile may depend
on the requested accuracy, but deviations are unrestricted complete
behavioral strategies.

## 2. Narrow sources inspected

### Paper

I checked G. Ashkenazi-Golan, I. Krasikov, E. Rainer, and E. Solan,
*The APS approach for undiscounted quitting games*, International Journal of
Game Theory 55 (2026), article 19,
<https://doi.org/10.1007/s00182-026-00982-6>.

- Definition 2.4 defines a Flesch absorption path: exactly one player quits
  at each continuous absorption-time point.
- Definition 2.9 says that a sequentially perfect FAP has nonnegative
  continuation payoffs and gives payoff zero to the currently active player,
  under the paper's singleton normalization.
- Lemma 3.2 and display (3) give the singleton-flow predecessor
  `T_i(E)=co({R_i}\cup E)\cap H_i\cap R_+^I`.
- Lemma 4.5 and display (6) restrict the continuation to Flesch successors
  and define the owner-indexed essential APS operator.
- Theorem 4.10 identifies the largest essential-APS sets with SFAP payoffs
  under finite simple-circuit face avoidance.  Its proof constructs an
  ordinary sequence of singleton-flow arcs with absorption tending to one.

The paper does not contain macroscopic simultaneous/product-root jumps.  It
explicitly leaves extension to more general strategy families for future
work.  Therefore the jump clause below is an extension, not a restatement of
Theorem 4.10.

### Project declarations

I inspected the following narrow interfaces.

- `quittingEssentialAPSPrefix`,
  `quittingSegmentEssentialAPSPrefix`,
  `quittingEssentialAPSSuccessorSet`, and
  `quittingEssentialAPSOperator` in
  `UniformEquilibrium/Quitting/EssentialAPS/Basic.lean`.
- `quittingEssentialAPSPrefix_subset_segment_of_convex` and
  `quittingEssentialAPSPrefix_eq_segment_of_convex` in
  `UniformEquilibrium/Quitting/EssentialAPS/ConvexProgress.lean`.
- `QuittingEssentialAPSCarrierEdge` and
  `quittingEssentialAPSCarrier_execution_of_segmentClosed` in
  `UniformEquilibrium/Quitting/EssentialAPS/SegmentClosedExecution.lean`.
- `quittingEssentialAPS_isUniformEquilibriumPayoff_of_terminalFree_unique_live_adaptiveMesh`
  in
  `UniformEquilibrium/Quitting/EssentialAPS/AdaptiveMeshUniformPayoff.lean`.
- `quittingRootSuccessorPayoff`, `quittingRootQuitPayoff`, and
  `quittingRootContinuePayoff` in
  `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`, and
  `IsεQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/FirstBranch.lean`.
- `quittingTerminalSemanticPrefix`,
  `quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash`,
  `quittingTerminalSemanticPair_rootThenContinuation`, and
  `continuous_quittingTerminalSemanticPrefix` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
- `exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff`
  and
  `quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

The load-bearing existing distinction is already stated in `Basic.lean`:
the full APS prefix convexifies an arbitrary continuation set, while the
segment prefix retains one actual continuation.  The converse from full
prefix to segment is proved only for a nonempty convex continuation set.

## 3. The exact jump operator, including the cap condition

Let `UE(r)` denote the set of uniform-equilibrium payoffs.  For
`E\subseteq\mathbb R^I`, define

\[
 \mathcal J_r(E):=
 \left\{
  v:\begin{array}{l}
  \text{there are }y\in E\text{ and a product root }x\text{ such that}\\
  v=F_r(x,y),\quad x\text{ satisfies (1.2) at }y
  \end{array}
 \right\}.                                      \tag{3.1}
\]

There is a useful semantic-pair version of the same definition.  A terminal
semantic pair is `(u,b)`, where `u` is prescribed payoff and `b` is the
all-behavior best-response cap.  Let `T_x` be the exact root-prefix action on
semantic pairs.  Then the jump conditions imply

\[
        T_x(y,y)=(v,v).                          \tag{3.2}
\]

This is precisely
`quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash`.  Equation (3.2)
is the cleanest way to remember the **cap condition**: the root must send a
diagonal continuation payoff/cap to a diagonal current payoff/cap.  Merely
requiring the Bellman equation `v=F_r(x,y)` is not enough.

All product roots are admitted.  In particular, no positive absorption and
no sure-quitter hypothesis is present.  At the all-Continue root, the jump is
the identity whenever its root inequalities hold.

### Proposition 3.1: exact jump closure of a supplied uniform payoff

**Claim (proved below).**

\[
                \mathcal J_r(UE(r))\subseteq UE(r).       \tag{3.3}
\]

#### Proof

Fix `y\in UE(r)`, a product root `x` satisfying (1.2), and
`v=F_r(x,y)`.  Choose `eta_n\downarrow0`.  By
`exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff`,
there is a tail behavior profile `sigma_n` such that

\[
 \sigma_n\text{ is terminal }\eta_n\text{-Nash},\qquad
 \|u_n-y\|_\infty\le\eta_n,                     \tag{3.4}
\]

where `u_n` is its prescribed terminal payoff.  Let `b_n` be its
all-behavior best-response cap.  The prescribed strategy itself is an
admissible response and terminal `eta_n`-Nash bounds every response, so

\[
             0\le b_{n,k}-u_{n,k}\le\eta_n       \tag{3.5}
\]

for every player.  Hence the semantic pairs converge:

\[
                 (u_n,b_n)\longrightarrow(y,y). \tag{3.6}
\]

Prefix `sigma_n` by the fixed root `x`.  Literal profile splicing and the
semantic prefix theorem give its exact semantic pair as

\[
                 T_x(u_n,b_n).                  \tag{3.7}
\]

The map `T_x` is continuous, while exact root Nash gives (3.2).  Therefore

\[
                 T_x(u_n,b_n)\longrightarrow(v,v).       \tag{3.8}
\]

The first coordinate of (3.8) says that the prefixed terminal payoffs tend to
`v`; the difference of the two coordinates says that their unrestricted
terminal exploitability tends to zero.  The fixed-target terminal acceptance
theorem now gives `v\in UE(r)`.  This proves (3.3).  Notice that the proof did
not use sure absorption at the first root.  `□`

### Why the cap clause is load-bearing

Suppose one knows only that a tail has prescribed payoff `y`, but its cap is
`b>y` in one coordinate.  Even an all-Continue root leaves that debt in
place: the exact formula
`quittingTerminalSemanticPrefix_allContinue_eq` replaces the current cap by
the maximum of the singleton payoff and the old cap.  Root Nash checked at
`y` does not control a continuation deviation worth `b`.  Proposition 3.1
works because a uniform payoff supplies profiles with **both** coordinates
converging to `y`, not merely profiles whose own payoffs converge to `y`.

## 4. A proper singleton-flow prefix in front of a jump

The following local result is independent of the Flesch successor graph.  It
is the exact game-semantic fact needed when a singleton-flow edge ends at a
macroscopic jump rather than at another singleton-flow owner.

### Proposition 4.1: one proper viable flow segment preserves `UE`

Let `i` be an owner and let `0<p<1`.  Suppose

\[
 z=pR_i+(1-p)y,                                  \tag{4.1}
\]

and assume

\[
 z_i=s_i,\qquad z_k\ge s_k,qquad y_k\ge s_k
 \quad(k\in I).                                  \tag{4.2}
\]

If `y\in UE(r)`, then `z\in UE(r)`.

This is a supplied-object compiler.  It claims neither that such a segment
exists for arbitrary game data nor that a full convex-hull prefix has a
one-continuation representation.

#### Proof

Choose `M` with `|r_k(S)|\le M` for every terminal coalition and player.
Let a tail profile have semantic pair `(u,b)` satisfying

\[
 \|u-y\|_\infty\le\eta,qquad
 0\le b_k-u_k\le\eta.                            \tag{4.3}
\]

Such profiles exist for a sequence `eta\downarrow0` by the same argument as
in Proposition 3.1.

For an integer `N\ge1`, put

\[
 q=(1-p)^{1/N},\qquad h=1-q.                     \tag{4.4}
\]

Play `N` identical rows in which only owner `i` quits, with probability `h`,
and then play the supplied tail.  Since `q^N=1-p`, the exact prescribed
terminal payoff is

\[
 U^{N,\eta}=pR_i+(1-p)u.                         \tag{4.5}
\]

In particular,

\[
       \|U^{N,\eta}-z\|_\infty\le\eta.           \tag{4.6}
\]

Because `p<1`, the owner equality in (4.2) and (4.1) implies `y_i=s_i`.
During the block the owner can obtain only `s_i` by quitting or at most
`b_i` by reaching and deviating in the tail.  Equations (4.3)--(4.5) therefore
bound the owner's debt by `3 eta`.

Now fix an outsider `k\ne i` and abbreviate

\[
 A=r_k(\{i\}),\quad S=r_k(\{k\}),\quad
 C=r_k(\{i,k\}).                                 \tag{4.7}
\]

At row `t\in\{0,\ldots,N-1\}`, conditional on survival to that row, the
ideal prescribed continuation value is

\[
 Y_t=(1-q^{N-t})A+q^{N-t}y_k.                   \tag{4.8}
\]

The remaining absorption mass `1-q^{N-t}` lies between `0` and `p`.
Consequently `Y_t` lies on the segment between `y_k` and `z_k`.  By (4.2),

\[
                         Y_t\ge S.               \tag{4.9}
\]

Replacing `y_k` by `u_k` changes (4.8) by at most `eta`.  Thus the actual
prescribed value at row `t` is at least `S-eta`.  If player `k` quits at that
row, its conditional payoff is exactly

\[
                         qS+hC.                  \tag{4.10}
\]

The conditional gain from (4.10) is therefore at most

\[
 qS+hC-(S-\eta)=h(C-S)+\eta\le2Mh+\eta.          \tag{4.11}
\]

Quitting after any randomized history cannot do better.  Before absorption,
the only observed history is a string of all-Continue actions; a behavioral
quitting rule is a probability distribution over the first quitting row and
the event of reaching the tail.  Its terminal payoff is a convex combination
of the pure-row values (4.10) and a tail response.  Reaching and deviating in
the tail gains at most `(1-p)eta`.  Hence the outsider's complete behavioral
deviation debt is bounded by

\[
                         2Mh+\eta.               \tag{4.12}
\]

Finally choose `N\to\infty` and `eta\to0`.  Equation (4.4) gives `h\to0`,
while (4.6) gives terminal payoff convergence to the fixed target `z` and
(4.12) gives terminal exploitability convergence to zero.  Fixed-target
terminal acceptance proves `z\in UE(r)`.  `□`

### Important endpoint qualification

The proof requires `p<1`.  At `p=1` the continuation is never reached, and a
negative singleton reward need not be enforceable: the owner can play Never
and obtain terminal payoff zero.  Thus the viable algebraic terminal clause
`R_i\in quittingEssentialAPSTerminal` is not by itself a uniform-payoff
compiler in baseline-invariant coordinates.  One needs, for example,
`0\le s_i`, or a separately supplied terminal implementation.  This is one
reason the current strongest essential-APS capstone assumes terminal freedom.

The endpoint issue does not affect a genuine flow--jump splice, where the
jump must be reached with positive probability and hence `p<1`.

### Corollary 4.2: reverse-order splice

Let `v\in\mathcal J_r(UE(r))`.  If a displayed `z` is related to `v` by
(4.1)--(4.2) with `0<p<1`, then

\[
                         z\in UE(r).              \tag{4.13}
\]

Indeed Proposition 3.1 first gives `v\in UE(r)`, and Proposition 4.1 then
gives (4.13).  By finite induction, any **finite** list of proper viable
singleton segments can be placed before the one jump.

No Flesch successor inequality is needed on the last flow-to-jump edge.  The
root Nash inequalities at the tagged jump replace the singleton-successor
sign rule.  If one forces the jump payoff into an ordinary owner-indexed APS
fiber, one silently assumes an active singleton owner that a simultaneous
product root need not possess.

## 5. A two-sorted jump--flow operator

A product-root jump is not naturally labelled by one active quitter.  The
minimal faithful state space therefore has two sorts:

- `Flow(i,v)`, carrying the active singleton owner `i`; and
- `Jump(v;x,y)`, carrying the product root, its continuation payoff, and the
  exact witness (1.1)--(1.2).

For an owner-indexed family `E=(E_i)` and a jump family `D`, define the
following set-level operator.  First,

\[
 \operatorname{Jump}_r(E)
     :=\mathcal J_r\!\left(\bigcup_{j\in I}E_j\right).     \tag{5.1}
\]

For the flow coordinate use

\[
\begin{split}
 \operatorname{Flow}_{r,i}(E,D):={}&
    \operatorname{Terminal}_{r,i}\\
 &\cup
   \operatorname{FullPrefix}_{r,i}
     \left(\bigcup_{j\in S_i}E_j\right)\\
 &\cup
   \operatorname{SegmentPrefix}^{<1}_{r,i}(D).           \tag{5.2}
\end{split}
\]

Here the first two terms are the existing essential APS clauses.  The final
term consists of (4.1)--(4.2) with `y\in D` and `0\le p<1`; it deliberately
uses one selected continuation, not the convex hull of `D`.  The full
two-sorted operator is

\[
 \mathfrak O_r(E,D)
 =\left(
    (\operatorname{Flow}_{r,i}(E,D))_{i\in I},
    \operatorname{Jump}_r(E)
  \right).                                      \tag{5.3}
\]

At witness level the edge types are:

\[
\begin{array}{ccl}
 \mathrm{Flow}(i,z)&\longrightarrow&\mathrm{Flow}(j,y),
       \quad j\in S_i,\ z=pR_i+(1-p)y;\\
 \mathrm{Flow}(i,z)&\longrightarrow&\mathrm{Jump}(v;x,y),
       \quad z=pR_i+(1-p)v;\\
 \mathrm{Jump}(v;x,y)&\longrightarrow&\mathrm{Flow}(j,y),
       \quad y\in E_j,\ v=F_r(x,y),\ x\in NE_r(y).
\end{array}                                      \tag{5.4}
\]

This is the promised full jump--flow essential APS **operator definition**.
It is monotone set-theoretically.  However, the supplied-object theorem proved
here applies only to the rank-one grammar

\[
 E\quad\leadsto\quad \operatorname{Jump}_r(E)
 \quad\leadsto\quad
 \operatorname{SegmentPrefix}^{<1}_r
       (\operatorname{Jump}_r(E)),               \tag{5.5}
\]

where every point of the base `E` has already been compiled.  It does not
assert that the greatest fixed point of (5.3) is executable.

### Theorem 5.1: the requested supplied-object compiler

Assume the hypotheses of
`quittingEssentialAPS_isUniformEquilibriumPayoff_of_terminalFree_unique_live_adaptiveMesh`
for a supplied compact convex unique-live component, and let `E_i` be its
greatest-family fibers.  Then:

1. every point of every `E_i` is in `UE(r)` by that checked capstone;
2. every point of `Jump_r(E)` is in `UE(r)` by Proposition 3.1; and
3. every point in a proper viable segment prefix of `Jump_r(E)` is in
   `UE(r)` by Proposition 4.1.

Thus one arbitrary exact product-root jump followed by the component, and
one proper singleton-flow segment followed by the jump and component, are
sound against all behavioral deviations.  The conclusion is target-specific:
the Bellman source payoff itself, not merely some compactly selected payoff,
is uniform.

## 6. Exact obstruction: the jump image is nonconvex inside `UE`

Consider two players with continuation `y=(0,0)` and terminal rewards

\[
 r(\{1\})=(-1,-1),\qquad
 r(\{2\})=(-1,-1),\qquad
 r(\{1,2\})=(1,1).                              \tag{6.1}
\]

The all-Never profile is an exact terminal equilibrium: it gives `(0,0)`,
whereas quitting alone gives `-1`.  Hence `y\in UE(r)`.  It is also viable
relative to the singleton baselines `s_1=s_2=-1`.

Let `p_i` be player `i`'s root Quit probability.  Player 1's payoff difference
between pure Quit and pure Continue is

\[
 \bigl(-(1-p_2)+p_2\bigr)-(-p_2)=-1+3p_2.       \tag{6.2}
\]

The analogous difference for player 2 is `-1+3p_1`.  Therefore the exact
product-root Nash set is

\[
       (p_1,p_2)\in
       \{(0,0),(1/3,1/3),(1,1)\}.               \tag{6.3}
\]

Indeed, below `1/3` the unique best response is Continue, above `1/3` it is
Quit, and at `1/3` the player is indifferent; mutual best response leaves
exactly the three points in (6.3).

Their Bellman payoffs are respectively

\[
        (0,0),\qquad(-1/3,-1/3),\qquad(1,1).     \tag{6.4}
\]

For the mixed point, each player's endpoint value is `-1/3`; equivalently,
the probabilities `4/9,2/9,2/9,1/9` of no, first-only, second-only, and joint
quitting give `-4/9+1/9=-1/3`.  Thus

\[
        \mathcal J_r(\{(0,0)\})
          =\{(0,0),(-1/3,-1/3),(1,1)\}.          \tag{6.5}
\]

All three points are viable (every coordinate is at least `-1`) and, by
Proposition 3.1, all three are uniform-equilibrium payoffs.  Nevertheless the
set is not convex: `(1/2,1/2)` is on the segment from `(0,0)` to `(1,1)` and
is absent from (6.5).

This is an exact obstruction to the naive definition

\[
 \operatorname{FullPrefix}_{r,i}
   \left(\bigcup_{j\in S_i}E_j\cup\mathcal J_r(E)\right) \tag{6.6}
\]

followed by the current convex-progress proof.  The hypotheses of
`quittingEssentialAPSPrefix_subset_segment_of_convex` fail even when the base
continuation is a viable uniform payoff.  Convexifying (6.5) erases which
root equilibrium and which tail were jointly selected.  Independent private
root randomization is not an exogenous public coin that selects an equilibrium
from (6.3).

Equation (6.5) does **not** prove that every newly convexified point is not a
uniform payoff.  It proves the narrower and sufficient obstruction: algebraic
membership after convexification is no longer a supplied executable
jump/continuation witness.  A new public-randomization or correlated-selection
lemma would be required to recover those convex combinations.

## 7. Reverse order after a complete component is not a live splice

The terminal-free unique-live adaptive-mesh capstone obtains a path whose
total absorption mass diverges.  The corresponding survival product tends to
zero.  Hence a continuation placed after **all** natural-number singleton
blocks has coefficient zero in terminal payoff, and there is no finite
history at which play enters it.

Consequently, “unique-live component then jump” has three possible meanings.

1. The jump is inserted at a finite cut.  Then only a finite flow prefix
   precedes it, and Corollary 4.2 applies after exact endpoint matching.
2. The jump is placed after the completed divergent component.  It is
   unreachable/payoff-invisible and adds no new construction.
3. The jump is placed at a limit-of-switches and is meant to start a new live
   phase.  This requires an ordinal/Zeno execution object not present in the
   current `Nat`-indexed essential APS compiler.

This distinction prevents a misleading apparent commutativity.  Jump then
component is a genuine prefix composition.  Component then jump is genuine
only at a finite or newly formalized transfinite cut.

## 8. Proved facts versus proposals

### Proved here in ordinary mathematics

- Exact product-root predecessor closure (3.3), with the exact continuation
  cap recovered through diagonal semantic-pair convergence.
- Proper viable singleton-flow prefix closure, Proposition 4.1, against all
  behavioral deviations.
- The exact outsider stopping bound `2Mh+eta`; no rowwise error sum occurs.
- Soundness of the rank-one splice (5.5) over any base family already known
  pointwise to consist of uniform payoffs.
- The exact viable-UE nonconvex jump image (6.5).
- A full divergent singleton-flow component has no positive-survival
  chronological endpoint at which to execute a later jump.

### Checked ingredients, not newly proved here

- The current compact, convex, terminal-free, unique-live essential APS
  component compiler.
- Exact root action on terminal semantic pairs and literal profile splicing.
- Continuity of the semantic prefix map.
- Fixed-target terminal acceptance for uniform-equilibrium payoffs.

### Proposals, not proved

- The greatest fixed point of the unrestricted two-sorted operator (5.3) is
  nonempty for arbitrary finite quitting games.
- Every point of that greatest fixed point has a coherent chronological
  execution.
- Compactness plus a jump budget suffices to select witnesses continuously or
  measurably.
- Convexified jump fibers can be implemented without an external public
  randomization device.
- A transfinite/Zeno jump--flow execution compiles under a suitable survival
  and cap condition.

## 9. What this redirects

The one-jump seam is not itself the missing arbitrary-game theorem.  Once the
tail is already a uniform payoff, exact root closure is clean and finite
singleton flow can precede it.  The serious missing mathematics begins when
one asks for a self-generating **family**:

- jump fibers are compact but can be nonconvex;
- the existing greatest-family proof extracts segments by convexity;
- a jump has no canonical active owner;
- infinite alternation reintroduces survival/terminal-debt questions; and
- a complete unique-live component cannot be followed at ordinary time by a
  payoff-relevant jump.

Accordingly, the next implementation should not insert `J(E)` into the old
owner-indexed convex hull.  It should formalize a witness-carrying, two-sorted,
one-jump-budget certificate and prove the two closure lemmas above.  Only
after that should one investigate compact selection or remove the jump
budget.

## 10. Next concrete question

Formalize, outside this conference lane, the following exact theorem pair.

1. **Root closure:** if `y` is a uniform-equilibrium payoff,
   `IsεQuittingRootNash reward y 0 root`, and
   `v=quittingRootSuccessorPayoff reward y root`, then `v` is a
   uniform-equilibrium payoff.
2. **Proper segment closure:** if `y` is a uniform-equilibrium payoff,
   `0<p<1`, `z=quittingSingletonArcPayoff p R_i y`, `z_i=s_i`, and both
   endpoints are `QuittingEssentialAPSViable`, then `z` is a
   uniform-equilibrium payoff.

The first should be short using terminal semantic pairs.  For the second, the
load-bearing formal lemma is that the all-behavior best-response cap of the
`N`-row solo-owner mesh is bounded by the maximum of the finitely many
pure-row values and the surviving tail cap, yielding (4.12).  If those two
theorems check, define a jump-budgeted carrier before attempting any new
fixed-point argument.
