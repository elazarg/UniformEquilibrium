# Strict-ray binding-pair collision signs from limiting solo probes

Identity: `CODEX_PROBE`

## Status

Ordinary mathematics, not checked in Lean.  This note repairs the collision-sign
gap in
`exports/FIN4_STRICT_MAXIMAL_RAY_CARDINAL_THREE_BINDING_REDUCTION.md` without
editing that export.  The repair is local: it supplies the two strict signs used
by both finite-cap support cases and leaves the component-index argument and its
formalization boundary unchanged.

It does **not** construct the missing local-parity certificate, prove the
cardinality reduction in Lean, consume cardinality three or full binding, or
prove a uniform-equilibrium payoff.

## Question

Let a four-player maximum-absorption exact-root ray have caps `b_k` converging
to `bbar`.  Put

\[
s_h=r_h(\{h\}),\qquad
\bar\delta_h=\bar b_h-s_h,
\qquad
A=\{h:\bar\delta_h=0\}.
\]

Assume:

1. `A = {i,j}` with `i != j`;
2. `bar_delta_h > 0` for each outsider `h`;
3. all Continue is the unique exact product-root Nash equilibrium against
   `bbar`.

For distinct players define

\[
J_{ab}=r_a(\{a,b\})-r_a(\{b\}).
\]

Does the limiting uniqueness assumption prove both

\[
J_{ij}>0,\qquad J_{ji}>0,
\]

and do those signs supply every finite-cap use made in the exported
cardinality-two argument?

## Source audit

The bounded source neighborhood inspected was:

- `QuittingForwardExactCapTail.bindingFinset` and
  `QuittingForwardExactCapTail.singleton_le_capLimit` in
  `Research/Quitting/ForwardExactCapTailFlow.lean`;
- `FinFourOwnerCompressedMinimumReturnForcedPairPacket.HasUniqueAllContinueAtCapLimit`
  and the conditional binding-cardinality consumer in
  `Research/Quitting/FinFourProducerAtlas/StrictRayBindingCardinality.lean`;
- `quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticEndpointDefectPolarity.lean`;
- the export named above and the two existing reviews
  `feedback/CODEX_BOREL__STRICT_RAY_TAIL_NORMALIZATION__BY_CODEX_NOETHER.md`
  and
  `feedback/FIN4_STRICT_MAXIMAL_RAY_CARDINAL_THREE_BINDING_REDUCTION__BY_CLAUDE_KAKUTANI.md`.

The Lean cardinality module is conditional: it does not construct either a
mod-two parity theory or the finite-cap local-zero certificate.  Nothing in
this note changes that status.

## 1. Exact solo-probe calculation

For `0 < t < 1`, let `x^(b,t)` be the product root at which player `b` Quits
with probability `t` and every other player Continues surely.  Write `g_a` for
Quit minus Continue against the limiting cap `bbar`.

The endpoint-toggle expansion gives the following exact formulas.

For the mixer `b`, none of its opponents Quits, so its endpoint comparison is

\[
g_b(x^{(b,t)})=s_b-\bar b_b=-\bar\delta_b.
\tag{1}
\]

In particular, it is independent of `t`, as every player's endpoint
difference is independent of that player's own hazard.

For any other player `a`, only the opponent coalitions `empty` and `{b}` have
positive probability.  Therefore

\[
g_a(x^{(b,t)})
=-(1-t)\bar\delta_a+tJ_{ab}.
\tag{2}
\]

If `a` is the other binding player, then `bar_delta_a = 0`, and (2) becomes

\[
g_a(x^{(b,t)})=tJ_{ab}.
\tag{3}
\]

If `h` is an outsider, then `bar_delta_h > 0`.  Since the right side of (2)
is continuous in `t` and equals `-bar_delta_h < 0` at `t=0`, there is
`epsilon_h > 0` such that

\[
g_h(x^{(b,t)})<0\qquad(0<t<\epsilon_h).
\tag{4}
\]

There are only two outsiders, so one positive `epsilon` works for both.

## 2. Strict collision signs

Take `b=j` and `a=i`.  Since `j` is binding, (1) gives

\[
g_j(x^{(j,t)})=0.
\]

Thus player `j`, who mixes with probability strictly between zero and one, is
exactly indifferent.  The outsiders strictly prefer Continue for sufficiently
small positive `t` by (4).  Player `i` is prescribed Continue, so its exact-root
condition is `g_i <= 0`.  By (3), that condition is

\[
tJ_{ij}\le 0.
\]

Consequently, if `J_ij <= 0`, every sufficiently small positive solo probe
`x^(j,t)` is an exact product-root Nash equilibrium against `bbar`.  It is not
all Continue because its absorption is `t > 0`.  This contradicts uniqueness.
Hence

\[
\boxed{J_{ij}>0}.
\tag{5}
\]

Interchanging `i` and `j` gives

\[
\boxed{J_{ji}>0}.
\tag{6}
\]

This argument uses neither finite-cap maximality nor the support of the
selected finite-cap root.  It therefore applies once, before splitting into
the both-mixed and solo cases.

## 3. Audit of the both-mixed finite-cap case

At a sufficiently late finite cap `b_k`, write

\[
\delta_{k,h}=b_{k,h}-s_h.
\]

Suppose the selected root has both binding hazards strictly between zero and
one.  Exact mixing gives

\[
(1-x_j)\delta_{k,i}=x_jJ_{ij},
\qquad
(1-x_i)\delta_{k,j}=x_iJ_{ji}.
\tag{7}
\]

Equations (5)--(7), together with `0 < x_i,x_j < 1`, imply

\[
\delta_{k,i}>0,\qquad\delta_{k,j}>0.
\tag{8}
\]

This supplies every collision-sign consequence used downstream:

- all Continue is strict in the two binding coordinates at the finite cap;
- both face comparisons have positive cross slope
  `delta_(k,i)+J_ij` and `delta_(k,j)+J_ji`;
- the completely mixed local root is unique and regular;
- the local two-player geometry is coordination geometry;
- the strict-pure and mixed local contributions are the two contributions
  counted by the component-index or mod-two argument.

The export's sentence that the two `J` entries are nonnegative does not follow
from the finite-cap mixing equations unless finite-cap nonnegativity of both
`delta_k` values has separately been proved.  The source structure exposes
`singleton_le_capLimit` at the **limit**, not this finite-cap inequality.
The solo-probe proof avoids that issue and gives strict positivity directly.

The export's subsequent `J=0` maximality perturbation is mathematically
unnecessary after (5)--(6) and should be deleted rather than retained as a
second proof.

## 4. Audit of the solo finite-cap case

Suppose only `i` has positive selected hazard `x_k`, while `j` has hazard zero.
Late small absorption gives `0 < x_k < 1`.  Player `i` mixes, and at `x_j=0`
its face comparison is `-delta_(k,i)`.  Hence

\[
\delta_{k,i}=0.
\tag{9}
\]

Player `j` Continues.  If its inequality were strict at `x_k`, increasing
`i`'s hazard slightly would preserve `i`'s equality, player `j`'s Continue
inequality and all strict outsider inequalities, producing a root with greater
absorption.  Finite-cap maximality therefore forces

\[
(1-x_k)\delta_{k,j}=x_kJ_{ji}.
\tag{10}
\]

Equation (6) and `0 < x_k < 1` then give

\[
\delta_{k,j}>0.
\tag{11}
\]

Equation (5) is the other strict sign needed in this case.  It implies that,
whenever `x_j>0` near the solo segment, player `i` strictly prefers Quit.  The
complete local equilibrium component is therefore exactly

\[
E_k=\{(x_i,x_j):0\le x_i\le x_k,\ x_j=0\}.
\tag{12}
\]

Thus the same two solo probes supply both signs required by the segment and
perturbation calculation.  The solo paragraph in the export already proves
`J_ij>0` by one of these probes; it can instead cite the common sign lemma.
The maximality argument remains needed for (10), but not to establish either
`J` sign.

For the newer explicit Sperner-count route, even (10)--(11) are unnecessary:
from (9) and `J_ij>0`, the face comparison

\[
g_i=x_jJ_{ij}\ge0
\]

makes the relevant label unattainable.  That is a possible simplification of
the topological implementation, not part of the export's current signed-index
proof.

## 5. Downstream conclusions unaffected by the repair

After replacing the unsupported sign assertion, the following parts of the
ordinary component-index proof are unchanged:

1. maximum absorption localizes the entire finite-cap Nash set near all
   Continue;
2. strict outsider inequalities reduce the local geometry to the binding
   pair;
3. the both-mixed local component has total signed index zero;
4. the solo segment has local component index zero after a sufficiently small
   cap perturbation inside a common isolating neighborhood;
5. global component-index sum `+1` contradicts localization of the entire
   Nash set;
6. cardinalities zero and one are excluded by the separate arguments in the
   export; and
7. the source-facing conclusion remains exactly the three-way split:
   positive-absorption exact root at the limiting cap, full binding, or
   binding cardinality three.

No conclusion becomes unconditional.  In particular, the strict signs rely
on limiting-root uniqueness.  When uniqueness is not supplied, the solo probe
with a nonpositive `J` is itself the positive-absorption limiting root returned
by the first arm of the source-facing split.

## 6. Additional issues found

### 6.1 A harmless formula error in existing review material

`feedback/FIN4_STRICT_MAXIMAL_RAY_CARDINAL_THREE_BINDING_REDUCTION__BY_CLAUDE_KAKUTANI.md`
writes the solo mixer's comparison as

\[
\bar g_j(t e_j)=-(1-t)\bar\delta_j.
\]

The exact formula is (1), namely `-bar_delta_j`, because an endpoint
difference never depends on the player's own hazard.  Both are zero for a
binding mixer, so the proof and sign conclusion are unaffected.  A corrected
export should use (1).

### 6.2 The topological/formalization prerequisite remains open

The sign repair does not construct
`ModTwoBoxComplementarityParitySpec`,
`FinFourBindingPairFiniteCapParityWitness`, or an explicit same-resolution
Sperner local-zero certificate.  The current Lean theorem in
`StrictRayBindingCardinality.lean` is still conditional on supplied parity
data.  Therefore the export remains ordinary mathematics and must not acquire
a Lean or unconditional-integration claim from this repair.

There is a plausible lighter formalization route in
`../FIN4_BINDING_PAIR_EXPLICIT_MOD_TWO_LOCAL_COUNT.md`: compute the finite-cap
local Sperner parity directly.  That document is itself ordinary mathematics
and has not passed the export gate.

### 6.3 The solo homotopy sentence needs the stated component-index package

The export's compactness sentence about raising `b_(k,i)` is valid only with
the standard upper-semicontinuity/isolation fact for the finite Nash solution
correspondence and local-index invariance under a common isolating homotopy.
Those are included in the external component-index package explicitly listed
by the export.  They are not consequences of the collision signs and are not
presently checked in this project.

## Final verdict

The collision-sign gap has a complete, source-matched repair:

\[
\boxed{
|A|=2\ \text{and unique all Continue at }\bar b
\quad\Longrightarrow\quad
J_{ij}>0\ \text{and }J_{ji}>0.}
\]

It applies before the both-mixed/solo split and supplies every downstream sign
used by the exported ordinary proof.  I found no further defect in the
quitting-game algebra.  The remaining obstacle is the already-declared
topological certification layer, not this sign calculation.

