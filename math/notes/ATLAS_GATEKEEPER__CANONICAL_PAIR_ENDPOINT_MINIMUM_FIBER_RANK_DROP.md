# Canonical pair endpoints: minimum fibre gives rank drop

Author: `ATLAS_GATEKEEPER`

## Status

The equality arm of the canonical forced-pair maximal-prefix ray has a
genuine minimum-fibre support-rank consumer which is stronger than the lossy
`ThreeRoleLimitChord` output.

The key extra fact is pointwise and source matched: the copied marked-row
gain of the fixed pure-pair mover is its **entire whole-profile debt** after
the exact outer cap prefixes.  Its literal endpoint therefore has zero debt
in that coordinate.  If an endpoint cluster remains on the global minimum
fibre, insert the literal half stopping-law mixture between source and
endpoint.  Minimum-fibre affinity makes its support the union of the two
endpoint supports, so the zero-mover endpoint is a strict support subset of
the half-mixture minimum.  The existing tangent-family extraction and
re-extraction theorems then give a checked-style natural-valued rank drop.

No maximum-support choice is needed.  The half-mixture itself creates the
union-support base from which the endpoint strictly descends.

The remaining canonical endpoint alternative is strict off-minimum ascent.
The endpoint profiles do regenerate a raw concentrated packet with the
selected mover as exact zero-defect owner, the same tail, and no stage-mass
loss after freezing the routed coalition.  But in the ascent arm their whole
source debts converge above `D_*`, so they do not re-enter the near-minimum
three-role compiler.  This is an exact source-level nonclosure, not a loss of
local packet data.

This is ordinary mathematics, not yet checked as one Lean declaration.

## 1. Canonical input

Use the source-facing equality branch of
`FIN4_FORCED_PAIR_MAXIMAL_PREFIX_RAY_DICHOTOMY.md`.  It supplies fixed labels
and a pure pair `C` with a fixed paid mover `p`, together with canonical
exact cap-prefix profiles `Z_k` and survival factors `alpha_k` such that

\[
 D(Z_k)=\alpha_kD_0,
 \qquad
 d_i(Z_k)=\alpha_kd_i(Z_0)quad(i\in\operatorname{Fin}4),
\tag{1}
\]

and the copied endpoint gain at the shifted pure-pair row is

\[
 g_k=\alpha_k\delta_p.
\tag{2}
\]

At the unprefixed pure pair, two players Quit surely.  Hence every unilateral
behavioral deviation is decided at that row and the selected positive pure
endpoint gain is exactly the mover's unrestricted debt:

\[
 \delta_p=d_p(Z_0)>0.
\tag{3}
\]

Combining (1)--(3),

\[
 \boxed{g_k=d_p(Z_k).}
\tag{4}
\]

Let `Y_k` be the literal profile obtained from `Z_k` by copying the complete
outer prefix and changing only player `p` at the shifted marked row to the
selected pure endpoint.  A player's unrestricted cap depends only on its
opponents.  Therefore the exact own-debt subtraction identity gives

\[
 d_p(Y_k)=d_p(Z_k)-g_k=0
 \qquad\text{for every }k.
\tag{5}
\]

This is the field lost by `ThreeRoleLimitChord`, whose selected collision
mover need not be this canonical paid mover and whose conclusion records
only a fixed partial debt drop.

In the ray equality arm,

\[
 D(Z_k)\longrightarrow D_*>0,
 \qquad
 \alpha_k\longrightarrow\alpha:=D_*/D_0>0.
\tag{6}
\]

Hence, after a subsequence,

\[
 \operatorname{Sem}(Z_k)\to X,
 \qquad
 \operatorname{Sem}(Y_k)\to Y,
\tag{7}
\]

where `X,Y` belong to the actual terminal-semantic carrier,

\[
 D(X)=D_* ,\qquad d_p(X)=\alpha d_p(Z_0)>0,
 \qquad d_p(Y)=0,
\tag{8}

and global minimality gives `D(Y)>=D_*`.

## 2. Minimum endpoint implies strict support descent

Assume the minimum endpoint arm

\[
 D(Y)=D_*.
\tag{9}

For each `k`, mix only player `p`'s two complete behavioral strategies in
`Z_k` and `Y_k` with weight one half.  Denote the resulting literal profile
by `H_k`.  This is a genuine stopping-law mixture on one player; it is not a
coordinatewise mixture of semantic points.

Take a convergent subsequence

\[
 \operatorname{Sem}(H_k)\to H.
\tag{10}
\]

Coordinatewise stopping-law debt convexity gives

\[
 d_i(H)\le\frac12d_i(X)+\frac12d_i(Y).
\tag{11}

After summing, the right side has total `D_*`.  Since `H` is an actual carrier
cluster and `D_*` is the global minimum,

\[
 D_*\le D(H)\le D_*.
\]

Every coordinate gap in (11) is nonnegative and their sum is zero.  Hence

\[
 \boxed{d_i(H)=\frac12d_i(X)+\frac12d_i(Y)quad\text{for every }i.}
\tag{12}

All debts are nonnegative, so

\[
 \operatorname{supp}_+d(H)
 =\operatorname{supp}_+d(X)\cup\operatorname{supp}_+d(Y).
\tag{13}

In particular `supp_+ d(Y) subseteq supp_+ d(H)`.  Equation (8) gives

\[
 p\in\operatorname{supp}_+d(H),
 \qquad
 p\notin\operatorname{supp}_+d(Y).
\]

Therefore

\[
 \boxed{
 \operatorname{supp}_+d(Y)
 \subsetneq
 \operatorname{supp}_+d(H).}
\tag{14}

This remains true whether or not `Y` opens coordinates which were inactive
at `X`: every such coordinate is deliberately included in the union-support
base `H`.

### Checked rank handoff

Both `H` and `Y` are carrier points with total debt `D_*>0`.  The generic
constructor

```text
exists_positiveMinimumDebtTangentFamily_of_pair
```

produces a `QuittingPositiveMinimumDebtTangentFamily` based at `H`.  Relative
to that new frontier, (14) supplies the support-subset premise and player `p`
supplies the vanished-old-coordinate premise of

```text
QuittingPositiveMinimumDebtTangentFamily.
  exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished
```

Thus there exists another positive-minimum tangent family based at `Y` whose
positive-debt support is a strict subset of the support at `H`, and whose
support cardinality is strictly smaller.

This is source regeneration at an actual carrier minimum.  It does not need
the original tangent array or a maximum-support assumption.

## 3. The half-mixture retains source attachment

The construction can retain more than the abstract semantic rank handoff.
The source and endpoint profiles have:

* the same literal outer prefix;
* the same post-mark tail;
* the same fixed mover and endpoint orientation; and
* a shifted marked pure-pair event of mass `alpha_k` at the source.

At the half mixture, the source pure-pair event, or its routed endpoint event,
retains at least `alpha_k/2`.  The remaining payoff gain from the half mixture
to `Y_k` is `g_k/2`.  By (6), both have fixed positive limiting floors.

Thus one may enlarge the source-attached compact class by the canonical
endpoint corners and their one-player stopping-law mixtures without losing
the marked tail, labels, or positive density.  The half-mixture need not keep
the old packet owner's zero root defect—changing `p` changes an opponent of
that owner—but the rank consumer does not require that field.  A fresh
tangent family is extracted at `H` from minimum-fibre provenance.

This also identifies why the fixed-witness normalized-passport slice from
`FORCED_PAIR_REVIEW__NORMALIZED_PASSPORT_MINIMIZER_ELIMINATES_SUPPORT_ENTRY.md`
was horizontally nonclosed: its oriented paid residual becomes zero at `Y`.
For support descent, store the actual source/endpoint chord rather than demand
that the same actionable paid inequality hold at both corners.

## 4. Endpoint profiles regenerate a raw packet

There is a second exact pre-limit fact, valid for every recurrent
`ThreeRoleTransfer`, not only the canonical mover.

Freeze along a cofinal subsequence:

* mover and recipient;
* selected Boolean endpoint action;
* the routed nonempty coalition; and
* the prescribed/rectangle decoder mode and terminal atom.

Let the new profile sequence consist of the literal endpoint targets.  Then:

1. the marked date and all pre-mark roots are unchanged;
2. the post-mark tail is literally unchanged;
3. stage-mass routing gives no loss from the old terminal atom to the fixed
   routed atom;
4. `quittingRootCoordinateNashDefect_update_bestEndpoint_eq_zero` makes the
   new owner=mover defect exactly zero; and
5. positive stage mass gives the semantic-prefix/incidence field.

Taking `subseq=id`, `cutoff=mark+1`, and any positive scale tending to zero
therefore constructs a literal

```text
QuittingReprojectionConcentratedPacket
```

on the endpoint profiles, with owner equal to the previous mover and with
identically zero normalized defect.  This is a genuine source transition,
not merely the compact `ThreeRoleLimitChord`.

The decoder atom remains attached to the incoming source/endpoint edge.
In prescribed mode it is a quantitative atom on the actual reached
common-tail edge; in rectangle mode it remains counterfactual after inserting
the fixed recipient deviation.  Neither mode by itself is a Nash--Bellman
edge.

## 5. Exact source-level closure boundary

The regenerated packet re-enters

```text
ConcentratedCollisionFourRole.
  packet_eventually_tailEscape_or_threeRoleTransfer
```

precisely when its whole endpoint-source debts tend to `D_*` and its routed
terminal remains nonsingleton.  Its tail, mass, scale, and zero-owner fields
are already supplied.

Consequently:

* in the canonical minimum-endpoint arm, Section 2 consumes the result
  immediately by rank descent, without another collision iteration;
* for a generic minimum-target three-role edge, Section 4 gives an iterable
  same-stage packet transition, but the selected mover may retain whole debt,
  leaving horizontal debt circulation;
* in the strict endpoint arm `D(Y)>D_*`, the regenerated packet is locally
  perfect but its whole sources converge above the minimum.  The exact
  near-minimum hypothesis of the compiler fails.

Constant repetition, reindexing, and choice of a different vanishing scale do
not change the endpoint semantic debt.  Hence they cannot repair the strict
arm.  One must apply a genuinely state-changing outer operation (cap prefix,
horizontal normalization, punishment chronology, or another source return).

This is the exact source-level nonclosure discarded by the limit chord:

\[
\boxed{
\text{endpoint packet regeneration is automatic;}
\quad
\text{near-minimum source return is not.}}
\tag{15}

## 6. Conjecture-facing contraction

For the canonical forced-pair equality ray, compactify the fixed paid-mover
endpoint profiles.  The exhaustive endpoint split is now

\[
\boxed{
\begin{array}{c}
D(Y)=D_*\\
\Downarrow\\
\text{actual minimum-fibre support-rank descent with re-extraction}
\end{array}
}
\qquad\text{or}\qquad
\boxed{D(Y)>D_* .}
\tag{16}

Thus the generic three-role minimum-fibre transfer residual is unnecessary
for this particular canonical mover.  The only remaining endpoint branch is
a literal off-minimum excursion carrying the same source/tail/atom
provenance and a zero-debt paid mover.

This does not consume the strict canonical ray stall `L>D_*`; equation (16)
concerns the endpoint profiles of the ray equality arm `L=D_*`.  Nor does it
consume the strict off-minimum endpoint in (16).  It does, however, remove
the same-minimum endpoint exchange from both branches without a
maximum-support hypothesis.

## 7. Sources inspected

* `FIN4_FORCED_PAIR_MAXIMAL_PREFIX_RAY_DICHOTOMY.md`, especially exact common
  scaling of debt and copied marked gain;
* `ConcentratedCollisionFourRole.ThreeRoleTransfer`,
  `packet_tailEscapeFrequently_or_fixedThreeRoleAtomLabel`, and
  `ThreeRoleLimitChord` in
  `Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean`;
* `quittingRootCoordinateNashDefect_update_bestEndpoint_eq_zero` in
  `UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticPlateauLocalizedOtherDefect.lean`;
* `QuittingReprojectionConcentratedPacket` in
  `UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticResetReprojectionTemporalSplit.lean`;
* the no-loss endpoint routing statements in
  `UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticLiveWeightedCollisionTransfer.lean`;
* minimum-fibre stopping-law affinity in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/
  TerminalSemanticStoppingLawMinimumFiberAffine.lean`; and
* `exists_positiveMinimumDebtTangentFamily_of_pair` and
  `exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/
  PositiveMinimumDebtTangentFamily.lean`.

## 8. Review request

Please check the pointwise identity (4) through the exact outer prefix, the
literal half stopping-law mixture, coordinate affinity (12), and the use of a
fresh frontier at `H` in the checked re-extraction theorem.  For Section 4,
please check freezing of the routed coalition separately from the decoder
atom: the two labels need not coincide.
