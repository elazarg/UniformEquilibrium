# Target-law regeneration from a minimum three-role endpoint

Author: `THREE_ROLE_CONSUMER`

## Status

There is a complete source-regeneration theorem hidden behind the
source-attached `ThreeRoleLimitChord`: if the literal endpoint cluster is on
the global minimum fibre, compactify the **endpoint semantic pair together
with its actual terminal law**.  The routed marked coalition has a fixed
positive terminal-law coordinate, and the same-point causalization theorem
then constructs a fresh `FinFourMinimumAtomProducer` at that endpoint.

This removes any ambiguity about whether the compact chord can be restarted
as a full atlas source.  It can.  The regenerated producer retains the same
hard residual and may retain the routed coalition itself as its causal atom.

It does not supply a well-founded descent.  The fresh causal chronology is
selected at the endpoint joint point and is not a continuation of the old
one-player replacement edge.  If one instead retains the endpoint profiles
themselves, successive minimum-fibre replacements form horizontal
better-response dynamics at one marked row.  Finite role or coalition
pigeonhole produces a horizontal improvement cycle, not a chronological
return.  Such cycles are ordinary finite-game phenomena and cannot be read
as successive quitting dates because every nonsingleton pure row absorbs
immediately.

Thus the missing datum is not another source label.  It is an orientation:
either a strict finite rank on regenerated minimum sources, or an executable
chronology which converts the horizontal replacements into admissible
charge.

This is ordinary mathematics, not a new checked Lean declaration.

## 1. Exact source-attached input

Let `I = Fin 4`, let `r` be a quitting reward table, and retain one
`FinFourQuantitativeFullSupportHardResidual r M`.  Let

\[
 \sigma_n
\]

be actual source profiles from a recurrent concentrated collision packet,
with marked dates `t_n`, fixed marked nonsingleton coalition `C`, resolution
`lambda > 0`, and fixed transfer roles `m` and `a`.  Let

\[
 \tau_n=
 \operatorname{targetProfile}(r,\sigma_n,t_n,m)
\]

be the literal best-endpoint replacements.  The checked
`ThreeRoleTransfer` gives, at every retained index,

* a strict actual gain by `m`;
* exact mover-debt subtraction;
* a distinct positive-debt recipient `a`; and
* a nonempty routed coalition
  \[
  T=\operatorname{Routed}(C,m,\text{selected endpoint action})
  \]
  in the appropriate Boolean orientation.  Thus `T` is obtained from `C` by
  inserting or erasing `m`; it may equal `C` when the selected pure action
  agrees with `m`'s membership in the marked atom.

The mover is fixed by the recurrent-role extraction.  Its Boolean endpoint
action takes only two values, so pass to one further strict subsequence on
which the action is fixed.  Since `C` and `m` are already fixed, the routed
coalition `T` is then fixed as well.  This finite refinement preserves every
convergence and quantitative floor below.

The public `ThreeRoleLimitChord` retains only the semantic cluster points.
For the statement below one must retain the actualizing subsequence used by
`exists_threeRoleLimitChord_of_frequently_packetTransferRoles` before it is
projected away.

Assume the endpoint arm is minimum:

\[
 \operatorname{Sem}(\tau_n)\longrightarrow Y,
 \qquad D(Y)=D_*.
\tag{1}
\]

## 2. The endpoint joint law has a fixed finite atom

The endpoint update changes only `m` at the marked date.  Its live mass at
that date is unchanged.  The checked theorem
`quittingStageCoalitionMass_le_stagePureEndpointRouted` says directly that
the **unconditional** stage mass of the routed coalition does not decrease:

\[
 \Pr_{\tau_n}(T\text{ at }t_n)
 \ge
 \Pr_{\sigma_n}(C\text{ at }t_n)
 \ge \lambda.
\tag{2}
\]

For every actual profile and date,
`quittingStageCoalitionMass_le_terminalOutcomeMass` gives

\[
 \lambda
 \le
 \operatorname{Law}(\tau_n)(T).
\tag{3}
\]

Compactness of `quittingTerminalSemanticLawCarrier r` gives, after one more
subsequence,

\[
 \bigl(\operatorname{Sem}(\tau_n),
       \operatorname{Law}(\tau_n)\bigr)
 \longrightarrow (Y,\nu).
\tag{4}
\]

Coordinate continuity in the finite law simplex and (3) imply

\[
 \boxed{\nu(T)\ge\lambda>0.}
\tag{5}
\]

The limit joint point belongs to the joint carrier.  Its semantic projection
is exactly the endpoint `Y`, not an independently chosen lift, because the
same subsequence is used in both coordinates.

## 3. Exact reconstruction of a full minimum-atom producer

Equation (1) and global minimality make `(Y,nu)` a minimum joint point.  The
hard residual and reward table have never changed.  Apply

```text
exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom
```

directly to `(Y,nu)`, the same coalition `T`, joint-carrier membership, (5),
positive literal debt infimum, and `D(Y)=D_*`.  This yields

```text
QuittingMinimumLawCausalSuffixAtom r (Y, nu)
```

whose stored terminal is `T`.  Equivalently, the four-player wrapper

```text
finFourHardResidual_minimumLaw_causalSuffixAtom
```

certifies same-point causalization abstractly.  To retain the particular
routed label `T`, use the generic theorem directly and package its returned
chronology with the `QuittingMinimumLawCausalSuffixAtom` constructor; the
wrapper's public result existentially selects an atom and does not name `T`.

Together with the unchanged hard residual, joint and semantic carrier
memberships, the global-minimum proof, positive debt infimum, and
`D(Y)=inf`, these fields define a fresh

```text
FinFourMinimumAtomProducer r M
```

based at `(Y,nu)`.  Therefore:

\[
\boxed{
\begin{array}{c}
\text{source-attached three-role endpoint}\\
{}+\ D(Y)=D_*\\
\Longrightarrow\\
\text{complete Fin4 minimum-atom source regeneration at }(Y,\nu),
\end{array}}
\tag{6}
\]

and the regenerated source may use the routed terminal `T` with mass at
least `lambda`.

This is stronger than merely applying
`exists_terminalSemanticLawCarrier_lift` to `Y`: the arbitrary lift theorem
would not preserve the endpoint law or the routed atom.

## 4. What regeneration retains and what it does not

The regenerated object retains every field required by the atlas source:

* the same reward table and hard residual;
* the actual endpoint minimum semantic point;
* one actual limiting endpoint law;
* the fixed routed finite atom and its mass floor;
* positive global minimum provenance; and
* arbitrarily deep source-matched cap--Nash causal chronologies at the new
  point.

The fresh chronology is selected **from the endpoint joint point**.  It is
not asserted to extend the old profiles `tau_n`, their marked dates, or the
one-player edge `sigma_n -> tau_n`.  The old mover, recipient, gain, and
decoder atom may be retained as historical decoration, but they are not an
active edge on the newly selected chronology.

This distinction does not obstruct restarting the atlas: the atlas source
requires no backward literal identification with the previous chronology.
It does obstruct summing the previous gain into a chronological return.

There is also a stronger noncausal restart.  Before selecting a new causal
chronology, the actual endpoint profiles themselves give a recurrent
concentrated packet with:

* the same mark and post-date tail;
* fixed routed stage mass at least `lambda`;
* owner `m`; and
* marked owner defect exactly zero.

This preserves the horizontal edge geometry but still supplies no temporal
composition.

## 5. Why finite role pigeonhole is not a charged recurrence

Suppose every regenerated endpoint remains on the minimum fibre and use the
endpoint packets rather than forgetting to fresh causal chronologies.  The
mass scale can remain fixed: endpoint routing is lossless at the actual
marked row.  Finiteness can then freeze movers, recipients, decoder modes,
and coalitions, or produce a repeated coalition state.

What repeats is a sequence of **alternative profiles** related by unilateral
same-date replacements.  It is not a play path.  At a pure nonsingleton row,
one other player still Quits after every unilateral deviation, so the tail
is inaccessible and the replacement is an improving toggle in the finite
membership game

\[
 A\longmapsto r(A).
\]

Strict finite better-response cycles are possible.  For example, keep a
host `h` in all four coalitions

\[
 \{h\}\to\{h,1\}\to\{h,1,2\}
 \to\{h,2\}\to\{h\},
\tag{7}
\]

and choose the four payoff comparisons so that player `1` joins, player `2`
joins, player `1` leaves, and player `2` leaves, each strictly.  These are
independent Boolean-edge comparisons and are realized by an ordinary
quitting reward table.  The cycle is the matching-pennies better-response
cycle on the two free membership bits.

This example is not claimed to have positive global minimum debt.  It is a
sharp refutation of the proposed adapter

\[
 \text{finite role/coalition recurrence}
 \Longrightarrow
 \text{chronological charged return}.
\]

No play visits two vertices of (7): the host Quits surely at the first
displayed row.  Reading the four edges as successive dates would multiply
the first row's zero joint-survival probability and erase every later edge.
More generally, a nonsingleton pure row screens the continuation exactly.

The same obstruction is visible at the semantic level.  A mover's debt can
fall by a fixed amount while another coordinate is recharged, and after
finitely many role changes the debt vector can return.  The rational
full-support circulation in
`ATLAS_GATEKEEPER__THREE_ROLE_LIMIT_CHORD_NONCAPSTONE.md` satisfies the exact
minimum-chord affinity and cap-invariant own-debt identities.  Adding the
target law and a common positive atom does not orient that circulation: take
the same full-support law at every tableau vertex.

Therefore none of the following is a valid rank for (6) without an extra
theorem:

1. positive-debt support alone;
2. terminal-law support alone;
3. their ordered pair;
4. the finite mover/recipient/coalition label; or
5. chronological depth of the newly selected causalization.

The first three can remain constant on a horizontal cycle, the fourth
repeats, and the fifth can be reset arbitrarily large at every regenerated
minimum point.

## 6. Strongest honest recursive reduction

The source-attached minimum-target chord therefore has the exhaustive
reduction

\[
\boxed{
\begin{array}{c}
\text{killed canonical mover at a minimum endpoint}\\
\Longrightarrow\\
\text{the reviewed half-chord support-rank handoff},\\[1mm]
\text{generic partially decreased mover at a minimum endpoint}\\
\Longrightarrow\\
\text{a fresh full minimum-atom producer at the actual target law}.
\end{array}}
\tag{8}
\]

The first arm is already covered by
`FIN4_CANONICAL_PAIR_MINIMUM_ENDPOINT_SUPPORT_RANK_HANDOFF.md`.  The second is
a complete producer regeneration but not a well-founded consumer.

To turn the second line into a conjecture-facing conclusion, one still needs
one of:

* a source operation which kills the generic mover rather than merely
  decreasing it;
* a finite rank which is forced to decrease under the regenerated atlas;
* an exact chronology which realizes the horizontal gain before absorption;
  or
* a structural theorem consuming the resulting terminal better-response
  recurrent class.

Finite pigeonhole alone supplies none of these.

## 7. Sources inspected

* `ConcentratedCollisionFourRole.ThreeRoleTransfer`,
  `packet_tailEscapeFrequently_or_fixedThreeRoleTransfer`,
  `packet_tailEscapeFrequently_or_fixedThreeRoleAtomLabel`,
  `ConcentratedCollisionFourRole.ThreeRoleLimitChord`, and
  `exists_threeRoleLimitChord_of_frequently_packetTransferRoles` in
  `Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean`;
* `quittingTerminalSemanticLawCarrier_isCompact`,
  `quittingTerminalSemanticLawPoint_mem_carrier`, and
  `exists_terminalSemanticLawCarrier_lift` in
  `UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticResetIncidenceReturn.lean`;
* `quittingStageCoalitionMass_le_terminalOutcomeMass` in
  `UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticPureTimeRectangleDisintegration.lean`;
* `quittingStageCoalitionMass_le_stagePureEndpointRouted` in
  `UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticLiveWeightedCollisionTransfer.lean`;
* `QuittingMinimumLawCausalSuffixAtom` and
  `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticLawCarrierCausalization.lean`;
* `finFourHardResidual_minimumLaw_causalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
* `FinFourMinimumAtomProducer` in
  `Research/Quitting/FinFourProducerAtlas/Source.lean`;
* `quittingTerminalOutcomeMass_stoppingLawMixture_eq` and minimum-fibre
  stopping-law affinity in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/
  TerminalSemanticStoppingLawMinimumFiberAffine.lean`;
* `FIN4_CANONICAL_PAIR_MINIMUM_ENDPOINT_SUPPORT_RANK_HANDOFF.md`; and
* `ATLAS_GATEKEEPER__THREE_ROLE_LIMIT_CHORD_NONCAPSTONE.md`.

## 8. Next concrete question

Can the regenerated endpoint be chosen so that the generic mover is killed,
or can a terminal recurrent class of the resulting fixed-mass membership
toggle dynamics be consumed by a persistent-base, constrained-root, or
punishment chronology theorem?  A valid answer must use the same target law
and actual endpoint sequence; reselecting only matching roles is insufficient.
