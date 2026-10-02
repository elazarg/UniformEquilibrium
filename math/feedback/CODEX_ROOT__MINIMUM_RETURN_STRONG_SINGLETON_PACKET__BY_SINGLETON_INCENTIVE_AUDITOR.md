# Review of the minimum-return strong singleton packet

Reviewer: `SINGLETON_INCENTIVE_AUDITOR`

## Verdict

The mathematical contraction is correct after one necessary dependent-index
repair.  The auxiliary packet owner should be fixed before constructing the
family, and the family must then be restricted to a strictly monotone
subsequence on which that owner's Boolean best endpoint is constant.  Before
this restriction the routed terminal is not a fixed dependent parameter, so
the proposed identity-subsequence packet is not defined.

With that repair, the construction gives a genuine source-attached
conjecture-facing contraction:

\[
\boxed{
\text{owner-compressed minimum-singleton source}
\Longrightarrow
\text{strategic singleton packet}
\ \lor\
\text{minimum-fibre collision packet}.}
\]

In the second branch the old strict off-minimum tail-cluster alternative is
impossible.  The resulting fixed-minimum other-coordinate defect and the
derived literal gain of at least \(\lambda^2D_*/6\) are both correct.

This does not consume the remaining fixed-minimum collision branch.  In
particular, the checked same-stage dispatcher cannot currently be used to
turn every such collision into a zero-defect singleton packet: at a pair it
may terminate through the geometric singleton-route predicate, which does not
retain an exact-best-endpoint certificate.

I recommend export after the author incorporates the fixed-action subsequence
and narrows the stated scope to the owner-compressed minimum-singleton source
(or separately proves the analogous cofinal construction for the other atlas
origins).  This is a strict reduction, not a completed consumer.

## Claim checked

Fix a Fin4 minimum-atom source whose selected terminal is the singleton
\(\{j\}\), one retained owner-compression chronology, and

\[
0<\lambda<\nu_*(\{j\}).
\]

The claim is that one can construct a moving concentrated packet with a fixed
auxiliary owner \(o\ne j\), fixed routed terminal, marked mass at least
\(\lambda\), exact zero marked defect for \(o\), and post-row tails whose
total debts converge to \(D_*\).  Consequently any collision residual selected
from that packet has cluster debt exactly \(D_*\), rather than strictly above
it.

## Source audit

I inspected only the declarations needed for this construction:

- `FinFourMinimumAtomChronology`,
  `FinFourOwnerCompressedSingletonEndpoint.referenceProfile`,
  `.targetProfile`, and `.target_stageMass_gt` in
  `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`;
- `QuittingStageAtomConcentratedPacketAdapter`,
  `.sourceStageMass_le_targetStageMass`, `.targetTail_eq_sourceTail`, and
  `.ownerMarkedDefect_eq_zero` in
  `Research/Quitting/PositiveStageAtomConcentratedPacket.lean`;
- `QuittingReprojectionConcentratedPacket` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionTemporalSplit.lean`;
- `QuittingConcentratedCollisionMinimumResidual` and
  `concentratedPacket_singletonStrategic_or_collisionMinimumResidual` in
  `Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean`;
- `quittingPartialPurification_then_finFourSameStage_dispatch` in
  `Research/Quitting/FinFourSameStageEndpointMonodromy.lean`; and
- `not_nonempty_finFourSameStageEndpointClosedSegment` in
  `Research/Quitting/FinFourProducerAtlas/MonodromyImpossible.lean`.

The existing strong adapter in
`Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacket.lean` repeats
one target profile constantly.  It does not state the moving construction
reviewed here.

## Repaired dependent construction

For every \(n\), choose an owner-compressed endpoint \(e_n\) of requested
depth \(n\).  Put

\[
k_n=e_n.\operatorname{rank},\qquad
\sigma_n=e_n.\operatorname{referenceProfile},\qquad
t_n=e_n.\operatorname{stage}.
\]

The endpoint field gives \(k_n\ge n\).  Hence \(k_n\to\infty\), without any
need for the chosen ranks themselves to be strictly monotone.  Composing this
with `chronology.prefix_debt_tendsto` gives

\[
D(\sigma_n)\longrightarrow D_*.
\tag{1}
\]

Let \(\widehat\sigma_n\) copy the live roots of
`e_n.targetProfile` through date \(t_n\), then resume the complete behavioral
profile \(\sigma_n\).  The ordinary self-tail identities give

\[
\Pr_{\widehat\sigma_n}(\{j\}\text{ at }t_n)>\lambda,
\tag{2}
\]

and the exact complete-tail identity

\[
\operatorname{tail}_{t_n+1}(\widehat\sigma_n)=\sigma_n.
\tag{3}
\]

Now fix one player \(o\ne j\) once and for all.  There is no reason to select
this player by pigeonhole: Fin4 has a player distinct from \(j\), and the same
one can be used at every rank.  At date \(t_n\), replace only \(o\)'s marginal
by its exact best Boolean endpoint against the actual tail in (3).  Call the
adapter \(A_n\), its action \(a_n\in\{\mathrm C,\mathrm Q\}\), and its target
profile \(\rho_n\).

The checked one-row identities give

\[
\Pr_{\rho_n}(T_n\text{ at }t_n)\ge\lambda,
\qquad
\delta_o(\operatorname{root}_{\rho_n}(t_n);U(\sigma_n))=0,
\tag{4}
\]

and retain the exact post-row tail \(\sigma_n\).  Here

\[
T_n=\begin{cases}
\{j\},&a_n=\mathrm C,\\
\{j,o\},&a_n=\mathrm Q.
\end{cases}
\tag{5}
\]

Equation (5) is the index issue in the original draft: a
`QuittingReprojectionConcentratedPacket` takes one fixed `terminal`, so the
unrestricted family \(\rho_n\) cannot yet be used with identity subsequence.

Because the action set has two elements, there is a strictly monotone
\(s:\mathbb N\to\mathbb N\) and a fixed action \(a\) such that
\(a_{s(r)}=a\) for every \(r\).  Reindex the profiles by
\(\widetilde\rho_r=\rho_{s(r)}\), or retain the original family and use \(s\)
as the packet subsequence.  Then (5) defines one fixed terminal \(T\).  Taking
marks \(t_{s(r)}\), cutoffs \(t_{s(r)}+1\), and any positive scale tending to
zero gives all fields of `QuittingReprojectionConcentratedPacket`:

- `stageMass` follows from (2) and lossless pure-endpoint routing;
- `semanticPrefix` follows from positive stage mass;
- `defect_tendsto` is in fact the identically-zero sequence by (4); and
- the packet subsequence is strictly monotone by construction.

This also records the useful preliminary split.  If \(a=\mathrm C\), then
\(T=\{j\}\) and the packet is already in the strategic singleton branch.  A
collision residual can occur only in the cofinal Quit mode
\(T=\{j,o\}\).

## Minimum-return conclusion

Let a collision residual choose a further strict subsequence and a semantic
tail cluster \(z\).  By the exact tail equality (3), all tail terms in that
subsequence are semantic pairs of \(\sigma_{s(r)}\).  Its `tail_tendsto` field
and continuity of total debt, combined with (1), give

\[
D(z)=D_*.
\tag{6}
\]

Thus the first residual disjunct \(D_*<D(z)\) is impossible, and its second
disjunct holds:

\[
\frac{\lambda D_*}{2}
\le
\sum_{i\ne o}\delta_i(r_r;U(\sigma_{s(r)}))
\quad\text{eventually}.
\tag{7}
\]

There are exactly three summands.  Nonnegativity and finite pigeonhole give a
fixed \(p\ne o\) and a further subsequence on which

\[
\delta_p\ge\frac{\lambda D_*}{6}.
\tag{8}
\]

The live mass at the marked row is at least its displayed coalition mass and
hence at least \(\lambda\).  Updating \(p\) to its exact best endpoint
therefore gives literal behavioral gain

\[
g_p=L_r\delta_p\ge\frac{\lambda^2D_*}{6}.
\tag{9}
\]

Because only \(p\)'s prescribed strategy changes, its unrestricted cap is
unchanged, so its complete terminal debt decreases by exactly \(g_p\).  The
marked pair is not \(\{p\}\), and the pure endpoint route retains its marked
mass without loss.  This verifies all quantitative claims in the note.

## Why the checked same-stage dispatch does not yet finish the branch

It is tempting to apply
`quittingPartialPurification_then_finFourSameStage_dispatch` to every late
pair row, use `not_nonempty_finFourSameStageEndpointClosedSegment`, and declare
that the result is a zero-defect singleton packet.  That inference is not
available at the public interface.

The dispatch's terminal predicate is `QuittingSameStageSingletonRoute`.  At a
two-player coalition this predicate holds geometrically by forcing either
member to Continue; see
`quittingSameStageSingletonRoute_of_card_eq_two`.  Its fields preserve mass,
but they do not assert that the selected Continue action is the player's exact
best endpoint.  Correspondingly, `FinFourTerminalSingletonProducer` records
the terminal vertex but deliberately records no best-endpoint certificate for
its terminal route.  The resulting singleton can be fed to the existing
strong adapter, but that new adapter may choose Quit and recreate the same
pair collision.

The preliminary-purification singleton case is stronger—it does retain
`action_eq_best`—but the exhaustive dispatcher can also return the weaker
terminal-orbit case.  Therefore the minimum-return packet does not by itself
reduce every collision residual to the strategic branch.

## Exact no-go for tail replacement as the missing whole-source repair

There is a simple reason that self-tail closure or a two-anchor tail closure
cannot supply the separate whole-profile near-minimum premise used by the
three-role transfer consumer.

Fix any finite prefix ending at a row where two distinct players \(j,o\) Quit
surely.  Attach arbitrary complete behavioral tails \(\tau\) and \(\tau'\)
after that row.  The two resulting profiles have exactly the same complete
terminal semantic pair.

For prescribed play, the row absorbs surely.  Under an arbitrary unilateral
behavioral deviation by a player \(i\), at least one of the two sure quitters
remains prescribed: both remain if \(i\notin\{j,o\}\), player \(o\) remains if
\(i=j\), and player \(j\) remains if \(i=o\).  Hence the row still absorbs
surely under every unilateral deviation.  Neither prescribed payoffs nor any
behavioral-deviation payoff can depend on the attached tail.  Taking the
supremum over deviations proves equality of all caps as well as all prescribed
payoffs.

Thus

\[
\operatorname{Sem}(P\triangleright\tau)
=\operatorname{Sem}(P\triangleright\tau')
\tag{10}
\]

for every such two-sure-quitter prefix \(P\).  The cofinal Quit-mode packet in
this review has exactly that pair at its marked row.  Replacing its post-row
tail by a minimum-approaching source does produce the required *tail*
minimum-return identity, but cannot move the *whole profile* any closer to the
minimum fiber.  Therefore this natural route cannot manufacture the
whole-source hypothesis of `tailEscape_or_threeRoleTransfer` unless it was
already independently known.

This is an exact all-behavior no-go, not a continuity objection.

## Conjecture-facing assessment

The repaired theorem removes a named alternative from the owner-compressed
minimum-singleton branch:

\[
\boxed{
D(z)>D_*
\quad\text{is eliminated from every newly constructed collision residual}.}
\]

That is strict atlas contraction and has a direct actual-data producer, so it
meets the mathematical relevance gate.  Its exact remaining obligation is

\[
\boxed{
\begin{array}{c}
\text{a fixed pair row with minimum-return tail, zero defect for one member,}\\
\text{and total defect at least }\lambda D_*/2\text{ on the other three}
\end{array}
\Longrightarrow
\text{a semantic consumer or finite-rank regeneration}.}
\]

The exact transfer (9) is not yet that consumer: the other three unrestricted
caps can absorb the mover's debt decrease.  Export should state this boundary
explicitly and should not claim closure of the full
`FinFourStrongConcentratedPacketConsumerResult` collision arm.

