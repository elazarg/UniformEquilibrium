# Review of the cap-band minimum-chord support descent

Reviewer: CODEX_HAHN

Reviewed file:
`notes/CODEX_SPINOZA__CAP_BAND_CUT_MINIMUM_CHORD_RENEWABLE_SUPPORT_DESCENT.md`

Reviewed SHA256:
`57ac0c48d9742b5fac4026130871325e66771465b8eb5e2dd6e38b5daf2496ad`

## Verdict

**PASS as exact ordinary mathematics and as a genuine one-use entry into the
existing renewable minimum-source trace.**  The result does not consume the
off-minimum arm.  I found no hidden conversion of the incoming cap-band edge
into a tangent column and no loss of literal source provenance in the
normalization step.

## 1. Literal suffix normalization

Let \(c_n\) be the first date at which the cap-band source and target differ,
and let \(r_n\) be their common probability of reaching that date.  The two
profiles agree at every earlier date, so conditioning on reach to \(c_n\)
gives literal suffixes \(A_n,B_n\) with the same opponents and

\[
 B_n=A_n[k\leftarrow b_{n,k}].
\]

There is only one live nonabsorbed history in a quitting game.  The
common-prefix payoff identity therefore gives the exact scaling

\[
 U_k(Y_n)-U_k(\Sigma_n)
 =r_n\bigl(U_k(B_n)-U_k(A_n)\bigr).
\]

The late-receiver/live-target construction supplies fixed joint reach through
the whole word, and \(c_n\) occurs strictly before its tail boundary.  Hence
the source reach \(r_n\) at the cut has the required uniform positive floor.

Every complete \(k\)-response at \(B_n\) can be copied after the unchanged
prefix of \(Y_n\).  Its gain is multiplied by \(r_n\), so

\[
 r_n d_k(B_n)\le d_k(Y_n)\le e_n.
\]

Because \(A_n\) and \(B_n\) have identical opponents, \(k\)'s complete cap is
the same at both suffixes.  Thus

\[
 d_k(A_n)-d_k(B_n)=U_k(B_n)-U_k(A_n)
\]

exactly.  These facts justify the fixed source debt, vanishing target debt,
and limiting killed coordinate.

## 2. Compact endpoint split

Joint semantic/law compactness applies simultaneously to the two literal
suffix sequences.  Both endpoint debts are at least the global minimum.  If
either limiting total debt is strict, convergence gives a uniform debt
excess on the corresponding actual suffix family; the note correctly keeps
this only as the source-attached off-minimum paid port.

If neither is strict, both endpoint total debts equal \(D_*\).  This split is
exhaustive.

## 3. Executable minimum chord and support

Mixing only player \(k\)'s two stopping laws gives actual behavioral profiles;
it is not public correlation or formal semantic interpolation.  Prescribed
payoff and terminal law are affine in that law.  Every complete cap, hence
every debt coordinate, is convex along the chord.  Therefore

\[
 D(H_\theta)\le(1-\theta)D(A)+\theta D(B)=D_*.
\]

Carrier minimality forces equality.  Since each coordinatewise convexity gap
is nonnegative and their finite sum is zero, every coordinate gap is zero.
This proves the asserted debt affinity.  Consequently every positive debt of
\(B\) remains positive at a proper chord point, while the killed mover \(k\)
belongs to the chord support and not the target support.  The strict support
inclusion is valid without a maximal-support assumption.

The same full replacement
\(B_n=H_{n,\theta}[k\leftarrow b_{n,k}]\) remains literal, and its limiting
gain is exactly \((1-\theta)G>0\).

## 4. Same-point source regeneration

The pointwise Fin4 minimum-law theorem applies to each of the actual joint-law
limits \(H_\theta\) and \(B\), not to an arbitrarily substituted law over the
same semantic point.  It supplies a positive finite terminal coordinate at
each point.  Same-point causalization then packages each as a complete
`FinFourMinimumAtomProducer` with the unchanged hard residual.  The note is
careful not to claim that the regenerated chronology is the original
cap-band calendar.

## 5. Renewable rank and the coherence boundary

The target support has cardinality at most three.  The checked neutral
adapter `FinFourSupportContractedRenewalInput` /
`nonempty_finFourSupportContractedRenewalResult` in
`Research/Quitting/FinFourProducerAtlas/SupportContractedRenewal.lean` is
exactly the interface used here: it accepts an arbitrary separately retained
incoming-edge proposition, a same-residual regenerated target source, and a
target-support bound.  It independently extracts a tangent family based at
the target point and starts the checked renewable trace.

Thus the incoming literal chord-to-target edge may be retained as a one-use
origin edge without being identified with any full-replacement column of the
new tangent family.  Origin rank five is above the first tangent rank, which
is at most four; all later recursive edges strictly lower support.  The
stronger checked count is at most two further tangent-to-tangent descents from
a support-at-most-three target.

This avoids the earlier canonical-handoff coherence gap.  The theorem does
not say that the incoming edge is renewable, that the re-extracted tangent
uses the incoming calendars, or that any terminal tangent alternative has
already been converted to a uniform payoff.

## Exact surviving contribution

The cap-band branch has the honest exhaustive reduction

\[
 \text{source-attached off-minimum paid port}
 \quad\text{or}\quad
 \text{one-use literal entry into a same-residual renewable minimum trace
 of support at most three}.
\]

Only the second arm is consumed as a finite-rank support reduction.  The
first remains the established off-minimum source-reentry waist, as the note
states.
