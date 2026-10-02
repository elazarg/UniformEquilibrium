# Review of conditioned-packet residual-port counterexample by `CODEX_CEDAR`

Reviewed note:
[`CHATGPT_EXTERNAL__CONDITIONED_PACKET_PORT_COUNTEREXAMPLE.md`](../notes/CHATGPT_EXTERNAL__CONDITIONED_PACKET_PORT_COUNTEREXAMPLE.md).

## Verdict

The **core three-player counterexample is valid** as an ordinary-mathematics
falsifier of semantic-source-only port stability, with two important scope
corrections.

**Follow-up correction.**  This verdict is only about retaining the two
displayed complete stopping-law ports.  It is not a negative answer to the
existential reprojection question: the constructor is allowed to choose a new
executable continuation, and on this table it can restore the frozen packet
hazard while preserving the reached semantic pair, the deleted clock, and the
prescribed atom.  Section 7 records the exact quantifier distinction.

1. The frozen and reached profiles have exactly the same terminal semantic
   **pair**, but not the same terminal outcome law.  Their law difference is
   nevertheless `O(delta)` while the deleted-clock difference is greater than
   `1/2`, so the asymptotic discontinuity survives this correction.
2. The table gives a literal prescribed-arm instance of
   `HasQuittingStoppingLawVanishingDebtAtomAlternative`.  It is not by itself
   a `QuittingVanishingDebtAtomAccess`, because no
   `QuittingPositiveMinimumDebtTangentFamily` or its eventual-rank fields are
   supplied.

The posterior formula and the proposed `Omega_L` clock estimate are valid
under the stated shared-two-component-law and positive-denominator
hypotheses.  The semantic estimates are safe.  The atom-label constant in
Section 7 is correct for the prescribed arm; a uniform claim covering the
rectangle arm needs a factor-two stronger smallness hypothesis.  “Maximal”
should therefore be read as a proposed sufficient repair, not a proved
classification.

I did not run Lean and assign no `L`, `A`, or `C` seal.

## 1. Behavioral realization and Bayes update

Let branch `A` have preceding survival `lambda^2` and then Quit at the packet
date, and let branch `B` Continue through those two dates and Quit at the next
date.  With entrance weight `lambda` on `B`, survival of the preceding date is

\[
 (1-\lambda)\lambda^2+\lambda.
\]

Thus the conditional weight of `B` at the packet date is exactly

\[
 \widehat\lambda=
 \frac{\lambda}{(1-\lambda)\lambda^2+\lambda}
 =\frac{N^2}{N^2+N-1}.
\]

This mixed stopping law has the standard behavioral realization: use the
unconditional survival at the preceding public all-Continue history, the
Bayes posterior at the packet history, and then the conditional residual
hazards.  No unobservable correlation across players is required.  For
`N>=17`, the displayed difference is indeed greater than `1/2`.

When `m,o` Continue, both branches terminate at `{a}`, including branch `A`
when it Quits at the preceding date.  Hence the pre-packet complete profile
has payoff, cap, and terminal law `((0,0,0),(0,0,0),delta_{\{a\}})` for every
entrance mixture.

## 2. Packet semantic pair and law

At the packet root, with `a` Continue probability `w`, `m` Quit probability
`delta`, and `o` Continue surely, the prescribed outcome law is

\[
 \Pr\{a\}=1-\delta,
 \quad \Pr\{a,m\}=(1-w)\delta,
 \quad \Pr\{m\}=w\delta.
\]

The reward calculation in the note is correct:

\[
 U_o=-\delta,\qquad Q_o=-1,\qquad C_o=-\delta,
 \qquad B_o=-\delta,
\]

and every `a,m` coordinate is zero.  Therefore the semantic pair is exactly

\[
 ((0,0,-\delta),(0,0,-\delta))
\]

for both `w=lambda` and `w=hatLambda`.

The outcome laws, however, are not equal: mass
`delta*(hatLambda-lambda)` moves from `{a,m}` to `{m}`.  Their `l1` distance is
`2*delta*(hatLambda-lambda)<=2delta`, so it still tends to zero.  Accordingly
the example refutes a modulus based on reset scale plus semantic-pair
distance, and also one continuous in the complete semantic/law-point distance,
but it should not be described as exact law equality.

Each literal complete profile has zero prescribed/direct defect when annotated
by its own shifted semantic pairs.  That fact does not identify the two
residual stopping-law ports.

## 3. Literal local atom interface

Take the source profile with `m` always Continue and the target strategy for
`m` that Quits surely at the packet date.  Use mover `m`, observer `o`, and
terminal `C={a,m}`.  In the source `Pr(C)=0`; at the target endpoint
`Pr(C)=1-w`.  Since `r_o(C)=-1`, the project's signed atom

\[
 (\Pr_{source}(C)-\Pr_{target}(C))r_o(C)
\]

equals `1-w`.  For three players
`Fintype.card (QuittingTerminalOutcome I)=8`, including `Never`, and therefore

\[
 \frac12\le 8(1-\lambda).
\]

This is exactly the prescribed branch of
`HasQuittingStoppingLawVanishingDebtAtomAlternative reward profile m o target
1 error`; the prescribed branch imposes no endpoint-debt field.  The note's
additional observation that both observer debts are zero is also correct.

After conditioning,

\[
 8(1-\widehat\lambda)<\frac12
\]

for `N>=17`, so terminal `{a,m}` no longer witnesses charge one.  Terminal
`{m}` does: its endpoint mass is `hatLambda`, giving signed atom
`hatLambda`.  Thus the fixed terminal label really switches.

This is a local-interface family.  It does not construct the `frontier`,
`source_tendsto`, normalized tangent, or eventual decoder fields required by
`QuittingVanishingDebtAtomAccess` in
`UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`.

## 4. Deleted-clock discontinuity

Deleting `m` from this one packet row leaves only `a,o` in the product.
Because `o` Continues surely, deleted-`m` survival is exactly `w`.  Hence the
frozen and conditioned clocks are `lambda` and `hatLambda`, and their distance
is greater than `1/2`.  Any common approximation has maximum error greater
than `1/4`, as claimed.

The example is temporally concentrated: its large port change occurs at one
row.  Thus it does not falsify a theorem whose hypotheses already include the
diffuse normalized-clock mesh field of
`QuittingReprojectionDiffuseWindowPacket`.  It does falsify the broader local
atom/reset claim when “fine mesh” means only the reset mixing scale `delta`.
The note should keep these two mesh notions distinct.

## 5. The `Omega_L` repair

For fixed component laws with survivals `S(s),T(s)`, direct algebra gives

\[
 F_s(a)-F_s(b)=
 \frac{S(s)T(s)(a-b)}{M_s(a)M_s(b)}.
\]

At suffix `s`, the two residual laws are mixtures of the same two conditional
component laws, with weights `F_s(a),F_s(b)`.  Their total-variation distance
is at most the absolute weight difference.  Product coupling across the
finite player set and telescoping products then bound every joint and every
one-player-deleted survival event by the sum of these distances, hence by
`Omega_L`.  This requires:

- identical component laws on the two compared sides, with only entrance
  weights changed;
- positive displayed survival denominators; and
- suffixes inside the finite packet, or a common coupled continuation beyond
  it.

Under those qualifications, (6.3)--(6.5) have the correct constants and
conditioning orientation.  Zero denominators are a real boundary: a public
history reached with probability zero has no Bayes-determined residual port.

Coupling the complete opponent stopping laws for any fixed unilateral
deviation gives the prescribed and unrestricted best-response estimates in
(7.1); taking the supremum preserves the common bound.  The debt bound is the
sum of the prescribed and cap bounds.

For a prescribed atom, changing both source and endpoint event masses by at
most `Omega_L` changes the signed atom by at most `2R*Omega_L`.  Multiplying by
`K`, condition

\[
 \Omega_L\le \frac{q}{8KR}
\]

retains the same label at charge `q/2`, exactly as stated.  In the rectangle
arm the original threshold is `q/4` and the new charge-`q/2` threshold is
`q/8`; the available margin is only `q/8`.  The uniform sufficient condition
there is

\[
 \Omega_L\le \frac{q}{16KR},
\]

unless an additional atom margin is recorded.

The example demonstrates necessity of some likelihood/survival-denominator
control for this port parameterization.  It does not prove that `Omega_L` is
the unique or maximal possible state enlargement.

## 6. Relation to Cedar's seam-only adapter

The counterexample does not falsify Propositions 1--2 of
[`CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION.md`](../notes/CODEX_CEDAR__CONDITIONED_ATOM_CLOCK_REPROJECTION.md).
That adapter never infers deleted clocks from a semantic pair.  It carries the
literal selected roots, asks separately for two persistent labels in those
actual roots, and charges only prescribed/cap mismatch at semantic seams.

Here the semantic seam price can be zero while the actual root port changes by
order one.  Therefore the example shows that the adapter's two-label root
hypothesis cannot be deduced from semantic seam summability.  If conditioned
roots are used, their actual marginal hazards—not the frozen hazards—must be
shown divergent.  Conversely, once that literal two-label condition and the
candidate seam budget are supplied, no frozen-clock approximation is needed.

There is a separate scope issue in Cedar Proposition 2: as first stated, its
initial candidate pair was an actual semantic pair with all debts at most
`eta`, already an unrestricted terminal `eta`-Nash profile.  That circular
initial condition must be replaced by a genuinely nonsemantic bounded
candidate block or otherwise supplied independently.  This issue is distinct
from the port counterexample.

## 7. Follow-up on the existential reprojection quantifier

Noether's quantifier objection is valid under the literal behavioral and
existential reading of
`questions/CONDITIONED_PACKET_REPROJECTION.md`.  The example fixes two
particular residual ports and proves that their common semantic pair does not
control their deleted clock.  It does not prove that every executable
continuation with that reached semantic source loses the clock or atom.

Indeed, after the preceding all-Continue history, choose a fresh behavioral
continuation in which `a`'s packet Continue probability is the frozen
`lambda`, `m` Quits with probability `delta`, and `o` Continues surely; retain
the later solo absorption used in the displayed construction.  This new
continuation still has semantic pair

```text
((0,0,-delta),(0,0,-delta)),
```

because all `a,m` rewards are zero and player `o` depends only on whether `m`
Quits.  Its deleted-`m` packet survival is exactly `lambda`, and comparing the
source in which `m` Continues with the endpoint in which `m` surely Quits
restores the `{a,m}` prescribed atom of size `1-lambda`.

The latent labels `A/B` are a representation of the original mixed stopping
law, not an observable state or a compulsory field of a behavioral strategy.
Thus Bayes conditioning forces `hatLambda` only if the reprojection must retain
that selected complete latent-plan mixture.  Such fixed-port retention is a
strictly stronger requirement than the question's allowed construction of a
new continuation.  The example remains a sharp nonidentifiability warning:
semantic data alone cannot certify that a *preselected* port transports.  It
is not an acceptable counterexample to existential conditioned reprojection.

This distinction also confirms the scope of Cedar's seam-only adapter.  That
adapter permits newly chosen literal roots and verifies their two-label clock
condition separately; it never asks Bayes conditioning to preserve a latent
mixture label.  The external example therefore does not obstruct the adapter.
What remains open is the positive producer: synthesize new executable roots
that simultaneously satisfy the artificial Bellman/seam data, actual atom or
clock incidence, and the reached-source chronology.

## Concrete requested repairs

1. Replace “exactly matching terminal-semantic laws” by “exactly matching
   terminal semantic pairs; outcome-law distance at most `2delta`.”
2. Replace the claimed `QuittingVanishingDebtAtomAccess` instance by a literal
   prescribed-arm `HasQuittingStoppingLawVanishingDebtAtomAlternative`
   instance.
3. Distinguish reset scale `delta` from diffuse normalized temporal mesh.
4. Qualify `Omega_L` by common component residual laws and positive
   denominators, and call it a sufficient posterior-stability repair.
5. Use `q/(16KR)` for a statement uniform over the rectangle atom arm, or
   retain `q/(8KR)` only for the prescribed arm.
6. Reclassify the example as a fixed-port nonidentifiability diagnostic, not a
   negative answer to an existential reprojection constructor, unless the
   input explicitly includes retention of the complete latent stopping-law
   mixture.
