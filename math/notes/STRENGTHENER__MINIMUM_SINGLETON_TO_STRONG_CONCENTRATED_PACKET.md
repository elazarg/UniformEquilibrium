# A positive stage atom is already a strong concentrated packet source

Author: `STRENGTHENER`

## Status

Ordinary mathematics, independently reviewed and exported, not checked in
Lean. The decisive strengthening is entirely local: at a positive stage atom
`A`, choose any `o` with `A != {o}` and replace `o`'s action **only at that
row** by its exact best pure endpoint against the actual tail. This preserves
the complete past and future, routes the atom without loss to `A.erase o` or
`insert o A`, and makes the selected local defect exactly zero. Repeating that
one target profile supplies the existing
`QuittingReprojectionConcentratedPacket`.

The earlier pure-time near-cap construction is valid but unnecessary. The
one-row construction is exact, has only two routing modes, needs no subsequence
selection, and retains the literal post-row tail.

## Theorem

Let `tau` be any actual behavioral profile in a finite quitting game, let `A`
be a nonempty coalition, fix `o` with `A != {o}`, and suppose

\[
 m:=\Pr_\tau(A\text{ at date }t)>0. \tag{1}
\]

Let

\[
 z^+=\operatorname{Sem}(\operatorname{tail}_{t+1}\tau),
 \qquad x=\operatorname{root}_\tau(t),
\]

and choose

\[
 a=\operatorname{BestEndpoint}_o(r,(z^+)_U,x)\in\{C,Q\}.
\]

Define

```lean
rho := quittingLiteralOneDateProfile reward tau o t a
```

using `quittingLiteralOneDateOverride`, so the entire behavior strategy is
copied at every date other than `t`, including off-live histories. Then:

1. the probability of reaching `t` is unchanged;
2. every live root strictly before and after `t` is unchanged;
3. the post-`t` behavioral tail and its semantic pair are unchanged;
4. the marked atom routes with no loss:
   \[
   \begin{array}{c|c}
   a=C&R=A\setminus\{o\},\\
   a=Q&R=A\cup\{o\},
   \end{array}
   \qquad
   \Pr_\rho(R\text{ at }t)\ge m; \tag{2}
   \]
5. the updated root has exact zero local defect for `o` against the unchanged
   actual tail:
   \[
   \operatorname{Defect}_o((z^+)_U,operatorname{root}_\rho(t))=0. \tag{3}
   \]

For every `lambda` with `0<lambda<=m`, repeat `rho` as a constant profile
sequence, take constant mark `t`, constant cutoff `t+1`, scale
`s_n=1/(n+1)`, identity subsequence, fixed terminal `R`, and resolution
`lambda`. Equations (2)--(3), together with the generic literal spine
identity, fill every field of

```lean
QuittingReprojectionConcentratedPacket
  reward profiles o terminal cutoff scale
```

The normalized defect expression is identically zero, not merely convergent
to zero.

## Proof

The literal one-date override copies the complete behavior strategy except at
`t`, so assertions 1--3 follow directly from its definition and the checked
literal live-mass/tail lemmas. In particular, the probability of reaching the
row is unchanged.

At the old event exactly the members of `A` Quit. If `a=C`, forcing `o` to
Continue removes its old prescribed-action factor and routes to `A.erase o`.
If `a=Q`, forcing it to Quit removes the same factor and routes to
`insert o A`. The assumption `A != {o}` makes the Continue target nonempty;
the Quit target is automatically nonempty. The root-level theorem
`quittingRootCoalitionMass_le_pureEndpointRouted`, multiplied by the unchanged
live mass, gives (2) without division.

The two pure endpoint payoffs for `o` depend on the opponents' root and on the
tail, not on `o`'s prescribed mixing probability. Hence they are unchanged
when only `o`'s marginal is made pure. By definition,
`quittingRootBestEndpointAction` selects their maximum. The prescribed
successor payoff under the pure updated marginal is therefore exactly that
maximum, and the coordinate defect—maximum endpoint payoff minus prescribed
successor payoff—is zero. This proves (3).

For the repeated target, stage mass is at least `lambda`, `mark<t+1`, and the
defect numerator is zero for every rank. Positive stage mass invokes
`positive_stageCoalitionMass_has_semanticPrefixIncidence`, supplying current
and tail carrier membership, the exact semantic prefix equation, and positive
root mass. These are all packet fields.

## Atlas consequences

The checked `FinFourAtlasWeakConcentratedSingletonCore` supplies one actual
target profile, one stage, a singleton terminal, a positive resolution, and
`resolution <= stageMass`. Choose any different Fin4 player and apply the
theorem. Thus both weak origins upgrade to a strong packet:

* `.reached`, covering purified-singleton and terminal-orbit singleton leaves;
* `.ownerClock`, covering the minimum-law singleton leaf.

For a selected minimum singleton law of mass `mu`, the checked clock
compression supplies an actual singleton row at every fixed resolution
`lambda<mu`; the theorem then gives a strong packet at that same resolution.

Thus

\[
 \boxed{
 \text{positive actual singleton row}
 \Longrightarrow
 \text{strong concentrated packet with no mass loss},}
\]

and in particular every weak Fin4 singleton atlas origin enters the strong
concentrated node.

This is an interface result, not a structural restriction on games. Given any
finite game with at least two players, play any nonempty pure coalition `A` at
date zero, choose `o` with `A != {o}`, and apply the generic theorem to the
mass-one atom. Hence the packet type is universally inhabitable. The atlas
content lies only in the external attachment to its selected endpoint and
tail; a conjecture-facing consumer must retain and use that provenance.

## Exact provenance and nonclaims

Unlike the pure-time construction, the one-row target retains the complete
post-date tail and every earlier root. It does not, however, make an old copied
cap--Nash stack exact for the changed suffix: cap--Nash exactness depends on
the full continuation caps, not only literal equality of the prefix roots.

The theorem controls one local root defect exactly. It does not assert small
full behavioral debt of `o`, near-minimum total debt, no-new-support,
punishment-floor admissibility, an exact chronological return, terminal
approximation, rank descent, or a uniform-equilibrium payoff. Those are
downstream concentrated-packet obligations.

## Lean handoff

The new local lemma should be generic:

```lean
theorem quittingRootCoordinateNashDefect_update_bestEndpoint_eq_zero
    (tail : Payoff iota) (root : iota -> PMF Bool) (who : iota) :
    quittingRootCoordinateNashDefect reward tail
      (Function.update root who
        (PMF.pure (quittingRootBestEndpointAction reward tail root who))) who = 0
```

Its proof unfolds the endpoint action and defect and splits on the comparison
of Quit and Continue values.

Then combine:

* `quittingLiteralOneDateProfile` and `quittingLiteralOneDateOverride`;
* `quittingProfileLiveRoot_literalOneDateProfile`;
* `quittingLiveMass_literalOneDateProfile_eq`;
* `quittingProfileLiveRoot_literalOneDateProfile_tail_eq`;
* `quittingRootCoalitionMass_le_pureEndpointRouted`;
* `quittingPureEndpointRoutedCoalition_four_way`; and
* `positive_stageCoalitionMass_has_semanticPrefixIncidence`.

The source-facing wrappers should first consume
`FinFourAtlasWeakConcentratedSingletonCore`, then expose the sharper arbitrary
`lambda<mu` corollary for `FinFourMinimumAtomProducer`.

## Downstream audit of the stronger actual output

The constant-profile and literal-tail strengthening does not close the
concentrated node.

First, the generic theorem proves that the packet structure is universally
inhabited: choose a pure nonempty coalition at date zero in any game with at
least two players. Therefore no conclusion using only
`QuittingReprojectionConcentratedPacket` can exploit positive-minimum
provenance; that information is absent from the type.

Second, in the singleton Continue-routing mode the exact row improves the
existing asymptotic fact only from

\[
 \max\{Q_o-C_o,0\}\longrightarrow0
\]

to the pointwise sign `Q_o-C_o<=0`. Under a terminal witness,
`concentratedSingletonStrategicDispatch_compress` still returns only an exact
player deletion or `HasQuittingStaticAtomicToggleHandoff`. The strict owner
join can be canceled by the literal tail or by another played coalition even
when the marked coordinate defect is exactly zero; the checked cancellation
identity already permits both cases.

Third, in the Quit-routing mode the marked terminal is `{j,o}` and the packet
enters the existing collision-minimum residual. Purifying the positive
coalition at the same date and following full-gap membership toggles retains
the past and tail, but produces only the already-known horizontal toggle
cycle. It is not an ordered Bellman chronology.

The checked `FourPlayerCyclicPlateauCandidate` is an exact boundary model for
the missing step: it has mass-one pure rows, exact solved local coordinates,
a literal debt-circulating toggle cycle, and unique all-Continue exact cap
roots, while its global minimum is zero. It does not refute a
positive-minimum theorem, but it proves that the local packet data and
horizontal toggle geometry alone cannot manufacture charged exact
chronology. Any successful downstream theorem must use the atlas minimum/source
attachment quantitatively, rather than the stronger packet fields alone.
