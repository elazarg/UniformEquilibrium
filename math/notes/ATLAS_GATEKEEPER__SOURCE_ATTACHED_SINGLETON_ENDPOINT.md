# Source-attached singleton endpoints: exact leakage and a no-go

## Status

The declaration-level audit is complete.  The source-attached minimum-law
singleton construction contains substantially more information than a
`QuittingReprojectionConcentratedPacket`, but the most natural proposed use of
that information is false: owner clock compression does not automatically
produce a nonzero deletion, premium, or charge.

What *is* forced is an exact minimum-debt leakage account.  Along cofinally
near-minimum reference profiles, every fixed prescribed-payoff gain obtained
by changing the singleton owner must reappear asymptotically in the aggregate
debt of the other players.  Thus a fixed profitable owner deletion **without
cap/debt leakage is impossible** at the positive minimum.  This is a genuine
no-go at the actual source interface, not another classification of the
generic concentrated packet.

The remaining productive target is consequently not “use the compressed
owner as an exact deletion.”  It is to consume the forced recipient leakage as
a source-matched response square, or to add a separately proved target
minimum-fiber/no-support-entry fact.

## Question checked

Starting from the minimum-law singleton arm of
`FinFourMinimumAtomProducer`, do its fields omitted by the generic
`QuittingReprojectionConcentratedPacket` force any of:

1. exact owner deletion without cap leakage;
2. positive prescribed-payoff charge/return; or
3. minimum-fiber support descent?

The first candidate is falsified below in its strongest useful form.  The
second is not supplied because the clock compression can have zero amplitude.
The third needs a target-side minimum/support fact not present in the source.

## Exact declarations inspected

### Source-attached data

`Research/Quitting/FinFourProducerAtlas/Source.lean`

* `FinFourMinimumAtomProducer`
* `FinFourMinimumAtomProducer.minimumDebt_pos`
* `FinFourLowTailRow`

`Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`

* `FinFourMinimumAtomChronology`
* `FinFourMinimumAtomChronology.prefixedTailMass`
* `FinFourMinimumAtomChronology.tendsto_prefixedTailMass`
* `FinFourOwnerCompressedSingletonEndpoint`
* `FinFourOwnerCompressedSingletonEndpoint.referenceProfile`
* `FinFourOwnerCompressedSingletonEndpoint.targetProfile`
* `FinFourOwnerCompressedSingletonEndpoint.rootStack_nash`
* `FinFourOwnerCompressedSingletonEndpoint.targetProfile_other_eq`
* `FinFourOwnerCompressedSingletonEndpoint.targetProfile_owner_of_ne`
* `FinFourOwnerCompressedSingletonEndpoint.targetProfile_postDate_liveRoot_eq`
* `FinFourOwnerCompressedSingletonEndpoint.targetProfile_ownerCap_eq`
* `FinFourMinimumAtomChronology.nonempty_ownerCompressedSingleton`
* `FinFourOwnerCompressedSingletonProducer`
* `FinFourOwnerCompressedSingletonProducer.nonempty_endpoint`

`Research/Quitting/AnchoredSingletonClockCompression.lean`

* `exists_least_positive_quittingAnchoredOwnerFiniteStopMass`
* `quittingAnchoredSingletonTailMass_le_total_mul_exposure`
* `quittingStageCoalitionMass_anchoredSingletonQuitProfile_eq_exposure`
* `exists_quittingAnchoredSingletonClockCompression`

`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMinimumLawFiniteAtom.lean`

* `minimumTerminalSemantic_strictSingleton_of_punishmentNormal`

`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`

* `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal`

### Generic packet data

`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionTemporalSplit.lean`

* `QuittingReprojectionConcentratedPacket`

`Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacket.lean`

* `FinFourSingletonStageStrongConcentratedPacket`
* `FinFourOwnerCompressedStrongConcentratedPacket`
* `FinFourOwnerCompressedSingletonProducer.nonempty_strongConcentratedPacket`

`Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean`

* `HasQuittingConcentratedSingletonStrategicDispatch`
* `QuittingTerminalExploitabilityWitness.concentratedSingletonStrategicDispatch`

`Research/Quitting/ConcentratedSingleton/Compression.lean`

* `QuittingTerminalExploitabilityWitness.concentratedSingletonStrategicDispatch_compress`

The matching maintained obligation is
`questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md`.

## What the generic packet forgets

A `QuittingReprojectionConcentratedPacket` retains a fixed stage-mass floor,
literal one-step semantic prefix data, a strict subsequence, and vanishing
normalized local defect for its selected packet owner.  It has no field saying
that its profiles approach a fixed global minimum, arise after longer exact
cap--Nash source stacks, share one source chronology, or are related to a
reference profile by one owner/date update.

The minimum-singleton origin retains all of the following extra data:

* one fixed hard residual and positive global minimum point;
* joint semantic/law convergence to that point;
* one common chronology of exact cap--Nash source stacks of length `n+1`;
* convergence of the *reference-prefix* debt to `D_*`;
* a target made by changing only the singleton owner at one selected date;
* literal equality of every opponent strategy and every post-date live root;
* exact invariance of the owner's unrestricted behavioral cap; and
* cofinal availability beyond every requested source depth.

The exactness warning is material: `rootStack_nash` is certified over the
unmodified source suffix.  It is not a cap--Nash certificate after the later
owner update, since that update may change continuation caps seen by the
copied roots.

## The exact leakage theorem

The following statement is ordinary mathematics; it has not been packaged as
one Lean declaration.

Let `D_*` be the global minimum of total terminal semantic debt.  Let
`sigma` be any actual behavioral profile and let `tau` be obtained by changing
only player `o`'s prescribed behavior (in particular, one may take an
`FinFourOwnerCompressedSingletonEndpoint` reference and target).  Assume
player `o`'s unrestricted cap is unchanged:

$$
B_o(\tau)=B_o(\sigma).
$$

Put

$$
g=U_o(\tau)-U_o(\sigma),
\qquad e=D(\sigma)-D_*\ge 0.
$$

Then

$$
\boxed{d_o(\tau)=d_o(\sigma)-g}
\tag{1}
$$

and

$$
\boxed{
\sum_{j\ne o}\bigl(d_j(\tau)-d_j(\sigma)\bigr)
\ge g-e.}
\tag{2}
$$

Indeed, (1) is immediate from cap invariance.  Since `tau` is an actual
profile in the same table, global minimality gives

$$
D_*\le D(\tau)
=D(\sigma)-g+
 \sum_{j\ne o}(d_j(\tau)-d_j(\sigma)).
$$

Rearrangement gives (2).

Now choose owner-compressed endpoints cofinally on their one common
chronology, with ranks tending to infinity.  The chronology field
`prefix_debt_tendsto` gives `e_n -> 0`.  Therefore

$$
\boxed{
\liminf_n\sum_{j\ne o}
  (d_j(\tau_n)-d_j(\sigma_n))
\ge \liminf_n g_n.}
\tag{3}
$$

In particular, if `g_n >= g_0 > 0`, some fixed recipient after a subsequence
satisfies

$$
d_j(\tau_n)-d_j(\sigma_n)
\ge \frac{g_0}{6}
$$

eventually on `Fin 4` (the constant can be taken arbitrarily close to
`g_0/3`; `g_0/6` avoids endpoint bookkeeping).

### Consequence: no leakage-free profitable deletion

If every other debt is nonincreasing,

$$
d_j(\tau)\le d_j(\sigma)\quad(j\ne o),
$$

then (2) forces

$$
g\le e.
\tag{4}
$$

Along the cofinal minimum chronology, `e_n -> 0`.  Hence an owner update with
no other-coordinate debt leakage can have only `g_n -> 0`.  A fixed positive
owner-debt deletion with no leakage would put the actual target below the
global minimum and is therefore impossible.

This is the opposite of the hoped-for automatic deletion theorem.  Positive
minimum provenance does not make leakage go away; it forces leakage to pay
for every profitable deletion.

## Why clock compression supplies no positive charge

The anchored compression selects the least post-anchor date having positive
owner stop mass and forces the owner to Quit there.  Its mass conclusion is a
lower bound on the **target** singleton mass.  It is not a lower bound on the
amount of behavior changed.

Write `p` for the source owner's live quit probability at the selected date,
`L` for live reach, and `m` for opponents' Continue probability at that row.
Then the source and target singleton masses at the row are

$$
Lpm,\qquad Lm,
$$

so the newly exposed mass is

$$
Lm(1-p).
\tag{5}
$$

The endpoint theorem lower-bounds `Lm`, not `Lm(1-p)`.  It permits `p=1`, in
which case `targetProfile = referenceProfile` and every prescribed-payoff,
cap, debt, and law difference is exactly zero.

This boundary is compatible even with strict prescribed-payoff separation
above the owner's singleton reward.  For example, before the owner's first
supported date an opponent may quit with positive probability and give the
owner a high payoff; conditional on survival, the owner then Quits surely at
its first supported date.  The owner's average payoff can be strictly above
its singleton reward while forcing Quit at the selected date changes nothing.

Therefore neither the fixed stage-mass floor nor the hard residual's uniform
minimum-fiber singleton gap turns the owner compression into positive charge.
An additional lower bound on update amplitude `1-p` would still not determine
the sign of the owner's payoff change, because the actual post-row Continue
value is not controlled by the global average singleton gap.

## The one additional object genuinely produced by leakage

When (3) gives a fixed recipient `j`, a near-best response of `j` at `tau_n`
produces a literal same-response square.  If `rho_n` is `epsilon_n`-optimal
against `tau_n`, then

$$
\begin{aligned}
&[U_j(\tau_n[j\leftarrow\rho_n])-U_j(\tau_n)]\\
&\quad-[U_j(\sigma_n[j\leftarrow\rho_n])-U_j(\sigma_n)]
\ge d_j(\tau_n)-d_j(\sigma_n)-\epsilon_n.
\end{aligned}
\tag{6}
$$

This square is actual and source-matched: `sigma_n` and `tau_n` differ only at
the displayed owner/date, and the same complete behavioral deviation is used
on both sides.  It is the weakest nonvacuous positive object forced by a fixed
profitable compression.

Equation (6) still does not answer
`FIN4_ATLAS_CONCENTRATED_SINGLETON`: it supplies no exact punishment-floor
chronology, no target minimum-fiber membership, and no no-new-support fact.
Calling it a charged return would overstate the conclusion.

## Verdict and next exact target

The extra source fields do not by themselves yield exact deletion, charged
return, or support drop.  They yield the exact leakage theorem (1)--(3), and
they turn any fixed profitable compression into the source-matched response
square (6).  The automatic deletion candidate is decisively false; the
compression can even be the identity.

The narrow next theorem worth attempting is not another packet adapter:

> Starting from the cofinal leakage square (6), use the retained near-minimum
> reference chronology and hard-residual data to produce either an actual
> punishment-floor charged chronology or a target cluster on the minimum
> fiber with strict positive-debt support loss.

Without that consumption, the source-attached fields sharpen the obstruction
but do not contract the atlas.

