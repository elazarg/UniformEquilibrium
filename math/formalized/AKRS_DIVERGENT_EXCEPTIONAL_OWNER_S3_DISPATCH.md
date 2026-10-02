# Divergent exceptional-owner sources close through instant punishment or S.3

Authors: CODEX_RAMSEY  
Independent reviews:
[CODEX_EULER](../feedback/CODEX_RAMSEY__AGKRS_DIVERGENT_EXCEPTIONAL_OWNER_S3_DISPATCH__BY_CODEX_EULER.md),
[CODEX_MINER](../feedback/AGKRS_DIVERGENT_EXCEPTIONAL_OWNER_S3_DISPATCH__BY_CODEX_MINER.md)

## Exact statement

Let `I` be a finite type with decidable equality, and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a finite quitting-game reward table, normalized so that Never quitting
pays zero.

Let

```text
source : QuittingUniqueExceptionalOwnerSource r
```

and suppose its selected horizons diverge:

```text
Tendsto
  (fun n => source.family.horizon (source.selected n)) atTop atTop.
```

Then

```text
QuittingInstantPunishmentεEquilibriumExistence r ∨
QuittingWellSupportedAbsorbingSequenceExistence r.
```

Equivalently, the source produces AGKRS branch S.2 or branch S.3.

In particular, for every

```text
residual : QuittingDivergentNegativeExceptionalOwnerResidual r
```

the same disjunction holds.  This is a strengthening: the residual's strict
negative-solo field is not needed.

## Conjecture-facing change

The maintained question
[`AGKRS_THEOREM_3_4_SOURCE_CLOSURE.md`](../questions/AGKRS_THEOREM_3_4_SOURCE_CLOSURE.md)
reduces the corrected paper argument to three source consumers.  Its third
consumer was open: a divergent unique exceptional owner with negative
singleton self-payoff had to reach S.1, S.2, or S.3.

This packet completely removes that third residual class.  It supplies
exactly the second-or-third disjunction accepted by the `hnegative` argument
of `theorem3_4_of_prioritizedSourceClosures`.  The two remaining obligations
are unchanged:

1. the prioritized corrected-pointwise residual; and
2. the positive-joint-reach endpoint with no sure-exit Nash prefix.

Thus this is not a proof of AGKRS Theorem 3.4, but it is a strict reduction
from three maintained source classes to two.

## Definitions and assumptions

### The actual source

`QuittingUniqueExceptionalOwnerSource r` retains:

* a literal `QuittingDiffuseStationaryPrefixFamily r`;
* one exceptional owner `o`;
* a strict source selection `selected : ℕ → ℕ`;
* vanishing joint survival through each selected repeated prefix;
* a strictly positive limit of the selected owner-deleted prefix survival;
* vanishing selected player-deleted prefix survival for every player other
  than `o`.

The family at an index `k` contains a product row `root k`, a finite repeated
horizon `horizon k`, a punished-player label, an actual punishment suffix,
and a positive error `e_k`.  Its full stationary-prefix-then-punishment root
sequence is a terminal `2e_k`-Nash profile.  The errors tend to zero and every
one-row joint Continue mass is positive.

The additional hypothesis of the theorem is divergence of the selected
horizons.  The checked exceptional-clock estimates then imply that the actual
initial payoff vector

\[
 V_n(i)=\texttt{quittingStationaryPrefixFamilyValue}
   (\texttt{source.family})(\texttt{source.selected }n)(0)(i)
\]

converges coordinatewise to the exceptional owner's singleton vector
`r({o})`.

### The output branches

`QuittingInstantPunishmentεEquilibriumExistence r` means that for every
positive error there is a terminal approximate Nash profile with a sure
first-stage quitter and a stationary punishment row holding that quitter
within the displayed error of its exact behavioral punishment value.

`QuittingWellSupportedAbsorbingSequenceExistence r` means that for every
positive `delta` there is a completely absorbing product-root sequence such
that, at every date and for every player, each action used with positive
probability is within `delta` of the other pure endpoint against the sequence's
actual next-tail payoff.  This is checked equivalent, after the harmless
factor-two adapter, to the paper's sequentially approximately perfect S.3
branch.

All product rows use independent player randomization.  A unilateral deviator
in the source Nash inequalities may replace its entire history-dependent
behavioral strategy.

## Proof

### Lemma 1: source individual rationality excludes the floor obstruction

Write `e_n=source.family.error (source.selected n)`.  The source's root
sequence is terminal `2e_n`-Nash against arbitrary unilateral behavioral
deviations.  The exact punishment value is below the best-reply value against
every behavioral profile.  Therefore, for every player `i`,

\[
                         P_i-2e_n\le V_n(i).                  \tag{1}
\]

This is the direct composition of the checked root-sequence/behavioral-Nash
equivalence and behavioral individual rationality.  Since `e_n→0` and source
concentration gives `V_n(i)→r_i({o})`, passing to the limit yields

\[
                              P_i\le r_i(\{o\}).              \tag{2}
\]

At `i=o`, (2) rules out the strict alternative
`r_o({o})<P_o` in
`QuittingDivergentNegativeExceptionalOwnerResidual.instant_or_floorAboveSolo_or_joinGain`.
The argument does not identify the punished player with `o`.

### Lemma 2: a singleton floor produces literal S.3

Fix an owner `o` and assume

\[
                    r_i(\{i\})\le r_i(\{o\})
                    \quad\text{for every }i.                 \tag{3}
\]

We prove `QuittingWellSupportedAbsorbingSequenceExistence r`.

Let `M` be the canonical nonnegative reward bound and fix `delta>0`.  Set

\[
 q=\min\!\left\{\frac12,\frac{\delta}{4M+2}\right\}.
\]

Then `0<q<1` and `2Mq<delta`.  Repeat forever the product row in which `o`
Quits with probability `q` and every other player Continues surely.  Survival
through `N` stages is `(1-q)^N`, so the sequence is completely absorbing.
Every tail payoff is exactly the singleton vector `r({o})`.

At that tail, `o`'s Quit and Continue endpoints are equal.  For `i≠o`, the
Continue endpoint is `r_i({o})`, whereas the Quit endpoint is

\[
                 (1-q)r_i(\{i\})+q r_i(\{o,i\}).             \tag{4}
\]

By (3) and the reward bound, the excess of (4) over Continue is at most

\[
 q\bigl(r_i(\{o,i\})-r_i(\{o\})\bigr)\le 2Mq<\delta.         \tag{5}
\]

Both of `o`'s used actions are exactly optimal.  Each other player uses only
Continue, and (5) is precisely the required support-local inequality for that
used action.  Hence the constant root sequence is a well-supported absorbing
witness at `delta`.  Since `delta` was arbitrary, S.3 follows.

The proof deliberately does not claim terminal Nash.  If `r_o({o})<0`, the
owner may profit by Continuing forever; S.3 only asks for the displayed
sequential row-perfectness and complete absorption of the prescribed
sequence.

### The source dispatch

First select a strict subsequence on which the finite label

```text
n ↦ source.family.punished (source.selected n)
```

is constant.  On that subsequence, compactness of `[0,1]` supplies a further
strict subsequence on which the one-row joint Continue mass converges to some
`lambda∈[0,1]`.  Compose both selections explicitly with `source.selected`.
Strictness, horizon divergence, source concentration, and vanishing error all
survive.

There are three cases.

#### `lambda=0`

The selected literal family has one-row live mass tending to zero.  The
checked
`quittingInstantPunishment_of_stationaryPrefix_liveMass_tendsto_zero`
therefore supplies S.2.

#### `0<lambda<1`

The fixed punished label and divergent horizons meet the hypotheses of
`exists_quittingPositiveLiveStationaryPrefixLimit_with_liveMass_eq`.  Choose
the returned limit.  Its recorded live mass is exactly `lambda`, hence is
strictly below one.  The checked
`QuittingPositiveLiveStationaryPrefixLimit.wellSupported_of_lt_one` supplies
S.3.

#### `lambda=1`

Let `c_n` be the selected full one-row Continue mass and let `d_{n,i}` be the
Continue mass after deleting player `i`'s hazard.  The product identity gives

\[
                  c_n=d_{n,i}p_{n,i},\qquad 0\le p_{n,i}\le1.
\]

Thus `c_n≤d_{n,i}≤1`, and `c_n→1` implies `d_{n,i}→1` for every `i`.

Let `Q_n(i)` be player `i`'s immediate-Quit value at the same selected root.
The checked estimate
`abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le` now gives

\[
                         Q_n(i)\longrightarrow r_i(\{i\}).    \tag{6}
\]

The source's immediate-Quit consequence of its unrestricted Nash field is

\[
                         Q_n(i)\le V_n(i)+2e_n.               \tag{7}
\]

Using (6), source concentration `V_n(i)→r_i({o})`, and `e_n→0`, the limit of
(7) is exactly the singleton floor (3).  Lemma 2 gives S.3.

These cases exhaust `[0,1]`, proving the theorem.

## Probability and deviation audit

* The source Nash premise is not stationary-only.  The checked equivalence
  identifies `IsεQuittingRootSequenceNash` with terminal Nash against every
  unilateral behavioral strategy, including history-dependent and Never
  deviations.
* Inequality (1) uses the behavioral best-reply infimum defining the exact
  punishment value.  It is not inferred from the selected punishment suffix
  or from a pure-time deviation.
* The compact selections concern only finite labels and real one-row live
  masses.  No probability is conditioned on a vanishing event.
* Equation (6) is an unconditional date-zero product-law estimate.  The full
  Continue mass is bounded above by every player-deleted Continue mass, so
  all relevant opponent-absorption probabilities vanish together.
* Lemma 2 uses fresh independent Bernoulli randomization at each live stage.
  Its absorption proof is the exact geometric product limit.  It makes no
  claim about the payoff from arbitrary behavioral deviations, because S.3
  does not require such a claim.

## Boundary tests

1. **Negative owner.**  Take `r_o({o})<0`.  The solo S.3 sequence remains
   support-perfect at `o`, although Never can be a profitable global
   deviation.  This confirms the proof lands in literal S.3, not terminal
   Nash.
2. **Maximal collision.**  Let
   `r_i({i})=r_i({o})=-M` and `r_i({o,i})=M`.  No positive solo rate is an
   exact endpoint equilibrium for `i`, but its support defect is exactly
   `2Mq` and is made smaller than every requested `delta`.
3. **Vanishing live limit.**  Positive live mass at each finite source row
   can still converge to zero.  The proof keeps this case and routes it to the
   checked instant consumer rather than dividing by the limit.
4. **Interior live limit.**  Any `lambda∈(0,1)` yields a genuinely absorbing
   compact limiting row and is consumed by the checked positive-live theorem.
5. **All-Continue limit.**  At `lambda=1`, collision payoffs may have either
   sign and outsider join gains may persist.  Only the own-singleton floor is
   extracted; Lemma 2 absorbs the collision error by taking `q→0` with the
   requested tolerance.
6. **Punished-label mismatch.**  The punished player is fixed only for the
   compact positive-live theorem.  It is never assumed equal to the
   exceptional owner.
7. **One player.**  The singleton floor is equality and the constant positive
   solo hazard gives the S.3 sequence directly.

## Source correspondence

The source structure and clock fields are checked in
`UniformEquilibrium/Quitting/Classification/Existence/DiffuseStationaryPrefixSourceAttachments.lean`.
Horizon divergence and the existing negative residual are in
`DivergentExceptionalOwnerHazard.lean` and
`StationarilyGeneratedNegativeOwnerBoundary.lean`.

The checked probabilistic concentration and immediate-Quit source inequality
are

* `QuittingUniqueExceptionalOwnerSource.tendsto_initialValue_soloReward`; and
* `QuittingUniqueExceptionalOwnerSource.fixedOpponentsQuitValue_le_initialValue`

in `ExceptionalOwnerPrefixConcentration.lean`.

The existing live-limit consumers are

* `quittingInstantPunishment_of_stationaryPrefix_liveMass_tendsto_zero` in
  `StationarilyGeneratedWitnessRegimes.lean`;
* `exists_quittingPositiveLiveStationaryPrefixLimit_with_liveMass_eq`; and
* `QuittingPositiveLiveStationaryPrefixLimit.wellSupported_of_lt_one`

in `StationarilyGeneratedPositiveLiveLimit.lean`.

The immediate-Quit estimate is in
`Cycles/ConditionedDiffuseStrategicRescaling.lean`.  The solo terminal-value
and endpoint formulas are in `Cycles/SoloRootSequenceValues.lean` and
`Punishment/SoloQuitterEquilibrium.lean`.  The S.3 adapter is in
`Classification/Existence/WellSupportedAbsorbingSequence.lean`.

The paper-facing consumer is the `hnegative` argument of
`theorem3_4_of_prioritizedSourceClosures` in
`Literature/AshkenaziGolanKrasikovRainerAndSolan2022.lean`.  The paper's
Theorem 3.4 requires one fixed S.1/S.2/S.3 branch at every sufficiently small
error; the checked capstone preserves that quantifier and accepts the global
S.2 or S.3 existence predicates produced here.

A narrow source search found no declaration consuming every divergent unique
exceptional-owner source.  Existing solo completion theorems either produce a
uniform payoff under punishment individual rationality or assume positive
own-solo payoffs.  The new content is the singleton-floor well-supported S.3
compiler and its actual-source live-limit composition.

## Adapter and consumer

The actual-data adapter is literal:

```text
residual.source
residual.horizon_tendsto
```

are exactly the hypotheses of the main theorem for any
`QuittingDivergentNegativeExceptionalOwnerResidual r`.

The theorem's instant output is already AGKRS S.2.  Its well-supported output
is converted by
`quittingSequentiallyεPerfectAbsorbingExistence_of_wellSupported` to AGKRS
S.3.  These inject directly into the `hnegative` codomain of
`theorem3_4_of_prioritizedSourceClosures`; there is no further producer,
selection, or source-matching premise.

## Lean handoff

The narrow formalization order is:

1. Prove a standalone theorem, perhaps named
   `quittingWellSupportedAbsorbingSequenceExistence_of_singletonFloor`, with
   hypotheses `(owner : I)` and
   `∀ i, quittingSoloReward r i i ≤ quittingSoloReward r owner i`.
   Use `quittingHazardCoin`, the solo endpoint formulas, and
   `quittingRootSequenceTerminalValue_eq_soloReward_of_absorbing`.
2. Prove the source individual-rationality lemma
   `source.quittingPunishmentValue_le_soloReward` by composing
   `isεQuittingRootSequenceNash_iff_isεAsymptoticNash`,
   `punishmentValue_sub_le_terminalPayoff_of_isεAsymptoticNash`, selected-error
   convergence, and `source.tendsto_initialValue_soloReward`.
3. Select the punished label, then the live-mass limit, keeping the composed
   strict subsequence explicit.
4. In the unit-limit arm, derive player-deleted Continue convergence from the
   product identity before applying
   `abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le` and
   `source.fixedOpponentsQuitValue_le_initialValue`.
5. State the source theorem with the exact S.2-or-well-supported-S.3 codomain,
   then add the one-line negative-residual and paper-capstone adapters.

Do not formalize the conclusion as terminal Nash, uniform payoff, or an
instant-punishment claim in the unit-live arm.

## Scope and nonclaims

This packet closes only the divergent unique-exceptional-owner source class.
It does not consume either remaining AGKRS source residual and does not prove
Theorem 3.4 unconditionally.  It does not show that the explicit solo S.3
sequence is a terminal approximate Nash profile or a uniform equilibrium.
It does not construct a punishment-floor Bellman orbit, a paid return, or a
finite support descent.  Outsider singleton-collision gains are allowed and
are absorbed only as an `O(q)` support defect.

## Checked Lean realization

The packet is realized in
`UniformEquilibrium/Quitting/Classification/Existence/DivergentExceptionalOwnerS3Dispatch.lean`.
The checked declarations are:

- `quittingWellSupportedAbsorbingSequenceExistence_of_singletonFloor`, the
  support-local solo-hazard compiler into literal S.3;
- `QuittingUniqueExceptionalOwnerSource.quittingPunishmentValue_le_soloReward`,
  the unrestricted-behavior individual-rationality limit;
- `QuittingUniqueExceptionalOwnerSource.instantPunishment_or_wellSupported`,
  the exhaustive zero/interior/unit live-mass dispatch; and
- `QuittingDivergentNegativeExceptionalOwnerResidual.instantPunishment_or_wellSupported`,
  the actual residual adapter.

The downstream paper consumer is
`theorem3_4_of_prioritizedAndPositiveSourceClosures`
(`Literature/AshkenaziGolanKrasikovRainerAndSolan2022.lean`). It discharges the
former exceptional-owner hypothesis of
`theorem3_4_of_prioritizedSourceClosures`, leaving exactly the prioritized
pointwise and positive-joint/no-sure-exit consumers.

Evidence seals:

- `M`: the packet passed two independent mathematical reviews and a further
  packet-to-Lean audit;
- `L`: all four production declarations above are checked by Lean;
- `A`: the residual adapter uses the literal `source` and
  `horizon_tendsto` fields of every supplied divergent negative exceptional
  owner; and
- `C`: the checked Literature capstone maps S.2 and well-supported S.3 into
  the paper's fixed small-error branch conclusion.

The unconditional `theorem3_4` is still open. The checked capstone assumes
universal consumers for the two remaining source classes, and the explicit
solo S.3 sequence is not claimed to be terminal Nash or a uniform
equilibrium.
