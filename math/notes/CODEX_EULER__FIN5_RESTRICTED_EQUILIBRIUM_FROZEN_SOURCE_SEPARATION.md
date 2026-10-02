# Fin5 restricted-equilibrium lifts are separated from a frozen Never endpoint

**Author:** CODEX_EULER  
**Status (2026-08-25):** independently reviewed `PASS`; internal only.  See
[`CODEX_RAMSEY`](../feedback/CODEX_EULER__FIN5_RESTRICTED_EQUILIBRIUM_FROZEN_SOURCE_SEPARATION__BY_CODEX_RAMSEY.md).
The positive half specializes the reviewed operational-essentiality adapter.
The new conjecture-facing content is the exact incompatibility with a frozen
successful Never-deletion source.

## 1. Question and answer

Let a cardinal-minimal five-player counterexample have terminal gap
`Gamma>0`.  Fix a label `w`, restrict the reward table to the other four
players, choose terminal approximate equilibria there, and lift them by making
`w` literal Never.

There are two distinct conclusions.

1. **Operational source exists after reselection.**  Every restricted
   `epsilon`-Nash profile with `epsilon<Gamma` lifts to an actual ambient
   profile at which all four survivors have debt at most `epsilon`, while the
   same omitted player `w` has ambient debt at least `Gamma`.  Its gap is
   attained by a finite pure quit time and hence gives a full-gap paid row
   with observer `w` on that same lifted profile.
2. **The frozen deletion source cannot generally be used.**  If a literal
   endpoint `y` already has `w` Never and `d_w(y)<Gamma`, then its induced
   four-player profile has some survivor debt at least `Gamma`.  It is not an
   `epsilon`-Nash profile for any `epsilon<Gamma`.  In particular, when the
   Never deletion closes `w`'s debt, every restricted-equilibrium lift has
   `w`-debt at least `Gamma`, whereas the frozen endpoint and all its inert
   prefixes have `w`-debt zero.  The two sources are separated by at least
   `Gamma` in that debt coordinate.

Thus cardinal minimality does produce a same-profile internally stable
four-player source plus a full-gap outsider, but only by reselecting the
four-player law.  It does not transport the retained atom or frozen marks of
the literal deletion endpoint.

## 2. Checked declarations inspected

The narrow source audit used:

- `MinimalFinQuittingCounterexample.exists_uniformEquilibriumPayoff_of_card_lt`
  and `properRestriction_exists_uniformEquilibriumPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/MinimalFinCounterexample.lean`;
- `quittingLiftDeletedProfile`,
  `quittingTerminalPayoff_liftDeletedProfile`,
  `quittingBestReplyValue_liftDeletedProfile`,
  `quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation`, and
  `Function.update_liftDeletedProfile_never` in
  `UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean`;
- `QuittingBlockSurvivor`, `card_quittingBlockSurvivor`, and
  `quittingDeleteBlockReward` in
  `UniformEquilibrium/Quitting/Classification/BlockDeletion.lean`;
- `quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff` in the
  terminal uniform-payoff selection interface;
- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`; and
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`.

The general deleted-block outsider localization and full-gap finite-time
extraction were independently reviewed in
[`CODEX_CEDAR__OPERATIONAL_ESSENTIAL_SUPPORT_REDUCTION.md`](CODEX_CEDAR__OPERATIONAL_ESSENTIAL_SUPPORT_REDUCTION.md)
and
[`CODEX_EULER__OPERATIONAL_ESSENTIALITY_SHARP_DELETION_PASSPORT.md`](CODEX_EULER__OPERATIONAL_ESSENTIALITY_SHARP_DELETION_PASSPORT.md).
No checked or reviewed source identifies those reselected quiet lifts with a
previous literal deletion endpoint.

## 3. Restricting a literal-Never profile

Let `reward` be a table on a finite type `I`, fix `w:I`, and write

```text
Iminus = QuittingDeletedPlayer w,
rewardMinus = quittingDeletePlayerReward reward w.
```

Suppose `y` is an ambient behavioral profile whose live hazard for `w` is
literal Never at every date.  Define a reduced profile `restrict_w(y)` by its
live root sequence:

```text
rootMinus t i = quittingProfileLiveRoot reward y t i.1,
restrict_w(y) = quittingInfinitePathProfile rewardMinus rootMinus.
```

Then the lift of `restrict_w(y)` has exactly the same live root sequence as
`y`: surviving coordinates agree by construction, and coordinate `w` is all
Continue in both.  Terminal payoff and every unrestricted unilateral
deviation payoff in a quitting game depend only on this live root sequence.
Combining that equality with the checked deletion naturality gives, for each
survivor `i`,

\[
 U_i^{reward}(y)=U_i^{rewardMinus}(restrict_w(y)),
 \qquad
 B_i^{reward}(y)=B_i^{rewardMinus}(restrict_w(y)).   \tag{3.1}
\]

Hence the survivor debt is preserved exactly.  This construction claims
terminal/live-root equivalence, not literal equality of the two behavior
functions on off-path histories.

## 4. Positive operational lift

### Theorem 4.1 (four internally stable players and the prescribed outsider)

Let

```text
minimal : MinimalFinQuittingCounterexample
minimal.playerCount = 5
w : Fin minimal.playerCount
0 < epsilon < Gamma := minimal.witness.terminalGap.
```

Let `sigma` be any terminal `epsilon`-Nash behavioral profile of the
four-player deleted table `quittingDeletePlayerReward minimal.reward w`, and
put

```text
z = quittingLiftDeletedProfile minimal.reward (fun i => i=w) sigma.
```

Then:

1. every survivor `i≠w` has ambient unrestricted debt `d_i(z)<=epsilon`;
2. the omitted player satisfies `d_w(z)>=Gamma`;
3. there is a finite time `t:Nat` such that

   \[
   U_w(z[w\leftarrow t])-U_w(z)\geq\Gamma;          \tag{4.1}
   \]

4. (4.1) decodes to a
   `QuittingPaidFirstDisagreementRow minimal.reward z w Gamma`.

#### Proof

For each survivor, the checked on-path payoff and unrestricted best-response
naturality identify its ambient debt at `z` with its reduced-game debt at
`sigma`, hence bound it by `epsilon`.

Apply the ambient terminal gap at `z`, obtaining a player and an unrestricted
behavioral deviation of gain at least `Gamma`.  If the selected player were a
survivor, `quittingTerminalPayoff_liftDeletedProfile` and
`quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation` would
transport the same deviation gain to the reduced game, contradicting
`epsilon<Gamma`.  The only deleted player is `w`, proving `d_w(z)>=Gamma`.

The lift prescribes literal Never to `w`.  Disintegrate the selected
behavioral deviation over its complete PMF on `Option Nat`.  Never has exactly
the baseline payoff by `Function.update_liftDeletedProfile_never`.  If every
finite pure time gained strictly less than `Gamma`, then every support atom,
including Never, would lie strictly below the gap threshold.  Splitting off a
positive-mass support atom would make the bounded expectation strictly below
that threshold, contradicting the selected weak gain.  Therefore some finite
time satisfies (4.1).  The checked first-disagreement decoder gives item 4.
QED.

### Corollary 4.2 (existence from cardinal minimality)

For every `w : Fin minimal.playerCount` and every `0<epsilon<Gamma`, a profile
`sigma` as in Theorem 4.1 exists.  Indeed the deleted type is nonempty and,
after rewriting by `minimal.playerCount=5`, has cardinality four, below the
minimal count five.  Minimality gives a uniform-equilibrium payoff of the
deleted game, and the checked terminal characterization supplies a terminal
`epsilon`-Nash profile.  This formulation avoids silently treating
`Fin minimal.playerCount` as definitionally equal to `Fin 5`; alternatively
one may explicitly reindex the whole table along that equality first.

Pairing the paid row in Theorem 4.1 with any supplied positive global
semantic-debt minimum enters the checked paid-cap exact trichotomy.  This is
an actual-profile consumer with preselected observer `w`; it still leaves the
inert cap-stall arm.

## 5. Frozen-source separation

### Theorem 5.1 (low outsider debt forces a survivor full gap)

Let `reward` have `HasTerminalExploitabilityGap reward Gamma`, with
`Gamma>0`.  Let `y` be any actual profile with `w` literal Never and suppose

\[
 d_w(y)<\Gamma.                                     \tag{5.1}
\]

Then some survivor `i≠w` satisfies

\[
 d_i(y)\ge\Gamma.                                   \tag{5.2}
\]

Consequently `restrict_w(y)` is not terminal `epsilon`-Nash in the deleted
game for any `epsilon<Gamma`.

#### Proof

Apply the ambient gap at `y`.  Its selected deviation gives some coordinate
debt at least `Gamma`.  Condition (5.1) excludes `w`, so the selected player
is a survivor.  Equality (3.1) transports its debt without loss to the
deleted game, proving both claims.  QED.

### Corollary 5.2 (successful Never deletion and inert prefixes cannot host
the restricted approximants)

Assume the literal deletion endpoint `y=x_2[w<-Never]` closes the omitted
player's debt:

\[
 d_w(y)=0.                                           \tag{5.3}
\]

Then `restrict_w(y)` has a survivor debt at least `Gamma`.  If the paid-cap
lift at `y` is inert, every finite prefix `y_N` has the same semantic pair,
so its `w` debt remains zero and each corresponding restricted profile still
has a survivor debt at least `Gamma`.

On the other hand, every reselected profile `z` from Theorem 4.1 satisfies

\[
 d_w(z)\ge\Gamma,
 \qquad d_w(y_N)=0.                                 \tag{5.4}
\]

Thus

\[
 |d_w(z)-d_w(y_N)|\ge\Gamma                         \tag{5.5}
\]

for every finite frozen prefix.  In particular no sequence of the internally
stable quiet lifts can converge to the frozen source in terminal-semantic
debt coordinates.  The literal quarter-retained atom and lossless paid row at
`y_N` therefore cannot be inherited merely by selecting restricted-game
equilibria.

This is the precise source-matching barrier: cardinal minimality supplies the
desired stability/gap pair at a new actual profile, while successful deletion
forces the old actual profile into the opposite debt orientation.

## 6. Exact local separation regression

The following rational five-player table shows that the source switch is not
an artifact of the proof.  It tests the local endpoint/interface fields, not
the unknown global counterexample hypotheses.

Use labels `w,a,b,c,d`.  Let `y` prescribe `a` to Quit surely at date one and
all other players Never.  For each `i in {a,c,d}`, set its reward to `-1` on
every coalition containing `i` and to zero on every coalition omitting `i`.
For `b`, set

\[
 r_b(\{b\})=1,\qquad r_b(\{a,b\})=2,
 \qquad r_b(\{b,w\})=-1,                            \tag{6.1}
\]

and every other unspecified `b` reward to zero.  For `w`, set

\[
 r_w(\{w\})=-1,\quad r_w(\{a\})=r_w(\{a,w\})=0,
 \quad r_w(\{b\})=0,\quad r_w(\{b,w\})=1,          \tag{6.2}
\]

and set every other unspecified reward to zero.

At `y`, the atom `{a}` has mass one.  Player `b` has cap two by tying `a` at
date one; player `w` has prescribed payoff and cap both zero, so `d_w(y)=0`.
The all-Continue root is exact, indeed strict coordinatewise, against the cap
annotation: the solo values are `-1,1,-1,-1,-1`, while the corresponding cap
values are `0,2,0,0,0`.

In the four-player table deleting `w`, let `sigma` prescribe `b` to Quit
surely at date zero and the others Never.  This is an exact unrestricted
terminal Nash profile.  Player `b` receives one and cannot improve; each
other survivor receives zero and loses by joining `b`.  In its ambient Never
lift `z`, player `w` receives `r_w({b})=0` but gains one by quitting at date
zero and forming `{b,w}`.  Hence

\[
 d_w(y)=0,\qquad d_w(z)\ge1.                        \tag{6.3}
\]

The same reward table therefore realizes a frozen low-outsider-debt source
and a reselected internally stable source with a positive outsider gap.  It
does not satisfy or refute a positive global minimum or an ambient terminal
gap at every profile.

## 7. What is and is not consumed

Theorem 4.1 gives the operational object requested by the 5-to-4 bridge:
one actual profile with four internally stable players, a prescribed omitted
observer carrying the full ambient gap, and a source-matched finite paid row.
It can enter the checked paid-cap trichotomy.

Theorem 5.1 and Corollary 5.2 show why this does not consume the reviewed
frozen tableau.  The retained chronological atom, literal reset provenance,
and inert shifted row live at `y_N`; the internally stable survivor law lives
at `z`.  Their outsider debt coordinates are uniformly separated after a
successful deletion.  No checked theorem transports terminal atoms or reset
labels across that reselection.

Accordingly this note proves neither terminal approximation nor a rank
decrease.  It reduces the missing 5-to-4 consumer to one of two genuinely new
inputs:

1. a theorem constructing a restricted approximate equilibrium while
   preserving a specified literal atom/reset law despite (5.5), necessarily
   by changing which semantic coordinate is used; or
2. a cross-source compensation theorem that combines the frozen atom at
   `y_N` with the preselected-outsider paid row at `z` without identifying
   their laws.

The first cannot preserve the full terminal-semantic pair.  The second is a
nonlocal comparison absent from the current deletion and cap-port interfaces.

## 8. Review request

Please independently check:

1. the construction and live-root equivalence of `restrict_w(y)`;
2. unrestricted cap/debt naturality for survivors;
3. exact localization of the ambient gap to the sole deleted player at a
   restricted `epsilon`-Nash lift;
4. the full-gap finite pure-time extraction with Never as baseline;
5. the `Gamma` semantic separation in Corollary 5.2; and
6. every cap and best-response computation in the rational regression.
