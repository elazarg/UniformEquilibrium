# Participant-only quitting rewards always admit an exact stationary equilibrium

Authors: external contributor, `CODEX_RAMSEY`

Independent falsification reviews:

- [`CODEX_EULER`](../feedback/INCENTIVE_GADGET_BREAKTHROUGH_QUITTER_ONLY_AND_TARGET_LOCK__BY_CODEX_EULER.md);
- [`CODEX_RAMSEY`](../feedback/INCENTIVE_GADGET_BREAKTHROUGH_QUITTER_ONLY_AND_TARGET_LOCK__BY_CODEX_RAMSEY.md).

## Exact statement

Let `I` be a finite player type (possibly empty) and

```text
reward : {S : Finset I // S.Nonempty} -> Payoff I
```

a quitting reward table.  Call it **participant-only** when

```text
reward(S)_i=0 whenever i notin S.                   (1)
```

Then there is a stationary product profile which is an exact stationary
terminal Nash profile against every unilateral behavioral strategy.  More
precisely, it satisfies `IsεAsymptoticNash` for terminal payoff and error zero.
Its terminal payoff is a uniform-equilibrium payoff of the quitting game.

For an arbitrary finite reward table, define the passive magnitude with the
empty-index-safe convention

```text
delta(reward)=max(
  {0} union {|reward(S)_i| : S nonempty and i notin S}). (2)
```

Then the game has a behavioral profile of terminal exploitability at most

```text
2 delta(reward).                                    (3)
```

Consequently, any reward table having a fixed terminal exploitability gap
`gamma>0` must satisfy

```text
delta(reward)>=gamma/2.                             (4)
```

Thus every participant-only incentive-gadget architecture is impossible, and
any positive-gap normalized gadget must use a passive reward at the same
quantitative scale as its claimed gap.

## Proof

### 1. One-shot stationary selection

If `I` is empty, the unique empty profile is vacuously exact and every payoff
statement is an equality of empty functions.  Assume henceforth that `I` is
nonempty.

Form the finite binary-action game in which each player chooses Quit or
Continue, a nonempty Quit set `S` pays `reward(S)`, and all-Continue pays zero.
Choose a mixed Nash equilibrium `q=(q_i)_i` of this finite game.

For player `i`, define the pure-Quit value against the opponents' product
mixture by

```text
Q_i=E_(q_-i)[reward(T union {i})_i].                (5)
```

Pure Continue pays exactly zero against every opponents' pure action profile:
if some opponent quits, the terminal coalition omits `i` and (1) applies; if
none quits, the one-shot outcome is all-Continue.  Nash complementarity is
therefore

```text
q_i=0       => Q_i<=0,
0<q_i<1     => Q_i=0,
q_i=1       => Q_i>=0.                              (6)
```

### 2. Repeat the row and compute its payoff

Repeat `q` independently at every live date and put

```text
rho=product_j(1-q_j).
```

If `rho<1`, player `i`'s one-round absorbing contribution is `q_iQ_i`, so its
stationary terminal payoff is

```text
V_i=q_iQ_i/(1-rho).                                 (7)
```

If no player quits surely, every positive `q_i` is interior and its numerator
vanishes.  If some player quits surely, `rho=0`, and (6) handles all three
coordinate types.  If `rho=1`, every hazard is zero and every `Q_i<=0`.
Therefore in every case

```text
V_i=max(0,Q_i).                                     (8)
```

This includes the all-Continue face, sure-quit faces, and a unique active
player whose opponents all Continue surely.

### 3. Arbitrary behavioral deviations

Against the stationary opponents, every reached live history has the same
conditional environment.  Quitting at that date has conditional value `Q_i`.
Continuing until any opponent absorbs pays zero by (1), and Never pays zero.

Writing

```text
rho_-i=product_(j!=i)(1-q_j),
```

a deterministic Quit time `t` has ex-ante payoff `rho_-i^t Q_i`, while Never
pays zero.  Thus the supremum over deterministic quit times and Never is
exactly `max(0,Q_i)`.  The checked behavioral pure-time extremality theorem
states that no randomized or history-dependent behavioral deviation can
exceed this supremum.  By (8), no player has a profitable deviation.

Hence the stationary repetition is an exact stationary terminal Nash profile
against the full behavioral strategy class.  The checked exact-terminal-Nash
consumer gives a uniform-equilibrium payoff.

### 4. Passive perturbation

Let `reward_part` retain participant coordinates and replace every passive
coordinate by zero.  It is participant-only, so the preceding theorem gives
an exact terminal Nash profile `sigma` for `reward_part`.

At every terminal outcome and for every player, changing from `reward_part`
to `reward` changes that coordinate by at most `delta(reward)`; Never is zero
in both games.  Therefore every prescribed payoff and every unilateral
behavioral-deviation payoff changes by at most `delta(reward)`.  A deviation
gain, being their difference, changes by at most `2delta(reward)`.  At `sigma`
the original game consequently has terminal exploitability at most (3), and
(4) follows.

## Conjecture-facing change

The maintained `INCENTIVE_GADGET` question accepts a universal architecture
no-go which constructs a stationary or sure-exit equilibrium for every table
in a precisely defined class.  Participant-only rewards form such a class and
allow arbitrary participant signs, negative influence cycles, calibrators,
and background-dependent participant rewards.  The theorem rules out the
whole class against unrestricted behavioral deviations.

Moreover, (4) makes the escape quantitative: passive rewards are not merely
logically necessary.  A gadget claiming terminal gap `gamma` must contain
some absent-player coordinate of magnitude at least `gamma/2`.

For the incompatible-pair clock target, an exact equilibrium cannot satisfy
both positive pair-mass floors and the strict leftover ceiling because the
checked clock inequality forbids them.  Thus the exact equilibrium produced
here directly falsifies every participant-only purported gadget.

## Probability, information, and deviation audit

The stationary profile uses independent private binary actions at each date,
with independent repetition across dates.  No public correlation or extra
signal is introduced.  Before absorption, the only public history is the
all-Continue word, so the deviator's arbitrary behavioral strategy is an
optimal stopping/randomization rule in the constant environment described
above.

The pure-time extremality result covers every unilateral behavioral strategy,
not only stationary or deterministic deviations.  The proof treats Never and
simultaneous quitting explicitly.  Payoffs on opponent-only first coalitions
are zero by the defining participant-only hypothesis.

## Boundary tests

1. **All Continue (`rho=1`).**  Every `q_i=0`, complementarity gives
   `Q_i<=0`, and Never realizes the exact value zero.
2. **Sure Quit (`rho=0`).**  Formula (7) has denominator one; (6) gives
   `V_i=max(0,Q_i)` for sure, interior, and inactive coordinates.
3. **Unique active player.**  That player's opponents' Continue mass is one,
   so a contraction-only best-response lemma would not apply.  The direct
   pure-time/Never comparison and the checked stationary endpoint boundary do
   apply.
4. **Negative Quit value.**  Delaying finite time only multiplies `Q_i<0` by a
   nonnegative survival factor; Never gives zero and is optimal.
5. **One-player passive set.**  The index set in (2) is empty, so the inserted
   zero makes `delta=0`; the one-player participant-only theorem remains
   meaningful.
6. **Perturbation factor two.**  Both the deviating payoff and prescribed
   payoff can move by `delta`; without a one-sided assumption, their gain can
   move by the full `2delta`.

## Source and novelty audit

The following strategic machinery is checked and is not claimed as new:

- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`; and
- `isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary` and
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
  `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.

The packet's new mathematical content was the reduction of the entire
participant-only reward class to those stationary interfaces and the
quantitative `2delta` perturbation consequence.  That content is now covered
by the checked declarations named below.

The no-harm singleton, acyclic solo-preemption, signed-influence, and odd-
blocker compilers cover different hypotheses and do not subsume arbitrary
signed, background-dependent participant rewards.  No external literature
result is used.

## Adapter and consumer

The checked arbitrary-data adapter is the pointwise predicate (1) on the
supplied reward table, formalized as `IsQuittingParticipantOnly`; no
equilibrium or graph certificate is assumed.  Finite Nash selection then
constructs the stationary row.

The downstream semantic consumer is the checked exact-terminal-Nash-to-
uniform-payoff theorem.  For the gadget question, existence of the exact
profile disproves the required fixed terminal exploitability gap throughout
the class.  Corollary (4) applies to every arbitrary table through the checked
participant projection and passive-magnitude bound.

## Original Lean handoff

1. Define `IsQuittingParticipantOnly reward := forall S i, i notin S ->
   reward S i=0`.
2. Either define the finite one-shot binary game and invoke compact finite Nash,
   or instantiate `exists_heterogeneousStationaryFaceNash` at lower bound zero
   and prove `excludedValue=0` from participant-only rewards.
3. Convert the selected hazards with `rootOfHazard`.  Prove the stationary
   payoff identity (8), splitting `rho=1`, `rho=0`, and the remaining face.
4. Use `isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary` or the
   pure-time extremality theorem plus the full-rate cap; do not assume strict
   opponent contraction at a unique active coordinate.
5. Invoke the checked exact terminal-Nash uniform-payoff consumer.
6. Define passive magnitude as a finite maximum after inserting zero, then
   prove the pointwise payoff perturbation and two-sided gain bound.

## Checked Lean realization

The source predicate and exact stationary realization are checked in
`UniformEquilibrium/Quitting/Classification/Existence/ParticipantOnlyStationary.lean`:

- `IsQuittingParticipantOnly` is the literal arbitrary-table adapter;
- `exists_stationary_isZeroAsymptoticNash_of_participantOnly` constructs an
  exact stationary terminal Nash profile against every unilateral behavioral
  strategy; and
- `exists_stationary_uniformEquilibriumPayoff_of_participantOnly` applies the
  exact terminal-Nash consumer and supplies the uniform-equilibrium payoff.

The quantitative projection is checked in
`UniformEquilibrium/Quitting/Classification/Existence/ParticipantOnlyPerturbation.lean`:

- `quittingPassiveMagnitude` is the empty-safe maximum in (2);
- `quittingParticipantProjection` and
  `isQuittingParticipantOnly_participantProjection` give the arbitrary-table
  adapter;
- `exists_stationary_isTwoPassiveMagnitudeAsymptoticNash` constructs the
  terminal `2 delta`-Nash profile; and
- `half_terminalExploitabilityGap_le_quittingPassiveMagnitude` is exactly the
  quantitative obstruction (4).

The full participant-only theorem and the passive-perturbation obstruction
have `M`, `L`, `A`, and `C`.  The consumer is unrestricted-behavior terminal
Nash and, in the participant-only case, the checked uniform-payoff theorem.
The result does not extend exact equilibrium existence to arbitrary reward
tables; the projected profile for an arbitrary table is only
`2 * quittingPassiveMagnitude reward`-Nash.

## Scope and nonclaims

- The theorem proves existence for the participant-only class, not for
  arbitrary quitting tables.
- It does not identify a sure-exit coalition; the equilibrium may be genuinely
  mixed.
- It does not say a particular negative influence cycle is harmless outside
  the participant-only class.
- The perturbation profile has exploitability at most `2delta`; it need not be
  exact for the original table.
- The result does not construct the two target pair atoms or a counterexample.
- It rules out an architecture; it does not decide the full quitting
  conjecture.
