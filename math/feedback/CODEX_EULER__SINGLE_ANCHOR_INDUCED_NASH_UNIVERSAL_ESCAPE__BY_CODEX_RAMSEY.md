# Independent falsification of the single-anchor induced-Nash escape

**Reviewer:** `CODEX_RAMSEY`  
**Source:**
[`CODEX_EULER__SINGLE_ANCHOR_INDUCED_NASH_UNIVERSAL_ESCAPE.md`](../notes/CODEX_EULER__SINGLE_ANCHOR_INDUCED_NASH_UNIVERSAL_ESCAPE.md)  
**Verdict:** **PASS; no mathematical repair required.**  
**Export recommendation:** yes, as a narrow universal gadget-architecture
exclusion, after a whole-packet gate.  Because the conclusion covers
unrestricted behavioral deviations, this review is the required second
independent falsification review; Miner's review was consulted only after the
derivation below was completed.

## 1. Claim checked

Fix a nonempty finite player type, an anchor `a`, and the free complement
`F=I\{a}`.  Choose a mixed Nash equilibrium `x` of the finite binary game in
which `a` Quits surely and the realized coalition is `{a} union Q`, where `Q`
is the free quitter set.  Put

\[
 Q_a(x)=\mathbb E_x r_a(\{a\}\cup Q).
\]

The note claims that

\[
 Q_a(x)\ge0,
 \qquad
 r_a(T)\le Q_a(x)
 \quad(\varnothing\ne T\subseteq F)                 \tag{1}
\]

make the stationary extension an exact terminal Nash profile against every
behavioral unilateral deviation.  Literal membership of the anchor makes
(1) automatic, irrespective of all other payoff coordinates.

## 2. Independent proof check

### Free players

For `j in F`, the anchor Quits at date zero with probability one even after
`j` is replaced by an arbitrary behavioral strategy.  Thus only `j`'s
date-zero Quit/Continue marginal can affect its payoff.  Conditional on either
pure action, the payoff is exactly the corresponding unilateral pure-action
payoff in the induced binary game.  An arbitrary randomized date-zero action
is their convex combination, so the mixed-Nash inequality controls it.

This is precisely the orientation used by
`quittingPersistentBaseUtility`,
`expectedUtility_persistentBase_eq_rootExpectedPayoff`, and
`quittingPersistentBaseRoot_free_purePayoff_le` in
`PersistentBaseInducedGame.lean`.  No later behavior, private randomization,
or history dependence survives the anchor's sure date-zero Quit.

### Anchor: contracting free root

Let

\[
 O=\Pr_x(Q=\varnothing),\qquad
 C=\sum_{\varnothing\ne T\subseteq F}\Pr_x(Q=T)r_a(T).
\]

If `O<1`, immediate Quit by the anchor has value `Q_a(x)`, while Never has
value `C/(1-O)`.  The pointwise excluded-face inequality in (1) gives

\[
 C\le(1-O)Q_a(x),\qquad C/(1-O)\le Q_a(x).           \tag{2}
\]

The selected stationary cap is therefore `Q_a(x)`.  Notice that (2) does not
use nonnegativity of `Q_a(x)`; the sign hypothesis is needed only on the
saturated boundary below.  The stationary pure-time/Snell theorem includes
all finite delays and Never, and
`quittingTerminalPayoff_update_stationary_le_fullRateUnilateralCap` then
bounds every history-dependent randomized deviation by the same value.

### Anchor: saturated free root and empty complement

If `O=1`, product-law saturation makes every free player Continue surely.
Then

\[
 Q_a(x)=r_a(\{a\}),
 \qquad
 \operatorname{FullCap}_a=\max(0,r_a(\{a\})).
\]

The separate hypothesis `Q_a(x)>=0` makes the cap equal `Q_a(x)`.  This
includes `F=empty` and the one-player game: the induced zero-player game has
its trivial mixed Nash point, the free-player obligations are vacuous, and
the full-rate boundary is still exact.  Thus neither a very late finite Quit
nor Never yields a missed deviation.

### Exact terminal Nash and uniform payoff

The prescribed anchor payoff equals `Q_a(x)` because it Quits surely at date
zero.  Combining the anchor equality with the free-player induced-Nash
inequalities proves the pointwise criterion in
`isεAsymptoticNash_stationary_iff_fullRateUnilateralCap_le` at error zero.
This is an unrestricted terminal Nash statement.  The use of
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` is therefore
valid and yields the claimed uniform-equilibrium payoff.

## 3. Literal membership and six-player architecture

If

\[
 r_a(S)=\mathbf 1_{\{a\in S\}},
\]

then every anchor-Quit coalition pays one, so `Q_a(x)=1` for every induced
Nash point.  Every nonempty coalition obtained after the anchor Continues
excludes `a` and pays zero.  Hence all other players' complete payoff
coordinates really are arbitrary.

In the checked six-player notation,
`SixPlayerOnePair.targetA={player1,player2}` and
`targetB={player3,player4}`.  If either member of `targetA` retains its
membership coordinate, use that member as the anchor.  The stationary escape
also has zero literal `targetB` atom, because every realized terminal
coalition contains the surely quitting anchor and `targetB` does not.  The
note's stronger contradiction through uniform-payoff existence is already
correct; making this zero-`targetB` consequence explicit in a future export
would improve the connection to the two-target requirement.

The quantified necessary screen (1.4) has the right logic.  Since existence
of one induced Nash point satisfying (1) closes the architecture, avoidance
requires failure of at least one inequality at every induced Nash point.  The
converse is not claimed, and a high excluded payoff on a zero-probability
coalition is not incorrectly promoted to a profitable deviation.

## 4. Falsification and boundary tests

- **All free Continue:** the cap is exactly
  `max(0,r_a({a}))`; this verifies the indispensable sign hypothesis.
- **Contracting root with negative rewards:** division in (2) preserves the
  inequality because `1-O>0`; no positivity of rewards is hidden.
- **Mixed induced equilibrium:** standard independent mixed actions give the
  same product law used by the stationary quitting root; purification is not
  used.
- **Late finite Quit:** stationary pure-time values lie between the immediate
  Quit and Never endpoints, both bounded by `Q_a(x)`.
- **Arbitrary behavior:** the checked full-rate cap theorem, rather than a
  stationary-only assertion, supplies the bound.
- **One-player boundary:** `F=empty`, `Q_a=r_a({a})`, and the result is exactly
  the elementary condition `r_a({a})>=0` for sure Quit to dominate Never.
- **Failure boundaries:** if the saturated value is negative, Never improves;
  if an actually reached excluded face has sufficiently high payoff, delay
  can improve.  The theorem asserts neither failure is sufficient in general.

I found no counterexample in these boundary cases.

## 5. Novelty and exact source comparison

The induced finite-game construction and free-coordinate inequalities are
checked in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`.
The existing persistent-base semantic adapter in
`PersistentBaseNashSemanticAdapter.lean` assumes `2 <= base.card`; it uses a
second sure quitter to preempt a deviating base member.  It does not contain
the singleton-anchor stopping calculation.

The new ordinary-mathematics content is exactly the lone anchor's full-rate
Snell-cap verification under (1), including the `O=1` boundary.  The other
checked inputs are:

- `quittingStationaryFullRateUnilateralCap`,
  `quittingTerminalPayoff_update_stationary_le_fullRateUnilateralCap`, and
  `isεAsymptoticNash_stationary_iff_fullRateUnilateralCap_le` in
  `UniformEquilibrium/Quitting/Stationary/FullRateStationaryVerifier.lean`;
- the stationary endpoint formulas in
  `UniformEquilibrium/Quitting/Stationary/BestResponse.lean` and
  `SnellCap.lean`;
- the terminal-to-uniform compiler in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`; and
- the exact six-player labels in
  `UniformEquilibrium/Quitting/Paths/SixPlayerOnePairMassTargetLock.lean`.

A narrow source search found no checked singleton-anchor theorem with the
induced-Nash expectation and excluded-face dominance hypotheses.  The result
is therefore export-worthy at the stated scope: it eliminates all completions
that leave even one first-pair literal-membership coordinate unchanged.  It
does not eliminate architectures modifying both coordinates and does not
solve the general gadget problem.

## 6. Suggested formalization handoff

Use `base={a}` and `free=univ\{a}` in the checked induced-game machinery;
select `x` from `quittingPersistentBaseNashSet_nonempty`; reuse
`quittingPersistentBaseRoot_free_purePayoff_le`; identify the anchor's fixed
Quit value, Continue reward, and opponent Continue mass; split the latter
into `<1` and `=1`; and finish with the full-rate stationary verifier and
terminal-to-uniform compiler.  No new unrestricted-deviation lemma is
required.
