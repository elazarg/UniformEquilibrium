# Fixed-coordinate Nashification of a reached Fin4 sure row

Author: `CODEX_MINER`

Status: **proved ordinary mathematics; internal producer/no-go pair;
independent review requested.**  The producer turns a literal reached
sure-observer row with one retained positive hazard into an actual stationary
source with two solved coordinates, a heavy atom containing both possible
debtors, and a full-gap paid row.  The exact regression in Section 5 shows
that these fields still do not exclude the unique all-Continue cap root.

This is a source strengthening for the inert-rectangle lane, not an answer to
[`FIN4_BT_QUESTION.md`](../../FIN4_BT_QUESTION.md): the two reselected Nash
coordinates are not the original reached suffix coordinates, and no checked
consumer currently spends the retained heavy atom at the cap port.

## 1. Question

The valid part of the recent inert-rectangle proposal reaches a literal
suffix row at which an observer `o` Quits surely and some distinct mover `m`
has a positive Quit hazard.  Full Nashification of the three complementary
players erases the mover hazard and the reached atom.  Can one retain that
hazard while still producing a useful exact stationary semantic source?

The answer is yes.  Nashify only the remaining two labels.  Since `o` Quits
surely, this is an ordinary two-player binary game and its Nash inequalities
are already unrestricted behavioral inequalities in the quitting game.

## 2. Exact theorem

Let `I=Fin 4`, let `r` be a quitting reward table, and fix distinct players
`o,m`.  Let

\[
 K=I\setminus\{o,m\},
 \qquad a\in[0,1].                                  \tag{2.1}
\]

Assume a terminal exploitability witness

\[
 W:\operatorname{HasTerminalExploitabilityGap}(r,\Gamma),
 \qquad \Gamma>0.                                   \tag{2.2}
\]

Then there is an actual stationary behavioral profile `sigma` with the
following properties.

1. Player `o` Quits surely at date zero, player `m` uses Quit rate exactly
   `a`, and the two players in `K` use a product mixed Nash equilibrium of an
   explicitly induced two-player binary game.
2. Every `j in K` has zero unrestricted terminal debt:

   \[
   B_j(\sigma)=U_j(\sigma).                          \tag{2.3}
   \]

3. Consequently the positive-debt support is contained in `{o,m}`.  The
   terminal witness selects

   \[
   d\in\{o,m\},\qquad d_d(\sigma)\ge\Gamma.          \tag{2.4}
   \]

4. The total terminal mass of coalitions containing both `o` and `m` is
   exactly `a`.  Hence some `A subset K` satisfies

   \[
   \Pr_\sigma\{Q_0=\{o,m\}\cup A\}\ge {a\over4}.    \tag{2.5}
   \]

5. The debt in (2.4) gives a
   `QuittingPaidFirstDisagreementRow r sigma d Gamma`.  Its first
   disagreement is date zero and its pre-disagreement live mass is one.

If the input is a literal product row `q` with `q_o=1` and an actual
coalition cell `S` of one-stage mass at least `w>0`, where `{o,m} subset S`,
take `a=q_m`.  Product-law monotonicity gives `a>=w`, so (2.5) improves to

\[
 \Pr_\sigma\{Q_0=\{o,m\}\cup A\}\ge {w\over4}.      \tag{2.6}
\]

Thus the output preserves the literal observer and mover labels and a fixed
fraction of the reached row's quantitative mass, though not its complete
coalition or the other two marginals.

## 3. Construction and proof

### 3.1 The induced binary game

For a pure quitting set `A subset K`, let a public calculation (not public
randomization in the quitting strategy) average over the fixed Bernoulli
action of `m`:

\[
 \widetilde r_j(A)
  =(1-a)r_j(\{o\}\cup A)
    +a r_j(\{o,m\}\cup A),\qquad j\in K.             \tag{3.1}
\]

This is an ordinary finite two-player binary-action game.  Choose a product
mixed Nash equilibrium `x` and define `sigma` stationarily by

\[
 q_o=1,\qquad q_m=a,\qquad q|_K=x.                   \tag{3.2}
\]

The randomization in (3.1) is exactly `m`'s independent date-zero action in
the ambient product root; no correlated strategy has been introduced.

### 3.2 The two Nash inequalities are fully behavioral

Fix `j in K` and replace its entire behavioral strategy arbitrarily.  Player
`o` still Quits surely at date zero, so absorption occurs at date zero with
probability one.  Only `j`'s randomized action at that date can affect its
payoff; every later prescription is irrelevant.  Conditional on Quit or
Continue, its two values are precisely its two pure-action values in (3.1)
against `x_{-j}`.  The induced mixed-Nash inequality bounds both endpoints,
and hence every randomized date-zero action.  This proves (2.3) against the
project's unrestricted behavioral deviation class.

The terminal witness applied to this literal profile gives a player with
debt at least `Gamma`.  Equation (2.3) excludes both labels in `K`, proving
(2.4).

### 3.3 Retained pair mass

The game terminates at date zero.  The event that the terminal coalition
contains both `o` and `m` is exactly the event that `m` Quits, of probability
`a`.  The four disjoint events indexed by `A subset K` partition it.  One has
mass at least `a/4`, proving (2.5).

If the original product row assigns mass at least `w` to a coalition `S`
containing `m`, then that cell mass is bounded above by the marginal Quit
probability `q_m=a`.  This proves (2.6); no division by another marginal or
positive all-Continue probability is used.

### 3.4 The paid row begins at date zero

For any player other than `o`, fixed opponents include a sure date-zero
quitter.  Its complete behavioral payoff therefore depends only on its
date-zero action.  For `o`, its prescribed action is sure Quit at date zero;
any profitable replacement must differ from that action at date zero.  Thus
for either possible debtor `d in {o,m}`, the two pure stopping-time witnesses
extracted from the full-gap deviation can be chosen with distinct date-zero
actions.  Their first disagreement is zero, and the common survival before
that date is one.  The checked pure-time paid-row decoder then supplies the
row in item 5 with the full weak gap `Gamma`.

Equivalently, one may invoke
`HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at` and simplify
its first-disagreement data using the sure date-zero absorption.  The direct
argument records the extra start-zero fact not present in the arbitrary-
profile theorem.

## 4. Rectangle-source adapter

The positive-orientation rectangle audit leaves exactly the needed input.
At the normalized first-disagreement suffix, the pure-time observer is sure
Quit.  A positive terminal cell containing that observer and another label
`m` has literal one-stage mass `w>0`, hence `q_m>=w`.  Applying Section 2
returns one stationary profile with:

```text
same observer o and mover m,
retained mover hazard at least w,
two unrestricted-debt-zero complementary coordinates,
debt support contained in {o,m},
a terminal atom containing {o,m} of mass at least w/4,
and a full-Gamma start-zero paid row with debtor in {o,m}.
```

This improves on fully Nashifying all three complementary players, which
retains only the observer label and can assign zero probability to every
coalition containing the original mover.  It also improves on applying the
arbitrary-profile paid-row theorem directly to the reached suffix, which
does not localize the debtor support.

The price is exact and important: the two coordinates in `K` are reselected.
The resulting stationary profile is not asserted to be the literal reached
suffix, to have its terminal law, or to lie on its common-response/reset
chronology.

## 5. Sharp inert regression

The preceding strengthening still cannot exclude a cap-port inert stall from
its displayed fields.  For every nonempty `S subset Fin 4`, define

\[
r_i(S)=
\begin{cases}
2,&i\notin S,\\
1,&S=\{i\},\\
0,&i\in S\text{ and }|S|\ge2.
\end{cases}                                         \tag{5.1}
\]

Fix distinct `o,m`, choose any rational `a in (0,1]`, and apply the
construction.  Each player in `K` strictly prefers Continue in the induced
game, so the selected point is uniquely all Continue on `K`.  The source
payoffs and debts are

\[
\begin{aligned}
U_o&=1-a,& B_o&=2,& d_o&=1+a,\\
U_m&=2(1-a),& B_m&=2,& d_m&=2a,\\
U_j&=B_j=2&&&(j\in K).
\end{aligned}                                       \tag{5.2}
\]

The terminal law has mass `1-a` on `{o}` and mass `a` on `{o,m}`, so the
heavy pair atom is actually `a`, stronger than (2.5).  Both possible debtor
labels have positive start-zero paid rows.

Against the source cap `B=(2,2,2,2)`, every player's Continue endpoint is
exactly `2`, while its Quit endpoint is at most `1`.  Hence all Continue is
the **unique** exact cap-Nash root.  The cap lift is locally inert despite
the localized two-debtor support, retained positive mover hazard, heavy
debtor-containing atom, and start-zero paid rows.

This is not a counterexample.  A singleton quitter with everyone else Never
is an exact unrestricted terminal Nash profile, so the global minimum is
zero and no positive terminal exploitability witness exists.  The example
proves only that the new local source fields do not algebraically consume
inertness; the positive global minimum/full hard residual must still be used
nonlocally.

## 6. Source and duplicate audit

The exact finite-game source machinery inspected was:

- `quittingPersistentBaseNashSet_nonempty` and
  `quittingPersistentBaseRoot_free_purePayoff_le` in
  `PersistentBaseInducedGame.lean`;
- `persistentBase_inducedNash_free_semantics` in
  `LargePersistentBaseDeletionAdapter.lean`;
- `FinFourLeaveJoinStationaryTwoDebtorHandoff` and
  `FinFourPairBaseStationaryTwoDebtorHandoff` in the corresponding
  `Collision/SingletonPacket` files; and
- `HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at` and the
  paid cap-port trichotomy in the current formalized packets.

The persistent-base definitions force every label outside `base union free`
to Continue and therefore do not directly retain one arbitrary Bernoulli
coordinate as in (3.1).  The two checked Fin4 handoffs produce related
two-solved/two-debtor stationary sources, but their positive atom is generated
from supplied static leave--join or pair-join inequalities.  The present
producer instead takes one literal positive hazard from a reached row and
keeps that exact rate while Nashifying the other two coordinates.

This distinction is mathematically real but currently has no final consumer.
The arbitrary-profile theorem already produces a paid row everywhere, and
no checked paid-port or minimum-fiber theorem uses an additional terminal
atom containing the complete debt support.  The result is therefore a
Research/source-interface candidate, not an export candidate.

## 7. Requested review and exact next test

Please check independently:

1. the induced payoff (3.1) and absence of hidden public correlation;
2. the upgrade from two-player mixed Nash to unrestricted free-player debt
   zero;
3. localization of the full terminal gap to `{o,m}`;
4. the `a/4` and `w/4` mass bounds;
5. the start-zero paid-row claim for both possible debtor labels; and
6. all cap, debt, and global-failure calculations in Section 5.

The only conjecture-facing continuation worth testing is whether the **full
positive-minimum rectangle provenance**, beyond the fields retained here,
forces this reselected source into the carrier debt moat or supplies a common
law/path to the heavy atom.  Without such a bridge, Section 5 rules out a
purely local inert contradiction.
