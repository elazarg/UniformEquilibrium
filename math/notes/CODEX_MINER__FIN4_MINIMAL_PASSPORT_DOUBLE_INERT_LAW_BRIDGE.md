# Fin4 minimal passports and the double-inert law bridge

**Author:** CODEX_MINER  
**Date:** 2026-08-25  
**Status:** independently reviewed **PASS**; internal, not exported.  See
[`feedback/CODEX_MINER__FIN4_MINIMAL_PASSPORT_DOUBLE_INERT_LAW_BRIDGE__BY_CODEX_EULER.md`](../feedback/CODEX_MINER__FIN4_MINIMAL_PASSPORT_DOUBLE_INERT_LAW_BRIDGE__BY_CODEX_EULER.md).
Propositions 3.1--3.3 are ordinary mathematics and are not Lean checked.
Proposition 5.1 is an exact realizable interface countermodel, not a
counterexample to the quitting-game conjecture.  No uniform-payoff or
contradiction claim is made.  The reviewer recommends keeping the result
internal until a conjecture-facing consumer or source-alignment export policy
exists.

## 1. Question and outcome

In a cardinal-minimal four-player counterexample, every deletion of one
player has a terminal approximate equilibrium.  Quietly lifting such a
profile forces a full-gap finite pure-time deviation by the deleted player.
Can the four resulting operational passports be combined with an inert
pair-base or singleton-base paid source to force positive cap absorption, a
punishment-floor edge, or a contradiction?

The direct answer is **not from the presently typed interfaces**.  The
deletion equilibria are reselected profiles.  Restricting an inert paid source
need not produce any one of them.  Proposition 5.1 gives one rational reward
table on which all four operational deletion passports coexist with a
same-source pair-base profile whose cap game has literal all-Continue as its
unique product Nash root.  The table escapes the conjecture hypotheses
exactly by having date-zero singleton terminal equilibria and hence global
minimum debt zero.

There is nevertheless a new source-matched fact in the stronger checked
singleton double-port producer.  Its original and repaired laws are not
arbitrary unrelated laws.  If `e` is the sure singleton owner, `F` is its
three-player complement, and `a` is the one-stage probability that some free
player Quits, then

\[
 \mu_{\rm src}
  =(1-a)\delta_{\{e\}}
   +a\, (A\mapsto A\cup\{e\})_*\mu_{\rm rep}.       \tag{1.1}
\]

The source debt and literal owner repair then give a reached repaired-law atom
of mass at least `Gamma/(28M)` on which either a solo comparison or the owner
leave toggle has size at least `Gamma/2`.  This identifies the two inert laws
and retains a quantitative atom, but it is a cross-profile unilateral repair,
not a chronological Bellman edge.  The repaired free profile actually has a
full-gap free-player deviation in the owner-deleted game, so it is not the
cardinal-minimal deletion equilibrium to which the operational passport
applies.

The exact residual after this synthesis is therefore:

* on a descent arm, regenerate paid/reset/profile provenance at the limiting
  carrier pair; or
* on the double-inert arm, connect the repaired free stationary point to a
  terminal approximate equilibrium of the owner-deleted game while retaining
  (1.1), or build a chronological consumer directly from the law bridge.

The compact minimum-fiber all-Continue tube and its linear absorption-defect
moat do not by themselves provide either connector.

## 2. Quantifiers and source alignment

Let `I=Fin 4`, let `r` be a reward table bounded by `M`, and suppose an
ambient terminal exploitability witness has gap `Gamma>0`.

For a deleted player `d`, put `J=I\{d}`.  Cardinal minimality and the checked
small-player theorem give, for every sufficiently small `epsilon>0`, a
terminal `epsilon`-Nash profile `tau_d` of the game restricted to `J`.
Its quiet lift `lambda_d` makes `d` play literal Never.  The reviewed
operational essential-support theorem gives a finite deterministic Quit time
`t_d` such that

\[
 U_d(\lambda_d[d\leftarrow \mathrm{QuitAt}(t_d)])
       -U_d(\lambda_d)\geq\Gamma.                      \tag{2.1}
\]

Both `tau_d` and `t_d` may depend on `d`.  Nothing in cardinal minimality
identifies any `tau_d` with the restriction of a separately selected
pair-base or singleton-base stationary source.

This is the decisive typing issue.  If a pair-base source has sure base
`B={b_0,b_1}`, then:

* deleting a free player leaves the two base coordinates as the possible
  debtors, so the restriction is not supplied as a survivor Nash profile;
* deleting a base player changes the induced terminal rows and does not
  preserve the source's free-coordinate Nash certificate.

Likewise, after repairing a singleton source by making its owner `e` Always
Continue, its restriction to `F=I\{e}` is an actual profile of the deleted
game, but the induced Nash point was selected for rows containing `e`, not
for the deletion table whose rows exclude `e`.

## 3. Exact law identification at the checked singleton repair

Fix a checked

```text
FinFourSingletonBaseResetRepairPaidChain reward bound residual e
```

and write `F=finFourSingletonBaseFree e`.  Let `x_i` be the Quit probability
of free player `i` at its selected induced Nash point.  For `A subseteq F`,
put

\[
 w(A)=\prod_{i\in A}x_i\prod_{i\in F\setminus A}(1-x_i),
 \qquad a=1-w(\varnothing).                            \tag{3.1}
\]

The producer's checked `free_absorption_lower` gives

\[
 a\geq {\Gamma\over \Gamma+2M}>0.                    \tag{3.2}
\]

Here and below, a terminal law includes the `Never` outcome.  All laws in
this section give it mass zero.

### Proposition 3.1 (exact original/repair law bridge)

Let `mu_src` be the terminal law of the original singleton-base stationary
profile and `mu_rep` the law after the literal owner-Continue repair.  Then,
for every nonempty `A subseteq F`,

\[
 \mu_{\rm rep}(A)={w(A)\over a},\qquad
 \mu_{\rm src}(A\cup\{e\})=w(A)=a\mu_{\rm rep}(A),   \tag{3.3}
\]

and

\[
 \mu_{\rm src}(\{e\})=1-a.                           \tag{3.4}
\]

All other terminal-coalition masses are zero.  Equivalently, (1.1) holds.
In particular, the two laws are mutually singular: every source terminal
coalition contains `e`, while every repaired terminal coalition excludes
`e`.

#### Proof

In the source root, `e` Quits surely.  Play therefore absorbs at date zero,
and the free Bernoulli atom `A` produces exactly `A union {e}` with mass
`w(A)`.  This proves (3.3) for the source and (3.4).

In the repaired stationary root, `e` Continues surely and the same free root
is repeated after every all-Continue row.  A particular nonempty `A` first
occurs at date `t` with probability `w(empty)^t w(A)`.  By (3.2),
`w(empty)<1`; summing the geometric series gives

\[
 \sum_{t\geq0}w(\varnothing)^t w(A)
   ={w(A)\over1-w(\varnothing)}={w(A)\over a}.
\]

The repaired Never mass is zero for the same reason.  Since `e` never Quits,
every repaired terminal coalition excludes it.  QED.

This identity is structural and holds before considering the cap ports.  In
the double-inert arm, every selected cap prefix is literal all-Continue and
therefore leaves each source profile's terminal semantics unchanged.  Hence
(1.1) identifies the two invariant law components throughout that arm.

### Proposition 3.2 (a reached half-gap atom on the repaired law)

Assume `|r_i(S)|<=M` for every terminal row and player.  There is a nonempty
`A subseteq F` such that

\[
 \mu_{\rm rep}(A)\geq {\Gamma\over 28M}               \tag{3.5}
\]

and

\[
 r_e(A)-\bigl((1-a)r_e(\{e\})
                 +a r_e(A\cup\{e\})\bigr)
       \geq {\Gamma\over2}.                            \tag{3.6}
\]

Consequently the same positive-mass atom satisfies at least one of

\[
 r_e(A)-r_e(\{e\})\geq {\Gamma\over2},                \tag{3.7}
\]

\[
 r_e(A)-r_e(A\cup\{e\})\geq {\Gamma\over2}.           \tag{3.8}
\]

#### Proof

The producer has

\[
 d_e(\mathrm{src})\geq\Gamma.
\]

The checked repair handoff identifies the repaired owner's prescribed payoff
with the source owner's unrestricted stationary cap.  Therefore

\[
 U_e(\mathrm{rep})-U_e(\mathrm{src})\geq\Gamma.        \tag{3.9}
\]

Using Proposition 3.1 in the two payoff moments, (3.9) becomes

\[
 \mathbb E_{A\sim\mu_{\rm rep}} g(A)\geq\Gamma,
\quad
 g(A)=r_e(A)-(1-a)r_e(\{e\})-a r_e(A\cup\{e\}).       \tag{3.10}
\]

Every `g(A)<=2M`.  Let `H={A:g(A)>=Gamma/2}` and
`h=mu_rep(H)`.  Then

\[
 \Gamma\leq 2Mh+(1-h){\Gamma\over2},
\]

so

\[
 h\geq {\Gamma\over4M-\Gamma}\geq {\Gamma\over4M}.
                                                                    \tag{3.11}
\]

Here `M>0` and `Gamma<=2M` follow already from (3.9) and the reward bound.
There are seven nonempty subsets of the three-player free set, so one atom in
`H` has mass at least `Gamma/(28M)`.  This proves (3.5)--(3.6).

Finally

\[
 g(A)=(1-a)[r_e(A)-r_e(\{e\})]
          +a[r_e(A)-r_e(A\cup\{e\})].                 \tag{3.12}
\]

It is a convex combination of the two displayed edge differences.  If both
were below `Gamma/2`, then so would `g(A)`.  Hence (3.7) or (3.8).  QED.

The atom selected here may differ from the producer's checked heavy
strict-superset atom.  The gain alignment is the new feature; silently
identifying the two atoms would be invalid.

### Proposition 3.3 (the repaired restriction is not the deletion passport source)

Let `tau_rep` be the restriction of the repaired profile to the free-player
game on `F`.  The checked repair handoff selects a free player `f` with
unrestricted terminal debt at least `Gamma`.  Exact deletion/lift naturality
therefore gives

\[
 \sup_{\sigma_f}
  \bigl(U_f(\tau_{\rm rep}[f\leftarrow\sigma_f])
          -U_f(\tau_{\rm rep})\bigr)\geq\Gamma         \tag{3.13}
\]

in the owner-deleted game itself.  Thus `tau_rep` is not a terminal
`epsilon`-Nash profile for any `epsilon<Gamma`.

#### Proof

The owner plays literal Always Continue and can never occur in a terminal
coalition, before or after a free player's unilateral deviation.  Deleting
that passive coordinate preserves the complete stopping law and every free
player payoff.  Apply this equality to the free observer and deviation in the
handoff's `outside_debt` field.  QED.

This proves that cardinal minimality necessarily selects some other
three-player equilibrium profile for the owner-deletion passport.  Merely
noting that both laws exclude `e` is not a source connector.

## 4. Why the minimum-fiber basin does not consume the bridge

The compact minimum-fiber theorem freezes exact product Nash roots at the
**prescribed payoff** `U` of a carrier pair near the positive global minimum.
Its linear refinement states, locally,

\[
 c\,A(q)\leq \operatorname{Defect}(U,q).               \tag{4.1}
\]

The repaired stationary root in Section 3 is positively absorbing, but it is
not an exact Nash root at its prescribed payoff: Proposition 3.3's free
observer has debt at least `Gamma`.  Inequality (4.1) is therefore compatible
with it and supplies no contradiction.

Conversely, the exact roots selected by the paid cap ports are Nash against
the **cap envelope** `B`, not against `U`.  In an inert stall those roots are
all-Continue and have absorption zero, so both the exact tube and the linear
absorption bound are satisfied identically.  No checked declaration
identifies a cap-port tail with a near-minimum prescribed projection or turns
the unilateral owner repair into an incoming Bellman edge.

On a quantitative-descent arm, the cap-port limit has strictly smaller total
semantic debt, but the checked type deliberately carries no behavior-profile
representative, paid row, reset law, or singleton-source Nash point.  Global
minimality only bounds its debt below by `D_*`; it does not make the limit a
new input to the singleton producer.  Reapplying the producer reselects a
source from the reward table and does not preserve the descent inequality.

## 5. Realizable four-passport / unique-allC pair-base countermodel

This section proves that the source-alignment issue is real even when all four
codimension-one passports are operational and exact.

Identify `Fin 4` with `{0,1,2,3}` and let

\[
 o(j)=j+2\pmod4.
\]

For every nonempty coalition `S`, define the rational reward table coordinate
`r_i(S)` as follows:

1. if `S={i}`, put `r_i(S)=1`;
2. if `i notin S`, put `r_i(S)=0` when `S={j}` and `i=o(j)`, and put
   `r_i(S)=2` otherwise;
3. if `i in S` and `|S|>=2`, put

   \[
   r_i(S)=r_i(S\setminus\{i\})-1.                     \tag{5.1}
   \]

All rewards lie in `[-1,2]`.

### Proposition 5.1

For `Gamma=1`, this one table has all of the following properties.

1. Every proper player subsystem has an exact terminal Nash profile.
2. For every deleted player `d`, one exact terminal Nash profile of the
   retained triple has a quiet lift on which `d` gains exactly one by a
   deterministic finite pure-time deviation.
3. The sure pair-base profile with players `0,1` quitting at date zero and
   players `2,3` playing Never has

   \[
   U=(1,1,2,2),\quad B=(2,2,2,2),\quad d=(1,1,0,0).    \tag{5.2}
   \]

   It has a paid row for player `0`, a zero-debt reset owner `2`, unit
   `(2,0)` opponent incidence, and all prescribed coordinates above their
   punishment floors.
4. At the cap tail `(2,2,2,2)`, all-Continue is the unique product Nash root.
5. Nevertheless every date-zero singleton profile is an exact ambient
   terminal Nash profile.  Hence the table has debt minimum zero and no
   positive terminal exploitability gap.

#### Proof

Fix a deleted `d` and put `j=o(d)`.  In the retained triple, let `j` Quit
exactly at date one and let the other two retained players play Never.
Player `j` receives its singleton payoff `1`; changing its finite Quit date
still pays `1`, while Never pays `0`.  Each other retained player receives
`2`.  Preempting pays its own singleton `1`, tying at date one pays `1` by
(5.1), and waiting or playing Never pays `2`.  Stopping-law disintegration
therefore proves exact Nash against arbitrary behavioral deviations.

In the quiet lift, deleted `d` receives
`r_d({j})=0`.  Quitting at date zero preempts `j` and pays the singleton value
`1`.  This proves item 2 for all four labels with exact source/deviation
provenance.

For completeness, every smaller proper subsystem is also solvable.  An
adjacent two-player subsystem has a date-zero singleton equilibrium.  For an
opposite pair, the stationary root in which both Quit with probability
`1/2` is exact: each player's Quit and Continue endpoint values are both zero,
and the repeated root has payoff zero.  Singleton subsystems are immediate.

At the pair-base profile `{0,1}`, the two base players receive `1`, and each
free player receives `2`.  A base player can leave the date-zero pair and
receive outsider singleton payoff `2`; a free player gets `1` by joining and
`2` by continuing.  Since a sure opponent ends play at date zero, these are
the unrestricted behavioral caps, proving (5.2).  Player `0`'s literal move
from Quit now to Never is the paid gain `1`.  Player `2` has zero debt and
sees sure opponent `0`, so the incidence is one.

For any player `i`, the other players can punish it by making `o(i)` Quit at
date zero.  Continuing pays `0` and joining pays `-1`, so the punishment value
is at most zero.  Every coordinate in (5.2) is therefore floor safe.

Now fix any player `i` at cap tail `b=(2,2,2,2)`.  If all opponents Continue,
own Continue pays `2` and own Quit pays `1`.  If the opponent quitter set is a
nonempty `A`, (5.1) gives

\[
 r_i(A\cup\{i\})=r_i(A)-1.                            \tag{5.3}
\]

Thus Continue beats Quit by exactly one at every pure opponent corner, and
hence under every opponent product law.  All-Continue is the unique product
Nash root.

Finally, at the date-zero singleton `{j}`, player `j` receives `1`, its
opposite `o(j)` receives `0`, and the other two outsiders receive `2`.
The active player cannot improve; the opposite player gets `-1` by joining;
and either remaining outsider gets `1` by joining or preempting.  The profile
is therefore an exact ambient terminal Nash profile against arbitrary
behavioral deviations.  This proves item 5 and explains precisely why the
construction is not a conjecture counterexample.  QED.

### Exact sharp-passport values

For every singleton deletion `d`, on the retained triple `J=I\{d}`,

\[
 \ell_d(J)=0,\qquad P_d(J)=1,\qquad C_d(J)=0.          \tag{5.4}
\]

Thus all four operational witnesses use the solo/preemption arm.  Moving the
delayed singleton from date one to date zero erases that preemption gain and
produces the global equilibrium.  This is the exact failed implication:

> four separately sourced operational deletion passports plus a floor-safe
> pair-base source with a unique all-Continue cap root do not force positive
> cap absorption or a contradiction.

The countermodel does **not** refute a theorem using the ambient hard residual,
positive minimum debt, or the checked singleton double-port producer; it
fails those fields at the explicit date-zero singleton equilibria.

## 6. Exact finite residual and next theorem

Combining the checked and reviewed inputs leaves the following finite system
inside an actual hard residual.

1. For every deleted `d`, there exists a separately selected survivor
   approximate equilibrium and a full-gap finite pure-time passport.
2. For every prescribed singleton owner `e`, one actual induced Nash point
   produces an original paid/reset source and its literal repaired paid
   source, both cap-lifted from the same positive global minimum.
3. The capstone returns original quantitative descent, repaired quantitative
   descent, or double inert.
4. In double inert, Proposition 3.1 gives the exact affine law bridge, and
   Proposition 3.2 gives a repaired-law atom of mass `Gamma/(28M)` carrying a
   half-gap solo/leave alternative.
5. The repaired restriction has a full-gap free-player deviation and hence
   cannot be substituted for the owner-deletion equilibrium.
6. Near the global minimum fiber, exact prescribed-payoff roots are uniquely
   all-Continue and approximate absorption pays the checked linear Nash
   defect; cap-envelope all-Continue roots pay neither charge nor defect.

The narrow missing implication is one of:

```text
quantitative cap descent limit
  -> regenerated actual paid singleton source at no larger debt,
```

or

```text
affinely coupled repaired law + reached half-gap atom
  + a deletion-game equilibrium on the same three labels
  -> chronological edge / prescribed-payoff defect reduction.
```

A plausible but presently unproved route is a continuation theorem for the
three-free-player induced Nash correspondence as the singleton owner's Quit
probability moves from one to zero.  At parameter one it contains the checked
source point; at parameter zero it becomes the actual owner-deleted game.
Such a theorem must retain a connected component or a controlled approximate
Nash path.  Mere existence of endpoint equilibria is insufficient and is not
claimed here.

## 7. Source and duplicate audit

Checked declarations inspected under their current imports:

```text
UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  SingletonBaseSameLawResetProducer.lean
    FinFourSingletonBaseSameLawResetProducer
    FinFourQuantitativeFullSupportHardResidual.
      nonempty_singletonBaseSameLawResetProducer

  SingletonBaseResetRepairPaidChain.lean
    repairedProfile_eq_ownerAlwaysContinueUpdate
    paidRows_before_and_after
    nonempty_resetRepairPaidChain

  SingletonBaseResetRepairPaidCapDoublePort.lean
    sourceDescent_or_repairedDescent_or_doubleInert

UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/
  LargeBaseStationarySemanticHandoff.lean
    QuittingSingletonBaseStationaryHandoff
    repaired_owner_payoff_eq_source_cap
    repaired_owner_cap_eq_payoff
    outside_debt

UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticFinFourMinimumFiberIsolation.lean
    exists_finFour_minimumFiberIsolation_and_debtMoat_of_no_uniformPayoff
    minimumFiber_debt_add_epsilon_le_of_carrierTail_exactRoot_absorption_pos

  TerminalSemanticFinFourMinimumFiberLinearAbsorptionDefect.lean
    exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff

UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean
  deletion/lift payoff and deviation transport
```

Conference inputs inspected:

```text
notes/CODEX_CEDAR__OPERATIONAL_ESSENTIAL_SUPPORT_REDUCTION.md
notes/CODEX_EULER__OPERATIONAL_ESSENTIALITY_SHARP_DELETION_PASSPORT.md
notes/CODEX_CEDAR__FIN4_SHARP_DELETION_PASSPORT_SCREEN.md
notes/CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT.md
notes/CODEX_EULER__FIN4_PAIRBASE_INERT_STALL_FEASIBILITY.md
feedback/CODEX_EULER__FIN4_PAIRBASE_INERT_STALL_FEASIBILITY__BY_CODEX_MINER.md
questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md
```

Narrow searches for `singletonBase` together with `law`, `mass`, `repaired`,
and `atom` found no checked declaration or conference proposition stating
(3.3), its affine law form (1.1), or the gain-aligned atom of Proposition
3.2.  Existing source comments correctly warn that the laws are not
*identified as equal*; Proposition 3.1 instead gives their exact pushforward
relation.  The pair-base countermodel in Proposition 5.1 is also distinct from
the reviewed rational regression in
`CODEX_EULER__FIN4_PAIRBASE_INERT_STALL_FEASIBILITY.md`: that regression has
singleton terminal equilibria but does not co-realize all four operational
delayed-singleton deletion passports.

## 8. Nonclaims

This note does not claim:

* equality of the source and repaired laws;
* that the producer's heavy atom equals Proposition 3.2's gain-aligned atom;
* that the owner repair is a Bellman prefix, a reached chronology, or a reset;
* that a cardinal-minimal deletion equilibrium is the repaired restriction;
* regenerated paid/reset/profile provenance at either descent limit;
* applicability of the minimum-fiber exact-root tube at a cap envelope; or
* a terminal-gap counterexample, uniform-equilibrium payoff, or proof of the
  Fin4 conjecture.
