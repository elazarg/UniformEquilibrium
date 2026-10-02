# Fin4 pair-base inert-stall feasibility boundary

**Author:** CODEX_EULER  
**Status (2026-08-25):** internal exact regression and finite residual screen;
the Gray-cycle candidate is now solved by an explicit stationary exact
terminal Nash profile. Independent falsification requested. This note does
not eliminate the ambient inert stall and does not produce a counterexample
to the quitting-game conjecture.

## 1. Question and answer

The checked Fin4 same-source construction supplies, from a terminal
exploitability witness, one actual pair-base stationary profile carrying a
full-gap paid row, a prescribed-owner zero-debt reset, unit base-to-owner
incidence, a positive global semantic-debt minimum, and its literal cap lift.
The remaining cap-port arm has total absorption

\[
 A=\sum_n a_n=0.
\]

Does this inertness contradict the reward/payoff identities of the actual
pair-base profile?

**Answer.** No contradiction follows from the local pair-base, paid-row,
reset, and inert-cap identities.  An exact rational Fin4 game below realizes
all of them, and in fact makes all Continue the unique exact cap root.  It also
has positive debt at all Never.  Its first failure is genuinely global: every
one-quitter stationary profile is an exact unrestricted terminal Nash profile,
so the global semantic minimum is zero and there is no terminal
exploitability gap.

Thus a proof excluding the ambient inert arm must use the global
positive-minimum/terminal-gap quantifier away from the pair-base source.  It
cannot be a pointwise algebraic contradiction at that source.

## 2. Narrow checked source audit

The source declarations inspected are:

- `FinFourPairBasePaidResetTarget`,
  `nonempty_finFourPairBasePaidResetTarget`, and
  `QuittingTerminalExploitabilityWitness.exists_finFour_pairBasePaidResetDispatch`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetAlignment.lean`;
- `QuittingTerminalExploitabilityWitness.exists_finFour_pairBasePaidResetDispatch_payoffAligned`
  in `PairBasePaidResetPayoffAlignment.lean`;
- `FinFourPairBasePaidResetTarget.capLiftedSource` and
  `QuittingTerminalExploitabilityWitness.nonempty_finFourSameSourcePaidResetCapPort`
  in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FinFourSameSourcePaidResetCapPort.lean`;
- `quittingCapLiftedPrefixRoot` and the cap-prefix debt/paid-row identities in
  `PaidCapLiftedSummablePort.lean`; and
- the checked trichotomy in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`.

One wording correction matters. `quittingCapLiftedPrefixRoot` is
`Classical.choose` applied to existence of an exact cap-Nash root. It is not a
maximum-absorption or maximal root. Hence `A=0` proves that every **selected**
root is all Continue. It does not by itself prove uniqueness among all exact
cap roots. The first regression below satisfies the stronger uniqueness
property, so it does not depend on this selection subtlety.

## 3. A sharp exact rational regression

Let the player set be `Fin 4`, written \(\{0,1,2,3\}\). For every nonempty
coalition \(S\), define

\[
r_i(S)=
\begin{cases}
2,&i\notin S,\\
1,&S=\{i\},\\
0,&i\in S\text{ and }|S|\ge2.
\end{cases}
\tag{3.1}
\]

Take base \(B=\{0,1\}\), reset owner \(o=2\), and the stationary profile
\(\sigma\) in which players 0 and 1 Quit surely at time zero while players 2
and 3 Never quit.

### Proposition 3.1 (exact local pair-base data)

The actual complete terminal law of \(\sigma\) is the point mass on
\(\{0,1\}\), and

\[
 U(\sigma)=(0,0,2,2),\qquad B(\sigma)=(2,2,2,2),
\tag{3.2}
\]

so

\[
 d(\sigma)=(2,2,0,0),\qquad D(\sigma)=4.
\tag{3.3}
\]

Both free players are solved against unrestricted behavioral deviations,
owner 2 has zero debt, the terminal opponent-incidence mass from base player
0 to owner 2 is one, and base player 0 has a same-profile pure-time paid row

\[
  \text{Quit now payoff }0
  \quad\longrightarrow\quad
  \text{Never payoff }2.
\tag{3.4}
\]

#### Proof

Absorption occurs at time zero at \(B\), giving (3.2)'s prescribed payoff.
If base player 0 replaces its whole behavior, player 1 still Quits surely at
time zero. Quitting gives coalition \(\{0,1\}\) and payoff 0, whereas
Continuing gives coalition \(\{1\}\) and payoff 2. The same calculation holds
for base player 1. If free player 2 or 3 deviates, the game is still resolved
at time zero by players 0 and 1: Continuing gives payoff 2 and joining them
gives payoff 0. Random behavioral deviations are convex mixtures of these
two time-zero outcomes, so no additional behavioral strategy improves on 2.
This proves the exact envelope and debts.

The outcome contains player 0 with probability one and 0 is distinct from
owner 2, so the corresponding opponent incidence is one. Finally, (3.4) is
the preceding base-player calculation with observer 0. It is a literal paid
first-disagreement row of gain 2. QED.

### Proposition 3.2 (the cap root is uniquely all Continue)

Against the displayed cap \(b=(2,2,2,2)\), every player's Continue endpoint
has payoff exactly 2 and every player's Quit endpoint has payoff at most 1,
for every product distribution of the opponents' current actions. Hence all
Continue is the unique exact cap-Nash root.

#### Proof

Fix player \(i\). If \(i\) Quits and no opponent Quits, the terminal coalition
is \(\{i\}\) and the payoff is 1. If at least one opponent Quits, the terminal
coalition contains \(i\) and has size at least two, so the payoff is 0. Thus
the Quit endpoint is at most 1.

If \(i\) Continues and some opponent Quits, the terminal coalition excludes
\(i\), so (3.1) gives payoff 2. If nobody Quits, continuation has cap value
\(b_i=2\). Thus the Continue endpoint is exactly 2. Continue is strictly
dominant at the cap root game, proving uniqueness. QED.

### Corollary 3.3 (literal inert paid cap chronology)

Every cap prefix selected by `quittingCapLiftedPrefixRoot` is all Continue.
Consequently \(A=0\), every finite prefix merely delays \(\sigma\), the
terminal law and the semantic pair remain (3.2), and the paid row (3.4) shifts
outward with its full gain 2.

This is an actual realization of the local inert paid-cap identities; it is
not merely a semantic tuple.

## 4. The first missing ambient field

The regression even has positive semantic debt at all Never. Let
\(\mathbf N\) be the all-Never profile. Its prescribed payoff is zero. Against
Never opponents, each player can Quit alone at an arbitrary finite time and
receive 1, while Never yields zero. Therefore

\[
 U(\mathbf N)=0,qquad B(\mathbf N)=(1,1,1,1),qquad D(\mathbf N)=4.
\tag{4.1}
\]

Nevertheless the game has an exact unrestricted terminal Nash profile. For
any \(i\), let \(\sigma^{\{i\}}\) have player \(i\) Quit surely at time zero
and every other player Never quit. Then

\[
 U_i(\sigma^{\{i\}})=1,qquad
 U_j(\sigma^{\{i\}})=2\quad(j\ne i).
\]

Player \(i\)'s alternatives give at most 1: Continuing forever changes the
outcome to Never and payoff zero, while quitting at any later finite time
still gives the singleton payoff 1. Every outsider \(j\) already receives 2;
joining at time zero gives coalition \(\{i,j\}\) and own payoff zero. Since
player \(i\) ends the game at time zero, later or history-dependent deviations
cannot create another outcome. Thus

\[
 B(\sigma^{\{i\}})=U(\sigma^{\{i\}}),\qquad
 D(\sigma^{\{i\}})=0.
\tag{4.2}
\]

The global positive semantic minimum and terminal exploitability witness both
fail precisely here. In particular, this regression does **not** instantiate
`FinFourSameSourcePaidResetCapPort`, because that structure correctly retains
a positive global minimum and a terminal witness as inputs. It realizes all
pointwise target/reset/paid/inert equations that precede those global fields.

## 5. Exact finite pure-profile screen under a terminal gap

The first necessary use of the global gap can be written as a finite
semialgebraic screen. Put \(v_i(\varnothing)=0\) and
\(v_i(S)=r_i(S)\) for nonempty \(S\). For a pure stationary quitting set
\(S\subseteq I\), define

\[
\delta_i(S)=
\begin{cases}
\bigl(v_i(S\setminus\{i\})-r_i(S)\bigr)_+,&i\in S,\\
\bigl(r_i(S\cup\{i\})-r_i(S)\bigr)_+,&i\notin S,\ S\ne\varnothing,\\
\bigl(r_i(\{i\})\bigr)_+,&S=\varnothing.
\end{cases}
\tag{5.1}
\]

Because every nonempty pure root absorbs at date zero, and because the empty
root is all Never, \(\delta_i(S)\) is exactly player \(i\)'s unrestricted
terminal debt at that pure profile. A terminal gap \(\Gamma>0\) therefore
forces the 16 finite disjunctions

\[
  \forall S\subseteq I,qquad \max_i\delta_i(S)\ge\Gamma.
\tag{5.2}
\]

For the pair-base target \(B=\{b,c\}\), the checked local fields reduce to

\[
\begin{aligned}
r_o(B)&\ge r_o(B\cup\{o\}),\\
r_k(B)&\ge r_k(B\cup\{k\}),\\
r_e(B\setminus\{e\})-r_e(B)&\ge\Gamma
   &&\text{for some }e\in B,
\end{aligned}
\tag{5.3}
\]

while an all-Continue cap root at its envelope requires

\[
  r_i(\{i\})\le B_i(\sigma)\qquad(i\in I).
\tag{5.4}
\]

Equations (5.1)--(5.4), together with the exact product-law moment formulas
for a mixed pair-base point, are the smallest finite reward-table residual
visible at the inert source. They are only necessary: the actual witness
quantifies over all behavioral profiles, not only the 16 pure stationary
profiles.

### Proposition 5.1 (even the finite pure screen has no incidence contradiction)

The pure-gap constraints (5.2), pair-base constraints (5.3), and existence of
an all-Continue cap root (5.4) are jointly feasible with \(\Gamma=1\).

#### Exact construction

Use the cyclic Gray word

\[
\begin{split}
\varnothing,&\{0\},\{0,1\},\{1\},\{1,2\},\{0,1,2\},
\{0,2\},\{2\},\\
&\{2,3\},\{0,2,3\},I,\{1,2,3\},\{1,3\},
\{0,1,3\},\{0,3\},\{3\},\varnothing.
\end{split}
\tag{5.5}
\]

For each directed edge \(S\to S\triangle\{i\}\) in (5.5), assign player
\(i\)'s payoff 0 at the source and 1 at the target. At the empty endpoint use
the fixed Never payoff 0: thus \(r_0(\{0\})=1\) on the first edge and
\(r_3(\{3\})=-1\) on the last edge. For every coordinate edge not used by
the Gray cycle, set that player's two endpoint rewards to zero. There is no
assignment conflict because, for fixed \(i\), the \(i\)-coordinate edges are
disjoint pairs.

At every pure profile the next Gray edge is a unilateral gain of exactly one,
proving (5.2). At \(B=\{0,1\}\), the next edge is the leave of player 0 and
has gain one. The joins of free players 2 and 3 are unused coordinate edges,
so both have zero debt. Taking owner 2 gives the pair-base reset coordinate.
The cap at this target is

\[
 B(\sigma)=(1,1,0,0),
\]

and the singleton rewards are \((1,0,0,-1)\), so (5.4) holds.

This construction only proves existence of the all-Continue cap root. It does
not prove that the opaque canonical `Classical.choose` selector uses that root,
nor that no mixed behavioral terminal profile has small debt. It is included
to show that the finite pure-incidence screen itself does not close the inert
arm.

## 6. Precise residual under the full Fin4 hypotheses

Combining the checked same-source theorem with `A=0` leaves the following
system, all on one reward table:

1. a positive global carrier minimum \(D_*>0\) and a terminal gap
   \(\Gamma>0\);
2. one actual pair-base profile with free-player unrestricted debts zero,
   a base debtor at least \(\Gamma\), a same-profile paid row, a prescribed
   owner of debt zero, and unit base-to-owner incidence;
3. a cap envelope \(B\) whose **selected** exact product root is all Continue;
4. exact stationary equality of the semantic pair and paid row under every
   finite all-Continue prefix; and
5. the global exclusions (5.2) and, beyond them, positive debt at every mixed
   and history-dependent behavioral profile.

Items 2--4 are mutually consistent by Section 3. Items 1 and the pure part of
5 do not contradict the finite incidence pattern by Proposition 5.1. The
remaining unspent datum is therefore the full behavioral/global-minimum
quantifier, or some checked consequence of it that couples a different
profile back to this same inert source.

In particular, the positive minimum only says

\[
  D_*\le D(\sigma)=4
\]

at the regression source. It does not make that source minimizing, and the
fixed-law reset dispatch starts from a separately selected minimum. The paid
row and unit incidence do not identify the minimum profile with the target.
This is the same source-separation that prevents a pointwise contradiction.

## 7. Consequence and exact next question

The inert Fin4 problem is not a finite payoff-identity inconsistency. A valid
consumer must prove at least one of the following genuinely nonlocal facts:

- the positive-minimum source can be chosen to be, reach, or preserve the
  pair-base inert target;
- the terminal gap forces a non-all-Continue cap root at that same target;
- a global no-small-debt condition forces a surcharge equality or a charged
  floor-admissible edge at the target; or
- another actual profile obtained from the target has a strict maintained
  debt/support rank decrease and retains enough source provenance to iterate.

No such producer is proved here. The note's contribution is the exact
regression and the finite residual boundary: local same-source
paid/reset/inert data are consistent, while the first failed ambient field is
global positive-minimum/terminal-gap control at other profiles.

## 8. Resolution of the Gray-cycle candidate beyond pure profiles

The Gray table in Proposition 5.1 has no pure stationary Nash profile, but it
does have a particularly simple mixed stationary exact terminal Nash profile.
This resolves that candidate completely and identifies its mixed-behavior
escape mechanism.

### Theorem 8.1 (a geometric singleton clock is exact terminal Nash)

Fix any \(x\in(0,1/2]\). Let \(\tau^x\) be the stationary profile in which
player 2 Quits independently with probability \(x\) at every live date and
players 0, 1, and 3 Never quit. Then absorption occurs almost surely at the
singleton \(\{2\}\),

\[
 U(\tau^x)=r(\{2\})=(1,0,0,0),
\tag{8.1}
\]

and

\[
 B(\tau^x)=U(\tau^x).
\tag{8.2}
\]

Thus \(\tau^x\) is an exact terminal Nash profile against unrestricted
behavioral deviations. In particular the Gray game has a uniform-equilibrium
payoff.

#### Proof

Since \(x>0\), player 2 eventually Quits with probability one. We calculate
every pure-time unilateral replacement; behavioral pure-time extremality then
gives the unrestricted cap.

For player 0, the three relevant rewards are

\[
r_0(\{2\})=1,\qquad r_0(\{0,2\})=0,
\qquad r_0(\{0\})=1.
\]

Never gives 1. Quitting at deterministic time \(t\) changes the payoff only
on the event of a tie with player 2 at time \(t\), whose probability is
\(x(1-x)^t\). Hence its payoff is

\[
  1-x(1-x)^t\le1.
\tag{8.3}
\]

Thus \(B_0=1=U_0\).

For player 1, all three relevant rewards vanish:

\[
r_1(\{2\})=r_1(\{1,2\})=r_1(\{1\})=0.
\]

Every deterministic time and Never therefore pay zero, so
\(B_1=0=U_1\).

Player 2 faces Never opponents. Its singleton reward and Never payoff are
both zero, so \(B_2=0=U_2\).

For player 3, the relevant rewards are

\[
r_3(\{2\})=0,
\qquad r_3(\{2,3\})=1,
\qquad r_3(\{3\})=-1.
\]

If player 3 Quits at deterministic time \(t\), the game already ended with
payoff zero when player 2 quit earlier. Conditional on survival to time
\(t\), player 3 receives 1 when player 2 ties it and \(-1\) when player 2
Continues. Therefore its unconditional payoff is

\[
(1-x)^t\bigl(x-(1-x)\bigr)
=(1-x)^t(2x-1)\le0.
\tag{8.4}
\]

Never gives zero, so \(B_3=0=U_3\). The checked theorem
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` upgrades these
pure-time maxima to the supremum over every behavioral replacement. This
proves (8.2).

Finally apply the sharper checked declaration
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact`: an exact
terminal Nash profile's own terminal payoff is a uniform-equilibrium payoff.
Thus the uniform target is exactly (8.1). QED.

### Interpretation

The pure Gray orbit forces a gain at every deterministic quitting-set vertex,
but its edge \(\{3\}\to\varnothing\) has reward \(-1\to0\), while the edge
\(\{2\}\to\{2,3\}\) has reward \(0\to1\) for the same player 3. The geometric
clock of player 2 mixes exactly these two signs. At \(x=1/2\) every finite
quit time of player 3 has value zero; for \(x<1/2\) every such value is
strictly negative. This is the precise mixed-behavior escape mechanism hidden
by the pure-profile no-sink screen.

Consequently Proposition 5.1 is useful only as a finite-screen boundary. It
cannot support a positive all-behavior terminal gap, and it provides no
regression for the ambient inert stall with positive global minimum.

## 9. Scope and nonclaims

- The rational regression is an actual quitting game and all deviations used
  in its calculations are unrestricted behavioral replacements.
- It is not a terminal-gap counterexample; it has exact terminal Nash profiles.
- The Gray construction is a finite pure-profile screen, not a proof about the
  canonical cap selector or arbitrary behavioral profiles.
- No cap annotation is identified with a prescribed payoff.
- No Bellman edge, payoff return, or well-founded descent is produced.
- This note is not export-ready without an independent review and, more
  importantly, it does not close a named conjecture obligation.

## 10. Requested independent check

Please independently check the unrestricted cap calculations in Propositions
3.1--3.2, the singleton-profile exact Nash obstruction (4.2), the pure-profile
debt formula (5.1), and the conflict-free Gray-cycle realization in
Proposition 5.1. Please also check the exact stationary cap calculation in
Theorem 8.1. The highest-risk distinction is selected all-Continue root versus
unique all-Continue root.
