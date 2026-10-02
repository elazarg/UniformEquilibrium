# Codimension-one passports: a reached atom and the aligned pair-base branch

**Author:** CODEX_EULER  
**Date:** 2026-08-25  
**Status:** Sections 1--9 were independently reviewed **REVISE -> PASS** after
the two bounded proof-writing repairs incorporated below; see
`feedback/CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT__BY_CODEX_RAMSEY.md`.
Section 10 independently passed after the proof-writing repairs incorporated
below; see
`feedback/CODEX_EULER__FIN4_CODIMENSION_ONE_PASSPORT_PAIRBASE_ALIGNMENT__BY_CODEX_RAMSEY__SECTION_10.md`.
Internal; no Lean declaration and no export claim for Section 10.

## 1. Question and outcome

The reviewed operational-support theorem gives, after deleting one player
from a cardinal-minimal four-player counterexample, an actual lifted
three-player approximate equilibrium and a finite pure quit time at which the
deleted player gains the full ambient terminal gap.  The sharp deletion cap
then gives the static passport

\[
\max(P_d(J),C_d(J))\geq \gamma.
\]

This note asks two narrower questions.

1. If the solo premium is separated below \(\gamma\), does the *same finite
   pure-time witness* carry a quantitatively positive nonsingleton terminal
   atom?
2. If its full-gap join coalition has size two, can the selected outsider and
   pair be aligned on one actual pair-base profile with both the checked paid
   handoff and the fixed-law reset target?

Both answers are yes.  After also applying the grand-coalition leave toggle,
the exact new finite residual is:

* a full solo passport; or
* an actual persistent-base stationary source which co-realizes the selected
  outsider as a solved reset owner, a base-localized paid debtor, a fixed
  strict-superset atom, and the fixed-law reset dispatch.  A singleton join
  gives a singleton base and exactly one debtor; a pair join gives a pair
  base and at most two possible debtors.

In the maintained full-support/all-normal hard residual, the checked
all-player singleton collision theorem makes the singleton-base producer
unconditional for every prescribed base owner.  What remains open is not
source existence but consumption of its unique-debtor/heavy-atom/reset data,
or of the operational solo passport when owner alignment is required.

This does not close the conjecture.  In particular, the quiet-lift source and
the pair-base source in the last arm are separate actual profiles selected on
the same reward table.  The result aligns the reward row and all pair-base
labels, not a chronology between those profiles.

## 2. Exact codimension-one setup

Let \(I=\operatorname{Fin}4\), let \(r\) be a quitting reward table, and let

\[
W:\texttt{QuittingTerminalExploitabilityWitness}(r),\qquad
\gamma=W.\texttt{terminalGap}>0.
\]

Fix \(M\geq0\) with

\[
|r_i(S)|\leq M                                             \tag{2.1}
\]

for every nonempty coalition \(S\) and every coordinate \(i\).  Fix a deleted
player \(d\), put \(J=I\setminus\{d\}\), and let \(\sigma\) be a terminal
\(\varepsilon\)-Nash profile of the restricted game on \(J\), where

\[
0<\varepsilon<\gamma.
\]

Let \(\lambda=L_J\sigma\) be the quiet lift: the retained players use
\(\sigma\) and \(d\) plays literal Never.  Assume that the exact operational
consumer selects this same \(d\) and a finite time \(t\) such that

\[
U_d(\lambda)+\gamma
 \leq U_d(\lambda[d\leftarrow\text{QuitExactlyAt }t]).     \tag{2.2}
\]

For the codimension-one face define

\[
\ell_d(J)=\min\!\left(0,\min_{\varnothing\ne S\subseteq J}r_d(S)\right),
\]

\[
P=P_d(J)=\max(0,r_d(\{d\})-\ell_d(J)),                    \tag{2.3}
\]

and write

\[
T(S)=r_d(S\cup\{d\})-r_d(S)
   \quad(\varnothing\ne S\subseteq J).                   \tag{2.4}
\]

At time \(t\), let \(w\) be the probability that every retained player has
continued strictly before \(t\).  Let \(a\) be the conditional probability
that at least one retained player quits at time \(t\), given that this row is
reached.  If \(a>0\), conditional on that nonempty event let \(\nu\) be the
distribution of its quitting coalition; if \(a=0\), choose \(\nu\)
arbitrarily on the nonempty subsets of \(J\).  (In the latter case the term
\(ay\) below vanishes.)  Put

\[
y=\sum_{\varnothing\ne S\subseteq J}\nu(S)T(S).           \tag{2.5}
\]

Finally let \(x=r_d(\{d\})-N_{t+1,d}\), where \(N_{t+1,d}\)
is the literal-Never payoff from the next live suffix.  Exact pure-time
transport and the opponent-coalition expansion give

\[
G_t=w\Delta,\qquad
\Delta=(1-a)x+ay,\qquad G_t\geq\gamma,                   \tag{2.6}
\]

with \(x\leq P\) and every \(T(S)\leq2M\).

The checked inputs for (2.2) and (2.6) are respectively the reviewed
Propositions 1--3 of
`CODEX_CEDAR__OPERATIONAL_ESSENTIAL_SUPPORT_REDUCTION.md` and

```text
quittingRootSequencePureTimeTerminalValue_some_sub_none_eq
quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle.
```

## 3. Quantitative reached-atom theorem

### Theorem 3.1 (solo deficit forces a source-matched join atom)

In the setup above, suppose that for some \(\eta>0\),

\[
P\leq\gamma-\eta.                                        \tag{3.1}
\]

Then \(M>0\), and the same finite time \(t\) from (2.2) satisfies

\[
w\geq\frac{\gamma}{2M},qquad
a\geq\frac{\eta}{2M},qquad y\geq\gamma.                \tag{3.2}
\]

Moreover, with

\[
\mathcal H=\{S:\varnothing\ne S\subseteq J,
                   \ T(S)\geq\gamma/2\},                \tag{3.3}
\]

the quiet-lift source has, at the selected time, aggregate first-absorption
mass

\[
\Pr_\lambda(\text{first quit is at }t
             \text{ and its coalition lies in }\mathcal H)
 \geq \frac{\gamma^2\eta}{16M^3}.                        \tag{3.4}
\]

Consequently there is a nonempty \(S_{1/2}\subseteq J\) such that

\[
T(S_{1/2})\geq\gamma/2,\qquad
\Pr_\lambda(\text{terminal coalition}=S_{1/2})
 \geq \frac{\gamma^2\eta}{112M^3}.                       \tag{3.5}
\]

There is also a possibly different nonempty \(S_1\subseteq J\), having
positive probability at the selected row, such that

\[
T(S_1)\geq\gamma.                                        \tag{3.6}
\]

Finally, \(\lambda\) is itself an actual behavioral source with

\[
d_d(\lambda)\geq\gamma,\qquad
d_j(\lambda)\leq\varepsilon\quad(j\in J).               \tag{3.7}
\]

Thus it has one uniquely \(\gamma\)-large debt coordinate, the exact
finite-time deviation provenance (2.2), and the quantitative atom (3.5) on
one profile.

#### Proof

All terminal rewards, including the nonabsorption payoff zero, lie in
\([-M,M]\).  Hence every pure-time payoff gain and every reached-row
Quit-minus-Continue difference is at most \(2M\).  Equations (2.2) and (2.6)
therefore imply

\[
0<\gamma\leq w\Delta\leq2Mw,
\]

so \(M>0\) and \(w\geq\gamma/(2M)\).  Since \(w\leq1\),
\(\Delta\geq\gamma\).

If \(a=0\), then \(\Delta=x\leq P<\gamma\), a contradiction.  Hence
\(a>0\), and

\[
\gamma
 \leq\Delta
 \leq(1-a)P+ay
 =P+a(y-P).                                               \tag{3.8}
\]

Because \(a\leq1\), (3.8) first gives \(y\geq\gamma\).  Also
\(y\leq2M\) and \(P\geq0\), so

\[
\eta\leq\gamma-P\leq a(y-P)\leq2Ma,
\]

which proves the second bound in (3.2).

Let \(h=\nu(\mathcal H)\).  Every toggle is at most \(2M\), while outside
\(\mathcal H\) it is at most \(\gamma/2\).  Therefore

\[
\gamma\leq y
 \leq 2Mh+(1-h)\frac\gamma2.
\]

In particular \(\gamma\leq2M\) and

\[
h\geq\frac{\gamma}{4M-\gamma}\geq\frac{\gamma}{4M}.      \tag{3.9}
\]

Applying the chain rule to the nested events--reach time \(t\), absorb at
that row conditional on reaching it, and land in \(\mathcal H\) conditional
on absorption--gives

\[
w a h\geq
 \frac\gamma{2M}\frac\eta{2M}\frac\gamma{4M}
 =\frac{\gamma^2\eta}{16M^3},
\]

which is (3.4).  A three-player set has exactly seven nonempty subsets, so
pigeonhole gives a coalition whose mass at time \(t\) is at least one seventh
of (3.4).  Its total terminal-outcome mass can only be larger, proving (3.5).

Since the finite conditional average \(y\) is at least \(\gamma\), some
positive-\(\nu\) coalition has toggle at least \(\gamma\), proving (3.6).
The pure-time deviation gives the first inequality in (3.7).  For every
retained player, exact deletion/lift naturality transports every ambient
unilateral deviation back to the restricted game; restricted terminal
\(\varepsilon\)-Nash therefore gives the second inequality.  QED.

### Boundary checks

* The margin \(\eta>0\) is essential.  At \(P=\gamma\), the whole gain may
  come from the empty row and no positive retained absorption is forced.
* The factor \(112=16\cdot7\) is only the Fin4 codimension-one pigeonhole
  loss.  The aggregate estimate (3.4) is sharper.
* The full-gap coalition in (3.6) need not be the quantitative atom in (3.5).
  This distinction cannot be removed at equality: arbitrarily small mass can
  carry the unique toggle strictly above \(\gamma\).
* The result uses the source-weighted event \(wa\), not merely the conditional
  row absorption \(a\).  This is the provenance missing from the static
  passport.

## 4. Finite incidence split and the pair-base consumer

Because \(|J|=3\), the full-gap coalition \(S_1\) in (3.6) has cardinality
one, two, or three.

### Theorem 4.1 (the card-two passport has a same-profile pair-base reset handoff)

Assume \(|S_1|=2\), write \(S_1=\{a,b\}\), let \(d\) be the deleted outsider,
and let \(k\) be the unique fourth label.  Thus

\[
r_d(\{a,b\})+\gamma\leq r_d(\{a,b,d\}).                  \tag{4.1}
\]

Let \(X_*\) be any supplied positive global minimum of total terminal debt in
the semantic carrier.  Then there is one actual pair-base stationary profile
\(\rho\), one actual terminal semantic pair/law \((T,\mu)\) generated by
\(\rho\), a base debtor \(e\in\{a,b\}\), and a returned pair \(R\) such that:

1. \(a,b\) Quit surely in \(\rho\), while \(d,k\) are selected from the full
   induced Nash set;
2. both free coordinates are solved against unrestricted behavioral
   deviations and lie above punishment;
3. the free absorption mass is at least
   \(\gamma/(\gamma+2M)\), and some strict-superset terminal atom has mass at
   least \(\gamma/[3(\gamma+2M)]\);
4. all positive debt lies in \(\{a,b\}\), with
   \(d_e(T)\geq\gamma\), and the literal stationary profile \(\rho\) carries
   a paid first-disagreement row of gain \(\gamma\) for this same \(e\);
5. the passport outsider is simultaneously a solved reset owner,
   \(d_d(T)=0\), and the complete law has unit \((d,a)\) opponent incidence;
6. the same \((T,\mu)\) enters a fixed-law reset dispatch

   \[
   \texttt{QuittingFixedLawResetDispatch}
      (X_*,T,\mu,d,a,R).                                \tag{4.2}
   \]

Thus the card-two passport does force compatible owner/base/incidence/debt
labels on one actual pair-base profile.  The paid debtor is necessarily a
base player and is distinct from the passport outsider/reset owner.

#### Proof

Apply

```text
nonempty_finFourPairBaseStationaryTwoDebtorHandoff
```

with base `a,b`, joiner `d`, and fourth label `k`.  Hypothesis (4.1) is
exactly its full-gap pair-join premise.  Its returned point and literal
stationary profile give items 1--4.

The theorem's `joiner_solved` field gives \(d_d(T)=0\).  Since `a` Quits
surely and `a != d`, every terminal realization contains `a`; absorption is
at date zero.  Hence the terminal opponent-incidence mass of `a` as observed
by `d` is exactly one.  The pair/law is an actual point of
`quittingTerminalSemanticLawCarrier`.

These are precisely the target hypotheses of

```text
QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch.
```

Use the supplied positive global minimum \(X_*\), reset owner `d`, and
incidence label `a`.  The theorem returns \(R\) and (4.2), without reselecting
the pair-base point or its law.  QED.

### Theorem 4.2 (the singleton passport has a one-debtor reset handoff)

Assume instead that the full-gap coalition in (3.6) is the singleton
\(S_1=\{j\}\).  Let \(d\) be the deleted outsider and let \(k,\ell\) be the
remaining two labels.  Thus

\[
r_d(\{j\})+\gamma\leq r_d(\{j,d\}).                     \tag{4.3}
\]

For the same supplied positive global minimum \(X_*\), there is one actual
singleton-base stationary profile \(\rho\), generated by an induced Nash
point on the three free labels \(\{d,k,\ell\}\), whose semantic pair/law
\((T,\mu)\) satisfies all of the following.

1. All three free coordinates are solved against unrestricted behavioral
   deviations and lie above punishment.
2. If \(A_{\rm free}\) is the probability that at least one free player
   Quits at date zero, then

   \[
   A_{\rm free}\geq\frac{\gamma}{\gamma+2M}.             \tag{4.4}
   \]

   Consequently some terminal atom strictly containing \(\{j\}\) has mass
   at least

   \[
   \frac{\gamma}{7(\gamma+2M)}.                          \tag{4.5}
   \]
3. Every positive debt coordinate is \(j\), and

   \[
   d_j(T)\geq\gamma.                                     \tag{4.6}
   \]

   The same stationary profile carries a paid first-disagreement row of gain
   \(\gamma\) for observer \(j\).
4. The passport outsider is a solved reset owner, \(d_d(T)=0\), and the law
   has unit \((d,j)\) opponent incidence.
5. There is a returned pair \(R\) with

   \[
   \texttt{QuittingFixedLawResetDispatch}
      (X_*,T,\mu,d,j,R).                                 \tag{4.7}
   \]

#### Proof

Choose a point in

```text
quittingPersistentBaseNashSet reward {j} (univ.erase j)
```

and form its persistent-base stationary root and profile.  Nonemptiness is
`quittingPersistentBaseNashSet_nonempty`.  The base player `j` Quits surely,
so after every unilateral deviation by a free player the row still absorbs
at date zero.  The induced Nash inequalities are therefore the full
unrestricted behavioral-cap inequalities, and all three free coordinates are
solved and above punishment.

Write \(x_d,x_k,x_\ell\) for the three free Quit probabilities and put

\[
z=(1-x_k)(1-x_\ell).
\]

Player \(d\)'s Quit-minus-Continue gap, conditional on \(k,\ell\), is at
least \(\gamma\) at their all-Continue corner by (4.3), and is at least
\(-2M\) at each other corner.  If \(x_d=1\), then
\(A_{\rm free}=1\).  If \(x_d<1\), Continue belongs to player \(d\)'s Nash
support, so its expected gap is nonpositive.  Hence

\[
0\geq z\gamma-(1-z)2M,
\qquad 1-z\geq\frac\gamma{\gamma+2M}.                    \tag{4.8}
\]

The probability that at least one free player Quits is at least \(1-z\),
proving (4.4).  The seven nonempty subsets of a three-player free set are
exactly the strict-superset terminal atoms of the sure base; their masses sum
to \(A_{\rm free}\).  Pigeonhole proves (4.5).

Apply the ambient terminal exploitability witness to this literal stationary
profile.  Stationary unrestricted-cap domination gives some debt coordinate
at least \(\gamma\); all free debts are zero, so that coordinate is `j`.
Rewriting the stationary envelope as the stationary unilateral cap and using
the checked Quit-now/Never orientation and first-disagreement decoder gives
the paid row for `j`.

The actual pair/law belongs to the joint carrier.  Since `d` is free and
solved, it has zero debt.  Since `j` Quits surely and `j != d`, its opponent
incidence as observed by `d` is one.  Apply
`QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch` to the
same pair/law, with source \(X_*\), reset owner `d`, and incidence label `j`.
This yields (4.7) without reselecting the induced Nash point.  QED.

### Corollary 4.3 (unconditional hard-residual one-debtor source)

Let `residual` be the checked
`FinFourQuantitativeFullSupportHardResidual`.  For every prescribed singleton
owner \(j\), the theorem

```text
FinFourQuantitativeFullSupportHardResidual.
  exists_terminalGap_collision_at_singleton
```

selects \(d\ne j\) satisfying (4.3).  Apply Theorem 4.2.  Thus, for every
singleton owner, the maintained Fin4 hard residual has an actual stationary
source with:

* positive-debt support exactly \(\{j\}\), with debt at least
  \(\gamma\);
* a source-matched paid row for \(j\);
* three unrestrictedly solved free coordinates;
* a strict-superset atom of mass at least
  \(\gamma/[7(\gamma+2M)]\); and
* on the same profile/law, a distinct zero-debt reset owner \(d\), unit
  \((d,j)\) incidence, and the fixed-law reset dispatch from the positive
  global minimum.

The positive minimum is supplied by the checked positive-minimum equivalence
for the terminal witness.  This corollary is independent of which player the
codimension-one operational deletion theorem selects.

It strengthens the already checked prescribed-owner stationary handoff in a
different direction: it keeps the unrepaired singleton source, quantitatively
forces a strict-superset atom, and co-realizes a distinct reset owner on that
same law.  It does not perform the singleton owner's Always-Continue repair,
and it does not remove the fixed-law dispatcher's all-Continue arm.

### Theorem 4.4 (minimum-debtor collider alignment or two-label support)

At the positive global minimum \(X_*\), at least one of the following holds.

1. There are distinct labels \(j,d\) such that \(d\) is a full-gap collider
   at the singleton \(\{j\}\) and

   \[
   d_d(X_*)>0.                                           \tag{4.9}
   \]

   Theorem 4.2 then gives one actual singleton-base source with unique debtor
   \(j\), reset owner \(d\), the quantitative atom, and a fixed-law dispatch
   whose transfer field is strictly positive:

   \[
   0<d_d(X_*)
    \leq\sum_{i\ne d}
       \bigl(d_i(R)-d_i(X_*)\bigr).                      \tag{4.10}
   \]
2. The positive-debt support of \(X_*\) has cardinality at most two.

#### Proof

Let \(C\) be the set of all labels which occur as a checked full-gap collider
at at least one singleton:

\[
C=\{d:\exists j\ne d,\
       r_d(\{j\})+\gamma\leq r_d(\{j,d\})\}.             \tag{4.11}
\]

The all-player collision theorem makes \(C\) nonempty and in fact
\(|C|\geq2\).  If \(C\) were the singleton \(\{c\}\), applying the collision
theorem to owner \(c\) would require a collider different from \(c\) which
still belongs to \(C\), a contradiction.

If the minimum positive-debt support meets \(C\), choose \(d\) in the
intersection and a singleton owner \(j\) witnessing \(d\in C\).  Corollary
4.3, with that exact collision pair, gives the source and reset dispatch.  Its
checked transfer inequality is the weak inequality in (4.10), while the
chosen minimum debt makes the left side strict.

Otherwise the minimum positive-debt support is contained in
\(I\setminus C\).  Since \(|I|=4\) and \(|C|\geq2\), its cardinality is at
most two.  The support is nonempty because \(D(X_*)>0\), but no stronger
cardinality conclusion follows from this counting argument.  QED.

This is a genuine same-table semantic alignment alternative, not raw
incidence bookkeeping.  Arm 1 aligns one positive minimum-debt coordinate
with the reset owner of the actual unique-debtor/heavy-atom stationary
source.  Arm 2 is a strict finite reduction of the possible minimum debt
support.  Neither arm orients total debt after the reset or removes its
all-Continue wall.

The checked prescribed-owner pair-base reset theorem can already choose an
arbitrary positive minimum debtor as reset owner, so Theorem 4.4 is not novel
as a bare reset-existence statement.  Its extra content is that the reset
target is the same collision-selected singleton-base law with exactly one
debtor and the quantitative strict-superset atom.  If that stronger alignment
fails, the two-label bound in arm 2 is the retained output.

### Corollary 4.5 (strict finite residual)

For each codimension-one operational source satisfying (3.1), at least one
of the following holds:

1. the same-profile singleton-base reset handoff of Theorem 4.2;
2. the same-profile pair-base reset handoff of Theorem 4.1; or
3. a full-gap grand-coalition join by its deleted player.

Without assuming the solo deficit (3.1), add the fourth arm
\(P_d(J)\geq\gamma\).  In a cardinal-minimal Fin4 counterexample, the
operational theorem supplies this alternative for every singleton deletion
\(d\), although the restricted profile and finite time may be reselected with
\(d\).

This is a strict finite reduction of the sharp deletion passport: its
singleton and card-two join chambers now enter actual unrestricted-deviation
semantic sources and fixed-law reset targets, rather than remaining static
hyperedges.  Only the solo and grand-join passports remain without this
consumer.

## 5. The grand-join arm is not an independent residual

The operational construction may reselect its restricted profile and finite
time when the deleted label changes.  Nevertheless, its full-gap row
inequality is static, and the grand-coalition toggle eliminates the apparent
grand-join residual after one label change.

### Theorem 5.1 (grand join descends to solo or a consumed small join)

Assume the codimension-one operational passport is available for every
player, as it is in a cardinal-minimal Fin4 counterexample.  Then at least one
of the following holds:

1. for some player \(e\),

   \[
   P_e(I\setminus\{e\})\geq\gamma;                      \tag{5.1}
   \]
2. a singleton join enters Theorem 4.2; or
3. a pair join enters Theorem 4.1.

In particular a grand join is never a final independent chamber.

#### Proof

Apply the sharp codimension-one passport to any player \(d\).  If its solo
arm holds, we have item 1.  If a full-gap join coalition has size one or two,
Theorem 4.2 or 4.1 applies.  It remains to consider

\[
r_d(I\setminus\{d\})+\gamma\leq r_d(I).                 \tag{5.2}
\]

Apply the checked terminal-witness leave-or-join theorem to the grand
coalition \(I\).  There is no outsider, so it returns a member \(e\in I\)
with

\[
r_e(I)+\gamma\leq r_e(I\setminus\{e\}).                 \tag{5.3}
\]

Necessarily \(e\ne d\): if \(e=d\), adding (5.2) and (5.3) gives
\(2\gamma\leq0\), contrary to \(\gamma>0\).

Now apply the codimension-one passport for the deleted player \(e\).  Its
grand-join row is impossible, because (5.3) gives

\[
r_e(I)-r_e(I\setminus\{e\})\leq-\gamma<\gamma.          \tag{5.4}
\]

Thus its passport is either the solo arm (5.1), a singleton join, or a pair
join.  The latter two enter Theorems 4.2 and 4.1.  This is a literal one-step
rank decrease from “grand join allowed” to “grand join forbidden” at the new
label \(e\); no chronology or common restricted profile is asserted.  QED.

### Corollary 5.2 (the only unconsumed passport is solo)

For a cardinal-minimal Fin4 witness, the operational essential-support and
sharp deletion theorems, Theorems 4.1--4.2, and Theorem 5.1 yield:

* an actual singleton- or pair-base stationary paid/reset source with a
  quantitative strict-superset atom; or
* a player \(e\) satisfying the full solo passport (5.1).

This is the smallest theorem-driven finite obligation obtained here.  The
second arm is still only a pure-time/continuation comparison and has no
checked stationary or Bellman consumer.

## 6. Exact regressions and the remaining mismatch

The pair-base consumer deliberately solves the passport outsider; it does not
preserve that outsider as the paid debtor.  This is not a proof artifact.
Fix a sure base \(B=\{0,1\}\), passport outsider \(d=2\), and fourth label
\(k=3\).  Program player 2's two pair-base endpoint gaps as

\[
\Delta_2(k=0)=1,\qquad \Delta_2(k=1)=-1,                \tag{6.1}
\]

for example by

\[
r_2(B)=0,\ r_2(B\cup\{2\})=1,\quad
r_2(B\cup\{3\})=0,\ r_2(I)=-1.                         \tag{6.2}
\]

Set player 3's two endpoint gaps to zero.  Then the induced point
\(p_2=p_3=1/2\) is an exact Nash point: player 2's averaged gap is zero and
player 3 is indifferent.  The full-gap pair passport at \(B\) coexists with
zero debt for player 2 on the pair-base source.  Any ambient terminal-gap
debtor at that source must therefore be selected in the sure base.

For a grand join the mismatch is sharper.  Reverse (6.1): put
\(\Delta_2(k=0)=-1\), \(\Delta_2(k=1)=1\), and make player 3 strictly prefer
Continue when player 2 Continues.  Then \((p_2,p_3)=(0,0)\) is an exact
induced Nash point despite the full-gap grand join.  The pair-base law is
concentrated on \(B\), so the grand passport alone forces no strict-superset
atom on that selected source.  A singleton passport is consumed by Theorem
4.2 using a singleton rather than a pair base; it does not constrain an
arbitrarily preselected pair-base point.

These are local exact interface regressions, not four-player counterexamples:
the partially specified tables are not claimed to retain a global terminal
exploitability witness.  They show why the grand arm cannot be sent to
Theorem 4.1 using only the displayed row inequalities.

The five-player same-profile spare-cancellation verifier does not remove this
boundary.  It needs sure-spare endpoint complementarity for every old free
coordinate and the scalar budget \(q_*\kappa\leq D_0\).  The exact rational
tables in
`CODEX_EULER__SPARE_CANCELLATION_HYPOTHESIS_INDEPENDENCE.md` show that these
conditions are independent of source debt localization, base cancellation,
and punishment floors.  No such fields are supplied by the codimension-one
passport.

## 7. Source and novelty audit

The following files and declarations were inspected.

```text
UniformEquilibrium/Diagnostics/Quitting/MinimalFinCounterexample.lean
  MinimalFinQuittingCounterexample.exists_uniformEquilibriumPayoff_of_card_lt

UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticSmallSurvivorDeletionExcessBound.lean
  exists_terminalNash_deleteBlock_of_card_le_three

UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean
  quittingTerminalPayoff_liftDeletedProfile
  quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation

UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean
  quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime

UniformEquilibrium/Quitting/Paths/OutsiderNeverGluing.lean
  quittingRootSequencePureTimeTerminalValue_some_sub_none_eq

UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticEndpointDefectPolarity.lean
  quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle

UniformEquilibrium/Quitting/Classification/
  TerminalExploitabilityToggles.lean
  QuittingTerminalExploitabilityWitness.exists_leave_or_join_gain

UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  PairBaseStationaryTwoDebtorHandoff.lean
  nonempty_finFourPairBaseStationaryTwoDebtorHandoff
  PunishmentNormalAtomicCollisionHandoff.lean
  FinFourQuantitativeFullSupportHardResidual.
    exists_terminalGap_collision_at_singleton

UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/
  PersistentBaseInducedGame.lean
  quittingPersistentBaseNashSet_nonempty
  persistentBase_inducedNash_free_semantics

UniformEquilibrium/Diagnostics/Quitting/
  TerminalSemanticResetIncidenceCapReturn.lean
  QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch

UniformEquilibrium/Quitting/Paths/SurvivalWindowLanding.lean
  quittingJointSurvivalWeight_mul_tailDeviationGain_le

UniformEquilibrium/Quitting/Root/EndpointOpponentStability.lean
  abs_quittingRootEndpointDifference_sub_le_opponentTVSum

UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean
  quittingTerminalSemanticDebt_prefix_le
```

The static inequality `max(P,C)>=gamma` and the exact finite pure-time
provenance were already independently reviewed in
`CODEX_EULER__OPERATIONAL_ESSENTIALITY_SHARP_DELETION_PASSPORT.md` and
`CODEX_CEDAR__OPERATIONAL_ESSENTIAL_SUPPORT_REDUCTION.md`.  A narrow search
found no checked or conference theorem which states the quantitative
source-mass conclusion (3.4)--(3.7), the singleton-join quantitative
one-debtor construction, or the same-selected-point composition of either
quantitative handoff with the fixed-law reset dispatcher.

Theorems 3.1, 4.2, and 5.1 are new ordinary mathematics.  Theorem 4.1 is a new
composition of checked components, not a new compiler.  Corollary 4.3 is the
strongest conjecture-facing producer here: it applies Theorem 4.2
unconditionally to the checked all-player singleton collision map.  Corollary
5.2 consumes both small-join chambers and removes the grand join by a one-step
label rank; it does not close the remaining solo residual.

## 8. Exact nonclaims and next check

This note does **not** claim:

* that the quiet-lift source equals or reaches the pair-base source;
* that the quantitative half-gap atom is the full-gap coalition used in
  Theorem 4.1 or 4.2;
* that the reset returned pair is the stationary target pair;
* that the stationary paid row transfers to the returned reset pair;
* punishment-floor admissibility of the reset's positive branch;
* an exact Bellman return, debt descent, or uniform-equilibrium payoff; or
* that the local endpoint regressions retain an ambient witness.

The independent review checked the event-mass constant in (3.4), including
the separate lower bounds on reach \(w\) and conditional absorption \(a\),
and checked that Theorems 4.1--4.2 apply the fixed-law reset dispatcher to the
*same* handoff point and law rather than to an independently selected reset
target.

## 9. Post-review consumer audit of the solo residual

I compared the remaining alternative

\[
P_e(I\setminus\{e\})\geq\gamma
\]

with the checked Fin4 solo-wall declarations in
`TerminalSemanticFinFourSoloWallDispatch.lean`.  There is a genuine type
gap.  The passport says that the singleton payoff of \(e\) exceeds the
*minimum over possible retained terminal coalitions* by \(\gamma\).  It does
not select a carrier pair realizing that minimizing coalition, make \(e\) the
unique semantic debtor there, make the carrier owner-tight at its singleton
payoff, or provide the uniform opponent-absorption hypothesis required by
`exists_strictCarrierDebtDescent_of_opponentAbsorptionFloor`.  It likewise
does not provide the exact solo root and positive limiting outsider endpoint
difference required by `exists_first_soloPrefix_outsiderWall`.

Thus the current checked solo-wall machinery does not consume (5.1) without
an additional actual-source selection theorem.  This is not merely a missing
incidence label: the minimizing coalition in the scalar definition of
\(P_e\) may have zero probability in every presently selected pair-base or
singleton-base stationary source.  No further chamber reduction is claimed
from the solo inequality alone.

## 10. The strict solo residual produces a one-debtor carrier descent

The scalar minimizer itself need not be reached, but the *operational
pure-time witness* has enough provenance to select a different carrier source.
This removes the purely static obstruction in Section 9, although it does not
make the resulting edge floor-admissible or iterable.

Fix a label \(e\), write \(J=I\setminus\{e\}\), and retain all hypotheses of
Theorem 3.1.  In addition assume the nonsingleton insertion cap is strictly
below the terminal gap:

\[
C_e(J):=\max\!\left(0,
  \max_{\varnothing\ne S\subseteq J}
    [r_e(S\cup\{e\})-r_e(S)]\right).
\]

\[
C_e(J)\leq\gamma-\eta,
\qquad \eta>0.                                      \tag{10.1}
\]

This is exactly the residual after the checked singleton/pair consumers and
the grand-to-distinct-label descent: if \(C_e(J)\geq\gamma\), a full-gap
nonsingleton join is already available.

### Theorem 10.1 (conditional solo source and exact carrier descent)

Let \(|r_i(S)|\leq M\), let \(I=\operatorname{Fin}4\), and suppose the same
table carries the maintained quantitative hard residual, so in particular
every singleton owner has a distinct full-gap collider.  Under (10.1), there
exist a carrier pair \(R\), an exact product root \(q\) at \(R.1\), and

\[
R'=\operatorname{Prefix}(q,R)
\]

such that

\[
\begin{aligned}
&d_j(R)=d_j(R')=0 &&(j\ne e),\\
&r_e(\{e\})-R.1_e\geq\gamma,\qquad d_e(R)\geq\gamma,\\
&A_{-e}(q)\geq \alpha:=\frac{\gamma}{12M}>0,\\
&D(R')\leq(1-\alpha)D(R),\\
&D(R)-D(R')\geq\frac{\gamma^2}{12M}>0,\\
&D(R)\geq D_*+\frac{\gamma^2}{12M}.           \tag{10.2}
\end{aligned}
\]

Thus the strict solo residual produces a literal exact carrier edge with a
fixed positive total-debt decrease while preserving the singleton debt
support \(\{e\}\).  In particular \(R\) is quantitatively separated from the
global minimum fiber.

#### Proof: selecting the next-suffix carrier

Choose \(\epsilon_n\downarrow0\).  Apply the checked
`quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three` and then
`quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff` to solve
the retained three-player game to terminal error \(\epsilon_n\), and lift it
quietly with \(e\) playing Never.
Proposition 2 of the reviewed operational-support note selects a finite time
\(t_n\) with gain at least \(\gamma\).  Use the notation of (2.6): \(w_n\)
is reach before the selected row, \(a_n\) is conditional retained absorption
at the row, \(c_n=1-a_n\), and

\[
\Delta_n=c_nx_n+(1-c_n)y_n,
\quad x_n=r_e(\{e\})-N_{n,t_n+1,e}.
\]

Here \(w_n\Delta_n\geq\gamma\), \(x_n\leq2M\), and (10.1) gives
\(y_n\leq C_e(J)\leq\gamma-\eta\).  Since \(w_n\leq1\),
\(\Delta_n\geq\gamma\).  A convex average below \(\gamma\) is impossible,
so

\[
x_n\geq\gamma.                                      \tag{10.3}
\]

Moreover \(\Delta_n\leq2M\) gives

\[
w_n\geq\frac{\gamma}{2M},
\qquad
c_n\geq\frac{\eta}{2M-\gamma+\eta}>0.               \tag{10.4}
\]

The second inequality follows from

\[
\gamma\leq c_n(2M)+(1-c_n)(\gamma-\eta).
\]

Condition on reaching the next suffix, namely on survival before \(t_n\) and
on no retained quit at row \(t_n\).  Its probability is at least

\[
\rho:=\frac{\gamma\eta}
 {2M(2M-\gamma+\eta)}>0.                              \tag{10.5}
\]

Let \(R_n\) be the literal terminal-semantic pair of that conditional suffix.
A retained player's conditional deviation transports back to the quiet lift
with the factor \(w_nc_n\).  Hence

\[
d_j(R_n)\leq\frac{\epsilon_n}{\rho}\qquad(j\ne e).  \tag{10.6}
\]

The semantic carrier is compact.  Pass to a convergent subsequence
\(R_n\to R\).  Equations (10.3) and (10.6) are closed.  Each \(R_n\) is the
semantic pair of an actual conditional suffix profile.  The checked terminal
gap witness therefore gives, for every \(n\), some coordinate whose debt at
\(R_n\) is at least \(\gamma\).  After a further finite-label subsequence this
coordinate is fixed.  It cannot be any \(j\ne e\), because (10.6) makes every
such debt converge to zero.  Hence it is \(e\), and closed cap/debt convergence
gives

\[
d_j(R)=0\ (j\ne e),\qquad
r_e(\{e\})-R.1_e\geq\gamma,qquad d_e(R)\geq\gamma.  \tag{10.7}
\]

This is the promised literal carrier selector.  It is a compactified
conditional suffix in the closed semantic carrier, not necessarily an
attained behavior profile and not the coalition attaining the scalar minimum
in \(P_e(J)\).

#### Proof: the exact root must expose an opponent

Choose an exact mixed Nash root \(q\) of the finite one-stage quitting game
with continuation \(R.1\).  Put \(A_{-e}(q)\) for the probability that some
opponent of \(e\) quits.  The terminal-gap bound gives \(0<\gamma\leq2M\), so
\(\alpha=\gamma/(12M)\) is well-defined and less than one.

Suppose \(A_{-e}(q)<\alpha\).  Compare \(q\) with the all-Continue root in
player \(e\)'s endpoint difference.  Each of the three opponent Quit
marginals is at most \(A_{-e}(q)\).  The checked opponent-TV stability bound
therefore moves the endpoint difference by less than

\[
4M\cdot3A_{-e}(q)<\gamma.
\]

By (10.7), Quit is strictly better than Continue for \(e\) at \(q\), so exact
complementarity forces \(q_e=1\).

Let \(c\ne e\) be the full-gap singleton collider supplied by the hard
residual:

\[
r_c(\{e\})+\gamma\leq r_c(\{e,c\}).                  \tag{10.8}
\]

Compare \(q\) with the row where \(e\) quits surely and the other two players
besides \(e,c\) Continue.  Only those two opponent marginals enter player
\(c\)'s endpoint difference, so opponent-TV stability moves (10.8) by less
than

\[
4M\cdot2A_{-e}(q)<\frac{2\gamma}{3}.
\]

Thus player \(c\) also strictly prefers Quit, and exact complementarity forces
\(q_c=1\).  This contradicts \(A_{-e}(q)<\alpha<1\).  Therefore
\(A_{-e}(q)\geq\alpha\).

#### Proof: debt contraction

Prefixing a carrier pair by any product root stays in the carrier.  The exact
root-debt inequality gives

\[
d_j(R')\leq O_j(q)d_j(R).
\]

Carrier debts are nonnegative, so (10.7) makes every \(j\ne e\) debt remain
zero.  For \(e\), \(O_e(q)=1-A_{-e}(q)\leq1-\alpha\).  Consequently

\[
D(R')=d_e(R')\leq(1-\alpha)d_e(R)=(1-\alpha)D(R).
\]

Since \(D(R)=d_e(R)\geq\gamma\), the displayed fixed debt drop in (10.2)
follows.  Finally \(R'\) belongs to the semantic carrier, so the global
minimum satisfies \(D_*\leq D(R')\); combining this with the debt drop gives
the last line of (10.2).  QED.

### Exact scope and obstruction after the descent

Theorem 10.1 is semantic rather than static: it produces a literal carrier
tail, an exact Nash--Bellman edge, positive absorption, and a fixed strict
total-debt decrease.  It does **not** complete the conjecture.

* The source need not be punishment-floor admissible in coordinate \(e\).
  The three zero-debt coordinates are automatically above their behavioral
  punishment floors, but \(R.1_e\) can lie below \(P_e\).
* The immediate solo-gap field (10.7) need not survive at \(R'\).  Thus the
  construction cannot simply be iterated from its endpoint.
* Reattaching the repaired suffix beneath the earlier quiet prefix can change
  the three retained players' continuation payoffs and destroy their zero
  debts.  No checked graft theorem preserves those coordinates.

Accordingly, the exact remaining connector is now narrower: either prove
\(P_e\leq R.1_e\) for the selected conditional source, or preserve all three
solved continuation coordinates while grafting the root repair.  The honest
closed-homotopy stalling regression
`localGlobal_periodOne_debtHomotopy_stalls` shows that auxiliary cap-to-payoff
interpolation alone cannot force a non-all-Continue selector.
