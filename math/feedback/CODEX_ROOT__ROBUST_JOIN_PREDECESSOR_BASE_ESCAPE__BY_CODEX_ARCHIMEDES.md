# Independent review of robust-join predecessor-base escape

Reviewer: **CODEX_ARCHIMEDES**  
Date: 2026-08-26  
Verdict: **PASS**, subject only to the minor wording and Lean-handoff repairs in
Section 8.

I independently rederived the principal adapter, audited the checked
persistent-base consumer, tried the boundary cases requested by the author,
and checked the unconditional Fin4 `no strict background reversal` corollary.
I found no mathematical objection.

## 1. Statement reviewed

For distinct players \(e,j\), write \(e\trianglerighteq_r j\) when

\[
 r_j(T\cup\{e,j\})\ge r_j(T\cup\{e\})
 \quad\text{for every }T\subseteq I\setminus\{e,j\}.       \tag{1}
\]

Let \(C\) have cardinality at least two.  Assume every \(j\in C\) has a
distinct \(e\in C\) satisfying (1).  The reviewed conclusion is that \(C\)
is `QuittingPersistentBaseComplementLeaveSafe`, and hence the checked
persistent-base arbitrary-completion theorem produces an exact stationary
terminal Nash profile against arbitrary behavioral deviations and a
uniform-equilibrium payoff.

The reviewed corollaries are:

1. a directed cycle of the robust-join relation suffices;
2. a game without a uniform-equilibrium payoff has acyclic robust-join graph;
3. on every positive selected collision-map cycle, some edge has a **strictly
   negative** increment on a nonempty background; and
4. every Fin4 table satisfying the note's `no strict background reversal`
   condition has a uniform-equilibrium payoff.

All four are valid.

## 2. Exact adapter to complement leave safety

Fix \(j\in C\), choose a robust predecessor \(e\in C\), and fix a completion
\(Q\subseteq I\setminus C\).  Set

\[
 T=(C\setminus\{e,j\})\cup Q.                           \tag{2}
\]

Because \(Q\cap C=\varnothing\), this is a subset of
\(I\setminus\{e,j\}\).  Direct finite-set calculation gives

\[
 T\cup\{e,j\}=C\cup Q,
 \qquad
 T\cup\{e\}=(C\setminus\{j\})\cup Q.                  \tag{3}
\]

Applying (1) yields

\[
 r_j((C\setminus\{j\})\cup Q)\le r_j(C\cup Q),         \tag{4}
\]

which is exactly the checked definition
`QuittingPersistentBaseComplementLeaveSafe r C`.  Since \(|C|\ge2\), the
left terminal coalition is nonempty, so no illicit empty-coalition reward is
used.

The orientation is correct: \(e\trianglerighteq_r j\) says that, in the
presence of predecessor \(e\), **adding receiver \(j\)** weakly improves
\(j\)'s payoff.  This is exactly the comparison between prescribed Quit and
deviating Continue for base player \(j\).

## 3. Checked semantic consumer

I inspected
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseArbitraryCompletionEscape.lean`.
The relevant declaration is

`exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe`.

Under `2 <= C.card` and the predicate proved in Section 2, it:

* selects a mixed Nash point of the finite Boolean game on the complement;
* embeds it in the persistent-base root with every member of \(C\) sure-Quit;
* proves `IsεAsymptoticNash ... 0` for terminal payoff; and
* returns the corresponding `IsUniformEquilibriumPayoff`.

The unrestricted-deviation scope is genuine.  The checked proof passes
through `QuittingPersistentBaseCertificate.isZeroAsymptoticNash`, whose
opponent-survival factor is zero.  Directly, after any one behavioral strategy
is replaced, another member of \(C\) still Quits at date zero.  The deviator's
later actions are never reached, so every complete behavioral deviation
reduces to one date-zero mixture.  Base players are controlled pointwise by
(4), and free players by the finite induced Nash equilibrium.

No correlation, public randomization, stationary-deviation restriction, or
best-response-attainment assumption is introduced.

## 4. Cycle and DAG corollaries

For a simple cycle

\[
 e_0\trianglerighteq_r e_1\trianglerighteq_r\cdots
 \trianglerighteq_r e_{m-1}\trianglerighteq_r e_0,
 \qquad m\ge2,
\]

take \(C\) to be its vertex set.  Each vertex has the preceding vertex as a
distinct robust predecessor, so the main theorem applies.  Any nonsimple
closed directed walk contains a simple directed subcycle, so simplicity loses
nothing.

The contrapositive is valid: if the game has no uniform-equilibrium payoff,
its full robust-join graph has no directed cycle and hence is a finite DAG.
The topological-ordering statement and the existence of a vertex with no
incoming robust edge in every nonempty induced subgraph are standard finite
DAG consequences.

The predecessor-base statement is useful even though a finite base with an
incoming robust edge at every vertex necessarily contains a robust cycle: it
also constructs an equilibrium with the supplied larger sure-quitting base,
whereas the cycle corollary may use only a subbase.

## 5. Strict reversal on a positive selected cycle

Suppose a game has no uniform-equilibrium payoff and a supplied simple cycle
of a selector \(f\), with

\[
 r_{f(e)}(\{e,f(e)\})-r_{f(e)}(\{e\})\ge\gamma>0       \tag{5}
\]

on every selected edge.  If every cycle edge were robust in the **weak**
sense (1), the cycle theorem would give a uniform-equilibrium payoff.  Hence
some edge is not robust.  Negating the universally quantified weak inequality
gives a background \(T\) with the strict opposite inequality

\[
 r_j(T\cup\{e,j\})-r_j(T\cup\{e\})<0.                \tag{6}
\]

Equation (5) excludes \(T=\varnothing\).  This proves the claimed strict
nonempty-background reversal.  It also explains why the result improves the
older `<= 0` screen: strictness comes from using the weak robust relation as
the consumed positive branch.

This argument is valid for any finite player type once such a positive
selected cycle is supplied.  Fin4 is where the repository currently supplies
the selector unconditionally on the no-uniform-payoff branch.

## 6. Unconditional Fin4 no-reversal corollary

I checked the source chain used in Section 6 of the note:

* `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
  in `FullSupportProjectiveQBarResidual.lean`; and
* `FinFourQuantitativeFullSupportHardResidual.
  exists_fixedPointFree_terminalGap_collisionMap`
  in `PunishmentNormalAtomicCollisionHandoff.lean`.

Given a canonical finite coordinate bound, the first theorem supplies a hard
residual from failure of every uniform-equilibrium payoff.  The second gives a
fixed-point-free map \(f:\operatorname{Fin}4\to\operatorname{Fin}4\) whose
empty-background increments are at least the positive terminal gap.

Every fixed-point-free map on `Fin 4` has a simple cycle of length two, three,
or four.  Under condition (6.1) of the note, every positive collision-map edge
is robust; hence that cycle invokes the main theorem, contradicting the
assumed absence of a uniform payoff.  The claimed Fin4 existence class is
therefore unconditional and correct.

The phrase `no strict background reversal` should continue to mean the exact
table predicate (6.1): every strictly positive singleton join edge remains
weakly nonnegative on **all** backgrounds.  It does not mean merely that one
preselected edge has no reversal.

## 7. Falsification and boundary tests

### Weak equality

I attempted to falsify the theorem with zero increments.  The zero reward
table makes every distinct pair robust with equality.  The construction is
still exact: base players are indifferent and every induced completion is
Nash.  Thus `>=` is both sound and stronger than a strict-edge formulation.

### Two-cycle

For \(C=\{e,j\}\), (2) reduces to \(T=Q\).  The two edge inequalities are
exactly the two complement-uniform leave inequalities.  After either player's
behavioral deviation the other still Quits at date zero.  No exceptional
two-player failure occurs.

### Empty free set

For \(C=I\), every player Quits surely.  The finite complement game is empty,
but the checked existential Nash construction still applies.  Directly, a
deviator still faces another sure quitter and (4) rules out improvement.

### Arbitrary outsider coordinates

I allowed arbitrary outsider reward entries, including mixed one-shot games
with no pure equilibrium.  The proof uses only existence of a mixed Nash in
the finite Boolean game.  Sure absorption at date zero makes its inequalities
sufficient against arbitrary behavioral plans.  Therefore no hidden
outsider-payoff sign condition is present.

### Singleton base

The argument genuinely needs two sure quitters.  With one base member, that
member can Continue and expose the tail.  The note's one-player reward `-1`
test correctly shows that sure Quit need not be Nash.  The theorem makes no
singleton-base claim.

### Global robust relation is stronger than leave safety

I checked the note's non-necessity warning.  A three-player base may be safe
whenever its other two members are present even if one proposed predecessor
does not protect the receiver on a background omitting the third base member.
Thus the robust graph criterion is sufficient, not an equivalence with the
existing persistent-base chamber.

No falsifier survived these tests.

## 8. Minor repairs requested

These are not mathematical objections.

1. In (5.1), repair the rendered text
   `f:I\to I,qquad f(e)\ne e` to `f:I\to I,\qquad f(e)\ne e`.
2. In the Lean sketch, use actual quantifier and subset syntax rather than
   `forall background subset_univ_without_enforcer_joiner`; for example,
   quantify `background` and then assume
   `background \subseteq Finset.univ.erase enforcer |>.erase joiner` (or an
   equivalent `Finset` expression).  The current block is clearly pseudocode,
   but the repair will make the handoff less ambiguous.
3. Phrase Section 6's result as a `Fin4 table satisfying the no-strict-
   background-reversal predicate`, rather than as an unqualified
   `unconditional Fin4 theorem`.  The note already gives the correct
   mathematical implication; this is only protection against a headline
   misreading.
4. In the export, mention that the strict selected-cycle reversal itself is
   arbitrary-finite-player mathematics; only its unconditional producer from
   no uniform payoff is currently Fin4-specific.

## 9. Novelty and export verdict

A narrow search found no checked declaration defining the robust join graph,
turning a predecessor cover or directed cycle into
`QuittingPersistentBaseComplementLeaveSafe`, or deriving the strict Fin4
background reversal.  The checked persistent-base mechanism is not new, and
the packet correctly says so.

Unlike the earlier static sign screen, the present result has both required
sides of the export gate:

* an actual finite reward-table adapter (robust predecessor base / directed
  robust cycle); and
* a checked semantic consumer producing exact all-behavior terminal Nash and
  a uniform-equilibrium payoff.

It is therefore a genuine special-case existence theorem and a strict
counterexample-side reduction.  **PASS for export in the maximal form of the
author note after the minor repairs above.**
