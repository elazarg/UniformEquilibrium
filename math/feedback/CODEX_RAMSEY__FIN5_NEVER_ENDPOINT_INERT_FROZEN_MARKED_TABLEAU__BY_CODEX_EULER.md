# Review of the Fin5 Never-endpoint inert frozen tableau

**Reviewer:** CODEX_EULER  
**Date:** 2026-08-25  
**Verdict:** `PASS` at the stated internal structure/no-discharge scope

I independently checked
[`CODEX_RAMSEY__FIN5_NEVER_ENDPOINT_INERT_FROZEN_MARKED_TABLEAU.md`](../notes/CODEX_RAMSEY__FIN5_NEVER_ENDPOINT_INERT_FROZEN_MARKED_TABLEAU.md)
against the current literal two-reset retention, stage-coalition factorization,
cap-lift, and inert-stall declarations.  The atom transport, frozen finite
prefix tableau, cap/debt consequences, and exact local regression are correct.
I do not recommend a standalone export: the only new lemma is a local
erase-one-clock atom comparison, and its composition deliberately produces no
compiler, contradiction, or maintained-rank decrease.

## 1. Erase-`w` chronological atom inequality

Fix a terminal coalition `T` and put `Tminus=T.erase w`, assuming `Tminus` is
nonempty.  Apply
`quittingStageCoalitionMass_update_eq_opponentFactor_mul` with the same
baseline profile `x_2`, once to its prescribed `w` strategy and once to
Never.  The opponent factors for terminal sets `T` and `Tminus` are equal:
after the factorization removes coordinate `w`, every other player's forced
membership action is identical in the two coalitions.  Call the common factor
`F>=0`.

For `x_2`, the remaining factor is either `w`'s stop mass at the displayed
date, if `w in T`, or its survival through the next date, if `w notin T`.
In either case it lies in `[0,1]`.  For the literal-Never update and terminal
set `Tminus`, the remaining survival factor is one.  Thus the compared masses
are `F*h` and `F`, proving

\[
 m_{x_2[w\leftarrow Never]}(t,T\setminus\{w\})
 \ge m_{x_2}(t,T).
\]

This is a stage-by-stage statement and includes arbitrarily late finite
dates.  It does not compare total terminal masses by an informal stopping
argument; the checked chronological factorization supplies the exact result.

Composing it with the checked non-excess two-reset field

\[
 \tfrac14 m_{x_0}(t,T)\le m_{x_2}(t,T)
\]

gives the claimed quarter retention.  If `w` is outside the selected role
set and `T` contains one of those selected roles, `T.erase w` is indeed
nonempty.  The note correctly does not apply this to an abstract cluster atom
which has not been identified with a literal `x_0` atom.

## 2. Exact inert finite-prefix propagation

From `source.totalAbsorption=0`, the checked theorem
`root_eq_allContinue_of_totalAbsorption_eq_zero` makes every selected root
literally all Continue.  The checked theorem
`semanticPair_eq_of_totalAbsorption_eq_zero` then fixes the whole semantic
pair at every finite cap prefix, so every coordinate debt, the debt sum, and
positive-debt support are fixed.

The literal-Never marginal of `w` remains Never after finitely many
all-Continue prefixes.  For chronological atoms,
`quittingStageCoalitionMass_rootThenContinuation_succ` multiplies the shifted
continuation atom by the root Continue mass.  That mass is one here, so
iteration gives exact equality after shifting the date by the prefix depth;
the quarter lower bound therefore propagates exactly as written.

The paid row is also frozen with the precise stated fields.  The
`InertStall.losslessShiftedPaidRow` output preserves live mass, reached gain,
orientation, delay, and total full-gap inequality, while adding the prefix
depth to both pure times and the first-disagreement date.  This is a literal
finite-prefix statement; it does not create an infinite behavior profile at
the semantic port.

## 3. Cap and debt consequences

The cap-prefix root is exact Nash against the tail envelope `B(y)`.  At the
all-Continue root, the pure-Quit endpoint of player `i` is `r_i({i})` and the
Continue endpoint is `B_i(y)`, so

\[
 r_i(\{i\})\le B_i(y).
\]

No analogous inequality with `U_i(y)` follows.  Separately, applying the
terminal exploitability gap at the actual literal profile `y` and bounding
the profitable deviation by the unrestricted cap yields some `j` with

\[
 B_j(y)-U_j(y)\ge\Gamma.
\]

Hence total debt is at least `Gamma`, and inert semantic equality transports
this fact to every prefix.  These arguments use unrestricted behavioral caps,
not stationary best responses.

## 4. Toggle and source qualifications

The two asserted sign failures are real.

- If `w in T`, deletion transports the mass to `T.erase w`, but an arbitrary
  nonsingleton reward table need not transport a strict reward comparison
  between those distinct coalitions.
- If `w notin T`, the same coalition and static reward comparison remain, but
  a unilateral action change also affects every other live coalition at that
  date.  One favorable atom need not dominate their aggregate contribution.

The paid row already averages its whole first-disagreement cylinder, but its
observer, direction, and date are not aligned with the retained four-role
atom.  The note therefore correctly distinguishes two same-source marks from
a common source-matched event.

The cluster-limit qualification is also necessary.  Literal quarter
retention starts from atoms of `x_0`; it does not identify the atom returned
by `exists_counterexampleLocalFourRoleCertificate` on a separate
`SameLawResetCluster` with any such literal atom.

## 5. Regression check

In the displayed five-player table, `a` Quits surely at date one and the other
players Never.  Thus the prescribed terminal atom is `{a}` with mass one.
The exact unrestricted caps are

\[
 B_a=0,\quad B_b=2,\quad B_c=B_d=B_w=0.
\]

Player `a` obtains zero by Never; player `b` obtains two by tying `a` at date
one; every other player obtains zero by Never.  Pure-time disintegration
shows that no behavioral strategy exceeds these values.

For `a,c,d,w`, Quit gives `-1` against every opponent row and Continue gives
zero.  They strictly Continue.  With them continuing, player `b` compares
solo `1` with continuation cap `2` and also strictly Continues.  Hence all
Continue is the unique exact product root at the cap annotation.  Yet the
profile has debt two for `b`, atom mass one, a literal Never spare, and the
strict static join change `0 -> 2`.  This verifies local compatibility.  The
note correctly excludes the global terminal-gap, positive-minimum, and
two-reset provenance hypotheses from this regression.

## 6. Source and export assessment

The relevant checked declarations are:

- `exists_twoMatchedHalfResets_or_firstExcessCharge` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawGlobalRetention.lean`;
- `quittingStageCoalitionMass_update_eq_opponentFactor_mul` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawMixture.lean`;
- `quittingStageCoalitionMass_rootThenContinuation_succ` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`;
- `QuittingPaidCapLiftedSource.nonempty_summablePort` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`;
  and
- `root_eq_allContinue_of_totalAbsorption_eq_zero`,
  `semanticPair_eq_of_totalAbsorption_eq_zero`, and `InertStall` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`.

The erase-`w` atom domination lemma appears new in the narrow search and is a
reasonable reusable formalization target.  The remainder is an exact
composition with the already checked inert tableau.  It does not close a
named chamber, produce a semantic compiler, or strictly decrease a maintained
rank; rather, it proves that no new rank is generated.  Under
`exports/README.md`, the packet should remain internal unless a named question
explicitly accepts this frozen-interface boundary as an answer.  The
mathematics itself passes without repair.
