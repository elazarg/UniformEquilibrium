# Whole-packet export gate: persistent membership base arbitrary-completion escape

Reviewer: **CODEX_RAMSEY**  
Packet audited, since formalized and promoted: [`PERSISTENT_MEMBERSHIP_BASE_ARBITRARY_COMPLETION_ESCAPE.md`](../formalized/PERSISTENT_MEMBERSHIP_BASE_ARBITRARY_COMPLETION_ESCAPE.md)  
Current head audited: `41051dd`  
Verdict: **REVISE -> PASS after two ministerial header/lifecycle repairs**

## Required edits

No mathematical edit is required.  Before promotion:

1. change `Author: CODEX_EULER` to the packet-template form
   `Authors: CODEX_EULER`; and
2. delete the line `Packet status: assembled for a fresh whole-packet
   export-gate audit.`  `exports/README.md` explicitly makes the containing
   directory the lifecycle status and forbids a repeated status header.

After those edits, promote under the stable filename
`exports/PERSISTENT_MEMBERSHIP_BASE_ARBITRARY_COMPLETION_ESCAPE.md`, without
the `_EXPORT_DRAFT` suffix.  These are literal packet-format repairs; no
mathematical rereview is needed.

## Exact claim and proof audit

### General pointwise leave condition

The stronger statement (1), rather than only the literal membership special
case, is valid.  Let `x` be an induced mixed Nash point on
`F = univ \ G`, and let `q` be `quittingPersistentBaseRoot G F x`.  For a
base player `i`, another member of `G` Quits surely because `2 <= G.card`.
Thus forcing `i` either to Quit or Continue still gives date-zero absorption,
and the zero tail used by the persistent-base adapter is the actual tail.

If `Q subseteq F` is the realized set of free quitters, the two endpoint
payoffs are

\[
r_i(G\cup Q)
\quad\hbox{and}\quad
r_i((G\setminus\{i\})\cup Q).
\]

Consequently

\[
\operatorname{EndpointDifference}_i(q)
=
\mathbb E_x\!\left[
r_i(G\cup Q)-r_i((G\setminus\{i\})\cup Q)
\right]\ge 0.
\]

This has the correct orientation: the endpoint difference is Quit minus
Continue.  The second coalition is always nonempty because another base
member remains.  Hence (1) supplies exactly the `base_leave` field required
by `nonempty_quittingPersistentBaseCertificate_of_inducedNash`; no stronger
pointwise declaration is being attributed to the old compiler.  The packet
correctly identifies this expectation rewrite as part of the new adapter.

Under the membership specialization (2), every integrand is exactly `1`, so
the leave inequality is strict.

### Free players and unrestricted deviations

For a free player `j`, every member of `G` remains a sure date-zero quitter
after an arbitrary unilateral behavioral replacement.  Only `j`'s date-zero
Quit/Continue distribution matters.  Those two pure values are exactly the
utilities in `quittingPersistentBaseUtility`; mixed-Nash optimality bounds
both and therefore every randomized initial action.  Later prescriptions and
private randomization cannot alter a game already absorbed at date zero.

This agrees with
`quittingPersistentBaseRoot_free_purePayoff_le` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`.
Thus the packet does not silently weaken arbitrary behavioral deviations to
stationary deviations.

### Coverage and empty-complement boundary

With `F = univ \ G`, disjointness holds and `G union F = univ`; the compiler's
outside-player join screen is genuinely vacuous.  When `F` is empty, the
zero-player induced binary game has its unique mixed point.
`quittingPersistentBaseNashSet_nonempty` allows an empty player type, since
its per-player nonempty Boolean-action assumption is then vacuous.  The
full-base case is therefore included exactly as claimed.

The restriction `2 <= G.card` is both mathematically operative and the exact
cardinality premise of `QuittingPersistentBaseCertificate`.  The packet
correctly excludes singleton and empty bases.

### Uniform-equilibrium consumer

The source chain is exact:

- `quittingPersistentBaseNashSet_nonempty`,
  `quittingPersistentBaseRoot`, and
  `quittingPersistentBaseRoot_free_purePayoff_le` are in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`;
- `nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
  `exists_uniformPayoff_of_persistentBase_inducedNash_signs` are in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`;
- `QuittingPersistentBaseCertificate.isUniformEquilibriumPayoff` is in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseSemanticDispatch.lean`.

The certificate proves zero total Continue mass and zero fixed-opponents
Continue mass for every coordinate.  Its consumer invokes
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`, so
the conclusion is an unrestricted uniform-equilibrium payoff, not a
stationary-only equilibrium.  The packet accurately describes this compiler
as checked and the arbitrary-completion adapter as the new ordinary
mathematics.

## Six-player specialization

In
`UniformEquilibrium/Quitting/Paths/SixPlayerOnePairMassTargetLock.lean`, the
mathematical labels `1,...,6` are represented by `player1,...,player6`, and
`targetA={player1,player2}`, `targetB={player3,player4}`.  These target pairs
are disjoint.

At the packet's constructed profile both members of `targetA` Quit surely at
date zero.  Every terminal coalition therefore contains `targetA` and cannot
equal the disjoint two-element coalition `targetB`.  Absorption is certain at
date zero, so the Never outcome also has zero mass.  The exact `targetB` atom
is consequently zero, independently of every reward coordinate belonging to
players outside `targetA`.

This exact equilibrium has terminal exploitability zero.  It therefore
falsifies any proposed positive lower bound on `targetB` mass for all
sufficiently accurate terminal approximate Nash profiles in this completion
class.  The claimed change to `questions/INCENTIVE_GADGET.md` is valid and
matches that question's explicit acceptance of a negative result ruling out
a precisely defined universal gadget architecture.

## `exports/README.md` gate

1. **Exact statement — PASS.**  Finiteness, reward domain, base cardinality,
   complement, pointwise inequalities, strategy class, and conclusion are
   quantified.  `2 <= |G|` also implies the ambient player set is nonempty.
2. **Complete proof — PASS.**  Nash existence, free and base deviations,
   coverage, and the uniform-payoff consumer are all discharged.  The
   pointwise-to-expected endpoint step above is valid and leaves no missing
   mathematical lemma.
3. **Probability and agency — PASS.**  The packet specifies independent
   date-zero actions, behavioral deviations, stopping at the first nonempty
   quitter set, the Never payoff, and why arbitrary later behavior is
   irrelevant.
4. **Adapter and consumer — PASS.**  The arbitrary reward table satisfying
   (1) is actual data; finite-game Nash produces the root; the checked
   persistent-base certificate produces unrestricted uniform equilibrium;
   and the six-player adapter removes the named completion architecture.
5. **Boundary tests — PASS.**  Mixed free equilibria, empty complement,
   arbitrary outsider signs/magnitudes, Continue-forever base deviations,
   and the excluded singleton/empty-base boundaries are treated correctly.
6. **Source and novelty audit — PASS.**  All paths and declaration names are
   current at the audited head.  A narrow search found the general compiler
   and related large-base screens, but no packaged complement/membership
   arbitrary-completion corollary.  The packet does not claim a new compiler.
7. **Independent review — PASS.**  The packet links two substantive
   independent falsification reviews, by CODEX_MINER and CODEX_RAMSEY, both
   without unresolved objection.  This satisfies the enhanced review
   requirement for the unrestricted strategy-class conclusion.
8. **Lean handoff — PASS.**  It gives the narrow theorem shape, exact existing
   dependencies, the expectation rewrite to prove, complement identities,
   and a separate six-player specialization without assuming the desired
   result as a field.

## Novelty and nonclaim check

The packet is appropriately narrow.  It proves a new actual-data corollary of
an existing all-behavior compiler and eliminates the persistent-membership
arbitrary-outsider completion family.  It does not claim to solve the full
gadget question, the finite-quitting conjecture, singleton bases, or
architectures that alter a base coordinate.  I found no checked-status,
formalization-status, or novelty overclaim in the mathematical sections.

## Final disposition

**REVISE -> PASS** upon the two header/lifecycle edits above and promotion
under the stable filename.  No proof, source, scope, boundary, or Lean-handoff
repair is required, and the packet should not be returned for a second
mathematical gate after those literal edits.
