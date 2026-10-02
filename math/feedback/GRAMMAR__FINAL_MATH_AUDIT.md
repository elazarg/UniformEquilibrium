# Final mathematical audit of `meta/GRAMMAR.md`

Reviewer: `FINAL_MATH_AUDIT`

## Verdict

**PASS: final whole-document mathematical signoff.** I found no unresolved
mathematical objection to the repaired `ClosedSelect`, `Decode`,
`TraceRank(K)`, coherent-diagonal, or downstream terminal-to-uniform
arguments under the document's standing certificate conventions.

The final edit explicitly imposes the standard all-Never payoff
`r_i(empty) = 0`. This resolves the sole downstream scope objection from the
initial audit and aligns the stopping-law terminal payoff with the checked
`quittingGame reward` consumer used in Section 9.1.

This is an ordinary-mathematics audit, not a Lean formalization of the
grammar.

## Claim checked

The repaired core claims that:

1. a selected operation is trace-safe only when a closed witness domain, an
   actual output compiler, a fixed-program modulus, and a typed legal-edge
   theorem are all supplied;
2. a summably approximated decoder preserves actuality and closed ancestry,
   including for triangular outer families only when fixed inner columns also
   converge;
3. a bounded ranked construction is trace-safe only when complete tagged
   terminal and successor relations are closed and every visible selected
   child and output is itself trace-safe; and
4. one common restriction-compatible tight sequence of executions then has a
   single witness subsequence and a compatible family of limiting finite
   executions sharing one reconstructed root controller.

Those four claims are valid as stated in Sections 2--8, with the minor
literalizations listed below.

## 1. `ClosedSelect` and `FiniteCase`

The earlier legality gap is closed. If `(s_m,w_m)` lies in the closed domain
and converges to `(s,w)`, ambient closedness gives `(s,w) in R`, the modulus
gives

$$
G(s_m,w_m)\longrightarrow G(s,w),
$$

and theorem (5a) gives the named legal-edge conclusion at the limiting point.
No closedness assumption on `Legal_a` is needed. The closed ancestry relation
is additional provenance data; in Lemma 1 its conclusion already follows
from (8) once `(s,w) in R` is known.

The repaired finite-case clause is also sufficient. A constant-tag
subsequence, compactness of the full branch-witness bundle, and ambient
closedness of the complete branch relation retain branch legality at a
boundary. Allowing branch overlap is correct and is necessary for closed
boundary coverage.

## 2. Selected roots and minimizers

The exact-root relation is closed under the stated intended reading that all
root conditions are non-strict polynomial inequalities with the continuous
cap vector as parameter. The prefix compiler estimate then gives a valid
`ClosedSelect` instance.

Closed graph alone is correctly not used to preserve moving optimality.
Comparison transport supplies a convergent competitor for every limiting
feasible point, which proves the argmax and approximate-argmin limit claims.
The recorded compact error coordinate and the explicit limit
`epsilon_m -> epsilon` give exactly `epsilon`-minimality; exact limiting
minimality is claimed only for `epsilon = 0`.

## 3. Fixed and triangular `Decode`

The decoder-domain repair is sufficient. Because `W` is closed in the
ambient product `S^p x Z`, rather than merely relatively closed in an open
input domain, a converging outer input and compact witness remain in the
domain. Uniform summability makes every `M_n(xi)` Cauchy in total variation,
the probability-law space is closed in `ell^1(K)`, and the displayed bound

$$
d(D(\xi),D(\xi'))
\le 2C_N+\omega_N(d_W(\xi,\xi'))
$$

proves continuity by first choosing `N` and then applying the one fixed-column
modulus. Closedness of `Anc` gives the claimed limiting provenance.

The triangular clause now contains the previously missing condition. To make
the sufficiency explicit, put

$$
\delta_N:=\sup_m\sum_{n\ge N}c_{m,n}.
$$

Fixed-column convergence gives limiting columns `M_N`. For `N < L`, passing
to the outer limit in the finite telescoping inequality gives

$$
d(M_N,M_L)\le\delta_N.
$$

Thus `M_N` is Cauchy and has a limit `D`. If `D_m` is the decoded output in
outer row `m`, then

$$
d(D_m,D)
\le
\delta_N+d(M_{m,N},M_N)+\delta_N.
$$

First choose `N` with `delta_N` small and then send `m` to infinity. Hence
uniform tail control plus the stated convergence of every fixed certified
column identifies the outer decoded limit. Uniform tails alone would not do
so, and the note no longer claims otherwise.

Hypothesis 7 of Theorem 7 should be read as invoking the full `Decode`
certificate, including the fixed-column condition following (40). Repeating
that phrase in hypothesis 7 would make the theorem surface more literal, but
the condition is already part of the constructor defined in Section 4.

## 4. Pointwise and trace-visible rank

Theorem 4 is a correct dependent induction on the natural rank. The terminal
consumer closes the left branch; the child outcome and recorded backward map
close the right branch. Strict descent bounds the number of nonterminal
transitions by the initial rank. Corollary 5 is valid for the
dispatch-selected successor relation.

The Section 6 example correctly shows that these pointwise data do not imply
trace closure. Complete replacement makes every selected child actual, but
the child map jumps at `delta_infinity`.

The strengthened `TraceRank(K)` clauses exclude exactly that counterexample.
For a convergent sequence of rank-`k` executions:

1. pass to a subsequence with constant terminal/successor tag and, in a
   successor branch, constant child rank;
2. extract the complete compact branch-witness bundle;
3. use the selected child's `TraceEdge` certificate to obtain convergence to
   an actual child;
4. only then pass the parent, tag, witness, rank, and child tuple through the
   complete closed tagged relation; and
5. recurse at the strictly lower child rank.

Terminal trace outputs and trace-visible backward compilers are covered by
clause 7. Finite rank gives finite recursion depth. This proves Theorem 6.

The prose proof currently mentions closedness before it mentions convergence
of the selected child. The hypotheses support the correct order above, so
this is a proof-presentation issue rather than a counterexample.

## 5. Theorem 7

The common-execution hypothesis is strong enough for the claimed one-root
conclusion. Coordinate convergence plus eventual finite-tail tightness
reconstructs every initial and exogenous law in total variation. The union of
the finite diagrams has only countably many persistent occurrence
coordinates, so successive compact/finite extraction followed by a diagonal
subsequence makes every witness converge and every finite tag stabilize.

For each fixed finite `P_k`, topological induction then applies the elementary
tight-fusion estimates, Lemmas 1--2, the full decoder theorem, closed finite
cases, and Theorem 6. Every limiting port is actual and every named edge is
legal. Since the approximating coordinates on a shared occurrence are
literal restrictions of the same execution `E_m`, their limits agree under
restriction, which proves (56). The root law was reconstructed once, before
the finite edge inductions, so the family uses one controller rather than one
controller chosen independently for each `k`.

No uniform rank bound over all future diagrams is needed: each fixed `P_k` is
finite and each of its visible rank occurrences has its own finite bound.

## 6. Nonblocking notation and presentation defects

1. `R` denotes both the global reward bound and the closed relation in the
   `ClosedSelect` definition. Renaming the latter would remove a genuine
   local ambiguity, especially because the reward bound reappears in (39).
2. `Root(mu,x)` is described but not displayed or tied to a named exact
   definition. The closure argument is valid for the intended non-strict
   inequalities, but a self-contained schema should state them.
3. The Section 6 counterexample should explicitly take all `Outcome` types to
   be singleton and record the unique backward map. Those data plainly exist,
   but the sentence claiming that all fields of (44) are present currently
   leaves them implicit.
4. The extraction list in Theorem 7 omits the compact branch-witness bundles
   of `TraceRank` and the internal fixed-column witnesses of triangular
   decoders. The standing convention and hypotheses include them, but listing
   them would match the proof literally.
5. Hypothesis 8 says tags stabilize "along the extracted subsequence" before
   the proof has extracted it. Tag stabilization is a conclusion of the
   countable finite-tag diagonal extraction, not an independent hypothesis.
6. The base grammar (2) omits `TraceRank`, while (3) calls it a derived
   trace-visible operation and (52) admits it. Calling (2) the *base* trace
   grammar and `TraceRank` its derived bounded constructor would remove this
   harmless syntactic hesitation.

The display delimiters and `begin`/`end` environments are balanced, equation
tags are unique, and the named local files and Lean source file exist. I found
no malformed mathematical display or duplicate equation label.

## 7. Resolved all-Never scope check

The opening now assumes

$$
r_i(\varnothing)=0
\qquad(i\in I).
$$

This is exactly the nonabsorption payoff of the project's standard
`quittingGame reward`: the live state pays zero, and nonabsorption contributes
zero to `quittingTerminalPayoff`. Consequently the law-level payoff `U`, its
complete unilateral cap `B`, and the exact terminal Nash conclusion in
Section 9.1 refer to the same payoff semantics as
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
The cited theorem therefore applies after the canonical stopping-law-to-
behavior compiler. Section 11 item 7 has the same corrected scope.

## Sources inspected

- `meta/GRAMMAR.md`, especially Sections 2--8 and Theorem 7;
- `meta/EXECUTABLE_COMPACT_STATE.md`, especially the stopping-law semantics,
  fixed-program estimates, and tight-fusion reconstruction theorem;
- the previous adapter, scope, and trace-rank audits under `feedback/` as
  falsification records, followed by an independent re-derivation of the
  repaired arguments;
- `quittingGame` in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Game.lean`;
- `quittingTerminalPayoff` in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Asymptotic.lean`;
  and
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

## Final signoff

No mathematical repair remains. The six items in Section 6 are optional
notation or proof-presentation literalizations and do not block use of the
canonical note as a sound sufficient ordinary-mathematics schema.
