# Review of `COMP.md`: finite monodromy, Fin4 geometry, tail limits, and rank regeneration

Reviewer: Codex Monodromy

## Verdict

- **Section 1 — PASS, with a stronger finite-player statement.** The same-row
  endpoint construction really does regenerate a literal behavioral source
  after the preliminary canonicalization. The gain constant is
  \(\lambda D_*/(2|I|)\) for an arbitrary finite player set, hence
  \(\lambda D_*/8\) on `Fin 4`.
- **Section 2 — PASS and strengthen.** Every simple Fin4 cycle in the
  rank-at-least-two cube has a common member or visits complementary pairs.
  A minimal directed endpoint cycle has length in \(\{2,4,6,8\}\), so the
  displayed upper bound \(K\le 11\) can be improved to \(K\le 8\).
- **Section 3 — REPAIR.** The compactness argument produces an exact
  positively absorbing Nash--Bellman datum in the closure of literal reached
  rows. It does **not** by itself produce an actual tail profile, a
  punishment-floor edge, or an executable admissible-path edge. The word
  `executable` must be removed unless those additional facts are supplied.
- **Section 6 — PASS, and it is already checked in greater generality.** Any
  carrier point on the same positive minimum fiber, with positive-debt support
  contained in the old support and one old active coordinate vanished,
  re-extracts a complete tangent family at that exact point with strict support
  inclusion. Full-replacement provenance is not needed for this abstract
  re-extraction theorem.

No counterexample was found to the corrected statements below. Sections 1--2
are suitable for a focused export packet as a strict reduction of the
same-row causal-regeneration obligation. Section 3 should be included only in
the repaired closure-level form. Section 6 is source correspondence, not new
mathematics to export.

## Exact source audit

The narrow source set inspected was:

- `quittingFinFourLiveWeightedCollisionTransfer_tailEscape_or_endpointGain`,
  `quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain`, and
  `quittingStageCoalitionMass_le_stagePureEndpointRouted` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiveWeightedCollisionTransfer.lean`;
- `quittingStagePureEndpointBehaviorDeviation` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauLocalizedOtherDefect.lean`;
- `quittingProfileLiveRoot_stagePureEndpoint_self` and
  `quittingLiveMass_stagePureEndpoint_eq` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCausalCollisionAtomicOrientation.lean`;
- `exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`;
- `exists_reextractedFrontier_of_minimumFiberEndpoint` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/NormalizedCurvaturePaidRow.lean`; and
- the maintained boundary descriptions `FINITE-SUPPORT-RANK-EXIT` and the
  collision/tangent entries in `docs/FRONTIER.md` and `docs/TOOLKIT.md`.

The live-weighted one-row transfer and no-loss routing are already checked.
The finite same-row closure and Fin4 graph classification are the new claims
reviewed here.

## 1. Maximal same-row monodromy statement

Let \(I\) be a nonempty finite player set of cardinality \(n\). Let \(r\) be a
quitting reward table and let \(z_*\) be a global minimizer of terminal
semantic total debt, with

\[
D_*:=D(z_*)>0.
\]

Fix an actual behavioral profile \(\sigma\), a reached date \(t\), and a
nonsingleton terminal coalition \(S\) whose unconditional stage mass is at
least \(\lambda>0\). Let

\[
z^+=\operatorname{Sem}(\sigma^{t+1}),\qquad
E=D(z^+)-D_*.
\]

Assume

\[
E<\frac{\lambda D_*}{2}. \tag{1}
\]

At date \(t\), an endpoint update replaces one player's action by a pure best
endpoint against the literal tail payoff, keeps the pre-\(t\) root word, and
resumes the same post-\(t\) live-root word. Route the marked coalition by the
same coordinate update.

Then, after at most \(n\) preliminary endpoint updates and at most

\[
N=2^n-n-1
\]

further strict endpoint updates, one obtains either:

1. an actual profile with a routed singleton stage atom of mass at least
   \(\lambda\); or
2. a literal closed word of actual behavioral profiles

   \[
   \rho_0\to\rho_1\to\cdots\to\rho_K=\rho_0,
   \qquad 2\le K\le N,
   \]

   all using the same date, prehistory, and post-date live-root word, such that
   every arrow changes one pure root coordinate to its best endpoint and has
   actual terminal-payoff gain

   \[
   g_k\ge \frac{\lambda D_*}{2n}>0. \tag{2}
   \]

For every mover \(p_k\), the mover's unrestricted terminal debt obeys the
exact identity

\[
d_{p_k}(\rho_{k+1})=d_{p_k}(\rho_k)-g_k. \tag{3}
\]

Consequently every coordinate has the exact circulation account

\[
\sum_{k:p_k=i}g_k
=
\sum_{k:p_k\ne i}
\bigl(d_i(\rho_{k+1})-d_i(\rho_k)\bigr). \tag{4}
\]

For `Fin 4`, (2) is \(g_k\ge\lambda D_*/8\), and every minimal closed segment
has \(K\le8\).

### Proof

The checked live-weighted alternative at a profile \(\rho\) carrying marked
stage mass \(m\ge\lambda\) is

\[
L E\ge\frac{mD_*}{2}
\quad\text{or}\quad
\exists p,\quad g_p\ge\frac{mD_*}{2n}, \tag{5}
\]

where \(0\le L\le1\) is the live mass at the row. Same-stage endpoint updates
do not change the pre-row live mass or the shifted live-root word, and the
routed marked mass does not decrease. Thus the same \(E\) occurs at every
later same-row state. By (1),

\[
LE\le E<\frac{\lambda D_*}{2}
\le\frac{mD_*}{2},
\]

so the first arm of (5) is impossible whenever the current routed coalition
is nonsingleton. This proves (2). Equation (3) is the checked fixed-opponent
own-strategy debt identity.

Update every coordinate once to a pure best endpoint. Routing through a pure
coordinate update cannot decrease the marked mass; while the marked coalition
is nonsingleton it cannot become empty. Stop if it becomes a singleton.

After these preliminary updates, every player's entire replacement strategy
is the canonical time-only strategy determined by:

- the original live-root coordinate before \(t\);
- its chosen pure bit at \(t\); and
- the original live-root coordinate after \(t\).

Later same-row updates preserve this form. Hence the resulting behavioral
profile is determined literally, not just semantically, by its pure root at
date \(t\). This is the point needed to justify source regeneration: equality
of two later pure roots implies equality of the complete canonical behavior
profiles.

There are exactly \(N=2^n-n-1\) nonsingleton pure quitting coalitions. Every
strict positive-gain update flips one bit: if the selected endpoint agreed
with the current pure bit, its gain would be zero. Thus, unless a singleton is
reached, \(N+1\) visited pure nonsingleton roots contain a repeated root. The
segment between the first repeated occurrences is the claimed literal closed
word. Telescoping each debt coordinate and using (3) proves (4).

This also identifies a safe Lean implementation strategy: define the
post-preliminary finite family of canonical one-row profiles indexed by pure
roots. Do not try to prove that arbitrary behavior profiles are determined by
their live roots; that stronger claim is false off the canonical family and is
unnecessary here.

## 2. Fin4 cycle geometry

Let \(Q_0,\ldots,Q_{K-1}\) be a minimal directed cycle of pure subsets of
`Fin 4`, each of cardinality at least two, with consecutive subsets differing
in one element. Then

\[
\bigcap_kQ_k\ne\varnothing
\quad\text{or}\quad
\exists k,\ell,quad
|Q_k|=|Q_\ell|=2,quad Q_\ell=Q_k^c. \tag{6}
\]

Moreover \(K\in\{2,4,6,8\}\).

### Proof

The graph is bipartite by cardinality parity. Its odd side consists of the
four triples, so a simple cycle of length at least four has length at most
eight and is even. A directed two-cycle is the remaining possibility and its
two adjacent sets already have nonempty intersection.

Assume no complementary pair vertices occur. The pair vertices visited by
the cycle form an intersecting family of edges of \(K_4\). Such a family is
contained in either a star or a triangle.

If it is contained in a star with center \(c\), every triple appearing in the
cycle contains an adjacent pair and therefore contains \(c\); the full set
also contains \(c\). Thus every cycle vertex contains \(c\).

If the pair family is not contained in a star, it contains the three edges of
a triangle, say \(12,13,23\). Each such pair has only two adjacent triples:
the common triple \(123\) and the triple obtained by adding the fourth
element. Since a pair vertex in a simple cycle needs two distinct neighbors,
the common triple \(123\) would have to be a cycle neighbor of all three pair
vertices, giving it cycle degree three. This is impossible. Therefore the
triangle case cannot occur, proving (6).

As an explicit boundary test, the common-host six-cycle

\[
01,012,02,023,03,013
\]

has common member \(0\). The eight-cycle

\[
01,013,0123,123,23,023,02,012
\]

has empty total intersection and visits the complementary pairs \(01\) and
\(23\). A complete enumeration of the induced cube graph found 37 undirected
simple cycles and no counterexample to (6).

## 3. Correct tail-limit statement

The valid compactness statement is the following.

Let \((\sigma_n,t_n)\) be actual reached rows, after passage to a subsequence
with one fixed marked coalition \(S\), and assume its stage mass is at least
\(\lambda>0\). Let \(L_n\) be row live mass and let

\[
R_n=\sum_i\operatorname{Defect}_i(x_n;u_n^+)
\]

be total pure-endpoint root defect against the literal shifted-tail payoff.
Then either:

1. for one fixed player along a subsequence, the legal same-row endpoint
   deviation has actual payoff gain bounded below by a fixed positive
   constant; or
2. after a further subsequence,

   \[
   x_n\to x,\qquad u_n^+\to u^+,qquad u_n^0\to u^0,
   \]

   and

   \[
   u^0=F_x(u^+),\qquad x\in\operatorname{Nash}(u^+),
   \qquad \mu_x(S)\ge\lambda,
   \]

   so \(\operatorname{Abs}(x)\ge\lambda\).

Indeed, stage mass at least \(\lambda\) implies both \(L_n\ge\lambda\) and
root coalition mass at least \(\lambda\). If
\(\limsup L_nR_n>0\), finite averaging selects the first branch. Otherwise
\(R_n\to0\); compactness and continuity give the second branch.

The rows in the second arm remain actual and have defect tending to zero. The
limit is exact algebraic Nash--Bellman data and is approximated by those
literal reached rows. However \(u^+\) is only known to be a limit of actual
tail payoff vectors. No theorem cited in `COMP.md` realizes it by one
behavioral tail, places both endpoints above punishment floors, or attaches
it to an admissible path. Therefore the maximal honest conclusion is:

> an exact positively absorbing Nash--Bellman anchor in the closure of actual
> reached-row data.

It is not yet an exact executable or punishment-floor edge.

## 4. Rank regeneration

Section 6 follows directly from the checked theorem
`QuittingPositiveMinimumDebtTangentFamily.exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished`.
Its strongest useful formulation is:

Let `frontier` be a positive-minimum tangent family and let \(z'\) be **any**
terminal-semantic carrier point satisfying

\[
D(z')=D(\texttt{frontier.base}),
\]

\[
d_i(z')>0\Longrightarrow
i\in\operatorname{supp}_+d(\texttt{frontier.base}),
\]

and

\[
\exists i\in\operatorname{supp}_+d(\texttt{frontier.base}),quad d_i(z')=0.
\]

Then there is a complete new tangent family `next` with

\[
\texttt{next.base}=z',
\qquad
\operatorname{supp}_+d(\texttt{next.base})
\subsetneq
\operatorname{supp}_+d(\texttt{frontier.base}).
\]

The full-replacement specialization, including strict cardinal decrease, is
`exists_reextractedFrontier_of_minimumFiberEndpoint`. Thus source
regeneration is not an additional obligation after the fiber, no-entry, and
vanishing-coordinate conditions have actually been proved.

## Export recommendation

Export only the following package after one additional independent review:

1. the arbitrary-finite-player same-row singleton-or-literal-cycle theorem;
2. its exact coordinatewise debt-circulation identity;
3. the Fin4 common-host/complementary-pair classification and \(K\le8\)
   corollary; and
4. optionally, the repaired closure-level tail compactness alternative.

The packet changes the named local boundary in
`TerminalSemanticLiveWeightedCollisionTransfer.lean`: that checked file
explicitly stops before causal regeneration, whereas the new theorem proves
literal finite source regeneration and reduces the Fin4 residual to two
finite geometries. It must not claim a uniform payoff, an admissible edge, or
chronological realization.

The proposed Lean handoff should build a finite canonical profile family
rather than quotient arbitrary strategies by live-root equality. Likely new
declarations are:

```lean
exists_sameStage_singletonDrop_or_closedUniformGainCycle
finFour_sameStageClosedEndpointGainCycle_commonHost_or_complementaryPair
finFour_sameStageClosedEndpointGainCycle_length_le_eight
```

The first should be stated for arbitrary finite `ι`, with gain
`lambda * Dmin / (2 * Fintype.card ι)`, and specialized to `Fin 4` only for
the graph classification.

