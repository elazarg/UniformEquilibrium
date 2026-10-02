# Quantile outer certificates generate a robust semantic prefix barrier

Author: `CODEX_MINER`

Status: **proved ordinary mathematics; independent review requested.**  This
is a narrow source-aware corollary of the exported quantile-clock hierarchy
and checked prefix-metric/barrier declarations.  It is intended as a
formalization addendum, not as a second hierarchy export and not as a new
Fin4 residual contraction.

## 1. Statement

Let `I` be a nonempty finite player set, `n=|I|`, and let `r` be a normalized
rational quitting reward table.  Retain the notation of
[`ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md`](../formalized/ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md):

\[
 K_M=2nM+1,
 \qquad \delta_M={n(n-1)\over M},
 \qquad R_M=\bigcap_{m\le M}N_m.                     \tag{1.1}
\]

Write `Prefix(q,z)` for the checked terminal-semantic prefix of pair `z` by
one product root `q`.  Let `Eval(w,z)` be its finite iteration over a word of
product roots, with the empty word evaluating to `z`.  Define the semantic
prefix hull

\[
 \mathcal H_M={\operatorname{Eval}(w,z):z\in R_M,
                   \ w\text{ a finite product-root word}\}.            \tag{1.2}
\]

Suppose a finite exact real-algebraic certificate proves

\[
 0<\gamma\le F(z)\qquad\text{for every }z\in R_M,     \tag{1.3}
\]

where `F=max(0,max_i(B_i-U_i))` is semantic exploitability.  Then:

1. the Never boundary belongs to `H_M`;
2. `H_M` is closed under prefixing by **every** product root;
3. every `p in H_M` satisfies

   \[
   \boxed{
   \gamma-2n\delta_M\le
      \sum_i(B_i(p)-U_i(p)).}                         \tag{1.4}
   \]

Consequently, if

\[
 \gamma>2n\delta_M,                                  \tag{1.5}
\]

then `H_M` is the barrier set of a checked
`TerminalSemanticGlobalDebtBarrierCertificate.Certificate` with positive
floor `gamma-2n delta_M`.  The checked theorem
`not_exists_uniformEquilibriumPayoff_of_certificate` therefore rules out a
uniform-equilibrium payoff.

For `I=Fin 4`, `delta_M=12/M`, so the robust inductive floor is

\[
 \boxed{\gamma-{96\over M}}.                          \tag{1.6}
\]

The direct hierarchy certificate already proves the stronger unrestricted
gap `gamma`.  The point of (1.4) is different: it shows that arbitrary finite
semantic prefixing of every outer witness preserves a positive global-debt
barrier once (1.5) holds.

## 2. Proof

### 2.1 Every outer point has an actual current-scale center

Because `R_M subset N_M`, every `z in R_M` has a center

\[
 a\in A_{K_M},\qquad \|z-a\|_\infty\le\delta_M.       \tag{2.1}
\]

The center is an exact finite product stopping law with a separate Never
atom, hence is behaviorally executable.  Its semantic pair belongs to the
terminal-semantic carrier.

### 2.2 Prefix words preserve the same distance

The checked theorem `quittingTerminalSemanticPrefix_within` says that every
fixed product root is nonexpansive for the coordinatewise semantic sup
metric.  Induction over the word `w` in (2.1) gives

\[
 \|\operatorname{Eval}(w,z)-
       \operatorname{Eval}(w,a)\|_\infty\le\delta_M.  \tag{2.2}
\]

The carrier is invariant under each semantic prefix, so
`Eval(w,a)` remains in the carrier.  Since the hierarchy maps the entire
carrier into `R_M`, (1.3) gives

\[
 F(\operatorname{Eval}(w,a))\ge\gamma.               \tag{2.3}
\]

All semantic debts are nonnegative on the carrier.  Hence maximum positive
debt is bounded by total debt and

\[
 \sum_i d_i(\operatorname{Eval}(w,a))\ge\gamma.       \tag{2.4}
\]

### 2.3 Transfer the debt floor to the outer prefix

The checked metric estimate
`abs_semanticDebtSum_sub_le_of_within` applied to (2.2) gives

\[
 \left|D(\operatorname{Eval}(w,z))-
       D(\operatorname{Eval}(w,a))\right|
       \le 2n\delta_M.                                \tag{2.5}
\]

Combining (2.4) and (2.5) proves (1.4).

The Never semantic pair is actual, hence lies in every `R_M`; use the empty
word to put it in `H_M`.  If `p=Eval(w,z)` belongs to `H_M`, prefixing by a
new root `q` gives `Eval(q::w,z)`, again in `H_M`.  Thus the three fields of
the checked barrier certificate are exactly the Never membership, this
prefix closure, and (1.4).  Under (1.5) its floor is positive, so the named
consumer applies.

## 3. Exact scope

This is a **semantic** source-aware hull.  An outer point `z in R_M` need not
be behaviorally realizable, and the theorem does not claim that its prefix
word is an actual behavioral chronology.  Instead, it pairs `z` with its
co-realized actual current-scale center and transports their distance under
the same root word.  This is exactly the level of generality accepted by the
global semantic barrier certificate.

The barrier set `H_M` has an explicit generating description but is not
claimed to have a finite semialgebraic membership test: its root-word length
is unbounded.  The finite proof object remains the RCF certificate (1.3).
Thus this theorem is not a replacement for the hierarchy's direct soundness
argument and should not be advertised as a new finite barrier-search
algorithm.

The prefix orientation is load-bearing.  Nonexpansiveness transports a
center and its approximation **forward** under common prefixes.  It gives no
inverse estimate from a near-minimum head to the shifted tails of an actual
profile; a sure-absorbing prefix can erase arbitrary tail differences.  Hence
this result does not supply the every-suffix near-minimum premise needed by
the max-debt costate theorem and does not consume the causal-atom
tail-excursion arm.

For `n=1`, `delta_M=0`, so the floor loss is zero.  No division by `n-1` or
strict positivity of the compression error is used.

## 4. Novelty and checked correspondence

The following current declarations were inspected:

- `quittingTerminalSemanticPrefix_within`,
  `quittingTerminalSemanticCarrier_mapsTo_tube`,
  `abs_semanticDebtSum_sub_le_of_within`, and
  `semanticDebtSum_ge_floor_of_mem_tube` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPrefixMetric.lean`;
- `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `TerminalSemanticGlobalDebtBarrierCertificate.Certificate`,
  `nonempty_certificate_iff_globalDebtFloor`, and
  `not_exists_uniformEquilibriumPayoff_of_certificate` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticGlobalDebtBarrierCertificate.lean`;
- the definition and center property of `R_M` in the exported hierarchy.

The checked prefix-metric file already proves invariance and debt loss for a
sup-metric tube around any invariant set.  The new content here is the exact
adapter from a quantile outer witness to that tube and the resulting prefix
hull floor, including the Fin4 loss `96/M`.  It is a short composition, not a
new analytic compression theorem.

A narrow search found no declaration or note stating this `R_M` prefix-hull
adapter.  Since the hierarchy itself is not yet Lean-formalized, the natural
handoff is to add this as a corollary after the analytic center theorem,
rather than creating an independent formalization project.

## 5. Requested review

Please check:

1. the inclusion `R_M subset N_M` and use of the current-scale actual center;
2. iteration of the nonexpansive prefix estimate with the correct word
   orientation;
3. carrier nonnegative debt and `F<=total debt`;
4. the factor `2n delta_M`, especially the Fin4 value `96/M`;
5. Never membership and arbitrary-root prefix closure of `H_M`; and
6. the scope distinction between a set-theoretic semantic barrier and a
   finitely semialgebraic barrier certificate.
