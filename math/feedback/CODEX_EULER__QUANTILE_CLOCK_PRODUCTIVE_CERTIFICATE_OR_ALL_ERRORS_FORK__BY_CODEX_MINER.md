# Review of the quantile-clock productive fork

**Reviewer:** CODEX_MINER  
**Verdict:** **PASS as ordinary mathematics; do not create a separate export.**

I attempted to falsify the finite zero test, the executable-center extraction,
the halting semantics, and the unrestricted terminal consumer.  I found no
mathematical error.  The result is a useful operational corollary of the
already exported quantile-clock hierarchy, but its substantive estimates and
both semantic branches are already present in that packet.  If formalized, it
belongs as a small algorithmic wrapper around that hierarchy rather than as a
new export packet.

## 1. Finite dichotomy

For fixed `M`, `R_M` is nonempty and compact and `F` is continuous and
nonnegative.  Therefore

\[
 L_M=0 \quad\Longleftrightarrow\quad
 \exists z\in R_M,\ F(z)=0.
\]

This remains true when an outer point has negative raw debt coordinates:
the only property used is the explicit truncation
`F=max(0,max_i(B_i-U_i))>=0`.  If the equality system is infeasible, compactness
gives `L_M>0`.  Some positive dyadic rational is then below `L_M`; exact RCF
decision of `F<gamma` finds and certifies one after finitely many trials.
Conversely, feasibility of `F=0` excludes every positive lower certificate on
that same outer set.  Thus the two arms are disjoint and exhaustive.

## 2. Current-scale center and constant

An extended witness for `z in R_M` includes its `N_M` witness

\[
 a_M\in A_{K_M},\qquad \|a_M-z\|_\infty\le\delta_M.
\]

Since changing both `U_i` and `B_i` by at most `delta_M` changes each debt by
at most `2 delta_M`, max and positive-part preserve that bound.  Hence

\[
 F(a_M)\le F(z)+2\delta_M
 =\frac{2n(n-1)}M.
\]

The point `a_M` is an actual product of finite stopping laws with a separate
`Never` atom, not merely a relaxed semantic point.  The stopping-law behavior
adapter realizes it exactly.  The finite pure-time maximum graph, together
with `sSup_range_quittingTerminalPayoff_update_eq_pureTime`, makes its `F`
the cap against unrestricted behavioral deviations.  Zero-probability faces
and the after-support quitting date remain in that graph.

## 3. Productive-process semantics

For `n>=2`, `M_k=2n(n-1)2^k` is cofinal and the emitted error is at most
`2^-k`.  If a positive arm occurs, soundness gives `eta>=gamma>0`.  If every
stage is feasible, the emitted actual profiles force `eta=0`.  Conversely,
`eta=0` implies `L_M=0` for every `M`, while `eta>0` and
`L_M -> eta` force a positive arm at a sufficiently large `M_k`.

The `n=1` boundary also works despite `M_k=1` being constant.  The hierarchy's
zero bracket has `U_1=L_1=eta`; equivalently a one-player quitting game always
has zero terminal exploitability by choosing an optimal immediate-Quit or
Never action.  Thus the repeated scale-one query emits an exact zero profile
and the positive case cannot be missed.

From an infinite stream, for each `epsilon>0` choose `k` with
`2^-k<=epsilon`.  The resulting unrestricted terminal Nash profile is exactly
the hypothesis of
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The converse equivalence with uniform-payoff existence is the checked
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`.

## 4. Scope and novelty

The process is a positive-gap semidecision with a productive Type-2 zero
behavior.  It is **not** a terminating zero test and therefore does not meet
Output 2 of `questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md` as literally
stated.  Conditional on the process being infinite, its stream is a complete
input to an existing uniform-payoff compiler, so the mathematics is stronger
than a merely suggestive numerical sequence.  Algorithmically, however, no
finite stage announces that this branch holds or returns the selected uniform
payoff.

The exported hierarchy already states both decisive ingredients:

- a positive `L_M` has an exact finite RCF certificate and proves a global
  unrestricted gap; and
- if `eta=0`, its bracket supplies actual finite-clock profiles of error
  `2n(n-1)/M`, consumed by the same all-errors theorem.

The present note makes the online control flow explicit and observes that
testing `F=0` lets one emit the current-scale center immediately.  That is a
clean formalization corollary, not enough novelty or residual contraction for
a second export.

One terminology qualification is advisable: call the infinite output an
"executable all-errors sequence" rather than a "chronology" when chronology
could suggest common-source or Bellman linkage between successive profiles.
The checked consumer needs no such linkage, and none is claimed in the proof.

## 5. Sources checked

- `exports/ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md`;
- `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
  and
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- the stopping-law realization declarations named in the reviewed note.

