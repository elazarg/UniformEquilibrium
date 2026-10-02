# Fin4 two-anchor universal Nash-selection regression

**Owner:** `CODEX_MINER`  
**Status:** independently reviewed **PASS** as ordinary mathematics; internal
architecture regression/no export.  Review:
[`CODEX_RAMSEY`](../feedback/CODEX_MINER__FIN4_TWO_ANCHOR_UNIVERSAL_NASH_SELECTION_REGRESSION__BY_CODEX_RAMSEY.md).
Not Lean-checked as a packaged result.  
**Question:** can the supplied affine-Nash-segment hypothesis in
[`CODEX_EULER__TWO_ANCHOR_NASH_SEGMENT_MINIMAX_ESCAPE.md`](CODEX_EULER__TWO_ANCHOR_NASH_SEGMENT_MINIMAX_ESCAPE.md)
be removed by selecting, in every actual two-anchor induced binary game, a
Nash point at which both sure-Quit anchors have nonnegative leave margins?

## 1. Result

No.  The proposed universal selection is false even for a four-player integer
table, a genuine two-target architecture, and an induced free game having a
**unique** Nash point.  Thus neither connectedness nor a topological selection
of the Nash correspondence can repair it.  In the same table an exact
singleton-anchor profile is nevertheless terminal Nash against unrestricted
behavioral deviations and yields a uniform-equilibrium payoff.  Consequently
the example is not a counterexample to the finite-quitting conjecture: it
strictly rules out the named universal two-anchor selection architecture and
exhibits the alternative exact escape that it misses.

Let the four players be

\[
                    I=\{a,b,f,g\},
\]

and let the two disjoint target pairs be `A={a,b}` and `B={f,g}`.  For every
nonempty quitter coalition `S`, define the complete reward table by

\[
\begin{aligned}
r_a(S)&=
 \begin{cases}1&S=\{a\},\\2&S=\{b\},\\0&\text{otherwise},\end{cases}\\
r_b(S)&=
 \begin{cases}1&S=\{b\},\\2&S=\{a\},\\0&\text{otherwise},\end{cases}\\
r_f(S)&=\begin{cases}-1&f\in S,\\0&f\notin S,\end{cases}\qquad
r_g(S)=\begin{cases}-1&g\in S,\\0&g\notin S.\end{cases}
                                                        \tag{1.1}
\end{aligned}
\]

For reference, all fifteen rows, in coordinate order `(a,b,f,g)`, are:

| quitter coalition | reward vector |
|---|---:|
| `{a}` | `(1,2,0,0)` |
| `{b}` | `(2,1,0,0)` |
| `{f}` | `(0,0,-1,0)` |
| `{g}` | `(0,0,0,-1)` |
| `{a,b}` | `(0,0,0,0)` |
| `{a,f}` | `(0,0,-1,0)` |
| `{a,g}` | `(0,0,0,-1)` |
| `{b,f}` | `(0,0,-1,0)` |
| `{b,g}` | `(0,0,0,-1)` |
| `{f,g}` | `(0,0,-1,-1)` |
| `{a,b,f}` | `(0,0,-1,0)` |
| `{a,b,g}` | `(0,0,0,-1)` |
| `{a,f,g}` | `(0,0,-1,-1)` |
| `{b,f,g}` | `(0,0,-1,-1)` |
| `{a,b,f,g}` | `(0,0,-1,-1)` |

### Theorem 1.1 (unique pair-base Nash, both margins negative)

In the binary game induced by the persistent sure-Quit base `A={a,b}` and
the full free complement `B={f,g}`, the unique mixed Nash point is

\[
                         f=C,\qquad g=C.                 \tag{1.2}
\]

At its ambient persistent-base root, both base leave margins are `-2`:

\[
                         L_a=L_b=-2.                     \tag{1.3}
\]

Hence there is no induced Nash point at which both base leave margins are
nonnegative.  In fact neither is nonnegative.

### Theorem 1.2 (exact alternative escape)

Let `sigma^a` be the stationary profile in which `a` Quits surely and
`b,f,g` Continue surely.  It is exact terminal Nash against every behavioral
unilateral deviation.  Its terminal payoff is

\[
                    r(\{a\})=(1,2,0,0),                 \tag{1.4}
\]

and therefore is a uniform-equilibrium payoff.  The symmetric profile with
only `b` Quitting surely is another exact escape.  Under `sigma^a`, both the
exact terminal-coalition atom on `B={f,g}` and the strict-first-`B` event have
probability zero.

## 2. Proof of the failed pair-base selection

Fix both `a` and `b` to Quit at date zero and consider the induced binary game
on `{f,g}`.  If `f` Continues, its payoff is zero, regardless of `g`'s action:
the realized coalition omits `f`.  If `f` Quits, its payoff is `-1`, regardless
of `g`'s action, because the realized coalition contains `f`.  Thus Continue
strictly dominates Quit for `f`.  The identical argument applies to `g`.
This proves uniqueness of (1.2), including against mixed induced strategies.

At that root the realized coalition is `{a,b}` and both anchors receive zero.
If `a` alone changes from Quit to Continue, `b` still Quits surely and `a`
receives `r_a({b})=2`.  Therefore

\[
 L_a=Q_a-C_a=r_a(\{a,b\})-r_a(\{b\})=0-2=-2.           \tag{2.1}
\]

Likewise

\[
 L_b=r_b(\{a,b\})-r_b(\{a\})=0-2=-2.                  \tag{2.2}
\]

This is exactly the sign used by
`exists_uniformPayoff_of_persistentBase_inducedNash_signs`: the free set is
the entire complement, so the outsider premise is vacuous, but both required
base-leave signs fail.  Since the induced Nash set is a singleton, there is no
Nash-component, path-selection, minimax, or equilibrium-correspondence choice
left to make.

## 3. The earlier pointwise singleton-anchor screens also fail

This table is not rejected by the pair-base selector merely because the
earlier pointwise singleton-anchor theorem already certifies the same pair
point.

With `a` as sure-Quit anchor, `f` and `g` again strictly Continue.  Given that,
`b` receives `2` by Continuing into `{a}` and `0` by Quitting into `{a,b}`.
Thus the unique induced complement Nash point has `b,f,g` all Continue.  The
anchor's Quit value there is

\[
                         Q_a=r_a(\{a\})=1,              \tag{3.1}
\]

whereas the excluded-face row `{b}` gives `r_a({b})=2`.  Hence
`QuittingSingleAnchorInducedDominance` fails its pointwise
excluded-coalition bound.
The symmetric statement holds for anchor `b`: its unique complement Nash is
all Continue, its Quit value is one, and the excluded row `{a}` pays it two.

For anchor `f`, every terminal coalition induced by its sure Quit contains
`f`, so its Quit value is `-1`; the required nonnegative-value condition
fails.  The same holds for `g`.  Therefore every one of the four candidate
anchors fails the earlier **pointwise** sufficient screen.  This does not say
that every singleton-anchor equilibrium mechanism fails: Section 4 gives an
exact singleton-anchor equilibrium whose anchor safety comes from the actual
continuation law rather than pointwise dominance over the entire excluded
face.

## 4. Unrestricted-deviation proof of the exact escape

Under `sigma^a`, date-zero absorption occurs surely at `{a}`, yielding (1.4).

* If `a` changes to an arbitrary behavioral strategy, every other player is
  all-Continue.  The deviated profile is literally

  ```text
  Function.update (quittingAlwaysContinueProfile reward) a deviation.
  ```

  The checked inequality
  `quittingTerminalPayoff_update_quittingAlwaysContinue_le_max` bounds `a`'s
  terminal payoff by

  \[
                    \max(0,r_a(\{a\}))=1,               \tag{4.1}
  \]

  equal to its prescribed payoff.  This covers random, delayed,
  history-dependent, and Never deviations.

* If `b` changes to any behavioral strategy, `a` still Quits surely at date
  zero.  Continuing at date zero gives `b` payoff `r_b({a})=2`; Quitting gives
  the collision payoff `r_b({a,b})=0`.  Later behavior is never reached.

* If `f` changes, `a` again forces date-zero absorption.  Continuing gives
  zero; Quitting gives `-1` because the coalition contains `f`.  The same
  argument applies to `g`.

Thus no arbitrary unilateral behavioral replacement improves any coordinate,
so `sigma^a` is exact terminal Nash.  The checked compiler
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` turns its own
terminal payoff into a uniform-equilibrium payoff.

The outcome is deterministically `{a}`.  Since `B={f,g}` is disjoint from it,
the exact terminal atom on `B` is zero.  Since `a` Quits at the first date and
no member of `B` does, the strict-first-`B` event is also zero.

## 5. Exact architectural conclusion

The supplied-segment hypothesis in the two-anchor minimax theorem cannot be
removed by the proposed universal statement

```text
every actual two-anchor induced game has some Nash point
at which all base leave margins are nonnegative.
```

The failure persists with an integer table, two disjoint target pairs, and a
unique induced Nash point.  It therefore strictly rules out the topological
selection/minimax architecture, not merely an attempted selection across a
disconnected Nash set.

The correct dispatch in this example is a different exact all-behavior
escape.  Accordingly this regression does **not** prove a positive terminal
gap, a counterexample to uniform equilibrium, or a universal replacement
theorem.  A complete post-single-anchor gadget architecture would have to
combine the pair-base search with a test of actual-law anchor safety (or some
other exact escape); pointwise excluded-face dominance and universal pair-base
Nash selection are both incomplete screens.

## 6. Source and novelty audit

Checked declarations inspected:

* `quittingPersistentBaseNashSet`, `quittingPersistentBaseRoot`, and
  `quittingPersistentBaseRoot_free_purePayoff_le` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`;
* `nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
  `exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`;
* `QuittingSingleAnchorInducedDominance` and the arbitrary-completion singleton
  compiler in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingleAnchorArbitraryCompletionEscape.lean`;
* `quittingTerminalPayoff_update_quittingAlwaysContinue_le_max` in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/SimpleBranches.lean`; and
* `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

A narrow search found related but nonduplicating boundaries:

* the supplied affine-segment verifier in
  [`CODEX_EULER__TWO_ANCHOR_NASH_SEGMENT_MINIMAX_ESCAPE.md`](CODEX_EULER__TWO_ANCHOR_NASH_SEGMENT_MINIMAX_ESCAPE.md);
* the reviewed alternating pair-base Nash-mass selector, whose pure arm can
  have a unique induced Nash with leave debt, in
  [`CODEX_MINER__FIN4_ALTERNATING_PAIRBASE_NASH_MASS_SELECTOR.md`](CODEX_MINER__FIN4_ALTERNATING_PAIRBASE_NASH_MASS_SELECTOR.md); and
* the pointwise singleton-anchor producer in
  [`CODEX_EULER__SINGLE_ANCHOR_INDUCED_NASH_UNIVERSAL_ESCAPE.md`](CODEX_EULER__SINGLE_ANCHOR_INDUCED_NASH_UNIVERSAL_ESCAPE.md).

None of these gives this complete four-player regression: unique pair-base
Nash with both margins `-2`, failure of all four pointwise singleton screens,
and a separately verified exact unrestricted singleton-law escape.

## 7. Requested check

Please independently check the fifteen-row table, uniqueness of the pair-base
induced Nash, both `-2` leave margins, the four singleton-screen failures, and
the unrestricted behavioral proof for `sigma^a`.  The key scope question is
whether this is correctly advertised as a no-go for universal two-anchor Nash
selection plus an exact alternative escape, rather than as a positive-gap
game or a complete new producer.
