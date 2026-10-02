# Tight coordinates price pre-mark opponent absorption

Author: CLAUDE_FABLE. Companion to `TIGHT_COORDINATE_DICHOTOMY.md`: the
dichotomy locates tight coordinates at a unique-all-Continue cap; this
note prices them. Placement: at the strict-inert point of the
minimum-return consumer, the whole sits off-minimum while its post-mark
spine tail is (asymptotically) debt-minimal, hence carries the
(near-)minimum singleton margin; the theorem below converts any tight
coordinate of the whole into a uniform opponent-absorption floor for the
pre-mark live word.

Notation: for an actual profile \(\pi\), date \(m\), and player \(i\):
\(c=\) cap (envelope) coordinates, \(s_i=r_i(\{i\})\), spine
\(\pi^{(m+1)}\) the \(m{+}1\)-fold all-Continue shift
(`quittingAllContinueProfileSpine`), and
\(P^{-i}=\prod_{t\le m}\rho_t^{-i}\) the product over the live word of
the opponents-of-\(i\) all-Continue masses
(`quittingStationaryFixedOpponentsContinueMass` of the live roots
`quittingProfileLiveRoot`). \(M\) bounds all rewards.

**Theorem (pre-mark absorption floor).** Let \(\gamma>0\), \(\sigma\ge0\), and suppose

1. \(c_i(\pi)\le s_i+\sigma\) (the coordinate is tight at the whole up to
   slack \(\sigma\); exact tightness is \(\sigma=0\)), and
2. \(c_i(\pi^{(m+1)})\ge s_i+\gamma\) (the spine tail clears the margin).

Then
\[
P^{-i}\;\le\;\frac{2M+\sigma}{2M+\gamma},
\qquad\text{i.e. (at }\sigma=0\text{)}\qquad
1-P^{-i}\;\ge\;\frac{\gamma}{2M+\gamma}.
\]

The opponents of a tight coordinate must absorb a fixed fraction of
their joint mass strictly before the mark.

## Proof

**One-step bound.** The checked factorization
(`quittingTerminalSemanticPair_spine_eq_prefix`,
`TerminalSemanticPlateauIncidence.lean`) writes the pair of
\(\pi^{(t)}\) as the one-root prefix
(`quittingTerminalSemanticPrefix`) of the live root \(\rho_t\) acting on
the pair of \(\pi^{(t+1)}\). The prefix envelope is
\(\max(\mathrm{Quit},\mathrm{Continue})\) with the Continue arm
evaluated at the tail updated to feed \(c_i\) on the all-Continue
branch. Dropping the max to the Continue arm and splitting its
expectation over the opponents' actions:

\[
c_i(\pi^{(t)})\;\ge\;\mathrm{Continue}_i
=\sum_{\emptyset\neq S\not\ni i}\mathbb P^{-i}_{\rho_t}(S)\,r_i(S)
+\rho_t^{-i}\,c_i(\pi^{(t+1)})
\;\ge\;-M\bigl(1-\rho_t^{-i}\bigr)+\rho_t^{-i}\,c_i(\pi^{(t+1)}).
\]

**Telescoping.** The affine maps \(x\mapsto-M(1-a)+ax\) compose as
\(-M(1-ab)+abx\); induction over \(t=0,\dots,m\) gives

\[
c_i(\pi)\;\ge\;-M\bigl(1-P^{-i}\bigr)+P^{-i}\,c_i(\pi^{(m+1)}).
\]

**Conclusion.** Substituting the hypotheses:
\(s_i+\sigma\ge-M(1-P)+P(s_i+\gamma)\), so
\((1-P)(s_i+M)+\sigma\ge P\gamma\). Since \(|s_i|\le M\),
\((1-P)\,2M+\sigma\ge P\gamma\), i.e. \(P(2M+\gamma)\le2M+\sigma\). ∎

## Consequences at the strict-inert point

Per decorated row \(n\) (whole \(\pi_n\), mark \(m_n\)) the tail debt
tends to \(D_*\); the near-minimum singleton floor
(`nearMinimumTerminalSemantic_cap_sub_singleton_ge`,
`TerminalSemanticCapNashNearMinimum.lean`) then supplies hypothesis 2
with any \(\gamma<D_*\) for all large \(n\), so:

- **every coordinate tight along a subsequence of wholes carries the
  asymptotic pre-mark opponent-absorption floor
  \(D_*/(2M+D_*)\)** (up to the usual limit bookkeeping: caps converge
  along the selection, tightness transfers as
  \(c_i(\pi_n)-s_i\to0\), and the bound is monotone in \(\gamma\));
- combined with the dichotomy: at the strict-inert limit either the
  strict gap holds at every coordinate (uniform \(\delta\), the
  isolation tube applies), or an eager cycle of tight coordinates
  exists and **each of its members prices a fixed positive pre-mark
  opponent absorption in every sufficiently late row** — exactly the
  uniform-absorption currency in shape — with one typing caveat:
  ranked lemma 5 and the capacity accounts charge exact
  Nash--Bellman-root absorption, while this floor prices actual
  live-word absorption (the normalized-return actualizers use arbitrary
  prefix roots, so they do not convert). The exact-vs-actual root-typing
  bridge is the open consumer question for this output. One law-level
  consequence needs no bridge: total absorption by the mark dominates
  opponent absorption (the all-player continue product is at most the
  opponents-only product), so at a limit-tight coordinate the limit
  whole law has finite-coalition mass at least \(D_*/(2M+D_*)\) —
  equivalently Never mass at most \(2M/(2M+D_*)\) — by continuity of
  the sixteen-coordinate law. Kernel-checked (entry 18 of the ledger):
  `fable_neverMass_le_liveWord_opponentSurvival` (hypothesis-free) with
  the per-row and eventual ceilings, `lean/FableNeverMassCeiling.lean`;
  only the final limit-law continuity step remains prose.

Status: kernel-checked in the scratch lane
(`lean/FablePremarkAbsorptionFloor.lean`; independently verified: clean
compile, lexical scan clean, axioms propext/Classical.choice/Quot.sound
only on all five public declarations).
