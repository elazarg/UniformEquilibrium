# Checked-consumer interface for the endogenous soft-cycle escape

Author: `CODEX_SPINOZA`

## Status

This is a source/interface audit, not a new existence claim.  The producer
being audited is frozen in
`CODEX_SPINOZA__ENDOGENOUS_SOFT_CYCLIC_BLOCK_ESCAPE.md` at SHA256
`9c2680d1a4216f28ce74b20dddaa684991edcfdd43477fc781d097f39de224b0`.
The two conclusions below identify the exact field missing from a checked
consumer in each of its boundary branches.

The singleton branch supplies every algebraic field of the checked
singleton-tight face except **global carrier minimality**.  The
vanishing-hazard branch is already a literal returned product block with
zero Bellman error; its exact missing field is **aggregate endpoint regret
little-o of total hazard**, not merely a better rowwise error label.

## Sources inspected

- `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`:
  `quittingTerminalSemanticCarrier`,
  `quittingTerminalSemanticCarrier_isCompact`.
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSingletonTightMinimumFaceIteration.lean`:
  `QuittingSingletonTightMinimumFace`,
  `quittingSoloRateControlled_of_q_le_debt_div_debt_add_gainMax`, and
  `QuittingTerminalExploitabilityWitness.singletonTight_atomicHandoff_or_playerDeletion`.
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourSoloWallDispatch.lean`:
  `exists_pos_exactRootOpponentAbsorptionFloor_of_no_soloExactRoot`,
  `exists_strictCarrierDebtDescent_of_opponentAbsorptionFloor`, and the
  unique-debtor solo-prefix identities.
- `UniformEquilibrium/Quitting/Stationary/ReturnedBlockTangentObstruction.lean`:
  `QuittingReturnedProductBlock`, `endpointRegret`, and
  `hasHomogeneousSimplexSolution_of_vanishing_returnedBlocks`.
- `UniformEquilibrium/Diagnostics/Quitting/FourPlayerReturnedBlockGap.lean`:
  `hasAmbientReturnedBlockRelativeErrorGap_of_fourPlayer_counterexample`.
- `UniformEquilibrium/Quitting/Classification/SingletonPacketRefusal.lean`:
  the exact refusal-amplification identities for a normalized singleton
  packet.

## 1. Singleton-dominant branch

Pass to a subsequence of the producer's singleton-dominant arm on which the
complete terminal semantic pairs converge.  Write the limit as

\[
 (v,W)\in\overline{\{\text{literal terminal semantic pairs}\}}.
\]

The frozen theorem gives, for its fixed debtor/owner \(i\),

\[
 v=r(\{i\}),\qquad W_j-v_j=0\quad(j\ne i),
 \qquad W_i-v_i\ge \Gamma>0.                 \tag{1}
\]

Compactness and closedness put \((v,W)\) in
`quittingTerminalSemanticCarrier`.  Thus (1) supplies:

- carrier membership;
- positive total debt;
- owner singleton tightness \(v_i=r_i(\{i\})\); and
- zero outsider debt.

These are exactly the non-minimal fields of
`QuittingSingletonTightMinimumFace`.  Once its `minimum` field is available,
a sufficiently small positive solo rate satisfies
`QuittingSoloRateControlled`; the checked
`singletonTight_atomicHandoff_or_playerDeletion` theorem then gives the
atomic handoff/deletion dispatch.  Equivalently, if there is no solo exact
root, the compact exact-root opponent-absorption floor and strict carrier
debt descent contradict minimality.

What the soft Brouwer selection does **not** show is

\[
 \sum_k(W_k-v_k)
   =\min_{(u,Z)\text{ in the carrier}}\sum_k(Z_k-u_k).  \tag{2}
\]

The global gap only gives a lower bound on every literal profile's maximum
debt.  It does not make an arbitrarily selected soft fixed point, or its
carrier limit, minimize total debt.  The terminal law convergence to
\(\delta_{\{i\}}\) also does not repair (2): the owner cap is precisely the
noncontinuous player-deleted normalization.  Hence the singleton branch is
blocked by **minimum-fibre anchoring**, not by the lack of an outsider-debt
or singleton-tight identity.

## 2. Vanishing-total-hazard branch

For the \(n\)-th soft word, package its cyclic roots and phase values as a
`QuittingReturnedProductBlock` and put

\[
 h_n=\sum_{t,i}x_{n,t,i},
 \qquad E_n=\operatorname{endpointRegret}(B_n).
\]

The Bellman error is exactly zero because the word returns literally.  If
\(\Delta_{t,i}=Q_{t,i}-C_{t,i}\), then the summand in the checked endpoint
regret is

\[
 (1-x_{t,i})\max(0,\Delta_{t,i})
   +x_{t,i}\max(0,-\Delta_{t,i}),              \tag{3}
\]

which is exactly the two-action defect of the prescribed soft mixture.
Consequently

\[
 0\le E_n\le 4H_n\varepsilon_n.                \tag{4}
\]

The checked arbitrary-horizon returned-block theorem would consume this
sequence if

\[
 E_n/h_n\longrightarrow0.                      \tag{5}
\]

The stronger displayed scale
\(H_n\varepsilon_n=o(h_n)\) from the producer note is sufficient for (5),
but is not logically necessary: (5), involving the actual logit regrets in
(3), is the exact missing hypothesis.

Under the contrary Fin4 hypothesis, the checked ambient returned-block gap
instead yields constants \(c,\delta>0\) such that, eventually when
\(0<h_n\le\delta\),

\[
 c h_n\le E_n.                                  \tag{6}
\]

Thus the soft escape does not evade the checked tangent obstruction.  It
lands in its positive relative-regret arm.  Formula (3) shows where the cost
sits, but (6) alone gives neither a source transition nor a terminal
profile.  Any useful refinement must turn this positive normalized cost
into a new global object; relabeling it as a paid row would merely return to
the already open paid-port waist.

## 3. Exact research boundary

The two missing adapters are therefore disjoint:

1. **singleton arm:** prove that some soft singleton semantic limit belongs
   to the global minimum-total-debt fibre (or give a source-preserving
   retraction to such a point);
2. **vanishing-hazard arm:** prove actual aggregate logit regret is
   \(o(h_n)\), or extract from \(E_n\ge c h_n\) an executable global
   certificate stronger than the already checked `R0`/homogeneous
   obstruction.

The next nonlocal question is whether zero-temperature soft fixed points
carry a normalized singleton law whose refusal caps can be computed
uniformly.  If the law has at least two owners, this may turn (6) into a
finite singleton-refusal certificate rather than a local port.  That claim
is not made here.
