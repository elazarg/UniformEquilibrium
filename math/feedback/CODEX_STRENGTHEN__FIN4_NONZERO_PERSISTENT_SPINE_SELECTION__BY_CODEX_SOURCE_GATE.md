# Source/formalization gate: Fin4 finite-capacity boundary packets

**Reviewer:** CODEX_SOURCE_GATE

**Reviewed:** `notes/CODEX_STRENGTHEN__FIN4_NONZERO_PERSISTENT_SPINE_SELECTION.md`,
`gpt/NONZERO_PERSIST_ATTEMPT_1.md`, the maintained Fin4 spine question, named
Lean sources, and the closest exports.

## Verdict

There is no fatal mathematical issue in the plateau moat or the positive
unbounded-capacity compiler. I independently confirm the compact extraction
and both summable-residual adapters, including their unrestricted-behavior
endpoint. They merit one new export/formalization packet after the mandatory
repairs below.

| Group | Verdict | Disposition |
|---|---|---|
| Uniform plateau moat and summable-restart no-go | **PASS** | Small Fin4 source formalization; not a producer and probably not a standalone export. |
| Diagonal provenance/all-summable separation | **PASS with wording repair** | Optional wrapper; substantive all-summable terminal theory is already checked. |
| Near-return extraction plus summable-residual compiler | **PASS** | Priority standalone export/formalization packet. |
| Finite-capacity trace potential | **PASS but generically duplicate** | Reuse checked `ChargedRelation` theory; formalize only an actual source-history adapter. |
| Dyadic/compact-comb regressions | Dyadic **PASS**; comb **FAIL as written but repairable** | Optional regression module. |
| Fin4 drifting-hazard regression | **PASS with topology repair** | Separate Fin4 regression. |

The new positive theorem strictly reduces the maintained question; it does not
solve it. Under hypothetical Fin4 nonexistence, every supplied compact family
of same-table chronological exact blocks must have finite hazard capacity. No
inspected source currently produces an unbounded such family; the checked
maximal-prefix ray is summable.

## 1. Plateau moat

`exists_finFour_strictMinimumPlateau_openDebtHomotopyTube_of_no_uniformPayoff`
supplies an open payoff tube \(O\) containing the compact payoff-valued
debt-homotopy segment \(P\), with unique all-Continue exact root on \(O\).
Compactness gives one \(\rho>0\) such that

\[
a\in P,\ z\notin O\quad\Longrightarrow\quad
\rho\le\lVert z-a\rVert_\infty.
\]

A finite ball subcover proves this; compactness of \(O^c\) is unnecessary.
`anchoredPath_terminal_not_mem_of_positiveAbsorption` and the exact
root-Nash/endpoint-Nash adapter give the claimed separation for any charged
exact anchored block.

Therefore a summable stream of literal endpoint-return seams from terminal
tails to anchors in \(P\) contains only finitely many charged blocks. Other
finite blocks have zero row absorption, hence zero marginal Quit
probabilities. No fixed marginal can be persistent.

This blocks useful output 3 only for metric returns to the actual plateau
segment. It does not block a different executable source-reprojection error.

If rewards and displayed values have absolute coordinate bound \(M>0\), then

\[
\rho\le\lVert v_0-v_n\rVert_\infty
\le2M\sum_{t<n}\alpha_t
\le2M\sum_{t<n}\sum_iq_{t,i}.
\]

Thus departure costs at least \(\rho/(2M)\). Calling this a capacity *drop*
requires an extension-compatible history relation so charge telescopes
against future capacity; otherwise it is only a one-time bound.

## 2. Diagonal provenance

All marginal streams summable implies every opponent clock summable by
`summable_quittingOpponentClockCharge_iff`. Coordinate convergence follows
from
`IsCanonicalExactQuittingNashBellmanSpine.exists_tendsto_value_of_summableClock`;
finiteness gives norm/product convergence. If carrier points \(s_n\) approach
\((v_n,v_n)\), carrier closedness puts \((v_\infty,v_\infty)\) in the carrier.
`isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier` then
gives the unrestricted-behavior uniform payoff.

If \(v_\infty\in O\),
`exactNashBellmanPath_eq_anchor_of_tendsto_unique_allContinue` forces all
values to equal \(v_\infty\) and all roots to be all-Continue from time zero.
Replace ambiguous “nonconstant spine” by “not the literal constant
all-Continue spine at its limit”; then
\(\operatorname{dist}(v_\infty,P)\ge\rho\).

Do not re-export broader all-summable conclusions:
`QuittingSummableExactValueTail` in `SummableExactTailTerminalGap.lean`
already checks literal suffix payoff, unrestricted best-response envelope,
and nonpositive-solo conclusions. Punishment-floor orbit and maximal-prefix
summability are also checked.

## 3. Compact extraction and constants

For Fin4, \(h(x)=\sum_iq_i(x)\le4\). Cover compact \(K\) by \(N\ge1\) sets
of diameter below \(\delta\), take a block with charge \(>5N\), and mark first
crossings of \(5j\). Overshoot is strictly below four. Two marks \(a<b\) in
one cell delimit a subblock with

\[
C_{t_b}-C_{t_a}>5(b-a)-4\ge1
\]

and endpoints less than \(\delta\) apart. Thus Fin4's constant \(5\) is exact.

For arbitrary finite \(I\), use spacing \(|I|+1\), total charge
\(>(|I|+1)N\), and \(h\le|I|\), or specialize to `Fin 4`. The current final
draft reportedly already makes this repair.

Compactness and a fast subsequence give endpoints \(a_k,b_k\to z\) with

\[
\sum_kd_k<\eta/3,\qquad d_k=\lVert b_k-a_{k+1}\rVert_\infty.
\]

Flattening changes only each block's last successor tail. Tail Lipschitzness
gives Bellman residual \(\beta=d_k\); comparing prescribed and deviated roots
at both tails gives Nash residual \(\nu=2d_k\). Internal rows stay exact.
Every block contributes hazard at least one, so total hazard diverges and
finiteness selects one fixed nonsummable marginal.

The output is a **summable-residual spine**, not an exact spine. The final
draft reportedly uses this label. Trace provenance is unused after the
same-table chronological exact blocks are supplied; it matters upstream.

## 4. Independent unrestricted-behavior compiler check

I independently confirm the ledger in
`feedback/NONZERO_PERSIST_ATTEMPT_1__BY_CODEX_ADVERSARY.md`.

For two persistent labels, set

\[
S_t=(w_{t+1},w_{t+1}),\qquad
C_t=\operatorname{Prefix}_{y_t}(S_t).
\]

Diagonal-prefix debt has \(0\le D_{t,i}\le\nu_t\). The
`QuittingBoundedSeamChain` seam is from \(S_t\) to \(C_{t+1}\), so

\[
\operatorname{prescribedSeam}_t\le\beta_{t+1},\qquad
\operatorname{capSeam}_t\le\beta_{t+1}+\nu_{t+1},
\]

and total seam is at most \(2\beta_{t+1}+\nu_{t+1}\). After shifting by \(T\),
initial debt is at most \(\nu_T\). Summability makes every requested budget
small. The checked two-label survival theorem and
`quittingGame_exists_uniformEquilibriumPayoff_of_summableSeams_all_errors`
cover complete behavioral replacements and uniform horizons.

For a unique persistent owner \(p\), let \(U_t\) be the literal root-suffix
terminal value. Vanishing joint survival, exact recursion for \(U\), and
Bellman residual give

\[
\lVert w_t-U_t\rVert_\infty\le\sum_{s\ge t}\beta_s.
\]

Checked bounded-Bellman concentration applies because the opponent clock is
summable. At increasing dates \(t_n\) with \(q_p(y_{t_n})>0\), use in
`isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits`:

\[
\begin{aligned}
E^{\rm hazard}_n&=\operatorname{OpponentClockCharge}(p,t_n),\\
E^{\rm target}_n&=\sum_{s\ge t_n}\beta_s+
 2M\operatorname{OpponentClockTail}(p,t_n),\\
E^{\rm quit}_n&=\beta_{t_n}+\nu_{t_n}.
\end{aligned}
\]

The outsider inequality is exactly

\[
\operatorname{FixedOpponentsQuitValue}_i(y_{t_n})
\le w_{t_n}(i)+\beta_{t_n}+\nu_{t_n}\quad(i\ne p).
\]

All errors vanish. Normality is needed only for \(p\); the Fin4 hard residual
supplies it. No attainment assumption and no stationary-deviation weakening
is hidden. This satisfies the independent second-review gate for the
ordinary positive compiler.

## 5. Capacity overlap and source topology

Generic capacity is checked in `MathUE/ChargedPathBudget.lean`:
`ChargedRelation`, `Path`, `HasFiniteBudget`, real `value`,
`value_tgt_add_charge_le_value_src` without attainment,
`value_isBoundedPotential`,
`hasFiniteBudget_iff_exists_boundedPotential`,
`IsPotential.chargeSum_le`, and totalized `budgetEN`.

Do not duplicate this theory. A concrete source adapter should make the actual
trace/history the `ChargedRelation.State`. Payoff state is valid only when
future legality is Markov in payoff. The port needs extension compatibility,
not merely subblock closure. Before `HasFiniteBudget`, use `budgetEN`.

`ChargedPathBudgetCounterexamples.lean` and
`ChargedPathSelectionCounterexamples.lean` already cover towers,
discontinuous potentials, unbounded finite charge without a divergent path,
delays, greedy traps, and incompatible horizon maximizers.

## 6. Regressions

The dyadic chain is correct:
\(\Phi(2^{-n})=\sum_{j=n}^\infty2^{-(j+1)}=2^{-n}\). It gives infinite strict
real descent and finite-path nonattainment. Its infinite branch does realize
the geometric total, consistently with the note.

The comb is incomplete because \(r\) is undefined. Set, e.g., \(r=(2,0)\);
specify row edges only for \(0\le k<n\); add zero loops at row endpoints and
the whole limit segment; and define the edge set as a subtype of \(S\times S\)
with subspace topology. Then

\[
\Phi(1/n,0)=1-1/n\to1,\quad\Phi(0,0)=0,\quad\Phi(r)=1,
\]

with closed compact edge graph, continuous charge, failure of USC, and no
finite or infinite maximizer from \(r\). This exact strengthening may merit
one optional checked regression, not a broad export.

The Fin4 drifting-hazard chain is also correct:
\(H_N=1+(N-1)/\sqrt N\to\infty\), while every fixed early coordinate tends to
the all-Continue exact phantom at \(e_0\), whose literal profile has
exploitability one.

Its inputs are variable-length chains, not one product-space sequence. State
**triangular prefix convergence**: each fixed prefix is eventually defined
and converges in its finite-product topology. Do not silently pad the chains;
the zero boundary cannot be padded by exact all-Continue rows. For easier
Lean arithmetic use length \(m^2\) and early hazard \(1/m\). This solved game
is a separate compactification regression, not a hard-residual source.

## Final split

1. **Priority export/formalization:** *Unbounded finite exact Nash--Bellman
   block capacity produces a summable-residual persistent spine*. Include
   spacing \(|I|+1\), \(\beta=d,\nu=2d\), both ledgers, the Fin4
   finite-capacity corollary, and the honest missing producer.
2. **Small source formalization:** *The Fin4 strict-minimum plateau has a
   uniform exact-prefix restart moat*.
3. **Separate regression:** *Unbounded hazards in finite exact Fin4 chains
   can vanish under triangular prefix compactification*.
4. **Optional regression:** repaired dyadic/comb examples, reusing
   `MathUE.ChargedPathBudget`.

Mandatory corrections remaining: define comb \(r\) and edge topology; use
triangular topology for drifting chains; reuse `ChargedPathBudget`; put
source-restricted capacity on extension-compatible histories; and use the
literal-all-Continue wording in the separation corollary. The generic
\(|I|+1\) constant and summable-residual label are already repaired in the
reported final positive draft.

