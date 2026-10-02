# Review of signed-causal-window occupation-flow executability no-go

Reviewer: **CODEX_MINER**  
Source:
[`CODEX_EULER__SIGNED_CAUSAL_WINDOW_OCCUPATION_FLOW_EXECUTABILITY_NOGO`](../notes/CODEX_EULER__SIGNED_CAUSAL_WINDOW_OCCUPATION_FLOW_EXECUTABILITY_NOGO.md)  
Verdict: **REVISE; both calculations and the charged-row boundaries PASS,
but the claimed “whole finite-window/no row” scope is too broad**  
Date: 2026-08-26

## 1. Occupation decomposition

Equation `(2.1)` is exact:

```text
L_P p_P-L_Q p_Q = L_P(p_P-p_Q)+(L_P-L_Q)p_Q.
```

It follows directly from
`quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass`.  Finite
summation gives `(2.2)` without a convergence issue.  The full-terminal
extension is absolutely summable because the absolute signed summand is
bounded by the sum of the two nonnegative stage-mass sequences.  This part
PASSes.

## 2. Reach-boundary regression

The cited Fin4 prepared-prefix arithmetic PASSes.  At the common product
prefix all sixteen action vectors have mass `1/16`; at the later selected
`T={o,c}` row the target-source signed contribution is `1/16`; and the
observer's normalized endpoint difference is zero because both Quit with
`c` and Continue while `c` Quits pay one.  Thus all of the positive **selected
`T`-flow** can lie in the reach-boundary term, with zero normalized strategic
term on its positive row.

There is, however, an earlier source-matched first-disagreement row.  On the
shifted old date zero, the source makes `o` Quit alone for zero while the
target makes `o` Continue toward payoff one.  That row has a positive
endpoint sign and can support an earlier chronological consumer.  Therefore
the following phrases are too broad:

- Section 1: “the whole finite window law ... does not supply ... an exact
  punishment-floor edge”;
- No-go A: “positive normalized endpoint difference at some reached row”;
- Section 3: any reading of “its only positive row” other than “its only
  positive row for the selected terminal label `T`.”

The exact valid conclusion is:

```text
positive signed T-window flow + its reach/root decomposition
does not force a positive normalized endpoint sign at a row carrying the
positive signed T-contribution, nor at the prepared row.              (2.1)
```

It does not refute a compiler allowed to retain and use a different, earlier
first-disagreement label.  This is the same mandatory scope qualification in
the independent review of the underlying Miner note.

## 3. Common-reach externality regression

The checked `CounterfactualAtomExternalityRegression` calculations all PASS:

- `source` has only `observer` Quit, `target` has both players Quit, and
  `quittingTerminalPayoffDifferenceAtom source target observer joint=1`;
- the mover replacement gains one and is an exact terminal best response;
- every unrestricted observer deviation from the source has payoff at most
  zero, equal to its baseline cap;
- debts are `(1,0)` at source and `(0,1)` at target, so total debt and support
  cardinality remain one;
- at the source root the mover has a tail-independent unit Quit gain, while
  at the target root the observer has a tail-independent unit Continue gain;
  hence neither displayed sure-exit root is exact Nash for any tail;
- arbitrary replicated all-Continue prefix roots are exact Nash, preserve the
  complete terminal semantic pair, and have mover-deleted survival one.

This refutes an externality-to-observer-gain implication and any claim that
the **displayed charged source/target row** is already a Nash--Bellman edge or
strict debt/support rank drop.  The exact-prefix roots themselves are exact
Nash roots, however; they merely carry no charged externality.  Accordingly
“no exact edge anywhere in the enriched finite object” should not be claimed.

## 4. Required repair and disposition

Please restrict the headline, Section 1, No-go A, and the first paragraph of
Section 5 to a **charge-compatible/same-selected-row conversion**.  Suggested
replacement scope:

> The exact signed-window packet does not force a positive normalized
> endpoint difference on a row carrying its selected signed terminal flow,
> and a common-reach mover externality does not make either displayed charged
> row Nash or give the observer an admissible deviation.  A converter may
> still use an earlier first-disagreement row or construct a different row
> from positive-global-minimum data.

After that wording repair the verdict is PASS at the intended local
architecture scope.  The result remains internal/no export: both regressions
are checked/local and have `D_*=0`; the synthesis is a useful no-go for one
converter, not a contraction of the full Fin4 hard residual.

