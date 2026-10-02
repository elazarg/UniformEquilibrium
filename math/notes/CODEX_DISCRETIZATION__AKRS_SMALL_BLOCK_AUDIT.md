# AGKRS small-block discretization audit

## Status

The S.3 discretization claim survives independent checking.  A complete
review with explicit uniform constants is recorded in
[`../feedback/AGKRS_3_4__BY_CODEX_DISCRETIZATION__DISCRETIZATION.md`](../feedback/AGKRS_3_4__BY_CODEX_DISCRETIZATION__DISCRETIZATION.md).

The essential facts are:

- Lemma 4.9's constructed witness, unlike an arbitrary nearby product row,
  preserves the singleton Quit support exactly;
- matching each cell's absorption probability gives a tail-payoff error
  bounded uniformly from every stage by a weighted absorption telescope;
- positive singleton mass in a small cell comes from either a supported
  nonterminal jump or a positive derivative on a continuous component; and
- small jumps require an $O(p)$ conversion from their actual endpoint payoff
  to the solo payoff.

For $d$ players, reward bound $R$, and the published resolution-$k$
discretization, the audit obtains the valid loose bound

$$
\eta_k\le \frac{R\bigl(12+2^{d+1}(2^d-1)\bigr)}{k}.
$$

The output is an absorbing profile uniformly sequentially $\eta_k$-perfect
at every stage.  No approximate-Nash conclusion is asserted here.

## Sources inspected

- AGKRS, published Proposition 4.8, Lemma 4.9, Definition 4.13, and Theorem
  4.15;
- `Literature/AshkenaziGolanKrasikovRainerAndSolan2022.lean`;
- `UniformEquilibrium/Quitting/AbsorptionPath/ContinuousPath.lean`.

## Next check

The full packet still requires an independent audit of the refusal-based
compactification and terminal-jump S.2 arguments.  This notebook establishes
only the no-terminal-jump S.3 arm.
