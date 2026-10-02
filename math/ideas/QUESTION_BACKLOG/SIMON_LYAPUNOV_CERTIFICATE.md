# Complete the Simon Lyapunov obstruction

## Mathematical data

Fix a rational finite quitting reward table, a rational \(\varepsilon>0\),
the compact near-feasible individually rational carrier \(K\), and the full
production correspondence \(G_\varepsilon\subseteq K\times K\). Let
\(c:G_\varepsilon\to\mathbb R_{\ge0}\) be its production-variation cost, with
\(c(x,x)=0\) on every self-loop.

A strict Lyapunov certificate is a bounded function
\(V:K\to\mathbb R\) and \(c_0>0\) such that

\[
V(y)\le V(x)-c_0c(x,y)
\qquad ((x,y)\in G_\varepsilon).
\]

## Question

Produce one of the following complete outputs.

1. Give a concrete rational table outside the stationary and
   immediate-punishment branches and an exact finite-cell or semialgebraic
   Lyapunov certificate on every edge of the full correspondence. Prove for
   this same correspondence that absence of a uniform positive exploitability
   gap would produce finite production orbits with arbitrarily large
   cumulative cost

   \[
   \sum_k c(x_k,x_{k+1}).
   \]

   Since the certificate bounds every such sum by
   \((\sup V-\inf V)/c_0\), conclude one fixed positive exploitability gap
   against every behavioral profile.
2. Refute that production-necessity implication on an actual quitting game
   satisfying its stated hypotheses.
3. Exclude such Lyapunov certificates on a mathematically defined class proved
   to contain every table left by the production classification.

Sampled or selected edges are insufficient. Every row variable, self-loop,
and positive-motion edge must be covered.

## Nonanswers

- a Lyapunov certificate without the production-necessity theorem;
- numerical bounded variation;
- a certificate on a strict subgraph;
- stationary branch exclusions without an all-behavior gap; or
- certificate soundness with no concrete certificate or exhaustive class.
