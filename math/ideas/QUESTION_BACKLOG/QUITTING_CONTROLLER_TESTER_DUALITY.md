# Decide or effectively certify the controller--tester value

## Mathematical data

Fix a four-player quitting reward table \(r\). Let \(\mathcal K_r\) be its
compact terminal-semantic carrier, whose elements are prescribed payoff and
unrestricted behavioral-cap pairs \((u,b)\). Define

\[
\eta(r)=\min_{(u,b)\in\mathcal K_r}\max_i(b_i-u_i).
\]

Let \(T_x\) be semantic prefixing by a product root and let \(e_\infty\) be
the all-Continue boundary state.

For rational tables, assume the escape-aware finite-clock shell hierarchy and
its exact rational interval-tree verifier. Accepted positive lower trees are
sound for \(\eta(r)>0\), and every rational table with positive value has such
a tree at some finite scale. The value \(\eta(r)\) can be approximated by
certified rational intervals to arbitrary accuracy, but exact equality to zero
is not thereby decidable.

## Question

Prove one of the following.

1. For every four-player table \(r\), \(\eta(r)=0\).
2. Give a concrete finite, preferably rational, four-player table and an
   independently checkable certificate proving \(\eta(r)>0\).

A positive certificate may be:

- a closed forward-invariant set containing \(e_\infty\) on which
  \(\max_i(b_i-u_i)\) has a fixed positive lower bound;
- a bounded upper-semicontinuous Bellman barrier with a fixed positive value
  at \(e_\infty\); or
- a finite algebraic certificate with a proved sound map to one of those
  objects.

## Useful intermediate results

- convert one source-preserving hard-residual branch into a positive barrier
  or into a zero-value controller;
- give a finite certificate system complete for the zero-value locus, or prove
  that no such system of a specified kind can exist;
- prove that one explicit rational search region has strictly positive shell
  lower value and provide the accepted tree; or
- construct, from every rational table and scale, an actual controller with a
  certified exploitability bound tending to zero under one fixed payoff
  target.

## Nonanswers

- restating \(\eta(r)\) using the carrier itself or its canonical greatest
  barrier;
- numerical evidence without an exact lower certificate;
- a finite-horizon lower bound that does not control escaping stopping times
  and Never;
- restricting the tester to stationary or bounded-clock deviations; or
- a positive-gap conclusion which assumes positive minimum exploitability for
  the same table instead of deriving it from the controller--tester data.
