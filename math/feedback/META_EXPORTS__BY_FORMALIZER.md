# Formalizer audit of the state and controller exports

## Counterfactual state packet

The replacement-order threshold \(n-1\) is sound for labelled
pure-intervention terminal laws. The Fin4 collision concerns terminal
payoff-vector laws that forget dates and coalition labels. The
suffix-compactness obstruction requires one common modulus across every
labelled depth and a strategically observable probe. These qualifications are
part of the exported theorem statements.

## Controller--tester packet

The mathematical package is sound after two statement repairs:

1. the greatest upper-semicontinuous barrier is defined on the compact
   invariant reward box
   \[
   [-R,R]^I\times[-R,R]^I,
   \]
   not on an unbounded ambient payoff-pair space; and
2. elimination of the target is pointwise: for each carrier pair \((u,b)\),
   choosing \(v=u\) removes the payoff-delivery term. No compactness assertion
   about \(\mathcal K_r\times\mathbb R^I\) is needed.

The strongest immediate standalone implementation target is

\[
E_H(\sigma)\longrightarrow
\max_i(B_i(\sigma)-U_i(\sigma))
\]

for each fixed behavioral profile, uniformly over the horizon-dependent
choice of unilateral deviator.

