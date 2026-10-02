# Review of Section 6J / Proposition 6J

Reviewer: `CODEX_EULER`

## Verdict

**VALID ordinary mathematics, with the stated local scope.**  The component-label
coupling proves the claimed baseline-absorption inequality.  The five-player
regression has arbitrarily fine literal root mesh, a fixed prescribed atom,
two fixed reset labels, and joint plus every-player-deleted exposure of order
at least `h`, while its actual prefix absorption is bounded below by `1/3` and
conditioning spends the same-label residual atom.  The construction is not a
positive-minimum tangent family and does not refute a theorem that exploits
such global structure.

## General coupling inequality

Choose all component labels first and couple the radial profile to the
all-source profile by using identical source-law samples whenever every label
is the source label.  This agreement event has probability

```text
product_j (1-a_j),
```

so the disagreement probability is

```text
ell = 1-product_j(1-a_j) <= sum_j a_j = H.
```

For any finite all-Continue event `H_L`, the total-variation coupling bound
therefore gives

```text
|P^a(H_L)-P^0(H_L)| <= ell <= H.
```

Writing `alpha=1-P(H_L)` yields both

```text
alpha^0_L-H <= alpha^a_L <= alpha^0_L+H.
```

In particular, the displayed lower bound (6J.2) is correct.  Consequently,
if `H=O(h)` and the actual radial packet is required to have
`alpha^a_L=O(h)`, then necessarily `alpha^0_L=O(h)` as well.  Deleting one
player merely removes its component label from this coupling and gives the
advertised at-least-as-sharp estimate.

## Exact five-player regression

Let `h=1/N` and

```text
s_N=(1-h/2)^N.
```

The source `c` clock survives its `N` displayed rows with probability `s_N`.
Both the source and target laws of each reset mover survive identically until
date `N`, so conditioning on reaching that row leaves its outer target weight
equal to `h`.  Its literal marginal Quit probability at date `N` is therefore
`h*(1/2)=h/2`.  Together with the `c` hazards `h/2`, this proves the claimed
mesh bound.

Under the source profile the terminal coalitions are `{c}` with probability
`1-s_N` and `{a}` with probability `s_N`.  Under the full `m` replacement,
`{m}` occurs exactly when `c` survives and `m` quits at date `N`, with mass
`s_N/2`.  Since the only nonzero reward is `r_o({m})=-1`, the prescribed
orientation has size

```text
(0-s_N/2)*(-1)=s_N/2.
```

The union bound gives `s_N>=1/2`, so this is at least `1/4` exactly as stated.

For the simultaneous outer packet, survival after deleting `c` is

```text
(1-h/2)^2,
```

and hence its exposure is `h-h^2/4>=h/2`.  After deleting `m` or `n`, the
baseline `c` clock and the other reset remain; after deleting `a` or `o`, the
baseline and both resets remain.  The Bernoulli estimate

```text
1/s_N=(1+1/(2N-1))^N >= 1+N/(2N-1) >= 3/2
```

is valid for `N>=2`, so all these latter survival values are at most
`s_N<=2/3`.  Their exposures are therefore at least `1/3`, which is in
particular at least `h/2` because `h<=1/2`.  Joint survival is

```text
s_N(1-h/2)^2,
```

so joint absorption is at least `1-s_N>=1/3`.  This verifies every joint and
one-player-deleted calculation and the two fixed visible reset labels.

Finally, conditional on all Continue through the date-`N` row, each selected
target mover law has survived its sole possible Quit row and is thereafter
identical to the source mover's Never law.  Player `a` then quits next.  The
residual source and target laws consequently give zero mass to `{m}`, so the
same prescribed orientation has residual atom zero.  This is a literal
conditioning calculation, not a semantic-state inference.

## Scope

The example proves exactly that fine mesh, fixed atom charge, and two-label
joint/every-deleted lower exposure do not determine either an `O(h)` upper
bound on actual prefix absorption or renewal of the same atom after the
cutoff.  Baseline source absorption (or stronger source-fiber information) is
an independent datum at this interface.

The reward table has minimum total debt zero and the reset movers themselves
have zero debt.  Thus the example does not instantiate the positive-minimum
atom/reset frontier, does not rule out rigidity derived from that frontier,
and is not a counterexample to uniform equilibrium.  The qualifications in
Section 6J state this boundary accurately.
