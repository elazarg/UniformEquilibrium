# Review of the third proposed answer to Question 172

## Decision

The answer does not close the problem, as it states.  It contributes one clean
quantitative theorem candidate—the vanishing conditional collision fraction—
and one potentially useful exact Poincaré-map regression for the four-player
singleton blocker.  Its phantom-boundary identities are already part of the
established toolkit.

The proposed seam-to-return dichotomy is the correct shape of the remaining
`T × W × C` problem, but is a requested theorem rather than a proved result.
The literature citation is not used in this audit and should be checked
independently before entering permanent documentation.

## Late conditional collision concentration

At date `t`, let `p_(i,t)` be player `i`'s Quit probability,

```text
alpha_t = 1-product_i(1-p_(i,t)),
```

and let `kappa_t` be the probability that at least two players Quit.  Since
`p_(i,t) <= alpha_t`, the union bound over player pairs gives

```text
kappa_t
  <= sum_(i<j) p_(i,t)p_(j,t)
  <= choose(|I|,2) alpha_t^2.                              (1)
```

For survival weights `P_(s,t)` in a finite window `[s,e)`, exact first-
absorption accounting gives

```text
sum_(t=s)^(e-1) P_(s,t) alpha_t = 1-P_(s,e).
```

If the denominator is positive, (1) therefore yields

```text
[sum_t P_(s,t) kappa_t]/[1-P_(s,e)]
  <= choose(|I|,2) sup_(t>=s) alpha_t.                    (2)
```

Along roots converging to all-Continue, the right side tends to zero.  Thus
every limit of normalized late absorption laws is supported on singleton
coalitions.  This proves the singleton-concentration portion of the occupation
bridge `O`; it does not prove target funding, the punishment floor, or equality
with the independently extracted packet.

Equation (2) is generic finite-product probability mathematics and merits
formal extraction with a separate zero-denominator branch.

## Phantom boundary identities

Unrolling an exact convergent Bellman tail gives

```text
v_s = u_s + P_(s,infinity) v_infinity,
v_s-v_infinity = H_s (y_s-v_infinity),
H_s = 1-P_(s,infinity),
y_s = u_s/H_s.                                           (3)
```

The corresponding finite-window identity is

```text
y_(s,e) = [v_s-P_(s,e)v_e]/[1-P_(s,e)].                  (4)
```

These identities are correct and explain why ordinary convergence of `v_t`
does not control normalized restarted delivery.  They are not new here: the
finite restart and phantom-boundary decompositions are already formalized.
The exact `T × W` regression strengthens the warning by showing that the
normalized quotient in (4) can converge to a nonzero constant while all
exposed debt and clock conditions hold.

## Four-player Poincaré-map construction

The answer completes the known four-player singleton blocker with pair rewards
and claims an exact owner cycle

```text
0 -> 1 -> 3 -> 2 -> 0
```

whose local return map has both:

- a contracting invariant ray producing a summable phantom-tail skeleton;
  and
- a positive interior fixed point producing an absorbing exact period-four
    equilibrium.

If the displayed rational/algebraic formulas and every outsider Nash
inequality check, this is a valuable regression: local phantom dynamics and a
robust singleton blocker can close nonlinearly into an actual periodic
equilibrium.  It would show that a prospective proof must exclude global
Poincaré closures, not merely stationary complementary singleton mixtures.

No executable artifact or full reward-table certificate accompanied the
answer.  Before accepting the construction, an isolated reconstruction must
verify:

1. the rational return map and its invariant ray;
2. the algebraic fixed point and all four hazards in `(0,1)`;
3. every on-support indifference and off-support deviation inequality at all
   four phases;
4. consistency of the chosen pair rewards across all phases; and
5. equality of the cyclic annotation with the actual periodic terminal payoff.

Even if verified, the construction is a solved-game regression, not a
`T × P × W` counterexample witness: the positive periodic fixed point supplies
an equilibrium, so the global terminal-instability condition fails.

## Seam-to-return dichotomy

The suggested dichotomy is:

1. a late compatible window admits an `o(1)`-exploitable realization; or
2. its persistent refusal/promise defect yields an exact positive-charge
   punishment-floor return.

The first branch contradicts terminal instability and the second contradicts
finite capacity.  This is precisely the attachment bridge `R` isolated by the
pair matrix.  The statement is sufficient, but no proof is supplied.  The
local cap regressions explain why it cannot be proved one root at a time.

The formal triple target should retain exact endpoints:

```text
selected cap segment w_end -> w_start with positive charge
plus either
  an exact return w_start -> w_end,
or
  a suffix co-realizing w_end as payoff and deviation envelope.
```

Without one of those data, behavioral periodic repetition is not an annotated
exact-chain cycle.

## Actions

- Add (2) to the experimental Q172 extraction and promote it if the generic
  statement is clean.
- Reconstruct the four-phase blocker map as a separate exact experiment before
  citing any of its formulas.
- Treat the seam-to-return dichotomy as the `T × W × C` triple task, not as an
  answer to Question 172.
