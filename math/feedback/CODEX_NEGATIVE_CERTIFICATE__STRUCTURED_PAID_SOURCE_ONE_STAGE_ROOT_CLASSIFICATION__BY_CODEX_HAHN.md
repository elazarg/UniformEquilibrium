# Review of the structured paid-source one-stage root classification

Reviewer: `CODEX_HAHN`

Frozen SHA-256 reviewed:
`f46c2456860a0fc744eb15ccd79cd4a525e23dada28748e67096491c0a133622`

## Verdict

**PASS as ordinary mathematics, conditional only on the structured-source
fields stated in the reviewed tropical export.** I found no probability-mode,
strategy-class, or cap-tail error. In particular, the sure-
`b` boundary is used correctly: it screens every outsider's arbitrary
behavioral replacement, but it does not screen `b` itself. The proof separately
bounds precisely that unscreened owner branch by the source cap pin.

The result is a genuine one-step quantitative debt descent, not yet a
renewable descent or a consumer of the off-minimum paid-port component.

## Checks

### Coalition accounting and owner selection

The checked inequalities

```text
lowerDebt_mul_collisionMass_le_debtDrop_of_exact
singletonMass_mul_otherDebt_le_debtDrop_of_exact
```

apply to the actual terminal-semantic source pair and an exact root at its
prescribed payoff. Global minimality supplies the lower debt `D_*`; the last
exact-cap Quit-now response supplies `d_b >= gamma`. Hence vanishing total
drop forces both collision mass and every singleton mass owned by a label
other than `b` to vanish. With the supplied uniform absorption floor, the
singleton-`b` mass stays bounded below.

The product-law ratio

```text
mu({b,j}) / mu({b}) = q_j / (1-q_j)
```

is legitimate because positive singleton-`b` mass makes every opponent's
Continue probability positive. Collision mass tending to zero therefore
forces every opponent marginal Quit probability to zero. No correlated-root
claim is being made.

### Sure-`b` conclusion

The structured source fields imply

```text
B_(n,b) -> r_b({b}),
d_(n,b) >= gamma,
```

and hence `limsup u_(n,b) <= r_b({b})-gamma`. Against the newly selected root,
the Quit and Continue endpoints of `b` consequently converge respectively to
`r_b({b})` and a value at most `r_b({b})-gamma`. Since singleton-`b` mass is
positive, `b` uses Quit with positive probability. Exact binary
complementarity then forces its marginal to be pure Quit once the endpoint
gap is strict.

### Cap-tail upgrade and unrestricted deviations

This is the delicate step, and it passes.

For every outsider `j != b`, the prescribed root and every unilateral root
replacement by `j` retain the sure quitter `b`. Therefore
`quittingRootExpectedPayoff_eq_of_hasSureQuitter` makes both sides of the root
Nash inequality independent of whether the continuation annotation is the
literal source payoff `u_n` or its complete behavioral cap `B_n`. Thus the
outsider inequalities remain exact.

For `b`, a Continue replacement removes the last sure quitter. Its only
additional root gain at cap tail is exactly

```text
[C_b(q_(-b); B_(n,b)) - Q_b(q_(-b))]_+.
```

Opponent marginals tending to all Continue and `B_(n,b) -> r_b({b})` make
this quantity tend to zero. This proves root approximate Nash against
`quittingContinuationBestResponse reward tau_n`, not merely against the
prescribed payoff. The theorem

```text
isεAsymptoticNash_quittingRootThenContinuation_of_isεQuittingRootNash
```

then gives terminal approximate Nash against the complete behavioral
deviation class, including Never and arbitrarily late stopping, even though
the tail `tau_n` is not itself Nash. That distinction is handled correctly.

Because the root has `b` surely Quit and every opponent Quit probability
tends to zero, the prescribed terminal payoff converges to the fixed vector
`reward({b})`. This contradicts the standing terminal exploitability gap.

### Uniformity over exact roots

The final diagonal argument is correct. If no common positive debt-drop floor
existed on a tail, one could choose increasing source indices and exact roots
whose drops tend to zero, producing exactly the forbidden sequence already
classified. Finite product-root Nash existence supplies the selections.

## Source-field audit

The reviewed export `FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT.md`
supplies the required data:

- the last update is an attained complete-strategy Quit-now cap with one
  fixed positive gain, so the source debt of `b` equals that gain;
- every cluster of the last-edge source has cap coordinate
  `B_b=r_b({b})`, which forces convergence of that bounded coordinate after
  the already permitted subsequence extraction;
- all source pairs are actual carrier points and hence have debt at least
  `D_*`;
- the strict source payoff gap excludes the all-Continue limit root and,
  by compactness of the product-root simplex and closedness of exact Nash,
  gives the uniform absorption floor for every exact root at the source
  payoff.

No punishment-floor admissibility is required.

## Scope

The theorem proves one fixed positive drop from each sufficiently late
structured source. It does not prove that the prefixed child is stationary,
has the tropical ancestry again, retains the paid row in a form to which the
same theorem reapplies, or lies in a smaller finite-rank class. Those are the
remaining consumer questions and should remain explicit.
