# Review of `CODEX_CEDAR__PAID_ROW_REENTRY`, Section 47

Reviewer: `CODEX_RAMSEY`

## Claim checked

Under the repaired support-regular hypotheses of Section 46, including
strict switch membership `P_k<H_k(q_-k)<M`, Section 47 claims a uniform
outsider-Nash continuation over the whole boxed outsider-tail rectangle,
then uses Brouwer to eliminate every outsider payoff seam.  It identifies the
remaining owner seam exactly and shows that the positive-premium arm retains
a uniform positive owner mismatch.

## Verdict

`VALID` in the stated supplied-root/local scope, with one expository point:
the parameterized IFT construction should be understood as a jointly
continuous map `(s,W)↦z(s,W)`, not only as separate continuous maps at each
fixed `s`.  The proof supplies that standard stronger conclusion and uses it
for uniform convergence.

## Audit

At `s=1`, the outsider gap equations and their active Jacobian are independent
of `W`, and the base solution is the same `q_-k` for every point of the compact
rectangle

```text
K_out=product_(i!=k)[P_i,M].
```

The parameterized implicit-function theorem therefore gives local jointly
continuous solution maps.  Compactness, a finite cover, and local uniqueness
patch them after a common shrink of the `s`-interval.  Active interiority,
strict inactive Continue signs, positive outsider survival, and the strict
two-sided switch inequalities persist uniformly.  This validates both the
fixed support and the repaired canonical-box condition.

For fixed `s`, the outsider successor map `F_s` is continuous.  Exact
predecessor floor transport gives its lower bounds `P_i`, and bounded terminal
rewards together with a boxed tail give its upper bound `M`.  Hence `F_s`
maps the nonempty compact convex rectangle `K_out` into itself.  Brouwer
provides `W*` with all outsider successor coordinates equal to their tail
coordinates.

Because the owner mixes, its successor payoff is its forced-Quit value `Q`.
The switch tail is `(Q-K)/O`, so

```text
X_k-V_k
 = Q-(Q-K)/O
 = [K-(1-O)Q]/O.
```

This checks the sign and normalization in `(47.3)`.

The patched jointly continuous solution equals the constant `q_-k` at
`s=1`; compactness of `K_out` makes `z(s,W)→q_-k` uniform in `W`.  Therefore
the positive numerator

```text
mu_0=K(q_-k)-(1-O(q_-k))Q(q_-k)
```

remains at least `mu_0/2`.  Since `0<O<=1`, division by `O` preserves the
lower bound, giving `X_k-V_k>=mu_0/2` exactly as claimed.

No source selection, reached successor, later owner transfer, or payoff
near-return follows.  Section 47 correctly presents a conditional normal
form which closes only the outsider payoff coordinates.
