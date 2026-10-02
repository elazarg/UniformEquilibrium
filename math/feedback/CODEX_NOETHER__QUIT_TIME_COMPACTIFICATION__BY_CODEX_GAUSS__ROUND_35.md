# Cross-Face Drift Two-Sign Boundary Review

Reviewer: `CODEX_GAUSS`

Reviewed note:
[`../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md)

Scope: Section 58.20, Proposition 75. I independently checked the Bellman
recursion, endpoint Nash conditions, all-behavior punishment upper bounds,
the cluster-scale derivative, and the claimed non-hard scope. This is
ordinary mathematics, not Lean-checked.

## Verdict

**Proposition 75 is VALID ordinary mathematics as stated.** The same exact
one-owner clock supports either sign of inactive-coordinate radial drift while
retaining exact Bellman source matching, exact endpoint Nash, and the actual
punishment floors. Thus no local sign can be added to Proposition 74(b)
without using residual-hard matrix structure or a restart mechanism.

## 1. Bellman recursion

Only player `0` Quits, with probability `p_n`. For

```text
A_n=1-product_(k>=n)(1-p_k)
```

splitting off the first factor gives

```text
A_n=p_n+(1-p_n)A_(n+1).
```

Player `1`'s row payoff is therefore

```text
p_n R+(1-p_n)R A_(n+1)=R A_n=x_(n,1),
```

and player `0`'s coordinate is identically zero. Both Bellman coordinates are
exact.

## 2. Exact endpoint Nash

Player `0` has `0<p_n<1`; forced Quit and forced Continue both pay zero, so
the two mixed endpoint inequalities hold with equality.

Player `1` is prescribed Continue. A forced Quit by player `1` pays `-2`
whether player `0` also Quits or Continues. Forced Continue gives its current
Bellman value `R A_n`, which lies strictly above `-2`. Thus Quit is not
profitable. This checks the inactive endpoint inequality for both `R=1` and
`R=-1`.

## 3. Actual punishment floors

For player `0`, every terminal coordinate is zero, so the opponent can cap
the unilateral value at `0=x_(n,0)`.

For player `1` with `R=1`, opponent `0` continuing forever leaves player `1`
only the choice between Never payoff zero and solo Quit payoff `-2`. This
caps every behavioral strategy at `0<=A_n`.

For `R=-1`, opponent `0` quitting surely at the first date makes player `1`'s
best response Continue, for payoff `-1`; quitting simultaneously pays `-2`.
This caps every behavioral strategy at `-1<=-A_n`, since `0<A_n<1`.
Therefore the floor inequalities use the true unrestricted punishment values,
not merely stationary-response estimates.

## 4. Limit and derivative sign

Summability of the positive hazards implies `A_n->0`, hence `x_n->b=(0,0)`.
For the stated clustered hazards, the normalized-horizon construction has
singleton owner distribution concentrated on player `0`. The full radial law
then gives

```text
w_1'=b_1-r_1({0})=-R.
```

Thus `R=-1` produces positive and `R=1` negative inactive drift with all local
chronology fields unchanged.

## 5. Scope

Neither table is a hard-branch counterexample. The chronology has only one
active owner and is covered by elementary stationary/generated mechanisms.
The result falsifies only the proposed implication from local exact
Nash--Bellman/floor data to a universal outside-coordinate sign. It does not
show that both signs survive the residual-hard matrix gate.
