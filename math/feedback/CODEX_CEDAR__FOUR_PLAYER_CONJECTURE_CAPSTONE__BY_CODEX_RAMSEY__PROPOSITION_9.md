# Independent falsification of Proposition 9

Reviewer: `CODEX_RAMSEY`

Source reviewed:
[`CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md`](../notes/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md), Section 12.

## Claim checked

Starting from the unique-debtor solo gate supplied by Propositions 5--6,
repeated literal exact solo prefixes reach a blocker wall.  At each wall,
either every exact root has positive opponent absorption for the debtor,
giving a strict semantic-debt contraction; a positive pair premium enters the
reviewed triple-join/stationary-handoff dispatch; or an exact solo root with a
strictly larger owner hazard restarts the construction.  Infinite restart is
claimed impossible because backward compactification produces a fixed-owner
solo semantic spine with vanishing survival, contradicting punishment
normality.

## Verdict

**REVISE, then PASS after three bounded statement/proof-writing repairs.**
There is no mathematical counterexample.  The compact root separation, debt
contraction, affine sign argument, restart, diagonal reversal, and checked
solo-spine contradiction are all valid.

The repairs needed before export are:

1. call the Proposition 5 source a **literal carrier gate**, not an “actual”
   gate if “actual” could mean attained by one behavioral profile; Proposition
   5 produces a compact carrier limit, and attainment is not asserted;
2. write the charged relation in `(12.1)` on payoff projections,
   `W.1 -> Prefix(z,W).1`, while retaining the carrier pairs separately; and
3. in the diagonal construction explicitly choose the terminal indices with
   `n_m>=m`, so `n_m-t-1` is defined for every fixed depth `t` eventually.

These are literal scope/typing/indexing repairs.  They do not change an
alternative, hypothesis, inequality, or constant.

## Compact exact-root separation

For a fixed wall pair `W`, the product-root cube is compact and the exact-Nash
conditions at `W.1` are closed, so the nonempty exact-root set `E(W)` is
compact.  If no exact root is supported in the singleton face `{k}`, then
every root has strictly positive opponent absorption for `k`: zero opponent
absorption forces every outsider of `k` to Continue purely, which is exactly
support inside `{k}`.  Continuity therefore gives

```text
omega=min_(z in E(W)) OppAbs_k(z)>0.
```

Choose any `z in E(W)`.  All outsider debts of `W` are zero.  Exactness at
the prescribed coordinate and coordinate-locality of the all-Continue tail
make their cap defects zero after prefixing, so their new debts remain zero.
For the unique debtor `k`, the exact defect--drift inequality gives directly

```text
OppAbs_k(z)*D(W) <= D(W)-D(Prefix(z,W)).
```

Equivalently, the block-action transport estimate gives

```text
d_k(Prefix(z,W)) <= OppContinue_k(z)*D(W)
                  <=(1-omega)D(W).
```

Thus total debt falls by at least `omega*D(W)`, and total absorption is at
least `OppAbs_k(z)>=omega`.  Carrier prefix closure and exact floor-forward
invariance supply the floor-safe edge.  In the checked relation orientation
the payoff edge is

```text
W.1 -> Prefix(z,W).1;
```

behavioral prefix chronology reads it in reverse.

## Singleton-face root and rate increase

Suppose instead that `E(W)` contains a root supported inside `{k}` and let
`y` be its owner Quit rate.  For the wall blocker `i`, with
`c=r_{ki}(i)-r_k(i)<=0`, the forced Quit-minus-Continue difference is

```text
F(u)=(1-u)(s_i-W.1_i)+u*c.
```

The incoming root has `F(x)>0`, while exactness of the selected singleton-face
root gives `F(y)<=0` because `i` Continues purely.

- If `y=0`, all-Continue exactness gives `F(0)<=0`; together with `c<=0`
  this contradicts `F(x)>0`.
- If `c=0`, `F(x)>0` and `x<1` give `F(u)>0` for every `u<1`; the terminal-gap
  marginal cap `y<=1-d<1` again contradicts exactness.
- Hence `c<0`.  Since `F(x)>0` is a convex combination of `F(0)` and `c<0`,
  one has `F(0)>0`; therefore `F` is strictly decreasing.  It follows that
  `x<y<=1-d`.

The lower bound `y>=alpha` is inherited from `y>x>=alpha`.  The wall prefix
has the same unique debtor and `W.1_k=s_k`, so the exact solo root of rate
`y` is another gate state.  Restart is legitimate.  If instead `c>0`, the
reviewed pair-premium dispatch applies with `kappa=c` and gives precisely the
triple-join or stationary-handoff alternative.

## Flattening and backward diagonal compactification

If restart never terminates, flattening the finite repeated-root words gives

```text
Z_(n+1)=Prefix(root_n,Z_n),
```

with every `Z_n` in the carrier, `root_n` exact at `Z_n.1`, all outsiders of
`k` pure Continue, and owner Quit rates in `[alpha,1-d]`.

Choose a diagonal subsequence of terminal indices with `n_m>=m` such that,
for every fixed `t`, both displayed limits exist, and put

```text
pair_t=lim_m Z_(n_m-t),
rho_t =lim_m root_(n_m-t-1).
```

The indexing has the required reverse orientation: applying the outward
identity at `r=n_m-t` gives

```text
Z_(n_m-t)=Prefix(root_(n_m-t-1),Z_(n_m-t-1)),
```

so continuity yields

```text
pair_t=Prefix(rho_t,pair_(t+1)).
```

Closedness of the carrier and exact-Nash graph gives carrier membership and
exactness of `rho_t` at `pair_(t+1).1`.  Pure outsider Continue is closed.
Every limiting owner Quit rate is at least `alpha`, so the solo survival
product is at most `(1-alpha)^n` and tends to zero.  The first root also has
Quit mass at least `alpha` and Continue mass at least `d`.

These are exactly the hypotheses of

```text
QuittingTerminalExploitabilityWitness.
  atomic_restrictions_of_soloSemanticSpine_survival_zero.
```

It gives `s_k<P_k`, contradicting the same-table punishment normality
`P_k<=s_k`.  Hence restart terminates after finitely many walls.

## Scope and export assessment

The result does not iterate a debt contraction after support changes, consume
the triple join, or produce a payoff near-return.  Nevertheless it **does**
meet the updated Fin4 partial-result criterion after the three literal
repairs: it is a finite, source-native carrier dispatch which removes the
previous all-Continue/changed-solo exact-selection wall as an independent
residual.  Its outputs are an explicit strict semantic-debt contraction or
the two already typed same-table Fin4 branches.

For the cleanest export, I recommend composing the triple-join output with
the independently reviewed Section 19 pair-base handoff.  The resulting
narrow packet would state: the zero-drop unique-debtor blocker gate finitely
enters either strict carrier-debt descent or one of the two actual stationary
two-debtor handoffs.  It must retain the nonclaims above and must not call the
initial compact carrier point behaviorally attained.
