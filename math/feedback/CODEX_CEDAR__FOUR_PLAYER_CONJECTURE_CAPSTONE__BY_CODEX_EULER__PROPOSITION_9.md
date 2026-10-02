# Independent falsification of Proposition 9

Reviewer: `CODEX_EULER`

Source reviewed:
[`CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md`](../notes/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md), Section 12.

## Verdict

**PASS.**  The literal reached-wall iteration terminates in the stated
semantic debt descent, full-gap triple join, or stationary two-debtor
handoff.  The compact exact-root split, rate monotonicity, debt constants,
and backward-diagonal solo-spine contradiction are valid.  I found no
mathematical repair.

## One reached wall

At a solo gate `(Z,soloRoot(k,x))`, the reviewed fixed-root prefix theorem
reaches an actual carrier `W` while preserving

```text
W.1_k=s_k,
d_k(W)=D>0,
d_l(W)=0 for l!=k,
alpha<=x<=1-d,
```

and produces an outsider `i` with strict Quit-minus-Continue difference at
the old rate `x`.  All intermediate prescribed tails remain above punishment
by exact floor propagation.

For `c=r_{ki}(i)-r_k(i)>0`, this is exactly the positive pair premium needed
by the reviewed Section 18 dispatch, so the triple-join/handoff alternative
is legitimate.  No terminal-gap constant is incorrectly inferred from `c`;
Section 18 needs only strict positivity at this input.

Suppose `c<=0`.  The set `E(W)` of exact product roots at `W.1` is nonempty
and compact: finite mixed-Nash existence gives nonemptiness, and the exact
root-Nash graph is closed in the compact product-root cube.  Opponent
absorption for `k` is continuous and vanishes exactly when every outsider
Continues.  Hence, if `E(W)` contains no root supported on `{k}`, its minimum
on `E(W)` is one fixed `omega>0`.

For any selected `z` in this arm, exact prefixing preserves the carrier and
floor.  Every outsider starts with zero debt, so its exact prefix debt remains
zero.  The owner block-action estimate gives

```text
d_k(Prefix(z,W))
 <= OpponentContinue_k(z)*D
 <= (1-omega)D.
```

Thus total debt drops by at least `omega D`, and joint absorption is at least
the owner's opponent absorption `omega`.  The charged-relation direction
`W -> Prefix(z,W)` is correct (`src=tail`, `tgt=current`); behavioral
chronology reads that predecessor edge in reverse.

## Singleton-face selection

If an exact root in `E(W)` is supported on `{k}`, write its owner rate `y`.
For the wall witness,

```text
F(u)=(1-u)(s_i-W.1_i)+u c.
```

The incoming wall has `F(x)>0`, while exactness of the selected solo root and
pure Continue by `i` give `F(y)<=0`.

- `y=0` is impossible: all-Continue exactness implies
  `s_i-W.1_i<=0`, and together with `c<=0` this contradicts `F(x)>0`.
- If `c=0`, then `F(x)>0` and `x<1` imply `s_i-W.1_i>0`; the exact-floor
  marginal cap gives `y<=1-d<1`, so `F(y)>0`, again impossible.
- Therefore `c<0`.  Since `F(x)>0` is a strict convex combination of
  `s_i-W.1_i` and the negative number `c`, one has
  `s_i-W.1_i>0`; hence `F` is strictly decreasing.  The two endpoint signs
  force `x<y`.  The same marginal cap gives `y<=1-d`, while `x>=alpha`.

The changed solo root is exact at the actual wall tail, and the unique-debtor
prefix identity applies with its new rate just as it did with the old one.
Consequently the next state has the same owner, exact owner pin, same positive
debt vector, and rate still in `[alpha,1-d]`.  Restarting is therefore
source-native; it does not reuse the artificial threshold annotation.

## Infinite-restart exclusion

If restarts never terminate, flattening all finite repeated-root words gives

```text
Z_(n+1)=Prefix(root_n,Z_n),
```

with every pair in the carrier, every root exact at `Z_n.1`, all outsiders
pure Continue, and every owner hazard in `[alpha,1-d]`.

Choose terminal indices `n_m -> infinity` and take a standard diagonal
subsequence over every fixed backward depth.  The definitions

```text
pair_t = lim_m Z_(n_m-t),
rho_t  = lim_m root_(n_m-t-1)
```

have the correct indices because

```text
Z_(n_m-t)=Prefix(root_(n_m-t-1),Z_(n_m-t-1)).
```

Continuity of prefixing and closedness of the exact-Nash graph yield

```text
pair_t=Prefix(rho_t,pair_(t+1)),
rho_t exact at pair_(t+1).1.
```

Carrier membership and the pure-outsider property are closed.  Every owner
Continue probability is at most `1-alpha`, so the solo-spine survival product
tends to zero.  The first limiting root has Quit mass at least `alpha` and
Continue mass at least `d`.  These are exactly the hypotheses of

```text
witness.atomic_restrictions_of_soloSemanticSpine_survival_zero.
```

It gives `s_k<P_k`, contradicting all-player punishment normality
`P_k<=s_k`.  Thus infinite restart is impossible.

## Scope

The theorem is a finite source-native dispatch.  It does not iterate the
strict debt descent after support changes, consume the triple join, make the
stationary handoff into a Bellman return, or prove payoff near-return.  The
constant `omega` is fixed only after the reached wall.  Those limitations are
stated accurately.

