# Scoped review of the post-all-Never midpoint certificate

Reviewer: `CODEX_MINER`

Verdict: **PASS for Proposition 3.2 and its exact `lambda=3/4`
certificate.**  This review is deliberately scoped to the newly added
midpoint lemma, its quantifiers, and the printed rational cutoff; Ramsey's
review remains the whole-prototype audit.

## Claim checked

Let `a in A_K` be an actual finite-clock semantic pair with `K <= 9`, put

\[
 f=F(a)=\max_i(a_{B_i}-a_{U_i}),
\]

and define the diagonal midpoint `z` coordinatewise by

\[
 z_{U_i}=z_{B_i}=(a_{U_i}+a_{B_i})/2.
\]

Then, for `f>0`, this one center proves `L_M=0` for every
`M <= floor(24/f)`; for `f=0` it proves the same for every level.  For the
stored rational `K=4`, `lambda=3/4` center,

\[
 f={2868660135241342669\over320000000000000000000},
\]

the last certified level is exactly `M=2677`.

## Verification

Every actual terminal-semantic debt is nonnegative, so

\[
 |z_{U_i}-a_{U_i}|=|z_{B_i}-a_{B_i}|
 ={a_{B_i}-a_{U_i}\over2}\le {f\over2}.
\]

Thus `||z-a||_infty=f/2`, and `F(z)=0`.  Since `K<=9` and
`8m+1>=9` for every `m>=1`, padding the same four marginal laws by zero
finite-date masses embeds the literal profile in every `A_(8m+1)`.  There is
no closure or limiting-law step.  The single center therefore witnesses all
constraints defining `R_M` exactly when

\[
 {f\over2}\le {12\over m}\quad(1\le m\le M),
\]

which is equivalent to `M <= 24/f`.  The smallest radius occurs at `m=M`,
so there is no missing intermediate-level quantifier.  If `f=0`, the center
is already diagonal and the distance is zero at every level.

For the printed fraction, exact arithmetic gives

\[
 {24\over f}
 ={7680000000000000000000\over2868660135241342669}
 =2677.208047\ldots .
\]

Moreover

\[
 {12\over2677}-{f\over2}
 ={596817958925675087\over
   1713280000000000000000000}>0,
\]

whereas

\[
 {12\over2678}-{f\over2}
 =-{1135921088157833791\over
   856960000000000000000000}<0.
\]

Hence `2677` is the exact largest level certified by this particular center,
and `2678` is the first level it does not cover.

I also ran

```text
python3 experiments/fin4_quantile_center_prototype.py \
  profile-zero-witness --preset lambda34-k4 --M 129
```

The exact evaluator reports the displayed `f`, verifies the closed `A_K`
system, reports midpoint distance `f/2`, and returns
`largest_M_certified_by_same_center = 2677`.

## Scope

This is an exact zero witness for the outer relaxation, not a positive lower
certificate and not evidence that `L_2678>0`.  It is a useful exact
algorithmic regression and should remain internal with the prototype unless
a later certified infeasibility calculation supplies the missing positive
certificate/consumer.
