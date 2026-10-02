# Round 50 feedback on `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION`

Reviewer: `CODEX_GAUSS`

Target: Section 72, Proposition 92.

## Verdict

**Valid ordinary mathematics.**  The Continue-contribution estimate, max-cap
orientation, within-block increase bound, seam telescope, and fixed-label
conclusion all check.  I found no counterexample to `(N266)--(N269)`.

The result is a useful conditional clock adapter: persistent favorable cap
drops with only summable reverse violations cannot be replenished inside a
uniformly bounded exact cap recursion unless opponents carry divergent total
Quit hazard.  It does not show that atom/reset source data have the required
one-sided seam orientation.

## One-row cap calculation

For fixed player `i`, forcing `i` to Continue leaves the opponent-only
terminal contribution

```text
C_(k,t,i)=sum_(nonempty opponent coalitions Q)
             Pr(Q is the quitting coalition)*r_i(Q).
```

The coefficients have total mass `1-O_(k,t,i)`.  Therefore the reward bound
gives exactly

```text
|C_(k,t,i)| <= M(1-O_(k,t,i)).
```

No normalization or missing own-Quit contribution occurs here: the own-Quit
branch is the separate constant `Q_(k,t,i)` in the maximum.

Exact recursion and the fact that a maximum dominates its Continue branch
give

```text
b_(k,t,i) >= C_(k,t,i)+O_(k,t,i)b_(k,t+1,i),
```

hence

```text
b_(k,t+1,i)-b_(k,t,i)
 <= (1-O_(k,t,i))b_(k,t+1,i)-C_(k,t,i).
```

Taking positive parts is legitimate.  More explicitly, the positive part of
the right side is at most its absolute value, and

```text
|(1-O)b_next-C|
 <= (1-O)|b_next|+|C|
 <= (K+M)(1-O).
```

This proves `(N270)`, including switches between the Quit and Continue max
branches.  At `O=1`, the opponent-only contribution is zero and the cap
cannot lie below its successor, so both sides vanish.  At `O=0`, the estimate
correctly permits a full bounded reset.

Summing positive row increments dominates the signed net increment, giving
`(N271)` without assuming that the cap is monotone inside the block.

## Seam telescope

For real numbers `x,y`, `(x-y)_+-(y-x)_+=x-y`; therefore

```text
R_(k,i)-V_(k,i)=b_(k,N_k,i)-b_(k+1,0,i).
```

Adding and subtracting each block source yields

```text
sum_(k<n)(R_k-V_k)
 =sum_(k<n)(b_(k,N_k)-b_(k,0))
   +b_(0,0)-b_(n,0).
```

The first sum is at most `(K+M)sum_(k<n)A_k` by `(N271)`, and the boundary
term is at most `2K`.  Rearrangement is exactly `(N266)`.  Notice that the
proof needs only an upper bound on the signed internal increments; large
internal cap decreases help rather than hurt.

If `sum R_k` diverges while `sum V_k` and `sum A_k` are finite, the right side
of `(N266)` is uniformly bounded in `n`, a contradiction.  Thus `(N268)`
follows.  Uniform boundedness of all candidate caps is essential for the
fixed `2K` terminal term, and summability of `V` is essential because
unpriced seam rises can otherwise fund all later drops.

## Fixed second label

At a product row,

```text
1-O_(k,t,i)
 =Pr(some opponent of i Quits)
 <=sum_(j!=i)p_(k,t,j).
```

Thus divergence in `(N268)` forces divergence of the sum of the finitely many
opponent marginal series.  At least one fixed `j!=i` has a divergent series.
If player `i` already has divergent own hazard, the two labels are distinct
and deleting any one player leaves one divergent marginal stream, giving all
deleted and joint suffix clocks.  The conclusion also handles the singleton
player-set boundary vacuously: with no opponents `A_k=0`, `(N266)` prevents
the hypotheses `(N267)` from holding.

## Orientation and scope

The sign called favorable is correct for the chronological forcing account.
If the donated endpoint cap is above the next block's source cap, replacing
the local successor by the lower global successor lowers the prefixed cap.
Relative to the unchanged current candidate debt this creates favorable,
not adverse, direct-debt defect.  A reverse seam rise has the opposite sign
and must be summably controlled.

Proposition 92 therefore identifies a concrete substitute for independently
preselecting a second clock label.  Its producer hypotheses remain the hard
part: it neither orients a single atom seam nor proves divergent favorable
variation, summable reverse variation, or persistent own hazard for one
fixed mover.  The quantitative block-cap telescope itself is a genuine new
composition of elementary cap recursion with the existing two-label clock
criterion.
