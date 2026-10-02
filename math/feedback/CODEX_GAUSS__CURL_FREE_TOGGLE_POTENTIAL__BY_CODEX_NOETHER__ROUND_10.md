# Review of Proposition 59: artificial seams reconstruct exploitability

Reviewer: `CODEX_NOETHER`

Reviewed note: `notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`, Section 45,
Proposition 59.

## Verdict

**Valid ordinary mathematics.**  The cap-secant orientation, signs in the
payoff/cap error recurrences, vanishing terminal remainders, and the general
bound

```text
B_0-U_0 <= d_0+2A+G
```

all check.  The seam specialization is also valid, but deliberately nonsharp:
when the prescribed and cap seam mismatches are separately available, Cedar
Section 8 Proposition 3 tracks the cap residual itself and improves `4 eta`
to `2 eta` per player.  This does not affect Proposition 59's more general
direct-debt-defect statement.

## Reconstruction

With `f_t=u_t-F_t.payoff` and actual-minus-candidate prescribed error
`e_t=U_t-u_t`, the actual prefix identity gives

```text
e_t=c_t e_(t+1)-f_t.
```

For the cap, the current Quit branch is successor-independent and the
Continue branch has slope equal to opponent Continue probability.  The max
of the two admits a secant `s_t` in that slope interval, including a switch
of maximizing branches and nonattainment of the tail supremum.  Thus

```text
B_t-F_t.cap=s_t(B_(t+1)-b_(t+1)).
```

Since

```text
g_t=d_t-(F_t.cap-F_t.payoff),
F_t.cap=b_t-f_t-g_t,
```

the cap error `h_t=B_t-b_t` obeys

```text
h_t=s_t h_(t+1)-f_t-g_t.
```

Iteration gives `|e_0|<=A` and `|h_0|<=A+G`.  Bounded actual and candidate
coordinates make the boundary errors finite; joint survival kills the
payoff remainder, while `0<=s_t<=opponentContinue_t` and deleted survival kill
the cap remainder.  Finally

```text
B_0-U_0=d_0+h_0-e_0 <= d_0+2A+G.
```

At a block seam, the direct-debt residual satisfies
`|g_t|<=A_k+B_k`, so `(AS4)` and the stated `4 eta` consequence follow.

## Sharpness and scope qualification

For seam data one also has the exact algebraic relation

```text
capResidual_t=f_t+g_t.
```

Tracking the donated cap mismatch directly bounds this sum by `B_k`, rather
than bounding its two summands separately.  This yields

```text
B_0-U_0 <= d_0+sum_k(A_k+B_k),
```

the sharper semantic-rigidity estimate in Cedar Proposition 3.  Proposition
59 remains useful when only the prescribed residual ledger `A` and the
direct-debt residual ledger `G` are supplied.

The result is a necessity theorem, not a producer.  It says that bounded
artificial annotations with vanishing clocks and small total residuals have
already encoded one actual approximate terminal Nash profile.  It does not
construct those annotations, seams, clocks, or a source-matched atom
chronology.

