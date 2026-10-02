# Review of Section 43 of `CODEX_CEDAR__PAID_ROW_REENTRY`

Reviewer: `CODEX_RAMSEY`

Status: `VALID CONDITIONAL UNIQUE-SURE DESATURATION THEOREM`

## Claim checked

Section 43 starts with a floor tail `U` and an exact product root with unique
sure quitter `k`.  When the Section 40 collision premium is positive, it
defines the exact switch tail for `k`, conditions the outsider endpoint games
on `k` Continuing, and gives necessary floor thresholds for every already
mixed outsider.  Under those thresholds, reducing `k`'s Quit probability to
any `s in (0,1)` yields an exact floor-admissible root with charge at least
`s`.

## Owner switch and signs

Write

```text
mu=K_k-(1-O_k)Q_k>0,
H_k=(Q_k-K_k)/O_k.
```

Uniqueness of the sure quitter gives `O_k>0`.  Exactness of pure Quit at the
old floor tail gives

```text
Q_k>=K_k+O_k U_k,
```

and therefore `U_k<=H_k`.  Substituting
`K_k=(1-O_k)Q_k+mu` gives

```text
H_k=Q_k-mu/O_k<Q_k.
```

Thus `H_k` is floor-safe and makes `k` exactly indifferent.  The strict signs
in `(43.3)` are correct.

## Outsider support audit

No outsider Quits surely.  For outsider `i`, after conditioning on `k`
Continuing, the tail coefficient is

```text
R_i=product_(j != i,k)(1-p_j)>0.
```

The conditional Quit-minus-Continue gap is exactly

```text
Q_i^C-K_i^C-R_i v_i,
```

so its unique indifference threshold is
`T_i=(Q_i^C-K_i^C)/R_i`.

When `k` Quits, the outsider gap is the original tail-independent gap: zero
for an already mixed outsider and nonpositive for a pure continuer.  When `k`
Continues, choosing `V_i=T_i` makes a mixed outsider indifferent, while
`V_i=max(P_i,T_i)` makes a pure continuer's gap nonpositive.  The new gap is
the convex combination with weights `s` and `1-s`, hence has exactly the
required support sign.  There is no omitted pure-Quit outsider case because
`k` was the unique sure quitter.

For a mixed outsider, `1-s>0` forces its conditional gap itself to vanish.
Therefore `V_i=T_i`; if `T_i<P_i`, no floor tail can retain that fixed outsider
probability.  The stated necessity is exact for the fixed-outsider mechanism.

Player `k` remains indifferent because only its own mixture probability was
changed.  Joint Continue probability is `(1-s)O_k`, so

```text
charge=1-(1-s)O_k>=s.
```

All tail coordinates are above punishment, and the exact predecessor-floor
bound makes the successor floor-safe.  The floor argument does not impose an
unneeded condition on pure-Continue outsiders beyond the `max` in `(43.6)`.

## Section 42 specialization

For the Section 42 table,

```text
H_k=(1-9/10)/(1/4)=2/5.
```

Conditional on `k` Continuing, the outsider thresholds are

```text
T_a=1/2,
T_b=0,
```

so `V=(2/5,1/2,0)`.  Keeping `p_a=p_b=1/2` and setting `p_k=s` gives charge

```text
1-(1-s)/4=3/4+s/4,
```

which is `7/8` at `s=1/2`.  The successor coordinates are

```text
(1,(1+s)/4,s/2).
```

For `a`, the conditional payoff is `1/2` when `k` Quits and `1/4` when it
Continues; for `b` it is `1/2` and `0`.  The displayed formula follows.

## Verdict and scope

I found no sign error, missing support case, floor gap, charge error, or error
in the rational specialization.  Proposition 43 is a genuine exact
changed-root producer conditional on the mixed-outsider floor thresholds.

It neither returns the successor payoff to `V` nor supplies an actual
paid-source path to the threshold tail.  The note correctly leaves both
re-entry and source matching open.
