# Review of `CODEX_CEDAR__PAID_ROW_REENTRY`, Section 46

Reviewer: `CODEX_RAMSEY`

## Claim checked

Section 46 starts from an exact product root with one unique sure quitter
`k`, all outsider probabilities below one, and a fixed punishment-floor
outsider tail `W`.  It claims that a support-regular outsider equilibrium at
the sure face, together with strict owner switch slack, continues by the
implicit-function theorem to exact uniformly charged roots with owner hazard
`s<1`.  It then gives the exact failure trichotomy and checks the Section 44
regression along its explicit local branch.  The stated scope is only a local
conditional exactification result, not a paid-source producer or payoff
near-return.

## Verdict

`REPAIR REQUIRED` in the original general statement.  It becomes valid after
adding strict canonical-box slack `H_k(q_-k)<M`; the concrete regression is
already inside the box.

### Post-review correction

Continuity preserves the lower floor inequality from strict `H_k>P_k`, but
not membership in the canonical upper payoff box.  Sure-root exactness yields
only `H_k>=U_k`, not `H_k<=M`; division by small positive `O` can make `H_k`
arbitrarily large.  Proposition 46 must assume `H_k(q_-k)<M` (or equivalent
strict interior membership in the canonical box) so that the continued
tails remain admissible.  With this repair, the IFT and all calculations
below are valid.  The Section 44 branch has `H_k=2/5` and is unaffected.

## Audit

At `s=1`, the owner Quits surely, so every outsider's endpoint gap is
independent of every continuation-tail coordinate.  The original exact root
therefore makes every active outsider gap zero and every inactive outsider
gap nonpositive.  Fixing the inactive coordinates at zero, the nonsingular
active-gap Jacobian gives a local continuous (indeed `C^1`) solution of all
active indifference equations.  Strict interiority of active probabilities
and the strict negative signs of inactive gaps persist, so the continued
profile is genuinely an outsider Nash equilibrium, not just a zero of the
mixed equations.  Unique sureness also gives `O(q_-k)>0`, and positivity
persists locally.

The owner switch value

```text
H_k(z)=(Q_k(z)-K_k(z))/O(z)
```

is continuous on this positive-survival neighborhood.  Strict
`P_k<H_k(q_-k)<M` therefore keeps `H_k(z(s))` inside the admissible interval
after shrinking the neighborhood.  The repaired Proposition 45 then supplies
the full exact root and charge at least `s`; restricting further to `s>=1/2`
gives the claimed uniform charge.

At the original sure root, owner optimality is

```text
Q_k(q_-k) >= K_k(q_-k)+O(q_-k)U_k.
```

Division by positive `O(q_-k)` proves `H_k(q_-k)>=U_k>=P_k`.  Hence failure of
the strict hypotheses can only be: equality at the owner floor, an inactive
gap equal to zero (positive is excluded by exactness), or a singular active
Jacobian.  This validates the trichotomy; it does not assert that any branch
of the actual paid source excludes those cases.

The chronological warning is also exact.  Continuity of `X(s)` and `V(s)`
turns a positive limiting mismatch `d` into the lower bound `d/2` on a small
one-sided neighborhood.  In the Section 44 table,

```text
Delta_a=2s z_b-1,
Delta_b=(1+s)/2-(1+3s)z_a/2
```

has active Jacobian `[[0,2],[-2,0]]` at `s=1`, with determinant `4`.  Solving
the two equations gives

```text
z_b(s)=1/(2s),
z_a(s)=(1+s)/(1+3s).
```

The displayed limits `V(1)=(2/5,0,0)` and `X(1)=(1,1/2,1/2)` have sup-norm
distance `3/5`, so the eventual `3/10` lower bound follows.

Apart from the repaired canonical-box hypothesis, no contradiction was
found.  The section correctly does not infer a reached successor relation, a
multi-edge return, or an adapter from the paid-row source data.
