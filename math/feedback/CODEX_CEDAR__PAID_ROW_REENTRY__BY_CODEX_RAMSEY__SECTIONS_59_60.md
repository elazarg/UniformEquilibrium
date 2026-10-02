# Review of Sections 59--60

Reviewer: `CODEX_RAMSEY`

## Verdict

**PASS in the stated behavioral-profile scope.**  I checked the literal
full-reset comparison in Section 59 and the bounded best-response walk and
two-step split in Section 60.  The identities, quantifiers, signs, and
constants are correct.  Neither result produces exact floor-admissible
Nash--Bellman edges.

## Section 59

For active `j`, both `H_(r,j)` and `G_r` use the replacement strategy
`R_(r,j)` in coordinate `j`; for inactive `j`, both use `sigma_r(j)`.
Distinct-coordinate updates commute, so the displayed unilateral word really
reaches `G_r` from each matching anchor.

The uniform low-debt estimate is exact.  The tangent-family endpoint field
gives `d_j(H_(r,j))<=lambda_r^2` on the active support.  Off the support the
base debt is zero, semantic source convergence makes each inactive source
debt tend to zero, and finiteness makes their maximum tend to zero.  Thus
`eta_r->0` without an unstated uniformity assumption.

The terminal gap at the actual profile `G_r` gives some `j` with
`d_j(G_r)>=gamma`.  Subtracting the two debt identities yields

```text
(B_j(G_r)-B_j(H))-(U_j(G_r)-U_j(H)) >= gamma-eta_r.
```

The payoff-loss/cap-rise dichotomy at half this amount follows immediately.
Because the two profiles have the same own `j` strategy, their prescribed
payoff difference is one of the strategywise differences defining `E_j`;
the difference of the two suprema is also bounded by `E_j`.  Hence either arm
implies the claimed opponent-environment discrepancy.  Eventually
`gamma-eta_r>=gamma/2`, so the fixed `gamma/4` lower bound is correct.

This is a reached behavioral reset comparison.  It does not show that any
unilateral row is a simultaneous exact root, nor that the high-debt endpoint
in the payoff-loss arm is already a low-debt re-entry.

## Section 60

At step `t`, choose a strategy whose payoff is strictly above
`B_(m_t)(sigma^t)-epsilon`.  Since `d_(m_t)(sigma^t)>=gamma`, its prescribed
gain is greater than `g=gamma-epsilon`.  Opponents of the mover are unchanged,
so its cap is invariant and its reached debt is at most `epsilon`.  No cap
attainment is assumed.

With

```text
X_t=sum_(i!=m_t)(U_i^(t+1)-U_i^t),
```

the exact telescope is

```text
sum_t X_t
 = sum_i(U_i^L-U_i^0)-sum_t moverGain_t
 <= 2*n*M-L*g.
```

The hypotheses give `g>gamma/2` and `L*gamma>8*n*M`, hence
`L*g>4*n*M` and the right side is strictly below `-L*g/2`.  Some step has
`X_t<-g/2`, and pigeonholing its `n-1` outsiders gives the strict loss
`g/[2(n-1)]`, which is strictly larger than `gamma/[4(n-1)]`.

For the harmed outsider `j`, updating to a `theta`-best response at `Q`
leaves its opponents and therefore its unrestricted cap unchanged, while
making its debt at most `theta`.  If the cap is at most the midpoint level,
the reached payoff is also below that level because prescribed payoff never
exceeds the cap.  Otherwise the best response gains more than
`delta/2-theta>delta/4`.  The two alternatives and their strict inequalities
are therefore correct.

The output is a bounded-length reached behavioral walk and then either a
low-debt negative payoff transfer or a fixed-gain paid recovery update.  It
does not supply exact punishment-floor roots, a charged exact edge, or payoff
re-entry along the maintained admissible relation.

