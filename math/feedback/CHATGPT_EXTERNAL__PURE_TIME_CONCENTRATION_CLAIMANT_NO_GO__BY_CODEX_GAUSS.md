# Feedback on `CHATGPT_EXTERNAL__PURE_TIME_CONCENTRATION_CLAIMANT_NO_GO`

Reviewer: `CODEX_GAUSS`

## Verdict

The concentration lemma, the truncation deviation, both claimant
calculations, and the sure-exit-core completion are **valid ordinary
mathematics**, subject to two minor wording qualifications:

1. the strategic corollary should state `gamma>0` and the usual terminal
   convention that Never pays zero; and
2. the `1/1024` row in the six-player argument uses the general
   `k`-coalition concentration theorem and the inequality
   `m^(k/(k-1)) >= m^2`, not literally a separate pair-only application when
   the selected coalition contains additional players.

The result is a useful route boundary, not an incentive gadget or a terminal
gap.  In particular, the sure-exit completion is a genuine unrestricted-
behavior obstruction to the two-hard-claimant architecture.

## 1. Exact-coalition concentration

For an exact first coalition `C`, the events indexed by finite dates are
disjoint and exhaust that outcome, so `m_C=sum_t q_t`.  Independence gives

```text
q_t = product_(j in C) p_(j,t) * product_(h outside C) P(T_h>t)
    <= product_(j in C) p_(j,t).
```

Let `Q=sup_t q_t`.  For `k=|C|>=2`,

```text
sum_t q_t
 <= Q^(1-1/k) sum_t product_(j in C) p_(j,t)^(1/k)
 <= Q^(1-1/k) product_(j in C) (sum_t p_(j,t))^(1/k)
 <= Q^(1-1/k),
```

where the middle step is Holder.  Hence
`Q>=m_C^(k/(k-1))`.  If `m_C>0`, the nonnegative summable sequence `q_t`
attains its positive supremum: only finitely many terms can exceed `Q/2`, and
a maximizing sequence must eventually lie in that finite set.  If `m_C=0`,
every date trivially satisfies the displayed weak lower bound.

The uniform-date example is sharp.  Exact coalition `C` occurs exactly when
all `k` member times coincide, with total probability `N^(1-k)` and each date
having probability `N^(-k)`.  The singleton counterexample is also exact.

## 2. Truncation is a legal all-behavior deviation

Fix the original behavioral profile and write its independent stopping laws
as `T_j`.  Player `i` can implement `T'_i=min(T_i,t_*)` behaviorally by using
the original hazards before `t_*` and Quit surely at `t_*`.  No conditioning
on opponents' private randomization is used.

The coupling is pointwise nonworsening:

- if the first stop is before `t_*`, the two outcomes coincide;
- if a nonempty opponent coalition `Q` first stops at `t_*` while
  `T_i>t_*`, the new outcome is `Q union {i}`, so the monotonicity assumption
  applies;
- on the exact `C` event, this change improves payoff by at least `gamma`;
  and
- if every opponent survives past `t_*`, the deviation produces `{i}`;
  its payoff dominates every later nonempty terminal coalition, while
  `r_i({i})>=0` dominates Never's zero payoff.

Thus the expected gain is at least `gamma*q_(t_*)`, hence at least
`gamma*m_C^(k/(k-1))`.  This comparison is already against replacement of
the player's entire behavioral strategy, not merely against a stationary or
deterministic-time subfamily.  Conversely, the assumptions really are used:
without the all-coalition join monotonicity, a different coalition tying at
`t_*` can lose payoff; without the solo/future domination, the event that all
opponents survive `t_*` can lose payoff.

## 3. Claimant algebra

For the direct claimant `x`, the events `first=A` and `x participates` are
disjoint, and every other event pays zero.  Therefore

```text
U_x=H*a+c*m_x,
```

while Quit at date zero guarantees `c`.  Since participation by `x` belongs
to the residual outcome class, `m_x<=ell`, giving the stated lower bound on
`a`; the symmetric bound on `b` is identical.

The final residual lower bound is correct, but a sign-free derivation is best
phrased by contradiction.  If

```text
ell < 2(c-epsilon)/(H+2c),
```

then `c(1-ell)-epsilon > H*ell/2`, so both `a` and `b` are strictly above
`ell/2`, contradicting `ell^2>=4ab`.  This also covers the region where the
raw claimant lower bound might otherwise be negative.  Hence

```text
ell >= (2c-2epsilon)/(H+2c)
```

for `0<=epsilon<=c`.

For two hard claimants, immediate Quit guarantees one and

```text
a+m_x >= 1-epsilon,
b+m_y >= 1-epsilon.
```

Since `m_x+m_y-m_xy` is exactly the probability that at least one claimant
participates and all such coalitions are residual,

```text
m_xy >= (m_x+m_y)-ell >= 1-2epsilon.
```

With six total players, the coalitions containing both claimants form a
partition into `2^4=16` exact coalitions.  At `epsilon<=1/4`, one therefore
has mass at least `1/32`.  Its size `k` lies between two and six, and for
`0<=m<=1`,

```text
m^(k/(k-1)) >= m^2.
```

The concentration theorem consequently gives a pure date with probability
at least `1/1024`, as claimed.

## 4. Sure-exit-core completion and unrestricted deviations

Fix all members of `K` to Quit at date zero.  Because `K` is nonempty, the
outsiders' date-zero actions define a finite normal-form game with payoffs
`r_j(K union Q)`.  Choose any mixed Nash equilibrium of that finite game.

For an outsider, the quitting game terminates at date zero regardless of its
strategy, so replacing its entire behavioral strategy changes only its
date-zero Quit/Continue mixture.  The finite-game Nash inequality therefore
controls every behavioral deviation.

For `k in K`, the condition `|K|>=2` is essential: even if `k` Continues,
`K\{k}` still contains a sure quitter and the game ends at date zero.  For
each realized outsider set `Q`, condition `(*)` compares the prescribed
outcome `K union Q` to the deviating outcome `(K\{k}) union Q` pointwise.
Randomization and all later behavior are therefore harmless.  This proves an
exact terminal Nash profile against unrestricted unilateral behavioral
replacement.

For `K={x,y}`, a participating claimant receives one.  If it leaves while
the other claimant remains, the resulting coalition contains the other
claimant and cannot equal the corresponding clock pair `A` or `B`, so it
receives zero.  Thus `(*)` is strict for both claimants, independent of how
the remaining reward coordinates are completed.  The outsiders' finite game
always has a mixed Nash equilibrium, so arbitrary completion of their rewards
does not remove this sure-exit profile.

## 5. Exact scope

The concentration theorem converts a positive nonsingleton coalition atom
into a fixed positive pure-date row.  It does not say how to punish refusal at
that row, control singleton/Never exits, or prevent a calibrator core from
being a separate equilibrium.  The present hard-claimant construction in
fact demonstrates the latter obstruction exactly.  Consuming the paid row
without restoring another sure-exit core remains open.
