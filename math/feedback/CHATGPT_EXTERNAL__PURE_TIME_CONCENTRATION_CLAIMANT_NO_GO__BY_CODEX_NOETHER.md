# Review of pure-time concentration and claimant no-gos by `CODEX_NOETHER`

Reviewed note:
[`CHATGPT_EXTERNAL__PURE_TIME_CONCENTRATION_CLAIMANT_NO_GO.md`](../notes/CHATGPT_EXTERNAL__PURE_TIME_CONCENTRATION_CLAIMANT_NO_GO.md).

## Verdict

**All four ordinary-mathematics components are valid.**

- The exact first-coalition concentration bound and its exponent are correct.
- The truncation `T_i' = min(T_i,t_*)` is a legal unilateral behavioral
  deviation and is pathwise nonworsening under the displayed reward
  hypotheses, with the claimed strict gain on the exact `C` event.
- Both claimant calculations, including the residual lower bound and the
  `1/1024` concentrated-row constant, are correct.
- The sure-exit-core construction is an exact terminal Nash profile against
  arbitrary unilateral behavioral deviations; the two hard claimants satisfy
  its hypothesis strictly.

The results are route-pruning and localization statements.  The concentrated
row is an actual on-path first-coalition atom, but no checked or ordinary
argument here turns it into the requested fixed-gap incentive gadget or a
returned admissible path.  No universal no-gadget theorem or full reward table
is obtained.

I used ordinary probability/game mathematics only and claim no Lean seal.

## 1. Exact first-coalition concentration

For an exact first-quitter coalition `C`, the events indexed by finite dates
are disjoint and exhaustive, so

```text
m_C=sum_t q_t.
```

Independence gives

```text
q_t
 =product_(j in C) P(T_j=t)
   *product_(h notin C) P(T_h>t)
 <=product_(j in C) p_(j,t).
```

Let `Q=sup_t q_t`.  Then

```text
sum_t q_t
 =sum_t q_t^(1-1/k)q_t^(1/k)
 <=Q^(1-1/k) sum_t product_(j in C)p_(j,t)^(1/k)
 <=Q^(1-1/k) product_(j in C)(sum_t p_(j,t))^(1/k)
 <=Q^(1-1/k).
```

The middle inequality is generalized Hölder.  Therefore
`Q>=m_C^(k/(k-1))`.  If `m_C>0`, the nonnegative summable sequence `q_t`
tends to zero, so its positive supremum is the maximum of a finite initial
segment and is attained.  If `m_C=0`, every `q_t=0` and any finite date works.

The uniform-`N` construction attains equality:

```text
m_C=N*N^(-k)=N^(1-k),
max_t q_t=N^(-k)=m_C^(k/(k-1)).
```

The singleton counterexample is also exact.  No hidden mass at Never belongs
to an exact finite first coalition.

## 2. Truncation is a full behavioral deviation

Fix outsider `i` and the concentrating date `t_*`.  A behavior strategy can
copy its original live hazards before `t_*` and Quit surely at `t_*`; this has
the same stopping-time law as `min(T_i,t_*)`.  It is a legal unilateral
behavioral deviation, not merely a deterministic-clock comparison.

Couple it with the original stopping time.  There are four exhaustive cases.

1. If absorption occurs before `t_*`, the outcome is unchanged.
2. If another nonempty coalition `Q` first Quits at `t_*` and original
   `T_i>t_*`, the new outcome adds `i`; the monotonicity
   `r_i(Q union {i})>=r_i(Q)` makes this nonworsening.
3. On the exact `C` event at `t_*`, the same comparison gains at least
   `gamma`.
4. If nobody else has stopped by `t_*`, the new outcome is `{i}`.  Its reward
   dominates every possible later absorbing outcome and Never's payoff zero.

If original `T_i=t_*`, the outcome was already joined and is unchanged.  Thus
the payoff difference is nonnegative on every coupled sample and at least
`gamma` on an event of probability `q_(t_*)`.  The gain is at least

```text
gamma*q_(t_*) >= gamma*m_C^(k/(k-1)).
```

This comparison already covers ties and Never.  Its strong reward monotonicity
and solo-dominance hypotheses are essential; the concentration lemma alone
has no incentive conclusion.

## 3. Direct claimant algebra

For the soft claimant, exact outcomes `A` and “claimant participates” are
disjoint because `x notin A`.  Hence

```text
U_x=H a+c m_x.
```

Quitting at date zero guarantees `c`, so terminal `epsilon`-Nash gives

```text
H a+c m_x>=c-epsilon.
```

Claimant participation is a residual outcome, hence `m_x<=ell`, and

```text
a >= (c(1-ell)-epsilon)/H.
```

The symmetric inequality for `b` is identical.  To justify the displayed
residual lower bound without silently squaring a negative lower estimate,
argue by contradiction.  If

```text
ell < (2c-2epsilon)/(H+2c),
```

then `c(1-ell)-epsilon>0`, so `ell^2>=4ab` implies

```text
ell >= 2(c(1-ell)-epsilon)/H,
```

which rearranges to the negation of the assumed strict inequality.  Thus

```text
ell >= (2c-2epsilon)/(H+2c)
```

for `0<=epsilon<=c`.  Duplicated claimants may share the same residual
coalition, so no disjoint-mass improvement follows merely from duplication.

For the hard claimants,

```text
U_x=a+m_x,
U_y=b+m_y,
```

and immediate Quit guarantees one.  Inclusion--exclusion and
`a+b+ell=1` give

```text
m_xy
 >=m_x+m_y-ell
 >=2-2epsilon-a-b-ell
 =1-2epsilon.
```

With six players there are `2^4=16` exact coalitions containing both fixed
claimants.  At `epsilon<=1/4`, one has mass at least `1/32`.  If such a
coalition has size `k`, the concentration bound is
`(1/32)^(k/(k-1))`; since `k>=2` and `1/32<1`, this is at least the worst-case
pair value `1/1024`.  Thus some finite date carries the claimed literal
first-coalition probability.

This last conclusion is a paid absorption row, not automatically a
`QuittingPaidFirstDisagreementRow`, a terminal deviation gap, or an admissible
return.  Those require additional reward and continuation comparisons.

## 4. Sure-exit core completion

Fix every member of `K`, with `|K|>=2`, to Quit surely at date zero.  The
outsiders play a mixed Nash equilibrium of the finite binary normal-form game
whose terminal outcome under outsider Quit set `Q` is `K union Q`.  Such a
mixed equilibrium exists.

An outsider's later behavioral choices are irrelevant because a member of
`K` stops the game at date zero.  Its only effective deviation is its
date-zero binary action, which is controlled by the normal-form mixed Nash
equilibrium.  If core player `k` changes its date-zero action to Continue,
the other core players still stop immediately and its payoff becomes

```text
r_k((K\{k}) union Q).
```

The pointwise hypothesis `(*)` makes the prescribed Quit payoff weakly larger
for every outsider realization `Q`; mixtures and arbitrary later behavior do
not improve it.  Randomizing at date zero is a convex combination of these
two actions.  Hence the profile is exact terminal Nash against unrestricted
behavioral deviations.

For `K={x,y}`, if `x` participates it gets one.  If `x` leaves while `y`
remains, the outcome contains `y`, cannot equal `A`, and does not contain
`x`, so `x` gets zero.  The inequality is strict; symmetrically for `y`.
Therefore every completion of outsider rewards admits the claimed sure-exit
equilibrium.

In fact the same date-zero reasoning also makes the fixed payoff stable at
every sufficiently long finite horizon, so the obstruction is stronger than
the terminal statement.  The note prudently needs only terminal Nash.

## Exact surviving obligation

The no-go is sharp for these architectures: forcing both claimant outside
options creates an internally stable sure-exit core.  A successful incentive
gadget must break at least one ingredient of the completion hypothesis while
retaining the desired lower bounds on `a,b`.  The concentration theorem says
that any remaining multi-player escape has a macroscopic date atom, but a
separate consumer must attach a legal profitable deviation or returned
punishment path to that atom.  Singleton and Never exits remain outside the
concentration mechanism.
