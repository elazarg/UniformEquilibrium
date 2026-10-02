# Round 16 Feedback on Quit-Time Compactification

Reviewer: `CODEX_GAUSS`

Reviewed note: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: Sections 47--48, Propositions 44--45. I independently reconstructed
the normalized-motion stationary-prefix argument `(D2)`--`(D13)` and the
near-total-absorption rounding argument `(E1)`--`(E3)`. I also compared both
claims with Simon (2012), Section 2.3, Lemma 2.1 and its proof sketch on
p. 185.

Status:

- Proposition 44: `VALID_ORDINARY_MATHEMATICS_WITH_ONE_UNUSED_BOUNDARY_CAVEAT`.
- Proposition 45: `VALID_ORDINARY_MATHEMATICS`.

Neither verdict is a Lean or integration seal.

## Proposition 44: static endpoint algebra

Write `q=Q(p)>0` and let `w` be the absorbing reward contribution of the row.
Then `h=w/q` and

```text
f(r,p)-r=q(h-r),
f(h,p)=h.
```

Thus `(D1)` gives `(D2)` exactly. For player `n`, forcing Continue changes
only the continuation coordinate and its coefficient is

```text
c_n=product_(ell != n)(1-p_ell) in [0,1].
```

After passing to the fixed no-sure-quitter scale supplied by
`exists_scale_without_sure_quitter_of_not_instant`, every `p_n<1`.
The Continue-support inequality at `r` therefore gives
`g_n=A_n-B_n(h)<=gamma+||h-r||`. If `p_n>0`, the Quit-support inequality gives
the reverse one-sided bound `-g_n<=gamma+||h-r||`. Hence `(D3)`--`(D4)` have
the correct support quantifiers, including `p_n=0`.

The affine endpoint identity

```text
h_n=p_n*A_n+(1-p_n)*B_n(h)
```

implies `B_n(h)-h_n=-p_n*g_n`, so `(D5)` is correct.

## Pure quit times and the largest marginal

For a finite pure quit time `t`, let `d_t=V_(n,t)-h_n`. Then

```text
d_0=(1-p_n)g_n,
d_(t+1)=c_n*d_t-p_n*g_n.
```

Solving this recursion gives `(D6)`, with the geometric quotient interpreted
as the finite sum when needed. If `c_n<1`, its limit gives the displayed
Never value. Choosing `j` with `m=p_j=max_n p_n` is legitimate because
`q>0`. For `n!=j`, player `j` is an opponent, so

```text
1-c_n>=m,  p_n<=m.
```

The two signs of `g_n` then give `(D7)` exactly. In particular, `p_n=0`
makes the dangerous numerator zero; no unsupported use of `(D4)` occurs.

For the selected player, a finite quit before the splice has positive gain at
most `zeta` when `g_j>=0`, and at most `L*m*zeta` when `g_j<0`. This proves
`(D8)` without dividing by `1-c_j`. If `c_j=1`, all opponents have zero
hazard. Since `q>0`, necessarily `p_j=m>0`, and `(D5)` forces `g_j=0`.

There is one harmless correction to the prose around `(D6)`: when `c_n=1`,
the stationary **Never** payoff is zero and need not be the limit of the
finite quit-time values relative to an arbitrary fixed point `h`. Thus the
sentence saying that the infinity formula merely drops the first term should
be restricted to `c_n<1`. This does not affect the proposition. The only
player for whom `c_n=1` can occur is the selected positive-hazard player, and
the spliced proof treats every response continuing through the prefix by the
actual punishment bound, not by a stationary-Never limit.

The production theorem
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`
(`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`)
does give the claimed unrestricted behavioral reduction for the final
spliced profile.

## Punishment, tail replacement, and horizon indexing

Rationality gives `r_j>=chi_j-gamma`; `(D2)` therefore yields `(D9)`.
For a selected-player response that continues through the stationary prefix,
the forced-Continue recursion with terminal tail value `z` is

```text
W_L-h_j = c_j^L*(z-h_j)
          -p_j*g_j*sum_(s<L)c_j^s.
```

`IsPunishmentWithin` bounds every shifted behavioral response by
`z<=chi_j+delta`. Combining this with `(D4)` proves `(D10)`, including
Quit after the splice and Never.

The notation transcription defines
`StationaryPrefixThenPunish G p M punishment` to use `p` at dates `t<=M`.
Thus the proof must instantiate its parameter as

```text
M=L-1,
```

which gives exactly `L` stationary dates. The note's phrase “horizon `L-1`”
is consistent with this convention. Since `L>=3`, the exact requirement
`1<M` in `HasStationarilyGeneratedApproximateEquilibria` holds even at the
smallest allowed value `L=3`.

The prescribed payoff differs from the infinite stationary payoff `h` only
if all players survive these `L` dates, proving `(D11)`. For `n!=j`, a pure
deviation reaching the splice has player `j` among its fixed opponents, so
that event has probability at most

```text
c_n^L <= (1-m)^L.
```

Replacing the post-splice opponents changes a bounded payoff by at most
`2B` on that event. A second `2B(1-m)^L` compares the prescribed payoff to
`h`, which gives `(D12)`. This comparison is valid for Quit times after the
splice and for Never; before the splice the two profiles agree up to
absorption.

No bounded-controller restriction is hidden here. Exact pure-time extremality
applied after these pointwise pure-time bounds covers replacement of a
player's entire behavioral strategy.

## Exposure window and error ledger

For `gamma<1/4`, put `R=1/sqrt(gamma)>2` and
`L=ceil(R/m)`. Since `0<m<=1`,

```text
L>=3,
R<=L*m<R+1,
(1-m)^L<=exp(-L*m)<=exp(-R).
```

As `zeta<2gamma`, this gives

```text
L*m*zeta < 2*sqrt(gamma)+2*gamma,
```

which verifies `(D13)`. The selected-player regret above `delta` and every
nonselected regret both tend to zero, independently of the rate of
`m/gamma`. Choosing an actual punishment with `exists_punishmentWithin` then
matches the two independent quantifiers `delta,epsilon` in
`HasStationarilyGeneratedApproximateEquilibria`.

## Proposition 45: finite-product rounding

Let `N` be the positive number of players. From

```text
product_n(1-p_n)<gamma
```

one factor satisfies `1-p_j<gamma^(1/N)`. After taking `gamma<1`, this also
ensures `p_j>0`, so the old Quit-support inequality for `j` is available.
Rounding `p_j` to one makes the Continue-support condition for `j` vacuous;
both of `j`'s forced endpoints are unchanged because they overwrite her own
coordinate.

For `n!=j`, each forced endpoint is affine in `p_j`. If terminal rewards and
the continuation carrier are bounded coordinatewise by `C`, every endpoint
lies in `[-C,C]`, so each endpoint moves by at most

```text
2*C*gamma^(1/N).
```

The difference of the Quit and Continue endpoints therefore moves by at most
`4*C*gamma^(1/N)`. This proves `(E2)` with the displayed constant, while all
other players' support conditions are unchanged. `IsRational.mono` upgrades
the same `r` from `gamma`- to `eta`-rational.

For complete quantifier precision, “arbitrarily small” may be read as:
for every positive accuracy threshold there is a positive `gamma` below it
with the stated data. Given the error `epsilon` in
`HasInstantApproximateEquilibria`, choose such a `gamma` with
`2*eta<=epsilon`, choose a punishment within `epsilon`, and apply
`instantProfile_isQuitEpsilonEquilibrium`. Its error is
`2*eta+epsilon<=2*epsilon`, exactly the definition's bound after monotonicity.

## Source and status

Simon (2012), Section 2.3, Lemma 2.1, p. 185 explicitly states both
contrapositive compactness mechanisms: normalized motion tending to zero
produces a stationarily generated approximate equilibrium using a largest
quitter and an advanced punishment date, while `Q(p)` tending to one produces
an instant approximate equilibrium. Propositions 44--45 are rigorous
quantitative expansions of that source sketch. Their novelty should therefore
be described as closing details in the source argument or supplying explicit
moduli, not as theorem-level novelty over Simon's stated Lemma 2.1.

The declarations `StationaryPrefixThenPunish`, `IsPunishmentWithin`,
`HasStationarilyGeneratedApproximateEquilibria`, `EpsilonRow`, and
`instantProfile_isQuitEpsilonEquilibrium` are in
`Literature/Simon2007.lean`. That transcription is not a production library,
and `lemma5_corrected_2012` itself remains a `sorry` theorem. The behavioral
pure-time endpoint cited above is checked in the production tree, but it does
not by itself prove either producer. No `L`, `A`, or full-theorem claim follows
from this review.

## Verdict

After restricting the stationary-Never sentence to `c_n<1`, Proposition 44
is valid ordinary mathematics and does compile the normalized-motion failure
sequence to the exact stationarily generated branch against unrestricted
behavior. Proposition 45's coordinate rounding and
`gamma+4*C*gamma^(1/N)` endpoint modulus are also valid ordinary mathematics.
I found no objection affecting either conclusion.
