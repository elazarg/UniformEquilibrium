# Round 6 Feedback on Pair-Atom Localization

Reviewer: `CODEX_NOETHER`

Reviewed note: `notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`

Scope: Propositions 22--23 only. The disjoint-pair leakage theorem and any
future counterexample gadget are outside this review.

Status: `VALID_ORDINARY_MATHEMATICS`

## Proposition 22 reconstructed

Let the players' planned quit times be independent random variables in
`N union {infinity}` and let `D={u,v}`. Write

```text
a = P(D is exactly the strict first-quitter coalition).
```

For every `lambda` with `0<lambda<a`, Proposition 22 asserts that some finite
date `t` has joint survival through the dates strictly before `t` at least
`a-lambda`, while both conditional hazards of `u` and `v` at `t` are at least
`lambda`. Replacing an outsider by deterministic quitting at `t` then makes
the first coalition contain `D` and that outsider with probability at least
`(a-lambda)lambda^2`. Optimizing gives `4a^3/27`.

I find the statement and proof correct.

## Survival indexing and one-date inequality

With

```text
R_t = P(for every j, T_j >= t),
q_j(t) = P(T_j=t | T_j>=t),
A_t = 1-product_j(1-q_j(t)),
```

`R_t A_t` is exactly the probability that the first quitting date is `t`.
Thus `sum_t R_t A_t<=1`; the missing mass is precisely the all-Never event.
The date-`t` exact-pair contribution is

```text
x_t=R_t q_u(t) q_v(t) product_(j notin D)(1-q_j(t)).
```

If `m_t=min(q_u(t),q_v(t))`, then

```text
q_u q_v = m_t max(q_u,q_v)
        <= m_t A_t,
```

because `A_t` is at least each individual hazard. Hence
`x_t<=m_t R_t A_t` with the claimed orientation.

Dates with `R_t=0` carry neither first-exit nor exact-pair mass, so assigning
zero to undefined conditional hazards there is harmless. If no date had
`m_t>=lambda`, then every positive `R_t A_t` term would have
`m_t<lambda`; since `a>0` supplies at least one positive exact-pair term,
summing yields the strict contradiction `a<lambda`. Thus the first threshold
date exists.

Before that first date, the exact-pair mass is at most `lambda` (indeed
strictly less whenever it is positive). At least `a-lambda` exact-pair mass
therefore occurs at or after `t`. Every such outcome survived strictly before
`t`, so it is contained in the event of probability `R_t`; hence
`R_t>=a-lambda`. This confirms both the survival index and the use of the
first, rather than an arbitrary, threshold crossing.

## Outsider deletion and optimized constant

Replace a distinct outsider `k` by the pure time `t`. Its replacement clock
survives strictly before `t` surely. Removing its old clock can therefore
only increase the pre-`t` survival probability of the remaining clocks.
Independence means the conditional hazards of `u` and `v` are unchanged.
There is no need to require other players to Continue at date `t`: on the
event being counted, the first coalition may properly contain `D`. The
resulting probability is at least

```text
(a-lambda) lambda^2.
```

The derivative of this expression in `lambda` is
`lambda(2a-3lambda)`, so its maximum on `(0,a)` occurs at `2a/3` and equals
`4a^3/27`. The older `lambda=a/2` corollary gives `a^3/8` exactly.

The argument also covers arbitrary Never atoms and extra players. It uses
only independence of private planned times, which is the correct law of an
ordinary behavioral profile along the unique all-Continue live history; it
does not assume stationarity, finite support, or bounded memory.

## Proposition 23 semantic adapter

For the outsider coordinate

```text
r(S)_k = 1  iff D union {k} is a subset of S,
           0  otherwise,
```

the prescribed terminal payoff is exactly the probability `L` of the
indicator event; a Never outcome contributes zero. At the date selected by
Proposition 22, the pure-time replacement of `k` earns one whenever all
opponents survive before `t` and both members of `D` quit at `t`. Other
players may join without changing the indicator. Complementary histories
pay zero or one, so the deviation payoff is at least `4a^3/27`, and its gain
over the prescribed profile is at least

```text
4a^3/27-L.
```

When `a=0`, this lower bound is `-L`; it follows from any nonnegative-payoff
pure-time replacement (or simply nonnegativity of exploitability), so no
division or threshold date is being used at the boundary.

If `k` belongs to the other designated pair, a first coalition containing
`D union {k}` is neither exact designated pair. Therefore `L<=ell`. Terminal
`epsilon`-Nash then gives
`ell>=L>=4a^3/27-epsilon`, with the inequalities in the stated direction.

This is unrestricted behavioral-deviation coverage at the terminal-law
level: the exhibited deterministic time replaces the player's entire
behavioral strategy. It is not a Nash producer and does not force `a>0`.
Indeed, the cubic estimate degenerates at `a=0`, exactly as the note states.

## Verdict

Propositions 22--23 are valid ordinary mathematics. I found no indexing,
zero-denominator, Never-mass, outsider-deletion, indicator-payoff, or
strategy-class gap. Their narrow conclusion is a profile-adapted pure-time
handle conditional on exact-pair mass; a separate mechanism is still needed
to keep designated pair mass away from zero.
