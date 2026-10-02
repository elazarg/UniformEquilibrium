# Round 7 Feedback on Quadratic Pair Localization

Reviewer: `CODEX_NOETHER`

Reviewed note: `notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`

Scope: Propositions 24--25 only. This review is separate from the cubic
Propositions 22--23 review and does not assert a counterexample game.

Status: `VALID_ORDINARY_MATHEMATICS`

## Exact pair atoms

For a designated pair `D={u,v}`, the date atom

```text
x_t=P(T_u=T_v=t and T_j>t for every j outside D)
```

is exactly the probability that `D` is the strict first-quitter coalition at
date `t`. Thus `a=sum_t x_t`, including arbitrary Never atoms in the
individual clocks; no mass at infinity contributes to `a`.

Independence gives

```text
x_t=P(T_u=t) P(T_v=t) product_(j outside D)P(T_j>t).
```

The outside-player product is in `[0,1]`, so countable Cauchy--Schwarz yields

```text
sum_t sqrt(x_t)
 <= sum_t sqrt(P(T_u=t)P(T_v=t))
 <= sqrt(P(T_u<infinity)P(T_v<infinity))
 <= 1.
```

This remains valid when either player has a Never atom or when extra players
have arbitrary countable laws.

If `a>0`, let `M=sup_t x_t`. Since the summable nonnegative sequence `x_t`
tends to zero, its positive supremum is attained at a finite index. Then

```text
a=sum_t sqrt(x_t)sqrt(x_t)
 <=sqrt(M) sum_t sqrt(x_t)
 <=sqrt(M),
```

so `M>=a^2`. If `a=0`, every atom is zero and the existence statement is
trivial. The uniform-on-`N` pair example gives `a=1/N` and
`x_t=1/N^2=a^2`, confirming sharpness of the exponent and constant.

## Outsider deletion

At a maximizing date with `a>0`, `x_t>0`. Therefore the factor
`P(T_k>t)` for a distinct outsider `k` is positive. Replacing `k`'s clock by
deterministic quitting at `t` leaves every other opponent law unchanged and
removes precisely that survival factor. The probability that the opponents'
strict first coalition is exactly `D` at `t` becomes

```text
x_t/P(T_k>t) >= x_t >= a^2.
```

This indexing is correct: outsiders other than `k` must be strictly later,
whereas `k` joins the pair at the selected date. No conditional hazard or
zero-denominator convention is needed in this sharper proof.

## Exact-triple adapter

For the coordinate

```text
r(S)_k=1 iff S=D union {k}, and 0 otherwise,
```

the prescribed payoff is exactly the probability `L` of the exact-triple
first coalition. Under the deterministic-time replacement, the opponent
event from Proposition 24 makes the full first coalition exactly
`D union {k}` with probability at least `a^2`; all complementary deviation
payoffs are zero. Thus the deviation gain is at least `a^2-L`.

At `a=0`, the claimed lower bound is `-L`; it follows because every payoff in
this coordinate is nonnegative, so some replacement has payoff at least zero
(equivalently, exploitability is nonnegative). If `k` belongs to the other
designated pair, the exact triple is neither exact pair and hence
`L<=ell`. Terminal `epsilon`-Nash gives
`ell>=L>=a^2-epsilon` with the stated orientation.

The deterministic date replaces the player's whole behavioral strategy, so
the lower bound applies against unrestricted behavioral deviations. The
argument assumes only the standard independence of private planned quit
times along the unique live history; it introduces no public correlation.

## Verdict

Propositions 24--25 are valid ordinary mathematics. The countable
Cauchy--Schwarz bound, maximum attainment, Never boundary, outsider deletion,
exact-coalition indicator, `a=0` case, and behavioral scope all check. The
result improves the conditional pair localization modulus from cubic to the
sharp quadratic `a^2`, but it still supplies no mechanism forcing `a>0` (or a
uniform positive lower bound on two designated pair masses).
