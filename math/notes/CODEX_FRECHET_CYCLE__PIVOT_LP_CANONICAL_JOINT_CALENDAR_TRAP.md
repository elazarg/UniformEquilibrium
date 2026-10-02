# Canonical pivot-LP trap and an explicit joint opponent-calendar escape

Author: `CODEX_FRECHET_CYCLE`.

Status: exact ordinary-mathematics mechanism test, not independently reviewed
or Lean-checked. On the literal canonical table H below, a profile with full
regret `1/3` globally minimizes full regret against every complete one-player
replacement. An explicit independent two-opponent calendar change lowers
regret to `1/6`. Alternating optimal pivot repairs with unrestricted opponent
best replies can also cycle. No global convergence or universal joint-descent
claim is made. This note is not part of the geometric-compression export.

## 1. Question, assumptions, and existing-result boundary

The proposed operation holds three finite nonpivot laws fixed and replaces
the pivot to minimize the maximum of all four FULL terminal regrets. The
geometric-compression theorem in
[`GEOMETRIC_COMPRESSION.md`](../archive/GEOMETRIC_COMPRESSION.md), currently
under independent review, identifies the infimum of this problem with a
finite LP. We assume only that stated compression theorem when discussing
the general operation. Every local optimum and obstruction below is proved
directly for arbitrary complete pivot laws, so these particular calculations
do not depend on an unverified numerical LP or that general theorem.

All clocks are independent laws on `ℕ∪{Never}`. A nonempty first simultaneous
quitting coalition receives its displayed reward; Never by everyone pays
zero. An arbitrary behavioral deviation on the all-Continue live history
induces such a clock, so all finite times, Never, and unrestricted mixtures
are covered. Write `Uᵢ`, `Bᵢ`, `dᵢ=Bᵢ−Uᵢ`, and `E=maxᵢdᵢ` for actual
terminal payoffs, complete caps, debts, and maximum regret.

Before testing the LP, I read the complete
[`CODEX_SKEPTIC__GLOBAL_PORTFOLIO_REFINEMENT_AUDIT.md`](CODEX_SKEPTIC__GLOBAL_PORTFOLIO_REFINEMENT_AUDIT.md).
Its Section 4 already proves a generic complete-law coordinatewise trap,
separate convexity, and a two-coordinate escape for a different table with
negative own singletons. Those general facts are not rediscovered here.
The present contribution is the exact test of the new pivot operation on
the specified canonical cyclic fixture, including a concrete missing calendar
move and comparison with the modified-pivot fixture.

The complete [`JENSEN_1.md`](../archive/JENSEN_1.md) was also read. Its screened
restart and two-track returnable-charge arguments do not say that a sequence
of horizontal full responses decreases maximum regret. No Nash–Bellman
charge or in-game chronological return is inferred from the updates here.
The narrow source route remains the actual timing-menu row of
`docs/TOOLKIT.md`, through `quittingFiniteDeadlineTimingGame` and
`quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU` in
`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineTimingGame.lean`, inspected
in the earlier intake audit. Actual complete-clock comparisons are given
below rather than attributed to a finite-menu theorem's larger telescope.

## 2. Fully specified canonical table and the trap

For every nonempty `S⊆{0,1,2,3}`, define H by

```text
r₀(S) = 1+1[2∈S] if 0∈S, and 3·1[2∈S] otherwise;
r₁(S) = 1[0∈S] if 1∈S, and 3·1[0∈S]−1 otherwise;
r₂(S) = 1[1∈S] if 2∈S, and 3·1[1∈S]−1 otherwise;
r₃(S) = 0 if 3∈S, and 1 otherwise.
```

This specifies all fifteen coalition rows, has own singletons `(1,0,0,0)`,
and has reward bound three. It is the actual HILBERT canonical cyclic table,
not an abstract convex-function regression.

Let A be the product law

```text
player 0:  (1/3)Quit0 + (2/3)Never;
player 1:  Never;
player 2:  Quit0;
player 3:  Never.                                         (A)
```

Direct evaluation gives

```text
U(A)=(8/3,0,0,1),       B(A)=(3,1/3,0,1),
d(A)=(1/3,1/3,0,0),     E(A)=1/3.                         (AD)
```

**Theorem.** For every player i and every complete stopping law μᵢ,

```text
E(A[i←μᵢ]) ≥ 1/3.
```

Thus A is a positive coordinatewise GLOBAL minimum, not merely a local or
finite-support stationary point.

### Pivot replacement

Let `v=μ₀({0})`; all remaining mass may have any finite or Never timing.
Player two surely quits at zero. The pivot's cap is three, its payoff is
`3−v`, and its debt is v. Player one still plays Never and obtains `3v−1`,
while Quit0 gives v. Its debt is therefore at least `1−2v`. Hence

```text
E ≥ max(v,1−2v) ≥ 1/3.                                  (P0)
```

At `v=1/3` all remaining pivot timing choices in fact attain `E=1/3`:
player one's cap is `max(v,3v−1)`, player two's cap and payoff are zero,
and the dummy's cap and payoff are one. This solves the full pivot-only
LP exactly; no early, late, diffuse, or Never pivot replacement improves it.

### Player-one or dummy replacement

Player two still quits at zero. The pivot reward depends on the membership
of player two but not on player one or three. Its payoff stays `8/3` and
its cap stays three under either replacement. Thus its debt alone stays
`1/3`, proving the required lower bound for both changed coordinates.

### Player-two replacement

Let `a=μ₂({0})` and `q=μ₂(ℕ)`; these include arbitrary infinite finite-time
support. Against this law, the pivot's prescribed payoff in A is

```text
U₀ = (1/3)(1+a)+(2/3)·3q = 1/3+a/3+2q.
```

Its pure-time payoffs tend, as the finite date tends to infinity, to
`1+2q`: prior player-two absorption pays three, while the remaining Never
event gives the pivot its own singleton one. Individual late atom masses
tend to zero. Hence the literal full cap is at least `1+2q`, and

```text
d₀ ≥ 1+2q−(1/3+a/3+2q) = (2−a)/3 ≥ 1/3.                (P2)
```

The lower bound uses a supremum of actual finite deviations and does not
assume that its limiting payoff is attained at Never. This completes the
all-coordinate proof.

## 3. A genuinely joint independent calendar move

Keep the pivot and dummy laws of A. Change both opponents independently to

```text
player 1: (1/2)Quit1+(1/2)Never;
player 2: (1/2)Quit2+(1/2)Never.                           (J)
```

Call the resulting product law J. There is no public lottery and no
correlation between the two coins. Direct first-event evaluation yields

```text
U(J)=(5/6,1/2,1/3,5/6),
B(J)=(1,2/3,1/3,5/6),
d(J)=(1/6,1/6,0,0),       E(J)=1/6 < E(A).               (JD)
```

For complete verification, the pivot's pure finite-date values at dates
0,1,2 and after two are respectively `1,1,3/4,1`; Never pays `3/4`.
Player one's values at dates 0,1,2 and after two are
`1/3,2/3,2/3,1/3`; Never pays `1/3`. Player two's corresponding values
are `0,0,1/3,1/3`; Never pays `1/3`. Dummy Never pays `5/6`, while any
finite Quit forfeits some nonnegative active-absorption reward and cannot
exceed that value. This checks every finite date and Never, hence every
behavioral mixture, not just the displayed support.

One further legal pivot replacement, to `(1/2)Quit0+(1/2)Never`, gives

```text
U=(7/8,7/8,0,7/8),       B=(1,1,0,7/8),
d=(1/8,1/8,0,0).
```

Therefore the exact pivot LP at the opponent laws (J) has value at most
`1/8`. No claim is needed that this displayed upper bound is its optimum.

The obstruction at A is thus not absence of independent product directions
or failure of finite calendars. It is the restriction to one complete
coordinate at a time. In this example the improvement comes from changing
both opponents' stopping dates and masses together.

## 4. Exact LP repairs interleaved with full responses can cycle

There is also a lawful alternating-repair cycle entirely on
`{Quit0,Never}`. For brevity write x for the pivot's probability of Quit0
with remaining mass at Never, and write C and Q for Never and Quit0 by a
follower. Dummy remains Never.

Start from `(x;player1,player2)=(1/3;C,Q)=A`.

1. Player one's full best response is Q. At `(1/3;Q,Q)`, player two has
   debt one, independently of the pivot law, so the pivot LP has optimum
   one and may retain the current pivot.
2. Player two's full best response is C. Against `(Q,C)`, aggregate an
   arbitrary pivot law into `v=Pr(Quit0)`, `w=Pr(0<T₀<Never)`, and Never
   mass. Its relevant debts are exactly `1−v` for the pivot and `v+2w`
   for player one. The LP uniquely chooses `v=1/2,w=0`, with value `1/2`.
3. Player one's full best response is C. Against `(C,C)`, if q is the
   pivot's total finite mass, the pivot and player-two debts are `1−q`
   and q. The LP has optimum `1/2` and may retain the current pivot.
4. Player two's full best response is Q. Equation (P0) makes the next
   pivot repair choose `v=1/3`; assigning the rest to Never returns to A.

Every follower update is an unrestricted best response at the profile
where it is made, and every intervening pivot update solves the full-law
maximum-regret problem. These are allowed choices of minimizers; the claim
is not that every possible tie-breaking rule cycles. Their existence
refutes an unconditional descent claim for this alternating operation.
In particular own-payoff improvement by an opponent need not lower maximum
regret, and leaving the coordinatewise trap may initially raise that regret.

## 5. Comparison with the modified-pivot envelope counterfixture

Now change only the pivot reward to `r₀(S)=1` if `0∈S` and two otherwise,
keeping all other rows as above. This is the separate table in
[`CODEX_FRECHET_CYCLE__GLOBAL_ENVELOPE_ALL_SELECTOR_COUNTEREXAMPLE.md`](CODEX_FRECHET_CYCLE__GLOBAL_ENVELOPE_ALL_SELECTOR_COUNTEREXAMPLE.md).
Its positive-loss exact proper-pivot restricted Nash family does not imply
failure of the present unrestricted pivot LP.

Indeed follow the same first two opponent responses from A. They give
opponent laws `(Q,C)`. In this modified table, an arbitrary pivot law has
debts `v` and `v+2w` in coordinates zero and one. The pivot LP therefore
chooses `v=w=0`, namely Never, and attains zero. The resulting profile has
only player one quitting at zero, with exact full Nash value `(2,0,2,1)`.

Thus the LP-plus-response operation has an explicit successful route on
that counterfixture, although a legal cycle remains on H. The difference
is precisely that the LP is permitted to select pivot Never; the failed
global-envelope mechanism prohibited it. These two mechanisms should not
be identified.

## 6. Arithmetic checks and the remaining constructive question

The exact `Fraction` coalition-law evaluator in
`experiments/CODEX_SKEPTIC__FINITE_PORTFOLIO_REGRESSIONS.py` was read and
reused in memory. It independently reproduced (AD), (JD), the subsequent
`1/8` debt vector, the two cycle swap states, and the modified-table zero
state. The finite supports need only dates 0 through 3 plus Never to check
their caps, since every later finite date has the same value. These checks
corroborate the direct proof; the arbitrary-law lower bounds (P0) and (P2)
are mathematical arguments, not finite tests.

The open research question is now the genuinely joint one: select opponent
calendar moves such as (J) from the raw reward table and current laws, with
a rigorous progress guarantee or an exhaustive constructive alternative.
Separate convexity, a complete pivot LP, and repeated one-opponent full
responses do not supply that selection theorem. No auxiliary restriction
is added to the original approximate-menu question.
