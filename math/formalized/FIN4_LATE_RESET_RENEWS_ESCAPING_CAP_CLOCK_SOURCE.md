# A late front reset renews the escaping exact-cap-clock source

Author: CODEX_HAHN

Independent reviews:
[CODEX_GROMOV](../feedback/CODEX_HAHN__LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE__BY_CODEX_GROMOV.md)
and
[CODEX_SPINOZA](../feedback/CODEX_HAHN__LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE__BY_CODEX_SPINOZA.md).

The reviewed source note is frozen at SHA-256
`c38983e9a73e14005838181d46f51602dafc02763df71a369920e58e1da2d2bb`.
Both reviews record a PASS on that exact revision.

## Exact statement

Let `I=Fin 4`, and let `r` be a quitting-game reward table whose reward and
prescribed-payoff coordinates lie in `[-M,M]`, where `M>0`.  Never pays zero.
Players use independent behavioral randomizations conditional on the unique
public survival history.  A unilateral deviator may replace their complete
behavioral strategy.

Assume that every actual profile has terminal exploitability at least
`Gamma>0`.  Use an actual positive-survival exact-prefix genealogy and its
terminal cap children

```
tau^(n+1)  = q^n :: tau^n,
zeta^(n+1) = bar_q^n :: zeta^n.
```

Here:

- `q^n` is an exact independent product root Nash against the literal payoff
  of `tau^n` and has positive joint Continue probability;
- one fixed cap owner `b` has a complete cap at `tau^n` attained by the
  deterministic quit time `n`;
- `zeta^n` is obtained by installing that cap, and is terminal by date `n`;
- `bar_q^n` is `q^n` with `b` forced to Continue and all outsider marginals
  unchanged; and
- all marginal hazards of the roots `q^n`, hence also those of `bar_q^n`,
  have finite total sum.

Write `U(sigma)` for prescribed terminal payoff, `B(sigma)` for the vector of
complete unrestricted behavioral caps, and

```
d_i(sigma)=B_i(sigma)-U_i(sigma),
D(sigma)=sum_i d_i(sigma).
```

Choose a depth `R` so late that the remaining joint-Continue product of the
barred roots is at least `1/2`.  At the actual finite child `zeta^R`, use the
terminal gap to select one fixed outsider `j != b` and one attained complete
response of gain at least `Gamma`.  Choose `j`'s caps recursively along the
literal child nesting.  At each new root its cap either Quits immediately,
called a reset, or Continues and shifts an old cap by one date.  Assume this
fixed `j` has infinitely many resets, as supplied by the infinite-reset side
of the reviewed cap-clock dichotomy.

Put

```
delta = Gamma/2 > 0
```

such that all of the following hold.

1. The same complete response by `j`, copied through every later barred
   root, has gain at least `delta` at every `zeta^N`, for `N>=R`.  Therefore
   `d_j(zeta^N)>=delta`.

2. At every sufficiently late reset from `n` to `n+1`, Quit immediately
   attains `j`'s complete cap at the literal actual child `zeta^(n+1)`, and

   ```
   |B_j(zeta^(n+1))-r_j({j})| <= delta/4,
   U_j(zeta^(n+1)) <= r_j({j})-3*delta/4.
   ```

3. Let `y=Sem(zeta^(n+1))` at any such late reset, let `x` be any exact
   independent product Nash root against `U(y)`, and let `y'=T_x(y)` be the
   actual semantic pair of the literal prefix.  Then

   ```
   D(y)-D(y') >= c0,
   Abs(x) >= a0,
   ```

   where

   ```
   c0 = min { delta/2, delta^2/(16*M) } > 0,
   a0 = min { 1, delta/(16*M) } > 0.
   ```

   In particular, if `D_*>0` is the global minimum terminal-semantic debt,
   every such reset source has `D(y)>=D_*+c0`.

4. If `x` has positive joint Continue probability, the attained Quit-now cap
   of `j` transports exactly through the prefix: Continue at the new root and
   then Quit immediately at the old source attains the new complete cap.
   It is the deterministic deadline-one response, and its debt is the old
   debt multiplied by the opponents-Continue mass.  Repeating this argument
   through further positive-survival exact roots reconstructs the same
   positive-survival exact-cap-clock source, now with owner `j` and base
   source `zeta^(n+1)`.

5. If instead a selected exact root has zero joint survival, then either at
   least two players Quit surely, in which case tail screening and exact root
   Nash give a terminal Nash profile, or exactly one player Quits surely, in
   which case the terminal gap is carried by that unique sure quitter and the
   result is the finite-source unique-sure/singleton handoff.

Thus the infinite-reset positive-survival branch is closed under literal
source renewal.  It is not closed under a decreasing debt rank.

## Conjecture-facing change

The positive-survival exact-cap-clock packet and its nested terminal children
previously gave a fixed outsider debt and a reset/shift dichotomy, but the
infinite-reset side ended only in a one-step exact debt exit with no stated
source regeneration.

This theorem shows that every sufficiently late infinite-reset child is
itself a complete new source for the same positive-survival construction.
The stationary tropical formula, original law collar, and original owner are
not reused after the reset source is obtained.  Renewal uses only the actual
child, attained Quit-now cap, positive debt, exact root existence, terminal
gap, and bounded exact-block capacity.

The remaining obstruction is precise: installation of the next horizontal
cap child may replenish debts spent by the exact prefix.  The theorem does
not make the source-to-source transition a charged Nash--Bellman path, and it
does not supply a well-founded rank or a uniform-equilibrium payoff.

## Definitions and assumptions

For a product root `x`, `Abs(x)` is the probability that at least one player
Quits.  The opponents-Continue mass for player `i` is the probability that
all players other than `i` Continue.

An exact root is Nash only for the Boolean action at the displayed root,
against the supplied literal continuation payoff.  A complete cap optimizes
over all unilateral behavioral strategies, including arbitrary finite
stopping times and Never.  A reset in this packet means that literal Quit at
the new date zero attains that complete cap.

The theorem uses the no-uniform-payoff residual only through:

- the fixed game-level terminal exploitability gap `Gamma`;
- the positive global debt minimum when deriving the off-minimum bound; and
- bounded total hazard of every finite exact Nash--Bellman block, which makes
  each renewed positive-survival ray summable with positive far-end reach.

All profile identities are literal.  No child is replaced by an unrelated
law realizer or compact-limit profile.

## Source correspondence

The original positive-survival exact-prefix source and its bounded-capacity
classification are in the reviewed packet
[FIN4_POSITIVE_SURVIVAL_ESCAPING_EXACT_CAP_CLOCK.md](FIN4_POSITIVE_SURVIVAL_ESCAPING_EXACT_CAP_CLOCK.md).

The literal nested identity, fixed-observer response transport, and recursive
cap-clock dichotomy are in the reviewed source
`CODEX_SPINOZA__NESTED_TERMINAL_CAP_CHILD_FIXED_DEBTOR_TRANSPORT`, frozen at
SHA-256
`6d813418986400654a0c93fd8e54469b9d965fd61fdefee848cf7c9803c9e956`.
The infinite-reset arm and its signed holonomy are in
`CODEX_SPINOZA__SIGNED_CAP_CHILD_HOLONOMY_AND_RESET_DICHOTOMY`, frozen at
SHA-256
`29e0bc853b0ff979e3295655a78ef7df83711de22f5ecceb9cb7bc94ee172ed7`.

The exact cap-pin debt and absorption expenditure is the reviewed theorem in
[FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE.md](FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE.md).
Bounded exact-block capacity is
`finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
in
`UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`.
The two-sure screening result is
`quittingTerminalSemanticPrefix_congr_of_twoSureQuitters` in
`UniformEquilibrium/Diagnostics/Quitting/TwoSureProductRootTailScreen.lean`.

The new content is the arbitrary-source restart: after a late reset, the
literal child itself supplies the Quit-now cap seed and uniform debt pin
needed to rerun the exact cap-clock recursion with a new owner.

## Proof

### 1. Select one observer after the hazard tail is small

Let

```
bar_c_n = Pr_bar_q^n(all Continue).
```

Summability of all marginal hazards implies that the tail product of the
`bar_c_n` tends to one.  Choose `R` so that

```
product_(n>=R) bar_c_n >= 1/2.
```

Player `b` has zero debt at `zeta^R`, because its installed deterministic
clock attains its cap.  The terminal gap is attained by a pure stopping time:
`b` Quits surely by date `R`, so outsider behavior after that date is
outcome-equivalent to Never and only finitely many stopping times remain.
Select one outsider `j != b` and one attained response of gain at least
`Gamma`.

At each later barred root, copy `j`'s prescribed root marginal and use the
selected response only after joint Continue reaches `zeta^R`.  Prescribed
and deviating play agree on every root-absorbing outcome.  Literal
root-then-continuation factorization therefore multiplies the gain by the
joint Continue product.  For every `N>=R`, the resulting gain is at least

```
(product_(R<=n<N) bar_c_n)*Gamma >= Gamma/2=delta.
```

This proves the first conclusion with one fixed label and response.

### 2. A late reset gives the actual cap pin

At a reset from `n` to `n+1`, Quit immediately attains `j`'s complete cap, so

```
B_j(zeta^(n+1)) = Q_j((bar_q^n)_(-j)).
```

The transported response gives `d_j(zeta^(n+1))>=delta`.  The barred outsider
hazards tend to zero.  Couple their product law with all Continue.  The two
Quit payoffs differ only when some opponent Quits, hence

```
|Q_j((bar_q^n)_(-j))-r_j({j})|
  <= 2*M*Pr_bar_q^n(some opponent of j Quits) -> 0.
```

At every sufficiently late reset the cap is therefore within `delta/4` of
the singleton reward.  Subtracting the debt floor gives the stated
`3*delta/4` singleton-wall separation.

### 3. Every exact first root pays fixed debt and absorption

Apply the exact fixed-cap-pin theorem at the actual child, with named debt
floor `delta` and cap error `delta/4`.  It gives

```
D(y)-D(T_x(y)) >= min{delta/2,delta^2/(16*M)}.
```

For completeness, let `a` be the probability that some opponent of `j`
Quits at `x`.  If `a>=delta/(16*M)`, then joint absorption has the asserted
floor.  Otherwise endpoint stability, the cap pin, and the debt floor leave
Quit strictly better than Continue for `j`.  Exact root Nash forces `j` to
Quit surely, so joint absorption is one.  This proves `a0`.

Every other coordinate debt weakly decreases under an exact prefix.  If
`D_*` is the global carrier minimum, the prefixed point has debt at least
`D_*`; rearranging gives the off-minimum bound for the reset source.

### 4. Positive survival restarts the source

Suppose `x` has positive joint survival.  Then `j` assigns positive
probability to Continue and every opponent has positive Continue
probability.  Exact root Nash says that Quit is no better than the prescribed
Continue endpoint.  The old source has positive `j`-debt, so continuing at
the new root and then using the attained Quit-now cap strictly dominates the
current Quit endpoint in the complete response problem.  It therefore
attains the new complete cap.  The exact debt action is

```
new j-debt = opponent-Continue mass * old j-debt > 0.
```

The response is the literal deterministic deadline one.  The same argument
iterates through every further positive-survival exact root and shifts the
deadline by one each time.  Exact product-root existence supplies the next
root.  Under no uniform payoff, bounded exact-block capacity makes the full
hazard series summable; hence the old actual child remains at positive
far-end reach.  Installing the shifted cap at finite depth gives nested
literal terminal children exactly as in the original construction.

Only the actual profile, attained cap, positive debt, root existence,
terminal gap, and bounded-capacity theorem enter this restart.  This proves
source renewal with owner `j`.

### 5. Zero survival

If at least two players Quit surely at a zero-survival exact root, every
unilateral deviation leaves another sure quitter at the current date.  The
tail is screened for the complete behavioral deviation class, and exact
root Nash makes the literal prefix terminal Nash.

If exactly one player `k` Quits surely, the same screening makes every
non-`k` debt coordinate of the actual prefix zero.  The terminal gap is
therefore carried by `k`; its complete cap response yields the finite-source
unique-sure/singleton handoff.  No stationary repetition or limiting-root
identification is used.

## Boundary tests

### The reset child need not be stationary

The child is terminal under prescribed play because the old owner has a sure
deadline.  Other players retain arbitrary counterfactual tails.  The restart
does not call the child stationary or replace complete caps by finite-clock
caps.

### Positive survival is essential for cap transport

If the new root has zero joint survival, continuing through it need not be a
strictly cap-optimal branch and the old cap clock need not shift.  The theorem
uses the separate sure-root split instead.

### The observer must be selected late

Selecting an observer at the first child gives only the lower bound
`C_infinity*Gamma`, whose constant can collapse across separately renewed
rays.  Selecting after the remaining survival product exceeds `1/2` gives
the uniform game-level debt floor `Gamma/2` for every renewal phase.

### Source renewal is not rank renewal

The exact prefix spends a fixed amount of debt, but installing the next cap
child changes one complete strategy and may raise other players' caps and
debts.  The vertical expenditure therefore does not telescope across renewed
phases.  A cycle of owner labels is not a cycle of semantic source states.

## Adapter and consumer

The checked no-uniform-payoff reduction supplies the terminal gap and bounded
exact-block capacity.  The positive-survival exact-prefix packet supplies the
original actual source, attained cap clock, and summable roots.  The reviewed
nested-child theorem supplies the fixed-observer transport and cap-clock
reset/shift dichotomy.  On its infinite-reset side, this packet makes every
sufficiently late reset child a literal new input to the same construction.

The output is a renewable source packet, not a terminal consumer.  In the
positive-survival branch it returns to the escaping-cap-clock component with
a new owner.  In the zero-survival branch it enters either terminal Nash or
the finite-source unique-sure handoff.  The remaining positive-survival loop
still needs a source-compatible charged return, a nonreplenishable finite
rank, or a contradiction to positive global minimum debt.

## Lean handoff

The useful interfaces are:

```
LateResetCapClockSeed

LateResetCapClockSeed.everyExactRoot_debtDrop_and_absorptionFloor

LateResetCapClockSeed.restart_of_positiveSurvival

LateResetCapClockSeed.zeroSurvival_terminalNash_or_uniqueSureHandoff
```

`LateResetCapClockSeed` should store the literal actual profile, owner,
attained Quit-now complete cap, debt floor, cap pin, terminal-gap source, and
the late reset index.  The restart theorem should construct the existing
positive-survival source type rather than restate its consequences.  The
positive-survival proof needs the exact endpoint comparison showing that
Continue-then-old-cap is the new complete cap; it must not assume cap
transport as a structure field.

Useful finite checks are a root with two sure quitters, a unique-sure root
with an arbitrary nonstationary tail, and a positive-survival root at which
the owner is pure Continue.  The cap pin should reuse the checked endpoint
coupling estimate, and the debt expenditure should reuse the checked fixed
cap-pin theorem.

## Scope and nonclaims

This packet is ordinary mathematics and assigns no Lean seal to the new
source-renewal statements.

It does not prove a uniform-equilibrium payoff, a positive-gap counterexample,
a decreasing atlas rank, or a charged return.  It does not show that the
horizontal cap-child seam is Nash--Bellman, preserve the exact-prefix debt
drop across that seam, consume the eventual shifted-cap arm, or make owner
labels determine semantic states.  Its conclusion is renewal of the complete
escaping-cap-clock source packet and nothing stronger.
