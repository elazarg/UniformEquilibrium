# Deterministic semantic-pair return: duplicate audit

Author: `CODEX_MINER`

## Status

**SUBSUMED; not a review, export, or formalization candidate.** The theorem
below is correct, but the broader duplicate search found a strictly sharper
checked route. `QuittingTerminalExploitabilityWitness.
exists_strictToggleClosedOrbit_from` already gives a closed literal coalition
toggle walk with gain at least `Gamma` on every edge. Interpret a coalition
`S` as the behavioral profile in which precisely `S` Quits at date zero and
all other players play Never. The checked pure-row cap formula says that a
strict membership toggle is the mover's exact best response, so its new debt
is zero. Recurrence of `S` returns the literal profile, complete law,
prescribed payoff, unrestricted cap, and semantic pair—not merely `U`.

Thus the reviewed Proposition 66 of
[`CODEX_CEDAR__PAID_ROW_REENTRY.md`](CODEX_CEDAR__PAID_ROW_REENTRY.md) and the
initial semantic-pair strengthening below are both weaker presentations of
the checked strict-toggle orbit. This note is retained as a durable duplicate
screen because the equivalence was obscured by “pure-time update” versus
“membership toggle” terminology.

## Exact checked subsumption

The relevant declarations are:

- `QuittingTerminalExploitabilityWitness.exists_strictToggleClosedOrbit_from`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StrictOrbit.lean`;
- `QuittingTerminalExploitabilityWitness.exists_closedImprovementWalk_multiple_four`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/FiniteInstability.lean`;
- `quittingStationaryUnilateralCap_pureSetRoot`, used explicitly in the
  independently reviewed Section 70 of
  `CODEX_CEDAR__PAID_ROW_REENTRY.md`; and
- on literal `Fin 4`, `exists_reachableStrictToggleSimpleCycle`, which gives
  a simple returned cycle of even length between four and sixteen.

At a pure coalition `S`, the current membership action and its toggle are the
only two outcomes available to one unilateral deviator before the date-zero
absorption. Therefore the strict checked inequality

```text
reward_S(i)+Gamma <= reward_(S triangle {i})(i)
```

makes the toggled action the exact unrestricted cap. Updating `i` to it gives
gain at least `Gamma` and new debt exactly zero. A repeated coalition is the
same date-zero/Never behavioral profile, so every semantic and law field
returns literally. These conclusions are stronger than `(2.2)--(2.3)` below.

## Self-contained question

Let `I` be a nonempty finite player set, let

```text
reward : {S : Finset I // S.Nonempty} -> Payoff I,
```

and assume

```text
HasTerminalExploitabilityGap reward Gamma,   Gamma>0.        (1.1)
```

For a behavioral profile `sigma`, write

```text
U(sigma) = its prescribed terminal payoff,
B_i(sigma) = sup over all unilateral behavioral replacements by i,
X(sigma) = (U(sigma),B(sigma)),
d_i(sigma) = B_i(sigma)-U_i(sigma).
```

A deterministic pure-time profile assigns every player one time in
`Option Nat`, with `none` meaning Never. Does the terminal gap force a
nonempty bounded unilateral-update loop whose endpoint **semantic pairs**
agree exactly?

## Initial theorem (valid but subsumed)

Put `n=card(I)`. For every `eta>0`, there are integers `r<s` and a sequence
of deterministic pure-time profiles

```text
sigma^r -> sigma^(r+1) -> ... -> sigma^s              (2.1)
```

of length at most `2^(n*(n+1))` such that

```text
X(sigma^s)=X(sigma^r).                                (2.2)
```

At every step `t`, exactly one player `m_t` changes its deterministic Quit
time (Never is allowed), and

```text
U_(m_t)(sigma^(t+1))-U_(m_t)(sigma^t) >= 3 Gamma/4,
d_(m_t)(sigma^(t+1)) <= min(eta,Gamma/4).              (2.3)
```

In particular both `U` and `B`, and hence the complete debt vector, return
exactly at the two endpoints. Profiles, stopping laws, and clocks need not
return.

## Lemma 1: deterministic opponents give finitely many cap values

Fix a player `i` and a deterministic pure-time profile `sigma`. Let `A_i`
be the coalition of opponents of `i` having the least finite Quit time. Put
`A_i=empty` if every opponent plays Never. Necessarily

```text
A_i subset I\{i}.                                     (3.1)
```

If `A_i=empty`, a deterministic pure-time replacement by `i` yields exactly
one of the two payoffs

```text
0, reward({i})_i.                                     (3.2)
```

If `A_i` is nonempty and its first time is positive, a replacement by `i`
can Quit before that time, at it, or after it (including Never). Its payoff
is respectively one of

```text
reward({i})_i,
reward(A_i union {i})_i,
reward(A_i)_i.                                        (3.3)
```

If the opponents' first time is zero, preemption is unavailable: the first
value in `(3.3)` must be deleted, while the tied and after/Never values are
still attained. Every alternative just listed is attained by a deterministic
time in its stated case.
The checked behavioral pure-time extremality theorem

```text
sSup_range_quittingTerminalPayoff_update_eq_pureTime
```

therefore gives

```text
B_i(sigma)=
  max(0,reward({i})_i)                                if A_i=empty,
  max(reward(A_i union {i})_i,reward(A_i)_i)          if time(A_i)=0,
  max(reward({i})_i,reward(A_i union {i})_i,
      reward(A_i)_i)                                  if time(A_i)>0.  (3.4)
```

There are `2^(n-1)-1` possible nonempty sets `A_i`, and only the two time
classes zero/positive matter. Consequently, as `sigma` ranges over all
deterministic pure-time profiles, `B_i(sigma)` belongs to a fixed finite set
of cardinality at most

```text
1+2(2^(n-1)-1) <= 2^n.                                (3.5)
```

This argument uses unrestricted behavioral deviations. Equality `(3.4)` is
not a stationary-cap substitution: the named checked theorem says that
deterministic pure times and Never have exactly the same supremum as all
behavioral replacements.

## Lemma 2: deterministic semantic pairs form a finite set

The prescribed outcome of a deterministic pure-time profile is either Never,
with payoff vector zero, or the reward of its nonempty first-quitter
coalition. Hence `U(sigma)` belongs to a fixed set of cardinality at most
`2^n`.

By Lemma 1, the best-response vector belongs to a product of `n` sets, each
of cardinality at most `2^n`. Thus the number of possible complete
semantic pairs is at most

```text
2^n * (2^n)^n = 2^(n*(n+1)).                          (4.1)
```

The bound is deliberately crude. Only finiteness is used below.

## Proof of the theorem

Let

```text
epsilon=min(eta,Gamma/4)>0.                            (5.1)
```

Start from the all-Never profile `sigma^0`. Given the deterministic
pure-time profile `sigma^t`, the terminal-gap assumption selects a player
`m_t` with

```text
d_(m_t)(sigma^t)>=Gamma.                              (5.2)
```

Behavioral pure-time extremality and the defining property of a supremum
select a deterministic Quit time or Never whose payoff is within `epsilon`
of `B_(m_t)(sigma^t)`. Replace only `m_t` by this pure time to obtain
`sigma^(t+1)`. The new profile is again deterministic pure-time. Because
the opponents of `m_t` did not change, its unrestricted behavioral cap did
not change. Therefore

```text
U_(m_t)(sigma^(t+1))-U_(m_t)(sigma^t)
  >= d_(m_t)(sigma^t)-epsilon
  >= Gamma-epsilon >= 3 Gamma/4,

d_(m_t)(sigma^(t+1))
  = B_(m_t)(sigma^t)-U_(m_t)(sigma^(t+1))
  <= epsilon <= min(eta,Gamma/4).                      (5.3)
```

Construct `2^(n*(n+1))` updates. Lemma 2 places the resulting
`2^(n*(n+1))+1` semantic pairs in a set of cardinality at most
`2^(n*(n+1))`.
Two indices `r<s` therefore have the same pair. Their intervening path is
nonempty, has the claimed length, and inherits `(5.3)` at every edge. This
proves `(2.1)--(2.3)`.

## Conjecture-facing verdict and combination audit

The initial finite-envelope observation appeared to close a cap seam in
reviewed Proposition 66:

```text
terminal gap
  -> finite deterministic unilateral-update loop
  -> exact return of prescribed payoff and unrestricted cap
  -> exact return of the complete terminal-semantic debt vector.  (6.1)
```

The checked strict-toggle orbit already closes that seam more strongly, so
there is **no new conjecture-facing change here**. The remaining seam is
categorically different: every arrow changes one player's complete strategy
and is not a root-then-continuation prefix. No root is asserted Nash against
the next prescribed payoff, no punishment floor is retained, and the
updater's payoff gain is not an absorption charge.

In particular, this does not eliminate the inert arm of
[`PAID_CAP_PORT_EXACT_TRICHOTOMY_AND_INERT_STALL.md`](../exports/PAID_CAP_PORT_EXACT_TRICHOTOMY_AND_INERT_STALL.md).
That arm is a literal cap-prefix chronology with zero charge and a fixed
semantic pair. The present loop has fixed positive unilateral-update gains
and an exact semantic-pair return, but no Bellman chronology. Existing
interfaces provide no connector identifying these two types of edge.

Likewise the small updater debt in `(2.3)` forces the terminal-gap debtor to
move to some other label after every update, but finite labels may cycle. It
does not define a strictly decreasing support or label rank.

## Source and corrected duplicate audit

The checked ingredients inspected were:

- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- the definitions of terminal payoff, behavioral best-response envelope,
  and terminal-semantic pair in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`; and
- the terminal-gap predicate and its carrier-wide debt consequence used by
  Proposition 66.

The reviewed source result is Proposition 66 and its review
[`CODEX_CEDAR__PAID_ROW_REENTRY__BY_CODEX_EULER__SECTION_66.md`](../feedback/CODEX_CEDAR__PAID_ROW_REENTRY__BY_CODEX_EULER__SECTION_66.md).
The first narrow phrase search found no theorem phrased as finiteness or
return of deterministic semantic pairs. That search was too syntactic. A
second search through membership toggles found the checked strict closed
orbit above. Its coalition recurrence, together with the pure-row cap
formula, entails exact `B` and pair recurrence immediately. This is a true
subsumption, not merely a nearby analogy.

No paper result is used.

## Boundary tests and nonclaims

1. If every opponent of `i` plays Never, the value zero in `(3.2)` is
   essential: player `i` may also play Never.
2. When several opponents tie at their first finite time, `A_i` is the whole
   tied coalition, not a selected member. If that time is zero there is no
   earlier date, so the singleton-preemption value must not enter the cap.
   The tied value is the literal simultaneous coalition `A_i union {i}`.
3. If `i` is the unique first quitter in the actual profile, its cap may
   depend on the opponents' later first coalition. This is exactly why the
   proof records `A_i` separately for every coordinate rather than trying to
   recover `B` from the actual first coalition alone.
4. Equality of semantic pairs does not imply equality of profiles or laws;
   absolute quitting times can differ arbitrarily.
5. No public correlation, bounded-deviation restriction, or stationarity
   assumption is used in the cap. Only the nominal profiles in the loop are
   deterministic pure-time.
6. No exact Nash--Bellman edge, floor-safe path, absorption charge, source-
   matched reset, support descent, or uniform-equilibrium payoff is produced.

## Lean handoff verdict

Do not formalize the finite-state proof below as a separate theorem merely to
recover semantic recurrence. If a convenient API corollary is ever needed,
prove directly that the pure profile associated to a returned strict-toggle
coalition has the same `quittingTerminalSemanticPair` at both endpoints and
that the selected mover's post-toggle debt is zero. The underlying orbit,
margin, and Fin4 length bound are already checked.
