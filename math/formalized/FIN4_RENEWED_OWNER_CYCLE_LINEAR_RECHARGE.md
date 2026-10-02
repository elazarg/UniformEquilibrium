# Renewed reset cycles require linear horizontal debt and capacity recharge

Author: CODEX_HAHN

Independent reviews:
[CODEX_GROMOV](../feedback/CODEX_HAHN__RENEWED_OWNER_CYCLE_CAPACITY_RECHARGE_LEDGER__BY_CODEX_GROMOV.md)
and
[CODEX_SPINOZA](../feedback/CODEX_HAHN__RENEWED_OWNER_CYCLE_CAPACITY_RECHARGE_LEDGER__BY_CODEX_SPINOZA.md).

The reviewed source note is frozen at SHA-256
`cd1a964b4c77073ade6a9ff371d294f1e3169a55883de39ea78320c9e21a54ef`.
Both reviews record a PASS on that exact revision.

## Exact statement

Let `I=Fin 4`, let `r` be a bounded quitting reward table, and assume the
game has no uniform-equilibrium payoff.  For an actual behavioral profile
`sigma`, write `Sem(sigma)=(U(sigma),B(sigma))`,

```
d_i(sigma)=B_i(sigma)-U_i(sigma),
D(sigma)=sum_i d_i(sigma).
```

Suppose an infinite source-renewal construction supplies, for every phase
`m`:

1. an actual source profile `S_m`;
2. a finite exact Nash--Bellman predecessor word above `S_m`, with actual
   endpoint profile `P_m` and joint-absorption charge `A_m`;
3. constants `a0,c0>0`, independent of `m`, such that

   ```
   A_m >= a0,
   Q_m:=D(S_m)-D(P_m) >= c0;
   ```

4. a horizontal cap child `S_(m+1)` obtained from `P_m` by changing only one
   player `b_m` to a complete cap-attaining behavioral response; and
5. literal source coherence: this same `S_(m+1)` is the tail source of the
   next exact predecessor word.

Let

```
H_m = D(S_(m+1))-D(P_m)
```

be the signed horizontal debt injection, and let

```
g_m=U_(b_m)(S_(m+1))-U_(b_m)(P_m) >= 0
```

be the cap-response gain.  Then for every `N`,

```
sum_(m<N) H_m
  = sum_(m<N) Q_m + D(S_N)-D(S_0),
```

and therefore

```
sum_(m<N) H_m >= N*c0-O(1).
```

Since changing `b_m`'s own strategy leaves its unrestricted cap unchanged,

```
H_m = -g_m
      + sum_(i != b_m)(d_i(S_(m+1))-d_i(P_m)).
```

Consequently,

```
sum_(m<N) sum_(i != b_m)
  (d_i(S_(m+1))-d_i(P_m))
  >= N*c0 + sum_(m<N) g_m-O(1).
```

There is also a strictly stronger global-capacity statement.  Let `R_box` be
the charged relation on the full canonical boxed Nash--Bellman state space:
an edge is an exact predecessor edge and its charge is the joint absorption
of its product root.  The checked Fin4 bounded exact-block hazard-capacity
theorem implies that all finite `R_box` paths have one common charge bound.
Therefore

```
Phi(s)=sup { charge(path) : path is a finite R_box path starting at s }
```

is a bounded potential on all boxed states.

Decorate every source payoff `U(S_m)` by the all-Continue simplex root,
calling the state `s_m`.  Decorate `P_m` by the last actual root of its exact
word, calling the endpoint `p_m`.  Reuse the identical all-Continue-decorated
state `s_(m+1)` as both the horizontal target and the next vertical source.
Put

```
K_m=Phi(s_(m+1))-Phi(p_m).
```

Then

```
sum_(m<N) K_m >= N*a0-O(1).
```

Thus every infinite renewed cycle must replenish both terminal-semantic debt
and global exact-prefix capacity at a positive linear rate across its
horizontal cap-child seams.

## Conjecture-facing change

The reviewed late-reset theorem makes the infinite-reset positive-survival
branch renewable with uniform exact debt and absorption expenditure in every
phase.  Finiteness of the owner labels alone does not consume the resulting
loop.

This packet identifies the exact global toll paid by such a loop.  It cannot
hide the repeated vertical expenditures in bounded source debt or bounded
exact-block capacity: the horizontal cap updates must inject linear
cross-player debt and restore linear global predecessor capacity.  A
hypothetical counterexample in this branch is therefore a quantitative
recharge machine, not merely a cycle of owner labels.

The packet is a necessary-recharge theorem, not a consumer.  It does not
bound the horizontal recharge, turn a cap response into an exact predecessor
edge, or produce a uniform-equilibrium payoff.

## Definitions and assumptions

The exact predecessor word uses independent product roots.  Every root is
exact Nash for its Boolean action against the literal payoff of the current
tail, and its Bellman predecessor is the literal payoff after prefixing that
root.  Its charge is actual joint absorption, not a payoff gain.

The cap response in the horizontal step optimizes over the complete
unilateral behavioral strategy class, including arbitrary finite stopping
times and Never.  It is an actual profile replacement, but it is not assumed
to be a Nash--Bellman predecessor edge.

The full boxed relation has no punishment-floor premise.  A boxed state
contains a payoff vector in the canonical reward box and one stored simplex
root.  The root decoration at the tail of an exact edge is irrelevant to the
edge equations, but this packet does not rely on that fact: it chooses one
all-Continue decoration for each source and reuses it literally in the next
phase.

The notation `O(1)` denotes a constant independent of `N`.  It is valid
because actual terminal-semantic debts are uniformly bounded and `Phi` is a
bounded real-valued potential.

## Source correspondence

The renewable phase input is the reviewed result
`FIN4_LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE`, whose source note is
frozen at SHA-256
`c38983e9a73e14005838181d46f51602dafc02763df71a369920e58e1da2d2bb`.

The full boxed charged relation is
`quittingPunishmentFloorBoxChargedRelation` in
`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorChargedRelation.lean`.
Despite its historical name, this relation is defined before restriction to
the punishment-floor subtype.  The generic bounded budget-to-go potential is
`ChargedRelation.value`, and its edge decrement is
`ChargedRelation.value_tgt_add_charge_le_value_src`, in
`MathUE/ChargedPathBudget.lean`.

The common path bound follows from
`finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
in
`UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`:
every full-box path decodes to a finite exact bounded Nash--Bellman block, and
joint absorption at each root is at most the sum of its four marginal
hazards.

The coordinate debt expenditure and arbitrary re-entry debt ledger are in
[FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE.md](FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE.md).
The new content here is the global full-box capacity construction and its
application to a source-coherent infinite sequence of renewed phases.

## Proof

### 1. Debt telescope

By definition,

```
D(S_(m+1))-D(S_m)
  = [D(S_(m+1))-D(P_m)]-[D(S_m)-D(P_m)]
  = H_m-Q_m.
```

Summing from `m=0` to `N-1` telescopes the left side and gives the first
displayed identity.  Since `Q_m>=c0` and the endpoint debts remain in a fixed
bounded interval, the linear lower bound follows.

Only player `b_m` changes strategy in the horizontal step.  Its opponents
are identical, so its complete behavioral cap is identical at `P_m` and
`S_(m+1)`.  Its payoff rises by `g_m`, hence its debt falls by exactly `g_m`.
Separating this coordinate in `H_m` proves the cross-player identity and its
summed lower bound.

### 2. A bounded potential on the full boxed relation

Every finite path in `R_box` is a finite list of literal exact
Nash--Bellman predecessor roots in the canonical bounded payoff box.  The
no-uniform-payoff capacity theorem bounds the sum of all their marginal
hazards.  At each root,

```
joint absorption <= sum_i marginal hazard_i.
```

Thus the set of charges of all finite `R_box` paths is bounded above.  The
generic charged-relation theorem makes `Phi` bounded above and below and
gives, for each phase path,

```
Phi(p_m)+A_m <= Phi(s_m).
```

Insert

```
K_m=Phi(s_(m+1))-Phi(p_m)
```

and rearrange:

```
A_m <= Phi(s_m)-Phi(s_(m+1))+K_m.
```

The chosen decoration of `s_(m+1)` is the same on both occurrences.  Summing
therefore telescopes the `Phi` terms.  Boundedness of `Phi` and `A_m>=a0`
give the asserted linear lower bound on the sum of the `K_m`.

## Boundary tests

### The floor-admissible potential cannot be substituted

A late reset source lies below its singleton wall in one coordinate.
Punishment normality only says that the punishment floor is at most the
singleton reward; it does not imply that this source remains above the
punishment floor.  The proof therefore uses the full boxed relation and the
global exact-block capacity bound, not the floor-admissible subtype.

### Decorations must be coherent

The potential is formally evaluated on boxed states, not bare payoff vectors.
Choosing unrelated decorations on the two occurrences of `S_(m+1)` would
break the telescope.  The explicit all-Continue decoration is reused as the
next vertical source, so no root-independence theorem is assumed.

### Finite owner labels do not close the loop

An infinite sequence of owners contains a repeated finite label pattern, but
the associated semantic source states need not repeat.  Strict horizontal
best-response cycles can rotate debt among coordinates in a bounded payoff
region.  Equations above force linear recharge but do not forbid it.

### Horizontal recharge is not physical charge

`H_m` is signed terminal-semantic debt displacement and `K_m` is displacement
of the abstract global capacity potential.  Neither is joint root absorption,
and neither horizontal cap replacement is thereby made an admissible edge.

## Adapter and consumer

The reviewed renewable late-reset theorem supplies `S_m`, the fixed constants
`a0,c0`, and the literal exact prefix in each phase.  Its cap-child
construction supplies the one-player horizontal response and the identical
actual source used in the next phase.  Hence it supplies all hypotheses of
this packet on any indefinitely renewed positive-survival branch.

The output is an obstruction certificate: such a branch has linear
cross-player debt recharge and linear full-box capacity recharge.  No current
consumer accepts those quantities as chronological charge.  A downstream
completion still needs a telescoping bound on horizontal recharge, an exact
predecessor realization of the horizontal seam, a nonreplenishable finite
rank, or a quitting-specific contradiction to the recharge machine.

## Lean handoff

Useful declarations are:

```
quittingFullBoxHasFiniteBudget_of_finFourHazardCapacity

quittingFullBoxCapacityPotential

renewedCapClock_debtRechargeLedger

renewedCapClock_capacityRechargeLedger
```

The first theorem should decode a full-box charged path into a finite exact
Nash--Bellman block and compare joint absorption with total marginal hazard.
The capacity potential should be the generic `ChargedRelation.value`; no new
choice principle or regularity assertion is needed.

The sequence structure for the last two theorems should store the exact
vertical path, its actual terminal-semantic source and endpoint, the
one-player cap child, and an equality identifying that child with the next
phase's source.  This equality is what makes both telescopes literal.

## Scope and nonclaims

This packet proves ordinary mathematics and assigns no Lean seal to the new
full-box adapter or recharge theorems.

It does not prove continuity, semicontinuity, or monotonicity of `Phi` across
a horizontal strategy replacement.  It does not turn owner-label recurrence
into semantic recurrence, horizontal cap gains into absorption charge, or
the concatenation of vertical and horizontal steps into a Nash--Bellman path.
It does not prove a uniform-equilibrium payoff or a counterexample.
