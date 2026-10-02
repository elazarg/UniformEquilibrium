# Operational essentiality: exact finite passport and sharp deletion cap

**Owner:** CODEX_EULER  
**Status (2026-08-25):** independent audit complete; ordinary mathematics
PASS with the scope qualifications stated below.  This note audits a proposed
second-half argument.  It is not a Lean declaration and is not proposed for
export.

## Question audited

Let `I` be a nonempty finite player type, let `r` be a quitting reward table,
and let `gamma > 0`.  Assume

```text
HasTerminalExploitabilityGap r gamma.
```

Partition the players into a nonempty retained set `J` and a nonempty deleted
set `B = I \ J`.  Let `sigma` be a terminal `epsilon`-Nash profile of the
restricted game on `J`, where `epsilon < gamma`, and let `L_J sigma` be its
literal-Never lift: every player in `B` has zero Quit hazard at every live
history.

For `d in B`, put

```text
ell_d(J) = min({0} union { r_d(S) : empty != S subset J }),
P_d(J)   = max(0, r_d({d}) - ell_d(J)),
C_d(J)   = max({0} union
               { r_d(S union {d}) - r_d(S) : empty != S subset J }).
```

The proposed conclusions were:

1. an ambient gap witness at `L_J sigma` is necessarily a deleted player;
2. that player's profitable behavioral deviation has a finite deterministic
   Quit-time witness with the same weak gain `gamma`;
3. a positive-probability local coalition row has an unweighted insertion
   toggle at least `gamma`, hence
   `max(P_d(J), C_d(J)) >= gamma`; and
4. if retained absorption at every live row is at most `A`, then

```text
BR_d(L_J sigma) - U_d(L_J sigma)
  <= P_d(J) + min(1,A) * (C_d(J)-P_d(J))_+ .                 (SC)
```

Here `U_d(L_J sigma)` is the prescribed terminal payoff, which equals the
payoff of literal `Never` because `d` is deleted.

## Verdict

All four conclusions are valid, subject to four exact qualifications.

1. The retained set must be nonempty for the stated restricted game, and the
   displayed finite-minimum notation should either assume this or use the
   `insertMin 0` convention.  The deleted set is automatically nonempty when
   `J` is proper.
2. In (SC), state `0 <= A` (it is in fact forced by the nonvacuous row bound)
   and define the absorption coefficient precisely.  It may be either the
   conditional retained-row absorption `a_t`, or, more generally, it is enough
   to bound the source-weighted mass `w_t a_t`.  A bound on conditional
   absorption implies the latter because `w_t <= 1`.
3. The localization produces a **positive-probability row whose unweighted
   payoff toggle** is at least `gamma`.  It does not say that the
   probability-weighted chronological atom is at least `gamma`.
4. The selected deleted player may depend on `sigma` and on the ambient gap
   witness.  The argument does not give the passport simultaneously for every
   member of `B`.

With those readings there is no sign, conditioning, or quantifier failure.
The sharp bound is a genuine strengthening of the currently checked deletion
bound `P + A*C`.

## Proof audit

### 1. The gap witness is deleted

Apply `HasTerminalExploitabilityGap r gamma` to `L_J sigma`, obtaining a player
`d` and a complete behavioral deviation with gain at least `gamma`.

If `d` were retained, both its prescribed payoff and the payoff after its
arbitrary ambient behavioral deviation transport exactly to the restricted
game.  The restricted `epsilon`-Nash inequality would then bound this gain by
`epsilon`, contradicting `epsilon < gamma`.  Thus `d in B`.

This uses no quiet-lift consumer beyond deletion naturality.  The exact checked
declarations are:

- `quittingTerminalPayoff_liftDeletedProfile`;
- `quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation`;
- `quittingBestReplyValue_liftDeletedProfile` (a stronger supremum-level
  version, not needed for the witnessed argument); and
- `Function.update_liftDeletedProfile_never`,

all in
`UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean`.

### 2. Exact finite pure-time extraction

Fix the profitable deleted-player deviation.  Let `mu` be its complete
stopping law on `Option Nat`, and let

```text
V(none)   = payoff against the retained profile when d Never quits,
V(some t) = payoff when d deterministically quits at time t.
```

The checked stopping-law identity gives exactly

```text
payoff(deviation) = E_mu[V].                                (1)
```

It is important to use (1), not merely the checked epsilon-extremality theorem.
The latter by itself would yield only a pure gain `gamma-eta`.

Suppose no finite `t` has `V(some t) >= V(none)+gamma`.  The `none` value is
also strictly below this threshold because `gamma>0`.  Hence every value on
the support of `mu` is at most the threshold, and every one is in fact
strictly below it.  Choose one support atom `q`; it has positive mass.  Splitting
off that atom bounds the expectation by the threshold minus

```text
mu(q) * (V(none)+gamma-V(q)) > 0,
```

contradicting (1) and the ambient gain.  Consequently some **finite** `t` in
the stopping-law support satisfies

```text
V(some t)-V(none) >= gamma.                                 (2)
```

The exact source is
`quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
`UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`, together with
`quittingBehaviorStoppingLaw` in
`UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`.  The nearby
`exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` is only
epsilon-dominating and should not be cited as the sole justification for the
exact `gamma` constant.

### 3. Reached-source transport and coalition localization

Write `w_t` for the probability that all opponents of `d` survive dates
strictly before `t`, and write `N_{t+1}` for `d`'s literal-Never payoff from
the next live suffix.  Exact pure-time transport gives

```text
V(some t)-V(none) = w_t * Delta_t,                          (3)
```

where `Delta_t` is Quit-minus-Continue at the reached row.  The checked source
for (3) is
`quittingRootSequencePureTimeTerminalValue_some_sub_none_eq` in
`UniformEquilibrium/Quitting/Paths/OutsiderNeverGluing.lean`.

By (2), `w_t>0`.  Also `w_t<=1`, so `Delta_t>=gamma`.  Since every other
deleted player is literal Never, the opponent-coalition expansion of this row
uses only `S subset J`:

```text
Delta_t = sum_{S subset J} m_t(S) T_t(S),

T_t(empty) = r_d({d}) - N_{t+1},
T_t(S)     = r_d(S union {d}) - r_d(S)       (S nonempty),
```

with nonnegative product weights summing to one.  This is exactly the content
of `quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle` and its
Quit/Continue expansions in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticEndpointDefectPolarity.lean`.

Because this is a finite convex average, some coalition with `m_t(S)>0`
satisfies `T_t(S)>=gamma`.  If `S` is nonempty, then `C_d(J)>=gamma`.  If it is
empty, the literal-Never suffix is a probability/subprobability average of
`0` and rewards `r_d(S)` for nonempty `S subset J`; hence
`N_{t+1}>=ell_d(J)`.  Therefore

```text
r_d({d})-ell_d(J) >= r_d({d})-N_{t+1} >= gamma,
```

and `P_d(J)>=gamma`.  Thus

```text
max(P_d(J),C_d(J)) >= gamma.                                (4)
```

The strict positivity of `w_t m_t(S)` proves that this row is actually
reached under the pure-time deviation.  It does not lower-bound that product,
nor the weighted atom `w_t m_t(S)T_t(S)`, by `gamma`.

### 4. The sharpened all-behavior cap

At an arbitrary time `t`, let

```text
c_t = probability that every retained player Continues at the row,
a_t = 1-c_t.
```

Let `x_t=r_d({d})-N_{t+1}` and let `y_t` be the conditional average of the
nonempty-coalition join toggles (its value is irrelevant when `a_t=0`).  The
definitions of the floor and join cap give

```text
x_t <= P_d(J),        y_t <= C_d(J),
Delta_t <= c_t P_d(J) + a_t C_d(J)
         = P_d(J) + a_t(C_d(J)-P_d(J)).                     (5)
```

This sign is the delicate point: the coefficient of the solo premium is the
empty-row mass `c_t`, not one.  Formula (5) is why the positive-part bound is
sharper than adding the two worst cases separately.

Let `Abar=min(1,A)`, assume `0<=A`, and suppose `a_t<=A` for every time.  If
`C_d(J)<=P_d(J)`, (5) gives `Delta_t<=P_d(J)`.  If
`P_d(J)<=C_d(J)`, then `a_t<=Abar` and (5) gives

```text
Delta_t <= P_d(J)+Abar(C_d(J)-P_d(J)).
```

In either case, using `0<=w_t<=1` in (3) yields every finite pure-time gain at
most

```text
R = P_d(J)+Abar(C_d(J)-P_d(J))_+ .                          (6)
```

The Never gain is zero and `R>=0`.  Finally, the exact stopping-law expectation
(1) says that every complete behavioral deviation is an average of these
finite-time gains and the zero Never gain.  Thus every behavioral gain is at
most `R`, and taking the unrestricted best-response supremum proves (SC).

The same proof only needs `w_t a_t<=Abar`, so a uniform bound on the
source-weighted first-absorption mass is sufficient.  A conditional row bound
`a_t<=A` is a clean stronger hypothesis.

## Comparison with checked code

The proposal sits directly beside the checked quantitative block-deletion
theorem.  In
`UniformEquilibrium/Quitting/Classification/BlockDeletionInequality.lean`:

- `quittingBlockContinueFloor` (defined in
  `Classification/BlockDeletion.lean`) is exactly `ell_d(J)` when `B=I\J`;
- `quittingBlockJoinCap` is exactly `C_d(J)`;
- `quittingBlockDeletionExcessBound` is the older bound
  `P_d(J)+A*C_d(J)`;
- `quittingBestReplyValue_liftDeletedProfile_le_add_excessBound` and
  `exists_mem_gap_le_blockDeletionExcessBound` provide the current checked
  all-behavior and gap consumers.

The sharpened expression

```text
P + min(1,A)(C-P)_+
```

was not found in the narrowly searched deletion, path, or diagnostic subtree.
It is never larger than `P+A*C` for `0<=A<=1`, and is strictly smaller away
from the corresponding zero faces.  Its proof is an exact refinement of the
one-row convex accounting, not a new quiet-lift producer.

## Boundary checks

- `A=0`: every row is empty, so the cap is exactly `P`; join rewards are
  irrelevant.
- `A=1`: the cap is `max(P,C)`, which recovers the full-gap passport (4).
- `C<=P`: additional coalition absorption cannot increase the worst bound;
  the cap remains `P`.
- `P=0<C`: the cap is `min(1,A)C`, the expected atomic-join scaling.
- The formula remains valid when `J` has one player, including sure Quit rows
  and positive Never mass.  If `J` is empty, use the `insertMin/insertMax`
  conventions explicitly rather than an undefined inner minimum/maximum.

## Exact nonclaims

This theorem selects one deleted owner and one reached local reward row.  It
does not construct an ambient equilibrium, a Bellman edge, an admissible
return, a punishment continuation, a common owner across restricted profiles,
or a bounded compression of all players.  It only strengthens the static
quantitative deletion/passport interface.

