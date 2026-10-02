# Punishment-floor split at the structured stationary paid port

Author: `CODEX_HAHN`

## Status

**Exact ordinary mathematics; no new terminal consumer.** The final
Quit-now response of the tropical stationary port always produces a
source-attached singleton-anchor row whose owner already satisfies the exact
punishment-floor inequality. Under the no-uniform-payoff hypothesis, all of
its fixed exploitability is therefore carried by an outsider endpoint and
converges to a strict singleton-collision toggle.

This is a narrower and more literal description of the punishment-floor
deficit than a generic coordinatewise clip. It does not make the free-player
root Nash and does not turn the finite endpoint response graph into a
chronology. The independently reviewed one-stage root classification is
strictly stronger for the present source: without any floor hypothesis it
gives one uniform positive terminal-semantic debt drop. That drop is still
only one-shot because the child need not regenerate the stationary tropical
source.

## Setting

Let `I=Fin 4`. Let `tau_n` be the last-edge source from
`FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT.md`. Write its stationary
root as `x_n`, its prescribed payoff as `u_n`, and its complete behavioral
cap as `B_n`. Let `b` be the fixed last mover. Literal Quit at date zero is
an exact complete best response of `b`, with gain at least `gamma>0`.
Moreover

```text
x_(n,i) -> 0 for every i,
B_(n,b) -> s_b := r_b({b}),
B_(n,b)-u_(n,b) >= gamma.
```

Let `P_i` denote player `i`'s behavioral punishment value. Hard-residual
punishment normality gives `P_i <= s_i` for every player.

Define `r_n` from `x_n` by making `b` Quit surely and changing no other
date-zero marginal. Its tail can be left literally equal to `tau_n`; it is
unreached under prescribed play.

## 1. The anchor's punishment-floor inequality is automatic

Against the opponent row `x_(n,-b)`, write

```text
Q_n = b's payoff from Quit now,
H_n = b's one-row opponent-absorption contribution when b Continues,
c_n = probability every opponent Continues.
```

When `c_n<1`, the stationary Never value is `H_n/(1-c_n)`. Since Quit now is
the exact stationary cap at the source,

```text
H_n <= (1-c_n) Q_n.
```

Also the punishment value is below the cap against every opponent plan, so
`P_b <= Q_n`. Hence

```text
H_n + c_n P_b <= (1-c_n)Q_n + c_n Q_n = Q_n.       (1)
```

The degenerate case `c_n=1` has `H_n=0` and the same conclusion. Equation
(1) is exactly `QuittingSingletonBaseCertificate.owner_floor_balance` for
the sure-`b` root `r_n`.

Thus neither strict slack `P_b<s_b` nor tightness `P_b=s_b` is needed for
the owner coordinate. Exact cap attainment at the actual stationary source
already supplies the correct punishment-priced owner inequality.

## 2. The terminal gap is an outsider collision gap

The actual profile with first root `r_n` has zero debt in coordinate `b`:
the prescribed Quit-now payoff is the attained complete cap against the
unchanged opponents. Every outsider is screened by the sure quitter `b`, so
its complete behavioral cap is exactly the better of its two date-zero
endpoints.

Let `Gamma>0` be the terminal exploitability gap in the no-uniform branch.
Some outsider `p_n != b` therefore has debt at least `Gamma`. After a fixed
label subsequence, take `p_n=p`. Since every opponent hazard tends to zero,
the prescribed root tends to pure singleton `{b}`. Consequently

```text
r_p({b,p}) - r_p({b}) >= Gamma.                    (2)
```

For every sufficiently large finite `n`, Quit now is `p`'s exact endpoint
best response at `r_n`, with gain bounded below by (say) `Gamma/2`. Updating
`p` produces a literal terminal pair row containing the sure quitters `b`
and `p`. This is source-attached and fully behavioral, but it is a horizontal
same-date response, not a Nash--Bellman predecessor edge.

## 3. Why the two scalar floor branches do not close

### Strict branch: `P_b<s_b`

Coordinatewise clipping of `u_n` at the punishment floor leaves a fixed
singleton gap in coordinate `b`. The checked floor-clip theorem therefore
produces a fixed-charge exact root against the clipped vector.

The exact endpoints are nevertheless wrong for source re-entry:

```text
clipped tail v_n = max(P,u_n),
abstract predecessor w_n = F_(q_n)(v_n),
actual tail payoff = u_n.
```

No actual continuation profile with payoff `v_n` is supplied. Prefixing the
same root to `tau_n` replaces `v_n` by `u_n`, and the root need not remain
Nash. The clipping displacement in the other three coordinates can be order
one. Stationarity of `tau_n` does not identify `v_n` with `u_n`, and positive
reach does not repair this seam. Thus bounded exact-block hazard capacity
cannot be applied: there is not yet one source-matched exact block, let alone
a replayable sequence of them.

This is precisely the nonclaim in
`Chronology/Conditioned/Diffuse/FloorClip.lean`: its fixed-target root is not
a source Bellman predecessor or chronological splice.

### Tight branch: `P_b=s_b`

Here `u_(n,b) <= P_b-gamma+o(1)`, and the literal Quit-now response crosses
the owner's punishment floor by a fixed amount. Equation (1) shows that the
resulting sure-anchor root already has the correct owner-floor balance. But
the terminal gap forces the outsider violation (2), so the root is not a
`QuittingSingletonBaseCertificate`.

One may solve the complementary finite Boolean game and obtain an induced
Nash point for the outsiders. At that newly selected point, however, the
owner-floor inequality (1) need not survive: Quit now was cap-attaining at
the original opponent row, not at the reselected induced Nash row. Conversely,
following literal outsider endpoint improvements preserves ancestry but need
not terminate; the finite response graph can move through pair, singleton,
and larger coalition faces. Existing singleton-base dispatches record
exactly this owner-floor-versus-free-Nash alternative. They do not identify
the horizontal response path with an exact temporal return.

Thus the tight branch reduces to the source-attached singleton-collision
waist, not to terminal approximate Nash.

## 4. Interaction with exact root prefixing

The independently reviewed result
`CODEX_NEGATIVE_CERTIFICATE__STRUCTURED_PAID_SOURCE_ONE_STAGE_ROOT_CLASSIFICATION.md`
proves a stronger fact for this exact source. For all sufficiently large
`n`, every exact product root against the literal payoff `u_n` satisfies

```text
D(X_n) - D(Prefix(q,X_n)) >= delta                 (3)
```

for one common `delta>0`. Its cap-tail upgrade is sound: the only possible
zero-drop roots converge to pure Quit by `b`; the sure quitter screens all
outsiders, while `B_(n,b)->s_b` makes the sole unscreened owner defect vanish,
contradicting the terminal gap.

If `u_n` happens to be floor-safe, the checked marked exact-orbit adapter can
prefix roots literally to `tau_n`. Equation (3) then makes the first prefix a
fixed debt decrease. It does **not** force finite termination or violate the
bounded-capacity theorem. After the first prefix:

- total debt may remain strictly above `D_*`;
- the new payoff/cap pair need not be stationary;
- the cap pin `B_b->s_b` need not persist;
- the same fixed-drop theorem cannot be reapplied; and
- under no uniform payoff the remaining exact orbit may simply have summable
  absorption and retain the paid suffix with positive reach.

This is one fixed charged step followed by a finite-charge port, which is
compatible with bounded exact-block hazard capacity. Reusing (3) requires a
new theorem reconstructing the full structured source at its child. No such
re-entry follows from the current data.

## 5. The first exact-prefix child's reach dichotomy

Choose an exact product root `q_n` against `u_n` and form the literal child

```text
X'_n = q_n :: tau_n.
```

The reviewed classification gives the fixed debt drop (3). Let `c_n` be the
root's joint all-Continue probability.

### Positive inherited reach

If `liminf c_n>0`, copy the old Quit-now response of `b` after the new root,
leaving `b`'s root marginal unchanged. The two child profiles differ only
after joint all-Continue, so the exact payoff gain is

```text
c_n * (B_(n,b)-u_(n,b)).                              (4)
```

It has a fixed positive lower bound. Thus this arm gives an actual lower-debt
child with one exact Nash--Bellman predecessor root and a fixed inherited paid
tail. It is stronger than a bare semantic descendant. It is not renewable:
the child is no longer stationary, and its new cap coordinate need not
converge to `s_b`, so the structured one-stage classification cannot simply
be applied again.

### Vanishing inherited reach

Suppose `c_n->0` and pass to a root limit. If two different players are sure
quitters at the limit, every player's opponent-Continue mass tends to zero.
The exact block-action formula

```text
d_i(Prefix(q_n,X_n))
  <= OppCont_i(q_n) * d_i(X_n)
```

then makes every complete behavioral debt tend to zero, contradicting the
terminal gap. Hence the limit has exactly one sure quitter, say `k`.

For every `i!=k`, the same estimate makes the child debt tend to zero.
Therefore the terminal gap forces the child debt of `k` to stay at least
`Gamma`. Since source debts are at most `2M`,

```text
OppCont_k(q_n) >= Gamma/(2M)                           (5)
```

eventually. Exact root Nash at `u_n` implies that this positive child debt can
only come from the Continue-at-root endpoint evaluated with the tail cap.
Thus `k` has an actual complete best response which Continues at the new root
and then uses a cap-attaining response against `tau_n`. Stationarity of
`tau_n` reduces that tail response to literal Quit-now or Never.

So the zero-reach arm is not an unreachable-tail dead end: it produces a
source-attached sole-owner reset which reaches an exact endpoint-updated
stationary tail with the fixed opponent reach (5). But that tail update may
change an opponent of the original payer `b`, destroying `b`'s cap pin and
paid gain. This is the existing charged-solo reset/source-reentry waist, not
a closed return.

The dichotomy is therefore:

```text
positive reach -> fixed paid lower-debt child,
zero reach     -> uniformly reached sole-owner reset into an endpoint-updated tail.
```

Both arms retain literal ancestry. Neither arm reconstructs the original
structured source at its endpoint.

## 6. Regression boundary

The duplicated-cyclic zero-minimum examples show that a sure singleton
anchor can have:

- owner punishment equality `P_b=s_b`;
- a source payoff below that floor;
- an exact Quit-now repair crossing the floor; and
- a strict outsider singleton-collision response.

They also have `D_*=0` and an equilibrium. Hence the local anchor/floor/collision
data are mutually compatible. Positive global minimum enters the serious
classification through the collision-weighted debt-drop inequality, not by
making the singleton-base root locally self-contradictory.

## Checked declarations inspected

```text
exists_pos_gap_quittingPunishmentFloorClip_le_singleton_sub
singletonReward_neg_or_punishmentValue_eq_of_singleton_le
quittingPunishmentValue_le_stationaryUnilateralCap
QuittingSingletonBaseCertificate.exists_terminalNash_fixedTarget
QuittingPaidRowFloorSafeSource.exists_markedExactOrbit_alternative_of_witness
lowerDebt_mul_collisionMass_le_debtDrop_of_exact
singletonMass_mul_otherDebt_le_debtDrop_of_exact
isεAsymptoticNash_quittingRootThenContinuation_of_isεQuittingRootNash
```

## Exact remaining question

Can the child in (3), or the terminal pair row obtained from (2), be
reconstructed as a source of the same structured class with either a strict
finite rank decrease or a source-matched exact return seam? Without that
reconstruction, neither the punishment-floor split nor the fixed first debt
drop is renewable.
