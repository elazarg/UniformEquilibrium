# Marked summable port and solo near-return

Author: external `ChatGPT` contribution supplied by the user

Review:
[`CODEX_ROOT`](../feedback/CHATGPT_EXTERNAL__MARKED_SUMMABLE_PORT_SOLO_NEAR_RETURN__BY_CODEX_ROOT.md)

## Current status

The proposed composition with the cap-lifted port is invalid: it changes the
Nash annotation from the behavioral cap `B(x_t)` to the prescribed payoff
`U(x_t)`.  The equality-stratum and singleton-tight solo iteration theorems
require exact Nash against `U`, whereas the cap lift supplies exact Nash
against `B`.

A substantial conditional lemma survives.  For an exact **prescribed-payoff**
floor orbit which lies on the positive global minimum-debt fiber and carries a
positive signed root label, equality-stratum rigidity produces a
singleton-tight unique-debtor minimum face.  The checked controlled-solo
iteration then gives cumulative-charge payoff near-returns with fixed charge
floor `1`.

This does not yet consume the cap-lifted summable port.

## Valid prescribed-orbit lemma

Let `z_t=(u_t,b_t)` be terminal semantic carrier points with

```text
z_(t+1)=Prefix(q_t,z_t),
q_t exact Nash against u_t,
punishmentValue(i)<=u_t(i).
```

Assume every `z_t`, and the all-Continue limit `z∞`, has the same positive
globally minimal total debt `D*>0`.  Suppose a signed terminal-port certificate
gives one nonempty coalition `T` with positive cumulative root mass.  Then
some `q_t` has positive `T`-mass.

Minimum-fiber exact-prefix rigidity preserves every debt coordinate.  If `k`
is a positive debtor, every opponent of `k` must Continue surely at `q_t`.  A
second positive debtor would force `k` to Continue as well, contradicting the
positive absorption.  Thus `k` is the unique debtor and `T={k}`.  Positive
Quit mass of `k` and exact complementarity give

```text
u_t(k)=r_k({k}).
```

All later roots are solo-`k` or all Continue, so the limit remains
singleton-tight at `k`.  The limit therefore satisfies
`QuittingSingletonTightMinimumFace r z∞ k`.

Let `G_k` be the maximum positive outsider collision-over-solo gain and set

```text
kappa = D*/[2(D*+G_k)].
```

The checked rate criterion makes the solo-`k` root of rate `kappa` exact Nash
against the **prescribed** coordinate of every fixed-row iterate.  Starting
from the floor-safe `u∞`, exact Bellman predecessors preserve the punishment
floor.  Their prescribed values obey

```text
u^(n)=(1-kappa)^n u∞+[1-(1-kappa)^n]r({k}).
```

Choose `L=ceil(1/kappa)`.  Every length-`L` segment has cumulative charge at
least `1`, while the endpoint payoff difference tends to zero geometrically
as the segment is moved later.  Hence these segments form a
`QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily` with charge floor
`1`.

## Why it does not consume the cap lift

For the cap-lifted chronology from
[`PAID_CAP_LIFTED_SUMMABLE_PORT.md`](../exports/PAID_CAP_LIFTED_SUMMABLE_PORT.md),

```text
q_t is exact Nash against b_t=B(x_t),
```

not against `u_t=U(x_t)`.  Its exact debt law is the stronger identity

```text
d_(t+1,i)=JointContinue(q_t)d_(t,i).
```

Thus, if its positive total debt were constant, any positive root absorption
would immediately contradict global minimality.  The opponent-survival
equality-stratum analysis used to select a solo owner is not applicable to
these cap-Nash roots.

Conversely, the controlled solo root on the singleton-tight face is exact Nash
against `u∞` but has owner cap-Nash defect

```text
kappa*D*>0.
```

It therefore cannot be appended as an exact edge of the cap orbit.  The cap
port supplies `punishmentValue<=b∞`; it does not supply
`punishmentValue<=u∞`, which is needed for the proposed prescribed-payoff
near-return path.

## Debt-descent boundary

If `D∞>D*`, merely naming the global minimizer `z*` as a lower-debt carrier
point is not a source-matched path or a well-founded descent from the marked
port.  If `D0>D∞`, a finite incoming prefix has a strict real-valued debt
drop, but a single strict decrease in a real number is not by itself a
well-founded producer.  A usable descent arm still needs a finite rank,
uniform decrement, or a direct consumer.

## Source correspondence inspected

- `quittingTerminalSemanticDebt_prefix_eq_of_minimum`,
  `quittingTerminalSemantic_minimum_positiveDebt_face`, and
  `quittingTerminalSemantic_minimum_positiveDebt_singleton_eq_of_quit_pos` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean` all
  assume exact Nash against the prescribed coordinate `pair.1`.
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`
  assumes exact Nash against the cap `pair.2` and scales debt by joint Continue
  mass.
- `isZeroQuittingRootNash_solo_of_singletonTightMinimumFace`,
  `quittingSingletonTightMinimumFace_iterate`, and the geometric prescribed
  iterate results in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSingletonTightMinimumFaceIteration.lean`
  concern prescribed-payoff Nash.  The same file explicitly computes the
  positive owner cap defect.
- `QuittingPunishmentFloorInfiniteOrbit.SummableChargeSignedTerminalPort` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorSummablePortLabel.lean`
  labels the roots and value annotations of a supplied exact floor orbit; it
  does not convert cap annotations into prescribed annotations.

## Missing connector

To use the surviving solo near-return lemma on the cap-lifted port, one would
need an additional theorem producing a prescribed-payoff floor port and an
exact prescribed-Nash charged root from the cap port, or else consuming the
cap/prescribed surcharge directly.  No such theorem is supplied here.

