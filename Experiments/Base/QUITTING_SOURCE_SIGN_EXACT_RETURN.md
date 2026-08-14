# Exact return and a collision-face sign

> **Update.** The literal packet-preserving source-return conjecture discussed
> here is now refuted. A positive actual-row packet has strictly positive
> root--tail complementarity residual, whereas an exact Nash--Bellman edge on
> the same root--tail fiber forces that residual to zero. See
> `Experiments/QUITTING_PACKET_PRESERVING_SOURCE_RETURN_NOGO.md` and
> `Experiments/quitting/PacketPreservingSourceReturnNoGo.lean`. The analytic
> return and collision-face sign below remain valid; what is no longer open is
> their coupling by an *unchanged exact* frontier row.

## Verdict

This experiment did not close the packet-preserving source-return gap. The
later no-go theorem shows that the literal formulation of that gap cannot be
closed: some root or tail datum must move, or the source residual must be
carried as an explicit non-Nash charge.
It proves two finite-dimensional facts and one exact coupling between them:

1. the punishment-normalized analytic endpoint translates to a literal
   period-one Nash--Bellman fixed point;
2. in a counterexample that fixed point is all-Continue, and the analytic
   construction exports a normalized singleton packet whose target is
   **exactly the same returned value**;
3. against that value, a newly constructed solo-owner row has a positive
   Quit-minus-Continue endpoint difference for a distinct receiver.

The constructed solo-owner row is not the all-Continue return root. Neither
it nor the analytic packet is identified with the base, reset source, reset
target, marked row, subsequence, coalition, or retained terminal law of the
stopping-law frontier. Thus this is a correct finite anchor and sign, not a
return of the current frontier packet.

The relevant code is
`Experiments/quitting/ExactNashBellmanRepairReturnTrichotomy.lean`.

## Exact stationary return

Let `q` and `W` be the endpoint root and value of the analytic germ of the
punishment-normalized auxiliary table, and translate `W` back to a value `v`
for the original table. The translation gives

```text
v = Successor(v,q),
q is exact Nash against v,
punishmentValue(i) <= v_i for every i.
```

The endpoint has three cases:

- `q` absorbs, and the period-one cycle compiles to a uniform-equilibrium
  payoff;
- `q` is all-Continue and the Never branch compiles;
- `q` is all-Continue and the analytic leading term exports a normalized
  singleton packet.

Consequently a counterexample occupies the third case. More strongly, every
punishment-floor-admissible stationary Nash--Bellman fixed return in a
counterexample is all-Continue, because an absorbing one already compiles.

The trichotomy is a sharpened packaging of the existing analytic waist. Its
new useful datum is the explicit stationary return object; it does not by
itself narrow the stopping-law frontier.

## Exact endpoint coupling

The original existential trichotomy erased a constructional equality: the
packet and the stationary return came from the same analytic endpoint, but the
theorem statement did not say so. The strengthened theorem

```text
exists_exactAllContinueReturn_and_targetMatchedPacket_of_no_uniformPayoff
```

retains

```text
packet.target = repair.value.
```

This is strict coupling progress inside the analytic certificate. It retains
the reward table, analytic germ, returned value, all-Continue root, packet
mass, packet inequalities, and packet target. It retains none of the
stopping-law packet's source/target chronology.

## Collision-face strategic sign

Let `delta > 0` be the terminal exploitability gap. Toggle instability gives
an owner `a` and a distinct receiver `b` with

```text
r_a({a}) >= delta,
g := r_b({a,b}) - r_b({a}) >= delta.
```

All-Continue is Nash against the returned value `v`, so

```text
s := v_b - r_b({b}) >= 0.
```

Set

```text
p := (s + g/2) / (s + g).
```

Then `1/2 <= p <= 1`. At the newly constructed product row where only `a`
Quits with probability `p`, player `b`'s endpoints against the same value `v`
are

```text
Quit:      p r_b({a,b}) + (1-p) r_b({b}),
Continue:  p r_b({a})   + (1-p) v_b,
```

and hence

```text
Quit - Continue = p g - (1-p) s = g/2 > 0.
```

The strengthened theorem

```text
exists_exactAllContinueReturn_targetMatchedPacket_collisionFaceSign
```

puts this sign, the returned value, and the target-matched analytic packet in
one existential statement. This sign is a legal one-row endpoint comparison
at the constructed solo-owner face. It is not a profitable deviation from
the all-Continue return root, because it changes the owner's row as well as
the receiver's action. It is also not a source-matched stopping-law deviation.

## Packet signs

In a counterexample the normalized packet has positive weighted surplus;
otherwise the existing singleton-mixture compiler gives a uniform-equilibrium
payoff. Therefore some supported reciprocal pair has positive total
singleton-delivery effect, and one orientation is positive.

These statements duplicate the already established strict packet-surplus and
reciprocal-pair consequences in the packet diagnostics. They are retained here
only to display the analytic packet beside the stationary return. A singleton
delivery comparison is not a same-row strategic gain: quitting at a
singleton-owner row creates a collision outcome.

## Recentring theorem

`Experiments/quitting/NearMinimumRecenteredStrategicSign.lean` is a direct
positive-gain corollary of the near-minimum actual-deviation rectangle. If a
whole-law reset with mixing weight `lambda` decreases mover debt by more than
the near-minimum error `epsilon`, then at the mixed profile some opponent has
an actual behavioral deviation with gain at least

```text
(lambda * moverGain - epsilon) / numberOfOpponents - eta > 0.
```

This is valid, but it changes the source to the mixed profile. It therefore
does not preserve the original frontier source, exact Nash--Bellman return,
marked row, terminal coalition, or retained law. It duplicates the strategic
content already present in the stronger affine-rectangle theorem and does not
close an open leaf.

## Exact missing implication

The source-return obligation is:

> Couple the stopping-law frontier packet to an exact Nash--Bellman return or
> another packet-preserving consumer, so that its legal marked-row gain (or
> negative-collision blocker balance) produces strict debt descent, a
> state-matched charged return, or terminal approximate equilibria at the
> original frontier source.

The analytic returned value plus collision-face sign does not imply this:
there is no equality between the analytic return and the frontier minimum,
reset source, reset target, or marked tail. Recentring also does not imply it,
because it deliberately replaces the source.

## Verification

Both active experiments compile with warnings treated as errors:

```text
lake env lean -DwarningAsError=true Experiments/quitting/ExactNashBellmanRepairReturnTrichotomy.lean
lake env lean -DwarningAsError=true Experiments/quitting/NearMinimumRecenteredStrategicSign.lean
```
