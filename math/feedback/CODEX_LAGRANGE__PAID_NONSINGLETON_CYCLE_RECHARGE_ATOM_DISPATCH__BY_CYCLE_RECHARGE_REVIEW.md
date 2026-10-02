# Export-gate review of the paid nonsingleton cycle recharge packet

Reviewer: `CYCLE_RECHARGE_REVIEW`

Verdict: **ACCEPT with two wording corrections incorporated in the export.**
There is no mathematical objection to the recharge lemma, its checked atom
dispatch, or its same-law minimum-target regeneration.  The result materially
contracts the live source-attached period `4/6/8` leaf, although it does not
turn the horizontal cycle into a chronology or close uniform existence.

## Literal cycle and source adapter

The explicit Fin4 constant requires the deterministic selector at every
nonsingleton coalition `C` to maximize

```text
h_i(C) = max (r_i(C triangle {i}) - r_i(C)) 0.
```

This is stronger than merely following an arbitrary strict selector, but it
is available from the maintained forced-pair row.  The stationary pure-`C`
profile is an actual profile, and
`quittingTerminalSemanticDebt_pureSetRoot_eq`
(`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`) gives

```text
sum_i h_i(C) >= D_*.
```

Consequently the maximum has size at least `D_*/4`.  If its toggle reaches a
singleton, this is the maintained paid-singleton arm.  Otherwise deterministic
iteration remains in the eleven nonsingleton Fin4 vertices.  Its eventual
simple cycle is bipartite, uses at most the four odd vertices (the triples),
and cannot have period two because the two strict inequalities would be
opposite comparisons for the same player.  Hence its period is exactly one of
`4, 6, 8`.  An independent enumeration of the induced nonsingleton Fin4 cube
also returns precisely these possible simple-cycle lengths.

For each maintained outer row, define every cycle sibling with
`quittingLiteralPureRootProfile` over the same
`crossTailProfile` and marked date.  The definitions in
`Research/Quitting/SameStageEndpointMonodromy.lean` then give literally:

* equality of the final and initial complete behavioral profiles;
* a `Function.update` presentation of each edge, changing only its mover;
* equality with the common source at every off-mark date, hence the same full
  post-mark spine and the same pre-mark behavior;
* the same live mass at the marked date; and
* marked coalition mass equal to that live mass.

The exact terminal-law decomposition into the common pre-mark sublaw plus
`L_n delta_(C_k)` is therefore valid.  It includes no post-mark mass because
the displayed nonsingleton pure row absorbs surely.

The maintained source supplies this input without the maximal-prefix ray.
For `FinFourOwnerCompressedMinimumReturnForcedPairPacket`, take the common
base profile to be

```text
packet.base.crossTailProfile (packet.subsequence n)
```

and the marked date to be the stored endpoint stage.  The forced target is
the literal pure pair over that base (by the definitions of
`pureSingletonProfile`, `targetProfile`, and
`quittingLiteralPureRootProfile_update_eq_routed`), while
`lambda_lt_forcedPairStageMass` and
`forcedPair_stageMass_eq_liveMass` give the required fixed live-mass floor.
The selected maximum-toggle orbit depends only on the fixed reward table and
the fixed pair, so it is the same finite orbit at every outer index.  The
already frozen payer is not needed; the cycle construction honestly
reselects a maximum toggle.

## Exact debt ledger and constants

If the `k`-th mover is `p_k` and its whole-profile payoff gain is `g_(n,k)`,
then changing only `p_k` leaves that player's unrestricted best-response cap
unchanged.  Therefore

```text
d_(n,k+1,p_k) - d_(n,k,p_k) = -g_(n,k).
```

There is no missing positive-part or cap-truncation term.  This is exactly
`quittingTerminalSemanticDebt_literalOneDateProfile_eq_sub_gain` in
`Research/Quitting/SameStageEndpointMonodromy.lean`; the same principle is
also exposed by
`quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiveWeightedCollisionTransfer.lean`).

All spectator cap changes remain inside their displayed debt increments.
Literal profile return telescopes every debt coordinate to zero.  Hence

```text
sum_k sum_(j != p_k) Delta_(n,k,j) = sum_k g_(n,k).
```

There are exactly `3K` spectator-edge pairs.  With

```text
g_(n,k) >= g_0 = lambda * D_* / 4,
```

one pair has rise at least

```text
c = g_0 / 3 = lambda * D_* / 12.
```

Signed spectator changes cause no issue.  The factor `1/3` is sharp for the
abstract four-player ledger: on a four-edge cycle with each player moving
once, give the mover increment `-g` and each of the three spectators
increment `g/3`; every coordinate then telescopes exactly and no spectator
rise exceeds `g/3`.

## Checked atom decoder

After freezing one edge and one distinct observer on a strict subsequence,
the target profile is literally

```text
Function.update source mover targetStrategy.
```

Thus the hypotheses of
`hasVanishingDebtAtomAlternative_of_endpointDebtRise`
(`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/VanishingDebtAtomAlternative.lean`)
match without translation.  With

```text
q = 7*c/8 = 7*lambda*D_*/96,
e_n = (q/8)/(n+1),
```

we have `0 < e_n`, `e_n -> 0`, and

```text
e_n <= q/8 = 7*c/64 <= c/8.
```

The conclusion is exactly

```text
HasQuittingStoppingLawVanishingDebtAtomAlternative
  reward source mover observer targetStrategy q e_n.
```

Its prescribed arm has a scaled payoff-difference atom at least `q/2`; its
rectangle arm has a scaled rectangle atom at least `q/4` and observer debt at
most `e_n`.  It is not a `QuittingVanishingDebtAtomAccess` and makes no
chronological-successor claim.

## Same-law minimum-target regeneration

Compactify the actual endpoint semantic/law pairs along the same retained
subsequence.  If their limit is `(Y, nu)`, continuity gives the observer
debt rise at least `c`.  At every prelimit endpoint the routed pure coalition
has stage mass equal to `L_n >= lambda`, and
`quittingStageCoalitionMass_le_terminalOutcomeMass`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPureTimeRectangleDisintegration.lean`)
therefore gives

```text
nu(routed coalition) >= lambda.
```

If `D(Y)=D_*`, the exact endpoint joint point, its particular law `nu`, and
that particular routed coalition meet every hypothesis of
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`).
Together with the unchanged hard residual, this fills every field of
`FinFourMinimumAtomProducer` (`Research/Quitting/FinFourProducerAtlas/Source.lean`).
The law atom itself has mass at least `lambda`.

Two phrases in the source note require the following precise reading and are
corrected in the export:

1. causalization does not guarantee that its individually selected marked
   stage has mass at least `lambda`; it guarantees positive selected-stage
   mass and eventually more than half of `nu(T)` across its retained finite
   window;
2. the compact point retains the actualizing source/endpoint sequence and
   its law atom, not an attained behavioral profile with a literal common
   tail.

Neither correction changes the regenerated producer.  If `D(Y) != D_*`,
carrier minimality makes the endpoint strictly off minimum.  No inspected
theorem returns that arm to the minimum fibre.

## Conjecture-facing assessment

The former live leaf was an unconsumed source-attached paid nonsingleton
cycle.  This theorem replaces it, without a new source hypothesis, by:

```text
fixed positive spectator recharge
  -> checked fixed-charge atom alternative
  -> minimum same-law source regeneration or strict off-minimum endpoint.
```

That is a strict reduction and merits export.  The remaining fence is also
strict: the horizontal source and endpoint are alternative same-date
profiles, not successive histories; the decoded atom need not be either
cycle coalition; and a freshly causalized minimum chronology need not begin
with the incoming paid edge.  Accordingly the result supplies neither a
chronological debt-shadowing certificate, an admissible return, a renewable
rank drop, nor a uniform-equilibrium payoff.

No unresolved mathematical, constant, source-adapter, behavioral-cap, or
same-law objection remains.
