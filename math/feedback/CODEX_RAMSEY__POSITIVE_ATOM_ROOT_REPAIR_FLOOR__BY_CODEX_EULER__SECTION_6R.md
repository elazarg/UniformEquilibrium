# Focused review of Corollary 6R

Reviewer: `CODEX_EULER`

## Verdict

**VALID checked first-mover provenance alignment, with the simultaneous-face
scope correction below.**  The circulation packet may first
select its two positive clock movers, after which the supplied-mover atom
theorem is applied to the already fixed first mover.  The two eventual rank
statements intersect without a subsequence or source mismatch.

## Quantifiers and provenance

`exists_frozenRadialLiteralFiniteProfilePackets` returns fixed data

```text
weight, first, second, kappa
```

with `first!=second`, both weights positive, and eventually a literal finite
packet for

```text
frontier.frozenRadialPacketProfile rank weight ...
```

whose two clock labels are exactly `first.1,second.1` and whose exposure scale
is `kappa*frontier.scale rank`.

After `first` has been selected,
`exists_quantitativeStrongVanishingDebtAtomAlternative_of_mover frontier first`
returns fixed `observer,charge`, with `observer!=first.1`, and eventually an
atom alternative whose arguments are literally

```text
frontier.source rank,
first.1,
observer,
frontier.replacement first rank.
```

Both conclusions are `Eventually atTop` on the original rank, so their
intersection is eventually true at every common sufficiently late rank; no
independently chosen subsequences are being identified.

The marginal provenance claim is also exact.
`frozenRadialPacketProfile_apply` identifies the packet's first marginal with
the outer mixture of `frontier.source rank first.1` and
`frozenRadialInnerResetStrategy rank first`.  By definition in
`Frozen/RadialScaling.lean`, that inner reset is the complete-law mixture of
the same source marginal with `frontier.replacement first rank` at the actual
frontier scale.  Thus the packet and atom theorem use the same source and the
same full-replacement law, although the packet marginal retains the additional
outer circulation weight.

## Scope

The corollary aligns one atom mover's original source/replacement/rank data
with one of the two frozen clock labels.  The atom alternative is proved in
the original whole-source environment `frontier.source rank`.  The full
radial packet simultaneously applies positive outer resets to the other
active movers as well.  Nothing in the two eventual statements transports
the first-mover atom inequality through those other simultaneous resets.
Thus the atom alternative must not be asserted for the full packet profile;
the narrowed provenance statement remains valid.

It also does not prove that the atom observer is the second clock label, preserve a
fixed terminal or pure-time atom orientation through conditioning, or produce
an actual-source successor on which the same packet can restart.  Those
nonclaims are stated accurately.  In particular this is a frozen-source
quantifier/provenance repair, not the missing chronological producer.
