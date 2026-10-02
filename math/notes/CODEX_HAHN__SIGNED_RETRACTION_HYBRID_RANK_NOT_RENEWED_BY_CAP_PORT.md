# Signed retraction lowers a horizontal hybrid index, not the cap-port source rank

**Owner:** `CODEX_HAHN`  
**Status:** exact ordinary mathematics; targeted rank no-go, not Lean-checked

## Question

Let `S` be a retained actual minimum-source profile and let `X` be an actual
off-minimum profile.  Fix an order of the four players and form the literal
coordinate hybrids

```text
S = Z^0, Z^1, Z^2, Z^3, Z^4 = X,
```

where `Z^(r+1)` replaces one further complete strategy of `S` by the
corresponding strategy of `X`.  The signed source-retraction theorem selects
an oriented edge

```text
A = Z^(r+1)  --->  B = Z^r
```

and produces a quantitative paid cap port based at the actual profile `A`.
Can the number of `X`-coordinates be used as a renewable rank by recursively
processing `B`?

The answer at the current interface is **no**.  The horizontal replacement
does lower that number, but it is not the child transition of the cap port.
The exact cap-prefix construction retains `A`, rather than `B`, as its
literal conditional tail.  Moreover the finite horizontal path terminates at
the already retained hard minimum source `S`, not at an impossible rank-zero
state.

## 1. The exact typing obstruction

Let `W` be any finite root word prefixed by the paid-cap construction to `A`,
and write

```text
P = W star A.
```

On the event that every root in `W` selects all Continue, the continuation
profile of `P` is literally `A`.  Thus:

1. if this event has positive probability, conditioning on it recovers `A`
   exactly, including every coordinate already copied from `X`;
2. if it has probability zero, neither `A` nor the paid row contained in its
   suffix is reached through the word.

In neither case does prefixing install `B`.  In particular, on the inert arm
of the exact paid-cap trichotomy all roots are all Continue, the event has
probability one, and every finite descendant has the same complete
terminal-semantic pair as `A`.

This is independent of debt estimates.  It follows from the literal
root-then-continuation definition before any compactification.

The mismatch is even stronger in the nonmover-leakage arm of signed
retraction.  There the retraction edge changes player `i`, but the extracted
paid row can belong to an observer `j != i`.  The profile `B` is not asserted
to be a response target of `j` at all.  Hence there is no candidate source
transition from the paid observer's port to the lower hybrid.

## 2. A Fin4 exact inert regression

Take four players.  Give every reward coordinate value zero except that
player `0` receives `-1` from every coalition containing `0`.  All-Never pays
zero as usual.

Let `S` be the all-Never profile and let `X` differ only in that player `0`
Quits at date `1`.  Then

```text
U(S) = 0,       D(S) = 0,
U_0(X) = -1,    B_0(X) = 0,    d_0(X) = 1,
d_j(X) = 0 for j != 0.
```

Thus the one-coordinate reverse hybrid edge `X ---> S` pays player `0`
exactly one and lowers the horizontal hybrid count from one to zero.

At the cap `B(X)=0`, all Continue is an exact product root: player `0`
strictly prefers Continue to quitting alone, and every other player is
indifferent.  Select all Continue at every cap-prefix stage.  Every resulting
profile is just a finite string of all-Continue roots followed by the literal
tail `X`; its terminal-semantic pair equals that of `X`, and its paid
Quit-at-1 versus Never comparison merely shifts to a later date.  Hence the
exact cap-port orbit is inert and its old-tail hybrid count stays one at every
finite depth.  It never becomes the rank-zero profile `S`.

This regression has `D_*=0` and is not a counterexample to uniform-equilibrium
existence.  Its role is exact and narrower: it falsifies the proposed
identification of the horizontal replacement edge with the cap-prefix child
transition.  The identification is structural, so assuming `D_*>0` does not
make it valid.

## 3. Why direct recursive processing of `B` is not a consumer

One may ignore the cap-port descendant, declare `B` to be a new actual
profile, and continue along the remaining predetermined hybrids whenever `B`
is still off minimum.  This reaches `S` after at most four replacements.
That finite construction is valid, but it proves none of the required
conclusions:

- the unresolved quantitative-debt or inert output of the port based at `A`
  was not transitioned to `B`;
- paid rows selected at successive hybrids do not compose into one
  Nash--Bellman chronology;
- in the leakage arm their observers need not equal the replaced coordinate;
  and
- the terminal horizontal rank-zero object is `S`, the original positive
  minimum hard source, which is allowed and still has the full terminal gap.

Therefore the hybrid count is a bound on a counterfactual comparison path,
not a well-founded rank whose zero state contradicts `D_*>0`.

## 4. Exact missing adapter

A genuine hybrid-rank theorem would need an additional operation taking an
unresolved cap-port output based at `A` and returning a complete source based
at `B`, while preserving the paid causal passport and all hypotheses needed
for the next step.  For positive-survival prefixes this operation must alter
the actually reached conditional tail from `A` to `B`; for zero-survival
prefixes it must reconstruct the lost tail provenance.  Neither operation is
a field of the signed retraction or paid-cap trichotomy.

Equivalently, it would need a new theorem making the horizontal response
installation an admissible temporal/source transition.  Merely causalizing
`B` afresh does not suffice, because that discards the incoming port edge and
resets the ancestry whose rank was supposed to decrease.

## Sources inspected

- `formalized/FIN4_SIGNED_SOURCE_RETRACTION_AND_NEAR_MINIMUM_RESPONSE_CYCLE_CONTRACTION.md`;
- `questions/FIN4_QUANTITATIVE_PAID_PORT_CONSUMER.md`;
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidRowExactPortAlternative.lean`; and
- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`.

## Surviving next question

Can one use a global account over the horizontal replacement itself—rather
than treating it as the cap-port child—to pay for changing the actually
reached tail from `A` to `B`?  Such an account must control the cap and
outsider-debt recharge caused by the complete-strategy replacement.  A local
gain-controls-leakage inequality is already false, so any positive result
must use the retained positive minimum, complete source law, or bounded
exact-block capacity.
