# Review of Proposition 6AJ

Reviewer: `CODEX_EULER`

Claim reviewed: in the prescribed-atom branch, finite frozen words with two
fixed near-killed labels may be concatenated first, so that their actual
suffixes give an exact chronology; the source semantics, unrestricted caps,
and the fixed-terminal atom then differ from the frozen data only by the
near-killed reach probability.

## Verdict

**VALID ordinary mathematics in the stated two-near-killed prescribed-arm
scope, with one provenance wording qualification.**  The construction gives
literal prefix provenance and exact suffix restart for the newly grafted
source/replacement pair.  It does not preserve equality with the original
complete frozen stopping laws beyond the cutoff, and should not be described
as doing so.

## Source and cap coupling

The infinite concatenation defines all tails simultaneously, and therefore

```text
Residual_allC^{L_n}(X_n)=X_(n+1)
```

without an inverse-limit choice.  The roots through `L_n` are exactly the
frozen roots.  For prescribed payoff, the frozen and grafted tails can differ
only after joint survival of the word, which is at most either labelled
survival and hence at most `epsilon_n`.

For player `i`'s unrestricted cap, fix an arbitrary behavioral deviation.
The changed tail can matter only if every opponent survives the word.  Of the
two distinct labels `first,second`, at least one is not `i`, remains governed
by its frozen marginal law through the word, and has survival at most
`epsilon_n`.  Product independence therefore gives opponent reach at most
`epsilon_n`, uniformly over the deviation.  The bounded-payoff coupling and
then the supremum yield exactly

```text
|Delta U_i| <= 2 M epsilon_n,
|Delta B_i| <= 2 M epsilon_n,
|Delta d_i| <= 4 M epsilon_n.
```

This correctly covers unrestricted stopping-time deviations, not only the
displayed product strategy.

## Replacement graft and atom

Replacing `first` by its old full-replacement hazards through `L_n` and by
`X_(n+1)(first)` afterward is one legal behavioral strategy.  All other
coordinates already have the `X_(n+1)` suffix, so all-Continue through the
word reaches exactly `X_(n+1)`.  The prefix roots of the updated profile are
the old full-replacement prefix roots.

The unchanged label `second` has prefix survival at most `epsilon_n` in both
the frozen and grafted full-replacement profiles.  Hence changing the endpoint
tail changes the probability of any fixed terminal coalition by at most
`epsilon_n`.  The analogous source-law change costs another
`epsilon_n`.  Multiplication by the fixed reward coordinate gives

```text
|Delta A_C| <= 2 M epsilon_n.
```

Thus the same fixed terminal orientation and a positive reduced charge survive
eventually.  The clock fields inside each word are pointwise unchanged, and
the restart to the next actual suffix is exact.

The precise provenance statement is:

```text
same frozen source/replacement prefix roots and labels through L_n,
followed by one common newly chosen actual suffix.
```

The complete source law `X_n` is not the original `P_n`, and the complete
replacement law is not the original `E_n`; their post-cutoff gauges were
deliberately replaced.  This does not affect the proposition's estimates or
its intended selected-chain conclusion.

## Scope

The three limitations are exact.

- For the rectangle cap of observer `second`, deviating deletes precisely the
  small second clock; the replaced `first` law can have order-one reach, so the
  two-label argument does not control that endpoint cap.
- The current cutoff theorem does not force both fixed labels into this
  near-killed branch at every chosen rank.
- Choosing one infinite tail gives a selected chronology, not a
  neighborhood-valued entrance rule, a radius bound, or arbitrary reached-port
  compatibility.

Accordingly Proposition 6AJ removes the later-rank splice problem only for
this prescribed two-near-killed selected chain.  It does not solve the
rectangle arm or Tier-I availability.

## Addendum: Proposition 6AK

**VALID ordinary mathematics.**  The two-word graft removes the provenance
qualification above in exactly the intended sense.

Concatenating the first-coordinate endpoint segments `V_n` defines one legal
behavioral strategy `T_n`.  Since the other coordinates of
`Y_n=update X_n first T_n` are the source-word coordinates, the prefix of
`Y_n` is exactly the frozen endpoint prefix, and shifting by `L_n` sends its
first coordinate to `T_(n+1)` and every other coordinate to `X_(n+1)`.
Therefore both identities

```text
Residual^{L_n}(X_n)=X_(n+1),
Residual^{L_n}(Y_n)=Y_(n+1)
```

hold literally.  This is one complete source/replacement pair whose two
fibers reconnect separately; it does not identify the endpoint tail with the
source tail.

The estimates do not change.  Source semantics and caps use the surviving
one-of-two-label argument from 6AJ.  At the endpoint, replacement changes
only `first`, so `second` still bounds all-Continue reach through the common
endpoint prefix by `epsilon_n`.  The source and endpoint fixed-terminal
probabilities therefore each move by at most `epsilon_n`, giving the same
`2M epsilon_n` prescribed-atom loss.

The strengthening remains conditional on selecting the prescribed arm with
both labels near-killed.  It gives a selected pair of exact infinite fibers,
not an arbitrary-entry neighborhood; and it does not control the rectangle
observer cap, where deviating by `second` removes the only unchanged small
endpoint label.

## Addendum: Corollary 6AL

**VALID conditional consumer.**  The extra hypothesis

```text
Reach(E_n,-second,L_n)<=epsilon_n
```

is exactly the port needed to compare unrestricted observer deviations at the
grafted endpoint.  For every fixed behavioral deviation of `second`, the
frozen and grafted endpoint payoff variables can differ only after all of its
opponents survive the common endpoint prefix.  The bound is uniform in the
deviation, so taking suprema gives `|Delta B_second|<=2M epsilon_n`.
Joint reach is smaller than observer-deleted reach, yielding the same bound
for prescribed payoff and hence the stated `4M epsilon_n` debt loss.

The rectangle sequence's fixed atom is a two-profile payoff-difference atom
after overriding `second` by the supplied pure time.  On the source side,
the distinct near-killed `first` label remains an opponent and bounds tail
reach; on the endpoint side the new deleted-port hypothesis does so.  Each
terminal probability moves by at most `epsilon_n`, hence the difference atom
moves by at most `2M epsilon_n`, not `4M epsilon_n`.  The pure time may vary
with rank because the coupling is pointwise and uniform for the chosen
override.

This proves vanishing endpoint observer debt and retention of the same
rectangle terminal orientation along the exact two-word suffix restart.  It
does not derive the deleted endpoint port from the checked two-label source
packet, and therefore does not close branch selection, arbitrary entry, or
Tier-I availability.
