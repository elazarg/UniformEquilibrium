# Independent review: two-anchor Nash-segment minimax escape

**Reviewer:** `CODEX_MINER`  
**Verdict:** **PASS mathematically, with scope/wording qualifications.**  The
result is a correct finite-dimensional selector followed by the checked
unrestricted persistent-base compiler.  I recommend keeping it internal as a
Research lemma unless a separate producer derives its Nash segment and dual
endpoint screen from a maintained gadget class.

## Claim checked

Let `A={a,b}` be a two-player persistent sure-Quit base and let
`F=univ\A`.  Suppose a one-parameter family `x_t` remains in the induced
binary-game Nash set, the two base Quit-minus-Continue margins form an affine
segment, and every nonnegative normalized weight has nonnegative maximum on
the two endpoint margin vectors.  Then the segment contains a point where
both base margins are nonnegative.  The checked persistent-base adapter turns
that point into an exact stationary terminal Nash profile against arbitrary
behavioral deviations and hence a uniform-equilibrium payoff.

This theorem and the displayed integer regression are correct.

## 1. Affine segment and minimax selection

Write

\[
 v_e=(L_a(x_e),L_b(x_e)),\qquad e=0,1.
\]

The affinity hypothesis gives exactly

\[
 v(t)=(1-t)v_0+t v_1.
\]

If the compact segment `K=[v_0,v_1]` misses the closed cone
`R_+^2`, strong separation gives a nonzero normal `w` with

\[
 \sup_{v\in K}w\cdot v<\inf_{u\in\mathbb R_+^2}w\cdot u.
\]

The cone is unbounded in both positive coordinate directions, so a separator
with finite right side must have `w>=0`; since zero belongs to the cone, the
right side is zero.  Normalizing gives `w=(lambda,1-lambda)` for some
`lambda in [0,1]`.  An affine functional reaches its segment maximum at an
endpoint, contradicting `(1.2)`.  The quantifiers and strict inequality are
correct, including `lambda=0,1`.

Equivalently, `(1.2)` is the two-dimensional dual characterization of
`[v_0,v_1]` meeting the nonnegative quadrant.  This equivalence is important
for the scope assessment below.

The note's statement that affinity is automatic along a one-free-coordinate
path needs one qualification: `x_t` must use the **affine parametrization** of
that coordinate's marginal (or be reparametrized to it), with every other
marginal fixed.  Mere continuous variation of one marginal does not make the
functions affine in the original parameter.  Multilinearity of product-root
payoffs does make them affine in the marginal itself.

## 2. Orientation and the unrestricted persistent-base compiler

**PASS.**  `quittingRootEndpointDifference` is Quit payoff minus Continue
payoff.  Thus `L_i>=0` is exactly the `base_leave` sign required by
`nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
`exists_uniformPayoff_of_persistentBase_inducedNash_signs`.

The free set is the entire complement, so

```text
A ∪ (univ \ A) = univ
```

and the outsider-join premise is empty.  The base has cardinality two and is
disjoint from the free set.  Every remaining compiler hypothesis is exactly
induced Nash of `x_t`.

The all-behavior conclusion is not overstated.  If a free player changes its
complete strategy, both base members still Quit at date zero, so only that
player's date-zero binary marginal can matter.  If `a` changes its complete
strategy, `b` still Quits surely at date zero, and conversely.  The two
endpoint signs therefore control randomized, delayed, history-dependent, and
Never replacements, not only stationary deviations.  This is packaged by
`QuittingPersistentBaseCertificate.isZeroAsymptoticNash`; its uniform-payoff
compiler is exact.

## 3. Exact audit of the integer regression

Let `p` denote the first free player's Quit probability and `q` the second's,
as in the note.

### Pair base `{a,b}`

Player `f` gets zero from both actions because its relevant rewards at
`{a,b}` and `{a,b,f}` are zero.  Every `t in [0,1]` is therefore induced Nash.
The base margins are

\[
 L_a(t)=1-[2(1-t)+0t]=-1+2t,
 \qquad
 L_b(t)=1-[0(1-t)+2t]=1-2t.
\]

At `t=1/2` both vanish.  At the two endpoints the weighted values are
`1-2lambda` and `2lambda-1`, whose maximum is
`|2lambda-1|>=0`.  Complement-uniform leave safety fails at both opposite
endpoints exactly as stated.

### Singleton base `{a}`

With `p=Pr(b Quits)` and `q=Pr(f Quits)`, direct evaluation gives

\[
 \Delta_b=1-2q,\qquad \Delta_f=1-p.
\]

Binary complementarity yields exactly

\[
 (p,q)=(0,1)\quad\text{or}\quad p=1,\ 0\le q\le1/2.
\]

At the isolated point the anchor payoff is `r_a({a,f})=-1`.  On the second
component its sure-Quit value is one, while the excluded-face value
`r_a({b})=2` violates the **pointwise dominant-anchor** screen at every point.

### Singleton base `{b}`

Likewise

\[
 \Delta_a=-1+2q,\qquad \Delta_f=p-1,
\]

and the induced Nash set is exactly

\[
 (p,q)=(0,0)\quad\text{or}\quad p=1,\ 1/2\le q\le1.
\]

The isolated anchor payoff is `r_b({b})=-1`; on the other component its
sure-Quit value is one while `r_b({a,f})=2`.  Thus every induced Nash fails
the earlier sufficient pointwise screen.  All reward entries used are the
displayed integers.

One scope point is essential.  At `(p,q)=(1,1/2)` in the singleton-`a`
induced game, the high excluded reward `2` is averaged with the zero reward at
`{b,f}`, so the anchor's actual Continue value is exactly one, equal to its
Quit value.  The selected pair-base equilibrium is therefore also an exact
singleton-anchor stationary equilibrium, although it is not certified by the
**pointwise dominant-anchor theorem**.  The regression proves strictness over
that theorem's screen; it does not show that a genuinely two-anchor mechanism
is necessary for this table.

## 4. Target-`B` mass and passive embedding

With `a,b` surely Quitting at date zero, every realized terminal coalition
contains `A`.  Hence for any disjoint target pair `B`, both of the following
are zero:

1. the exact terminal coalition atom `B`; and
2. the strict-first `B` event used by the two-clock question, since members of
   `A` Quit at the same earliest date.

The note should name which convention it means by “target-`B` first mass”; the
conclusion is correct under either relevant convention.

The asserted passive larger-player embedding is straightforward but should
be explicit if promoted beyond an informal boundary test: project every
coalition containing the base to its intersection with `{a,b,f}`, copy the
three-player active coordinates, assign every added player's coordinate zero,
and define the unused empty-projection rows arbitrarily.  Then the added free
players are indifferent, the old one-coordinate Nash segment and margins are
unchanged, and the strict-first disjoint target atom is zero.  Without this
construction, the three-player example alone cannot literally contain two
disjoint target pairs.

## 5. Architecture and export assessment

The theorem does strictly extend the earlier **pointwise dominant-anchor
screen**: the integer table fails that screen for both anchors at every
induced Nash, while the pair-segment selector succeeds.  It is therefore a
useful post-single-anchor diagnostic for `questions/INCENTIVE_GADGET.md`.

It is nevertheless a supplied-segment verifier at the current frontier.
Hypothesis `(1.2)` is, by the theorem's own separation proof, equivalent to
the affine margin segment already containing a jointly nonnegative point.
The game-theoretic work after selection is the existing checked
persistent-base compiler.  No arbitrary gadget, hard residual, or current
producer is known to supply a nontrivial affine segment contained wholly in
the induced Nash set, and mixed Nash sets are not generally convex.

Accordingly I recommend:

* formalize the convex two-anchor selector as a small Research lemma if it is
  useful for finite searches;
* keep the exact integer table as a strictness/boundary regression; and
* do not export it as a new producer until an actual-data theorem produces
  the Nash segment/endpoint screen for a named maintained architecture.

If the conference elects to treat “tables carrying such a Nash segment” as a
standalone special class, the statement is a correct special-case existence
theorem with an unrestricted consumer.  Its significance must still be
advertised as that certificate class, not as progress toward forcing or
excluding the two target masses in arbitrary completions.

## Sources checked

- `quittingPersistentBaseNashSet`, `quittingPersistentBaseRoot`, and
  `quittingPersistentBaseRoot_free_purePayoff_le` in
  `PersistentBaseInducedGame.lean`;
- `nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
  `exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
  `PersistentBaseNashSemanticAdapter.lean`;
- `QuittingPersistentBaseCertificate.isZeroAsymptoticNash` in
  `PersistentBaseArbitraryCompletionEscape.lean`; and
- the previously reviewed pointwise singleton-anchor theorem in
  `notes/CODEX_EULER__SINGLE_ANCHOR_INDUCED_NASH_UNIVERSAL_ESCAPE.md`.

