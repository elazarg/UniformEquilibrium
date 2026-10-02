# Review of `gpt/TEMPORALIZE.md`

Reviewer: `SOCIAL_WEIGHT_REVIEW`

Verdict: **FAIL as a temporal/Nash--Bellman consumer; PASS for the isolated
geometric-retry and total-variation lemmas.**

## Claim checked

The note claims that a finite literal cycle of exact complete behavioral
best-response replacements can be lifted to a geometric-retry ladder whose
vertical direction is actual calendar time, whose horizontal response gains
stay uniformly positive, and whose summable vertical seams are negligible
relative to an indefinitely renewable accepted response charge.

The retry profiles are legitimate actual behavioral profiles.  The claimed
conversion of their horizontal response comparisons into temporal charge is
not.

## Valid part

For a finite clock `t`, the retry clock starting at level `n` stops at its
first copy with probability `1-eta_n`, so its stopping-law total-variation
distance from `delta_t` is exactly `eta_n`.  Product TV gives the stated
`4 eta_n` and `3 eta_n` bounds.  The payoff and unrestricted-cap estimates
then follow by coupling and taking suprema.  Never and unbounded behavioral
responses are genuinely covered.

At one fixed level `n`, coordinatewise retry preserves every literal
one-player replacement and the exact horizontal cycle.  The lifted mover's
gain differs from the original gain by at most `8 R eta_n`, and its opponents
are unchanged.  Equations (11)--(24) are therefore valid static response-
cycle statements, apart from the typographical duplicate `:=` in the
definition of `widehat g`.

For one fixed column `k`, equations (25)--(28) are also correct: conditional
on all finite-clock players skipping their attempts in block `n`, the actual
calendar suffix is the level-`n+1` retry profile in the same column.  The
triangle estimates (29)--(32) are valid semantic comparisons after the
common time-origin identification.

These facts are useful as a retry/TV stability lemma for a supplied finite
pure-clock response cycle.

## Fatal typing gap

### 1. Horizontal arrows are not temporal edges

The arrow

\[
\widehat\sigma^{k,n}\longrightarrow\widehat\sigma^{k+1,n}
\]

is a unilateral counterfactual replacement of one player's entire strategy.
It is not a row of play, a Bellman successor, an exact cap--Nash prefix, or a
punishment-floor edge.  The equality saying that its target is the next
horizontal source does not change that type.

Actual play in column `k` moves vertically only:

\[
\widehat\sigma^{k,n}\rightsquigarrow
\widehat\sigma^{k,n+1}.
\]

It never moves horizontally to column `k+1`.  Conversely, choosing the
horizontal response replaces the counterfactual profile; it does not make
that target the continuation reached by the original play.  No single
behavioral chronology traverses the grid in the order used by (41).

### 2. No root-Nash estimate is proved

The roots inside a retry block reproduce the pure-clock calendar of an
arbitrary off-minimum response-cycle state.  At a finite clock's attempt row,
Quit is used with probability `1-eta_n`.  If Quit has a fixed local Bellman
defect there, making `eta_n` small leaves a used action with essentially the
same fixed defect; it does not make the row `O(eta_n)`-Nash.

Closeness of whole terminal payoffs and caps to those of `sigma^k` says
nothing about Nash optimality of each displayed temporal root against its
literal successor.  The note proves neither exact Nash--Bellman typing nor a
summable support-Nash error.  Equations (29)--(32) compare suffix packets;
they are not root-Nash error bounds.

### 3. Equation (41) sums alternative columns

The double sum

\[
\sum_{n<N}\sum_{k<L}\widehat g_{k,n}
\]

adds horizontal gains available at mutually alternative source profiles.
These gains cannot be accumulated as charge by one player path or one
Nash--Bellman block.  Even gains for the same mover at different `k` are
counterfactual comparisons at different columns, not successive temporal
payments.

For one actual column `k`, the probability of reaching level `n` is

\[
\prod_{p<n}\eta_p^{f_k}.
\]

With `eta_p=2^{-p} bar_eta`, this decays superexponentially.  Weighting one
available horizontal comparison at each reached suffix therefore gives only
a finite quantity, and still does not make those comparisons temporal edges.
The sentence following (43) cannot repair the missing chronology: equal
reach weights preserve a conditional ratio but do not create an accepted
edge or divergent cumulative charge.

### 4. The vertical charge is untyped

For `f_k>0`, the conditional absorption charge
`1-eta_n^{f_k}` is indeed positive and close to one.  But the roots carrying
that absorption have no proved Nash--Bellman or punishment-floor validity.
It is therefore raw behavioral absorption, not charge accepted by the
existing chronological or exact-capacity consumers.

## Exact surviving statement

The sound conclusion is:

> A finite pure-clock exact-response cycle has coordinatewise geometric-retry
> approximants.  At every retry level the same finite horizontal response
> cycle persists, whole laws/payoffs/unrestricted caps are `O(eta_n)` close
> to the original cycle, and each fixed column has a genuine retry temporal
> decomposition.

This is not alternative 2 of the relevant temporalization question.  To
obtain that alternative one still needs a theorem which either:

1. makes the vertical retry roots exact or summably approximate
   Nash--Bellman roots while retaining the horizontal paid data; or
2. converts one horizontal replacement into a source-matched temporal block
   whose target is literally the next reached continuation.

No such theorem is present in the packet.  Equations (41)--(43) and the final
claim of renewable response charge should be rejected, while the retry/TV
lemma may be retained as a nonconsumer.
