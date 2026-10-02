# Review of generic paid-response maximal-root reduction

Reviewer: `SOCIAL_WEIGHT_REVIEW`  
Date: 2026-08-31  
Verdict: **PASS**, with two wording qualifications below.  The packet is a
sound strict reduction, not a consumer of any terminal Fin4 chamber.

## Claim checked

The note starts from literal profiles `P_n,Y_n` differing only in one fixed
player `p`, with `P_n` asymptotically globally minimum, a fixed positive
`p`-gain, and vanishing target `p`-debt.  It claims:

1. a fixed signed finite terminal-law coordinate after subselection;
2. preservation of that coordinate under one common maximal exact root;
3. an exhaustive charged/minimum/reset-rigid/strict-off-minimum split; and
4. in the uniformly charged arm, a fixed nonmover cap displacement of at
   least `alpha D_*/6` and a same-response payoff comparison of at least
   `alpha D_*/12`.

I checked the algebra and tried to falsify the quantitative arm by affine
cap translation.  The translation example in the note correctly shows the
limit of the conclusion rather than refuting it.

## Verified steps

### Signed atom

The payoff gain is the sum of fifteen signed finite-law reward coordinates;
Never contributes zero.  A sum at least `G` forces one summand at least
`G/15`, even when the selected reward and law difference are both negative.
Finite pigeonhole and common compactification preserve one fixed label and
the weaker `G/16` bound.  No absolute-value or positivity-of-reward
assumption is hidden here.

### Maximal-root ledger

For a maximal exact root `x_n` against `B(Y_n)`, exact debt scaling gives

```text
D(x_n star Y_n) = s_n D(Y_n).
```

Global minimality therefore gives `s_n >= D_*/D(Y_n)`.  With four players
and rewards bounded by `M`, `D(Y_n)<=8M`, so the common-prefix signed atom is
at least `G D_*/(128M)`.  Positive `D_*` itself excludes the degenerate
`M=0` case.  When absorption tends to zero, the prefixed joint semantic/law
points converge to the same target cluster, as required by the reset-rigid
and strict alternatives.

### Charged cap displacement and constants

The coordinate root defect is one-Lipschitz in its own continuation-cap
coordinate.  Since `x_n` is exact at `B(Y_n)`, the arbitrary-root minimum
budget at `P_n` gives

```text
a_n D(P_n)
  <= D(P_n)-D_* + sum_i |B_i(P_n)-B_i(Y_n)|.
```

The mover cap cancels exactly.  If `a_n>=alpha`, then eventually the three
nonmover absolute cap changes sum to at least `alpha D_*/2`; hence one fixed
nonmover and sign have displacement at least `alpha D_*/6`.  Approximating
the larger cap within `alpha D_*/12` by a pure stopping time gives a common
response comparison of at least `alpha D_*/12`.  The pure time may depend on
`n`; no cap attainment or bounded-time claim is needed.

The affine-translation regression is correct: the derived comparison can
move every response value together, so it need not be a response-gap curl or
cap-switch certificate.  Thus the new quantitative conclusion does not by
itself enter the normalized full-chord consumer.

### Remaining alternatives

When absorption tends to zero, compactness leaves exactly `D(z)=D_*` or
`D(z)>D_*`.  In the equality case, zero opponent incidence plus a positive
finite atom forces the law to be supported on `{p}` and Never; zero `p`-debt
then contradicts the positive-minimum singleton margin.  Hence the stated
reset-rigid entry is valid.  The strict case only supplies the external
reset-face minimizer and correctly disclaims law or chronology matching.

The postmark constants also check: taking `G=K/16` and multiplying by the
root-survival floor gives `K D_*/(2048M)`.

## Wording qualifications

1. In the charged arm, “fixed-response comparison” should be read as using
   the **same selected response on the two backgrounds at each rank**.  The
   pure time is not shown to stabilize across ranks and can escape to
   infinity.
2. “Four-profile response chord” is mathematically accurate as a literal
   same-response rectangle, but it is not yet the stronger normalized-gap
   or cap-switching chord used by existing consumers.  The note already
   states this boundary explicitly.

## Novelty and consumer status

Narrow phrase and theorem searches found the maximal-root reduction only for
the specialized vanishing-response rectangle.  The automatic signed-atom
extraction from an arbitrary fixed-gain asymptotically optimal response, and
the charged-arm `alpha D_*/6` cap-displacement conclusion, are genuine new
generic adapters.

They do not close the charged arm, reset rigidity, or the strict neutral
port.  The exact remaining charged-arm datum is a non-affine response-gap
effect or an extension-compatible chronological return.  The packet is
therefore suitable as a strict producer/refinement, not as evidence that a
Fin4 terminal SCC has been consumed.
