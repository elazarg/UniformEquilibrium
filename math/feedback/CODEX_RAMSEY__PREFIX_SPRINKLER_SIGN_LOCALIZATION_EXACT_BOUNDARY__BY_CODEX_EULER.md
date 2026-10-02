# Review of `CODEX_RAMSEY__PREFIX_SPRINKLER_SIGN_LOCALIZATION_EXACT_BOUNDARY`

Reviewer: **CODEX_EULER**  
Date: 2026-08-26  
Verdict: **REVISE (one declaration-source repair); mathematical content PASS; internal/no export**

## Claim audited

The note claims that a prepared finite product word cannot by itself localize
the sign of a later terminal payoff-difference atom.  A word common to the
compared profiles annihilates every signed stage contribution in that word;
allowing the mover's prepared marginal to change still does not orient the
prepared-stage sign.  The latter failure is witnessed by an exact half-law
Fin4 profile pair.  Finally, for a fixed terminal atom, the exact missing datum
is the signed-tail budget

```text
P_K >= theta  iff  R_K <= A-theta,
```

which is asserted only as a characterization and not as a producer.

## Independent checks

### 1. Common-word and rectangle scaling: PASS

If the two live-root sequences agree through dates `0,...,K-1`, their common
survival is `H_K` and the pre-`K` contribution to the difference of every
fixed terminal-coalition mass is zero.  The remaining difference is exactly
`H_K` times the shifted-suffix difference.  Multiplication by the fixed
observer reward gives (2.1)--(2.3).

For four corners the common prefix law contributes the same absorbing mass
to all corners and hence cancels in the alternating order
`x11-x10-x01+x00`.  The suffix masses all acquire the same factor `H_K`.
Thus (2.4), including its orientation, is correct.  Positive incidence at a
common full-support root has no signed content.

This agrees with
`quittingTerminalOutcomeMass_sub_eq_liveMass_mul_spine_sub` and
`quittingTerminalPayoffDifferenceAtom_eq_liveMass_mul_spineAtom` in
`Research/Quitting/CausalEndpointAtomLocalStateMatch.lean`.

### 2. Full-support response-square example: PASS

Conditional on reaching the suffix, the selected collision `{w,j}` has
probabilities

```text
x00: 2/5,  x10: 3/5,  x01: 1/10,  x11: 9/10.
```

Therefore the two `u -> v` response gains are respectively `1/5` and `4/5`,
and the rectangle in the declared orientation is

```text
9/10 - 3/5 - 1/10 + 2/5 = 3/5.
```

The common Fin4 sprinkler multiplies all three numbers by
`C=(1-kappa)^4`, while its own stage rectangle is zero.  Arbitrarily many
common all-Continue rows may be inserted without changing those values.
The example is an exact behavioral-profile construction and is correctly not
presented as a terminal-gap game.

### 3. Half-law regression: PASS

The half mixture of the mover's complete laws is

```text
h(0)=3/8, h(1)=3/8, h(Never)=1/4.
```

Its behavioral hazards are `3/8` at date zero and
`(3/8)/(5/8)=3/5` at date one.  Direct independent-clock multiplication gives

```text
source date 0: (1/4)^2 (3/4)^2       = 18/512,
target date 0: (3/8)(1/4)(3/4)^2     = 27/512,
source date 1: (3/4)^4               = 162/512,
target date 1: (3/8)(3/4)(3/4)^2     = 81/512.
```

Hence the source-minus-target contribution at date zero is `-9/512`, while
the terminal source-minus-target atom is
`(-9+81)/512=9/64`.  All four date-zero quit and Continue probabilities are
strictly positive in both profiles, so every nonempty coalition indeed has
positive date-zero mass.  This exactly falsifies sign inference from the
listed unsigned/full-support and terminal-law data.

### 4. Summability and tail criterion: PASS

For a fixed coalition and observer reward,

```text
|a_t| <= |r_j(T)|
  * (StageMass(x,t,T) + StageMass(y,t,T)).
```

Each nonnegative stage-mass series has sum at most one, so `a_t` is absolutely
summable.  Thus `A=P_K+R_K`, and (5.2) is the immediate algebraic equivalence
`P_K>=theta iff R_K<=A-theta`.  For `K>0`, one of the first `K` summands is at
least their average `P_K/K`, proving (5.3), even when other summands are
negative.

The note scopes this correctly.  It explicitly denies a uniform bound on
`K`, a pre-decoder prepared block, and a one-date floor.  Proposition 5.1 is
therefore an exact characterization, not a circular approximate-minimizer or
finite-tail producer.

### 5. Bellman scope and decisiveness: PASS

The examples decisively close the **prefix-only sign-localization grammar**:

- a common word has identically zero prefix sign; and
- once the prepared mover law is permitted to change, the stated endpoint
  and incidence data do not determine even the sign of the first prepared
  contribution.

They do not rule out a genuinely nonlocal consumer that selects a later
stage and also preserves a literal common tail, exact root Nash, and the
punishment floor.  The note says exactly this.  The cited local-state-match
declarations require a stage-pure endpoint update and common subsequent tail;
the half-law reset does not provide that hypothesis.  I found no cited or
nearby checked Bellman consumer that accepts only the weaker signed-window
data.

The local regressions have no positive-global-minimum or terminal-witness
claim, so internal/no export is the honest status absent a new executable
consumer.

## Mandatory source repair

Section 8 assigns two declarations to the wrong declaration file:

- `quittingStoppingLawMixtureBehaviorStrategy` is declared in
  `UniformEquilibrium/Quitting/Paths/StoppingLawMixture.lean`;
- `quittingTerminalOutcomeMass_stoppingLawMixture_eq` is declared in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`.

`TerminalSemanticStoppingLawMixture.lean` imports/reuses adjacent mixture
infrastructure, but it is not the declaration source for either theorem as
currently stated in the audit.  Replace that bullet with the two exact source
paths.  No mathematical rereview is needed after this bounded provenance
repair.

## Final assessment

After the declaration-source correction: **PASS as a sharp internal
converter-class boundary**.  It is neither an export candidate nor a Fin4
breakthrough by itself.  Its useful content is the exact separation between
unsigned prepared incidence and signed temporal localization, together with
the honest identification of a signed-tail budget plus common-tail/floor
provenance as the missing executable data.

## Delta confirmation

The author replaced the declaration-source bullet with the two exact paths
listed above and recorded the independent-review status.  No adjacent claim
was broadened.  Final verdict: **REVISE → PASS, internal/no export**.
