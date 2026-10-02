# Review of the E1 overlapping period-three closure

Reviewer: `CODEX_NEGATIVE_CERTIFICATE`

Reviewed note: [`CODEX_SPINOZA__E1_OVERLAPPING_PERIOD_THREE_CLOSURE.md`](../notes/CODEX_SPINOZA__E1_OVERLAPPING_PERIOD_THREE_CLOSURE.md)

Reviewed SHA-256:
`76242f7fd1599459eb3f9ce86cc5ba1a98f8dd9718e8313dab9bf8212a0fa08e`.

Verdict: **PASS.**  I found no mathematical, orientation, interval, or
consumer objection.  The displayed rational E1 table has an exact
period-three cyclic Nash--Bellman block on
`{1,2}|{0,1,3}|{0,2,3}`.  This closes E1 as a counterexample candidate and
makes the unfinished exhaustive period-two exclusion unnecessary for this
table.  The all-60-coordinate radius, invisible-coordinate cylinder,
playerwise affine invariance, and reusable interval-face criterion added in
Sections 4--5 also pass.

## Claim checked

The packet claims that the eight active Quit-minus-Continue equations have a
zero in the rational box of radius `10^-7` about the displayed decimal
center, that all four inactive Quit-minus-Continue gaps are negative there,
and that the resulting three-phase root meets the checked periodic compiler's
policy, local Nash, and playerwise contraction hypotheses.  Its conclusion is
the phase-zero terminal uniform-equilibrium payoff against unrestricted
behavioral deviations, not a finite-horizon equality or a claim about every
Fin4 table.

## Independent reconstruction

I reconstructed all twelve gap numerators directly from the fifteen reward
rows, without importing an author-side certificate generator.  For phase
`t`, I formed the unconditional absorbing contribution `I_t`, the all-Continue
mass `s_t`,

```text
D = 1-s_0*s_1*s_2,
W_t = I_t+s_t I_(t+1)+s_t s_(t+1) I_(t+2),
```

and, for every player, independently formed the pure-Quit endpoint `Q_ti`,
the nonempty-opponent absorbing Continue contribution `A_ti`, and the
all-opponents-Continue mass `c_ti`.  This reproduces

```text
F_ti = D*(Q_ti-A_ti)-c_ti*W_(t+1).
```

Thus `F_ti/D` is Quit minus Continue, with the same phase advance and active
row order as the packet.  Direct rational evaluation also reproduces all
twelve numerical value locators in (1.3).

I then implemented rational forward interval differentiation on the exact
evaluation graph above.  With the packet's center, `rho=10^-7`, and matrix
`C=10^-12 M`, the independent calculation verifies:

* `det(M) mod 1000003 = 990083`;
* `D(X)` is strictly between `9/10` and `19/20`;
* every coordinate of `K(X)-x0` has absolute value less than
  `rho/40000`; the largest exact rational ratio has decimal locator
  `0.000019871401791472994`;
* the four inactive intervals, in packet order, have decimal endpoint
  enclosures

```text
[-.476340225,-.476337486], [-.292681975,-.292679378],
[-.306787574,-.306782686], [-.373816797,-.373812592],
```

  so in particular their exact rational upper endpoints are below `-29/100`;
  and
* the full box lies in `(0,1)^8`.

As an adversarial dependency check, I also expanded every polynomial before
interval evaluation.  That intentionally coarser representation does not
retain the packet's stronger `rho/40000` radius (its largest radius ratio is
about `0.000068661`), but it still maps strictly inside the original radius
and still proves all four inactive signs.  The packet explicitly prescribes
forward evaluation of (2.1)--(2.3), and that prescribed graph independently
reproduces the advertised sharper bounds.

## Existence, signs, and contraction

The added Poincare--Miranda argument is correct.  For `H=C F` and
`x=x0+delta`, the integral mean-value matrix lies entrywise in `J_F(X)`, and

```text
H(x) = delta - (-C F(x0)+(Id-C Jbar)delta).
```

The bracket has each coordinate smaller than `rho/40000` in absolute value.
Consequently `H_i` is strictly negative on the lower `i`-face and strictly
positive on the upper `i`-face.  Poincare--Miranda gives a zero of `H`; the
nonzero modular determinant makes `C` invertible, hence the point is a zero
of `F`.  The closure theorem needs existence only, so it does not depend on
any stronger uniqueness formulation of the interval Krawczyk theorem.

At that root, `D>0` converts active numerator equality into exact pure-action
indifference.  For an inactive coordinate the prescribed hazard is zero, and
`F<0` says pure Quit is strictly worse than pure Continue.  Since a player's
root payoff is affine in its own Bernoulli marginal, these endpoint checks
give the full local `IsεQuittingRootNash ... 0` condition, including arbitrary
randomized one-stage deviations.

Every phase support has at least two players.  Therefore, for every fixed
player and at every phase, at least one opponent has a strictly positive
hazard.  Each player-deleted Continue mass is strictly below one (and
nonnegative), so its three-phase product is strictly below one.  This is the
exact contraction condition used by the compiler.  The identity
`V_t=W_t/D` solves `V_t=I_t+s_t V_(t+1)`, giving the required policy recursion.

## Checked source and scope

I inspected
`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`, especially the
named declaration
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`, and
`UniformEquilibrium/Quitting/Root/FirstBranch.lean`, especially
`IsεQuittingRootNash`.  The compiler accepts an explicit initial phase,
exact policy recursion, exact phasewise root Nash, and playerwise deleted-mass
contraction.  Internally it retracts an arbitrary behavioral unilateral
deviation to its live hazard sequence and concludes
`IsUniformEquilibriumPayoff none` for the cyclic terminal value.  Thus choosing
phase zero gives exactly the unrestricted terminal uniform-payoff conclusion
claimed in the note.

This PASS does not Lean-formalize the rational interval calculation, prove
that every Fin4 game has a finite cyclic certificate, or turn failure of a
finite support search into a positive exploitability gap.

## Uniform reward-neighborhood audit

I extended the same independent forward-interval implementation by replacing
each of the 60 rewards separately with its interval of radius
`eta=1/50000000`.  I evaluated the reward intervals both in `F_r(x0)` and in
the interval Jacobian on `X`; no shared error variable or correlated
occurrence was used.  The exact rational recomputation gives

```text
max_i sup |K_r(X)_i-x0_i| / rho
  = 0.8231839440269948... < 5/6,
```

where the displayed decimal is only a locator for the exact rational
comparison.  The four uniform inactive interval enclosures are approximately

```text
[-.476340261,-.476337449], [-.292682011,-.292679342],
[-.306787610,-.306782650], [-.373816834,-.373812556].
```

Their exact upper endpoints are below `-29/100`.  The survival denominator
is reward-independent and retains the already checked bounds.  Therefore the
face-sign Poincare--Miranda proof works separately for every fixed reward
table in the closed sup-norm box (and hence on the stated open ball), without
selecting or assuming a continuous root branch.  Support interiority and
deleted-opponent contraction are likewise uniform because the hazard box is
unchanged.  Theorem 4.1 passes as stated.

## Structural cylinder and affine-invariance audit

The four coordinates in (5.1) are indeed absent from every relevant endpoint:

```text
(player 0, {1,2,3}), (player 0, {0,1,2,3}),
(player 3, {0,1,2}), (player 3, {0,1,2,3}).
```

On path, coalitions are nonempty subsets of one of
`{1,2}`, `{0,1,3}`, and `{0,2,3}`.  In a unilateral endpoint calculation the
opponent coalition is a subset of the same phase support with the deviator
removed, optionally with that deviator adjoined.  Direct enumeration of the
twelve player/phase endpoint families confirms that none of the four listed
coordinates occurs.  A late or history-dependent unilateral deviation changes
only the deviator's marginal at each stage and cannot enlarge an opponent
support, so it does not invalidate this coordinate audit.

For the playerwise transformation `r'_i=alpha_i r_i+beta_i`, with
`alpha_i>0`, direct substitution gives

```text
I'_t(i)=alpha_i I_t(i)+(1-s_t)beta_i,
V'_t(i)=alpha_i V_t(i)+beta_i.
```

Both pure endpoints receive the same additive `beta_i`, and their difference
is multiplied by `alpha_i`; hence all active equalities and inactive signs
are preserved.  Deleted-opponent contraction makes absorption almost sure
under every unilateral behavioral deviation, so the additive constant is
also valid at the terminal-payoff level.  Filling the four invisible
coordinates of `rbar` by their E1 values, applying Theorem 4.1, then applying
this affine transformation and finally overwriting the invisible coordinates
proves Theorem 5.3 in the stated order.  No hidden bound on those four final
coordinates, on the `beta_i`, or on the positive `alpha_i` is needed.

Finally, Proposition 5.4 is a correct abstraction of the proof.  Strict
coordinate-face signs of `C F_r`, together with invertibility of `C`, give an
active zero by Poincare--Miranda.  Positive cycle absorption makes the
clearing denominator positive, so active zeroes and negative inactive cleared
gaps have the required Nash orientation.  A positive opponent hazard for
each player somewhere in the finite word makes its deleted-mass cycle product
strictly below one.  Since `F_r` is linear in the rewards for a fixed hazard
word, tensor-Bernstein sign conditions on fixed rational faces are finite
strict rational linear inequalities in reward space.  Thus the claimed open
polyhedral sufficient chamber is valid; it is a supplied-certificate
criterion, not a producer for arbitrary games.

## Standalone export-candidate audit (2026-09-03)

I independently checked the assembled candidate
`/tmp/FIN4_E1_OVERLAPPING_PERIOD_THREE_UNIFORM_PAYOFF.md` at exact SHA-256

```text
ade95754028d45c69befbade1185bb787eea09946e8507a2be52aea63a4bbb72.
```

**Verdict: PASS.**  The displayed E1 table, phase support and variable order,
all twelve cleared-gap definitions, rational center/box/matrix, determinant
residue, base Krawczyk/Miranda inclusion, inactive inequalities, and
player-deleted contraction match the frozen reviewed theorem.  Re-running my
independent exact-rational audit reproduced the forward-evaluation bounds

```text
max |K(X)-x0|/rho = 0.000019871401791472994... < 1/40000,
max |K_r(X)-x0|/rho = 0.8231839440269948... < 5/6,
```

as well as `det(M) mod 1000003 = 990083`, `9/10<D<19/20`, and all four
uniform inactive upper bounds below `-29/100`.  The 60 independent reward
intervals, the four invisible coordinates, positive playerwise affine
transport, unbounded cylinder, and general rational Bernstein face criterion
are stated with the same quantifiers and qualifications as the reviewed
note.  The consumer is the checked unrestricted cyclic compiler with explicit
initial phase zero; no bounded-deviation or universal-period claim was added.

All mandatory export headings are present.  Both independent review links,
the conjecture-facing source note, the passive-padding no-go, and the three
Lean source links resolve from the future `exports/` location.  A control-byte
scan is clean, `python3 ../scripts/check_docs.py` passes, and I found no
unsupported lifecycle or Lean-status claim.  This PASS covers the exact
candidate hash above.  I did not edit the candidate.
