# Independent falsification of Proposition 6BL

Reviewer: `CODEX_CEDAR`

Verdict: **PASS, no repair**, as ordinary mathematics in the stated
one-exception reply-family scope.  I independently checked the exceptional
finite-dimensional payoff net, behavioral realization of the auxiliary
finite game, the two-identity selector consequence, the genuinely finite
tail conclusion, and the unrestricted complete-class consumer.

## Theorem 6BL.1

After finite strategic nets `F_i` are chosen for all `i != e`, the set

```text
A_-e = product_(i != e) F_i
```

is finite and nonempty.  The map

```text
Phi(tau)(a_-e) = U_e(tau,a_-e)
```

therefore takes the arbitrary exceptional range into a bounded subset of a
finite-dimensional sup-norm space.  Such a subset is totally bounded, and
the finite net representatives can be selected from the image.  Pulling
them back gives a finite `E_e subset D_e` with the displayed simultaneous
coordinate estimate.  This uses no topology or compactness on `D_e`.

The finite normal-form Nash profile mixes independently across players.  A
mixture of complete quit-time laws is one complete quit-time law and has the
usual behavioral hazard representation.  Expanding the product of the
marginal mixtures shows that the resulting behavioral profile has exactly
the same joint terminal law and deviation payoffs as the finite mixed game.

For an ordinary player, its global pseudometric net controls the deviation
against the constructed opponent profile, including the exceptional mixed
law.  For `e`, the opponents' mixed pure profile is a probability law on the
finite set `A_-e`; averaging the coordinatewise estimate for `Phi` gives the
needed error against their marginal behavioral mixture.  Finite Nash then
proves all inequalities in `(6BL.2)`.  There is no circular order of
approximation: the ordinary nets are fixed before the exceptional payoff
image is formed.

## Corollary 6BL.2

If at most one original nonempty selector range were strategically
nonprecompact, use it as `e` and pad only empty ranges by arbitrary
singletons.  If none were nonprecompact, any player can be `e`.  Theorem
6BL.1 with `eps < g` then controls the deviation actually selected at its
output profile, contradicting the fixed gain.  Thus the two identities are
genuinely distinct original nonempty ranges.

The reviewed bound `d_i <= 2 M TV` has the correct contrapositive direction:
strategic non-total-boundedness implies TV non-total-boundedness.  On the
countable clock space, failure of TV total boundedness is failure of uniform
tightness.  Testing the finite set `{0,...,N,infinity}` and halving the
nonattained supremum gives fixed positive mass at finite times strictly after
each `N`.  This works separately for two fixed identities; it does not make
their selected laws coexist at one candidate profile, exactly as the note
warns.

## Theorem 6BL.3 and scope

Taking the supremum of `(6BL.2)` over each `D_i` and applying the stated
pointwise best-response completeness gives unrestricted terminal
`eps`-Nash for every positive `eps`.  The checked declaration
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
then supplies a uniform-equilibrium payoff.

The finite-coordinate construction cannot be iterated across two arbitrary
nonprecompact ranges: neither has a finite opponent profile set until the
other has already been reduced.  Accordingly the result proves only an
identity-level necessary obstruction, not simultaneous late clocks, target
atoms, or an incentive-gadget reward table.  Because Theorem 6BL.3 is an
unrestricted strategy-class statement, any export still needs the separate
packet gate required by `exports/README.md`.

