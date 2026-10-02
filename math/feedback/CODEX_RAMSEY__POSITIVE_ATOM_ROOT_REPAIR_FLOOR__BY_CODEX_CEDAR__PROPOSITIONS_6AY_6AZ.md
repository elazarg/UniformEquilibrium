# Review of Propositions 6AY--6AZ

## Claims checked

I checked the current versions of Proposition 6AY (zero-cost coefficient
deflation, intrinsic same-endpoint carrier, and the corrected interpretation
of the 6AW example) and Proposition 6AZ (periodicization from two actual
zero-Never labels).  This is an ordinary-mathematics and interface review.  I
did not inspect or run Lean code.

## Verdict

**6AY: REVISE by one exact range correction, then valid.**

**6AZ: PASS in its stated conditional prescribed-arm scope.**

Neither proposition supplies arbitrary packet entry, the rectangle
observer-deleted cap port, or a positive-minimum producer.

## Proposition 6AY

The algebraic chart is exact.  For `0<=a<=p<1`, the two coefficients in

```text
A[a]=((1-p)/(1-a))*A+((p-a)/(1-a))*R
```

are nonnegative and sum to one, and substitution gives
`P=(1-a)A[a]+aR`.  Affinity then gives both displayed gain identities.  Since
the actual marginal `P`, the named endpoint marginal `R`, and all opponents
are unchanged, the actual source/endpoint profiles, their `U` and `B`, fixed
terminal atoms, and fixed pure-time comparisons really are identical.  This
is a change of latent coordinates, not a semantic port move.

The exposure calculation is also correct under the range explicitly used in
its proof.  With `e(.)=EverQuitMass(.)`,

```text
e(P)=(1-a)e(A[a])+a e(R) >= a(e(A[a])+e(R))
```

uses `a<=1/2`.  The endpoint contrast equals `G/(1-a)`, while coupling the
two component stopping laws gives contrast at most
`2M(e(A[a])+e(R))`.  Hence

```text
e(P) >= aG/(2M(1-a)) >= aG/(2M).
```

There is one literal overstatement immediately after this calculation.  The
text says that the same chart answers every declared scale `h<=p`, but the
displayed exposure proof chose `a<=min(p,1/2)`.  As written, the intermediate
inequality above can fail for `a>1/2`.  Replace that sentence by

```text
every 0<h<=min(p,1/2)
```

(which is all that a small-scale packet application needs), or state a
separate large-`a` estimate using `min(a,1-a)`.  No other argument changes.

The intrinsic coefficient formula is correct on the countable stopping-time
space:

```text
p_max(P,R)=inf_{R(omega)>0} P(omega)/R(omega).
```

It is in `[0,1]`, and for `a<1` the representation exists exactly when
`a<=p_max`.  At the endpoint `a=1`, the normalized residual formula is
undefined; the coefficient-one representation is possible exactly when
`P=R` and is trivial.  It would be clean to include `a<1` in the sentence
claiming exact legality, although all preceding uses already have `a<=p<1`.
Conditioning gives the stated factor `R(E)/P(E)` with no missing reciprocal.

The 6AW correction is important and correct.  After the firing row, both the
actual conditional law and the conditional endpoint law are
`delta_infinity`, so the intrinsic coefficient rises to one.  What collapses
is the oriented endpoint contrast (gain and atom), not endpoint domination.
Thus 6AW is a coordinate-radius counterexample, not an invariant
`p_max`-loss example.

The added intrinsic upper bound `(6AY.10)` is also exact.  At the maximal
coefficient, write `P=p_max R+(1-p_max)A_max` (with the coefficient-one case
handled by `P=R`).  For one fixed terminal event `C`,

```text
|Pr_P(C)-Pr_R(C)|
  =(1-p_max)|Pr_Amax(C)-Pr_R(C)| <= 1-p_max.
```

Multiplication by the relevant reward coordinate gives
`terminalAtomMagnitude<=M(1-p_max)` with no factor two.  Thus a fixed atom
does bound `p_max` away from one, while supplying no lower bound away from
zero.

## Proposition 6AZ

The periodic construction is literal.  `X_L` repeats the first `L` source
roots, while `Y_L` replaces only `first` by the repeated endpoint word.
Positive source word reach makes the length-`L` residual of `X_L` an actually
reached copy of `X_L`.  The endpoint suffix identity is literal replacement
provenance when its word is reached and remains a valid counterfactual suffix
identity when its reach is zero.

The survival and atom estimates check.  The unchanged `second` label has
zero Never mass on both source and endpoint, so both joint word reaches tend
to zero.  Each member of the source/endpoint pair agrees with its periodic
counterpart until its own word-survival event.  For a fixed reward-weighted
terminal atom this gives exactly

```text
|A_C(X_L,Y_L)-A_C(P,E)| <= M(beta_L+beta_L^E),
```

with no missing factor two: each terminal-event probability changes by at
most its corresponding survival probability, and the atom uses one reward
coordinate bounded by `M`.

The full source semantic seam also checks.  Two distinct zero-Never labels
force every one-player-deleted word reach `delta_(L,-i)` to vanish: after
deleting either retained label the other remains, and after deleting any
other player both remain.  Common-prefix coupling gives the `2M beta_L`
prescribed-payoff estimate.  Holding an arbitrary deviation of player `i`
fixed, the two opponent environments can differ only after all opponents
survive the word, so the same uniform coupling gives
`2M delta_(L,-i)` before taking the best-response supremum.  Thus both `U`
and `B` of `X_L` converge to those of `P`.

Finally, zero Never mass supplies a finite positive hazard contribution for
each retained label.  Choosing a word containing both contributions and
repeating it makes both hazard sums diverge from every suffix.  Therefore
joint and every one-player-deleted survival vanish, and the fixed word can
answer all smaller declared scales only because the current port interface
requires a lower progress bound and no root-mesh upper bound.

The scope statement is exact.  The source is the newly constructed nearby
periodic profile `X_L`, not an arbitrary supplied reached port.  The theorem
assumes two actual zero-Never labels, positive finite source reach, and a
prescribed atom; it does not solve the rectangle arm or prove that the frozen
radial source has those hypotheses.

## Sources inspected

- `notes/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md`, current
  Propositions 6AY--6AZ and the 6AO/6AW comparisons used there.
- The established pure stopping-law semantics used throughout the same note;
  no new repository theorem is asserted by this review.
