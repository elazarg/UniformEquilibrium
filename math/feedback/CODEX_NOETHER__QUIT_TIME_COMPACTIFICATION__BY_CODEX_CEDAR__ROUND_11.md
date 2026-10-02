# Round 11 feedback on Quit-Time Compactification

Reviewer: `CODEX_CEDAR`

Reviewed note: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: Section 46, Proposition 43, including `(C1)`--`(C8)`.  I treat the
corrected compact-near-feasible Lemma 2.1 and independently reviewed
Proposition 42 as hypotheses.  I did not use the earlier review as a premise.

Status: `VALID CONDITIONAL ORDINARY MATHEMATICS; ONE NAMED-DECLARATION ADAPTER MUST BE STATED`

## Claim audited

Under failure of stationarily generated and instant approximate equilibria,
and conditional on the corrected uniform-`rho` lemma, every arbitrary
behavioral terminal approximate equilibrium family yields
`CyclicOrbitCondition`: at every positive error there is a finite
positive-absorption cyclic `F_epsilon` orbit with `epsilon`-rational tails.

This is an equilibrium-to-orbit necessity direction.  It is not by itself a
universal positive producer from arbitrary payoff data, and it does not prove
the corrected Lemma 2.1, whose transcription
`Literature.Simon2007.lemma5_corrected_2012` still contains `sorry` in the
non-built literature lane.

## Constant choices and first crossing

After positive normalization, choose

```text
eta <= min(epsilon/5,rho,sigma),  beta=eta/4,  e=eta/8.
```

Then `4 eta<=epsilon`, `beta+2e=eta/2<=eta`, and all quantities used as
upper bounds for `U`, `L_0`, and `alpha` are positive.  The positive-solo
forcing declaration `exists_tailSurvival_lt_of_equilibrium_positiveSolo` in
`Literature/Simon2007.lean` asks for exactly

```text
alpha < U*v_j/2.
```

Because `S_0=1>U`, the first `T` with `S_T<U` is positive and satisfies
`S_T<U<=S_(T-1)`.  At the crossing, `u=S_(T-1)>=U>s`, where
`s=rho*U/2`.  From

```text
n*alpha/(s*beta)<L_0<rho/2
```

one gets strictly `n*alpha/(u*beta)<rho/2`.  Proposition 42's weak general
bound therefore gives

```text
1-Q(p_(T-1)) > rho/2,
S_T > rho*U/2 = s.
```

For every `t<T`, the actual reach is `S_t>=S_T>s`.  The same hypotheses
`alpha<s*beta*d`, `eta<=rho,sigma`, and `beta+2e<=eta` therefore allow a new
application of Proposition 42 at that row.  This proves

```text
1-Q(p_t) >= rho-n*alpha/(S_t*beta) > rho/2.            (1)
```

No rationality premise for the actual tail is used circularly in this step:
Proposition 42 first clips the tail and uses the attainable min--max response.
Actual-tail rationality is derived only after the common survival floor is
known.

## Logarithmic direction

Put `q_t=Q(p_t)`.  Equation (1) gives
`0<=q_t<1-rho/2`.  Hence

```text
-log(1-q_t) <= q_t/(1-q_t) <= 2*q_t/rho.
```

The finite product identity `S_T=product_(t<T)(1-q_t)` yields

```text
-log S_T <= (2/rho) sum_(t<T) q_t.
```

Since `S_T<U<exp(-4H/rho^2)`, the direction and strictness are

```text
sum_(t<T) q_t > (rho/2)(-log U) > 2H/rho.             (2)
```

Thus `(C6)` is correct.  This also covers `T=1`; the finite sum then has one
term.  The endpoint `1-Q=rho/2` cannot occur in this construction because
the error comparison above is strict.

## Rationality, seam, and variation

The choice `alpha<eta*s` and `S_i>=S_T>s` for every `i<=T` imply the exact
hypothesis of `equilibrium_tail_rational`, so every actual tail through `T`
is `eta`-rational.  With

```text
L=n*alpha/(s*beta),
```

the prefix calculation gives

```text
z.totalError <= 2*M*L,
rho*(sum_(t<T)q_t-L) <= z.exactVariation.
```

Because `L<L_0<eta/(8M)`, the first quantity is strictly below `eta/4`.
Because (2) holds and `L<L_0<H/(2rho)`, in fact

```text
rho*(sum q_t-L) > 3H/2 > H,
```

so `(C8)` has ample margin.  The path starts at the actual tail at `T`, whose
norm is at most the terminal reward bound `M`.  Failure of the instant branch
and `eta<=sigma` exclude a sure quitter from every purified `E_eta` row.
These are precisely the remaining hypotheses of
`exists_cyclicOrbit_of_large_approximatePath`; its conclusion includes both
positive absorption and rationality of every periodic tail.

## Required corrected-`rho` adapter

The note should not describe the current private declaration
`exists_supportPurifiedPrefixPath` as literally accepting corrected Lemma
2.1.  In `Literature/Simon2007.lean` it still takes the old unrestricted
premise

```text
hρ : IsUniformRho G rho.
```

The corrected ordinary version is immediate but must be stated separately.
Replace that premise by the compact-near-feasible conclusion of
`lemma5_corrected_2012`.  At its motion-bound use, supply

```text
NearFeasible G 1 (QuitTailPayoff G p (i+1))
```

from `QuitTailPayoff.feasible` in the same file (distance zero).  At its
no-sure use, use the independent `sigma` conclusion from
`exists_scale_without_sure_quitter_of_not_instant`, with monotonicity from
`eta<=sigma`.  No point of the resulting approximate path needs to be fed
back into corrected Lemma 2.1; only actual feasible tails do.  Therefore the
NearFeasible restriction causes no mathematical gap, but the literal named
private theorem is not yet the claimed adapter.

## Scaling and verdict

Positive payoff scaling preserves terminal strategies and row supports,
scales terminal/min--max/one-stage payoffs and all norm errors by the same
factor, and preserves the qualitative branch failures.  To be quantifier
exact, for an original target error `epsilon`, apply the normalized argument
at the scaled target error and divide the resulting orbit data back.  The
uniform `rho` used inside the proof is selected afresh for the normalized
game; it is not asserted to be scale-invariant despite appearing in both a
payoff tolerance and a probability bound.

Subject to the corrected Lemma 2.1 and Proposition 42, Proposition 43 is
valid ordinary mathematics.  The only repair is source-exact wording (or a
restated private prefix lemma) for the corrected NearFeasible-`rho` adapter.
It remains conditional and is not proved in production Lean.
