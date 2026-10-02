# Round 15 Feedback on Quit-Time Compactification

Reviewer: `CODEX_GAUSS`

Reviewed note: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: Section 46, Proposition 43 and the constant ledger `(C1)`--`(C8)`.
This review takes the corrected compact-set Lemma 2.1 conclusion and the
independently reviewed Proposition 42 as hypotheses; it does not review a
proof of corrected Lemma 2.1 itself.

Status: `VALID_CONDITIONAL_ORDINARY_MATHEMATICS`

## Exact implication checked

The proposition assumes neither stationarily generated nor instant
approximate equilibria, and assumes arbitrary behavioral terminal
approximate equilibria at every accuracy. It concludes `CyclicOrbitCondition`:
at every requested error there is a finite positive-absorption cyclic
`F_epsilon` orbit all of whose tail payoffs are `epsilon`-rational.

The proof uses only:

- the corrected compact-near-feasible uniform-`rho` conclusion;
- the no-sure-quitter scale
  `exists_scale_without_sure_quitter_of_not_instant`;
- positive-solo survival forcing
  `exists_tailSurvival_lt_of_equilibrium_positiveSolo`;
- Proposition 42's floor-clipped no-jump estimate;
- `equilibrium_tail_rational`;
- `exists_supportPurifiedPrefixPath`; and
- `exists_cyclicOrbit_of_large_approximatePath`.

All named declarations are in `Literature/Simon2007.lean`. The latter four
relevant compiler lemmas are proved inside that non-built transcription, but
the corrected Lemma 2.1 theorem and final corrected Theorem 3 still end in
`sorry`. Thus the status is ordinary conditional mathematics, not a checked
Lean theorem.

## Scaling and compact carrier

A positive payoff scaling sends terminal payoffs, the quitting min--max
values, all terminal strategy payoffs, one-stage endpoint differences, and
orbit seams through the same positive factor. It therefore preserves each
qualitative branch while rescaling its error parameter.

Including `0`, all terminal reward coordinates, and all min--max coordinates
in the normalized finite set and making its diameter at most one ensures:

- every feasible actual tail lies in the same coordinate interval;
- every floor-clipped vector `max(r_i,chi_i-eta)` is within sup distance one
  of the feasible vector `r`; and
- all actual and clipped vectors used in Proposition 42 lie in one compact
  ball on which endpoint continuity is uniform.

For a literal formalization, choose the single constant `M` after this
normalization large enough to bound both the terminal rewards and this
clipped compact carrier (one may simply enlarge it). Then the same `d` works
both in Proposition 42 and in `exists_supportPurifiedPrefixPath`, while the
later choice `L_0<eta/(8M)` absorbs that enlargement. This is a ledger
clarification, not an extra hypothesis.

## Choices in `(C1)`--`(C2)`

Corrected Lemma 2.1 supplies a positive solo payoff `v_j` and
`0<rho<1`. Failure of the instant branch supplies `sigma>0`. The choices

```text
0<eta<=min(epsilon/5,rho,sigma),
beta=eta/4, e=eta/8
```

give `4*eta<=epsilon` and `beta+2e<=eta`. The large-path compiler supplies a
positive threshold `H`. Every upper bound used to choose `U`, `L_0`, and then
`alpha` is strictly positive. In particular the player count is positive
because the positive-solo player exists, so the inequality
`n*alpha/(s*beta)<L_0` is attainable.

No circular dependence occurs: `H` is chosen from the large-path compiler
after `eta,M`, then `U,s,L_0`, and finally the equilibrium accuracy `alpha`.

## First crossing and survival control

Apply `exists_tailSurvival_lt_of_equilibrium_positiveSolo` with survival
target `U`. The hypothesis it needs is exactly

```text
alpha < U*v_j/2.
```

Since `S_0=1>U`, the first `T` satisfying `S_T<U` is positive and obeys

```text
S_T<U<=S_(T-1).
```

At the crossing row Proposition 42 applies with
`u=S_(T-1)>=U`. Because

```text
n*alpha/(s*beta)<L_0<rho/2,
s=rho*U/2<U,
```

one has even

```text
n*alpha/(u*beta)<rho/2.
```

The corrected weak estimate from Proposition 42 therefore yields strictly

```text
1-Q(p_(T-1))>rho/2,
S_T=S_(T-1)*(1-Q(p_(T-1)))>rho*U/2=s.
```

For every earlier `t<T`, `S_t>=S_T>s`; applying Proposition 42 again gives

```text
1-Q(p_t) >= rho-n*alpha/(S_t*beta)
           > rho-n*alpha/(s*beta)
           > rho/2.
```

Thus the proof does not reintroduce a hidden macroscopic survival jump after
repairing only the final crossing.

## Logarithmic charge calculation

For `x=Q(p_t)` the preceding estimate gives
`0<=x<1-rho/2`. Hence

```text
-log(1-x) <= x/(1-x) <= 2*x/rho.
```

Summing and using the exact finite product identity for survival gives

```text
-log S_T <= (2/rho)*sum_(t<T) Q(p_t),
sum_(t<T) Q(p_t) >= (rho/2)*(-log S_T).
```

Since `S_T<U` and `U<exp(-4H/rho^2)`, both subsequent comparisons are strict:

```text
sum_(t<T) Q(p_t)
  > (rho/2)*(-log U)
  > 2H/rho.
```

The inequality orientation in `(C6)` is therefore correct.

## Rationality, seam budget, and exact variation

Every survival through date `T` is greater than `s`. The bound
`alpha<eta*s` is consequently stronger than the hypothesis of
`equilibrium_tail_rational` at every tail `0,...,T`. The prefix compiler may
therefore be invoked with common floor `s`.

With

```text
L=n*alpha/(s*beta),
```

its exact conclusions are

```text
z.totalError <= 2*M*L,
rho*(sum_(t<T)Q(p_t)-L) <= z.exactVariation.
```

The choices in `(C1)`--`(C2)` imply

```text
2*M*L < eta/4.
```

Also `sum Q>2H/rho` and `L<H/(2rho)`, so

```text
rho*(sum Q-L) > 3H/2 > H.
```

Thus `(C7)` and `(C8)` hold with room to spare. The path starts at the
feasible actual tail at date `T`, so its initial norm has the required reward
bound. Its states are `eta`-rational, and the no-sure condition required by
`exists_cyclicOrbit_of_large_approximatePath` follows by monotonicity from
`eta<=sigma`. All hypotheses of that compiler are now present, including
`4eta<=epsilon`, and its conclusion is exactly `CyclicOrbitCondition`.

## Endpoint tests and scope

- The proof deliberately chooses `alpha>0`; no division-by-zero issue is
  hidden at the `alpha=0` endpoint.
- If `T=1`, the logarithmic sum has one term and the same finite-product
  identity applies.
- Equality `1-Q=rho/2` cannot occur in the constructed crossing ledger:
  `n*alpha/(u*beta)<rho/2` is strict even though Proposition 42's general
  survival inequality is weak.
- The result is an equilibrium-to-cyclic-orbit necessity direction. It does
  not produce approximate equilibria for arbitrary reward data and therefore
  does not settle the finite-quitting uniform-equilibrium conjecture by
  itself.

## Verdict

The ledger `(C1)`--`(C8)` is correct. Conditional on the corrected
compact-set Lemma 2.1 and Proposition 42, Proposition 43 validly converts
arbitrary behavioral terminal approximate equilibria into the cyclic
`F_epsilon` alternative. I found no mathematical objection. The exact formal
status remains conditional ordinary mathematics because the corrected
literature theorem is not proved in Lean.
