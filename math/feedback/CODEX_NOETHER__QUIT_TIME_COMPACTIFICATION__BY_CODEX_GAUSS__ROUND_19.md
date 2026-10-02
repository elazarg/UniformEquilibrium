# Round 19 Feedback on Quit-Time Compactification

Reviewer: `CODEX_GAUSS`

Reviewed note: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: Section 55, Proposition 53 only.  I refreshed the conference board,
reconstructed the logarithmic-time rate representation, differentiated the
payoff kernel, checked the deleted-clock Snell identity and transversality
limit, and audited the uniqueness, normal-owner, and abnormal-owner adapters.

Status: **Proposition 53 is valid ordinary mathematics.**  I found no
mathematical objection.  The rates and the support implication should be read
almost everywhere, as the note already signals by defining the rates only
almost everywhere.  This review supplies no Lean or integration seal and does
not review Proposition 51's discrete decoder.

## Rate representation and support

Let `t=1-exp(-tau)`.  Literal singleton support of the continuous path and
absolute continuity give densities `a_j(tau)` with

```text
d pi_j(t) = a_j(tau) exp(-tau) d tau,
sum_j a_j(tau)=1
```

almost everywhere.  Dividing the remaining absorption measure by
`1-t=exp(-tau)` gives exactly

```text
gamma(tau)=integral_[tau,infinity)
  exp(-(u-tau)) sum_j a_j(u) reward({j}) du.
```

The measure-support statement from `(J3)` becomes
`a_i>0 -> gamma_i=s_i` almost everywhere.  No converse at zero density is
used.  The exponential kernel has total mass one because `sum a=1`, so the
formula is bounded and needs no unrecorded terminal atom at logarithmic
infinity.

## Deleted-clock identity

Differentiating the kernel at Lebesgue points gives

```text
gamma_i' = gamma_i-sum_j a_j reward({j})_i.
```

Since `reward({i})_i=s_i` and `a_i(gamma_i-s_i)=0` almost everywhere, this is

```text
gamma_i'=(1-a_i)gamma_i-sum_(j!=i)a_j reward({j})_i.
```

For

```text
R_i(T)=exp(-integral_0^T (1-a_i)),
```

one therefore has

```text
(R_i gamma_i)'=-R_i sum_(j!=i)a_j reward({j})_i
```

almost everywhere.  Absolute continuity and integration give `(K4)` with
the displayed orientation.

The terminal term comparison is also correct.  If player `i` waits until
log-time `T` and then Quits, its payoff is the opponent-absorption integral
through `T` plus `R_i(T)s_i`.  Sequential perfection gives
`gamma_i(T)>=s_i`, so this finite Quit time cannot beat `gamma_i(0)`.
Randomizing the stopping time cannot improve on the deterministic supremum.

The opponent integral is absolutely convergent, not merely conditionally:
if `M` bounds singleton rewards, then

```text
|R_i sum_(j!=i)a_j reward({j})_i|
  <= M R_i(1-a_i) = -M R_i',
```

whose integral is at most `M`.  Hence `R_i(T)gamma_i(T)` has a limit and the
Never payoff is the full opponent integral.  Subtracting `(K4)` gives the
exact sign in `(K5)`:

```text
Never_i-gamma_i(0)=-lim_T R_i(T)gamma_i(T).
```

## Exceptional owner and raw-data endpoint

Positive deleted survival is equivalent to

```text
integral_0^infinity sum_(j!=i)a_j < infinity.
```

Two distinct players cannot both satisfy it.  The condition for `i` makes
every `a_j`, `j!=i`, integrable; the condition for a second player makes
`a_i` integrable, contradicting `sum_j a_j=1` on an infinite interval.

For the unique possible exceptional `i`, the probability that the residual
exponential clock after `T` is owned by an opponent is bounded by

```text
integral_T^infinity sum_(j!=i)a_j,
```

which tends to zero.  The kernel formula therefore gives
`gamma(T)->reward({i})`.  Passing `gamma_k(T)>=s_k` to the limit yields the
full column inequalities

```text
reward({i})_k>=s_k
```

for every `k`.  In particular

```text
lim R_i(T)gamma_i(T)=R_i(infinity)s_i.
```

Thus positive Never debt occurs exactly when the unique exceptional owner has
positive deleted survival and negative solo.  The one-player negative-solo
test gives the same sign and magnitude.

If this owner is normal, the first half of reviewed Proposition 48 applies
directly: the column inequalities are its no-harm hypothesis for every
outsider, and no sign condition on the owner's solo is needed after the
finite-prefix punishment repair.  Hence the hard non-generated survivor is
indeed abnormal.

For an abnormal owner, Simon's `lemma3` gives

```text
reward({j})_i >= chi_i > s_i
```

for every `j!=i`, so the owner row of the normalized singleton matrix is
strictly positive.  This has the opposite orientation from the nonpositive
row blocker required by
`isQuittingStationaryUniformEquilibriumPayoff_of_nonnegative_column`
(`UniformEquilibrium/Quitting/Classification/LCP/LaterLayerAbnormal.lean`).
At the same time `(K6)` makes the owner column nonnegative.  The note's
row/column distinction and its conclusion that the named producer does not
compose are therefore exact.  The `lemma3` use remains ordinary
source-to-project mathematics from the non-built Literature lane, not an
integrated Lean adapter.

## Verdict and surviving obligation

Proposition 53 correctly reduces failure of global optimality along the
continuous zero-perfect path to one transversality datum.  After excluding
the generated branch, the precise survivor is a negative abnormal owner whose
singleton column weakly dominates all solo payoffs while its normalized
owner row is strictly positive.  This is a materially smaller universal
raw-data configuration, but it is not itself a strategy producer or a game
counterexample.
