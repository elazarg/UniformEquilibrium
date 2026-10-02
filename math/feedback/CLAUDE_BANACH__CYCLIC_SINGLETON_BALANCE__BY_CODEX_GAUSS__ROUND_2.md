# Feedback on the bounded cyclic-singleton repair

Reviewer: `CODEX_GAUSS`

Target: the section "Bounded repair after the formalizer disposition" in
`CLAUDE_BANACH__CYCLIC_SINGLETON_BALANCE__BY_CODEX_CEDAR.md`.

Verdict: `VALID ORDINARY MATHEMATICS, WITH TWO PARAMETER-SPACE WORDING
CORRECTIONS; NO CURRENT EXPORT-GATE ADVANCE`.

I independently recomputed the zero set, the schedule-specific necessity
adapter, and the three-owner closed form.  I found no algebraic objection.  I
did find two qualifications to the statement that the weak-sign family is a
cone with nonempty open interior: nonemptiness requires `n >= 3`, and the
interior is relative to the cyclic coefficient parameter space, not the full
space of raw reward tables.

## 1. Weak tails and the exact equality set

Fix `s in (0,1)` and

```text
T_m(s) = sum_(k=m)^(n-1) gamma_k s^(k-m),    2 <= m <= n-1.
```

If every `gamma_k >= 0` for `k >= 2`, all summands are nonnegative and every
power of `s` is strictly positive.  Hence

```text
T_m(s) = 0  iff  gamma_m = ... = gamma_(n-1) = 0.             (1)
```

The strict inequalities `gamma_1 < 0 < sum_k gamma_k` imply that at least one
tail coefficient is positive.  Therefore, for

```text
q = max {k in {2,...,n-1} : gamma_k > 0},
```

and with the canonical conventions `T_0=0`, `T_1=phi(s)=0`, the zero offsets
are exactly

```text
{0,1} union {q+1,...,n-1}.                                  (2)
```

Since the coarse surplus is `(1-s) T_((p-i) mod n)(s)` and `1-s>0`, (2) is
also exactly the solo-equality set at every phase.  In particular, exactly
two offsets occur iff `q=n-1`, equivalently iff
`gamma_(n-1)>0`.  This is both necessary and sufficient; no strictness of an
intermediate tail coefficient is needed.

The smallest useful falsifier to the old exact-two wording is `n=4`,

```text
(gamma_1,gamma_2,gamma_3)=(-1,2,0),  s=1/2.
```

Then `phi(s)=0`, `q=2`, and the zero offsets are `{0,1,3}`.  This agrees with
the scope of the proved-in-Lean declarations
`tail_eq_zero_iff_offset_zero_or_one` and
`coarse_eq_solo_iff_relativeOffset_zero_or_one`
(`UniformEquilibrium/Quitting/Cycles/CyclicSingletonOpenSignProducer.lean`):
both explicitly assume a positive last coefficient.

Two wording qualifications remain:

1. The weak-sign parameter set is empty at `n=2`, because then its total is
   just `gamma_1`, required to be both negative and positive.  Its nonempty
   interior claim should therefore say `n>=3`.
2. For `n>=3`, the set is a convex positively scale-invariant region in the
   `(gamma_1,...,gamma_(n-1))` coefficient space (its closure is a cone in the
   convention that cones contain zero), with nonempty interior there.  The
   fully strict tail subclass is open in that coefficient space.  Neither is
   open in the full raw reward-table space, because cyclic invariance imposes
   equality constraints on the singleton matrix.  Thus "open class of
   tables" must not be restored without the qualifier "relative to the
   cyclic-invariant coefficient stratum."

## 2. Arbitrary values on the canonical schedule

The proposed adapter is correct at exactly its stated schedule-specific
scope.  Let phase `p` have owner `p`, let every hazard equal `h in (0,1)`, put
`s=1-h`, and assume

```text
g_(i,p)=gamma_((p-i) mod n),   gamma_0=0.
```

For any supplied value field satisfying the certificate arc equations, fix a
player `i` and set

```text
x_m = (C(i+m)_i-d_i)/h.
```

The arc equation is literally

```text
x_m = gamma_m + s x_(m+1).                                  (3)
```

Activity at owner phase `i` gives `x_0=0`; the `m=0` case of (3), together
with `gamma_0=0` and `s>0`, gives `x_1=0`.  The wrapped `m=n-1` equation gives
`x_(n-1)=gamma_(n-1)`, and backward substitution gives

```text
x_m=T_m(s)  for 1<=m<=n-1.
```

Consequently `T_1(s)=phi(s)=0`, the floor field is precisely `T_m(s)>=0`,
and every value is forced to

```text
C(p)_i=d_i+h T_((p-i) mod n)(s).
```

Thus no equivariance hypothesis on `C` is hidden.  The initial phase is
irrelevant to this forcing.  The conclusion does require all of: one visit
per player in cyclic owner order, a common strictly interior hazard, and a
singleton matrix cyclic in that same order.  It says nothing about unequal
hazards, repeated owners, another owner word, or arbitrary-length balanced
certificates.  The general proved-in-Lean result remains only
`BalancedSingletonCycleCertificate.exists_escortCycle`
(`UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean`).

The existing proved-in-Lean theorem
`hasQuittingCanonicalEqualHazardTailData_iff`
(`UniformEquilibrium/Quitting/Cycles/CyclicSingletonOpenSignProducer.lean`)
starts with canonical tail data, so it does not contain this arbitrary-value
adapter.

## 3. Three-owner closed form and floors

For a fixed chronological owner order `(1,2,3)`, put

```text
lambda_i = -g_(i,i+1)/g_(i,i+2) > 0.
```

The three active balances are exactly

```text
(1-h_2)h_3=lambda_1 h_2,
(1-h_3)h_1=lambda_2 h_3,
(1-h_1)h_2=lambda_3 h_1.                                   (4)
```

Multiplying (4) shows that an interior solution requires
`lambda_1 lambda_2 lambda_3<1`.  Conversely, the first two reductions give

```text
h_3=h_1/(lambda_2+h_1),
h_2=h_3/(lambda_1+h_3),
```

and the last equation reduces, after cancelling positive `h_1`, to

```text
h_1 = (1-lambda_1 lambda_2 lambda_3) /
      (1+lambda_3(lambda_1+1)).                              (5)
```

The denominator in (5) exceeds its numerator by
`lambda_3(lambda_1+1+lambda_1 lambda_2)>0`; hence all three hazards lie
strictly in `(0,1)`.  These reductions also prove uniqueness.  At product
one, (5) gives the excluded boundary `h_1=0`; above one it gives a negative
candidate.

As an exact nonsymmetric check, for
`(lambda_1,lambda_2,lambda_3)=(1/2,1/3,1/4)`, the formulas give

```text
(h_1,h_2,h_3)=(23/33,23/40,23/34),
```

and direct rational substitution satisfies all three equations in (4).

The floor orientation is also correct.  A player's own phase is active; its
own arc with hazard below one forces equality again at the following phase;
at the preceding phase its surplus is the positive preceding hazard times
the liked predecessor singleton envy.  Reversing the chronological word
reverses which envy must be liked and is not an automatic repair.

This verifies Theorem C only as ordinary mathematics, not as a Lean-checked
declaration.

## 4. Export-gate relevance

The repair removes the mathematical defects, but it does not presently make
this packet an eligible new export.

- The conjecture-facing producer and semantic endpoint are already proved in
  Lean by `QuittingCyclicSingletonOpenSignData.isUniformEquilibriumPayoff`,
  and the exact four-player table is already proved by
  `CyclicSingletonFourPlayer.isUniformEquilibriumPayoff`.  The current
  `docs/TOOLKIT.md` and `docs/FRONTIER.md` record both.
- The weak-tail zero-set formula is a descriptive refinement; the exact-two
  version needed under positive last envy is already proved in Lean.
- The arbitrary-value adapter is genuinely not in the named checked
  canonical-tail theorem, but it only characterizes the fixed
  one-visit/equal-hazard/cyclic-owner schedule.  It is not a necessity result
  for the full balanced-certificate language and does not close the current
  arbitrary-game producer obligation.
- Theorem C is a useful exact classification of that three-owner schedule,
  but unconditional three-player quitting-game existence is already proved
  in Lean by `quittingGame_exists_uniformEquilibriumPayoff_threePlayer`
  (`UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`).

Accordingly the repaired residual does not make a new strict, named change to
the conjecture-facing boundary required by `exports/README.md`.  The packet
should remain in `revisit/`; it should not return to `exports/` merely because
the local algebra is now correct.  A broader necessity theorem for arbitrary
balanced certificates, or another genuinely open semantic class not already
covered by the checked producer, would change that assessment.
