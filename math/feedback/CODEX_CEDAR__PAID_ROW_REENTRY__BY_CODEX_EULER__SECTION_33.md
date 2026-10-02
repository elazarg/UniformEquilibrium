# Focused feedback on Section 33 of `CODEX_CEDAR__PAID_ROW_REENTRY`

Reviewer: `CODEX_EULER`

## Scope and verdict

I independently checked only Section 33 / Proposition 33 for the fixed reward
table completed in Section 32.

**Verdict: VALID ordinary mathematics.**  The perturbation proves that the
existence, and even the maximal amount, of positive charge among exact roots
is not lower-semicontinuous in the diagonal tail payoff.  The stated scope as
a source-matching/Nashification adapter no-go is exact.

## Exact check

For every `epsilon>0`,

```text
U^epsilon=(epsilon,3/4,0,0)
```

dominates the punishment vector `P=0`, and `U^epsilon -> U` as `epsilon ->0`.
At this tail the Section 32 dominance chain remains strict:

1. For `m`, when no opponent Quits, Continue gives the tail coordinate
   `3/4` and Quit gives `1/2`.  Every nonempty opponent set has the same
   strict cellwise Continue advantage as in Section 32.  Hence `m` Continues
   in every exact product-Nash root.
2. With `m` continuing, `o` gets `epsilon>0` from Continue and zero from solo
   Quit if `h,k` Continue.  If at least one of `h,k` Quits, Continue gives one
   and joining gives zero.  Hence `o` also Continues strictly.
3. With `m,o` continuing, each of `h,k` gets zero from Continue and `-1` from
   Quit, whether or not the other inactive player Quits.

Thus all-Continue is the unique exact product-Nash root at every
`U^epsilon`; it is an exact self-loop and has charge zero.  At `epsilon=0`,
the observer becomes indifferent, and the Section 32 root in which only `o`
Quits is an exact charge-one self-loop at

```text
U=(0,3/4,0,0).
```

Consequently, if `C(v)` denotes the supremal charge among exact roots at tail
`v`, then

```text
C(U)>=1,       C(U^epsilon)=0,
```

so lower semicontinuity fails at `U`.

## Scope

The construction does not refute the paid-return producer: the limiting tail
`U` itself has the desired charged return.  It proves that mere convergence
of floor-admissible payoff tails to `U` cannot transport that charge to exact
roots at the approximating tails.  A successful Nashification therefore needs
a robust face sign, exact prescribed-payoff provenance, or a separate charged
row elsewhere in the path; endpoint seam tolerance alone does not make an
internal approximate root exact.
