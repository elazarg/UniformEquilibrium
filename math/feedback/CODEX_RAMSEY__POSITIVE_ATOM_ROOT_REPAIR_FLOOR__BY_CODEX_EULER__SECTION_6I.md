# Review of Proposition 6I of `CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR`

Reviewer: `CODEX_EULER`

Status: `VALID MINIMUM-SET TUBE ESTIMATE WITH CORRECT SCOPE`

## Debt transport

For one literal exact prefix, a deviator can use the prescribed current root
action and, conditional on joint Continue, switch to a tail best response.
Relative to the prescribed profile this realizes joint-Continue probability
times the tail semantic debt.  Hence, coordinatewise,

```text
joint survival * tail debt <= current debt.
```

Iterating over a finite word multiplies the joint-survival factors.  Summing
over the finite player set therefore gives exactly

```text
beta*D(z)<=D(x).
```

No player-deleted survival or unsupported equality is used here.

## Entry error and constants

If both prescribed and cap coordinates of `x` are within `delta` of those of
`x_*`, then each debt coordinate `B_i-U_i` differs by at most `2*delta`.
Summing gives

```text
D(x)<=D_*+2*n*delta.
```

Since `D(z)>=D_*`, division by `beta>0` and subtraction of `D_*` yield

```text
D(z)-D_* <= [D_*(1-beta)+2*n*delta]/beta.
```

The factor `2*n` and the denominator are therefore correct and unavoidable in
this direct argument.

## Compactness modulus

The minimum set `M_*` is nonempty and compact because the carrier is compact
and total debt is continuous.  For every `s>=0`, the sublevel
`{D<=D_*+s}` is compact and contains `M_*`, so the maximum defining `mu(s)`
exists.  If `mu(s_k)` failed to tend to zero for some `s_k downarrow 0`, a
convergent subsequence of maximizers would have limiting debt `D_*`, hence lie
in `M_*`; continuity of distance to the closed set would contradict their
fixed positive distance.  Thus the modulus assertion and the substitution
`beta=1-alpha` are valid.  Any substituted absorption upper bound must of
course remain below one so the displayed denominator is positive.

## Scope

The conclusion is only proximity to the whole minimum set.  It does not select
the original minimum point or preserve its component fiber, stopping-law ray,
mover, observer, terminal orientation, or atom.  Multiple minimum points can
carry incompatible such data.  Proposition 6I is therefore a genuine
actual-source tube invariant, not a reconnection theorem.  The note states
this limitation accurately.

I found no mathematical error in Proposition 6I.
