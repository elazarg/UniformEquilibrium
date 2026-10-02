# Strict inert source-relative debt orientation

Source: external response in `strict_inert/RESPONSE.md`.

## Status

The exact calculation below is valid ordinary mathematics from the checked
one-step prefix debt identity.  It sharpens the interpretation of the strict
normalized-inert toll but does not consume that node.  Its local wrong-sign
conclusion overlaps Section 6.2 of
[`CODEX_RIEMANN__NORMALIZED_INERT_SINGLE_DENSITY_TOLL`](CODEX_RIEMANN__NORMALIZED_INERT_SINGLE_DENSITY_TOLL.md);
the source-relative finite-stack identity is the useful additional normal
form retained here.

## Exact finite-stack account

Let a literal prefix word have semantic suffix states

```text
z_0, z_1, ..., z_N,
```

where `z_0` is the front state and `z_N` the retained tail.  At row `t`, let

```text
c_t     = joint Continue mass,
a_t     = 1 - c_t,
delta_t = total root Nash defect against cap(z_(t+1)),
L_0     = 1,
L_(t+1) = L_t c_t,
D_t     = total debt of z_t.
```

The exact one-step identity is

```text
D_t = c_t D_(t+1) + delta_t.
```

Therefore

```text
D_0 - D_*
  = L_N (D_N - D_*)
    + sum_(t<N) L_t (delta_t - D_* a_t).          (1)
```

This is just iteration plus

```text
1 - L_N = sum_(t<N) L_t a_t,
```

so there is no compactness, attainment, or strategy-class issue.

Two orientations follow.

1. If the retained tail is minimum, `D_N=D_*`, then an off-minimum front is
   financed by positive cumulative excess defect

   ```text
   sum L_t (delta_t - D_* a_t) = D_0-D_* > 0.
   ```

   This has the opposite sign from the absorption surplus consumed by the
   punishment-floor near-return compiler.

2. If the front is minimum, `D_0=D_*`, then

   ```text
   sum L_t (D_* a_t - delta_t) = L_N (D_N-D_*).
   ```

   This orientation is useful only when one literal chronology genuinely
   advances from the minimum front to the displayed suffix.  Independent
   prefix descendants converging in a closed carrier do not supply that
   source-to-suffix attachment.

## Consequence for normalized strict inertness

At a strict point of debt `D_p>D_*`, the positive-slack toll says locally

```text
D_p a(x) <= delta_p(x).
```

Hence every absorbing root in the toll region satisfies

```text
delta_p(x) - D_* a(x) >= (D_p-D_*)a(x) > 0.
```

Thus the toll explains the cost of keeping a prefix descendant above the
minimum.  It does not directly produce positive admissible absorption charge.
Reversing the edge would not be a legal Nash--Bellman operation, and positive
absorption surplus for a defect-bearing behavioral root does not itself
produce a positive-absorption exact root.

The saturation equality which halves normalized marked-mass density remains
a possible rank only after constructing a complete child source on the same
literal chronology with a fixed positive density floor.  The current carrier
point does not provide that renewable source.

## Remaining question

Can one literal source-attached finite stack with a signed relative-debt
surplus be transformed into either:

- an exact punishment-floor Nash--Bellman chronology with compatible seams
  and fixed positive surviving absorption charge; or
- a complete child minimum source with a renewable finite rank?

Any such theorem must prove exactification, seam compatibility, and charge
preservation together.  The toll inequality alone has the wrong sign.

