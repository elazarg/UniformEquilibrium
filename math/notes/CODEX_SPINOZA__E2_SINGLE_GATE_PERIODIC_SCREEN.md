# A single-gate successor to the closed E1 table

Author: `CODEX_SPINOZA`

Status: **exact destruction of the reviewed E1 period-three certificate, plus
numerical stationary/period-two/period-three/period-four screens.  This is a
search seed only.  No exact exclusion of those other channels and no positive
unrestricted lower gap are claimed.**

This note is separate from the frozen and reviewed
[`CODEX_SPINOZA__E1_OVERLAPPING_PERIOD_THREE_CLOSURE.md`](CODEX_SPINOZA__E1_OVERLAPPING_PERIOD_THREE_CLOSURE.md).

## 1. Exact seed

Let `rE` be the E1 table displayed in the linked note.  Define `rE2` by the
single rational change

```text
rE2_0({0,1,2}) = 8                                      (1.1)
```

in place of `rE_0({0,1,2})=1`.  Every other one of the 59 reward coordinates
is unchanged.

The coordinate in (1.1) was not chosen blindly.  For the E1 support word

```text
{1,2}|{0,1,3}|{0,2,3},                                 (1.2)
```

it is absent from every on-path Bellman value and all eight active endpoint
equations.  It enters only player 0's inactive Quit endpoint at phase zero,
with coefficient `a*b` in the actual gap and `D*a*b` in its cleared
numerator.

### Proposition 1.1 (the certified E1 block is exactly destroyed)

On the rational root box `X` of the E1 closure, the eight active equations
for `rE2` are literally the same as for `rE`.  At every point of `X`, however,
player 0's phase-zero inactive cleared gap is strictly positive.  Thus no
active root in that box can make (1.2) a cyclic Nash--Bellman certificate for
`rE2`.

**Proof.**  The support-incidence assertion follows directly from (1.2).
The reviewed E1 interval certificate gives

```text
F^E_00 > -477/1000,   D>9/10,   a>35/100,   b>1/4.     (1.3)
```

Changing (1.1) adds exactly `7*D*a*b`.  Hence

```text
F^E2_00 > -477/1000 + 7*(9/10)*(35/100)*(1/4)
         = 297/4000 > 0.                               (1.4)
```

The active equations are unchanged, while the calculation proves the strict
failure throughout `X`.  This proves the claim.  \(\square\)

The statement is deliberately local to the support and box.  It does not
exclude another root of the same support outside `X`.

## 2. Independent numerical screens

I reconstructed cyclic terminal values from the exact rational table, formed
all Quit-minus-Continue endpoint gaps, and solved the active equations by
damped Newton steps from deterministic pseudorandom interior starts.  Every
reported candidate was checked against all inactive and sure-player signs.

The following searches returned no feasible root:

* all 15 nonabsorbing-excluded pure stationary profiles, by direct endpoint
  sign evaluation;
* all 65 stationary support faces containing at least one mixed hazard, with
  30 interior starts per face;
* all 3,120 non-pure period-two support words modulo phase rotation, allowing
  hazards `Never`, strictly mixed, or sure, with eight interior starts per
  face;
* all 1,135 period-three `Never/mixed` support words modulo phase rotation,
  with ten starts on active count at most eight and fifteen starts on active
  count at least nine;
* a deterministic sample of 1,200 period-three faces allowing `Never`,
  strictly mixed, and sure hazards, with one to eight mixed coordinates and
  six starts per face;
* a deterministic sample of 1,000 period-four `Never/mixed` support words
  having between five and ten active hazards, with five starts per word; and
* a deterministic sample of 800 period-five `Never/mixed` support words
  having between six and twelve active hazards, with five starts per word.

These are numerical non-detections, not exact exclusions.  In particular the
period-three sure-hazard screen and the period-four/period-five screens are
only samples.  Finite-period absence, even if later certified, would still
not be an unrestricted negative certificate.

## 3. Why this is a useful next seed

The one-coordinate deformation is outside the explicit E1 neighborhood and
crosses a literal inactive Nash gate without moving that support's active
root.  Unlike simultaneously raising all four analogous gate coordinates,
it did not immediately create a numerical stationary root.  It has also
survived a complete numerical period-two face pass and the complete
`Never/mixed` period-three support pass.

The next exact work should proceed in this order:

1. rerun the exact `3^4` stationary face elimination for (1.1);
2. exactify the full period-two face screen, especially singular and sure
   faces;
3. search period-three sure-hazard faces and broaden period four before any
   lower-gap computation; and
4. if a periodic locator appears, isolate its exact support and use a rational
   Miranda/Krawczyk box rather than treating floating-point residuals as a
   certificate.

Sources inspected:

* `notes/CODEX_NEGATIVE_CERTIFICATE__ASYMMETRIC_STATIONARY_SEAM_CLOSURE.md`;
* `notes/CODEX_SPINOZA__E1_OVERLAPPING_PERIOD_THREE_CLOSURE.md`; and
* `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.
