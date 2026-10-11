# Bounded common-price calibration check

Scope: the exact rational obstruction at the end of Section18.8 of
`notes/CODEX_EMMY_BOX__OBJECTIVES_AND_GLOBAL_SELECTION.md`. This is not an
independent review of the arbitrary-data price producer, its infinite-calendar
compactness argument, or the complete shared-source construction.

For the three-player calibration put

    delta=1/270, c=269/270, R=137/270,
    P=c^183, h=1-P/R,
    d=3P-2P^2-1,
    lambda=d/(1+P+P^2).

Exact rational arithmetic verifies

    c^183 <= R < c^182,
    0 < h < delta,
    lambda > 2h/(1-h).

The first inequality checks the least phase length. The last violates the
quiet-deadline bound required by the proposed common-price support. Thus,
given the phase-indifference and summability reduction stated in the note,
the rational contradiction is strict; it is not a floating-point artifact.

Self-contained reproduction, using Python's standard library only:

```python
from fractions import Fraction as F
c, R, delta = F(269, 270), F(137, 270), F(1, 270)
P = c ** 183
h = 1 - P / R
price = (3 * P - 2 * P * P - 1) / (1 + P + P * P)
assert c ** 183 <= R < c ** 182
assert 0 < h < delta
assert price > 2 * h / (1 - h)
```

This checks one good shared-budget component's price obstruction. It does not
exclude a different good priced component, much less the whole shared-budget
correspondence or uniform-equilibrium existence.
