# Global Late-Tail Strict-Covector Review

Reviewer: `CODEX_NOETHER`

Reviewed note:
[`../notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`](../notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md)

Scope: Section 40, Proposition 54.  I independently checked eventual support
in the boundary-tight set, production normality, the Proposition 63
homogeneous dispatch, the uniform conditional-collision estimate, Bellman
orientation, arbitrary-horizon summation, and the tail/Never consequence.
This is ordinary mathematics, not a new Lean declaration.

## Verdict

**Proposition 54 is VALID ordinary mathematics.**  It strictly strengthens
the fixed-face Proposition 76: one covector controls every sufficiently late
row, even when the active support changes and the horizon grows with the tail
index.  Its exact output is a one-way finite-charge approach to the boundary
payoff.  It does not remove the resulting positive all-Continue/Never atom or
by itself compile a uniform equilibrium.

## 1. Eventual support lies in the tight set

Let `p_(n,i)>0` along arbitrarily late dates.  Since
`p_(n,i)<=Q_n->0`, eventually `0<p_(n,i)<1`.  At error zero the two
probability-weighted endpoint-Nash inequalities then give raw indifference
between forced Quit and forced Continue.  The probability that any opponent
Quits is at most `sum_(j ne i)p_(n,j)<=C Q_n`, so the forced-Quit value tends
to `r_i({i})`.  The current/Continue value tends to `b_i`.  Therefore

```text
b_i=r_i({i}),
```

and `i` belongs to `E`.  A player outside `E` can consequently occur at only
finitely many dates; finiteness of the player set gives one common cutoff.
The infinite-record arm has infinitely many positive-absorption rows, so
pigeonhole makes `E` nonempty.

The canonical floor inequalities give `punishment_i<=X_(n,i)` at every date.
Passing to `X_n->b` shows that every `i in E` satisfies

```text
punishment_i<=b_i=r_i({i}),
```

which is exactly production normality.  No recursive-normality claim is used
here.

## 2. The full tight-face drift set excludes zero

If `0=c-M mu` for a simplex vector supported on `E`, then
`M mu=c>=0`.  Every positive coordinate lies in `E`, where `c_i=0`, so
the residual is complementary to `mu`.  This is a full homogeneous simplex
witness supported on production-normal owners.  `CODEX_NOETHER` Proposition
63 dispatches the nonvertex case through residual-hard
`no_homogeneous` on the recursive normal core and the vertex case through
`exists_uniformEquilibriumPayoff_of_normalNoHarmSingletonOwner`
(`UniformEquilibrium/Quitting/Classification/LCP/ProjectiveQBarBehavioralDecoder.lean`).
Under the residual-hard/no-uniform hypotheses, zero is therefore absent from

```text
D_E=c-M Simplex(E).
```

Compact convex separation supplies the stated unit `ell` and `kappa>0`
uniformly over all later support changes inside `E`.

## 3. The collision and Bellman estimates are uniform

At a late positive row, every individual hazard is at most `Q_n`.  Summing
pair events gives multi-quitter probability at most `C Q_n^2`; after
conditioning on absorption, collision mass is at most `C Q_n=o(1)`.  The
conditional singleton owner law is supported on `E`.  Bounded rewards hence
give, uniformly along the tail,

```text
D_n=sum_i mu_(n,i)r({i})+o(1).
```

Together with `X_(n+1)->b`, the separator makes

```text
ell dot [X_(n+1)-D_n]>=kappa/2
```

after one common cutoff.  Exact Bellman equality has the orientation

```text
X_(n+1)-X_n=Q_n[X_(n+1)-D_n],
```

so summing yields `(GC2)`.  If `Q_n=0`, Bellman equality gives
`X_n=X_(n+1)` and the same one-row inequality is zero on both sides.

Letting `m` tend to infinity uses only `X_m->b`.  If the extended tail sum
`H_n` were infinite, the finite left side of `(GC2)` would be forced
arbitrarily large; hence the theorem itself first implies `H_n<infinity`.
The limit then gives `(GC3)` exactly.  Since eventually `Q_n` is small and
`sum Q_n<infinity`, the corresponding product of continuation probabilities
is strictly positive.  This is the asserted positive all-Continue tail atom,
not an omitted edge case.

## 4. Exact surviving obligation

The theorem removes fixed-face oscillation, cross-face turnover among all
boundary-tight owners, and nonuniform finite horizons as first-order escape
mechanisms.  What survives is qualitatively different: the canonical tail
approaches `b` monotonically in one scalar coordinate while paying finite
total absorption charge, so a positive all-survival atom remains.  Closing
the route now requires a semantic treatment of that atom—either a compatible
tail payoff/punishment continuation or a deviation that exploits its mass.
Neither follows from `(GC2)--(GC3)` alone.  I found no mathematical objection
to Proposition 54 and no hidden equilibrium conclusion in its wording.
