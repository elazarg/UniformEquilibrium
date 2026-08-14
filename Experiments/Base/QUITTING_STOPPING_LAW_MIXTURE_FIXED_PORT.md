# Fixed terminal-semantic ports under stopping-law mixtures

## Result

Complete stopping-law mixing has a projective flux geometry, and that
geometry preserves a useful exact port fiber.

For scalar endpoint hazards `a` and `b`, write

```text
S_lambda(t) = (1-lambda) S_a(t) + lambda S_b(t),
J_lambda(t) = (1-lambda) J_a(t) + lambda J_b(t),
```

where `S` is live survival and `J` is stopping flux. The reconstructed mixed
hazard satisfies the homogeneous equation

```text
h_lambda(t) S_lambda(t) = J_lambda(t)
```

even when `S_lambda(t)=0`. On a positive-survival row this is the projective
coordinate

```text
h_lambda(t) = J_lambda(t) / S_lambda(t).
```

Two exact face consequences are formalized.

1. At time zero, `S_lambda(0)=1`, so the mixed hazard itself is affine.
2. At any positive-survival date, if the two endpoint hazards agree, the
   mixed hazard equals that common hazard exactly.

Thus equal endpoint boundary roots are not disturbed by complete
stopping-law mixing.

The Lean development
`QuittingStoppingLawMixtureFixedPort.lean`
combines this root fact with payoff affinity and debt rigidity. If two
one-player endpoint profiles have the same:

- time-zero live product root;
- terminal prescribed-payoff vector; and
- terminal semantic-debt vector,

and the source is a global minimum of total terminal semantic debt, then
every point of their complete stopping-law mixture has exactly the same
payoff/root/debt tuple. On the common zero-debt face, the same conclusion
holds without separately assuming global minimality.

## 1. The projective coordinate is the right geometry

Rowwise interpolation of hazards repeatedly spends the interpolation weight
and is not affine in the terminal law. Complete stopping-law mixing first
interpolates the homogeneous coordinates `(survival, stopping flux)` and then
projectivizes:

```text
(S_a,J_a), (S_b,J_b)
        |
        | affine chord
        v
(S_lambda,J_lambda)
        |
        | J/S on S>0
        v
h_lambda.
```

This explains both the strength and the nonlinearity of the construction.
Terminal mass and payoff see the affine homogeneous coordinates. A live
root at an internal date sees their ratio.

The ratio causes no boundary mismatch on a common-root face. If

```text
h_a(t) = h_b(t)
```

and `S_lambda(t)>0`, then

```text
J_a(t) = S_a(t) h_a(t),
J_b(t) = S_b(t) h_a(t),
```

so `J_lambda(t)=S_lambda(t)h_a(t)` and the projectivized mixed hazard is the
same root. Time zero needs no positivity hypothesis because its survival is
one.

This is more useful than Fourier truncation here. The nonlinear coordinate
is a quotient of two affine flux coordinates, not an oscillatory signal whose
frequency tail is the main obstruction.

## 2. The exact fixed-port theorem

For this experiment, the entrance port of a behavioral tail is the raw tuple

```text
(
  terminal prescribed payoff,
  time-zero live product root,
  terminal semantic debt
).
```

The root is stored as Boolean PMFs rather than as `QuittingRootSimplex`; the
two presentations carry the same product-root data.

Assume the source and target have equal ports. Prescribed payoff is affine,
so it stays fixed. The time-zero root is affine, so it stays fixed. For
debt, coordinatewise convexity gives

```text
D_lambda(i) <= (1-lambda) D_source(i) + lambda D_target(i)
             = D_source(i).
```

If one coordinate were strictly smaller, summing would give total debt
strictly below the source. Global minimality rules this out. Therefore

```text
D_lambda(i) = D_source(i)
```

for every player and every mixture weight.

This yields a genuine equivalence-class geometry. Inside the global
minimum-total-debt set, profiles with the same terminal semantic port form a
class which is closed under any legal one-player stopping-law segment whose
endpoint time-zero roots agree. If such a class contains two distinct
realizations, it contains the entire continuum between them while its port
remains literally fixed.

On the zero-debt face the conclusion is even cleaner: nonnegativity plus the
convex upper bound forces every mixed debt to remain zero. Equal endpoint
payoff and root then fix the whole terminal semantic port.

## 3. Why this is relevant to fixed neighbours

The previous enriched compression theorem could replace a whole seam but
could not keep its original external neighbours. The new theorem identifies
a condition under which stopping-law motion has **zero external terminal-port
displacement**. It is therefore a candidate internal deformation direction:
change chronology or absorption law inside a nontrivial port fiber without
changing the port seen from outside.

This sharpens the search target. One no longer needs a universal local
inverse for arbitrary anchor errors. A sufficient alternative is to find
two distinct legal middle realizations which:

```text
share the required external terminal-semantic port,
share the boundary root,
and lie on the same minimum-total-debt fiber.
```

Their stopping-law segment then stays in that fiber exactly. The finite
witness passports from E74 control all off-face behavioral inequalities along
the segment by finitely many affine charts.

## 4. The remaining limitation after the exact-D bridge

The later exact-D/terminal-semantic bridge now proves that, for every
preterminal boundary of a production zero-boundary finite chain completed by
all-Continue, `QuittingBehaviorTerminalPort` is exactly the raw-root
presentation of the production `QuittingDebtPoint` anchor. In particular,
its infinite-horizon semantic-debt coordinate is the recursively defined
finite exact-D costate, at every displayed boundary.

This closes the semantic mismatch, but not fixed-neighbour repair.

- The theorem fixes one entrance live root/port, not an independently
  prescribed pair of entry and exit ports or an arbitrary two-ended list of
  marked internal roots.
- It does not preserve the marked-stage graph, terminal packet, holonomy, or
  an independently prescribed exit anchor.
- A stopping-law mixture of two exact-chain endpoints need not itself satisfy
  every local Nash--Bellman edge equation, even when its behavioral port is
  fixed.
- Most importantly, it does not prove that a fixed-port class contains two
  distinct realizations.

Accordingly, it would be wrong to call this a fixed-neighbour seam-repair
theorem. It is an exact **terminal-semantic port-preservation theorem** and a
reduction of seam repair to two-ended fiber multiplicity and exact-chain
closure. See
[`QUITTING_DYNAMIC_DEBT_TERMINAL_SEMANTIC_BRIDGE.md`](QUITTING_DYNAMIC_DEBT_TERMINAL_SEMANTIC_BRIDGE.md).

## 5. Revised next question

The next concrete question is now:

```text
For a pair of exact-D ports arising at a compressed seam, can one find two
distinct finite or eventually finite realizations with the same entry and
exit ports, and deform between them while remaining inside—or returning
exactly to—the local Nash--Bellman chain class?
```

There are three plausible ways forward.

1. **Same-port loop extraction.** Use recurrence or a dimension argument in
   the bounded enriched codebook to force two distinct realizations in one
   port fiber.
2. **Exact-chain fiber closure.** Determine whether a same-port stopping-law
   segment stays in the finite Nash--Bellman carrier, or construct an exact
   decoder back into that carrier.
3. **Two-ended flux chart.** Store boundary roots by homogeneous
   survival/flux equations. Shared-root constraints become polynomial
   cross-product identities, while the finite witness passport handles the
   remaining best-response inequalities.

The first genuine obstruction to check is fiber injectivity: there may be
ports for which the enriched realization map has a singleton fiber. The
fixed-port theorem says what to do when multiplicity exists; it does not
guarantee multiplicity.

## 6. Lean inventory

The experiment formalizes:

- the homogeneous mixed-hazard identity `h_lambda S_lambda = J_lambda`;
- exact time-zero hazard affinity;
- preservation of a common endpoint hazard on positive-survival rows;
- literal preservation of the full time-zero live product root when the
  endpoint mover roots agree;
- exact preservation of the terminal payoff/root/debt port on a common
  global minimum-total-debt fiber; and
- the zero-debt fixed-port specialization.

All printed capstones compile without `sorry` or `admit` and use only
`propext`, `Classical.choice`, and `Quot.sound`.
