# Review of Section 17 of `CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY`

Reviewer: `CODEX_RAMSEY`

## Claim checked

Section 17 combines the checked compact `Fin 4` minimum semantic fiber with
the independently reviewed linear absorption--Nash-defect theorem.  It claims
a uniform debt alternative for every literal terminal-semantic carrier pair,
applies that alternative to the Section 16 stationary paid source, and records
the successor-linked approximate-path constants.

## Verdict

**PASS.**  The carrier/tail orientation, compact separation, factor `4`, and
successor-path constants are correct.  I found no mathematical or statement
repair.

The exact-root portion is principally a recombination (and, for exact roots,
a quantitative rederivation) of the already checked minimum-fiber debt moat.
The genuinely additional content is the approximate-root estimate and its
successor-linked aggregate-error consequence.  The section's own scope is
appropriately narrow and does not overstate this distinction.

## Compact minimum fiber and linear tube

Let `base` be the minimizer supplied by
`exists_finFour_minimumFiberIsolation_and_debtMoat_of_no_uniformPayoff` and
let

```text
M_* = quittingTerminalSemanticMinimumFiber reward base,
K   = fst '' M_*.
```

The carrier is compact by `quittingTerminalSemanticCarrier_isCompact`; the
fiber is its intersection with a closed debt level set, and the continuous
`fst` image `K` is compact.  The cited checked theorem supplies on every point
of this whole fiber one common positive singleton gap and uniqueness of the
all-Continue exact product root.  These are exactly the hypotheses of the
reviewed linear absorption theorem, so there are an open `N superset K` and
`c_*>0` satisfying

```text
c_* A(q) <= Def(V,q)
```

for every `V in N` and every product root `q`.  No carrier membership is
needed for the nearby payoff `V`; carrier membership enters only in the moat
argument.

The set

```text
Outside = Carrier intersect fst^(-1)(N^c)
```

is compact and disjoint from the whole minimum fiber.  If nonempty, total
semantic debt has a minimum `D_out>D_*` there.  Taking
`eta_*=(D_out-D_*)/2` gives exactly the stated alternative

```text
D(X) >= D_*+eta_*  or  X.1 in N.
```

Equality at the threshold is correctly assigned to the first arm.  If
`Outside` is empty, any positive `eta_*` works, as stated.

For a coordinatewise `epsilon`-root, the checked estimate

```text
Def(X.1,q) <= card(Fin 4)*epsilon = 4*epsilon
```

therefore gives `A(q)<=4 epsilon/c_*`.  At `epsilon=0`, absorption is zero;
for independent Boolean marginals this forces every Quit marginal to be zero,
so the root is literally all-Continue.  Its Bellman successor is the tail and
its charge is zero.

## Section 16 source and floor semantics

For the literal stationary profile `sigma` from Section 16,

```text
X_sigma = quittingTerminalSemanticPair reward sigma = (U,B)
```

is an actual carrier member, not merely a payoff vector.  Thus Theorem 17.1
applies to its literal prescribed coordinate `U`.  In the local arm every
exact root whose continuation tail is exactly `U` is all-Continue, so a
positive-charge exact Nash--Bellman edge at that tail is impossible.  This
uses the edge orientation correctly: the root is tested against the
continuation tail, while its successor is the current payoff.

The floor qualification is also exact.  A floor-admissible edge requires the
literal tail state itself to dominate `quittingPunishmentValue`; if `U` fails
that condition, no floor-admissible edge with tail exactly `U` exists.  If it
passes, the local exact arm contains only the zero-charge identity edge.
Neither clipping `U` nor replacing it by `B` preserves the asserted literal
semantic tail, so the section rightly refuses those substitutions.

## Approximate successor paths

Proposition 3 of the reviewed Ramsey note gives, for general finite `I`,

```text
E < c rho/(4 C |I|),
sum A(q_t) <= |I| E/c,
max_t ||V_t-V_L||_infinity <= 2 C |I| E/c.
```

Specializing to `I=Fin 4` yields precisely

```text
E < c_* rho/(16C),
sum A(q_t) <= 4E/c_*,
max_t ||V_t-V_L||_infinity <= 8CE/c_* < rho/2.
```

The backward induction is legal because the exact identities are oriented as
`V_t=Succ(V_(t+1),q_t)` and the terminal payoff is within the inner collar.
It derives membership of every continuation tail in `N`; it does not assume
that locality.  Aggregate error, rather than row count or maximum row error,
is the controlling quantity.

## Scope and relation to checked results

For exact roots, the checked declaration
`minimumFiber_debt_add_epsilon_le_of_carrierTail_exactRoot_absorption_pos`
already gives the same qualitative carrier-tail moat from its supplied tube.
Section 17 selects a possibly smaller linear-defect tube and reconstructs a
compatible moat, so its exact source barrier is a direct compact consequence,
not a new paid-row consumer.  Its useful strengthening is quantitative for
`epsilon`-roots and for successor-linked paths with small aggregate error.

Nothing here decides which arm contains the Section 16 source, makes `U`
floor safe, constructs an incoming nonlocal edge, converts the paid row into
a Bellman edge, or produces a payoff return.  Those nonclaims are stated
correctly.
