# Review of Proposition 2 in `CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE`

Reviewer: `CODEX_RAMSEY`

## Verdict

**PASS**, with one orientation qualification on the prose consequence.  The
debt-gate exclusion, quantitative absorption estimate, and compactness
argument establish an open payoff neighborhood on which all-Continue is the
unique exact root.  The result is about arbitrary tail payoffs in that
neighborhood; they need not be terminal-semantic carrier points or punishment
floor points.

## Detailed audit

### 1. Exact roots at the plateau cap

For the positive minimum semantic pair `x=(U,B)`, the checked theorem
`minimumTerminalSemantic_exactNash_allContinue_or_debtGateSolo` applies to
every exact root at tail `U`.  A debt gate for player `i` says

```text
d_i = D,
B_i - s_i - D = 0.
```

Since `B_i=U_i+d_i`, these identities imply `U_i=s_i`.  Proposition 1 gives
the strict opposite inequality for every `i`, so there is no debt gate.
Equivalently,
`minimumTerminalSemantic_exactNash_eq_allContinue_of_no_debtGate` applies
directly.  Thus all-Continue is the unique exact root at `U`.

This step uses the carrier/minimum hypotheses only at the distinguished pair
`x`; it does not incorrectly assert that nearby tails are semantic carrier
points.

### 2. Quantitative lower absorption bound

Let

```text
delta = min_i (U_i-s_i) > 0
```

and choose any positive coordinate bound `M` for the terminal reward table
(for example enlarge `quittingRewardBound reward` by `1`).  If
`|V_i-U_i|<delta/2`, then `V_i-s_i>delta/2` for every `i`.

For a non-all-Continue exact root `q` at `V`, choose `i` with positive Quit
probability, and let `O_i` be the absorption probability of the opponents of
`i`.  Positive Quit support in an exact root gives the correct orientation

```text
0 <= Quit_i - Continue_i.
```

The exact outsider decomposition is

```text
Quit_i - Continue_i
  = (1-O_i)(s_i-V_i) + joining_i.
```

The terminal coordinate bound gives

```text
|joining_i| <= 2 M O_i.
```

Consequently

```text
(delta/2)(1-O_i) <= 2 M O_i,
delta <= (delta+4M) O_i,
delta/(delta+4M) <= O_i.
```

Finally `O_i` is bounded above by the joint absorption of `q`.  This verifies
both the sign and the constant in (4.3), including the pure/sure-Quit case:
exact Nash still compares that supported Quit action against the unused
Continue action.

### 3. Uniform open neighborhood

If no such neighborhood existed, finite-dimensional first countability would
give `V_n -> U` and non-all-Continue exact roots `q_n`.  After entering the
strict singleton box, the preceding estimate bounds every absorption mass
below by the same positive constant.  Compactness of the finite product-root
simplex gives a convergent subsequence.  Root payoffs and the exact Nash
inequalities are continuous jointly in tail and root, so the limit is exact
at `U`; absorption continuity keeps its absorption strictly positive.  It is
therefore not all-Continue, contradicting uniqueness at `U`.

Shrinking the neighborhood inside `V_i>s_i` ensures all-Continue itself is
exact at every nearby tail.  Hence it is the unique exact root throughout the
neighborhood.

### 4. Bellman consequence and orientation

For an exact Nash--Bellman edge whose **continuation/tail node** `V` lies in
the neighborhood, the root must be all-Continue.  Its successor is exactly
`V` and its charge is zero, so that edge is the identity.

The precise statement should retain this tail orientation.  It does not say
that an edge whose *head* lies near `U` has a nearby tail: a nonlocal outside
tail could in principle map to a head in the neighborhood.  In particular,
the theorem blocks local departures and any finite path whose terminal tail
is in the neighborhood (backward induction makes such a path constant), but
it does not exclude a nonlocal incoming edge from outside.  The current
claimed need for a nonlocal excursion is consistent with this qualification.

## Scope

Proposition 2 is a valid architecture obstruction, not a producer.  It proves
neither existence of a nonlocal exact predecessor nor return of an executable
carrier profile.  Its neighborhood can be shrunk inside the punishment floor
because Proposition 1 has strict floor slack, but floor admissibility is not
needed for the root-uniqueness proof itself.
