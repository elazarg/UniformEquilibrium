# Export-gate strengthening review of `SHADOW.md`

Reviewer: `CODEX_GATE_STRENGTHENER`

## Claim reviewed

I independently checked the three mathematical claims proposed for export:

1. universal inhabitance of the present
   `QuittingBudgetStablePacketSystem` interface;
2. the all-behavior lower bound on implementing a coordinatewise small-debt
   semantic seed by an actual profile; and
3. the total-debt and one-coordinate drift telescopes for a compatible packet
   chain.

I inspected:

* `QuittingBudgetStablePacketData`,
  `QuittingBudgetStablePacketSystem`, and
  `QuittingBudgetStablePacketSystem.exists_chronologicalDebtShadowingCertificate_of_seed`
  in
  `UniformEquilibrium/Quitting/Debt/Dynamic/BudgetStableCompatiblePacketIteration.lean`;
* `quittingTerminalSemanticPair_rootThenContinuation` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` and
  `quittingRootThenContinuationProfile_stationary` in
  `UniformEquilibrium/Quitting/Stationary/Root.lean`;
* `IsOperationallySublinearCost`,
  `exists_budgetedDivergentCostSchedule`, and
  `isOperationallySublinearCost_iff_exists_vanishing_schedule` in
  `MathUE/SublinearCostSchedule.lean`;
* the direct-seam results in
  `UniformEquilibrium/Diagnostics/Quitting/PositiveMinimumSeedSeamBarrier.lean`;
* the question
  `questions/FIN4_TWO_TIER_CHRONOLOGICAL_SHADOWING.md`; and
* the earlier interface and Tier-II analyses in Sections 6AO, 6BG, and 6BH of
  `notes/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md`.

## Verdict

`SHADOW.md` in its present wording: **FAIL**.

A corrected and strengthened packet containing the exact results below:
**CONDITIONAL PASS**, subject to the explicit gate conditions at the end of
this review.

The mathematics contains one exact interface characterization and two clean
necessary-condition theorems.  It does not construct either tier of the
shadowing producer, and it does not construct an admissible payoff return.
Its conjecture-facing value is instead a strict no-go: the current formal
Tier-I target carries no provenance information, and any repaired target that
really transports persistent positive drift through a summable-seam schedule
must also transport an unbounded cumulative amount of internal debt drain.

## 1. Sharp interface theorem

The Fin4 construction in the note generalizes and admits an exact converse.

### Theorem A: exact inhabitance criterion

Let `I` be a finite player set and let `r` be any quitting reward table.  Then

```text
Nonempty (QuittingBudgetStablePacketSystem r)
  iff
2 <= |I|.
```

The forward implication is immediate from the two fields `first`, `second`
and `labels_ne`.

For the reverse implication, choose distinct players `a,b`.  Let `q` be the
product root at which every player Quits with probability `1/2`, let
`sigma` be its stationary behavioral profile, and put

```text
z = quittingTerminalSemanticPair r sigma.
```

Use a singleton port, constant annotation `z`, radius one, zero `omega` and
`chi`, `kappa=1/2`, labels `a,b`, and at every legal scale use the one-row
block with root `q`, both candidates equal to `z`, and the unique port as
successor.

The stationary splice identity and the complete terminal-semantic prefix
identity give

```text
z = quittingTerminalSemanticPrefix r q z,
```

including every unrestricted cap coordinate.  Actual terminal semantic debt
is nonnegative.  If every reward coordinate has absolute value at most `R`,
then both the prescribed payoff and the cap have absolute value at most `R`,
so the debt has absolute value at most `2R`.  Thus a common bound exists.
For every `0<h<1`, both displayed label hazards equal `1/2` and hence dominate
`kappa*h`.  Zero cost is operationally sublinear.

This proves every declared field.  The result is stronger than the note's
Fin4 statement and is sharp at cardinality one.

### Necessary correction about the atom and reach bullets

The all-half stationary example also has joint-Continue probability
`2^(-|I|)` and stage-zero probability `2^(-|I|)` for each prescribed
coalition.  These are correct external facts.  They are **not fields** of
`QuittingBudgetStablePacketSystem`: the interface stores neither an actual
profile nor an atom.  The export must say that their absence is part of the
specification defect, not that those bullets verify packet fields.

### Novelty boundary

Section 6AO of the earlier Ramsey note already identified the missing
upper-mesh/provenance information and constructed a conditional one-port
fixed-word system.  The new content here is the unconditional stationary
self-loop and the exact cardinality characterization.  An export must cite
that overlap rather than present the general specification diagnosis as new.

## 2. Sharp all-behavior implementation bound

The cleanest statement is first a general finite-player algebraic theorem and
only then its positive-minimum corollary.

### Theorem B: one-sided semantic implementation

Let `I` be finite, `z=(u,b)` a semantic pair, and `sigma` an actual behavioral
profile.  Let `U(sigma)` be its prescribed terminal payoff and `B(sigma)` its
complete unilateral behavioral cap, including Never and arbitrary late or
history-dependent stopping.  Suppose, for every player `i`,

```text
b_i-u_i <= eta,
U_i(sigma) >= u_i-alpha_i,
B_i(sigma) <= b_i+beta_i.
```

Then

```text
d_i(sigma) <= eta+alpha_i+beta_i
```

and therefore

```text
D(sigma) <= |I|*eta + sum_i (alpha_i+beta_i).       (B1)
```

No compactness, chronology, or stationarity is used.  If `D_*` is any lower
bound on the debt of actual profiles, then

```text
D_* <= |I|*eta + sum_i (alpha_i+beta_i).            (B2)
```

For Fin4 this is the displayed `4*eta` inequality in the note.

If `D_*>|I|*eta` and the player set is nonempty, (B2) also yields the useful
localized forms

```text
exists i, (D_*-|I|*eta)/|I| <= alpha_i+beta_i,
```

and, when `alpha_i,beta_i >= 0`,

```text
exists i,
  (D_*-|I|*eta)/(2*|I|) <= alpha_i
  or
  (D_*-|I|*eta)/(2*|I|) <= beta_i.
```

Thus the Fin4 symmetric constant `1/8` is optimal for this purely one-sided
accounting argument.

### Boundary tests for Theorem B

* With zero implementation error, (B1) reduces to `D(sigma)<=|I|*eta`.
* For a one-player table with solo reward one and the Never profile,
  `U=0`, `B=1`.  Taking the seed `(u,b)=(0,0)`, `eta=0`, `alpha=0`,
  `beta=1` gives equality.  Taking `(u,b)=(1,1)`, `alpha=1`, `beta=0`
  gives equality on the other side.  Hence neither the payoff error nor the
  cap error can be omitted, and their coefficients cannot be improved in the
  general statement.
* The positive-minimum corollary cannot be supplied with a known sharp table,
  because a finite quitting table with `D_*>0` would itself be a counterexample
  to the open conjecture.  The export must not pretend otherwise.

### Relation to existing work

The checked direct-seam theorem is narrower.  Sections 6BG--6BH of the Ramsey
note already give a stronger obstruction for the particular persistent
same-root summable-seam architecture.  Theorem B is still useful because it
is independent of how an implementation was constructed, but the export must
describe it as a reusable one-shot all-behavior bound, not as the first
discovery that Tier II is UE-strength.

As a corollary, if a family of actual implementations has `eta -> 0` and
total implementation error tending to zero, then its actual total debt tends
to zero.  The checked terminal-Nash selection theorem then gives a uniform
equilibrium payoff after compactly selecting the terminal payoff target.
This corollary is a consequence, not an assumed adapter.

## 3. Sharp drift telescope

The argument is valid for every finite player set and has a stronger exact
finite-prefix form.

### Theorem C: total-debt internal-drain account

Consider a compatible chain of packet annotations `x_n`, terminal candidates
`e_n`, positive scales `h_n`, marked internal candidates `m_n`, and residuals
`rho_n`.  Suppose

```text
D(m_n)-D(x_n) >= c*h_n-rho_n,                       (C1)
```

and the endpoint seam obeys the current packet field

```text
for every i,
  |e_n.U_i-x_(n+1).U_i| + |e_n.B_i-x_(n+1).B_i|
    <= omega(h_n).                                  (C2)
```

Put

```text
R_n = max(0,D(m_n)-D(e_n)).
```

Then for every `N`, with `q=|I|`,

```text
sum_(n<N) R_n
  >= c*sum_(n<N) h_n
     -sum_(n<N) rho_n
     +D(x_0)-D(x_N)
     -q*sum_(n<N) omega(h_n).                       (C3)
```

This is sharper than immediately replacing the endpoint term by a global
bound.  If each coordinate debt lies in `[0,M]`, then

```text
sum_(n<N) R_n
  >= c*sum_(n<N) h_n
     -sum_(n<N) rho_n
     -q*M-q*sum_(n<N) omega(h_n).                   (C4)
```

If `sum h_n` diverges while `sum rho_n` and `sum omega(h_n)` converge, then

```text
sum_n R_n = infinity.                               (C5)
```

More quantitatively, for every `epsilon>0`, infinitely many `n` satisfy

```text
R_n >= (c-epsilon)*h_n.                             (C6)
```

Otherwise the tail of `sum (R_n-c*h_n)` would tend to minus infinity,
contradicting (C3).

### Literal Bellman-row strengthening

To justify the word "chronological", require `m_n` to be a stored candidate
at a mark before the packet endpoint.  For every row `t` from that mark to the
endpoint define

```text
r_(n,t) = max(0,D(candidate(n,t))-D(candidate(n,t+1))).
```

Then the elementary positive-part telescope gives

```text
R_n <= sum_(t from mark_n to end_n-1) r_(n,t).
```

Every such row satisfies the packet's exact semantic Bellman-prefix identity.
Consequently (C5) strengthens to divergence of the sum of positive total-debt
drops over literal exact-Bellman rows.  This is the strongest conclusion
supported by the argument.  It is still not prescribed-payoff charge,
punishment admissibility, or semantic recurrence.

### Theorem D: one-coordinate account

For a fixed coordinate `j`, assume

```text
d_j(m_n)-d_j(x_n) >= c*h_n-rho_n
```

and define

```text
R_n^j = max(0,d_j(m_n)-d_j(e_n)).
```

Then

```text
sum_(n<N) R_n^j
  >= c*sum_(n<N) h_n
     -sum_(n<N) rho_n
     +d_j(x_0)-d_j(x_N)
     -sum_(n<N) omega(h_n).                         (D1)
```

If coordinate debt lies in `[0,M]`, the endpoint contribution is at least
`-M`.  If the intended support-entry hypothesis is actually
`d_j(x_n)=0` for every `n`, that contribution is exactly zero; the `-M` in
the current note is then unnecessary.  The export must state which version is
intended rather than mixing them.

The same literal-row localization applies coordinatewise.

### Boundary tests for Theorems C--D

* Exact compensation is sharp: take `x_n=e_n=0`, `m_n=c*h_n`, and
  `rho_n=omega(h_n)=0`.  Then `R_n=c*h_n` and (C3) is equality.
* A terminate-at-the-mark construction has `e_n=m_n`.  If it also has a
  summable seam to `x_(n+1)`, persistent positive drift and bounded `x_n`
  contradict (C3).  This is the exact frozen-packet no-go.
* A direct reprojection can pay the drift through the seam by taking
  `x_n=x_(n+1)=0`, `m_n=e_n=c*h_n`; but then the semantic endpoint cost is
  order `h_n` and cannot be summable along a divergent scale schedule.  This
  tests the coefficient and the distinction between operational sublinearity
  along a selected schedule and a pointwise `o(h)` assertion.

## 4. What the results do and do not change

The exact conjecture-facing narrowing is:

```text
current formal packet interface
  -> no source attachment at all;

source-attached compatible packet with persistent marked drift
  -> divergent cumulative internal exact-Bellman debt drain.
```

Therefore the following proposed completions of Tier I are eliminated:

* a stationary or frozen packet justified only by the present structure;
* a packet which stops at every positive-slope mark and has no later debt
  drain;
* direct return to the prior annotation using only a summable endpoint seam;
* a bounded monotone chain which carries every positive drift into the next
  successor without compensation.

What remains open is exactly the bridge from the forced internal debt drain
to one of:

* an admissible prescribed-payoff return consumed by the existing compiler;
* a renewable finite-rank transition; or
* a direct terminal approximate-equilibrium construction.

The results do **not** supply Tier I or Tier II from the entrance in
`FIN4_TWO_TIER_CHRONOLOGICAL_SHADOWING.md`.  They do not prove a logical
nonimplication from that entrance.  They show that the presently encoded
target is vacuous and that a nonvacuous repair has an unavoidable additional
chronological obligation.

## 5. Lean handoff

The narrowest theorem shapes are:

```text
nonempty_quittingBudgetStablePacketSystem_iff_two_le_card

quittingTerminalSemanticDebtSum_le_of_oneSidedImplementation

positiveMinimum_le_card_mul_seedDebt_add_implementationError

compatibleMarkedDrift_sum_positiveInternalDrain_ge

compatibleMarkedDrift_not_summable_positiveInternalDrain

compatibleMarkedCoordinateDrift_sum_positiveInternalDrain_ge
```

The scalar telescope can first be proved in `MathUE` for bounded real
sequences and then specialized to semantic debt.  The semantic specialization
uses the elementary Lipschitz lemma

```text
|D(z)-D(w)|
  <= sum_i (|z.U_i-w.U_i|+|z.B_i-w.B_i|).
```

The stationary inhabitance regression belongs in a diagnostics/specification
file, not as a constructor advertised as a meaningful game-data producer.
No theorem shape should include the desired source attachment, marked drift,
or admissible return as a structure field merely to prove it by projection.

## 6. Export PASS/FAIL conditions

### PASS only if all are satisfied

1. The packet is retitled and framed as an interface characterization and
   internal-drift obstruction, not as the shadowing producer.
2. Theorem A is stated in its sharp finite-player `iff` form, or the packet
   explicitly explains why it retains only Fin4.
3. The atom and successor-reach observations are labelled external facts, not
   packet fields.
4. Theorems C--D state every extra hypothesis: compatible successors, marked
   candidates, positive drift, summable residual, and bounded nonnegative
   debts.
5. "Return" is replaced by "internal exact-Bellman debt drain" everywhere
   unless an independent admissible-payoff bridge is proved.
6. Operational sublinearity is used only through its selected vanishing
   divergent schedule; no pointwise `omega(h)=o(h)` claim remains.
7. The source audit acknowledges Sections 6AO and 6BG--6BH and identifies the
   exact sharpening rather than claiming the whole diagnosis as new.
8. The export includes the positive and negative boundary tests above and an
   independent adversarial review with no unresolved objection.
9. The conjecture-facing section says only that these theorems eliminate the
   listed frozen/no-drain architectures and sharpen the named two-tier
   shadowing obligation.

### FAIL if any of the following remains

* "the full producer does not follow from the entrance" is presented as a
  proved logical nonimplication;
* divergent debt drain is called a charged or admissible payoff return;
* the current packet structure is said to store actual profiles, atoms, or
  source matching;
* the drift telescope is presented as unconditional on the marked-drift data;
* the result is presented as supplying either requested tier; or
* the packet consists only of the interface-vacuity example, which by itself
  is primarily a specification regression and overlaps prior Section 6AO.

Under these conditions, the combined packet makes a strict and permanent
change to the named shadowing boundary.  Without them, it fails the export
gate as an overclaimed interface audit or an unconsumed local lemma.
