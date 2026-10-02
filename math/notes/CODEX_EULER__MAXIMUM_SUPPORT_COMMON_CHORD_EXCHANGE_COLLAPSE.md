# Maximum-support common chords collapse equal-debt exchange

**Identity:** `CODEX_EULER`

**Status:** `REVISE -> PASS after independent review; ordinary mathematics;
internal`

Independent review:
[`feedback/CODEX_EULER__MAXIMUM_SUPPORT_COMMON_CHORD_EXCHANGE_COLLAPSE__BY_CODEX_RAMSEY.md`](../feedback/CODEX_EULER__MAXIMUM_SUPPORT_COMMON_CHORD_EXCHANGE_COLLAPSE__BY_CODEX_RAMSEY.md).
Theorem 2.1 and the rank handoff passed; the repaired Corollary 2.2 below
retains the required carrier/minimum hypotheses on `X`.

## 1. Question and answer

Let `D_* > 0` be the global minimum of total terminal-semantic debt and let
`X` be a minimum carrier point whose positive-debt support has maximum
cardinality among all minimum carrier points.  Suppose actual source and
one-player replacement profiles approach `X` and a second minimum point `Y`
along one common complete-stopping-law chord.  If the replacement kills the
mover's debt, can `Y` replace that mover by a new positive-debt label while
keeping total debt equal to `D_*`?

No.  Minimum-fiber chord affinity makes the midpoint debt vector exactly

\[
                  d(Z)=\tfrac12d(X)+\tfrac12d(Y).
\]

Thus `supp(d(Z)) = supp(d(X)) union supp(d(Y))`.  Since `Z` is another
minimum point and `X` has maximum support cardinality, the union cannot be
larger than `supp(d(X))`.  Hence

\[
                 supp(d(Y))\subseteq supp(d(X)).
\]

If the mover is active at `X` and has zero debt at `Y`, this inclusion is
strict.  In particular, an equal-cardinality minimum-fiber exchange is
impossible whenever the reset retains a common actual chord, even if neither
endpoint is itself attained by a fixed behavioral profile.

This consumes the *same-source/common-chord* exchange arm into a genuine
support-cardinality decrease.  It does not source-match independently
reselected reset points, and it does not convert a support-label cycle into a
Nash--Bellman cycle.

## 2. Exact theorem

Let `I` be finite and let `r` be a finite quitting reward table.  Write
`Sem(sigma)` for the terminal semantic pair of an actual behavioral profile,
`d_i(V)=B_i-U_i`, `D(V)=sum_i d_i(V)`, and

\[
                  A(V)=\{i:d_i(V)>0\}.
\]

### Theorem 2.1 (maximum-support common-chord exchange collapse)

Assume:

1. `D_*` is the global minimum of `D` on the terminal-semantic carrier;
2. `X` and `Y` belong to that carrier and
   `D(X)=D(Y)=D_*`;
3. `A(X)` has maximum cardinality among all carrier points `V` with
   `D(V)=D_*`;
4. there are actual profiles `sigma_n`, one fixed mover `o`, and alternative
   complete behavioral strategies `tau_n` for `o` such that

   \[
   X_n=Sem(sigma_n)\to X,
   \qquad
   Y_n=Sem(sigma_n[o\leftarrow tau_n])\to Y;
   \tag{2.1}
   \]

5. `d_o(X)>0` and `d_o(Y)=0`.

Then

\[
                         A(Y)\subsetneq A(X).
\tag{2.2}
\]

The same conclusion holds if (2.1) is given only after a common subsequence.

### Proof

For every `n`, form the literal half-mixture of `sigma_n(o)` and `tau_n` as
the complete stopping law of player `o`, leaving every opponent strategy
unchanged.  Let its semantic pair be `Z_n`.  Compactness of the
terminal-semantic carrier supplies a subsequence `Z_n -> Z` with `Z` in the
carrier.

For every coordinate `i`, stopping-law debt convexity gives

\[
 d_i(Z_n)\le \tfrac12d_i(X_n)+\tfrac12d_i(Y_n).
\tag{2.3}
\]

Summing and passing to the limit gives `D(Z)<=D_*`.  Global minimality gives
the reverse inequality, so `D(Z)=D_*`.  Equivalently, apply the quantitative
minimum-fiber chord-gap estimate with source excess
`epsilon_n=D(X_n)-D_* -> 0` and endpoint rise
`D(Y_n)-D(X_n)->0`: every nonnegative coordinate chord gap tends to zero.
Consequently

\[
                  d_i(Z)=\tfrac12d_i(X)+\tfrac12d_i(Y)
\quad\hbox{for every }i.                              \tag{2.4}
\]

Every semantic debt is nonnegative.  Therefore (2.4) implies

\[
                         A(Z)=A(X)\cup A(Y).            \tag{2.5}
\]

The point `Z` is on the minimum fiber.  Maximality of `|A(X)|` gives
`|A(Z)|<=|A(X)|`, while `A(X) subseteq A(Z)` by (2.5).  Finiteness forces
`A(Z)=A(X)`, hence `A(Y) subseteq A(X)`.  Finally `o in A(X)` and
`o notin A(Y)`, so the inclusion is strict.  `QED`

### Corollary 2.2 (equal-cardinality exchange forces an excursion)

Keep hypotheses 1 and 3--5, retain that `X,Y` belong to the carrier and that
`D(X)=D_*`, but replace `D(Y)=D_*` by only `D(Y)>=D_*`.  If `A(Y)` contains a
newcomer outside `A(X)`, then `D(Y)>D_*`.

Indeed equality would invoke Theorem 2.1 and exclude the newcomer.  If `Y`
is a fixed compact cluster, the strict inequality has a fixed positive size
`D(Y)-D_*`; along the selected actual target subsequence the same fixed
off-minimum excess eventually persists.

For `Fin 4`, this removes the need to seek a four-label cycle in the exact
common-chord arm: a mover-killing target is either a strict support drop on
the minimum fiber or a fixed actual off-minimum excursion.

### Corollary 2.3 (checked rank handoff in the minimum arm)

Suppose additionally that `X` is the base of a supplied
`QuittingPositiveMinimumDebtTangentFamily`.  In the `D(Y)=D_*` arm, Theorem
2.1 supplies exactly the support-subset and vanished-old-coordinate fields of
`exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished`.  Hence
there is a new positive-minimum tangent family based at `Y` whose support is
a strict subset of the old support and has strictly smaller cardinality.

This is a maintained natural-valued rank decrease; it does not claim that the
new tangent family retains the original rectangle, atom, or law fields.  The
strong-induction support-rank machinery needs only the freshly re-extracted
tangent family, while any attempt to reapply a more specialized packet would
need a separate producer.

## 3. Why finite label recurrence is not a compiler

The stronger-looking claim

> repeated equal-total-debt resets over four labels eventually form a cycle
> accepted by an existing periodic compiler

is false at the available interface.

The checked
`finite_stageFullBestEndpoint_cycle_signedCirculation` and
`finite_stageFullBestEndpoint_cycle_strictBestResponseWord` show that even an
*exact literal closed profile word* may have positive mover gains, exact
zero-face landings, exact total-debt preservation, and semantic recurrence.
The coordinate changes telescope as a signed debt circulation.  This is not
an exact Nash--Bellman word: at every selected phase the mover has a positive
root defect.

The checked compiler
`isUniformEquilibriumPayoff_of_cyclicNashBellmanCycle` instead requires, at
every phase, both an exact successor-value identity and an exact zero-defect
root Nash condition.  Neither follows from profile recurrence, debt
recurrence, or four-label pigeonhole.

For independently re-extracted carrier points the mismatch is earlier still:
finite repetition of support subsets does not identify the semantic points,
their behavioral sources, or the target of one reset with the source of the
next.  Thus label finiteness gives no literal chronology.

## 4. Exact exchange tableau showing the purely scalar obstruction

The following rational tableau records why constant positive total debt and
four-label finiteness alone cannot orient the exchange.  This is an abstract
semantic tableau, not a quitting-game realization and not a counterexample to
the conjecture.

Let the four debt vectors be

\[
\begin{aligned}
d^0&=(1/2,1/2,0,0),& d^1&=(0,1/2,1/2,0),\\
d^2&=(0,0,1/2,1/2),& d^3&=(1/2,0,0,1/2).
\end{aligned}                                      \tag{4.1}
\]

Every vector has total debt `1`.  With movers `0,1,2,3`, respectively, each
step kills the mover, activates one newcomer, preserves support cardinality
two, and transfers aggregate opponent debt exactly `1/2`.  The fourth step
returns to `d^0`.

One compatible bounded payoff display is

\[
\begin{aligned}
U^0&=(0,0,0,0),&
U^1&=(1/2,0,0,0),\\
U^2&=(0,1/2,0,0),&
U^3&=(0,0,1/2,-1/2),
\end{aligned}                                      \tag{4.2}
\]

with `B^t=U^t+d^t`.  Along step `t -> t+1 mod 4`, the displayed mover's
payoff rises by exactly its source debt `1/2`.  Thus (4.1)--(4.2) satisfy the
nonnegativity, positive scalar floor `D_*=1` on the displayed fiber,
zero-face, aggregate-transfer, bounded-payoff, and closed signed-circulation
identities.  They intentionally omit the decisive common-chord affinity (and
all game-realization/root data).  Adding that affinity makes the tableau
impossible at a maximum-support minimum by Theorem 2.1.

The actual checked regression
`FiniteResetCirculationRegression.exact_literal_fullBestResponse_cycle_preserves_totalDebt`
is stronger in literal provenance but is explicitly outside the positive
global-minimum setting: its recurrent fiber has debt `2`, whereas the Never
profile has debt `1`.

## 5. Conjecture-facing use and exact remaining mismatch

Theorem 2.1 gives a real consumer whenever the current positive-minimum
packet supplies **one common actual source/replacement sequence** with both
semantic limits on the minimum fiber.  The target is then a carrier minimum
with strict support inclusion, so the checked positive-minimum tangent-family
re-extraction may restart at a lower natural-valued support rank.

It does not apply when the endpoint is produced by fixed-law minimization or
another independent selection lacking (2.1).  Nor does it consume the
off-minimum alternative in Corollary 2.2.  Those are provenance failures, not
exceptions to the chord argument.

In particular, the forced-owner output currently recorded in Proposition 8.1
of `CODEX_MINER__SIGNED_CAUSAL_RECTANGLE_ORIENTATION_COMPILER_BOUNDARY` is not
silently covered.  That packet compares a normalized forced-owner source with
a **half** endpoint and provides a transfer alternative there.  The present
theorem requires a common chord to the **full mover-killing endpoint**, and
requires both source and full endpoint clusters to lie on the minimum fiber.
Forcing the owner to Quit may already move the source off minimum, while
convexity does not promote a signed half-endpoint transfer to the full
endpoint.  Thus the theorem consumes only the explicit two-minimum full-chord
subarm; the off-minimum forced-root/full-endpoint arm remains separate.

In particular, the reviewed positive-Never rectangle already uses the same
support-union mechanism at four corners and forces a fixed actual off-minimum
corner.  The present theorem isolates the generic one-chord core; it does not
claim a new consumer for that surviving excursion.

## 6. Checked sources and novelty audit

Inspected declarations:

- `quittingTerminalSemanticDebt_stoppingLawMixture_chordGap_le_nearMinimum`
  and
  `quittingTerminalSemanticDebt_stoppingLawMixture_eq_of_minimum_sameDebtSum`
  in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawMinimumFiberAffine.lean`;
- `exists_reextracted_of_minimumFiber_of_supportSubset_of_vanished` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`;
- `finite_stageFullBestEndpoint_cycle_signedCirculation` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveMinimumUnitResetCycle.lean`;
- `finite_stageFullBestEndpoint_cycle_strictBestResponseWord` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveMinimumUnitResetOrientation.lean`;
- `isUniformEquilibriumPayoff_of_cyclicNashBellmanCycle` in
  `UniformEquilibrium/Quitting/Cycles/CyclicKofNBellmanBridge.lean`; and
- the regression in
  `Research/Quitting/FiniteResetCirculationRegression.lean`.

The support-union observation is already present in the reviewed
positive-Never four-corner theorem and in the minimum-fiber support-lattice
intake.  The potentially reusable statement here is its nonattained,
source-matched one-chord formulation and the exact conclusion that maximum
support collapses exchange to strict support inclusion.  This is not proposed
for export before independent review and a named producer actually supplies
hypothesis 4.

## 7. Review request

Please check the varying-source half-mixture compactification, passage from
the near-minimum chord gaps to coordinate equality, maximum-support selection,
strictness at the killed mover, and the distinction between a literal reset
word and a Nash--Bellman cycle.  Also check whether Theorem 2.1 is already
available verbatim rather than only as the four-corner specialization.
