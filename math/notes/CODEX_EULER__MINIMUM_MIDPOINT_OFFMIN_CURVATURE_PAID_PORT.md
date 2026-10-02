# A minimum midpoint and an off-minimum full endpoint force a literal curvature-paid port

**Identity:** `CODEX_EULER`

**Status:** `PASS after independent review; ordinary mathematics composed
with checked declarations; internal`

Independent review:
[`feedback/CODEX_EULER__MINIMUM_MIDPOINT_OFFMIN_CURVATURE_PAID_PORT__BY_CODEX_RAMSEY.md`](../feedback/CODEX_EULER__MINIMUM_MIDPOINT_OFFMIN_CURVATURE_PAID_PORT__BY_CODEX_RAMSEY.md).
The reviewer confirmed the factor-two normalization, the sharpened
`Delta/12` paid gain, literal full-endpoint provenance, and the exact
return/descent/inert handoff.  No checked theorem removes the inert arm from
source-plus-midpoint minimum provenance alone.

## 1. Question and verdict

Consider a literal one-player stopping-law chord

```text
source S_n  -- half replacement --> H_n -- full replacement --> E_n,
```

where `H_n` is exactly the half mixture of the mover's source and full
replacement strategies.  Suppose the source and midpoint semantic limits lie
on the positive global minimum-debt fiber, while the full endpoint has a
fixed excess

\[
 D(S)=D(H)=D_*,\qquad D(E)=D_*+\Delta,\qquad \Delta>0. \tag{1.1}
\]

Is the scalar midpoint curvature `Delta/2` too weak to locate an observer or
an executable literal row?

No.  Mover debt is exactly affine under mixing its own complete strategy, so
the mover carries no chord curvature.  The entire scalar gap is distributed
among the other players.  For `Fin 4`, after a subsequence one fixed observer
has limiting midpoint debt curvature at least `Delta/6`, equivalently
limiting normalized curvature at least `Delta/3`.

The checked normalized-curvature decoder then attaches a paid
first-disagreement row of gain `Delta/12` on the **literal full endpoint
profile** (the clean constant below spends a factor two for eventuality and
then leaves a strict error budget).  Its checked cap lift
produces a summable semantic port and the exact alternatives

```text
charged cumulative near-return
or quantitative cap-debt descent
or literal inert stall.                              (1.2)
```

Under the maintained terminal exploitability witness, the first arm is
impossible because it yields a uniform-equilibrium payoff.  Thus the honest
conclusion is descent **or inert stall**.  Scalar curvature is sufficient for
observer localization and a source-matched paid row, but it does not force
positive cap absorption.  The unique-all-Continue hard residual can realize
the last arm without contradicting the curvature row.

## 2. Exact sequence theorem

Let `I` be finite with at least two players, let `r` be a quitting reward
table, and let `o` be one fixed mover.  For every `n`, let `sigma_n` be an
actual profile and `tau_n` a complete alternative strategy of `o`.  Define

\[
\begin{aligned}
 S_n&=\operatorname{Sem}(\sigma_n),\\
 E_n&=\operatorname{Sem}(\sigma_n[o\leftarrow\tau_n]),\\
 H_n&=\operatorname{Sem}(\sigma_n[o\leftarrow
             \tfrac12\sigma_n(o)+\tfrac12\tau_n]).
\end{aligned}                                      \tag{2.1}
\]

The mixture in the last line is the repository's complete stopping-law
mixture, not a correlated mixture of whole profiles.

### Theorem 2.1 (off-minimum endpoint curvature localization)

Assume semantic convergence

\[
 S_n\to S,\qquad H_n\to H,\qquad E_n\to E,           \tag{2.2}
\]

and (1.1), where `S,H,E` are carrier points and `D_*` is the positive global
minimum.  Put `N=|I|-1`.  Then, after a subsequence, there is one fixed
observer `i != o` such that

\[
 \liminf_n\left[
 d_i(E_n)-d_i(S_n)-2(d_i(H_n)-d_i(S_n))
 \right]\ge \frac{\Delta}{N}.                       \tag{2.3}
\]

The bracket is exactly the stopping-law normalized debt curvature at weight
`1/2`:

\[
 C_{n,i}=d_i(E_n)+d_i(S_n)-2d_i(H_n).                \tag{2.4}
\]

For every fixed `0<c<Delta/N`, all sufficiently late selected ranks therefore
admit a checked `QuittingStoppingLawCurvaturePaidWitness` attached to the
literal chord `sigma_n -> sigma_n[o<-tau_n]`, with any positive budgets

\[
       g+e_{\rm src}+e_{\rm end}<c.                  \tag{2.5}
\]

In particular, for `Fin 4`, take

\[
c=\Delta/6,\qquad
g=\Delta/12,\qquad
e_{\rm src}=e_{\rm end}=\Delta/48.                  \tag{2.6}
\]

The sum of the three budgets is `Delta/8<c`, so every sufficiently late
rank carries a paid first-disagreement row of gain `Delta/12` on `E_n`.

### Proof

For every coordinate define its half-chord gap

\[
 \kappa_{n,j}=\tfrac12d_j(S_n)+\tfrac12d_j(E_n)-d_j(H_n). \tag{2.7}
\]

Stopping-law debt convexity gives `kappa_(n,j)>=0`.  Summing and passing to
the limit in (2.2) gives

\[
  \sum_j\kappa_{n,j}\longrightarrow
   \tfrac12D(S)+\tfrac12D(E)-D(H)=\Delta/2.          \tag{2.8}
\]

Changing a player's own complete strategy leaves that player's behavioral
best-response envelope invariant.  Its prescribed payoff is affine in the
stopping-law mixture.  Hence mover debt is affine and

\[
                         \kappa_{n,o}=0.             \tag{2.9}
\]

exactly at every rank.  By finite pigeonhole and a subsequence, some fixed
`i!=o` satisfies

\[
                \liminf_n\kappa_{n,i}\ge\Delta/(2N).\tag{2.10}
\]

At mixture weight `lambda=1/2`, the repository's normalized debt direction
is

\[
 2(d_i(H_n)-d_i(S_n)).
\]

Subtracting it from the full endpoint debt change gives

\[
 C_{n,i}=d_i(E_n)-d_i(S_n)-2(d_i(H_n)-d_i(S_n))
        =2\kappa_{n,i}.                              \tag{2.11}
\]

which proves (2.3).

For fixed `0<c<Delta/N`, eventually `c<C_(n,i)`.  The hypothesis of
`exists_quittingStoppingLawCurvaturePaidWitness` at `lambda=1/2` is

\[
 \tfrac12(g+e_{\rm end})+\tfrac12 e_{\rm src}
       \le \tfrac12 C_{n,i},                         \tag{2.12}
\]

equivalently `g+e_src+e_end<=C_(n,i)`.  Thus (2.5) supplies the checked
witness.  The numerical choices (2.6) satisfy the strict budget and give the
claimed literal paid row.  `QED`

## 3. Exact paid-port composition

Fix a sufficiently late rank and its curvature-paid witness `carrier`.  Let
`minimum=S` (or any displayed positive global minimum point).  The checked

```text
carrier.nonempty_capLiftedSummablePort_of_tangentFamily
```

is stated using a supplied positive-minimum tangent family; equivalently the
more primitive `carrier.nonempty_capLiftedSummablePort` uses the minimum,
global-minimality, and positivity fields directly.  It returns a
`QuittingPaidCapLiftedSource.SummablePort` whose actual paid profile is the
full endpoint `sigma_n[o<-tau_n]`, and whose shifted rows preserve the same
paid suffix at every finite cap-prefix depth.

Applying
`QuittingPaidCapLiftedSource.exactTrichotomy` gives (1.2).  In the charged
near-return arm, the structure already stores a
`QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily` and a
uniform-equilibrium payoff.  Under a positive terminal exploitability gap
this arm is contradictory.  Therefore each selected curvature port lies in

```text
QuantitativeDebtDescent or InertStall.               (3.1)
```

This is a literal same-endpoint composition: no fixed-law minimizer or
independently selected paid source replaces `E_n`.

The strategic decoder can also be invoked.  By taking `e_end` smaller than
`gamma*g/(2*quittingRewardBound r)`, the checked
`carrier.nonempty_strategicDispatch` gives either a legal observer deviation
or a legal reached outsider endpoint deviation with fixed gain.  This is an
unrestricted behavioral-gain statement, but terminal exploitability already
supplies such deviations and it does not eliminate (3.1)'s inert branch.

## 4. Exact limitation: curvature does not force cap charge

The paid row compares two pure-time response chronologies on the full endpoint
and records their first disagreement.  The cap-lifted roots are selected
against the endpoint's behavioral envelope `B(E_n)`.  Nothing in (2.3) says
that an exact root Nash against that envelope has positive absorption.

If its unique exact cap root is all Continue, then every selected cap prefix
has absorption zero.  The complete semantic pair, total debt, and paid suffix
remain unchanged at every finite depth.  This is exactly
`QuittingPaidCapLiftedSource.InertStall`; the row survives, but no charge is
spent and no prescribed-payoff Bellman return is created.

Thus the proposed stronger implication

```text
positive midpoint curvature => checked descent or charged return
```

is not supplied by the exact interface.  What is proved is

```text
positive midpoint curvature
  => fixed observer normalized curvature
  => literal curvature-paid row on E_n
  => charged return or quantitative descent or inert stall.       (4.1)
```

Eliminating the final arm requires an additional theorem connecting the
source/midpoint minimum provenance to the exact cap correspondence at the
off-minimum full endpoint.  The midpoint chord itself does not contain such a
field.

## 5. Relation to the minimum-endpoint arm

If instead `D(E)=D_*`, the midpoint gap (2.8) is zero and every coordinate is
affine.  When `S` is chosen with maximum support and the full replacement
kills an active mover, Theorem 2.1 of
`CODEX_EULER__MAXIMUM_SUPPORT_COMMON_CHORD_EXCHANGE_COLLAPSE` gives strict
support inclusion and the checked tangent-family rank re-extraction.

Hence the honest literal-chord split is:

1. `E` minimum: strict support re-extraction, provided the source is the
   maximum-support minimum point and the mover is killed;
2. `E` off minimum: a fixed source-matched curvature-paid port, with exact
   trichotomy (4.1).

Only the inert subarm of item 2 survives the current consumers.

## 6. Sources inspected

- `quittingTerminalSemanticDebt_stoppingLawMixture_le` and
  `quittingTerminalSemanticDebt_stoppingLawMixture_eq_self` in
  `StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`;
- `exists_quittingStoppingLawCurvaturePaidWitness` and
  `QuittingStoppingLawCurvaturePaidWitness.nonempty_strategicDispatch` in
  `StoppingLaw/Endpoint/NormalizedCurvatureStrategicDispatch.lean`;
- `QuittingStoppingLawCurvaturePaidWitness.nonempty_capLiftedSummablePort` and
  `nonempty_capLiftedSummablePort_of_tangentFamily` in
  `StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`;
- `QuittingPaidCapLiftedSource.exactTrichotomy` in
  `StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`; and
- `QuittingActualProfileTerminalGapPaidCapPort.quantitativeDebtDescent_or_inertStall`
  in `StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean` for the same
  terminal-gap exclusion of the charged-return arm.

The asymptotic tangent-family version of the curvature localization already
appears as
`FullReplacementCluster.exists_eventually_curvatureStrategicDispatch`.  The
new point isolated here is the fixed-half literal chord formula (2.11) and
its direct application to the source/midpoint-minimum versus full-endpoint
split.  It is internal pending independent review and does not claim to
consume the inert hard residual.

## 7. Review request

Please check the mover zero-curvature identity, the `Delta/(2N)` observer
pigeonhole constant, normalized-curvature factor two, budgets (2.6), exact
profile on which the paid row lives, and the cap-port/trichotomy handoff.
Most importantly, verify that no checked declaration silently excludes the
inert stall from the source/midpoint-minimum provenance alone.
