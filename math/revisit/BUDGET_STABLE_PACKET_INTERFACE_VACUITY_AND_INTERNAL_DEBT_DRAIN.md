# Budget-stable packet interface vacuity and internal debt-drain obstruction

Author: `GPT`

Independent reviews:
[source and freshness audit](../feedback/SHADOW__BY_GATE_SOURCE_AUDIT.md),
[strengthening review](../feedback/SHADOW__BY_GATE_STRENGTHENER.md), and
[adversarial falsification](../feedback/SHADOW__BY_GATE_FALSIFIER.md)

## Exact statement

Let \(I\) be a finite player set and let \(r\) be any quitting-game reward
table.

### Theorem A: exact inhabitance criterion for the bare packet interface

The present formal interface satisfies

\[
\operatorname{Nonempty}
  (\texttt{QuittingBudgetStablePacketSystem }r)
\quad\Longleftrightarrow\quad
2\le |I|.
\tag{A}
\]

Thus, as soon as two distinct player labels exist, this structure is inhabited
for every reward table without using a positive-minimum source, tangent
family, retained atom, or source chronology.

### Theorem B: all-behavior implementation barrier

Let \(z=(u,b)\) be a semantic pair and let \(\sigma\) be an actual behavioral
profile. Write \(U_i(\sigma)\) for its prescribed terminal payoff and

\[
B_i(\sigma)=\sup_{\tau_i}U_i(\tau_i,\sigma_{-i})
\]

for the unrestricted unilateral behavioral cap. The supremum ranges over all
behavioral deviations, including Never and arbitrarily late stopping.

Assume, for every \(i\in I\),

\[
b_i-u_i\le\eta,\qquad
U_i(\sigma)\ge u_i-\alpha_i,\qquad
B_i(\sigma)\le b_i+\beta_i,
\]

where \(\alpha_i,\beta_i\ge0\). Then

\[
B_i(\sigma)-U_i(\sigma)\le \eta+\alpha_i+\beta_i
\]

and consequently

\[
D(\sigma)\le |I|\eta+\sum_i(\alpha_i+\beta_i).
\tag{B1}
\]

If every actual profile has debt at least \(D_*\), then

\[
D_*\le |I|\eta+\sum_i(\alpha_i+\beta_i).
\tag{B2}
\]

For four players, if \(\alpha_i,\beta_i\le\delta\), this gives

\[
D_*\le4\eta+8\delta.
\tag{B3}
\]

If instead \(\alpha_i+\beta_i\le\delta\), it gives

\[
D_*\le4\eta+4\delta.
\tag{B4}
\]

When \(D_*>|I|\eta\), at least one coordinate satisfies

\[
\alpha_i+\beta_i\ge \frac{D_*-|I|\eta}{|I|}.
\tag{B5}
\]

### Theorem C: total-debt internal-drain telescope

Let \(x_n,m_n,e_n\) be semantic pairs, let \(h_n>0\), let
\(\rho_n,\omega(h_n)\ge0\), and let \(c>0\). Interpret \(x_n\) as a packet
entrance, \(m_n\) as one marked candidate in that packet, and \(e_n\) as its
endpoint. Assume

\[
D(m_n)-D(x_n)\ge c h_n-\rho_n
\tag{C1}
\]

and, for every coordinate \(i\),

\[
|e_n^U(i)-x_{n+1}^U(i)|
+
|e_n^B(i)-x_{n+1}^B(i)|
\le\omega(h_n).
\tag{C2}
\]

Put

\[
R_n=(D(m_n)-D(e_n))_+.
\]

Then, for every \(N\),

\[
\sum_{n<N}R_n
\ge
c\sum_{n<N}h_n
-\sum_{n<N}\rho_n
+D(x_0)-D(x_N)
-|I|\sum_{n<N}\omega(h_n).
\tag{C3}
\]

If all coordinate debts lie in \([0,M]\), then

\[
\sum_{n<N}R_n
\ge
c\sum_{n<N}h_n
-\sum_{n<N}\rho_n
-|I|M
-|I|\sum_{n<N}\omega(h_n).
\tag{C4}
\]

Hence, if

\[
\sum_nh_n=\infty,\qquad
\sum_n\rho_n<\infty,\qquad
\sum_n\omega(h_n)<\infty,
\]

then

\[
\sum_n R_n=\infty.
\tag{C5}
\]

More precisely, for every \(\varepsilon>0\), infinitely many \(n\) satisfy

\[
R_n\ge(c-\varepsilon)h_n.
\tag{C6}
\]

If \(m_n\) is a literal candidate inside an exact Bellman-prefix block ending
at \(e_n\), define at every row after the mark

\[
r_{n,t}=
\bigl(D(z_{n,t})-D(z_{n,t+1})\bigr)_+.
\]

Then

\[
R_n\le\sum_t r_{n,t}.
\tag{C7}
\]

Thus (C5) forces divergent cumulative positive debt drop over literal exact
Bellman rows. It does not by itself produce prescribed-payoff charge.

### Theorem D: one-coordinate telescope

Fix \(j\in I\). Under the coordinate drift hypothesis

\[
d_j(m_n)-d_j(x_n)\ge c h_n-\rho_n,
\]

put

\[
R_n^j=(d_j(m_n)-d_j(e_n))_+.
\]

Then

\[
\sum_{n<N}R_n^j
\ge
c\sum_{n<N}h_n
-\sum_{n<N}\rho_n
+d_j(x_0)-d_j(x_N)
-\sum_{n<N}\omega(h_n).
\tag{D1}
\]

If \(0\le d_j(x_n)\le M\), the boundary term may be replaced by \(-M\). If
\(d_j(x_n)=0\) for every \(n\), it vanishes exactly. The same literal-row
localization as in (C7) applies coordinatewise.

## Conjecture-facing change

The maintained two-tier chronological-shadowing question requires literal
attachment to one supplied positive-minimum source, its atom, its labels, and
its renewable successors.

Theorem A proves that the current Lean structure is not a formalization of
that Tier-I obligation: it is inhabited uniformly from an unrelated
stationary self-loop. Any theorem whose output is merely that structure can
ignore all source and atom hypotheses. A nonvacuous replacement must encode
the missing source equations rather than leave them as external commentary.

Theorems C and D impose a second permanent restriction. A source-attached
repair with persistent marked drift, a divergent exposure schedule, and
summable endpoint seams cannot simply pass the drift through its successors:
it must carry divergent cumulative internal exact-Bellman debt drain.

This eliminates a bare-interface proof, a frozen positive-drift packet, a
terminate-at-the-mark packet with summable seams, and a bounded monotone
successor chain with no compensating internal drain. It does not construct
either requested shadowing tier.

## Definitions and assumptions

A terminal semantic pair consists of a prescribed payoff vector \(U\) and the
complete unilateral behavioral cap vector \(B\). Coordinate debt and total
debt are

\[
d_i=B_i-U_i,\qquad D=\sum_i d_i.
\]

The current budget-stable packet system stores:

- a port type and one semantic annotation at each port;
- a positive availability radius;
- two fixed distinct labels;
- nonnegative seam and availability costs;
- finite positive-length root blocks with exact semantic prefix recursion;
- entrance and successor endpoint seams;
- lower marginal-hazard bounds for the two labels;
- successor-radius and global boundedness data; and
- operational sublinearity of the combined cost.

It does not store an actual profile realizing a port, an outcome law, a marked
terminal atom, or an equation tying its annotations and successors to an
externally supplied source family.

The telescope additionally assumes compatible successive annotations, one
marked candidate per block, a quantitative marked-drift inequality, and
summable drift residuals. These are not fields of the present packet system.

## Source correspondence

The exact packet definitions and conditional shadowing compiler are in
`UniformEquilibrium/Quitting/Debt/Dynamic/BudgetStableCompatiblePacketIteration.lean`.
The cap in the semantic pair is the supremum over the full behavior-strategy
type defined in
`UniformEquilibrium/Quitting/Root/FirstBranch.lean`.

The stationary fixed-point proof uses:

- `quittingRootThenContinuationProfile_stationary` from
  `UniformEquilibrium/Quitting/Stationary/Root.lean`; and
- `quittingTerminalSemanticPair_rootThenContinuation` from
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.

Operational schedules are supplied by
`IsOperationallySublinearCost` and
`exists_budgetedDivergentCostSchedule` in
`MathUE/SublinearCostSchedule.lean`.

Nearby checked seam estimates occur in
`UniformEquilibrium/Diagnostics/Quitting/PositiveMinimumSeedSeamBarrier.lean`,
`UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalSeamReduction.lean`,
and
`UniformEquilibrium/Quitting/Root/TerminalSemanticPrefixMetric.lean`.
They do not state Theorem A, the one-sided implementation theorem with
independent payoff and cap errors, or the marked internal-drain telescopes.

The missing-provenance diagnosis was anticipated conditionally in Sections
6AO and 6BG--6BH of
`notes/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md`. Theorem A is the
unconditional sharp cardinality characterization. Theorems C and D are the
new exact finite-prefix accounts.

No paper theorem is used.

## Proof

### Proof of Theorem A

If the packet system is inhabited, its stored labels are distinct, so
\(|I|\ge2\).

Conversely, choose distinct \(a,b\in I\). Let \(q\) be the product root at
which every player Quits with probability \(1/2\), let \(\sigma^q\) be the
stationary behavioral profile using \(q\), and put

\[
z=\operatorname{SemPair}(\sigma^q).
\]

Use a singleton port, constant annotation \(z\), radius one, zero seam and
availability costs, \(\kappa=1/2\), and labels \(a,b\). At every legal scale
\(0<h<1\), use the one-row root block \(q\), set both candidates equal to
\(z\), and return to the unique port.

Stationarity and semantic prefixing give the exact complete-pair identity

\[
z=T_qz.
\]

Both seams are zero. Each label has marginal Quit hazard \(1/2\), which is at
least \(\kappa h=h/2\). Because the reward table and player set are finite,
choose \(R\ge1\) bounding every reward coordinate. Prescribed payoffs and
unrestricted caps lie in \([-R,R]\), and coordinate debts lie in \([0,2R]\),
so a global bound exists. Zero combined cost is operationally sublinear.
This verifies every field.

The stationary realization additionally has positive joint Continue,
positive mass for every coalition, and positive deleted-player survival.
Those are facts about this realization, not fields of the packet interface.

### Proof of Theorem B

For every \(i\),

\[
\begin{aligned}
B_i(\sigma)-U_i(\sigma)
&\le(b_i+\beta_i)-(u_i-\alpha_i)\\
&=(b_i-u_i)+\alpha_i+\beta_i\\
&\le\eta+\alpha_i+\beta_i.
\end{aligned}
\]

Summation proves (B1), and the actual-profile lower bound proves (B2).
Equations (B3)--(B5) are immediate finite-sum consequences.

### Proof of Theorem C

Debt is Lipschitz in the payoff-cap \(\ell^1\) metric:

\[
|D(z)-D(w)|
\le
\sum_i\bigl(|z_i^U-w_i^U|+|z_i^B-w_i^B|\bigr).
\tag{L}
\]

Thus (C2) implies

\[
D(x_{n+1})-D(e_n)\ge-|I|\omega(h_n).
\]

Since \(a_+\ge a\),

\[
\begin{aligned}
R_n
&\ge D(m_n)-D(e_n)\\
&=[D(m_n)-D(x_n)]
  +[D(x_n)-D(x_{n+1})]
  +[D(x_{n+1})-D(e_n)]\\
&\ge c h_n-\rho_n
  +D(x_n)-D(x_{n+1})
  -|I|\omega(h_n).
\end{aligned}
\]

Summing telescopes the middle term and proves (C3). Bounded nonnegative
coordinate debt gives \(D(x_0)-D(x_N)\ge-|I|M\), proving (C4). Under the
summability assumptions, the right side tends to \(+\infty\), proving (C5).

If (C6) failed for some \(\varepsilon>0\), then eventually
\(R_n<(c-\varepsilon)h_n\). Its finite-prefix upper bound would contradict
(C3), since \(\varepsilon\sum h_n\) diverges while the error and boundary
terms stay bounded.

Finally, for any finite real sequence,

\[
\bigl(D(z_{\mathrm{mark}})-D(z_{\mathrm{end}})\bigr)_+
\le
\sum_{t=\mathrm{mark}}^{\mathrm{end}-1}
\bigl(D(z_t)-D(z_{t+1})\bigr)_+.
\]

This proves (C7).

### Proof of Theorem D

Repeat the preceding proof with \(d_j\) in place of \(D\). The coordinate
form of (L) uses only the \(j\)-th payoff and cap seam and has coefficient one.

## Boundary tests

The cardinality condition in Theorem A is exact: with fewer than two players,
the required distinct labels cannot exist; with at least two, the construction
works for every reward table.

The coefficients of \(\alpha_i\) and \(\beta_i\) in Theorem B cannot be
deleted. In the one-player game with solo reward one, the Never profile has
\(U=0\) and \(B=1\). With seed \((u,b)=(0,0)\), the bound is equality for
\(\alpha=0,\beta=1\); with seed \((u,b)=(1,1)\), it is equality for
\(\alpha=1,\beta=0\).

The telescope is sharp under exact compensation: take scalar debts
\(x_n=e_n=0\), \(m_n=c h_n\), and
\(\rho_n=\omega(h_n)=0\). Then \(R_n=c h_n\).

A direct reprojection can take \(x_n=x_{n+1}=0\) and \(m_n=e_n=c h_n\), but
then its endpoint seam is order \(h_n\) and cannot be summable along a
divergent-scale schedule. This tests why the conclusion is scheduled rather
than a pointwise claim that \(\omega(h)=o(h)\).

The coordinate telescope does not imply a support-cardinality decrease.
For example,

\[
d(x)=(1,0),\qquad d(m)=(1,h),\qquad
d(e)=d(x_{\mathrm{next}})=(0,h)
\]

has zero endpoint seam and positive entry of the second coordinate, while
positive-support cardinality remains one.

## Adapter and consumer

Theorem A is a direct adapter from an arbitrary finite reward table with at
least two players to the present packet structure. Its consumer is a
specification test: any purported proof of Tier I which concludes only that
this structure is inhabited has not encoded the required source attachment.

Theorems C and D consume compatible marked-drift packet chains and return
quantitative internal exact-Bellman debt drain. This output currently has no
adapter to the admissible-payoff near-return compiler. The remaining
mathematical obligation is to turn that drain into an admissible
prescribed-payoff return, a renewable rank transition, or terminal
approximants.

## Lean handoff

The narrow declarations are:

- `nonempty_quittingBudgetStablePacketSystem_iff_two_le_card`;
- `quittingTerminalSemanticDebt_le_of_oneSidedImplementation`;
- `positiveMinimum_le_card_mul_seedDebt_add_implementationError`;
- a scalar finite-prefix telescope in `MathUE`;
- `compatibleMarkedDrift_sum_positiveInternalDrain_ge`;
- `compatibleMarkedDrift_not_summable_positiveInternalDrain`; and
- `compatibleMarkedCoordinateDrift_sum_positiveInternalDrain_ge`.

The stationary theorem should be placed in a diagnostics or specification
file. The telescope should be proved first for bounded real sequences and
then specialized using (L). No proposed declaration should assume source
attachment, marked drift, or an admissible return as a field merely to recover
it by projection.

## Scope and nonclaims

These results do not construct Tier I or Tier II, a uniform-equilibrium
payoff, terminal approximate Nash profiles, a source-preserving rank decrease,
or a counterexample table. Divergent internal debt drain is not an
admissible payoff return. Theorem A refutes the adequacy of the present bare
structure as a formal Tier-I specification; it does not refute the intended
source-attached mathematical producer.

## Checked implementation and revisit gate

The export packet at intake had SHA-256
`38bd76af69110d8358c5e980fe4f7921353945cc31c158bfdf11f421627adf8f`.
Its mathematically valid core was integrated and pushed at repository
revision `c9aefad1b696665ec321574395f0d688b8933d0f`.

The checked implementation is split as follows.

1. `UniformEquilibrium/Diagnostics/Quitting/BudgetStablePacketInterfaceVacuity.lean`
   proves the exact specification test
   `nonempty_quittingBudgetStablePacketSystem_iff_two_le_card`.  The reverse
   implication constructs the stationary half-Quit, one-port, zero-cost
   witness for every reward table with at least two players.
2. `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` and
   `UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean`
   expose coordinate and total-debt Lipschitz bounds together with
   `quittingTerminalSemanticDebt_le_of_oneSidedImplementation` and
   `quittingTerminalSemanticDebtSum_le_of_oneSidedImplementation`.
3. `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticImplementationBarrier.lean`
   proves the literal actual-profile bounds, the Fin4 `4 * eta + 8 * delta`
   and `4 * eta + 4 * delta` specializations, and the average-coordinate
   obstruction.  Representative capstones are
   `quittingTerminalDebtSumInf_le_of_seedImplementation`,
   `quittingTerminalDebtSumInf_le_four_eta_add_eight_delta`, and
   `exists_seedImplementationError_ge_average_of_debtSumInf`.
4. `MathUE/SequenceVariation.lean` contains the game-independent finite
   marked-drain telescope, bounded-boundary specialization,
   `not_summable_positivePart_markedDrain`, and
   `frequently_positivePart_markedDrain_ge`.
5. `UniformEquilibrium/Quitting/Debt/Dynamic/MarkedInternalDebtDrain.lean`
   specializes the scalar ledger to exact variable-length Bellman blocks.
   `sum_positiveInternalDebtDrain_ge` and its coordinate/bounded/zero-entry
   variants prove the finite accounts;
   `tendsto_sum_positiveInternalDebtDrain_atTop` and
   `frequently_positiveInternalDebtDrain_ge` make the asymptotic conclusions
   literal; `markedRow_exact_step` and the two marked-to-row bounds retain the
   exact Bellman rows; and
   `tendsto_sum_positiveRowCoordinateDebtDrop_atTop` states the cumulative
   exact-row coordinate-drain divergence directly.

Evidence seals:

- **M:** PASS.  The stationary vacuity witness, all-behavior implementation
  inequalities, scalar and coordinate telescopes, summability argument,
  frequent large-drain conclusion, and literal-row localization were
  independently rechecked.
- **L:** PASS.  All modules are integrated through the production and
  Diagnostics umbrellas, occur in the generated exhaustive axiom audit, and
  pass the named dependency builds.  Representative capstones use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- **A:** FAIL for the conjecture-facing source route.  The stationary witness
  adapts an arbitrary reward table only to the *bare* packet structure; that
  is precisely the vacuity result.  No theorem attaches the ports,
  annotations, marked candidates, labels, and successors to one supplied
  positive-minimum source, retained atom, or renewable chronology, and no
  external small-debt seed adapter is constructed.
- **C:** FAIL for the conjecture-facing route.  The internal drain is not
  converted to prescribed-payoff charge, an admissible near-return,
  source-preserving rank descent, terminal approximants, or a uniform payoff.
  The inhabitance equivalence is a specification diagnostic, not a producer
  consumer.

Validation at revision `c9aefad1b696665ec321574395f0d688b8933d0f`
included the documentation gate, 109 script unit tests, execution of all 33
registered experiments, import-graph, proof-duplicate, reward-bound,
redundant-order, derivable-telescope, and trust checks, and a full
`lake build` of 11,078 jobs.  The generated axiom audit was exact.

This packet remains useful as a checked tool and specification warning, but
it is not Fin4 or uniform-equilibrium progress by itself.  Revisit it only
when an actual source-attached packet producer and a consumer of cumulative
internal drain are available; neither should be added as a field merely to
project it back out.
