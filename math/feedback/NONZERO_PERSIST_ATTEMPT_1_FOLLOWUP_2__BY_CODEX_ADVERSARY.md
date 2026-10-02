# Adversarial audit of Followup 2, Sections 3--5

Reviewer: `CODEX_ADVERSARY`

Claim reviewed: the exact two-cut coercivity theorem, its seam-stable form,
and the post-mark paid replacement in
`gpt/NONZERO_PERSIST_ATTEMPT_1.md`, Followup 2, Sections 3--5. I used
`feedback/NONZERO_PERSIST_ATTEMPT_1_FOLLOWUP_2__BY_CODEX_ROOT.md` only as a
list of objections to retest.

## Verdict

The literal-block coercivity theorem is **correct**. The post-cut behavioral
replacement is also correct after one quantifier repair to the parent reach
estimate. The best hazard constant is stronger than the draft's constant.

**Standalone export recommendation:** export a source-neutral exact
two-cut lemma and, separately, a conditional behavioral-splice corollary. Do
not export Followup 2 as a Fin4 producer or completion theorem. Current Fin4
sources supply positive minimum debt, actual paid sources, and some reach
floors, but do not supply the required renewable post-mark, order-one-hazard
block with compatible child and complete semantic seams.

## 1. Exact debt recursion

Let \(z_t=(U_t,B_t)\) be the literal terminal semantic pair of the actual
suffix beginning at \(C_1+t\), and let \(x_t\) be its live root. The checked
chronological identity is

\[
 z_t=\operatorname{Prefix}_{x_t}(z_{t+1}).
\]

For every player \(i\), the checked arbitrary-root cap--debt reduction gives

\[
 d_i(z_t)
 =c_t d_i(z_{t+1})+
   \operatorname{NDef}_{r,i}(x_t;B_{t+1}),
 \qquad
 c_t=\Pr_{x_t}(\text{all Continue}).
\]

Thus equations (14)--(15) have the correct orientation and, importantly,
the coefficient is joint Continue mass, not opponent-only Continue mass.
The defect must be evaluated against the unrestricted cap vector
\(B_{t+1}\); evaluating it against \(U_{t+1}\) would make (14) false. The
defect is nonnegative because the played successor value is a convex
combination of the two pure endpoint values.

Writing \(P_t=\prod_{u<t}c_u\), literal telescoping gives exactly

\[
 D(z_0)=\mathcal C+P_LD(z_L),
 \qquad
 \mathcal C=\sum_{t<L}P_t\rho_t.
\]

Both endpoint pairs are literal attainable pairs and therefore lie in the
compact carrier. Hence \(D(z_0),D(z_L)\ge D_*\). If
\(P_L\le\theta<1\), with \(\Delta=D(z_L)-D_*\), then

\[
 \mathcal C+\theta\Delta\ge(1-\theta)D_*.
\]

This proves (17). No rowwise Nash or approximate-Nash hypothesis is used.

## 2. Sharp hazard constant

If \(q_{t,i}\) is player \(i\)'s actual marginal Quit probability, then

\[
 c_t=\prod_i(1-q_{t,i})
     \le \exp\!\left(-\sum_iq_{t,i}\right).
\]

Consequently a block with
\(H=\sum_{t<L}\sum_iq_{t,i}\ge\chi\) satisfies

\[
 P_L\le e^{-H}\le e^{-\chi}.
\]

The factors \(1/4\) in (18)--(21) are unnecessary. They are safe but not
sharp. Define instead

\[
 \bar K_\chi=(1-e^{-\chi})D_*,
 \qquad
 \bar\delta_\chi=\frac{e^\chi-1}{2}D_*.
\]

Then the exact strengthened alternative is

\[
 D(z_L)\ge D_*+\bar\delta_\chi
 \quad\text{or}\quad
 \mathcal C>\bar K_\chi/2.
\]

For \(n=|I|\), the second arm selects a block-dependent player \(p\) with

\[
 \mathcal C_p>\frac{\bar K_\chi}{2n},
 \qquad
 d_p(z_0)\ge\mathcal C_p.
\]

In Fin4 this is \(d_p(z_0)>\bar K_\chi/8\). The denominator eight is
therefore specifically a four-player constant and must not appear in a
generic finite-player statement.

## 3. Seam-stable form

The safe seam statement needs an explicit signed-debt formulation. Suppose a
root step uses an expected child \(\widehat z_{t+1}\), while the next decoded
candidate is \(z_{t+1}\), and put

\[
 e_t=D(\widehat z_{t+1})-D(z_{t+1}).
\]

Then the exact telescope is

\[
 D(z_0)=\mathcal C+P_LD(z_L)
   +\sum_{t<L}P_{t+1}e_t.
\]

Thus the sharp seam toll is the survival-weighted quantity

\[
 S_P=\sum_{t<L}P_{t+1}|e_t|.
\]

The unweighted \(S=\sum_t|e_t|\) used in (20) is a valid coarser bound because
\(0\le P_t\le1\). With literal carrier endpoints,

\[
 \mathcal C+S_P+e^{-\chi}\Delta
 \ge(1-e^{-\chi})D_*.
\]

If seams are recorded at the semantic-pair level, both coordinates are
needed. For coordinatewise payoff and cap errors \(a_{t,i},b_{t,i}\), one
may take

\[
 |e_t|\le\sum_i(a_{t,i}+b_{t,i}).
\]

In particular, a common sup error \(d_t\) in each of the two coordinates
costs at most \(2|I|d_t\), hence \(8d_t\) in Fin4. The payoff-only seam
\(d_k\) in the macro tower does not instantiate this semantic seam.

Two endpoint conditions must be stated in a standalone theorem: \(z_0\) and
\(z_L\) must be literal carrier points so that the two uses of the global
floor are justified. Artificial intermediate annotations need not themselves
be carrier points for the algebraic telescope, but an artificial cap
annotation has no behavioral paid interpretation.

## 4. Exact post-cut behavioral replacement

In the paid arm, fix the player \(p\) selected from \(\mathcal C_p\), before
choosing an approximation tolerance. Since \(B_{0,p}\) is the supremum over
all behavioral deviations against the fixed opponents, the checked supremum
approximation theorem gives, for every \(\eta>0\), an actual behavioral
deviation \(\sigma_p^\eta\) satisfying

\[
 \operatorname{Payoff}_p(\sigma_p^\eta,U_{-p})
 \ge B_{0,p}-\eta.
\]

Therefore the suffix gain and the replacement's new \(p\)-debt obey the
simultaneous bounds

\[
 G_p^\eta\ge d_p(z_0)-\eta
   >\frac{\bar K_\chi}{2|I|}-\eta,
 \qquad
 d_p(z_0^{\,\eta})\le\eta.
\]

The second inequality is exact in strategy class: the opponents are
unchanged, so the replacement profile has the same unrestricted cap
\(B_{0,p}\), while its prescribed payoff lies within \(\eta\) below that
cap. The returned object is an unrestricted behavioral strategy, equivalently
its hazard on the unique live history. It is not proved to be a finite-time,
pure-time, stationary, or cap-attaining law.

Now splice this strategy into a parent profile, leaving player \(p\)
unchanged at every row strictly before \(C_1\). If \(R\) is the parent's
actual joint probability of reaching row \(C_1\), then pre-cut branches are
identical and

\[
 \text{parent payoff gain}=R G_p^\eta.
\]

Because the opponents are globally unchanged, the parent's unrestricted
\(p\)-cap is also unchanged. Hence this same quantity is the **exact reduction
of the parent's \(p\)-debt**. No analogous conclusion holds for total debt:
changing \(p\)'s tail may change every other player's cap.

### Mandatory quantifier repair to (25)

From \(R\ge r_0>0\) and
\(G_p^\eta\ge \bar K_\chi/8-\eta\), one may infer

\[
 RG_p^\eta\ge r_0(\bar K_\chi/8-\eta)
\]

only when the displayed suffix lower bound is nonnegative. Equation (25), as
written for arbitrary positive \(\varepsilon\), is false as an inference when
\(\varepsilon>\bar K_\chi/8\): multiplying a negative lower bound by the larger
reach reverses the useful comparison with \(r_0\).

Restrict (25) to \(0<\eta\le\bar K_\chi/8\), or state the exact formula
\(RG_p^\eta\) first. The final choice \(\eta=\bar K_\chi/16\) is valid and
gives

\[
 \text{parent gain and }p\text{-debt drop}
 >r_0\bar K_\chi/16,
 \qquad
 d_p(z_0^{\,\eta})\le\bar K_\chi/16.
\]

## 5. Payer and atom quantifiers

The selected payer is fixed independently of \(\eta\) for one block. It is
not automatically common to an infinite family. Finite pigeonhole gives a
cofinal subsequence on which one payer recurs, but not eventual constancy on
all macro levels. If the paid replacement itself must be the next renewable
source, the payer must be stored in the source state or supplied by a serial
same-payer kernel; merely discarding intervening macro levels can destroy the
required child equality.

The splice preserves every event measurable strictly before \(C_1\). Thus a
literal coalition atom at a marked row \(m<C_1\), its absolute reached mass,
and every terminal branch ending before \(C_1\) are unchanged. The first
possible strategy difference is at row \(C_1\), not strictly after it. Replace
“agrees through \(C_1\)” by “agrees strictly before \(C_1\).”

This does not preserve an arbitrary mark whose certificate includes a
post-\(C_1\) payoff, cap, counterfactual continuation, or infinite terminal-law
event. The reusable atom interface must say that the retained datum is a
finite pre-cut cylinder (as the displayed coalition atom is), not just a
semantic cluster label.

The required reach \(R\ge r_0\) is the absolute parent reach of \(C_1\). It
does not follow from a positive local marked-row atom or from the macro's local
reach field. It must be a numbered producer hypothesis whenever the paid
splice is iterated.

## 6. Connection to current Fin4 sources

There is a genuine but limited connection.

- Positive \(D_*\) is a checked consequence of a hypothetical failure of
  uniform-payoff existence, and literal suffix semantic pairs satisfy the
  exact checked prefix recursion. Thus the source-neutral two-cut theorem is
  immediately formalizable from existing semantics.
- `QuittingPaidCapLiftedSource` and its summable port supply actual profiles,
  exact cap-Nash prefixes, the checked floor
  `reachFloor_le_suffixReach`, and literal shifted paid rows. The same module
  also proves `absorption_summable`. Its cap prefixes lie before the unchanged
  paid suffix, and the source supplies no renewable order-one-hazard block
  after a retained mark. It therefore does not instantiate the post-mark
  producer demanded here.
- `FinFourQuantitativeFullSupportHardResidual.nonempty_paidCapDoublePort`
  supplies strong actual same-table paid/reset ports. It still does not say
  that the replacement selected by the two-cut debt is a child in the same
  residual domain, nor does it supply a compatible tower of post-mark cuts
  with a uniform \(\chi\), absolute \(r_0\), and summable full semantic seams.
- The source-preserving minimum-atom/forced-pair packets retain marks and
  literal post-date profiles, but no checked declaration gives the missing
  order-one post-mark hazard plus renewable child interface.

Accordingly the coercivity lemma can analyze any supplied literal block, and
some current objects may instantiate it once after additional choices. It
does not turn the current hard residual into the block family assumed in
Followup 2, and it yields neither terminal approximation nor uniform
equilibrium on its own.

## 7. Exportable statement

The strongest clean standalone packet has three layers:

1. a general finite-player exact two-cut identity and coercivity inequality,
   with the sharp \(e^{-H}\) survival bound;
2. an abstract seam version with the weighted signed-debt toll \(S_P\) and
   literal carrier endpoints; and
3. a Fin4 conditional splice corollary returning one block-dependent payer,
   an arbitrary-accuracy behavioral replacement, exact parent
   reach-weighted payer-debt reduction, and preservation of finite pre-cut
   cylinders.

It must explicitly disclaim production of the cuts, a common payer across
blocks, source-child closure, total-debt descent, terminal Nash profiles, and
uniform equilibrium.

## Declarations inspected

- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect` and
  `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect`,
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`;
- `quittingRootCoordinateNashDefect_nonneg`,
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`;
- `QuittingBoundedSeamChain.actualPair_eq_prefix` and the prescribed/cap
  seam reductions,
  `UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalSeamReduction.lean`;
- `exists_quittingContinuation_deviation_ge_sub`,
  `UniformEquilibrium/Quitting/Root/FirstBranch.lean`;
- `quittingTerminalSemanticCarrier_isCompact` and the semantic debt
  definitions,
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt`,
  `UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean`;
- `QuittingPaidCapLiftedSource.reachFloor_le_suffixReach`,
  `QuittingPaidCapLiftedSource.absorption_summable`, and the shifted paid-row
  declarations,
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`;
- `FinFourQuantitativeFullSupportHardResidual.nonempty_paidCapDoublePort`,
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/SingletonBaseResetRepairPaidCapDoublePort.lean`.
