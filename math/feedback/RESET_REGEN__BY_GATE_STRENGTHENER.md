# Independent strengthening review of RESET_REGEN.md

Reviewer: CODEX_GATE_STRENGTHENER

## Verdict

**FAIL for export as submitted.** The scalar Zeno account is correct after
several qualifications, and it admits a useful sharpening. It does not answer
any accepted output of
[FIN4_PAID_RESET_REGENERATION_RANK.md](../questions/FIN4_PAID_RESET_REGENERATION_RANK.md):
there is still no finite well-founded rank, positive charged return, terminal
approximation, contradiction, or positive-gap counterexample.

Moreover, its main positive content is already present, in stronger and more
careful form, in
[CHATGPT_EXTERNAL__NONCOLLAPSING_MAXIMAL_PAID_RESET_ORBIT.md](../notes/CHATGPT_EXTERNAL__NONCOLLAPSING_MAXIMAL_PAID_RESET_ORBIT.md).
That note already records conservative and sharp gain transport, noncollapse
above a positive global minimum, atom transport, summable absorption, the
actual-source/reset adapter, and the remaining renewal boundary.

The material is worth retaining internally if rewritten as the sharp
blockwise Zeno theorem below. The useful refinement is the quantitative
comparison of payoff, cap, and law with the exact remaining composite
absorption.

## Exact valid core, in sharp general form

Let \(I\) be a nonempty finite player set and let all terminal rewards have
absolute value at most \(M\). Let \(\sigma_n\) be actual behavioral profiles.
For every \(n\), let \(q_n\) be an exact product Nash root against the complete
behavioral cap of \(\sigma_n\), and assume

\[
\sigma_{n+1}=q_n\mathbin\triangleright\sigma_n .
\]

Write

\[
a_n=\operatorname{Abs}(q_n),\qquad c_n=1-a_n,\qquad
d_n^i=d_i(\sigma_n),\qquad D_n=\sum_i d_n^i.
\]

Assume \(0<a_n<1\) and that the global lower bound satisfies
\(0<D_*\le D_n\). Put \(P_0=1\) and \(P_n=\prod_{k<n}c_k\).
Exact cap--Nash debt transport gives

\[
d_n^i=P_nd_0^i,\qquad D_n=P_nD_0,\qquad
P_n\ge \rho:=\frac{D_*}{D_0}>0. \tag{1}
\]

This is player-count independent. It gives

\[
\operatorname{supp}_+(d_n)=\operatorname{supp}_+(d_0),\qquad
\frac{d_n^i}{D_n}=\frac{d_0^i}{D_0}. \tag{2}
\]

If the paid certificate scalar is deliberately re-extracted with the
conservative value \(g_{n+1}=c_ng_n\), then

\[
g_n=P_ng_0\ge\rho g_0,\qquad
\frac{g_n}{D_n}=\frac{g_0}{D_0}. \tag{3}
\]

The sharper natural transport factor is

\[
\beta_n=\Pr_{q_n}(\text{all opponents of the paid observer Continue}),
\qquad \beta_n\ge c_n.
\]

The shifted pure-time payoff difference is exactly \(\beta_n\) times the old
difference. Hence the descendant certificate may instead be chosen as
\(g_{n+1}=\beta_ng_n\), which still implies \(g_n\ge P_ng_0\).
Neither convention says that \(g_n\) is the whole payoff difference unless
the initial certificate was exact.

For a fixed inherited terminal atom of mass \(m_0\), literal law prefixing
gives

\[
m_n=P_nm_0. \tag{4}
\]

For a fixed reset-owner/opponent incidence \(\mu_n\), the correct formula has
a nonnegative fresh-prefix term:

\[
\mu_{n+1}=c_n\mu_n+\xi_n,\qquad \xi_n\ge0.
\]

Thus

\[
\mu_n\ge P_n\mu_0\ge\rho\mu_0,\qquad
\frac{\mu_n}{D_n}\ge\frac{\mu_0}{D_0}. \tag{5}
\]

The atom equality (4) and incidence inequality (5) must not be conflated.

### Exact block telescope

For \(m<n\), the composed block has survival and absorption

\[
\prod_{k=m}^{n-1}c_k=\frac{D_n}{D_m},\qquad
A_{m,n}:=1-\prod_{k=m}^{n-1}c_k
=\frac{D_m-D_n}{D_m}. \tag{6}
\]

There is also an exact debt-weighted telescope:

\[
\sum_{k=m}^{n-1}D_ka_k=D_m-D_n. \tag{7}
\]

Since \(1-c\le-\log c\),

\[
\sum_{k=m}^{n-1}a_k\le\log\frac{D_m}{D_n}. \tag{8}
\]

Consequently \(D_n\downarrow D_\infty\ge D_*\), and

\[
\sum_{n=0}^{\infty}a_n
\le\log\frac{D_0}{D_\infty}
\le\log\frac{D_0}{D_*}. \tag{9}
\]

The first bound in (9) is sharper than the submitted one. For the infinite
tail,

\[
A_{m,\infty}=1-\frac{D_\infty}{D_m}\longrightarrow0,\qquad
\sum_{k=m}^{\infty}a_k
\le\log\frac{D_m}{D_\infty}\longrightarrow0. \tag{10}
\]

Thus it is specifically the future portion of this canonical maximal-root
ray whose root charge vanishes. The hypotheses do not rule out a different
admissible chronology leaving \(\sigma_m\).

### Sharp semantic/law displacement bounds

Let \(u_n,b_n,\lambda_n\) be the prescribed payoff, full behavioral cap, and
terminal-outcome law of \(\sigma_n\). Coupling the old profile with its
block-prefixed version gives

\[
\lVert u_n-u_m\rVert_\infty\le2M A_{m,n},\qquad
d_{\mathrm{TV}}(\lambda_n,\lambda_m)\le A_{m,n}. \tag{11}
\]

The same sharp cap bound holds:

\[
\lVert b_n-b_m\rVert_\infty\le2M A_{m,n}. \tag{12}
\]

For one exact root, its successor cap is the expected payoff of the
equilibrium product action against continuation cap \(b_m\). It equals
\(b_m\) on joint all Continue and remains in \([-M,M]\) on absorption.
This proves the one-step estimate; composition proves (12). Equivalently,
split player \(i\)'s root into its Quit and Continue endpoints and use exact
support complementarity. This concerns the complete behavioral cap, not a
stationary response class.

Equations (10)--(12) prove convergence, with

\[
\max\{\lVert u_m-u_\infty\rVert_\infty,
\lVert b_m-b_\infty\rVert_\infty\}
\le2M\left(1-\frac{D_\infty}{D_m}\right). \tag{13}
\]

This is the cleanest rigorous Zeno normal form.

For \(N=|I|>0\), every descendant satisfies

\[
\max_i d_n^i\ge\frac{D_n}{N}\ge\frac{D_*}{N}. \tag{14}
\]

The Fin4 constant is therefore \(D_*/4\), sharp given only total debt.
Since \(D_0\le2MN\), one also has the weaker table-only floor
\(\rho\ge D_*/(2MN)\), hence \(\rho\ge D_*/(8M)\) in Fin4.

## Corrections required in RESET_REGEN.md

1. **Gain scaling is not an automatic semantic identity.** The physical
   shifted difference scales by opponents-only survival \(\beta_n\).
   The equality \(g_{n+1}=c_ng_n\) is a valid conservative choice of
   certificate scalar. The public MaximalOneStepPaidResetRegeneration
   structure exposes neither equality, so an arbitrary inhabitant cannot be
   iterated with it without strengthening the interface.

2. **The paid row is re-extracted.** The proof shifts two pure-time witnesses
   and invokes exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub.
   It does not expose literal equality of every descendant-row field with a
   shifted parent row. Fixed observer and witness order can be retained, but
   the stronger literal-row statement is not public.

3. **Only the displayed invariant ranks are excluded.** Equations (1)--(3)
   rule out descent by positive-debt support, normalized debt, the
   conservative gain/debt ratio, and fixed player/reset labels. They do not
   exclude ranks based on changing root components, binding faces, coalition
   labels, or an owner-repair phase. The conclusion must not say that all
   finite-label ranks are ruled out.

4. **Available future charge is too broad.** Equation (10) concerns the
   consecutive maximal roots of this ray. A reset dispatch or another
   source-matched operation might start a different charged path. Producing
   such a path is precisely the open problem.

5. **Cauchy convergence needs the cap proof.** The submitted note says
   similarly for caps without the exact-Nash support argument. Equations
   (11)--(13) repair this and give sharp block constants.

6. **The surcharge seam is correctly identified but not consumed.**
   capNash_isZeroNash_at_prescribed_iff_surcharge_eq_liveDebt proves the
   stated equivalence. Positive survival and positive returned debt exclude
   only the easy killed-debt converter; they do not prove the surcharge
   equality.

7. **The proposed renewal lemma feeds the direct cumulative-return
   consumer.** Its conclusion is the data of
   QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily. Packaging it
   there and applying exists_uniformEquilibriumPayoff is precise. The
   varying-source paid-cap theorem instead assumes absorption floors and cap
   displacement for supplied cap ports.

8. **Zero-minimum regressions are only boundary examples.** They show that
   actual maximal Zeno behavior is nonempty, but not compatibility with
   \(D_*>0\). The honest conclusion is only that equations (1)--(13) do not
   themselves yield a contradiction.

## Actual-data adapter

The generic checked input is
QuittingPaidCapLiftedSource.maximalOneStepPaidResetRegeneration_or_uniqueAllContinue
in Research/Quitting/PaidCapMaximalOneStepRegeneration.lean. Its positive
branch supplies the actual prefixed profile, the same global minimum, debt
contraction, zero reset debt, positive incidence, and a fresh fixed-law reset
dispatch.

The Fin4 checked adapter is
FinFourSingletonBaseResetRepairPaidCapDoublePort.sourceMaximalRegeneration_or_repairedMaximalRegeneration_or_doubleUnique
in Research/Quitting/FinFourPaidCapMaximalDoubleRegeneration.lean. It starts
the construction on the source or repaired side, or terminates at the
separate double-unique-cap question.

The public API still lacks the recursive wrapper. Classical dependent choice
gives the mathematical alternative

\[
\text{finite arrival at unique all Continue}
\quad\text{or}\quad
\text{an infinite actual orbit satisfying (1)--(13)}.
\]

To formalize this without an arbitrary weakened certificate, the one-step
result should expose the scalar chosen by its own constructor.

## Lean theorem shapes

The smallest useful one-step strengthening is:

    descendant_debt_eq :
      descendant.initialDebt =
        quittingStationaryContinueMass maximalRoot * source.initialDebt

    descendant_coordinateDebt_eq (who) :
      debt descendant who =
        quittingStationaryContinueMass maximalRoot * debt source who

    descendant_gain_eq :
      descendant.gain =
        quittingStationaryContinueMass maximalRoot * source.gain

    descendant_incidence_ge :
      quittingStationaryContinueMass maximalRoot * sourceIncidence ≤
        descendantIncidence

The sharper optional constructor uses
quittingStationaryFixedOpponentsContinueMass maximalRoot source.observer for
the gain factor.

Then define a recursive actual-data object and prove, rather than store as
unexplained fields:

    orbit_coordinateDebt_eq_prefixProduct
    orbit_totalDebt_eq_prefixProduct
    orbit_gain_ge_minimum_ratio_mul
    orbit_incidence_ge_minimum_ratio_mul
    orbit_absorption_summable
    orbit_sum_absorption_le_log_debt_ratio
    orbit_blockAbsorption_eq_debtDrop_div
    orbit_payoff_dist_le_two_mul_bound_mul_blockAbsorption
    orbit_cap_dist_le_two_mul_bound_mul_blockAbsorption
    orbit_law_tv_le_blockAbsorption
    orbit_tailCharge_tendsto_zero

The cap theorem should be proved directly for exact cap--Nash roots; it must
not be inserted as an orbit field.

## Boundary tests

1. **Necessity of \(D_*>0\).** Without a positive lower bound, take
   \(c_n=1/2\). Then \(D_n=2^{-n}D_0\to0\), the paid and atom passports
   collapse, and \(\sum a_n=\infty\).

2. **Sharp logarithmic constant.** Fix \(0<\rho<1\) and use \(N\) equal
   factors \(c=\rho^{1/N}\). Then
   \(N(1-\rho^{1/N})\to-\log\rho\), so no smaller universal function of
   \(\rho\) replaces the logarithm.

3. **Joint versus opponent survival.** If only the paid observer has a Quit
   hazard, then \(\beta_n=1\) while \(c_n<1\). The physical delayed
   pure-time gap is unchanged although the conservative scalar \(c_ng_n\)
   shrinks.

4. **Atom versus incidence.** An old suffix atom is multiplied exactly by
   \(c_n\), while a prefix coalition containing the displayed opponent can
   make the incidence inequality strict.

5. **No terminal selection from the ray.** Equal coordinate debts
   \(d_n^i=D_n/N\) attain (14). The \(D_*/N\) separation cannot be improved
   from total debt alone.

6. **No positive late charge.** Every positive summable \(a_n\) satisfies
   \(\sum_{k\ge m}a_k\to0\). Consecutive late maximal roots cannot provide a
   fixed charge even when paid gain and inherited atoms remain positive.

## Export PASS/FAIL conditions

### PASS as an internal mathematical normal form

Pass after all of:

- state the theorem conditionally on a recursively coherent actual orbit;
- expose the conservative or sharp gain transport;
- distinguish atom equality from incidence inequality;
- include the cap and law displacement proofs;
- restrict the rank no-go to the proved invariant data; and
- state the renewal consumer as open.

### FAIL for exports

Fail unless the packet additionally does at least one of:

- prove the Zeno-passport charge-renewal lemma and package a cumulative
  admissible near-return;
- construct a finite renewable rank with consumed terminal states;
- eliminate the infinite Zeno arm or finite unique-cap arm from the actual
  Fin4 hard residual; or
- construct an actual positive-gap table realizing the complete obstruction.

Without one of these, the packet is a duplicate refinement of an already
reviewed internal normal form and is explicitly a nonanswer under the named
question.

## Sources inspected

- QuittingPaidCapLiftedSource.MaximalOneStepPaidResetRegeneration and
  maximalOneStepPaidResetRegeneration_or_uniqueAllContinue,
  Research/Quitting/PaidCapMaximalOneStepRegeneration.lean;
- quittingMaximalCapPrefixProfile_debt_succ and the literal stage-scaling
  theorem, Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean;
- quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash,
  UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean;
- quittingPureTimeDeviationPayoff_sub_rootThenContinuation_shift_one,
  UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean;
- quittingStationaryContinueMass_mul_incidence_le_lawPrefix,
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean;
- capNash_isZeroNash_at_prescribed_iff_surcharge_eq_liveDebt,
  UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetEndpointSeam.lean;
- QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily,
  UniformEquilibrium/Quitting/Projective/CumulativeChargeNearReturn.lean; and
- sourceMaximalRegeneration_or_repairedMaximalRegeneration_or_doubleUnique,
  Research/Quitting/FinFourPaidCapMaximalDoubleRegeneration.lean.
