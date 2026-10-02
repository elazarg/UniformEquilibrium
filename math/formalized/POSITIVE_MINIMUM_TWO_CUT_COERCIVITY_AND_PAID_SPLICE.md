# Positive-minimum two-cut coercivity and paid splice

Authors: GPT conference participant; strengthened and assembled by
`CODEX_ROOT` and `CODEX_ADVERSARY`

Independent reviews:
[CODEX_ROOT](../feedback/NONZERO_PERSIST_ATTEMPT_1_FOLLOWUP_2__BY_CODEX_ROOT.md)
and
[CODEX_ADVERSARY](../feedback/NONZERO_PERSIST_ATTEMPT_1_FOLLOWUP_2__BY_CODEX_ADVERSARY.md)

## Exact statement

Let \(I\) be a nonempty finite player set and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a finite quitting-game reward table. Payoff is \(r(S)\) if the first
nonempty quitting coalition is \(S\), and zero if everyone Continues forever.
At every live date the players randomize independently. A unilateral
behavioral strategy may be history-dependent, may Quit arbitrarily late, and
may put positive mass on Never.

For an executable behavioral profile \(\sigma\), define its terminal semantic
pair

\[
 z(\sigma)=(U(\sigma),B(\sigma)),
\]

where

\[
 U_i(\sigma)=\operatorname{Payoff}_i(\sigma),\qquad
 B_i(\sigma)=
 \sup_{\tau_i}\operatorname{Payoff}_i(\tau_i,\sigma_{-i}).
\]

The supremum ranges over all unilateral behavioral strategies. Put

\[
 d_i(U,B)=B_i-U_i,\qquad D(U,B)=\sum_{i\in I}d_i(U,B).
\]

Let \(\mathcal K_r\) be the closure of the set of all executable terminal
semantic pairs. Its compactness gives

\[
 D_*=\min_{z\in\mathcal K_r}D(z).
\]

Assume \(D_*>0\).

Take one executable profile and two finite cuts \(C_1<C_2\). Let
\(L=C_2-C_1\). For \(0\le t\le L\), let
\(z_t=(U_t,B_t)\) be the literal terminal semantic pair of the suffix starting
at date \(C_1+t\). For \(t<L\), let \(x_t\) be its actual product root, let
\(q_{t,i}\) be player \(i\)'s marginal Quit probability, and put

\[
 c_t=\prod_{i\in I}(1-q_{t,i}),\qquad
 P_0=1,\qquad P_t=\prod_{u<t}c_u.
\]

For a root \(x\) and continuation vector \(b\), write
\[
 \operatorname{NDef}_{r,i}(x;b)
 =
 \max\{Q_{r,i}(x;b),C_{r,i}(x;b)\}-F_{r,i}(x;b),
\]
where \(Q,C\) are the pure-Quit and pure-Continue endpoint payoffs and \(F\)
is the payoff under the displayed mixed root. Define

\[
 \rho_{t,i}=\operatorname{NDef}_{r,i}(x_t;B_{t+1}),\qquad
 \rho_t=\sum_i\rho_{t,i},\qquad
 \mathcal C_i=\sum_{t<L}P_t\rho_{t,i},\qquad
 \mathcal C=\sum_i\mathcal C_i.
\]

Then:

1. The coordinate and total debt identities are

   \[
   d_i(z_t)=\rho_{t,i}+c_t d_i(z_{t+1}),
   \]

   \[
   D(z_0)=\mathcal C+P_LD(z_L).
   \]

2. For every \(0\le\theta<1\), if \(P_L\le\theta\), then, with
   \(\Delta=D(z_L)-D_*\ge0\),

   \[
   \boxed{\mathcal C+\theta\Delta\ge(1-\theta)D_*.}
   \]

3. Let

   \[
   H=\sum_{t<L}\sum_{i\in I}q_{t,i}.
   \]

   If \(H\ge\chi>0\), define

   \[
   K_\chi=(1-e^{-\chi})D_*,
   \qquad
   \delta_\chi=\frac{e^\chi-1}{2}D_*.
   \]

   Then

   \[
   \boxed{
   D(z_L)\ge D_*+\delta_\chi
   \quad\text{or}\quad
   \exists p\in I,\quad
   d_p(z_0)>\frac{K_\chi}{2|I|}.}
   \]

   The selected payer \(p\) may depend on this block, but is selected before
   any cap-approximation tolerance.

4. In the second alternative, for every \(\eta>0\) there is one actual
   unilateral behavioral replacement of player \(p\) on the \(C_1\)-suffix
   such that, writing \(G_p^\eta\) for its suffix payoff gain and
   \(z_0^\eta\) for the replacement suffix's semantic pair,

   \[
   G_p^\eta\ge d_p(z_0)-\eta
      >\frac{K_\chi}{2|I|}-\eta,
   \qquad
   d_p(z_0^\eta)\le\eta.
   \]

5. Extend this replacement to the parent profile by leaving player \(p\)'s
   strategy unchanged at every date strictly before \(C_1\). Let \(R\) be
   the parent's actual probability of reaching date \(C_1\). Then

   \[
   \text{parent payoff gain}=R\,G_p^\eta,
   \]

   and this is also the exact decrease of the parent's \(p\)-debt. No
   total-debt decrease is asserted.

   If \(R\ge r_0>0\) and
   \(0<\eta<K_\chi/(2|I|)\), then

   \[
   \text{parent payoff gain and \(p\)-debt decrease}
   >
   r_0\left(\frac{K_\chi}{2|I|}-\eta\right).
   \]

   In particular, for \(I=\operatorname{Fin}4\) and
   \(\eta=K_\chi/16\), the gain and \(p\)-debt decrease are strictly larger
   than

   \[
   \boxed{\frac{r_0K_\chi}{16},}
   \]

   while the reached replacement suffix has \(p\)-debt at most
   \(K_\chi/16\).

6. The parent splice preserves the law of every finite cylinder determined
   strictly before \(C_1\). Therefore, if a marked row is at \(m<C_1\), its
   root, its reach, every specified quitting-coalition atom at that row, and
   every terminal branch ending before \(C_1\) are unchanged. No event or
   semantic annotation depending on play at or after \(C_1\) is claimed to
   be preserved.

### Seam-stable version

There is also a purely semantic version. At step \(t\), let the exact root
step use an expected child \(\widehat z_{t+1}\), while the next decoded
candidate is \(z_{t+1}\), and assume

\[
 z_t=\operatorname{Prefix}_{x_t}(\widehat z_{t+1}).
\]

Put

\[
 \widehat\rho_{t,i}
 =\operatorname{NDef}_{r,i}(x_t;\widehat B_{t+1}),\qquad
 \widehat{\mathcal C}
 =\sum_{t<L}P_t\sum_i\widehat\rho_{t,i},
\]

and

\[
 e_t=D(\widehat z_{t+1})-D(z_{t+1}),\qquad
 S_P=\sum_{t<L}P_{t+1}|e_t|.
\]

Assume the endpoint pairs \(z_0,z_L\) lie in \(\mathcal K_r\). Then

\[
 D(z_0)
 =\widehat{\mathcal C}+P_LD(z_L)+\sum_{t<L}P_{t+1}e_t.
\]

If \(H\ge\chi>0\), then

\[
 \boxed{
 \widehat{\mathcal C}+S_P+e^{-\chi}\bigl(D(z_L)-D_*\bigr)
 \ge(1-e^{-\chi})D_*.}
\]

If the seam has coordinatewise bounds

\[
 |\widehat U_{t+1,i}-U_{t+1,i}|\le a_{t,i},
 \qquad
 |\widehat B_{t+1,i}-B_{t+1,i}|\le b_{t,i},
\]

then

\[
 |e_t|\le\sum_i(a_{t,i}+b_{t,i}).
\]

Thus a payoff-only seam is insufficient. A common sup error \(s_t\) on each
of the two semantic coordinates costs at most \(2|I|s_t\), or \(8s_t\) in
Fin4. The seam-stable inequality is algebraic; it does not itself produce a
behavioral replacement unless the starting pair is the literal semantic pair
of an executable profile.

## Conjecture-facing change

This result closes the finite analytic step in the positive-minimum
chronology route:

\[
\text{literal post-mark block with order-one total hazard}
\Longrightarrow
\begin{cases}
\text{a quantitative off-minimum endpoint},\\
\text{or a block-specific actual paid replacement}.
\end{cases}
\]

It removes the need to replace approximately Nash rows by exact roots. The
local defects are evaluated directly against the actual unrestricted cap
coordinates. In the paid arm it supplies the precise output needed for a
source-preserving next step: an actual behavioral move, a small reached
payer-debt coordinate, exact parent reach scaling, and retention of every
finite pre-cut atom.

Relative to the live positive-minimum and paid-exit obligations, the remaining
work is source-specific: produce such blocks with a uniform hazard and reach
floor, make the selected output a renewable child or a terminal consumer, and
control any full payoff/cap seams. This packet supplies none of those producer
claims.

## Definitions and assumptions audit

- Probability is the ordinary product law of the displayed behavioral
  profile. All reach and survival quantities are unconditional probabilities.
- The only public nonterminal history at a date is that all previous players
  Continued. Consequently an arbitrary behavioral deviation is represented
  on payoff-relevant histories by an arbitrary time-dependent Quit hazard.
- The cap \(B_i\) ranges over all behavioral deviations. It includes Never
  and arbitrarily late quitting and is not a stationary, finite-deadline, or
  bounded-controller cap.
- The replacement is only approximately cap-attaining. No attainment or
  compactness of the behavioral strategy space is assumed.
- The player \(p\) is fixed for the displayed block and all choices of
  \(\eta\), not across an unrelated family of blocks.
- The parent reach floor is an explicit hypothesis. It is not inferred from
  the marked atom's local mass.

## Source correspondence

The exact semantic translations already exposed in Lean are:

- `quittingTerminalSemanticPair`, `quittingTerminalSemanticDebt`, and
  `quittingTerminalSemanticCarrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `QuittingBoundedSeamChain.actualPair_eq_prefix` in
  `UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalSeamReduction.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect`
  and
  `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect`
  in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`;
- `quittingRootCoordinateNashDefect_nonneg` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`;
- `exists_quittingContinuation_deviation_ge_sub` in
  `UniformEquilibrium/Quitting/Root/FirstBranch.lean`; and
- `not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt`
  in
  `UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean`.

The new ordinary mathematics is the two-cut telescope organized at the
positive global floor, the sharp \(e^{-H}\) dichotomy, the survival-weighted
two-coordinate seam form, and the exact pre-cut behavioral splice conclusion.
No literature theorem is invoked.

## Proof

For a literal suffix, dynamic programming gives

\[
 z_t=\operatorname{Prefix}_{x_t}(z_{t+1}).
\]

The cap coordinate at date \(t\) is the maximum of the pure-Quit and
pure-Continue values against the unrestricted cap at date \(t+1\). Subtracting
the prescribed Bellman value gives, coordinatewise,

\[
 d_i(z_t)
 =
 \operatorname{NDef}_{r,i}(x_t;B_{t+1})
 +c_t d_i(z_{t+1}).
\]

Summing over players gives
\[
 D(z_t)=\rho_t+c_tD(z_{t+1}).
\]
Multiplying the equation at date \(t\) by \(P_t\) and summing over
\(t<L\) telescopes to
\[
 D(z_0)=\mathcal C+P_LD(z_L).
\]

Since both endpoints belong to the carrier,
\[
 D_*\le D(z_0)=\mathcal C+P_L(D_*+\Delta).
\]
Therefore
\[
 \mathcal C+P_L\Delta\ge(1-P_L)D_*.
\]
If \(P_L\le\theta<1\), increasing the nonnegative coefficient of
\(\Delta\) to \(\theta\) and decreasing the right side to
\((1-\theta)D_*\) proves the two-cut inequality.

For every \(q\in[0,1]\), \(1-q\le e^{-q}\). Hence
\[
 P_L
 =\prod_{t<L}\prod_i(1-q_{t,i})
 \le e^{-H}.
\]
When \(H\ge\chi\), use \(\theta=e^{-\chi}\). If
\(\Delta<\delta_\chi\), then
\[
 e^{-\chi}\Delta
 <
 e^{-\chi}\frac{e^\chi-1}{2}D_*
 =\frac{K_\chi}{2}.
\]
The two-cut inequality therefore gives
\(\mathcal C>K_\chi/2\). Since
\(\mathcal C=\sum_i\mathcal C_i\), some player \(p\) has
\(\mathcal C_p>K_\chi/(2|I|)\). The coordinate telescope and
\(d_p(z_L)\ge0\) give
\[
 d_p(z_0)=\mathcal C_p+P_Ld_p(z_L)
 \ge\mathcal C_p.
\]

By the definition of \(B_{0,p}\) as a supremum, for every \(\eta>0\) an
actual behavioral deviation has payoff at least \(B_{0,p}-\eta\). Its gain
over \(U_{0,p}\) is at least \(d_p(z_0)-\eta\). The opponents did not change,
so its own new cap remains \(B_{0,p}\); its new \(p\)-debt is at most
\(\eta\).

Splice that deviation at the live history at \(C_1\), leaving the parent's
strategy unchanged before the cut. The pre-cut law is identical. Conditional
on reaching the cut the payoff change is \(G_p^\eta\), and otherwise it is
zero, so the parent payoff change is exactly \(RG_p^\eta\). Player \(p\)'s
outer cap also depends only on the opponents and is unchanged. Thus the same
quantity is the exact reduction of outer \(p\)-debt. If the suffix lower
bound is positive, \(R\ge r_0\) gives the displayed quantitative lower
bound. This positivity condition is why the claim is restricted to
\(\eta<K_\chi/(2|I|)\).

For seams, substitute
\[
 D(\widehat z_{t+1})=D(z_{t+1})+e_t
\]
in every one-step debt equation. The coefficient of \(e_t\) is
\(P_tc_t=P_{t+1}\), giving the exact signed telescope. Bound the signed sum
above by \(S_P\) and repeat the carrier-floor argument. Finally,
\[
 |D(\widehat z)-D(z)|
 \le\sum_i\left(
   |\widehat U_i-U_i|+|\widehat B_i-B_i|
 \right),
\]
which proves the two-coordinate seam estimate.

Every cylinder determined before \(C_1\) has the same probability under the
parent and the splice because every player's pre-cut behavior is identical.
This proves the atom-preservation clause.

## Boundary tests

1. **Zero hazard.** If \(H=0\), then \(P_L=1\), and the coercive constant
   \(K_\chi\) is unavailable. A positive hazard floor is indispensable.
2. **Zero semantic minimum.** If \(D_*=0\), the coercive lower bound is zero.
   The theorem correctly makes no paid or off-minimum conclusion.
3. **Exact cap-Nash block.** If every \(\rho_t=0\) and \(H\ge\chi\), the
   identity gives the stronger bound
   \[
   D(z_L)-D_*\ge(e^\chi-1)D_*.
   \]
   Thus a positive-hazard exact cap-Nash block cannot return close to the
   positive-minimum fibre.
4. **One player.** The argument remains valid with \(|I|=1\); the unique
   player is the payer. No multi-player pigeonhole fact is hidden in the
   coercivity identity.
5. **Reach-sign falsifier.** From \(R\ge r_0\), the implication
   \(RG\ge r_0g\) is invalid if the only known lower bound \(g\) is negative.
   This is why the parent conclusion explicitly requires
   \(\eta<K_\chi/(2|I|)\). The Fin4 choice \(K_\chi/16\) is safely positive.
6. **Payoff-only seam falsifier.** Two semantic pairs may have identical
   prescribed coordinate \(U\) and different cap coordinate \(B\), hence
   different debt. A payoff-only seam bound cannot control the debt
   telescope.
7. **Post-cut events.** The replacement may change the law at date \(C_1\)
   and afterward. Preservation is deliberately limited to finite cylinders
   strictly before the cut.

## Adapter and consumer

The actual-data adapter is literal: start with any executable profile and two
finite cuts, take the suffix profiles, and apply
`quittingTerminalSemanticPair`. The checked semantic-prefix identity supplies
the recursion with unrestricted cap coordinates. No abstract payoff
annotation is substituted for these pairs.

The finite consumer is the paid splice. In the non-off-minimum arm it returns
one actual behavioral replacement, an arbitrarily small reached debt for its
block-dependent payer, an exact reach-weighted decrease of the parent's same
debt coordinate, and unchanged finite pre-cut atoms. This directly consumes
the analytic charge without rowwise exactification.

It is not a terminal equilibrium consumer. Applying it recursively requires a
separate source theorem showing that its output remains in a renewable domain,
or a separate terminal/return consumer.

## Lean handoff

A narrow formalization can be split into:

1. `quittingTerminalSemanticDebtSum_twoCut_eq`, iterating
   `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect`;
2. `quittingTerminalSemanticDebtSum_twoCut_coercive`, adding the two carrier
   floor inequalities;
3. `quittingJointContinueProduct_le_exp_neg_totalMarginalHazard`, proving the
   sharp product estimate;
4. `exists_paidSuffixReplacement_of_twoCut_not_offMinimum`, returning the
   block-dependent player, behavioral deviation, gain, and new coordinate
   debt;
5. `quittingParentDebt_sub_spliceDebt_eq_reach_mul_suffixGain`, with an
   explicit splice and equality of opponents; and
6. an abstract weighted signed-seam telescope, followed by the existing
   semantic-debt Lipschitz estimate.

Useful tests are a one-player profile, an all-Continue block, a sure-absorption
row, a cap-Nash block, and a seam changing only the cap coordinate. The
formalization must quantify over `BehaviorStrategy`, not a finite or
stationary substitute.

## Scope and nonclaims

This packet does not:

- produce the two cuts, a positive \(\chi\), or a positive parent reach floor;
- choose one payer common to multiple blocks;
- make the paid replacement a legal child of a source graph;
- preserve a cap, payoff annotation, or terminal-law event depending on play
  at or after the cut;
- prove total semantic-debt descent;
- turn payoff-only seams into semantic seams;
- construct a macro tower, renewable rank, cumulative return, terminal
  approximate Nash profile, or uniform-equilibrium payoff; or
- consume the strict positive-minimum trichotomy.

## Lean formalization record

Pre-formalization packet SHA-256:
`f6ea261fc1f3f3d2c692d53fb3c26d5d8fcddfa393823baea746d810e8dc0403`.

The executable two-cut layer landed in commit
`db878ac8eb1b54a6777de784fec369ded0adbae4`, in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveMinimumTwoCutPaidSplice.lean`.
The separate signed-seam algebra landed in commit
`0702492673091c10f9e14f0be6aa9b4d9fe36d55`, in
`UniformEquilibrium/Quitting/Debt/Dynamic/TerminalSemanticSignedSeamTelescope.lean`.

The principal checked declarations are
`quittingTerminalSemanticDebtSum_twoCut_eq`,
`QuittingPositiveMinimumTwoCutBlock.totalCharge_add_theta_mul_exitExcess_ge`,
`QuittingUniformlyReachedPostMarkTwoCutBlock.offMinimum_or_exists_paidSplice`,
`finFour_offMinimum_or_exists_paidSplice`, the literal `paidSpliceProfile`
update and pre-entry preservation theorems,
`QuittingTerminalSemanticSeamChain.debtSum_eq_totalCharge_add_endpoint_add_weightedSignedSeamError`,
`finFour_weightedAbsoluteDebtSeamError_le_of_commonCoordinateBound`, and
`totalCharge_add_coordinateSeamBound_add_theta_endpointExcess_ge`.

Evidence seals are `M` and `L`, with a conditional `C` for a supplied
uniformly reached two-cut block.  There is no source `A`: the checked code
does not produce cuts, a reach floor, or a renewable child.  It does not fix
one payer across blocks, preserve post-cut caps or laws, prove total-debt
descent, accept payoff-only seams, or produce a terminal or
uniform-equilibrium conclusion.
