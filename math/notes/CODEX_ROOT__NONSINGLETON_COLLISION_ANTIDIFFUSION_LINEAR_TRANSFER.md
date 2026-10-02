# Nonsingleton collision anti-diffusion and linear causal transfer

Author: Codex Root

## Current status

Reviewed mathematical **PASS** and internal Research/formalization candidate.
The unrestricted-strategy and composed deep claims were independently
falsification-tested in
[`CODEX_TESLA`](../feedback/CODEX_ROOT__NONSINGLETON_COLLISION_ANTIDIFFUSION_LINEAR_TRANSFER__BY_CODEX_TESLA.md)
and
[`CODEX_RAMSEY`](../feedback/CODEX_ROOT__NONSINGLETON_COLLISION_ANTIDIFFUSION_LINEAR_TRANSFER__BY_CODEX_RAMSEY.md),
and the complete packet received a final review from
[`CODEX_MINER`](../feedback/CODEX_ROOT__NONSINGLETON_COLLISION_ANTIDIFFUSION_LINEAR_TRANSFER__BY_CODEX_MINER.md).
Their mathematical and source corrections have been incorporated, with no
remaining technical objection.  The result has not been checked as a Lean
declaration.

The final review did not pass the current export-significance gate.  The
sharp Holder concentration theorem and a weaker fixed-resolution causal
split were already present in reviewed conference work.  The genuinely new
content here is the live-weighted linear gain, the direct diffuse-packet
specialization, exact preservation of reached stage mass under routing, and
the sharper deep composition.  These strengthen the already-produced causal
atom interface, but leave its maintained consumer obligation unchanged.

It does **not** construct chronological debt shadowing, an exact
prescribed-payoff Bellman return, a uniform-equilibrium payoff, or a
well-founded consumer of repeated debt transfer.

## 1. Self-contained setting

Let `I` be a nonempty finite player set.  In a discrete-time quitting game,
each player independently randomizes between Continue and Quit at the unique
live history of each date.  The game absorbs at the first date at which the
set of quitters is nonempty.  Infinite continuation pays zero.

Fix a behavioral profile `sigma`.  Each player's live-history hazards induce
a complete stopping law on `Nat ∪ {infinity}`.  Write

\[
  p_i(t)=\Pr(T_i=t),\qquad
  \bar p_i(t)=\Pr(T_i>t).
\]

The player clocks are independent across players.  Dependence across dates
inside one clock is already incorporated in its stopping law; no independence
over dates is assumed.

For a nonempty coalition `S`, write

\[
  m_S(t)=\Pr(\text{the terminal coalition is }S\text{ at date }t).
\]

Then product behavior gives the exact identity

\[
  m_S(t)=
    \prod_{i\in S}p_i(t)
    \prod_{j\notin S}\bar p_j(t).
  \tag{1}
\]

Never atoms are allowed.  They occur in the tail factors and do not affect
the finite-mass estimates below.

## 2. Sharp collision anti-diffusion

### Theorem A: sharp temporal concentration

Let `S` have cardinality `k >= 2`.  For every nonempty finite set of dates
`A`, put

\[
  M_A=\sum_{t\in A}m_S(t),
  \qquad a_A=\max_{t\in A}m_S(t).
\]

Then

\[
  \boxed{a_A\ge M_A^{k/(k-1)}.}
  \tag{2}
\]

For the full countable time axis, with

\[
  M=\sum_{t\ge0}m_S(t),
  \qquad a=\sup_{t\ge0}m_S(t),
\]

one has

\[
  \boxed{a\ge M^{k/(k-1)}.}
  \tag{3}
\]

In particular, because `0 <= M_A,M <= 1` and `k/(k-1) <= 2`,

\[
  \boxed{a_A\ge M_A^2,\qquad a\ge M^2.}
  \tag{4}
\]

If `M>0`, the supremum in (3) is attained at a finite date.

### Proof

By (1),

\[
  m_S(t)\le\prod_{i\in S}p_i(t).
\]

Generalized Holder on `A`, with all exponents equal to `k`, gives

\[
\begin{aligned}
  \sum_{t\in A}m_S(t)^{1/k}
  &\le \sum_{t\in A}\prod_{i\in S}p_i(t)^{1/k}\\
  &\le \prod_{i\in S}
       \left(\sum_{t\in A}p_i(t)\right)^{1/k}\\
  &\le 1.
\end{aligned}
\tag{5}
\]

Therefore

\[
\begin{aligned}
  M_A
  &=\sum_{t\in A}m_S(t)^{(k-1)/k}m_S(t)^{1/k}\\
  &\le a_A^{(k-1)/k}
      \sum_{t\in A}m_S(t)^{1/k}\\
  &\le a_A^{(k-1)/k}.
\end{aligned}
\]

Raising to the power `k/(k-1)` proves (2).  Applying (2) to increasing
finite initial intervals and using monotone convergence proves (3).
Alternatively, generalized Holder applies directly to the summable
nonnegative sequences.

Every finite atom sequence tends to zero because it is summable.  If `M>0`,
then `a>0`; choose a tail on which every term is below `a/2`.  The global
supremum is consequently the maximum of a finite initial segment and is
attained.  Formula (4) follows from `0 <= M <= 1`.  This proves Theorem A.

### Sharpness and the singleton boundary

Let the `k` members of `S` independently choose a date uniformly from
`{0,...,N-1}`, and let every outsider play Never.  Then

\[
  M=N^{1-k},\qquad
  \max_t m_S(t)=N^{-k}=M^{k/(k-1)}.
\]

Thus the exponent in (2)--(3) is sharp.

For `k=1` no positive concentration function of total mass exists: one
player may put total finite mass one uniformly over `N` dates, while the
largest atom is `1/N`.  Hence singleton clocks are the exact exceptional
case.

## 3. Diffuse reprojection packets are singleton-labelled

The current temporal-tightness interface uses
`QuittingReprojectionDiffuseWindowPacket`.  Its window mass is eventually
strictly larger than a fixed `lower > 0`, while its normalized clock mesh
tends uniformly to zero.

### Corollary B

For every such packet,

\[
  \boxed{|S|=1.}
  \tag{6}
\]

### Proof

Suppose `|S|>=2`.  On every sufficiently late packet index, let `M_n` be the
mass of `S` in the selected finite window.  Theorem A gives a date in that
window with stage mass at least `M_n^2`.  The corresponding normalized clock
atom is therefore at least

\[
  \frac{M_n^2}{M_n}=M_n>\text{lower}.
\]

This contradicts uniform convergence of the normalized clock mesh to zero,
applied for example at `epsilon = lower`.  Since terminal coalitions are
nonempty, their only remaining cardinality is one.

This is a literal same-profile conclusion.  It does not condition or replace
the packet's profiles, windows, observer, scale, or defect normalization.

## 4. Survival-weighted collision charge

Fix now:

- a global minimum carrier pair `z_*` of total semantic debt `D_*>0`;
- an actual profile `sigma`;
- a date `t` and a terminal coalition `S` with `|S|>=2`;
- the shifted tail pair after date `t`, denoted `z_tail`;
- the actual product root `x` at date `t`;
- live mass `L` at date `t`;
- stage mass `m=m_S(t)`;
- tail excess `E=D(z_tail)-D_* >= 0`;
- coordinate root Nash defects `delta_i>=0` against the actual tail
  prescribed payoff; and
- total root defect `R=sum_i delta_i`.

Let

\[
  C=\sum_i
    \Pr_x(\text{some opponent of }i\text{ Quits})\,d_i(z_{tail})
\]

be the opponent-absorption debt charge.

The existing exact collision and minimum-debt accounts give

\[
  mD_*\le LC,
  \tag{7}
\]

and

\[
  C\le E+R.
  \tag{8}
\]

The current aggregate wrapper uses `LC<=C` before applying (8).  Retaining
`L` is stronger.

### Theorem C: live-weighted collision alternative

Under the preceding assumptions,

The strongest direct chain is

\[
  \boxed{mD_*\le LC\le L(E+R)=LE+LR\le E+LR.}
  \tag{9}
\]

Consequently either, more sharply,

\[
  LE\ge \frac{mD_*}{2},
  \tag{10a}
\]

which implies the weaker tail-escape form

\[
  E\ge \frac{mD_*}{2},
  \tag{10b}
\]

or there is a player `p` for whom the literal pure-endpoint deviation at the
same reached row has global payoff gain

\[
  g_p=L\delta_p
  \ge \frac{mD_*}{2|I|}.
  \tag{11}
\]

### Proof

Multiplying (8) by `L>=0` gives

\[
  LC\le LE+LR.
\]

Composing with (7) gives `mD_*<=LE+LR`.  Splitting this sum gives (10a) or
`LR>=mD_*/2`.  Since `0<=L<=1` and `E>=0`, (10a) implies the weaker
tail-escape bound (10b), and `LE<=E` gives the final comparison in (9).
Since all coordinate defects are nonnegative, the second arm has some `p`
satisfying

\[
  R\le |I|\delta_p.
\]

Multiplication by `L` and the exact reached-row identity

\[
  \text{payoff gain from the best pure endpoint}=L\delta_p
\]

give (11).  This deviation changes only player `p`'s action at the displayed
row and is a legal complete behavioral deviation.

For `I=Fin 4`, (11) reads

\[
  \boxed{g_p\ge mD_*/8.}
  \tag{12}
\]

## 5. Exact debt transfer at the endpoint

Let `sigma'` be the target profile after the selected player `p` makes the
pure endpoint update, and let `z,z'` be the semantic pairs of `sigma,sigma'`.
Because the opponents are unchanged, player `p`'s unrestricted behavioral
best-response envelope is unchanged.  Hence

\[
  d_p(z')=d_p(z)-g_p.
  \tag{13}
\]

If the source is `epsilon`-near-minimal,

\[
  D(z)\le D_*+\epsilon,
\]

then global minimality of `D_*` and (13) give

\[
  \sum_{j\ne p}(d_j(z')-d_j(z))\ge g_p-\epsilon.
  \tag{14}
\]

For four players, if `epsilon<=g_p/2`, one of the three other players has

\[
  d_j(z')-d_j(z)\ge g_p/6.
  \tag{15}
\]

No sign condition on the other two changes is needed: the maximum of three
real numbers is at least their average.

## 6. Pure endpoint routing preserves stage mass

Let `a` be the selected pure endpoint action and let

\[
  S'=\begin{cases}
    S\cup\{p\},&a=\mathrm{Quit},\\
    S\setminus\{p\},&a=\mathrm{Continue}.
  \end{cases}
\]

This is the repository's `quittingPureEndpointRoutedCoalition`.

### Theorem D: no routed-cylinder loss

If `|S|>=2`, then `S'` is nonempty and

\[
  \boxed{m_{S'}^{\sigma'}(t)\ge m_S^\sigma(t).}
  \tag{16}
\]

### Proof

The pure endpoint update is made only at date `t`, so the probability of
reaching date `t` is unchanged:

\[
  L_{\sigma'}(t)=L_\sigma(t).
\]

At the root, the exact factorization is

\[
  \operatorname{RootMass}_x(S)=
  x_p(\mathbf 1_{p\in S})
  \operatorname{RootMass}_{x[p\leftarrow a]}(S').
  \tag{17}
\]

The first factor lies in `[0,1]`, so routed root mass is at least original
root mass.  Multiplying by the common live mass proves (16).  If the update
removes `p`, the assumption `|S|>=2` guarantees `S\setminus\{p\}` is still
nonempty.

Thus a routed collision may become a singleton, but it becomes a
**concentrated singleton of the same fixed stage mass**, not a diffuse
singleton clock.

## 7. Deep minimum-law consequence

Let `(z_*,muLaw)` be a joint semantic/law carrier point whose semantic
coordinate has debt `D_*>0` equal to the global literal debt infimum.  Suppose
a nonsingleton coalition `S` has law mass

\[
  \mu=\muLaw(S)>0.
\]

The existing causalization theorem supplies actual suffix profiles `sigma_n`,
finite windows carrying more than `mu/2` mass of `S`, and exact cap-Nash root
words of length `n+1`.  Both suffix debt and prefixed debt converge to `D_*`.

### Theorem E: fixed-resolution deep collision transfer

After reselecting the marked date inside each causal window, and discarding
finitely many indices, every suffix has a marked stage satisfying

\[
  m_n>\mu^2/4,
  \tag{18}
\]

and its deeply prefixed actual profile has the shifted stage mass

\[
  \widetilde m_n>\lambda,
  \qquad
  \boxed{\lambda=\mu^2/8.}
  \tag{19}
\]

At each such shifted row, Theorem C gives either

\[
  D(z_{tail,n})-D_*\ge \frac{\mu^2D_*}{16},
  \tag{20}
\]

or an actual pure-endpoint deviation with

\[
  g_n\ge\frac{\mu^2D_*}{64}.
  \tag{21}
\]

The endpoint profile retains a routed nonempty stage atom of mass at least
`mu^2/8`.  In the gain branch, sufficiently late source profiles are close
enough to `D_*` that one of the other three players receives debt increase at
least

\[
  \frac{\mu^2D_*}{384}.
  \tag{22}
\]

After finite-label subsequence extraction, the mover, recipient, endpoint
orientation, and routed coalition can all be held fixed.

### Proof

Apply Theorem A to the finite causal window, whose mass exceeds `mu/2`, to
obtain (18).  Let `c_n` be the joint Continue product of the exact prefix
word.  Exact cap-Nash debt scaling says

\[
  D(\widetilde\sigma_n)=c_nD(\sigma_n).
\]

Both debts converge to the same positive number `D_*`; hence `c_n->1`.
Eventually `c_n>1/2`.  Exact literal root-stack transport gives shifted mass
`c_nm_n`, proving (19).

Apply Theorem C with `m=\widetilde m_n` and `|I|=4`.  This gives (20) or
(21).  Theorem D gives the endpoint atom with no further mass loss.  Since the
prefixed source debts converge to `D_*`, eventually their excess is at most
half the fixed lower bound in (21).  Equations (14)--(15) then prove (22).
Finite player/action/coalition sets permit one final subsequence on which all
listed labels are constant.

### Sharp exponent from the existing joint-law convergence

The current causalization interface already gives convergence of each actual
suffix profile's complete terminal law.  Let `M_n` be the suffix profile's
total `S`-mass.  Then `M_n->mu`.  Apply the full-axis form of Theorem A to
each suffix and select a maximizing finite date.  Its stage mass is at least
`M_n^{k/(k-1)}`.  Since the prefix Continue product tends to one, the shifted
stage mass is eventually larger than every fixed

\[
  \lambda<\mu^{k/(k-1)}.
\]

No stronger cutoff interface is needed; a new finite cutoff can, if desired,
be chosen after the maximizing date.  The conservative statements
(18)--(22) remain useful because their constants follow immediately from the
already named half-mass window.

## 8. Exact effect on the conjecture-facing interface

The live atom route contains a cardinality-blind temporal split and a causal
collision transfer whose packaged actual gain and routed stage atom are
quadratic in a supplied stage-mass floor.  Theorems A--E sharpen that
interface:

\[
\boxed{
  \text{Every genuinely diffuse finite terminal atom is singleton-labelled.}
}
\]

and

\[
\boxed{
  \begin{array}{c}
  \text{Every nonsingleton minimum-law atom yields arbitrarily deep,}\\
  \text{source-matched fixed-resolution collision rows, followed by}\\
  \text{fixed tail escape or a literal gain linear in reached mass,}\\
  \text{with no reached-stage mass loss under routing.}
  \end{array}
}
\]

This gives a direct formal route from the diffuse packet to singleton
cardinality and removes the artificial quadratic losses from the checked
nonsingleton transfer wrappers.  Qualitatively, however, reviewed prior work
already ruled out nonsingleton diffusion and already produced a fixed-scale
tail-escape/profitable-endpoint split.  The surviving strategic obstruction
is unchanged: endpoint debt transfer may cycle, tail escape is not yet a
return, and neither output automatically regenerates the exact
source/successor packet required by chronological debt shadowing.

## 9. Source correspondence and novelty audit

The relevant checked declarations are:

- `quittingBehaviorStoppingLaw_some_toReal` and
  `quittingHazardStoppingLaw_some_toReal` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`;
- `quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauIncidence.lean`;
- `QuittingReprojectionDiffuseWindowPacket` and
  `exists_concentrated_or_diffuseWindowPacket` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionTemporalSplit.lean`;
- `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` and
  `quittingStageCoalitionMass_literalRootStack_add_length` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
- `quittingTerminalDebtSum_capNashRootStack_eq` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`;
- `quittingStageCoalitionMass_mul_tailDebtSum_le_liveMass_mul_charge` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDefectTelescope.lean`;
- `minimumTerminalSemantic_sum_opponentAbsorption_charge_le_excess_add_defect`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDefectCharge.lean`;
- `quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauLocalizedOtherDefect.lean`;
- `quittingRootCoalitionMass_eq_actionProbability_mul_routed`,
  `quittingRootCoalitionMass_le_pureEndpointRouted`, and
  `quittingTerminalPayoff_stageBestEndpointDeviation_markedRouting` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDefectStratification.lean`;
- `quittingLiveMass_stagePureEndpoint_eq` and the current quadratic wrapper
  `causalCollisionEndpoint_atomicBarrier_or_continueRecipient` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCausalCollisionAtomicOrientation.lean`;
- `causalCollision_tailEscape_or_quantitativeNearMinimumTransfer` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCausalCollisionMinimumTransfer.lean`.

The exact routed-root factorization and the underlying collision/debt
accounts are checked.  The conference-source audit also found the following
prior ordinary mathematics:

- [`CHATGPT_EXTERNAL__PURE_TIME_CONCENTRATION_CLAIMANT_NO_GO.md`](CHATGPT_EXTERNAL__PURE_TIME_CONCENTRATION_CLAIMANT_NO_GO.md)
  already proves the full-axis Holder concentration theorem, sharp exponent,
  attainment, uniform-clock equality example, and singleton failure;
- Proposition 2 of
  [`CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md`](CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET.md)
  gives the same nonsingleton concentration and deterministic join/leave atom
  handle;
- [`CODEX_MINER__MACROSCOPIC_COLLISION_LAW_CAUSAL_DISPATCH.md`](CODEX_MINER__MACROSCOPIC_COLLISION_LAW_CAUSAL_DISPATCH.md)
  already composes minimum-law causalization with a weaker cubic
  concentration estimate to obtain the same qualitative fixed-scale
  tail-escape/profitable-endpoint split; and
- [`CODEX_EULER__CAUSAL_SUFFIX_ATOM_AGGREGATE_CONVERSION_ATTEMPT.md`](CODEX_EULER__CAUSAL_SUFFIX_ATOM_AGGREGATE_CONVERSION_ATTEMPT.md)
  records the related whole-window tail-excess/defect-occupation split and
  the absence of a return or finite rank.

Relative to those sources, the new content is:

1. the direct diffuse-packet singleton specialization;
2. retaining live mass through the minimum-charge inequality so the actual
   endpoint gain is linear in stage mass;
3. lifting checked root-mass routing to exact stage-mass monotonicity; and
4. the resulting sharper fixed-resolution deep minimum-law composition.

No paper theorem is invoked.

## 10. Lean handoff

A conservative implementation order is:

1. Prove a generic finite/countable sequence lemma: for `k>=2`, nonnegative
   summable families `p_i` with sums at most one and
   `m_t <= prod_i p_i(t)`, the total mass of `m` is bounded by
   `(sup m)^((k-1)/k)`.  If generalized Holder is inconvenient, first prove
   the cardinality-free square version by selecting two members of `S` and
   applying Cauchy--Schwarz.
2. Connect the individual factors to
   `quittingBehaviorStoppingLaw` and prove the exact stage-coalition clock
   factorization.
3. Add
   `QuittingReprojectionDiffuseWindowPacket.terminal_card_eq_one`.
4. Add a strengthened local charge theorem with conclusion
   `stageMass * Dmin <= tailExcess + liveMass * totalNashDefect`.
5. Strengthen `causalCollision_tailEscape_or_quantitativeBestEndpoint` and
   `causalCollision_tailEscape_or_quantitativeNearMinimumTransfer` to bound
   `card I * gain` below by `lower * Dmin / 2`, not
   `lower^2 * Dmin / 2`.
6. Add the direct stage-mass routing corollary using
   `quittingLiveMass_stagePureEndpoint_eq` and
   `quittingRootCoalitionMass_le_pureEndpointRouted`.
7. Package the conservative deep suffix-atom adapter with resolution
   `mu^2/8` and the Fin4 constants above.

The existing source structures should not receive the desired conclusions as
new fields.  Each theorem should derive them from the current profiles,
windows, prefix words, and literal endpoint update.

## 11. Scope and remaining question

The result controls arbitrary behavioral source profiles in the ordinary
quitting-game information model.  It does not restrict deviations to
stationary, pure-time, or bounded-memory strategies: semantic debt and caps
remain the existing unrestricted behavioral quantities.  Only the selected
profitable endpoint update is pure, as supplied by the exact row-best-endpoint
identity.

The next concrete question is:

> Can a fixed-resolution nonsingleton tail escape or a fixed-resolution
> finite-label endpoint debt-transfer monodromy be converted into an exact
> source/successor packet with a well-founded regeneration rank, or directly
> into cumulative admissible payoff near-return?
