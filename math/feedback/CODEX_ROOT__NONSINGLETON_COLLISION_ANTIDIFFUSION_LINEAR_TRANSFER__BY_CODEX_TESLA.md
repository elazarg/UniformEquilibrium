# Independent review of nonsingleton collision anti-diffusion

Reviewer: Codex Tesla

## Verdict

I independently checked the stopping-law anti-diffusion argument, its diffuse
packet consequence, and its use in the deep minimum-law causalization theorem.
Those claims are mathematically correct in the repository's ordinary
behavioral quitting-game semantics.  Never mass, unbounded stopping support,
and history-dependent behavioral strategies do not create counterexamples.

I found two minor statement repairs and one available strengthening:

1. The finite-window maximum in Theorem A must assume that the finite date set
   is nonempty, or use a maximum-with-zero convention.  The packet application
   has strictly positive window mass, so this does not affect Corollary B or
   Theorem E.
2. Equation (20) has a typographical missing `\ge`.
3. The optional sharp exponent does **not** require a parameterized cutoff
   theorem.  It already follows from the full terminal-law convergence in the
   current causalization interface by applying full-axis anti-diffusion to each
   actual suffix profile.  The conservative `mu^2 / 8` conclusion remains
   valid, but the dependency sentence should be revised.

Subject to the first wording repair, I have no mathematical objection to the
anti-diffusion portion of the packet.  I did not independently re-audit the
later live-weighted collision and endpoint-routing proofs in this review.

## Claim restated and checked

For one actual behavioral profile, let `T_i` be player `i`'s complete stopping
time, let

\[
  p_i(t)=\Pr(T_i=t),\qquad \bar p_i(t)=\Pr(T_i>t),
\]

and let `m_S(t)` be the probability that the first quitting coalition is the
fixed nonempty coalition `S` at date `t`.  The claimed exact identity is

\[
  m_S(t)=\prod_{i\in S}p_i(t)
          \prod_{j\notin S}\bar p_j(t).
  \tag{R1}
\]

This is correct.  Before absorption there is exactly one live public history
at each date.  A behavioral strategy therefore determines one hazard sequence
for each player, hence one stopping law.  Player randomizations are product
distributed across players.  The event in (R1) is precisely `T_i=t` for all
members and `T_j>t` for all outsiders.

No independence across dates is needed in the proof.  All within-player
temporal behavior is already summarized by `T_i`.  A Never atom merely makes

\[
  \sum_{t\in\mathbb N}p_i(t)\le 1
\]

rather than equality, which is exactly the inequality used below.

Let `k=|S|>=2`.  Since outsider survival factors lie in `[0,1]`,

\[
  m_S(t)\le\prod_{i\in S}p_i(t).
\]

Generalized Holder with all exponents equal to `k` gives, on any finite
window `A` and also on the full countable time axis,

\[
  \sum_t m_S(t)^{1/k}
  \le \prod_{i\in S}\left(\sum_t p_i(t)\right)^{1/k}
  \le 1.
  \tag{R2}
\]

If `M=sum_t m_S(t)` and `a=sup_t m_S(t)`, then

\[
  M
  =\sum_t m_S(t)^{(k-1)/k}m_S(t)^{1/k}
  \le a^{(k-1)/k},
\]

so

\[
  a\ge M^{k/(k-1)}\ge M^2.
  \tag{R3}
\]

The last inequality uses `0<=M<=1` and `k/(k-1)<=2`.  The same proof gives
the finite-window statement.  If the full-axis mass is positive, the
supremum is attained: the nonnegative summable atom sequence tends to zero,
so a positive supremum is the maximum of a sufficiently long finite prefix.

The exponent is sharp.  If the `k` members choose independently and uniformly
among `N` dates and all outsiders Never quit, then each collision atom is
`N^{-k}` and the total collision mass is `N^{1-k}`.  Thus

\[
  N^{-k}=(N^{1-k})^{k/(k-1)}.
\]

The singleton boundary is also genuine: a single clock can distribute unit
finite mass uniformly over arbitrarily many dates.

## Diffuse-packet consequence

`QuittingReprojectionDiffuseWindowPacket` provides a fixed `lower>0`, eventual
window mass `M_n>lower`, and normalized clock mesh tending uniformly to zero.
If its terminal label had cardinality at least two, (R3) would produce a date
in the same window with stage mass at least `M_n^2`.  The normalized atom at
that date would be at least

\[
  M_n^2/M_n=M_n>\text{lower},
\]

contradicting the mesh statement at `epsilon=lower`.  Since the terminal
subtype is nonempty, its cardinality is therefore exactly one.

This is a direct same-profile theorem.  It is stronger and earlier than the
currently checked
`QuittingReprojectionDiffuseDeletedWindowPacket.terminal_eq_singleton`, which
first transfers to an owner-deleted clock and then assumes the diffuse-deleted
arm.  The new result removes a nonsingleton
`QuittingReprojectionDiffuseWindowPacket` before that split.

## Deep minimum-law constant

The checked theorem
`exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` supplies:

* actual suffix profiles converging jointly in semantic pair and complete
  terminal law;
* finite `S`-windows of mass greater than `mu/2` eventually;
* cap--Nash root stacks of depth `n+1`;
* prefixed debt tending to the same positive minimum `D_*`.

The suffix semantic debts also tend to `D_*` by joint convergence.  Exact
cap-stack debt scaling therefore makes the stack Continue product `c_n` tend
to one.  Finite-window anti-diffusion gives a suffix stage mass strictly above

\[
  (\mu/2)^2=\mu^2/4,
\]

and eventually `c_n>1/2`.  The checked exact stack transport identity then
gives shifted mass strictly above `mu^2/8`.  Hence the conservative constant
in Theorem E is valid.  Positive minimum debt also excludes any problematic
zero-product stack eventually.

There is a stronger consequence already available from the same hypotheses.
Let

\[
  M_n=\operatorname{quittingTerminalOutcomeMass}(\sigma_n)(S).
\]

Joint law convergence gives `M_n -> mu`.  Apply the full-axis version of
Theorem A to each actual suffix profile, selecting a maximizing finite date
`t_n` once `M_n>0`.  Then

\[
  m_{S,n}(t_n)\ge M_n^{k/(k-1)}.
\]

After exact prefix transport its mass is at least

\[
  c_n M_n^{k/(k-1)},
\]

and this converges to `mu^{k/(k-1)}` because `c_n->1` and `M_n->mu`.
Therefore every fixed

\[
  \lambda<\mu^{k/(k-1)}
\]

is eventually retained.  This does not require the pre-existing cutoff to
capture asymptotically all of the mass.  The maximizing date may be reselected
anywhere on the actual suffix time axis, and the literal stack-transport
identity applies at every date.  If a downstream interface insists on a
cutoff containing the mark, one may choose a new cutoff after selecting that
finite maximizing date.

Accordingly, the draft should replace the statement that the sharp variant
"depends on exposing that parameterized cutoff".  It follows directly from
the already exposed joint-law convergence plus full-axis anti-diffusion.

## Edge cases and attempted falsifications

* **Never atoms:** harmless.  They only reduce each finite stopping-law mass
  sum from one to at most one and appear in outsider survival factors.
* **Infinite stopping support:** harmless.  Summability supplies Holder on the
  countable axis and makes stage masses tend to zero, ensuring attainment of a
  positive supremum.
* **Empty finite window:** as written, `max_{t in A}` is undefined for
  `A=empty`.  Add `A.Nonempty`, define the maximum with zero, or state the
  theorem only under `M_A>0`.  Every intended packet application has positive
  window mass.
* **Zero total collision mass:** (R3) remains true, but there is no positive
  maximizing witness to extract.  The draft correctly assumes positive mass
  when claiming finite-date attainment and in all downstream applications.
* **History dependence:** harmless in the ordinary quitting-game information
  model because the only pre-absorption public history of a given length is
  all Continue.  This argument would require re-examination in a correlated
  or public-signal extension, but no such extension is in scope.
* **Coalition cardinality two:** gives the square exponent exactly and can be
  formalized using the already checked two-member root mass bound plus
  Cauchy--Schwarz.  Larger coalitions only improve the exponent.

## Sources inspected and novelty

I checked the following source interfaces:

* `quittingBehaviorLiveHazard` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
* `quittingBehaviorStoppingLaw`,
  `quittingBehaviorStoppingLaw_some_toReal`,
  `quittingHazardStopMass_eq_survival_mul_stop`,
  `hasSum_quittingHazardStopMass`, and
  `tendsto_quittingHazardStopMass_zero` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`;
* `quittingStageCoalitionMass` and
  `quittingStageCoalitionMass_nonneg` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauTimeDisintegration.lean`;
* `quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass` and
  `quittingLiveRowCoalitionMass_eq_rootCoalitionMass` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauIncidence.lean`;
* `quittingRootCoalitionMass_le_mul_quitProbability_of_mem` and the existing
  deleted-clock singleton theorem in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionDiffuseClockBridge.lean`;
* `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom` and
  `quittingStageCoalitionMass_literalRootStack_add_length` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
* `capNashStack_continueProduct_lowerBound` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`;
* `Math.Probability.exists_maximal_of_tendsto_zero_of_exists_pos` in
  `MathUE/Probability/SquareRootCoalitionClock.lean`.

The repository already contains the root-level two-member product bound and
a square-root budget for related pair clocks, but I found no checked theorem
giving the sharp concentration of one fixed nonsingleton terminal-coalition
clock or the direct source-packet cardinality-one conclusion.  The direct
anti-diffusion adapter is therefore new relative to the inspected sources.
For formalization, the cardinality-free square theorem obtained from two
members and Cauchy--Schwarz is sufficient for every conjecture-facing
conclusion here; the sharp `k/(k-1)` exponent can be added separately if the
real-power or finite-family Holder overhead is substantial.

## Required edits before export

1. State finite-window Theorem A for nonempty finite windows (or give a
   maximum-with-zero convention).
2. Correct the missing `\ge` in equation (20).
3. Revise the optional-sharp-exponent paragraph: the stronger result already
   follows from joint-law convergence and full-axis anti-diffusion, without a
   parameterized cutoff dependency.

After those edits, this review has no unresolved objection to Theorem A,
Corollary B, or the anti-diffusion and prefix-retention portion of Theorem E.
