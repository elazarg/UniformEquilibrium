# Five-face cyclic Green seed and scalar alignment

Author: `CHATGPT_EXTERNAL`

Status: `MATH_REVIEWED` for the generalized conditional cyclic debt theorem;
`REFUTED` as an automatic producer from the currently reviewed quiet-face
fields.

Independent reviews:

- [`feedback/CHATGPT_EXTERNAL__FIN5_FACE_CYCLIC_SEED__BY_CODEX_EULER.md`](../feedback/CHATGPT_EXTERNAL__FIN5_FACE_CYCLIC_SEED__BY_CODEX_EULER.md)
- [`feedback/CHATGPT_EXTERNAL__FIN5_FACE_CYCLIC_SEED__BY_CODEX_RAMSEY.md`](../feedback/CHATGPT_EXTERNAL__FIN5_FACE_CYCLIC_SEED__BY_CODEX_RAMSEY.md)
- [`feedback/CHATGPT_EXTERNAL__FIN5_FACE_CYCLIC_SEED__BY_CODEX_MINER.md`](../feedback/CHATGPT_EXTERNAL__FIN5_FACE_CYCLIC_SEED__BY_CODEX_MINER.md)

Research recommendation: after independent mathematical review, formalize the
conditional cyclic estimate in the repository's `Research` lane even if the
upstream producer remains open. Its value there is to test the proposed seed
interface against the exact periodic and opponent-Green APIs. Such a Research
declaration would be a checked conditional tool, not an `A`/`C` seal or an
unconditional conjecture contraction.

## Current best attempt

For an arbitrary nonempty finite period, approximate cyclic Bellman
annotations and local root Nash error produce an actual periodic profile with
explicit unrestricted terminal-debt bounds whenever each player is excluded
from one positive nonempty coalition atom somewhere in the word. The marked
phase may depend on the player, phases may repeat, and neither own-face
quietness nor an own-phase atom is required.

The proof is in **General finite-period cyclic seed lemma**. The remaining
producer problem is in **What the existing face extraction does not yet
supply**. The scalar separation is valid. Canonical payoff-box rows are
redundant, but phase--seam crossings are real and cannot be renamed as
two-face crossings; see **Scalar alignment and its precise residual**.

## Exact question

Let the player type be finite and nonempty, and let a nonempty finite-period
word have literal product roots `x^t`. Assume:

1. `v^t` is an approximately cyclic Bellman annotation with uniform residual
   `delta`;
2. `x^t` is coordinatewise `epsilon`-Nash against `v^(t+1)`;
3. for every player `i`, some marked phase gives mass at least `rho_i > 0`
   to a nonempty coalition not containing `i`.

Does periodic repetition give an actual ambient profile with all-behavior
terminal debt bounded by

\[
d_i\le {L\over\rho_i}\left(\varepsilon+
{L\delta\over\rho_{\max}}\right),
\qquad \rho_{\max}=\max_i\rho_i?
\]

Can global positive-minimum or terminal-witness structure consume the exact
common-intersection residual when the selected atoms do not cover every
player? Can it exclude or consume the independently reviewed phase--seam
crossing which local quiet-face source fields alone permit?

## Why it could matter

If `epsilon` and `delta` vanish while the atom floors remain fixed, the
periodic word is an actual ambient small-debt seed. This would feed the checked
terminal approximate-Nash endpoint and avoid aligning five full semantic
pairs. Under a positive terminal exploitability gap, the same estimate forces
a quantitative scalar incompatibility.

This is a conditional consumer until the nonempty atoms and scalar cyclic
annotations are produced from arbitrary counterexample data.

## Sources checked

- `quittingRootSequenceTerminalDebt_le_actualCoordinateDefect_add` and the
  finite opponent-Green telescope in
  `UniformEquilibrium/Quitting/Root/TerminalDebtGreenAccount.lean`.
- `isεQuittingRootEndpointNash_of_tail_close` and
  `abs_quittingRootEndpointDifference_sub_le_tail` in
  `UniformEquilibrium/Quitting/Root/TailStability.lean`.
- `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart` and
  `isεQuittingRootNash_iff_coordinateNashDefect_le` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`.
- `isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` in
  `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.
- `finiteAffineIntervalFeasible_iff` in
  `MathUE/FiniteAffineIntervalFeasibility.lean`.
- `notes/CHATGPT_EXTERNAL__CODIMENSION_ONE_QUIET_FACE_ATOM.md` and its two
  independent reviews. That result permits its fixed selected coalition to
  be empty.

No Lean declaration for the composed five-face estimate has been compiled.

## One-coordinate endpoint dependence

For a fixed product root `x`, the Quit-minus-Continue endpoint difference of
player `i` has the form

\[
G_i(x,z_i)=c_i(x)-m_i(x)z_i,
\]

where `m_i(x)` is the probability that every opponent of `i` Continues. No
other continuation coordinate occurs.

If player `w` Continues surely and the survivor coordinates are already
`epsilon`-Nash, the missing endpoint condition is

\[
G_w(x,z_w)\le\varepsilon.
\]

When `m_w(x)>0`, the algebraic correction

\[
\widehat z_w=z_w+
{[G_w(x,z_w)-\varepsilon]_+\over m_w(x)}
\]

makes the outsider condition safe without changing another player's endpoint
difference. This is an algebraic statement in `R^5`. To use it as a bounded
continuation annotation, one must additionally prove that `widehat z_w`
remains in the canonical payoff box. If it lies beyond the box, the scalar row
is individually infeasible. If `m_w(x)=0` and the row is unsafe, no tail
coordinate can repair it.

## General finite-period cyclic seed lemma

Index `L>0` phases cyclically. Let `u^t` be the actual terminal payoff of the
periodic profile started at phase `t`, and put

\[
\beta_t=\Pr_{x^t}(\text{all Continue}).
\]

Assume

\[
\|v^t-F(x^t;v^{t+1})\|_\infty\le\delta
\]

and that `x^t` is an `epsilon`-Nash root against `v^(t+1)`. Assume a nonempty
player type and nonnegative `epsilon,delta`. For every player `i`, choose a
phase `tau(i)`, a number `rho_i>0`, and a nonempty coalition `A_i` not
containing `i` whose full root mass under `x^(tau(i))` is at least `rho_i`.
Put `rho_max=max_i rho_i>0`.

### Payoff attachment

The Bellman operator has scalar tail coefficient `beta_t`, hence

\[
|u_i^t-v_i^t|
\le\delta+\beta_t|u_i^{t+1}-v_i^{t+1}|.
\]

Every displayed atom is disjoint from all Continue. Choosing a player with
largest `rho_i` shows that the `L`-phase joint survival product is at most
`1-rho_max`. Iterating around the
cycle gives

\[
|u_i^t-v_i^t|\le {L\delta\over\rho_{\max}}.
\]

Tail stability then makes every `x^t` an

\[
\eta_0=\varepsilon+{L\delta\over\rho_{\max}}
\]

Nash root against the literal periodic continuation `u^(t+1)`.

### All-behavior debt account

Let `D_i^t` be the full behavioral terminal debt from phase `t`, and let
`m_{i,t}` be the probability that every opponent of `i` Continues at root
`x^t`. The checked one-step Green account gives

\[
D_i^t\le\eta_0+m_{i,t}D_i^{t+1}.
\]

At phase `tau(i)`, the full atom `A_i` already contains the factor that `i`
Continues. Removing that factor by forcing `i` to Continue weakly increases
the corresponding opponent-only event. Hence

\[
m_{i,\tau(i)}\le1-\rho_i.
\]

All other factors are at most one. Iterating once around the periodic word and
using `D_i^(t+L)=D_i^t` yields

\[
D_i^t\le L\eta_0+(1-\rho_i)D_i^t,
\]

and therefore

\[
\boxed{
D_i^t\le {L\over\rho_i}
\left(\varepsilon+{L\delta\over\rho_{\max}}\right).}
\]

This debt is defined using the unrestricted behavioral cap. The lemma does
not merely control deviations within the periodic strategy class.

When `epsilon=delta=0`, the exact cyclic values and local exact roots, together
with the playerwise opponent-cycle contraction just proved, satisfy the
interface of the exact periodic compiler directly. No punishment-floor
hypothesis is needed for that compiler.

## Scalar alignment and its precise residual

For fixed roots, every Bellman equation and endpoint condition for player `i`
contains only that player's five continuation scalars. Thus the vector problem
does separate into five scalar systems. Recombining player coordinates inside
one closed Bellman cycle is legitimate because the periodically repeated word
then realizes the resulting vector; this is different from claiming that an
arbitrary coordinatewise recombination belongs to the terminal-semantic
carrier.

After cutting the cycle, propagate `L-1` Bellman rows exactly and retain the
remaining Bellman mismatch as a two-sided closing seam. The other phase values
are affine functions of one cut scalar. Endpoint inequalities and the two seam
inequalities form a finite affine interval system.
The checked interval theorem implies that infeasibility is witnessed by:

- one row infeasible at both endpoints; or
- one lower-oriented and one upper-oriented crossed pair.

Canonical payoff-box rows are redundant: every exact one-step Bellman map
preserves the canonical reward interval. The two seam rows are jointly
feasible and therefore cannot form a singleton or seam--seam minimal
obstruction. The exact exhaustive minimal certificate types are:

1. one phase-Nash row infeasible throughout the reward interval;
2. two crossed phase-Nash rows; or
3. one phase-Nash row crossed with one closing-seam row.

The third type occurs in literal rational Fin5 data with a mass-`1/2`
nonempty atom on every quiet face. It persists for a fixed positive seam
range. See the reviewed classification
[`CODEX_MINER__FIN5_SCALAR_SEAM_BOX_CERTIFICATE_CLASSIFICATION.md`](CODEX_MINER__FIN5_SCALAR_SEAM_BOX_CERTIFICATE_CLASSIFICATION.md)
and the stronger full-face-source completion
[`CODEX_RAMSEY__FIN5_FULL_FACE_SOURCE_PHASE_SEAM_SEPARATION.md`](CODEX_RAMSEY__FIN5_FULL_FACE_SOURCE_PHASE_SEAM_SEPARATION.md).

For exact Bellman closure, the absorbing five-root word has a unique cyclic
payoff annotation. In that specialization there is no free cut scalar after
the closing equality is imposed; failure means that the unique annotation
violates a root-Nash condition; canonical box failure is impossible.

## Quantitative counterexample consequence

Let

\[
a=\inf_\sigma\max_i d_i(\sigma)>0.
\]

For a five-root word satisfying covering atom floors, let `alpha` be its
largest coordinate root defect against its own actual periodic continuation.
The conditional seed lemma with `delta=0` and
`rho_max=max_i rho_i` gives

\[
\boxed{\alpha\ge {a\rho_{\min}\over5},
\qquad \rho_{\min}=\min_i\rho_i.}
\]

If, in addition, every face supplies a **nonempty** conditional atom with

\[
\rho_i\ge {a\over64M},
\]

then

\[
\boxed{\alpha\ge {a^2\over320M}.}
\]

With an approximate seam, the corresponding conditional inequality is

\[
\varepsilon+{5\delta\over\rho_{\max}}
\ge {a\rho_{\min}\over5}.
\]

The second displayed constant is not currently an unconditional consequence
of the reviewed quiet-face extraction, for the reason below.

## What the existing face extraction does not yet supply

The reviewed codimension-one result selects a fixed coalition
`A subseteq I \ {i}` at a reached quiet-face row and proves, after taking
`gamma=a/2`, the conditional-row mass bound

\[
p(A)\ge {a\over64M}.
\]

But `A` may be empty. In the empty case this is the all-survivors-Continue
event; it supplies no absorption and no opponent-survival contraction for the
periodic seed. The associated gain is a solo/continuation premium created only
when the omitted player deviates.

Discard the selected empty cells and let `C` be the intersection of all
selected nonempty cells, using the whole player set when all are empty. The
selected cells cover every player exactly when `C` is empty. In that case the
cross-phase version of the seed lemma has the required contraction atoms even
if some own-face selected cells are empty.

If `C` is nonempty, every `i in C` has an empty own-face premium and belongs
to every selected nonempty cell on the other sources. This
common-participant/solo-premium pattern has no checked same-source consumer.
The exact set-cover theorem and two reviewed separation tables are in
[`CODEX_RAMSEY__FIN5_FACE_ATOM_COVER_AND_CYCLIC_ALIGNMENT_BARRIER.md`](CODEX_RAMSEY__FIN5_FACE_ATOM_COVER_AND_CYCLIC_ALIGNMENT_BARRIER.md).

The prior extraction also produces five unrelated reached suffix families,
not scalar cyclic annotations satisfying a vanishing Bellman seam. Solving or
certifying failure of those five scalar systems remains the alignment
producer.

## Reviewed disposition and live objections

The cyclic estimate, its unrestricted-deviation scope, cross-phase atom
generalization, set-cover residual, scalar certificate classification, and
three exact Fin5 regression families have passed independent review.

Two producer obligations remain:

1. consume the nonempty common-intersection residual using genuinely
   same-source data; and
2. use global positive-minimum/terminal-witness structure to exclude or
   consume phase--seam incompatibility.

Local quiet-face source fields alone cannot do either: the reviewed rational
examples already include exact two-date deleted-game Nash sources, positive
omitted-player gaps, and uniform nonempty atom floors while retaining the
phase--seam obstruction. Their ambient games have exact equilibria and
`D_*=0`, so they do not rule out a theorem using positive global-minimum data.

## Narrow Research implementation target

The first implementation should contain only the supplied-object theorem:

```lean
theorem finiteCycle_terminalDebt_le_of_coveringAtoms
    (roots : Fin K → ι → PMF Bool)
    (value : Fin K → Payoff ι)
    (epsilon delta : ℝ)
    (rho : ι → ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hdelta : 0 ≤ delta)
    (hrho : ∀ i, 0 < rho i)
    (hbellman : ...)
    (hnash : ...)
    (hatom : ∀ i, ∃ phase A,
      A.Nonempty ∧ i ∉ A ∧
      rho i ≤ quittingRootCoalitionMass (roots phase) A) :
    ∀ phase i,
      quittingTerminalDeviationDebt reward
          (quittingCyclicBehaviorProfile reward roots phase) i ≤
        (K : ℝ) / rho i *
          (epsilon + (K : ℝ) * delta / Finset.univ.sup' ... rho)
```

The exact Lean representation of the positive finite maximum of `rho` should
follow the existing finite-maximum API rather than the schematic `sup'` above.
The proof should reuse the one-step Green inequality and tail stability, not
rebuild behavioral best-response semantics.

Only after this theorem compiles should a second Research adapter encode the
five independent scalar interval systems. That adapter should omit redundant
canonical box rows and preserve phase rows and closing-seam rows as distinct
constructors. The two reviewed rational regressions should be formalized as
negative tests for atom-cover and phase--seam producer claims.
