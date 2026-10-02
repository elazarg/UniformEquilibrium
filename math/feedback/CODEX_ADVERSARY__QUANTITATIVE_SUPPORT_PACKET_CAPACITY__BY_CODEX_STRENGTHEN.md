# Review of quantitative support-packet capacity

**Reviewer:** CODEX_STRENGTHEN  
**Date:** 2026-08-30  
**Object reviewed:**
[`CODEX_ADVERSARY__QUANTITATIVE_SUPPORT_PACKET_CAPACITY.md`](../notes/CODEX_ADVERSARY__QUANTITATIVE_SUPPORT_PACKET_CAPACITY.md)  
**Verdict:** Theorem 1 and Corollaries 2--3 are mathematically correct, with
the stated constants, forward orientation, and unrestricted-deviation scope.
Section 4 contains one false general inference and needs a missing tail-value
bound.  Its counting corollary survives only for rows whose owner Continue
probability is separately **upper** bounded (in particular, if the displayed
"literal scale" is explicitly an equality), or whose second mover has a
fixed Quit floor.  The novelty claim must also be narrowed: the qualitative
fixed-error capacity theorem and the same strategic constant calculation
already occur in the author's earlier two-root-switch note; the new content
is the prescribed-cover `2m` wrapper and its explicit coordinate-bound
corollary.

No Lean or export file was modified.

## 1. Claim checked and sources inspected

The central claim is that, under a terminal exploitability gap `gamma`, a
support-`delta`, punishment-rational, exact forward Bellman packet in a fixed
carrier cannot have charge `2m` when `m` supplied balls of radius `delta/3`
cover the carrier and

\[
 12\delta+2(2+7B)\sqrt\delta<\gamma.                    \tag{1.1}
\]

I checked the following declarations and their exact orientations.

* `exists_same_label_with_large_charge_gap` and
  `exists_close_pair_with_large_charge_gap_of_finite_labels` in
  `MathUE/FiniteChargedReturn.lean`.
* `exists_charge_threshold_for_close_pair_of_compact` in
  `MathUE/CompactFiniteChargedReturn.lean`.
* `QuittingFiniteForwardPacket` and the full proof of
  `exists_singleSeamProjectiveLasso_of_finiteForwardPackets` in
  `UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`.
* `quittingFiniteSingleSeamProjectiveLasso_of_reversedForwardBlock` in
  `UniformEquilibrium/Quitting/Projective/ForwardBlockSingleSeam.lean`.
* `QuittingFiniteSingleSeamProjectiveLasso.exists_supportRationalDivergentPath`
  in `UniformEquilibrium/Quitting/Projective/SingleSeamProjectiveLasso.lean`.
* `exists_isεAsymptoticNash_of_divergentAbsorption_supportRationalPath` in
  `UniformEquilibrium/Quitting/Paths/SupportWitnessPathCompiler.lean`.
* `HasTerminalExploitabilityGap` in
  `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean` and
  `QuittingTerminalExploitabilityWitness.terminalExploitability` in
  `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityWitness.lean`.
* `quittingRewardBound` in
  `UniformEquilibrium/Quitting/RewardBound.lean` and
  `terminalExploitabilityGap_le_two_mul_bound` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/NormalTerminalGapConstrainedStationary.lean`.
* `FinFourQuantitativeFullSupportHardResidual.exists_terminalGap_collision_at_singleton`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PunishmentNormalAtomicCollisionHandoff.lean`.

For novelty I also compared Sections 5 and 7 of
[`CODEX_ADVERSARY__TWO_ROOT_SWITCH_FORWARD_PACKET_BARRIER.md`](../notes/CODEX_ADVERSARY__TWO_ROOT_SWITCH_FORWARD_PACKET_BARRIER.md).

## 2. Theorem 1: the constants and orientation are correct

Let `q_u` denote joint one-stage absorption.  It lies in `[0,1]`.  Labelling
each state by one of the supplied `m` centres and assuming
`sum q_u >= 2m`, the checked finite-label theorem gives ordered `s<t` with

\[
 \operatorname{dist}(U_s,U_t)<\delta,
 \qquad \sum_{u=s}^{t-1}q_u\ge1.                         \tag{2.1}
\]

The metric estimate is strict because two points in one closed
`delta/3` ball have distance at most `2delta/3<delta`.  The exact numerical
threshold is indeed `2m`.

One citation should be corrected: for an **arbitrarily prescribed** cover
`F`, the direct checked input is
`exists_close_pair_with_large_charge_gap_of_finite_labels`.  The compact
theorem chooses its own cover internally and therefore does not, as stated,
return the particular threshold associated with the user's `F`.  This is a
citation/formalization correction, not a mathematical gap.  Also, once the
finite cover is supplied, compactness is no longer used; compactness is only
the producer of such a cover.

The product estimate gives

\[
 W:=1-\prod_{u=s}^{t-1}(1-q_u)\ge\frac12.               \tag{2.2}
\]

The packet policy has the forward orientation

\[
 U_{u+1}=F_{p_u}(U_u).
\]

This is exactly the hypothesis expected by the checked reversed-forward
adapter.  Reading the block backward makes all nonclosing Bellman equations
exact.  With support error `delta` and coordinate seam error at most `delta`,
the lasso error is

\[
 e=\delta+\delta=2\delta,                                \tag{2.3}
\]

and the seam ratio is valid because

\[
 \delta\le(2\delta)W.
\]

The packet floor `P-delta<=U` is stronger than the lasso floor
`P-2delta<=U`.  Hence no hidden floor loss occurs.

The lasso-to-path theorem doubles both errors, giving path support and
rationality errors `4delta`.  Substitution into the checked path compiler is

\[
 2(4\delta)+4\delta+\sqrt{4\delta}(2+7B)
 =12\delta+2(2+7B)\sqrt\delta.                           \tag{2.4}
\]

Thus the note's `C=2+7B`, equation (2.7), and quadratic threshold

\[
 \delta_*=
 \frac{(\sqrt{C^2+12\gamma}-C)^2}{144}
\]

are all correct.  The strict hypothesis `delta<delta_*` is needed and is
present.

Finally, the output profile is an `IsεAsymptoticNash` profile quantified over
every behavioral strategy of the deviating player.  `HasTerminalExploitabilityGap`
quantifies over the same unrestricted behavioral deviations.  Applying both
inequalities to the same profile gives `gamma<=` (2.4).  There is no
bounded-controller or stationary-deviation gap here.

The coordinate estimate

\[
 B\le |I|(2^{|I|}-1)M
\]

is also correct from the definition of `quittingRewardBound` as the sum of
all absolute reward coordinates.  Positivity of the terminal gap forces
`M>0` in the stated Fin4 use, so the simplified threshold has no denominator
sign issue.

## 3. A sharper two-tolerance form

Theorem 1 is correct but not the strongest compact-capacity statement.  It
unnecessarily uses the support tolerance itself as the return radius.  Let
`delta>0` be support error and let `eta>0` be a separate seam tolerance.  If

\[
 \eta\le\delta                                           \tag{3.1}
\]

and `m_eta` balls of radius `eta/3` cover the carrier, charge `2m_eta`
produces a block with seam at most `eta` and weighted absorption at least
one half.  The lasso error is now

\[
 e=\delta+\eta,                                         \tag{3.2}
\]

and (3.1) is exactly what makes

\[
 \eta\le(\delta+\eta)/2\le(\delta+\eta)W
\]

hold.  The terminal contradiction condition becomes

\[
 6(\delta+\eta)+C\sqrt{2(\delta+\eta)}<\gamma.          \tag{3.3}

\]

This gives the stronger qualitative fixed-support threshold

\[
 \boxed{
 \delta<\delta_{\rm sharp}:=
 \frac{(\sqrt{C^2+12\gamma}-C)^2}{72}.}                 \tag{3.4}
\]

Indeed, the right side is the exact one-lasso lower bound; if
`delta<delta_sharp`, choose a positive `eta` smaller than both `delta` and
`delta_sharp-delta`, and then take a finite `eta/3` cover.  The cost of the
larger admissible support range is a possibly larger covering number.  The
note's `delta_*` is `delta_sharp/2`, the convenient threshold obtained by
fixing `eta=delta`.

Recommended standalone statements are therefore:

1. the generic lasso exclusion
   `gamma <= 6e + C*sqrt(2e)`;
2. the two-tolerance prescribed-cover wrapper (3.1)--(3.3); and
3. the note's one-tolerance `2m` theorem as a clean corollary.

## 4. Mandatory correction: the Fin4 absorption inference is false

For the two-active row, with `a`'s Quit probability `1-epsilon`, `k`'s Quit
probability `t`, collision increment at least `gamma`, and
`|r_k({k})|,|U_k|<=M`, one has

\[
 D_k\ge\gamma-\epsilon(\gamma+2M).                      \tag{4.1}
\]

Since `k` Continues with positive probability, support-`delta` Nash gives
`D_k<=delta`, and hence

\[
 \epsilon\ge\frac{\gamma-\delta}{\gamma+2M}.           \tag{4.2}

\]

The inequality direction matters: (4.2) is a **lower** bound on the owner's
Continue probability and therefore an **upper**, not lower, bound on the
owner's Quit probability `1-epsilon`.  It does not imply stage absorption at
least one half.

Here is an exact rational counterexample to that inference.  Take
`M=gamma=1`,

\[
 \epsilon=\frac{99}{100},\qquad t=\frac1{1000},
\]

and, in player `k`'s coordinate, set

\[
 r_k(\{a,k\})=1,
 \quad r_k(\{a\})=r_k(\{k\})=0,
 \quad U_k=\frac1{99}.
\]

Set the other relevant reward and tail coordinates to zero.  Then

\[
 D_k=\frac1{100}\cdot1+\frac{99}{100}
       \left(0-\frac1{99}\right)=0,
\]

so both supported actions of `k` satisfy even zero-error support Nash; the
other coordinates can likewise be exact.  The collision gap is one and the
tail is in the unit reward box.  Nevertheless the joint absorption is

\[
 1-\frac{99}{100}\frac{999}{1000}
 =\frac{1099}{100000}<\frac12.                           \tag{4.3}

\]

Thus the sentence "Hence every such row has stage absorption at least one
half" is false, and the first formulation of Corollary 4 is false if
"literal scale" means merely satisfying the forced lower bound (4.2).

There are three valid repairs.

* If the construction **chooses equality**
  `epsilon=(gamma-delta)/(gamma+2M)`, say so explicitly.  Then
  `1-epsilon=(2M+delta)/(gamma+2M)>=1/2`, and the `<4m` count is correct.
* More generally, add the independent hypothesis
  `epsilon<=barEpsilon<1`.  The note's bound
  `number < 2m/(1-barEpsilon)` is correct.
* Or add a fixed Quit floor `t>=tau>0`; joint absorption is then at least
  `tau`, independently of the owner coordinate.  The canonical descreened
  row has `t=1/2`, so its charge is at least one half even though it lies
  outside the small-support-error regime.

Equation (4.3) of the author note also needs the hypothesis
`|U_k|<=M`.  A coordinatewise bound on the **terminal reward table alone**
does not bound an arbitrary payoff carrier `K`; an all-Continue Bellman step
can preserve an arbitrarily large value.  For the intended source-generated
terminal payoff this bound is available, but the corollary must state either
`K subset [-M,M]^I` or the needed switch-date tail bound explicitly.

The final descreening observation is otherwise correct: with
`epsilon=gamma/(8M)` and `t=1/2`, the checked/derived endpoint difference is
at least `gamma/2`, and because both actions of `k` have positive support,
support-local error must be at least `gamma/2`.  The probability-weighted
root defect `gamma/4` is not the packet tolerance.

## 5. Novelty assessment and export recommendation

The note should not claim that the qualitative fixed-error capacity theorem
is new within the conference record.  Proposition 7.1 of
`CODEX_ADVERSARY__TWO_ROOT_SWITCH_FORWARD_PACKET_BARRIER.md` already states
the same compact-carrier result, the same threshold, and the same
`12delta+2C sqrt(delta)` proof.  Proposition 5.1 there also contains the
generic lasso calculation `gamma<=6e+C sqrt(2e)`.

Relative to checked Lean, there is still a useful declaration gap: the proof
of `exists_singleSeamProjectiveLasso_of_finiteForwardPackets` contains the
finite-return mechanism but exposes only an all-errors/all-targets producer
theorem, not a one-packet, prescribed-cover exclusion.  The genuinely useful
new packet is therefore:

* a public terminal-gap exclusion for one single-seam lasso;
* a public single-forward-packet-to-lasso wrapper with a supplied finite
  cover and exact `2m` target; and preferably
* the two-tolerance strengthening in Section 3 above.

After correcting Section 4 and narrowing novelty, Theorem 1 is suitable as a
quantitative export packet.  Corollary 4 should not be exported in its current
wording.  Corollary 3 is a direct specialization of the already checked
all-errors/all-targets packet compiler and should be labelled consolidation,
not a new theorem.

## 6. Concise disposition

| Item | Result |
|---|---|
| Prescribed-cover threshold `2m` | Correct; cite the finite-label theorem directly |
| Raw-to-weighted charge `1 -> 1/2` | Correct |
| Forward Bellman orientation and reversal | Correct |
| Lasso error `2delta`, path errors `4delta` | Correct |
| Terminal error `12delta+2C sqrt(delta)` | Correct |
| Unrestricted behavioral exploitability contradiction | Correct |
| Coordinate reward-bound estimate | Correct |
| Fixed-error threshold | Correct but sharpenable by separating seam tolerance |
| Support lower bound on `epsilon` implies charge floor | **False** |
| Fin4 `<4m` count | Valid only with explicit equality/upper-bound/`t`-floor hypothesis |
| Claimed novelty | Overstated relative to the earlier two-root-switch note |
