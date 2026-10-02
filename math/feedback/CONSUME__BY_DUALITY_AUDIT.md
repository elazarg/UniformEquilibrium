# Adversarial audit of `meta/CONSUME.md`

## Status

The note contains two sound and useful cores:

1. exact actual-profile data are set-theoretically sufficient for every unilateral behavioral response, but the unrestricted cap is discontinuous in the natural compact profile topology; and
2. on a genuinely chronological compact edge space, invariant occupation measures, positive-mean-charge recurrence, and the standard ergodic-optimization duality behave as claimed.

The present text nevertheless overstates both cores. The exact cap lower bound does not generally yield an attained deviation at the same numerical margin; the graph of the complete counterfactual tensor is not itself a compact actual-state space; the two proposed responses to discontinuity are not exhaustive; and the constrained separator is not an unconditional Lyapunov exit unless its displacement term is controlled along the paths under consideration.

These are repairable statement issues. They do not invalidate the spectator-table discontinuity example or the occupation-measure theorem.

## Claim audited

I audited Sections 1--3 and 7, together with the positive-charge occupation result from Section 6 that Section 7 uses. The relevant claims are:

- positive global minimum debt makes the proposed counterexample output circular;
- a compact state of complete actual profiles plus counterfactual data is compositionally sufficient;
- actuality, compactness, finite-coordinate continuity, and cap continuity cannot coexist as asserted;
- invariant-flow optimization has the displayed additive-potential dual; and
- infeasibility of a zero-displacement invariant flow produces a strict separator.

## Sources inspected

- `quittingContinuationBestResponseValue` and `quittingTerminalPayoff_update_le_continuationBestResponseValue` in `UniformEquilibrium/Quitting/Root/FirstBranch.lean`;
- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `quittingTerminalSemanticPair`, `quittingTerminalSemanticDebt`, and `quittingTerminalPayoff_update_sub_le_terminalSemanticDebt` in `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`; and
- `HasTerminalExploitabilityGap` and `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap` in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.

## 1. The circularity observation is correct, but the exact gap is overstated

For every actual profile,

\[
  \max_i d_i(\sigma)\ge \frac14\sum_i d_i(\sigma)
  \ge \frac{D_*}{4}.
\]

Thus, if the question already assumes a fixed table with positive global minimum debt, allowing the counterexample output to return that same table with a cap-based positive lower bound is circular. This criticism is correct.

There is one numerical distinction that the note must preserve. The cap is defined as a supremum over behavioral deviations. A debt lower bound

\[
  d_i(\sigma)\ge D_*/4
\]

does not imply that one actual deviation attains gain at least exactly \(D_*/4\). Best-response attainment is not available for an arbitrary nonstationary opponent profile. It does imply an actual terminal-exploitability witness at every strictly smaller margin, for example \(D_*/8\), by approximation to the supremum.

Therefore:

- \(D_*/4\) is a valid lower bound on the cap-defined exploitability;
- any fixed \(0<\gamma<D_*/4\) is a valid actual-deviation gap; but
- the sentence identifying \(\gamma=D_*/4\) with the exact negative semantic interface is unjustified without an attainment theorem.

There is also a logical distinction between a conditional counterexample and an independently certified one. Under a premise asserting \(D_*>0\), the input table is already a counterexample in the ordinary existential sense. It is not an independently checkable counterexample certificate that can discharge the premise. The note's proposed noncircular interpretation is appropriate for the latter goal, but it should be presented as a strengthened deliverable, not as the only possible meaning of “counterexample.”

## 2. What the complete actual profile does and does not provide

The profile space

\[
  \Sigma=([0,1]^4)^{\mathbb N}
\]

with the displayed product metric is compact. In the project's quitting-game semantics, one player's live behavioral strategy induces a stopping law on \(\mathbb N\cup\{\infty\}\), and the checked stopping-law theorem proves that its payoff is the expectation of the pure-time/Never payoffs. The checked extremality theorem then proves the cap formula as a supremum over pure times and Never. Equations (4)--(5) are therefore valid.

The order-four counterfactual tensor is also set-theoretically sufficient for simultaneous independent behavioral replacements, provided the standard private independent randomization convention is stated. Equation (7) is then the product-mixture expansion of the pure-time counterfactual laws. The raw profile remains necessary for literal off-path suffix operations, as the note says.

The compactness claim needs to be split into three different objects:

1. \(\Sigma\) is a compact space of actual profiles and determines all strategic observables set-theoretically.
2. The ambient product in (2) is compact if every annotation coordinate is assigned a specified compact topology and \(\overline{\mathbb N}\) carries its one-point compactification topology.
3. The subset on which the stored law/cap/counterfactual coordinates equal the actual values generated by the stored profiles need not be closed. In fact Section 3's own example shows that the graph of the cap is not closed.

Consequently, the phrase “compositionally complete compact source state” is accurate only if “state” means the bare actual profiles, with semantics treated as discontinuous derived functions. It is false if it means the graph

\[
  \{(x,\mathcal K_4(x),U(x),B(x),\ldots):x\in\Sigma\}
\]

with the product topology. Merely embedding that graph in a compact raw ambient product introduces inconsistent or nonactual packets.

The same warning applies to the conclusion's claim that the “entire actual source packet, with ... counterfactual tensor” is an explicit compact state. Either omit the derived tensor from the topological state, prove the relevant graph closed, or call the compact object an ambient compactification rather than a compact actual-packet space.

## 3. The discontinuity example is valid; the trilemma needs a precise scope

For the spectator table in (11), the delayed sure-quit profiles converge coordinatewise to all Continue, while every delayed profile gives each player cap one and all Continue gives cap zero. The calculation is correct and it directly witnesses cap discontinuity.

A precise topological statement is:

> There is no compact topology on the set of actual profiles for which every finite hazard coordinate and every actual unrestricted cap are continuous.

Indeed, compactness gives a convergent subnet of the delayed profiles; continuity of all finite coordinates forces its limit to be the all-Continue profile, while cap continuity gives cap one there.

This formulation also covers compact topologies finer than the displayed product topology. It should state that states are identified by their actual finite hazard coordinates and that the cap coordinate is required to equal the actual cap.

The subsequent “two honest choices” are two important choices, not an exhaustive dichotomy. Other honest architectures include:

- a noncompact topology in which more strategic observables are continuous;
- a two-layer actual/escape state with an explicitly nonactual semantic boundary;
- upper or lower semicontinuous envelopes rather than a continuous graph; and
- compact actual profiles with measurable, rather than continuous, strategic observables.

The real no-go is the simultaneous compactness/actuality/continuity demand, not a classification of all possible repairs.

## 4. Positive-charge occupation recurrence is correct under explicit hypotheses

The invariant-occupation existence proof is standard and correct for a nonempty compact metric edge space with continuous source and target maps and seriality. The positive-charge recurrence theorem is also correct under the following exact assumptions:

- the edge and state spaces are standard Borel (compact metric suffices);
- the invariant occupation is supported on literal composable chronological edges;
- \(q\) is Borel, bounded, nonnegative, and has positive mean; and
- the semantic observation is Borel into a compact metric space.

Disintegration yields a stationary path measure, an ergodic positive-mean component exists, and recurrence plus Birkhoff gives arbitrarily highly charged finite segments whose two endpoints approach one fixed observed target.

This consumes a component only when **some invariant occupation has positive mean charge**. The existence of positive-charge edges somewhere in a component is insufficient: all invariant occupations may avoid them. The phrases “positive-charge component” and “all positive-charge components are consumed” should be replaced by this invariant-measure condition.

Likewise, the near-return can be passed to an existing compiler only if the edge's charge and the chosen observation contain every admissibility, punishment, law, and seam field required by that compiler. The abstract occupation theorem supplies recurrence, not those game-theoretic fields.

## 5. The unconstrained duality is sound

Under the compactness and continuity hypotheses, equation (35) is the standard ergodic-optimization linear-programming duality:

\[
 \max_{\pi:s_\#\pi=t_\#\pi}\int q\,d\pi
 =
 \inf_{f\in C(C)}\max_{e\in\mathcal E_C}
 \bigl(q(e)+f(t(e))-f(s(e))\bigr).
\]

One may justify the minimax exchange by Sion's theorem, using compactness of \(\mathcal P(\mathcal E_C)\). For a noninvariant measure, continuous functions separate its source and target marginals, and scaling the separating function sends the inner infimum to \(-\infty\). For an invariant measure the coboundary integrates to zero. Seriality from the preceding section guarantees that the invariant feasible set is nonempty, and compactness makes the maximum attained.

## 6. The constrained duality is sound, but “Lyapunov exit” is conditional

Equation (36) is valid when the constrained invariant set is nonempty. If it is empty, the left side needs an extended-real convention rather than the notation “max”; the dual infimum is then \(-\infty\).

The strict-separation claim is valid. Consider the compact convex image

\[
  \left\{
  (t_\#\mu-s_\#\mu,\int\Delta\,d\mu):
  \mu\in\mathcal P(\mathcal E_C)
  \right\}.
\]

If it omits zero, strong separation in the weak-star measure space times \(\mathbb R^m\) gives \(f\in C(C)\), \(\lambda\in\mathbb R^m\), and \(\eta>0\). Testing the resulting integral inequality on Dirac measures yields (37) pointwise on every edge.

However, (37) is an augmented separator, not by itself a strict Lyapunov function on the source states. Along a finite path it gives

\[
  f(x_N)-f(x_0)
  +\lambda\cdot\sum_{n<N}\Delta(e_n)
  \ge N\eta.
\]

To force exit from a compact component one still needs the cumulative displacement term to be bounded, telescoping, or otherwise controlled. If \(\Delta\) is a coboundary, its zero-mean constraint is automatic for every invariant measure, as the note already observes. If it is not a coboundary, the \(\lambda\cdot\Delta\) term may finance the inequality indefinitely.

Therefore “infeasibility gives a strict Lyapunov exit” should be weakened to:

> infeasibility gives a strict augmented separation certificate; it gives a chronological exit once the selected displacement has a proved bounded-cumulative or telescoping realization along legal paths.

## Verdict

The manuscript's main negative diagnosis survives: a compact untyped relation of arbitrary legal source transformations does not represent chronological recurrence, and compact actual profiles do not make unrestricted terminal semantics continuous.

The occupation/duality mathematics also survives and is worth retaining. Its proper scope is a compact closed space of already source-matched chronological edges. It cannot manufacture that edge space, its admissible charge, or the displacement control needed to interpret a separator as an exit.

The file should be revised before being treated as a clean meta-level reference. The most important corrections are:

1. replace the exact actual gap \(D_*/4\) by any fixed smaller gap unless attainment is supplied;
2. distinguish compact actual profiles from the generally noncompact graph of their semantic/counterfactual annotations;
3. make the discontinuity alternatives nonexhaustive; and
4. distinguish an augmented constrained separator from an unconditional Lyapunov exit.

No Lean-checked status is asserted for the occupation or separation theorems.
