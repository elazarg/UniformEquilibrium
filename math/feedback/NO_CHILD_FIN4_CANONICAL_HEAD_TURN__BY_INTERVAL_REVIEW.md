# Independent whole review: canonical-tail amplitude after Nash head repair

Verdict: PASS for the exact internal obstruction stated in the proof. No
unresolved mathematical objection. This is not a source-mode exclusion or
a counterexample to UE.

Reviewed proof: the section “Canonical-tail amplitude can have an interior minimum after repairing a head” retained verbatim in [the benchmark](../notes/CODEX_COORDINATOR__NO_CHILD_FIN4_BENCHMARK.md). The reviewed section source has SHA256
`fe0ebc11b397565589e770f7a3fe0d42c150ac5ded5bd5aae336f7490edaefce`.
Reviewed and independently rerun single checker:
`math/experiments/CODEX_NO_CHILD__CANONICAL_HEAD_TURN_CHECK.py`, SHA256
`ed70985e4cdca7b2fe3e51d2ff1433830786a546cc109b2bd7366786b405ea2d`.

## Claim and actual-tail production

The claim is existence of a continuous family of actual M14 full native Nash
profiles, each with 41 full-support roots and a canonical infinite tail.
Its Never probability has an interior minimum along this family, while
every entrance cap lies above the stated positive vector and admits no
nonempty Nash prefix. Neither local optimality against all head variations
nor global optimality over the source carrier is asserted.

I checked the complete analytic producer. The positive algebraic eigenvector,
rational root bracket, coefficient majorants for the exact contact polynomial,
and both matrix norms give an invariant radius4 quadratic ball and contraction
constant below .732. The real fixed point has positive summable hazards.
The payoff and survival error bounds follow from the displayed polynomial
majorants and geometric series. These bounds apply uniformly to the tiny
positive seed interval used in the computation; no supplied continuation
strategy or numerical approximation is substituted for the actual tail.

The contact recurrence prices every deadline and Never equally. Arbitrary
private behavioral deviations are mixtures of those first-Quit responses.
The clocks are independent, and finite Nash prefixing preserves the exact
full-response property. The root maximum corresponds to
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`; literal prefix
semantics correspond to `quittingTerminalSemanticPair_rootThenContinuation`
in `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`. These were
inspected as semantic interfaces; no Lean build or new formalization seal is
claimed.

## Interval existence, transport and gluing

Floating arithmetic only nominates rational centers and preconditioners.
Every existence, inclusion, contraction and comparison assertion uses exact
Fractions with outward dyadic rounding. I checked the arithmetic operations,
the exact odds contact Jacobian, and the forced-Quit Jacobian including its
zero diagonal.

For each input cap box the verified Newton map is a strict self-map of its
positive root box and a contraction. The derivative estimate therefore proves
existence and uniqueness, rather than merely a small residual. The bound
`||I-B DC||<1` also makes both DC and the fixed preconditioner B invertible.
The Neumann column bound encloses DC inverse correctly. Enlarging the input
cap box to contain C(x0) makes the mean-value transport of Q through
Q' DC inverse valid on the entire connecting segment. Direct products bound
the associated survival probability.

The ten closed parameter tiles cover the complete interval. At each depth,
the common convex hull of all root boxes passes the same derivative
contraction test. This makes C injective on that hull: integrate its Jacobian
on the segment between any two proposed roots and apply the norm bound.
Consequently neighboring tile constructions agree at their common boundary,
inductively through all 41 roots. The resulting actual Nash family is
continuous on the whole compact interval.

The final single checker passed all local coefficient checks, all three
rational survival comparisons, all ten parameter tiles, and all 41 common
hull checks. The middle survival upper bound is strictly below both endpoint
lower bounds. Compactness therefore gives an interior family minimum.

## Prefix obstruction and limitations

I separately recomputed positivity of L inverse and the exact inequalities
`L inverse b0>(37/1000)1` and `L inverse 1>(12/25)1`. The checker verifies
entrance cap>b0 uniformly on every tile. Positive continuation forces a
nonempty proper Nash prefix to have full support; its minimum odds would
violate the displayed quadratic of negative discriminant. The proof now also
includes the complete sure-quitter contradiction, so its prefix conclusion
does cover all nonempty Nash roots.

This is a concrete M14 obstruction to universal monotone amplitude repair
and Nash-prefix grafting, with changing entrance caps. It does not establish
a minimum against other gap directions, a minimum over the semantic carrier,
a positive absorbing gap, or failure of original-game UE. Keeping it as one
internal appendix/checker is appropriate; no export admission as a new
counterexample-class exclusion is claimed.
