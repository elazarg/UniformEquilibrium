# A pivot-specific secant source and the cap-control boundary

Status: ordinary-mathematics source reduction under the hypothetical failure
of Fin4 UE; no new Lean declaration or terminal consumer is asserted.

## Exact question and quantities

Fix four players, independent private stopping laws on finite dates and
Never, and zero live/Never rewards. Freeze all terminal reward coordinates
except player 0's own-singleton reward. Let rˣ have own-singleton vector
(x,0,0,0), with x∈[0,1] and every reward entry bounded by one.

For an actual profile p, write Eₓ(p) for maximum unrestricted behavioral
regret, e(x)=infₚEₓ(p), and z(p) for the probability that the first quitting
coalition is {0}. Can a positive value somewhere on this one-coordinate
family force a source with pivot singleton mass and strictly negative
pivot reward pressure, without varying the other own-singletons?

## The full-cap secant

For 0≤y<x≤1, prescribed pivot payoff changes by (x−y)z(p). Every pivot
response changes by between zero and x−y, while all nonpivot payoffs and
caps are unchanged. Hence

    E_y(p)−(x−y)z(p) ≤ Eₓ(p) ≤ E_y(p)+(x−y)(1−z(p)).

In particular e is 1-Lipschitz. All Never gives e(0)=0. The positive
maximum-regret minimum singleton margin, together with B₀≤1, gives e(1)=0.
Single-pivot normalization, scaling, and reward continuity supply rational
frozen coordinates and a rational t∈(0,1) with e(t)>0 under no Fin4 UE.

Choose 2α<e(t), and use the last descending crossing of level α, followed
by maximization of e(x)+(α/4)x. The selected ξ<1 has
3α/4≤m=e(ξ)≤α and, for every actual profile,

    E_ξ(p)+(ξ−t)z(p)≥e(t)>2α.

Thus every sufficiently accurate near-minimizer has z(p)≥3α/4. The same
inequality passes to the joint semantic/law carrier. It is pivot-specific
and needs neither a fixed-date atom nor a screened-root reconstruction.

## The additional source data and their boundary

The tilted common-calendar selection supplies actual finite near-minimizers
at the one fixed table r^ξ, with almost-active tester weights, vanishing
enlarged-domain directional error, and strictly negative pivot pressure

    P₀ = ∑[pivot testers u] λ₀ᵤ(zᵤ−z).

Here zᵤ is the pivot singleton probability under the deterministic response
u, with Never kept as a separate response. The pressure uses the weights
of the selected profile, not weights from another minimizing sequence.

Its extracted finite reply T is almost cap-attaining, gains at least m−ε,
and lowers pivot singleton probability by at least α/16. If T₀ is the old
pivot clock and O is the first opponent clock, then

    Pr(T₀<O≤T)≥α/16.

The legal private replacement max(T₀,T) loses at most ε of pivot payoff,
retains the same pivot cap, and removes at least α/16 of singleton mass.
The event's reward contribution need not be favorable. Other players'
whole-profile caps can increase.

This source retains three zero own-singletons. It does not additionally
retain full four-coordinate fiber maximality, nonpositive total owner
pressure, or membership-stretch ancestry. Optional generic frozen rewards
are compatible, but genericity is not used in the secant collar.

The unresolved mathematical step is a repair or consumer that controls the
other three caps while retaining useful singleton-mass loss. A fixed loss
in a bounded probability is not a renewable rank without such a theorem.

## Named tracked dependencies inspected

- `exists_finFour_no_uniformPayoff_iff_exists_singlePivot`
  (`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`).
- `abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close`
  (`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`).
- `minimumTerminalSemantic_exploitabilitySingletonMargin`
  (`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`).
- `escapeAwareQuantileClock_fin4_normalized_quantitative_bracket`,
  `exists_finiteClockSemanticPair_exploitability_eq_upper`, and
  `quantileClockSupport_fin4`
  (`Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`).

These give the entrance, minimum margin, and uniform actual finite-clock
approximation. The one-coordinate tilt and same-profile strict-pressure
extraction are additional ordinary mathematics, not supplied by those
declarations alone.
