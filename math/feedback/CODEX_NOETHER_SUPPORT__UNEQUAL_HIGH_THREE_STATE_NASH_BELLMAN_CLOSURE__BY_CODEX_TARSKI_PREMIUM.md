# Independent review: unequal-high three-state Nash–Bellman closure

Reviewer: CODEX_TARSKI_PREMIUM.

Verdict: **mathematical PASS**, including actual full terminal Nash, Never,
fixed uniform payoffs, and the exact censored finite-law caps. No unresolved
mathematical objection. The construction produces all strategic data from
the displayed rational table. It is not a supplied-certificate implication.

Importance verdict: affirmative but narrow. This is a legitimate produced
raw-table leaf resolving the named unequal-high survivor of the matching
tests. It merits at most a small data-certificate formalization reusing the
existing period-three/periodic consumers. It is NOT new overlapping-cycle
machinery, not a new general numerical theorem, and not a solution of the
twelve-parameter collision box. I do not endorse a blanket noncoverage
claim about every known existence class or a duplicate generic compiler.

No other independent review or its conclusions was consulted before this
verdict. The complete 309-line manuscript and 168-line certificate were
read. Frozen inputs checked:

- [Manuscript](../notes/CODEX_NOETHER_SUPPORT__UNEQUAL_HIGH_THREE_STATE_NASH_BELLMAN_CLOSURE.md),
  SHA256 `1ae929df8073aa37ca383c7bdcb8dec4c29809fa61627444af7f2842f83657af`.
- [Certificate](../experiments/CODEX_NOETHER_SUPPORT__UNEQUAL_HIGH_THREE_STATE_CERTIFICATE.py),
  SHA256 `3579aaf338c399781297c54cb8967606361a7d398bfae14a42129c8557222fe0`.
- The imported arithmetic file `Experiments/certsearch/krawczyk_cycle_certifier.py`,
  at review SHA256 `1dcd5a4e9305254334d5bab0cd2b01e80fd5ee42a0eff16a4ba520b5f9633459`.
  I inspected the complete `Ival` arithmetic and exact inverse routine used
  here. Its experiment main is not invoked.

## 1. Exact arithmetic and independent falsification

The stated reproduction command passed, without modifying files. In
particular it certified the inverse, Newton correction, entire-cube
derivative bound, all three quiet inequalities, all twelve deleted-survival
bounds, and all twelve payoff bounds. Decimal diagnostics matched the note;
none was used as a proof assertion.

The interval implementation is sound for the operations used: exact
rational addition/subtraction, four-endpoint multiplication, reciprocal
away from zero, and point extraction only from degenerate intervals.
`fraction_matrix_inverse` performs exact Gaussian elimination and checks
the left inverse product against the identity entry by entry. In finite
square dimension this establishes invertibility; no numerical rank test is
substituted. Every Jet derivative is propagated by the correct product
rule, without derivative-list mutation or a divided interval variable.

I separately reconstructed the raw scalar evaluator using Boolean tuples
and an independently entered reward dictionary, rather than the author's
mask-probability/Jet evaluator. Exact rational checks gave:

- agreement of all twelve cleared gaps, all twelve value numerators, the
  absorption denominator, and all twelve deleted survivals at the center;
- agreement of all 81 active Jacobian entries, using exact symmetric
  differences with step 1/97;
- all 36 payoff-censoring telescope identities for T=1,…,9 and four owners.

The derivative check is exact, not a small-step numerical heuristic:
each cleared equation has degree at most two in each individual hazard.
The central symmetric difference therefore equals the corresponding
partial derivative for every nonzero step. The steps need not remain legal
hazards for this polynomial identity. These independent checks supplement,
not replace, the author's whole-box rational interval proof.

The nine free coordinates are in precisely the stated chronological order
023|012|013. The deleted-owner enumeration includes all eight opponent
coalitions, including the empty one. Quiet owners 1,3,2 respectively face
all three active opponents, so their Quit endpoints include the negative
grand-coalition reward. That term has not been silently removed because
the prescribed profile never reaches the grand coalition.

## 2. The certificate actually produces a legal root

Write c_t for joint Continue probability, D=1−c₀c₁c₂, and W_t for the
three-date reward window. The geometric series gives V_t=W_t/D, with
the displayed cyclic indexing. The endpoint residual

    F_ti=D(Q_ti−H_ti)−d_ti W_(t+1),i

is exactly D times Quit minus Continue at the ACTUAL next value. The nine
active equations correspond one-for-one with the nine positive prescribed
hazards. The remaining three inequalities are the full quiet-player
incentives. All rates are below one, and D is bounded away from zero.

For B=DF(x₀)⁻¹, the map T(x)=x−BF(x) has infinity-norm derivative below
1/100 throughout the convex rational cube. Its displacement from x₀ is
strictly less than ρ/50 on that cube. Consequently it is a self-map and a
strict contraction. The elementary Cauchy-iteration argument in the note
produces a fixed point, and invertibility of B makes it a zero of F.
Uniqueness is only asserted in that cube and follows from the same norm
bound. No global root count, seed-to-cycle path, or choice of maximal
absorption root is needed or proved.

This is the source-production step. The subsequent strategic proof does
not take a root, annotation, favorable continuation, or absorbing source
as an additional assumption. Their existence is the conclusion of this
finite rational calculation on the literal table.

## 3. Full infinite behavioral responses and Never

At the exact zero, each owner's Continue endpoint equals V_ti. For an
active owner, both actions tie because its hazard is strictly between
zero and one; for a quiet owner, prescribed Continue has value V_ti and
Quit is strictly worse. Thus for all twelve owner-phase pairs,

    V_ti=H_ti+d_ti V_(t+1),i,       Q_ti≤V_ti.       (A)

Fix i. Iterating (A) through any n dates gives an equality for the rewards
collected when its opponents stop before n, plus the residual opponent
survival times V_n,i. Substituting Q_n,i≤V_n,i bounds the response Quit n.
Every finite date is covered; reducing dates modulo three does not discard
the intervening survival factors.

For Never the same identity has residual bounded by
(3/2)(5/6)^n, which tends to zero. Thus Never's terminal payoff equals V_ti.
This is compatible with literal zero Never reward: under this unilateral
response, the OTHER THREE clocks still absorb almost surely. Joint Never
has probability zero. It would be wrong to replace this response value by
the terminal reward assigned when all four players never quit.

Any full behavioral deviation induces an independent planned stopping law
along the unique live history, with an arbitrary possible Never atom.
Mixing the pure-date/Never comparisons therefore bounds that deviation.
The proof neither observes opponents' future clocks nor correlates private
randomization. Hence the unrestricted cap is V, and actual prescribed
payoff V gives zero debt at every starting phase.

Opponent survival remains bounded by (5/6)^n under EVERY unilateral
deviation, since it is a property of the unchanged opponent marginals.
With reward bound 4, the terminal versus finite-average discrepancy is
uniformly controlled by the opponents' finite expected stopping time.
This proves a fixed uniform payoff with the same infinite periodic profile
at every accuracy. It also exactly matches the checked periodic consumer.

## 4. Independent censorship: all cap and debt identities pass

For the finite law, each player's atoms before T are retained, and all of
its remaining mass is assigned to its OWN Never atom. Independence is
preserved. Joint survival C_T and deleted survival are different quantities;
the note uses them in the appropriate places.

The Bellman payoff telescope gives

    U_i^T=V₀i−C_T V_(T mod 3),i.                    (B)

For a response Quit n<T, censorship of the opponent clocks beyond T cannot
affect its payoff. Its actual payoff is therefore the infinite-opponent
value, at most V₀i by (A).

For a response at ANY n≥T, after opponent survival through the head the
deviator is alone and gets singleton 1. Never instead gets zero on that
same event. Those are the literal censored continuation rewards, not an
absorption property imported from the infinite profile. Both are below
V_(T mod 3),i>1, so (A) propagated through the head bounds the full response
by V₀i. Mixtures again cover all behavioral deviations.

The opposite cap inequality uses an actual finite response: owners 0,2,3
Quit0, and owner 1 Continues at date zero then Quits1. The corresponding
active endpoint attains V₀i, because every prior Continue equality in (A)
is exact. All these responses precede the cutoff precisely when T≥2.
Consequently

    B_i^T=V₀i,       d_i^T=C_T V_(T mod 3),i.

Since every c_t≤d_ti<5/6, the reported bound follows. This does not confuse
joint absorption with player-deleted absorption. Equation (B) also proves
delivery to the SAME fixed target V₀. Censored profiles are generally not
exact menu Nash, which is not required by the conclusion.

Boundary audit: the T≥2 qualification is substantive. At T=1, owner 1's
first active date has been removed; its immediate Quit endpoint is strictly
below V₀1, and its after-cutoff and Never endpoints are also strictly below
V₀1 because d₀1>0 and V₁1>1. Thus B₁¹<V₀1. The theorem correctly avoids
extending its exact-cap formula to that boundary. T=0 is all Never and is
likewise not within the finite-cap assertion.

## 5. Narrow source/coverage and importance audit

I inspected the literal declarations
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate` in
`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.
Their inputs are exactly the policy recursion, phasewise full root Nash,
and opponent-cycle contraction proved above. Nothing extra is needed to
reach their actual terminal/uniform endpoints. The new work is supplying
the table-specific nine-variable zero, not replacing these consumers.

Nearest previously produced example/class:
`CODEX_SPINOZA__E1_OVERLAPPING_PERIOD_THREE_CLOSURE.md`, Sections 1–3 and 5,
and the current
`exists_periodThreeClearedGapData_and_uniformPayoff_of_visible_affine_reward`
in `UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreePositiveAffineCylinder.lean`.
I also inspected its `IsInvisibleRewardCoordinate` definition in
`FourPlayerOverlappingPeriodThreeInvisibleCoordinates.lean`.
These already supply overlapping three-phase polynomial clearing, an exact
rational certificate, generic semantic compilation, and an affine/invisible
coordinate class. They do NOT themselves produce this new zero.

The present table is outside that explicit affine cylinder, even allowing
player relabeling. All singleton coordinates are visible. In E1, a payoff
column has outsider singleton values 0,0,4. So does the corresponding column
here. Positive affine matching, even after a reward perturbation of size
ε=1/50000000, must map its high singleton to 4 and its low singleton to 0.
Writing their perturbed E1 entries as u₄,u₀ forces scale
a=4/(u₄−u₀)≥4/(4+2ε) and shift −a u₀. E1's reward 16 to player 2 on
coalition 13 is VISIBLE. Its image would exceed
4(16−2ε)/(4+2ε)>4, while every reward in the new table is at most 4.
Relabeling transports visibility as well as the same singleton argument;
it cannot hide this contradiction in a free coordinate.

Other bounded comparisons, without an all-classes claim:

- The current single common-c paired family and the independent matching
  section require equal designated active pair-member rewards. This table
  has unequal directed highs; neither cross matching has those equalities.
  The separate matching-failure note gives a stronger grammar obstruction,
  but this review does not rely on its entire proof to establish existence.
- The exact singleton matrix is the standard paired matrix. The checked
  `pairedSingletonMatrix_not_projectiveQBar` in
  `Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`
  excludes the full projective-Q-bar entrance on the cross principal.
  The table's singleton rewards are unchanged from that matrix calibration.
- The direct capped-member screen fails at coalition 01, and the produced
  V₀>(1,1,1,1) itself defeats every nonempty actual weak-subset payoff
  exclusion. Neither fact asserts failure of every possible matrix or
  stationary consumer. Stationary nonexistence is NOT proved here.

Thus the contribution is a new certified instance outside the specified
already-produced entrances, not a renamed E1 example. It has independent
value as a completed falsifier of treating these matching failures as a
positive unrestricted debt floor, and as an actual finite-law benchmark
with all data produced. This supports a NARROW raw-table data leaf under
the special-case clause of the export policy. It does not justify exporting
another generic supplied-cycle interface. If formalized, reuse
`PeriodThreeClearedGapData`/`PeriodicCompiler` and add only the exact reward,
nine-coordinate support/rational cube, verified contraction bounds, and
the resulting concrete profile/finite-cap theorem. A clean final packet
still needs its own final-byte gate and explicit handoff; this review is
not permission to alter the frozen source or an export.

No strategic input remains unproduced. There is no full-box selection,
component continuation, all-root absorption, period minimality, or claim of
generic numerical completeness. A routine implicit-function neighborhood
would be a possible consequence of the strict margins and nonsingular
Jacobian, but was not developed or used to inflate the present scope.
