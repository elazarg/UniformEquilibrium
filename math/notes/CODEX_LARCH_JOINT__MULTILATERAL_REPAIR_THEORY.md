# Common second-order repair of independent stopping laws

Identity: CODEX_LARCH_JOINT.

## Status and recommendation

**Theory candidate with an elementary proof sketch and an exact calibration.**
This is ordinary mathematics, not Lean-checked or exported. The proposed
addition is a common second-order correction test for the *whole* response
envelope. It connects individual mixed-response squares to one actual product
profile whose full exploitability decreases. Its optimization ingredients are
known; the possible useful contribution is their source-preserving assembly
and, eventually, a stopping-game condition producing the required direction.

No such arbitrary-table producer is obtained here. The small game below has
an obvious equilibrium. It calibrates a second-order phenomenon, not the
positive-global-minimum frontier. The candidate deserves a bounded test before
a library: determine whether a current minimum-source construction supplies a
nonzero critical direction and restricts the entire dual curvature family.

[Independent review](../feedback/CODEX_LARCH_JOINT__MULTILATERAL_REPAIR_THEORY__BY_CODEX_LARCH_DUAL.md)
checks the Taylor criterion, dual alternative, and exact game calibration.
Its face-restriction and general signed-payoff approximation qualifications
are incorporated below. No unresolved objection to those local statements
was reported; the arbitrary-source producer remains open.

The originally proposed first-order bridge is already substantially present:
[NOETHER's joint repair note](CODEX_NOETHER_SUPPORT__JOINT_OPPONENT_MOVE_AND_COMPLETE_REPAIR_VALUE.md)
contains an infinitesimal joint escape from the complete coordinate trap and
the all-optimal-primal/all-optimal-dual derivative of the outer repair value.
[RENY's recombination boundary](CODEX_RENY__SIMULTANEOUS_ACTIVE_RESPONSE_RECOMBINATION_BOUNDARY.md)
already keeps every tied response, including zero-multiplier responses.
Neither should be rediscovered as a new theory.

## 1. The question on actual finite data

There are finitely many players, a real reward vector for every nonempty
quitting coalition, and reward zero if everybody plays Never. Players sample
their stopping clocks independently; there is no public random corner label.
Fix a finite calendar A={0,...,N−1,Never}, N≥1, and its product of probability
simplexes X. A proposed calendar enlargement is made *before* what follows.

For p∈X let U_i(p) be the prescribed terminal payoff. Let V_i,t(p) be the
payoff when player i replaces its entire law by deterministic date t, and set

    g_i,t(p)=V_i,t(p)−U_i(p),
    E(p)=max_(i,t) g_i,t(p),       t∈{0,...,N,Never}.

This is the full exploitability, not just regret on the controller menu:
every later finite response is equivalent to N, Never is retained separately,
and a mixed response averages pure responses. Each g is multiaffine in the
marginal laws and hence an ordinary finite polynomial.

At a profile p with m=E(p)>0, can individually favorable response-square
information be assembled into one feasible curve p(ε) with E(p(ε))<m?
The precise issue is compatibility across *all* tied responses. A signed
alternating square alone is not a profile; its sign alone answers no such
question.

## 2. An exact game requiring second-order analysis on a fixed face

Take players {0,1,2,3}. For every nonempty coalition S define r_0(S)=1
and r_3(S)=0. For i∈{1,2}, with j the other member of {1,2}, define

    r_i(S)=0                              if 0∉S;
           −1                             if 0∈S and i∉S;
           0                              if 0,i∈S and j∉S;
           1                              if 0,i,j∈S.

Membership of player 3 changes nothing. This specifies the entire table,
has reward bound one, and has own-singleton vector (1,0,0,0).

Let player 0 quit surely at date zero and player 3 play Never. Players 1 and
2 independently quit at zero with probabilities a,b and otherwise Never.
Absorption occurs at zero with probability one. Direct conditioning gives

    U_1=−1+a+ab,       U_2=−1+b+ab,
    B_1=b,            B_2=a.

These are full caps. Player 1's Quit0 payoff is b; any positive finite
date or Never gives −1, since the pivot has already stopped. Mixtures do
not improve the cap. The argument for player 2 is identical. The pivot
gets one and no complete deviation exceeds one because every terminal
pivot reward is one and the no-absorption reward is zero. Player 3's payoff
and cap are both zero. Consequently, on the entire square,

    E(a,b)=max{(1−a)(1+b),(1−b)(1+a)}
          =1+|a−b|−ab.                                  (1)

At (0,0), changing just a or just b strictly increases E. For every feasible
first-order direction (h,k), h,k≥0, the directional derivative is |h−k|,
so no joint direction has a negative first-order derivative. Nevertheless

    E(s,s)=1−s² < 1                    for 0<s≤1.         (2)

Thus the failure of first-order descent need not mean local optimality,
even for a canonical quitting table with complete behavioral caps. The
diagonal is first-order flat and has favorable curvature for both tied
responses simultaneously.

Scope matters: this is a fixed face with the pivot held at Quit0. It is
not the stronger arbitrary-law coordinate-closure theorem in
[HILBERT's trap](CODEX_HILBERT__FULL_EXPLOITABILITY_COORDINATE_REPAIR_TRAP.md).
Neutral changes of the pivot are not classified here. At a=b=1 the displayed
profile is already exact terminal Nash, so the positive value at the origin
is certainly not a global minimum. The example is useful because its first
derivative really vanishes along the improving direction; the already known
joint escape from HILBERT's fixture has strictly negative first derivatives.

## 3. A common acceleration criterion

Write a for a complete response label and let

    I={a:g_a(p)=m},       L_a(v)=Dg_a(p)[v],
    Q_a(v)=½ D²g_a(p)[v,v].

The following finite statement is the proposed common interface. Fix v with

    Σ_t v_i,t=0;
    v_i,t≥0 wherever p_i,t=0;
    L_a(v)≤0 for every a∈I.

Let Z={a∈I:L_a(v)=0}. If Z is empty, ordinary first-order descent already
works. Otherwise allow an acceleration w satisfying

    Σ_t w_i,t=0;
    w_i,t≥0 wherever p_i,t=0 AND v_i,t=0.                 (3)

There is no sign restriction on w at a zero source atom with v_i,t>0:
the positive εv term dominates ε²w for small positive ε. These conditions
make p(ε)=p+εv+ε²w a literal product of probability laws for all sufficiently
small ε>0.

**Sufficient criterion.** If there are w satisfying (3) and c>0 such that

    L_a(w)+Q_a(v)≤−c             for every a∈Z,          (4)

then E(p(ε))≤m−(c/2)ε² for all sufficiently small positive ε.

Proof sketch: finite Taylor expansion gives

    g_a(p(ε))=g_a(p)+εL_a(v)
                    +ε²[L_a(w)+Q_a(v)]+O(ε³).

The remainder is uniform over the finite tester set. Inactive tests have
a strictly positive source gap; active tests outside Z have a strictly
negative first-order coefficient. Both groups remain below the claimed
bound for small enough ε. Equation (4) controls the remaining group.
No derivative of the maximum and no assumed constancy of one best response
is needed.

At the calibration (1), v=(1,1), w=0, both active L_a(v) vanish and both
Q_a(v)=−1. All newly possible late responses were included and are inactive.

One acceleration can be essential even when some Q_a(v) is positive:
linear redistribution at order ε² may repair that tester while retaining
the negative margin for the others. Requiring each raw Q_a(v)<0 would
throw away this flexibility.

A coefficient-level check is L_1(w)=w, L_2(w)=−w, Q_1=1, Q_2=−3 on
the free acceleration line. Taking w=−2 makes both corrected coefficients
equal −1; requiring both raw Q entries negative would reject it. This is
an abstract LP check, not an asserted stopping-game realization.

## 4. The exact dual asks for compatible curvature

Let W_v be the polyhedral cone of accelerations (3). For fixed v, deciding
whether (4) holds is a finite LP, not a nonconvex search over w. Define

    Λ_v={λ∈Δ(Z): Σ_a λ_a L_a(w)≥0 for every w∈W_v}.

These are *all* normalized nonnegative certificates that block a common
linear acceleration. Finite polyhedral separation gives the exact strict
alternative:

    ∃w∈W_v, max_(a∈Z)[L_a(w)+Q_a(v)]<0
      iff Λ_v is empty, or max_(λ∈Λ_v) Σ_a λ_a Q_a(v)<0. (5)

For completeness, the forward implication follows by averaging (4): the
weighted linear term is nonnegative. For the converse, failure of strict
feasibility separates the polyhedral set L(W_v)+Q from the open negative
orthant. The separating vector is nonnegative and nonzero, can be normalized
to sum one, is nonnegative on L(W_v), and has λ·Q≥0. This is precisely a
member of Λ_v violating the right side. Compactness of Λ_v makes pointwise
strict negativity equivalent to a uniform negative margin.

If the optimization is restricted to one face and the source lies in that
face's relative interior, W_v is its tangent space. Then Λ_v is simply the
family of convex combinations of tied-response gradients that vanish on that
space. Relative interior of the source's minimal face does not suffice when
new atoms outside that face remain legal. At such a boundary the one-sided
version in (3) is required; replacing it by gradient equality is generally
wrong.

Multiaffinity gives

    Q_a(v)=Σ_(j<k) D_jD_k g_a(p)[v_j,v_k].               (6)

There are no same-player quadratic terms. Thus the quadratic data consists
exactly of pairwise interactions of whole-law changes. A repository response
square supplies one part of (6); criterion (5) says what would turn enough
such parts into an actual simultaneous improvement.

The important quantifier is

    one v works against EVERY λ∈Λ_v.

Finding a favorable pair for each λ separately, or one convenient multiplier
with negative weighted curvature, does not satisfy (5). Nor can one exchange
the nonlinear search over v with the maximum over λ without a theorem.
After v is fixed, however, both primal correction and dual failure are finite
linear programs. This is a potentially useful diagnostic compression.

## 5. What positive minimum hypotheses can and cannot provide

At an actual global minimum on the same finite calendar, no criterion giving
strict improvement within that calendar can hold. First-order minimality
supplies nonnegative directional slopes, but does not by itself supply a
nonzero direction with slope zero. A sharp minimum may have no such direction.
The automatic zero direction has Q=0 and carries no progress.

A source theorem could help in one of three concrete ways:

1. A payoff/cap-preserving family might supply a nonzero feasible v satisfying
   L_a(v)=0 for all active tests. This must be a curve of the same actual laws,
   rather than a signed cancellation of unrelated squares.
2. A newly added calendar atom might give a critical external direction that
   old-calendar minimality did not constrain. All tests are then recomputed
   on the larger calendar, including the new after-support date.
3. A balanced whole-law response relation might give L_a(v)≤0 for every
   active test. A single KKT-weighted equality does not imply these inequalities.

For a hypothetical positive unrestricted minimum, the useful theorem would
derive one of these directions plus the incompatible-with-minimality sign
in (5) from stopping order and reward structure. This is the missing producer,
not a consequence of generic second-order calculus. A clean alternative is
to show that every attempted v has a λ∈Λ_v with nonnegative weighted curvature,
and then ask whether this common certificate has a structural game-theoretic
interpretation. Without such an interpretation it is a local obstruction only.

Near-minimizing finite calendars add a quantitative obligation. A decrement
c_N ε_N² that vanishes faster than all representation or source errors has
no fixed-gap consequence. Any UE use must compare the decrement with the
source's excess above the limiting infimum and every tail/calendar error.
The current sketch supplies no horizon-uniform c or usable ε.

## 6. Relationship to complete pivot repair

For finite opponent laws, the pivot mass polytope and the complete affine
repair objective already eliminate the pivot's infinite-dimensional choice.
One can apply Sections 3–4 to the joint variables (opponent laws, feasible
pivot mass), keeping every pivot-cap candidate as a separate smooth row.
The mass polytope's linear inequalities give the corresponding feasible
velocity/acceleration conditions in place of (3).

This avoids differentiating a selected LP optimizer. At an optimizer with
positive first geometric atom, a small feasible curve implements actual
pivot laws. At zero first atom with positive late mass, the point is only
a limiting mass representation. An actual-law approximation must have
error o(ε²) to preserve the claimed strict quadratic improvement; merely
knowing that the boundary is approachable is insufficient for a rate claim.
The general supplied approximation bound is 2Mα; it improves to Mα when
nonpivot singleton rewards vanish, as in the canonical setting. Either bound
makes α=o(ε²) an available choice once the curve's strict margin is known.
This is a verifier/implementation observation, not a producer of the opponent
perturbation.

The potentially useful unification is therefore modest and precise: a
fixed-witness square, an active-response multiplier, and a complete pivot
LP can share one finite set of curvature rows and one correction problem.
It would be premature to introduce a large general second-order library.

## 7. Failure tests and next bounded experiment

- Keep the full tester set, including after-support and Never. Deliberately
  omit an active zero-weight tester in a negative regression and require the
  common-correction verifier to reject the resulting false certificate.
- Require the exact anchored table in Section 2 to pass with v=(1,1), w=0.
  A first-order-only method must report zero, not strict improvement.
- Use HILBERT/NOETHER's existing coordinate trap as a first-order calibration,
  not as evidence that second-order machinery is necessary there.
- Test a source where raw Q has mixed signs but an acceleration repairs them;
  this tests the actual value of the correction LP over the simpler condition
  Q_a<0 for all zero-slope rows.
- On an actual finite global minimizer, an internal strict certificate is a
  red flag for a missing response, an infeasible boundary curve, or an
  incorrectly tagged numerical minimum. Do not reinterpret it as UE progress.

**Next mathematical question:** can a source-retaining balanced response or
payoff-preserving fibre give a nonzero critical direction whose entire dual
curvature family has a reward-table interpretation? An initial bounded search
should classify that family before spending effort on iteration or export.

## 8. Source audit and known mathematical background

Exact Lean declarations inspected statically, with no build performed:

- `QuittingPivotRepairLPInput.constraintGain` and
  `QuittingPivotRepairLPInput.exists_objective_minimizer`
  (`UniformEquilibrium/Quitting/Terminal/PivotRepairFiniteLP.lean`).
- `singlePivotFiniteMenuScalarSource_iff_smallPivotRepairValue`
  (`UniformEquilibrium/Quitting/Terminal/SinglePivotRepairSourceEquivalence.lean`).
- `QuittingPositiveMinimumDebtTangentFamily.exists_frozenRadialPaidSquare_of_negativeSquare`
  (`UniformEquilibrium/Diagnostics/Quitting/Frozen/RadialCurvatureStrategicDispatch.lean`):
  the inspected theorem constructs a paid-square carrier from a supplied
  negative square and budget; it does not construct common descent.

The source lookup also located the exact objective/behavioral-infimum results
in `PivotRepairExactObjective.lean` and `PivotRepairBehavioralInfimum.lean`, and
the fixed-witness square-sum and cap-nonadditivity declarations in
`MathUE/Optimization/SupremumTwoResetWitnessSwitch.lean`; their bodies were not
audited here. No new claim about Lean coverage is based on this lookup.

Overlap checks included the joint repair, recombination, two-law competitor,
and infinitesimal corner-alignment notes. In particular
[the KKT two-law checkpoint](CODEX_NOETHER_SUPPORT__GLOBAL_KKT_TWO_LAW_COMPETITOR_CHECKPOINT.md)
already computes quadratic decrease of two marked gains and explicitly stops
because the other complete responses are uncontrolled. Sections 3–4 state the
common compatibility obligation rather than silently assuming it is solved.

This is a finite polynomial specialization of established second-order
optimization ideas; see Bonnans, Cominetti, and Shapiro,
[Second Order Optimality Conditions Based on Parabolic Second Order Tangent Sets](https://epubs.siam.org/doi/10.1137/S1052623496306760).
That primary source is background, not an invoked black-box theorem: the
finite Taylor and separation arguments used here are written above. The
game-specific producer remains separate from that general theory.
