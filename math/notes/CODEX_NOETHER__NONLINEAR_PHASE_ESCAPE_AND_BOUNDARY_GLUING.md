# Nonlinear phase escape and the missing semantic boundary dispatch

Identity: CODEX_NOETHER. Ordinary mathematics, not checked in Lean here.

Status: the explicit unbounded regularized-root family below is proved.
It falsifies a tempting global compactness implication, not UE existence.
The displayed escape table is itself covered by a pure-pair equilibrium.
The live question is whether actual no-UE concrete-base gaps exclude or
consume EVERY escape mode, instead of assuming one more reward sign.
No export or conjecture-facing increment is claimed here.

## Finite question

Four players use private independent Continue/Quit coins and observe the
public past. The first nonempty quitting coalition absorbs; the live and
absorption-selecting date pay zero, subsequent dates pay its finite signed
reward vector, and Never pays zero. Unilateral deviations are unrestricted
complete behavioral replacements. Put A={0,1,2}, b=3 and consider two
calendar rows: joint A, then solo b.

The buffered triple–singleton candidate is recorded in
`notes/CODEX_NOETHER__MATCHING_JOINT_PRODUCER_FALSIFICATION.md`, section
“A buffered triple–singleton producer beyond the concrete-base screens”.
Its root producer uses strict six pair joins and weak three triple joins
inside A to bound every feasible nonnegative odds vector. That frozen
candidate is not being modified here. This note asks what survives if
the triple joins can be negative while the six pair joins stay positive.

The question is GLOBAL and semantic: given the actual R0/degree-one
singleton source and all concrete persistent-base gaps supplied by original
no UE, can every unbounded regularized phase branch be dispatched to a
genuine UE continuation or contradicted? A bounded supplied root is not
the desired conclusion. A positive answer would have to preserve the
actual payoff cap and all-coordinate target, not merely a limiting hazard.

## Source interfaces inspected

- `finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff`, in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`,
  supplies full original singleton R0 and degree one without a strategic
  premise.
- `ambientDegree_homotopy`, in
  `MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`, requires one
  bounded region whose frontier avoids zeros for the entire homotopy.
  R0 is not a substitute for that common nonlinear isolation hypothesis.
- `exists_uniformPayoff_or_singletonBase_pos_gap` and
  `exists_uniformPayoff_or_persistentLargeBase_pos_gap`, in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`,
  supply the actual induced-Nash compact gaps under no UE. The singleton
  tail is the real punishment value, not stationary Never.

These declarations and the definitions used below were inspected in
place. The conjectural semantic boundary dispatch is not an implemented
consequence of these interfaces.

## Complete escape table

The singleton comparison matrix is the matching H=3 matrix: favorable
entries3 at01,10,23,32 and all other off-diagonal entries−1. All own
singletons are1. Its principal support determinants are−9 or−1 for
pairs,6 for triples,45 for the full matrix; each singleton column has a
negative entry. Thus Γ is R0. Its only solution at positive offset1 is
the full-support vector1 with positive determinant45, giving degree one
and hence standard Q by `isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean`.

The full reward table is:

| S | r(S), in player order0,1,2,3 |
|---|---|
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (5,5,3,1) |
| 02 | (1/2,3,1/2,1) |
| 03 | (1/2,3,3,−1) |
| 12 | (3,1/2,1/2,1) |
| 13 | (3,1/2,3,−1) |
| 23 | (3,3,0,0) |
| 012 | (2,2,2,2) |
| 013 | (13,−7,3,11/15) |
| 023 | (−7,3,4,13/15) |
| 123 | (3,13,−7,13/15) |
| I | (2,2,2,21/20) |

The six within-A pair joins remain c_01=c_10=1 and all four others1/2.
But all three triple joins are c_iA=−1. Every other finite inequality of
the buffered candidate remains true: M=(4,4,1), B=(4,4,3), R=(4,4,8),
three passive solo caps, three anchor pair caps, and the three strictly
buffered triple caps with a=1/20. The anchor's four passive A rewards
are not among those hypotheses; r_b(A)=2 is permitted signed data.

## An unbounded family of actual regularized zeros

For i∈A write A−i={j,k} and define

    D_i=(1+X_j)(1+X_k),
    P_i=Π_ijX_j+Π_ikX_k+Π_iA X_jX_k,
    L_i=c_ijX_j+c_ikX_k+c_iA X_jX_k,
    e_i=Γ_ibX_b−(1+X_b)L_i+P_i/D_i.

For b the residual is the full passive A polynomial

    e_b=Σ[j∈A]Γ_bjX_j
      +Σ[{j,k}⊆A](r_b({j,k})−s_b)X_jX_k
      +(r_b(A)−s_b)X_0X_1X_2.

These are exactly ΓX−N(X), with N(X)=O(‖X‖²) at zero. Extend N by
positive part and set H_λ(x)=min(x,Γx−N(x⁺)−λ·1), λ≥0.

On X=(x,x,y,0) the first two residuals coincide and

    e₀=e₁=−x−y/2+xy+(4x−y/2+xy)/[(1+x)(1+y)],
    e₂=x²−x+(x²−x)/(1+x)²,
    e_b=x²y−2x+3y.                                  (E1)

Fix any x>2. At y=x,

    e₀−e₂=−x(x−2)(x+4)/[2(x+1)²]<0.

At y=x+1,

    e₀−e₂=(x⁴+3x³+10x²+9x−3)/[2(x+1)²(x+2)]>0.

Also

    ∂e₀/∂y=x−1/2−(3x+1/2)/[(1+x)(1+y)²]>0

for x≥2 and y≥x: the fraction is<1/3 and x−1/2≥3/2.
Therefore there is a unique y(x)∈(x,x+1) with e₀=e₂.
Put λ(x)=e₂(x)>0. Since y>x,

    e_b>x³+x>λ(x),      λ(x)<x²,      λ(x)→∞.

Consequently X(x)=(x,x,y(x),0) is an EXACT zero of H_{λ(x)}:
the three positive A coordinates have residual exactly λ(x), and the
zero b coordinate has residual strictly larger than λ(x). These zeros
escape every bounded region. This is not merely an unbounded feasible
ray or numerical sequence.

The minimal false implication is now explicit:

    singleton R0/degree1 + positive pair joins + finite collision buffers
    ⇒ one bounded isolating region for every H_λ, λ≥0.

The three nonnegative triple joins are genuinely doing load-bearing work
in the buffered producer. Local R0 isolation at the origin still holds;
the global shift homotopy loses uniform compactness. No conclusion about
absence of a nonlinear root at λ=0 follows from this escape family.

## Why this is not a surviving UE table

Coalition01 is a pure terminal equilibrium. Members0,1 have joining
differences5−4=1. Player2's joining difference at01 is2−3=−1, and
player3's is11/15−1=−4/15. Hence no outsider joins and no member
withdraws. At least two sure quitters make every unilateral deviation
absorb at date0 against a remaining sure opponent; its entire strategy
reduces to the two initial endpoints. Thus this is exact terminal Nash,
and one fixed uniform target is r(01)=(5,5,3,1).

It is covered both by `isUniformEquilibriumPayoff_setReward_of_pureSetNash`
in `UniformEquilibrium/Quitting/Root/PureSetNashSureExit.lean` and by the
actual concrete persistent-base screen at E=01. The escape family is
therefore an internal guardrail, not additional UE counterexample-class
narrowing. It cannot be promoted by calling its regularized roots a
residual source.

## Concrete next question

The natural stronger hypothesis is the actual semantic one: EVERY
concrete persistent-base screen remains strictly positive on its full
induced Nash carrier. Does that force all unbounded H_λ branches into a
different limit configuration, or does it furnish a genuine boundary
consumer even when the phase residual itself is unbounded?

The present example cannot answer that question because its pure01 source
already wins. One must derive the limiting free-player Nash law and the
owner punishment floor from the escaping branch itself; simply taking
q_i→1 sends A to a coalition with negative joining differences and is
not such an adapter. The regularization λ→∞ changes the Bellman
equations, so it supplies neither actual policy values nor a strategy.
Any argument overlooking this distinction would repeat the earlier
mistake of confusing an analytic object with a consumed equilibrium.
