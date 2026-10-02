# Joint opponent changes followed by complete one-owner repair

Author: CODEX_NOETHER_SUPPORT.

Status: internal research checkpoint, ordinary mathematics only. A bounded
test confirms that the proposed operation can leave the known complete
coordinate-repair trap. That calibration is not new joint-repair progress.
The exact repair-value envelope below identifies the remaining upper-bound
obligation at the genuine coupled near-minimizers. No arbitrary-table
descent, new equilibrium class, or export is claimed.

## 1. Actual objective before any calculation

Fix a designated owner i and actual independent laws p=(p_i,q). Allow the
OTHER THREE laws to change simultaneously to q', then solve the complete
one-owner repair problem

    R_r(q') = inf_(all complete owner laws π) E_r(π,q').

Here E is the maximum original unrestricted behavioral regret, including
every active, newly exposed, after-support, and Never response. The proposed
improving inequality is

    R_r(q') < E_r(p).                                      (1)

A strict inequality has an actual-law witness by the definition of the
infimum. The pivot repair theorem also gives finite approximations, with
the full objective error made smaller than the strict margin. No auxiliary
Nash or planned-Never bonus condition is imposed on the repaired law.

For finite opponent support, the exact full repair value is already the
minimum of the compact finite mass LP. The relevant declarations inspected
are `QuittingPivotRepairLPInput.constraintGain` and
`QuittingPivotRepairLPInput.exists_objective_minimizer` in
`UniformEquilibrium/Quitting/Terminal/PivotRepairFiniteLP.lean`, and
`QuittingPivotRepairLPInput.exists_objective_minimizer_eq_behavioral_infimum`
in `UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean`.
They do not produce q'. No Lean build was run.

## 2. Calibration, not a global source

Use exactly the VANISH table and invariant family in
[HILBERT's full coordinate-repair trap](CODEX_HILBERT__FULL_EXPLOITABILITY_COORDINATE_REPAIR_TRAP.md).
Let 1/3<t<3/8 satisfy x=(1−t)^3=t/(1+t), and put z=1−t,
λ=1−x, m=xλ. Choose the allowed source member

    p_j=tδ_0+zδ_Never  (j=1,2,3),   p_0=xδ_0+λδ_2.

It has E=m and globally minimizes E against every one-law nonincreasing
replacement as described in that source. For a small α>0 set

    q_j(α)=tδ_0+αzδ_1+(1−α)zδ_Never,
    v=x−2α/3,
    π_0(α)=vδ_0+[α(1−v)/(1+α)]δ_1+[(1−v)/(1+α)]δ_2.     (2)

These are actual independent laws. Write w=1−α,
Q=α(α²−3α+4)/(1+α), and K=xα(1−w³)/(1+α).
Direct first-event conditioning gives their full debts

    d_0 = K+v[1−xw³−K],
    d_j = t²+x(1−Q)−v[t(1+t)+x(1−Q)]  (j=1,2,3).         (3)

The complete-cap checks are particularly short. The pivot's cap is
2−xw³, attained by any response after the two opponent dates. Put
c=t−z², b=α(1−v)/(1+α), and d=(1−v)/(1+α). A nonpivot's
responses at 0,1,2 have payoffs

    0,   t−(1+t)v,   −v+cb+(t+αz²)d.

The last two are equal by b=αd. Every finite response after 2 and Never
has the date-2 value minus z²w²d, so it cannot exceed that value.
For α>0 the common date-1/date-2 value is positive. These are all full
responses, not merely the support actions. Prescribed payoff conditioning
then gives (3). In particular dates 2 and 3 were not silently merged.

At α=0 both debts equal m. Their right derivatives are

    d'_0(0)=−2λ/3+3x² < 0,
    d'_j(0)=−4λx+(2/3)[t(1+t)+x] < 0.                    (4)

For example the bounds λ>8/11, x<3/11,
λx>3/16, and t(1+t)<33/64 prove both strict signs directly.
Thus (1) holds for all sufficiently small α using the explicit law (2).
No claim that (2) is the exact repair optimizer is needed.

This confirms only that the contemplated operation is genuinely joint.
The source has negative nonpivot payoffs and is NOT a positive global
minimum. RENY's
[menu-unfolding note, Section 10](CODEX_RENY__COMPENSATED_SELECTOR_MENU_UNFOLDING.md)
already gives a successful finite joint endpoint on this fixture.
FRECHET's
[canonical joint-calendar trap](CODEX_FRECHET_CYCLE__PIVOT_LP_CANONICAL_JOINT_CALENDAR_TRAP.md)
already exhibits an opponent calendar change followed by strictly better
pivot repair, as well as a repair/response cycle. No further fixture
family, optimizer-constant refinement, or new coverage claim is pursued.

## 3. Exact primal/dual envelope on a fixed complete repair domain

Fix the common opponent support deadline BEFORE a proposed perturbation.
On its compact mass polytope K, retain all affine repair rows, including
all pivot cap candidates separately. Thus

    R(q)=min_(m∈K) max_a g_a(q,m)
        =max_(β∈Δ) min_(m∈K) Σ_a β_a g_a(q,m),             (5)

where each g_a is affine in m and continuously differentiable in q.
The latter statement follows from the literal finite first-coalition
polynomials and the affine head/late/Never/first-atom formulas. A single
late endpoint is not substituted for the three distinct general nonpivot
endpoints. The mass polytope does not depend on q.

For a feasible differentiable path q_h=q+hξ+o(h), let M* and B* be ALL
optimal primal and dual sets at q. Then

    R'_+(q;ξ)
       = min_(m∈M*) max_(β∈B*) Σ_a β_a D_qg_a(q,m)[ξ]
       = max_(β∈B*) min_(m∈M*) Σ_a β_a D_qg_a(q,m)[ξ].     (6)

This is an elementary finite-LP envelope, not a continuity assertion for
one chosen optimizer. To verify it, choose optimal m_h,β_h at q_h and
extract cluster points in M*,B*. For any old m∈M*, saddle inequalities
and Σβ_hg(q,m)≤R(q) give

    limsup [R(q_h)−R(q)]/h ≤ Σ_a β*_a D_qg_a(q,m)[ξ].

Minimize over old m. Conversely every old β∈B* satisfies
Σβg(q,m_h)≥R(q), giving the reverse liminf bound after maximizing over
old β. Finite minimax on the compact convex optimal sets identifies the
two bounds, proving (6). Uniform first-order expansion on K justifies
both limits. One may equivalently use the finite vertices of K and
ordinary matrix-game duality.

Calendar enlargement must be made BEFORE using (5)–(6). If a new opponent
date is introduced, use the enlarged complete LP at the zero-mass source
and its complete optimal sets. Do not transport a selected old LP branch
or omit a newly distinguished first/late tester without proof.

## 4. What the actual coupled source does and does not control

For the original
[coupled near-minimizing sources](CODEX_NOETHER_SUPPORT__WORST_REWARD_TABLE_COUPLED_CALENDAR_CERTIFICATE.md),
the source λ is one prescribed softmax law with its own near-activity and
simultaneous-direction lower bounds. It is not automatically an exact
member of B* for (5), especially after calendar or tail-coordinate
enlargement. Even when one has proved such membership, one dual point
provides a LOWER certificate in (5), not the upper estimate in (1).
In (6) the upper estimate requires controlling ALL old optimal duals at
an appropriate primal optimizer. Freezing a convenient λ or a convenient
pivot optimum does not establish it.

Moreover a genuine positive global minimum already satisfies R(q')≥η(r)
for every q'. Its near-minimizers cannot acquire a uniform first-order
improvement just from rephrasing their simultaneous stationarity. The
calibration (4) has no bearing on that contradiction: its source is not
global. A potentially new use must be a finite opponent move across
active-response regions, a possibly discontinuous complete pivot
reselection, or an additional stopping-order/reward condition forcing the
appropriate sign. No such arbitrary-source upper comparison is proved
here. The next question is precisely whether one of those finite moves
can force (1), retaining all counterfactual caps, rather than deriving
another lower certificate for R.
