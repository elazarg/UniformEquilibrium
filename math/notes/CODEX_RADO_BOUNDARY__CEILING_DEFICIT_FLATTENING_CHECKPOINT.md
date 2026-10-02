# Below-ceiling response mass does not fund endpoint-fixing reward flattening

Identity: CODEX_RADO_BOUNDARY. Date: 2026-09-08.

Status: bounded operation tested and stopped. Ordinary mathematics, no new
source restriction, UE construction, or export claim. This is a follow-through
to the separate ceiling-face note, whose SHA
`39bfb13ab79024d2ae711c30a38c63854b89a0dfe35622ac472664311d1ee22e`
is preserved during its independent review. The obstruction here is an exact
same-weight cancellation, including finite-amplitude payoff transport, not
an inferred no-UE example or a general impossibility of reward/law operations.

## 1. One proposed operation, with the whole source retained

Use the actual full-cube worst-table source from
[the ceiling-face calculation](CODEX_RADO_BOUNDARY__FULL_NORMAL_MAX_SOURCE_EXCLUDES_JOINT_CAP_CEILING.md).
Four independent complete stopping laws, all unilateral behavioral responses,
rewards r*=r∈[−1,1]^60, and original joint-Never payoff zero are retained.
The fixed table has η(r)=Ω>0. The produced finite entry weights ω_m and
same complete tester weights λ_(p,i,a), including zero and Never, satisfy
uniform E_r(p)→Ω, vanishing inactivity, pointwise owner floors, and the
stated enlarged-calendar directional inequalities. Their entire reward-row
average G_m tends to the outward cube normal G. No individual source is
asserted normal.

The preceding result supplies positive same-weight below-ceiling response
deficit mass. The concrete test was whether the endpoint-fixing deformation

    φ_i(S)=1−r_i(S)^2  for nonempty S,       φ_i(Never)=0,
    r_i^t(S)=r_i(S)+t φ_i(S),               |t|≤1/2,

can use that mass to improve full regret, either on the retained laws or
after globally re-minimizing at the nearby ACTUAL reward table. The map
x↦x+t(1−x²) is increasing on [−1,1] and fixes both endpoints for this
range of t, so every r^t lies in the same cube. Never remains zero; φ at
Never is not obtained by substituting its zero payoff into the polynomial.

## 2. Exact transfer for every complete response

For any actual independent profile p, and ANY complete response a of i,
put

    Z_i(p)=Σ_(S≠Never) φ_i(S) μ_p(S),
    W_(i,a)(p)=Σ_(S≠Never) φ_i(S) ν_(p,i,a)(S),
    h_(i,a)(p)=W_(i,a)(p)−Z_i(p).

Then, exactly and at finite t,

    U_i^(t)(p)=U_i(p)+t Z_i(p),
    V_(i,a)^(t)(p)=V_(i,a)(p)+t W_(i,a)(p),
    g_(i,a)^(t)(p)=g_(i,a)(p)+t h_(i,a)(p),
    E_(r^t)(p)=sup_a [g_a(p)+t h_a(p)].                (1)

The zero tester has g_0=h_0=0. Since 0≤φ≤1 on ALL outcomes, |h_a|≤1.
These formulas include arbitrary unbounded laws, every omitted date,
collisions, and original Never. They do not freeze the full-cap active set.

## 3. The same-weight cancellation is exact at finite amplitude

Use the full common-weight measures from the preceding note,

    P_i^m(S)=E_ω[θ_i(p) μ_p(S)],
    N_i^m(S)=E_ω Σ_a λ_(p,i,a) ν_(p,i,a)(S),
    G_i^m(S)=N_i^m(S)−P_i^m(S).

The retained source gives

    E_ω Σ_a λ_(p,a) h_a(p)=Σ_(i,S) φ_i(S)G_i^m(S)→0. (2)

Indeed at every interior reward coordinate G_i(S)=0. At either endpoint
φ_i(S)=0. This uses the full sixty-coordinate normal and the original
actual law differences, not a new scalar multiplier or a law at an unrelated
profile. Equivalently, every positive φ-weighted response mass is matched
by precisely the same φ-weighted baseline mass in the limit.

Combining (1)–(2) with inactivity gives, for EVERY fixed |t|≤1/2,

    E_ω Σ_a λ_(p,a) g_a^(t)(p) → Ω,
    liminf_m E_ω E_(r^t)(p) ≥ Ω.                       (3)

Thus this actual reward deformation cannot uniformly lower full regret by
a fixed amount on all retained entries while keeping their laws. This is
not only a vanished derivative: the transfer in (1) is affine in t, so the
same frozen-weight cancellation holds at every allowed finite amplitude.
Some entries might improve and others worsen; (3) claims no individual sign.

The preceding ceiling theorem does not evade this cancellation. Its positive
deficit account is

    K_m=E_ω Σ_(i,a) λ_(p,i,a)[1−V_(i,a)(p)].

Deficit at a −1 outcome or at Never is invisible to φ. Deficit at an
interior outcome can contribute to W, but its contribution is canceled
by Z in the full normal account. In neither case can K_m replace the
signed transfer h in (1).

## 4. Globally re-minimizing does not repair the sign

This step does use the genuine global reward maximum. Let m_t=η(r^t)≤Ω,
and take ANY actual ε-minimizer p_t for that complete unrestricted value.
For 0<t≤1/2, (1) and the original global floor give

    Ω≤E_r(p_t)
      ≤m_t+ε+t sup_a[−h_a(p_t)].                       (4)

Consequently some complete-response transfers approach the bound

    sup_a[−h_a(p_t)] ≥ (Ω−m_t−ε)/t.                   (5)

This is compensation in the wrong direction for transferring the lower
deformed regret back to the original table. It supplies no upper bound on
E_r(p_t) strictly below Ω. Since |h_a|≤1, letting t→0 and ε→0 does retain
original near-minimality E_r(p_t)≤Ω+ε+t. It does NOT retain the original
source's λ or its common full normal at those newly selected profiles.
Fresh multiplier selection or identification with the old tuple would add
an unproved assertion. No such assertion is made here.

## 5. Exact actual-law calibration of the invisible-deficit arm

This one solved fixture verifies that the endpoint-blind alternative is a
literal stopping-law phenomenon, not merely an arbitrary normal array.
For nonempty S set

    r_0(S)=−1 if 0∈S, and +1 otherwise;
    r_i(S)=+1 exactly when S={1,2,3}∖{i}, and −1 otherwise
        for i∈{1,2,3}.

Joint Never pays zero. Let player 0 stop at date one with probability 1/2
and otherwise Never; let the other three stop surely at date two. The
baseline coalitions {0} and {1,2,3} each have probability 1/2. Exact full
values are

    U=(0,−1,−1,−1),     B=(1,0,0,0),     d=(1,1,1,1).

Never attains every cap. Times {0,1,2,3,Never} are complete response
representatives against these opponents; all later finite dates equal three.
Each owner's response-law difference is an outward normal at this Boolean
table. With λ_(i,Never)=1/4, inactivity is zero, all owners have positive
weight, and the weighted response deficit is K=3/4. The deficit is carried
by the unchanged {0} outcome in the three nonzero owners' Never responses.
Yet φ is identically zero and every r^t is literally the same table.

Exact rational enumeration checked all displayed values and every normal
sign at all fifteen coalitions. This fixture is NOT a produced positive
global source: all own singletons pay −1, so all-Never is exact terminal
Nash and η=0. It does not falsify the ceiling theorem or claim to satisfy
all its directional/source fields. Equations (2)–(5), not this calibration,
are the conclusions established for the genuine produced source.

## 6. Outcome and boundary

No further concrete use of the new cap-ceiling restriction was obtained by
this operation. The exact surviving global comparison is (4), with no
favorable transfer sign. This stops the chosen endpoint-fixing deformation;
it does not open a hierarchy of residual interfaces or certify any class.
A genuinely different next operation would have to change actual product
laws while controlling the ENTIRE original cap, or bring another global
comparison that does not cancel in (2). Neither is supplied here.

Narrow source checks used the preceding note's full-source producers, the
existing [owner-block deformation checkpoint](CODEX_RADO_BOUNDARY__GLOBAL_OWNER_BLOCK_DEFORMATION_CHECKPOINT.md),
and reward/Jensen/normal records to distinguish this literal table operation
from profile convexification and from the known affine Never correction.
No mathematical source under review, Lean file, export, or shared index was
changed. The note is a failed-operation record, not an additional theorem
admission request.
