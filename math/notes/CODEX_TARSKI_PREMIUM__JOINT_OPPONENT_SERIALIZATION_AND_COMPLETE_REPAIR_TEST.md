# Joint opponent serialization: exact repair improvement and format failure

Author: CODEX_TARSKI_PREMIUM.

Status: bounded ordinary-mathematics test, STOPPED. Serialization can
strictly lower the COMPLETE pivot-repair value on the cyclic calibration,
but its entire output format has a positive all-behavior gap on a simple
solved canonical table. It therefore is not an unconditional arbitrary-table
producer. This does NOT falsify a theorem restricted to a hypothetical
positive global infimum: the negative calibration has global infimum zero
and an existing capped-member exit. No new counterexample restriction,
UE class, export, or conditional compiler is claimed.

Section 5 performs the additional hypothetical positive-global-source
check. It retains the checked all-owner tie consequence and isolates the
literal deleted-collision term that neither it nor the inner repair LP
signs. This is a stopped comparison, not a claim that the hard-source
version of serialization is false.

## 1. Exact source and proposed operation

Read `questions/FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md` and the current
repair route in `docs/FRONTIER.md`. There are four players, independent
complete stopping laws on ℕ∪{Never}, zero live/Never reward, and own
singletons (1,0,0,0). Rewards have a finite bound M. Every unilateral
behavioral strategy is an allowed replacement; no future private clock
is observed.

For three finite nonpivot laws q define

    R(q)=inf_(all complete pivot laws π) E(π,q),
    m=inf_(all finite triples q, all finite deadlines) R(q).

E is the maximum of ALL FOUR original complete debts. The exact current
`exists_objective_minimizer_eq_behavioral_infimum` in
`Quitting/Terminal/PivotRepairBehavioralInfimum.lean` identifies R(q) with
the attained finite mass-LP value, not necessarily an attained behavioral
value. `singlePivotFiniteMenuScalarSource_iff_smallPivotRepairValue` in
`Quitting/Terminal/SinglePivotRepairSourceEquivalence.lean` makes selecting
q with R(q)→0 exactly the canonical remaining source obligation. These
paths are below `UniformEquilibrium/`.

The proposed hypothetical source is m>0 and actual finite triples q^k
with R(q^k)≤m+ε_k, ε_k→0. It assumes neither a global actual minimizer
nor a fixed-calendar minimum equal to m. Approximate pivot realizers may
be selected separately from the checked inner-LP approximation theorem.

For each old date t, choose a permutation rank_t of {1,2,3} onto {0,1,2}.
Replace each nonpivot clock by

    T'_j=3T_j+rank_(T_j)(j) if T_j<Never,
    T'_j=Never otherwise.

This is one joint deterministic calendar operation on three marginal laws,
not shared randomness. Old blocks remain chronologically ordered, but
the three labels' finite supports become pairwise disjoint. Every marginal
Never mass is preserved. Against the new triple the pivot is optimized
afresh over ALL complete laws, with all new within-block, joining,
after-support and Never responses in the exact LP. No baseline response
is declared unchanged merely because a calendar label was refined.

For the positive-infimum application the intended comparison was a fixed
δ=δ(m,M)>0 and cofinally many k with some rank choices satisfying

    R(q_serial^k)≤m−δ.                                (1)

Isolated strict improvements of decreasing finite-calendar minima would
not prove m=0. Neither (1) nor a weaker positive-global-source sign is
proved below. The whole-format check stops this operation before a
selector or a general comparison is built around it.

## 2. Exact successful calibration, including the full repair value

Use the standard VANISH table: r₀(S)=1 when 0∈S and 2 otherwise.
For cyclic order 1→2→3→1, a nonpivot i receives zero if i∈S, receives
−1 if 0∈S and i∉S, and otherwise receives
2·1_{pred(i)∈S}−1_{succ(i)∈S}. Never pays zero.

Initially let each nonpivot use (Quit0+Never)/2. For ANY complete pivot
law set v=Pr(T₀=0), l=Pr(0<T₀<Never), with v,l≥0 and v+l≤1.
Direct conditioning on the only opponent date gives

    B₀=15/8,       d₀=1/8+3v/4−l/8,
    d_i=|1/4−3v/4|+l/8        for i=1,2,3.           (2)

For clarity, a nonpivot's Quit0 payoff is zero. Its best strictly later
finite response is Quit1, with payoff 1/2−3v/2. Subsequent finite
responses only lose from earlier pivot absorption. Never has payoff
1/2−3v/2−l/4. The prescribed payoff is half this Never payoff. These
facts prove its cap max(0,1/2−3v/2) and (2), including arbitrary pivot
tails and the unused after-support dates.

The sum of d₀ and any nonpivot debt is at least 3/8: it is exactly 3/8
when v≤1/3, and equals −1/8+3v/2 when v≥1/3. Hence R(q)≥3/16.
The actual pivot law (3/14)Quit0+(11/14)Quit1 attains equality, proving
R(q)=3/16 without relying on a numerical LP or actual-infimum attainment
in general.

Now serialize the three atoms in order 1,2,3, at dates 0,1,2, each still
with mass 1/2 and with its original Never mass 1/2. Select pivot Never.
Direct first-event calculation gives

    U=(7/4,0,7/8,0),        B=(15/8,0,1,0),
    d=(1/8,0,1/8,0).                                 (3)

For the pivot, Quit0, Quit1, Quit2, after2, Never pay respectively
1,3/2,7/4,15/8,7/4. The three nonpivot caps are respectively 0,1,0;
their own zero singleton means every date after the other clocks is
equivalent to Never. Enumerating dates 0,1,2,3 and Never therefore covers
ALL responses, and random laws average them. Thus
R(q_serial)≤1/8<3/16. There is no claim that 1/8 is the new optimum.

This is method evidence only. The cyclic table is already solved by
known constructions, and the source in this paragraph is not claimed
near the GLOBAL infimum, which is zero.

## 3. Whole serialized-format obstruction on a solved canonical table

For every nonempty S⊆{0,1,2,3}, set

    r₀(S)=1_{0∈S},
    r_i(S)=−1_{0∈S and i∉S}       for i=1,2,3.        (4)

Live and Never pay zero. This is an explicit rational canonical table
with |r|≤1. All four players surely Quit0 is exact terminal Nash: its
payoff is (1,0,0,0), each nonpivot can guarantee and cannot exceed zero,
and the pivot cannot exceed one. Thus the table has a fixed UE payoff.

Now allow ANY complete pivot law and ANY independent nonpivot laws such
that no two nonpivots tie at a finite clock with positive probability.
No finite-support or stationarity assumption is made. This includes every
serialized output, regardless of old calendar, atom masses, rank choices,
or pivot repair. Let A be the probability that the pivot belongs to the
actual first finite quitting coalition.

The pivot has payoff A and cap exactly one, attained by Quit0. Every
nonpivot has cap exactly zero, attained by Quit0, since every reward to
a participating nonpivot is zero and all its rewards are nonpositive.
On a pivot-participation outcome, at most ONE nonpivot can participate.
At least two nonpivots then each get −1. On other outcomes their total
payoff is zero. Consequently

    d₀=1−A,         d₁+d₂+d₃≥2A,
    E≥max(1−A,2A/3)≥2/5.                             (5)

These are complete behavioral caps, not lower bounds for a selected finite
tester alone. Equation (5) covers the entire nonpivot-collision-free format,
including unbounded support and all exact Never masses. Independence is
retained throughout; the payoff inequality itself does not require a
correlation relaxation.

There is also an exact source-to-output failure of every rank choice.
Take the three original nonpivot laws to be sure Quit0. Their full repair
value is zero, using pivot Quit0. After serialization one nonpivot surely
quits at date zero and the other two at dates one and two. For ANY pivot
law let v be its mass at zero. The first nonpivot screens every later
clock. Full debts are 1−v at the pivot, zero at the first nonpivot, and
v at each of the other two. Therefore

    R(q)=0,       R(q_serial)=1/2                     (6)

for ALL six orderings. The latter value is attained by
(Quit0+Never)/2 at the pivot. Reoptimizing over diffuse, late, or unbounded
pivot laws cannot alter (6).

## 4. Exact boundary and stopped status

The negative table is not a positive-global-infimum source. It is already
within the forward canonical image of the unit-singleton/capped-member
class: add one to every nonpivot absorbing coordinate in (4), leaving
Never zero, and every participating reward becomes its unit singleton.
Its displayed pure equilibrium independently makes the global infimum
zero. Thus (5)–(6) do NOT refute (1) under a genuine no-UE hypothesis.

What is decisively false is unconditional collision eradication, even
allowing an optimal choice among all datewise rank orders and complete
pivot reselection. A theorem first dispatching solved classes and then
serializing a remaining positive-infimum source would need a genuinely
new raw/global argument allowing the relevant collisions to be removed.
No such implication is supplied or assumed here. The broader paired-table
collision-free format is not classified in this test; the small exact
failure suffices to stop the unrestricted format claim.

Narrow overlap checks read the exact current repair sources above, plus
`CODEX_NOETHER_SUPPORT__JOINT_OPPONENT_MOVE_AND_COMPLETE_REPAIR_VALUE.md`,
`CODEX_RENY__SIMULTANEOUS_ACTIVE_RESPONSE_RECOMBINATION_BOUNDARY.md`,
`CODEX_FRECHET_CYCLE__PIVOT_LP_CANONICAL_JOINT_CALENDAR_TRAP.md`, and
`CODEX_NOETHER_SUPPORT__ENDPOINT_COLLISION_REFINEMENT_TEST.md`.
Those already cover joint affine replacement envelopes, simultaneous
first-order KKT, fresh tester bills, and end-row splitting. None of their
signs is reused as an upper bound for (1). The finite joint serialization
tested here changes every opponent's relative timing and was assessed by
actual payoffs/caps, rather than by copying an old multiplier to the new
calendar.

An exploratory rational LP calculation suggested the successful numbers
in Section 2. A later returned LP vector failed a direct feasibility check,
so no solver assertion is retained as evidence: (2)–(6) are independent
ordinary proofs with all pure-response classes explicitly accounted for.
No further serialization parameter, compiler, or export is pursued.

## 5. Additional check at the genuine positive-global-infimum source

This section does not reuse the solved calibration as its source. Suppose
m>0 as in Section 1. Full finite-profile approximation and the exact inner
repair value permit actual finite profiles p^k=(π^k,q^k) with E(p^k)→m.
They may be chosen on a common finite calendar separately for each k; no
common deadline across k, actual minimum, or compatible limiting law is
asserted. The infimum over these profiles equals the global actual full
regret infimum by full-profile finite approximation, not merely because
the two source statements have the same zero set.

The checked `minimumTerminalSemantic_maximumDebt_allPlayersTie` in
`UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`
implies

    d_i(p^k)→m for EACH i=0,1,2,3.                    (7)

For the arbitrary reward bound, apply the unit-cube theorem after uniform
positive scaling by 1/M (M≥1 here), which scales all actual payoffs/caps/
debts and preserves minimization. To obtain (7) without attainment, take
any convergent subsequence in the compact prescribed-payoff/full-cap
carrier. Its limit minimizes MAX debt, so the theorem makes all four
limit debts m. If any coordinate failed (7), a subsequence violating it
would have such a cluster point, a contradiction. This transports only
the scalar debts, not clock labels, laws, or multipliers.

Fix one of these actual finite sources and a rank choice. As a concrete
pivot comparison, send its own atom at t to 3t (the first subdate),
retaining Never. Let h_t=Pr(T₀=t), b_t=Pr(T₀<t), and let

    ν₀(t,Q)=Pr(the FIRST finite opponent time is t,
                 with exactly the nonempty coalition Q⊆{1,2,3}).

This is a player-deleted outcome law, independent of the pivot's clock.
Let j_t(Q) be Q's earliest label in the chosen rank order, and let f_t
be the label of rank zero. Define the actual reward differences

    A_t(Q)=r₀({j_t(Q)})−r₀(Q),
    J_t(Q)=r₀({0}∪(Q∩{f_t}))−r₀(Q∪{0}).

Original first opponent coalitions become singletons under serialization.
If the pivot also stops at old date t, it either ties the rank-zero label
or preempts the entire old opponent coalition. Therefore exact conditioning
gives

    ΔW₀=Σ_(t,Q) ν₀(t,Q) A_t(Q),
    ΔU₀=Σ_(t,Q) ν₀(t,Q)
                   [Pr(T₀>t) A_t(Q)+h_t J_t(Q)],
    ΔL₀=Σ_(t,Q) ν₀(t,Q)
                   [b_t A_t(Q)+h_t(A_t(Q)−J_t(Q))]. (8)

The last equality uses L₀=W₀+D₀−U₀ and exact preservation of all three
opponent Never masses, hence of D₀. All sums are finite here. No division
by reach probabilities is used, so zero-reach rows are included correctly.

The specific unresolved joint serialization contribution is

    Σ_(t,|Q|≥2) b_t ν₀(t,Q)
                         [r₀({j_t(Q)})−r₀(Q)].      (9)

It consists of OLD DELETED collisions occurring after the pivot's
prescribed stopping time. Such collisions never affect the source's
prescribed payoff, but can alter its full Never/late response. Original
on-path collision mass cannot bound (9). The second term in (8) is also
retained: even for a singleton Q not containing f_t it includes
h_t ν₀(t,Q)[r₀({0,j_t(Q)})−1], the actual pivot joining premium lost by
preemption. Canonical singleton normalization does not assign either
of these reward differences a sign.

All other owners and tester dates must remain as well. A concise exact
description is as follows. Let μ(t,S) be the prescribed first-coalition
law and ν_i(t,Q) the owner-i-deleted one. Give the pivot subdate zero and
the nonpivots their selected ranks; let φ_t(S) be the labels in S of
smallest subdate. Then

    ΔU_i=Σ_(t,S) μ(t,S)[r_i(φ_t(S))−r_i(S)].

For a new response 3t+a, its change relative to original response t is

    ΔV_i(t,a)=Σ_(u<t,Q)ν_i(u,Q)[r_i(φ_u(Q))−r_i(Q)]
       +Σ_Q ν_i(t,Q)
          [r_i(φ_t^{i,a}(Q∪{i}))−r_i(Q∪{i})],       (10)

where φ_t^{i,a} assigns the deviator its actual chosen subdate a. On the
event of no opponent stop by t, the singleton payoff is unchanged, so it
contributes zero to the difference. Never has the analogous first sum
over ALL finite u. The after-support difference is the same as Never's,
because the deleted Never product is unchanged. Thus every new complete
tester has gain

    g'_(i,3t+a)=g_(i,t)+ΔV_i(t,a)−ΔU_i,              (11)

with separate Never and after-support tests as just specified. These are
identities for actual independent laws, not averages over strategically
chosen corners. On a source calendar {0,…,N−1}, include all new dates
0,…,3N and Never; later dates duplicate the complete after-support row.

By (7), every owner has original cap-attaining rows of gain m+o(1).
For this displayed pivot transport, a fixed decrease therefore requires
negative changes in (11) for EVERY old near-cap row's new subdate copies,
for all four owners, as well as control of all other new rows. There is
no off-pivot slack furnished by the global source. An average sign at one
chosen tester would not suffice. Equation (8) is an additional compulsory
pivot row, whether or not it was the old cap attainer.

Complete pivot reoptimization is still allowed; (8) is not asserted to
describe every repaired pivot law. At the new finite opponent input, the
CURRENT exact LP instead minimizes the maximum of all its affine rows.
Prescribed-payoff changes are affine in the new pivot mass coordinates;
the complete nonpivot head, first-late, Never/limit rows must be priced
together. The scalar ΔW₀ in (8) is fixed by the new opponent triple,
independently of that pivot choice. The old LP's dual gives a lower
certificate, not the needed upper bound for this new maximum. This is
exactly the distinction already established in the joint-opponent repair
note cited in Section 4; no source-dual weights are silently transported.

Outcome of this additional hard-source check: (7) is genuinely available,
but it supplies no proved sign for (9), for the joining term in (8), or
for the simultaneous full-row correction in (11). This is NOT a proof
that the entire no-UE hypothesis cannot force a sign. The specific missing
step is a global source argument selecting ranks and a new pivot law so
that the complete new LP objective lies below m by a fixed amount, despite
the actual deleted-collision contribution (9). No such argument was found.
The comparison consequently returns to the already documented unpaid
counterfactual-collision/full-repair boundary and is stopped here, without
another framework or purported conditional producer.
