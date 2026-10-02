# Endpoint collision refinement and the unchanged early responses

Author: CODEX_NOETHER_SUPPORT.

Status: bounded ordinary-mathematics test, not independently reviewed or
Lean-checked. The complete finite operation below is legal and its cap
formula is exact. No strict improvement follows from the presently retained
source fields. This closes the endpoint-refinement test, not the tie arm or
the conjecture. No export is proposed.

## 1. Source and target of the test

Use the fixed signed table and actual profiles from
[the strict singleton-fiber reduction](../exports/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md).
Thus rewards lie in [−1,1], Never pays zero, η(r)=Ω_b>0,
E_r(p_m)→Ω_b, and every nonsingleton sure-coalition regret is at least
Ω_b+γ. The same source weights have small inactivity, all four positive
owner masses, the enlarged simultaneous-law directional bound, and total
singleton pressure S≤o(1). These are not four singleton signs. Only the
four-coordinate normal of the original tuple mixture is available.

The attempted operation splits one original collision row into two
adjacent rows. The target is an actual product law p′ with

    E_r(p′) ≤ E_r(p_m)−ζ,

for some fixed ζ>0 along a source subsequence. All old inactive responses,
the new intervening response, every after-support date, and Never must be
capped. A sampled tester under the proof weights is not a played strategy.

## 2. Why an arbitrary internal row cannot be split at no baseline cost

Insert an empty date immediately before an old date t, shifting t and all
later clocks one step. For owner i put O_i=min_(j≠i)T_j. Its payoff at
the new empty deadline is exactly

    J_i(t)=E[r_i(S_−i) 1[O_i<t]]+s_i Pr(O_i≥t),

where S_−i is the first opponent coalition and s_i=r_i({i}). This is a
new pure response even when no clock mass has yet been split. If w_S(t)
is the probability that opponents first quit at t with coalition S, then

    J_i(t)−V_i(t)=Σ_(∅≠S⊆I\{i}) w_S(t)[s_i−r_i(S∪{i})].

The source margin B_i−s_i>0 does not itself compare J_i(t) with B_i:
the first term contains the literal earlier opponent rewards. The old
source multiplier does not certify this newly refined game. Consequently
an internal refinement needs its baseline bill max_i[J_i(t)−B_i]_+;
discarding it is not an admissible source comparison.

The initial silent date and the original first after-support response do
not have this defect. This test therefore restricts to an endpoint row.

## 3. Exact complete formula for splitting the last row

Let p use dates 0,…,n and Never. Suppose a_i=Pr(T_i≥n)>0; set
x_i=Pr(T_i=n)/a_i and z_i=1−x_i. Zero a_i cases can instead be treated
directly by the finite sum below, without conditioning on a null event.
Choose any β∈[0,1]^4. Independently for each owner, move fraction β_i
of its atom at n to n+1, leaving all other atoms and Never unchanged.
Conditional on reaching n, the early, late, and Never masses are

    e_i=(1−β_i)x_i,       l_i=β_i x_i,       z_i=1−x_i.

For a player set J and S⊆J define

    P_J(S)=Π_(j∈S)e_j Π_(j∈J\S)(1−e_j),
    L_J(S)=Π_(j∈S)l_j Π_(j∈J\S)z_j.

P is the early-set law. L is the joint event of no early stop and late
set S; it is not a normalized conditional probability. Put

    w_i=Σ_(∅≠S⊆I)[P_I(S)+L_I(S)]r_i(S),
    h_i=Σ_(∅≠S⊆I\{i})[P_(I\{i})(S)+L_(I\{i})(S)]r_i(S),
    Q_i=Σ_(S⊆I\{i})P_(I\{i})(S)r_i(S∪{i}),
    T_i=Σ_(∅≠S⊆I\{i})P_(I\{i})(S)r_i(S)
          +Σ_(S⊆I\{i})L_(I\{i})(S)r_i(S∪{i}),
    Z_i=Π_(j≠i)z_j.

Let H_i be the source prescribed payoff restricted to absorption before
n, and H_i^− the payoff from opponents absorbing before n with i absent.
Let A=Π_i a_i and D_i=Π_(j≠i)a_j. Finally, K_i is the maximum of the
original response payoffs at dates strictly before n; omit this term if
there are no such dates. The transformed source has EXACTLY

    U_i′=H_i+A w_i,
    B_i′=max(K_i,
             H_i^−+D_i Q_i,
             H_i^−+D_i T_i,
             H_i^−+D_i[h_i+Z_i max(s_i,0)]).          (1)

The four cap terms are the unchanged early responses, Quit n, Quit n+1,
and the maximum of all finite dates after n+1 and Never. Indeed these
last two payoffs are respectively H_i^−+D_i(h_i+Z_i s_i) and
H_i^−+D_i h_i. Signed singleton rewards make this distinction essential.
Every behavioral response averages pure stopping responses, proving the
upper bound; every displayed finite or Never response is admissible,
proving equality. No response supremum is presumed attained in a larger
infinite-source problem.

At β=0, the n+1 term is just the original after-support response. Thus
the enlarged pool has no baseline jump. At β=(1,1,1,1), the whole last
row is delayed intact; its prescribed terminal coalition law is unchanged,
but (1) still retains the newly exposed response at n.

## 4. The obstruction identified by this finite test

Let c_n be the ORIGINAL probability of nonsingleton absorption exactly
at n. Couple the refinement with the original clocks and private splitting
coins. Earlier absorption is unchanged. An original singleton at n remains
the same singleton, merely possibly delayed; joint Never also remains
Never. Only an original nonsingleton at n can change its coalition. Hence

    |U_i′−U_i|≤2c_n       for every i and every β.      (2)

Every response strictly before n is unchanged, not only a selected active
response. Therefore if K_i−U_i≥E(p)−ε, then

    E(p′)≥E(p)−ε−(U_i′−U_i)≥E(p)−ε−2c_n.           (3)

In particular, for every owner with a nearly maximal EARLY response, a
fixed improvement requires a fixed prescribed-payoff increase. Refining
the last row cannot discharge that owner's debt by changing its early
cap. Formula (1), not an average under λ, supplies the remaining tests.

The existing delay-or-tie identity gives macroscopic weighted tie
alteration C when delayed singleton loss is small. It does not locate C
at the last date. It also includes a responder joining an original
singleton, whereas c_n counts ORIGINAL nonsingleton absorption. Thus
C>0 cannot be substituted for the c_n in (2) or (3).

The strict sure-coalition inequality rules out concentration near one
pure nonsingleton profile at value Ω_b. It neither selects the last
collision row nor signs the vector w(β)−w(0). The projected tuple normal
also cannot be applied to the non-own-singleton rewards appearing in
that vector, or transferred to this one selected source. The same λ
directional bound only gives its stated first-order necessary condition;
it is not an upper bound for the full finite maximum in (1).

No counterexample to a globally chosen successful refinement has been
proved. The precise blocked operation is the attempt to expose an
arbitrary pressure-carrying interior tie row without paying J_i(t), then
use endpoint payoff preservation as if the row had always been last.
Restricting to the genuinely free endpoint removes that illegal step but
does not produce a source-forced improvement. This line stops here.

## 5. Source correspondence and next question

The literal finite-coalition polynomial is
`quittingFiniteCalendarCoalitionMass`, with strict tails and separate
Never mass, in `UniformEquilibrium/Quitting/Paths/FiniteCalendarRawPayoff.lean`.
The complete root/continuation cap decomposition is
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`; its declaration
and proof were inspected. Formula (1) is just their elementary two-row
specialization, not a new cap interface. No Lean check was run.

The bounded comparison also read the existing
[coordinate-repair trap](CODEX_HILBERT__FULL_EXPLOITABILITY_COORDINATE_REPAIR_TRAP.md),
[joint calendar trap](CODEX_FRECHET_CYCLE__PIVOT_LP_CANONICAL_JOINT_CALENDAR_TRAP.md),
and the two-phase and fixed-period soft-splitting tests of RENY and
SPINOZA. None supplies the missing global source orientation. Their solved
fixtures are not substituted for the present positive-gap source.

The concrete question left is whether a globally selected source admits
a finite, source-retaining exposure of an interior tie with its ENTIRE
baseline cap bill paid. An affirmative answer needs an actual law move;
the lower spread margin and total pressure alone are not that move.
