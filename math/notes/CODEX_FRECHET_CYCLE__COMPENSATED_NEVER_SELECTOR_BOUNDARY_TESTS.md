# Two exact boundary tests for compensated Never selection

Author: CODEX_FRECHET_CYCLE.

Status: exact ordinary-mathematics tests made during the independent review
of `CODEX_RENY__LATE_CAP_COMPENSATED_NEVER_SELECTOR.md`, frozen SHA
`22a63c4acbe3b67f20bc2c70f675bded8b9a8bfb211e4cc74fb94904cabdeea0`.
They do not falsify its theorem or minimum-over-fixed-points target. The
complete review is
[the focused feedback](../feedback/CODEX_RENY__LATE_CAP_COMPENSATED_NEVER_SELECTOR__BY_CODEX_FRECHET_CYCLE.md).

## 1. Exact rule and variables

There are four independent stopping laws, zero Never reward and canonical
own singletons (1,0,0,0). Nonpivot laws use F_N={0,…,N−1,Never}, N≥1.
The pivot's closed point is m=(x,λ,ν,α): head masses x, late FINITE mass
λ, Never mass ν, Σx+λ+ν=1, and 0≤α≤λ. For α>0 its late atoms
are α(1−α/λ)^k at N+k; α=0<λ is only a compactification point.

Write z_j for nonpivot Never masses, D=z₁z₂z₃, D_j=∏_(k≠0,j)z_k,
a_j=r_j({0}), and b_j=r_j({0,j}). A coupled point globally minimizes
original full repair objective L over m with the other laws fixed, while
each nonpivot maximizes original old-menu payoff with Never subsidy

    γ_j=β_j+D_j[b_jα−a_jλ]₊,             β_j≥0.

The source bound is L≤max_j(β_jz_j+D[b_jα−a_jλ]₊). All caps below
include every finite date and Never, not just the prescribed finite menus.

## 2. Zero closed value with λD=1 and no actual attainment

Use the existing production table: r₀(S)=1 if 0∈S, otherwise zero;
r₁(S)=1 if 0,1∈S, otherwise zero; r₂=r₃=0. Set all three nonpivots
Never and x=0, λ=1,ν=α=0, at any N≥1.

The original closed objective is L=0, hence globally minimal. Every old
finite response and original Never payoff of a nonpivot is zero. Since
all a_j=0 and α=0, Δ_j=0. Thus Never is an adjusted best reply for
every β≥0, and this is a coupled closed fixed point. Here λD=1.
Consequently λD≤f(L) with f(0)=0 is false at EVERY-fixed-point scope.
The distinct all-player Never mass is νD=0, consistent with νD≤L.

No actual pivot law attains L=0 against these opponents. Its own debt
is its Never mass. If that vanishes, the countable finite law has a
positive atom. Player 1 gains that atom by quitting at the same date,
whereas its prescribed payoff is zero. A positive first geometric atom
α' instead gives actual exploitability exactly α'→0.

This is the checked nonattainment result
`behavioral_repair_infimum_zero_not_attained` in
`UniformEquilibrium/Diagnostics/Quitting/PivotRepairNonattainedAllLaws.lean`;
the table and zero mass point are defined in `PivotRepairNonattainedZeroLP.lean`.
The extra observation is simply membership of this existing boundary point
in the new compensated correspondence. It supports its approximation clause,
not an objection to it, and does not exclude selecting a different point.

## 3. Actual bad VANISH fixed points at every deadline and every bonus

Use the source's VANISH table. For nonempty S, r₀(S)=1 if 0∈S and 2
otherwise. For cyclic j=1,2,3, r_j(S)=0 when j∈S, equals −1 when
j∉S and 0∈S, and otherwise equals
2·1_(pred(j)∈S)−1_(succ(j)∈S).

Let all three nonpivots Never. For EVERY pivot law its own payoff is
1−ν and full cap one, so d₀=ν. Each nonpivot's prescribed payoff is
−(1−ν) and full cap zero: all response payoffs are nonpositive and
Quit0 guarantees zero. The same identities hold on the closed LP domain.
Thus L=max(ν,1−ν), whose global minimum is 1/2.

Choose x=0 and λ=ν=1/2, with any α∈[0,1/2]. Here a_j=−1,b_j=0,
D_j=1, so Δ_j=1/2. Original Never pays −1/2; adjusted Never pays
β_j≥0. Every old finite action pays zero because it precedes the pivot's
late mass. These are coupled fixed points for EVERY N≥1 and every β≥0,
all with L=1/2. Choosing α=1/2 gives the ACTUAL finite pivot law that
quits at N with probability one half and otherwise Never.

At β=0 the sharp source estimate is attained:
D[b_jα−a_jλ]₊=1/2=L. This refutes an every-fixed-point decay claim,
not the minimum-over-all-fixed-points target. The reviewed good truncated
cycle still has values tending to zero along other points of the same rule.

## 4. Stopping point

Selection is essential even on the solved stress table, and small L does
not bound λD from above at every point. Neither test settles whether SOME
compensated fixed points have arbitrarily small L for every canonical table.
No new consumer, export, parameter search, or further research is asserted.
