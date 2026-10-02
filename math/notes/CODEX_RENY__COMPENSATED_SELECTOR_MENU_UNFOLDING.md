# Exact menu unfolding and the compensation budget

Author: CODEX_RENY. Ordinary mathematical proof draft, not independently
reviewed or newly checked in Lean.

This note tests renewal of the
[late-cap-compensated selector](CODEX_RENY__LATE_CAP_COMPENSATED_NEVER_SELECTOR.md).
Unfolding the SAME geometric pivot law into a longer finite menu preserves
its global original repair optimality. However, the recalculated Never
compensation falls. Exact old best replies can be restored by transferring
that loss to the extra bonus, but this changes the permitted bonus budget
and leaves the original full value unchanged. At zero extra bonus, EVERY
positive-value literal fixed point with positive first late atom fails
unchanged one-date embedding. The nonattained zero-first-atom boundary
does embed. These claims do not settle minimum-value selection after
re-equilibration at the larger menu.

## 1. Fixed data and the selected-value question

There are four players with independent stopping laws on ℕ∪{Never}.
The first finite quitting coalition S pays r(S), all Never pays zero,
|r_i(S)|≤M, and own singletons are (1,0,0,0). Other reward entries are
arbitrary signed reals. Every cap includes all behavioral replacements,
equivalently all pure finite times and Never.

For N≥1 the nonpivot laws p_j use F_N={0,…,N−1,Never}. Set

    z_j=p_j(Never),   D=∏_{j=1}^3 z_j,
    D_j=∏_{k∈{1,2,3}\{j}}z_k,
    a_j=r_j({0}),     b_j=r_j({0,j}).

The pivot closed domain has coordinates

    m=(x_t:t<N; λ,ν,α),
    x_t,λ,ν≥0,   Σx_t+λ+ν=1,   0≤α≤λ.

Here λ is late FINITE mass and ν is Never mass. For α>0 its late law
is α(1−α/λ)^k at N+k. If λ=0 it has no late finite mass. The face
α=0<λ describes the closed LP infimum convention, not an actual law.

Write A_j for the early absorption contribution when j Never, and

    W_j=A_j+D_j a_jλ,    C_j=A_j+D_j b_jα,
    Δ_j=[C_j−W_j]₊=D_j[b_jα−a_jλ]₊,
    γ_j=Δ_j+β_j,        0≤β_j≤η.

Let L_N(m,p) be the ORIGINAL full pivot-repair LP objective: it is the
maximum of zero, pivot debt, and every nonpivot gain from a head date,
W_j, or C_j. It is the full behavioral value when m is literal and its
minimum is the unrestricted pivot-repair infimum on the closed face.

A compensated fixed point satisfies

    m∈argmin_{m'}L_N(m',p),
    p_j maximizes U_j(m,q_j,p_−j)+γ_j q_j(Never).

The source theorem proves this set nonempty compact for every N,β.
Let c_N(η) denote the minimum of L_N over ALL β∈[0,η]^3 and ALL such
fixed points. The actual open target is arbitrarily small c_N(η), with
N selectable for every positive η and desired full error. There is no
assumption that c_N(η) is monotone in N or that nearby fixed points
exist after adding an action.

## 2. Exact full-debt residual, including all support faces

At any compensated fixed point let

    V_j^aux=U_j+z_jγ_j

be the maximal subsidized finite-menu value. The source proof shows
that every original full response endpoint is at most V_j^aux.
If z_j<1, some finite action has positive prescribed mass. It receives
no subsidy and has value V_j^aux. Therefore it attains the FULL cap,
and

    d_j=z_jγ_j=z_jΔ_j+z_jβ_j,       if z_j<1.             (1)

This includes z_j=0. If z_j=1, then U_j=W_j, and the full cap includes
max(W_j,C_j)=W_j+Δ_j, while remaining at most W_j+γ_j. Hence

    Δ_j≤d_j≤Δ_j+β_j,               if z_j=1.             (2)

Every supported finite action is consequently a full best reply,
whether or not Never is also supported. Only prescribed Never can
contribute to that player's original debt.

The global pivot minimum cannot have the pivot as its sole positive
maximal debtor: a small mixture toward a pure pivot best response would
then reduce the original maximum. Thus L_N=max(d_1,d_2,d_3). Combining
(1)–(2), and defining

    K(m)=max_{j=1,2,3}[b_jα−a_jλ]₊,

gives the sharper all-selector bracket

    D K(m) ≤ L_N(m,p) ≤ D K(m)+η.                        (3)

At β=0 this is the exact identity

    d_j=z_jΔ_j,       L_N=D K(m).                        (4)

Equations (1)–(4) apply to the closed LP debts as well as literal
profiles; boundary actualization is still only approximate in full
value. They do NOT identify the objective with λD. In particular K
can vanish while λD is positive. The cruder λD estimate is sufficient
for smallness but cannot replace the actual selected-value objective.

## 3. One-date embedding preserves global pivot optimality

Define c=1−α/λ when λ>0 and c=1 when λ=0. Embed the nonpivot laws
into F_(N+1) by giving the new action N zero mass. Define the unfolded
pivot point by

    x'_t=x_t (t<N),   x'_N=α,
    λ'=cλ=λ−α,       ν'=ν,       α'=cα.                  (5)

It is feasible, including c=0, λ=0, and α=0<λ. For α>0 this is
literally the SAME entire pivot law: its first geometric atom moves
into the displayed head and the remaining atoms keep their dates.
No nonpivot law or original payoff changes.

The endpoint identities can also be checked without assuming literal
attainment:

    A'_j=A_j+D_j a_jα,
    W'_j=W_j,
    C'_j−W_j=c(C_j−W_j),
    Δ'_j=cΔ_j.                                          (6)

The NEW pure finite response at date N is exactly C_j. All old finite
and Never responses remain unchanged. The new late endpoint C'_j is
between W_j and C_j. Thus every full cap and the objective remain
unchanged:

    L_(N+1)(m',p)=L_N(m,p).                              (7)

For the pivot, the added head response N is its old late response,
already one of the old cap candidates. Its prescribed payoff is also
unchanged by the mass identity α+λ'=λ. These observations verify all
four coordinates of (7), not just the nonpivot cap formulas.

Crucially, (7) preserves GLOBAL pivot optimality. Both LP minima, at
N and N+1, equal the infimum over ALL pivot behavioral laws against
the SAME three actual nonpivot laws. That infimum does not depend on
which support deadline is used to describe those laws. Therefore an
old global minimizer maps to a new global minimizer. This is not an
unsupported claim that a restricted geometric family remains optimal.

At α=0<λ, (5) puts zero mass at the new head date and retains λ,ν,α.
The new finite response is A_j, already the old C_j. This proves (7)
directly at the nonattained face too. It does not realize the positive
late mass as a fictitious actual law.

## 4. The precise lost best response and its repair

Keep β fixed under (5). By (6), the subsidized Never payoff falls by

    (1−c)Δ_j,

whereas every old finite payoff stays fixed. The new finite response
C_j was already bounded by V_j^aux, so it introduces no value beyond
the OLD full cap. Nevertheless its availability can expose the lost
Never compensation.

At β=0, unchanged best replies survive if and only if

    z_j(1−c)Δ_j=0 for every j.                           (8)

For necessity, suppose z_j>0 and (1−c)Δ_j>0. Then Δ_j>0 and the new
finite action N has value C_j=W_j+Δ_j. Newly compensated Never pays
W_j+cΔ_j<C_j. A law putting positive mass on Never is not a best
response. This argument covers z_j=1 as well as mixed support; it does
not rely on an old supported finite action.

For sufficiency, if z_j>0 then its subsidy is unchanged by (8), and
the newly added finite action was already dominated by its old maximal
subsidized value. If z_j=0, every prescribed action is finite and has
value V_j^aux; decreasing the unused Never action and adding an old
full-cap-bounded finite action cannot destroy optimality.

It follows from (4) that if β=0, α>0 and L_N>0, unchanged one-date
embedding ALWAYS fails for at least one nonpivot. Global inner
optimality and every old full response bound still hold. Thus the
failure is not a missed late test in the original objective or loss
of global pivot optimality; it is precisely the recalculated outer
objective. When α=0 (including λ=0), c=1 and the embedding succeeds
at the same β on every support face.

There is an exact repair at a possibly larger bonus budget:

    β'_j=β_j+(1−c)Δ_j.                                  (9)

Now Δ'_j+β'_j=Δ_j+β_j, so every original subsidized menu payoff is
unchanged, and the new finite action is still bounded by V_j^aux.
Thus (5),(9) give a compensated fixed point at N+1 with the SAME full
value L_N. The additional β is nonnegative but need not fit the
original ceiling η. This is an embedding theorem, not descent.

## 5. Repeated unfolding is a telescoping budget, not progress

After k≥0 unfolded dates, the identical-law representation has

    λ_k=λc^k,    α_k=αc^k,
    Δ_j,k=c^kΔ_j,
    β_j,k=β_j+(1−c^k)Δ_j.                               (10)

Its added head atoms are α,αc,…,αc^(k−1). At c=0 the whole tail
has already entered the head after the first step; at c=1 there is no
change. Formula (10) follows either by induction from (5),(9), or by
summing the transferred increments (1−c)c^ℓΔ_j.

The total numerical subsidy γ_j is conserved. So are the actual
profile, its unrestricted caps, and its full exploitability. The
loss of compensation has merely been transferred into β. For a
literal positive tail c<1, the eventual bonus increase is Δ_j, not
an arbitrarily small quantity obtained by waiting longer.

For example, (5),(9) yield a comparison with an enlarged allowance

    c_(N+k)(max_j {β_j+(1−c^k)Δ_j}) ≤ L_N(m,p),           (11)

for this particular source point. They do not yield c_(N+k)(η)≤c_N(η)
at the original allowance, and still less any strict contraction.
Failure of unchanged embedding does NOT prove that such a minimum
comparison is false: another fixed point at the larger menu might
have a smaller value. Re-equilibration is exactly the unproved step.

## 6. A literal and a closed boundary test

On the VANISH table, r_0(S)=1 if 0∈S and 2 otherwise. For nonpivot
j, r_j(S)=0 if j∈S; otherwise it is −1 if 0∈S, and
2·1_(pred(j)∈S)−1_(succ(j)∈S) if 0∉S, with cyclic labels 1,2,3.
Let all three nonpivots choose Never. At every N, choose no pivot head,
λ=ν=1/2, and arbitrary α∈[0,1/2].

Against these laws the pivot's cap is 1, its payoff is 1−ν, and its
debt is ν. Each nonpivot's payoff is −(1−ν), and its full cap is zero
(Quit0 yields zero; all rewards it can receive here are nonpositive).
Thus its debt is 1−ν. The unrestricted pivot minimum is exactly 1/2,
attained by EVERY pivot law with ν=1/2, including every displayed α.

At the specified points, W_j=−1/2, C_j=0, Δ_j=1/2. Every old finite
action pays zero; subsidized Never pays β_j. These are fixed points
for every nonnegative bonus vector. This exact all-Never guardrail was
independently supplied by FRECHET while reviewing the producer theorem.

Take β=0 and α=1/2. Unfolding moves the finite pivot atom to head
date N and leaves λ'=0. The old numerical compensation disappears.
The newly subsidized Never value is −1/2, while Quit N gives zero;
the source is not a new fixed point. Restoring β'=1/2 repairs it but
leaves full value 1/2.

By contrast, at α=0<λ the closed point embeds indefinitely at β=0
and retains the same positive value 1/2. Therefore unchanged boundary
embedding is not a small-value producer either. Neither test shows
that all fixed points are bad or that their minimum is positive for
all large menus. The known bonus-dependent good branch remains.

## 7. Dependencies and exact next question

The full-cap and fixed-point ingredients are from the owned compensated
selector note, frozen at SHA-256
`22a63c4acbe3b67f20bc2c70f675bded8b9a8bfb211e4cc74fb94904cabdeea0`.
The substantive production bridge needed in Section 3 is
`exists_objective_minimizer_eq_behavioral_infimum` in
`UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean`:
the inner optimum is independent of which valid finite support deadline
describes the unchanged nonpivot laws. Endpoint definitions and the
zero-first-atom convention are those in `PivotRepairFiniteLP.lean` and
`PivotRepairBehavioralApproximation.lean`. These are source dependencies,
not newly implemented declarations.

This note establishes an exact comparison map and its failure at a fixed
bonus budget. It does not produce a new equilibrium class, a smaller
full value, a fixed-point continuation theorem, or an algorithm. The
next genuine source problem is to change the nonpivot laws and
re-equilibrate at the larger menu while improving the ORIGINAL minimum
L under arbitrarily small permitted β. Preserving the old laws and
rewriting their geometric tail cannot do that by itself.

## 8. Existing singleton-stationary screen on the positive-gap class

The sharper residual in (3) has a useful interpretation under an ACTUAL
positive terminal-gap premise. Define, directly from the fixed rewards,

    F(h)=max_{j=1,2,3}[b_j h−a_j]₊,   0≤h≤1.             (12)

For 0<h≤1, let only the pivot quit, independently at each date with
hazard h, while every nonpivot Never quits. This stationary profile
absorbs at {0} almost surely and has payoff r({0}). The pivot's full
cap is one, so its debt is zero. A nonpivot j's response at time t has
payoff

    a_j+(1−h)^t(b_jh−a_j),

and Never pays a_j. The complete cap is max(a_j,b_jh), attained at
Never or time zero. Its exact full debt is [b_jh−a_j]₊. Therefore this
ACTUAL stationary profile has unrestricted exploitability F(h).

Suppose Γ>0 is a terminal exploitability gap for the whole table:
EVERY actual product behavioral profile has E≥Γ. Then F(h)≥Γ for
every 0<h≤1, and continuity of the explicit finite maximum (12)
extends that inequality to h=0. This is continuity of F, NOT continuity
of the profile's terminal payoff at zero hazard. At h=0 the actual
all-Never profile has payoff zero and pivot debt one; it need not have
exploitability F(0).

For λ>0 the exact algebra is

    K(m)=λF(α/λ),

including the closed α=0 face. If λ=0 both K and λD vanish. Thus in
the stated positive-gap class every compensated fixed point obeys

    ΓλD ≤ D K(m) ≤ L_N(m,p) ≤ η+2MλD.                  (13)

This comparison is false for arbitrary tables without the gap premise.
It neither furnishes that premise nor makes the residual small. It
does explain why a solved-game example with L=0 and λD>0 is not a
counterexample to using λD as a comparable quantity INSIDE an actual
hard-table argument. The objective of global selection remains L.

This is an existing singleton-stationary screen, not new UE existence
mathematics. The narrow exact source checks are
`quittingContinuationBestResponseValue_stationary_eq_fullRateUnilateralCap`
and `quittingContinuationBestResponseValue_stationary_eq_max_quitNow_never`
in `UniformEquilibrium/Quitting/Stationary/CompleteBehavioralCap.lean`;
`quittingTerminalPayoff_soloStationary`,
`quittingStationaryUnilateralCap_solo_other`, and
`quittingTerminalPayoff_update_solo_owner_le` in
`Quitting/Boundary/Exceptional/TailFallback.lean`; and the literal
Quit-versus-singleton/collision mixture
`quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix` in
`Quitting/Stationary/SingletonStationaryRoot.lean`. Their specialization
gives the displayed full caps, including the pivot's noncontracting
opponents. The separate induced-Nash singleton-base owner-floor gap in
`QuittingTerminalExploitabilityWitness.exists_prescribedOwner_stationaryHandoff`
has a different source domain; no identification with that induced
carrier is needed here. These were static source checks, not new builds.

## 9. Delaying the tail is a different, conditionally valid embedding

There is another map which does NOT preserve the literal pivot law.
Give the new head date N zero mass, retain λ,ν,α, and keep the same
three nonpivot laws. This delays the pivot's entire geometric finite
tail by one date. The old prescribed payoffs and old finite response
tests are unchanged. A_j,W_j,C_j and therefore Δ_j stay unchanged.
However the new finite nonpivot test at N is now A_j: a player can
quit before the delayed pivot tail instead of colliding with its first
atom.

If A_j≤B_j for every nonpivot, no full cap increases. The new inner
point has the same objective and is globally optimal against unchanged
p by the unrestricted-infimum argument in Section 3. The old outer
objectives are unchanged, and the new finite response is bounded by
the old full cap, hence by V_j^aux. Thus this map gives a new fixed
point at the SAME bonus budget and SAME L. A sufficient raw condition
at the source is max(a_jλ,b_jα)≥0 for every j. In particular this
holds on VANISH, where b_j=0, so the same-law failure in Section 4 is
not a no-go for every menu embedding even on that fixture.

Here is an exact signed-table failure of this DIFFERENT map. At N=1,
use r_0(S)=1 if 0∈S, and 3/2 otherwise. For j∈{1,2,3} use cyclic
predecessor and successor labels and set

    r_j(S)=−1 if 0,j∈S;
            0 if j∈S and 0∉S;
           −2 if 0∈S and j∉S;
            2·1_(pred(j)∈S)−1_(succ(j)∈S) otherwise.

This is a complete canonical table with M=2. Take p_j=(δ_0+δ_Never)/2
and the pivot point

    x=6/29,   λ=α=22/29,   ν=1/29,   β=0.                (14)

For these fixed nonpivot laws, ANY feasible pivot point satisfies

    B_0=23/16,
    d_0=1/8+5x/16−λ/8,
    A_j=1/2−5x/2,
    W_j=A_j−λ/2,      C_j=A_j−α/4,
    U_j=1/4−7x/4−λ/4.

The finite time-0 gain and first-late gain are respectively

    g_f=−1/4+3x/4+λ/4,
    g_ℓ=1/4−3x/4+λ/4−α/4 ≥ 1/4−3x/4.

Their nonnegative weighted combination is an exact global LP certificate:

    (12/29)d_0+(6/29)g_f+(11/29)g_ℓ ≥ 11/116.           (15)

The weights sum to one. Substituting α≤λ gives the inequality by
cancellation of the x and λ coefficients, so (15) covers EVERY pivot
law through the complete LP, not a few selected times. Equality holds
at (14), and every full debt there is 11/116. Each nonpivot's finite
payoff and compensated Never payoff both equal −6/29. Thus (14) is
a genuine compensated fixed point with a GLOBAL original pivot repair.

At this point A_j=−1/58 exceeds its old full cap B_j=−6/29. Delaying
the pivot tail exposes that new finite value and raises each nonpivot
debt from 11/116 to 33/116. Their original prescribed payoffs are
unchanged. Thus neither inner optimality nor outer best responses are
preserved by the delayed-tail map on arbitrary signed tables.

This is a failure of one exact operation at a valid source, NOT a claim
that (14) minimizes over all nonpivot laws or over all fixed points.
It does not falsify monotonicity of c_N(η), and is not a counterexample
to uniform equilibrium: the usual three-nonpivot cyclic equilibrium
with pivot Never still works on this table. The signed entry condition
above and the lack of descent must therefore both remain explicit.

## 10. A joint move lowers full value but leaves the fixed-point class

This tests a different operation: change ALL three nonpivot tails, then
globally optimize the ENTIRE pivot law. It begins at the true minimum
over all corrected fixed points for one menu, not an arbitrary bad branch.

Use the VANISH table of Section 6. HILBERT's independently developed
[one-menu selection calculation](CODEX_HILBERT__COMPENSATED_FIXED_POINT_TAIL_MATCHING_OBSTRUCTION.md)
proves the following source: there is a unique t∈(1/3,3/8) with

    D=(1−t)³=t/(1+t),

and the minimum over ALL N=1, β=0 compensated fixed points is
m=D(1−D)>0, attained by

    p_j=tδ_0+(1−t)δ_Never,
    μ_0=Dδ_0+(1−D)δ_1.

The proof there derives symmetry rather than restricting the selector
to symmetric laws; this exact source fact is used, not re-audited here.

Set z=1−t and replace each nonpivot Never arm by date one:

    p'_j=tδ_0+zδ_1.

Now globally reoptimize the pivot repair LP at N=2 against p'. Unlike
the fixed-pivot splice, this operation DOES reduce actual unrestricted
exploitability. A concrete comparison pivot is

    μ'_0=(δ_1+δ_Never)/2.

Its cap is two; its prescribed payoff is 2−D/2, since pure date one
pays 2−D and Never pays two. Thus its debt is D/2. For each nonpivot,
pure date zero pays zero, pure date one pays t, and every later date
and Never also pays t. For the last assertion, the contribution from
opponent absorption at zero is t. On the event both other nonpivots
stop at one, the pivot's two equally likely choices give respectively
−1 and +1 to a continuing nonpivot, so their additional contribution
cancels. There are no surviving opponents beyond date one. The original
prescribed payoff is zt, and its full debt is consequently t². Hence

    E(μ'_0,p')=max(D/2,t²)<D(1−D)=m.                    (16)

Indeed D<1/2 gives the first strict comparison. The second is equivalent
to t(1+t)²<1, which follows from t<3/8 and
(3/8)(11/8)²=363/512<1. Every global pivot optimizer against p' has
value no greater than this genuinely smaller bound.

Nevertheless NO globally optimizing pivot against these new nonpivot
laws yields a corrected fixed point, for ANY nonnegative bonus vector.
To see this, write X and Y for arbitrary pivot masses at dates zero and
one. Every later finite date and Never pays the pivot two. Its full cap
is two and its debt is exactly

    d_0=X+DY.

If the full repair objective were zero, X=Y=0. But with the pivot
absent until after date one, a nonpivot has prescribed payoff zt and
a late/Never response payoff t+z², giving debt t²+z²>0. Thus the closed
LP has no zero point. Its attained minimum is strictly positive.

On the other hand all three p'_j have Never mass zero. At a corrected
fixed point the source bound gives every nonpivot full debt zero,
independently of β, and global pivot optimality then forces L=0.
This contradicts the preceding fixed-opponent calculation. The failure
therefore covers EVERY global repair optimizer after the joint move,
not merely the explicit comparison pivot μ'_0.

This is a precise failure of the proposed renewal step: actual full
value decreases and the pivot is globally reoptimized, but the new
finite supports cannot satisfy the outer best-response equations. It
does not prove that reselecting those supports cannot give a lower
fixed-point value, and it does not disprove c_2(η)≤c_1(η). The missing
inequality is still a comparison with the minimum over NEW fixed points,
not with the minimum over all pivot repairs of one improved triple of
laws. No uniform-in-N approximate-to-exact fixed-point transfer follows.
