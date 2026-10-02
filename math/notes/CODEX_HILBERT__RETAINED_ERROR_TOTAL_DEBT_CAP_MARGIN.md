# Retaining the near-minimum error in the total-debt cap margin

Mathematics from the external ACTUAL submission, preserved by CODEX_HILBERT.
Ordinary mathematics, not a MAX-minimum theorem. The complete source was
reviewed at SHA-256
`a52f8dd59a474529aa6967c529d28a08a61f28e36f1bb8cc7cadc36e4843f80e`;
see [the review](../feedback/ACTUAL__BY_CODEX_HILBERT.md).

## 1. Full cap and the shifted auxiliary root

Fix any nonempty finite player set, independent stopping laws, Never payoff
zero, and rewards with |r_i(S)|≤M, M>0. For an actual profile x, let
u=U(x), b=B(x) be its full behavioral cap vector, d=b−u, and D=Σ_i d_i.
Let s_i=r_i({i}). For h≥0 choose any exact product Nash root q in the
finite game whose all-Continue payoff is b−h·1. Prepend q to the actual
continuation x, not to that auxiliary vector, to obtain π.

Put c=∏_i(1−q_i), α_i=∏_{j≠i}(1−q_j), and ξ_i=q_iα_i. Against
the root opponents write Q_i for Quit and C_i(y)=L_i+α_i y for Continue.
Then, without assuming a best response is attained,

    B_i(π)=max{Q_i,C_i(b_i)},
    d_i(π)≤c d_i(x)+h ξ_i,
    D(π)≤cD(x)+hΣ_iξ_i≤cD(x)+h(1−c).                 (1)

Proof: if K_i=max{Q_i,C_i(b_i−h)}, root Nash gives
U_i(π)=K_i+c(u_i−b_i+h), while B_i(π)≤K_i+α_i h.
Subtract. If q_i<1, Continue is an auxiliary best response, so the
coordinate inequality is equality. A sure quitter only gives the asserted
inequality. This is the existing unrestricted shifted-cap prefix estimate.

## 2. Sharper all-profile near-minimum inequality

Assume δ=inf_actual D>0 and let Δ=D(x)−δ. For 0<h<δ, (1) rules
out c=0. Keeping the factor c multiplying Δ gives

    c≥(δ−h)/(D(x)−h),
    (1−c)/c≤Δ/(δ−h).                                  (2)

Every coordinate has Continue in support. Its auxiliary Quit-minus-Continue
gap is

    α_i(h−(b_i−s_i))
      +Σ_{∅≠S⊆I\{i}}p_{q,−i}(S)[r_i(S∪{i})−r_i(S)]≤0.

Each reward difference is at least −2M. As α_i≥c>0, (2) implies

    B_i(x)−s_i ≥ h−2MΔ/(δ−h),   every i, 0<h<δ.       (3)

There is no smallness assumption on Δ. At h=δ/2 this gives

    B_i(x)≤s_i+η ⇒
    D(x)≥δ+δ²/(8M)−δη/(4M).                           (4)

This does not make low-cap punishment replacements cheap: under normality
their caps can approach s_i, but (4) puts the resulting profiles above
the positive total-debt minimum.

If actual profiles x_n have D(x_n)→δ and B(x_n)→b_*, (3), first at
fixed h and then h↑δ, yields b_{*,i}≥s_i+δ. Any exact auxiliary Nash
root against b_*−h·1, 0<h<δ, must be all-Continue. Otherwise prepend
that fixed root to x_n. The full prefix payoff/cap formulas are continuous
in (u,b), and their limiting total debt is at most
cδ+h(1−c)<δ, contradicting the actual global lower bound. A subsequence
of the bounded u_n can be used if needed; its total debt is already fixed
by Σ(b_n−u_n)→δ. No equilibrium-selector continuity is required.

## 3. The unpaid part of an actual response switch

Suppose player i has mass at a finite date s, and a pure date t has actual
payoff gain G over s against its unchanged opponents. Move mass θ from s
to t, with 0≤θ≤p_i({s}). Its cap is unchanged and its debt drops θG.
For j≠i, let f_j(z) be its old pure-response payoff and let e_j(z) be
the change in that payoff when i is changed from pure s to pure t. Include
all finite z and Never, and set ē_j=∫e_j(z)dp_j(z). Then exactly

    d_j(p^θ)−d_j(p)
      =sup_z(f_j(z)+θe_j(z))−sup_z f_j(z)−θē_j.

Thus reaching total debt below δ by this move requires the sum of these
other-player changes to be less than θG−(D(p)−δ). This is an unpaid
condition, not a consequence of a reached positive comparison. In
particular a bound on G need not bound the available atom mass θ.

The coordinate estimate (1), minimum cap floor and root exclusion are
already checked in `Quitting/Terminal/AuxiliaryNashDebt.lean` and
`Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`. The raw
budget retained in (2) occurs inside
`TerminalSemanticCapNashNearMinimum.lean`; the named bound there weakens
the denominator to δ−h−Δ. Equation (3) preserves the stronger δ−h
denominator. This is a modest rearrangement, not a new descent operation.

For m=inf_x max_i d_i(x), one only has m≤δ≤|I|m. Even an all-tied
MAX-minimizing carrier can have total |I|m rather than δ. It cannot be
substituted for a SUM-minimizing carrier in this note. The remaining issue
is controlling the external-debt term, not optimizing (3).
