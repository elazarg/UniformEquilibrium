# Recipient scaling: independent review and finite-player scope

## Current status

Identity: CODEX_BANACH_GATE. The frozen Fin4 candidate received a complete
independent ordinary-mathematical PASS in
[`CODEX_MORSE__RECIPIENT_SCALE_DEBT_RIGIDITY_SOURCE_REDUCTION__BY_CODEX_BANACH_GATE.md`](../feedback/CODEX_MORSE__RECIPIENT_SCALE_DEBT_RIGIDITY_SOURCE_REDUCTION__BY_CODEX_BANACH_GATE.md).
That record contains the full reconstruction, exact falsification attempts,
and named tracked declaration/file audit. No Lean checking or export occurred.

This notebook records one further scope observation. It is ordinary
mathematics, not independently reviewed or Lean-checked, and is not a claim
of unrestricted equilibrium existence.

## Standalone finite-player question

Let I be any finite player set with n≥2, let bounded real rewards r_i(S) be
specified for every nonempty coalition, and let all-Never pay zero. Each
player uses an independent complete stopping law on ℕ⊔{Never}; deviations
replace one entire law. Let K_r be the closure of actual prescribed-payoff
and full behavioral-cap pairs, a_i=B_i−U_i, and δ=inf_p Σ_i a_i(p)>0.

For any ε>0, can positive recipient scales θ_i in
(1−min(ε,1/2),1) produce a table r'_i=θ_i r_i such that all SUM-minimizing
pairs of K_(r') have one debt vector, and such that a supported earliest
unique cap at a produced marked minimum forces every cap to have the same
date?

The answer is yes. No Fin4 source spectra are needed for this statement.

## Dimension-free mechanism

The old chart uses μ=Σ_i p_i/n and densities bounded by n. The endpoint,
moving-reply, and old supported-reset arguments are unchanged, with bounded
products n^n. The singleton margin cited in the review is already stated for
an arbitrary finite player type. Thus the universal earliest-active-point
argument has exactly the same proof: a zero-mixture earliest point either
has a sure strictly-earlier owner and multiple upper caps for the other
n−1 recipients, or strict-late conditioning produces a true minimum with
one cap equal to its own singleton, contradicting that margin. With every
cap unique, the earliest point is finite and an isolated positive mixture
atom.

The debt image A of K_r is compact, nonempty and nonnegative. The function
W(θ)=min_(a∈A) θ·a is concave and Lipschitz. One-dimensional concavity and
Fubini applied to the finite union of n coordinate exceptional sets produce
arbitrarily close positive coordinate-regular weights. For every minimizing
a, the two supporting inequalities in direction ±e_i give
a_i=∂_i W(θ). Positive diagonal scaling carries K_r onto K_(r'), so every
SUM-minimizing pair of the final table has debts θ_i∂_i W(θ). Its gap stays
positive because W(θ)≥min_i θ_i δ.

At a produced all-unique marked minimum of that table, suppose an earliest
maximizing owner h has positive own atom at its cap τ. A signed reset toward
that existing atom fixes the other earliest caps by isolation. Every later
cap is fixed by positive affine rescaling of all replies above τ and a
compact lower gap. The SUM is affine and locally minimized, hence constant;
all reset pairs are original-carrier minima. Common debt vectors then give
d_h=(1−u)d_h, so d_h=0 and unique maximization forces q_h=δ_τ. This sure
earlier exit makes every putative later cap tie Never or the distinct finite
c. Thus all cap dates must be τ.

If cap dates are not all equal, every earliest maximizing owner therefore
has zero own point mass. If all later owners were supported, all unique cap
points would be isolated. A signed reset of any supported owner, now using
uniform isolated gaps for every other cap, would force that owner to be pure
at its own cap and to have zero debt. Later owners would then supply no
earliest mass, and earliest owners already have zero own mass there. This
contradicts the positive earliest mixture atom. Hence there is a later
unsupported owner as well. When all caps are isolated, every supported
owner is pure with zero debt, irrespective of cap order.

## What remains unproved here

The dimension-free statement retains the common-unique-cap branch. I have
not exported a general-n finite-contact producer or claimed that this
observation settles any player count. It extends the actual scale producer
and its supported-earliest consumer, rather than replacing a table by a
supplied weight or a supplied minimum as a hypothesis.

Concrete next check: independently verify the dimension-free marked
transport and singleton-margin application, then decide whether the
general-n contact endpoint can also exclude the common-cap branch. That is
a separate scope extension and does not change the frozen Fin4 review.
