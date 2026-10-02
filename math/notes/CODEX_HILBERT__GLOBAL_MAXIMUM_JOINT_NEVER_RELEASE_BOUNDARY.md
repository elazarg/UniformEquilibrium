# Joint Never-arm release at a true MAX-minimizing source: the remaining cap inequality

Author: CODEX_HILBERT.

Ordinary mathematical bounded test. No strict improvement or new producer
is proved. The one operation tested returns to the complete tail-versus-head
cap comparison already exposed by earlier splicing work. It is stopped here,
not promoted as a supplied-successful-splice theorem.

## Source and actual operation

Consider a canonical four-player table with |r_i(S)|≤M and own singletons
s=(1,0,0,0). Let m_N be the GLOBAL original full-exploitability minimum over
three nonpivot laws on F_N and the compact pivot repair domain. This is not
the minimum over compensated fixed points. If m_N↓m>0, the existing MAX
results give, after actual boundary implementation with error tending to
zero, a source sequence with

    E(p^N)→m,       d_i(p^N)→m,
    liminf_N (U_i(p^N)−s_i) ≥ m²/(64M)>0.

The actual implementations preserve U. No literal profile attaining m is
assumed. In particular the negative-payoff coordinate trap is not substituted
for these sources.

The joint operation retains every nonpivot's old finite part, but replaces
its Never arm by Quit at the new common date N with private probability
θ_j, and Never otherwise. The three coins are independent. All θ_j are
selected JOINTLY from [0,1]³, after which the pivot may be globally repaired
again. This changes several actual laws at once and exposes new calendar
responses; it is not a sequence of one-law objective decreases.

## Exact comparison before pivot reoptimization

Suppress N. Let z_j be nonpivot Never masses, D=∏z_j and D_i=∏_(j≠0,i)z_j.
Write λ for the pivot's finite mass after the cutoff, ν for its Never mass,
and w=λ+ν. The following displayed conditional interpretation assumes w>0;
the source hypotheses above do not themselves provide w>0 or D>0.

Let A_i be the old contribution to pure Never payoff from absorption before
N, and H_i the maximum old finite response payoff. Set a_i=r_i({0}) for
i≠0. The original pivot conditional tail has finite mass λ/w and Never
mass ν/w. Against it and the new nonpivot root θ followed by Never, let
v_i(θ) be the actual conditional prescribed payoff and c_i(θ) the FULL
conditional response cap. For c_0 the pivot is deleted and replaced freely.
Define

    Δ_i=w v_i−λa_i          (i≠0),
    Δ_0=w v_0−λ.

Every player's prescribed payoff changes by DΔ_i. The complete new caps are

    B'_i=max(H_i, A_i+D_i w c_i)             (i≠0),
    B'_0=max(H_0, A_0+D c_0).

Thus the original full objective of this actual comparison profile is

    max {
       max_(i≠0)[max(H_i,A_i+D_i w c_i)−U_i−DΔ_i],
       max(H_0,A_0+D c_0)−U_0−DΔ_0 } .                 (1)

These formulas include all old dates, every new and arbitrarily late date,
and Never. They follow by conditioning separately on the prescribed joint
survival event and the opponent-deleted survival event. The corresponding
coefficients are D and D_i w, not the same probability. They remain formulas
for suprema if a cap is not attained. A relaxed α=0<λ is first implemented
by an actual positive first atom; no conditional law is assigned to that
closed point.

The new nonpivot laws lie in F_(N+1), so the globally reoptimized pivot value
is no larger than (1). This is the correct use of inner optimality. It does
not imply that the bound (1) is below the source value.

## Why the proposed decrease is not obtained

A positive increase of each prescribed tail payoff is insufficient. To
lower all four almost-maximal debts uniformly, one must also dominate the
new terms D_i w c_i, and the pivot's independent term D c_0, on the SAME
chosen θ. Strict initial singleton-payoff margins constrain U_i, not these
conditional caps, the old finite response slack, or the joint tail weight D.
In particular no positive lower bound on the amount changed by this
Never-only operation has been extracted from true global minimality.

The exact remaining global assertion would be a table-derived choice of θ
and pivot repair giving a fixed positive drop along the actual minimizing
sequence. Equation (1) gives a sufficient numerical comparison for a chosen
θ, but no inequality forcing such a choice. Global minimality itself gives
the reverse lower comparison with m. Neither summing private gains nor
replacing cap changes by a quadratic remainder supplies the missing upper
comparison.

The narrow source check read the cap-switch/full-chord and frozen-cube
declarations in

- `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticCapSwitchFullChord.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/Frozen/ResetCube.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/Regression/FinFourCapSwitchAllProper.lean`.

Fixed-response mixed remainders can be quadratic while a supremum changes
at first order. The all-proper regression has no positive-minimum premise;
it blocks that estimate, not the present global-minimum hypothesis. The
inspected frozen reset-cube minimum theorem uses SUM debt, which must not
be silently substituted for MAX. The strengthened MAX source comes instead
from the all-player-tie and lowered-root-margin notes.

The complete head/tail formulas specialize those already in
[the tail-matching note](CODEX_HILBERT__COMPENSATED_FIXED_POINT_TAIL_MATCHING_OBSTRUCTION.md).
The earlier compensated support equations are deliberately absent here.
Dropping them restores the correct global source but does not orient (1).
The existing joint VANISH escape is an example at negative nonpivot payoffs,
not evidence that (1) improves a strictly positive global minimum.

No second variation of this same tail ansatz is pursued. The unresolved
source question is a genuinely global comparison changing more than the
terminal Never arms, or a proof that these specific arms necessarily carry
the required improving head/cap balance. Neither is established here.
