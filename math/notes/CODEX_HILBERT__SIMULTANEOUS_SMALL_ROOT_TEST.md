# Simultaneous small roots at an all-tied MAX minimum

Identity: CODEX_HILBERT. Ordinary mathematics. This bounded test reproduces
the already recorded harmonic contact condition, not a new producer or a
new export candidate. It does not resolve the all-tied strict-interior case.

## Question and exact full-cap calculation

Let I be finite and nonempty. Terminal rewards are bounded, Never pays zero,
players use independent stopping laws, and all behavioral deviations are
allowed. Let (U,B) belong to the closure C of actual payoff/full-cap pairs.
Suppose every debt is the same positive number m and put

    d_i=B_i−U_i=m,    s_i=r_i({i}),    κ_i=B_i−s_i>0.

Can one prefix a single simultaneous product root with small Quit
probabilities so that every full debt decreases?

For nonnegative rates a_i and sufficiently small ε>0 set q_i=εa_i.
Write Q_i(q_−i) for immediate Quit, and

    C_i(y;q_−i)=H_i(q_−i)+c_−i(q)y

for Continue followed by value y, where c_−i=∏_(j≠i)(1−q_j). The exact
prescribed payoff and unrestricted cap after prefixing are

    U′_i=q_i Q_i+(1−q_i)C_i(U_i),
    B′_i=max(Q_i,C_i(B_i)).

At q=0 the second branch beats the first by κ_i>0. Since there are finitely
many players, all these strict inequalities persist for sufficiently small
ε. In that neighborhood the full debt is therefore exactly

    d′_i=c_−i m+q_i[C_i(U_i)−Q_i].                 (1)

This selects the full Continue cap using a proved strict gap; it does not
discard a potentially active new immediate response. Never and all later
behavioral responses are included in C_i(B_i).

Let A=Σ_j a_j. Differentiating the finite polynomial expression (1) at zero
gives

    d′_i=m+ε[κ_i a_i−mA]+O(ε²).                 (2)

Indeed c_−i has derivative −Σ_(j≠i)a_j, and
C_i(U_i;0)−Q_i(0)=U_i−s_i=κ_i−m. The error is uniform over the finite
player set for any fixed rates.

## Exact first-order selection test

There exist nonnegative rates, not all zero, for which all first-order
coefficients in (2) are negative if and only if

    m Σ_i 1/κ_i > 1.                            (3)

For sufficiency take a_i=1/κ_i. Every coefficient then equals
1−mΣ_i1/κ_i<0; hence some sufficiently small actual product root strictly
lowers the full maximum debt. For necessity, divide each negative inequality
κ_i a_i−mA<0 by κ_i and sum. This gives A[1−mΣ_i1/κ_i]<0, so (3) follows.

If (U,B) is a GLOBAL minimum of max_i d_i over C, such a prefix is impossible:
fixed-root semantic prefixing is continuous and preserves C. Equivalently,
prefix sufficiently close actual approximants to obtain literal profiles
below the global infimum. Thus

    m Σ_i 1/(B_i−s_i) ≤ 1.                      (4)

If the inequality in (4) is strict, every nonzero nonnegative rate vector
has at least one strictly positive first-order debt coefficient. If equality
holds, balanced rates proportional to 1/κ_i make all first-order coefficients
zero. This test alone then says nothing about the second-order terms. It
also says nothing about finite-amplitude roots or a multi-date retiming.

## Scope and stopping point

The narrow search found (4) already stated as a known necessary contact
condition in `CODEX_BLINDSPOT__FIN4_GLOBAL_ROUTE_AUDIT.md`, Section 7, and
used by `CODEX_HAHN__CONTACT_CONE_SEMANTIC_BARRIER_ANSATZ.md`, Section 3.
The present calculation is a checked ordinary-math rediscovery of that
condition, not a novelty claim. HAHN's raw-superlevel counterexample concerns
noncarrier points, and supplies no contradiction to a genuine global minimum.

The exact source ingredients inspected are `quittingTerminalSemanticPrefix`,
`continuous_quittingTerminalSemanticPrefix`, and
`quittingTerminalSemanticPrefix_mem_carrier` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`, together with
the MAX singleton-margin declarations in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`.
No weighted-total-debt minimum has been substituted for a MAX minimum.

One next mathematical question, not pursued here: can a finite-amplitude
two-date retiming from the SAME genuine global minimum lower all full debts
when the harmonic inequality is strict? The first-order small-root rule
provides no such improvement, and no successful continuation is supplied.
