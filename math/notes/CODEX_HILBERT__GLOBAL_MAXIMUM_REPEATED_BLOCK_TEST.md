# Repeating a finite MAX candidate exposes a rescaled Never cap

Author: CODEX_HILBERT.

Ordinary-mathematics bounded test. The complete repetition formula is
already present in the source chains identified below. Its application to
a global MAX minimum gives only a necessary rescaled-Never inequality,
not a new calendar-descent producer. This particular mechanism is stopped
at that limitation; no exact compensated fixed-point condition is imposed.

## 1. A direct selection operation

Fix a canonical four-player quitting game, bounded signed terminal rewards,
Never payoff zero, and own singleton vector s=(1,0,0,0). Every player uses
an independent law on {0,…,n−1,Never}. All caps test arbitrary complete
behavioral replacements, equivalently every pure finite date and Never.
Let U_i and B_i be its prescribed payoff and full cap, and let E=max_i(B_i−U_i).

The candidate operation repeats the profile's finite behavioral hazard
block K times, resampling independently within each successive block on
survival, and then uses Never. It may choose K by minimizing ORIGINAL full
E. This expands the calendar, changes the product laws, and requires no
return to an exact finite-game Nash or compensated fixed-point set. It does
not assume a supplied successful continuation.

Write z_i for the source Never mass and set

    R=∏_i z_i,       c_i=∏_{j≠i}z_j.

Let W_i be the source's pure Never payoff and F_i its maximum pure response
payoff among dates 0,…,n−1. Its full source cap is

    B_i=max(F_i,W_i,W_i+s_i c_i).

Here R is the probability of surviving a prescribed block; c_i is survival
when i deletes its own stopping rule. They cannot be interchanged.

## 2. The complete infinite-repetition formula

Assume R<1 and c_i<1 for each player. Infinite repetition is an actual
independent periodic profile and has prescribed payoff

    U_i^∞=U_i/(1−R).                                  (1)

Let f_i(t) be the original pure response at offset t<n. A response in
block k at that offset gives exactly

    W_i(1−c_i^k)/(1−c_i)+c_i^k f_i(t).                 (2)

Indeed an earlier opponent block contributes its unconditional absorption
reward W_i, with each further block discounted by the deleted survival
c_i. Never gives W_i/(1−c_i). Each finite value in (2) is a convex
combination of f_i(t) and that Never value. Thus the complete cap is

    B_i^∞=max(F_i,W_i/(1−c_i)),
    E^∞=max_i {max(F_i,W_i/(1−c_i))−U_i/(1−R)}.         (3)

This checks every finite response, including arbitrarily late blocks,
as well as Never. It is not just a comparison of current endpoints.

The finite K-copy profile has payoff U_iΣ_{k<K}R^k. Its finite responses
inside those blocks are (2), its Never value is
W_i(1−c_i^K)/(1−c_i), and every finite response after those blocks adds
s_i c_i^K to that value. Consequently its FULL exploitability converges
to (3). A strict decrease in (3), if available, therefore gives an actual
finite-calendar strict competitor, not merely an infinite limit.

If c_i=1, its opponents never quit in any block. Then W_i=0 and its full
cap is max(s_i,0); one must not divide by 1−c_i. If R=1, all prescribed
players Never and (1) is inapplicable. These cases are separate, not
automatic zero-over-zero certificates.

## 3. What true global MAX minimality contributes

Suppose the actual finite source attains the unrestricted global minimum
m>0, all U_i>0, and 0<R<1. Its positive canonical minimum's known strict
singleton margins exclude c_i=1: otherwise all of i's opponents Never,
and U_i=s_i(1−z_i)≤s_i. Thus the denominators in (3) are positive.

Because F_i≤B_i≤U_i+m,

    F_i−U_i/(1−R)≤m−U_i R/(1−R)<m.                    (4)

Global minimality prevents the actual repeated profile from having E^∞<m.
Therefore (3)–(4) force at least one player i to satisfy

    W_i/(1−c_i)−U_i/(1−R)≥m.                          (5)

Equivalently,

    W_i≥(1−c_i){m+U_i/(1−R)}.                         (6)

This is the exact remaining obstruction, not its solution. The source cap
bound W_i≤U_i+m does not imply the reverse of (5). Its scaling involves
c_i, while the prescribed payoff scaling involves R. The identities
therefore do not orient a new decrease, even after the current finite
candidate was selected by a global original objective rather than by an
auxiliary equilibrium restriction.

The statement is deliberately conditional on an ACTUAL finite global
minimum and positive R. A compact semantic minimum may not have such a
realization, and near-minimizer Never masses or deleted survivals need not
have uniform positive gaps from the problematic boundaries. No carrier
actualization or horizon-uniform inequality is inferred here.

For a finite-domain global minimum m_n, (3) instead gives the elementary
upper comparison with larger calendars through its actual K-copy profiles.
It supplies a descent only when the displayed new cap is already small;
there is no proof that global minimization at the old calendar ensures
that condition. Treating this supplied-cap test as a producer would leave
the main question unchanged.

## 4. Exact overlap and stopping point

The narrow lookup found the same finite block cap recursion and its
incentive-preservation failure in
[RENY's global finite-Nash reach test](CODEX_RENY__GLOBAL_FINITE_NASH_REACH_MINIMIZATION.md),
Section 9. That note's exact global counterexample concerns minimum reach
among finite approximate Nash laws, not minimum original MAX debt; its
objective must not be silently substituted here.

The repeated-opponent pure-response formula is also part of the exact
finite-only punishment argument in
[the normalization proof](CODEX_RENY__SINGLE_PIVOT_ZERO_NEVER_NORMALIZATION_DRAFT.md),
Part D. The checked full semantic splicing declarations
`quittingTerminalSemanticPair_literalRootStack_eq_wordPrefix` and
`quittingFiniteRootWordPayoff_sub_eq_jointSurvival_mul` in
`UniformEquilibrium/Quitting/Root/FiniteWordSemanticSplice.lean` retain the
same joint/deleted coefficient distinction. The global minimum input used
in Section 3 is the all-player tie/strict-margin surface preserved in
`CODEX_HILBERT__GLOBAL_MAXIMUM_MINIMUM_ALL_PLAYER_TIES.md` and
`CODEX_FRECHET_CYCLE__GLOBAL_REPAIR_LOWERED_ROOT_MARGIN_TEST.md`.

Thus (5) is only an immediate application of known response semantics to
a stricter objective hypothesis, not a new branch elimination. No new
producer was identified in this repeated-block test. The operation is not
expanded into additional retry parameters.

One surviving genuinely global question is whether one can change the
opponent laws and reselect the pivot so that the rescaled Never caps are
controlled without paying a larger full cap elsewhere. Merely supplying
that cap control, or averaging profiles with a shared random index, would
not answer it. No such construction is claimed here.
