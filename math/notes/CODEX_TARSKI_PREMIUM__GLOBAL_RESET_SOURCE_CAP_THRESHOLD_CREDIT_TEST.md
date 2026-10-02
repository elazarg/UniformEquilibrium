# Global-source reset credit and the finite cap-threshold block

Author: CODEX_TARSKI_PREMIUM.

Status: completed bounded composition test, ordinary mathematics not checked
in Lean. Section 2 proves an anchor-preserving auxiliary step at every literal
pinned reset source and verifies that the new actual ray can restart from its
output. This is a source-interface refinement, NOT a new uniform-equilibrium
consumer. Sections 3–4 state the precise attempted global-source lemma and
derive the exact horizontal credit inequality still needed. The lemma is
unproved. No arbitrary-source counterexample with zero global minimum is
presented as refuting its positive-global-minimum hypothesis. No export.

## 1. Exact source and mathematical target

There are four players and a bounded real reward table on all nonempty
quitting coalitions, with |r_i(S)|≤M and M>0. Never pays zero. Every profile
is an actual independent behavioral profile on the unique live history;
every unilateral deviation may replace the complete stopping law. Define

    U_i(p), B_i(p), d_i(p)=B_i(p)−U_i(p), D(p)=Σ_i d_i(p),
    s_i=r_i({i}), L_i(p)=B_i(p)−s_i.

All caps are unrestricted. Let K be the closure of all actual (U,B) pairs
and m=min_K D. Whenever m>0 is assumed below, it is this GLOBAL semantic
minimum, not an infimum over one exact ray, one owner, anchored sources,
attained-cap profiles, or a finite timing menu.

The newly read source gives literal reset children z with:

    an anchor a quitting surely by a finite deadline T,
    d_a(z)=0,
    an observer j≠a with d_j(z)≥δ>0,
    |B_j(z)−s_j|≤δ/4,
    Quit0 attaining B_j(z).

The zero anchor is the previously installed cap owner. In particular it
must not be confused with the observer j, whose debt is positive.
The direct restart theorem constructs an actual exact-prefix ray from z.
Its all-positive-survival arm retains j's initial Quit0 cap; the last-zero
arm instead supplies the unique sure quitter's bounded finite-or-Never cap
at the literal last-zero child. The latter cap is NOT promised to be Quit0.

The question is whether these literal source facts, combined with the frozen
[finite cap-threshold block](../exports/FINITE_CAP_THRESHOLD_BLOCKS_AND_WEAK_EXCLUSION_SELECTION.md),
give a renewed decrease from a globally near-minimal PARENT source after the
next cap installation, rather than only a decrease from its off-minimum child.

## 2. A protected-anchor auxiliary row really does restart

Here is a complete source-level composition. It applies in any finite player
count, without a preemption hypothesis or a positive global minimum.

Proposition. Suppose z has a finite sure deadline T for a, d_a(z)=0, and
some j≠a satisfies d_j(z)≥δ>0 and |L_j(z)|≤δ/4. Put D=D(z). There is a
literal one-row prefix y=q::z such that

    d_a(y)=0,  a quits surely by T+1,
    D(y)≤D−κ(D),          κ(D)=D²/(16M+2D)>0.                (1)

Proof. Set h=D/2 and choose the finite auxiliary game's continuation as

    v_a=B_a(z),           v_i=B_i(z)−h  (i≠a).

Equivalently, h_a=0 and h_i=h for i≠a. Choose one exact product Nash root q
of this finite Boolean game. For its joint survival c, absorption A=1−c,
opponent survival β_i, and sole-quitter probability π_i=q_iβ_i, write
H_i for the nonempty-opponent Continue contribution and Q_i for Quit.
Let w_i=q_iQ_i+(1−q_i)(H_i+β_i v_i). Exact finite Nash means
w_i=max(Q_i,H_i+β_i v_i). The literal complete cap and payoff identities give

    B_i(y)=max(Q_i,H_i+β_i B_i(z))≤w_i+β_i h_i,
    U_i(y)=w_i+c(h_i−d_i(z)),
    d_i(y)≤c d_i(z)+π_i h_i.                               (2)

At i=a both right-hand terms vanish, so nonnegative debt gives d_a(y)=0.
Summing and using Σ_iπ_i≤A yields

    D(y)≤D−A(D−h)=D−AD/2.                                  (3)

Since δ≤d_j(z)≤D and j≠a,

    v_j=B_j(z)−D/2≤s_j−D/4.

The endpoint subtraction from the frozen packet applies with deficit D/4:
an exact root has A≥D/(8M+D). Substitute in (3) to get (1). Prefixing one
row shifts the old sure deadline by one regardless of null histories or
zero survival. This proves all assertions for the actual profile y.

If the game additionally has a positive terminal gap, the new declaration
`initial_or_lastZero_uniqueSure_shiftedCapTail` applies to an actual exact
ray constructed from y, using this SAME zero-debt anchor and shifted sure
deadline. It produces an initial or last-zero shifted cap source. Thus the
auxiliary row itself need not be exact against U(z), nor need its output
retain an immediate-Quit cap for j. No unsupported identification of those
two finite games is used.

This removes a specific interface problem in using the uniform-h auxiliary
row verbatim: its bound at a would only be d_a(y)≤π_a h, not zero. It does
not solve the next horizontal cap-child cost. The already integrated exact
root at U(z) also preserves the anchor and gives a δ-dependent drop by
`LateResetChildCapPin.everyExactRoot_debtDrop_and_absorptionFloor`; no new
constant optimization or new strategic principle is claimed here.

## 3. Precise attempted global-source reset-return lemma

Here are the complete hypotheses of the attempted lemma, granting more
global control than the new restart declarations currently supply.

Assume m>0, choose 0≤e<κ(m), and suppose P is an actual source with

    D(P)≤m+e.                                               (4)

Let p_n be a literal exact-prefix ray from P: p_0=P and
p_{n+1}=q_n::p_n, where q_n is exact Nash at U(p_n). Suppose its roots
have positive joint survival and summable marginal hazards. Let b be a
fixed owner and t_0 a finite time such that the response Quit(t_0+n)
attains b's COMPLETE cap at p_n for every n, with positive owner debt.
Define the literal cap children

    z_n=p_n[b←Quit(t_0+n)].

Thus b is a zero-debt sure anchor at every z_n. Assume one fixed j≠b and
δ>0 have cofinally many literal reset indices n at which

    d_j(z_n)≥δ,     |L_j(z_n)|≤δ/4,
    Quit0 attains j's complete cap at z_n.                    (5)

The new assembly supplies precisely such pins in its infinite-reset arm,
once its own source hypotheses hold. In (4) GLOBAL nearness is an extra
assumption; it is not obtained by minimizing over that assembly's sources.

Attempted conclusion. At some sufficiently late reset n, a finite literal
prefix of z_n has total debt below m, consuming this residual arm.

This conclusion is NOT proved. Here is the exact scalar implication it
requires in the actual genealogy, rather than a replacement source model.

Write the gross outsider debt change of the one actual cap installation as

    H_n=Σ_{i≠b}[d_i(z_n)−d_i(p_n)].

The cap-attaining owner has d_b(z_n)=0, so the exact identity is

    D(z_n)=D(p_n)−d_b(p_n)+H_n.                              (6)

No cap displacement or prescribed-payoff displacement has been dropped:

    H_n=Σ_{i≠b}[(B_i(z_n)−B_i(p_n))−(U_i(z_n)−U_i(p_n))].

Exact prefixes weakly decrease every debt coordinate, so
m≤D(p_n)≤D(P)≤m+e. Applying Section 2 at a reset gives an actual y_n
with its zero anchor retained and

    D(y_n)≤D(p_n)−d_b(p_n)+H_n−κ(D(z_n)).                    (7)

Consequently the following one inequality would prove the attempted lemma:

    H_n < d_b(p_n)+κ(D(z_n))−(D(p_n)−m).                    (R)

This is the exact missing GLOBAL source-credit inequality. It includes the
original owner's eliminated debt, every outsider's full-cap leakage, the
actual child's expenditure, and the actual parent's global excess. It is
not the assertion that an arbitrary cap installation cannot increase debt.

For comparison, the frozen arbitrary-source block also applies at z_n if
j is preempted: L_j(z_n)≤δ/4≤D(z_n), so its C is exactly D(z_n). It gives
an actual word with debt at most

    D(z_n)−k(D(z_n)),        k(t)=3t²/(32M+6t).

Thus the corresponding threshold-block version of (R) replaces κ by k.
The word need not retain b's zero debt; Section 2 explains how to retain
the anchor when that interface is required. Under no UE in Fin4 every
owner's strict preemptor is supplied by the named singleton-column source,
with no sign assumption on s.

## 4. What the global hypotheses actually force

The global lower bound applies to y_n because it is an actual profile.
Combining it with (7) proves the reverse necessary inequality at EVERY
reset satisfying (5):

    H_n ≥ d_b(p_n)+κ(D(z_n))−(D(p_n)−m)
        ≥ d_b(p_n)+κ(m)−e.                                 (8)

The second step uses D(z_n)≥m, (4), and monotonicity of κ on positive
arguments. In particular, if e<κ(m), the outsiders' total debt replenishment
strictly exceeds the debt removed from the installed owner, by one uniform
positive amount. The frozen block supplies the analogous bound with k.
This is an exact consequence on the hypothetical positive-global-minimum
arm, not a counterexample to it. Deriving (R) from additional actual-source
geometry would contradict (8) and genuinely consume that arm.

The current source declarations provide attainment, deadlines, owner-zero
debt, a positive copied-response floor, and summable *generating root*
hazards. They provide no upper bound in (R) on the finite replacement of
the owner's entire law. Small generating hazards describe successive
vertical rows; the replacement at z_n still reaches the old tail with its
positive surviving mass. Neither summability nor the finite player count
alone identifies H_n with a vanishing root charge. No such identification
is made here.

Also, a minimum taken only over reset children, attained-cap sources, or
one anchored family would not justify m≤D(y_n) unless y_n were proved to
remain in that exact minimizing family. The argument above avoids this by
using only the global carrier. Conversely, the source theorem does not
produce (4) from its arbitrary reset child: the existing cap-pin collar
already places that child a positive distance ABOVE the global lower bound.

Accordingly the new literal restart strength closes the executable-source
and anchor interfaces, but does not prove (R). No unproved cap-budget
closure is inferred from the fact that the output can seed another ray.
The eventual-shift and last-zero branches remain explicitly separate; no
last-zero shifted cap is silently replaced by a cap-pinned stationary row.

## 5. Bounded source record and next mathematical check

Selected via the current toolkit and read under their imports:

- `finFour_lateResetChild_exists_directShiftedCapRestart` in
  `UniformEquilibrium/Diagnostics/Quitting/LateResetDirectSourceRestart.lean`;
- `LateResetChildCapPin`, its payoff bound, its exact-root coordinate/total
  drop and absorption theorems, and
  `LateResetChildCapPin.totalDebt_ge_minimum_add_expenditure` in
  `UniformEquilibrium/Diagnostics/Quitting/LateResetChildCapPinExit.lean`;
- `QuittingActualExactPrefixRay.initial_or_lastZero_uniqueSure_shiftedCapTail`
  in `UniformEquilibrium/Diagnostics/Quitting/ActualExactPrefixRayRestart.lean`;
- `HasTerminalExploitabilityGap.exists_late_childRestart_capPinDichotomy`
  and `LateFixedOutsiderTransport` in
  `UniformEquilibrium/Diagnostics/Quitting/LateResetChildRestartAssembly.lean`;
- `QuittingActualExactPrefixRay`, `exists_quittingActualExactPrefixRay`,
  `ShiftedCapTail`, `nonempty_shiftedCapTail_of_attainedCap`, and the two
  anchor-persistence theorems in
  `UniformEquilibrium/Quitting/Paths/ActualExactPrefixRay.lean`;
- `quittingPureTimeCapChild_ownerDebt_eq_zero`,
  `quittingPureTimeCapChild_ownerGain_eq_debt`, and the sure-deadline theorem
  in `UniformEquilibrium/Quitting/Root/PureTimeCapChild.lean`;
- `fixedCapPin_coordinateDebtDrop` and `fixedCapPin_totalDebtDrop` in
  `UniformEquilibrium/Diagnostics/Quitting/FixedCapPinCoordinateDebtDrop.lean`.

The frozen finite cap-threshold packet was read in full, including its
arbitrary-source C=max(D,L_i), exact first-hit scope, global minimum collar,
and weak-exclusion renewal argument. HAHN's existing
`CODEX_HAHN__LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE.md` already warns
that executable renewal does not pay the horizontal seam. This note does
not rebrand that warning as a new no-go; it records the attempted inequality
(R), the protected-anchor calculation, and the precise global reverse
budget (8) for the strengthened sources. No Lean build was run.

Next concrete question: can the full attained-response geometry at a
GLOBAL near-minimum force (R) on some cofinal reset, or else exclude such
globally near-minimal anchored rays altogether? An arbitrary-source
counterexample whose game's global minimum is zero would not answer that
question. No consumer is claimed until one of these implications is proved.
