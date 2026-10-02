# Same-table polynomial words and the actual global minimum: a paid-seam test

Author: CODEX_NOETHER_SUPPORT.

Status: ordinary mathematics, not independently reviewed or Lean-checked.
The complete-cap comparison below gives a certificate-dependent separation
between actual near-minimizing payoff vectors and the polynomial's lower-
boundary minimizing set. It does not pay that separation, improve the true
global minimum, or contradict a positive worst-table value. The bounded
operation is complete and stops at this precise seam. No export is proposed.

## 1. Question and same-table provenance

Fix a four-player quitting table r, zero Never reward, and |r_i(S)|≤M with
M>0. Strategies are independent private stopping clocks on the nonnegative
integers together with Never. Write U(p) for prescribed terminal payoff,
B_i(p) for the supremum against EVERY unilateral behavioral replacement,
d_i(p)=B_i(p)−U_i(p), and E(p)=max_i d_i(p). In particular E(p)≥0.
Let

    m=inf_p E(p)>0,

where the infimum is over all actual behavioral profiles, not only finite
menus or Nash laws. The semantic carrier is the closure of the actual
(U,B) pairs; it is compact and has the same minimum m. No cap-attaining
response at that carrier minimum is assumed.

The motivating table is the ORIGINAL maximizer of m over the unit reward
cube. Its positive minimum excludes a uniform-equilibrium payoff, by the
actual-profile/diagonal-carrier characterization. The following production
composition provides the polynomial at that literal table:

- `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
  in `Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`
  gives `all_punishmentNormal` at the same reward table. Its full-normal-core
  fields are not a replacement by a reduced game.
- `exists_uniformEquilibriumPayoff_of_zeroSolo` in
  `Quitting/Punishment/ZeroSoloDisjunct.lean` shows that some own singleton
  s_i=r_i({i}) must be positive. Otherwise all-Never is already exact.
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in `Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`
  then gives, on this SAME table, a rational tolerance 0<δ≤1/4 and a
  polynomial H that decreases by at least absorption on every robust edge
  in the box of radius b=M+2. No membership stretch, canonicalization, or
  singleton reselection occurs in this composition.

These declarations and their relevant definitions were inspected statically;
no Lean build was run here. The argument below only needs their same-table
conclusion, and in fact applies to any table with m>0 and the displayed H.
Outer worst-table maximality is not subsequently used. Neither the original
full-cube reward normal nor the coupled-source tester multipliers are
transported through the operation or attached to a selected payoff.

## 2. The polynomial word used, with its exact scope

Put K=[−b,b]^4, C=∏_i[s_i,b], and

    L={v∈C : v_i=s_i for at least one i},
    X_H=argmin_(v∈L) H(v).

This is a nonempty compact set. For a product root q, write a(q) for the
probability that somebody quits and F(q,v) for its expected payoff with
public all-Continue payoff v. The robust hypothesis is

    ||w−F(q,v)||∞≤δa(q),
    max(Q_i(q,v),C_i(q,v))−F_i(q,v)≤δa(q) for every i
       ⇒ H(v)−H(w)≥a(q),                              (1)

for every v,w∈K and q. This is exactly the residual and defect convention
of `IsQuittingFloorFreeRobustEdge` in
`Quitting/Projective/RobustChargedRelation.lean`, together with the
source-minus-target convention of `IsPotential` in `MathUE/ChargedPathBudget.lean`.

Use the ordinary finite-word result in
[TARSKI's crossing note](CODEX_TARSKI_PREMIUM__UNIVERSAL_DRIFT_FINITE_WORD_FORCES_MACROSCOPIC_FLOOR_CROSSING.md),
independently checked in
[our review](../feedback/CODEX_TARSKI_PREMIUM__UNIVERSAL_DRIFT_FINITE_WORD_FORCES_MACROSCOPIC_FLOOR_CROSSING__BY_CODEX_NOETHER_SUPPORT.md).
For each x∈X_H, let J={i:x_i=s_i}. For all sufficiently small ε>0,
v⁰=x−ε1_J satisfies H(v⁰)<min_L H. Starting at v⁰, EVERY sequence of
exact Nash roots against its current annotation enters C after finitely
many Bellman updates. Write one such word as

    vᵏ⁺¹=F(qᵏ,vᵏ),       k=0,...,n−1.

Its last crossing root has collision probability χ, meaning at least two
simultaneous quitters. If κ is any finite negative directional-curvature
bound

    D²H(z)[h,h]≥−κ||h||∞²       (z∈K),

the reviewed word theorem gives κ>0 and

    χ>χ_H:=δ/[2Mκ²(M+b)^4]>0.                          (2)

Indeed its crossing absorption a satisfies a>2/[κ(M+b)²], and
χ>δa²/(8M). In particular χ_H<1. The same χ_H works for every x,
every sufficiently small ε, and every root-choice sequence; word length
need not be bounded uniformly.

The actual chronological head is qⁿ⁻¹,...,q⁰, in REVERSE annotation order.
It is a finite timing-game Nash head with public terminal value v⁰, by
backward induction. This does not claim that v⁰ is an actual terminal
payoff, that this head is terminal Nash, or that it repeats indefinitely.

## 3. The complete signed seam bill

Fix such a finite head. Let c be its joint all-Continue probability and
D_i its opponent-deleted all-Continue probability. Thus 0≤c≤D_i≤1.
The collision event at the crossing row implies that at least one
opponent of EVERY i quits at that row. Consequently

    D_i≤1−χ<1−χ_H             for every i.              (3)

Let K_i be the best payoff of a pure response that quits within this
head. Let W_i be the absorbed contribution to a response that continues
through the head, excluding its remaining boundary payoff. Let z be the
head's prescribed payoff with public continuation v⁰. Exact head Nash
gives

    z_i=max(K_i,W_i+D_i v⁰_i).                         (4)

Prepend this literal head to ANY actual tail p. Fresh private draws in
the head and tail preserve independence. All head dates remain available,
and every finite late response and Never is retained. The exact identities
are

    U'_i=z_i+c(U_i−v⁰_i),
    B'_i=max(K_i,W_i+D_i B_i).                         (5)

The second identity concerns a supremum: if D_i>0, approximate the old
tail supremum; if D_i=0, its contribution vanishes. It needs no maximizing
tail response. Randomized responses cannot exceed the supremum of the
pure deadline and Never responses.

Put h_i=U_i−v⁰_i. Equations (4)–(5) imply

    d'_i≤max(D_i d_i+(D_i−c)h_i, −c h_i).             (6)

Both terms are essential. The annotation may exceed U_i or B_i, so a
nonnegative cap-shift hypothesis is not available. For instance the scalar
Nash data z=K=0, W=−1/2, D=1/2, c=1/4, v⁰=1, U=B=0 satisfy (4) and give
d'=1/4: dropping the second term would give the false bound −1/4. This
tests the signed algebra, not existence of a positive-gap game or of a
universal H with those data.

Since d_i≤E(p), E(p)≥0, 0≤D_i−c≤1, and (3), (6) yields

    E(head followed by p)
       ≤(1−χ_H)E(p)+||U(p)−v⁰||∞.                    (7)

This is an actual independent-profile comparison with complete behavioral
caps. It does not identify deleted survival D_i with joint survival c.
As an algebra check, exact rational enumeration verified (7)'s scalar
envelope for y_i∈{0,1/4,1/2,1}, c=∏y_i, D_i=∏_(j≠i)y_j,
χ_H=(1−max_i D_i)/2>0, E∈{1/10,1/2,1}, and every
h∈{−2,−1/2,0,1/2,2}^4: 455625 checks. These test the displayed signed
inequality, including c=0, not existence of a universal H or a positive
global minimum. The proof of (7) is the elementary bound preceding it.

## 4. A genuine same-table necessary separation

By the definition of m, the left side of (7) is at least m. For a fixed
x∈X_H take ε↓0, allowing a different head at each ε but retaining (2):

    ||U(p)−x||∞ ≥ m−(1−χ_H)E(p).                      (8)

This holds for EVERY actual p and EVERY x∈X_H. Taking the infimum over
x gives the equivalent useful near-minimum form

    dist∞(U(p),X_H)+(1−χ_H)(E(p)−m) ≥ mχ_H.           (9)

Continuity and the definition of the semantic carrier extend (8)–(9)
to every carrier pair, with its own E. In particular, for EVERY global
MAX-minimizing carrier pair (U,B),

    dist∞(U,X_H)≥mχ_H.                                (10)

Thus one cannot jointly choose an actual near-minimizing payoff and an
H-boundary minimizer with a vanishing seam. The quantifier is not merely
one selected root, source, or equilibrium component. All-player MAX ties
are available at this minimum but are not needed for (9).

## 5. What this adds, and why the operation stops here

The whole-head identities (5) and the signed debt accounting are prior:
[the whole timing-block note](CODEX_NOETHER_SUPPORT__WHOLE_TIMING_BLOCK_BONUS_COMPETITION.md)
already retains joint and deleted survival separately. The one-step source
is `quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`Quitting/Root/TerminalDebtPrefix.lean`. The distinct cap-annotation identity
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
`Quitting/Root/CapNashRootStack.lean` assumes Nash at the ACTUAL cap and is
not applicable to this arbitrary v⁰ as if that condition were automatic.
Carrier passage uses `continuous_quittingTerminalSemanticPrefix` and
`quittingTerminalSemanticPrefix_mem_carrier` in
`Quitting/Root/TerminalSemanticPair.lean`.

The additional relation here is (9): the independently produced
collision-bearing H-word imposes a certificate-dependent distance from
ALL global MAX-near-minimizing payoffs of that SAME table. It is not a new
root producer or reward-portfolio normal condition. The existing
[critical-box repair](CODEX_FRECHET_CYCLE__GLOBAL_MAXIMUM_DEBT_CRITICAL_BOX_REPAIR.md)
already puts minimizing U strictly above the own-singleton boundary by
U_i−s_i≥m²/(64M). No dominance of (10) over that prior moat is proved.
The size χ_H depends on the supplied polynomial and curvature bound;
enlarging κ only weakens it. No uniform raw-table quantitative gain follows.

Most importantly, same-table existence of H and global near-minimizers
does not give the U-to-v⁰ upper bound needed to consume (7). The full-cube
outer normal is a statement about a complete proof tuple; it supplies no
gradient inequality for H and cannot be reassigned to this chosen head.
Selecting a lower-boundary minimizer using closeness to U is already
covered by (10), and cannot erase the positive seam.

The tested operation therefore yields a necessary separation, not a
descent. A genuinely new continuation would have to pay the signed seam
in (6), or obtain a different actual operation whose boundary is supplied
by its source. Merely bundling H with the global-source multipliers, or
discarding the negative-seam branch, does not do that. This bounded line
is stopped rather than developed into another conditional compiler.
