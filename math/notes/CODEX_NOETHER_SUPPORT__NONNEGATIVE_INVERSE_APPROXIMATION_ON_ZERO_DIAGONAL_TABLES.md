# Nonnegative inverses: zero-diagonal approximation and actual UE closure

Author: CODEX_NOETHER_SUPPORT.

Status: complete independent ordinary-mathematics strengthening, not
independently reviewed or Lean-checked. This was reconstructed without
consulting TARSKI's argument. The matrix-density proof is self-contained;
the Fin4 UE conclusion uses the separately audited strict-inverse theorem
in [the frozen index candidate](CODEX_FRECHET_CYCLE__INVERSE_POSITIVE_DISCOUNTED_INDEX_ESCAPE.md)
and the exact terminal-all-errors consumer. The original strict-class
[PASS](../feedback/CODEX_FRECHET_CYCLE__INVERSE_POSITIVE_DISCOUNTED_INDEX_ESCAPE__BY_CODEX_NOETHER_SUPPORT.md)
remains a separate review. No candidate or export was edited.

## 1. Precise strengthening

Let r be an arbitrary signed Fin4 quitting table on nonempty coalitions,
with independent behavioral play and Never payoff zero. Write

    s_i=r_i({i}),       Γ_ij=r_i({j})−s_i.

Then Γ_ii=0. The proposed strengthened conclusion is valid:

    det Γ<0 and Γ⁻¹≥0 entrywise
       ⇒ the original game has a uniform-equilibrium payoff.       (1)

No strict positivity of individual inverse entries, punishment-normality
assumption, or sign restriction on the own singleton vector is added.
All 44 nonsingleton reward coordinates remain arbitrary. The proof
preserves every own singleton and every nonsingleton reward during its
approximation; it does not translate the table or change Never.

## 2. Matrix lemma: second-order positivity is sufficient

Let n≥3, let Γ be an invertible real n-by-n matrix, and suppose
B=Γ⁻¹ is entrywise nonnegative. Set

    K=J−I,       Γ_ε=Γ−εK,

where J has every entry equal to one. For all sufficiently small ε>0,

    Γ_ε is invertible and Γ_ε⁻¹ is entrywise STRICTLY positive.     (2)

Moreover Γ_ε has exactly the same diagonal as Γ, and its determinant has
the same sign. Thus the lemma applies on the zero-diagonal slice, with
negative determinant retained.

### Proof

Put T=BK≥0. Choose ε>0 with ε||T||∞<1, using the maximum absolute row-sum
matrix norm. The absolutely convergent geometric series gives

    (I−εT)⁻¹=Σ_(m≥0) ε^m T^m.

Indeed multiplication by I−εT telescopes the finite partial sums, and the
remaining power tends to zero by the norm bound. Hence

    Γ_ε=Γ(I−εBK),
    Γ_ε⁻¹=B+εBKB+ε²BKBKB+... .                       (3)

Every coefficient in (3) is nonnegative. Fix an entry (i,j). If B_ij>0,
it is already positive in (3). Otherwise, if (BKB)_ij>0 the first-order
term suffices. Suppose instead that (BKB)_ij=0. Since B is invertible,
its row i and column j are nonzero. The equality

    0=Σ_(k≠l) B_ik B_lj

and nonnegativity imply that these two supports are both the SAME
singleton {k}: B_ik>0 and B_kj>0, with all other entries in that row
and column zero.

There exist u,v≠k with B_uv>0. Otherwise every row outside k would be
supported only on column k. There are at least two such rows because
n≥3; they would be linearly dependent, contradicting invertibility.
The single term

    B_ik K_ku B_uv K_vk B_kj

in (BKBKB)_ij is strictly positive. This handles the remaining case,
so every entry of (3) is positive for every sufficiently small ε>0.

The diagonal is unchanged because K_ii=0. The inverse exists throughout
the segment 0≤t≤ε under the same norm bound. By continuity the determinant
cannot change sign on that segment. This proves (2) and all claims.

No irreducibility hypothesis on B, positive diagonal of B, or positive
first-order coefficient was assumed. Invertibility and n≥3 are the exact
facts used to obtain the second-order term.

## 3. Literal reward-table perturbation

For the four-player table, define r^ε by

    r^ε_i({j})=r_i({j})−ε       when i≠j,
    r^ε_i({i})=r_i({i}),
    r^ε_i(S)=r_i(S)             when |S|≥2.

Never remains zero. This changes precisely the twelve off-own singleton
coordinates and has sup-norm reward distance ε from r. Its singleton gap
matrix is Γ_ε=Γ−εK. Section 2 gives strict inverse positivity and negative
determinant for every sufficiently small ε>0. The strict inverse-positive
Fin4 theorem therefore gives a UE payoff for EACH of those actual tables.

This invocation is of that theorem's unconditional raw-table conclusion.
No claim is made that punishment values, punishment-normality, equilibrium
profiles, or their targets are unchanged under the perturbation. None of
those preservation statements is needed.

## 4. Actual reward-closedness of UE existence

Fix two tables r,r' on the same finite quitting game structure, both with
Never zero, and suppose ||r−r'||∞≤d. Read actual strategies and deviations
as independent stopping laws. Their outcome law is identical under the
two tables, because rewards do not alter available actions, information,
or the first-stopping transition. For EVERY prescribed profile p and
EVERY unilateral behavioral replacement τ_i,

    |U_i^r(p)−U_i^(r')(p)|≤d,
    |U_i^r(p[i←τ_i])−U_i^(r')(p[i←τ_i])|≤d.          (4)

The finite-absorption event has probability at most one, and on Never the
difference is zero. Thus taking the full response supremum gives

    |B_i^r(p)−B_i^(r')(p)|≤d,
    |E_r(p)−E_(r')(p)|≤2d.                            (5)

This includes all finite deadlines, Never, and adaptive behavioral
strategies; it is not a finite-menu bound or a payoff-only compression.
No cap-attaining deviation is assumed.

Consequently, if r^n→r and each r^n has a UE payoff, then r has one too.
For any accuracy η>0 choose n with ||r^n−r||∞<η/4. The UE at r^n supplies
an actual terminal η/2-Nash profile p. The SAME stopping laws satisfy
E_r(p)<η by (5). Hence the original game has terminal approximate Nash
profiles at every positive error. The exact target-free consumer

    quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors

then selects one fixed uniform-equilibrium payoff for r. Targets of the
approximating games need not have been fixed jointly in advance, and no
uniform choice of their strategies or horizon thresholds is required.
This is UE EXISTENCE closedness in reward data, not a claim that any
specified equilibrium law remains an equilibrium after changing rewards.

Applying this argument to Section 3 proves (1).

## 5. Exact boundary tests and dimension restriction

The four-cycle permutation matrix

    Γ=[0 1 0 0; 0 0 1 0; 0 0 0 1; 1 0 0 0]

has zero diagonal, determinant −1 and a nonnegative inverse with many
zeros. At ε=1/20, the inverse of Γ−εK is

    (1/129523) [  7240   7580    780 136780 ]
                [136780   7240   7580    780 ]
                [   780 136780   7240   7580 ]
                [  7580    780 136780   7240 ].

Every entry is positive and the perturbed determinant is negative.
For this B, the entries (0,2),(1,3),(2,0),(3,1) of both B and BKB vanish.
Thus an assertion that the first-order inverse correction is always
positive would be false; the second-order argument is genuinely needed.

Exact rational checks also verified the positivity conclusion and
entrywise positivity of B+BKB+BKBKB for every permutation inverse in
dimensions 3,4,5 (150 matrices). These check the lemma, not a new game
class or a substitute for its proof.

The n≥3 restriction cannot simply be removed from the matrix-density
statement. In dimension two, every invertible zero-diagonal matrix is
[0 a; b 0], whose inverse has zero diagonal. No zero-diagonal-preserving
perturbation can have a strictly positive inverse. In particular
Γ=[0 1;1 0] has negative determinant and nonnegative inverse, yet lies
outside the closure of strict-inverse matrices within that two-dimensional
zero-diagonal slice. This is a direct obstruction to the proposed density
there, not an inference from failure of only one perturbation. It says
nothing negative about two-player UE existence. The UE conclusion of this
note remains specifically Fin4.

## 6. Source correspondence and review boundary

The original strict theorem remains the frozen source cited at the top,
SHA `0d1a77885542d00559e3a146abc9e40bd1f47884b81be73c571a062d7419702a`.
Its existing independent audit is not amended by this separate argument.

For the semantic closure I inspected both directions of
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`,
including `quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff`
and `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`,
in `Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The same-clock full-response convention is the one in
`Quitting/Paths/CounterfactualStoppingLaw.lean`; (4)–(5) are also proved
directly here. The singleton convention is exactly
`normalizedSoloMatrix_eq_soloReward_sub` in
`Quitting/Classification/PreemptionGateDictionary.lean`.
These paths are relative to `UniformEquilibrium/`.

No checked Lean matrix-density or reward-closedness composition is
asserted. The ordinary proof does not weaken the determinant premise,
extend the no-UE punishment-normal source to arbitrary player counts,
or assume the original discounted equilibria themselves have positive
support. Independent verification of this added density/closure argument
and final-byte acceptance remain separate from the strict-candidate gate.
The bounded strengthening test is complete; await final-packet review.
