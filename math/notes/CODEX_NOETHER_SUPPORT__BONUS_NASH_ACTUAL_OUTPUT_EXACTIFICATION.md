# Actual-output exactification in Never-only auxiliary games

Author: CODEX_NOETHER_SUPPORT.

Status: bounded investigation, not an export or a solved universal producer.
Section 2 records an exact finite-dimensional membership characterization,
specializing previously derived scalar bonus algebra to the all-four-player
uncompensated program. Section 3 tests it on a known genuine no-finite-exact
canonical example. Neither an all-horizon actual-output counterexample nor
a universal approximation-to-exact auxiliary Nash theorem is obtained.

## 1. Precise remaining question

Fix one finite real canonical Fin4 table r, with own singletons (1,0,0,0),
zero Never payoff, and independent private stopping laws. Complete original
exploitability E uses every finite date and Never, equivalently all unilateral
behavioral replacements. For each N≥1 and δ≥0 let G_N,δ consist of ξ∈[0,δ]^4
and exact Nash laws p of the finite menu F_N={0,...,N−1,Never}, where player
i's auxiliary pure payoff is its original terminal payoff plus ξ_i only
for its own privately PLANNED Never action. No finite-action rewards change.

Write U_i(p), F_i(t;p_-i), and W_i(p_-i) for ORIGINAL prescribed, finite
response, and Never response values. Put

    D_0=∏_{j>0}p_j(Never),       L_0=W_0+D_0−U_0,
    A(N,δ)=min_(ξ,p)∈G_N,δ E(p).

All finite-dimensional minima exist by compactness and the continuous finite
cap formula. The question is

    [∀ε>0 ∃ actual profile p with E(p)<ε]
       ⇒ [∃N_k→∞, δ_k→0 with A(N_k,δ_k)→0].              (X)

The premise is the project's terminal approximate-existence equivalent of
canonical UE existence. Laws, bonuses and horizons may be reselected
completely. The conclusion does not preserve a supplied approximate source.

At auxiliary Nash, menu error is at most δ. Therefore minimizing ACTUAL
L_0 over G_N,δ is equivalent to minimizing E up to that known δ error:

    max(0,min_G L_0) ≤ A(N,δ) ≤ max(δ,min_G L_0).          (1)

The deleted-Never proxy is not equivalent. The completed
[counterexample](CODEX_NOETHER_SUPPORT__BONUS_BOX_DELETED_NEVER_COMPLETENESS_FAILURE.md)
has minimum D_0 equal to one for every horizon and every δ<1, yet A=0 and
every proxy optimizer is an exact original equilibrium. Its unused-Never
slack supplies the cancellation omitted by L_0≤D_0.

## 2. Elimination of the bonus variables

Fix ANY finite profile p; no Nash condition is assumed. For each i define

    z_i=p_i(Never),      H_i=max_(t<N) F_i(t),
    G_i=Σ_(t<N) p_i(t)(H_i−F_i(t))≥0.

Here G_i measures finite support payoff gaps. The original prescribed value
is U_i=(1−z_i)H_i−G_i+z_i W_i. At bonus ξ_i, its ordinary auxiliary regret is

    R_i(ξ_i)=G_i+(1−z_i)[W_i+ξ_i−H_i]_+
                   +z_i[H_i−W_i−ξ_i]_+.                  (2)

The function is piecewise affine, with slope −z_i before its kink and
1−z_i afterwards. A minimizer on [0,δ] is

    ξ_i*=min(δ,[H_i−W_i]_+),

and its minimum is

    R_i*=G_i+(1−z_i)[W_i−H_i]_+
                 +z_i[H_i−W_i−δ]_+.                      (3)

Thus p is representable as an exact Nash law for SOME permitted bonus
vector if and only if, for every i,

    G_i=0,
    (1−z_i)[W_i−H_i]_+=0,
    z_i[H_i−W_i−δ]_+=0.                                 (4)

Proof of simultaneity: once p is fixed, each player's finite/ Never response
values depend only on its opponents' laws. Its own bonus affects none of
the other players' payoff comparisons. The four independent scalar choices
therefore solve all auxiliary best-response conditions together. Conversely
zero auxiliary regret makes each nonnegative term of (3) zero.

All faces are retained. For z_i=0, one needs G_i=0 and W_i≤H_i, and may
choose zero bonus. For 0<z_i<1, every positive finite atom must attain H_i
and 0≤H_i−W_i≤δ. For z_i=1, only H_i−W_i≤δ is required; W_i may already
exceed H_i. No division by a small Never mass is used.

These are finite-dimensional, semialgebraic conditions on the raw table and
the literal finite laws: all response payoffs are polynomials, maxima and
positive parts have standard finite inequality encodings. They characterize
the entire union of auxiliary Nash sets, not merely one supplied support.

This algebra is not claimed new independently of
[RENY's positive-bonus calculation](CODEX_RENY__POSITIVE_BONUS_APPROXIMATE_COMPLETENESS_TEST.md).
It is that calculation with compensation endpoint T=W, applied also to
the pivot. The present use isolates the exact representation restriction
in (X), without importing the different geometric-pivot optimizer.

If an original profile has E≤ε, then its zero-bonus menu regrets are at
most ε and hence R_i*≤ε. This does NOT make (4) exact. In particular a
Never-only subsidy cannot change G_i with opponents and support weights
fixed. Pruning gives approximate support optimality, not these exact zeros;
changing opponents to repair them changes every F_i and the actual L_0.

At fixed N, compactness says approximate auxiliary Nash profiles have exact
auxiliary Nash limit points. It supplies no horizon-uniform correction that
also preserves small original L_0. Invoking such a correction without proof
would be precisely the missing implication (X), not an implementation detail.

## 3. Test on an actual no-finite-exact boundary: VANISH

Use the canonical table from
[HILBERT's bonus construction](CODEX_HILBERT__VANISHING_PRIVATE_NEVER_BONUS_SELECTOR.md).
For nonempty S, the pivot receives one if it quits and two otherwise.
Each nonpivot j has cyclic predecessor pred(j) and successor succ(j) in
{1,2,3}, and receives

    0                                    if j∈S,
    −1                                   if j∉S and 0∈S,
    2·1_(pred(j)∈S)−1_(succ(j)∈S)         otherwise.

The independently reviewed positive branch is recorded again in
[RENY's coupled note](CODEX_RENY__PIVOT_LP_AND_FINITE_NONPIVOT_BEST_REPLY_COUPLING.md),
Section 7. Its global pivot-repair statement is not needed here. Set

    N=3K,       a=2^(−K),       b=4^(−K),       D=8^(−K).

Take the pivot Never and, for j=1,2,3,

    p_j(3k+j−1)=2^(−k−1) for 0≤k<K,      p_j(Never)=a.

The directly computed finite response maxima and Never values are

    H_0=W_0=2−2D,
    (H_1,H_2,H_3)=(0,1,0),
    (W_1,W_2,W_3)=(0,1−b,0).

Every prescribed finite nonpivot date attains its corresponding H_j;
the pivot has no finite support. Hence ALL four G_i equal zero exactly.
The only finite-versus-Never gap needing subsidy is H_2−W_2=b. Choosing
ξ=(0,0,b,0) therefore satisfies (4) exactly. The original complete debt
vector is (D,0,D,0), so both actual late gain and full error tend to zero.
Given any positive bonus ceiling, sufficiently large K puts this profile
inside its permitted box. The uniform bounds in (2) alone would not have
produced its exact support equalities.

This really is a finite-boundary test, not an example secretly possessing
a finite exact equilibrium. Here is the short obstruction, also proved in
[RENY's zero-extra-bonus note](CODEX_RENY__ZERO_BONUS_COMPENSATED_CONTINUATION_OBSTRUCTION.md).
The three-nonpivot root with zero continuation has Quit value zero and
Continue value C_j=2q_pred(j)−q_succ(j). Its unique Nash root is all Continue:
if q_m>0 is maximal, its successor's Continue value is positive, forcing
that successor's hazard zero; m's own optimality then forces its predecessor
zero; that predecessor consequently has negative Continue value and must
quit surely, a contradiction.

In a finite-support FULL exact equilibrium, any reached sure nonpivot
quitter forces the pivot to Continue (two exceeds one). Prescribed current
absorption is certain, so each nonpivot's Quit-now and Continue-then-quit-
next-date responses impose precisely that impossible three-player root
with a sure quitter. A reached sure pivot instead forces all nonpivots to
Quit (zero exceeds −1), after which the pivot prefers Continue. Thus no
reached row has certain absorption. Every row through the last finite
support date is reached and has all hazards below one, making every Never
mass positive. Moving the pivot's positive Never mass to one later finite
date gains its mass times the three nonpivot Never masses, a strict full
deviation. Contradiction.

The example therefore validates membership in (4) along a genuine
no-finite-exact boundary. It does not prove (X) generally, and this test
does not create a new special-case producer beyond the credited construction.

## 4. Why canonicalized passive Solan padding was retired as a benchmark

The suggested original rational padded Solan table has own singletons
(1,1,1,−1), dummy-only reward (3,3,3,−1), and dummy reward zero at every
old-containing coalition. Old rewards there equal the three-player
perturbed Solan table, whether or not the dummy joins.

The original game's UE existence is sound: the current declaration
`quittingGame_exists_uniformEquilibriumPayoff_threePlayer` in
`UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`
covers the old table. Keeping the new player always Continue preserves
every old payoff and old unilateral comparison; every new-player reward
under deviation is nonpositive. This literal quiet lift preserves the
uniform inequalities. Its terminal counterpart was inspected in
`isεAsymptoticNash_passivePaddingQuietProfile`, in
`UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingRetraction.lean`,
and in `quittingTerminalExploitability_quiet_solanPassivePaddedReward_le`.

The latter declaration, `solanPassivePaddedReward_dummySingleton`,
`solanPassivePaddedReward_fresh_of_oldPart_nonempty`, and
`no_isQuittingBlockCertificate_solanPassivePaddedReward_one` were read in
`UniformEquilibrium/Quitting/Boundary/Analytic/SolanPassivePaddingBlockNoGo.lean`.
The old singleton values were checked in `perturbedReward_singletonTerminal`
in `Quitting/Examples/Cyclic/ThreePlayer/PerturbedCycleExclusion.lean`.
The periodic no-go has its stated exact bounded absorbing certificate scope;
it does not exclude approximate or nonperiodic laws.

But the natural canonical terminal-only change, keeping player 0 unshifted,
subtracting one from old players 1,2 and adding one to the dummy, makes the
dummy-only row (3,2,2,0), with own singletons (1,0,0,0) and Never still zero.
The dummy can now Quit at date zero while all old players Continue. Each
old player's joining payoff is its own canonical singleton, strictly below
its passive dummy-only reward. The dummy's Never deviation pays zero,
equal to its singleton. This is an immediate pure exact equilibrium.

It is also auxiliary Nash with ξ_3=0 and any nonnegative old-player
bonuses. Thus this canonicalized table has minimum deleted Never zero
at EVERY N and δ and is an easy successful bonus-box instance. The original
no-period certificate cannot be transported through this terminal-only
shift. No contrary interpretation of the original source is proposed.

## 5. Exact public-boundary shooting correspondence

One concrete joint equalization mechanism is finite backward induction with
a public terminal boundary vector b: all finite absorbing coalitions retain
r, but the all-Never outcome pays b. This differs from directly adding a
private planned-Never bonus, yet their Nash conditions have the following
exact correspondence at a supplied product profile p.

Put D_i=∏_(j≠i)z_j. Against p_-i, the public-boundary payoff of ANY unilateral
replacement with Never mass z'_i is

    U_i(p[i←p'_i])+z'_i D_i b_i.

The same replacement in the private-bonus game pays

    U_i(p[i←p'_i])+z'_i ξ_i.

Thus setting ξ_i=D_i b_i identifies every unilateral comparison, not merely
prescribed values. A Nash law of the public-boundary game is exactly Nash
for these endogenous private bonuses. Conversely, if all D_i>0, every
private-bonus Nash law has the public-boundary representation b_i=ξ_i/D_i.
Nonnegative bonuses correspond to nonnegative b on this nonsingular stratum.
When D_i=0, representation at that same profile requires ξ_i=0; if both are
zero, any b_i has the same unilateral effect. A positive ξ_i on D_i=0 cannot
be represented by any finite b_i.

Finite backward induction supplies Nash laws for each fixed b: select a
mixed Nash root at each successive continuation vector, beginning at b.
The finite Bellman inequalities cap every finite-menu deviation. However,
this does not select b or prove that either max_i D_i b_i or the original
full-response scalar E becomes small. Letting b vary arbitrarily also makes
the correspondence a reformulation, not a producer. Even bounded b does not
by itself control a coordinate whose opponents retain positive Never mass.

The singular-profile issue cannot be promoted to a joint-selection no-go.
For example, STALL's finite solo-pivot approximation requires a positive
bonus for player 2 at a profile with D_2=0. That one profile has no finite
public-boundary representation. Nevertheless the SAME STALL table has a
different bounded boundary shot. Its singleton reward at player 1 is

    b=r({1})=(3,0,3,1).

Let only player 1 quit with a fixed hazard q∈(0,2/3] on each of N dates,
and let everyone else plan Never. At boundary b the prescribed value stays
exactly b. Player 1 is indifferent; pivot Quit at a reached date pays
q·4+(1−q)·1=1+3q≤3; player 2 Quit pays q·1≤3; and player 3 Quit pays zero
instead of one. Hence this is public-boundary Nash by finite Bellman
comparison. The resulting private bonuses are

    ξ=(1−q)^N(3,0,3,1).

Their maximum tends to zero, and D_0=(1−q)^N. Nonnegative auxiliary bonuses
give W_0≤U_0 and menu error at most max_i ξ_i, so the original COMPLETE
error is at most 3(1−q)^N. All raw entries used here are the STALL entries
already analyzed in the
[earlier discount/selection note](CODEX_NOETHER_SUPPORT__GLOBAL_NEVER_BONUS_SELECTION_AND_DISCOUNT_STALL.md).
This is not a new class producer. It is an exact test showing why exclusion
of one singular source does not exclude all boundary shots of that table.

VANISH's successful profile in Section 3 likewise admits the bounded shot
b=e_2: there D_2=4^(−K), making D_2b_2 exactly its required bonus. These
calculations leave the all-table completeness question (X) unresolved.

## 6. Current stopping point

The exact finite membership condition (4) is now explicit for the actual
program, and its interaction with actual L_0 is separated from the deleted-
Never proxy. Known good cyclic constructions meet its exact support
conditions; known delayed bad branches do not rule out globally selecting
those good ones. The canonicalized padding is unsuitable as a hard test.
Public-boundary shooting identifies exact finite Nash laws with endogenous
private bonuses, but neither its singular-face issue nor a failed shot
excludes joint reselection, as the explicit STALL check demonstrates.

What remains is JOINT RESELECTION: from an arbitrary canonical table known
only to possess small complete-regret laws, obtain new finite laws meeting
the four zero conditions (4) with vanishing δ and small actual L_0. No
uniform stability theorem, fixed-horizon compactness argument, bounded
support assumption, or arbitrary finite-action payoff perturbation has
been shown to supply this step. This precise problem remains open here.
