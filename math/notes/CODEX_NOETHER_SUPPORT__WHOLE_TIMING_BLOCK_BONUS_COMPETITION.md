# Whole timing-block competitors for the actual-output bonus objective

Author: CODEX_NOETHER_SUPPORT.

Status: ordinary-mathematics exact closure and finite-source necessary
condition, not Lean-checked or exported. A two-date exact test separates
whole-block Nash from backward stacks of one-stage Nash roots. It does not
prove small actual output for arbitrary canonical tables. The strictness
test uses a large bonus box, not a positive global minimum or a vanishing
bonus counterexample. The parent coordinator proposed the whole-block test.

## 1. Question and data

Use the actual-output objective and notation in
[the all-root note](CODEX_NOETHER_SUPPORT__ALL_ROOT_RESTRICTION_AT_GLOBAL_BONUS_MINIMA.md).
Thus r is any bounded canonical Fin4 table, with own singletons (1,0,0,0)
and zero Never. All laws are independent private clocks, and original
exploitability E uses every unilateral behavioral replacement. A finite
source (ξ,p) is exact Nash with bonuses ONLY for privately planned Never,
ξ∈[0,δ]^4. Write

    u_i=U_i+ξ_i z_i,    k_i=ξ_i z_i,    K=max_i k_i,
    d_i=B_i−U_i,        E=max_i d_i.

The question here is whether one may prefix an arbitrary finite TIMING
Nash block against continuation u, rather than only a backward stack of
one-stage Nash roots. Such a block is an ordinary finite normal-form game:
each player chooses a date in {0,...,L−1} or Continue; the first finite
date pays r, and the all-Continue event pays the PUBLIC vector u. Continue
here means survive the whole block. There is no private bonus in this
block game. Exact Nash is normal-form Nash, not subgame-perfect Nash.

## 2. Exact whole-block closure

Let σ be ANY independent exact Nash profile in this L-date block game.
Let y_i be its probability of Continue, and define

    a_i=∏_(j≠i)y_j,              c=∏_j y_j.

Let R_i(t) be the block payoff to pure date t<L. It has no continuation
term because i itself quits within the block. Let H_i be the absorbing
contribution to i's pure Continue response, excluding the event that all
its opponents Continue. Set

    Q_i=max_(t<L)R_i(t),         C_i=H_i+a_i u_i,
    n_i=max(Q_i,C_i).

The Nash payoff is n_i. Whenever σ_i(t)>0, R_i(t)=n_i; whenever y_i>0,
C_i=n_i. These are the only equilibrium properties required.

Construct a new independent clock for i by following σ_i within the
block, and, if σ_i chooses Continue, following a fresh copy of p_i shifted
by L. Put

    ξ'_i=a_i ξ_i.                                      (1)

The resulting law p' is an EXACT finite auxiliary Nash profile with
bonuses ξ'∈[0,δ]^4. Indeed its pure block-date responses have auxiliary
values R_i(t). A shifted finite response from the old source has value
H_i+a_i F_i(t); its Never response INCLUDING the new private bonus has
value H_i+a_i(W_i+ξ_i). The maximum over all old responses is C_i, and
every supported old action reaches C_i. The block Nash support equalities
therefore verify every supported new action and every omitted finite-menu
response. This argument includes y_i=0 and a_i=0 and requires no optimality
at public histories that the prescribed block reaches with probability zero.

The new Never mass and bonus credit are

    z'_i=y_i z_i,       k'_i=c k_i,       K'=cK.

The original prescribed payoff is the block payoff with continuation U
in place of u. Only the joint all-Continue event changes, so

    U'_i=n_i−c k_i.                                    (2)

For the ORIGINAL complete cap, every response either quits at a block
date or waits and uses an arbitrary original tail response. Thus

    B'_i=max(Q_i,H_i+a_i B_i)
         =max(Q_i,C_i+a_i(B_i−u_i)).                    (3)

Equations (2)–(3) imply the exact debt formula

    d'_i=max(c k_i−(n_i−Q_i),
             a_i d_i−(a_i−c)k_i−(n_i−C_i)).           (4)

For a nonpivot, B_i≤u_i and d_i≤k_i by the canonical finite-menu/full-cap
identity. Hence

    d'_i≤c k_i             (i>0),
    d'_0≤max(c k_0,a_0d_0),
    E(p')≤max(cK,a_0E(p)).                             (5)

This retains all original finite dates and Never, not only the block
response menu. No comparison u_i≤B_i is assumed. For the original pivot
late scalar L_0=W_0+D_0−U_0, its exact transport is

    L'_0=a_0L_0−(a_0−c)k_0−(n_0−C_0).               (6)

In fact W'_0=H_0+a_0W_0 and D'_0=a_0D_0. Opponent-deleted continuation
a_0, not joint continuation c, is the coefficient of the old late scalar.

## 3. Consequence for a positive horizon-global minimum

Let A(N,δ) be the minimum original E over all N-date exact auxiliary
Nash laws in the bonus box, and b_δ=inf_N A(N,δ). Suppose b_δ>δ. At ANY
actual finite minimizer of A(N,δ), EVERY exact finite timing-block Nash
profile σ against its continuation u, of EVERY block length L≥1, satisfies

    b_δ≤A(N+L,δ)≤a_0 A(N,δ),
    1−∏_(j>0)y_j≤(A(N,δ)−b_δ)/A(N,δ).                (7)

The proof is (5), c≤a_0, and K≤δ<b_δ≤A(N,δ). No block length occurs
in this bound. Nash profiles for every block length exist by ordinary
finite-game Nash existence; the supremum over all these profiles is
controlled at each finite source, without taking a limit of game roots.

If a positive b_δ>δ is attained at a finite horizon, EVERY finite block
Nash profile against that source u has every nonpivot Continue surely.
Along finite minimizers approaching b_δ, the supremum of nonpivot block
activation, jointly over all finite lengths and all exact block Nash
profiles, tends to zero. This strengthens the one-stage source restriction.
It neither constructs such a block nor asserts persistence of arbitrary
new block equilibria at a limiting continuation.

## 4. Exact two-date separation from one-stage backward selection

Here is a complete canonical table demonstrating why one must not replace
whole-block Nash by subgame-perfect backward induction. For nonempty S,

    r_0(S)=1 if 0∈S; otherwise 2 if 1∈S; otherwise 0;
    r_1(S)=−1 if 0∈S and 1∉S; otherwise 0;
    r_j(S)=0 if j∈S, and 1 otherwise,      j=2,3.

Take public continuation u=(2,1,1,1). The one-stage game has UNIQUE Nash
root all Continue. Players 2 and 3 strictly prefer Continue: Quit pays
zero, while Continue pays one for every opponent realization, including
all Continue. With these players continuing, player 0's Quit endpoint
is one and its Continue endpoint is two, independently of player 1.
Then player 1's Quit endpoint is zero and its Continue endpoint is one.
Backward stacks of exact one-stage roots at this boundary are therefore
all Continue at every date.

Nevertheless the two-date block has an exact Nash profile

    player 1: Quit0; player 0: Quit1; players 2,3: Continue.

Its payoff is (2,0,1,1). Player 0 receives one by Quit0 and two from
Quit1 or Continue. Player 1 receives zero from Quit0 or Quit1 and −1
from Continue, because player 0 is privately committed to date one.
Players 2 and 3 receive one when they stay out of the absorbing coalition
and zero if they join it, so cannot improve. Thus every block response
is checked. Player 0's date-one commitment is not optimal at the public
history where player 1 failed to quit: there it would prefer the terminal
continuation two to singleton one. That history is off path, so this
does not violate normal-form Nash. It explains the strict difference
between the two competitor domains.

The same block is an ORIGINAL full equilibrium when Continue means Never.
Additional later dates for player 1 yield −1, and those for player 0
yield two; players 2 and 3 cannot exceed one. The table is therefore
already solved and is not a hard equilibrium-existence benchmark.

For a literal auxiliary-source test, take a one-date all-Never source
with bonuses ξ=(2,1,1,1). It is exact auxiliary Nash and has u above,
original E=1, and δ=2. No one-stage prefix changes this law or its E,
but the displayed whole block has a_i=0 for EVERY i and concatenation
gives ξ'=0 and E'=0. This verifies strict extra force of the competitor
operation at an actual source. The source is not a global A minimizer,
and δ is not small. No vanishing-bonus or positive-global-gap conclusion
is drawn from this test.

The exact rational checker
[CHECK_WHOLE_BLOCK_BONUS_TRANSPORT.py](../experiments/CODEX_NOETHER_SUPPORT__CHECK_WHOLE_BLOCK_BONUS_TRANSPORT.py)
enumerates all pure responses in this test and in the all-root note's
positive-unused-bonus test. It verifies auxiliary Nash before and after
concatenation, every coordinate of (2)–(4), and the exact late identity (6).
Running `python experiments/CODEX_NOETHER_SUPPORT__CHECK_WHOLE_BLOCK_BONUS_TRANSPORT.py`
from `math/` reports E=1 to E=0 and E=1/4 to E=0, respectively. The script
reads and writes no files. These bounded checks do not prove the general
theorem or search the all-length equilibrium correspondence.

## 5. Source correspondence and remaining question

The ordinary source for the complete finite-menu cap split is
`singlePivot_nonpivot_fullCap_eq_menuCap` and
`singlePivot_pivot_fullCap_eq_max_menu_never_add_deletedNever` in
`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`.
The one-stage semantic recursion in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` supplies the
same first-stopping-time decomposition used directly in (3). Neither
source is being described as a global auxiliary selector or as proving
this whole-block source restriction. The linked all-root note records why
the existing nonnegative lower-cap-shift ledger cannot be applied to u
without checking its sign hypothesis.

Next question: can the finite source's exact timing support equalities
force an activating WHOLE block when (7) would otherwise make all such
blocks nearly inactive? The two-date test proves that a unique one-stage
all-Continue root is not a sufficient obstruction, but does not answer
this question at an actual near-minimizer with vanishing bonuses.
