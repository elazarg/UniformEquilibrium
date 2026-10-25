# A signed Fin4 table beyond the joint-margin stationary split

Owner: CODEX_ARBITRARY_TOPOLOGY.

**Complete stationary and exact finite-calendar exclusions, with an exact
rational checker.** Independent review status is recorded in accompanying
feedback. This is ordinary mathematics, not a Lean result or an export.
The uniform-equilibrium status of this table is not decided here. In particular,
the result is not a counterexample to Fin4.

The table has the same singleton matrix as the current difficult reference
family, but strongly signed and unequal nonsingleton rewards. All four raw
observer-margin capacities are positive. Nevertheless stationary profiles
have a strictly positive terminal exploitability floor, and no absorbing
exact finite-calendar Nash profile exists. The concrete remaining
question is to construct nonstationary approximate equilibria for this SAME
table, or derive a valid obstruction against unrestricted behavioral profiles.

## 1. Complete original game

Players are0,1,2,3. They choose Continue or Quit independently at each live
date. The first nonempty quitter coalition A absorbs at r(A); original live
play and literal AllNever pay zero. All unilateral complete behavioral laws,
including arbitrary finite deadlines and Never, are permitted.

The following table specifies native numbers Z. Set r_i(A)=1+Z_i(A) on
nonempty coalitions ONLY. Thus every original own singleton is1.

| A | Z0 | Z1 | Z2 | Z3 |
| --- | ---: | ---: | ---: | ---: |
| 0 | 0 | 2 | 2 | -1 |
| 1 | 3 | 0 | -2 | -2 |
| 01 | 0 | -1 | -10 | -12 |
| 2 | -1 | 1 | 0 | 1 |
| 02 | 0 | 5 | -10 | 7 |
| 12 | -12 | -100 | 0 | -6 |
| 012 | -13 | 6 | -9 | 11 |
| 3 | 3 | -3 | -1 | 0 |
| 03 | -3 | 3 | -5 | 1 |
| 13 | 2 | -100 | -1 | 0 |
| 013 | -7 | 8 | 10 | -10 |
| 23 | -6 | 9 | 3 | -100 |
| 023 | -7 | -8 | -3 | 15/2 |
| 123 | -8 | 11 | 2 | -5 |
| 0123 | -5 | -9 | 8 | 21/2 |

The singleton matrix is

    Gamma=[0,3,-1,3;2,0,1,-3;2,-2,0,-1;-1,-2,1,0].

Its determinant is25 and Gamma^(-1)e0=(8,3,14,10)/25 is strictly positive.
The size-two principal determinants, in lexicographic subset order, are
(-6,2,3,2,-6,1); the size-three determinants are(10,-3,5,8).
Every column has a negative entry.

Consequently Gamma is R0: a nonzero alpha>=0 with Gamma alpha>=0 and
alpha_i(Gamma alpha)_i=0 cannot exist. Support size at least two would
give a nonzero kernel vector of its invertible principal submatrix. A
singleton support violates the negative entry in that column. These are
specific verified screens, not a claim to meet every source hypothesis.

## 2. All four upper-coalition margin tests pass

For pivot p and observer i!=p write

    A_i^p=Z_i(I\{p})-Z_i(I\{p,i}),
    C_i=Z_i(I)-Z_i(I\{i}),
    Lambda_p=max_(0<=t<=1) min_(i!=p)[(1-t)A_i^p+t C_i].

The row shift cancels in these differences. Here C=(3,-1,-2,-1/2).
Observers in each row below are listed in increasing player order:

| p | A^p | Lambda_p | maximizing t |
| --- | --- | --- | --- |
| 0 | (2,3,1) | 1 | 0 |
| 1 | (-1,2,1/2) | 1/5 | 3/10 |
| 2 | (-9,5,2) | 3/29 | 22/29 |
| 3 | (-1,1,1) | 1/7 | 2/7 |

Each maximum follows by intersecting the increasing observer0 line with
the lowest decreasing line, or by evaluating t=0 in the first row.
The negative joining gaps within the three C-negative owners include
row1 at12 (-101), row1 at13 (-97), and row3 at23 (-101).
Thus every pair of these owners has a negative joining gap, but their
orientation is transitive, unlike the symmetric cyclic countercontrol.

## 3. Exact stationary conditions and all-support exclusion

For stationary hazards q in[0,1]^4, define H_i=product_(j!=i)(1-q_j),
native forced-Quit offer Q_i, and native passive one-date contribution P_i.
All three quantities are finite polynomial expressions from the table:

    Q_i=sum_(A subset I\{i}) mu_i(A) Z_i(A union{i}),
    P_i=sum_(nonempty A subset I\{i}) mu_i(A) Z_i(A),
    mu_i(A)=product_(j in A)q_j product_(j notin A,j!=i)(1-q_j).

When at least two players have positive hazards, every deviator faces sure
opponent absorption. The row shift then adds exactly1 to every payoff and
response. Stationary Nash necessarily has the endpoint signs

    F_i=(1-H_i)Q_i-P_i,
    F_i<=0 if q_i=0; F_i=0 if 0<q_i<1; F_i>=0 if q_i=1.       (1)

Indeed the native Never offer is P_i/(1-H_i), every deadline offer lies
between it and Q_i, and the prescribed value is their convex combination.
An interior own hazard uses both endpoints with positive weight.

Every solo stationary profile is excluded directly, including arbitrarily
small positive hazards. The following observer's Quit0-minus-Never gap is
strictly positive, in native or original coordinates:

| Solo owner j | Observer i | Gap |
| --- | --- | --- |
| 0 | 3 | 1+q0 |
| 1 | 2 | 2 |
| 2 | 0 | 1 |
| 3 | 2 | 1+3q3 |

AllNever is also not original Nash: any owner can Quit for1.

The self-contained standard-library checker
[CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_STATIONARY_CHECK.py](../experiments/CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_STATIONARY_CHECK.py)
proves that no nonzero q satisfies(1). It constructs the gain polynomials
directly from the printed rational table; no solver, numerical search,
external data or generated box list is an input.

Here is the proof represented by its finite calculation.

1. Enumerate the80 nonzero patterns whose coordinates are fixed0, fixed1,
   or interior. Substitute every fixed coordinate. Pure cases are exact
   scalar sign checks, and the four solo interior cases use the table above.
2. For each remaining pattern, require equality for the interior rows and
   the appropriate weak sign for the fixed rows. Cover the interior variables
   by the larger CLOSED unit cube. Exact linear combinations of the equality
   rows, using the relevant inverse principal matrix, add valid zero tests.
3. Every polynomial has degree at most two in each variable. Convert its
   power coefficients to tensor Bernstein coefficients via

       b_k=sum_(m<=k) c_m product_j binom(k_j,m_j)/binom(2,m_j).

   These coefficients bound its values on the cube, since the Bernstein
   weights are nonnegative and sum to one. A strict inconsistent bound
   discards a box. Common positive denominators are removed, so every
   subsequent arithmetic operation is on integers.
4. A dyadic bisection replaces a degree-two coefficient triple(u,v,w) by
   the integer triples(4u,2(u+v),u+2v+w) and(u+2v+w,2(v+w),4w).
   These are four times the exact coefficients on the two closed halves.
   The accumulated denominator is positive, so every sign test stays exact.
5. When there is no sure coordinate, let S be the interior support and
   t=max_(i in S)q_i. The active equalities have the exact expansion
   F_S=-Gamma_SS q_S+R. If C_i is the sum of absolute degree-at-least-two
   coefficients of row R_i, then |R_i|<=C_i t^2. Consequently a nonzero
   common zero satisfies t<=K t^2, where

       K=max_i sum_j |(Gamma_SS^(-1))_ij| C_j.

   Thus a sufficiently small origin cube contains no nonzero common zero.
   The checker verifies its constant and linear coefficients before using
   this exclusion. For the full support K=159656/25 and t<=2^(-13) suffices.

The search exhausts all patterns after898 nodes, including213 for the
full interior. A million-node or depth limit raises an unresolved-case
failure; it is never accepted as exclusion. Run

    python math/experiments/CODEX_ARBITRARY_TOPOLOGY__SIGNED_FIN4_STATIONARY_CHECK.py

The first output line is `EXACT RATIONAL PASS: all 80 nonzero supports excluded; 898 nodes`.
The code is the retained exact certificate; preliminary numerical and SMT
searches play no part in this theorem.

## 4. No sure Nash root over any actual continuation

Every actual original continuation cap B has the coordinatewise lower bound

    B_i-1>=L_i,
    L_i=min(-1,min_(nonempty A subset I\{i}) Z_i(A)),
    L=(-12,-8,-10,-12).                                  (2)

To prove this, the literal Never response receives1+Z_i(A) if opponents
eventually quit as A, and0 if they Never quit. Subtracting1 gives an average
of the listed passive native rewards and -1. The full cap dominates this
particular response. No properness or optimality of the tail is assumed.

Let Delta_i=Q_i-P_i. A product root evaluated at original continuation
caps B has native gap Delta_i-H_i(B_i-1). Suppose some owner p quits surely.
For every i!=p, H_i=0, so its root gap is just Delta_i. For the sure
owner, replacing B_p-1 by its lower bound L_p can only increase the gap.
Its required inequality is nonnegativity, which this replacement preserves.
With multiple sure owners all H_i vanish. Thus any such actual Nash root
would also satisfy the Nash signs for the FOUR fixed polynomials

    J_i=Delta_i-H_i L_i.                                 (3)

The same checker constructs(3) directly and excludes all65 patterns
containing a sure coordinate, in325 nodes. It reuses only the exact
Bernstein bounds, valid linear combinations of equality rows, and closed
subdivisions from Section3. There is no origin exclusion in this mode,
because every tested pattern has a fixed sure coordinate. Its second
output line is

    EXACT RATIONAL PASS: all 65 sure-root patterns excluded; 325 nodes

Consequently no root with a sure quitter can be Nash against ANY actual
continuation caps for this original game.
In particular, no exact terminal Nash profile can have even one bounded
proper clock, regardless of the other players' possibly infinite supports.

Every absorbing finite-calendar independent profile reaches a sure root:
at least one player's law is proper and finitely supported. In a full
exact terminal Nash profile, a reached root is Nash against the actual
continuation caps, including a sure owner's off-path continuation deviation.
The other rows have zero continuation coefficient at a sure root. Therefore
there is no absorbing exact finite-calendar Nash profile. This argument
allows arbitrary off-path finite punishments; it does not assert a positive
gap for finite-calendar approximate equilibria.

## 5. A positive regret floor for the entire stationary class

There is eta>0 such that every original stationary profile has full
terminal regret max_i(B_i-U_i)>=eta. Suppose otherwise and take a
convergent sequence of stationary hazards with regret tending to zero.

At a nonzero limit with at least two active owners, all response endpoints
and prescribed values are continuous, giving an exact stationary Nash
profile contrary to Section3. At a solo limit, the corresponding explicit
observer gap above persists by continuity. No continuity of the solo
owner's Never response is assumed.

At the zero limit, omit the zero profiles themselves (whose regret is at
least1), normalize alpha=q/sum q, and pass to a simplex limit. Original
prescribed values tend to1+Gamma alpha and forced Quit offers tend to1.
Hence Gamma alpha>=0. For alpha_i<1, opponents are eventually proper and
Never offers tend to1+(Gamma alpha)_i/(1-alpha_i). Vanishing regret gives
alpha_i(Gamma alpha)_i=0. If alpha_i=1 the equality follows from the zero
diagonal. This contradicts the R0 property in Section1.

Therefore stationary profiles cannot supply uniform epsilon equilibria
at arbitrarily small error. This conclusion still says nothing adverse
about unrestricted nonstationary approximate equilibria of this game.

The semantic target and terminal endpoint inspected are
`quittingUniformEquilibriumPayoffConjecture` in
`UniformEquilibrium/Quitting/Conjecture/Basic.lean` and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
No Lean source was edited or built. The next task is the nonstationary
producer for this exact raw table, not another stationary search.
