# Successive direct minimizers: an actual concatenation test

Identity: CODEX_NOETHER_SUPPORT.

Status: bounded law-changing mechanism stopped at a precise missing
cross-source cap comparison. The complete response formula and its use of
true finite-domain global minimality are valid. No decrease, nonsummable
improvement budget, selector, or counterexample to the finite-menu question
is proved. No Lean, question, or export edit.

## 1. The actual minimizing source

The question is
[FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION](../questions/FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md):
four independent stopping laws, own singletons s=(1,0,0,0), arbitrary
finite real remaining rewards with absolute bound M≥1, and zero Never.
All unilateral behavioral replacements are allowed. On
F_N={0,…,N−1,Never}, N≥1, minimize the ORIGINAL unrestricted objective

    f_N(p)=max(E_N(p), W_0(p)+D_0(p)−U_0(p)),
    V_N=min_{p∈∏_i Δ(F_N)} f_N(p).

The exact scalar identity is
`singlePivot_fullExploitability_eq_max_menuExploitability_scalar` in
`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`.
It was read with its canonical-singleton hypothesis and imports. The
nonpivot cap includes every late date through Never; the pivot has the
additional late singleton term. Finite simplex compactness and continuity
of this finite maximum give an attained minimum. Literal menu inclusion
gives 0≤V_(N+1)≤V_N≤1, the last bound using all-Never.

Choose actual global minimizers P_N and P_(N+1), with no exact Nash or
compensated equations imposed. The tested operation concatenates these
two independently selected laws, in either chronological order. This uses
the two global minimizers themselves, not an alleged exactification of them.

The narrow lookup first read the existing
[recutting test](CODEX_TARSKI_PREMIUM__FINITE_MENU_RECUTTING_AND_ACTUAL_VALUE_TEST.md),
[minimax exchange test](../feedback/FIN4_SINGLE_PIVOT_RAW_MINIMAX_EXCHANGE__BY_CODEX_FRECHET_CYCLE.md),
[joint Never-release test](CODEX_HILBERT__GLOBAL_MAXIMUM_JOINT_NEVER_RELEASE_BOUNDARY.md),
and [repeated-block test](CODEX_HILBERT__GLOBAL_MAXIMUM_REPEATED_BLOCK_TEST.md).
They prevent substituting bookkeeping, correlated convexification, a
supplied cap comparison, or a total-debt minimum for this source. The
two-source formula below is a specialization of existing finite-word
splicing, not a new general semantic interface.

## 2. The actual independent law change and its full cap

For a law P on F_n and Q on F_k, independently for each player sample
T_i^P and T_i^Q. Quit at T_i^P when finite; if T_i^P=Never, instead use
n+T_i^Q when finite, and Never otherwise. Denote this actual product law
P▷Q. It belongs to F_(n+k). There is no common random selector between
players; prescribed joint survival merely makes the second block reached.

Write

    z_i(P)=P_i(Never),    R(P)=∏_i z_i(P),
    c_i(P)=∏_{j≠i}z_j(P),
    F_i(P)=max payoff of pure dates 0,…,n−1 against P_−i,
    W_i(P)=payoff of Never against P_−i.

Since s_i≥0 in this canonical question, the old unrestricted cap is

    B_i(P)=max(F_i(P), W_i(P)+c_i(P)s_i).

For the concatenated law, the EXACT complete formulas are

    U_i(P▷Q)=U_i(P)+R(P)U_i(Q),
    B_i(P▷Q)=max(F_i(P), W_i(P)+c_i(P)B_i(Q)).          (1)

A deviation stopping during the first block has its old pure-date payoff.
A deviation waiting past that block receives the old Never payoff on
earlier opponent absorption, and can use ANY complete response against Q
on opponent survival. The latter coefficient is c_i(P), not R(P).
This includes every date beyond both menus and Never. Taking the supremum
over complete responses gives (1), with no cap-attainment assumption.

Thus, with Ψ(P,Q) equal to

    max_i {
      F_i(P)−U_i(P)−R(P)U_i(Q),
      W_i(P)−U_i(P)+c_i(P)B_i(Q)−R(P)U_i(Q)
    },                                                        (2)

global minimality gives the actual larger-menu comparison

    V_(2N+1)≤min(Ψ(P_N,P_(N+1)), Ψ(P_(N+1),P_N)).       (3)

The reverse order is another legal independent law. It does not share a
random block index with the first order. Equations (1)–(3) retain the
global minimizer hypothesis, but do not yet show a decrease below V_(N+1).

## 3. What a hypothetical positive limit really supplies

Let m=lim_N V_N. Full finite-law approximation gives

    m=inf_{p actual complete product law} max_i(B_i(p)−U_i(p)).

One can see this directly by censoring each player's late finite mass to
Never. The total changed mass tends to zero; bounded coupling controls
both prescribed payoffs and EVERY response payoff, hence full caps and
exploitability. The exact existing source is
`exists_finiteDeadlineTimingProfile_approximation` in
`UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`.

If m>0, every convergent subsequence of the full pairs (U(P_N),B(P_N))
ends at a genuine global MAX-exploitability minimum in the compact
terminal-semantic carrier. The relevant source is explicitly
`minimumTerminalSemantic_exploitabilitySingletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`.
Its minimized objective is `quittingTerminalSemanticExploitability`, NOT
total debt, and its conclusion is m≤B_i−s_i at that minimum.

It follows, for any chosen sequence of direct global minimizers, that

    B_i(P_N)≥s_i+m/2            for all i and all sufficiently large N. (4)

Otherwise a low-cap subsequence, followed by compact extraction of its
full semantic pair, contradicts the named MAX theorem. No finite P_N is
claimed to attain m, and no total-debt margin or punishment-normality
reduction is used.

The same source also immediately gives U_i≥s_i at every limiting minimum:

    U_i−s_i=(B_i−s_i)−d_i≥m−d_i≥0.

Consequently liminf_N U_i(P_N)≥s_i. This is a limiting statement, not an
assertion that each finite minimizer has U_i≥s_i exactly. For every η>0,
all sufficiently late minimizers have U_i≥s_i−η. Thus the prescribed
concatenation contribution is asymptotically nonnegative in every
coordinate, and in the pivot coordinate is at least R(P)(1−η).
Nevertheless the limiting tail term in the Never cap branch is

    c_i(P)B_i(Q)−R(P)U_i(Q)
      =c_i(P)[d_i(Q)+(1−z_i(P))U_i(Q)]≥0.

The favorable payoff sign does not cancel the differently scaled new cap.

For such late source pairs, (1) and (4) imply

    B_i(P_N▷P_(N+1))≥B_i(P_N).

The appended minimizer cannot lower any old cap. Its only possible debt
improvement comes from the prescribed payoff increment R(P_N)U_i(P_(N+1)).
Since U_i≤M, this yields the exact descent-capacity bound

    f(P_N▷P_(N+1))≥V_N−M R(P_N),                    (5)

and the analogous reverse-order bound. If R(P_N)=0, this order cannot
improve on V_N at all. Small prescribed reach does not make the second
block harmless for deviations: c_i(P_N) can remain much larger than R(P_N).

There is also a literal blocking branch. If a nonpivot i is a maximal
debtor of P, B_i(P)=W_i(P), c_i(P)>0, and Q has d_i(Q)>0 and U_i(Q)≥0,
then (1) gives

    d_i(P▷Q)≥d_i(P)+c_i(P)[d_i(Q)+(1−z_i(P))U_i(Q)]>d_i(P). (6)

This is a conditional no-descent calculation, not a constructed positive
global minimum. The global minimizing property has not eliminated this
Never-active branch or supplied a favorable alternative Q on the adjacent
menu. Merely knowing f(Q)≤f(P) does not control it.

## 4. Exact STALL and EXACT_EXAMPLE calibration

I read both [STALL](../gpt/STALL.md) and
[EXACT_EXAMPLE](../archive/EXACT_EXAMPLE.md). Their exact deadline Nash
profiles are NOT silently substituted for P_N. They test the complete
formula and expose the danger of a falsely contracting cap recursion.

In both examples the exact deadline equilibrium has one nonzero root at
the last displayed date. Let z be its Never vector, R=∏z_i,
c_i=∏_{j≠i}z_j, and U its payoff. For each core player its displayed
finite best reply and Never give U_i. For player 3, Never gives U_3 and
the finite cap is no larger. The full cap is B_0=U_0+c_0 and B_i=U_i otherwise.
Concatenating the exact sources from any two deadlines therefore has debts

    d'_0=c_0²+(c_0−R)U_0,
    d'_i=(c_i−R)U_i                 for i≠0.          (7)

For EXACT_EXAMPLE,

    z=(5/7,3/7,6/7,1),
    U=(31/7,19/7,34/7,31/49),
    old debt=(18/49,0,0,0),
    concatenated debt=(1440,2280,510,0)/2401.

The new maximum 2280/2401 is larger than 18/49. In particular one cannot
bound the new cap by an old-cap multiple using joint rather than deleted
survival. Yet this is not a global-minimizer falsifier: the example's
explicit geometric finite laws give V_N≤2^(−N), and for N≥2 its exact
deadline Nash profile is demonstrably not a global f_N minimizer.

For STALL, put θ=3/2−√2,
z=(1−2θ,1−θ,1−4θ,1), and U_i=3(1−c_i) for core i.
Then R=35√2−49 and old maximum c_0=21/2−7√2. Equation (7) gives

    d'=( (−6503+4599√2)/2, −11349+8025√2,
         −1332+942√2, 0 ).

This particular two-block change improves the displayed source. But the
source is not a global minimizer even on F_1: having only the pivot quit
at date zero with probability 1/2 gives full debts (1/2,0,1/2,0), below
c_0>1/2. The published geometric laws further give V_N≤(3/4)^N.
Neither test exhibits a positive limiting V_N. Exact symbolic arithmetic
checked (7) and both displayed debt vectors; numerical values are not
used as proof.

## 5. Precise stopping point

The potential improvement is an actual joint-law change with unrestricted
responses, and (3) is its correct global-minimum comparison. However,
global minimality at two successive menus supplies no upper bound forcing
the right side of (3) below V_(N+1). The unresolved term is exactly

    c_i(P)B_i(Q)−R(P)U_i(Q)

together with the old Never/head cap slack in (2), not a missing local
stationarity condition. Under a hypothetical positive limit, (5) also
limits every possible improvement by the old joint-Never reach. No
nonsummable lower reach budget follows from the inspected minimizer facts.
Since the move enlarges N to 2N+1, any proposed rate would moreover need
to be nonsummable along actual concatenation lengths, not merely summed
over overlapping pairs of adjacent input menus.

This is the exact failed inference: "two globally minimal source blocks
have no worse full debt, therefore appending one to the other contracts
the original objective." The second clause does not follow from their
global optimality and the valid formulas; the Never-active arm (6) retains
the opposite sign. No table with a hypothetical positive global minimum
has been manufactured to strengthen that statement into a class no-go.

The source counterpart of (1) is
`quittingTerminalSemanticPair_literalRootStack_eq_wordPrefix`, together
with `quittingFiniteRootWordPayoff_sub_eq_jointSurvival_mul`, in
`UniformEquilibrium/Quitting/Root/FiniteWordSemanticSplice.lean`.
Those declarations and the scalar/MAX sources above were inspected, not
built. This cross-concatenation test is stopped; a favorable cross-cap
inequality or reach budget is not promoted into a new hypothesis packet.
