# Crossed matching joint phases with arbitrary passive rewards

## 1. Game, raw criteria, and conclusions

There are four players I={0,1,2,3}. At each live date each player independently
chooses Continue or Quit using private behavioral randomization and the public
history. A nonempty quitting coalition S absorbs the game at reward vector
r(S)∈ℝ⁴. The live state pays zero, including the date at which the absorbing
state is first selected. A play that never absorbs pays zero. The fifteen
reward vectors are arbitrary finite real vectors subject only to the stated
inequalities. A unilateral deviation can replace the player's entire
behavioral strategy, including arbitrary randomized delay or Never.

Write

    s_i=r_i({i}),                 Γ_ii=0,
    Γ_ij=r_i({j})−s_i             for j≠i.

The notation centers numerical differences only: the original game is not
translated, and Never still pays zero. The s_i may have either sign.

Let f=(01)(23), a=(02)(13), and o=f∘a=a∘f. The two scheduled pairs are
A={0,2} and B={1,3}; a(i) is i's scheduled mate, and
O(i)={f(i),o(i)} is the other pair. Relabelings are allowed. Define

    Π_i=r_i({i,a(i)})−s_i,       K_i=r_i(O(i))−s_i.

The twelve outsider caps are the literal inequalities

    r_i({i}∪T)≤s_i       for every i and every ∅≠T⊆O(i).       (C)

Thus each player has two capped cross-pair participant rewards and one capped
triple participant reward. The other nonsingleton coordinates are unrestricted.

### Weak matching existence theorem

Every raw table satisfying (C) and

    Γ_i,f(i)≥0,       Γ_i,a(i)≤0,       Γ_i,o(i)≤0,
    Π_i≥Γ_i,a(i)                                   for all i   (W)

has a uniform-equilibrium payoff in its original four-player quitting game.
There is no restriction on the signs or magnitudes of the four K_i.
The participant comparison means exactly
r_i({i,a(i)})≥r_i({a(i)}). The conclusion supplies one target v∈ℝ⁴:
for every ε>0 there are a behavioral profile and N₀ such that every N≥N₀
delivers v within ε in every coordinate and permits no unilateral behavioral
gain exceeding ε in the N-date average game. The target precedes ε.

### Strict producer and matrix alternative

The strict version of (W) is

    Γ_i,f(i)>0,       Γ_i,a(i)=−b_i<0,       Γ_i,o(i)<0,
    Π_i>−b_i                                      for all i.   (S)

For a matrix Γ, standard Q means that for every d∈ℝ⁴ there is z≥0 with
d+Γz≥0 and z_i(d+Γz)_i=0 for every i. Under (S), (C), and standard Q,
the proof constructs four proper probabilities q_i∈(0,1). Alternating the
two joint rows

    qᴬ=(q₀,0,q₂,0),             qᴮ=(0,q₁,0,q₃)

gives an exact terminal Nash profile at either starting phase against all
behavioral deviations. Its phase value is a fixed uniform payoff, witnessed
by this same profile at every accuracy. No refinement is needed.

If Γ is not standard Q, the existing original-game matrix implication in
Section 2 gives UE instead. An exact proper two-phase profile is not asserted
in that branch or at the weak boundaries of (W).

### Additional inverse-positive criterion

For any partition into two pairs, not necessarily with the matching sign
pattern, the same exact two-phase conclusion holds if Γ⁻¹ is strictly
positive entrywise, Γ_i,a(i)=−b_i<0, Π_i≥0, K_i≤0, and (C) holds.
All remaining singleton comparisons are unrestricted. This is a second
raw sufficient condition, sharing the strategy and fixed-point proof below.

### Exact pure-pair special case

Under (C) and Π_i≥Γ_i,a(i), either scheduled pair P is a pure terminal
equilibrium whenever K_i≥0 for both i outside P. This conclusion needs no
singleton sign or Q condition. It gives a simpler exact profile on this part
of the class; the matching theorem itself allows all mixtures of passive signs.

The new content is an actual raw-table producer, including signed singleton
and participant rewards and unequal singleton magnitudes, pair increments,
and passive increments. It does not assert completeness of periodic strategies
or settle arbitrary four-player tables.

## 2. Exact source and consumer correspondence

Three existing source statements suffice for the existence chain.

1. Bare failure of original Fin4 UE implies that its actual receiver-row,
   singleton-owner-column matrix Γ is standard Q:
   `isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff`
   in `UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`.
   It assumes no singleton sign, normalization, strategy, or punishment data.
   Its contrapositive provides the non-Q alternative above.
2. Exact phase policy equalities, exact root Nash inequalities, and a strict
   opponent-deleted survival contraction for each player produce an exact
   terminal Nash profile and its fixed uniform payoff:
   `isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
   `isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
   in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.
   Sections 3–6 produce every one of these inputs. Section 6 also gives the
   complete direct behavioral and finite-horizon argument.
3. UE existence is closed under uniform approximation of all reward entries:
   `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
   in `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.
   Its input is, for every δ>0, a table within δ possessing some UE target;
   targets may vary. Its conclusion selects one fixed target for the original
   table. There is no reward-sign or supplied-limit-target assumption.

The matrix convention is `quittingProjectiveLCPMatrix` in
`UniformEquilibrium/Quitting/Projective/SingletonLCP.lean` and
`quittingSingletonMatrix` in
`UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`.
The textbook LCP convention is `IsStandardQ` and `IsStandardLCPSolution` in
`MathUE/LinearProgramming/CopositiveQ.lean`: the residual is d+Γz.
The pure-action endpoints are those in
`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`.

The matrix reduction, positive-odds producer, and raw criteria proved here
are ordinary mathematics, not claims of new Lean-checked declarations.
No strategic object is an unproduced hypothesis of the raw existence theorem.

## 3. Matching Q forces a positive inverse

Assume (S) and standard Q. Use the LCP offset d=−1. Its solution z≥0
satisfies Γz≥1. Each row has exactly one positive coefficient, at f(i),
and all other coefficients are nonpositive. Hence z_f(i)>0 for every i;
since f is a permutation, z>0. Complementarity now gives Γz=1.

Let P be the permutation matrix (Px)_i=x_f(i), so P²=I, and set M=ΓP.
Its diagonal is positive and its off-diagonal entries are nonpositive.
The two strictly negative entries in each row correspond to the two other
matchings; their directed graph is strongly connected. With u=Pz>0,

    Mu=1.

Here is an elementary inverse proof. Put D=diag(M_ii)>0 and
C=I−D⁻¹M≥0. Then Cu=u−D⁻¹1<u. In the weighted sup norm
‖x‖_u=max_i |x_i|/u_i, the operator norm of C is at most
max_i(Cu)_i/u_i<1. Thus

    M⁻¹=(I+C+C²+⋯)D⁻¹≥0.

For each ordered pair of indices, strong connectivity supplies a positive
entry in some power Cⁿ; consequently M⁻¹ is strictly positive entrywise.
Since Γ⁻¹=P M⁻¹, Γ too is invertible with strictly positive inverse.
This argument does not presuppose nonsingularity.

### Signed participant increments and arbitrary passive increments

Set α_i=max(−Π_i,0), K_i⁺=max(K_i,0), and K_i⁻=max(−K_i,0).
Under (S), 0≤α_i<b_i. For finite X∈[0,∞)⁴ put
θ_i(X)=X_a(i)/(1+X_a(i)) and define

    B(X)_ij=Γ_ij+α_i θ_i(X)1_{j=a(i)}
                   +K_i⁺ X_o(i)1_{j=f(i)}.                  (1)

After multiplication by P the K_i⁺ term is a nonnegative diagonal addition.
Thus M(X)=B(X)P remains a Z-matrix with positive diagonal, and M(X)≥M.
Its altered negative entry is −b_i+α_iθ_i(X)<0; the strongly connected
negative graph is unchanged. For u=M⁻¹1>0, M(X)u≥1. The preceding
geometric-series proof applies with this same positive vector, showing that
every B(X)⁻¹ is strictly positive. For each finite R, continuity and
compactness of [0,R]⁴ therefore give constants

    0<m≤B(X)⁻¹_ij≤L        for X∈[0,R]⁴ and all i,j.        (2)

The constants may depend on R. Section 5 chooses a finite outer radius
from raw data before using (2); no uniform inverse bound on an unbounded
domain or unknown cone is asserted.

For the additional inverse-positive criterion, use instead the constant
matrix B=Γ. Its strictly positive inverse has global bounds (2), with
no matching or standard-Q argument needed.

## 4. The four coupled odds equations

Seek X_i>0 and put q_i=X_i/(1+X_i). For i's active and passive phases set

    U_i=s_i+Π_i q_a(i),
    W_i=s_i+(Π_i+b_i)X_a(i).                                 (3)

In both strict cases Π_i+b_i>0, hence W_i>s_i. U_i need not exceed s_i.
At i's active phase, forced Quit gives U_i. Forced Continue gives

    q_a(i)(s_i−b_i)+(1−q_a(i))W_i=U_i.                        (4)

Let {j,k}=O(i) and D_i=(1+X_j)(1+X_k). At the passive phase, Continue
gives the average of s_i+Γ_ij, s_i+Γ_ik, s_i+K_i and U_i, with
the actual singleton, joint, and no-Quit probabilities of j,k. Equating
this value to W_i is exactly

    (Π_i+b_i)X_a(i)D_i
       =Γ_ij X_j+Γ_ik X_k+K_i X_jX_k
           +Π_i X_a(i)/(1+X_a(i)).                           (5)

The term K_i X_jX_k is the simultaneous other-pair event; it has not
been suppressed. Rearranging (5), using Γ_i,a(i)=−b_i, gives ΓX=N(X),
where

    N_i(X)=(Π_i+b_i)X_a(i)(X_j+X_k+X_jX_k)
             +Π_i X_a(i)²/(1+X_a(i))−K_i X_jX_k.             (6)

Move both the negative part of the Π_i square term and the negative part
of −K_i X_jX_k to the left. With B from (1), equations (6) become

    B(X)X=N⁺(X),                                            (7)

    N⁺_i(X)=(Π_i+b_i)X_a(i)(X_j+X_k+X_jX_k)
              +max(Π_i,0)X_a(i)²/(1+X_a(i))+K_i⁻ X_jX_k.

Every term in N⁺ is nonnegative on the positive orthant, and the cubic
coefficient Π_i+b_i is strictly positive. For the additional criterion
Π_i≥0, simply use N⁺=N and B=Γ. In either case a positive solution of
(7) is exactly a solution of the original four passive indifferences (5).

## 5. A compact Brouwer producer

Define F(X)=B(X)⁻¹N⁺(X), or F(X)=Γ⁻¹N(X) in the constant case.
It is continuous and strictly positive on X>0. The two criteria use the
same compact fixed-point map but different valid choices of its outer radius.

### Matching case: bound scaled eigenpoints before choosing the cone

Write h_i=Γ_i,f(i)>0, d_i=−Γ_i,o(i)>0, and c_i=Π_i+b_i>0.
If X>0 and F(X)=ηX with 0<η≤1, then N⁺=ηB(X)X. The two harmful
coefficients of B(X) are strictly negative, giving

    N⁺_i < η(h_i+K_i⁺X_o(i))X_f(i).

But (7) gives N⁺_i≥c_i X_a(i)X_f(i)(1+X_o(i)). Dividing by the
positive X_f(i)(1+X_o(i)) yields

    c_i X_a(i)
       < η(h_i+K_i⁺X_o(i))/(1+X_o(i)) ≤ max(h_i,K_i⁺).

Hence EVERY such scaled eigenpoint satisfies

    ∑_i X_i < L₀:=∑_i max(h_i,K_i⁺)/(Π_i+b_i).              (8)

This statement concerns η≤1, not merely actual roots with η=1.
Choose R=1+L₀ first, then choose m,L from (2) on [0,R]⁴, and put

    κ=m/(4L),
    Δκ={x∈ℝ⁴: ∑_i x_i=1 and x_i≥κ for every i}.

Since κ≤1/4 this is nonempty, compact, and convex. For every X in the
cube and nonzero y≥0, each coordinate of B(X)⁻¹y is at least m∑y_j,
and its coordinate sum is at most4L∑y_j. Its normalization lies in Δκ.

For x∈Δκ and 0<t≤R, tx lies in the cube and N⁺(tx)>0 coordinatewise.
Uniformly in x as t↓0, N⁺(tx)=O(t²), while the inverse is uniformly
bounded. Consequently ∑F(tx)/t→0 uniformly. Choose 0<r<R so that this
ratio is below one for every x∈Δκ at t=r.

### Constant-inverse case: uniform cubic expansion

For the additional general inverse-positive criterion, use the global
minimum and maximum entries of Γ⁻¹ for m,L, and define the same Δκ.
The small-radius estimate holds as before. For large t, each cubic gives

    N_i(tx)≥(Π_i+b_i)κ³t³.

The constant positive inverse implies ∑F(tx)/t→∞ uniformly on Δκ.
In this case choose 0<r<R so the ratio is below one at r and above one
at R. This argument is used only for the constant inverse and K_i≤0,
not for the arbitrary-K matching case.

### The common fixed-point map

In either case, on Δκ×[r,R] define the continuous self-map

    x'=F(tx)/∑F(tx),
    t'=clamp_[r,R](t+1−∑F(tx)/t).                            (9)

Brouwer supplies a fixed point. At t=r the clamp input is strictly larger
than r, so this endpoint cannot be fixed. For the constant inverse the
outer input is strictly below R. In the matching case, a fixed direction
at t=R gives F(Rx)=ηRx with η=∑F(Rx)/R>0. The radial clamp could
fix R only if η≤1, but then (8) would imply R<L₀<R. Thus neither
endpoint can be fixed in either case. At an interior fixed t the clamp
can equal t only when its argument equals t, so ∑F(tx)=t. The x equation
then yields F(tx)=tx. Therefore X=tx>0 solves (7).

All four rates q_i are strictly between zero and one. The proof does not
assume uniqueness, a favorable root selection, an implicit-function branch,
or continuity of a chosen root as the table varies. Rates and a bounded
continuation vector have been produced from raw data.

## 6. Complete strategic verification and uniform horizons

Let V_A have entries U_i on A and W_i on B; let V_B reverse these roles.
Alternate qᴬ,qᴮ from Section 1. All randomizations are the players' own
independent coins. Only the public date parity is used; no correlating
device or information beyond the actual game is needed.

At each active date both action endpoints equal U_i by (3)–(4). At
each passive date the Continue endpoint equals W_i by (5). The forced
Quit endpoint is an average of s_i and the three rewards in (C), so it
is at most s_i<W_i. This checks all sixteen unilateral pure endpoints
and all eight policy coordinates. Every triple coalition obtainable from
a deviator is included. The grand coalition cannot occur in either phase
under a unilateral deviation, which is why its entries can be arbitrary.

The joint survival probability per full period is

    c=∏_i(1−q_i)<1.

Iterating the bounded exact policy recursions proves V_A,V_B are the
actual terminal payoff vectors: the unabsorbed remainder after n periods
is bounded by a constant times cⁿ. This remains valid for signed values.

Fix a deviator i. The other players' probability of surviving a full period is

    ρ_i=∏_{j≠i}(1−q_j)<1.

At every live history, either pure action, and hence any randomized action,
has terminal reward plus surviving prescribed continuation bounded by the
current V coordinate. Iterate these inequalities for any complete behavioral
strategy of i. The residual continuation is bounded in absolute value by a
constant times ρ_iⁿ, independently of the deviator's past choices. It tends
to zero. Thus every behavioral terminal payoff is at most the prescribed
payoff. This includes Never, nonstationary hazards, and unbounded delays.

For explicit uniform finite horizons let M=max_{i,S}|r_i(S)|. The first
opponent Quit has expected date-plus-one at most

    C_i=1+2/(1−ρ_i),

by grouping dates into full periods. Under any deviation absorption is no
later than that opponent Quit. The initial live-zero date is included.
Pathwise the terminal and N-date average rewards differ by at most
2M min(τ+1,N)/N when absorption occurs at date τ. Hence their expected
difference is at most 2MC_i/N, uniformly over all deviations. The on-path
payoff obeys the same bound. With C=max_i C_i, every N-date unilateral
regret is at most 4MC/N, and delivery of V_A has error at most 2MC/N.
One fixed target and one profile therefore satisfy the uniform contract.

This proves the additional inverse-positive theorem directly. In the strict
matching class, standard Q produces the inverse by Section 3 and then the
exact profile. If standard Q fails, Section 2 supplies UE. These alternatives
prove the strict matching existence theorem on the original table.

## 7. Weak boundaries and the pure-pair arm

Assume (W). For δ>0 form r^δ by increasing only r_i({f(i)}) by δ and
decreasing r_i({a(i)}) and r_i({o(i)}) by δ, for every i. Own singletons
and all nonsingleton coordinates are unchanged. This is twelve independent
off-diagonal singleton changes, each of absolute size δ.

All singleton signs are now strict. With b_i=−Γ_i,a(i)≥0,

    b_i^δ=b_i+δ>0,        Π_i≥−b_i>−(b_i+δ).

The arbitrary K_i and all caps (C) are unchanged. The strict theorem gives
UE for every r^δ. The exact reward-closure theorem of Section 2 gives one fixed
uniform payoff for r. This proves the weak existence conclusion without
asserting a limiting periodic strategy or interchanging target quantifiers.

For the pure-pair alternative, make P quit surely at date zero and all
outsiders Continue. A participant's unilateral withdrawal leaves its mate
quitting, giving r_i({a(i)})≤r_i(P). An outsider's prescribed payoff is
r_i(P)=s_i+K_i≥s_i, while its simultaneous join is at most s_i by (C).
There is no live continuation after that date under any one deviation.
The profile is therefore exact terminal and N-date Nash, delivers
(N−1)r(P)/N at N≥1, and has fixed target r(P) with error at most M/N.

For clarity, the signed common-parameter subclass with favorite singleton
gap H b_i, both harmful gaps −b_i, H>2, common Π_i/b_i>−1 and common
K_i/b_i=K is exhausted by the matching theorem for every real K;
the K≥0 arm also has the pure-pair exit. A symmetric root formula is not
needed for existence coverage.

## 8. Exact boundary tests

### Signed values, cap equalities, and arbitrary unused rewards

Let Γ have favorable entry 13/4 and both harmful entries −1 in every row;
take any signed singleton vector, for example s=(−4,−1,0,7). Set Π_i=−1/2
and K_i=0, and set all twelve capped rewards equal to s_i. All remaining
reward coordinates can be arbitrary. Then X_i=1 and q_i=1/2 give

    U_i=s_i−1/4,              W_i=s_i+1/2.

The scheduled-mate coefficient in B is −3/4, so BX has every coordinate
3/2. Also N⁺_i=(1/2)(1+1+1)=3/2. Active endpoints equal U_i; passive
Continue equals W_i and passive Quit equals s_i. Negative own singletons,
negative participant increments, K=0, and all cap equalities coexist.
The below-singleton active value causes no deviation at an inserted date,
since the construction inserts no additional dates.

A second signed check uses favorable gap17/4, harmful gaps−1, Π_i=−1/2,
K_i=−1, and X_i=1. Then BX=N⁺=(5/2)1. For s_i=1, active value is3/4
and passive value3/2. Both examples retain zero Never payoff.
The caps cannot simply be discarded: in this second example, take all capped
rewards initially equal to1, then increase one outsider triple-join reward
to4. Its passive Quit endpoint becomes7/4, exceeding W_i=3/2. The
unchanged profile is no longer Nash outside the stated raw class.

### Mixed passive signs with negative participant increments

Take harmful gaps−1, Π_i=−1/2, favorable gaps
(9/4,11/4,17/4,15/4), K=(1,1/2,−1,−1/2), and X_i=1.
The permuted singleton matrix is strictly diagonally dominant, with its
same strongly connected negative graph, so its inverse is positive.
For any signed s, U=s−(1/4)1 and W=s+(1/2)1. Directly,

    B(X)X=N⁺(X)=(3/2,3/2,5/2,2).

All caps may be at equality. Each scheduled pair has one negative-K and
one positive-K outsider, so neither pure scheduled-pair alternative applies.
This checks mixed passive signs together with negative participant increments.

### Why weak existence does not imply the same proper producer

Let favorable gap H>2, harmful gaps−1, Π_i=−1 and K_i=0. The inverse
of Γ is strictly positive, but the original odds equations have no positive
solution, because

    ∑_i(ΓX)_i=(H−2)∑_i X_i>0,
    ∑_iN_i(X)=−∑_i X_i²/(1+X_i)<0.

This lies on Π_i=−b_i. It refutes replacing the strict inequality in
the proper-profile conclusion by a weak one, not the weak UE theorem.
When (C) holds either scheduled pair is itself a pure terminal equilibrium.

## 9. A complete asymmetric coverage fixture

The following table specifies all sixty coordinates; no unspecified reward
is used in the coverage claims. All s_i=1. The favorable singleton gaps are
(249/40,53/8,53/8,53/8) and both harmful gaps are−1. Put
Π_A=145/32, Π_B=99/14.

| S | r(S) |
|---|---|
| 0 | (1,61/8,0,0) |
| 1 | (289/40,1,0,0) |
| 2 | (0,0,1,61/8) |
| 3 | (0,0,61/8,1) |
| 01 | (−1,−1,0,0) |
| 02 | (177/32,0,177/32,0) |
| 03 | (−1,0,0,−1) |
| 12 | (0,−1,−1,0) |
| 13 | (2,113/14,0,113/14) |
| 23 | (0,0,−1,−1) |
| 012 | (−10,1/2,−10,0) |
| 013 | (1/2,−10,0,−10) |
| 023 | (−10,0,−10,1/2) |
| 123 | (0,−10,1/2,−10) |
| 0123 | (−11,−12,−13,−14) |

Here K=(1,−1,−1,−1), and every sign, participant comparison, and cap is strict.
The exact odds, rows, and phase values are

    X=(1/4,1/5,1/4,1/5),
    qᴬ=(1/5,0,1/5,0),        qᴮ=(0,1/6,0,1/6),
    V_A=(61/32,183/70,61/32,183/70),
    V_B=(305/128,61/28,305/128,61/28).

Substitution verifies (5) in every coordinate, including the positive K₀.
At the moved system (7), B(X)X=N⁺(X)=(167/200,193/160,7/8,193/160).
At phase A each passive Quit endpoint is17/50, below its Continue value183/70;
at phase B each
passive Quit endpoint is31/72, below its Continue value305/128. Both
active endpoints equal the displayed active values. The raw strict
inequalities persist throughout some full sixty-coordinate open reward
neighborhood. The raw theorem covers that neighborhood without requiring
continuous selection of these particular rates or an explicit radius.

### Finite matrix exits

Set g=249/40 and H=53/8. The actual singleton matrix is

    Γ = [[0,g,−1,−1],
         [H,0,−1,−1],
         [−1,−1,0,H],
         [−1,−1,H,0]].

Its favorite-permuted matrix ΓP has diagonal (g,H,H,H), two off-diagonal
entries−1 per row, and one zero. It is strictly diagonally dominant. The
geometric-series argument of Section 3 with u=1 proves Γ⁻¹>0. Directly,

    det Γ=33583397/20480>0.

Thus the negative-determinant premise of
`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse` in
`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`
fails. Every principal submatrix of size at least two is nonsingular:
pair determinants are−gH,−H², or−1; triple determinants are g+H=257/20
or2H=53/4. A homogeneous LCP solution with support at least two would
give a singular principal; a singleton support fails since every column
has a negative off-diagonal entry. Hence Γ is R₀. Its degree is+1 by
`r0Degree_eq_sign_det_of_nonnegative_inverse` in
`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`.

A harmful principal pair is [[0,−1],[−1,0]]. It has no nonzero homogeneous
LCP solution and is not Q: offset−1 has no solution. Thus an all-principal
Q-or-homogeneous matrix criterion fails. Every triple inverse diagonal is
negative, since its diagonal cofactor is a negative pair determinant and its
triple determinant is positive. This fails the required child-inverse premise
of `exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
These are comparisons with actual matrix exit hypotheses, not a claim that
Q or a positive inverse alone implies nonexistence.

### Pure, child, premium, and weighted-floor tests

A premium trap means a nonempty set T such that each i∈T has some
coalition S⊆T containing i with r_i(S)>s_i. The only traps here are
02,13,I. In a triple its unmatched player has no positive participant
premium; the full set has a positive-premium scheduled pair for every player.
Consequently the greatest trap is the full four-player set, excluding
criteria requiring at most two or three players in that greatest core.

No pure coalition is Nash. A singleton's active mate profits by joining;
pair02 is profitably joined by1 or3, and pair13 by2, each with gain1/2.
In any other pair a member can leave its payoff−1 for a nonnegative
singleton payoff. In any triple
a scheduled-pair member can leave−10 for0. A grand participant can leave
its negative payoff for0. All Never is defeated by an own singleton1.

Every proper nonempty child has an exact terminal Nash profile with zero
joint Never and some profitable omitted player. If the child cuts a
scheduled pair, choose j in the child with a(j) omitted and make j quit
surely. All other child members obtain0,289/40, or61/8 by waiting and−1
by joining, so this is child Nash. The omitted mate gains177/32 or113/14 by joining
instead of receiving0. The only children cutting neither pair are02,13;
their sure joint exits are child Nash, and an omitted player gains1/2
(player1 for child02 and player2 for child13).
Thus for each proper child there is some omitted player whose gain cannot
be bounded universally by any fixed nonnegative weighted child-regret sum
plus a finite multiple of joint Never. This does not exclude a separately
chosen safe child profile.

At either sure active pair all active Quit payoffs strictly exceed their
own singletons. This violates product-low and any supportwise nonpositive
weighted-premium test with nonzero weights on that support. Every player
has a negative grand-coalition participant premium, so no nonempty protected
set whose members have all participant premiums nonnegative is available.
At the full trap, every nonzero nonnegative weighted grand premium is
negative, violating a global weighted-floor test. Criteria excluding pair
traps fail at02,13. For a larger-trap charge test requiring
∑_{i∈I\{j}}(r_i({i,j})−s_i)<0, this sum is Π_a(j)−4>0.

For a nonnegative weight λ, weighted upper bounds
∑λ_i r_i(02)≤∑λ_i s_i and ∑λ_i r_i(13)≤∑λ_i s_i would sum to
(Π₀+1)λ₀+∑_{i≠0}(Π_i−1)λ_i≤0. Every coefficient is positive,
forcing λ=0. This also excludes weighted
terminal-upper-bound criteria requiring a nonzero such weight, including
`exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`.

### Response quotients, including positive affine transports

At the all-sure vector the zero-discount response displacement is
r_i(I)−r_i(I\{i}), namely−11,−12,−13,−14. The all-sure vector is
constant on every block partition, so every nondiscrete response-invariant
partition fails. Fin4 has fourteen such partitions.

The exclusion even survives arbitrary positive playerwise affine changes
r'_i(S)=c_i r_i(S)+d_i. Indeed the response's derivative at zero is
minus the singleton row Γ_i. Equality of response rows on a block cube
forces equality of their sums over each source block; this is
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
Sum over all blocks. Each row sum is h_i−2>0, so c_i(h_i−2) must
agree within a block. But the four ratios of original all-sure displacement
to row sum are

    −440/169,       −96/37,       −104/37,       −112/37,

which are pairwise distinct; the first two differ by−56/6253. Equality of
transformed all-sure responses is therefore impossible within a nontrivial
block. Translations cancel. No nondiscrete block can exist. This is a raw
nonmembership test, not an assertion that arbitrary reward translations
preserve the game's zero-Never equilibrium problem.

### Other concrete sign and local-producer tests

Each row has two negative off-diagonal singleton comparisons, contradicting
the unique below-own partner property
`PairedCycle.RawRegion.eq_partner_of_singleton_lt` in
`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`.
The sole-positive graph is two transpositions, not a favorable Hamiltonian
four-cycle. Reciprocal signs agree on every pair, rather than being opposite
as in integral-tournament singleton patterns. Deleting any player leaves
its favorite mate with two negative child comparisons, excluding every
deleted cyclic-child pattern requiring one positive and one negative entry
per child row. These tests survive relabeling and positive row scaling.

The visible period-three affine cylinder in
`exists_periodThreeClearedGapData_and_uniformPayoff_of_visible_affine_reward`,
`UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreePositiveAffineCylinder.lean`,
has favorable/harmful singleton-gap ratio less than4 throughout its
radius1/50000000 visible box: its central own, favorable, and harmful
singleton levels are1,4,0, so at radius ε the ratio is at most
(3+2ε)/(1−2ε)<4. These coordinates are visible. Our ratio is53/8>4
in every row except row0, whose ratio249/40 also exceeds4. Singleton
differences cancel translations and their ratio cancels positive scaling.

A separate four-phase branch with two proper solo players a,b has the
following intrinsic necessary condition if its phase floors obey
V_D,a>s_a and V_B,b>s_b and its Continue equalities are

    s_a=w r_a({b})+(1−w)V_D,a,
    V_B,b=z r_b({a})+(1−z)s_b,          0<z,w<1.

These identities force Γ_ab<0<Γ_ba. No relabeling of this fixture has
such a pair. This excludes precisely branches with these stated floor
identities; it does not exclude every two-joint or four-phase schedule.

For every ordered crossed selected pair(i,j), its lower polynomial face
has a pure negative witness. If j≠f(i), put favorite f(i) surely Quit
and every other opponent Continue; the selected partner is absent and the
response is r_i({i,f(i)})−r_i({f(i)}), namely−329/40 for i=0 and
−69/8 for the others. If j=f(i), instead put
the harmful nonactive partner o(i) surely Quit; the response is−1.
Thus even nonnegative lower-face guards fail, including
`QuittingHalfWeakPolynomialGuards` in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`
and `QuittingOneSidedWeakUnitGuards` in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.
The stronger strict/unit/half raw guards fail at the same points. The
`halfCeiling_fullRewardBall_source` and `unitCeiling_fullRewardBall_source`
in `UniformEquilibrium/Quitting/Examples/GuardedCrossedResponseFullRewardNeighborhood.lean`
produce these excluded guards. The literal `sharpReward` family in
`UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskyStationaryClosure.lean`
has a zero off-diagonal singleton comparison; this fixture has none.

Every auxiliary blocker choice in `IsQuittingConditionalFaceGapRange` in
`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`
also fails. Its Continue upper bound covers every passive coalition and
therefore is at least289/40. Its Quit lower bound without the blocker is at
most1, by the empty background, and its Quit lower bound with the blocker
is at most r_i(I)<0, by the maximal background. For a blocker lower hazard
ℓ∈(0,1), the required strict lower-face inequality is

    ContinueUpper_i < (1−ℓ)QuitWithoutLower_i+ℓ QuitWithLower_i.

The left side is at least289/40 and the right side is at most1, a contradiction
for every blocker and every permitted choice of auxiliary range bounds.

### Exact exclusion of proper-three stationary supports

Any three-player support contains one full scheduled pair i,k and a third
player j favorable to i; k's favorite is omitted. Let their proper hazards
be a,c,x respectively, and let Π be the common premium of that full pair.
Player k's Never payoff is zero, so its Quit value must vanish:

    1+Πa−2x−(Π+9)ax=0.

Writing D(x)=(Π+9)x−Π gives

    a=(1−2x)/D(x),           (Π+1)/(Π+11)<x<1/2.

To see the range, note Π<9: D<0 would require x>1/2 for a>0, impossible
since Π/(Π+9)<1/2. Thus D>0 and x<1/2; a<1 gives the lower bound.
For player i, direct endpoint evaluation gives

    Q_i=D(x)(a−c),
    N_i=F_i x(1−c)/(x+c−xc)>0,

where N_i is its Never payoff and F_i is289/40 or61/8. The positive
passive entry r₀(13)=2 is never used by the designated k in these four
support calculations: its two opponents form a nonscheduled pair with
passive reward0. Equality forces c<a<1, hence Q_i<D(x)(1−c), whereas
N_i≥F_i x(1−c). Both actual premiums satisfy0<Π<9 and Π+F_i>9,
so F_i x>D(x) for every x<1/2. Contradiction.
Thus all four proper-three supports fail, excluding every relabeling of
`PairedCubicStationaryExample.exists_local_stationary_branch` in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`.
No exclusion of arbitrary full-support stationary profiles is claimed.

Finally, the singleton signs fix the favorite matching and both harmful
gaps equal−1. The only eligible scheduled matching is02/13, since03/12
has Π_i=−2<−1. Its K₀=1 cannot be relabeled into the additional condition
that all passive increments be nonpositive. Neither scheduled pair has two
nonnegative-K outsiders. A common-normalized-premium subclass would require
equal Π_i, but145/32≠99/14; its common singleton-ratio condition also fails.
The new class therefore includes an actual mixed-sign passive region beyond
those two simpler mechanisms, not only a different root at a symmetric table.

## 10. Formalization handoff and limits

The main raw predicate should contain exactly (W), (C), and the selected
two disjoint matchings; equivalently it may quantify over player relabelings.
It contains no rates, continuation values, matrix inverse, root choice,
periodic certificate, or desired equilibrium conclusion. A strict helper
uses (S). The additional general inverse-positive predicate is separate.

The proof outputs needed by the existing periodic compiler are four proper
rates, the two phase vectors (3), their eight policy identities, their sixteen
endpoint inequalities, and all four deleted-player contractions. The proposed
ordinary-mathematics chain is: actual Q gives a positive inverse; the matrix
family, raw scaled-eigenpoint bound, and radius-first simplex-times-radius
map produce positive odds;
these produce the literal cyclic certificate; the exact compiler supplies
the fixed target. The non-Q branch uses the contrapositive of the named
original-source theorem. The weak predicate is discharged by the twelve-entry
perturbation and the named reward-closure theorem, not a strategy limit.

Useful finite regression tests are the complete table in Section 9, the
signed K=0 test, and the excluded Π=−b proper-profile boundary. The source
and consumer declarations cited above are existing library dependencies;
this packet does not assert that the new raw producer has been checked in Lean.

The matching construction covers every real passive-increment vector K,
including the mixed-sign case where every scheduled pair has a negative-K
outsider. It does not cover arbitrary singleton sign graphs, violations of
the participant comparison, or arbitrary outsider joining rewards. It does
not require or prove uniqueness of odds. The exact periodic conclusion is
restricted to the stated strict construction branches, while weak boundary
and non-Q branches assert original-game UE existence. The coverage tests
exclude the stated raw producers, not all conceivable strategies in their
broad stationary, child, or periodic languages. The arbitrary Fin4 conjecture
remains open.
