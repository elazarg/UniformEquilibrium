# Matching joint phases with arbitrary passive pair rewards

Identity: CODEX_BROUWER. Complete proof candidate in ordinary mathematics,
not checked in Lean. The result below removes the passive-sign restriction
from the strict matching producer. Its proof uses a finite outer-radius
bound for scaled fixed points, not uniform expansion at infinity.

## Exact question and statement

Let I={0,1,2,3}, f=(01)(23), a=(02)(13), and o=f∘a=a∘f. The game has
one live state, independent private Continue/Quit actions, public histories,
zero live-stage and Never rewards, and arbitrary finite real reward vectors
r(S) for all fifteen nonempty quitting coalitions. Deviations replace one
player's entire behavioral strategy. Write

    s_i=r_i({i}),       Γ_ii=0,       Γ_ij=r_i({j})−s_i,
    h_i=Γ_i,f(i),       b_i=−Γ_i,a(i),       d_i=−Γ_i,o(i),
    Π_i=r_i({i,a(i)})−s_i,           K_i=r_i({f(i),o(i)})−s_i.

Assume h_i,b_i,d_i>0 and Π_i>−b_i for every i. Impose the twelve
literal outsider caps

    r_i({i}∪T)≤s_i       for every i and ∅≠T⊆{f(i),o(i)}.     (A)

There is NO restriction on any K_i. Own singletons may be signed; all other
reward entries, including all grand-coalition entries, are unrestricted.

Claim: every such raw table has a uniform-equilibrium payoff in its original
game. If Γ is standard Q, the proof produces four proper rates q_i∈(0,1),
one exact period-two terminal Nash profile alternating pairs02 and13,
and its one fixed uniform target, with the same profile for every accuracy.
If Γ is not standard Q, the original-game matrix exit supplies UE without
a claim that this proper profile exists. The weak raw closure

    Γ_i,f(i)≥0,       Γ_i,a(i)≤0,       Γ_i,o(i)≤0,
    Π_i≥Γ_i,a(i)

with (A) and arbitrary K also has UE, but no proper-profile conclusion is
asserted at its boundaries.

## Original-source and positive-matrix reduction

Standard Q means: for every offset e∈ℝ⁴ there is z≥0 with e+Γz≥0 and
z_i(e+Γz)_i=0. Under the actual no-UE hypothesis it is supplied by
`isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff`
in `UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean`.
This theorem has no singleton sign, normalization or strategic premise.

At offset−1, Q supplies Γz≥1. Each row has its sole positive entry at
f(i), so z_f(i)>0 for every i. Thus z>0, and complementarity gives Γz=1.
For the permutation matrix (Px)_i=x_f(i), put M=ΓP and u=Pz>0.
Then Mu=1. M is a Z-matrix with positive diagonal h_i and a strongly
connected negative graph supplied by the two harmful matchings.

For any Z-matrix T with positive diagonal and Tu>0, set D=diag T and
C=I−D⁻¹T≥0. Then Cu=u−D⁻¹Tu<u. In the u-weighted sup norm C is a
strict contraction. Its Neumann series proves T⁻¹=(∑_{n≥0}Cⁿ)D⁻¹≥0.
If its negative graph is strongly connected, every inverse entry is strictly
positive. Applying this to M proves Γ⁻¹=P M⁻¹>0 without assuming
nonsingularity in advance.

## Modified equations for arbitrary K

Put

    c_i=Π_i+b_i>0,       α_i=max(−Π_i,0)<b_i,
    K_i⁺=max(K_i,0),     K_i⁻=max(−K_i,0).

For X∈[0,∞)⁴ let θ_i(X)=X_a(i)/(1+X_a(i)) and define

    B(X)_ij=Γ_ij
        +α_i θ_i(X)1_{j=a(i)}+K_i⁺ X_o(i)1_{j=f(i)},         (B)

    N⁺_i(X)=c_i X_a(i)(X_f(i)+X_o(i)+X_f(i)X_o(i))
        +max(Π_i,0)X_a(i)²/(1+X_a(i))
        +K_i⁻ X_f(i)X_o(i).                                 (N)

The extra favorite coefficient becomes a nonnegative diagonal addition in
B(X)P. Its scheduled-mate coefficient stays −b_i+α_iθ_i(X)<0; the
other harmful coefficient stays −d_i<0. Hence B(X)P remains a Z-matrix
with the same strongly connected negative graph and positive diagonal.
Moreover B(X)P≥M, so B(X)Pu≥1. The preceding inverse argument proves
that B(X)⁻¹ is strictly positive for every finite X≥0.

For positive X put q_i=X_i/(1+X_i) and seek phase values

    U_i=s_i+Π_i q_a(i),       W_i=s_i+c_i X_a(i)>s_i.          (V)

At i's active phase both action endpoints equal U_i because

    q_a(i)(s_i−b_i)+(1−q_a(i))W_i=U_i.

At its passive phase the Continue identity is exactly

    c_i X_a(i)(1+X_f(i))(1+X_o(i))
      =h_i X_f(i)−d_i X_o(i)+K_i X_f(i)X_o(i)
           +Π_i X_a(i)/(1+X_a(i)).                           (E)

Rearrangement gives ΓX=N with the negative term −K_i X_f(i)X_o(i).
Moving that term's negative part and Π_i's negative rational part to the
left gives precisely

    B(X)X=N⁺(X).                                            (F)

No term of either sign has been deleted. Simultaneous quitting by the other
scheduled pair is the K_i term in (E).

## The finite outer bound for scaled fixed points

Define F(X)=B(X)⁻¹N⁺(X). It is continuous on X≥0 and strictly positive
on X>0. The following statement concerns SCALED fixed points, not only
solutions of (F): if X>0 and F(X)=ηX with 0<η≤1, then

    c_i X_a(i)<max(h_i,K_i⁺)             for every i.         (R1)

Indeed N⁺=ηB(X)X. The scheduled-mate and other harmful coefficients
of B(X) are strictly negative, so

    N⁺_i < η(h_i+K_i⁺X_o(i))X_f(i).

On the other hand, (N) gives

    N⁺_i ≥ c_i X_a(i)X_f(i)(1+X_o(i)).

Dividing by the positive X_f(i)(1+X_o(i)) proves

    c_i X_a(i)
      < η(h_i+K_i⁺X_o(i))/(1+X_o(i))
      ≤ max(h_i,K_i⁺).

This is (R1). In particular every such scaled fixed point satisfies

    ∑_i X_i < L₀:=∑_i max(h_i,K_i⁺)/c_i.                   (R2)

The bound is computed solely from raw data. It neither assumes a favorable
solution nor depends on a cone truncation constant.

## Brouwer map: radius first, inverse bounds second

Choose R=1+L₀ FIRST. On the compact cube [0,R]⁴ every B(X) remains
invertible with a strictly positive inverse. Continuity therefore gives
constants 0<m≤B(X)⁻¹_ij≤L<∞ throughout that cube. Put κ=m/(4L)
and Δκ={x≥κ:∑x_i=1}. For any X in the cube and any nonzero y≥0,
the normalization of B(X)⁻¹y lies in Δκ.

For x∈Δκ and 0<t≤R, tx lies in the cube and N⁺(tx)>0. Uniformly
as t↓0, N⁺(tx)=O(t²), and the inverse is uniformly bounded. Thus
S(tx)/t→0 uniformly, where S(X)=∑F(X)_i. Choose 0<r<R so that
S(rx)/r<1 for every x∈Δκ. Define the continuous self-map

    x'=F(tx)/S(tx),
    t'=clamp_[r,R](t+1−S(tx)/t)                             (Brouwer)

on Δκ×[r,R]. Its fixed point exists by Brouwer.

At t=r, the small-radius inequality makes the unclipped argument strictly
greater than r, so this endpoint cannot be fixed. At t=R, the fixed
direction would give F(Rx)=ηRx with η=S(Rx)/R>0. For the radial clamp
to fix R, its input must be at least R, so η≤1. But (R2) would imply
R=∑Rx_i<L₀<R, a contradiction. No uniform large-radius expansion is
being claimed; it is unnecessary and would be circular if its cone were
chosen using that same radius.

At an interior fixed radius the clamp is inactive and S(tx)=t. The fixed
direction then gives F(tx)=tx. This produces X>0 solving (F), and all
q_i∈(0,1). No parameter continuation, degree invariance, or root uniqueness
is assumed. The full arbitrary-K production step is complete.

## All behavioral actions, Never, fixed target, and weak restoration

Alternate the two scheduled pairs with these independent rates. Let V_A
use U on02 and W on13; let V_B reverse them. The active endpoints are
equal by (V), and each passive Continue equals W_i by (E). A passive
Quit averages s_i and exactly the three rewards in (A), so it is at most
s_i<W_i. This verifies all sixteen endpoints and all eight policy values.
The grand coalition is unreachable under any one unilateral deviation;
its free rewards cause no omitted cap.

Joint survival per period is ∏(1−q_i)<1. Bounded policy iteration proves
the two vectors are actual terminal values. For deviator i, the three
opponents' period survival is ρ_i=∏_{j≠i}(1−q_j)<1. Iterating endpoint
inequalities leaves an absolute bounded remainder times ρ_iⁿ; it vanishes
for every full behavioral deviation, including Never and unbounded delay.
Thus this is exact terminal Nash. With M=max|r_i(S)| and
C=max_i[1+2/(1−ρ_i)], expected terminal and N-date average payoffs
differ by at most2MC/N uniformly over deviations. Regret is at most4MC/N
and delivery of the fixed target V_A has error at most2MC/N. The initial
live-zero date is included in C. The same profile works at every accuracy.

These are exactly the inputs of
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.
The non-Q case is already supplied by the contrapositive of the source in
the second section. Hence every strict raw table has original-game UE.

For the weak statement, increase each favorable off-diagonal singleton
entry by δ and decrease each harmful one by δ. Preserve own levels and
every collision coordinate. All strict singleton signs then hold, and
Π_i≥−b_i>−(b_i+δ). The caps and arbitrary K_i remain unchanged.
The strict theorem gives UE for a table uniformly δ-close to the original.
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables` in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`
gives one fixed original-game target. No limiting proper profile is claimed.

## Exact mixed-sign coverage table

Here is a complete table with K=(1,−1,−1,−1), beyond the all-K≤0 class
and beyond either pure scheduled-pair exit. It keeps proper roots with
unequal pair premiums Π_A=145/32 and Π_B=99/14.

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

The singleton favorite gaps are (249/40,53/8,53/8,53/8), all exceeding2;
the harmful gaps are−1. Thus ΓP is strictly diagonally dominant with
positive diagonal and irreducible nonpositive off-diagonals, proving Γ⁻¹>0
directly. Its determinant is33583397/20480>0. Exact odds and values are

    X=(1/4,1/5,1/4,1/5),
    qᴬ=(1/5,0,1/5,0),          qᴮ=(0,1/6,0,1/6),
    V_A=(61/32,183/70,61/32,183/70),
    V_B=(305/128,61/28,305/128,61/28).

All sixteen endpoints check: active endpoints equal the stated values,
and passive Quit is17/50 at A and31/72 at B. In row0 of (E), decreasing
h₀ by2/5 and increasing K₀ by2 exactly cancel since X_o(0)=1/5.
All other rows are unchanged. Every sign, participant and cap inequality
is strict, and K₀>0 persists on a neighborhood of this table.

The following coverage checks are exact raw-data facts.

- The sole-positive matching fixes f under every relabeling. The only
  scheduled matching satisfying Π_i>Γ_i,a(i) is02/13: the alternative03/12
  has participant increment−2 and harmful singleton gap−1. The displayed
  K₀=1 therefore cannot be relabeled into the all-K≤0 theorem. Neither
  scheduled pair has both outsiders with K≥0. Unequal normalized premiums
  exclude a common-premium cubic criterion.
- The only premium traps are02,13,I. Grand participant premiums are all
  negative, so protected-set and global nonnegative-weight floor tests fail.
  A larger-trap negative-charge requirement fails since the singleton charge
  is Π_a(j)−4>0. A weighted terminal upper bound fails: adding its02 and13
  tests yields coefficients Π₀+1 for player0 and Π_i−1 for the others,
  all positive. Product-low fails at either sure scheduled pair.
- No pure exit appears: scheduled02 is joined profitably by1 or3;
  scheduled13 is joined profitably by2; the other pure failures follow
  directly from a negative participant reward and its nonnegative withdrawal
  reward. Every proper child cutting a scheduled pair has the sure-singleton
  child Nash witness at the cut mate; the omitted mate profits by joining.
  The two remaining children02,13 have their joint child Nash witnesses,
  with profitable omitted player1 and2 respectively. All have zero Never.
- All principal matrices of order at least two are nonsingular, all columns
  have negative entries, and the positive inverse has positive determinant.
  Thus the R₀ degree is+1, not a negative-determinant inverse exit. Triple
  determinants are53/4 or257/20; all triple inverse diagonals are negative.
  Harmful principal pairs are neither Q nor homogeneous-LCP admissible.
- At all-sure, responses are−11,−12,−13,−14. Under a positive affine row
  transport, equality of block singleton row sums forces c_i(h_i−2) to
  agree within a block. But the four ratios of all-sure response to row sum
  are −440/169,−96/37,−104/37,−112/37, all distinct. Hence no nondiscrete
  response quotient exists even after those transports.
- The two-negative-per-row, reciprocal-same-sign, and two-transposition
  singleton pattern excludes unique-negative paired schedules, integral
  tournaments, favorable four-cycles, and cyclic children under every
  deletion. Every favorable/harmful gap ratio exceeds4. Crossed lower-face
  guards fail at the sure favorite outsider (response−329/40 for owner0,
  −69/8 otherwise), or at its harmful nonactive outsider (response−1).
  Conditional-range Continue upper bounds are at least289/40, while their
  required lower Quit mixture is at most1. A branch requiring some
  Γ_ij<0<Γ_ji cannot occur.
- There is no stationary profile with exactly three proper positive hazards
  and the fourth zero. For the full scheduled pair i,k and third j favorite
  to i, its common premium Π is145/32 or99/14. With hazards a,c,x,
  k's Never payoff is0 and indifference gives
  a=(1−2x)/[(Π+9)x−Π] and (Π+1)/(Π+11)<x<1/2.
  Player i then has Q_i=[(Π+9)x−Π](a−c) and
  N_i=F_i x(1−c)/(x+c−xc), where F_i is289/40 or61/8.
  Since Π+F_i>9, equality is impossible by Q_i<D(x)(1−c)<N_i.
  No full-support stationary exclusion is asserted.

The exact source predicates for these bounded comparisons are those already
spelled out in the standalone strict matching proof. This note adds a new
raw class and complete strategy producer, not a claim that every conceivable
stationary or quiet-child strategy fails. The revised final packet must retain
the full named-source comparison rather than depend on this note.

## Status and next question

The arbitrary-K proof is ready for independent adversarial checking, especially
the scaled outer-boundary argument (R1)–(R2), the order R then inverse cone
then inner radius, and the exact mixed-sign coverage fixture. All original
frozen manuscripts and exports are untouched. The remaining raw restrictions
are the matching singleton geometry, participant comparison Π_i≥Γ_i,a(i),
and the twelve outsider caps. Removing them would require another argument;
none is claimed here.
