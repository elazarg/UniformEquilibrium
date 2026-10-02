# Heterogeneous singleton Perron-cycle producer

Author: `CODEX_RENY`.

## Current status

Complete ordinary proof draft, not independently reviewed or Lean-checked.
The surviving content is an explicit ACTUAL-DATA producer of a balanced
singleton cycle for a heterogeneous Fin4 class, followed by an explicit
construction of EA witnesses on every requested finite menu scale. The
existing balanced singleton semantic compiler is reused, not claimed as
new. No arbitrary-Fin4 producer or counterexample is claimed.

The closest inspected class producer requires cyclically invariant singleton
comparisons and equal hazards. The class below permits heterogeneous rows
and constructs unequal hazards. Section 7 gives an exact rational witness
outside that old cyclic producer's hypotheses. HOWEVER, the wider matrix
audit in Section 8 proves that this entire class is already covered by the
union of the checked ordinary-non-Q and full projective-Q-bar consumers.
It cannot intersect the surviving standard-Q/non-Q-bar regime. Thus this
is a constructive sharpening inside a known solved region, NOT a new
UE-class exclusion. No literature-priority claim is made. All nonsingleton
rewards and own singleton levels are unrestricted; no punishment-normality
hypothesis is assumed.

## 1. Exact reward-table class and conclusion

Players are 0,1,2,3 in the indicated cyclic order, with indices interpreted
modulo four. Let rᵢ(S) be arbitrary real rewards for every nonempty
coalition S. Infinite all-Continue pays zero. Define

    sᵢ=rᵢ({i}),       Γᵢⱼ=rᵢ({j})−sᵢ.

Assume the off-diagonal singleton comparisons have the form

    Γᵢ,ᵢ₊₁=−bᵢ<0,
    Γᵢ,ᵢ₊₂=gᵢ>0,
    Γᵢ,ᵢ₊₃=hᵢ>0.                                  (1.1)

Thus each player dislikes only the next quitter, relative to quitting alone.
Put aᵢ=gᵢ/bᵢ and dᵢ=hᵢ/bᵢ; all eight numbers are positive. Define

    X=a₀d₁+(a₀a₁+d₀)a₂,
    Y=(a₀a₁+d₀)d₂,

    K = [ a₃X+d₃(d₁+a₁a₂)    a₃Y+d₃a₁d₂ ]
        [ X                   Y             ].       (1.2)

Every entry of K is strictly positive. Let

    λ = (K₀₀+K₁₁+√((K₀₀−K₁₁)²+4K₀₁K₁₀))/2.

The final table assumption is

    λ>1.                                            (1.3)

A simpler sufficient condition is gᵢ+hᵢ>bᵢ for every i, proved below.
Neither (1.1) nor (1.3) constrains any nonsingleton reward or the levels sᵢ.
An arbitrary relabeling admitting this cyclic order is allowed.

### Theorem draft

Every such reward table has a fixed uniform-equilibrium payoff. More
constructively, for EVERY e>0, integer H≥1, ρ>0, and integer N₀≥0, the
construction below gives an integer N≥max(H,N₀) and independent product
law p on {0,…,N−1,Never} such that

    E_r(p)<e,          R_p(N−H)<ρ.                   (1.4)

Here E_r is FULL terminal exploitability over unrestricted unilateral
behavioral deviations, so p is in particular e-Nash on its actual finite
menu. This is a producer from the displayed reward coefficients, not an
assumed UE or a supplied near-equilibrium family. The completed proof also
identifies a fixed payoff v⁰ for the infinite fine-mesh approximants.

## 2. Global cycle balance: explicit two-dimensional Perron construction

Introduce a prospective full-cycle Continue probability z and the matrix

    B(z) = [ 0       a₃      d₃       0  ]
           [ 0       0       a₀       d₀ ]
           [ z d₁    0       0        a₁ ]
           [ z a₂    z d₂    0        0  ].          (2.1)

At z=0 this matrix is strictly upper triangular, hence B(0)⁴=0. For z>0
its positive-entry graph is strongly connected. For example, the arrows
from an input coordinate to an output coordinate include 0→3→1→0,
3→2, and 2→0. Thus no hidden zero coordinate can be discarded in a
Perron balance. Rather than rely on continuity of a selected eigenvector,
we solve the relevant eigenvalue crossing explicitly.

Since K is a strictly positive 2×2 matrix, its displayed eigenvalue λ is
strictly greater than both diagonal entries. The vector

    W₀=K₀₁,         W₁=λ−K₀₀

is strictly positive and satisfies K(W₀,W₁)ᵀ=λ(W₀,W₁)ᵀ. This follows
directly from the quadratic characteristic equation; no attainment at an
infinite strategy boundary is involved. Set

    A=1/λ∈(0,1),
    W₃=A(a₂W₀+d₂W₁),
    W₂=A d₁W₀+a₁W₃.                               (2.2)

Both new coordinates are positive. The eigenvector equations for K give

    W₁=a₀W₂+d₀W₃,
    W₀=a₃W₁+d₃W₂.

Together with (2.2), these are exactly B(A)W=W. This proves a positive
crossing at some A strictly between zero and one from the TABLE DATA.
The construction permits unequal W coordinates and unequal hazards.

Normalize

    wᵢ=(1−A)Wᵢ/∑ⱼWⱼ,
    t₀=1,       t_k=1−∑[j<k]wⱼ   (1≤k≤4),
    q_k=w_k/t_k,       c_k=1−q_k=t_(k+1)/t_k.       (2.3)

Every wᵢ is positive, their sum is 1−A<1, and t₄=A. Consequently every
qᵢ lies strictly between zero and one, and ∏ᵢcᵢ=A. In a cycle of four
successive singleton roots, with only player k active at phase k with
hazard q_k, w_k is exactly its unconditional first-absorption probability
within the cycle. All laws are independent product laws.

### The simple row-sum sufficient condition

Write U=B(0), L=B(1)−B(0), and S=I+U+U²+U³=(I−U)⁻¹. If
aᵢ+dᵢ>1 for all i, then B(1)1>1, so L1>(I−U)1. Multiplying by the
nonnegative matrix S≥I gives SL1>1. Only columns 0 and 1 of SL are
nonzero, and its first two rows on those columns form K, as direct
elimination in (2.2) shows. Hence K(1,1)ᵀ>(1,1)ᵀ. A positive left
eigenvector for the displayed eigenvalue λ (obtained by the same explicit
2×2 formula for Kᵀ) gives λ>1 after taking its inner product. Thus
gᵢ+hᵢ>bᵢ for every i implies (1.3).

### Exact criterion for this positive four-phase cycle architecture

Conversely, any cycle with each of the four designated owners active once,
all four hazards strictly between zero and one, and owner indifference at
every phase gives positive first-absorption weights w and A∈(0,1) obeying
(3.3), hence B(A)w=w. Eliminating w₂,w₃ as above gives

    K(w₀,w₁)ᵀ=(1/A)(w₀,w₁)ᵀ.

Take its inner product with a positive left λ-eigenvector of K. Since
w₀,w₁>0, this gives λ=1/A>1. Thus (1.3) is also NECESSARY for this
particular positive four-phase owner-indifferent cycle. The condition
λ≤1 is not an obstruction to UE or to other strategy classes. At λ=1 the
construction reaches A=1 and cannot be normalized to positive hazards;
this boundary is not silently admitted in the theorem.

## 3. Literal cyclic values and all singleton floors

Repeat the four coarse roots from (2.3) indefinitely. Joint survival through
each full cycle is A<1, so this defines an actual almost-surely absorbing
profile. Let vᵏ be its terminal payoff vector when started at phase k.
These values are uniquely determined by the actual profile and satisfy

    vᵏ=q_k r({k})+c_k v^(k+1),                    (3.1)

with cyclic phase indices. Their initial value is explicitly

    v⁰=Σⱼ wⱼ r({j})/(1−A).                         (3.2)

The matrix equation B(A)w=w is equivalent, row by row, to

    Σ[j>i]wⱼΓᵢⱼ+AΣ[j<i]wⱼΓᵢⱼ=0                  (3.3)

for every player i. For i=3 all terms have the common factor A, which
was canceled in row zero of B; A>0 makes this cancellation legitimate.

From phase i+1, a quitting phase j>i has one-cycle probability
wⱼ/t_(i+1), while j≤i has probability A wⱼ/t_(i+1). The next full cycle
has the same factor A. Since Γᵢᵢ=0, (3.3) therefore gives

    v^(i+1)_i−sᵢ
      = [Σ[j>i]wⱼΓᵢⱼ+AΣ[j<i]wⱼΓᵢⱼ]
          /[(1−A)t_(i+1)] = 0.

Equation (3.1) now also gives vⁱ_i=sᵢ. Every owner's coarse Quit and
Continue values are thus equal to its own singleton payoff.

For the remaining phases, move backward from phase i around the cycle
to phase i+2. Every encountered singleton comparison Γᵢⱼ is positive:
the only negative one is the excluded phase i+1. Applying (3.1) in this
backward order gives vᵏ_i≥sᵢ at every such phase. Phases i and i+1
already have equality. Hence

    vᵏ_i≥sᵢ for EVERY phase k and player i.          (3.4)

This supplies every field of an ACTUAL balanced singleton cycle:
owner=k, hazard=q_k, coarse=vᵏ, owner indifference, all-player singleton
floors, and positive opponent hazard for every player. No punishment-floor
or other equilibrium existence premise has been inserted.

## 4. Fine subdivision controls every behavioral deviation

The coarse roots need not be root Nash for arbitrary collision rewards.
We do NOT discard those rewards. Fix M>0 bounding the entire reward table,
including nonsingleton coalitions. Choose an integer L≥1 and replace phase
i by L successive dates with only i active, each with hazard

    θᵢ=1−cᵢ^(1/L).

The product of Continue probabilities through that phase remains cᵢ.
Thus the infinite subdivided cycle has the same coarse values vᵏ and the
same fixed initial payoff v⁰. Every value inside a phase is a convex
combination of its two coarse endpoint values, by the singleton Bellman
recursion. Hence all fine-date values are still at least each player's
singleton payoff. The active owner's value is identically sᵢ throughout
its phase, so its Quit and Continue endpoints agree exactly.

For a passive player j at a fine date owned by i≠j, Quit pays

    (1−θᵢ)sⱼ+θᵢrⱼ({i,j}) ≤ sⱼ+2Mθᵢ,

whereas Continue equals its prescribed fine-date value, at least sⱼ.
Thus the sole possible Quit advantage is at most 2M maxᵢθᵢ. At an own
date the player's Continue advantage is zero by exact owner indifference;
at every other date Continue is its prescribed action.

To check FULL deviations, fix player j and force it to Continue through
any finite prefix. Bellman iteration gives exactly the same prescribed
value if the original continuation is restored at the end: its Continue
endpoint equals its prescribed value at every intermediate date. A pure
Quit at the last date changes this by at most its opponent-deleted reach
times 2M maxᵢθᵢ, hence by at most 2M maxᵢθᵢ. A Never deviation is the
limit of Continue-through-prefix responses, because the opponent-deleted
survival through each cycle is ∏[i≠j]cᵢ<1. Its terminal payoff therefore
equals the original prescribed payoff. All unilateral stopping laws are
mixtures of deterministic finite dates and Never. Consequently

    E_r(infinite fine profile) ≤ 2M maxᵢθᵢ.         (4.1)

Since θᵢ→0 as L→∞, this is an actual full terminal approximate-Nash
family at the SAME target v⁰. It is also exactly the source handled by
the checked balanced singleton cycle consumer; that consumer is not new.

## 5. Actual finite EA witnesses at the requested error and window

Fix e>0,H≥1,ρ>0,N₀≥0. First choose L so 2M maxᵢθᵢ<e/2. Next choose
an integer K≥1 so

    4MΣᵢcᵢ^K<e/2,       A^K<ρ.                    (5.1)

Both are possible because every cᵢ and A lie strictly between zero and
one. Start with the infinite fine profile and move each player's finite
stopping atoms at dates at least T=4LK to Never. Its original Never mass
was zero; the mass moved in marginal i is exactly cᵢ^K. The product
coupling changes each prescribed payoff and each full pure-deviation cap
by at most 2MΣᵢcᵢ^K. Taking suprema and subtracting values yields a change
of exploitability at most 4MΣᵢcᵢ^K. By (4.1) and (5.1), the resulting
finite-clock law p satisfies E_r(p)<e.

All finite atoms of p lie before T, and its joint Never mass is exactly
∏ᵢcᵢ^K=A^K. Finally choose

    N≥max{T+H,N₀}.

The law belongs to the actual menu F_N and is finite-menu e-Nash because
its FULL error was already proved below e. Moreover
R_p(N−H)=A^K<ρ. This proves (1.4) with its complete quantifier order.
The enlargement is legal because the full cap was controlled before the
deadline was declared; it is not padding an arbitrary finite Nash source.

Independence is preserved throughout the matrix-produced cycle, its fine
subdivision, and marginal censoring. There is no lottery over correlated
whole profiles or detection of a unilateral deviation.

## 6. Named source and consumer audit

The comparison convention was checked against `quittingSingletonMatrix`
in `UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`:
it is exactly rᵢ({j})−rᵢ({i}), not its negative or transpose.

`BalancedSingletonCycleCertificate` in
`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`
has exactly the fields filled in Section 3. Its
`BalancedSingletonCycleCertificate.isTerminalNash_and_hasValue` compiles a
fixed fine subdivision to full terminal approximate Nash at the coarse
target; `.isUniformEquilibriumPayoff` supplies the fixed uniform target.
The collision bound is inferred from the finite reward table, leaving all
nonsingleton rewards arbitrary. The proof above independently retains the
same deleted-survival and one-Quit-deviation reasoning needed by that
consumer, rather than asserting that the COARSE root is exact Nash.

The nearest checked producer is
`QuittingCyclicSingletonOpenSignData.isUniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Cycles/CyclicSingletonOpenSignProducer.lean`.
Its data include `IsQuittingCyclicSingletonMatrix reward gamma`, requiring
Γᵢⱼ=gamma(j−i), a negative first offset, nonnegative later offsets, and
positive total envy. It produces the equal-hazard object
`CyclicSingletonTailData` in `CyclicSingletonTailProducer.lean`.
The present raw data do not require cyclic invariance. The matrix W and
the qᵢ are PRODUCED from heterogeneous coefficients; no balanced cycle is
assumed as an input.

The integral-tournament class in
`UniformEquilibrium/Quitting/Classification/LCP/FinFourIntegralTournamentBalancedSingleton.lean`
requires its literal tournament-normalized singleton matrix. It is not the
heterogeneous one-bad-successor class here; in particular the rational
witness below has strictly positive comparisons in both directions on
opposite vertices. Narrow searches in these cycle/LCP modules for Perron,
spectral-radius, heterogeneous, and one-negative-row producers did not find
this actual-data construction. No broad claim about all solved classes is
being made.

Thus the surviving constructive advance is an explicit heterogeneous
balanced-cycle producer feeding an existing unrestricted semantic consumer,
not a new supplied-certificate verifier, another payoff restriction on
hypothetical global minimizers, or a universal finite-game selection
theorem. The broader solved-chamber comparison in Section 8 prevents calling
it a new sufficient UE class.

## 7. Exact heterogeneous rational test

Take sᵢ=1 and singleton comparison matrix

    Γ = [  0   −1    1/2   1 ]
        [  2    0   −1     1 ]
        [  1    3    0    −1 ]
        [ −1    1    2     0 ].                     (7.1)

Here b=(1,1,1,1), a=(1/2,1,1,1), d=(1,2,3,2). Every aᵢ+dᵢ>1.
The reduced matrix and its eigenvalues are

    K = [17/2  21/2],       eigenvalues 12 and 1.
        [ 5/2   9/2]

The construction gives

    A=1/12,
    w=(1/2,1/6,1/6,1/12),
    q=(1/2,1/3,1/2,1/2).

Its exact coarse values are

    v⁰=(1,2,2,1),
    v¹=(1,1,2,2),
    v²=(3/2,1,1,2),
    v³=(3/2,2,1,1).

The four Bellman equations, owner equalities, and all-player singleton
floors can be checked by direct rational substitution. For example the
singleton reward columns are

    r({0})=(1,3,2,0),     r({1})=(0,1,4,2),
    r({2})=(3/2,0,1,3),   r({3})=(2,2,0,1).

The matrix is not cyclically invariant: its first row's positive entries
are {1/2,1}, while other rows have different multisets. No relabeling can
make all row multisets equal. Nor can playerwise positive rescaling repair
this: the unique negative edge at every row forces the cyclic order, and
its common magnitude fixes the relative normalization, while the positive
ratios still differ. Thus this exact table fails the old cyclic producer's
data hypothesis, yet the heterogeneous producer gives the displayed
unequal-hazard cycle. Every choice of the 44 nonsingleton reward coordinates
is covered after the fine-mesh step; no particular collision completion is
used to manufacture the example.

An exact rational-arithmetic check independently evaluated the four
equations (3.3), all sixteen entries of (3.1), the four owner equalities,
and every singleton floor for this fixture; all passed. This computation
checks the example, not the general theorem.

The older delayed cyclic bad-selector examples motivated avoiding a
selection confined to exact finite Nash. The present construction does
not iterate their bad selectors. It builds one whole nonstationary cycle
from the raw table, and tests every full deviation before using finite
menu enlargement. The three-active-plus-passive example is outside the
strict four-active class (1.1), so no unsupported claim of covering that
entire earlier table is made.

## 8. Decisive comparison with the already solved matrix chambers

This section answers the stronger novelty question. It applies the actual
matrix predicates from `MatrixClasses.lean`, not a sign-pattern analogy.
The normalized matrix used there is exactly Γ: this was checked through
`normalizedSoloMatrix_eq_projectiveLCPMatrix` in `Normalization.lean` and
the singleton reward adapter. `IsStandardQMatrix` means solvability of
w=q+Γz≥0, z≥0, zᵢwᵢ=0 for EVERY q. Projective Q also permits a cemetery
coefficient on q; `IsProjectiveQBarMatrix` means projective Q on EVERY
nonempty principal submatrix.

### Every proper principal is already projective Q

Let S be any nonempty proper subset of the four-cycle. Some j∈S has
predecessor j−1 outside S; otherwise predecessor closure would force S to
be all four vertices. Column j restricted to S has diagonal zero and
strictly positive entries everywhere else: its only negative entry in the
ambient matrix is at the omitted predecessor. Consequently the vertex
weight eⱼ is a homogeneous simplex-LCP solution on S. It is a projective
solution for EVERY right-hand side q by assigning cemetery coefficient zero.
Thus every proper principal of Γ is projective Q, without any spectral
assumption. In particular

    full Γ standard Q  ⇒  full Γ projective Q-bar.  (8.1)

The full-set principal uses ordinary standard-Q normalization; all other
principals use the displayed homogeneous vertex. This is the exact use of
`isProjectiveQMatrix_iff_standard_or_homogeneous` in `MatrixClasses.lean`.
No assertion that these proper principals are STANDARD Q is made.

### Normal core and exclusion of the full homogeneous branch

The recursive normal core is all four players. At every layer each player
i has the distinct retained successor i+1 with Γᵢ,ᵢ₊₁<0; induction from
the full initial layer proves that no player is removed. This matches the
distinct-witness definition `normalLayer` in `NormalCore.lean`.

Under λ>1, Γ has no homogeneous simplex-LCP solution. To prove this, let
z be a purported simplex weight and S its positive support.

- If S={j}, its residual at the predecessor j−1 is negative.
- If 2≤|S|<4, choose i∈S with successor i+1 outside S. Every off-diagonal
  entry of row i on S is strictly positive. Since another coordinate in
  S has positive weight, (Γz)ᵢ>0, contradicting complementarity at i.
- If S is all four players, complementarity gives Γz=0. The same
  elimination as in Section 2, now at A=1, gives K(z₀,z₁)ᵀ=(z₀,z₁)ᵀ.
  Inner product with a strictly positive left λ-eigenvector forces λ=1,
  contrary to (1.3).

Thus the ordinary non-Q branch hypotheses are available whenever Γ is
not standard Q: the normal core is nonempty and equals the full matrix,
and its homogeneous simplex problem is infeasible.

### The whole proposed class is already strategically covered

There are now only two cases, both already solved by checked declarations:

- If Γ is standard Q, (8.1) supplies the hypothesis of
  `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` in
  `UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`.
- If Γ is not standard Q, the preceding argument supplies exactly
  `OrdinaryNonQMatrixBranch` from `Gate.lean`, consumed by
  `exists_uniformEquilibriumPayoff_of_ordinaryNonQMatrixBranch` in
  `UniformEquilibrium/Quitting/Classification/LCP/OrdinaryNonQClosure.lean`.

Both named conclusions concern the original ambient reward table and every
behavioral deviation; neither places a nonsingleton-reward restriction here.
The neighboring homogeneous producer was also inspected, but the argument
above excludes that branch at λ>1 rather than using it. No decision about
which of the two remaining branches contains the rational fixture is needed
for this exhaustive coverage proof.

Therefore the heterogeneous Perron construction does NOT remove any table
from the current surviving standard-Q/non-Q-bar class. Its useful result is
the explicit table-to-cycle formula, exact architecture criterion, fixed
payoff, and direct finite EA construction for an already-solved region.
The attempted implication “outside the cyclic equal-hazard producer implies
new UE-class coverage” is false, and is not retained as a research claim.

## Remaining check

Independently verify the global elimination B(A)W=W, especially the wrap
factor for i=3, the phase-value normalization, and the passive-floor/
fine-mesh full-cap argument. Then check the claimed class increase against
the nearest existing raw-data producers, together with the decisive fact
that the entire class is nevertheless contained in already-solved matrix
chambers. This is a complete proof draft
awaiting independent falsification, not an export or a Lean implementation.
