# Two independently signed rewards on one three-owner coalition

Four private stopping laws compete to quit first. Nonempty first exits S pay r(S), perpetual play and live dates pay zero. Put s_i=r_i({i}), Z_i(S)=r_i(S)−s_i and Γ_ij=Z_i({j}), Γ_ii=0. The hazards below are stationary and exact against every unilateral stopping law. Their original-game payoff is one fixed uniform-equilibrium target. All statements here are ordinary mathematics.

**Two-dimensional exterior.** Choose distinct i,a,b and put D={a,b}, C={i,a,b}, o outside C. Require the two nonsingular matrices to satisfy

    v=Γ⁻¹e_i>0,   w=−Γ_CC⁻¹e_i>0,    Γ_oC w>0.

Extend w by zero outside C. Let T=Z_i(D) and R=Z_i(C) vary independently with either sign. Put K=max(|T|,sqrt(|R|)). There are K₀,δ,c,C₀>0 such that whenever K>K₀ and every other centered nonsingleton entry obeys |Z_j(S)|≤δ K^(|S|−1), the game has an exact stationary equilibrium with maximum hazard ≤C₀/K, at least three hazards ≥c/K, and support either all four or C. The constants are uniform over compact sets of Γ meeting the strict tests with the same labels. This exterior includes comparable, oppositely oriented contributions to the same stationarity equation.

For a row j let H_j be rival survival, P_j its passive expectation for a nonempty rival exit on the current date, and Q_j its forced-Quit expectation, all centered. With any rival active, the sharp stationary Never value is P_j/(1−H_j) and the immediate Quit offer is Q_j. Each finite deadline is a geometric interpolation of those endpoints, so the field F_j=P_j−(1−H_j)Q_j suffices: impose F_j=0 on positive hazards, F_j≥0 on inactive ones. There are always at least three active players below. Under any unilateral replacement the other players give uniformly geometric absorption. Thus row shifts add their full constant to all behavior, and terminal payoffs approximate finite-horizon averages uniformly over unilateral replacements for the fixed game.

Set ε=1/K,t=T/K,u=R/K² and θ=max_{other entries}|Z_j(S)|/K^(|S|−1). On compact z-sets,

    F(εz)/ε = Γz + e_i z_a z_b [t−u Σ_{j≠i} z_j]+O(ε+θ).

The bound holds with first derivatives. The passive pair has exactly two rival quit factors and one rival wait factor. The participant triple has the two quit factors in Q_i and a further 1−H_i factor in F_i, whose first-order term is ε times the displayed sum. Other passive or participant entries on size d events contribute O(ε^(d−1)|Z_j(S)|), by the same two product calculations.

Take an arbitrary sequence K→∞, θ→0 and a subsequence with limit Γ,t,u. At least one of |t|,|u| is one. On either support S=I or C use d=v or w, respectively, with d written on S. For any compact positive radial interval, fix z_i=ρd_i and solve every active row except i near z=ρd. The matrix of the remaining active rows against the remaining active coordinates is the principal block obtained by deleting row and column i of Γ_SS. Its determinant is det(Γ_SS)(Γ_SS⁻¹)_ii≠0. These rows have only vanishing errors; contraction or the implicit function theorem produces a continuous curve uniformly converging to ρd for the whole fixed interval. On the triple the omitted row tends uniformly to ρΓ_oC w>0. On these exact curves the remaining active row divided by ρ converges to

    full:     1 + ρ v_a v_b [t−uρ Σ_{j≠i}v_j],
    triple: −1 + ρ w_a w_b [t−uρ Σ_{j≠i}w_j].

At small positive ρ these signs are opposite. At large finite ρ the two signs are the same, namely −sign(u) when u≠0 and sign(t) otherwise. Choose the support giving strict opposite endpoint signs and then use the intermediate value theorem for the exact last equation. All three or four active coordinates stay in a compact positive interval. This constructs solutions along every convergent subsequence. Failure of common constants would give games K>n, θ≤1/n with no solution having scaled hazards at most n and third-largest at least 1/n, a contradiction.

**Selecting the three labels.** Suppose Γ has no zero off-diagonal entries, detΓ>0 and Γ⁻¹ is strictly positive. If there is a mutually negative reciprocal pair, labels satisfying the test always exist. Indeed every row and column has both signs from ΓΓ⁻¹=Γ⁻¹Γ=I. Every principal triple has positive determinant since all inverse diagonal entries are positive. The finite sign lemma below gives a,b,i distinct with sign Γ_ab=sign Γ_ba=−sign Γ_ai=−sign Γ_bi. In the 3×3 adjugate the column at i has diagonal −Γ_ab Γ_ba and other entries Γ_ab Γ_bi and Γ_ba Γ_ai, all strictly negative. Thus w>0. Block inversion yields Γ_oC w=detΓ(Γ⁻¹)_oi/detΓ_CC>0.

The sign lemma can be verified by this exhaustive exact check. It keeps an overestimate of the realizable sign patterns using only mixed rows and columns, a mutual negative pair, and positivity of at least one determinant monomial for every triple.

```python
from itertools import combinations, permutations, product
I = range(4)
edges = [(a,b) for a in I for b in I if a!=b]
count = 0
for pattern in product((-1,1), repeat=12):
    g = dict(zip(edges,pattern))
    if any(len({g[j,i] for j in I if i!=j})<2 or
           len({g[i,j] for j in I if i!=j})<2 for i in I): continue
    if not any(g[a,b]==g[b,a]==-1 for a,b in edges): continue
    if any(max(g[a,b]*g[b,c]*g[c,a],g[a,c]*g[c,b]*g[b,a])<0
           for a,b,c in combinations(I,3)): continue
    assert any(g[a,b]==g[b,a]==-g[a,i]==-g[b,i] for i,a,b in permutations(I,3))
    count += 1
assert count == 207
```

**A generic iff for one passive reward and shrinking stationary rates.** More generally fix an invertible zero-diagonal Γ with no zero off-diagonal entries, nonsingular principal triples and all entries of Γ⁻¹ nonzero. Require R₀, meaning the only complementary solution of x≥0, Γx≥0, x·Γx=0 is zero. Fix i and any rival coalition D of size m≥2. Take Z_i(D)=sign·L with sign in {−1,+1} and L→∞, all other nonsingleton entries bounded. There are nonzero stationary equilibria with maximum hazard tending to zero if and only if there exists S containing D and i with

    d=−sign Γ_SS⁻¹e_i>0,        Γ_out,S d>0.

The empty outside test is vacuous. When the test holds, every sufficiently large L works for arbitrary remainders in the bounded box. More generally allow the weighted small errors |Z_j(B)|≤δ L^((|B|−1)/(m−1)) elsewhere. The root is obtained at scale L^(−1/(m−1)). If m=3, S must be full and at most one sign passes. For m=2, test only the full support and the one specified triple.

For necessity pass to a fixed nonempty exact support S, q/h→x and h=max q→0. If D is absent from S in any coordinate, the entire pole vanishes. Dividing F by h gives a nonzero homogeneous complementary solution, contrary to R₀. If D⊆S but i is absent, all active rows are homogeneous in the limit and the nonsingular Γ_SS gives the same contradiction. Otherwise |S|≥3. Exact indifferences off row i yield x_S=cΓ_SS⁻¹e_i. Here c≠0 and every component of that inverse column is nonzero (for triples its cofactors are signed products of two nonzero off-diagonal entries). Consequently all supported x coordinates are strictly positive. The row i equation divided by h gives

    c + sign·L h^(m−1) (Π_{j∈D}x_j + o(1)) + o(1) = 0.

Thus c has sign −sign and L h^(m−1) tends to a finite strictly positive limit along this subsequence. At each outside row Γ_out,S d≥0. For a triple, equality is excluded by the displayed block inverse formula and the generic nonzero inverse entries. Conversely, on the support in the test, the positive ray ρd changes the sign of the remaining normalized equation −sign+sign·ρ^(m−1)Π_{j∈D}d_j. The transverse active rows and the quiet slack lift exactly as above, with scale ε=L^(−1/(m−1)). This proves both directions and also excludes hierarchical shrinking rates on every failing support.

**Sharpness of the four-column selection by column count.** Take

    Γ = [[0,−7,8,3],[−3,0,−3,6],[2,5,0,−5],[−8,−2,8,0]].

Here detΓ=1644 and adjΓ has rows (210,80,222,−180), (144,368,528,−6), (246,172,354,24), (228,400,288,−78). The first three inverse columns are strictly positive. For triples omitting 0,1,2,3 in turn, the determinants are 210,368,354,−78; the first three triple adjugates have respective rows

    [40,48,15; 10,12,30; 40,6,15],
    [40,24,−40; 40,24,6; 16,−64,−16],
    [12,−6,−42; −48,24,−9; 6,56,−21].

None of these adjugates has a strictly negative column. For the fourth triple, the negative determinant would make the required outside slack negative at every strict full inverse column. Thus no coordinate among these three recipients supports shrinking stationary equilibria for both signs of a single passive pair reward. The matrix is R₀ because each singleton column has a negative entry and every higher principal block is nonsingular. At offset −1 its only complementary solution, checked by the eleven nonsingleton supports, is Γ⁻¹1=(166,517,398,419)/822, giving degree +1. Its only strictly positive-inverse triple omits 0; the exterior inverse row has mixed signs by the block formula and the adjugate above. This example obstructs the proposed shrinking-rate argument. It does not exclude equilibria at other scales or claim failure of UE.

**Opposite directions at comparable pair and triple scales.** For a concrete nonmatching matrix take

    Γ=[[0,3,1/10,−1],[3,0,−1,−1],[−1,−1,0,3],[−1,−1,3,0]].

It has detΓ=549/10 and min Γ⁻¹=2/549. Since rows 0 and 2 have opposite signs on their common edge, no pair partition puts all cross entries below zero and all mate entries above zero. Take i=0, D={2,3}. The strictly positive full vector is v=(20,70,30,30)/183 and the triple vector on C=(0,2,3) is w=(10/3,10/9,10/9), with Γ_1C w=70/9>0. Set all other centered nonsingleton entries to zero. On (T,R)=(K,K²) only the full support can give the constructed O(1/K) equilibrium; on (T,R)=(−K,−K²) only the triple can. Both destinations allow arbitrary signed own levels.

Indeed for each of v and w one has p/(4s)<1, where p=d₂d₃ and s=Σ_{j≠0}d_j. On the first ray the triple scalar −1+pρ−psρ² is always negative. On the second ray the full scalar 1−pρ+psρ² is always positive. No bounded nonzero subsequential limit at either excluded support can solve the equations: the transverse rows force the stated ray. A putative sequence with all Kq→0 would leave the nonzero normalized direction q/max q homogeneously complementary to Γ, as contributions of both special cells after division by max q are O(K max q+(K max q)²). All higher principal blocks of this Γ are nonsingular and every singleton has a negative observer, ruling this out. At a shrinking root any other exact support either misses a member of D or has i inactive; in both cases the same homogeneous contradiction follows from absence of both special terms in the active equations and, when D is missing, in the quiet equations as well. Thus the two equal-weight opposite directions require an actual change of support despite both contributions appearing at leading order.

**Two different passive recipients on the same pair.** Write A=I−D={i,j}. Invert Γ_DD and assume L=−Γ_DD⁻¹Γ_DA>0 entrywise. Define the two by two matrix W=Γ_AA+Γ_AD L. Require B=W⁻¹>0 entrywise and det B<0. No full inverse positivity is needed. Under these raw tests the preceding two-dimensional exterior statement also holds for T_i=Z_i(D) and T_j=Z_j(D), now with K=max(|T_i|,|T_j|), the other 42 nonsingleton coordinates on the same weighted scales, and either outsider available to be quiet. The nonmatching example above meets the conditions on D={2,3}: L has all entries 1/3, B is the positive AA block of Γ⁻¹ by Schur inversion, and det W=detΓ/detΓ_DD<0.

For a sequence as before write k=(T_i,T_j)/K in A, extended by zero outside, and extract normalized G,k limits, |k|∞=1. Scaling gives F(εz)/ε=Γz+k z_a z_b+E_n(z), with E_n→0 in C¹ on compact sets. Put z=y/(y_a y_b). Multiplication by y_a y_b changes the scaled complementary field to Γy+k+(y_a y_b)E_n(y/(y_a y_b)). Seek its value λ≥0, λ·y=0. In the limiting model λ supported on A gives y_A=B(λ_A−k_A), y_D=L y_A. Write u=−B k_A, which cannot be zero. If u>0, use λ=0 and lift directly by invertibility of Γ; all y>0. If u has a zero coordinate and the other positive, try the exact full root with λ=0 first. If one y coordinate is negative, it is the vanishing outsider h. Adding a positive slack λ_h moves y_h with derivative approaching B_hh>0, so a small nonnegative slack gives y_h=0 with the other three coordinates positive.

If at least one component of u is negative, there is an h with u_h<0 such that, for the other outsider l,

    u_l−B_lh u_h/B_hh>0.

This is automatic if u_l≥0. If both components are negative, failure in both orders would yield 1≥B_ij B_ji/(B_ii B_jj)>1. At the positive slack λ_h=−u_h/B_hh the limiting y_h vanishes and the other three coordinates are positive by L>0. Solve the exact perturbed equations for nearby λ_h values by IFT; y_h changes sign transversely, so there is an exact crossing and a strictly positive slack at h. In all cases the scaling is legitimate since y_a y_b stays positive. The same compactness contradiction yields uniform constants.

For the count-control fixture above one can verify degree and proper lifts with the following exact support test. Singletons cannot solve the −1 offset since the diagonal is zero. No such singleton, degree, or passive-lift calculation asserts exclusion of every arbitrary-completion sufficient theorem.

```python
from itertools import combinations
from sympy import Matrix, ones
G = Matrix([[0,-7,8,3],[-3,0,-3,6],[2,5,0,-5],[-8,-2,8,0]])
I = range(4)
assert G.det() == 1644
roots = []
for n in (2,3,4):
    for S in combinations(I,n):
        O = [i for i in I if i not in S]
        inv = G.extract(S,S).inv()
        x = inv*ones(n,1)
        slack = G.extract(O,S)*x-ones(len(O),1)
        if min(list(x)+list(slack)) >= 0: roots.append((S,x))
assert roots == [((0,1,2,3), Matrix([166,517,398,419])/822)]
```


**Formalization handoff.** The checked declaration `quittingGame_fixedProfile_uniformPayoffWitnesses_of_terminalNash_exact` in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean` takes a concrete original behavioral profile with zero terminal regret against every unilateral replacement and returns a fixed target with horizon witnesses at every positive accuracy. The geometric endpoint and support arguments above produce exactly that input. The producing arguments are ordinary mathematics. These criteria leave general four-player quitting games open.
