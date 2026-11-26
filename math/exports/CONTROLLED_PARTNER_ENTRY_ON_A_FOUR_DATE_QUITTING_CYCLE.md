# A three-dimensional return map gives equilibrium throughout the mixed passive strip

At the golden boundary, number players modulo four, use the centered singleton matrix with G_{j+2,j}=3 and crossed entries −1, joining rewards J_{j+2,j}=x_*=(3+√5)/2 and crossed joining rewards J_{j−1,j}=−0.9, J_{j+1,j}=−1.1. Put ρ=(3−√5)/2, h=1−ρ, a=ρ² and r=a⁴. Write T₁,T₃ for the passive rewards of 1 and 3 on {0,2}. Define

    d=−a+a²+ρhT₃,   c=ρ(h−ρ)+ρhT₁,   C=ρ+a c+a²d,   β=a²C.

Assume d<0, C>0, c+a d>0, and λ=r+β/(−d)>1. There is a full open neighborhood of every such table on which the original quitting game has an exact absorbing private equilibrium at arbitrary signed singleton levels. Every four dates the potential joint date is the phase of player 0, joined only by player 2. Some visits use this joint row and some use the solo row of 0. No period is asserted for this construction. The two other passive matched-pair rewards and all 28 residual centered rewards are arbitrary and finite. For T₁=0, T₃=t this covers the whole open interval t₄<t<t∞, where t₄ solves d+β/(1−r)=0 and t∞ solves d=0. The interval is nonempty since d=−a+a²<−β/(1−r) at zero and C>0 at d=0.

**An exact return with a controlled entrant.** Read four consecutive dates backwards, starting with the next phase-0 payoff (x₀,x₁,x₂,0). The zero is required by the preceding phase-3 incumbent. Let x denote the first three coordinates, x°=(0,−h,1+h), and let u be the next earlier phase-0 entrant's trial hazard. The following finite rational operations define a return x'=P(x,u) and four mate Wait-minus-Quit advantages F_j(x,u). These formulas at any nearby centered raw table R use its true rewards.

Start with v=(x,0). For j=3,2,1, let i=j−1 and target b=0 for j=3,2, whereas b=−u(G_{02}−J_{02})/(1−u) for j=1. Set

    q=(v_i−b)/(v_i−G_ij),    F_j=(1−q)v_{j+2}+q(G_{j+2,j}−J_{j+2,j}),
    v ← qG_{·j}+(1−q)v.

This gives the required zero child coordinate for the preceding incumbent at j=3,2 and the exact own indifference of incumbent 0 at j=1. For phase 0 take Q=(1−u)G_{·0}+u Z({0,2}), V=(1−u)v+uG_{·2}, and set

    q=V₃/(V₃−Q₃),   F₀=(1−q)v₂+q(G₂₀−J₂₀),   (x',0)=qQ+(1−q)V.

Every incumbent satisfies its contact, and exactly x'₀=J₀₂u. All four incumbent hazards equal h at the central x=x°, u=0, and all denominators are nonzero there. At that point all crossed quiet guards are strict and all four mate guards equal zero.

**Linear data.** At the central raw table let A=P_x, B=P_u, f=(ρ⁶,ρ⁷,ρ⁸), y=f·(x−x°), and X=x₀/x_*. In the first-order terms about x°,0, the map and the four guards obey

    P' = A dx+B u,       fA=r f,     fB=β,     det(zI−A)=z(z−ρ⁴)(z−r),
    F₀'=y+d u,           F₁'=a u+(aC/β)y,     F₂'=(C/β)y,
    F₃'=(c+a d)X+(C/a)(y/β−X).

Here P' and F' denote the differentials, not full nonlinear functions. These identities may be verified directly with the displayed return. To spell out the differentiation, take the four-vector ξ=(dx,0) and scalar u. At each j=3,2,1 use p=aξ_{j−1}−ρ db, dF_j=ρξ_{j+2}+p, and replace ξ by ρξ+(G_{·j}−V°_{j+1})p, where db=0,0,−ρu respectively. V°_j has cyclic entries 0,−h,1+h,0 starting at j. At 0 take q' and v' from

    v' = ρξ + (G_{·0}−V°₁)q' + [ρG_{·2}+h Z({0,2})−V°₀]u,
    v'₃=0,   dF₀=ρξ₂+q'.

The coefficients above follow by multiplying these four elementary linear maps, using ρ²=3ρ−1. For example F₁,F₂,F₃ have x-coefficient rows (ρ⁴,ρ⁵,ρ⁶), (ρ²,ρ³,ρ⁴), (0,ρ,ρ²), and u coefficients a,0,0 respectively. The trace of A is ρ⁴+r, its determinant is zero (the first output coordinate at u=0 is identically zero), and fA=rf. Since f is nonzero, this gives the stated characteristic polynomial and the two eigenvalues of A restricted to ker f.

**Invariant set for the two genuine updates.** Write η for the sup distance of the actual centered reward entries from the central table. All remainders below are O((||x−x°||+|u|)²+η) on a fixed small ball, by smoothness. Use the genuine branch u=0 or the exact contact F₀(x,u)=0. The latter exists by d<0 and has u=y/D+O(||x−x°||²+η), D=−d. The first coordinate of the actual parent is J₀₂(R)u on both branches.

Choose a vector e with fe=1, e₀=0. Write x−x°=ey+w with w∈ker f. In a norm on ker f the restriction of A has operator norm γ<1, by its two distinct eigenvalues 0,ρ⁴. Denote the projection onto ker f along e by Π. At either update,

    y'=r y+β u+O((||x−x°||+|u|)²+η),
    w'=A w+(ΠAe)y+(ΠB)u+O((||x−x°||+|u|)²+η).

Fix M=4λ/r. Use a small level δ>0, an H>0 to be specified, and the closed set

    δ≤y≤Mδ,      ||w||≤Hδ,      0≤βx₀/J₀₂(R)≤y.

It contains x°+δe. Given a child in the set, choose the contact branch when y≤2δ/r and the zero branch otherwise. In scalar terms these branches have leading laws λy and ry. For the active branch λδ≤λy≤Mδ/2. For the inactive one 2δ≤ry≤rMδ. Since λ>1 and r<1, both ranges are strictly inside the permitted bounds by a constant times δ. On the active branch u>0 and u=O(Mδ/D); on the zero branch u=0. First choose H so large that

    γ H+||ΠAe|| M+||ΠB|| (2M/D)<H.

Then fix δ sufficiently small and η sufficiently small relative to δ. These choices make all quadratic errors smaller than the strict margins, retain proper incumbent hazards, and preserve the scalar and transverse bounds. Also y'−βx'₀/J₀₂(R)=r y+O((||x−x°||+|u|)²+η)>0, and x'₀/J₀₂(R)=u≥0, so the final constraint is invariant as well.

The inactive phase-0 mate guard is y+O(||x−x°||²+η)>0; the active one is satisfied exactly. The phase-1 and phase-2 guards are bounded below by a positive constant times δ up to the small remainders. For phase 3 the actual set gives 0≤x₀/J₀₂(R)≤y/β. Replacing x_*=J₀₂ at the central table by the actual J₀₂(R) costs O(η||x−x°||). Its linear guard is at least min(c+a d,C/a)y/β, which is strictly positive of order δ. The crossed comparisons remain strict by continuity. Thus each chosen update actually consists of Nash rows at its four true children.

Start at x°+δe and iterate as many backward blocks as desired. Read starting dates in physical order and extract a coordinatewise subsequence, including the bounded continuation payoffs. Four consecutive phases always contain a rival incumbent who quits with probability uniformly bounded below, even if any one owner replaces its entire law. Thus the finite-block payoffs differ from their uniformly bounded terminal substitutions at late dates by a uniformly vanishing tail. The limiting continuations are the actual native payoffs; all one-action comparisons survive, and iteration controls every deadline, Never, and therefore every private stopping law. Uniform rival absorption also makes the finite-average payoffs converge uniformly over each owner's complete replacement laws. All signed row shifts add their entire level under every replacement and preserve the result.

Both branches occur repeatedly: indefinitely choosing λ expansion exceeds the ceiling and indefinitely choosing r contraction falls below the floor, with the errors chosen smaller than half the one-step scalar changes. This controls incidence intrinsically and gives a genuine joint calendar. This assertion concerns the constructed orbit.

**Raw check and scope.** Take T=(1,0,1,1/2), any signed singleton levels (for the collision comparison take all one), and all remaining higher centered rewards zero. In order d, c+a d, C, d(1−r)+β the four quantities are

    19−17√5/2, (499−223√5)/4, (3425−1531√5)/4, −1705+1525√5/2.

Their signs are −,+,+,+, as follows for example from 2236067977/10⁹<√5<2236067978/10⁹ by squaring the two rational bounds. Increase just J₂₀ by any sufficiently small positive amount. The theorem still supplies exact play. The displayed golden four-date solo policy now fails the phase-0 mate guard: immediate Quit by 2 gains h times this increase. At the comparator T=(1,0,1,1) the designated d=18−8√5 is positive and this gate fails. At T=(1,0,1,0) the designated d(1−r)+β=−1704+762√5 is negative and that gate fails through its other inequality. Failure is solely failure of this designated sufficient test.

The actual target is the limiting calendar's original payoff. The checked [terminal-to-uniform compiler](../../UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean) includes `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` and `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`. The finite block construction above supplies their strategic input by verifying exact Nash against complete original private clocks. The new return-map argument is ordinary mathematics.
