# A quadratic small-exit law and a finite exclusion of the AllNever source

For a four-player native quitting game, the least total weighted regret at small total marginal stopping mass has an exact quadratic coefficient with a cubic error. The coefficient depends on the twelve passive singleton rewards and twelve joining rewards against a single rival. Combining this law with the true deviation caps at a positive minimum gives finite polynomial tests excluding the global AllNever-only source. The first of two open exclusions gives a rational box allowing all 24 entries to vary independently by $10^{-4}$ and all other 32 native rewards to take arbitrary finite values. For both centers the complete homogeneous matrix pencil has degree one, and all the specified two- and three-phase eigenvector tests fail.

On each natural date the four owners independently choose Continue or Quit. The first nonempty quitting coalition $S$ absorbs at a finite reward vector $Z(S)$. The live, perpetual and own-singleton rewards are zero. Before absorption there is one live public history per date, so private behavioral strategies are independent stopping laws on natural dates and a separate Never point. A player may replace its entire stopping law. Let $\Gamma_{ij}=Z_i(\{j\})$ and $J_{ij}=Z_i(\{i,j\})$ for distinct $i,j$, with zero diagonals. A uniform-equilibrium payoff is one fixed target approached at every accuracy with unilateral gains bounded by that accuracy at every sufficiently large average horizon.

For independent actual stopping times on natural dates and Never, use pᵢ(n)=Pr(Tᵢ=n), fᵢ=∑pᵢ, β=∑fᵢ, ν=∏(1−fᵢ). Write Uᵢ for the prescribed payoff, eᵢ for the payoff of deviating to literal Never, Bᵢ for the full cap including all finite deadlines and Never, and dᵢ=Bᵢ−Uᵢ. Fix positive recipient weights w, write W=∑w and D_w=∑wᵢdᵢ.

## Minimum weighted debt at fixed marginal mass

**Pair-data functional.** Take any finite word x(n)≥0 of four-vectors with ∑_{i,n} xᵢ(n)=1. Put R(n)=∑_{k≥n}x(k), g(n)=ΓR(n)−Jx(n). Define

    V(x)=max(0,max_{n,i}(−gᵢ(n))),
    Cᵢ(x)=∑ₙ xᵢ(n)gᵢ(n),
    κ(w)=lim_{a↓0} inf{∑ᵢ wᵢCᵢ(x): V(x)≤a}.

Include every old physical date between the first allowed date and the last entry; zeros in the word can be retained. The empty tail has g=0. Extending to infinite summable words in these definitions gives the same limiting value: truncate and normalize to change all g, V and C by amounts tending to zero uniformly on the retained dates, and remove only a vanishing tail. Under the hypothesis Γy≫0 below, the feasible collections are nonempty at every a>0. For instance put x(n)=y/L on L consecutive dates. Then ΓR(n)≥0 and V≤max|J|/L. The limit is nonnegative and finite since each Cᵢ≥−a on the feasible set and all g are uniformly bounded. Define κ also on nonnegative w by the same formula. It is a Lipschitz continuous concave homogeneous function of w on the nonnegative orthant, as a monotone limit of bounded-slope infima of linear functions.

**Theorem.** Suppose there is a simplex vector y with Γy strictly positive. On actual profiles, for EVERY completion of the 32 native rewards other than Γ,J,

    lim_{b↓0} b⁻² inf_{β=b} D_w = κ(w).                          (1)

More precisely, the infimum differs from κ(w)b² by at most Cb³ for all sufficiently small b, with C allowed to depend on the complete table and the weights. In particular positivity, vanishing and value of this coefficient depend only on the 24 entries and the weights. The infimum in (1) fixes the sum of physical marginal finite masses, without any cap, time horizon or prescribed target restriction.

**Expansion on a native profile.** Set x=p/β. For every player i and every deadline n the actual offer Fᵢ(n) satisfies

    eᵢ−Fᵢ(n)=β gᵢ(n)+O(Mβ²),
    eᵢ−Uᵢ=β² Cᵢ(x)+O(Mβ³),                                     (2)

where M≥1 bounds all rewards, uniformly over n, all calendars, and all their durations. Indeed ignore all but one opposing finite draw. When a lone opponent j stops before n, the two comparisons coincide. At n the difference is Γᵢⱼ−Jᵢⱼ, and beyond n it is Γᵢⱼ. The independent probability of two or more finite rivals is O(β²); replacing the single-opponent event probabilities by their individual unconditional probabilities likewise costs O(Mβ²). The error in the second equality is the first error averaged against i's finite draws, of total mass fᵢ≤β. Similarly eᵢ=∑ⱼΓᵢⱼ fⱼ+O(Mβ²). The cap is a supremum over the complete family of finite deadlines and literal Never, since a mixed response averages their values. In particular dᵢ≥(1−fᵢ)(Bᵢ−eᵢ). For positive w and sequences D_w=O(β²), all cap-minus-Never gaps are O(β²), giving V(x)=O(β). Then D_w≥∑wᵢ(eᵢ−Uᵢ) proves the liminf in (1). A sequence with unbounded D_w/β² along every subsequence is harmless for this lower bound.

**Correcting the linear deadline constraints.** In fact for all 0<a<1, every finite unit word x with V≤a satisfies ∑wᵢCᵢ(x)≥κ(w)−C a for a fixed C. Choose a fixed multiple λa such that λa minᵢ(Γy)ᵢ≥a, and append after the word a summable geometric tail with n-th mass λa(1−r)rⁿ y. Choose 0<r<1 so (Γ−(1−r)J)y≥0. Every old g gains λaΓy; each tail g equals λa rⁿ(Γ−(1−r)J)y≥0. Divide the combined word by 1+λa. It has unit mass, V=0, and its cost differs from the old cost by O(a), since C is quadratic, the old g change by O(a), and the unnormalized tail's own cost is O(a²). Truncating and renormalizing this infinite word meets arbitrarily small finite-word tolerances. The same lower bound holds on summable x by truncation. Consequently any family with D_w≤C₀b² and β=b satisfies D_w≥κ(w)b²−C₁b³ by (2), for constants depending on the fixed C₀ and the table. To bound the infimum it suffices to take fixed C₀>1+κ(w), since higher debts already obey that lower bound.

**A terminal reserve meeting every original deadline.** For any z close to y and any sufficiently small positive a, use independent unconditional finite masses a zᵢ (1−r)rⁿ, with r<1 fixed close enough to one. At every reserve date n the conditional remaining rival masses are a rⁿ(zⱼ+O(a)), because all denominators for old individual survival lie in [1−O(a),1]. In the conditional laws the current mass for each rival is exactly (1−r) times its remaining mass. The first estimate of (2), applied conditionally at that cut without normalizing, gives a native Never-minus-current-Quit gap

    a rⁿ[(Γz)ᵢ−(1−r)(Jz)ᵢ+O(Ma)].

Choose a neighborhood and r using Γy≫0, then choose a small. Every term is positive at every n. The unconditioned difference has the same sign: preceding rival exits cancel and pre-date rival survival multiplies this conditional difference. Thus Never really is a full best reply for every player on this reserve. Its own Never values are at least c a for some fixed c>0 by (2), and its debts are O(Ma²) by the second formula, uniformly for z close to y. This argument permits z with some zero coordinates and total close to one.

For small desired b choose a finite unit word x with V(x)≤b and ∑wᵢCᵢ(x)≤κ(w)+b, by the definition of infimum. Its length may grow arbitrarily as b↓0. Set a=L b² for a sufficiently large FIXED L. Put individual unconditional head masses (b−a)xᵢ(n) on its dates and unconditional reserve masses a yᵢ (1−r)rⁿ on the following dates. This matches total β=b exactly. Given that the head was survived, each reserve component has zᵢ=yᵢ/(1−fᵢ^h), with fᵢ^h the finite head mass; these z approach y uniformly. The unmodified head, with Never afterwards, has Bᵢ^h−eᵢ^h≤C b² uniformly by the first part of (2) and V(x)≤b. The reserve lifts its Never offer by at least (∏_{j≠i}(1−fⱼ^h)) ca, which dominates C b² by choice of L. Every deadline in the head retains its old value; on reserve dates the literal Never comparison is optimal. Hence Bᵢ=eᵢ on this new full calendar. By (2) the head's Never-minus-prescribed defect was (b−a)² Cᵢ(x)+O(Mb³). The change in that defect is

    (∏_{j≠i}(1−fⱼ^h))(eᵢ^res−Uᵢ^res)
       + (∏_{j≠i}(1−fⱼ^h)) fᵢ^h Uᵢ^res = O(Ma²+Mba).

This is exact by conditioning, with all reserve values evaluated at the conditional reserve laws. Thus the new D_w is at most b²κ(w)+O(b³), proving the limsup. This repair of all moving deadline caps is why ordinary Taylor expansion of a selected cap at one deadline would not suffice.

## The positive-gap source and the original response caps

Let $A=\inf\{\sum_i d_i:\nu=0\}$ on actual profiles, and let $E$ be the zero-debt subset of the compact Euclidean closure of the actual tuples $(U,B,e,(1-f_i)_i)$. Set $\alpha=\min_E\nu$. Finite mass escaping dates is recorded separately from the original Never mass. AllNever belongs to $E$. We study the joint alternative $A>0$, $\alpha=1$. The positive absorbing gap is a necessary native reduction of the signed Fin4 conjecture. Indeed, if a finite four-player table lacks a uniform-equilibrium payoff, choose any bound on its finitely many rewards. The checked normalization gives another such table with one own singleton equal to one and the others zero. Its total-debt infimum is strictly positive by the checked equivalence below. Subtract one from all nonempty rewards of the pivot recipient. On an absorbing profile the pivot's prescribed payoff and every finite-deadline reply lose exactly one. At either own level the finite-deadline supremum dominates literal Never, as follows by sending the deadline to infinity. Thus on such profiles the full debts are unchanged, proving $A>0$ in the resulting native table. Our conclusion concerns the possibility $\alpha=1$ at this native reduction. [`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff`](../../UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean)

For completeness $A>0$ implies the singleton hypotheses needed here. Move the smallest original Never marginal to one finite date. Its size is at most $\nu^{1/4}$. All four prescribed payoffs and three rival-dependent caps change by at most $2M\nu^{1/4}$ each by coupling, so $A\le\sum_i d_i+14M\nu^{1/4}$. Raise every nonempty native reward in recipient row $i$ to $w_i(Z_i+t)$, with $w_i,t>0$ and origin unchanged. On the native table finite deadlines tending to infinity give the Never response in the limit. On the raised table such late replies dominate the raised Never payoff. Every finite response shifts by the same amount before scaling. Thus the true raised cap and the raised regret are $w_i(B_i+t)$ and $w_i(d_i+t\nu)$. The total raised debt therefore has strictly positive infimum $m_w(t)$ by the repair bound. The terminal Nash criterion implies no uniform-equilibrium payoff at this raised table. In particular with all $w_i=1$ the known no-UE matrix theorems give $\Gamma y\gg0$ for some simplex vector $y$, and the singleton matrix is $R_0$, meaning $x\ge0,\ \Gamma x\ge0,\ x_i(\Gamma x)_i=0$ for all $i$ implies $x=0$. In particular every column has a negative entry. With arbitrary positive weights the centered singleton matrix is $\operatorname{diag}(w)\Gamma$, with the same $R_0$ property. [`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`](../../UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean) · [`exists_finFour_simplex_positive_projectiveResidual_of_no_uniformPayoff`](../../UniformEquilibrium/Quitting/Projective/FinFourAmbientQSimplex.lean) · [`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff`](../../UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean)

We recall the cap estimate to retain its full strength along the changing prices. At a fixed raised table let $m=m_w(t)>0$, let $M'\ge1$ bound its rewards, and put $b'=\min(m/4,m^2/(32M'))$. At any actual tail of raised debt $D\le m+b'$, all raised caps satisfy $B_i^{r}>s_i+m+b'$, where $s_i=w_it$. Here is the proof. Prefix a mixed Nash row of the finite stage game with child $B^{r}-(m/2)\mathbf1$. In the true child the passive Continue offer rises by $H_i m/2$, where $H_i$ is the probability all rivals continue through this row. Continuing has zero row regret whenever prescribed with positive probability. The assigned Quit loss is at most $q_iH_i m/2$ with $q_i$ the hazard of owner $i$. The exact prefix identity gives new total debt equal to the old total times the joint survival plus the sum of assigned row losses at the true child. If the row exits with probability $z$, then $\sum_i q_iH_i\le z$, so $m\le(1-z)(m+b')+zm/2$. Thus $z<1$ and $z/(1-z)\le2b'/m$. Everyone can wait at this proper row. Its Wait inequality at the lowered child gives $B_i^r-s_i\ge m/2-2M'(1-H_i)/H_i\ge m/4$.

If $B_k^r-s_k\le m+b'$ for some $k$, prefix that owner alone at hazard $u=m/(16M'+2m)$. The owner's cap selects Wait and stays fixed. An outsider's Wait advantage is at least $(1-u)m/4-2M'u=m/8$. The resulting total debt is $(1-u)D+u(B_k^r-s_k)\le m+b'$. Iterate. Every resulting outsider cap still exceeds its own level by at least $m/4$ by the preceding paragraph and tends to its reward when $k$ quits alone. This makes column $k$ of the centered singleton matrix nonnegative, contradicting $R_0$. Thus the claimed full-cap estimate holds at the actual tails.

## Price asymptotics at the AllNever-only source

Assume A>0 and α=1. The preceding identity gives the original total-debt infimum

    m_w(t)=inf (D_w+tWν).

AllNever gives the upper bound Wt. Let t↓0 and take any actual family of excess o(t²). Its native D_w→0, hence β→0 by compactness and α=1. Uniformly 1−ν=β+O(β²). If κ(w)>0 then

    Wt−m_w(t)=W²t²/(4κ(w))+O(t³),
    β/t → W/(2κ(w)) on every family of excess o(t²).              (3)

Indeed use (1) and its cubic error at b=Wt/(2κ(w)) for the lower bound on the improvement. The lower cubic estimate and D_w≤Wt β+o(t²) bound β/t from above. Completing the square in Wtβ−κ(w)β², with error O(t³) on this bounded scale, gives the upper bound on the improvement and the unique optimizing ratio. On every family of excess O(t³) the sharper bound is β=Wt/(2κ(w))+O(t^{3/2}).

If κ(w)=0, on every sufficiently small slice b there are actual profiles with D_w≤C b³. At b=k√t, with small fixed k>0, the improvement over Wt is at least [Wk−Ck³+o(1)]t^{3/2}. Hence Wt−m_w(t)≥c t^{3/2}. Every family of excess o(t^{3/2}) has β≥c′√t, by 1−ν≤β and nonnegative native debt. For near-minimizing references with excess o(t²), D_w≤Wtβ+o(t²) gives D_w/β²→0.

Both regimes are determined completely by the same pair-data functional on every higher completion satisfying α=1 and A>0. No family of o(t²)-minimizers can have t≪β≪√t.

## An optimized endpoint and its four necessary inequalities

Choose actual profiles within both $o(t^2)$ and the cap tolerance $b'$ of the original infimum, with $t\downarrow0$. Let $G=\operatorname{diag}(w)\Gamma$, $K=\operatorname{diag}(w)J$, and choose a subsequence of normalized total vectors converging to $z$ in the probability simplex. If $\kappa>0$, then (3) gives $D_w/\beta^2\to\kappa$ by subtracting $Wt\nu$ from the raised objective. If $\kappa=0$, the same ratio tends to zero. In either case $B_i-e_i=O(\beta^2)$ by the marginal Never bound, so (2) gives $V=O(\beta)$ and $C_w=\sum_i w_i C_i\le D_w/\beta^2+O(\beta)$. The definition of $\kappa$ gives the reverse liminf. Truncating and normalizing gives finite words $x^n$ with the same limits of totals, deadline violations and costs. The original cap estimate gives $w_i B_i>m_w(t)>0$. Since $B_i=e_i+O(\beta^2)=\sum_j\Gamma_{ij}f_j+O(\beta^2)$, this implies $\Gamma z\ge0$. For $\kappa>0$, dividing by $\beta$ and applying (3) gives
\[
                   (Gz)_i\ge2\kappa\quad\text{for all }i.       \tag{4}
\]

If \(\kappa>0\), the necessary endpoint inequality is actually **strict in every coordinate**. More precisely set
\[
 r_i(z)=\min_{j:\Gamma_{ji}<0}\frac{(\Gamma z)_j}{-\Gamma_{ji}}>0 .
\]
Then \((Gz)_i\ge (2+r_i(z))\kappa\). To prove this, fix \(0<d<1\) with \(d/(1-d)<r_i(z)\). Scale the old unit word by \(1-d\) and place a new block of total mass \(d\), all assigned to owner \(i\), before its first physical date, subdivided into vanishingly small pulses. Throughout this block the leading passive vector runs from \((1-d)\Gamma z^n\) to \((1-d)\Gamma z^n+d\Gamma_{\bullet i}\) and is strictly positive for large \(n\) by the chosen bound. The joining term \(Jx(t)\) there tends uniformly to zero as the mesh is refined. Old deadline residuals merely scale by \(1-d\); the new sequence still has \(V\to0\). The new cost is exactly \((1-d)^2 C_w(x^n)+d(1-d)(Gz^n)_i\), because both diagonals are zero. Comparing its limit with \(\kappa\), cancelling \(d\) and letting \(d/(1-d)\uparrow r_i(z)\) proves the claim.

**Energy exclusion.** If \(G\) is symmetric and each unordered pair satisfies
\[
       K_{ij}+K_{ji}\le G_{ij},                                   \tag{5}
\]
then \(A>0\) and the AllNever-only alternative cannot both hold. The other 32 native rewards are arbitrary. For a unit word with total vector \(v\), direct expansion gives
\[
 C_w(x)=\tfrac12 v^\top Gv+
           \sum_t x(t)^\top (G/2-K)x(t).
\]
The diagonal vanishes and each off-diagonal pair coefficient in the sum is nonnegative by (5). Consequently \(z^\top Gz\le2\kappa\) for the limiting words just selected. For \(\kappa>0\) this contradicts the strict endpoint bounds after multiplying them by \(z_i\) and summing. For \(\kappa=0\), we have \(\Gamma z\ge0\) and \(z\) is a probability vector. The \(R_0\) property and positivity of the weights imply \(z^\top Gz>0\), again a contradiction.

**Finite quantitative necessary condition for arbitrary pair data.** Put
\[
 H=(G+G^\top)/2,\quad
 a=\max_{ij}|G_{ij}-H_{ij}|,\quad
 b=\max_{i<j}(K_{ij}+K_{ji}-H_{ij})_+,\quad
 M=\max(1,\max_{ij}|\Gamma_{ij}|).
\]
Write \(K_\Gamma=\{z\in\Delta:\Gamma z\ge0\}\). If this set is empty the necessary endpoint condition already fails. Otherwise for \(z\in K_\Gamma\) put \(m(z)=\min_i(Gz)_i\), \(r(z)=\min_i(\Gamma z)_i/M\), and
\[
 \delta_\Gamma(w)=\min_{z\in K_\Gamma}
  \left[z^\top Gz-\frac{2m(z)}{2+r(z)}\right] .
\]
For every fixed positive price direction, survival of \(A>0\) and the AllNever-only alternative requires
\[
                         a+b\ge \delta_\Gamma(w)>0.                \tag{6}
\]
All variables in this minimization are just the four simplex coordinates. The test uses the 24 pair entries. To prove it, the skew-sensitive part of \(C_w\) is
\(\sum_{n<m} x(n)^\top(G-H)x(m)\), which is bounded below by \(-a/2\) since the word has unit mass. Its simultaneous pair correction is \(\sum_n\sum_{i<j}(H_{ij}-K_{ij}-K_{ji})x_i(n)x_j(n)\ge-b/2\). The symmetric total-vector term is \(z^\top Hz/2=z^\top Gz/2\). Hence the limiting optimized words give \(z^\top Gz\le2\kappa+a+b\). The endpoint inequalities give \(m(z)\ge(2+r(z))\kappa\), also when \(\kappa=0\); indeed \(r(z)\le r_i(z)\) for every negative-column ratio above. Combining proves the weak inequality in (6). Finally \(z^\top Gz\ge m(z)\) on \(K_\Gamma\). If \(m(z)>0\) then \(r(z)>0\), giving strict positivity of the minimized integrand. If \(m(z)=0\), equality \(z^\top Gz=0\) would be a nonzero homogeneous complementarity solution since every term \(z_i w_i(\Gamma z)_i\) is nonnegative. The \(R_0\) condition excludes this and compactness gives the uniform strict inequality.


There is a second finite comparison which uses the coefficient directly. For each of the 75 weak orders $\pi$ of four owners (ordered set partitions), assign each unordered pair $i,j$ the coefficient $c_{ij}(\pi)=G_{ij}$ if $i$ is earlier, $G_{ji}$ if $j$ is earlier, and $(G-K)_{ij}+(G-K)_{ji}$ if they tie. Put $L_*(z)=\min_\pi\sum_{i<j}z_i z_jc_{ij}(\pi)$. Every word of total $z$ has $C_w\ge L_*(z)$. Independently draw one date per owner from its normalized mass, choosing any date for a zero-mass owner. Their weak order gives exactly the expected pair charges in $C_w$. Conversely every deterministic weak order is a word of this total, so this lower bound is exact before the deadline constraints are imposed. The optimized endpoint must obey $L_*(z)\le\kappa$, as well as $\Gamma z\ge0$ and the coordinate upper bounds on $\kappa$ above. Every unit word of fixed length with $V=0$ gives a further upper bound $\kappa\le C_w(x)$. For example a single date with total $v$ is feasible when $(\Gamma-J)v\ge0$ and costs $v^\top(G-K)v$. The joint conditions are finite real algebraic tests for any selected word length.

## A rational box and its matrix tests

Use the prices \(w=(1,1,1,1)\) and the central pair data
\[
 \Gamma_0=\begin{pmatrix}0&-7&-2&5\\-7&0&6&-1\\-2&6&0&-1\\5&-1&-1&0\end{pmatrix},
 \qquad 10J_0=\begin{pmatrix}0&-7&-18&15\\-63&0&24&-3\\-8&36&0&-6\\5&-8&-9&0\end{pmatrix}.
\]
In lexicographic pair order, the values \((\Gamma_0)_{ij}-(J_0)_{ij}-(J_0)_{ji}\) are \((0,3/5,3,0,1/10,1/2)\). All six satisfy the symmetric energy comparison. More quantitatively, the indicated native positive-gap AllNever alternative is excluded whenever **each of the 24 independent entries lies within \(10^{-4}\) of its displayed center**, with every higher reward arbitrary. Here is an explicit bound. The central inverse is
\[
 M_0=\frac1{385}\begin{pmatrix}12&25&35&126\\25&20&105&70\\35&105&70&175\\126&70&175&168\end{pmatrix}.
\]
Its maximum row sum is \(7/5\) and the sum of all entries is \(122/35\). The inverse perturbation series gives \(\|\Gamma^{-1}-M_0\|_\infty\le (7/5)^2(3\cdot 10^{-4})/(1-(7/5)3\cdot 10^{-4})<10^{-3}\) in the row-sum norm. Thus \(M=\Gamma^{-1}\) has every entry greater than \(3/100\), every column sum less than \(3/2\), and its total sum is less than \(7/2\). For a feasible simplex point \(z\), write \(u=\Gamma z\ge0\). From \(z=Mu\) and \(\mathbf1^\top z=1\) we get \(\max u>2/7\), \(\sum u>2/3\), and \(z_i>1/50\) for every \(i\). Write \(m=\min u\). If \(m\le1/7\), then \(z^\top u-m\ge(\max u-m)/50\ge 1/350\). If \(m\ge1/7\), the threshold integrand in (6) is at least \(m^2/(2M_*+m)\ge1/791\) since \(M_*=\max(1,\max|\Gamma_{ij}|)\le8\). Consequently \(\delta_\Gamma(\mathbf1)\ge1/791\) throughout this box, whereas \(a+b\le4\cdot10^{-4}\). This proves the exclusion with the stated radius.

At the center every matrix \(D_t=\Gamma_0-tJ_0\), \(0\le t\le1\), is \(R_0\) of homogeneous complementarity degree one. All columns have the same strict matched signs with positive mates \((03)(12)\) and negative crossings, throughout the segment. With \(v=(18,20,35,49)^\top\) we have \(\Gamma_0v=35\mathbf1\) and \(10(\Gamma_0-J_0)v=(385,791,68,735)^\top\). Thus \(D_t\,\mathrm{diag}(v)\) followed by the mate column permutation is a strictly row diagonally dominant Z-matrix with positive diagonal. Its inverse is nonnegative by the Neumann series and strictly positive by irreducibility. The mate permutation has positive determinant, as does the dominant matrix by homotopy to its diagonal, so \(D_t^{-1}\gg0\), \(\det D_t>0\). At homogeneous offset complementary feasibility forces zero, and at offset \(-\mathbf1\) the unique response is \(D_t^{-1}\mathbf1\gg0\), of local index one. Write $Q_i(q)$ for the Quit offer against the independent rival actions in a single row $q$. The condition that every sufficiently small nonzero row has an active $i$ with $Q_i(q)\le0$ fails for every higher completion. If only owners 0 and 3 have positive hazards, each has a strictly positive Quit offer from its mate. Also set $\rho=\min_{ij}(M_0)_{ij}/\sum_k(M_0)_{kj}$ and $\tau=\max_{ij}|(M_0(\Gamma_0-J_0))_{ij}|$. The bound $\tau\le\rho^2/8$ fails since $(M_0(\Gamma_0-J_0))_{20}=18/11>1$ and $\rho\le1/4$.

Consider the following two families of finite support words in construction order. Take all three partitions into complementary pairs, using the pair containing owner 0 first. In the second family take all 24 relabelings of $((2,3),(0,2),(0,1,3))$; the order inside each support has no effect. At an expanding real eigenvector the required margins are strict positivity of all active hazards and of all quiet players' Continue-minus-Quit comparisons. The following calculation specifies these margins as linear forms and tests both orientations of each eigenvector. All fail at the center. Respectively they have four and 36 real expanding eigenvalues in total, all simple; each associated eigenvector has both positive and negative tested hazard-or-quiet margins. None of the 27 products has eigenvalue one. Here is reproducible pseudocode using only rational arithmetic and isolating the real roots of quartics. For each tested support \(S\), embed \(((J_0-\Gamma_0)_{SS})^{-1}\) into four columns in the positions \(S\), obtaining \(C_S\). Put \(A_S=I+(\Gamma_0)_{\bullet S}C_S\) and stack the rows of \(C_S\) and \((A_S)_{\bar S\bullet}-(J_0)_{\bar S S}C_S\) to form \(B_S\). Build each word product \(H\) from the identity in construction order, stacking \(B_S H_{\rm old}\) into \(B\) before each update \(H=A_SH_{\rm old}\). Compute \(p(X)=\det(XI-H)\) and \(T(X)=B\operatorname{adj}(XI-H)\). Check \(p(1)\ne0\), and form disjoint rational isolating intervals of width at most \(10^{-30}\) for every real root above one. For each such root verify its multiplicity is one and that, in some fixed column of \(T\), ordinary rational interval Horner evaluation gives one strictly positive and one strictly negative entry on its isolating interval. For the two families the counts of roots satisfying these strict rejections are \((4,36)\), accounting for every expanding real root. Thus the finite tests do not certify this box center. The strict rejections persist on some neighborhood by continuity. These comparisons concern the specified finite support words.

At this center $J_0-\Gamma_0$ fails positive diagonal symmetrizability. The products around the directed triangle $0,1,2$ in opposite orientations have unequal absolute values.

## A second open exclusion from a single trial date

Use owners 0 through 3, $w=(1,1,1,1)$, and put $K=\Gamma-J$ **in this example**. Take
$$
 \Gamma=\begin{pmatrix}0&-2&3&-1\\-1&0&-1&3\\3&-1&0&-1\\-1&3&-1&0\end{pmatrix},\qquad
 K=\begin{pmatrix}0&3&5/2&-2\\-2d&0&2&1/2\\2&-2&0&6\\3&10&-1/2&0\end{pmatrix},
 \quad d=1/10000,\quad J=\Gamma-K .
$$
Write $H_{ij}=\min(\Gamma_{ij},\Gamma_{ji})$, with zero diagonal. Here each of the three possible pair charges is at least $H_{ij}$, so $L_*(z)\ge Q(z):=z^\top Hz/2$. The inverse of $\Gamma$ is strictly positive. Thus the feasible simplex section is the convex hull of the normalized columns $v_j=(\Gamma^{-1})_{\bullet j}/\sum_i(\Gamma^{-1})_{ij}$. Indeed $z=\Gamma^{-1}(\Gamma z)$, with nonnegative coefficients before normalization. Direct multiplication gives the matrix $V$ with these columns and its pair charges
$$
 V=\begin{pmatrix}2/15&4/21&2/5&10/57\\1/5&1/7&1/5&7/19\\7/15&5/21&1/5&17/57\\1/5&3/7&1/5&3/19\end{pmatrix},\quad
 \frac{V^\top H V}{2}=
 \begin{pmatrix}1/25&1/15&11/75&13/285\\1/15&1/21&1/15&7/57\\11/75&1/15&1/25&13/285\\13/285&7/57&13/285&1/57\end{pmatrix}.
$$
Every entry is at least $1/57$, attained by the last vertex, so the minimum of $Q$ on the feasible simplex section is $1/57$. The date $v=(1,d,d,d)/(1+3d)$ has $Kv=(7d/2,d/2,2+4d,3+19d/2)/(1+3d)\gg0$ and $C_w=(17d/2+14d^2)/(1+3d)^2<1/57$. This proves the exclusion. With the same word and weights it holds on an open neighborhood in all 24 pair rewards. The strict guards and strict comparison persist by continuity and compactness. In detail, a sequence of feasible minimizing totals for perturbed data has a subsequential limit feasible at the center, and its polynomial costs converge to the centered cost.

Every member of the central pencil $(1-t)\Gamma+tK$ is $R_0$ of degree one. Each column retains an entry strictly negative for the whole pencil, in rows 1,2,3,0 for columns 0,1,2,3 respectively. A positive two-coordinate kernel requires both reciprocal entries to vanish, which never happens here: in each pair at least one of its two entries keeps its strict sign throughout. Every principal triple and the full matrix have strictly positive determinant throughout. Here are small rational certificates for that last assertion. On each quarter $t=(j+u)/4$, $j=0,1,2,3$, write the principal determinant in powers $\sum_h c_h u^h$ and form its Bernstein coefficients of degree $k$ equal to the size of the principal block. The coefficient with index $l$ is $\sum_{h=0}^l c_h {l\choose h}/{k\choose h}$. The minima over all four quarters and all indices for blocks $012,013,023,123,0123$, respectively, are
$$
341719/160000,\quad2020217/480000,\quad223/96,\quad207/128,\quad150157/5000.
$$
The positivity of these coefficients implies pointwise positivity. Thus no support gives a homogeneous nonzero complementary solution, and the degree along the pencil is constant. The degree of $\Gamma$ equals that of its symmetric version with $\Gamma_{01}=-1$. On the straight segment between them, every two- and three-owner determinant is nonzero by reciprocal signs and the two same-sign terms in each hollow triple determinant. After scaling the columns by $(1,1,11/10,1)$ and swapping positive mates the full matrix is strictly row-diagonally dominant, and every singleton column has a negative entry. For the latter matrix at offset minus the all-ones vector, every row of $\Gamma x$ must be at least one. Each row has just one positive mate, forcing $x\gg0$ and hence $\Gamma x=\mathbf1$. The unique solution is $x=\mathbf1$, with positive determinant 45 and local index one. This proves the degree claim. The small-row Quit-offer condition also fails for every completion, because if only 0 and 2 play with small positive hazards each has strictly positive Quit offer from its mate with $J_{02}=1/2$ and $J_{20}=1$.

The quantitative bound (6) permits this example at **every** price direction. Normalize $\max_i w_i=1$. Write $a=\max_{ij}|w_i\Gamma_{ij}-w_j\Gamma_{ji}|/2$. If $a<1/40$, every pair other than 01 has equal reciprocal entries of absolute value at least one, so its weight difference is less than $1/20$. All weights would exceed $9/10$ along paths of at most two such edges. Pair 01 then gives $a\ge(2w_0-w_1)/2>2/5$, a contradiction. On the other hand set $z=c\Gamma^{-1}(1/w_i)_i$, with $c>0$ normalizing its sum to one. From positivity of the inverse,
$c\le(\sum_{ij}(\Gamma^{-1})_{ij})^{-1}=4/21$.
Every weighted coordinate of $\Gamma z$ is $c$, and its minimum unweighted coordinate is $c$. Testing this $z$ in the preceding finite norm threshold gives
$$
 \delta_\Gamma(w)\le c-\frac{2c}{2+c/3}=\frac{c^2}{6+c}<1/100.
$$
Thus the strict separation uses a low-cost word compatible with the signed deadline constraints even though the uniform skew bound by itself cannot exclude the example. Both the failure of that norm exclusion for all normalized positive weights and the degree and small-row Quit-offer comparisons persist on a sufficiently small open neighborhood. For the norm comparison use the same path argument with slightly perturbed reciprocal entries, and the same inverse-vector construction with a uniform bound on the perturbed inverse column sums. The two finite support-word tests above fail here too. Applying the exact quartic calculation above yields no real expanding eigenvalues on the three pair partitions and 16 on the 24 mixed words. All 16 are simple, each fails by opposite strict signs in one adjugate column, and none of the 27 word matrices has eigenvalue one. These computations and the strict test-word comparison depend only on the two pair matrices.


The quadratic coefficient, cap comparisons, and the two raw source exclusions are ordinary mathematical results. They leave unrestricted four-player existence and the possibility of a positive absorbing gap with $0<\alpha<1$ open.
