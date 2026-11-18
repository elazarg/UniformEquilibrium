# Exact native equilibria and the cost of small absorption

The [quadratic small-exit theorem](../exports/QUADRATIC_COST_AND_ALLNEVER_SOURCE_EXCLUSION.md) excludes the AllNever-only alternative at a hypothetical positive native gap on two explicit regions of pair rewards. Here the true unconstrained cost coefficient is computed, and exact infinite equilibria are constructed on the same tables. In these equilibria each clock can wait forever with positive probability. Ruling out a gap on absorbing profiles for every higher completion would require an additional argument. The final calculation uses a 25-date sequence of supports on the asymmetric example. [Rational checker for the expanding directions](../experiments/CODEX_ROOT__TWO_EXPANDING_NATIVE_CLOCKS.py)

## Zero unconstrained cost at both pair centers

Use the normalized physical words of the quadratic small-exit theorem. At a date their nonnegative vectors are x(t), R(t)=Σ_{s≥t}x(s), ∑_i R_i(1)=1 and g(t)=ΓR(t)−Jx(t). The unconstrained coefficient κ(w) is the limit, as a decreases to zero, of the infimum of Σ_t Σ_i w_i x_i(t)g_i(t) over all finite unit words with every g_i(t)≥−a. The endpoint-constrained coefficient κ₊(w) also requires ΓR(1)≥−a. Assume Γ maps some simplex point to a strictly positive vector, as in the original small-exit theorem. Below Δ is the four-coordinate simplex and |y| denotes the sum of the coordinates when y≥0.

Take any strictly positive diagonal matrix D and any symmetric H with H≤DΓ entrywise. Write

    t=max(0,max_{x∈Δ} xᵀ(DJ+JᵀD−H)x),     m=min_{z∈Δ, Γz≥0} zᵀHz.

Any upper bound on t may replace t throughout. Assume m>t, that some nonzero y₀≥0 satisfies y₀ᵀHy₀<t|y₀|², and that K=Γ−J is a Q-matrix. Thus for every vector b there is x≥0 with Kx+b≥0 and x·(Kx+b)=0. Then for every w≫0,

    κ(w)=0,     κ₊(w) ≥ [min_i w_i/D_ii] (m−t)/2 >0.

Starting from y₀, solve the linear complementarity problem with offset Γy, put z=y+x, and repeat from z. Its residual g=Γz−Jx is nonnegative and x_i g_i=0 for each i. The quadratic E(y)=yᵀHy−t|y|² cannot increase. Indeed

    zᵀHz−yᵀHy = 2xᵀHz−xᵀHx
                ≤ 2xᵀDΓz−xᵀHx
                = xᵀ(DJ+JᵀD−H)x ≤ t|x|².

The change of t|y|² is at least t|x|². Every normalized aggregate y/|y| therefore stays in the compact set {v∈Δ:vᵀHv≤t}, disjoint from Γv≥0. Some component of Γy is at most −c|y| at every step for a fixed c>0. Feasibility Γy+Kx≥0 forces |x|≥c|y|/max(1,max|K_ij|). Hence the aggregates grow at least geometrically, for any choice of complementarity solutions.

After n steps put the increments into physical order x_n,…,x_1 and divide by |y_n−y₀|. In the unnormalized word the remaining mass at every date is its original new aggregate minus the same y₀. Its guards thus differ from the exact complementary guards by −Γy₀. After normalization their maximal negative part tends to zero. The weighted cost is exactly −Σ_i w_i(Γy₀)_i (y_{n,i}−y_{0,i})/|y_n−y₀|², which tends to zero. The definition of κ gives the first claim since all feasible costs are at least −a max_i w_i.

For every finite word, weighted by D itself, the arbitrary residuals give

    zᵀHz−yᵀHy ≤ 2xᵀDg+t|x|²

on each backwards step from y to z=y+x. Summing from zero to a simplex endpoint z gives Σ xᵀDg≥(zᵀHz−t)/2 since Σ|x|²≤1. On words with g≥−a, changing weights from D to w preserves this lower bound after multiplication by min_i w_i/D_ii, up to O(a). Every limiting endpoint of words admissible for κ₊ has Γz≥0. This proves its lower bound. In particular no unknown optimum over orders or word lengths enters the strict gap. A nonzero homogeneous complementarity degree together with the R₀ property implies the Q assumption by the finite-dimensional degree theorem. The established AllNever-only source requires κ=κ₊ at every positive w, so this gap excludes it.

For the two pair centers in the quadratic-cost result take D=I, H_ij=min(Γ_ij,Γ_ji). A seed with equal positive masses on the hostile pair 01 has negative H energy. At the symmetric center H=Γ, all six entries of H−J−Jᵀ are nonnegative, and hence t=0. On Γz≥0, positivity of Γ⁻¹ implies strictly positive energy: writing u=Γz gives zᵀHz=uᵀΓ⁻¹u>0. The published matched positive-mate certificate gives R₀ and degree one for K.

In fact the conclusion holds throughout the full symmetric box of 24 independent changes of at most 10⁻⁴. Use the perturbed H=min(Γ,Γᵀ), so t≤3·10⁻⁴. Its distance from Γ is at most 2·10⁻⁴ entrywise. The inverse bounds in the box give z_i>1/50 and Σ_i(Γz)_i>2/3 throughout the feasible simplex. Thus m>1/75−2·10⁻⁴, and κ₊(w)>(min_i w_i)/160. For completeness the Q verification persists throughout this specified box. For v=(18,20,35,49), at the center Kv=(385,791,68,735)/10. Its coordinates change by at most 2·10⁻⁴Σ_i v_i=0.0244. All matched positive and other off-diagonal negative signs of K persist. After column scaling by v and swapping its two pairs of positive mates, K is a strictly row-diagonally dominant matrix with positive diagonal and nonpositive off-diagonal entries. Its inverse is strictly positive by the convergent geometric series and irreducibility. Undoing the scaling and permutation gives K⁻¹ strictly positive and det K>0. A homogeneous complementary solution is zero, since any nonzero nonnegative Kx would give x≫0; offset minus the ones vector has unique solution K⁻¹1≫0 and positive local index. This establishes the required R₀ degree one.

At the asymmetric center the six off-diagonal sums J_ij+J_ji are, in lexicographic pair order, −29999/5000, 3/2, −3, −2, −9/2, −15/2. All are strictly below the corresponding H entries −2,3,−1,−1,3,−1. Thus t=0. The previously computed Gram bound on normalized inverse columns gives m≥2/57, with equality at the last column, and K has R₀ degree one by the principal determinant calculation. Hence κ₊(w)≥(min_i w_i)/57 while κ(w)=0, and the strict coefficient gap persists on an open neighborhood in all 24 entries. Indeed the strict coefficient inequalities, the negative seed, the positive feasible direction and the positive minimum on the compact simplex persist, and an R₀ matrix of nonzero degree retains both properties on a neighborhood. All other native entries can vary arbitrarily.

This computes the previously undetermined unconstrained value at both centers and their indicated neighborhoods. The generated contacts need not repeat a finite support pattern. Their limiting total directions stay separated from Γz≥0. Native normalized words alone do not assert an actual positive-debt signed source or produce a four-player uniform equilibrium.

[Pair data and rational certificates](../exports/QUADRATIC_COST_AND_ALLNEVER_SOURCE_EXCLUSION.md) · [Endpoint-constrained coefficient](CODEX_ROOT__NATIVE_QUADRATIC_GRID.md)

## Exact equilibria at every small absorption level for arbitrary higher rewards

Consider the pair data of the zero-cost criterion. Thus H is symmetric, D is strictly positive diagonal, H≤DΓ entrywise, t≥0 bounds xᵀ(DJ+JᵀD−H)x on the simplex, and m=min_{Γz≥0,z∈Δ} zᵀHz satisfies m>t. Some simplex point y₀ satisfies y₀ᵀHy₀<t. Assume K=Γ−J has the R₀ property and nonzero homogeneous complementarity degree. Both neighborhoods of pair data in the preceding calculation satisfy these hypotheses. The 32 remaining native rewards can be assigned any finite real values.

For every sufficiently small prescribed β>0 there exists an actual native Nash profile whose sum of individual probabilities of ever quitting is exactly β. One can instead prescribe its joint absorption probability to be exactly any sufficiently small positive number. These are separate scalar prescriptions. Every player chooses Never with positive probability and every unilateral finite deadline or literal Never is tested. Conditional hazards on the resulting physical calendar have geometrically summable tails with a rate bounded away from one for the fixed table. In particular these are literal independent equilibria on the infinite calendar. The theorem establishes microscopic equilibria at the AllNever boundary; a positive joint Never probability prevents a general inference to absorbing equilibria on signed row shifts.

Write v for a finite timing block's continuation. In one actual product row of hazards q, let P_i be the expected passive reward on a rival exit, H_i the rival survival probability, and Q_i the forced Quit payoff. Near zero set G_i(q,v)=P_i(q)+H_i(q)v_i−Q_i(q). The polynomial identities give, in any fixed norm,

    G(q,v)=v+Kq+O((|q|+‖v‖)|q|),
    P(q)+H(q)v=v+Γq+O((|q|+‖v‖)|q|).

Here and below |q| is the sum of absolute values. All constants may depend on the full table. For small q the equation min(q,G(q,v))=0 componentwise says precisely that q≥0 and the Wait action is optimal for everyone, with all active owners indifferent. Its output equilibrium payoff is w=P+Hv. The homogeneous map min(q,Kq) has norm at least c|q| for all q by R₀ and compactness of the unit sphere. Thus any sufficiently small solution for sufficiently small v satisfies |q|≤C‖v‖: replacing its second argument G by Kq changes the minimum by at most ‖v‖+O((|q|+‖v‖)|q|).

Begin at a terminal boundary v₀=εΓy₀, ε≥0. Read an arbitrary finite sequence of such Nash rows backwards, put y=εy₀+Σq over the rows already taken, and let v be their current output. If the aggregate stays small, uniformly in the length we have

    ‖v‖≤C|y|,      ‖v−Γy‖≤C|y|².

Indeed |P_i|≤M(1−H_i)≤M|q| at each row for a reward bound M, and multiplying v_i by H_i cannot increase its absolute value. This proves the first estimate by summation. Summing the second polynomial expansion proves the other estimate since Σ(|y|+|q|)|q|≤C|y_final|². Consequently every next small solution has |q|≤C|y|. For θ strictly between t and m (hence θ>0), its contact equality qᵀDG(q,v)=0 gives

    qᵀDΓ(y+q)=qᵀDJq+O((|y|+|q|)²|q|).

Applying H≤DΓ as in the linear calculation, the change of E_θ(y)=yᵀHy−θ|y|² is at most

    (t−θ)|q|²−2θ|y||q|+O((|y|+|q|)²|q|).

This is nonpositive for all sufficiently small aggregates, because |q|≤C|y|. If ε>0 the energy begins negative and remains so. The normalized aggregate lies in the compact set zᵀHz≤θ disjoint from the feasible simplex Γz≥0. In particular a coordinate of Γy is at most −c|y|. Since v differs from Γy by O(|y|²), the Nash inequality G(q,v)≥0 requires |q|≥c'|y|. The aggregate grows by a factor ≥1+c' at each row. All constants and the permitted neighborhood are independent of the number of rows and the choice among Nash solutions.

To hit an exact prescribed level β, take N physical rows and consider their 4N variables in backward order q₁,…,q_N. For signed trial variables extend P,H,Q by their polynomials. Define v_n=P(q_n)+H(q_n)v_{n−1} and use the 4N-dimensional map whose n-th block is min(q_n,G(q_n,v_{n−1})). A zero within the open cube of coordinate absolute values below 1/2 supplies genuine nonnegative Nash rows. On this cube define the continuous size

    B(q)=Σ_i [1−∏_{n=1}^N(1−|q_{ni}|)],   Ω={q: B(q)<β}.

For β<1/4 the closure of Ω lies strictly inside the cube. Every individual coordinate has absolute value at most β there; moreover Σ_n|q_n|≤−Σ_i log(1−f_i)≤β/(1−β), with f_i=1−∏_n(1−|q_{ni}|). These bounds hold also on the boundary. Thus for 0≤ε≤β and sufficiently small β all actual zeros in the closure satisfy the uniform estimates above. At ε=0 the only such zero is zero: the R₀ stage bound successively forces q₁=0,q₂=0,… . Its local degree is the N-th power of the nonzero degree for K. In detail, for each fixed N the first-order positively homogeneous map at the origin is triangular, with blocks min(q_n,Kq_n+ΓΣ_{k<n}q_k). Multiplying all earlier-stage contributions by a common homotopy parameter from one to zero introduces no nonzero root, by induction using R₀. Compactness on the 4N-dimensional unit sphere and the uniform first-order remainder give the same local degree as the product of N copies of min(q,Kq). This uses ordinary finite-dimensional Brouwer degree only.

At ε=β the closure of Ω has no zero for sufficiently large N: a zero would have terminal aggregate β and final aggregate at most β+β/(1−β), whereas growth by (1+c')^N is required. If no ε∈[0,β] gave a zero on the boundary, homotopy invariance would equate the nonzero degree at ε=0 with the zero degree at ε=β. Hence for every sufficiently large N some ε_N>0 and some exact set of Nash rows have B(q)=β. The growth estimate gives ε_N≤3β(1+c')^(−N). After reversing the rows to physical order, the sum of all hazards strictly after physical date k is at most 3β(1+c')^(−k), from the same estimate on the last k backward increments. The payoffs of the block and its complete caps are those of its initial Nash row against the common child, by backward induction.

Extract coordinatewise limits of the rows at each physical date. The uniform tail bound implies convergence in total variation of each private stopping law on the dates and the Never point, retaining B=β. The limiting profile's prescribed native payoffs and all caps converge, since this coupling bounds the payoff error uniformly for every complete unilateral replacement. In the finite blocks replacing terminal v₀ by zero changes every comparison by o(1) as ε_N→0. Appending literal Never after each resulting block adds no profitable late option: on rival survival both an eventual solo quit and literal Never pay the native own singleton zero. The limiting native profile is therefore exactly Nash. Each player's Never probability is at least 1−β. For the separate prescription of joint absorption replace B by 1−∏_{n,i}(1−|q_{ni}|), with the same coordinate bound and Σ_n|q_n|≤−log(1−β). The same degree argument applies.

This argument uses the nonzero degree of each complete native pair matrix at the origin. It requires no choice of a periodic support, smooth selection of a best response, lower bound on an individual active coordinate or uniform strict margin at the quiet coordinates.

## Two expanding modes give a surface of exact equilibria near AllNever

The following asymmetric pair data admit a two-parameter real-analytic family of exact native terminal Nash payoffs arbitrarily close to zero. Every finite completion of the remaining 32 native rewards has this property. At every nonzero point of the positive parameter quadrant sufficiently close to the origin, all four players make finite attempts and each retains positive probability of literal Never. At a relatively open subfamily of completions the only one-date Nash row at zero continuation is blank, and every exact finite timing-block equilibrium with positive survival at that continuation is blank. The infinite calendars are then essential. The results persist on an open neighborhood of the 24 directed pair coordinates.

Quitting is private and independent on natural dates; the first nonempty quitting set S absorbs at a native vector Z(S). Own singleton, live and perpetual rewards vanish. Write Γᵢⱼ=Zᵢ({j}), Jᵢⱼ=Zᵢ({i,j}) for i≠j with zero diagonals, and K=Γ−J. Take

    Γ = [ 0, −2,  3, −1;    −1, 0, −1, 3;     3, −1, 0, −1;    −1, 3, −1, 0 ],
    K = [ 0,  3,  5/2, −2;  −1/5000, 0, 2, 1/2;  2, −2, 0, 6;    3, 10, −1/2, 0 ].

**Two strict expanding directions.** In construction order, successively prepending dates, use the following 25 supports:

    01, (12 repeated 5 times), (123 repeated 8 times), 013,
    (03 repeated 9 times), 013.

For each support S form Xₛ by putting −Kₛₛ⁻¹Γₛ,· on the rows of S and zero elsewhere, and Aₛ=I+Xₛ. Let Dₛ contain the active rows of Xₛ followed by the outside rows of Γ+KXₛ. Starting with P=I and four initial identity rows in D, append DₛP to D before replacing P by AₛP. All the required inverses exist. The two eigenvalues

    λ₁ ∈ (62855,62856),       λ₂ ∈ (1169838,1169839)

are simple and have eigenvectors y¹,y² with Dy¹,Dy² strictly positive in all 104 coordinates. The remaining two eigenvalues lie in (−1,0) and (0,1). Here and below estimates are verified on rational enclosing intervals, without treating floating point approximations as roots.

The following instructions reproduce the exact certificate. For t symbolic set p(t)=det(tI−P) and W(t)=D adj(tI−P)₍·₀₎, the latter using column zero. At t=−1,0,1,62855,62856,1169838,1169839, the signs of the monic p are respectively +,−,+,+,−,−,+. Each of its four bands therefore contains exactly one simple real root. At each of the two large bands, all 104 entries of W have strictly negative upper rational interval bound. To reproduce this last test, initialize a range [l,h]=[0,0] for every entry, then for each descending monomial coefficient c replace the range by the minimum and maximum of the four products {l·a,l·b,h·a,h·b} plus c, where [a,b] is the indicated integer band. The vectors −adj(λᵢI−P)₍·₀₎ have the required signs. The previous three complementary-pair words and all 24 relabelings of (23,02,013) miss these data: the former have no real expanding mode, and all 16 expanding real roots across the latter fail their strict margins. For this comparison repeat the same matrix products on each word, isolate the real roots above one to width 10⁻³⁰, and on each root interval test the four adjugate columns after multiplying by the stacked active and quiet margins (without the initial identity rows). Each expanding root is simple with upper and lower signs both strict and opposite in one column. No product has eigenvalue one.

**Vanishing quadratic cost.** For a timing word xₙ≥0 of unit total coordinate mass, let yₙ be the sum of xₘ over m strictly after n and write gₙ=Kxₙ+Γyₙ. A finite word is a feasible quadratic limit when maxₙ,ᵢ(−gₙ,ᵢ)₊ tends to zero; its weighted cost is Σₙ,ᵢwᵢxₙ,ᵢgₙ,ᵢ for any w≥0. The limiting quadratic infimum κ(w) is nonnegative since a uniform deficit e gives cost ≥−e maxᵢwᵢ. Either eigenray gives κ(w)=0 simultaneously for all weights. Indeed start one reverse cycle with y=yʲ, put x=Xₛy at each indicated date and replace y by y+x. Active gaps gₛ vanish and outsider gaps are strictly positive. The full cycle ends with λⱼyʲ. In physical time take infinitely many cycles in the opposite order with inputs scaled successively by λⱼ⁻¹,λⱼ⁻²,… . The sums telescope, so y is exactly each strictly later tail, and normalization now gives a summable unit word with all deficits and costs zero. Truncate and renormalize: the omitted mass tends to zero geometrically, perturbing each retained g uniformly by o(1), while its removed cost was zero. This proves the claim even though these ordered tails need never lie in the cone Γy≥0.

**Exact nonlinear calendars.** For a single stage at continuation w write Qᵢ for its expected forced-Quit reward and Pᵢ for its passive immediate absorption contribution if it waits, with Hᵢ its opponents' all-Continue probability. Its wait payoff is Pᵢ+Hᵢwᵢ. With only S hazards present, solve the active equations Pᵢ+Hᵢwᵢ−Qᵢ=0. Near (q,w)=0 their q-derivative on S is Kₛₛ and their w-derivative is the restriction to S. By analytic implicit inversion near zero the signed hazard solution qₛ(w) is analytic. Define Fₛ(w)=P+Hw as a four-vector using these solutions; this is a stage equilibrium payoff wherever its hazards are proper and all quiet comparisons are nonnegative. At w=Γy, the hazard differential is Xₛy, the quiet advantage differential is the outside part of (Γ+KXₛ)y, and the parent differential is Γ(I+Xₛ)y. Thus the composed analytic map Φ=Fₛ₂₅∘…∘Fₛ₁ has derivative A=ΓPΓ⁻¹. The displayed Γ has nonzero determinant by direct evaluation. The differential of every necessary hazard and quiet margin along the whole word is positive on each of the two vectors bⱼ=Γyʲ. It is uniformly positive on their nonnegative mixtures of unit total coefficient.

For completeness there is a local analytic parametrization Θ(s,t)=s b₁+t b₂+O((|s|+|t|)²) with

    Φ(Θ(λ₁⁻¹s, λ₂⁻¹t)) = Θ(s,t).

Write T=diag(λ₁,λ₂), V=[b₁ b₂] and look for Θ(a)=Va+g(a) with g of quadratic order. In the complex eigenbasis norm for A, its operator norm is less than 1169839. In a sufficiently small complex neighborhood the derivative norm of Φ is bounded by D₀=2000000<λ₁². On a small closed two-variable polydisk use bounded analytic corrections with norm supₐ≠₀‖g(a)‖/‖a‖∞², extending continuously to the boundary. The map

    g ↦ [a ↦ Φ(V T⁻¹a+g(T⁻¹a))−Va]

contracts distances by at most D₀/λ₁². The image of zero has a uniform finite norm C by the quadratic Taylor estimate and AV=VT. A ball of radius greater than C/(1−D₀/λ₁²) is invariant upon shrinking the polydisk so all the arguments stay in the derivative neighborhood. This Banach space is complete by uniform convergence of holomorphic functions, and the fixed point is real on real inputs by uniqueness. Since V has rank two, a linear projection to two coordinates followed by the inverse function theorem shows the parametrization is a local analytic embedding. The two variables genuinely vary the payoff.

For sufficiently small s,t≥0 with s+t>0, all 25 hazards on their supports and every quiet advantage meet their strict tests. Their positive first-order bounds are proportional to s+t, uniformly in its division between the two eigenmodes; the error is O((s+t)²). All nonzero hazards are less than one. Realize each physical cycle using the exact stages in reverse construction order, with its child at Θ(T⁻ⁿ⁻¹(s,t)) and parent at Θ(T⁻ⁿ(s,t)), for n=0,1,… . Every conditional parent therefore equals its exact Nash payoff against that child. The sum of the hazards is finite since the nth cycle contributes O((s+t)λ₁⁻ⁿ), and all four owners occur with positive hazard in every cycle. Thus the four actual Never marginals all belong to (0,1). The terminal annotations tend to zero along every phase. Cutting after a finite number of cycles, the difference made by replacing the remaining annotation with zero tends uniformly to zero for every deterministic deadline and Wait. Equivalently iterate the stage inequalities along the partial calendar: past the cutoff any realized nonempty exit requires a rival or prescribed future draw of vanishing probability, and quitting alone pays zero. Infinite Bellman iteration then shows no complete unilateral replacement improves, and every player's literal Never is optimal because Wait is in support at every phase. Hence prescribed payoffs, full caps and Never offers all equal Θ(s,t). No positive-Never clock is interpreted as certainly absorbing.

All finite strict margins and simplicity, the spectral contraction inequality and invertible Γ and Kₛₛ persist on a neighborhood of the 24 inputs. The nonlinear construction uses no assumption on the 32 higher entries beyond finiteness; its local parameter radius can depend on those entries.

**A completion where every finite positive-survival block is blank.** For passive coalitions D not containing i with |D|≥2 choose Zᵢ(D) freely and set

    Zᵢ(D∪{i})−Zᵢ(D) = Σⱼ∈D (Jᵢⱼ−Γᵢⱼ).

This identity already holds on singletons. The one-date Quit-minus-Wait advantage at zero continuation is then exactly (−Kq)ᵢ, by the independent product expectation. Take w=(1,2,1,1). The six sums wᵢKᵢⱼ+wⱼKⱼᵢ are strictly positive, with respective values in lexicographic pair order 3−2/5000, 9/2, 1, 2, 11, 11/2. With two or more active owners qᵀdiag(w)Kq>0, so some owner assigned positive Quit probability strictly prefers Wait. With only one active owner j a quiet i has Kᵢⱼ<0, a strictly profitable join. Thus blank is the unique Nash row. Positive-survival finite block equilibrium reaches every date with positive probability, and its last row is Nash at zero. Removing that blank last row preserves the same zero continuation and optimality. By induction the complete finite block is blank.

This one-stage uniqueness also persists openly. Keep each K near the displayed matrix, preserving those six weighted signs and every column's strictly negative entry. A sufficiently small error e in any higher joining increment from its displayed sum changes Dᵢ=Qᵢ−Pᵢ by at most e Σⱼ<ₗ;ⱼ,ₗ≠ᵢ qⱼqₗ, since the formula remains exact unless at least two rivals quit. The resulting change in Σᵢ wᵢ qᵢDᵢ is bounded by e(Σᵢwᵢ) Σⱼ<ₗqⱼqₗ, dominated by the minimum positive pair coefficient for sufficiently small e. This gives a full-dimensional open set of native games with the claimed finite/infinite separation. Own levels are zero throughout the native statement. A nonblank equilibrium with positive Never does not by itself resolve the signed-original uniform-equilibrium question.
