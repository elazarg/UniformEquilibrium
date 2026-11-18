# A finite triangle and quadrilateral test for continuous singleton paths in four-player quitting games

Let Γ be a real hollow four-by-four matrix. A continuous singleton path is specified by a measurable x:[0,1]→Δ({0,1,2,3}) such that

    g(t)=∫_t^1 Γx(u)du ≥0 for every t,       x_i(t)g_i(t)=0 almost everywhere for every i.

Assume all off-diagonal Γ entries are nonzero and neither Γ nor any of its four three-by-three principal submatrices has a nonzero nonnegative kernel vector. These assumptions can be checked by five small linear feasibility tests, normalizing the candidate kernel vector to sum to one. They hold in particular on the open dense set where all these determinants and off-diagonal entries are nonzero.

**Path theorem.** A nonnegative column j supplies the constant path x=e_j. If every column has a negative entry, a continuous singleton path exists exactly when the following finite test succeeds. For one of the cyclic orders of three or four distinct labels c_0,...,c_(k−1), choose 0<ρ<1 and d_0,...,d_(k−1)>0 with sum 1−ρ. Put

    W_0=(Σ_j d_j Γ_.c_j)/(1−ρ),             W_(j+1)=W_j−d_j Γ_.c_j.

Require W_j≥0 and (W_j)_(c_j)=0 for every phase j. There are at most fourteen cyclic orders before sign pruning: four triples with two orientations each and six orders on four labels up to rotation. An arc p→j must satisfy Γ_jp>0>Γ_pj. Each remaining test is a finite semialgebraic feasibility problem. Repeating the first tour with successive scale factors ρ^n gives actual nonnegative tails, by affine interpolation, and zero active coordinates. Necessity must handle arbitrary measurable paths even if the sign graph has several intersecting cycles.

In fact, at most four real scale factors need testing across all words. Complete the sign graph arbitrarily to a tournament. The number of its transitive triangles equals Σ_v binom(outdeg(v),2), at least two since the four outdegrees sum to six. At most two of its four triangles are cyclic. It has at most one directed Hamiltonian cycle: after fixing one such cycle, each of the other two undirected Hamiltonian cycles traverses its two shared edges in mutually incompatible orientations. Deleting arcs cannot create new cycles.

For a remaining order put M(ρ)_jh=Γ_(c_j,c_h) for h>j, ρΓ_(c_j,c_h) for h<j, and zero on the diagonal. Then the active zero conditions give M(ρ)d=0. In the permutation expansion of its determinant every surviving permutation has between one and k−1 lower entries. Only the increasing cyclic permutation has exactly one: every cycle has at least one descent, and if there is just one the one cycle visits the labels in increasing order up to rotation. Reversing indices gives the corresponding unique permutation with k−1 lower entries. Their products are nonzero. Thus det M(ρ)/ρ is of degree exactly k−2 with nonzero constant. The at most two triangles contribute at most one real candidate each and the sole quadrilateral at most two. For each surviving ρ in (0,1) the positive mass constraints and all four boundary rows, including the outsider on a triangle, are just linear feasibility. The constant nonnegative-column alternative can be checked first.

**Game consequences.** In the independent four-player quitting game let r_i(A) be finite original rewards on the first nonempty quitting coalition A, s_i=r_i({i}), Z_i(A)=r_i(A)−s_i, and Γ_ij=Z_i({j}). Live play, including perpetual continuation, pays zero. A unilateral replacement may use any complete independent behavioral stopping law. Write e for the maximum original terminal payoff improvement under such replacements, and C for the profile's actual probability of a joint first exit by at least two players.

When each Γ column has a negative entry, the finite test's success produces actual calendars with at most one possible quitter at every date, terminal regret tending to zero, and exactly the original target s+g(0) for every calendar. This gives an original fixed-target uniform equilibrium for arbitrary signed own levels and arbitrary higher rewards. If instead a nonnegative column j has s_j≥0, repeated small solo hazard of j also supplies an original fixed target. A nonnegative column with s_j<0 gives a path but its own player may gain by Never; that alone is insufficient to justify the latter solo construction.

For a stronger conclusion, assume at least one positive own level. For each player i require one of two alternatives. It may have original upper punishment level μ_i≥s_i, meaning the best-response supremum against every fixed opponent schedule is at least its own level. Alternatively, require J_ij=Z_i({i,j})≥0 whenever Γ_ij<0. The latter raw condition leaves all higher rewards free. Different players may use different alternatives. With every Γ column containing a negative entry, the following conditions are equivalent: (i) the finite path test succeeds, (ii) inf e=0 among solo calendars, and (iii) inf(e+C)=0 among all behavioral profiles. With all own levels nonnegative, the same equivalence also covers a nonnegative column, counting that column as a successful path test. If the test fails, some ε,c>0 depending on the table ensure that every behavioral profile with e≤ε has one date with unconditional probability at least c²/4 of a simultaneous first exit. If both forms of row protection are dropped but some own level is positive, failure of the test still forces an unconditional first-exit atom, of any coalition size, bounded away from zero in every sufficiently accurate terminal equilibrium. On these branches existence of such equilibria still requires a producer.

## Necessity of a finite geometric cycle

**A compact flow on trajectories.** In the remaining proof assume every column has a negative entry and a path is given. Let z(t)=∫_t^1 x, let θ=−log(1−t), and put p(θ)=z(t)/(1−t). Then p lies in the simplex, Γp≥0 and p'=p−x in θ-time, with x_i(Γp)_i=0 almost everywhere. Conversely these constraints specify the same local dynamics in θ-time. Translates of a solution are uniformly Lipschitz and bounded. Taking times tending to infinity gives a nonempty family of entire solutions on the real line. Equivalently take all entire solutions; this is a compact metric space in locally uniform convergence. Indeed on every finite interval the integrals of x are recovered from p via ∫x=∫p−[p] and converge on subintervals. The limiting x=p−p' is simplex-valued almost everywhere because its integral over every interval has nonnegative entries and coordinate sum equal to the interval length. Where (Γp)_i>0, row i is absent on smaller compact intervals for all sufficiently close approximants, so complementarity passes. Shifts define a continuous invertible flow on this space. A minimal nonempty compact invariant subset exists by compactness and nested intersections. Any trajectory in it is recurrent: its positive omega-limit is nonempty compact and invariant under all shifts, so contains the original trajectory. Thus arbitrarily large translates of that trajectory approximate it on every fixed compact window. This argument concerns a flow on entire trajectories; uniqueness of state evolution at a multiple zero is unnecessary.

**Local geometry.** Pass to the sphere Σ which is the boundary of the positive tetrahedron of unit-sum payoff vectors. Put w=Γp/Σ_i(Γp)_i. The denominator is positive by the full cone-kernel hypothesis. Every w has a zero coordinate by continuity and complementarity. On a finite θ interval replace p by z=e^(−θ)p (and time by t with dt=e^(−θ)dθ); locally z has derivative −x. The unnormalized vector W=Γz therefore has derivative −Γx in physical mass time, and w is its direction. A color i moves only where W_i=0. Each finite piece with sole color j traces a straight segment in the j face of Σ. It is nonconstant: constancy would force Γ_.j collinear with a nonzero W≥0. A positive proportionality contradicts the column's negative coordinate, and a negative one would give a nonzero nonnegative kernel vector by adding a multiple of e_j to z.

There are locally finitely many such pure segments. A color with W_i>0 is absent nearby. With two available colors i,j, W_i is monotone with slope proportional to the mass of j, so its zero set is an interval in which j has zero mass, and outside this interval i has zero mass. At a point with three zero rows S, the remaining positive row is absent on a neighborhood. The three W rows on S cannot vanish at two times in that neighborhood: integrating gives a forbidden nonnegative kernel vector on S. Away from that exceptional time the local two-color argument applies. If infinitely many changes accumulate from either side, the three-color transitions in that side would form an infinite directed walk. On every transition p→j the predecessor segment ends at W_j=0 and began with W_j≥0, hence Γ_jp>0; the new segment starts at W_p=0 and ends nonnegative, hence Γ_pj<0. Reversals are impossible. A directed graph with one possible orientation per pair on three labels permits an infinite walk only if it is a directed triangle. On such a triangle every row of the adjugate of Γ_SS has strictly positive entries: its diagonal cofactors are minus the product of the two opposite signs, and its off-diagonal cofactors are products of two weights with the same sign. The matrix is nonsingular since a zero determinant would supply a strictly positive kernel column. Its inverse therefore has one strict sign throughout. But the two sides of a three-zero time furnish positive-total, nonnegative integrated controls u,v with Γ_SS u≥0 and Γ_SS v≤0 respectively. One of these is impossible with a one-sign inverse. This precludes every interior accumulation, and finitely many pure segments suffice on any compact θ interval of an entire trajectory. Between changes, the segment lies inside its open face: a different row has nonzero constant slope in W and cannot vanish between its nonnegative endpoints. Two adjacent distinct faces meet through their open shared edge or through one of its endpoints. Every open-edge hit is thus a transverse crossing, always in its unique sign direction.

**Recurrent crossings.** Suppose the recurrent entire trajectory has no repeated normalized state w. Then it is a continuous injective curve on Σ. It can encounter each of the four vertices only once. If it has no open-edge crossing it must eventually remain in one face, say i. Then p'=p−e_i there, and boundedness on the infinite future implies p=e_i, which would give a nonnegative column. Thus it has an open-edge crossing. Use that edge, choose a small closed subarc J with the crossing interior and both ends avoided by the curve. Such ends exist because the crossings are locally finite in time and therefore countable. Orient J so the crossing enters its designated plus side. Every crossing of J has that same direction.

Here is the elementary Jordan order argument. For consecutive crossings A,B on J, assume after reversing the segment coordinate if needed that A<B. The trajectory piece from A to B, closed by the chord BA in J, is a Jordan curve on the sphere since the trajectory is injective and meets no other point of J between these two times. One complement component N abuts the plus side of the open chord, and immediately after B the trajectory is in N. This is seen in a small disk around B: the ending trajectory arc approaches B from the minus side, the chord leaves B toward A, and the outgoing arc is on the plus side. The segment of J past B is in N, and the segment before A is in the other component, by the corresponding local disk at A. The future trajectory cannot cross the old trajectory segment nor revisit its endpoints by injectivity, and cannot leave N across the chord since every crossing there goes into N. Thus its next hit of J, if any, must be strictly beyond B. The analogous order holds if B<A. Iteration orders all hits strictly monotonically. Recurrence gives infinitely many later hits approaching the original interior crossing A: before and after it the curve belongs to the two open faces, and every sufficiently close shifted path must pass through J by continuity. This contradicts the order after its first subsequent distinct hit. It follows that two different times have identical w.

**Closing the path and eliminating vertex contacts from the count.** On the finite interval between two equal normalized states there are finitely many pure segments. They are locally injective, including at junctions since the two adjacent segments have interiors in different open faces. On that compact interval injectivity on short enough time windows follows by a finite cover. Choose a pair with equal w minimizing the positive time difference, which exists since the set of such pairs stays away from the diagonal. Its image is a simple closed piecewise linear curve traversed once. At the initial and terminal endpoints W'=ρW, ρ>0. If d is the nonzero nonnegative vector of owner masses between the endpoints, then Γd=(1−ρ)W. Since W=Γz with z≥0, having ρ≥1 would give Γ(d+(ρ−1)z)=0, contradicting the full cone-kernel assumption. Hence ρ<1. Repeating the owner masses with this geometric factor reconstructs W exactly up to normalization of total mass and gives the claimed admissible clock. If the cutting point lies inside a run, the two fragments of its owner merge cyclically; equivalently shift the starting point to any junction, where the geometric continuation has the same ratio.

In a simple closed curve each tetrahedron vertex is touched at most once. At a vertex switch p→j the incoming and outgoing open face sectors are p and j. Both are incident on the shared edge E_pj in a small punctured neighborhood of this vertex (there are only three face sectors). Choose pairwise disjoint small disks about the curve's vertex contacts meeting only their incident segments. Replace the two arcs inside each disk by a simple arc in those same two sectors, crossing the interior of E_pj once and avoiding the vertex and the other edges. This perturbation is topological only. It preserves the successive face labels, the orientation of each switch, and the Jordan property. The perturbed curve avoids every vertex and crosses all its edges in the directed sign orientation; an open edge cannot be crossed twice because successive transverse crossings of a Jordan curve by an oriented interval alternate sides. Thus its cyclic owner word is a directed closed trail with no repeated undirected edge. If it repeated a vertex label it would decompose into at least two edge-disjoint directed simple cycles, each of length at least three. On four vertices this is impossible: two triangles share an edge, and any other two such cycles require more than six edges. The word is a simple triangle or a simple quadrilateral. The topological perturbation was used only to count the switches of the original periodic path; the original geometric masses supply the finite test.

## Solo discretization and unrestricted deviations


Let M≥1 bound all |Z_i(S)|. On each interval [a,b] of the infinite geometric mesh with 1-b=(1-h)(1-a), for 0<h≤1/4, let L_j=∫_a^b x_j. Prescribe one successive pure-owner phase for each j with L_j>0, in an arbitrary fixed label order, of that unconditional exit mass. A phase starting at mass time t with length L has physical hazard q=L/(1-t). It lies in (0,h] because L≤b-t and (b-t)/(1-t)≤(b-a)/(1-a)=h. Global absorption is certain. Denote by g^h(t) the tails of its singleton columns colored on these subintervals. At every mesh boundary g^h=g, so the initial native payoff is exactly g(0). Inside a mesh interval each coordinate differs by at most 2M(b-a) from the continuous parent tail. Its actual prescribed native continuation V_i=g_i^h(t)/(1-t) at any physical phase is therefore at least -2Mh/(1-h). If i receives any mass in that mesh interval, some point of the interval has g_i=0 by complementarity and positive assigned mass. Lipschitz continuity of g then shows |V_i|≤3Mh/(1-h) throughout that interval, including at each such owner's physical date. At every date the native forced quit offer is bounded above by Mh (zero on i's own date). A player who continues at another owner's date does exactly what the profile prescribes. At i's own date, skipping instead of mixing has conditional gain V_i q/(1-q), by the exact renewal V_i=(1-q)V_i(next). Hence a prescribed deviation to a fixed quitting deadline pays at most 4Mh at that terminal decision and earns at most 6Mh q per preceding date owned by i. The same estimates for the limit Never will follow from assured opponent absorption.

Here is the required uniform bound against an owner who suppresses all its own hazards. The compact set K={p∈Δ(I):Γp≥0} contains normalized remaining masses of the parent path at every mesh boundary. Since no basis vector belongs to K, choose η>0 such that p_i≤1−η for every p∈K and i. Group consecutive mesh intervals into blocks of J=ceil(log(2/η)/[-log(1-h)]) intervals, so in each block the relative total survival α=(1-h)^J lies in ((1-h)η/2,η/2]. From its starting boundary at least η of the conditional prescribed future first quits belong to opponents of i, because the discretization exactly preserves the remaining owner masses at that boundary. At most α of all first quits occur after the block, leaving at least η/2 probability of an opponent first quit within it. The probability of an opponent exit within the block when i is deleted is at least that quantity. The products of opponent survival across blocks thus decrease at least geometrically as (1−η/2)^k. In any one block the sum of all hazards is at most the sum of their negative log survivals, exactly -log α≤log(4/η). Therefore

    Σ_dates Pr(no opponent has quit before date) q_i(date) ≤ (2/η)log(4/η).

Finite deadline gain relative to the profile is bounded above by 4Mh+6Mh(2/η)log(4/η) by telescoping the above one-date gains against actual opponent reach. Deleted-owner survival tends to zero, so the Never payoff is a limit of finite deadline payoffs by bounded convergence. Mixtures of deadlines exhaust complete unilateral stopping laws. Every original deviation absorbs almost surely, restoring each row offset exactly. Each block contains at most |I|J dates, so even the expected physical absorption time is uniformly finite over all deviations for this chosen h. The usual comparison of terminal with finite-average payoffs then gives the fixed target s+g(0) for every sufficiently long horizon after choosing h for the tolerance.

If Γ_.j≥0 and s_j≥0, one may instead schedule only j at a constant positive hazard h tending to zero. Its original prescribed payoff is s_j and even its Never deviation pays zero. For an outsider i the prescribed payoff is s_i+Γ_ij≥s_i; at any reached date its forced quit pays s_i+hJ_ij with J_ij=Z_i({i,j}). Its waiting payoff remains the prescribed value, so stopping offers at most O(h) gain against repeated j play, uniformly over deadlines. Its Never deviation faces absorption by j. For finite horizons the prescribed process and every outsider deviation have geometric absorption tails, and j itself gains at most the vanishing long-horizon difference between its prescribed average and s_j. This proves the nonnegative-column game assertion including the case s_j=0.

## Necessity of the path under row protection

Suppose there are profiles with regret tending to zero and
total probability τ of a tied first exit tending to zero. Fix such a
profile for the estimates, with regret at most e. Truncating the private
law of an owner with positive s_i at a large finite date and passing to
the limit gives gain s_iν, where ν is joint Never. Bounded convergence
proves ν≤e/s_i. Write S_k for joint survival to the start of k, p_ik for
the owner's conditional hazard, H_ik for its opponents' conditional
survival through k, and W_ik for the original conditional prescribed
payoff minus s_i. Ignore unreached dates. In every row protected by μ_i≥s_i, pasting a best response to
the conditional opponents onto the original law at k gives

    S_k W_ik≥−e.

Approximate responses suffice for this use of a supremum. Write Q_ik
for the immediate forced native Quit offer. Its absolute value is at
most M(1−H_ik) with a fixed reward bound M since own solo pays native
zero. Let U_ik be the best-response supremum on this tail, minus s_i.
Let P_ik be the native passive contribution with zero at empty exit.
Then U_ik≥Q_ik and U_ik≥P_ik+H_ik U_i,k+1, whereas W_ik is the
prescribed mixture of Q_ik and P_ik+H_ik W_i,k+1. Subtracting gives

    S_k (U_ik−W_ik) ≥ S_k p_ik (U_ik−Q_ik)
                        + S_(k+1)(U_i,k+1−W_i,k+1).

All terms are nonnegative. Summation to any cutoff and U_ik≥W_ik give
Σ_k S_k p_ik (W_ik−Q_ik)_+ ≤ e by the original regret bound. The
probability that i participates in a tied first exit is exactly
Σ_k S_k p_ik(1−H_ik), at most τ. Thus

    Σ_k S_k p_ik (W_ik)_+ ≤ e+Mτ.                         (1)

Give each date an interval of length its unconditional first-exit
probability. Assign each first exit to one quitting owner (least index
on ties), with unconditional masses ℓ_ik. Spread these assigned
proportions uniformly on the date's interval to obtain x_i; fill the
remaining interval of length ν arbitrarily in the simplex. The
cumulative four coordinates are 1-Lipschitz. Put g(t)=∫_t^1 Γx(s)ds,
and let t_k be a date's left endpoint. For a fixed game constant K,

    |g_i(t_k)−S_k W_ik| ≤ K(τ+ν).

Singleton contributions agree exactly; ties and Never have the
indicated total mass. For each row protected by its punishment level the endpoint inequality and affine interpolation
therefore bound g_i below by −e−K(τ+ν), with a further O(ν) on the
filled Never interval. This works even on macroscopic single-owner
intervals; a vanishing time mesh is unnecessary.

By (1), ℓ_ik≤S_k p_ik and Σ_k ℓ_ik≤1, the left-endpoint approximation to
the integral of x_i(g_i)_+ is at most e+Mτ+K(τ+ν). On a date's interior
the variation of g_i from its endpoint is at most MΣ_(j≠i)ℓ_jk,
since Γ_ii=0. Also Σ_(j≠i)ℓ_jk≤S_k(1−H_ik). Hence the aggregate
interpolation error is at most

    MΣ_k ℓ_ik Σ_(j≠i)ℓ_jk ≤ MΣ_k S_k² p_ik(1−H_ik) ≤ Mτ.

The filled interval adds O(ν). By compactness the cumulative functions
converge uniformly along a subsequence to integrals of a measurable
simplex-valued x. Then g converges uniformly and the assigned measures
x_i(t)dt converge weakly. Passing to the limit in the continuous tests (g_i)_+ gives ∫x_i(g_i)_+=0 for every i. Write G_i for the limiting continuous tails in the next argument.

For a row protected only by its raw joining conditions, fix an opponent j with Γ_ij<0. At any point t in the support of the limiting j measure one has G_i(t)≥0. To see this, retain every color on dates with unconditional exit mass below η, and on dates of mass at least η retain only the assigned mass of a largest-hazard owner. There its hazard is ≥η/4 by the union bound. For each other color h, its assigned mass is at most S p_h ≤(4/η)S p_h p_l, where l is that largest owner. Each pair intersection is part of a tied first quit. Thus the total discarded mass across the large dates is at most 12τ/η. Take η=√τ+1/n along the sequence. On every neighborhood of a point in the limiting j support there are retained j dates for large n. By diagonal selection take points on such dates tending to t. If their date lengths tend to zero, immediate Quit gives G_i(t)≥0 since S|Q_i| is at most three times M times the date length. Otherwise take a subsequence with a positive limiting date interval [a,b] containing t. The large-date owner is j. Every other hazard tends to zero by S p_j p_h≤τ, since S and p_j stay bounded below. Its assigned proportions consequently converge to pure j, its slope in the limit is −Γ_ij, and its native forced offer for i multiplied by S tends to J_ij(b−a). Immediate Quit thus gives G_i(a)≥J_ij(b−a)≥0 and G_i(t)≥G_i(a) since Γ_ij<0. This proves the assertion including interval endpoints. If G_i were negative somewhere, its negative component would contain no support of any j with Γ_ij<0. There the derivative −ΣΓ_ij x_j is nonpositive almost everywhere. The component cannot end at zero on its right, although continuity and G_i(1)=0 require just that. Hence G_i≥0 also in all raw-protected rows. The integral active bounds now give ∫x_i G_i=0, completing the path.

Consequently, if the finite path test fails, some ε,c>0 give total tie probability at least c on every profile with regret at most ε. In fact at a single date the
unconditional tied first-exit probability is at least τ²/4. For any
finite list of independent hazards p_i, write H=Π(1−p_i), r=1−H,
and let d be the probability of at least two quits. If H>0, the
probability of exactly one quit is HΣ_i p_i/(1−p_i)≥Hr, since
Σ_i p_i≥r. Thus d≤r², also immediate if H=0. For a calendar put
a=sup_k S_k d_k and h_k=S_k r_k. Ignoring dates with S_k=0, one has

    S_k d_k ≤ √a h_k/√S_k
            ≤ 2√a (√S_k−√S_(k+1)).

Summation gives τ≤2√a. A positive supremum is attained because the
unconditional probabilities form a summable sequence. In Fin4 at
least one of the eleven nonsingleton coalitions therefore has
unconditional probability ≥τ²/44 at one specific date.

## Diffuse first exits without a security assumption

Retain at least one positive own level. Suppose e tends to zero and the largest unconditional probability m of any first exit at one date also tends to zero. Then ν tends to zero as above and τ≤2√m by the simultaneous-atom estimate. In the necessity proof security was used to obtain S_k W_ik≥−e. Here pasting immediate Quit gives S_k W_ik≥S_k Q_ik−e instead, and |S_k Q_ik|≤M Σ_(j≠i)S_k p_jk≤3Mm. Indeed each event of surviving to a given date and its owner quitting then is included in the event of an exit on that date. The interpolation error within one physical date is also at most M m. All other compactness and complementary-support estimates apply unchanged. Thus one again obtains a nonnegative singleton path, without any condition on the upper punishment levels. Failure of the fourteen tests in the absence of a nonnegative column consequently implies a positive table-dependent lower bound on e+m for every profile. Conversely, when the signed solo decoder applies, the mesh construction uses only hazards at most h so its largest unconditional first-exit mass tends to zero. This identifies the diffuse-exit branch even when the stronger collision conclusion lacks its security hypothesis.

## Two exact matrices

For a strictly oriented four-cycle take the circulant matrix with first row (0,−3,4,4), obtained by rotating rows and columns together. Its determinant is 975 and each principal triple has determinant 100. The two opposite pairs are positive in both directions and give no arcs. The mixed directed graph is exactly 0→1→2→3→0. Take d=(1/2,1/4,1/8,1/16) and ρ=1/16. Then W_0=(0,2,3,0), with later boundary vectors given by successive rotations and factors of 1/2. The quadrilateral passes while no triangle is eligible. The solo decoder gives the same original target (s_0,s_1+2,s_2+3,s_3) for all sufficiently fine calendars, independently of the higher rewards.

For the opposite outcome take

    Γ = [0,−1,−1,5; −5,0,2,−1; −2,4,0,−5; 3,−4,2,0].

The full determinant is 60 and the four principal triple determinants in lexicographic order are 24,103,−5,32. The only mixed pair is 23, giving arc 2→3. There is no directed cycle and no nonnegative column. For a concrete secure completion with s_i=1, give i the sum of the Γ_ij over quitters j if it waits and the negative of that sum if it quits. A constant own hazard 1/2 guarantees native zero against every opponent schedule and ensures absorption. The finite test thus forces an actual simultaneous first exit of uniformly positive probability at a single date in every sufficiently accurate original terminal equilibrium. The earlier proportional-additive existence theorem applies on this completion; the collision assertion itself uses only the row protection and the singleton matrix. In fact here every negative Γ_ij has a strictly positive J_ij, so every finite higher-coalition completion preserving these singleton and participant pair data has the atom conclusion; those unrestricted completions need not satisfy the punishment floor.

The row protection matters for the conclusion about simultaneous quitting. For example take the symmetric diamond with rows

    (0,−1,2,2),  (2,0,−1,−1),  (−1,17/8,0,−9/32),  (−1,17/8,−9/32,0)

in order X,Y,U,V. Its full determinant is 2079/512 and its triple determinants in deletion order are 153/128,9/8,15/2,15/2. The only oriented cycles are XYU and XYV. In either candidate the omitted twin's tail at the active twin's phase equals that active owner's zero tail minus 9/32 times its strictly positive total remaining mass. Therefore neither continuous path test passes. Set s_i=1 and choose joining rewards J_ij=k_iΓ_ij with k=(1/2,1/2,9/10,9/10); all remaining higher rewards are arbitrary. Nevertheless a solo exact equilibrium uses the six successive labels X,Y,U,X,Y,V repeatedly, each at hazard 1/2. Twice the actual native values at those dates respectively are

    (0,2,1/16,0), (0,0,17/8,2), (2,0,0,−1/4),
    (0,2,0,1/16), (0,0,2,17/8), (2,0,−1/4,0).

The displayed rows satisfy the one-date continuation equalities. Each active coordinate is zero before and after its date, and the quiet joining premium does not exceed the corresponding displayed coordinate. Half the vector is the actual value and the physical forced Quit offer is J_ij/2. Opponents absorb geometrically under any replacement, so endpoint comparison gives exact terminal Nash. Every row has a negative singleton rival with a strictly negative joining premium, and opponents prescribing that rival to quit for sure at the first date keep the very best payoff strictly below the own level. This table fails both protection alternatives in every row. Its affirmative solo equilibrium is consistent with the unconditional diffuse obstruction, since each nonblank date is a genuine atom.

## Relation to the existing path theory

Continuous equilibria in absorption time and projective complementarity appear in Ashkenazi-Golan, Krasikov, Rainer and Solan (2024), Section 5. Projective Q-bar is a known sufficient condition, and the paper distinguishes it from necessity. The checked declaration `continuousEquilibrium_of_projectiveQBar` in `Literature/AshkenaziGolanKrasikovRainerAndSolan2024.lean` constructs a continuous equilibrium under that hypothesis. `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` in `UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean` gives the checked original uniform-payoff conclusion for the ambient projective-Q-bar class. Earlier supplied cyclic certificates and continuous-path decoders establish sufficient implications. Here the finite word list is also necessary throughout the stated four-player matrix domain, including graphs with several cycles; the literal solo construction and the security converse identify the implications for actual first exits. The terminal-to-uniform characterization is `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`. The finite decision, necessity proof and quantitative bounds in this packet are ordinary mathematics.
