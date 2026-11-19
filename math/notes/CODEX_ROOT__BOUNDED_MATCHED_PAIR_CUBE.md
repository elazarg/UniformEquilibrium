# Private equilibria on the bounded matched-pair cube

In the normalized four-player matched-pair family, a single equality between the two passive rewards in either matched pair suffices throughout the cube [−1,2/3]⁴. Four six-date boxes cover regions where both pairs have different passive rewards. The entire lower cube [−1,−2/3]⁴, the entire cube [−1/2,2/3]⁴ and all sixteen vertices also have exact private terminal equilibria and fixed uniform-equilibrium payoffs. Intermediate points with both pairs split remain open.

Let the players be i modulo four, let m(i)=i+2, and let O(i)={i−1,i+1}. For arbitrary own singleton level s_i and positive row scale ℓ_i put Z_i(S)=(r_i(S)−s_i)/ℓ_i for nonempty coalitions S. The mate singleton pays 3, either opposing singleton pays −1, and own matched-pair participation pays 8/3. In the crossed pair {j,j−1} require Z_(j−1)≤−1+d, and in {j,j+1} require Z_(j+1)≤−1−d. The bounded-cube results use d=1/10. The one-tied-pair argument also covers unbounded sets for other d. Set T_i=Z_i(O(i)) and require Z_i({i}∪O(i))≤T_i.

All 24 nonsingleton rewards outside these conditions may be arbitrary finite numbers. Every equilibrium constructed below has a positive proper rival hazard during each cycle for each player. Therefore absorption has a geometric tail uniformly over a single player's replacement policy, including Never. The Bellman comparisons iterate to exact terminal Nash against every such policy. Replacing a normalized terminal value V_i by s_i+ℓ_i V_i preserves all comparisons because stopping occurs almost surely under every replacement. Truncating at N dates and paying the terminal coalition reward for the remaining fraction of the horizon introduces an error bounded uniformly over replacements by a reward bound times the expected truncated waiting time divided by N. This yields one fixed original uniform-equilibrium payoff.

## One tied matched pair

Write A={0,2} and B={1,3}. Suppose T_0=T_2=T_A with the other two rewards independent. If max(T_1,T_3)≤2/3 it suffices that 0≤d≤1/10 and d|T_1−T_3|≤64/27. This allows d=1/10 for every spread up to 640/27 without any lower bound on either reward. Thus it covers every T_A throughout the bounded cube. If max(T_1,T_3)>2/3 the earlier exterior theorem applies for sufficiently small positive d depending on the rewards. Taken together, these statements cover the entire real three-dimensional one-tied-pair locus for sufficiently small d at each fixed game. The same holds with the groups interchanged. [Earlier matched-pair plane and exterior theorem](../exports/INDEPENDENT_PASSIVE_REWARDS_ON_MATCHED_PAIRS.md)

Write c=1/3, M=8/3, r=c/M=1/8, k=(1+c)/(1+M)=4/11, N(C)=1+c−(1+M)C, P(C)=(1−√C)², and τ=N(r/k)/P(r/k)−1. Numerically τ≈−0.57395. For a matched pair scheduled with hazards x,y write C=(1−x)(1−y), D=xy. For fixed C the exact possible D interval is [0,P(C)]. At every date when its group is scheduled a mixing player's prescribed value is M times the mate hazard.

### T_A ≥ τ

Choose C_A=k, D_A=0, C_B=r/k, D_B=N(C_B)/(1+T_A). These are feasible by the definition of τ and N(r/k)>0. The A members alternate solo hazards 1−k. The B members alternate the larger and smaller hazards with survival C_B and product D_B. Take the larger B hazard at player 1 following solo 0, and at player 3 following solo 2. The own-group comparisons hold with equality, including the idle mate of the A soloist. Indeed, on a group's row with opposite survival C_h, when roles swap, the needed opposite-date head is

    −c u/(1−u)−C_h M t = c−M C_h,

where u and t are the current and next mate hazards and (1−t)(1−u)C_h=r. The actual head is −(1−C_h)+(1+T_i)D_h; equality is exactly (1+T_i)D_h=N(C_h). This holds for A by construction and for B since D_A=N(k)=0.

At an opposite-group date the idle guard is C_h M times the next mate rate, minus at most d(w−z) where w,z are the successor and predecessor rates. At a B date, the A player whose next mate rate is zero has w≤z by the chosen ordering. Its mate has C_B M(1−k)>d. At an A date only the B player with larger next mate rate can have w>z, and its continuation term is at least kM(1−√(r/k))>d. All comparisons follow. In this upper case no member of B sees the opposite pair stop together, so T_1,T_3 and both associated triple-join payoffs may be arbitrary.

### T_A ≤ τ

In this case assume max(T_1,T_3)≤2/3. Put T̄=(T_1+T_3)/2 and Δ=|T_1−T_3|. Initially both A players use the same rate x at each of their active dates. Fix x∈(0,3/4). At B dates give the mate of each B player i the rate z_i determined by

    z_i [c/(1−z_i)+M(1−x)²] = 2x−(2+T_i)x².

The right side is positive because T_i≤2/3. The left increases continuously from zero to infinity, giving unique continuous proper rates; write v,w for these two B hazards and C_B=(1−v)(1−w). All B active comparisons are now equalities. Let x_* be the first x with (1−x)² C_B=r. It exists strictly between 0 and 3/4 by continuity, since the product starts at one and is at most (1−x)². Write C_*=(1−x_*)². Adding the two B equations at resonance gives

    (1+T̄)x_*²=N(C_*).

Indeed, the mean of c z_i/(1−z_i)+M C_* z_i equals M C_*(1−C_B), using c=M C_* C_B. We have C_*≥1/4. Indeed, 3N(C_*)≤5P(C_*) gives (1−8√C_*)(1−2√C_*)≥0. Since C_*>r, this forces √C_*≥1/2 and x_*≤1/2.

The remaining active comparison, common in A after a positive factor is removed, is

    F(x)=cx/(1−x)+M C_B x−(1−C_B)+(1+T_A)vw.

It is positive near zero: z_i=2x/3+O(x²), so F(x)=(3−4/3)x+O(x²). If F(x_*)≤0 there is a root in (0,x_*]. Its quiet comparisons hold. B sees equal A hazards, and A needs C_B M x≥d|v−w|. Subtracting the B equations yields |v−w|/C_B=Δ x²/(c+M(1−x)² C_B)≤Δ x²/(2c) up to the first crossing, and dΔx≤(64/27)/2<2cM.

Now consider F(x_*)≥0. If 1+T̄≠0, move C=C_A continuously from C_* to k in whichever direction is required, and set

    C_B=r/C,  D_A=N(C)/(1+T̄),  δ=ΔD_A/(2MC).

Along this segment C≥1/4 and N/P decreases with C because its derivative has the sign of k−√C. The ratio D_A/P is therefore monotone with endpoint values 1 and 0, regardless of the sign of 1+T̄. Take x≥y as the A hazards with survival C and product D_A, swapping their assignments on successive A visits. Give each B player i the same mate hazard z_i at both its visits, requiring survival C_B and z_1−z_3=−(T_1−T_3)D_A/(2MC). Such hazards exist continuously. Indeed their required relative difference δ/(1−C_B) is a nonnegative constant times |C−k|/(C−r), which decreases to zero as C moves from C_* to k from either side. At the first crossing it is at most one. The allowed absolute difference at fixed survival C_B is exactly [0,1−C_B]. If T̄=−1 the first crossing has C_*=k. Instead hold C=k fixed and move D_A from P(k) to zero, keeping the same C_B and δ formulas. The difference decreases to zero with fixed survival. In both cases the two B contacts follow by adding and subtracting them. Their sum uses (1+T̄)D_A=N(C), and their difference uses c/C_B+MC=2MC.

The two A contacts reduce, by resonance and role swapping as in the upper case, to the one scalar equality

    (1+T_A)vw−N(C_B)=0.

The left side at C_* equals F(x_*)≥0. At the endpoint C=k and D_A=0, so the B rates are equal; the left side becomes (1+T_A)P(r/k)−N(r/k)≤0. Hence a root exists.

For the quiet B comparison let z be the smaller B hazard. Its active equation for the corresponding observer i gives z[c/(1−z)+MC]=1−C−(1+T_i)D_A. Since 1−z≥C_B and c/C_B=MC, the left side is at most 2MCz. The right side is at least (4/9)(1−C), because 1+T_i≤5/3 and D_A/(1−C)≤P(C)/(1−C)=(1−√C)/(1+√C)≤1/3. Hence CMz≥(2/9)(1−C)≥d|x−y|. In particular both B hazards are positive. For the quiet A comparison C_B M y≥dδ follows from δ=Δxy/(2MC), C C_B=r, and dΔx≤2M²r since x≤1−C≤3/4. All hazards are below one and every player faces a positive recurring rival.

## Two-date threshold

If T_i∈[−1,−2/3] independently, every player can mix on its own group's recurring date under the alternating two-date calendar. Conversely, if T_i∈[−2/3,2/3] independently, a nonzero proper solution of the scheduled comparisons requires all four T_i=−2/3, and its hazards all equal 1/2. Here proper means every hazard is less than one. Under equality at every predecessor join cap the sure case also fails, since the sure player's mate must wait and its predecessor can strictly gain by joining. With only upper bounds on the crossed rewards the sure case is not excluded.

For two properly scheduled groups let s=q_m be the mate's hazard and let w,z be the opposite hazards. A full-support contact requires

    K(s,w,z;T_i)=w+z−(2+T_i)wz−s[c/(1−s)+M(1−w)(1−z)]=0.

For −1≤T_i≤−2/3 and 1/2≤w,z≤3/4, the upper sign K(3/4,w,z;T_i)≤0 follows because c(3/4)/(1/4)=1 and the passive loss is at most one. For s=1/2, K is bounded below by its expression at T=−2/3; that bilinear polynomial has corner values 0,1/2,1/2,1/3 on [1/2,1]². Strict decrease in s gives four continuous responses in [1/2,3/4], one for each player's mate. Brouwer gives a joint solution. Waiting on the opposite date adds at least M(1/4)²/2=1/12 to the passive head, whereas deviating adds at most d|w−z|≤1/40.

For the reverse implication, both groups must have a mixer. A lone mixer leaves its opposite players with a strictly negative wait value; if two mates alone mix the payoff from waiting for the mate is 3, strictly greater than quitting. A sole mixer in each group has zero active value and negative expected next value. With a sole mixer of rate p facing two mixers, both opposing rates are the same v determined by v[c/(1−v)+M(1−p)]=p. This gives v<3/4, and the sole mixer's own contact requires T_i=2(1/v−1)>2/3. Thus all four must mix.

At a full root choose the maximal hazard s. The corresponding K is bilinear over [0,s]² in w,z. It is negative at (0,0); at either one-positive corner K/s≤1−2√(cM)<0. At (s,s), for T≥−2/3,

    K/s ≤ −(3−2s)(2s−1)²/[3(1−s)].

Consequently w=z=s=1/2 and T_i=−2/3. Applying the same argument to the new maximal opposing hazards forces every rate to equal 1/2, which in turn forces all four rewards to equal −2/3.

## Four and six dates with independent split rewards

The entire cube [−1/2,2/3]⁴ admits equilibria. When both members of one matched pair have T_i in [−1/2,1/3], use the existing two-observer result, which leaves the other pair unrestricted. Elsewhere the checker chooses one of the following two calendars, allowing cyclic player relabeling and time translation. The four-date supports are {0,2}, {1,3}, {2}, {3}. The six-date supports are {0}, {1}, {0,2}, {1,3}, {0,2}, {3}. Each listed hazard is strictly between zero and one, and every idle comparison on a computationally accepted cell is strictly positive. [Earlier two-observer region](../exports/INDEPENDENT_PASSIVE_REWARDS_ON_MATCHED_PAIRS.md)

Split each parameter axis initially at 0 and 1/3. Identify a rational cell with the lexicographically least cyclic rotation of its four intervals. For each representative the checker first tests the two-observer result, then the calendars in all cyclic player orientations. It bisects each remaining cell at the midpoint of a longest side, testing both children after reducing them to cyclic representatives. The game and the directed crossed inequalities are invariant under these rotations, so acceptance of a representative covers its entire orbit. Both children cover their parent, including the cutting hyperplane. The checker stops after accepting every remaining representative; it raises an error if its finite depth limit is reached. The verified partition uses 590 accepted representatives and at most ten successive bisections.

For −1≤T_0,T_1≤−3/4 and 1/2≤T_2,T_3≤2/3 an exact terminal equilibrium repeats the six supports {0}, {1}, {0,2}, {1,3}, {0,2}, {3}, in that order. Each listed player independently uses a strictly interior hazard. On every point of this box all fifteen idle advantages exceed 1/100. The four triple caps may be attained simultaneously. Cyclic relabeling gives three further boxes.

For each recipient i let m=i+2 modulo four. Let q_t be the four-vector of hazards at date t. On the next date u>t (taken on the cyclic calendar) on which i mixes, prescribe V_i(u)=M q_u(m), its payoff from immediate Quit. Propagate backwards from u to t+1 while i waits. On a date of its own group with mate hazard z, replace V by 3z+(1−z)V. On an opposite-group date with hazards w,z, replace V by −1+(1−w)(1−z)(1+V)+(1+T_i)wz. Write v_i(t+1) for the resulting continuation. On own-group dates with mate hazard z the wait-minus-quit comparison is

    (3−M)z+(1−z)v_i(t+1).

On opposite-group dates, with w the successor's hazard and z the predecessor's, the wait-minus-quit comparison is bounded below by

    (1−w)(1−z)v_i(t+1)−d(w−z).

This follows by comparing the two crossed-pair caps and the triple cap to the same wait outcomes. The comparison is exact at the three corresponding cap equalities. Requiring equality on the mixing slots and nonnegativity on all idle slots yields consistent cyclic values by backward substitution.

The accompanying checker verifies the equations and inequalities on each computationally accepted four- or six-date cell with rational arithmetic. [Exact checker](../experiments/SIX_DATE_MATCHED_BOX.py)

Write F for the active comparisons and G for all idle lower bounds. These are polynomials in the hazards and the four rewards. In the six-date calendar they are multiaffine; in the four-date calendar a single hazard can have exponent two when the next active visit is the same date a period later. The sparse polynomial constructor checks all exponents are at most two. For the six-date region, split the four axes into 8,8,6,6 equal rational intervals. For a cell of center T_c and halfwidth vector θ, choose a rational hazard center x_c. Center all polynomials there. Set J=F_x, L=F_T at the center. Choose rational B near J⁻¹ and rational X near −BL. For each fixed δ=T−T_c, seek the hazards x_c+Xδ+y, where |y|≤r coordinatewise for a rational positive r. Put u=(|X|θ+r,θ), with absolute values taken entrywise. The verifier checks

    |BF_c|+|B(JX+L)|θ+|I−BJ|r
       + Σ_[|α|≥2] |(BF)_α| ∏_j u_j^(α_j) < r.

Here α is a multi-index in the centered polynomial expansions and |α| is its total degree. This inequality makes y↦y−BF(x_c+Xδ+y,T) a self-map on the closed box of radii r. It also gives |I−BJ|r<r, hence I−BJ has induced norm below one in the weighted sup norm. Consequently B is invertible, and Brouwer yields a true zero of F. Finally the script checks x_c±u_x lie strictly inside the probability cube. For each G it subtracts from the constant term the weighted absolute sum of all nonconstant terms. The result must exceed zero in the adaptive cube check and 1/100 in the separate six-date low/high boxes. Floating arithmetic proposes centers and radii only. An accepted run verifies the inequalities independently on the cells covering the middle cube and on all 2,304 closed cells of the low/high rectangle. No agreement of chosen hazards across adjacent boundaries is needed.

## The sixteen vertices of the bounded cube

At twelve binary vertices of [−1,2/3]⁴ at least one matched pair has equal rewards, so the one-tied-pair construction applies. The other four vertices have adjacent high rewards and fall in the six-date boxes. This proves the vertex claim without making any interpolation assumption.
