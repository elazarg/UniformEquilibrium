# Private equilibria on the bounded matched-pair cube

For the four independent passive rewards in the canonical matched-pair cube [−1,2/3]⁴, each of the following raw conditions supplies an exact private terminal equilibrium and one fixed original uniform-equilibrium payoff.

- Either matched pair has equal observer rewards.
- Both matched-pair means are at most −2/3.
- All four observer rewards are at least −1/2.
- Each matched pair has an observer reward at least 1/3.

The two mean inequalities give a two-date equilibrium. Every point of the last two regions has a four- or six-date equilibrium. Four particular adjacent-low/adjacent-high boxes share one six-date word with all idle gains from waiting above 1/100. The results cover all sixteen vertices. A surviving point must have two split pairs, a pair with mean above −2/3, and a pair with both entries below 1/3 and at least one below −1/2. Further restrictions follow from the previously proved two-observer region. The complete four-player conjecture remains open.

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

## Two independent pair means

Suppose T_0+T_2≤−4/3 and T_1+T_3≤−4/3. For example, T=(−49/50,−3/4,−9/25,−59/100) passes both tests, has neither pair tied, and lies outside the middle cube and the adjacent-high boxes. For a group g, let C_g=(1−q_i)(1−q_m), D_g=q_i q_m, and δ_g the nonnegative difference between the two hazards. Write h for the opposite group. If all four players mix, an active row's contact, solved for its passive reward as a function of its mate's hazard s, requires

    D_h t_g(s)=1−C_h−D_h−s[c/(1−s)+M C_h].                              (1)

First construct a comparison table in which both group means equal −2/3, allowing each group's reward spread Δ_g independently in [0,2/3]. Assign the higher hazard to the owner with the higher reward (that hazard is the output of the lower observer's contact).

Keep C_A C_B=1/16. For C_B ranging from 9/40 to 5/18, C_A=(16C_B)⁻¹ stays in the same interval. The difference between the two t-values in (1) is

    δ_g(c/C_g+M C_h)/D_h = 8 C_h δ_g/D_h.

Thus the required gap is δ_g=Δ_g D_h/(8C_h). For given survival C_g and gap δ_g the two hazards are 1−(sqrt(4C_g+δ_g²)∓δ_g)/2 and their product is 1+C_g−sqrt(4C_g+δ_g²). Require the pair of product equations

    D_g=1+C_g−sqrt(4C_g+[Δ_g D_h/(8C_h)]²),     g=A,B.                (2)

These give a continuous self-map of the square [0,1/3]². Indeed k_g=Δ_g/(8C_h)≤10/27 and δ_g≤10/81<1/8<1−C_g. Hence both outputs are strictly positive and at most (1−√C_g)²<(1−9/20)²<1/3. Their derivatives in the opposing input are bounded in magnitude by (10/27)²/(3·(9/10))<1/16 since 2√C_g>9/10. There is a unique fixed point, depending continuously on C_B, with D_A,D_B>0. The resulting genuine hazards lie strictly between 19/48 and 3/4: sqrt(4C_g+δ_g²)<13/12, δ_g<1/8, and the larger hazard is at most 1−√C_g+δ_g/2<1−9/20+1/16.

The mean contact condition is now scalar. The sum of the two hazards in g is 1−C_g+D_g, and the sum of their odds q/(1−q) is (1−C_g−D_g)/C_g. Thus at mean −2/3, averaging (1) requires

    D_h/3 = 1−C_h−(c/C_g+M C_h)(1−C_g)/2+(c/C_g−M C_h)D_g/2.

At C_g C_h=1/16 this is equivalent to E_g=0, where

    E_g=15/4−15C_h+4C_h D_g−D_h.

The identity E_B+4C_A E_A=0 holds for every choice of the two products on that survival curve. At C_B=9/40, E_A≥3/8−1/3>0; at C_B=5/18, E_A≤−5/12+10/27<0. Continuity gives a zero of both residuals. The two reward differences and both means now have their specified values, proving all four contacts of the comparison table simultaneously.

For the actual table, raise both entries of each group by the same nonnegative constant to give it mean −2/3. Each original high is ≤−1/3 since the other entry is ≥−1. Each original spread is ≤2/3, so the raised entries, now −2/3±Δ_g/2, remain in [−1,−1/3]. Use the comparison solution above as the lower hazard for each respective player; use 3/4 as every upper hazard. In the active comparison write

    K(s,w,z;T)=w+z−(2+T)wz−s[c/(1−s)+M(1−w)(1−z)]

for the response s of a mate to two opposing hazards w,z. K decreases in T. For s≥19/48, w,z≤3/4 and T≤−1/3 its partial in either opposing hazard is at least 1−(5/3)(3/4)+(8/3)(19/48)(1/4)=1/72. Therefore at each lower output the opposing lower corner is the worst, and it satisfies K≥0 by the comparison table. The passive loss w+z−(2+T)wz is at most 1 since T≥−1. Thus K≤0 at s=3/4 because cs/(1−s)=1. The unique continuous root in each mate's interval defines a self-map of the four-dimensional box; Brouwer gives the actual four contacts. At a quiet date the future contribution is at least M(1/4)²(19/48)=19/288, whereas the crossed and triple caps bound the advantage of joining the passive head by d|w−z|≤17/480. Thus all quiet inequalities hold strictly. Every player has a proper recurring rival, so geometric rival absorption controls all private replacements and restores the original signed levels and uniform target.

### General singleton and matched-pair parameters

The mean construction extends to any common mate singleton reward a and crossed singleton reward −b with a>2b>0. Take x=(a+√(a²−4b²))/2 and x<M<a. Put c=a−M, e=√(b²−cM), s=(b−e)/M. Then 0<s<1 and c/s+Ms=2b. Suppose all T_i≥−b and each matched group's mean is at most −b+e. This forces each T_i≤−b+2e and each within-group spread Δ_g≤2e. The same directional crossed and triple caps are used with these a,b,M,d.

Choose C_l<s and C_u=s²/C_l<1. Put D_max=(1−√C_l)², k_max=e s/(b C_l), δ_max=k_max D_max, and

    L=1−[sqrt(4C_u+δ_max²)+δ_max]/2,
    H=1−√C_l+δ_max/2,       U=max(H,b/(b+c)).

The following explicit scalar conditions suffice for a full private two-date equilibrium:

    0<C_l<s<C_u<1,        0<L≤H≤U<1,
    δ_max<1−C_u,           k_max² D_max<2√C_l,
    b(1+s)(1−C_l/s)>e D_max,
    b−(b+2e)U+M L(1−U)≥0,      d(U−L)≤M(1−U)² L.

For the comparison table raise each group mean to −b+e preserving its spread. On C_A C_B=s² set δ_g=Δ_g sD_h/(2b C_h), the required difference of hazards since c/C_g+M C_h=2b C_h/s. The product equation (2) above holds with this δ. It has a unique continuous product solution in [0,D_max]² since k_max² D_max/(2√C_l)<1, with the corresponding hazards in [L,H]. The mean conditions at −b+e become

    E_g=b(1+s)(1−C_h/s)+e(C_h/s)D_g−eD_h=0.

Here c/C_g−M C_h=2e C_h/s and C_g C_h=s². The exact dependence E_h+(C_g/s)E_g=0 leaves only one scalar equation. It changes sign as C_B moves from C_l to C_u: at the lower endpoint E_A≥b(1+s)(1−C_l/s)−eD_max>0; at the upper endpoint divide by C_u/s to obtain the negative of the same strict bound. This gives both comparison means and both spreads. On the box from those template hazards to U, the derivatives of the actual K in either opposing hazard are at least b−(b+2e)U+ML(1−U). The lower signs follow. At U the passive loss is at most b by T≥−b and cU/(1−U)≥b, giving upper signs. The quiet comparison follows from the last bound. As in the canonical proof all four rates are positive and proper and the result lifts to the original uniform target.

For every fixed a>2b, a nonempty right interval of M at x satisfies these tests for some d_0>0 uniform in that interval. Indeed e tends to zero as M decreases to x and s tends to s_0=b/x∈(0,1). Choose C_l=s(1−√(e/b)), C_u=s/(1−√(e/b)). The sign margin b(1+s)√(e/b) dominates eD_max. The C interval has the required order for small positive e; the formula for L and H gives L≤H. The bounds on δ_max, the contraction and the opposing derivative have strict limiting margins, with L,H→1−√s_0>0 and U→b/(b+c_0)=1/(1+s_0)<1, where c_0=a−x. The positive limiting quiet bound permits a fixed positive d_0. The mean cutoff is explicit in the original normalized singleton and matched-pair parameters; at (a,b,M)=(3,1,8/3) it is exactly −2/3.

### Independently varying singleton and participation rewards

The canonical mean test also gives a finite range in which all twelve off-diagonal singleton entries can vary independently in the chosen row units. Write G_ij=−b_ij for opposing singletons, M_i=Z_i({i,m(i)}), a_i=G_i,m(i), c_i=a_i−M_i and B_i=max_{j∈O(i)} b_ij. Assume

    1≤b_ij,       136/95≤M_i≤8/3,      0<c_i≤1/3,
    B_i≤(16/5)c_i+M_i/20,      T_i≥−1,
    T_0+T_2≤−4/3,               T_1+T_3≤−4/3.

In crossed pairs bound the observer's gain from joining relative to its actual opposing singleton by +1/10 at the predecessor and −1/10 at the successor. Keep the four joining triple caps. The remaining 24 entries are free. At the canonical upper values of c_i,M_i the interval for b_ij extends to 6/5.

Use the comparison table and its lower hazard vector from the canonical mean construction. The actual row's K has loss b_ij w(1−z)+b_ik z(1−w)−T_i wz and cost s[c_i/(1−s)+M_i(1−w)(1−z)]. Throughout the box the loss is at least that of the comparison row and the cost is at most its cost, so every lower output sign holds. At U=3/4 the loss is at most B_i(1−(1−w)(1−z))≤15B_i/16 since T_i≥−1 and B_i≥1. The cost is at least 3c_i+3M_i/64, which is at least that upper loss. The same strictly decreasing response in s gives the four contacts. The worst quiet guard holds because M_i(1/4)²(19/48)≥17/480. These bounds apply directly to the raw normalized parameters.

## Limits of the two-date calendar

If every T_i belongs to [−2/3,2/3], a nonzero proper two-date scheduled root requires all four rewards to equal −2/3 and all hazards to equal 1/2. Here proper means every hazard is less than one. At exact predecessor crossed increments +1/10 a sure player’s mate must wait and the predecessor strictly gains by joining. With only upper bounds on the crossed rewards this sure case may be feasible.

Both groups must have a mixer. A lone mixer leaves its opposite players with a strictly negative wait value; if two mates alone mix the payoff from waiting for the mate is 3, strictly greater than quitting. A sole mixer in each group has zero active value and negative expected next value. With a sole mixer of rate p facing two mixers, both opposing rates are the same v determined by v[c/(1−v)+M(1−p)]=p. This gives v<3/4, and the sole mixer's own contact requires T_i=2(1/v−1)>2/3. Thus all four must mix.

At a full root choose the maximal hazard s. The corresponding K is bilinear over [0,s]² in w,z. It is negative at (0,0); at either one-positive corner K/s≤1−2√(cM)<0. At (s,s), for T≥−2/3,

    K/s ≤ −(3−2s)(2s−1)²/[3(1−s)].

Consequently w=z=s=1/2 and T_i=−2/3. Applying the same argument to the new maximal opposing hazards forces every rate to equal 1/2, which in turn forces all four rewards to equal −2/3.

The two mean inequalities cannot be replaced by a bound of −2/3 on the mean of all four rewards for this two-date conclusion. Take both rewards in A equal to −1 and both in B equal to −1/3. Under the ceiling 2/3 a nonzero proper scheduled solution must have full support by the three-support obstruction. Equality of the two passive rewards within either group forces its two hazards to be equal, by the common strictly decreasing mate response. Let x,y be the within-group odds of waiting, (1−q)/q, in A and B. The two required rewards satisfy

    T_A=2y−c(1+y)²/x−M y²/(1+x),      T_B=2x−c(1+x)²/y−M x²/(1+y).

Writing S=x+y, Cauchy–Schwarz gives T_A+T_B≤2S−c(2+S)²/S−M S²/(2+S). This is the sum of the two required rewards at equal odds S/2, and the homogeneous maximum-hazard calculation bounds it by −4/3, with equality only at odds one. Equality in the Cauchy bound forces x=y, hence identical required rewards in both groups. The example has T_A+T_B=−4/3 and T_A≠T_B, which rules out the two-date profile even though its grand mean equals −2/3. The one-tied-pair theorem supplies a longer equilibrium for this example.

### The sharp cutoff when each group has a high observer

In the four passive rewards T_i∈[−1,2/3], put H=min(max(T_0,T_2),max(T_1,T_3)). There is an absolute algebraic constant σ≈−0.333198490 such that no nonzero proper two-date matched calendar solves its scheduled contacts if H>σ. When H=σ a solution requires the two rewards in each matched group to be exactly −1 and σ. On the benchmark line (−1,−1,t,t), a full two-date equilibrium exists precisely at −1≤t≤σ, including equality. With exact predecessor crossed increments +d>0 the sure case separately fails. These are statements about this calendar class.

The formulas defining σ involve one scalar B. Set

    A(B)=B(8B²−13B+6)/[(1−B)²(8B+3)],
    h(A,B)=[A+B−A·(c/(1−A)+M(1−A)(1−B))]/(AB)−2,
    σ=max h(A(B),B)   over 0<B≤3/4 with A(B)≤B.

At each of the four contacts K=0, with s the mate output of the row whose reward is T. The passive loss is at most one, so all rates are ≤3/4. In each matched group call the higher-reward observer high and its mate low; break ties arbitrarily. The high owner's own hazard is at least the low owner's: K is strictly decreasing in s, decreases in T, and the high hazard is the output of the low observer's contact with the same w,z. Let A and B be the largest low and high owner rates respectively. Thus A≤B.

In the row producing B, use T=−1 to bound above that row's actual K. This K is strictly increasing in each opposing hazard on [0,3/4]², since each partial is (1−z)(1+MB) or its analog. Hence K(B,A,B;−1)≥0. Solving this inequality for A gives A≥A(B), and therefore the scalar B lies in the defining feasible interval. Now put t=min(0,H). In the row producing A, upper-bound the actual K by using T=t. Over [0,A]×[0,B] the two partial derivatives with respect to the opposing hazards are at least
    1−2B+M(1−B)A(B) =
    (112B³−158B²+45B+9)/[3(1−B)(8B+3)]>0.
For instance the cubic's Bernstein coefficients on [0,1/2] are (9,33/2,65/6,6) and on [1/2,3/4] are (6,43/12,11/8,9/8). Thus K(A,A,B;t)≥0, i.e. t≤h(A,B). Moreover ∂_A h<0 for 0<A≤B, since B∂_A h=−B/A²−c/(1−A)²+M(1−B) and B/A²≥1/B>M(1−B). We get t≤h(A(B),B)≤σ. The algebraic evaluation below gives σ<0, which also excludes H≥0.

At H=σ every upper bound above is attained. In particular A=A(B), h(A,B)=σ and the two bounding K values vanish. Both K's increase strictly in both opposing rates. The row producing B must therefore see its opposing group use exactly A,B and have passive reward −1. The row producing A must similarly see exactly A,B and have reward σ. Applying these same equalities to the opposite group, now known to attain both maxima, forces the rates and reward assignments in both groups as claimed.

On the benchmark line choose both low owners' rates A(B) and both high owners' rates B. Then the low-observer equality holds by construction. The high-observer equality holds at t=h(A(B),B). On either endpoint of the feasible B interval A(B)=B, hence h=−1 because the two K rows coincide. By continuity all values from −1 to σ occur. For the off-group guards, A(B)>B/2: its ratio to B equals [c/(1−B)+M(1−B)−1]/[(1−B)(1+MB)], with numerator at least 2√(cM)−1>3/4 and denominator at most 1+(M−1)²/(4M)<3/2. Thus M(1−A)(1−B)A≥MA/16>d(B−A) at every quiet date. Rival hazards are strictly positive, yielding the full equilibrium and fixed uniform target with all 24 unused rewards arbitrary.

For reproducible algebraic evaluation the condition A(B)≤B is C(B)=8B³−21B²+15B−3≥0. Its feasible set in (0,3/4] is one closed interval. The endpoint Sturm variations for C at B=0,0.3438,0.3439,0.6820,0.6821,0.75 are 3,3,2,2,1,1 respectively. On this interval h(A(B),B) has numerator
    512B⁷−2752B⁶+5784B⁵−7257B⁴+6558B³−4149B²+1539B−243
and positive denominator 3B(B−1)(4B−3)(8B+3)(8B²−13B+6). For the numerator of its derivative, normalized with positive leading coefficient, the Sturm variations at 0.3438,0.53672,0.53673,0.6821 are 6,6,5,5, and the respective signs are +,+,−,−. There is a unique interior maximum. To verify σ<−3/10 directly, take the numerator of −h−3/10 with denominator 30B(B−1)(4B−3)(8B+3)(8B²−13B+6). Its minimum Bernstein coefficients on [0.34,0.50],[0.50,0.55],[0.55,0.69] are 9/2,27271953/14000000,815819/400000. Also h(A(7/13),7/13)=−63603499/190855665>−1/3.

## Four and six dates with independent split rewards

The entire cube [−1/2,2/3]⁴ admits equilibria. When both members of one matched pair have T_i in [−1/2,1/3], use the existing two-observer result, which leaves the other pair unrestricted. Elsewhere the checker chooses one of the following two calendars, allowing cyclic player relabeling and time translation. The four-date supports are {0,2}, {1,3}, {2}, {3}. The six-date supports are {0}, {1}, {0,2}, {1,3}, {0,2}, {3}. Each listed hazard is strictly between zero and one, and every idle comparison on a computationally accepted cell is strictly positive. [Earlier two-observer region](../exports/INDEPENDENT_PASSIVE_REWARDS_ON_MATCHED_PAIRS.md)

Split each parameter axis initially at 0 and 1/3. Identify a rational cell with the lexicographically least cyclic rotation of its four intervals. For each representative the checker first tests the two-observer result, then the calendars in all cyclic player orientations. It bisects each remaining cell at the midpoint of a longest side, testing both children after reducing them to cyclic representatives. The game and the directed crossed inequalities are invariant under these rotations, so acceptance of a representative covers its entire orbit. Both children cover their parent, including the cutting hyperplane. The checker stops after accepting every remaining representative; it raises an error if its finite depth limit is reached. The verified partition uses 590 accepted representatives and at most ten successive bisections.

For −1≤T_0,T_1≤−3/4 and 1/2≤T_2,T_3≤2/3 an exact terminal equilibrium repeats the six supports {0}, {1}, {0,2}, {1,3}, {0,2}, {3}, in that order. Each listed player independently uses a strictly interior hazard. On every point of this box all fifteen idle advantages exceed 1/100. The four triple caps may be attained simultaneously. Cyclic relabeling gives three further boxes.

There is also a larger high-observer region. If max(T_0,T_2)≥1/3 and max(T_1,T_3)≥1/3, the other two rewards may independently range throughout [−1,2/3]. Partition each axis at −1, −3/4, −1/2, 0, 1/3, 1/2 and 2/3. The 102 initial cyclic representatives consist of cells with a lower endpoint ≥1/3 in each pair. Their closed union, including rotations, is the full stated region. The checker accepts cells covered by the middle cube, the two-observer interval or the four earlier low/high boxes. For the rest it uses the same longest-side bisection and Brouwer test, trying the earlier rosters and the additional six-date word {2},{3},{0,2},{1,3},{0,2},{1,3}. The rational replay accepts 9,275 cyclic representatives and exhausts the parameter cover after at most eighteen bisections. Its direct calendar checks verify strictly interior hazards and strictly positive idle advantages. [High-observer checker](../experiments/MATCHED_PAIR_UPPER_CONE.py)

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
