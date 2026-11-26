# Solo and joint equilibria and the necessity of simultaneous quitting on a four-player diamond

This ordinary mathematical result gives an open reward class on a diamond of singleton comparisons. On an asymmetric open region it characterizes exactly when arbitrarily accurate terminal equilibria with vanishing probability of simultaneous first quitting exist. Under an additive completion, three-date joint strategies give original uniform equilibria across the entire interval of equal twin joining factors and over an explicit rectangle of unequal factors. For each accuracy one profile must approximate a fixed target at every sufficiently large finite-average horizon against every complete unilateral behavioral replacement. The producer selects one profile before accuracy. Every player's live and Never rewards are zero. Row i has own singleton level s_i. At any nonempty coalition S put Z_i(S)=r_i(S)-s_i and write Gamma_ij=Z_i({j}), J_ij=Z_i({i,j}) for different players. A solo calendar has at most one positive hazard at each date. All equilibrium comparisons allow any complete unilateral behavioral replacement.

## Raw six-phase producer

In the order X,Y,U,V, suppose the singleton matrix is

    [ 0   -b   h   k ]
    [ d    0  -e  -f ]
    [-u    v   0   c ]
    [-z    t   l   0 ],

where b,h,k,d,e,f,u,v,z,t are positive. The two entries c,l are signed. Define

    A=v h/b,    B=u e/d,    C=v k/b+c-u f/d,
    E=t h/b+l-z e/d,        F=t k/b,     G=z f/d.

Take each real root rho of the explicit quadratic

    (A rho-B)(F rho-G)-C E rho=0.

Assume C is nonzero. Retain roots 0<rho<1 for which W=(B-A rho)/C is positive. The finite list of candidate phase lengths, in chronological order X,Y,U,X,Y,V, is

    L = (f W/(d rho), h/b, 1, e/d, (k/b)W, W).

Repeat these six entries multiplying masses by rho each cycle. For each of the six phases j with owner m_j, form the actual quartet

    K_j=(sum_{i=0}^5 rho^{floor((j+i)/6)} L_((j+i) mod 6)
                      Gamma_{.,m_((j+i) mod 6)})/[(1-rho)L_j].

If one retained root has J_{a,m_j}<=K_{ja} for every j and every a different from m_j, then the original game has an exact terminal Nash profile that witnesses fixed uniform payoffs at all requested accuracies. All higher coalition coordinates and all passive pair rewards are free. The own levels may be any finite numbers.

To prove this, work in unconditional mass units, with L_j summing over the infinite schedule to a finite total. At date j take its hazard L_j divided by the remaining tail mass. The normalized infinite sum of the weighted singleton columns from a phase supplies its native continuation. The actual hazard times K_j is that continuation. Owner indifference is equivalent to zero sum of native singleton rewards between consecutive visits (then the geometric tail tends to zero). The two X intervals require bL_1=hL_2 and bL_4=kL_5, and the two Y intervals require eL_2=dL_3 and fL_5=d rho L_0. The U and V intervals respectively require

    A rho-B+C W=0,          E+(F-G/rho)W=0.

These are precisely the quadratic and its reconstruction formula. Owners have native zero both before and after their own phase. A quiet player a's forced quit offer is the actual hazard times J_{a,m_j}. Continuing gives its prescribed value. Iterating the Bellman inequalities is valid for every behavioral choice. Omitting one owner leaves positive hazards every cycle and geometric opponent survival, uniform over that owner's entire replacement. Every deviation absorbs almost surely and has uniformly bounded mean absorption time. Thus the original payoff restores s, finite averages differ from terminal payoffs by O(1/N) uniformly over deviations, and every phase's prescribed payoff witnesses uniform equilibrium.

## Rational calibration

Take

    Gamma = [ 0 -1  2      2     ]
            [ 2  0 -1     -1     ]
            [-1 17/8 0    -9/32  ]
            [-1 17/8 -9/32 0     ].

Write t=17/8, g=9/32. Set all s_i=1, take passive Z_i(S)=sum_{j in S} Gamma_ij, and when i is a participant take Z_i(S)=k_i sum_{j in S} Gamma_ij, with k=(1/2,1/2,9/10,9/10). Change only Z_Y({Y,U,V}) to 8. This last cell is used only to test an alternative three-phase joint strategy below.

All six hazards are 1/2, the mass ratio rho is 1/64 and W=1/8. In displayed column order the six K_j are

    (0,2,1/16,0),  (0,0,17/8,2), (2,0,0,-1/4),
    (0,2,0,1/16),  (0,0,2,17/8), (2,0,-1/4,0).

In particular every quiet comparison is strict. The quadratic has a simple root at 1/64: here A=F=17/4, B=G=1/2, C=E=111/32. Its other root equals (B/A)^2 divided by 1/64, which is 256/289. The simple root, reconstructed W, and strict finite comparisons persist on an open set in all sixty entries. All thirty-two unused coordinates remain arbitrary. At X the target is (1,2,33/32,1).

## A classification on the marked singleton and joining data

More generally write the marked cyclic rows as (0,-1,2,2),(2,0,-1,-1),(-1,t,0,-g),(-1,t,-g,0), assume g>0 and 4t-1-2g>1, s_i>0, and J_ij=k_i Gamma_ij with 0<k_i<1. The following necessity holds for EVERY exact terminal Nash profile that is a solo calendar, even one with infinite nonperiodic timing or arbitrary subdivisions. Ignore dates at which everyone continues for sure. After finitely many initial blocks, successive distinct owners must follow

    X,Y,U,X,Y,V,X,Y,U,... ,

up to cyclic rotation and interchange of U,V. The total unconditional exit masses b_i of successive sporadic runs (U or V) have ratio equal to the positive root of

    4t r^2+(4t-1-2g)r-1=0.

At the marked data this ratio is 1/8. Thus every exact solo equilibrium has the same aggregate phase lengths in its tail up to rotation and scale. The unrestricted first run may have a different mass.

Indeed no positive Never probability is possible: in that case along sufficiently long surviving histories all residual stopping probabilities tend to zero, hence the original prescribed conditional payoff tends to zero, whereas quitting at once earns a value tending to s_i>0. In exact Nash every positive-survival live history obeys local endpoint optimality, as otherwise deviating after that history improves at the start. At a sure singleton date some quiet player's Gamma_ij<0 in that column, so joining strictly beats waiting. Perpetual play with only one remaining owner j also fails: since it must absorb, a player with Gamma_ij<0 receives this negative native payoff, whereas quitting at once earns k_i Gamma_ij times j's current hazard, strictly above its value. Therefore infinitely many distinct-owner blocks occur, all hazards at their live dates are proper, and every individual run ends after finitely many active dates.

A mixing owner has native value zero both before and after every one of its dates. On a change p to j the value of p is zero at the first j date. Its joining comparison requires Gamma_pj<0, because its immediate offer is its positive k_p times Gamma_pj times a positive hazard. Also Gamma_jp>0: j's value after the p block is zero, so at the beginning of that block its unnormalized native continuation is Gamma_jp times the whole block's mass, while its forced join offer in the same units is k_j Gamma_jp times the first substep mass. Negative Gamma_jp would give a strict gain. The directed graph of allowed changes is exactly X to Y, Y to U or V, and either of U,V to X. After a possible incomplete initial block, denote its blocks X_i,Y_i,B_i where B_i is one of U,V and the respective masses are x_i,y_i,b_i>0.

Between consecutive visits of X and Y their indifference implies y_i=2b_i, x_{i+1}=b_i/2. The owner of B_i has zero native tail after that block. Summing all its future singleton columns gives

    b_i=(4t-1) sum_{l>i} b_l - 2g sum_{l>i:B_l!=B_i} b_l.       (1)

Thus b_i>sum_{l>i} b_l. At the first date of B_i the difference between the twin's and incumbent's unnormalized values is

    -g [ b_i + sum_{l>i:B_l=B_i}b_l - sum_{l>i:B_l!=B_i}b_l ].

Joining that date earns at least -k_twin g b_i in the same units. Since the incumbent's value is zero, the future sum over the opposite label exceeds the future sum over the same label by at least (1-k_twin)b_i>0. By (1) at i+1 the sign of that imbalance is dictated by the very next sporadic block. Consequently B_{i+1} is always the opposite twin. Between consecutive visits of the same twin, indifference now yields

    4t b_{i+2}+(4t-1-2g)b_{i+1}-b_i=0.

Its two real roots have opposite signs; the negative root has strictly larger absolute value because 4t-1-2g>0. Any nonzero coefficient of that root would eventually alternate the sign of b_i. Hence only the positive root remains. At the marked data the second root is -16/17.

In fact the existence of ANY exact solo equilibrium on this symmetric two-parameter singleton class is equivalent to the two inequalities

    1/(1+r) <= k_i <= 1-g/[2t(1+r)]  for both i=U,V,              (2)

where r is the positive root above. The other two factors may be anywhere in (0,1). All other coordinates are arbitrary. To see why subdivisions cannot enlarge the domain, consider any run with mass L, joining factor k, singleton comparison h and quiet player's opening native value in mass units W. When h<0, the first substep of mass d requires W>=kh d>=kh L. When h>0, the last substep of mass d requires W-h(L-d)>=kh d and hence W>=h L-(1-k)h d>=kh L. These are exactly the quiet requirements when every complete run is coarsened to a single date. The aggregate word and its owner equations already fix all conditional values. With b_i as unit, sum the geometric columns, using y_i=2 b_i, x_i=b_i/(2r), and (4tr-1)(1+r)=2gr. In row order X,Y,B_i,its twin, the resulting K vectors at X_i,Y_i,B_i are

    (0,2,2gr/(1+r),0),    (0,0,t,t-g/[2(1+r)]),
    (2,0,0,-g/(1+r)).

For verification the last phase's twin value follows by subtracting the two rows: the future signed branch masses sum to b_i/(1+r), with incumbent value zero. At X_i the previous twin's value is zero and the row difference gives 2gr/(1+r); at Y_i the two branch values follow by subtracting the X_i column from these two opening values and dividing by y_i. The X,Y rows follow from their two owner equalities. Requiring each joining payoff below its displayed cap yields precisely (2); when these hold the coarsened six-phase clock is exact by the Bellman argument above. At the marked table the interval is [8/9,16/17]. Outside (2) any exact Nash equilibrium must put positive hazard on at least two players at the same live date.

## Exact classification on an open asymmetric diamond region

Return to the general singleton matrix of the raw producer. Assume its two signed cross entries c,l are both negative, every s_i>0, and 0<J_ij/Gamma_ij<1. Write m,n for different twins U,V and set

    alpha_m=Gamma_Xm/(-Gamma_XY),     beta_m=(-Gamma_Ym)/Gamma_YX,
    gamma_m=-Gamma_mX,                delta_m=Gamma_mY,
    L_ma=delta_m alpha_a-gamma_m beta_a+Gamma_ma,
    D=min_{m,a in {U,V}} L_ma/(gamma_m beta_m),
    C(m,a)=(delta_n-gamma_n delta_m/gamma_m)alpha_a
                         +Gamma_na-(gamma_n/gamma_m)Gamma_ma.

Suppose D>1 and C(m,m)+max(0,C(m,n))/D<0 for both m. On this open region the six-phase producer's single positive mass cycle gives a necessary and sufficient test for the existence of *any* exact solo equilibrium. Violation therefore forces simultaneous positive hazard somewhere in every exact equilibrium, irrespective of its timing or memory. The inequalities above contain no strategy variables. At the marked data D=111/16 and C(m,m)=-9/32, C(m,n)=9/32. The region has interior in all sixty raw coordinates. There is no row-factor proportionality requirement.

Proof. The same adjacency comparison and absence of last run as in the symmetric proof apply with individual joining ratios in (0,1). The graph of any exact solo calendar again has blocks X_i,Y_i,B_i, with B_i in {U,V}. Denote the masses by x_i,y_i,b_i, and put m=B_i. Core indifference gives y_i=alpha_m b_i and x_{i+1}=beta_m b_i. Let T_a=sum_{j>i:B_j=a} b_j. The unnormalized payoff to m after its own block vanishes, so

    gamma_m beta_m b_i=sum_a L_ma T_a.

In particular b_i>=D sum_{j>i}b_j. The opening native payoff of the other twin n in mass units is Gamma_nm b_i+sum_a C(m,a)T_a. This follows by subtracting gamma_n/gamma_m times the incumbent row's zero value in the unnormalized tail. Its first joining offer is no less than J_nm b_i because J_nm<0. Thus sum_a C(m,a)T_a>0 since J_nm>Gamma_nm. If B_{i+1}=m then T_m>=b_{i+1} and T_n<=b_{i+1}/D by the dominance bound at i+1. Since C(m,m)<0 this would make the displayed sum strictly negative. Therefore B_{i+1}=n in every run after the initial segment.

Along the alternating tail indifference between visits of m gives

    b_i=d_m b_{i+1}+e_m b_{i+2},   d_m=L_mn/(gamma_m beta_m),
    e_m=delta_m alpha_m/(gamma_m beta_m).

Both d_m and e_m are positive, and d_m>=D>1. Set A_m=[[d_m,e_m],[1,0]]. The positive two-step matrix M=A_m A_n has positive determinant e_m e_n, two distinct positive eigenvalues (the larger is strictly above both diagonal entries, and the smaller strictly below both). Its larger root has a positive eigenvector and its smaller root has opposite-sign coordinates. For any starting twin m, the vectors of consecutive masses obey v_{i+2k}=M^{-k}v_i>0. A nonzero smaller-eigenvalue coefficient would eventually dominate and force one negative coordinate. Thus v_i lies on the positive Perron ray. Conversely this ray supplies a unique positive tail up to scale with two-step factor rho=1/lambda_Perron<1 (M's first diagonal entry is d_m d_n+e_m>1). The reconstruction coefficient C of the raw producer equals L_UV and is positive under D>1. The ratios y_i,x_{i+1} reconstruct the same six masses as the raw producer. The same first/last substep proof coarsens all quiet comparisons in each complete block, using each J_ij/Gamma_ij separately. Hence an exact solo equilibrium forces the canonical coarse comparisons. Their sufficiency follows from the six-phase Bellman proof. Higher coalition data never enter.

## An unrestricted regret and collision criterion

Under all the hypotheses of the open asymmetric classification above, write e for the maximum original terminal gain from any unilateral behavioral replacement and C for the on-path probability that the first quitting coalition contains two or more players. Then

    inf over all behavioral profiles of (e+C) = 0
                   if and only if the six-phase raw test succeeds.

Thus failure of the raw test implies a strictly positive table-dependent lower bound on e+C for every profile. On the symmetric singleton and row-factor family the test is exactly (2). In particular any sufficiently accurate terminal equilibrium profile on the other side must have a positive probability of simultaneous first quitting bounded below independently of accuracy. Success gives an exact solo equilibrium, proving one implication. For the converse take a sequence with e+C tending to zero.

**Compactness in exit probability.** Write S for incumbent survival at a date, q_i for the independent hazard on the unique live history, and H_i=prod_{j!=i}(1-q_j). The total exit mass at this date is m=S(1-prod_j(1-q_j)). Split the physical interval [1-S,1-S+m) into subintervals (in any fixed order) carrying the unconditional masses of each nonempty quitting coalition. In particular the i-singleton mass Delta_i=S q_i H_i receives color i; mark every simultaneous coalition gray. Only the sum over all dates of the gray lengths, C, enters the bounds. Let T_i(s) be the integrated tail of Z_i from point s, minus s_i N where N is joint Never. This is linear on each subinterval and extended constantly after 1-N. At the beginning of the physical date T_i=S V_i, where V_i is its conditional prescribed original value minus s_i. If N>0, each player has finite cumulative hazard and conditional expected original payoffs tend to zero far out on the surviving tail, whereas quitting there pays a value tending to s_i. Following the incumbent before that date thus gives a limiting gain N s_i; in all cases N<=e/min_i s_i. No stationarity is assumed, since before absorption the sole public history is repeated all-Continue and each surviving owner's independent stopping law has its conditional hazard.

Let M bound |Z_i(T)| over all rows and nonempty coalitions. At a physical date write Q_i for native forced Quit, P_i^c for native forced Continue with the incumbent future, and D_i=P_i^c-Q_i, so V_i=Q_i+(1-q_i)D_i. Since Q_i is zero when nobody else quits, |Q_i|<=M(1-H_i). Changes to the strategy made only on reached histories give T_i>=S Q_i-e by immediate Quit. Also

    sum_dates S q_i [D_i]^+ <= e.

Indeed suppress i's own hazards on its favorable dates D_i>0 through a finite prefix and then resume the incumbent. The changed survival to every altered date is at least S. The finite Bellman telescope of its gain is the sum of the changed survivals times q_i D_i there. Use the deviation bound and increase the prefix. This also holds if some incumbent hazard is one: at histories unreachable under the incumbent one can instead simply resume it there, and the old continuation values there still give the performance-difference telescope. Any candidate with an unreachable future due to player's own sure hazard can use the specified strategy's conditional continuation at that pure hypothetical live history.

Using Delta_i<=S q_i and S<=1, the sum of Delta_i S |Q_i| is at most M C: the event that i and some rival quit is a simultaneous exit. Therefore the sum over dates of Delta_i |T_i(start)| is at most 2e+2MC. In fact the negative part costs at most e+MC by immediate Quit, and the positive part costs at most e+MC by V_i=Q_i+(1-q_i)D_i and the skip bound. Interpolation from a date's beginning to any point on its i-colored part changes T_i by at most M(m-Delta_i), because i's own singleton has native value zero. Moreover

    sum_dates Delta_i (m-Delta_i) <= sum_dates S q_i(1-H_i) <= C,

since m-Delta_i counts only exits containing a rival. Thus integral |T_i| d mu_i <=2e+3MC for each color i. When e+C tends to zero, take a subsequence along which the four cumulative singleton color masses converge uniformly (they are 1-Lipschitz on the unit interval); these determine limiting measures mu_i whose sum is Lebesgue measure, since the gray and Never masses disappear. The bounded tail functions T_i converge uniformly to W_i(t)=sum_j Gamma_ij integral_[t,1] d mu_j. The integral bound just proved gives integral |W_i| d mu_i=0. Thus a point with W_i(t) nonzero has a neighborhood without i mass.

**Local structure before t=1.** At any fixed t<1 the four remaining masses x,y,z_U,z_V sum to 1-t>0. If W_X=W_Y=0 then y=sum alpha_a z_a and x=sum beta_a z_a. Consequently W_m=sum L_ma z_a>0 for both twins m, since D>1 and at least one z_a is positive. No set of allowable movers at t can contain X,Y and either twin. By continuity there is an interval around t on which all colors belong to one of {X,Y}, {X,U,V} and {Y,U,V}: exclude every row nonzero at t. When X,Y are the only colors, W_X is monotone with strictly signed change per unit Y mass. Its zero set is an interval (possibly empty). Only X may move on the interior of that interval, and only Y off it. The same argument works for any two distinct colors since every singleton comparison is nonzero.

In {X,U,V} the two singleton comparisons in row X at U,V are of the same strict sign. Thus W_X is monotone, and its zero set is again an interval. Only X moves on its interior, as constancy of W_X forces zero U and V mass there. Outside this zero interval only U,V may move, giving at most three pure subintervals on each side by the two-color argument. The argument in {Y,U,V} is the same, with two negative coefficients. A finite cover shows that on every compact subinterval of [0,1) the limiting calendar consists of finitely many runs of a single color. Merging adjacent identical colors gives a consecutive finite or countable set of runs, beginning at zero and accumulating, if infinite, only at 1. Each run of owner j has W_j=0 throughout its closure by continuous support.

**Passing physical-date comparisons to the limit.** To pass the quiet comparisons, retain every colored point of physical dates of mass less than eta, and on dates of mass at least eta retain only the color j of a largest hazard (break ties by fixed player order). The discarded minority singleton lengths over all such dates are at most 12 C/eta. Indeed q_j>=m/(4S)>=eta/4 there by the union bound, while for any i!=j, S q_i q_j is bounded by the simultaneous exit mass at that date. Choose eta=sqrt(C)+1/n on the nth approximating profile. The discarded mass tends to zero. Thus one can select retained points of color j approaching the beginning or end of any pure limiting run of that color by diagonal extraction, since each fixed interval in the run has positive limiting j mass.

For a selected physical date interval [l_n,r_n] take convergent endpoints. If m_n tends to zero then S|Q_i|<=3M m_n, using S q_h<=m_n for every opponent. The quiet comparison in the limit is W_i(l)>=0. Otherwise, on a subsequence m_n tends to m>0, and j must be its dominant color. All hazards other than j tend to zero: q_j>=m_n/4, and S>=m_n, while S q_j q_h<=C_n for h!=j. All but a vanishing part of the physical date is j-colored, so any positive length limiting interval lies inside the maximal run of j. Moreover for every i!=j, S Q_i=J_ij m_n+o(1). This follows by discarding other rival hazards, with an error bounded by a fixed multiple of their sum, and using S q_j=m_n+o(1). Immediate Quit at the physical date gave T_i(l_n)>=S Q_i-e, hence W_i(l)>=J_ij(r-l). This same formula already follows when m_n tends to zero. For Gamma_ij<0 select points tending to a from the interior of its maximal run [a,b] of color j. Any limiting physical interval of positive length is contained in [a,b], since it cannot contain positive mass of an adjacent color; consequently l=a, r<=b. As J_ij<0, the inequality gives W_i(a)>=J_ij(b-a). For Gamma_ij>0 approach b from inside, so r=b and l>=a. Since W_i(a)=W_i(l)+Gamma_ij(l-a) and Gamma_ij>J_ij, this too yields W_i(a)>=J_ij(b-a). The same containment holds at the domain endpoints 0 and 1.

A final run [a,1] of color j is impossible: choose i with Gamma_ij<0, then W_i(a)=Gamma_ij(1-a)<J_ij(1-a). Hence the limiting calendar has infinitely many runs. Coarsen each one to an ordinary date with hazard (b-a)/(1-a) in (0,1), so the resulting independent stopping laws absorb almost surely. The owner has exact native zero at both endpoints; every quiet player's forced offer is bounded by its actual native continuation by the preceding comparison. To finish without any assumption about opponents' chance of perpetual continuation, first apply the elementary **necessary** adjacency, tail balance, and dominance calculations of the asymmetric rigidity proof: they use only these endpoint comparisons, positive masses and owner equalities. They force the alternating six-phase tail with strictly positive periodic hazards after at most finitely many blocks. Each player then faces geometric opponent absorption. Thus the Bellman comparisons imply exact Nash under every complete unilateral replacement, and specifically force the raw inequalities of the six-phase producer. This proves the necessity under unrestricted vanishing regret and vanishing actual collisions.

The resulting collision probability cannot be dispersed across arbitrarily many negligible dates. More generally, in any four-player independent quitting game with C>=c>0 there is a date with unconditional probability at least c^3/1152 of a simultaneous first quit. All dates after survival first falls below c/2 account for at most c/2 total first quits. Therefore on some date with S>=c/2 the conditional probability of a multiple divided by that of any exit is at least c/4; otherwise summing the corresponding unconditional probabilities gives less than c/2 collisions on this prefix. For the two largest hazards q_1>=q_2 at that date, the union bound gives Pr(multiple)<=6q_1q_2 and Pr(any)>=q_1. Hence q_2>=c/24 and that day's actual collision probability is at least S q_1 q_2>=c^3/1152. In particular, on the side where the six-phase test fails, every sufficiently accurate terminal equilibrium has a single joint first-exit date of uniformly positive probability.

At the marked table there also exists a positive lower bound on terminal regret for ALL periodic solo calendars with at most five distinct-owner runs per period, even with arbitrarily many substeps and varying aggregate hazards. Otherwise take a vanishing-regret sequence and the convergent mass coordinates just established. Its limit has the exact alternating six-run tail. Pass to a subsequence fixing the at-most-five cyclic labels and their rotation (a run can be split across the initial period boundary), and let the period survival tend to lambda. If lambda=0, the entire limiting calendar in 0,1) is contained in the first period, which has finitely many runs; a final run is impossible. If lambda=1, let p_i be a subsequential limit of the first-period singleton i mass divided by total first-period exit mass. Every complete later period has the same relative composition. Any interval in exit-mass time contains at most two incomplete endpoint periods, each of length tending to zero. Hence the limiting mu_i is p_i times Lebesgue measure, incompatible with runs of changing pure color. Finally if 0<lambda<1, take limits of the first-period block masses. Each later period has exactly those limiting masses scaled by the corresponding power of lambda, up to omission of zero masses and merger of consecutive equal colors. Its compressed cyclic word therefore repeats at most five labels. The forced infinite word X,Y,U,X,Y,V has fundamental period six. This proves the bound. Six dates attain zero regret on the marked game.

## Comparison with stationary schedules and sure openings

On the marked completed table use hazards (x,y,u,v), z=u+v, b=Gamma q. The passive native expected payoff at a date is b. The forced-Quit native offer is Q_i=k_i b_i except Q_Y=b_Y/2+9uv(1-x). In a nonzero stationary equilibrium with at least two positive hazards, a player faces geometric opponent absorption. Always continuing pays b_i/(1-H_i), with H_i the product of its opponents' survival probabilities for the date. In rows other than Y, positive hazards require b_i<=0 and nonsure hazards require b_i>=0. In row Y a positive hazard requires (1-k_Y)b_Y<=9uv(1-x) if b_Y>0, and a nonsure hazard requires b_Y>=0. If only one hazard is positive consider a negative passive recipient of its column, who gains by joining because k_i<1 and the correction is nonnegative.

Assume first x,z>0. Row X gives y>=2z>0. An active sporadic row gives x>=t y-gz. Hence b_Y=2x-z >=(4t-2g-1)z >6z. But Y needs b_Y/2<=9uv(1-x)<=9z^2/4, impossible as z<=1/2. If x=0,z>0 then b_Y=-z forces y=1. Both sporadics now have b>=t-g>0, incompatible with z>0. If z=0,x>0,y>0, row Y requires b_Y=2x<=0. If z=y=0 and x>0 a quiet sporadic has b<0; if x=z=0 and y>0, quiet X has b_X<0. Finally all Never fails at s_i=1.

In an opening with two sure owners every owner faces a sure opponent. The same sign proof applies directly to those two one-date choices. If X alone is sure, b_Y=2-u-v>0 and the bonus vanishes. This gives y=0 and b_U<0, requiring U to be sure. If Y alone is sure then b_U,b_V>=t-1-g>0, forcing u=v=0, and b_X=-1 forces X sure. If U alone is sure then b_X>=2-y>0 gives x=0, and b_Y=-1-v<0 gives y=1. The last argument covers V by symmetry. No punishment tail enters these necessary comparisons on the other owners.

The four-by-four determinant is 2079/512. Every principal of size at least two is invertible and each full column contains a negative component, giving R0. At unit target the unique complementary vector has full support (463/462,233/231,116/231,116/231); direct substitution on each of eleven nonsingleton sets verifies uniqueness. Thus its degree is +1. The full inverse has two strictly positive columns, X and Y. The outside row times the inverse of the deleted principal, by deletion X,Y,U,V, is respectively (-263/136,-4/17,-4/17),(-41/64,-1,-1),(-51/320,-3/80,37/40),(-51/320,-3/80,37/40). No nonnegative inverse-weights triple applies. The joint-sign test survives using a tiny multiple of the complementary vector, which has all b_i positive and all g_i=Q_i-b_i negative for a small enough scale. Every reverse survival surface sees a single negative supplier so its sign premise fails. The marked game also meets the hypotheses used in the global residual-path argument of [the joint stationary tests: the singleton minimum map is R0 of degree one, and the stationary residual B_i=b_i-(1-H_i)Q_i has no nonzero complementary root, since such a root would satisfy the box inequalities just excluded.

Every pair partition has a strict negative directed joining gap on one of its two pairs, since UV alone has both gaps nonnegative. The two-unrestricted-recipient criterion requires nonnegative joining gaps in row a at both free singleton opponents. Its only surviving (a,b;h,k) are (Y,X;U,V), (U,Y;X,V), and (V,Y;X,U). For the first, choose e=X with hazards x=(0,1/4), y=(0,1/4,3/4) in the criterion's free-free-other order. With P,Q,H denoting passive expected native contribution, forced-Quit offer, and opponent survival, use subscripts o at x and p at y. The two-free test requires A_e>=0 to imply B_e>=0, where A_e=H_o(P_p+H_p Q_o)-(Q_o-P_o) and B_e=P_p+H_p P_o-(1-H_o H_p)Q_p. Their values here are 25/256,-25/512. For the other two use e=a, x=(1/2,0), y=(1/2,0,1/2); the values are 7/40,-7/1280. This exhausts the role assignments.

The supportwise Low/Charge/Orientation test fails on XYU. Take all three active odds equal and sufficiently small. Every active forced-Quit numerator has positive linear term since Gamma_XYU times the ones vector is (1,1,t-1), and k_i>0. The Charge coefficient at singleton Y is -1/2+k_U t>0. In the odds coordinates the joining-gain Jacobian at zero is diag(k_i-1) Gamma_XYU with determinant negative because det Gamma_XYU=4t-1>0. Thus (-1)^3 det D Phi is positive throughout a small neighborhood and the required negative orientation fails. The other sporadic triple is identical. No pair has two positive participant premiums. These comparisons concern the named criteria and persist under small changes where their relevant signs are strict.

The same small uniform odds on XYU and XYV rule out every nonempty marked set in the marked-support criterion. At least one of the triples meets the marked set, all active forced offers exceed the own levels, and the physical indifference values converge to the own levels 1, above every permitted unmarked floor. All first-action tubes of the payoff-domain orientation criterion contain a neighborhood of native zero since zero has the all-zero first-action witness. On XYU the native indifference coordinates for small equal odds are all strictly negative to first order, so its wrong orientation persists inside each tube. The separate closed hull test fails on YUV at positive odds (1/9,1/4,1/4). There the native forced Quit values are (4/25,9/64,9/64), the odds indifference map is (7/8,-25/1152,-25/1152), and its Jacobian determinant is -3641/307200. The three displayed indifference coordinates are exactly the projection of (37453/260784)Z({X})+(2395/32598)Z({Y,U,V}), with its remaining convex weight on zero. Thus both the hull membership and the strict orientation failure are exact.

## Comparison with grouping the twins into one joint date

Consider the proper strictly positive stationary-by-phase strategy X then Y then {U,V}, with respective hazards x,y,r,s. If this is exact terminal Nash, U,V have native values -k g s,-k g r in the last phase, from quitting immediately, where k=9/10. Their required next-phase values, from indifference at that joint phase, are g(1-k)s/(1-s),g(1-k)r/(1-r). Since both twin rows receive the same payoffs in the X,Y phases, subtracting their recursions gives

    (1-k)(s-r)/[(1-s)(1-r)] = (1-x)(1-y)k(r-s).

Thus r=s. Indifference across each of the X and Y intervals now gives x=r/(1-r)^2, y=4r/(1+4r), using the unchanged additive passive rewards of these two players at {U,V}. The twin continuation yield at X divided by r is

    -x/r+(1-x)t y/r-(1-x)(1-y)kg,

which must equal (1-k)g/(1-r). If r<=1/8 then x/r<=64/49, 1-x>=41/49, y/r>=8/3, so the displayed quantity exceeds 3 whereas the required value is below 1. But at r>1/8, Y has native value zero just after its own date, while joining the joint date would earn -r(1-r)+8r^2>0. This excludes every proper three-date joint strategy of this form with independent, possibly unequal, twin probabilities. It makes no claim about more general joint calendars.

## Three-date equilibria across the whole interval of symmetric joining factors

Return to the symmetric singleton family in role order X,Y,U,V, now allowing arbitrary signed own levels. In this section f=t from its earlier notation; k denotes the common twin joining factor. Fix g>0 and 4f>1+2g. Define the singleton columns by the rows

    (0,-1,2,2),   (2,0,-1,-1),   (-1,f,0,-g),   (-1,f,-g,0).

Write b_i for the sum of that player's opponent singleton rewards weighted by the opponents' current hazards. Suppose i's expected native one-date absorbing payoff on continuing is b_i, with a surviving date contributing zero, and its native payoff on quitting is k_i b_i. Equivalently the passive coalition reward is the sum of the corresponding singleton entries and joining pays k_i times that sum. Take 0≤k_X≤1, 0≤k_Y≤1/2 and k_U=k_V=k anywhere in [0,1]. The game has an original uniform-equilibrium payoff. The construction also works when the reward rows agree with these formulas only on the on-path coalitions and on those reachable by one deviator in the constructed phases.

For k<1 we construct a proper three-date cycle. Only X acts at date A. At B, Y acts and each twin independently uses the same hazard v, possibly zero. At C, each twin independently uses hazard r>0. Denote the hazards of X and Y by x and y. Every player faces a positive probability of absorption by opponents alone each cycle, uniformly over unilateral replacements. At any date with opponent survival H, native payoff from continuing is b_i+H times next date's native value, while quitting pays k_i b_i. If continuing attains the prescribed value everywhere and quitting ties it at each active occurrence and never exceeds it elsewhere, iteration gives best response against all behavioral stopping rules. The residual after n cycles is bounded geometrically even under unilateral replacement. Restoring s_i gives original terminal Nash. The same uniform bound on expected absorption time gives the fixed original target for all sufficiently large finite-average horizons.

Put d=4f/(4f+g). For k≤d take v=0. The X and Y owner equalities give

    x=r/(1-r)^2,       y=4r/(1+4r).

Choose 0<r<1 with x<1 to solve

    -x+(1-x)[fy-(1-y)kgr] = (1-k)gr/(1-r).                   (1)

At r tending to zero the left side minus the right side divided by r tends to 4f-1-g>0. At the first r with x=1 the difference is strictly negative. The intermediate value theorem supplies r. X has value zero at A and B, and 4r at C. Y has value 2x at A and zero at B and C. These values give the required inequalities since k_X,k_Y lie in [0,1]. At C a twin's value is -kgr, and continuing ties exactly when its value at A is (1-k)gr/(1-r). At B its continuation is fy-(1-y)kgr and dominates the offer kfy precisely when k≤d. Equation (1) gives the value at A, which dominates the offer -kx.

For d<k<1 let a(v)=4(1-v)(1-k)/k and set

    y=g v[4-a(v)]/[g-fa(v)],
    r=(y-4v)/[4(1-y)(1-v)^2].                               (2)

The denominator of y is positive for 0≤v≤1/4 since fa(0)<g. Also 4f>g, hence 0<a(v)<4 and y>4v for v>0 on this interval. There is a first v_*∈(0,1/4) with y=1. As v increases from zero to v_*, r is continuous, starts at zero and tends to infinity. Stop at the first point where r=1. Before it set

    K=k(fy-gv),    m=(1-k)gr/(1-r),    x=(K-m)/(1+K).

Here K>0. At B a twin's quitting value K equals its continuing value precisely when (1-k)(fy-gv)=(1-y)(1-v)kgr. This identity follows from (2). At C its quitting value -kgr ties continuing iff its value at A is m, and -x+(1-x)K=m holds by definition. Equation (2) also gives X's equality 0=-y+4v+4r(1-y)(1-v)^2 at B.

To impose Y's equality, take a zero of the continuous scalar function

    E(v)=(1-r)^2[2x-(1-x)2k_Y v]-2r-2(1-k_Y)v/(1-v)^2.

There is an interior zero. At v approaching the first r=1, x grows in absolute value at most as a constant times 1/(1-r) and E tends to a strictly negative number. At zero let R be the limit of r/v, which exists and is positive and finite by (2) and fa(0)<g. Then y/v tends to 4+4R and E/(2v) tends to

    [k(4f-g)-1]+[4kf-(1-k)g-1]R > 0.

Both bracketed expressions increase with k. At k=d the second equals 4f-g-1>0, and the first is positive because, writing h=4f>1+2g, h(h-g)>(h+g). At a zero of E the term 2x-(1-x)2k_Y v is strictly positive, so x>0. Also x<1 by K>0 and m>0. All four selected hazards are proper.

At this zero Y's native values at A,B,C are 2x-(1-x)2k_Yv, -2k_Yv, and 2(1-k_Y)v/(1-v)^2. Continuing and quitting tie at B. At C the positive value dominates -2k_Y r. The value at A exceeds 2(1-k_Y)v by E=0, so x>v/(1+k_Yv). Since k_Y≤1/2 this implies (1-k_Y)x≥k_Y v(1-x), exactly the comparison to quitting for 2k_Y x at A. X has the same three values 0,0,4r as before. At B its offer k_X(-y+4v) is nonpositive, and at C its offer 4k_Xr is at most 4r. At A a twin's positive m exceeds -kx. These exhaust all decisions.

At k=1 let Y,U,V quit for sure at the first date and X continue. Each player faces a sure opponent. Each twin is indifferent, Y prefers quitting since -2k_Y≥-2, and X prefers continuing since 3≥3k_X. This yields the same uniform conclusion.

For f=17/8 and g=9/32 the switch occurs at d=272/281. The only multipliers on this singleton matrix for which a calendar with at most one mover per date can be exact, at positive own levels and interior k_i, satisfy 8/9≤k≤16/17. Thus the three dates above give exact equilibria on both sides of the interval admitting a solo calendar. A further part of the square of unequal twin factors has the same conclusion. Suppose 0≤k_U,k_V≤2f/(2f+g), while k_X,k_Y may both range independently over [0,1]. Take v=0 and let the two C hazards be a,b. Write S=a+b, a=lS and b=(1-l)S. Put

    x=S/[2(1-a)(1-b)],    y=2S/(1+2S),    A=(1-x)(1-y),
    W=(1-x)fy-x,          F_i(z)=z[(1-k_i)/(1-z)+A k_i].

For each 0≤l≤1 there is a unique positive first S_1(l) with x=1, before either hazard reaches one. This follows from strict increase on the proper interval, and S_1 varies continuously. Use the rectangle 0≤l≤1, 0≤u≤1, with S=(1-u)epsilon+u S_1(l) and sufficiently small fixed epsilon>0. On the two l sides, F_U(b)-F_V(a) has opposite strict signs. On the small-S side W-g[F_U(b)+F_V(a)]/2 has leading term (4f-1-g)S/2>0 uniformly in l. On the far side x=1 it is strictly negative. The Poincaré–Miranda theorem gives an interior zero of both expressions. Then W=gF_U(b)=gF_V(a). These are precisely the two independent twin indifference equations (1) with opponent hazards b and a respectively. The B comparison for twin i with C opponent hazard z is 2f(1-k_i)S≥g k_i z. It holds by the bound on k_i and z≤S. All other inequalities follow from the three phase values as in the v=0 proof, replacing 4r by 2S at X's C date and 2r by S in Y's waiting payoff. Thus every factor pair in this rectangle gives a uniform equilibrium.

One exact point on the upper branch has f=17/8, g=9/32, s_i=1, k_X=1/10, k_Y=1/2 and k=99/100. Since k>16/17, the unrestricted criterion above gives a positive lower bound on e+C over all behavioral profiles. Every sufficiently accurate terminal equilibrium of this particular game therefore assigns a probability bounded away from zero to a simultaneous first quit. It also escapes the passive-payoff hull orientation test. On support X,Y,U the projected singleton columns generate every strictly positive vector, since their three-by-three matrix has strictly positive inverse. The projected XUV coalition is (2/5,0,-4059/3200), and adding half the singleton Y column makes its X and U coordinates negative while leaving its Y coordinate zero. A sufficiently small addition of the U singleton makes all three negative. The positive cone of the projections is therefore the whole space and zero is interior to their convex hull with zero. At small equal positive odds on X,Y,U the forced-Quit offers are positive and the nonempty active continuation thresholds (Q-P)/H lie in that hull, tend to zero, and have derivative diag(k_i-1) times the singleton submatrix at the origin. Its signed determinant is strictly positive, the wrong sign for the weak-orientation test. The stationary and sure-opening exclusions above simplify with the triple bonus set to zero. For the staggered two-recipient test the same three admissible assignments and hazard witnesses as in the marked six-date calculation give the pairs (69/256,-69/512) and (343/1600,-637/12800), the latter twice. All these calculations concern the additive completion here. The modification of Y's triple reward to 8 in the six-date calibration is a different reward table.

## Formalization handoff

The construction proves unilateral endpoint comparisons and geometric opponent survival directly. The existing Lean declaration `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean` gives the original existence conclusion from the terminal profiles. The implemented `BalancedSingletonCycleCertificate` in `UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean` requires nonnegative passive native continues at every phase; the opposite twin's negative native continuation shows why it does not supply the marked construction. A formalization can isolate the two-step positive matrix, the compactness criterion on colored exit masses, and the scalar and rectangle intermediate-value constructions. These are ordinary mathematical results.
