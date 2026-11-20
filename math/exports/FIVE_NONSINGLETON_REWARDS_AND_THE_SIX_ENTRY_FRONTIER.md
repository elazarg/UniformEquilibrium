# Five arbitrary nonsingleton entries and the six-entry frontier

For four independent quitting players let $Z_i(S)=r_i(S)-r_i(\{i\})$ on nonempty exits and $G_{ij}=Z_i(\{j\})$. The four original own singleton rewards have arbitrary signs. There are 44 nonsingleton entries.

**Every table with at most five nonzero nonsingleton entries has an original uniform-equilibrium payoff.** Among the $\binom{44}{6}=7,059,052$ choices of six positions, all but at most 96 guarantee an original uniform-equilibrium payoff for every singleton matrix and every choice of the six numbers. The 96 are possible positions only. Even on them, the following role, sign, and size conditions are necessary for a counterexample.

Use four distinct labels $u,v,a,b$. Write $M=\{u,v\}$, $T=I-\{a\}=\{u,v,b\}$ and $C=T-\{u\}=\{v,b\}$. Both $G_{uv},G_{vu}<0$, and every other pair has a strictly positive comparison in at least one direction. The six nonzero entries must be precisely these:

| Positions | Native values |
|---|---|
| $Z_a(M+a)$ | positive |
| $Z_u(I), Z_v(I), Z_b(I)$ | all positive |
| one of $Z_a(I),Z_a(T)$ | respectively negative or positive |
| one of $Z_u(T),Z_u(C)$ | respectively negative or positive |

Set $K=Z_a(M+a)-Z_a(M)$, $L=Z_a(T)-Z_a(I)$ and $N=Z_u(C)-Z_u(T)$, all strictly positive. In addition,
$$
                         KN>(-G_{uv})L .
$$
These restrictions apply to arbitrary real singleton data, including ties.
They exclude every six-entry table with at least three ties among the twelve foreign singleton comparisons. A positive gap requires a strictly negative entry in every column by the singleton complementarity condition, and one in every row. For the latter, if a row had no negative entry, a small upward perturbation of its foreign ties would leave a positive gap and give that player a strictly positive foreign row, contrary to the normal-core reduction. The five pairs other than $M$ require five distinct positive entries. With at least three ties there is room for at most four negatives. Exactly four would have to occupy distinct rows and columns. They would define a permutation without fixed points containing the transposition $u,v$, forcing a second mutually negative pair on $a,b$. This contradicts the six-entry restrictions. Filtering the surviving singleton sign census by the same pair condition leaves eight strict sign classes, eleven one-tie classes and four two-tie classes up to relabeling (respectively 180, 264 and 96 labeled patterns). To reproduce these numbers take the existing strict census and its boundary representatives, retain each matrix with exactly one pair satisfying $\max(G_{ij},G_{ji})\le0$, and require both comparisons of this pair to be strictly negative. [Singleton sign census and negative-column condition](TWENTY_ONE_SINGLETON_SIGN_CLASSES_FOR_FOUR_PLAYER_QUITTING_GAMES.md) · [Boundary enumeration](../experiments/FIN4_SINGLETON_SIGN_CLASSES.py)


For any full table write $m_k$ for the $k$th-largest absolute native nonsingleton entry. Its infimum of maximum terminal regret is at most $2m_6$. If retaining any choice of six largest entries gives a table outside the displayed exceptions, the bound is $2m_7$. Indeed the first truncation keeps five entries and the second six, leaving all original singleton and perpetual payoffs fixed. The prescribed payoff and every unilateral offer change by at most the largest deleted magnitude, uniformly over all profiles. Thus at a positive gap $\gamma$ there must be at least six higher entries of magnitude $\gamma/2$ or larger. If there are only six, their signed projection must pass the role and size restrictions above.

**There is a positive size threshold even on the 96 exceptional supports.** For each fixed real singleton matrix (ties included), either all six-entry tables are solved or the singleton signs select one of the two outsiders to the mutually negative pair. In any six-entry counterexample that player's positive participating higher reward must exceed a positive threshold depending only on the singleton matrix, with the other five prices arbitrary. With the other five prices held fixed, this same price must also lie below a finite upper threshold. At the upper end the positive inverse column proved below gives a proper stationary equilibrium by the single-column jackpot theorem, for a triple or a grand reward as appropriate. [Single-column theorem](SIGNED_SINGLE_COLUMN_JACKPOT_UNIFORM_EQUILIBRIUM.md)

For a dense table, retain any six largest higher entries. If this projection has the required signed template, let $x$ denote the selected player's positive higher price and $c(G)>0$ the lower threshold just described. The original maximum-regret infimum is at most $2\max\{m_7,(x-c(G))_+\}$. Reduce only that price to $\min(x,c(G))$ in the six-entry projection. The resulting game has a uniform-equilibrium payoff; the two changes have disjoint supports, so the largest change at any exit is the maximum in the formula.

## First-date comparisons and the six edits

A pure first-date set $S$ of at least two quitters is a terminal equilibrium whenever no player prefers the adjacent set $S\mathbin{\triangle}\{i\}$. Each unilateral replacement still faces a sure rival at the first date, so these comparisons prove original uniform equilibrium, including signed own rewards. On the reference table with all nonsingletons zero every triple and the grand coalition meet this test. So does each pair with both singleton comparisons nonpositive. Let $m$ be the number of such pairs. A new strict improvement at a previously stable vertex needs a change in one of the two entries on its comparison edge. Different spoiled vertices require different edges, since one edge cannot give a strict improvement in both directions. A changed row entry belongs to just one comparison edge. Thus $m+4$ arbitrary changes preserve a pure equilibrium. Every strict singleton matrix of a possible counterexample has a mutually negative pair, and the same necessity holds without genericity. This proves the five-entry conclusion. [Reciprocal-negative necessity](NO_MUTUALLY_NEGATIVE_SINGLETON_PAIR_UNIFORM_EQUILIBRIUM.md)

At a six-entry counterexample we must therefore have $m=1$. Every change is on a different edge and pays for one strict exit from one of the five large coalitions or the unique pair $M$. No other change is available. A change that spoils a large coalition cannot create a positive participating pair or a positive participating triple. In fact the improvement either removes a member or adds the sole outsider to a triple. For a removal one lowers that member's payoff at the original set or raises its passive payoff at the smaller set. For an addition one raises the outsider's grand payoff or lowers its passive triple. The change spoiling $M$ cannot create a positive participating pair either. The only possible positive participating reward on a proper coalition is therefore a single positive triple reward $Z_a(M+a)$, obtained by adding outsider $a$ to $M$.

The earlier supportwise lowness theorem applies if each support of size three or four has some member whose forced quit offer is at most its native singleton zero, since there are no mutual-positive pair rewards. On any three-person support, at most one member has a positive participating reward within that support, so another member supplies the bound for every product row. On the full support the test still succeeds if any recipient has no positive participating reward anywhere. This gives native absorbing regret infimum zero and hence uniform equilibrium at every signed translation by the zero-column theorem. [Supportwise lowness](SUPPORTWISE_LOW_OR_CHARGE_UNIFORM_EQUILIBRIUM.md) · [Signed translation](ZERO_SINGLETON_COLUMN_EQUIVALENCE.md)

A possible exception needs a positive participating reward for each of the four players. The owner withdrawing from the grand coalition cannot have positive grand payoff, since its one change on that edge either lowers its own grand payoff or raises its passive triple. Thus this owner is the unique recipient $a$ of the positive participating triple. The remaining three owners must get positive grand payoffs, using exactly their three respective strict exits from $I-\{j\}$ toward $I$. The remaining triple $T=I-\{a\}$ must have a member who prefers withdrawing. This accounts for all six changes.

If this last withdrawing member is $b\notin M$, prescribe both members of $M$ to quit surely on date one. They weakly prefer quitting at each of the four pure choices of $a,b$: at the pair this is the baseline pair comparison, and at the three larger sets their joining payoffs are unchanged or increased. The two unrestricted players have a mixed equilibrium in the resulting finite two-action game, giving a full first-date equilibrium. Thus the withdrawing member must be some $u\in M$, leaving exactly the choices in the table.

Keep $u,v$ sure and $a$ quiet, and have $b$ quit independently with probability $q$. Player $b$ is indifferent and $v$ weakly prefers quitting. Player $a$ weakly prefers waiting if $q\ge K/(K+L)$, and $u$ weakly prefers quitting if $q\le (-G_{uv})/[(-G_{uv})+N]$. These intervals intersect exactly when $KN\le(-G_{uv})L$, proving the stated strict necessity. All these profiles absorb immediately under every unilateral replacement.

For signed or unsigned positions, choose the ordered labels in $4!$ ways and choose either implementation of each of the last two lines, giving 96 distinct supports. If there are three grand positions, the missing grand owner identifies $a$. If there are four, $a$ is the unique recipient of the participating triple when the remaining changed proper entry is passive. When both proper entries are participating triples, the two arrows from recipient to the omitted label form the directed path $u\to a\to b$, which identifies the roles. In the three-grand cases the changed proper entry of recipient $a$ on $M+a$ identifies $b$, and the other withdrawal entry identifies $u$. The distinguished reciprocal pair must be strictly negative in both directions even at a tie: a surviving signed table would persist at all sufficiently close strict singleton refinements with the same six higher rewards. Each such refinement must have that same pair as its unique mutually negative pair. A zero within it, or a second pair with both entries nonpositive, is inconsistent with this requirement. [Strict census and perturbation](TWENTY_ONE_SINGLETON_SIGN_CLASSES_FOR_FOUR_PLAYER_QUITTING_GAMES.md)

The counting and reduction also apply around any reference assigning the same constant $d_i\le0$ to all eleven nonsingleton rewards of row $i$, whenever at least one pair qualifies by $d_i\ge G_{ij}$ and $d_j\ge G_{ji}$. Count changes from these row constants. The proof above uses only that unchanged participating rewards are nonpositive and that the reference comparisons on edges between larger coalitions are tied. With $m$ qualifying pairs, $m+4$ changes preserve a pure equilibrium. At six changes with $m=1$ the same 96 positions and roles are necessary. The four positive participating rewards in the table must exceed native zero. The two withdrawal changes lower the participant below its row constant or raise the passive reward above its row constant. The size inequality becomes $KN>(d_u-G_{uv})L$, using the same actual payoff differences. The unconditional all-matrix assertion at the start uses $d_i=0$.

## Seven higher rewards and a signed test at every support size

Of the $\binom{44}{7}=38,320,568$ sets of seven higher positions, **at least 38,288,940 guarantee an original uniform-equilibrium payoff for every assignment of their values and all singleton rewards**. The other 31,628 sets pass the following necessary conditions for some signs and some choice of the mutual pair. For a specified pair at most 6,644 sets pass. The test itself applies to any number of nonzero rewards.

For a possible counterexample choose a strictly mutually negative singleton pair $M$. A signed higher entry $(i,S)$ can witness damage to exactly one reference vertex: $S$ for a negative entry and $S\mathbin{\triangle}\{i\}$ for a positive entry. Its comparison edge is $\{S,S\mathbin{\triangle}\{i\}\}$. Three simultaneous requirements on the *same signed entries* are necessary.

1. Each of $M$, the four triples and the grand coalition has a signed witness at its vertex, on six distinct comparison edges. All six vertices start as pure equilibria on the zero-higher reference. A strict gain after changing their payoffs needs a change in the indicated direction on that edge. Opposite ends of the same edge cannot both gain strictly from flipping along it.
2. There is a coalition $A$ of size two or more such that every $i\in A$ has a positive entry $Z_i(S)$ with $i\in S\subseteq A$ and $|S|\ge2$. Otherwise there is no mutually positive participating pair; on each larger support at least one member has a nonpositive native quit offer for every choice of hazards. The supportwise-low theorem and signed translation give uniform equilibrium.
3. Some $i\in M$ has a negative participating entry $Z_i(S)$ or a positive passive entry $Z_i(S-\{i\})$ for some $S\supseteq M$. Without such an entry both members of $M$ weakly prefer quitting when the other is sure, for all four choices of the outsiders' actions. At the reference this follows from their mutually negative singletons at $M$ and equality at larger sets. With both sure, a Nash equilibrium of the outsiders' finite two-player game then gives an original equilibrium.

The [position checker](../experiments/SEVEN_REWARD_POSITIONS.py) fixes $M=01$, enumerates the witnesses of requirement 1, and adds each possible signed seventh entry not already used. It retains the unsigned positions if the same signs meet requirements 2 and 3. This is exhaustive because any signed table satisfying the requirements can supply the first six witnesses, with exactly one position left over. The computation yields 16 sets of six and 6,644 sets of seven for $M=01$. Relabeling this pair in six ways and taking the union gives 96 and 31,628 respectively. A passing set need not admit any counterexample.

There is also a magnitude test on a dense table. Fix $t\ge0$ and retain only the higher entries of absolute value greater than $t$, preserving all singletons. If the resulting signed positions fail the three requirements for every strictly mutually negative pair, the original maximum-regret infimum is at most $2t$. Indeed the truncated game has a uniform-equilibrium payoff and every prescribed or replacement payoff changes by at most $t$. In particular, retaining a choice of seven largest higher rewards outside the 31,628 sets improves the earlier bound to $2m_8$. The same argument applies when the positions pass but their signs or their actual singleton pairs fail the test.

## The first possible support size in each singleton class

Fix the labeled singleton signs. Let $H$ consist of the pairs $ij$ with $G_{ij},G_{ji}\le0$ and put $k=|H|+5$. Fewer than $k$ nonzero higher entries leave a protected pure opening, as proved above. At exactly $k$ there are also the following support exclusions. The class numbers use the strict singleton census. Each count is an upper bound on the number of labeled sets of $k$ positions that can contain a counterexample at a fixed labeled singleton sign pattern in the indicated class.

| Strict class | $k$ | Surviving position sets |
|---|---:|---:|
| 6, 8, 15–19, 21 | 6 | 16 |
| 3 | 7 | 359 |
| 12 | 7 | 403 |
| 11, 13 | 7 | 419 |
| 1, 5 | 7 | 435 |
| 7, 14, 20 | 7 | 608 |
| 2 | 8 | 5,809 |
| 10 | 8 | 8,668 |
| 4 | 8 | 8,684 |
| 9 | 9 | 110,124 |

The same test works on tied signs. In the five tied classes with $k=9$, it leaves 101,456 sets in the one-tie class, between 92,788 and 93,396 in the three two-tie classes, and 85,550 in the three-tie class. The checker reports counts for every strict class and ranges by support size in each boundary stratum. [Singleton census](TWENTY_ONE_SINGLETON_SIGN_CLASSES_FOR_FOUR_PLAYER_QUITTING_GAMES.md) · [Exact integer enumeration](../experiments/MINIMUM_HIGHER_SUPPORTS_BY_CLASS.py)

To prove the exclusion, a positive gap requires a strictly positive comparison in every row and a strictly negative comparison in every column. Thus a triple contains at most two pairs of $H$. Otherwise the three members' positive comparisons would all come from its outsider, contradicting the negative comparison in that column. At $k$ edits each protected pair, triple and grand coalition $S$ must have exactly one improving flip $S\to S\mathbin{\triangle}\{i\}$. Their edges are distinct. The changed entry either lowers the origin or raises the destination. No positive participating pair payoff can occur. A positive participating payoff at a triple can only come from adding its owner to a protected pair there. Hence every proper support has a member with no positive participating higher reward on that support. By supportwise lowness, a surviving table must therefore give **every owner** a strictly positive participating triple or grand reward.

Each owner with $Z_i(I)\le0$ therefore needs a *distinct* protected pair omitting that owner, from which its addition creates its positive triple reward. In particular at least $4-|H|$ grand rewards must be positive. In class 9, if all four grand rewards are nonpositive, the protected pairs form a four-cycle. The bipartite graph connecting these pairs to their omitted owners is an eight-cycle. Its two perfect matchings assign exactly one positive participant to each of the four triples. Indeed labeling the cycle vertices $v_j$ modulo four, the two assignments add $v_{j+2}$ to every edge $v_jv_{j+1}$ or add $v_{j+3}$ to every such edge. In this case the physical row selected by the positive participant-surplus escape theorem must mark a triple. Its designated recipient's gain above its own singleton exceeds the sum of the other members' losses plus twice the total-debt infimum of the escape table. This conclusion uses the theorem's participant inequality on the actual row and is preserved by the signed translations that keep centered exit rewards fixed. [Physical participant inequality](ONE_ESCAPE_OBLIGATION_FOR_ARBITRARY_FOUR_PLAYER_GAMES.md#1-the-source-coalition-and-its-physical-row) · [Same native rewards under signed translation](PRESCRIBED_SIGNS_AND_NATIVE_LIMITS_OF_FOUR_PLAYER_ESCAPE.md)

There is an exact magnitude test for full-support product-lowness on this branch. Denote owner $i$'s positive triple by $T_i$, its reward by $P_i>0$, and its omitted label by $o_i$. All participating pair rewards are zero, since all four pair edits create the four premiums. With full-support hazards $q_j$ and inverse odds $y_j=(1-q_j)/q_j$, the native forced quit offer divided by $\prod_{j\ne i}q_j$ equals $Z_i(I)+\sum_{j\ne i}Z_i(I-\{j\})y_j$. Each $T_i$ has at most one negative participating payoff, given by a withdrawal at $T_i$ implemented by lowering its owner's entry there. If that owner is $j(i)$ and the loss is $L_i$, draw $i\to j(i)$ with weight $L_i/P_i$. Since the $o_i$ are distinct, the variables $x_i=P_i y_{o_i}>0$ are independent. All four offers can be positive exactly when $x_j>\sum_{i:j(i)=j}(L_i/P_i)x_i$ is feasible: the nonpositive grand terms can only tighten these inequalities, and scaling a strict solution absorbs their finite magnitudes. This system is feasible exactly when every directed cycle has product strictly below one. Indeed a strict positive supersolution bounds the nonnegative matrix's spectral radius below one, and when that radius is below one the geometric matrix series applied to the all-ones vector gives a strict supersolution. A graph with at most one outgoing edge per vertex has only cycle blocks and acyclic singleton blocks in its decomposition into strongly connected components. Thus **any cycle of product at least one gives an original uniform-equilibrium payoff** by product-lowness on all supports. After the face test below, this branch has 7,200 signed supports on 7,192 different sets of positions. Of the signed supports, 6,256 are acyclic; 608, 304 and 16 have a single cycle of lengths two, three and four respectively; 16 have two cycles of length two. The count records only the positions and signs.

Form the directed graph of strict one-date improvements on nonempty coalitions, retaining only moves to another nonempty coalition. At the protected vertices these are precisely the assigned arrows. At each other pair $ij$ only members with positive $G_{ij}$ or $G_{ji}$ improve by withdrawing. At singleton $i$, a rival $j$ improves by joining exactly when $G_{ji}<0$ and the pair $ij$ has no assigned arrow withdrawing $j$. These rules follow because each changed comparison edge has its strict gain at its protected origin and all other edges keep their reference comparisons.

Consider a face of the four-dimensional action cube with a nonempty set of fixed quitters and any disjoint set of fixed waiters. If all its improvement arrows stay in the face, take a mixed Nash equilibrium of the free players' one-date game. Every fixed player weakly prefers its prescription at each pure vertex of the face, for comparisons between nonempty outcomes. With a unique fixed quitter $i$ a withdrawal can also leave the opening blank. Have a rival $j$ with $G_{ij}<0$ quit alone on date two following a blank. The comparison with this continuation is valid because $i$'s best reply there is bounded by $\max(G_{ij},Z_i(ij))\le0=Z_i(i)$. Every player faces absorption within two dates under any unilateral deviation, so restoring the signed own levels gives an original uniform-equilibrium payoff. A counterexample must have no such face.

The checker assigns one owner to each protected vertex, discards opposite arrows on a common edge, and tries the possible reward edits on each remaining arrow. It requires a positive participating entry for every owner and tests all faces with a fixed quitter. In class 9 the positive-participation and edge tests leave 162,776 unsigned supports. Faces with at least two fixed quitters reduce that number to 111,864. Allowing one fixed quitter gives the table's 110,124 out of $\binom{44}{9}=708,930,508$. For a dense table, if the positions of a choice of $k$ largest absolute native higher rewards fail this check, truncation bounds the original maximum-regret infimum by $2m_{k+1}$, with $m_j$ as defined above.

### The same position counts around nonzero reference rewards

Fix the actual singleton matrix $G$. Give row $i$ a reference payoff $p_{ij}\le0$ at the pair $ij$, with $\operatorname{sgn}(G_{ij}-p_{ij})=\operatorname{sgn}G_{ij}$. For each $T\subseteq I\setminus\{i\}$ of size at least two, give $i$ the same reference payoff $d_{i,T}\le0$ at $T$ and $T\cup\{i\}$. Now count positions that differ from this reference. **Every exclusion in the preceding table of position counts applies without change.** With strict singleton signs there are twelve independent choices of $p_{ij}$ and sixteen independent choices of $d_{i,T}$. They can all be strictly negative. Consequently these guarantees include tables where all 44 higher rewards are nonzero.

Indeed the reference has the same strict improvement graph on nonempty coalitions as the zero reference. A single changed position still affects just one comparison edge. At the first possible size, each improvement from a protected vertex needs its own edit on its own edge. Only an upward arrow with a raised participating destination can create a positive participating reward. Starting all higher entries nonpositive therefore gives exactly the same necessary owner-coverage test. The second-date punishment still applies because participating pair rewards remain nonpositive whenever every protected vertex has been spoiled with exactly one edit each. For the bound of $k-1$ edits using only pure vertices, all sixteen common levels $d_{i,T}$ can even have arbitrary signs, since only payoff differences enter that proof.

This gives a computable regret bound for tables away from these references. Fix a set $E$ of free positions, either of size less than $k$ or of size $k$ excluded by the position test. For each pair reward outside $E$ take its distance to the allowed interval of $p_{ij}$ above. For a pair of positions sharing $d_{i,T}$, omit positions in $E$. If both remaining values are $x,y$, take $\max\{|x-y|/2,x,y,0\}$. With just $x$ remaining take $\max(x,0)$, and with none take zero. If the largest of these distances is $t$, the infimum of unrestricted maximum terminal regret is at most $2t$. Indeed each common-level expression is the best sup-norm approximation of its entries by one nonpositive number. Each $p_{ij}$ can likewise approach its distance independently, including at an open interval endpoint. Keep the free entries at their original values and approximate all other entries this way. Every resulting table has a uniform-equilibrium payoff, and changing terminal rewards by at most $t+\varepsilon$ changes each prescribed or deviation payoff by at most $t+\varepsilon$. Taking $\varepsilon\downarrow0$ proves the bound. One may minimize it over the eligible sets $E$.

### Nine entries are sharp for nonstationarity on the positive matching

There is a class-9 game with an original uniform-equilibrium payoff in which every sufficiently accurate equilibrium has a simultaneous first exit of uniformly positive probability on one date and every stationary profile has regret bounded away from zero. It has exactly nine nonzero native higher entries, the fewest possible in this class by the protected pure openings above. All nine are positive and every native grand reward is zero.

Take mates $01,23$. Pay $G_{ij}=a>2$ to a mate and $-1$ to a crossed recipient; take all original own singleton levels equal to one. Set the following entries to one, with all other native higher entries zero:

| Owner | Positive participating triple | Positive passive rewards |
|---|---|---|
| 0 | 013 | 12 |
| 1 | 012 | 03, 023 |
| 2 | 023 | 13 |
| 3 | 123 | 02 |

**An exact equilibrium.** Alternate the active pairs $02$ and $13$. Use hazard $p$ for players 0 and 1 at their active dates and $q$ for 2 and 3. Write $X=p/(1-p)$, $Y=q/(1-q)$, $D=(1+X)(1+Y)$. Each active owner's quit offer is zero. The quiet owner from pair $01$ receives $(aX-Y)/D$ if its next active value is zero, and the quiet owner from $23$ receives $(-X+aY+XY)/D$. An active owner faces its crossed rival, so active indifference asks that these quiet values equal $Y$ and $X$, respectively. Equivalently,
\[
 aX=Y(1+D),\qquad aY=X(2+X(1+Y)).
\]
Set $X=Y(2+Y)/(a-Y(1+Y))$. On $0<Y$ with positive denominator, $(X/Y)(2+X(1+Y))$ increases continuously from $4/a$ to infinity. It equals $a$ at an interior point. The quiet $01$ owner can get $pq<Y$ by quitting; the quiet $23$ owner's quit offer is $0<X$. Thus the displayed values verify all four best replies. Against every unilateral replacement a rival hazard stays positive in each phase. Iterating the two-date value equations therefore verifies full terminal optimality and uniform convergence to the target $(1,1+Y,1,1+X)$ starting at $02$.

**Sure openings.** All participating native rewards are nonnegative, so a deviating unique sure owner can secure at least zero after a blank by quitting next. Thus every sure opening would satisfy the finite stage comparisons with blank payoff zero. In each case below $x_i$ is the finite quit odds of an owner who is not sure; the comparisons use the sign of the quit-minus-wait numerator after division by the probability that every nonsure rival waits. A nonsure player's numerator must be nonpositive, and must be zero at positive odds.

With sole sure 0, 1, or 3, the respective players 2, 3, or 0 have numerators $1+x_3$, $1+x_2$, or $1+x_1$, forcing a second sure owner. With sole sure 2 the three outsider numerators (in order 0, 1, 3) are $1-x_1$, $1+x_0-x_0x_3$, $-x_0+x_1-a$. The first forces $x_1>0$, so the second vanishes and forces $x_0>0$, $x_3>1$. Then $x_1=1$ and the third is negative, contradicting $x_3>0$.

For exact sure set $01$ the two sure inequalities require $x_3-x_2\ge a$ and $x_2-x_3-x_2x_3\ge a$. At $23$ they require $x_0-x_1\ge a$ and $x_1-x_0\ge a$. At $02$, outsider 3 strictly waits, then 1 strictly prefers quitting. At $03,12,13$, respectively 2, 3, 0 strictly prefers quitting. At sure triples $012,013,023,123$, respectively 0, 1, 3, 2 strictly prefers waiting whenever the fourth player is nonsure. At the grand coalition 1 strictly prefers waiting.

**Positive stationary regret gap.** For proper stationary hazards with at least two positive entries, put $x_i=q_i/(1-q_i)$ and $D_i=\prod_{j\ne i}(1+x_j)$. Let $V_i$ be the product of the two rival odds at $i$'s premium triple and $U_i$ the product of the rival odds at its positive passive pair. The rival nonempty passive payoff minus the rival exit probability times the immediate quit offer, multiplied by $D_i$, is
\[
 F_i=(Gx)_i+U_i+\mathbf1_{i=1}x_0x_2x_3-(1-D_i^{-1})V_i.
\]
A positive proper hazard requires $F_i=0$. The four $U_i$ and four $V_i$ list the same four monomials, so
\[
 \sum_i F_i=(a-2)\sum_i x_i+x_0x_2x_3+\sum_i V_i/D_i>0.
\]
This excludes four active owners. With three active, the unpaired owner's mate is absent; its higher monomials vanish and its two crossed singleton terms are negative. With two active, either both strictly prefer the mate's singleton over quitting or both prefer quitting against their crossed rival.

For completeness, consider any stationary sequence with regret tending to zero. A limit with at least two positive hazards faces positive rival exit probability in each row, making prescribed payoffs and pure reply endpoints continuous, so it would give one of the excluded exact profiles. A single positive limiting hazard gives a crossed outsider a strict gain from joining. If all hazards vanish, the all-zero profile itself has unit regret. Otherwise normalize by their sum and pass to a limit $d$ in the simplex. With at least two positive hazards along the sequence, the native prescribed payoff tends to $(Gd)_i$; immediate quitting has limit zero. For $0<d_i<1$ the native Never payoff tends to $(Gd)_i/(1-d_i)$, so vanishing regret forces $(Gd)_i=0$. All rows must have $(Gd)_i\ge0$. A unit vector $d$ has a negative crossed row, which also excludes sequences with only one positive hazard. Hence $d$ would be homogeneous complementary. Full support is impossible since $\sum_i(Gd)_i=a-2>0$. A triple has an unpaired negative active row, and a pair has a nonzero active comparison. This excludes every limit.

Finally, the same homogeneous test and the absence of opposite strict signs on any reciprocal pair preclude every continuous singleton path: a switch $i\to j$ requires $G_{ji}\ge0\ge G_{ij}$ with a strict sign. The triple principal blocks are nonsingular (their determinant is $2a$), the full block is nonsingular for $a>2$, and every participating pair pays native zero. In fact immediate quitting guarantees at least the own singleton on every row because all participating rewards are native nonnegative. The physical collision-floor theorem therefore applies with the positive own levels, including for profiles with isolated solo dates. [Singleton path test](ALL_FOUR_PLAYER_SINGLETON_PATHS_HAVE_A_FINITE_TEST.md) · [Uniform collision mass on one date](GENERIC_FOUR_PLAYER_SINGLETON_PATH_CLASSIFICATION.md)

## All sure openings on the residual template

On the six-position, zero-reference template above, suppose $G$ has strict off-diagonal comparisons, a negative entry in every column and a weak blocker in every row. Write $R_i=Z_i(I)>0$ for $i=u,v,b$, $m=-G_{uv}$, and $m_v=-G_{vu}$. For $KN\le mL$ the preceding square already works. For $KN>mL$, there is no equilibrium opening with two or more sure quitters. A unique sure quitter exists exactly when one of the following scalar tests succeeds. This concerns openings followed by unrestricted private clocks, so a positive test gives an original uniform equilibrium.

* For sure $v$, require $G_{bv}>0$, and put $B=G_{bv}/R_b$. There is a unique $0<Y<N/R_u$ satisfying
  $$
  \frac{m}{N-R_uY}=\frac{K}{L}-\frac{G_{av}Y}{LB}.
  $$
  Put $X=B/Y$, $Z=m/(N-R_uY)$. The test is $m_v X-G_{va}Y-G_{vb}Z+R_vXYZ\ge0$.
* For sure $b$, require $G_{ab}<0<G_{vb}$ and put $C=-G_{ab}/L$, $D=G_{vb}/R_v$. Test the at most two positive roots of
  $$
  -G_{ub}X^2-N C X+R_u C D=0 .
  $$
  At least one must satisfy $-G_{bu}X^2-G_{bv}C-G_{ba}D+R_b C D\ge0$.

To verify exhaustiveness, at a sure set of three players other than $T$, the missing owner strictly wants its positive grand reward. At $T$ the outsider $a$ strictly waits and $u$ withdraws. The grand coalition itself loses $a$. Consider exactly two sure owners. If they are $a$ and another owner, the two others must both wait: either's positive probability of quitting would give the other a strict gain from its grand reward, since its joining advantage at the smaller set is zero. At the resulting pair at least one sure owner prefers its rival's singleton. On $\{u,b\}$, positive $a$ would force $v$ to quit surely, so $a$ waits. With positive probability $v$ waits too. Owner $b$ withdraws if $G_{bu}>0$, since its joining advantage when $v$ quits is zero. Otherwise $G_{ub}>0$ and $u$ would withdraw whether $v$ waits or quits (its gains are $-G_{ub}$ and $-N$). On $\{v,b\}$, positive $u$ forces $a$ to wait, since its gains facing $vb$ and $uvb$ are respectively zero and $-L$. This in turn makes $u$ strictly wait. Thus $u$ waits; either $v$ or $b$ strictly prefers its rival's singleton on the event that $a$ waits and is indifferent when $a$ quits. For $M$ itself, positive $a$ would make $b$ quit surely. When $a$ waits the necessary and sufficient inequalities on $b$ are the two square inequalities already proved.

A unique sure $a$ would have a rival facing a negative $a$ singleton and this rival's joining advantage is nonnegative against all larger sets containing $a$. Since the singleton has positive probability this rival must also quit surely. Likewise sure $u$ forces its mutually negative partner $v$ to join. With sole sure $v$, use odds $X,Y,Z$ for $u,a,b$. After dividing each first-date gain by its positive opponent-wait factor, their respective gains are
$$
 m-NZ+R_uYZ,\qquad -G_{av}+KX-LXZ,\qquad -G_{bv}+R_bXY .
$$
Each must be nonpositive, with equality for every positive odds coordinate. The first implies $Z>0$, hence the third is zero. Strict singleton signs force $G_{bv}>0$ and $X,Y>0$. All three gains vanish and give the displayed equation for $Y$. Its left side minus right side is strictly convex, negative at zero since $KN>mL$, and tends to positive infinity at the upper endpoint, so its positive root is unique.

With sole sure $b$ let $X,V,Y$ be the odds of $u,v,a$. The gains for $a,v,u$ are respectively
$$
 -G_{ab}-LXV,\qquad -G_{vb}+R_vXY,\qquad -G_{ub}-NV+R_uVY .
$$
If $G_{ab}>0$, then $Y=0$, so the second inequality forces $G_{vb}>0$ and $V=0$. The third forces $G_{ub}>0$ as well, contradicting a negative entry in column $b$. Thus $G_{ab}<0$, requiring $X,V>0$, and the second equality then forces $G_{vb}>0$, $Y>0$. Substitution of $V=C/X$, $Y=D/X$ yields the displayed quadratic.

For either candidate the sure owner $i$ has nonnegative native payoffs on all coalitions in which it participates. After a blank, its exact minimal possible reply cap is zero: it can immediately quit for a nonnegative payoff, while having a weak blocker $k$ quit alone on the following date, all others strictly later, bounds all its replies by $\max(0,G_{ik})=0$. Hence its exact timed incentive is the stated final inequality, comparing quitting and waiting with that zero continuation. Each other owner faces a sure rival on the first date, so its stage action comparisons suffice. Finite punishment clocks and first-date absorption give an exact terminal equilibrium against every unilateral replacement, valid also after signed row translations.

## A three-date equilibrium on the six-entry frontier

Label the unique mutually negative pair $M=01$, let $a=2$ be the owner with the positive reward $K=Z_2(012)$, and let $b=3$. Either mate may make the final withdrawal. Throughout this section the other five edits in the six-position template have arbitrary magnitudes and either permitted implementation.

Suppose $G_{03},G_{13},G_{32}>0$, $G_{23}<0$, and that positive masses $(X,U,Y,Z)$ satisfy
$$
G(X,U,Y,Z)^\top=\delta e_2,\qquad \delta>0 .
$$
For invertible $G$ this last condition just tests the signs of its column $G^{-1}e_2$. Put $D=G_{20}X+G_{21}U=\delta-G_{23}Z>0$, $\rho=-G_{23}Z/D\in(0,1)$, and choose the unique $P>0$ with
$$
 XU=P\left[Y+Z+\frac{\rho}{1-\rho}(X+U+Y+Z+P)\right].
$$
Then **$KP\le D$ gives an exact periodic equilibrium for every signed row translation**. Rescaling the four singleton masses rescales $D$ and $P$ equally.

Use the three successive dates $01,2,3$, where only the named players may quit. Assign the first cycle unnormalized singleton exit masses $X,U,Y,Z$ and joint exit mass $P$ on $01$. Multiply all masses by $\rho$ on each later cycle. Divide by the total remaining mass at each date to obtain its probabilities. At the joint date the blank mass is the quantity inside the brackets above. The equation for $P$ is exactly the independence identity for the two binary actions, and its right side increases strictly from zero to infinity. Thus the masses specify genuine private hazards.

The zero rows of $G(X,U,Y,Z)^\top$ give the two mates value zero on date $01$, and player 3 value zero there and on its own preceding date. The equation $G_{23}Z+\rho D=0$ gives player 2 value zero on its date and the subsequent date of player 3. Every mover's forced quit payoff is also zero. At the joint date player 2's prescribed value and its quit offer, multiplied by the remaining mass, are $D$ and $KP$. At the date of player 2, the two mates have strictly positive weighted values $G_{02}Y+G_{03}Z=-G_{01}U$ and $G_{12}Y+G_{13}Z=-G_{10}X$, while player 3 has $G_{32}Y>0$. Both mates have positive value on player 3's date. All remaining quiet quit offers are zero. None of the other five changed entries affects these comparisons, since there is no date with three possible quitters and the only possible pair is $01$. Every unilateral deviation faces a recurring rival, so the local comparisons iterate to the complete stopping law, including Never. This gives the signed uniform payoff as well. The earlier attached-pair construction uses the same phase order and assumes that all six offers for either solo player joining the joint phase are nonpositive. Here the continuation on that phase funds a strictly positive offer. [Earlier attached-pair theorem](ATTACHED_NEGATIVE_PAIR_COMPLEMENTARY_SOLO_UNIFORM_EQUILIBRIUM.md)

Exactly eight of the 21 integer calibrations in the sign census have a unique mutually negative pair. In the labels of each listed matrix, $M=01$ and the displayed assignments use $a=2$. The table gives exact masses at $Z=1$.

| Census witness | $X$ | $U$ | $Y$ | $\rho$ |
|---|---:|---:|---:|---:|
| 6 | 1 | 1 | 1 | $1/2$ |
| 8 | 1 | 1 | 1 | $1/3$ |
| 15 | $5/2$ | $1/2$ | $3/2$ | $2/9$ |
| 16 | 1 | 1 | 1 | $1/2$ |
| 17 | $7/4$ | $5/4$ | $3/4$ | $4/9$ |
| 18 | $8/5$ | $4/5$ | $6/5$ | $5/6$ |
| 19 | 1 | 1 | 1 | $1/2$ |
| 21 | $11/5$ | $7/5$ | $3/5$ | $5/9$ |

Direct multiplication gives the three zero rows and the positive axis entry for each witness. Since all eight matrices are invertible, every strict $KP<D$ persists throughout a neighborhood of its singleton matrix, with all other five edit sizes still free. [Exact integer singleton witnesses](../experiments/FIN4_SINGLETON_SIGN_CLASSES.py)

For example witness 18 has rows $(0,-1,-1,2),(-2,0,1,2),(1,1,0,-2),(-1,-1,2,0)$. Here $125P^2+630P-32=0$, giving
$$
 0<K\le\frac{3(63+\sqrt{4129})}{8}.
$$
For an instance strictly inside this interval take $u=0,v=1$, $K=2$, $L=N=1$, $R_u=1$ and $R_v=R_b=1/10$. Fix either implementation of each withdrawal. The two-sure test fails since $KN=2>(-G_{uv})L=1$. The sole-$v$ test fails at $G_{bv}=-1$. For sole $b$ the unique positive solution of $2X^2+2X-40=0$ is $X=4$, and its required gain numerator is $16+2-40+4=-18$. Thus all sure openings fail. The only mutually negative pair is $01$ and its triple joining offer $K$ is positive, so every relabeling fails the earlier attached-pair caps. The full-support product-low test also fails. Indeed proper hazards with the hazard of 2 sufficiently near one and that of 3 sufficiently near zero make all four native forced quit offers strictly positive. The new periodic certificate does not require a verdict on mixed stationary equilibria.

### A positive axis throughout all six-entry sign chambers

In the labels of the three-date theorem, suppose
\[
 G_{01},G_{10}<0,\qquad G_{03},G_{13},G_{32}>0>G_{23},
 \qquad \min(G_{02},G_{12})<0 .
\]
These strict comparisons hold in a suitable labeling throughout all eight strict, eleven one-tie and four two-tie singleton sign orbits in the six-entry census. Other comparisons may be zero. At every such matrix, either every higher-reward completion already has an original uniform-equilibrium payoff, or $\det G>0$ and $G^{-1}e_2>0$ entrywise.

Indeed if any completion fails, the singleton minimum map is $R_0$ of degree one and $\det G>0$. Its nonzero degree at target $e_2$ gives $x\ge0$, $Gx\ge e_2$, $x\cdot(Gx-e_2)=0$. The degree carries to this possibly nonregular target because the $R_0$ condition bounds all zeros uniformly over any bounded target homotopy. A solution omitting 2 would be nonzero and homogeneous complementary, contrary to $R_0$. The singleton support $\{2\}$ cannot pay its positive target. For a pair containing 2, its other member $i$ must have $G_{i2}=0$. Thus $i$ is a mate, and the other mate dislikes both $i$ and 2, violating its inactive inequality. Triple $012$ cannot balance the mate who dislikes 2, since it also dislikes the other mate. These arguments do not require nonsingularity of principal triples.

If the support is $i,2,3$ with $i$ a mate, scale $x_2$ to one and write the other occupied masses as $X=x_i/x_2$, $Z=x_3/x_2$. The active equations give $G_{3i}X=-G_{32}$, $G_{i3}Z=-G_{i2}$ and $G_{2i}X+G_{23}Z>0$. The directed singleton cycle $i,2,3$ therefore has masses proportional to $(X,1,Z)$ and tour ratio $\rho=-G_{23}Z/(G_{2i}X)\in(0,1)$. Its active zero conditions follow successively from those three equations. Its quiet mate $o$ has initial unnormalized tail $A=G_{oi}X+G_{o2}+G_{o3}Z\ge0$ by the inactive inequality. Removing the first phase's negative term raises this tail. Before the last phase its value is $\rho A+(1-\rho)G_{o3}Z>0$. This verifies each phase and gives an actual uniform equilibrium for every completion by the singleton path theorem. Hence at a failed completion the solution has full support and equals $G^{-1}e_2$. [Positive determinant and source conditions](FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md) · [Degree](UNIVERSAL_REDUCED_SINGLETON_DEGREE.md) · [Singleton paths](ALL_FOUR_PLAYER_SINGLETON_PATHS_HAVE_A_FINITE_TEST.md)

In particular the three-date theorem applies throughout these twenty-three sign chambers in the assignment $a=2,b=3$. At any singleton matrix lacking the uniform conclusion for every completion, the positive masses in its four-by-four linear system are automatic. Its positive threshold $K_*(G)=(G_{20}X+G_{21}U)/P$ gives an original uniform-equilibrium payoff for every $0<K\le K_*(G)$, with all five remaining prices independent and unrestricted, either withdrawal owner, either implementation of either withdrawal, and arbitrary own levels. The threshold depends only on singleton data and is invariant under a common rescaling of the axis masses.

The count uses the previously verified singleton census. For each eligible ternary sign orbit in each stratum, try the 24 assignments to the labels in the displayed inequalities. All eligible orbits pass, giving respective counts $8/8$, $11/11$, $4/4$. At least one valid assignment has $G_{02}<0$ by swapping the mates.

### An exact three-date equilibrium with two different triple dates

Take $a=2,b=3$ in the six-entry template. Write $u$ for the mate owning the $N$ withdrawal and $v$ for the other mate. For every eligible strict or tied singleton matrix and both choices of withdrawing mate there is a constant $c_0>0$ depending only on singleton data with the following consequence. The original game has a uniform-equilibrium payoff whenever $K\le K_*(G)$ or
\[
 R_b\le c_0\min(A_L,A_N),\quad
 A_L=\begin{cases}K & \text{negative participating }L,\\
 \min(K,\max(K^{3/4},K^{4/3}/L^{1/3})) & \text{positive passive }L,\end{cases}
 \qquad A_N=\begin{cases}+\infty&G_{bv}<0,\\ K^{3/2}/N&G_{bv}\ge0.\end{cases}
\]
Neither positive grand $R_u,R_v$ enters the comparison, and either implementation of $N$ is allowed. In particular a sufficiently small $R_b$ alone suffices independently of the other five prices if $G_{bv}<0$. This covers both choices of withdrawing mate throughout the strict chambers of witnesses 6, 15 and 18, and one choice in each other strict six-entry chamber.

Use the positive axis from the earlier reduction and normalize it as $(\xi,\upsilon,\omega,1)$ in the order $u,v,a,b$. Write $G_{uv}=-m,G_{vu}=-n,G_{ua}=-e,G_{va}=-f,G_{ub}=c,G_{vb}=d,G_{au}=h,G_{av}=i,G_{ab}=-j,G_{bu}=-k,G_{bv}=-l,G_{ba}=g$. Thus $c,d,g,j,m,n>0$, while the remaining letters need not be positive. Put $D=h\xi+i\upsilon$ and $\Delta=D-j>0$. On the unresolved branch $K\ge K_*=D/P$ and $L<KN/m$. In the earlier three-date formula $\sigma=P/(\xi\upsilon)$ solves
\[
 \Delta=[D(1+\omega)+j(\xi+\upsilon)]\sigma+j\xi\upsilon\sigma^2.
\]

Consider a repeating calendar with successive dates $\alpha=(u,v,a)$, a solo $b$ of probability $S$, and $\beta=(u,v,b)$. First consider the limiting case with an empty $\beta$ date and $R_b=0$. Take odds $(\xi S,\upsilon S,\omega S)$ on $\alpha$. The two mates' values at $\alpha$ vanish, and $b$ receives zero there by its balanced axis row. The indifference equation of $a$ is
\[
 K\xi\upsilon S^2\frac{1+\xi+\upsilon+\xi\upsilon S}{(1+\xi S)(1+\upsilon S)}=\Delta .\tag{1}
\]
The left side increases strictly from zero to infinity. At its root the waiting guard of $a$ on the solo $b$ date is $K\xi\upsilon S^2\ge DS$. Substituting (1) gives $S\le S_c$, where $\Delta=[D+j(\xi+\upsilon)]S_c+j\xi\upsilon S_c^2$. Thus $\sigma<S_c<1$ and $K_*>D/(\xi\upsilon S_c)$. At every $K\ge K_*$ the solution of (1) gives a strict guard and $S<1$.

Now fix a small constant $\delta>0$ depending only on $G$. We will take $0<s\le\delta S$, with $s\le\delta/N$ also imposed if $l\le0$. We prescribe $s$ as the actual value of the quiet $b$ at $\alpha$. On $\beta$ use odds $(U,V,B)$ given by
\[
 U=dB/n,\qquad V=cB/(m-NB),\qquad kU+lV=s,\qquad 0<B<m/N .
\]
The final left side equals $(kd/n+lc/m)B+l[V-cB/m]$. The coefficient $kd/n+lc/m$ is $\det G_{uvb,uvb}/(mn)>0$ by the positive $a$-diagonal cofactor. If $l>0$ the expression strictly increases from zero to infinity, and $U,V,B=O_G(s)$ uniformly in $N$. Indeed $B\le s/(kd/n+lc/m)$ and $lV=s-kU$. For $l\le0$ the difference from its linear part is $lcNB^2/[m(m-NB)]$. On $0\le NB\le\eta(G)$ the derivative of this difference is bounded by a constant times $\eta$. On that interval the whole derivative is therefore at least $(kd/n+lc/m)/2$ for sufficiently small $\eta$. Every $s\le\delta/N$ is attained uniquely there for sufficiently small $\delta$, again with $U,V,B=O_G(s)$. Write $p=NV B/[(1+V)(1+B)]$ if $u$ has a negative participating withdrawal and $p=0$ otherwise. Then $0\le p\le mV$. When the following $\alpha$ values of $u,v$ are zero and that of $b$ is $s$, their respective expected payments on $\beta$ are $-p,0,0$, equal to each mover's forced offers. For $u$ the two implementations give the same indifference equation $-mV+cB+NVB=0$.

Let $(X,Y,W)$ be the odds on $\alpha$. Set
\[
 X=(dS-fW)/n,\qquad Y=[cS-eW-(1-S)p]/m,
 \qquad gW-kX-lY=s(1+X)(1+Y)(1+W).
\]
The first two equations make both mates indifferent at zero using their values on the solo date. The third gives $b$ its prescribed value $s$. At $s=p=0$ their solution is $(\xi,\upsilon,\omega)S$. The left side of the last equation has slope $g+k f/n+l e/m=(kd/n+lc/m)/\omega>0$ in $W$, by the axis equations. On a bounded interval around $\omega S$ the derivative of the right side is $O_G(s)$, and the residual at $\omega S$ is $O_G(s)$. Taking the unique nearby root yields a continuous solution $(X,Y,W)=(\xi,\upsilon,\omega)S+O_G(s)$, positive whenever $s/S$ is sufficiently small. All constants here are independent of the six price sizes.

Write $A=KXY/[(1+X)(1+Y)]$, the forced value of $a$ at $\alpha$, and $D_\beta=(1+U)(1+V)(1+B)$. The passive value at $\beta$ is
\[
 A_\beta=[hU+iV-jB+\ell LUVB+A]/D_\beta,
\]
where $\ell=1$ for a positive passive $L$ and zero for its negative participating implementation. The remaining indifference equation at $\alpha$ is $F(S)=0$, with
\[
 F=KXY-hX-iY+jS-(1-S)A_\beta .
\]
Let $F_0$ denote the same expression at $s=0$. Then $F_0/S$ is the left side of (1) minus $\Delta$. On any fixed compact positive interval for $z=\sqrt K S$, with $S$ bounded above by one, one has
\[
 |F-F_0|\le C_G[s+\ell\min(Ks^2,Ls^3)] .\tag{2}
\]
Indeed the two terms containing $KXY$ combine to $KXY[1-(1-S)/((1+X)(1+Y)D_\beta)]$. The bracket is $O(S)$ and changes by $O(s)$ from $s=0$, while $XY$ changes by $O(Ss)$ and $KS^2$ stays bounded. The linear terms change by $O(s)$, and $LUVB\le K UV$ because $L<KN/m$ and $NB<m$; also $LUVB=O(Ls^3)$. This proves (2) uniformly in the prices. If $\ell=0$, choose $s=\delta S$. If $\ell=1$, choose
\[
 s=\delta\min\{S,\max(S^{3/2},(S/L)^{1/3})\}.
\]
In either case take the additional minimum with $\delta/N$ if $l\le0$. All choices are continuous in $S>0$. When the larger term in the displayed maximum is $S^{3/2}$, use $Ks^2\le\delta^2(KS^2)S$. Otherwise use $Ls^3\le\delta^3 S$. Thus the right side of (2) is $O_G(\delta+\delta^2)S$ in all cases.

For precision let $q=1/\sqrt K$ vary in $[0,1/\sqrt{K_*}]$. In variable $z=S/q$ the function $F_0/S$ extends continuously to $q=0$ with value $\xi\upsilon(1+\xi+\upsilon)z^2-\Delta$. Its unique positive simple root $z_0(q)$ is continuous. At that root the solo guard $K\xi\upsilon S^2-DS=\xi\upsilon z_0(q)^2-Dqz_0(q)$ is strictly positive throughout the compact interval, including its endpoint $q=0$. Also $S<1$ uniformly there. Choose a uniformly narrow strip around $z_0(q)$ with these strict margins, with $z$ bounded above and away from zero, and with opposite strict boundary signs of $F_0/S$. By (2) and continuity a sufficiently small fixed $\delta$ gives a zero of $F$ inside the strip for each $K\ge K_*$ and all allowed remaining prices. The actual solo guard $KXY-hX-iY\ge0$ persists, since $K|XY-\xi\upsilon S^2|=O_G(KSs)=O_G(\delta)$ on the strip. The mates' solo-date values are the waiting values $cS-(1-S)p$ and $dS$, strictly positive for small $s/S$.

At $\beta$ the passive $a$ numerator exceeds its forced offer $KUV-(1-\ell)LUVB$: the term $A$ is bounded below by a fixed positive constant throughout the strip, the linear terms are $O_G(s)$ and $KUV=O_G(Ks^2)=O_G(\delta^2KS^2)=O_G(\delta^2)$. At $\alpha$, the only remaining quiet guard is $R_b XYW\le s(1+X)(1+Y)(1+W)$. Since $XYW=O_G(S^3)$ and $S$ is between two positive singleton-dependent multiples of $K^{-1/2}$, the chosen $s$ gives $s/S^3\ge c_1\min(A_L,A_N)$ throughout the strip. This proves the quiet guard in the claimed price range for sufficiently small $c_0>0$. These three proper product rows now repeat with exact local obedience. Under any single-player replacement a recurring rival stops with positive probability per block, so the local comparisons extend to arbitrary stopping rules and signed row translations.

### A period with two triple dates and no stationary approximation

Use witness 6 with rows $(0,-1,-1,2),(-1,0,-1,2),(1,1,0,-1),(-1,-1,2,0)$. Take $u=0,v=1,a=2,b=3$, all own singleton levels one, $K=L=16$, $N=48$, and $R_u=R_v=R_b=1$, using both positive passive withdrawals. The ordinary $01,2,3$ calendar fails its $K$ guard, since $K_*=6+2\sqrt{10}<16$. There is an exact equilibrium with the two triple dates. In the preceding notation set $s=1/5$, $(U,V,B)=(1/30,1/6,1/60)$, and use equal mate odds $X=Y=x$ on $\alpha$, where $2/15\le x\le3/20$. Set
\[
 W=\frac{2x+s(1+x)^2}{2-s(1+x)^2},\qquad S=(x+W)/2,\qquad A=16x^2/(1+x)^2.
\]
These choices give $U=2B$, $V=2B/(1-48B)$, $U+V=s$ and $2(W-x)=s(1+x)^2(1+W)$. Taking $A_\beta=(s-B+16UVB+A)/[(1+U)(1+V)(1+B)]$, the residual $16x^2-2x+S-(1-S)A_\beta$ at the two endpoints is respectively $-84297320981/3375806297850$ and $9276037343/694435333800$. At an intervening zero all active owners are indifferent. Throughout the interval $x<W<1/3$, so $x^2 W<1/5\le 2(W-x)$; also $16x^2>2x$ and $A>16UV$. These are the quiet guards of $b$ on $\alpha$ and of $a$ on the solo and $\beta$ dates. Both mates earn $2S>0$ on the solo date. This verifies the exact signed periodic profile.

There is no sure opening. Here $KN>mL$, $G_{bv}<0$ excludes sole $v$, and the sole-$b$ candidate satisfies $2X^2+3X=1/8$, so $X\le1/24$ and its guard $X^2+3/16-4\ge0$ fails. Consider a stationary profile of strictly positive proper odds $(x,y,t,w)$ in order $u,v,a,b$, writing $h_i=1-\prod_{j\ne i}(1+p_j)^{-1}$. The four stationary indifferences give
\[
 2w-t=x(1+h_vtw)=y(1-48w+h_utw),\qquad x+y=(2-h_bxy)t,\qquad w=x+y+16(w-h_a)xy.
\]
If $w\ge2$, the last equation gives $xy\le1/8$ and $x+y\le w$. Thus $x+y\ge3t/2$ and $2w-t\ge4w/3$. The first identities imply $\min(x,y)\ge4/[3(t+1/w)]$ and $t>48-1/w>1$, while $\max(x,y)\ge3t/4$. This forces $xy\ge t/(t+1/w)>1/2$. Hence $w<2$ and $t<2w<4$; the positive factor $1-48w+h_utw$ now yields $w<1/44$. The first identities and $x+y\le2t$ imply $t\ge w/(1+w^2)$, since $x,y\ge(2w-t)/(1+2w^2)$. Therefore $x+y-w\ge(2-4w^2)t-w>w/2$, using $xy\le t^2$. But $h_a\le x+y+w\le5w$ gives $16h_a xy\le320w^3<w/2$, contradicting the last equation.

Proper stationary triples omitting either mate reduce on the active rows to the nonsingular singleton submatrix. Without $a$, row $b$ is negative on both mates; without $b$, either mate sees both its active rivals negatively. Pairs have nonzero internal singleton comparisons, and every singleton has a negative outsider who benefits by quitting immediately. Perpetual continuation by all four loses to the positive own singleton. These also exclude stationary approximations whose hazards converge to a nonzero vector: at two positive limiting hazards the prescriptions and immediate and Never offers are continuous for all rows, while at a sole positive limiting hazard its negative outsider already strictly gains in the limit. If all hazards tend to zero, pass to a subsequence of positive total hazards with their sum-normalized vector tending to $z$ of sum one. The native prescription tends to $(Gz)_i$ and the immediate quit offer to zero. For $z_i<1$ the Never offer tends to $(Gz)_i/(1-z_i)$. The signed row constants cancel whenever there is another positive hazard; profiles with only one active owner are uniformly excluded by a negative outsider. Vanishing regret would give $Gz\ge0$ and $(Gz)_i=0$ on every positive $z_i<1$; if $z_i=1$, its row is zero by hollowness. This contradicts the $R_0$ property checked for witness 6. Thus a positive regret gap separates every stationary profile from the exhibited exact equilibrium.

The two-triple period and the positive stationary regret gap also hold on a nonempty open set in all sixty original reward coordinates. To see this, give $b$ pair joining rewards $Z_b(ub)=5\varepsilon$ and $Z_b(vb)=-\varepsilon$ at the calibration above, with $\varepsilon>0$ sufficiently small. At the same odds $V=5U$ on $\beta$, its forced payoff is still zero. At $\alpha$ its forced-offer numerator increases by only $4\varepsilon x$, so the strict quiet guard persists throughout the bracket. The stationary gap persists as well: changing every reward by at most $d$ changes every deviation gain by at most $2d$, uniformly in the profile.

For arbitrary nearby tables use as each active player's stage value its forced immediate payoff, with native value zero at the solo date of $b$. Compute the quiet value of $b$ at $\alpha$ from that following solo value, the quiet value of $a$ at $\beta$ from its forced $\alpha$ value, and the three quiet solo values from $\beta$. This gives seven smooth indifference equations in the seven odds or probabilities. At the modified calibration fix $X=x$ in the stated interval. The solo indifference of $b$ sets its forced $\beta$ numerator $\varepsilon(5U-V)$ to zero. The $\beta$ indifferences of $v,u$ require $U=2B$, $V=2B/(1-48B)$. These three equations have an invertible Jacobian in $U,V,B$, since $[2B/(1-48B)]/(2B)$ has strictly positive derivative there. After them, the two $\alpha$ mate equations are $X=Y=2S-W$, and the $\beta$ indifference of $b$ reduces to $2(W-x)=s(1+x)^2(1+W)$; its coefficient $2-s(1+x)^2$ is positive. Thus the six equations have invertible Jacobian in $U,V,B,Y,S,W$ throughout the compact $x$ interval. The implicit function theorem, with local solutions agreeing by uniqueness, solves them on the interval for every sufficiently small perturbation of the full table. The seventh equation retains opposite strict signs at its endpoints, and every quiet guard stays strict on the interval. An intervening root supplies the exact same phase supports on this open set.

## A return for the opposite assignment on every surviving singleton matrix

Here the joining owner is denoted by $a$, the remaining outsider by $b$, and the mutual pair by $u,v$. Either mate may own the withdrawal edit, independently of this labeling. Write $K=Z_a(M+a)>0$ and $R=Z_b(I)>0$. As in the three-date construction the other four edits may have arbitrary magnitudes with either allowed withdrawal implementation.

Use the following singleton data:
$$
  c=G_{ua},\quad c'=G_{va},\quad e=-G_{ub},\quad d=-G_{ba},\quad
  f=G_{ab},\quad m=-G_{uv},\quad n=-G_{vu}.
$$
Require these seven numbers to be positive. Set $g=G_{vb}$, $l=-G_{au}$, $k=-G_{av}$, $h=G_{bu}$, $i=G_{bv}$, and put
$$
 C=c/m,\quad D=c'/n,\quad E=lD+kC,\quad H=hD+iC-d,\quad
 V=(c'+gc/e)/(nd),\quad W=fc/(ed)-lV,\quad B=\max(h,i).
$$
For each remaining singleton matrix these constants can be chosen with $B,E,W,h>0$, $V\ge0$ and $hV+HW/E>1$. To see this, let $a=3,b=2$ in the eight-chamber axis result above. Among mates who dislike $b$ choose $u$ to minimize $G_{ua}/(-G_{ub})$. This makes $V\ge0$, including when the other mate likes $b$. Since every pair other than $M$ has a strictly positive comparison and $G_{ub}<0$, we have $h=G_{bu}>0$. The diagonal cofactor at $b$ is $mnE$, positive by $G^{-1}e_b>0$ and $\det G>0$. Put
$$
 z_0=(V+D W/E,\ C W/E,\ c/(ed),\ 1/d+W/E)
$$
in the coordinate order $u,v,b,a$. Direct substitution gives $Gz_0=(hV+HW/E-1)e_b$. Since its $b$ coordinate is strictly positive, the positive inverse column forces the scalar on the right to be strictly positive, and then $C W/E>0$. This verifies every sign condition on the entire chambers. More generally the return below uses only the displayed sign and slope conditions.

There are $r_0,r_1>0$ depending only on the singleton matrix such that **every $R\le\max(r_0,r_1 K)$ yields an original uniform-equilibrium payoff**. All other four changed rewards can have arbitrary permitted magnitudes. Together with the opposite assignment this gives a global six-entry restriction: at every real singleton matrix, including ties, either the earlier exclusions solve every six-entry table or the singleton signs identify an outsider (player 2 in the printed labels) whose positive higher reward must exceed a positive singleton-dependent threshold in any counterexample. This reward is its participating triple if it is the joining player, and its grand reward otherwise. A common threshold is obtained by taking the smaller of the two assignment thresholds, and if necessary a minimum over the finite relabelings. In particular, with any real singleton matrix held fixed, all sufficiently small higher tables supported on at most six entries have an original uniform-equilibrium payoff.

For explicit constants define
$$
 P=\frac{B}{1+(1+c/e)B/d},\quad T=WP/E.
$$
One sufficient bound, used below at the calibrated matrices, is as follows. Suppose that some $L\ge0$ satisfies $hV\ge LW$ and $\epsilon=H+L(E-WP)>0$. Then the original game has a uniform-equilibrium payoff whenever
$$
 R\min\!\left\{C T(VP+DT),\ WP/K\right\}\le\epsilon.
$$
For any fixed singleton matrix satisfying the hypotheses this permits every $K>0$ and a positive interval of $R$ whose upper endpoint grows at least linearly as $K$ tends to infinity.

**Return calculation.** Start at the native continuation $S e_b$, where $0<S\le B$. Prepend a solo date for $a$ at odds $S/d$, followed in backward order by a solo date for $b$ at odds $(c/e)S/(d+S)$. Direct averaging gives the output $(w_u,w_v,w_b,w_a)=(0,nVz,0,(W+lV)z)$, with $z=S/[1+(1+c/e)S/d]\le P$. All quiet players obtain nonnegative values and could receive zero by quitting. Both solo movers have value zero.

Prepend a joint date with odds $p_u=Vz+Dt$, $p_v=Ct$, $p_a=t$; $b$ waits. The mates tie at zero. The two offers to $a$ agree exactly when
$$
 Et+KCt(Vz+Dt)=Wz.
$$
There is a unique positive $t\le T$. The outputs in rows $u,v$ vanish. In the other two rows they are
$$
 x=\frac{KCt(Vz+Dt)}{(1+Vz+Dt)(1+Ct)}\quad(a),\qquad
 y=\frac{hVz+Ht}{(1+Vz+Dt)(1+Ct)(1+t)}\quad(b).
$$
For each subsequent backward step from $(0,0,y,x)$ use the same odds with $Vz$ replaced by zero, now choosing $Et+KCDt^2=x$. The new formulas for $x',y'$ replace the two numerators by $KCDt^2$ and $y+Ht$, respectively. Only the singletons, the positive triple entry $K$ and the grand offer $R$ of the quiet player enter these calculations. At joint dates the quiet player can quit for $R p_up_vt$ in units multiplied by the full odds denominator.

First run these equations for every seed before imposing the quiet player's guard. Beyond the first step $x-x'\ge Et$ and $x'/x$ is continuous on $[0,WP]$, with value zero at zero and strictly below one everywhere. Thus its maximum is below one at each fixed table. The quantities $y$ are bounded by the minimum and maximum of the quiet player's on-path rewards and seed values, since they are actual prescribed one-stage averages even if an offer to deviate is profitable. In particular $y\le B$. The change in $y$ on each subsequent step is bounded by a common multiple of $t$. Hence the backward iteration converges uniformly to $F(S)e_b$, with $F$ continuous on $[0,B]$ and $F(B)\le B$. As $S$ decreases to zero the first $t=W S/E+O_K(S^2)$, the first $x=O_K(S^2)$ and the sum of subsequent $t$ is $O_K(S^2)$. Therefore
$$
 F(S)=(hV+HW/E)S+O_K(S^2)>S
$$
for small positive $S$. Fix a positive seed with $F(S)=S$.

If $H>0$, the displayed explicit bound already applies with $L=0$: on every joint date the quiet payoff numerator is at least $Ht$, while $p_up_v\le C T(VP+DT)$ and $Kp_up_v\le WP$. More generally the earlier bound with $L\ge0$ follows by induction on $y\ge Lx$. At the first joint date subtract $L(1+t)(Wz-Et)$ from $hVz+Ht$; the result is $(hV-LW)z+[H+L(E-Wz)]t+LEt^2\ge\epsilon t$. Thereafter $y+Ht-L(1+t)(x-Et)\ge[H+L(E-x)]t+LEt^2\ge\epsilon t$. Thus all guards hold in the stated range.

If $H\le0$, a nonpositive $y$ could never yield a positive limiting value in the later recurrence. All joint outputs at the chosen seed are therefore positive, and they decrease to $S$. In particular every quiet numerator is at least $S$. At all joint dates $z\le S$ and $t\le WS/E$. Consequently
$$
 p_u p_v t\le C(W/E)^2(V+D W/E) S^3,\qquad
 Kp_u p_v t\le W^2 S^2/E .
$$
These estimates give the required two bounds, for example $r_0=1/[C(W/E)^2(V+D W/E)B^2]$ and $r_1=E/(W^2 B)$. Uniform positive constants also exist near $H=0$: if $H_+ W/E<1/2$ the total possible later increase from the positive forcing terms is at most $H_+\sum t\le H_+WS/E<S/2$. A nonpositive output could then never reach the limit $S$. Starting from a positive output, each further positive output is at most the previous value plus $H_+t$. Thus all joint outputs exceed $S/2$, and half the displayed thresholds suffice throughout this neighborhood.

Truncate the backward steps at this fixed point and repeat the finite block. Each deviator faces at least one of the two distinct fixed solo hazards per block. Its best-reply and prescribed value maps therefore have a common contraction factor below one, uniformly in truncation length. The block's prescribed and best-reply outputs at the seed coincide and converge to the seed. Hence both true values converge to it and the maximum terminal regret vanishes. With each truncation fixed, survival under any individual replacement is geometrically bounded in the number of blocks. Restoring the four own singleton levels therefore gives the corresponding signed uniform target.

For the sharper explicit bounds the following exact substitutions use $u=0,v=1,a=3,b=2$ at each of the eight strict integer calibrations from the three-date table.

| Witness | $E$ | $H$ | $V$ | $W$ | $WP$ | $L$ | $hV+HW/E$ |
|---|---:|---:|---:|---:|---:|---:|---:|
| 6 | 4 | 3 | 0 | 4 | 1 | 0 | 3 |
| 8 | 2 | 5 | 0 | 2 | 4/7 | 0 | 5 |
| 15 | 3 | -1 | 3 | 1 | 2/7 | 1 | 17/3 |
| 16 | 1/2 | -1/2 | 5/3 | 1 | 3/13 | 2 | 4 |
| 17 | 3 | -1 | 3 | 5 | 10/7 | 1 | 13/3 |
| 18 | 3 | 1 | 1 | 1 | 2/5 | 0 | 4/3 |
| 19 | 1/2 | 7/6 | 5/3 | 1 | 1/5 | 0 | 4 |
| 21 | 3 | 1 | 5/2 | 7/2 | 7/5 | 0 | 11/3 |

The assignment here exchanges the two outsiders in the three-date theorem. For witnesses 6 and 8 the two mates tie in the choice of the second solo date. On small singleton perturbations both still have negative comparisons for that donor. Choose the mate for which its value first reaches zero; this gives $V\ge0$. At both calibrations the other strict inequalities hold in either order with $L=0$. At the other six witnesses the displayed order persists with $V>0$. For witnesses 15, 16 and 17 the inequality $hV>LW$ is strict. In the other cases $L=0$ and $h>0$. Consequently the existence criterion holds in singleton neighborhoods of all eight witnesses for strict reward bounds.

At witness 18 the first quiet numerator is $Vz+t=p_u$ and on every subsequent step it is at least $t=p_u$. The quiet guard therefore follows already from $2Rt^2\le1$. Since $t\le WP/E=2/15$, the whole range $R\le225/8$ works for every $K>0$, in addition to the growing interval in the general bound. Earlier constructions also used accumulating backward phases; here the prices and column conditions are evaluated on the six-position residual. [Earlier accumulating prefixes](ALL_NONNEGATIVE_PAIR_PREMIUMS_UNIFORM_EQUILIBRIUM.md) · [Earlier three-player return](UNIFORM_EQUILIBRIUM_REQUIRING_TRIPLE_FIRST_EXITS.md)

### A six-entry calibration separating exact and approximate calendars

At witness 18 set $Z_3(013)=1$, $Z(I)=(1,1,1,-1)$, $Z_0(012)=-4$, all other higher entries zero, and all original own levels one. This game has the uniform target just constructed using at most three positive hazards on every date. Every *exact* terminal equilibrium, if one exists, must use all four hazards together on some reached date.

Here $u=0,v=1,a=3,b=2$, $K=L=R_u=R_v=R_b=1$ and $N=4$. The sure-opening tests eliminate all sure dates: $KN>1$, $G_{ab}=2>0$, and a sole $v$ would require $Y=(3+\sqrt{21})/2$, $X=1/Y$, $Z=1+Y$, with gain numerator $2/Y-2Y<0$. Each reached restart of an exact equilibrium must itself be an equilibrium: an owner can copy its old behavior up to that date and replace its future on joint survival. Joint survival forever has probability zero. Otherwise every private clock would assign positive mass to Never, and moving only one's Never mass to a sufficiently late finite deadline would give a strictly positive gain, tending to the probability of joint Never times the positive own singleton. The prescribed continuation, quitting now, and waiting for this date and then following prescribed play all absorb surely. Comparisons among these offers are therefore unchanged by the row constants. Delete blank dates and write $w,w'$ for the current and next native prescribed values.

Suppose every date has at most three active players. At each date a mixing owner gets its forced quit offer, and every owner can obtain at least that offer. In rows 1 and 2 it is nonnegative and, whenever the owner acts, it is zero (its only higher participating premium is for the grand coalition). If 2 mixes with 0 or 1 in the absence of 3, its waiting payoff is positive from the singleton(s) valued at one and its nonnegative continuation. Likewise 1 cannot mix with 2 or 3 in the absence of 0. With the three-active cap, 1 and 2 can therefore never both be active. Now even rows 0 and 3 always have a nonnegative forced quit offer: a negative one would require 1 and 2 together for row 0, or all of 0,1,2 for row 3. Hence every $w,w'$ is nonnegative. A two-player date must use the mutually negative pair $01$, since both active offers vanish and each waits against one rival's singleton and a nonnegative continuation. On a hypothetical $023$ date the movers also get zero. If their odds are $p_0,p_2,p_3>0$, waiting yields the necessary inequalities $p_2\ge2p_3$, $p_0\le2p_3$, $p_0\ge2p_2$, which are incompatible. Thus the only nonsolo dates are $01$ and $013$.

On both of these dates $w_0=w_1=0$ and $w_2,w_3>0$. Row 3 can earn its positive triple joining offer; row 2 earns positive singleton contributions on $01$ or can quit for its positive grand offer on $013$. Such a date cannot follow a solo 2 or 3, whose own value must remain zero across its solo date. It cannot follow a solo 0 or 1, since that mover's mate would then have had negative value. Nor can it follow $01$, which leaves both mates with strictly positive next values to compensate for their negative reciprocal singletons. Consequently all nonsolo dates form an initial consecutive run of $013$, possibly ending with one $01$. Any two consecutive nonsolo dates force, on the first, odds $p_0=p_3=t$, $p_1=2t$, by the two zero mate continuations and the waiting equations. Then $w_3=2t^2/[(1+t)(1+2t)]$ and $w'_3=3t+2t^2$. An infinite consecutive run is impossible: $w_3$ grows by at least $3t$ at each step and, from its first strictly positive value onward, the formula for $w_3$ bounds $t$ away from zero. All continuation payoffs are bounded.

The remaining tail has only solo dates and absorbs almost surely. As cumulative exit probability increases, linearly interpolate its remaining *unconditional* native payoffs along each solo segment. These vectors stay nonnegative, and the active owner's coordinate is zero throughout its segment. This is a continuous singleton path for witness 18. The exact singleton classification excludes it: the only switch cycle is $023$, with relative masses $1,1/2,1/4$ and scaling $1/2$. The omitted row 1's total on its first tour is $-2+1/2+1/2=-1$. The singleton matrix satisfies the $R_0$ condition as checked by the census. This gives the contradiction. The limiting construction above avoids it because the number of three-player dates per finite block tends to infinity. [Finite singleton-path test](ALL_FOUR_PLAYER_SINGLETON_PATHS_HAVE_A_FINITE_TEST.md) · [Census calibration](../experiments/FIN4_SINGLETON_SIGN_CLASSES.py)

## Every grand-reward size at the surviving singleton matrices

Fix any of the remaining singleton matrices, using the role labeling from the axis result. For each assignment of the two outsiders there is $\eta>0$ such that $K,L,N,R_u,R_v$ may independently take any values in $(0,\eta)$, while $R_b=Z_b(I)$ may be any positive real number. Either mate can own the withdrawal, either implementation is permitted and all original row levels are arbitrary. For the assignment $a=2,b=3$ this is immediate from the three-date construction: sufficiently small $K$ alone already suffices. For $a=3,b=2$ the accumulating return supplies a low interval $0<R_b\le r_0$ independently of the five other prices. The positive-axis stationary theorem applied with $J=\{b\}$ covers the complementary interval $R_b\ge r_0$ for uniformly small other prices. Indeed its scale $t$ stays bounded above there, and all three tolerances in its inequalities have positive lower bounds. Together the intervals cover the entire positive line. On the branch with $G^{-1}e_2>0$ these conclusions hold on singleton neighborhoods: the axis remains positive, the designated singleton signs persist, and the two possible orders at a tie of the initial mate ratios both meet the return conditions. [Positive grand rewards at every scale](POSITIVE_GRAND_REWARDS_AT_EVERY_SCALE.md)

### A sure opening extends the return to five unrestricted prices

Use the opposite assignment and abbreviate the positive grand reward of $b$ by $R$. Write $L=Z_a(T)-Z_a(I)>0$ for the grand withdrawal size, independently of the auxiliary slope in the accumulating-return calculation. Suppose the returns above give equilibrium for
$$0<R\le\max(r_0,r_1K),\qquad r_0,r_1>0.$$
Both numbers can be chosen locally uniformly on the positive-axis branch by the bounds in the preceding return. Assume $G_{bv}>0>G_{vb}$, and set $m=-G_{uv}$, $m_v=-G_{vu}$. When $G_{av}\ne0$, define
$$
 R_{\rm sure}=\begin{cases}
 L G_{bv}(G_{va})_+/[(-G_{vb})(-G_{av})] & (G_{av}<0),\\
 K^2 G_{bv}(G_{va})_+/(m_vG_{av}^2) & (G_{av}>0).
 \end{cases}
$$
Every $R\ge R_{\rm sure}$ gives original uniform equilibrium for arbitrary positive sizes of the other entries. In particular the entire positive $R$ line works whenever $R_{\rm sure}\le\max(r_0,r_1 K)$.

Indeed $KN\le mL$ already gives a sure pair. Otherwise the sole-$v$ test above supplies its candidate $Y>0$, with $B=G_{bv}/R$, $X=B/Y$ and $Z=(K-G_{av}Y/B)/L>0$. Its remaining inequality is
$$m_vX-G_{va}Y-G_{vb}Z+R_vBZ\ge0.$$
If $G_{av}<0$, one has $Z\ge(-G_{av})Y/(BL)$, so the sufficient bound prices $G_{va}Y$ with $-G_{vb}Z$. If $G_{av}>0$, then $Y<BK/G_{av}$ and $X>G_{av}/K$, and the bound prices $G_{va}Y$ with $m_vX$. This verifies every sure-owner comparison, including withdrawal after a first-date blank.

For $G_{av}<0$, either a sufficiently small $L$ alone or a sufficiently small $N$ alone gives equilibrium for **all five other positive prices independently**. In the second case only $KN>mL$ needs checking, and then $L<KN/m$: use the $r_1K$ part of the return. For $G_{av}>0$ the same five-free-price conclusion holds with only $K$ sufficiently small. All statements persist on singleton neighborhoods with strict sign conditions, with arbitrary original row constants and either implementation of each withdrawal.

In the census labels $a=3,b=2$, the fixed mate $v=0$ satisfies $G_{bv}>0>G_{vb}$ at all eight witnesses. Its $G_{av}$ is negative at 6, 8, 15, 16, 18 and 19, and positive at 17 and 21. The mate $v=1$ also qualifies at 6 (negative $G_{av}$) and 8 (positive $G_{av}$). Here $u$ is the other mate and owns the withdrawal from $T$; the order used in the accumulating return may be chosen independently. With outsider roles exchanged, the earlier three-date theorem already allows all five other prices for sufficiently small $K$ for either mate.

### Independent large prices for the three-date assignment

Take $a=2,b=3$ on the positive-axis branch, and let $J$ be any subset of $\{u,v,b\}$ whose inverse columns are strictly positive. The triple price $K$, the grand withdrawal size $L$, and every grand reward $R_j$ for $j\in J$ may vary independently over $(0,\infty)$ whenever $N$ and the grand rewards of the other owners are sufficiently small. Either mate may own the withdrawal and either implementation of each withdrawal is allowed. For witnesses $6,8$ the maximal $J$ is $\{3\}$; for $15,16,17$ it is $\{1\}$; for $18,21$ it is $\{0,1\}$; for $19$ it is empty. The indices denote the original census labels. The grand $R_b$ here is $R_3$, while in the opposite assignment the sufficient small-grand condition concerns $R_2$.

The three-date equilibrium covers $K\le K_*(G)$, and the sure pair covers $mL\ge KN$. Otherwise apply the all-scale positive-column theorem with the marked triple $K$ in row 2 and the marked grands $R_j$ for $j\in J$. Its scale $t$ satisfies $h_*(t)[Kt+\sum_{j\in J}R_jt^2]=1$, $h_*(t)=1-(1+t)^{-3}$. Thus $t$ is bounded above and $Kt^2\le t/h_*(t)$ is also bounded. An unmarked withdrawal of size $L$ on the rival triple gives a perturbation bounded by a constant times $Lt^2\le N Kt^2/m$, for either its passive or its participating implementation. The $N$-term and the unmarked grand rewards have bounded scale factors. Uniformly small $N$ and unmarked grands therefore satisfy the perturbation bounds, independently of all designated prices. This also gives the whole $K$ line when $J$ is empty.

There is a stronger conclusion when $G_{bu},G_{bv}<0$. In this case **$N$ alone can be sufficiently small while every other price is arbitrary and positive**. Use the sure-$b$ test with $C=-G_{ab}/L$, $D=G_{vb}/R_v$. Its unique positive candidate solves $G_{ub}X^2+NCX=R_uCD$. If the test fails, $|G_{bu}|X^2+|G_{bv}|C+R_bCD<G_{ba}D$. Thus $X^2\le c/R_v$, $R_v,R_b\le cL$ and $R_u\le c(L+N\sqrt{R_v})\le c'(L+N\sqrt L)$, with constants depending only on the singleton matrix. Since $K\ge K_*(G)>0$, $L<KN/m$ and $N\le1$, all three grand prices and $L$ are at most $c''KN$. Mark only the triple $K$ in the preceding scale argument. Each of these four errors is then bounded by a constant times $KNt^2=O(N)$, and the $N$ withdrawal is also $O(N)$. This covers the complete strict singleton chambers of witnesses $6,15,18$ and the tied matrices with the same strict comparisons, with either withdrawing mate. At a tied matrix satisfying the displayed signs, the sure-$b$ candidate remains sufficient by its explicit first-date indifferences and its weak-blocker fallback; its use here requires no exhaustive classification of sure openings at ties.

At witness 18, $N\le1$ suffices for both withdrawal owners in the opposite assignment and all five other prices may vary independently. Other results cover large withdrawals and allow variations in all 38 formerly zero higher entries. The companion paper gives the sharper constants, the stationary proofs and the four-player adjustment of the accumulating return. [Large withdrawal rewards](SIX_ENTRY_EQUILIBRIA_WITH_LARGE_WITHDRAWAL_REWARDS.md)
