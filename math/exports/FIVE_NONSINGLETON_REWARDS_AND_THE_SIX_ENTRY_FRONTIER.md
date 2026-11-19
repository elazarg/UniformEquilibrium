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

For any full table write $m_k$ for the $k$th-largest absolute native nonsingleton entry. Its infimum of maximum terminal regret is at most $2m_6$. If retaining any choice of six largest entries gives a table outside the displayed exceptions, the bound is $2m_7$. Indeed the first truncation keeps five entries and the second six, leaving all original singleton and perpetual payoffs fixed. The prescribed payoff and every unilateral offer change by at most the largest deleted magnitude, uniformly over all profiles. Thus at a positive gap $\gamma$ there must be at least six higher entries of magnitude $\gamma/2$ or larger. If there are only six, their signed projection must pass the role and size restrictions above.

## First-date comparisons and the six edits

A pure first-date set $S$ of at least two quitters is a terminal equilibrium whenever no player prefers the adjacent set $S\mathbin{\triangle}\{i\}$. Each unilateral replacement still faces a sure rival at the first date, so these comparisons prove original uniform equilibrium, including signed own rewards. On the reference table with all nonsingletons zero every triple and the grand coalition meet this test. So does each pair with both singleton comparisons nonpositive. Let $m$ be the number of such pairs. A new strict improvement at a previously stable vertex needs a change in one of the two entries on its comparison edge. Different spoiled vertices require different edges, since one edge cannot give a strict improvement in both directions. A changed row entry belongs to just one comparison edge. Thus $m+4$ arbitrary changes preserve a pure equilibrium. Every strict singleton matrix of a possible counterexample has a mutually negative pair, and the same necessity holds without genericity. This proves the five-entry conclusion. [Reciprocal-negative necessity](NO_MUTUALLY_NEGATIVE_SINGLETON_PAIR_UNIFORM_EQUILIBRIUM.md)

At a six-entry counterexample we must therefore have $m=1$. Every change is on a different edge and pays for one strict exit from one of the five large coalitions or the unique pair $M$. No other change is available. A change that spoils a large coalition cannot create a positive participating pair or a positive participating triple. In fact the improvement either removes a member or adds the sole outsider to a triple. For a removal one lowers that member's payoff at the original set or raises its passive payoff at the smaller set. For an addition one raises the outsider's grand payoff or lowers its passive triple. The change spoiling $M$ cannot create a positive participating pair either. The only possible positive participating reward on a proper coalition is therefore a single positive triple reward $Z_a(M+a)$, obtained by adding outsider $a$ to $M$.

The earlier supportwise lowness theorem applies if each support of size three or four has some member whose forced quit offer is at most its native singleton zero, since there are no mutual-positive pair rewards. On any three-person support, at most one member has a positive participating reward within that support, so another member supplies the bound for every product row. On the full support the test still succeeds if any recipient has no positive participating reward anywhere. This gives native absorbing regret infimum zero and hence uniform equilibrium at every signed translation by the zero-column theorem. [Supportwise lowness](SUPPORTWISE_LOW_OR_CHARGE_UNIFORM_EQUILIBRIUM.md) · [Signed translation](ZERO_SINGLETON_COLUMN_EQUIVALENCE.md)

A possible exception needs a positive participating reward for each of the four players. The owner withdrawing from the grand coalition cannot have positive grand payoff, since its one change on that edge either lowers its own grand payoff or raises its passive triple. Thus this owner is the unique recipient $a$ of the positive participating triple. The remaining three owners must get positive grand payoffs, using exactly their three respective strict exits from $I-\{j\}$ toward $I$. The remaining triple $T=I-\{a\}$ must have a member who prefers withdrawing. This accounts for all six changes.

If this last withdrawing member is $b\notin M$, prescribe both members of $M$ to quit surely on date one. They weakly prefer quitting at each of the four pure choices of $a,b$: at the pair this is the baseline pair comparison, and at the three larger sets their joining payoffs are unchanged or increased. The two unrestricted players have a mixed equilibrium in the resulting finite two-action game, giving a full first-date equilibrium. Thus the withdrawing member must be some $u\in M$, leaving exactly the choices in the table.

Keep $u,v$ sure and $a$ quiet, and have $b$ quit independently with probability $q$. Player $b$ is indifferent and $v$ weakly prefers quitting. Player $a$ weakly prefers waiting if $q\ge K/(K+L)$, and $u$ weakly prefers quitting if $q\le (-G_{uv})/[(-G_{uv})+N]$. These intervals intersect exactly when $KN\le(-G_{uv})L$, proving the stated strict necessity. All these profiles absorb immediately under every unilateral replacement.

For signed or unsigned positions, choose the ordered labels in $4!$ ways and choose either implementation of each of the last two lines, giving 96 distinct supports. If there are three grand positions, the missing grand owner identifies $a$. If there are four, $a$ is the unique recipient of the participating triple when the remaining changed proper entry is passive. When both proper entries are participating triples, the two arrows from recipient to the omitted label form the directed path $u\to a\to b$, which identifies the roles. In the three-grand cases the changed proper entry of recipient $a$ on $M+a$ identifies $b$, and the other withdrawal entry identifies $u$. The distinguished reciprocal pair must be strictly negative in both directions even at a tie: a surviving signed table would persist at all sufficiently close strict singleton refinements with the same six higher rewards. Each such refinement must have that same pair as its unique mutually negative pair. A zero within it, or a second pair with both entries nonpositive, is inconsistent with this requirement. [Strict census and perturbation](TWENTY_ONE_SINGLETON_SIGN_CLASSES_FOR_FOUR_PLAYER_QUITTING_GAMES.md)

The counting and reduction also apply around any reference assigning the same constant $d_i\le0$ to all eleven nonsingleton rewards of row $i$, whenever at least one pair qualifies by $d_i\ge G_{ij}$ and $d_j\ge G_{ji}$. Count changes from these row constants. The proof above uses only that unchanged participating rewards are nonpositive and that the reference comparisons on edges between larger coalitions are tied. With $m$ qualifying pairs, $m+4$ changes preserve a pure equilibrium. At six changes with $m=1$ the same 96 positions and roles are necessary. The four positive participating rewards in the table must exceed native zero. The two withdrawal changes lower the participant below its row constant or raise the passive reward above its row constant. The size inequality becomes $KN>(d_u-G_{uv})L$, using the same actual payoff differences. The unconditional all-matrix assertion at the start uses $d_i=0$.

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
