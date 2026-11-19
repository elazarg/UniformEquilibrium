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

## A return for the opposite assignment at all eight calibrations

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
Assume $B,E,W>0$, $V\ge0$, and $hV+HW/E>1$. Define
$$
 P=\frac{B}{1+(1+c/e)B/d},\quad T=WP/E.
$$
Suppose that some $L\ge0$ satisfies $hV\ge LW$ and $\epsilon=H+L(E-WP)>0$. Then the original game has a uniform-equilibrium payoff whenever
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

The first joint step gives $y\ge Lx$. Indeed subtract $L(1+t)(Wz-Et)$ from $hVz+Ht$. The difference is
$$
 (hV-LW)z+[H+L(E-Wz)]t+LEt^2\ge\epsilon t.
$$
At a subsequent step $x\le WP$ and $y\ge Lx$ imply
$$
 y+Ht-L(1+t)(x-Et)\ge [H+L(E-x)]t+LEt^2\ge\epsilon t.
$$
Hence the invariant persists, and every quiet payoff numerator is at least $\epsilon t$. On all steps $p_up_v\le C T(VP+DT)$ and $Kp_up_v\le WP$, which prove the quiet guard. Beyond the first step, $x-x'\ge Et$ and $x'/x$ is a continuous function of $x$ on $[0,WP]$, taking value zero at zero and strictly less than one everywhere. Its maximum is strictly below one for each fixed table. Each quiet value $y$ belongs to $[0,B]$, since the quiet row's on-path rewards are at most $B$ and the invariant gives nonnegativity. The change in $y$ on each subsequent step is bounded by a common multiple of $t$. Thus the backward iteration converges uniformly to $F(S)e_b$, with $F$ continuous on $[0,B]$ and $F(B)\le B$. As $S$ decreases to zero the first $t=W S/E+O_K(S^2)$, the first $x=O_K(S^2)$ and the sum of subsequent odds $t$ is $O_K(S^2)$. This gives
$$
 F(S)=(hV+HW/E)S+O_K(S^2)>S
$$
for all sufficiently small positive $S$. There is a positive fixed point. Truncate the backward steps at this fixed point and repeat the finite block. Each deviator faces at least one of the two distinct fixed solo hazards per block. Its best-reply and prescribed value maps therefore have a common contraction factor below one, uniformly in truncation length. The block's prescribed and best-reply outputs at the seed coincide and converge to the seed. Hence both true values converge to it and the maximum terminal regret vanishes. With each truncation fixed, survival under any individual replacement is geometrically bounded in the number of blocks. Restoring the four own singleton levels therefore gives the corresponding signed uniform target.

The following exact substitutions use $u=0,v=1,a=3,b=2$ at each of the eight strict integer calibrations from the three-date table.

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

## Every grand-reward size near all eight singleton calibrations

At each of the eight singleton calibrations with a unique mutually negative pair, both assignments of the two outsiders admit a whole positive line in the six-entry template. For each assignment there are a neighborhood of its singleton matrix and $\eta>0$ such that the other five required magnitudes $K,L,N,R_u,R_v$ may independently take any values in $(0,\eta)$, with either mate owning the withdrawal and either implementation of its two edges, while $R_b=Z_b(I)$ may be any positive real number. At the assignment $a=2,b=3$ the three-date construction already gives more: for sufficiently small $K>0$ its guard $KP<D$ is strict, and all five other magnitudes are arbitrary.

For the opposite assignment $a=3,b=2$, the accumulating theorem supplies a fixed interval $0<R_b\le r$, with $r>0$ bounded away from zero on a neighborhood of each listed calibration. Its sufficient bound using $CT(VP+DT)$ does not depend on $K$. The remaining interval follows by perturbing a stationary branch. At the reference table whose only nonzero higher reward is $R_b$ for the grand coalition, put $y=G^{-1}e_b>0$ as verified for all eight matrices. In proper odds $p$ the three nonpivot equations are $(Gp)_i=0$. They have the ray $p=ty$, $t>0$. The pivot equation becomes
$$
 R_b=\frac{1}{t^2\,[1-\prod_{j\ne b}(1+t y_j)^{-1}]\prod_{j\ne b}y_j}.
$$
The denominator is strictly increasing with strictly positive derivative, from zero to infinity. Each $R_b>0$ has a transverse positive solution: the three nonpivot rows have rank three, and the remaining scalar equation has nonzero derivative on their kernel.

These solutions persist uniformly over $R_b\ge r$ under small perturbations of the singleton matrix and other fixed higher entries. To include infinity, set $\lambda=R_b^{-1/3}$ and $p=\lambda x$. After division by $\lambda$ the stationarity field at $\lambda=0$ is $Gx-H(x)e_b$ with $H(x)=(\sum_{j\ne b}x_j)\prod_{j\ne b}x_j$. The field extends smoothly to this endpoint since $(1-\prod_{j\ne b}(1+\lambda x_j)^{-1})/\lambda$ does. There is a positive transverse root $x=y/H(y)^{1/3}$, with Jacobian determinant $-3\det G$. All other bounded higher entries give vanishing scaled terms there. The reference roots thus extend to a compact positive transverse graph on $0\le\lambda\le r^{-1/3}$. Finitely many implicit-function neighborhoods ensure a proper stationary root at every $R_b\ge r$ throughout one neighborhood of the reference parameters. The stationary and accumulating intervals together give the claimed whole line, including cases in which the two-sure inequality fails.

### A sure opening extends the return to five unrestricted prices

Use the opposite assignment and abbreviate the positive grand reward of $b$ by $R$. Write $L=Z_a(T)-Z_a(I)>0$ for the grand withdrawal size, independently of the auxiliary slope in the accumulating-return calculation. Suppose the returns above give equilibrium for
$$0<R\le\max(r_0,r_1K),\qquad r_0,r_1>0.$$
Both numbers can be chosen locally uniformly at the eight calibrations: take the two terms of the previously proved bound separately. Assume $G_{bv}>0>G_{vb}$, and set $m=-G_{uv}$, $m_v=-G_{vu}$. When $G_{av}\ne0$, define
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

### Three unrestricted prices at witness 18

At the singleton matrix of witness 18, use the opposite entrant assignment $a=3,b=2$. Write $R=Z_2(I)$ and $A=Z_0(I)$, $B=Z_1(I)$ for the three positive grand rewards. Fix $N=4,L=B=1$. **All three prices $K,A,R$ may vary independently throughout $(0,\infty)$.** This holds for either withdrawal owner and both implementations of each edge, and for all original own levels. The conclusion persists throughout an open neighborhood of the singleton data and three fixed prices within the six-position template.

With withdrawal owner $u=1$, the preceding sure-$v$ criterion for $v=0$ applies at $R\ge2L$, while the accumulating return already covers every $K>0$ at smaller $R$. It suffices to establish the claim for $u=0$. In the general return specialized here, write $s=2z=4S/(2+3S)$. The first joint step uses odds $p_0=s/2+t$, $p_1=2t$, $p_3=t$, with $3t+K(st+2t^2)=s/2$. Every later joint prepend uses $p_0=p_3=t$ and $p_1=2t$. In the recurrence for witness 18, $y+x/3$ decreases under each subsequent prepend: its new numerator over $(1+t)^2(1+2t)$ is $y+(1+t)x/3-t^2$. Its value at the first prepend is at most $2s/[3(1+s/2)]$, since the corresponding numerator is $2s/3+st/6-t^2$ and denominator $(1+s/2+t)(1+2t)(1+t)$. Thus $F(S)\le8S/(6+15S)$, using $s=4S/(2+3S)$. Choose $S=1/7$, where $F(S)<S$; every seed up to this value has $s\le4/17$ and first and subsequent $t\le s/6\le2/51$. The row-2 guard $2Rt^2\le1$ holds with strict margin for $R\le300$. We now give stationary equilibria whenever $R\ge250$.

Let the positive stopping odds be $(x,y,s,w)$ and $h_i=1-\prod_{j\ne i}(1+p_j)^{-1}$. Set $n,l\in\{0,1\}$ equal to one for a positive passive implementation of the respective withdrawals $N,L$ and zero for a negative participating implementation. The nonpivot equations are
$$
\begin{aligned}
 f_0&=2w-s-y+sy[N(n+(1-n)h_0)-A h_0 w],\\
 f_1&=2w+s-2x-sx B h_1 w,\\
 f_3&=2s-x-y+xy[sL(l+(1-l)h_3)-Kh_3].
\end{aligned}
$$
In $s/2\le w\le2s$ and $0<s\le1/5$, the first two equations have unique nonnegative continuous roots in $y,x$, respectively. They decrease strictly in their own variable, with derivatives at most $-1+sN<0$ and $-2$, since $h_i+p_j\partial_jh_i<1$. They tend to minus infinity at large own variable. The root $x$ lies in $[(2w+s)/(2+sBw),w+s/2]$, and $y>0$ except at the left edge. At that edge $f_3=2s-x>0$. On the right edge $x\ge5s/(2+2s^2B)>2s$ and $sLx<1$, so $f_3<0$. These signs are uniform in $K,A$.

The remaining row is $f_2=x+y-2w-R h_2xyw$. At the top edge $s=1/5$ we have $w\ge1/10$, $x\ge (2/5)/(2+2/25)>19/100$ and $h_2\ge1-1/[(1+19/100)(1+1/10)]>23/100$. Because $x\le w+s/2\le2w$, the top has $f_2<0$ for $R\ge250$ (also at $y=0$, since $x<2w$). On every sufficiently small bottom edge at every zero of $f_3$, one has $f_2>0$. In fact, for any fixed finite prices, divide the three nonpivot equations by $s$ and take $s\downarrow0$ along such zeros. Since $y\le(2w-s)/(1-sN)$ and $x\le w+s/2$, compactness and the nonsingular leading equations give $(x,y,w)/s\to(4/3,2/3,5/6)$ and $f_2/s\to1/3$.

The rectangle in $(w/s,s)$ has opposite strict $f_3$ signs on its vertical sides and opposite strict $f_2$ signs at the $f_3$ zeros on its two horizontal sides. Its two-component field has nonzero degree: homotope $f_2$ to the affine function that is positive at the bottom and negative at the top, then $f_3$ to the affine function positive on the left and negative on the right. No boundary zero occurs. The interior zero has strictly positive odds and gives an exact absorbing stationary equilibrium, valid also after the row translations.

For perturbations of $G,N,L,B$, replace the left edge by $w/s=-G_{02}/G_{03}$ so that $y=0$ there. The monotone inverses and bounds on the sides persist with strict relative margins after division by $s$, uniformly in $K,A$: the contribution of $A$ to $f_0$ and of $K$ to $f_3$ on the right is nonpositive. For the top, $x$ depends only on $G_{10},G_{12},G_{13},B,s,w$, and the baseline $G_{20}x+G_{23}w=x-2w$ is strictly negative throughout that compact edge even at its left end, since $B>0$. The positive lower bounds on $h_2,x,w$ absorb the nearby $G_{21}y$ term. The positive leading $f_2/s$ at the lower $f_3$ zeros persists by nonsingularity for each fixed finite price.

For the lower interval use the general return notation and $\alpha=H/E>0$. The subsequent-step identity gives
$$
 y'+\alpha x'=\frac{y+\alpha(1+t)x-\alpha E t^2}{(1+Dt)(1+Ct)(1+t)}\le y+\alpha x.
$$
At the first step its numerator is $(hV+\alpha W)z+\alpha Wzt-\alpha Et^2$ and its denominator is $(1+Vz+Dt)(1+Ct)(1+t)$. Consequently $F(S)\le (hV+\alpha W)z/(1+Vz)$. The upper bound at $S=1/7$ is strictly smaller than that seed and depends only on singleton data. Every prepend has $t\le Wz/E$, where $z$ is at most its endpoint value, and the quiet guard follows from $R C t^2\le\min(h,H/D)$. The strict margin up to $R=300$ persists for nearby singleton data, independently of $K,A$. This proves openness of the entire orthant.

There is a second, larger orthant at the same singleton matrix. **Fix $N=B=1$. All four $K,L,A,R$ may independently take any positive values**, in either withdrawal orientation and both implementations. This also holds on neighborhoods of $G,N,B$. For $u=0$ only the right-side sign of $f_3$ needs a new check. If $KN\le mL$ the sure pair already works ($m=-G_{01}=1$). Otherwise $L<KN/m$. On the right edge $w=2s$ one has $x>2s$ and
$$h_3\ge 1-[(1+x)(1+s)]^{-1}\ge s/(1+s)+x/[(1+s)(1+x)]> 3s/2$$
for $0<s\le1/5$, using $x>2s$. This strictly exceeds $sN/m$ with a uniform relative margin. Hence $sL(l+(1-l)h_3)-Kh_3<0$ for every $K>0$. All other estimates above apply with their original margins. For $u=1$ the sure-$v$ cutoff is $2L$ while $m=-G_{10}=2$. Whenever $KN>mL$, this cutoff is smaller than $K$. The general return at this matrix already supplies $R\le(5/2)K$ since $\epsilon=1$ and $WP=2/5$. These strict overlaps persist on neighborhoods. This proves the four-price assertion.

### One bounded price at witness 18, in either orientation

Let $G$ be the displayed witness 18 matrix, $a=3,b=2$. If $0<N\le1/4$, **all five other prices $K,L,R_0,R_1,R_2$ are independently arbitrary and positive**. Either mate may own the withdrawal and either implementation of each edge is permitted. The conclusion holds uniformly on a neighborhood of the singleton matrix for all these choices. For $u=1$, the preceding sure-$v$ and accumulating comparison already proves the result, since on the only remaining branch $KN>2L$ one has $2L<KN\le K/4$. We give a different argument for $u=0$, where that sure-$v$ sign comparison fails. Write $A=R_0,B=R_1,R=R_2$ and $m=-G_{01}$. On a sufficiently small neighborhood we may suppose $m>3/4$. The earlier square and return let us assume
$$
 L<KN/m,\qquad R>20,\qquad K<R .
$$
Indeed the return covers every $R\le20$ with a strict uniform guard and also $R\le K$, since its center linear cutoff is $(5/2)K$.

Write the odds as $p=(x,y,s,w)$ and $h_i=1-\prod_{j\ne i}(1+p_j)^{-1}$. Set $z=Ns[n+(1-n)h_0]$, $M=(G+z e_0 e_1^\top)^{-1}$, and write stationary indifference as $p=M q$, where
$$
 q=\big(A s y w h_0,\ B s x w h_1,\ R x y w h_2,\ xy[Kh_3-sL(l+(1-l)h_3)]\big).
$$
Use $0<s\le1$, so $0\le z\le1/4$ and $sN/m<h_3$ since $h_3\ge s/(1+s)$. Hence $q$ is nonnegative.

We record explicit matrix inequalities uniform in this interval of $z$. At the stated witness,
$$
 G^{-1}=\begin{pmatrix}3&1&4&1\\1&1&2&0\\2&1&3&1\\2&1&5/2&1/2\end{pmatrix},\qquad
 M=G^{-1}-\frac{z}{1+z}G^{-1}e_0e_1^\top G^{-1}.
$$
Every $M_{2j}>0$, and all ratios $M_{0j}/M_{2j},M_{3j}/M_{2j}$ lie strictly between $1/3$ and $4$. The ratios $M_{1j}/M_{2j}$ are strictly below $4$. Moreover $M_{10},M_{11}>0$, $M_{12}>3/2$ and $M_{13}>-1/20$. These follow directly from $0\le z/(1+z)\le1/5$, including $M_{13}=0$ at the center, and persist throughout one singleton neighborhood by compactness.

Use angular variables $(x/s,y/s,w/s)\in[1/3,4]\times[0,4]\times[1/3,4]$. Form $T=Mq$ and send these ratios to $(T_0,\max(0,T_1),T_3)/T_2$. This is a continuous self-map of the angular box for each $s>0$, since $q_1>0$. At any angular fixed point $y>0$: if $y=0$, the only nonzero coordinate of $q$ is $q_1$ and $M_{11}>0$. Thus $T_1/y=T_2/s$ there. For every fixed finite choice of the six prices the maximum of $T_2/s$ over the angular box tends to zero as $s\downarrow0$. In contrast, at $s=1$ and at every angular fixed point, $h_2\ge 1-(1+1/3)^{-2}=7/16$, and
$$
 \frac{T_2}{s}=\frac{T_1}{y}
 \ge x\left(\tfrac32 R w h_2- K/20\right)
 > \frac R3\left(\frac7{32}-\frac1{20}\right)>1 .
$$
The bound includes the potentially negative $M_{13}q_3$, since $q_3\le Kxy$. Choose a small bottom radius $s_*>0$ where all angular ratios have $T_2<s_*$. Adjoin to the angular map the scalar update $s\mapsto\operatorname{proj}_{[s_*,1]}(2s-T_2)$. Brouwer gives a fixed point; the two strict radial inequalities exclude both endpoint radii. At the interior fixed point $s=T_2$ and all four odds are positive, so $p=Mq$. This gives an original absorbing stationary equilibrium throughout the remaining region, uniformly over the five unrestricted prices. Together with the square and return this proves the full statement.
