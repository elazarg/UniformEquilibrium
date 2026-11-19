# One joining payoff controls both exterior tails on every four-player singleton matrix

Let G be a four-player hollow singleton comparison matrix with all off-diagonal entries nonzero. If a completion of G lacks a fixed-target uniform equilibrium, G is R0 of degree one, det G>0, G^{-1} has some strictly positive column, each column has a negative entry, and there is a mutually negative pair (known matrix and path exits). Given this matrix data alone there are distinct players o,j and numbers K0,c,C,delta>0 depending only on G with the following property. At any original table with this G, let Z denote the native centered rewards and K=|Z_o({o,j})|. Whenever K≥K0 and each of the other 43 nonsingleton coordinates obeys |Z_i(S)|≤delta K^{|S|−1}, there is an exact stationary terminal equilibrium against every private stopping deviation with maximum hazard ≤C/K and at least three hazards ≥c/K. Either sign of the one distinguished joining payoff works, with the same choice of o,j. Signed own levels are arbitrary. This is an exact equilibrium on the stated matrix branch; if the necessary matrix conditions fail then complete UE coverage follows from prior results, without a claim that it is stationary. Consequently on every strict singleton matrix some single original pair joining reward can carry two entire UE-exterior tails while fixing the other 59 original entries arbitrarily. The threshold may depend on those fixed entries.

## Deleting one row and column

Choose a mutually negative pair i,k. If either row has a negative entry at a third label l, use T={i,k,l} and omit the remaining player o. Otherwise i,k see both other owners positively. To witness a negative in each of those two owners' columns they must themselves form another mutually negative pair. If both of their remaining entries are also positive in each row, both three-cycles in every principal triple use exactly one negative entry. All principal triple determinants are negative. This contradicts the positive diagonal element in a positive column of G^{-1}, since det G>0. Thus one can always obtain such a T. For B=G_TT, there is a nonnegative row vector a with a^T B strictly negative: give positive weights to the mutually negative pair, choosing their ratio to make their sum strictly negative on its third column. In particular no nonzero x≥0 has Bx≥0. Thus B is R0 of degree zero: moving the target from zero to a small positive vector creates no boundary zeros by homogeneity/compactness and ends without any feasible solution.

## Opposite axis targets share a rival

Write L_b(y)=min(y,Gy−b) coordinatewise. Its zeros satisfy y≥0, Gy≥b, and y_i(Gy−b)_i=0. The homogeneous R0 property bounds all its solutions along any bounded target homotopy, by normalizing any unbounded sequence. At b=+e_o and b=−e_o its degree on a common large ball is therefore one. At the positive target zero is infeasible. At the negative target zero is an isolated zero near which the o-th minimum selects y_o identically. Its local degree is deg B=0: homotope the G_To y_o term in the other rows to zero while keeping the o-th residual y_o; every zero has y_o=0, so only zero is possible in that small neighborhood. This reduces to the product of the identity with the child minimum map.

At any nonzero solution of either target one has y_o>0, since otherwise B y_T≥0. There is a rival in the support, since (Gy)_o=±1. In fact at least two rivals have positive mass, since with exactly one rival j its active equation is G_jo y_o=0, impossible. Thus the possible nonzero supports are full or triples containing o. Full support gives a unique candidate by det G>0. For a triple S={o,i,k}, the equations G_SS y_S=±e_o admit at most one solution: if G_SS were singular, the o-th coordinate of adj(G_SS)e_o would be −G_ik G_ki≠0, precluding consistency. Consequently both target solution sets are finite, without any generic principal-minor or strict-inactive-slack assumption. Their global degrees and the negative target's degree-zero origin give, for each sign s, an isolated nonzero zero y^s of nonzero local degree. Each has o and at least two rivals active. Two subsets of size at least two among three rivals intersect. Fix a common rival j with y^+_j,y^-_j>0. All choices use only G; finite support enumeration and local degree can select witnesses if desired.

## A stationary root at scale 1/K

For the native game let q be one stationary row of hazards, H_i(q)=prod_{r≠i}(1−q_r), P_i the unconditional contribution on nonempty rival exits when i waits, and Q_i the forced quit offer. Stationary complementary equations are q≥0, F_i(q)=P_i(q)−(1−H_i(q))Q_i(q)≥0, q_i F_i(q)=0. With two active owners and hazards strictly below one, the passive value at Never is P_i/(1−H_i) in every row; deterministic deadlines interpolate between these and the immediate offer. Equality in every occupied row and the inequalities on quiet rows imply exactly zero terminal regret. Rival survival vanishes geometrically, uniformly over the one-player replacement, and row translations transport exactness and supply uniform equilibrium.

Fix s=sign Z_o({o,j}). For x in any bounded neighborhood of the positive scale candidates and q=x/K, the scaled F satisfies
$$
 K F(x/K)=Gx-s\,x_j\Big(\sum_{r\ne o}x_r\Big)e_o+E_K(x).
$$
With all other native higher rewards bounded, E_K→0 uniformly on compact sets. With the stated weighted boxes it is bounded uniformly there by C'(G,box)/K+C''(box)delta: a passive monomial from coalition S has |S| rival factors; a participant term has |S|−1 rival factors and one further 1−H_i=O(1/K). Only the distinguished pair coefficient is order K without the small factor. Its remaining wait factors are 1+O(1/K), giving the displayed polynomial, with the same compact estimate on a small real open neighborhood should some coordinates there be negative.

Let H(x)=x_j sum_{r≠o}x_r, which is positive at each selected y^s. The map x↦x/H(x) is an involutive homeomorphism on H>0 because H is homogeneous of degree two. Composing the leading minimum map for K F(x/K) with that map sends the target residual at y to min(y,Gy−s e_o)/H(y). The positive denominator and local homeomorphism preserve nonvanishing local degree, also at solutions with inactive ties. A compact neighborhood around each selected dilated root has positive minimum distance of its boundary residual from zero. Choose K0 large and delta small to preserve both degrees by uniform homotopy. A root of the actual scaled minimum map exists in each relevant sign's neighborhood; it is nonnegative. Its at least three selected positive coordinates are uniformly bounded below there. Division by K gives the claimed proper stationary clock bounds. No equality or sign hypothesis on the other 43 higher entries is required inside the weighted box.

## Relation to earlier exterior criteria and zeros

The earlier two-signed-reward theorem gives a passive pair and a participant triple at fixed roles from opposite full and proper positive rays, and selects the roles when the entire inverse is strictly positive. Its generic one-entry converse concerns a passive reward. The common-rival argument gives both signs of a single pair joining reward on the full degree-one hard strict class, including singular principal triples and mixed inverse columns. The weighted collision and sparse criteria use additional matrix or direction tests. [Two independently signed rewards](TWO_SIGNED_REWARDS_FROM_A_SINGLETON_MATRIX.md) · [Weighted collision dominance](WEIGHTED_COLLISION_DOMINANCE_UNIFORM_EQUILIBRIUM.md) · [Sparse large coalition rewards](../notes/CODEX_ROOT__SPARSE_LARGE_COALITION_REWARDS.md)


**Why the partner matters.** Take
$$
G=\begin{pmatrix}0&-1&-1&3\\-1&0&-1&2\\-1&2&0&-1\\-1&-1&2&0\end{pmatrix},\qquad o=3.
$$
The only nonzero axis solutions at $+e_3$ and $-e_3$ are respectively $(0,1,4,2)/7$ and $(2,3,0,1)/5$; the inactive slacks are $1/7$ and $3/5$. Indeed the columns $G_{SS}^{-1}e_3$ at $S=013,023,123,0123$ are respectively $(-2,-3,-1)/5,(-1,3,1)/7,(1,4,2)/7,(-1,0,3,1)/7$. The child has a strictly negative row combination, and smaller supports cannot occur. Both proper solutions are transverse. Only rival 1 occurs in both. When all other nonsingleton native entries vanish, on $q_i<1$ write $p_i=q_i/(1-q_i)$. The three nonpivot rows of $F$ are $H_i(Gp)_i$, and the pivot row is $H_3[(Gp)_3-J_{3j}(1-H_3)p_j]$. A nonzero proper solution requires $p_j>0$, since $G$ is $R_0$ (each column has a negative entry, smaller active pairs are impossible, and $G$ and its principal triples are nonsingular). Dividing by $|J_{3j}|(1-H_3)p_j$ then gives the corresponding axis solution. Thus arbitrarily large positive $J_{30}$ or negative $J_{32}$ gives no nonzero stationary solution with all hazards below one, whereas $J_{31}$ works on both tails. This example itself has a grand-coalition equilibrium at date one.

## Two independent scales on every hard strict matrix

For the strict-case roles $o,j$ above, let $J=Z_o(\{o,j\})$ and let $R_k=Z_o(\{o,j,k\})$ for the two rivals $k\ne o,j$. Fix $0<\eta\le1$. Suppose that the two $R_k$ have the same weak sign and that $\min_k|R_k|\ge\eta\max_k|R_k|$. Allow $J$ to have either sign, independently of the common sign and magnitude of the two triple rewards. Put $K=\max(|J|,\sqrt{\max_k|R_k|})$. For all $K\ge K_0(G,\eta)$ the strict stationary conclusion holds with the other 41 higher coordinates in the weighted error box, for sufficiently small $\delta(G,\eta)>0$. In particular $R_k=R$ gives a full two-dimensional exterior with $J,R$ independently signed and scaled.

To see this, take a subsequence on which $t=J/K$ and $u_k=R_k/K^2$ converge. At the limit $\max(|t|,\max|u_k|)=1$. The leading field becomes $Gx-H(x)e_o$, with
$$
H(x)=t H_2(x)+U_3(x),\qquad H_2(x)=x_j\sum_{a\ne o}x_a,\qquad
U_3(x)=H_2(x)\sum_{k\ne o,j}u_k x_k .
$$
Each axis root $y^s$ has $o,j$ and another rival positive. Thus $H_2(y^s)>0$ and, if the $u_k$ are nonzero, $U_3(y^s)$ has their common strict sign by comparability. Choose $s$ equal to that sign, or to $\operatorname{sign}(t)$ if $u_k=0$ at the limit. The equation
$$
s\big[t r H_2(y^s)+r^2 U_3(y^s)\big]=1
$$
has a unique positive simple root $r$. Indeed the quadratic coefficient, when present, is positive and the constant after moving 1 to the left is negative. In the linear case the coefficient is positive. Near $x=r y^s$ the map $\Phi(x)=x/|H(x)|$ is a local diffeomorphism: it preserves radial directions, and its radial derivative is nonzero by the simple root just proved. Its image contains $y^s$. In that neighborhood the target minimum at $\Phi(x)$ is precisely $\min(x,Gx-H(x)e_o)/|H(x)|$. The local degree of the leading stationarity equation is therefore nonzero even when an inactive row ties. The same uniform perturbation argument on its isolating neighborhood applies. To see common constants, if none existed one could choose $K>n$, other weighted errors $\le1/n$, and no stationary root with maximum hazard $\le n/K$ and third-largest hazard $\ge 1/(nK)$. A convergent coefficient subsequence and its fixed neighborhood contradict this. This argument also gives uniformity over compact positive ratios of the two triple magnitudes.

## Three raw entries are necessary for a universal two-dimensional stationary exterior

The preceding strict two-scale theorem uses a pair entry and two comparable triple entries. It is impossible, on some strict singleton matrices, to select any two individual nonsingleton entries whose entire two-dimensional exterior produces stationary equilibria with at least two active owners and maximum hazard below one. The two raw entries may even be in different recipient rows. Consider the following integer strict sign-census witness, with all other nonsingleton native entries zero:
$$
G=\begin{pmatrix}
0&-2&-1&3\\-3&0&1&2\\1&1&0&-1\\-3&1&2&0
\end{pmatrix}.
$$
Its four principal triple determinants in lexicographic order are $1,3,3,3$ and its determinant is $3$. Each singleton column has a negative entry. These facts imply $R_0$: with two active coordinates the active singleton equations cannot vanish, with three or four active coordinates the corresponding principal matrix is nonsingular, and one active coordinate is excluded by the negative column entry.

For a stationary hazard vector with every $q_i<1$, write $p_i=q_i/(1-q_i)$. When only one nonsingleton entry $V=Z_o(S)$ varies, the exact field in odds coordinates is $F_i/H_i=(Gp)_i$ off row $o$. Its pivot row is $(Gp)_o-b$, where
$$
 b=-V\prod_{j\in S}p_j \quad(o\notin S),\qquad
 b=V(1-H_o)\prod_{j\in S-o}p_j \quad(o\in S).
$$
A nonzero solution must have $b\ne0$ by $R_0$. If there are at least two active owners then $p_o>0$ since otherwise the active subset in the complementary principal triple cannot have size two or three. Thus $p/|b|$ solves the axis problem at target $\operatorname{sign}(b)e_o$, with its support containing $o$ and every required rival in the displayed product. All axis solutions with $o$ positive are enumerated by supports of size three or four: retain $sG_{SS}^{-1}e_o>0$ only when the outside slacks are nonnegative. This gives

| Recipient | Supports at $-e_o$ | Supports at $+e_o$ |
|---|---|---|
| 0 | 013 | 023 |
| 1 | none | 013 |
| 2 | none | 0123 |
| 3 | 013 | 023 |

In particular, any payoff entry independently capable of both signs must be either $J_{03}=Z_0(03)$ or $J_{30}=Z_3(03)$. Every passive entry would require two common rivals, as would every participating triple or larger coalition. It remains to test those two entries together.

Set $J_{03}=-K$, $J_{30}=K$, $K>0$. A solution with two or more active owners must have $p_0,p_3>0$. If either vanishes the other affected row's extra term vanishes, leaving the nonsingular complementary principal triple's homogeneous equations, which cannot admit two or three active owners. Put $x=p_0/p_3$, $y=p_1/p_3$, $z=p_2/p_3$. The unaffected rows require $-3x+z+2$ and $x+y-1$ to be nonnegative and complementary to $y,z$, respectively. Both $y,z$ cannot vanish, since that would require $x\le2/3$ and $x\ge1$. When both are positive, $2/3<x<1$, and the pivot row 0 has $(Gp)_0/p_3=3-x>0$ although its right side is strictly negative.

If $y>0$ and $z=0$, then $x=2/3$. Row 3 requires $y>2$, and the two pivot equations give
$$
\frac{J_{30}}{|J_{03}|}=
\frac{(y-2)(1-H_0)}{x(2y-3)(1-H_3)}
\le \frac{(y-2)(1+y)}{x(2y-3)(x+y)}<\frac34 .
$$
Indeed $(1-H_0)/(1-H_3)=1+(1-x)/[(1+p_3)(x+y+xyp_3)]\le(1+y)/(x+y)$. If $y=0$ and $z>0$, then $x=1$, the two rival survival probabilities are equal, and row 0 requires $z>3$. The forced ratio is $(2z-3)/(z-3)>2$. Both possible ratios exclude $J_{30}/|J_{03}|=1$, at every $K$. This proves the obstruction. The table still has a grand-coalition equilibrium at date one. The sharpness concerns the universal proper stationary conclusion of the exterior theorem.

## A single coordinate at all tied singleton matrices

**Boundary conclusion.** For every real hollow singleton matrix, including ties and singular matrices, there is a recipient o and a rival j such that making the single native pair payoff $J_{oj}=Z_o(\{o,j\})$ sufficiently large with either sign produces an original uniform equilibrium for all 43 other higher rewards fixed and arbitrary signed own levels. Equivalently, the same type of weighted boxes with some $\delta,K_0>0$ works. On an already solved singleton matrix the conclusion applies to every completion. On the remaining weak matrices the construction usually gives exact proper stationary equilibria on both tails. The sole-quitter construction below gives arbitrarily accurate stationary profiles when the sole owner's signed singleton is negative.

A weak sign pattern that has even one strict refinement solved for all higher rewards is itself solved for every completion, by perturbing its zero singleton comparisons. Otherwise the [sign census](TWENTY_ONE_SINGLETON_SIGN_CLASSES_FOR_FOUR_PLAYER_QUITTING_GAMES.md) leaves 46 one-tie classes, 39 two-tie classes, ten three-tie classes and none with four or more ties. We may suppose the actual $G$ satisfies the previous degree and strict-inverse-column necessities; failure already proves UE for its every completion. Any role chosen below again has $B=G_{TT}$ with a strictly negative nonnegative combination of its rows. Use the normalized compact set of nonnegative directions satisfying complementarity in all rows other than $o$:
$$
 \mathcal D_o=\{x\ge0:\max x_i=1,\ (Gx)_i\ge0,\ x_i(Gx)_i=0\text{ for }i\ne o\}.
$$
Every such direction has $x_o>0$ by the strictly negative combination. If one $j\ne o$ is positive throughout this set, both signs of the one-entry construction apply even if axis solutions form continua. Indeed the nonzero solution set at either target is compact, disjoint from zero (the origin at the negative target is isolated), and lies in $y_j>0$, $\sum_{i\ne o}y_i>0$. Choose a bounded open neighborhood of that set with closure in these inequalities, excluding the origin. Its target degree is one by excision and the degree-zero origin. On its image the involution from the strict proof still gives nonzero degree: its derivative has determinant $-H(y)^{-4}$, by Euler's identity $y\cdot\nabla H=2H$, so it reverses orientation everywhere there. Uniform perturbation and the same weighted-box estimates give a root with at least the two coordinates $o,j$ positive of order $1/K$ and with maximum $O(1/K)$.

For a purely sign-based test enumerate the possible supports of $x\in\mathcal D_o$, containing $o$. In each other active row, the entries on the other active columns must either include both signs or all be zero. Each other inactive row must either have a positive entry on the support or be zero on it. These necessary tests only enlarge the set of supports. The [exact finite checker](../experiments/FIN4_ONE_JOINING_BOUNDARIES.py) permutes the possible choices of $o$ with a strictly negative child combination from the pair test above, and checks for a rival in every surviving support. It succeeds on 42 of 46 one-tie classes, 37 of 39 two-tie classes and all ten three-tie classes. For the six remaining labelled representatives take $o=3$, $T=\{0,1,2\}$. The reciprocal pair 0,1 supplies the negative child combination in each. Set $x_3=1$ by homogeneity and denote the three nonpivot coordinates by $x,y,z$.

On two of the six representatives the three relevant rows evaluate to
$$
 a-b y-c z,\qquad d-e x-f z,\qquad -g+h x+i y,
$$
with all nine letters strictly positive. If $x=0$, the other two coordinates must be positive, so $z=d/f$, $y=g/i$ and the first inequality forces $a/c>d/f$. If $y=0$, then $z=a/c$, $x=g/h$ and the second inequality forces $d/f>a/c$. Thus either $x$ is positive throughout or $y$ is, yielding the claimed single donor.

For the last four representatives the full matrix is
$$
 G=\begin{pmatrix}0&-b&-c&a\\-e&0&f&0\\h&i&0&-g\\r&-s&t&0\end{pmatrix}
$$
with $a,b,c,e,f,g,h,i,s>0$. Here $t>0$ and $r$ has any sign, or $t=0$ and $r>0$. Define
$$
 A=a-bg/i,\qquad D=a-ceg/(fh).
$$
When $x=0$, the second and third rows imply $y>0,z=0$, and $g/i\le y\le a/b$. When $y=0$, the third and second rows imply $x,z>0$, hence $(x,z)=(g/h,a/c)$ and $D\ge0$. Thus $A<0$ or $D<0$ gives a common rival. Suppose both are nonnegative. They cannot both vanish, since $\det G=iA(et+fr)+sfhD>0$. If $x,y>0$, then $z=ex/f$ and $y=(g-hx)/i$ with $0<x<g/h$. The first row would have to vanish, but as a function of $x$ along this segment it is affine with endpoint values $A,D$. Thus all admissible directions either have $(x,y,z)=(0,y,0)$ or equal $P=(g/h,0,a/c)$. The fourth row is strictly negative on the former directions. The degree at $+e_3$ requires a direction with strictly positive fourth row. Consequently
$$
 r g/h+t a/c>0.
$$

If $et+fr\le0$, we have $r<0$ and $t>0$. The last display gives $\rho=-cgr/(aht)\in(0,1)$. On the singleton triangle $(0,2,3)$ take masses proportional to $(-t/r,1,c/a)$ and multiply successive tours by $\rho$. All three active zero equations follow by substitution. In their active rows the directed signs ensure nonnegative tails between visits: row 0 removes a negative and then a positive, row 2 is zero after 0 and increases after 3, and row 3 is zero after 2 and increases after 0. The omitted row 1 has first-tour total $et/r+f\ge0$, increases on removing its negative entry at 0, then decreases until its scaled next-tour initial value, staying constant at 3. Thus the geometric singleton path yields original uniform equilibrium on this entire singleton matrix, independently of all higher payoffs. [All-matrix path theorem](ALL_FOUR_PLAYER_SINGLETON_PATHS_HAVE_A_FINITE_TEST.md)

If $et+fr>0$ and $t>0$, select the joining reward $J_{02}$. The adjugate column at 0 is $(fgs,g(et+fr),egs,i(et+fr)+fhs)$, strictly positive, so the positive target has a nonzero-index full solution at recipient 0 and the positive large reward gives a proper stationary root. For $J_{02}=-K$ let owner 2 alone use constant hazard $q_2=2c/K$ for $K$ large. For owner 0 the actual passive native value is $-c$ and the immediate offer is $-2c$. For owners 1 and 3, the respective passive values $f$ and $t$ are strictly positive and the immediate offers $q_2J_{12}$ and $q_2J_{32}$ are smaller for the stated weighted error box after decreasing $\delta$. Owner 2 receives zero on every native reply. This is an exact native equilibrium with a single active owner; if its original own level is nonnegative it is also exact after restoring all signed rows. At arbitrary signed own levels give owner 3 a small stationary hazard $\varepsilon$ and owners 0 and 1 hazards $\varepsilon^2$, leaving $q_2$ fixed. Against any unilateral replacement a rival then absorbs surely, so row translations preserve every regret. As $\varepsilon\downarrow0$ the native prescriptions, immediate offers, and Never offers of all owners other than 2 converge to their solo-owner values. Row 2's native prescription and immediate offer tend to zero, and its Never offer tends to $G_{23}=-g<0$ because 3 accounts for asymptotically all rival exits. The stationary endpoint comparison thus gives terminal regret tending to zero, hence an original fixed uniform target. The limit in $\varepsilon$ is taken at each fixed reward table.

The remaining possibility $t=0,r>0$ gives a strictly positive adjugate column at 1:
$$
 (cgs,\ cgr,\ ahs+r(ai-bg),\ chs+cir).
$$
Its full positive-target solution is transverse. At target $-e_1$ there is also a transverse solution on support $\{0,1,3\}$. Give owner 1 weight one, owner 0 weight $s/r$, and owner 3 weight $b/a$. Rows 0 and 3 vanish, row 1 equals $-es/r$, and omitted row 2 has value $hs/r+i-gb/a>0$. The active principal determinant is $aes>0$. Normalize by $es/r$. With common donor 0 the previous local transformations give proper exact stationary equilibria for both signs of $J_{10}$. This exhausts the weak sign classes and proves the boundary conclusion.

## Ten independently unbounded recipient payoffs

For the all-matrix roles $o,j$ put $s=\operatorname{sign}J_{oj}$, $K=|J_{oj}|$. All 33 nonsingleton entries in other rows retain the weighted bounds above. Each of the other ten nonsingleton entries in row $o$ needs only a one-sided bound:
$$
 s Z_o(S)\ge-\delta K^{|S|-1}\quad(o\in S),\qquad
 s Z_o(S)\le\delta K^{|S|-1}\quad(o\notin S).
$$
The opposite sides can grow independently, faster than any function of $K$. The original UE conclusion still holds. On the proper stationary branches the maximum hazard remains $O(1/K)$. The same selected two or three hazards are at least $c/L$, where $L=\max(1,K,\max_{i,S:\,|S|\ge2}|Z_i(S)|^{1/(|S|-1)})$.

On a degree branch take the compact isolated nonzero-index set $Y$ at $s e_o$ used above. Its normalized directions form an isolated part of the unit-sphere directions $v\ge0$ complementing $Gv$ in every nonpivot row. Indeed $v_o,v_j,s(Gv)_o$ are bounded below there, and the inverse radial normalization is $v\mapsto v/|(Gv)_o|$. Choose an angular neighborhood $O$ in the whole unit sphere with closure inside those strict inequalities, containing no other complementary directions in its closure, and preserving each further selected positive coordinate. Linearly homotope all higher entries except $J_{oj}$ from zero to their final values. At a complementary zero one always has $q\ge0$. For $r=\|q\|$, $v=q/r$, the nonpivot fields obey uniformly
$$
F_i(q)/r=(Gv)_i+O_G(r)+O\!\left(\delta\sum_{d=2}^4(Kr)^{d-1}\right).
$$
Thus for $0<r\le C/K$, large $K$ and small $\delta$ there are no zeros on the angular boundary, by compactness. At $r=C/K$ the distinguished term in $sF_o/r$ is at most $-c_0Kr$: here $q_j/r$ is bounded below, $1-H_o\ge q_j$, and remaining wait factors tend uniformly to one. At nonnegative $q$ all ten unrestricted portions have the same favorable sign as this term. Their adverse portions cost at most $O(\delta\sum_{d=2}^4 C^{d-1})$; the singleton contribution is bounded. Choose $C$ large, then $\delta$ small and $K$ large, making $sF_o/r<0$ on the outer sphere, whereas $q_o>0$ requires zero. For $0<r\le c/L$ all rows are uniformly close after division by $r$ to $Gv$ by the same monomial estimate with $L$ in place of $K$. The $R_0$ property and compactness exclude zeros for small $c$.

At the initial table only $J_{oj}$ is nonzero among higher entries, so the inner exclusion holds all the way to $c/K$. In $c/K<r<C/K$, rescale by $K$. The limiting field on the angular sector has precisely the radial image of $Y$ as its zero set, interior for $c$ small and $C$ large, with nonzero degree by the involution above. Uniform convergence transfers this degree to the initial table. The boundary estimates then carry it throughout the homotopy in $c/L<r<C/K$. Every resulting root has the asserted lower and upper hazard bounds. On the exceptional negative tail with sole owner 2 the ten other entries of the pivot row contribute to none of the limiting offers. The fixed-table signed perturbation there still applies. The cases solved for every completion require no bounds.

## One positive joining entry and three unrestricted recipient rows

Suppose a row $i$ has one strictly positive foreign singleton comparison $G_{ij}$ and two strictly negative ones. A sufficiently large **positive** native joining reward $K=Z_i(\{i,j\})$ then guarantees an original uniform-equilibrium payoff under the following one-row conditions. The other three recipients have all **45 original entries arbitrary**, even for fixed $K$. In row $i$ the other ten nonsingleton entries need only satisfy
$$
 Z_i(T)\ge-\delta K^{|T|-1}\quad(i\in T),\qquad
 Z_i(T)\le\delta K^{|T|-1}\quad(i\notin T),\qquad |T|\ge2 .
$$
The favorable direction is unlimited at each of these ten entries. The explicit $K_0,\delta>0$ below depend only on this row's three foreign singleton comparisons. All four signed own singleton levels are free.

For every fixed real singleton matrix, including ties, either its every completion already has a uniform-equilibrium payoff, or it admits a row of the indicated type. In the second branch the resulting certificate allows the other three singleton rows to vary as well. Indeed if the fixed matrix admits a positive-gap completion, its $G$ has a strictly positive inverse column and must have a strictly negative entry in every row. The latter also follows by perturbing that row's foreign ties upward and applying the positive-row exit. Perturb all foreign ties upward in a hypothetical positive-gap completion. The gap persists for a sufficiently small perturbation. Each canonical representative in the 21-class strict census has first mask 2, hence a row with just one positive rival. Before the perturbation its corresponding row $i$ already had two strictly negative rivals. Multiplying that row by the positive inverse column shows that the remaining rival $j$ is strictly positive. This proves the required selection on tied matrices as well. Matrices already excluded by the previous necessities have a uniform payoff for every completion. [Strict census and weak-face reduction](TWENTY_ONE_SINGLETON_SIGN_CLASSES_FOR_FOUR_PLAYER_QUITTING_GAMES.md) · [Negative rows and columns](FIVE_NONSINGLETON_REWARDS_AND_THE_SIX_ENTRY_FRONTIER.md)

There is a version at **every prescribed recipient** $i$ of a possible counterexample. Let $A=\{j\ne i:G_{ij}\ge0\}$ and $K=\min_{j\in A}Z_i(\{i,j\})$. Every hard row has a negative entry and at least one positive entry by the inverse-column condition, so $1\le |A|\le2$. Impose the displayed one-sided bounds only on entries other than these $|A|$ joining rewards. There is no upper bound on their ratios, and the three other recipient rows are again completely arbitrary.

To prove both statements write $p_T=Z_i(T)$, $j_T=Z_i(T+i)$ on nonempty subsets of the three opponents. Put
$$
 \theta=\frac1{2\max(1,\max_{k\ne i}G_{ik})},\quad
 b=\min\{1/2,\ \theta\min_{k\notin A,\ k\ne i}(-G_{ik})\},\quad
 C=1+(1+\theta)\bigl[3(2/\theta)+(2/\theta)^2\bigr].
$$
Take $K_0=2/\theta$ and $\delta=b/(2C)$. The previously published seven-coalition criterion for a single recipient tests all nonempty opponent subsets $S$ at one common scalar $c\ge1$. Its left sides, divided by $(c-1)^{|S|-1}$ when $c>1$, are
$$
 \sum_{k\in S}(j_{\{k\}}-cG_{ik})+
       \sum_{\substack{T\subseteq S\\|T|\ge2}}
       (c-1)^{1-|T|}(j_T-cp_T).
$$
Choose $c=\theta K\ge2$. For a paid singleton its bracket is at least $K/2$, and for a negative singleton it is at least $(b-\delta)K$. Thus the singleton sum for any nonempty $S$ is at least $(b-\delta)K$. Each remaining term has lower bound $-\delta K(1+\theta)(2/\theta)^{|T|-1}$, since $c-1\ge\theta K/2$. There are at most three pairs and one triple. Every test is therefore at least $K(b-C\delta)>0$. The seven-coalition criterion gives the original uniform payoff. This is an explicit exterior of that existing criterion, obtained using the singleton census. In particular any counterexample with large positive joining rewards at all its nonnegative donors must have a comparably large adverse reward **in that same recipient row**, irrespective of the other payoffs. [One-recipient seven-coalition criterion, inequality (3)](ONE_RECIPIENT_JOINING_PAYOFF_UNIFORM_EQUILIBRIUM.md)

For comparison take the census matrix with rows $(0,-1,-1,3),(-1,0,-1,2),(-1,2,0,-1),(-1,-1,2,0)$. Set $Z_0(03)=K$, $Z_2(0123)=-K^6$, $Z_0(12)=1$, $Z_0(012)=-1$, and every other native higher entry to $1/100$. Row 0 passes the seven comparisons for all sufficiently large $K$. Its unrestricted-cube implication $P>0\Rightarrow Q\ge P$ fails at the pure rival set $12$, where $P=1,Q=-1$. At each other recipient that same implication fails against its sole positive singleton donor. No assignment of the two reciprocal endpoint guards works: the first forces the other core owner to be the tested row's unique positive donor, who sees it negatively since the matrix has no mutually positive pair; the second at zero leaf hazards then fails because all participating pair entries are positive. The growing pair is the only possible distinguished joining entry at unbounded scale; the other recipient's negative grand violates the earlier all-matrix one-joining bounds, including their one-sided stretch in the distinguished row. For weighted collision dominance the negative grand lies outside the favorable positions at every proper support. At full support column 2 of $G^{-1}$ equals $(3,7,5,4)^\top/7>0$, making the negative participant reward adverse there too. Its adverse scale $K^2$ exceeds every favorable scale, which is at most $K$. All higher entries in this comparison are nonzero. [One joining entry on all matrices](ONE_JOINING_PAYOFF_ON_EVERY_FOUR_PLAYER_SINGLETON_MATRIX.md) · [Weighted collision criterion](WEIGHTED_COLLISION_DOMINANCE_UNIFORM_EQUILIBRIUM.md)
