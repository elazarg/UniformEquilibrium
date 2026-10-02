The decisive issue is **finite hazard capacity**, not compact existence of an exact spine. Compactness always admits the all-Continue phantom, and the repository explicitly records that this source-free spine has zero clock and cannot distinguish a counterexample.

I do not obtain the boxed implication from the present Fin4 source machinery. I do obtain the following source-preserving selection theorem, which substantially sharpens the remaining alternative.

## 1. Hazard-capacity selection theorem

For a product root \(x\), write

$$
q_i(x):=\Pr_x(i\text{ Quits}),
\qquad
h(x):=\sum_{i\in\operatorname{Fin}4}q_i(x).
$$

Thus \(0\le h(x)\le4\).

Consider a trace-safe family \(\mathcal B\) of finite, exact, source-provenant Nash–Bellman blocks

$$
B=(v_0,x_0,v_1,x_1,\ldots,x_{n-1},v_n)
$$

such that

$$
v_t=F_{x_t}(v_{t+1}),
\qquad
x_t\in\operatorname{NE}(v_{t+1}),
$$

all \(v_t\) lie in one compact set \(K\subseteq\mathbb R^4\), and every contiguous subblock retains its actual source provenance.

Define the hazard charge

$$
H(B):=\sum_{t<n}h(x_t).
$$

### Theorem — unbounded finite hazard capacity gives one persistent spine

Suppose

$$
\sup_{B\in\mathcal B}H(B)=\infty.
\tag{1}
$$

Then, for every \(\eta>0\), there are bounded payoff annotations \(w_t\), one literal infinite product-root sequence \(y_t\), and nonnegative Bellman and root-Nash errors \(\beta_t,\nu_t\) such that

$$
\|w_t-F_{y_t}(w_{t+1})\|_\infty\le\beta_t,
\tag{2}
$$

$$
\sup_{z_i}
\left(
F_{y_t[i\leftarrow z_i]}(w_{t+1})_i
-
F_{y_t}(w_{t+1})_i
\right)
\le\nu_t,
\tag{3}
$$

$$
\sum_t(\beta_t+\nu_t)<\eta,
\tag{4}
$$

and

$$
\sum_t h(y_t)=\infty.
\tag{5}
$$

Consequently there is one fixed player \(p\in\operatorname{Fin}4\) such that

$$
\sum_tq_p(y_t)=\infty.
\tag{6}
$$

Every root \(y_t\) is copied from one of the actual source blocks. The only nonexact operations are the displayed seams, whose total error is absolutely summable.

### Proof

Two elementary estimates control a seam.

For every root \(x\) and tails \(u,w\),

$$
\|F_x(u)-F_x(w)\|_\infty\le \|u-w\|_\infty,
\tag{7}
$$

because the tail enters \(F_x\) multiplied by the all-Continue probability.

If \(x\) is exact Nash against \(u\), then its Nash defect against \(w\) is at most

$$
2\|u-w\|_\infty.
\tag{8}
$$

Indeed, for any unilateral root replacement \(z_i\),

$$
\begin{aligned}
&F_{x[i\leftarrow z_i]}(w)_i-F_x(w)_i\\
={}&
\bigl(F_{x[i\leftarrow z_i]}(w)_i
      -F_{x[i\leftarrow z_i]}(u)_i\bigr)\\
&+\bigl(F_{x[i\leftarrow z_i]}(u)_i-F_x(u)_i\bigr)
 +\bigl(F_x(u)_i-F_x(w)_i\bigr).
\end{aligned}
$$

The middle term is nonpositive, and the other two have absolute value at most
\(\|u-w\|_\infty\).

Now fix \(\delta>0\). Cover the compact set \(K\) by \(N\) sets of diameter less than \(\delta\). By (1), choose a source block \(B\) with

$$
H(B)>5N.
$$

Let

$$
C_t:=\sum_{s<t}h(x_s).
$$

For \(j=0,\ldots,N\), let \(t_j\) be the first index for which \(C_{t_j}\ge5j\). Since one edge has charge at most \(4\),

$$
C_{t_j}<5j+4.
\tag{9}
$$

Among the \(N+1\) vectors \(v_{t_0},\ldots,v_{t_N}\), two, say
\(v_{t_a}\) and \(v_{t_b}\) with \(a<b\), belong to the same cover element. Therefore

$$
\|v_{t_a}-v_{t_b}\|_\infty<\delta,
\tag{10}
$$

while the intervening source subblock has hazard charge

$$
C_{t_b}-C_{t_a}
\ge 5(b-a)-4
\ge1.
\tag{11}
$$

Apply this construction with \(\delta_k\downarrow0\). We obtain exact source subblocks \(B_k\), each with charge at least \(1\), whose two endpoint payoff vectors have distance tending to zero. By compactness, pass to a subsequence for which both endpoints converge to one vector \(z\). Refine once more so that, writing \(a_k\) and \(b_k\) for the initial and terminal payoff of \(B_k\),

$$
\sum_k\|b_k-a_{k+1}\|_\infty<\eta/3.
\tag{12}
$$

Concatenate the literal root words of the \(B_k\). Every internal edge remains exact. At the seam following \(B_k\), the final root expected tail \(b_k\), while the actual next annotated value is \(a_{k+1}\). By (7)–(8), that seam contributes at most

$$
\beta\le\|b_k-a_{k+1}\|_\infty,
\qquad
\nu\le2\|b_k-a_{k+1}\|_\infty.
$$

Equation (12) gives (4). Each block contributes at least one unit of total marginal hazard, proving (5). Finally,

$$
\sum_i\sum_tq_i(y_t)=\sum_t h(y_t)=\infty.
$$

Since there are four players, at least one fixed \(p\) satisfies (6). This label is chosen once for the entire flattened sequence, not afresh on different blocks. ∎

### Exact-cycle special case

If one source block has equal endpoints and positive hazard charge, periodic repetition gives an **exact** bounded Nash–Bellman spine with a persistent fixed player. No seam estimates are then needed.

## 2. Consequence for a hypothetical Fin4 counterexample

Under the premise in the question that every nonempty persistent set is consumed, the theorem gives the following necessary condition for a counterexample.

For every compact trace-safe actual-source graph \(\mathcal G\),

$$
\boxed{
\sup\left\{
\sum_{t<n}\sum_iq_i(x_t):
\begin{array}{c}
\text{finite exact Nash--Bellman block}\\
\text{legally generated inside }\mathcal G
\end{array}
\right\}<\infty.
}
\tag{FC}
$$

This is strictly stronger than saying that every infinite selected spine has four summable marginal streams. It also rules out hazard mass that escapes to later and later positions in unrelated finite chains: unbounded finite towers would themselves yield the required persistent spine by the theorem above.

The supplied unique-persistent result leaves precisely the zero-persistent alternative and explicitly does not select a nonsummable marginal or consume the phantom. 

Once (FC) holds, define the hazard-capacity potential

$$
\Phi(s):=
\sup\left\{
\sum_{t<n}h(x_t):
\text{source-legal exact block beginning at }s
\right\}.
\tag{13}
$$

For every legal exact edge \(s\xrightarrow{x}s'\),

$$
\Phi(s)\ge h(x)+\Phi(s').
\tag{14}
$$

Hence every infinite legal path satisfies

$$
\sum_{t<N}h(x_t)
\le \Phi(s_0)-\Phi(s_N)
\le \Phi(s_0),
\tag{15}
$$

and therefore has summable total hazard. Thus a counterexample is forced into a genuine **finite-capacity all-summable component**. Merely selecting another compact path cannot escape it.

## 3. What an all-summable exact spine actually implies

Suppose an exact bounded spine has

$$
\sum_tq_{t,i}<\infty
\qquad\text{for every }i.
\tag{16}
$$

Let

$$
a_t:=1-\prod_i(1-q_{t,i})
$$

be its one-row absorption probability. Then

$$
a_t\le\sum_iq_{t,i},
\qquad
\sum_ta_t<\infty.
\tag{17}
$$

If rewards and spine values are bounded by \(K\), the Bellman identity gives

$$
\|v_t-v_{t+1}\|_\infty\le2Ka_t.
\tag{18}
$$

Consequently \(v_t\to z\) for some \(z\).

Since \(q_{t,i}\to0\), exact root Nash and passage to the limit imply

$$
r_i(\{i\})\le z_i.
\tag{19}
$$

Moreover, if \(q_{t,i}>0\) at infinitely many dates, then eventually both Quit and Continue are in player \(i\)'s support on those dates. Exact indifference gives

$$
z_i=r_i(\{i\}).
\tag{20}
$$

The actual executable suffix payoff tends to zero because its future absorption probability is bounded by the tail of \(\sum_ta_t\). The exact repository theorem identifies the residual unrestricted behavioral cap: late exploitability converges to the positive part of the singleton self-payoffs. In particular, if every \(r_i(\{i\})\le0\), the late suffixes are terminal approximate Nash profiles and zero is a uniform-equilibrium payoff.

Thus, in a hypothetical counterexample, an all-summable spine only forces

$$
\max_i r_i(\{i\})>0.
\tag{21}
$$

It does **not** force any prescribed marginal hazard to diverge.

## 4. A Fin4 regression showing why pointwise compactness is insufficient

Let \(I=\operatorname{Fin}4\), distinguish player \(0\), and define

$$
r_0(S)=
\begin{cases}
1,&0\in S,\\
0,&0\notin S,
\end{cases}
\qquad
r_j(S)=0\quad(j\ne0).
\tag{22}
$$

For each \(N\ge2\), construct a length-\(N\) exact chain with terminal boundary

$$
v_N=0
$$

and

$$
v_t=e_0:=(1,0,0,0)
\qquad(0\le t<N).
$$

At the last row let player \(0\) Quit surely. At every earlier row let player \(0\) Quit with probability

$$
N^{-1/2},
$$

and let all other players Continue surely.

At an earlier row, player \(0\)'s Quit and Continue values are both \(1\); all other players always receive \(0\). Hence the root is exact Nash and its Bellman value is \(e_0\). At the last row, Quit gives player \(0\) value \(1\), whereas Continue gives \(0\), so sure Quit is exact Nash.

The total finite hazard is

$$
1+\frac{N-1}{\sqrt N}\longrightarrow\infty.
\tag{23}
$$

Nevertheless, for every fixed date \(t\),

$$
q^{(N)}_{t,0}\longrightarrow0,
\qquad
v^{(N)}_t=e_0.
$$

The ordinary prefix-diagonal compact limit is therefore the constant all-Continue phantom spine at \(e_0\), with zero marginal hazards. Its literal all-Continue behavioral profile has payoff zero and is exploitable by player \(0\) by one unit.

So even

* actual four-player reward data,
* exact zero-boundary finite chains, and
* unbounded total finite hazard

do not survive pointwise compactification. The block theorem above repairs this particular escape by extracting near-return subblocks before taking the limit. The example is a solved game, so it does not refute the counterexample-dependent implication; it isolates why the source discriminator is indispensable.

## 5. Why the current positive-minimum source does not finish the proof

The present Fin4 source machinery reaches exactly the finite-capacity alternative.

First, the positive minimum fiber has one open prescribed-payoff tube in which all-Continue is the unique exact root. A positively absorbing exact root against a carrier tail near that fiber must pay a fixed excess-debt moat. Thus an exact positive-charge block cannot simply enter and return locally to the minimum plateau.

Second, the actual forward exact-cap ray is source-attached and has a strictly positive but summable hazard clock. It is a predecessor ray

$$
b_{n+1}=F_{y_n}(b_n),
\qquad
y_n\in\operatorname{NE}(b_n),
\tag{24}
$$

whereas a chronological spine would have to read these edges backwards. The structure deliberately assumes summable absorption and produces no terminal profile by itself.

Third, the strongest current strict-ray capstone is the exhaustive alternative

$$
\begin{array}{l}
\text{fresh minimum-law handoff},\\
\text{strict off-minimum descent},\\
\text{ballistic renewal},\\
\text{one fixed player omitted infinitely often},\\
\text{or binding face of cardinality three}.
\end{array}
\tag{25}
$$

None of those conclusions currently supplies a renewable rank decrease or one concatenable nonsummable chronological root stream.

There is also a structural obstruction to the simplest near-return argument. On the full binding face, the first-order cap law has the form

$$
\frac{b_b-b_a}{\sum_{n=a}^{b-1}h(y_n)}
=
M\bar q_{a,b}+o(1),
\tag{26}
$$

where \(M\) is the normalized singleton matrix and \(\bar q_{a,b}\) is a simplex-valued average hazard direction. A sequence of full-binding blocks with normalized displacement tending to zero would yield, after compactification,

$$
Mh=0
$$

for a nonnegative simplex vector \(h\), hence a homogeneous singleton-LCP solution. The Fin4 hard residual excludes such a solution. This is why the checked full-binding reduction produces ballistic renewal or support loss rather than the zero-drift return needed for straightforward block repetition.

Finally, a paid first-disagreement row cannot substitute for hazard charge. The corrected source theorem gives

$$
\text{charged near-return}
\;\lor\;
\text{quantitative debt descent}
\;\lor\;
\text{inert stall},
\tag{27}
$$

and explicitly retracts the implication from a paid payoff premium directly to an admissible charged return. 

## 6. Exact remaining implication

The selection question is therefore reduced to the following sharper statement:

$$
\boxed{
\begin{array}{c}
\text{positive-minimum Fin4 source with finite exact hazard capacity}\\[2mm]
\Longrightarrow\\[2mm]
\text{terminal approximate Nash profiles, or a trace-safe}\\
\text{regeneration to a strictly smaller well-founded source rank.}
\end{array}}
\tag{28}
$$

Equivalently, one must consume the finite-capacity all-summable/inert component. Unbounded exact source capacity is already enough, by the theorem in Section 1, to select the required fixed persistent label with summable seams.

No independently checkable positive-gap Fin4 table is present in the current source or supplied files. The exact rational semidecision procedure proves that a genuine counterexample would eventually yield such a finite certificate, but it has not supplied one; nontermination has no mathematical conclusion. 

Accordingly, the boxed implication in the question is **not established here**, but its remaining content is no longer general spine selection: it is precisely the consumption or well-founded regeneration of the finite-hazard-capacity positive-minimum source component.

The hazard-capacity theorem above is a paper-level proof and has not been added to or compiled in Lean. I inspected the current repository state and made no source or branch changes; this distinction follows the project’s validation and provenance requirements. 

## Followup 1

The correction separates into three facts:

1. unbounded finite hazard capacity does give one literal persistent approximate Nash–Bellman spine with summable seams, from a precise proof-relevant source graph;
2. those summable errors are accepted by the existing consumers after suffixing, with one fixed persistent label and one fixed limiting payoff;
3. finite capacity is only a real-valued Lyapunov bound. It is neither generally upper semicontinuous nor attained, and it has no uniform positive drop. In the positive-minimum Fin4 branch, it yields a genuine finite rank only on nonlocal returns carrying a fixed debt-excess toll.

The remaining unresolved branch is a retained off-minimum all-Continue-inert source, not generic spine selection.

## 1. A precise source graph and provenance interface

Fix \(I=\operatorname{Fin}4\), the reward table \(r\), and

$$
X:=\prod_{i\in I}\Delta\{C,Q\}.
$$

Write \(q_i(x)=x_i(Q)\) and

$$
h(x):=\sum_{i\in I}q_i(x)\in[0,4].
$$

A **witness-lifted compact exact Nash–Bellman source graph** is the following data.

### States and proof-relevant edges

There are compact metrizable spaces \(S\), \(E\), and \(A\), with continuous maps

$$
\partial_0,\partial_1:E\to S,\qquad
x:E\to X,\qquad
v:S\to[-R,R]^I,\qquad
\operatorname{origin}:S\to A.
$$

An element \(e\in E\) is the complete proof-relevant edge witness. Its visible edge is

$$
\partial_0e\xrightarrow{x(e)}\partial_1e.
$$

The map

$$
e\longmapsto \bigl(\partial_0e,x(e),\partial_1e\bigr)
$$

has compact—and hence closed—image in \(S\times X\times S\). Distinct legal witnesses with the same visible endpoints are not identified.

Every edge preserves the original source packet:

$$
\operatorname{origin}(\partial_0e)
=
\operatorname{origin}(\partial_1e).
\tag{1}
$$

The state space is already witness-lifted: all source profiles, outcome laws, marks, optimizer witnesses, and other data required to validate an edge are part of the point of \(S\) or \(E\), rather than being existentially forgotten after edge selection.

### Exact Nash–Bellman legality

For every \(e\in E\),

$$
v(\partial_0e)
=
F_{x(e)}\bigl(v(\partial_1e)\bigr),
\tag{2}
$$

and

$$
\operatorname{NDef}_r
   \bigl(x(e);v(\partial_1e)\bigr)=0,
\tag{3}
$$

where

$$
\operatorname{NDef}_r(x;w)
:=
\max_{i\in I}
\sup_{y_i\in\Delta\{C,Q\}}
\left[
F_{x[i\leftarrow y_i]}(w)_i-F_x(w)_i
\right]_+ .
$$

Thus every visible edge is an exact root-Nash Bellman edge against its displayed successor value.

### Paths and actual behavioral compiler

For \(m\in\mathbb N\), let \(\operatorname{Path}_m(\mathcal G)\) be the compact fiber product consisting of tuples

$$
P=(e_0,\ldots,e_{m-1})
$$

satisfying

$$
\partial_1e_j=\partial_0e_{j+1}
\qquad(j+1<m).
$$

For an actual behavioral tail \(\tau\), define

$$
\operatorname{Comp}_m(P,\tau)
=
x(e_0)\triangleright
x(e_1)\triangleright\cdots\triangleright
x(e_{m-1})\triangleright\tau .
\tag{4}
$$

This is the ordinary finite product-root prefix compiler. It is continuous and has exact stopping-law semantics, including every finite stopping date and Never. Every contiguous restriction of \(P\) is again a path with the same source origin by (1).

For an infinite list of finite paths, its decoder is the actual behavioral profile whose root sequence is the flattened list of roots. The seams are not asserted to be edges of \(E\); they are separately tagged decoder seams with displayed Bellman and Nash budgets.

This is the precise replacement for “trace-safe family.” The compact edge witness, the closed visible relation, and the actual compiler are all explicit.

## 2. Hazard-capacity extraction theorem

Fix \(a\in A\), and consider only states and paths of origin \(a\). For a finite path \(P=(e_0,\ldots,e_{m-1})\), define

$$
H(P):=\sum_{j<m}h(x(e_j)).
$$

Define its finite-path capacity by

$$
\operatorname{Cap}(a)
:=
\sup\left\{
H(P):
P\in\operatorname{Path}_m(\mathcal G)
\text{ for some }m,\ 
\operatorname{origin}(\partial_0e_0)=a
\right\}.
$$

### Theorem 1 — witnessed unbounded-capacity extraction

Assume

$$
\operatorname{Cap}(a)=\infty.
\tag{5}
$$

Then there exist:

* source paths \(B_k\), each a contiguous path of origin \(a\);
* one actual flattened root sequence \(y_t\);
* one uniformly bounded payoff sequence \(w_t\);
* nonnegative Bellman errors \(\beta_t\);
* nonnegative root-Nash errors \(\nu_t\);

such that

$$
\left\|
w_t-F_{y_t}(w_{t+1})
\right\|_\infty
\le \beta_t,
\tag{6}
$$

$$
\operatorname{NDef}_r(y_t;w_{t+1})
\le \nu_t,
\tag{7}
$$

$$
\sum_t\beta_t<\infty,
\qquad
\sum_t\nu_t<\infty,
\tag{8}
$$

$$
\sum_t h(y_t)=\infty,
\tag{9}
$$

and every nonzero \(\beta_t,\nu_t\) occurs at a displayed seam between two source paths. The seam totals can be made smaller than any prescribed positive bound.

Consequently, one fixed player \(p\in I\) satisfies

$$
\sum_tq_p(y_t)=\infty.
\tag{10}
$$

The roots \(y_t\) form one actual behavioral profile; \(p\) is fixed for that entire profile.

### Proof

Let \(\rho>0\). Compactness of \(v(S_a)\) gives a cover by \(N\) sets of diameter less than \(\rho\).

By (5), choose a source path \(P\) with

$$
H(P)>5N.
$$

Write

$$
C_j=\sum_{\ell<j}h(x(e_\ell)).
$$

For \(r=0,\ldots,N\), let \(t_r\) be the first index with

$$
C_{t_r}\ge 5r.
$$

Since one root has \(h(x)\le4\),

$$
C_{t_r}<5r+4.
\tag{11}
$$

Two of the \(N+1\) values \(v(s_{t_r})\) lie in the same cover element. Say they correspond to \(r<s\). The intervening contiguous source block \(B\) then satisfies

$$
\left\|v(\operatorname{start}B)-v(\operatorname{end}B)\right\|_\infty
<\rho
\tag{12}
$$

and

$$
H(B)
=
C_{t_s}-C_{t_r}
\ge5(s-r)-4
\ge1.
\tag{13}
$$

Apply this with \(\rho\downarrow0\). By compactness, pass to blocks \(B_k\) whose two endpoint values both converge to one \(z\in[-R,R]^I\). Thin them so that, writing \(a_k,b_k\) for their initial and terminal values,

$$
d_k:=\|b_k-a_{k+1}\|_\infty
$$

satisfies

$$
\sum_k d_k<\infty.
\tag{14}
$$

Flatten the root words of the \(B_k\). Every internal edge remains exact. At the seam after \(B_k\), the last source edge was Nash–Bellman against \(b_k\), while the decoded successor annotation is \(a_{k+1}\).

For every root \(x\), both \(F_x\) and every unilateral-replacement payoff \(F_{x[i\leftarrow y_i]}\) are \(1\)-Lipschitz in the continuation vector. Therefore

$$
\beta_{\mathrm{seam}}\le d_k,
\qquad
\nu_{\mathrm{seam}}\le2d_k.
\tag{15}
$$

This proves (6)–(8). Equation (13) gives

$$
\sum_t h(y_t)
\ge\sum_kH(B_k)
\ge\sum_k1
=\infty.
$$

Finally,

$$
\sum_i\sum_tq_i(y_t)
=
\sum_t h(y_t)
=
\infty,
$$

so at least one fixed player satisfies (10). ∎

This theorem is source-dependent. The canonical all-Continue phantom graph simply has capacity zero; compact spine existence alone remains useless, exactly as fenced in the current clock-reduction module.

An exact positive-charge cycle is the special case in which \(b_k=a_{k+1}\) identically. Then the repeated spine is exact and has no seams. Compactness alone does not force such a cycle.

## 3. Closing the consumer quantifiers

The strongest formulation uses **one** extracted approximate spine, rather than a new spine for every accuracy.

Let

$$
\beta_t
=
\left\|w_t-F_{y_t}(w_{t+1})\right\|_\infty
$$

and let \(\nu_t\) bound its root-Nash defect. Define tail budgets

$$
B_N:=\sum_{t\ge N}\beta_t,
\qquad
Q_N:=\sum_{t\ge N}\nu_t.
\tag{16}
$$

Then \(B_N,Q_N\to0\).

Let

$$
P:=
\left\{
i\in I:\sum_tq_i(y_t)=\infty
\right\}.
$$

This is one fixed nonempty subset of \(I\). No player label is selected afresh after suffixing.

### 3.1 At least two persistent players

Suppose \(|P|\ge2\). Choose fixed distinct \(p,q\in P\). The repository theorem then gives, on every suffix,

* vanishing joint survival;
* vanishing survival after deleting any one player.

This is exactly the two survival fields required by the chronological certificate.

For the suffix starting at \(N\), use the shifted roots \(y_{N+t}\), the shifted prescribed values \(w_{N+t}\), and candidate debt identically zero.

The generated secant construction is unchanged from the exact-spine adapter. The nonzero certificate fields satisfy the following estimates.

The prescribed defect is the Bellman residual, so for every player \(i\), start \(s\), and length \(L\),

$$
\left|
\sum_{\ell<L}
\operatorname{prescribedDefect}_{N+s+\ell,i}
\right|
\le B_N.
\tag{17}
$$

For a diagonal candidate successor \((w_{t+1},w_{t+1})\), its one-stage semantic debt is at most the root-Nash defect:

$$
0\le
d^{\mathrm{prefix}}_{t,i}
\le\nu_t.
\tag{18}
$$

Since candidate debt is zero, the direct debt defect is

$$
\operatorname{directDebtDefect}_{t,i}
=
-d^{\mathrm{prefix}}_{t,i}.
$$

Every generated-secant survival weight lies in \([0,1]\), hence for every finite length,

$$
-\sum_{\ell<L}
\operatorname{weight}_{\ell,i}
\operatorname{directDebtDefect}_{N+s+\ell,i}
\le Q_N.
\tag{19}
$$

Thus the shifted data is a `QuittingChronologicalDebtShadowingCertificate` at every accuracy

$$
\eta>\max(B_N,Q_N).
\tag{20}
$$

The generic certificate structure was designed precisely with finite-suffix prescribed discrepancy and weighted adverse direct forcing, rather than demanding that both defects vanish pointwise. It evaluates the literal executable root-sequence profile and its unrestricted behavioral best-response cap.

The current exact adapter proves only the zero-error specialization: exact Bellman makes prescribed defect zero and exact root Nash makes direct debt defect zero. The estimates (17)–(19) are therefore a missing local adapter theorem, not a modification of the chronological compiler itself.

A suitable Lean-facing statement is:

$$
\begin{aligned}
&\operatorname{Summable}(\beta)
\ \land\
\operatorname{Summable}(\nu)
\ \land\
\operatorname{HasTwoPersistentQuittingMarginals}(y)\\
&\qquad\Longrightarrow
\forall\eta>0,\ \exists N,\
\operatorname{Nonempty}
\bigl(
\operatorname{Certificate}_r
(\operatorname{shift}_N y)
(\operatorname{shift}_N w)
\,\eta
\bigr).
\end{aligned}
\tag{21}
$$

The existing all-errors theorem then supplies one fixed uniform-equilibrium payoff. It already performs compact terminal-payoff selection from certificates at every positive accuracy.

### 3.2 Freezing the limiting payoff explicitly

Let \(u_N\) be the actual terminal payoff of the behavioral root-sequence profile beginning at \(N\).

Because at least one player is persistent, joint survival tends to zero on every suffix. Unrolling the Bellman residual gives

$$
\|u_N-w_N\|_\infty
\le B_N.
\tag{22}
$$

Indeed, after \(L\) stages, the difference is bounded by the weighted residual sum plus

$$
\left(\prod_{t=N}^{N+L-1}
\operatorname{ContinueMass}(y_t)\right)
\|u_{N+L}-w_{N+L}\|_\infty,
$$

and the latter term tends to zero.

Choose \(N_n\uparrow\infty\) so that

$$
B_{N_n}+Q_{N_n}\le2^{-n}.
$$

The bounded sequence \(u_{N_n}\) has a convergent subsequence. Write

$$
u_{N_{n_k}}\longrightarrow z.
\tag{23}
$$

By (22), also \(w_{N_{n_k}}\to z\). The chronological certificate bounds the actual initial terminal-semantic debt by \(4\eta_k\), with \(\eta_k\to0\). Hence these are terminal approximate Nash profiles with one fixed limiting payoff \(z\). The terminal compact-selection theorem then makes this same \(z\) a uniform-equilibrium payoff.

Never and arbitrarily late deviations remain covered: the certificate’s actual semantic pair uses `quittingRootSequenceProfile`, and its second coordinate is the unrestricted behavioral best-response value, not a finite-time or root-only deviation class.

### 3.3 Exactly one persistent player

Suppose \(P=\{p\}\). The player \(p\) is already frozen by the single extracted spine. Every other marginal stream is summable, hence \(p\)'s opponent clock is summable.

The new exact-spine compiler on current `main` proves that, under punishment normality, the fixed singleton vector

$$
r(\{p\})
$$

is a uniform-equilibrium payoff. Its proof exposes three error channels: opponent hazard, target-value concentration, and the nonowner Quit inequality.

The same proof accepts summable Bellman and Nash defects after the following replacements.

Let

$$
T_p(N)
:=
\sum_{t\ge N}
\operatorname{OpponentClockCharge}_p(y_t).
$$

The actual root-sequence payoff concentrates on the solo reward with error at most \(2R\,T_p(N)\). Combining this with (22) gives

$$
\left|
w_N(i)-r_i(\{p\})
\right|
\le
2R\,T_p(N)+B_N.
\tag{24}
$$

At a selected row \(t\) with \(q_p(y_t)>0\), approximate root Nash and approximate Bellman give, for every nonowner \(i\),

$$
\operatorname{QuitValue}_{t,i}
\le
w_t(i)+\nu_t+\beta_t.
\tag{25}
$$

Thus the exact proof's error streams may be replaced by

$$
\begin{aligned}
\operatorname{hazardError}_n
&=
\operatorname{OpponentClockCharge}_p(y_{t_n}),\\
\operatorname{targetError}_n
&=
2R\,T_p(t_n)+B_{t_n},\\
\operatorname{quitError}_n
&=
\nu_{t_n}+\beta_{t_n}.
\end{aligned}
\tag{26}
$$

All three tend to zero. The underlying deleted-clock solo compiler already accepts vanishing error streams; the current exact theorem specializes the third stream to zero. Therefore the summable-error unique-persistent adapter is mathematically closed. It is not yet the theorem stated in the inspected current-head file.

So the consumer quantifiers are now clean:

* one approximate spine;
* one fixed persistent set \(P\);
* a fixed \(p\) in the singleton branch;
* fixed \(p,q\) in the multi-persistent branch;
* one limiting payoff \(z\), except that the singleton branch has the predetermined limit \(r(\{p\})\).

## 4. Capacity is not a well-founded rank

For a fixed-origin compact source graph with finite capacity, define

$$
C(s)
:=
\sup\left\{
H(P):
P\text{ is a finite path beginning at }s
\right\}.
\tag{27}
$$

Define the finite-horizon capacities

$$
C_n(s)
:=
\max\left\{
H(P):
P\text{ begins at }s,\ 
\operatorname{length}(P)\le n
\right\}.
\tag{28}
$$

### Finite-horizon regularity

Each \(C_n\) is upper semicontinuous and its maximum is attained on every nonempty starting fiber.

To see upper semicontinuity, take \(s_k\to s\) and maximizing paths \(P_k\) of length at most \(n\). Compactness of the finite path space gives a convergent subsequence \(P_k\to P\) beginning at \(s\), and continuity of the charge gives

$$
\limsup_k C_n(s_k)
=
H(P)
\le C_n(s).
$$

### Total capacity need not be upper semicontinuous

Let the state space be the one-point compactification of

$$
\{(n,k):n\ge1,\ 0\le k\le n\},
$$

with limit state \(\infty\). Put edges

$$
(n,k)\to(n,k+1)
$$

of charge \(1/n\), terminal zero-charge edges \((n,n)\to\infty\), and a zero loop at \(\infty\).

The edge and state spaces are compact, and the charge is continuous because every escaping edge has charge tending to zero. But

$$
C(n,0)=1
\qquad\text{while}\qquad
C(\infty)=0,
$$

and \((n,0)\to\infty\). Thus \(C\) is not upper semicontinuous.

The reason is structural:

$$
C=\sup_n C_n,
$$

and an increasing supremum of upper-semicontinuous functions need not be upper semicontinuous.

### Total finite-path capacity need not be attained

Let

$$
S=\{s_0,s_1,\ldots,s_\infty\},
\qquad
s_n\to s_\infty,
$$

with edges

$$
s_n\to s_{n+1}
$$

of charge \(2^{-n-1}\), and a zero loop at \(s_\infty\). Then

$$
C(s_n)=2^{-n},
\qquad
C(s_\infty)=0.
\tag{29}
$$

Here \(C\) is continuous, but no finite path from \(s_n\) attains \(C(s_n)\); finite partial sums approach the value strictly from below.

Even if infinite paths are admitted, attainment is not automatic. One may attach to an isolated root finite branches whose total charges are \(1-1/n\), with the branches converging to a zero-charge limit branch. The root then has capacity \(1\), but no finite or infinite branch realizes it.

A sufficient additional condition is uniform tail tightness,

$$
\sup_s\bigl(C(s)-C_n(s)\bigr)\longrightarrow0.
\tag{30}
$$

That makes the total charge a uniform limit of finite-horizon values and gives the usual compact maximization consequences. No such estimate is currently available for the positive-minimum source.

### No uniform positive capacity drop

For every edge \(e:s\to t\),

$$
C(s)\ge h(x(e))+C(t),
\tag{31}
$$

because \(e\) may be prepended to every finite path from \(t\).

But in the chain above,

$$
C(s_n)-C(s_{n+1})
=
2^{-n-1}
\longrightarrow0.
\tag{32}
$$

Thus even a continuous, finite capacity potential can have positive drops tending to zero.

The repository now contains a source-specific conditional analogue: on a canonical positive-minimum maximal-prefix ray, every step has positive absorption, the total absorption is summable, late finite blocks have arbitrarily small total charge, and normalized debt support and the retained labels remain constant. That file explicitly says this does not construct a counterexample or consume the ray.

Accordingly, \(C\) is only a real-valued Lyapunov bound.

### When capacity does yield a finite rank

Suppose a tagged class of macro transitions satisfies a fixed toll

$$
H(P)\ge\kappa>0.
\tag{33}
$$

Then

$$
\rho_\kappa(s)
:=
\left\lceil\frac{C(s)}{\kappa}\right\rceil
\in\mathbb N
\tag{34}
$$

strictly decreases across every such macro:

$$
\rho_\kappa(\operatorname{target}P)
<
\rho_\kappa(\operatorname{source}P).
\tag{35}
$$

Neither upper semicontinuity nor attainment of \(C\) is needed. The uniform toll—not real-valued strict decrease—is what creates the well-founded rank.

## 5. The nonlocal return toll at positive minimum

Let \(D(z)\) be total terminal-semantic debt, let

$$
D_*=\min D>0,
$$

and let

$$
D_{\max}:=\max_{z\in\mathcal K_r}D(z)<\infty.
$$

For an exact cap-Nash root \(x\) against an attainable tail \(z\), the repository proves the exact identity

$$
D(T_xz)
=
D(z)-D(z)\operatorname{Abs}(x).
\tag{36}
$$

It also proves that return selection is exactly equivalent to entering the requested minimum-debt neighborhood.

Suppose

$$
D(z)\ge D_*+\delta
\tag{37}
$$

and the exact prefix returns within \(\delta/2\):

$$
D(T_xz)\le D_*+\frac{\delta}{2}.
\tag{38}
$$

Then

$$
D(z)\operatorname{Abs}(x)
=
D(z)-D(T_xz)
\ge\frac{\delta}{2},
$$

so

$$
\operatorname{Abs}(x)
\ge
\kappa_\delta
:=
\frac{\delta}{2D_{\max}}.
\tag{39}
$$

Since absorption is at most the sum of marginal Quit hazards,

$$
h(x)\ge\operatorname{Abs}(x)\ge\kappa_\delta.
\tag{40}
$$

This is exactly the kind of fixed toll required by (33).

Consequently, whenever source reprojection records the returned profile as the source of the literal edge

$$
T_xz\xrightarrow{x}z
$$

inside one finite-capacity graph, the natural-valued rank

$$
\rho_\delta(s)
=
\left\lceil
\frac{2D_{\max}}{\delta}C(s)
\right\rceil
\tag{41}
$$

strictly decreases.

This is nonlocal: the tail lies a fixed distance above the minimum fiber, and the prefix discharges at least half that excess. It does not restart inside the unique-all-Continue minimum neighborhood.

The current source-preserving completion consumer constructs the actual returned profile and proves that its semantic pair is the literal exact prefix. But it explicitly stops at “same-tail return selection or universal same-tail undercharge” and does not provide the renewable source reprojection needed to place that edge in one capacity graph.

## 6. What finite capacity does to the uniform-escape branch

The preceding toll gives a sharper reduction of the finite-capacity case.

Consider one composable source-provenant chronology of uniform-escape tails \(z_n\) satisfying

$$
D(z_n)\ge D_*+\delta
$$

for one fixed \(\delta>0\). At each tail select a maximal-absorption exact cap-Nash root \(x_n\), as in the existing maximal-root dispatch. That dispatch gives either:

1. a \(\delta/2\)-return; or
2. universal same-tail undercharge, together with either all-Continue exactness or a singleton-cap blocker.

Assume the chronology has finite hazard capacity \(C_0\).

### Returns occur only finitely often

Every return has charge at least \(\kappa_\delta\). Therefore the number of return-selected rows is at most

$$
\left\lfloor
\frac{C_0}{\kappa_\delta}
\right\rfloor
=
\left\lfloor
\frac{2D_{\max}C_0}{\delta}
\right\rfloor.
\tag{42}
$$

Equivalently, each such row strictly descends the integer rank (41).

### An infinite undercharge chronology converges to an inert cap

On the remaining infinite undercharge chronology,

$$
\sum_n\operatorname{Abs}(x_n)<\infty,
$$

hence

$$
\operatorname{Abs}(x_n)\to0.
\tag{43}
$$

Suppose player \(i\) has singleton-cap gap

$$
g_{n,i}
=
r_i(\{i\})-(z_n)_i^{\mathrm{cap}}>0.
$$

The maximal-root dispatch gives the quantitative bound

$$
\frac{g_{n,i}}{g_{n,i}+2M}
\le
\operatorname{Abs}(x_n).
\tag{44}
$$

Pass to a compact source-provenant subsequence \(z_n\to z_\infty\). If some limiting singleton gap were positive, it would be bounded below by a positive constant on a tail, and (44) would contradict (43). Thus

$$
r_i(\{i\})
\le
(z_\infty)_i^{\mathrm{cap}}
\qquad\text{for every }i.
\tag{45}
$$

Therefore the all-Continue root is exact Nash against the limiting cap. Meanwhile closedness of the uniform-escape floor gives

$$
D(z_\infty)\ge D_*+\delta.
\tag{46}
$$

So finite capacity reduces an infinite uniform-escape chronology to a retained **off-minimum all-Continue-inert omega-source**.

If the exact cap-Nash correspondence is known to be the singleton \(\{\text{all-Continue}\}\), this is precisely the normalized strict-inert source currently packaged in the atlas. That package has a correct single-density toll, but its file explicitly states that it does not construct terminal approximations or consume the strict arm.

This gives the strongest current finite-capacity reduction:

$$
\boxed{
\begin{array}{c}
\text{finite-capacity positive-minimum source chronology}\\[1mm]
\Longrightarrow\\[1mm]
\text{fixed-toll capacity-rank descent}\\
\text{or minimum-fiber support-rank descent}\\
\text{or a retained off-minimum all-Continue-inert omega-source.}
\end{array}}
\tag{47}
$$

The minimum-fiber handoff already has a genuine natural rank: regenerated children strictly reduce positive-debt-support cardinality, the global phase/support rank is at most six, and every recorded transition strictly lowers it. The module is explicit that this is compiler-free and does not supply a horizontal backward compiler.

Thus the exact remaining implication is now:

$$
\boxed{
\begin{array}{c}
\text{retained off-minimum all-Continue-inert Fin4 source}\\
+\ \text{finite hazard capacity}\\
+\ \text{full source law and marked-atom provenance}\\[1mm]
\Longrightarrow\\[1mm]
\text{terminal approximants}
\quad\text{or}\quad
\text{a regenerated minimum-fiber support child.}
\end{array}}
\tag{48}
$$

In addition, the same-tail return profile must be reprojected as an actual source state so that the fixed-toll edge belongs to one renewable graph. Those are the two missing source-level operations.

## 7. Why local charged restarts cannot fill the gap

The independent moat is decisive.

Near a unique-all-Continue minimum segment, every exact local cap-Nash root is all-Continue, so every exact finite local stack has zero absorption and leaves the semantic point unchanged. The checked local no-go states that escape requires a cap/state change, a paid nonexact root, or an independent source-matched strategic edge.

More quantitatively, for every fixed absorption threshold \(\alpha>0\), compactness gives a positive Nash-defect moat \(m(\alpha)>0\) around that segment. Therefore a root with

$$
\operatorname{Abs}(x)\ge\alpha
$$

inside the neighborhood must have Nash defect at least \(m(\alpha)\).

If seam defects are summable, only finitely many such restarts are possible:

$$
\#\{t:\operatorname{Abs}(x_t)\ge\alpha\}
\le
\frac{\sum_t\nu_t}{m(\alpha)}.
\tag{49}
$$

Letting the charges tend to zero avoids this count, but produces exactly the Zeno behavior in which no finite rank follows from debt, support, labels, or raw capacity.

Therefore a viable completion must use one of the two mechanisms isolated above:

$$
\text{fixed off-minimum debt excess}
\Longrightarrow
\text{uniform nonlocal return toll},
$$

or

$$
\text{debt/support discharge before return}
\Longrightarrow
\text{minimum-fiber finite-rank regeneration}.
$$

Local charged-block restart is not a remaining option.

## Status

The hazard-capacity theorem, the two summable-error consumer adapters, the capacity regressions, and the fixed-excess return-toll argument above are mathematical proofs. They have not been added to or compiled in Lean.

The repository’s current `main` is `a0842d13cbe2c1b2854ef4fb4e671b3970d1f089`, whose new commit adds the exact unique-persistent compiler; no workflow run for that commit was visible during this inspection.  I made no source or branch changes. This report therefore distinguishes paper-level closure from checked Lean closure in the manner required by the project runbook. 


## Followup 2

The correction moves finite capacity entirely **downstream of source compatibility**. The earlier Section 6 should not be stated as a Fin4 consequence. The exact next step is a source-faithful macro theorem, together with a positive-minimum coercivity lemma that avoids rowwise exactification.

The distinction is already visible in the formal interfaces: the integrated finite-capacity module explicitly ranges over supplied finite blocks and says that it is not a source-trace capacity and does not concatenate the returned blocks; the chronological seam module begins only after one literal root schedule with summable seams has been supplied.

## 1. The correct C1/C2 macro interface

A level-\(k\) macro must be a proof-relevant object

$$
M_k=
\bigl(
s_k,s_{k+1},L_k,x^k,v^k,
\beta^k,\nu^k,
m_k,C_{1,k},C_{2,k},
\mathfrak a_k,\mathsf{anc}_k
\bigr),
$$

where \(s_k,s_{k+1}\) are actual source ports and \(L_k>0\). Its roots and payoff annotations are

$$
x^k_j\in\prod_{i\in\operatorname{Fin}4}\Delta\{C,Q\},
\qquad
v^k_j\in\mathbb R^4
\quad
(0\le j\le L_k).
$$

The ancestry witness must prove an actual factorization, schematically

$$
\operatorname{profile}(s_k)
=
A_k\triangleright
x_k^{\mathrm{mark}}\triangleright
B_k\triangleright
\operatorname{profile}(s_{k+1}),
\tag{1}
$$

not merely convergence of the semantic coordinates of the two sides. Here the preceding marked row occurs at \(m_k\), the charged interval is the displayed \(C_{1,k}\)-to-\(C_{2,k}\) portion of \(B_k\), and \(\mathfrak a_k\) records the actual coalition atom and its reach. In particular,

$$
m_k<C_{1,k}\le C_{2,k}\le L_k.
\tag{2}
$$

Equation (1), or its certified summable-decoder version, simultaneously proves:

* the roots are one literal piece of behavior;
* \(s_{k+1}\) is the actual child source;
* the marked atom occurs before the charged block in that same behavior;
* replacing behavior only after \(C_{1,k}\) leaves the marked row literally unchanged.

This is precisely why the grammar requires a closed ancestry relation whose membership semantically implies source-faithful succession; a textual origin label or carrier membership is insufficient. 

The approximate Nash–Bellman fields are

$$
\left\|
v^k_j-F_{x^k_j}(v^k_{j+1})
\right\|_\infty
\le \beta^k_j,
\tag{3}
$$

$$
\operatorname{NDef}_r(x^k_j;v^k_{j+1})
\le \nu^k_j.
\tag{4}
$$

At a macro seam put

$$
d_k:=
\left\|
v^k_{L_k}-v^{k+1}_0
\right\|_\infty.
\tag{5}
$$

The macro also records its literal total marginal hazard

$$
H_k:=
\sum_{j<L_k}\sum_i q_i(x^k_j).
\tag{6}
$$

Two logically separate semantic records are needed:

1. the payoff annotation \(v^k\), used by the summable approximate Nash–Bellman compiler;
2. the actual terminal-semantic pairs at the two cuts, including unrestricted cap coordinates, used by the positive-minimum argument below.

Payoff matching alone does not supply the second record.

## 2. Source-faithful macro-tower theorem

Let \(\mathcal T_n\) be the space of legal compatible towers

$$
(M_0,\ldots,M_{n-1})
$$

starting from one fixed actual port \(s_0\). Assume:

1. every \(\mathcal T_n\) is nonempty and compact;
2. restriction

   $$
   \mathcal T_{n+1}\longrightarrow\mathcal T_n
   $$

   is surjective;
3. compatibility means the actual equality

   $$
   \operatorname{child}(M_k)
   =
   \operatorname{source}(M_{k+1})
   \tag{7}
   $$

   inside the recorded ancestry relation;
4. the annotations are uniformly bounded;
5. $$
   \sum_k
   \left[
     \sum_{j<L_k}
       \bigl(\beta^k_j+\nu^k_j\bigr)
     +3d_k
   \right]
   <\infty;
   \tag{8}
   $$
6. $$
   \sum_k H_k=\infty.
   \tag{9}
   $$

Surjectivity in item 2 may equivalently be replaced by a serial source kernel: every reached source has an admissible next macro at the requested error scale. Merely having a nonempty tower separately at every depth is insufficient.

### Theorem — compatible macro towers compile to one consumed spine

Under these assumptions there is one actual flattened root sequence \(y_t\), one uniformly bounded payoff annotation \(w_t\), and summable Bellman and Nash errors such that

$$
\sum_t
\left\|
w_t-F_{y_t}(w_{t+1})
\right\|_\infty
<\infty,
\tag{10}
$$

$$
\sum_t
\operatorname{NDef}_r(y_t;w_{t+1})
<\infty,
\tag{11}
$$

and

$$
\sum_t\sum_iq_i(y_t)=\infty.
\tag{12}
$$

Hence one fixed player is persistent on this literal sequence. The already-exported persistent-player consumers then give a uniform-equilibrium payoff.

### Proof

The compact projective system \((\mathcal T_n)\) has an inverse-limit point, giving one compatible tower \(M_0,M_1,\ldots\). This is where the common ancestry chain is selected. It is not obtained by independently choosing one macro at every level.

Set

$$
N_0=0,\qquad
N_{k+1}=N_k+L_k,
$$

and flatten by

$$
y_{N_k+j}=x^k_j,
\qquad
w_{N_k+j}=v^k_j
\quad(j<L_k).
$$

At an internal row the errors remain \(\beta^k_j,\nu^k_j\). At the final row of macro \(k\), its original continuation was \(v^k_{L_k}\), whereas the actual next annotation is \(v^{k+1}_0\). Since every root payoff, including every unilateral replacement payoff, is \(1\)-Lipschitz in the continuation,

$$
\operatorname{BellErr}_{\rm seam}
\le
\beta^k_{L_k-1}+d_k,
$$

and

$$
\operatorname{NashErr}_{\rm seam}
\le
\nu^k_{L_k-1}+2d_k.
$$

Thus (8) gives (10)–(11). Equation (12) follows directly from (6) and (9). Since there are four players, one fixed marginal stream diverges.

The ancestry witnesses and (7) make every finite flattened prefix an actual composition of the corresponding macros. In the decoded version, the summable finite-program decoder first constructs the actual ports and preserves the closed ancestry relation; the coherent-diagonal theorem then ensures that all finite diagrams share one initial controller, rather than producing one controller per cutoff.  

The marked row of macro \(k\) occurs at the literal global date

$$
N_k+m_k.
$$

Its **local** reach and coalition mass are exactly those recorded by \(\mathfrak a_k\). No uniform lower bound on its absolute reach from date zero follows unless the macro interface separately supplies one.

This theorem isolates the missing C1/C2 field: the current rank-indexed blocks do not provide the surjective restriction or serial-child property (7).

## 3. Positive-minimum two-cut coercivity

There is a useful way to exploit positive minimum debt without exactifying any approximate root.

Let

$$
D_*:=\min_{z\in\mathcal K_r}D(z)>0.
$$

Take one actual behavioral profile and two literal cuts \(C_1<C_2\). Let

$$
L=C_2-C_1,
$$

and let \(z_t=(U_t,B_t)\in\mathcal K_r\) be the actual terminal-semantic pair of the suffix beginning at \(C_1+t\). Let \(x_t\) be its actual root. Write

$$
c_t=\Pr_{x_t}(\text{all Continue}),
\qquad
P_0=1,\qquad
P_t=\prod_{u<t}c_u.
$$

For player \(i\), define the cap-root defect

$$
\rho_{t,i}
:=
\operatorname{NDef}_{r,i}(x_t;B_{t+1}).
\tag{13}
$$

This is evaluated against the actual unrestricted cap \(B_{t+1}\), not against the prescribed payoff \(U_{t+1}\). The exact semantic-debt identity is

$$
d_i(z_t)
=
\rho_{t,i}+c_t\,d_i(z_{t+1}),
\tag{14}
$$

and therefore

$$
D(z_t)
=
\rho_t+c_tD(z_{t+1}),
\qquad
\rho_t:=\sum_i\rho_{t,i}\ge0.
\tag{15}
$$

This is the positive-minimum prefix identity already used throughout the semantic carrier development. 

Define

$$
\mathcal C
:=
\sum_{t<L}P_t\rho_t,
\qquad
\Delta:=D(z_L)-D_*\ge0.
\tag{16}
$$

### Theorem — exact two-cut coercivity

If

$$
P_L\le\theta<1,
$$

then

$$
\boxed{
\mathcal C+\theta\Delta
\ge
(1-\theta)D_*.
}
\tag{17}
$$

### Proof

Telescoping (15) gives

$$
D(z_0)
=
\sum_{t<L}P_t\rho_t+P_LD(z_L)
=
\mathcal C+P_L(D_*+\Delta).
$$

Since \(z_0\in\mathcal K_r\),

$$
D_*
\le
\mathcal C+P_L(D_*+\Delta).
$$

Rearranging and using \(P_L\le\theta\) gives (17). ∎

For a Fin4 block with total marginal hazard

$$
H:=\sum_{t<L}\sum_iq_i(x_t),
$$

one has

$$
c_t
\le
\exp\left(
-\frac14\sum_iq_i(x_t)
\right),
$$

and hence

$$
P_L\le e^{-H/4}.
\tag{18}
$$

Thus, when \(H\ge\chi>0\),

$$
\boxed{
\mathcal C+
e^{-\chi/4}\Delta
\ge
\bigl(1-e^{-\chi/4}\bigr)D_*.
}
\tag{19}
$$

This is vacuous when \(D_*=0\), exactly as required by the new zero-Never exactification regression.

### Seam-stable form

Suppose instead that a decoded artificial chain has exact macro steps but debt-coordinate seams of total absolute size \(S\). The same telescope gives

$$
\boxed{
\mathcal C+
S+
e^{-\chi/4}\Delta
\ge
\bigl(1-e^{-\chi/4}\bigr)D_*.
}
\tag{20}
$$

This is the form appropriate to a summably decoded C1/C2 macro. The seam term must control complete semantic debt—hence both payoff and cap coordinates—not merely parent and child payoffs.

## 4. A post-mark paid exit without exactification

The coercivity charge \(\mathcal C\) has an actual behavioral interpretation.

Set

$$
K_\chi:=
\bigl(1-e^{-\chi/4}\bigr)D_*,
\qquad
\delta_\chi:=
\frac{e^{\chi/4}-1}{2}D_*.
\tag{21}
$$

For a literal block with \(H\ge\chi\), exactly one of the following holds.

### Uniform off-minimum exit

$$
D(z_L)\ge D_*+\delta_\chi.
\tag{22}
$$

### Post-\(C_1\) paid replacement

There is a fixed player \(p\) and, for every positive \(\varepsilon\), an actual unilateral stopping law for the \(C_1\)-suffix whose gain is at least

$$
\frac{K_\chi}{8}-\varepsilon.
\tag{23}
$$

Indeed, if (22) fails, then

$$
e^{-\chi/4}\Delta<\frac{K_\chi}{2},
$$

so (19) gives

$$
\mathcal C>\frac{K_\chi}{2}.
$$

For some \(p\),

$$
\mathcal C_p:=
\sum_{t<L}P_t\rho_{t,p}
>
\frac{K_\chi}{8}.
$$

The coordinatewise telescope yields

$$
d_p(z_0)
=
\mathcal C_p+P_Ld_p(z_L)
\ge
\mathcal C_p.
\tag{24}
$$

By the definition of the unrestricted behavioral cap, an actual stopping law achieves payoff within \(\varepsilon\) of \(B_{0,p}\), proving (23).

Now suppose the preceding marked row satisfies

$$
m<C_1
$$

and the original parent profile reaches \(C_1\) with probability at least \(r_0>0\). Extend the selected stopping law to the parent by leaving player \(p\)'s strategy unchanged before \(C_1\). Its parent-level payoff gain is at least

$$
r_0
\left(
\frac{K_\chi}{8}-\varepsilon
\right).
\tag{25}
$$

Taking \(\varepsilon=K_\chi/16\) gives the uniform gain floor

$$
\boxed{
\frac{r_0K_\chi}{16}.
}
\tag{26}
$$

At the reached \(C_1\)-port, the target profile has \(p\)-debt at most \(K_\chi/16\), because the opponents are unchanged and the prescribed payoff is within that amount of their fixed best-response cap.

Crucially, this replacement agrees with the parent through \(C_1\). Therefore:

* the preceding marked root is unchanged;
* its reached mass is unchanged;
* the complete terminal law on every branch terminating before \(C_1\) is unchanged;
* the first possible strategy difference occurs strictly after the marked row.

This is the separate atom-retention proof that semantic clustering alone cannot supply.

The conclusion is not yet a terminal approximation or a renewable rank. It is, however, an actual source-faithful **paid/debt exit with a uniform positive gain**, obtained without replacing the approximate block by exact roots.

## 5. Scope of the coercivity result

Several boundaries remain important.

First, an ordinary exact or \(1/n\)-Nash root against \(U_{t+1}\) need not have small \(\rho_{t,i}\), because \(\rho_{t,i}\) is evaluated against \(B_{t+1}\). Thus the theorem does not contradict the exactification regression and does not secretly exactify the C1/C2 roots.

Second, if every block root is exact Nash against the actual cap, then \(\mathcal C=0\), and (19) forces the stronger uniform exit

$$
D(z_L)-D_*
\ge
\bigl(e^{\chi/4}-1\bigr)D_*.
\tag{27}
$$

So a source-faithful, order-one-hazard, exact cap-Nash block cannot return close to the positive minimum fiber.

Third, the one-root positive-root branch remains as described in the correction. If its absorption is merely positive, with no fixed lower bound, then \(\chi\) may tend to zero and both \(K_\chi\) and the exit bound in (27) tend to zero. Hence the theorem supplies no renewable rank for the strict off-minimum descent

$$
D(T_xX)<D(X).
$$

It gives a uniform conclusion only for an order-one block or another fixed survival loss. It is unrelated to the tangent-family flat-support-entry condition.

Fourth, the paid replacement in (26) preserves the atom only because the ancestry factorization places the mark strictly before \(C_1\). A cluster of the escaped \(C_2\)-continuation does not contain this conclusion.

## 6. The exact remaining Fin4 producer theorem

The finite-capacity branch is reduced to the following source-specific statement.

For every actual positive-minimum hard-residual source \(s\) and every requested summable accuracy budget, produce one of:

$$
\boxed{
\begin{array}{ll}
\textbf{Macro:}&
\text{a source-faithful C1/C2 macro }s\leadsto s'
\text{ satisfying (1)--(9),}\\
&\text{with }s'\text{ in the same renewable domain};\\[1mm]
\textbf{Paid exit:}&
\text{the post-mark paid/debt replacement obtained from (26),}\\
&\text{together with a terminal or renewable-rank consumer};\\[1mm]
\textbf{Off-minimum exit:}&
D(s')\ge D_*+\delta_\chi,
\text{ together with either}\\
&\text{a source-faithful next macro, a fixed-toll return, or a finite-rank child};\\[1mm]
\textbf{Terminal:}&
\text{a terminal approximate Nash profile.}
\end{array}}
\tag{28}
$$

If the macro arm continues forever, the macro-tower theorem gives the already-consumed persistent spine. A fixed-toll return can be charged to a natural-valued capacity rank, but only after that return and its child are edges of the same ancestry graph. A bare strict off-minimum decrease is not such a rank.

The existing minimum-fiber support rank is genuinely natural-valued and strictly decreasing, but its module is explicit that it is compiler-free and supplies no horizontal seam compiler.  The corrected terminal-exit analysis likewise identifies nested marked-suffix compatibility, rather than additional static geometry, as the missing atom-chronology datum. 

Thus the generic exactification route can be dropped. The viable positive-minimum route is:

$$
\text{source-faithful approximate charged macro}
\Longrightarrow
\begin{cases}
\text{summably composable macro},\\
\text{post-mark paid/debt exit},\\
\text{uniform off-minimum exit}.
\end{cases}
$$

What remains construction-specific is to prove that the current C1/C2 packet supplies the actual ancestry and complete cap co-realization needed to invoke this trichotomy, and then to make the paid or off-minimum child renewable.

These statements are paper-level. I made no repository changes and have not claimed Lean compilation or integration; formal status would require current-head implementation and validation under the project runbook. 


## Followup 3

The corrections improve the route. The useful source is not the whole parent containing the marked row, but its **literal post-mark continuation**. On that continuation, a uniformly reached order-one C1/C2 block forces a uniformly positive debt coordinate. A complete best response from the start of that continuation then drives that coordinate to zero while leaving the preceding marked row untouched.

This gives a direct positive-minimum coercivity theorem into the existing support-rank handoff, without exactifying any row of the charged block.

## 1. Corrected two-cut coercivity

Let \(\sigma\) be one actual behavioral profile, viewed from the start of the relevant continuation. For its suffix at time \(t\), write

$$
Z_t=(U_t,B_t),
\qquad
d_{t,i}:=B_{t,i}-U_{t,i},
\qquad
D_t:=\sum_i d_{t,i}.
$$

Let \(x_t\) be the actual root and put

$$
c_t:=\Pr_{x_t}(\text{all Continue}),
\qquad
h_t:=\sum_i q_{t,i}.
$$

For each player, let

$$
\rho_{t,i}
:=
\operatorname{Def}_i(r,B_{t+1},x_t)
$$

be the coordinate root-Nash defect against the **actual cap** of the next suffix. No root-Nash hypothesis is imposed.

The exact arbitrary-root identity is

$$
d_{t,i}
=
\rho_{t,i}+c_t d_{t+1,i}.
\tag{1}
$$

This is the theorem
`quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul`
in `TerminalSemanticOwnStrategyTransport.lean`.

For cuts \(C_1<C_2\), write \(L=C_2-C_1\) and

$$
P_0=1,
\qquad
P_s=\prod_{u<s}c_{C_1+u}.
$$

Define

$$
\mathcal C_i
:=
\sum_{s<L}P_s\rho_{C_1+s,i},
\qquad
\mathcal C:=\sum_i\mathcal C_i.
$$

Telescoping (1) gives

$$
d_{C_1,i}
=
\mathcal C_i+P_Ld_{C_2,i},
\tag{2}
$$

and

$$
D_{C_1}
=
\mathcal C+P_LD_{C_2}.
\tag{3}
$$

Now

$$
c_t
=
\prod_i(1-q_{t,i})
\le
\exp\left(-\sum_iq_{t,i}\right)
=
e^{-h_t}.
$$

Therefore, if the block hazard is

$$
H:=\sum_{t=C_1}^{C_2-1}h_t\ge\chi,
$$

then the correct estimate is

$$
P_L\le e^{-H}\le e^{-\chi}.
\tag{4}
$$

Set

$$
\theta_\chi:=e^{-\chi},
\qquad
K_\chi:=(1-\theta_\chi)D_*,
\qquad
\delta_\chi
:=
\frac{K_\chi}{2\theta_\chi}
=
\frac{e^\chi-1}{2}D_*.
\tag{5}
$$

Assume

$$
D_{C_2}\le D_*+\delta_\chi.
\tag{6}
$$

Since every actual suffix belongs to the terminal-semantic carrier,

$$
D_{C_1}\ge D_*.
$$

Consequently,

$$
\begin{aligned}
\mathcal C
&=D_{C_1}-P_LD_{C_2}\\
&\ge D_*-\theta_\chi(D_*+\delta_\chi)\\
&=\frac{K_\chi}{2}.
\end{aligned}
\tag{7}
$$

There is therefore a player \(p\), depending on this block, such that

$$
\boxed{\mathcal C_p\ge\frac{K_\chi}{8}.}
\tag{8}
$$

By (2),

$$
d_{C_1,p}\ge\frac{K_\chi}{8}.
\tag{9}
$$

This is an actual semantic-debt statement, not a claim that some approximate charged root has been exactified.

## 2. Lifting the block payer to the post-mark source

Let \(s\) be the post-mark continuation profile containing the C1/C2 block. Suppose the probability, measured from the start of \(s\), of reaching \(C_1\) is explicitly bounded below:

$$
R(C_1)\ge r>0.
\tag{10}
$$

The exact finite literal-spine account gives

$$
d_p(s)
=
\sum_{t<C_1}
R(t)\rho_{t,p}
+
R(C_1)d_{C_1,p}.
\tag{11}
$$

All terms are nonnegative. This is precisely the content of
`quittingTerminalSemanticDebt_eq_sum_liveMass_mul_capDefect_add_liveTailDebt`
in `TerminalSemanticReachedRowDebtLocalization.lean`.

Combining (9)–(11),

$$
\boxed{
d_p(s)
\ge
g_{\chi,r}
:=
\frac{r(1-e^{-\chi})D_*}{8}.
}
\tag{12}
$$

This is why the reach floor must be a field of the C1/C2 packet. Hazard one with vanishing reach gives no source-level debt floor.

For a sequence of such blocks, the payer \(p_n\) is selected separately for each block. Since there are four players, a strict subsequence fixes one player \(p\). On that subsequence,

$$
d_p(s_n)\ge g_{\chi,r}>0.
\tag{13}
$$

No player is claimed fixed before this finite-label extraction.

## 3. Post-mark best response gives the support-rank handoff

Assume now that \(s_n\) are actual post-mark continuation profiles satisfying

$$
D(s_n)\longrightarrow D_*,
\tag{14}
$$

and that their C1/C2 data satisfies the fixed \(\chi,r\) hypotheses above. If the C2 suffix debts converge to \(D_*\), condition (6) is automatic eventually for every fixed \(\chi>0\).

After fixing the payer \(p\), choose \(\varepsilon_n\downarrow0\). By the definition of the unrestricted behavioral cap, choose an actual complete strategy \(\tau_n^p\) such that, for

$$
t_n:=\operatorname{update}(s_n,p,\tau_n^p),
$$

one has

$$
U_p(t_n)\ge B_p(s_n)-\varepsilon_n.
\tag{15}
$$

Because only \(p\)'s strategy changes, \(p\)'s best-response envelope is unchanged:

$$
B_p(t_n)=B_p(s_n).
\tag{16}
$$

Hence

$$
d_p(t_n)\le\varepsilon_n\longrightarrow0,
\tag{17}
$$

and

$$
U_p(t_n)-U_p(s_n)
\ge d_p(s_n)-\varepsilon_n
\ge g_{\chi,r}-\varepsilon_n.
\tag{18}
$$

Thus the target has small debt only at the reached continuation port:

$$
\boxed{d_p(t_n)\to0.}
\tag{19}
$$

Nothing here implies that the full parent profile, obtained by reattaching the preceding marked row, has small \(p\)-debt or small total debt.

Pass to a further subsequence on which

$$
d_p(s_n)\longrightarrow g
\qquad\text{with}\qquad
g\ge g_{\chi,r}>0.
\tag{20}
$$

### Asymptotic-zero support-handoff theorem

The current theorem
`exists_minimumEndpointSupportRankHandoff_or_debtAscent`
assumes \(d_p(t_n)=0\) at every index. Its proof extends directly to the weaker hypothesis \(d_p(t_n)\to0\).

The resulting conclusion is:

$$
\boxed{
\begin{array}{l}
\text{either a same-minimum endpoint with strict support-rank descent,}\\
\text{or an off-minimum endpoint with }p\text{-debt zero.}
\end{array}}
\tag{21}
$$

Here is the complete argument.

Jointly compactify the source profiles, target profiles, and their literal half stopping-law mixtures:

$$
Z^{\rm src}_n\to S,
\qquad
Z^{\rm tgt}_n\to T,
\qquad
Z^{1/2}_n\to H.
$$

Then

$$
D(S)=D_*,
\qquad
d_p(S)=g>0,
\qquad
d_p(T)=0.
\tag{22}
$$

If

$$
D(T)>D_*,
$$

we obtain the off-minimum endpoint.

Suppose instead that

$$
D(T)=D_*.
$$

Coordinatewise debt convexity of the half profile gives

$$
d_i(H)
\le
\frac{d_i(S)+d_i(T)}2.
\tag{23}
$$

Summing,

$$
D(H)\le\frac{D(S)+D(T)}2=D_*.
$$

Global minimality gives \(D(H)\ge D_*\), so equality holds. Since each coordinate gap in (23) is nonnegative and their sum is zero,

$$
d_i(H)
=
\frac{d_i(S)+d_i(T)}2
\qquad\text{for every }i.
\tag{24}
$$

Therefore

$$
\operatorname{supp}_+(H)
=
\operatorname{supp}_+(S)\cup\operatorname{supp}_+(T).
\tag{25}
$$

But \(p\in\operatorname{supp}_+(S)\) and \(p\notin\operatorname{supp}_+(T)\), so

$$
\boxed{
\operatorname{supp}_+(T)
\subsetneq
\operatorname{supp}_+(H).
}
\tag{26}
$$

This is exactly the strict finite support descent required by the existing renewable lane.

The important point is that the order-one approximate block itself is never modified. It is used only to prove the lower bound (13); the endpoint is produced by a genuine complete behavioral replacement.

## 4. The correct marked-row provenance package

Suppose the full source profile has a literal factorization

$$
\widehat s_n
=
A_n
\triangleright
x^{\rm mark}_n
\triangleright
s_n,
\tag{27}
$$

where \(s_n\) is the post-mark continuation used above.

Define

$$
\widehat t_n
=
A_n
\triangleright
x^{\rm mark}_n
\triangleright
t_n.
\tag{28}
$$

Then the entire behavior through the marked row is identical in
\(\widehat s_n\) and \(\widehat t_n\). Consequently:

$$
x^{\rm mark}_n(\widehat t_n)
=
x^{\rm mark}_n(\widehat s_n),
\tag{29}
$$

the probability of reaching the marked row is identical, and every coalition atom generated at that row has exactly the same mass.

Thus the correct output is a **two-port endpoint**:

* an upstream actual profile \(\widehat t_n\) retaining the marked atom;
* its downstream post-mark continuation \(t_n\), whose \(p\)-debt tends to zero;
* the literal ancestry equality (28).

The retained atom does not belong to the outcome law of the downstream suffix \(t_n\). Conversely, the zero-debt statement does not automatically hold at the upstream parent. Keeping the two ports prevents precisely the invalid identification in the earlier reduction.

## 5. Exact-root dichotomy at the off-minimum endpoint

Suppose the support-handoff gives an off-minimum post-mark cluster \(T\):

$$
D(T)>D_*,
\qquad
d_p(T)=0.
\tag{30}
$$

The exact cap-Nash correspondence at \(T.2\) has the exhaustive dichotomy

$$
\boxed{
\{\text{all Continue}\}
\quad\text{or}\quad
\text{an exact root with positive absorption}.
}
\tag{31}
$$

Indeed, an exact root either has positive absorption or has absorption zero. A product root has zero absorption only when every marginal Quit probability is zero, hence it is the all-Continue root. Therefore absence of a positive-absorption exact root means uniqueness of all Continue.

This is strictly weaker than inferring uniqueness from all-Continue exactness alone.

### Summable actualization of the positive-root arm

Assume \(x\) is exact Nash against the limiting cap \(T.2\), with

$$
a:=\operatorname{Abs}(x)>0.
$$

Let the actual post-mark targets satisfy

$$
Z(t_n)\longrightarrow T.
$$

Use the **same fixed root** \(x\) against each actual target \(t_n\). Continuity of root Nash defect gives

$$
\epsilon_n
:=
\operatorname{NDef}_r(x;Z(t_n).2)
\longrightarrow0.
\tag{32}
$$

Thin so that

$$
\sum_n\epsilon_n<\infty.
\tag{33}
$$

The profiles

$$
y_n:=x\triangleright t_n
\tag{34}
$$

are literal actual behavioral profiles. Their semantic and outcome-law points converge to

$$
Y=
\bigl(
T_x(T.1),
L_x(T.2_{\rm law})
\bigr).
\tag{35}
$$

The semantic prefix identity is exact at every \(n\); only the displayed cap-Nash residual is \(\epsilon_n\). Reattaching (34) after the same marked row again preserves the upstream marked atom.

This avoids the lower-hemicontinuity problem for the exact-root correspondence. No exact root near \(x\) is selected at the finite approximants.

At the limit, exact cap Nash gives

$$
\boxed{
D(Y)=(1-a)D(T)<D(T).
}
\tag{36}
$$

If \(D(Y)=D_*\), the existing strict-ray positive-root handoff regenerates a same-residual minimum source. If \(D(Y)>D_*\), it remains only a strict off-minimum descent; the checked file explicitly makes no quantitative-rank claim in this arm.

## 6. Positive-root descent has automatically finite hazard

There is a further useful quantitative fact.

Consider a composable sequence of semantic prefixes

$$
X_{k+1}=T_{x_k}X_k,
$$

where \(a_k=\operatorname{Abs}(x_k)\), and let \(\rho_k\ge0\) be the total cap-Nash residual. The exact arbitrary-root debt identity gives

$$
D_{k+1}
=
(1-a_k)D_k+\rho_k.
\tag{37}
$$

Assume

$$
D_k\ge D_*>0,
\qquad
\sum_k\rho_k<\infty.
$$

Then

$$
a_kD_k
=
D_k-D_{k+1}+\rho_k.
$$

Therefore, for every \(N\),

$$
D_*\sum_{k<N}a_k
\le
D_0-D_N+\sum_{k<N}\rho_k
\le
D_0-D_*+\sum_k\rho_k.
\tag{38}
$$

Hence

$$
\boxed{
\sum_k a_k
\le
\frac{D_0-D_*+\sum_k\rho_k}{D_*}
<\infty.
}
\tag{39}
$$

For four players, every marginal quit event is contained in the absorption event, so

$$
q_{k,i}\le a_k
$$

and thus

$$
h(x_k)=\sum_iq_{k,i}\le4a_k.
$$

Consequently,

$$
\boxed{
\sum_k h(x_k)
\le
\frac{4}{D_*}
\left(
D_0-D_*+\sum_k\rho_k
\right)
<\infty.
}
\tag{40}
$$

Thus an infinite positive-root descent lane with summable cap-Nash errors is intrinsically an all-summable Zeno lane. It cannot itself provide the persistent spine. Its purpose can only be:

* to hit the minimum fiber;
* to trigger a discrete support/rank transition; or
* to converge to the all-Continue-inert residual.

This also explains why a merely strict real-valued descent is insufficient.

## 7. Sharpened remaining producer theorem

The current C1/C2 construction now only needs to supply the following exact source data.

There must be actual post-mark tails \(s_n\) such that:

$$
D(s_n)\to D_*,
\tag{41}
$$

the C1/C2 roots are literal consecutive roots inside \(s_n\),

$$
\Pr_{s_n}(\text{reach }C_{1,n})\ge r>0,
\tag{42}
$$

$$
\sum_{t=C_{1,n}}^{C_{2,n}-1}h(x_{n,t})\ge\chi>0,
\tag{43}
$$

and

$$
D\bigl(\operatorname{suffix}_{C_{2,n}}s_n\bigr)\to D_*.
\tag{44}
$$

The ancestry record must also identify \(s_n\) as the literal continuation after the retained marked row.

Under (41)–(44), the argument above produces, after finite-label selection:

$$
\boxed{
\begin{array}{l}
\text{a strict minimum-fiber support-rank child,}\\
\text{or an off-minimum zero-debt continuation retaining the upstream atom.}
\end{array}}
\tag{45}
$$

At the off-minimum continuation, one then has:

$$
\boxed{
\begin{array}{l}
\text{unique all Continue,}\\
\text{or a source-faithfully actualized positive-root descent.}
\end{array}}
\tag{46}
$$

This is stronger than generic “paid exit or exact charged exit.” It requires no rowwise exactification and is unaffected by the zero-minimum exactification regression: the coercive constant is proportional to \(D_*>0\), and the only selected exact root is a single root at the final compact endpoint.

The remaining obstruction is therefore narrowed to two source adapters:

1. prove that the present C1/C2 block really lies inside one uniformly reached post-mark near-minimum continuation, rather than between independently selected rank objects;
2. make the same-minimum support child or the positive-root prefixed child a renewable source in the existing ancestry graph.

The exactification no-go remains fully respected: it rules out preserving the approximate block's charge by replacing its rows with exact Nash–Bellman rows, whereas the construction above never replaces those rows.

Repository state was rechecked according to the task runbook.  Current `main` is
`ff46b0b4db3d01dde15ff97d6f4c748b25448360`, which adds the summable-residual spine compiler; its trust and static checks had passed, while the full `lake build` was still running when inspected.   No repository changes were made.

## Followup 4

The raw packet still does not contain the requested chronology. On the **normalized-return equality arm**, however, there is an exact construction that supplies it: replay the actualized profile behind its own pure pair row.

The construction uses no rowwise exactification, no Bellman seam, and no unrelated rank reindexing.

# 1. Pure nonsingleton rows are complete semantic/law shields

Let \(S\subseteq I\) with \(|S|\ge2\), and let \(q^S\) be the pure product root under which exactly the players in \(S\) Quit.

For any two continuation semantic pairs \(z,z'\),

$$
T_{q^S}z=T_{q^S}z'.
\tag{1}
$$

Indeed, the prescribed payoff is \(r(S)\). The cap coordinate is

$$
\bigl(T_{q^S}z\bigr)^2_i=
\begin{cases}
\max\{r_i(S),r_i(S\setminus\{i\})\},
   &i\in S,\\[1mm]
\max\{r_i(S),r_i(S\cup\{i\})\},
   &i\notin S.
\end{cases}
\tag{2}
$$

The set \(S\setminus\{i\}\) remains nonempty when \(i\in S\), so every unilateral deviation still leaves a sure quitter other than the deviator. Consequently neither a finite quitting time, an arbitrarily late quitting time, nor Never can expose the continuation.

Likewise, for any two terminal outcome laws \(\lambda,\lambda'\),

$$
L_{q^S}\lambda=L_{q^S}\lambda'=\delta_S.
\tag{3}
$$

Thus \(q^S\) shields both the unrestricted behavioral cap and the complete outcome law.

Now let \(A\) be any finite product-root word. Applying the deterministic prefix maps to (1)–(3) gives

$$
T_A T_{q^S}z=T_A T_{q^S}z',
\qquad
L_A L_{q^S}\lambda=L_A L_{q^S}\lambda'.
\tag{4}
$$

This yields the behavioral form.

## Pure-pair cross-tail shield

Suppose an actual profile \(\sigma\) has live root \(q^S\) at date \(m\). For an arbitrary behavioral tail \(\tau\), let

$$
\operatorname{Cross}_m(\sigma,\tau)
$$

copy the live roots of \(\sigma\) through date \(m\), inclusive, and then restart \(\tau\).

Then

$$
\boxed{
\operatorname{SemLaw}\bigl(\operatorname{Cross}_m(\sigma,\tau)\bigr)
=
\operatorname{SemLaw}(\sigma).
}
\tag{5}
$$

The proof decomposes both profiles through the same prefix \(A\) and the same final copied root \(q^S\); their post-\(q^S\) tails disappear by (4).

The current cross-tail implementation already proves that copied roots through \(m\), the exact marked-stage coalition mass, and the post-\(m\) behavioral tail are literal identities. It deliberately makes no semantic comparison; equation (5) is the missing nonsingleton-shield lemma.

This is stronger than a summable decoder:

* the upstream source point is preserved exactly;
* its full outcome law is preserved exactly;
* the marked atom is preserved exactly;
* there is no seam error;
* the restarted tail may be arbitrary.

# 2. The equality actualizer produces the same-witness two-cut block

Take the normalized-return equality arm. Let

$$
\sigma_n:=\text{actualizer.profiles}(n),
\qquad
m_n:=\text{actualizer.mark}(n),
$$

and let \(S\) be its fixed marked coalition.

The Fin4 specialization has:

$$
|S|=2;
\tag{6}
$$

the live root at \(m_n\) is the pure pair root \(q^S\);

$$
\rho
\le
\Pr_{\sigma_n}(\text{terminal coalition }S\text{ at }m_n)
\tag{7}
$$

for one fixed \(\rho>0\); and

$$
D(\sigma_n)\longrightarrow D_*,
\tag{8}
$$

$$
D\!\left(
  \operatorname{Spine}(\sigma_n,m_n+1)
 \right)
\longrightarrow D_*.
\tag{9}
$$

These are literal actual profiles, not carrier representatives. The equality actualizer records the uniform mass floor and both debt convergences, while the Fin4 forced-pair family identifies the marked terminal as one fixed pair and the marked target as the corresponding pure coalition row.

Define the parent

$$
\pi_n
:=
\operatorname{Cross}_{m_n}(\sigma_n,\sigma_n)
=
\operatorname{SelfTailClosure}(\sigma_n,m_n).
\tag{10}
$$

If \(A_n\) denotes the word of the first \(m_n\) live roots of \(\sigma_n\), then literally

$$
\pi_n
=
A_n\triangleright q^S\triangleright \sigma_n.
\tag{11}
$$

Inside the restarted post-mark tail \(\sigma_n\), the same pair root occurs again:

$$
\sigma_n
=
A_n\triangleright q^S\triangleright R_n,
\qquad
R_n=\operatorname{Spine}(\sigma_n,m_n+1).
\tag{12}
$$

Thus the beginning of \(\pi_n\) is

$$
A_n\triangleright q^S
\triangleright
A_n\triangleright q^S
\triangleright R_n.
\tag{13}
$$

The first copy is the retained source mark. The second copy is the charged two-cut block.

## Exact fields

Set

$$
\begin{aligned}
\operatorname{parent}_n&:=\pi_n,\\
\operatorname{postMarkTail}_n&:=\sigma_n,\\
\operatorname{parentMark}_n&:=m_n,\\
\operatorname{entryCut}_n&:=m_n,\\
\operatorname{exitCut}_n&:=m_n+1.
\end{aligned}
\tag{14}
$$

The cuts in (14) are measured from the start of the post-mark tail. Their absolute dates in \(\pi_n\) are \(2m_n+1\) and \(2m_n+2\).

They satisfy all requested fields.

### Literal ancestry

$$
\operatorname{parent}_n
=
A_n\triangleright q^S\triangleright
\operatorname{postMarkTail}_n.
\tag{15}
$$

Moreover,

$$
\operatorname{Spine}(\operatorname{parent}_n,m_n+1)
=
\operatorname{postMarkTail}_n.
\tag{16}
$$

### Source and law preservation

By the pair-shield theorem,

$$
\operatorname{SemLaw}(\operatorname{parent}_n)
=
\operatorname{SemLaw}(\sigma_n).
\tag{17}
$$

Hence the new parents still converge to the same minimum joint semantic/law point. This is exact source reprojection, not merely preservation of a textual origin label.

### Retained marked atom

The copied roots agree through the parent mark, so

$$
\Pr_{\operatorname{parent}_n}
  (\text{coalition }S\text{ at }m_n)
=
\Pr_{\sigma_n}
  (\text{coalition }S\text{ at }m_n)
\ge\rho.
\tag{18}
$$

### Strict cuts

$$
\operatorname{entryCut}_n
<
\operatorname{exitCut}_n.
\tag{19}
$$

### Uniform reach to the entry cut

Because the root at \(m_n\) is pure \(q^S\), conditional on reaching that row the coalition is \(S\) with probability one. Therefore

$$
\Pr_{\sigma_n}(\text{reach }m_n)
=
\Pr_{\sigma_n}(\text{coalition }S\text{ at }m_n)
\ge\rho.
\tag{20}
$$

This is the required reach floor measured from the post-mark-tail port. Absolute reach beyond the outer pair row is of course zero; the construction relies essentially on the upstream/downstream two-port interpretation.

### Uniform block hazard

The block consists of the single pure-pair row:

$$
\sum_{t=\operatorname{entryCut}_n}^{\operatorname{exitCut}_n-1}
  \sum_i q_{n,t,i}
=
\sum_i q_i(q^S)
=
|S|
=
2.
\tag{21}
$$

Thus one may take the uniform hazard floor to be \(2\), not merely an unspecified \(\chi>0\).

### Near-minimum post-mark tail and exit suffix

Equations (8)–(9) give

$$
D(\operatorname{postMarkTail}_n)\to D_*,
\tag{22}
$$

and

$$
D\!\left(
 \operatorname{Spine}
   (\operatorname{postMarkTail}_n,\operatorname{exitCut}_n)
 \right)
\to D_*.
\tag{23}
$$

Therefore:

$$
\boxed{
\text{the normalized-return equality actualizer}
\Longrightarrow
\texttt{HasUniformlyReachedPostMarkTwoCutBlock}.
}
\tag{24}
$$

This does not assert that the raw forced-pair packet already had these fields. The new operation is the source-preserving self-replay (10).

It also avoids the audited moat obstruction. The restart is not across a near-minimum unique-all-Continue segment and pays no approximate seam. It occurs behind a pure pair row whose continuation is exactly invisible to every unilateral deviation.

# 3. The one-row block gives a sharper fixed-player debt floor

The general exponential two-cut estimate is unnecessary for this instantiated block because its one-row joint survival is exactly zero.

Let

$$
Z_n
:=
\operatorname{Sem}
 \bigl(\operatorname{Spine}(\sigma_n,m_n)\bigr).
$$

Global minimality gives

$$
D(Z_n)\ge D_*.
\tag{25}
$$

At a pure nonsingleton row, current total debt equals the sum of the four literal endpoint defects:

$$
D(Z_n)
=
\sum_{i\in\operatorname{Fin}4}\delta_{n,i}.
\tag{26}
$$

Hence some block-dependent payer \(p_n\) satisfies

$$
\delta_{n,p_n}\ge \frac{D_*}{4}.
\tag{27}
$$

The canonical one-date best-endpoint deviation at the inner pair row has actual payoff gain

$$
G_{n,p_n}
=
\Pr_{\sigma_n}(\text{reach }m_n)\,
 \delta_{n,p_n}
\ge
\frac{\rho D_*}{4}.
\tag{28}
$$

The pure-row screening identity and the exact live-mass gain formula are already present in the pure nonsingleton collision module.

Since this is a legal unilateral behavioral deviation from \(\sigma_n\),

$$
d_{p_n}(\sigma_n)\ge G_{n,p_n}
\ge
g,
\qquad
g:=\frac{\rho D_*}{4}>0.
\tag{29}
$$

The payer is not fixed before this argument. Because there are four players, pass to a strict subsequence on which

$$
p_n=p
\tag{30}
$$

for one fixed \(p\).

Choose \(\varepsilon_n\downarrow0\), and let \(\tau_n\) replace only player \(p\)'s complete strategy in \(\sigma_n\) by an \(\varepsilon_n\)-best response. Then

$$
d_p(\tau_n)\le\varepsilon_n\longrightarrow0,
\tag{31}
$$

while

$$
U_p(\tau_n)-U_p(\sigma_n)
\ge
d_p(\sigma_n)-\varepsilon_n
\ge
g-\varepsilon_n.
\tag{32}
$$

All other players' complete strategies are unchanged.

Joint compactification of

$$
\sigma_n,\qquad
\tau_n,\qquad
\frac12\sigma_n+\frac12\tau_n
$$

now gives a source cluster \(S_0\), target cluster \(T_0\), and half cluster \(H_0\), with

$$
D(S_0)=D_*,
\qquad
d_p(S_0)\ge g>0,
\qquad
d_p(T_0)=0.
\tag{33}
$$

If

$$
D(T_0)=D_*,
$$

coordinatewise stopping-law convexity and global minimality force equality in every coordinate:

$$
d_i(H_0)
=
\frac{d_i(S_0)+d_i(T_0)}2.
\tag{34}
$$

Consequently,

$$
\operatorname{supp}_+(H_0)
=
\operatorname{supp}_+(S_0)
\cup
\operatorname{supp}_+(T_0),
\tag{35}
$$

and, because \(p\) belongs to the first support but not the second,

$$
\operatorname{supp}_+(T_0)
\subsetneq
\operatorname{supp}_+(H_0).
\tag{36}
$$

This is exactly the checked support-rank handoff. The minimum endpoint can then be reconstructed as a complete same-residual source and entered into the renewable natural-valued support rank.

Thus the equality arm is reduced to

$$
\boxed{
\begin{array}{c}
\text{renewable strict support descent}\\
\text{or}\\
\text{an actual same-opponent off-minimum target }T_0
\text{ with }d_p(T_0)=0.
\end{array}}
\tag{37}
$$

# 4. The off-minimum branch has a canonical relative plateau

The positive-root Zeno sequence need not be followed. There is a direct compact reduction to a unique-all-Continue relative minimum.

Let \(\mathcal K_r\) be the compact terminal-semantic carrier and fix the payer \(p\). Define the closed zero-debt face

$$
\mathcal F_p
:=
\{z\in\mathcal K_r:d_p(z)=0\}.
\tag{38}
$$

It is nonempty because \(T_0\in\mathcal F_p\).

Let \(Z_p\) minimize total debt on this face:

$$
D(Z_p)
=
\mu_p
:=
\min_{z\in\mathcal F_p}D(z).
\tag{39}
$$

The minimum is attained by compactness.

## Relative-plateau theorem

Every exact cap-Nash root against \(Z_p^2\) is all Continue.

Indeed, let \(x\) be exact Nash against the cap \(Z_p^2\), and write

$$
c(x)=\Pr_x(\text{all Continue}).
$$

The arbitrary-root cap decomposition gives, coordinatewise,

$$
d_i(T_xZ_p)
=
\operatorname{Def}_i(x;Z_p^2)
+
c(x)d_i(Z_p).
\tag{40}
$$

Exact root Nash makes the defect term zero, so

$$
d_i(T_xZ_p)=c(x)d_i(Z_p)
\quad\text{for every }i.
\tag{41}
$$

In particular,

$$
d_p(T_xZ_p)=0,
$$

so \(T_xZ_p\in\mathcal F_p\). Also,

$$
D(T_xZ_p)=c(x)\mu_p.
\tag{42}
$$

By the minimality of \(Z_p\) on \(\mathcal F_p\),

$$
\mu_p\le c(x)\mu_p.
\tag{43}
$$

Since

$$
\mu_p\ge D_*>0
\quad\text{and}\quad
c(x)\le1,
$$

we obtain

$$
c(x)=1.
\tag{44}
$$

A product root has joint Continue probability one only when every player Continues surely. Hence

$$
x=q^{\mathrm{allC}}.
\tag{45}
$$

One-stage Nash existence now shows that all Continue is exact, so it is the unique exact root:

$$
\boxed{
\operatorname{ExactNash}(Z_p^2)
=
\{q^{\mathrm{allC}}\}.
}
\tag{46}
$$

Equation (40) is the exact cap-defect decomposition already available in the own-strategy transport module.

The same proof works for every nonempty closed face obtained by requiring an arbitrary fixed set of debt coordinates to vanish.

## Source-faithful actualization

Choose actual profiles \(\zeta_k\) whose semantic pairs converge to \(Z_p\). For the equality-arm parents above, form

$$
\widehat\pi_{n,k}
:=
\operatorname{Cross}_{m_n}(\sigma_n,\zeta_k).
\tag{47}
$$

The pure-pair shield gives

$$
\operatorname{SemLaw}(\widehat\pi_{n,k})
=
\operatorname{SemLaw}(\sigma_n)
\tag{48}
$$

for every \(n,k\), while

$$
\operatorname{Spine}(\widehat\pi_{n,k},m_n+1)
=
\zeta_k.
\tag{49}
$$

Thus a diagonal sequence produces one exact-ancestry, source-preserving omega tail port converging to \(Z_p\). The compact endpoint is not substituted for an actual profile: every approximant is an explicit behavioral tail, and every parent retains the original marked source exactly.

This replaces the possible positive-root Zeno branch by the sharper alternative

$$
\boxed{
\begin{array}{l}
\mu_p=D_*:
\text{ a source-attached minimum point with }p\text{-debt zero};\\[1mm]
\mu_p>D_*:
\text{ a source-attached off-minimum, unique-all-Continue}\\
\text{relative plateau with }p\text{-debt zero}.
\end{array}}
\tag{50}
$$

If \(\mu_p=D_*\), the hard residual reconstructs a complete same-residual minimum source at that point. However, unless the point is obtained through the same-opponent half-mixture limit above, this alone does **not** prove the checked strict support-rank comparison with the incoming parent.

If \(\mu_p>D_*\), the remaining obstruction is now canonical and has no positive exact-root arm at all.

# 5. What this attaches—and what remains

The normalized-return equality arm now genuinely supplies the requested same-witness producer:

$$
\boxed{
\text{equality actualizer}
\Longrightarrow
\texttt{HasUniformlyReachedPostMarkTwoCutBlock}.
}
\tag{51}
$$

Its consumer gives

$$
\boxed{
\text{renewable support descent}
\ \lor\
\text{source-attached }p\text{-zero relative plateau}.
}
\tag{52}
$$

This is an attachment to the current Fin4 source architecture, not merely a conditional theorem about hypothetical cuts.

The strict normalized-inert arm remains different. The generic carrier actualizer still provides:

* the fixed pure pair row;
* its positive reached-mass floor;
* the near-minimum post-row tail;
* literal raw descendants.

The same pair-shielded self-replay therefore gives exact ancestry, reach \(>0\), one-row hazard \(2\), and a near-minimum exit suffix. But its post-mark tail debt converges to the strict whole debt

$$
L>D_*,
$$

rather than to \(D_*\). So it fails exactly the first-cut near-minimality field, not the ancestry, reach, hazard, or exit fields.

The live residuals are therefore:

$$
\boxed{
\begin{array}{ll}
\textbf{Equality arm:}&
\text{consume a source-attached }p\text{-zero relative plateau};\\[1mm]
\textbf{Strict inert arm:}&
\text{lower the actualized first-cut debt from }L\text{ to }D_*,\\
&\text{or consume the unique-all-Continue strict point directly.}
\end{array}}
\tag{53}
$$

The positive-root Zeno descent is no longer needed as a separate terminal case in the equality arm: compact minimization on the killed-debt face produces the unique-all-Continue endpoint directly. What remains is the consumption of that relative inert plateau, or a finite-rank transition out of it.

## Lean-facing decomposition

The reusable declarations suggested by the argument are:

```text
quittingTerminalSemanticLawPoint_crossTailClosure_eq_of_pureNonsingleton

QuittingMarkedPairMinimumReturnActualizer
  .hasUniformlyReachedPostMarkTwoCutBlock_of_purePair

QuittingMarkedPairMinimumReturnActualizer
  .completeBestResponse_supportDescent_or_offMinimumZeroDebt

exists_zeroDebtFaceMinimum_uniqueAllContinue
```

The first belongs beside the current self-tail semantic identities. The second is generic over a decorated-family actualizer with a pure nonsingleton marked terminal. The Fin4 adapter only supplies `terminal_card = 2`. The fourth is a compact carrier theorem and does not depend on Fin4.

These are paper-level proofs here; I did not modify the repository. Current `main` is
`e509d5c355a98afa361ff3b8688ba355b4aa278b`. Its static, trust, documentation, and import checks had passed, while the full `lake build` was still running at the latest inspection.   The source and validation status were checked under the project runbook. 
