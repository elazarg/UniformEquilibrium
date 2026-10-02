# Normalized-motion convex circulation closes approximate forward packets

Identity: PAIRED_HULL_REVIEW  
Date: 2026-09-01  
Status: ordinary mathematics, independently reviewed; the periodic-word
theorem is valid, but its unrestricted common-tail existence arm collapses
to the already checked one-row normalized-motion producer. The surviving new
content is an exact description of the boundary motion set and a sharp
robust-inert/separator diagnosis. No unconditional Fin4 consumer or Lean
declaration is claimed.

Independent review:
[CODEX_DESCENDANT](../feedback/PAIRED_HULL_REVIEW__NORMALIZED_MOTION_CONVEX_CIRCULATION__BY_CODEX_DESCENDANT.md),
including a fresh delta check of the full convex-hull identity (4.3).

## 1. Question and answer

Let small positive-absorption asymptotically exact support roots be available at tail vectors
converging to one common vector \(b\). Must their actual source profiles be
ordered as literal successors before they can produce an approximate forward
packet?

No. Literal source-to-source ordering is sufficient but not necessary. The
exact Bellman values in the forward packet can be constructed afresh from a
periodic root word. What must cancel is the roots' **normalized Bellman
motion**.

The main theorem below says:

> if zero lies in the convex hull of finitely many limiting normalized
> motions at one common tail, then those independently selected root families
> produce arbitrarily charged exact-Bellman forward packets with vanishing
> support error.

By Carathéodory, at most \(|I|+1\) motion families are needed; for Fin4, at
most five.

Only the absolute support errors must tend to zero. No estimate of the form
\(\eta_{n,\ell}=o(a_{n,\ell})\) is required. The same selected row is reused
at a fixed stagewise tolerance inside the periodic packet, so its Nash error
does not accumulate with the number of repetitions.

The theorem is mathematically sound, but Section 4.2 shows that it is not a
new producer in the unrestricted product-root setting. The full common-tail
motion set is already convex: it is the convex hull of the binding singleton
reward columns. Thus if the motions in the theorem cancel, one synthetic
small product root has vanishing normalized motion and enters the checked
one-row stationary-prefix compiler directly. The periodic word is useful as
an exact finite-packet calculation, not as a strictly stronger existence
route.

The genuinely surviving contrapositive is a sharp bounded-capacity barrier.
In a game with no uniform-equilibrium payoff, the binding singleton columns
at any common limiting tail are strictly separated from zero. Along a bounded
exact path this separator is a local ballistic costate. At an attained
positive global-minimum cap the checked singleton moat is strict in every
coordinate, so the motion set is empty altogether: small positive-absorption
support roots cannot be based at that cap.

## 2. Data

Let \(I\) be a finite nonempty player set and let all reward coordinates lie
in \([-M,M]\), where \(M>0\). Write

\[
 T_q(v)=\operatorname{quittingRootSuccessorPayoff}(v,q)
\]

for the one-row Bellman map of a product root \(q\). Put

\[
 c(q)=\Pr_q(\text{all Continue}),\qquad
 a(q)=1-c(q).
\]

When \(a(q)>0\), let \(u(q)\) be the conditional absorbing payoff of the
stationary repetition of \(q\). Coordinatewise,

\[
 T_q(v)=c(q)v+a(q)u(q),
\qquad
 u(q)\in[-M,M]^I.
\tag{2.1}
\]

Let

\[
 P_i=\operatorname{quittingPunishmentValue}(r,i)
\]

be the game's checked punishment-floor vector. Fix one vector
\(b\in[-M,M]^I\),
and finitely many phase labels \(\ell\in\{1,\ldots,L\}\). For every \(n,\ell\)
suppose we are given:

1. a tail \(b_{n,\ell}\in[-M,M]^I\) with
   \[
   b_{n,\ell}\longrightarrow b;
   \tag{2.2}
   \]
2. a number \(\eta_{n,\ell}\ge0\) and a product root \(q_{n,\ell}\) which is
   support-\(\eta_{n,\ell}\) Nash against \(b_{n,\ell}\), with
   \[
   \max_\ell\eta_{n,\ell}\longrightarrow0;
   \tag{2.2a}
   \]
3. positive absorption
   \[
   a_{n,\ell}:=a(q_{n,\ell})>0,
   \qquad
   \max_\ell a_{n,\ell}\longrightarrow0;
   \tag{2.3}
   \]
4. the floor bound \(b_{n,\ell}\ge P\) coordinatewise; and
5. normalized-motion limits
   \[
   w_{n,\ell}:=u(q_{n,\ell})-b_{n,\ell}
   \longrightarrow w_\ell.
   \tag{2.4}
   \]

Assume there are weights

\[
 \beta_\ell>0,\qquad
 \sum_{\ell=1}^{L}\beta_\ell=1,\qquad
 \sum_{\ell=1}^{L}\beta_\ell w_\ell=0.
\tag{2.5}
\]

The tails may be caps of unrelated actual profiles. No literal handoff
between phase \(\ell\) and phase \(\ell+1\) is assumed.

## 3. Convex-circulation theorem

### Theorem 3.1

Under the data in Section 2, for every \(\delta>0\) and \(Q\ge0\) there is a
finite forward packet in the fixed cube \([-M,M]^I\) such that:

1. every Bellman successor equation is exact;
2. every displayed root is support-\(\delta\) Nash at its packet tail;
3. every packet tail is at least \(P-\delta\) coordinatewise; and
4. total raw absorption charge is at least \(Q\).

Consequently the quitting game has a uniform-equilibrium payoff against
unrestricted unilateral behavioral deviations.

### Proof

Put

\[
 \alpha_n=\max_\ell a_{n,\ell},
 \qquad
 \tau_n=\sqrt{\alpha_n}.
\]

After discarding finitely many indices, \(0<\alpha_n<1\). For every phase
define the positive integer

\[
 m_{n,\ell}
 =
 \left\lfloor
   {\tau_n\beta_\ell\over a_{n,\ell}}
 \right\rfloor.
\tag{3.1}
\]

Because \(a_{n,\ell}\le\alpha_n\),

\[
 {\tau_n\beta_\ell\over a_{n,\ell}}
 \ge {\beta_\ell\over\sqrt{\alpha_n}}
 \longrightarrow\infty,
\]

so every \(m_{n,\ell}\) is eventually positive. Moreover,

\[
 0\le
 \tau_n\beta_\ell-m_{n,\ell}a_{n,\ell}
 <a_{n,\ell}\le\alpha_n.
\tag{3.2}
\]

Construct a finite root word \(W_n\) by repeating \(q_{n,1}\)
\(m_{n,1}\) times, then \(q_{n,2}\) \(m_{n,2}\) times, and so on. The order
is arbitrary but fixed. Its total raw absorption is

\[
 A_n=\sum_{\ell=1}^{L}m_{n,\ell}a_{n,\ell}
 =\tau_n+o(\tau_n).
\tag{3.3}
\]

Let \(C_n\) be the whole-word Continue product. Since the largest one-row
absorption is \(\alpha_n\to0\) and

\[
 \sum_{\ell}m_{n,\ell}a_{n,\ell}^2
 \le\alpha_n A_n=o(A_n),
\]

the logarithmic product estimate gives

\[
 1-C_n=A_n+o(A_n)=\tau_n+o(\tau_n).
\tag{3.4}
\]

In particular, the word has positive whole-word absorption.

Write an individual occurrence in the word as \(r\), with absorption \(a_r\),
conditional payoff \(u_r\), and let

\[
 \omega_r=\prod_{s>r}(1-a_s)
\]

be the survival weight of all later rows. Iterating (2.1) at the common
reference vector \(b\) gives

\[
 T_{W_n}(b)-b
 =\sum_r\omega_r a_r(u_r-b).
\tag{3.5}
\]

First ignore the survival weights. By (2.4), (3.2), and (2.5),

\[
\begin{aligned}
 \sum_r a_r(u_r-b)
 &=
 \sum_{\ell}
 m_{n,\ell}a_{n,\ell}
 \bigl(w_{n,\ell}+b_{n,\ell}-b\bigr)\\
 &=\tau_n\sum_\ell\beta_\ell w_\ell+o(\tau_n)
 =o(\tau_n).
\end{aligned}
\tag{3.6}
\]

All vectors \(u_r-b\) have sup norm at most \(2M\). Also

\[
 0\le1-\omega_r\le\sum_{s>r}a_s.
\]

Therefore the difference between (3.5) and (3.6) has norm at most

\[
 2M\sum_{r<s}a_ra_s\le M A_n^2=o(\tau_n).
\tag{3.7}
\]

Equations (3.5)--(3.7) give

\[
 T_{W_n}(b)-b=o(\tau_n).
\tag{3.8}
\]

The affine whole-word map has the form

\[
 T_{W_n}(v)=C_nv+A_n^{\mathrm{vec}}.
\]

Its unique periodic fixed point is

\[
 v_{n,0}^{\mathrm{per}}
 ={A_n^{\mathrm{vec}}\over1-C_n}.
\]

Using (3.4) and (3.8),

\[
 v_{n,0}^{\mathrm{per}}-b
 ={T_{W_n}(b)-b\over1-C_n}
 \longrightarrow0.
\tag{3.9}
\]

Starting from this fixed point, apply the rows of \(W_n\) in order and write
\(v_{n,r+1}=T_{q_r}(v_{n,r})\). The word closes exactly:

\[
 v_{n,|W_n|}=v_{n,0}^{\mathrm{per}}.
\tag{3.10}
\]

The fixed point is a convex combination of the conditional absorbing payoff
vectors \(u_r\), and every successor is a convex combination of its current
tail and one \(u_r\). Hence every \(v_{n,r}\) lies in \([-M,M]^I\). From
(2.1),

\[
 \|v_{n,r+1}-v_{n,r}\|_\infty\le2M a_r.
\]

Together with (3.3) and (3.9), this yields the uniform within-word estimate

\[
 \max_r\|v_{n,r}-b\|_\infty\longrightarrow0.
\tag{3.11}
\]

At an occurrence of phase \(\ell\),

\[
 \|v_{n,r}-b_{n,\ell}\|_\infty\longrightarrow0.
\tag{3.12}
\]

The root \(q_{n,\ell}\) is support-\(\eta_{n,\ell}\) Nash at
\(b_{n,\ell}\). Changing the tail affects only the Continue endpoint, by the
opponent-Continue probability times the coordinate displacement. Thus it is
support-
\(\eta_{n,\ell}+\|v_{n,r}-b_{n,\ell}\|_\infty\) Nash at \(v_{n,r}\).
The same tail estimate and \(b_{n,\ell}\ge P\) give

\[
 v_{n,r}\ge P-\|v_{n,r}-b_{n,\ell}\|_\infty.
\tag{3.13}
\]

Choose \(n\) so large that the support error above and the floor error in
(3.13) are both below \(\delta\). Periodically repeat the root word and its
exact Bellman value cycle.
Every repetition contributes the positive raw charge \(A_n\). A finite
number of repetitions therefore reaches any prescribed \(Q\), while the
same support and floor tolerance remains valid at every row.

This is precisely the checked finite-forward-packet interface. Its checked
consumer gives a uniform-equilibrium payoff. \(\square\)

## 4. Finite-dimensional separation alternative

For a fixed limiting tail \(b\), let \(\mathcal W(b)\) be the set of all
limits \(w\) arising from sequences satisfying (2.2)--(2.4), (2.2a), and the
floor condition. This is a compact subset of \([-2M,2M]^I\): closedness
follows by a diagonal selection from the defining sequences. Explicitly, if
\(w^m\to w\), choose from the sequence defining \(w^m\) one term whose tail,
absorption, support error, and normalized motion are respectively within
\(1/m\) of \(b,0,0,w^m\). These selected terms form one defining sequence
for \(w\), and the floor inequality is closed.

If

\[
 0\in\operatorname{conv}\mathcal W(b),
\]

Carathéodory gives at most \(|I|+1\) points and nonnegative weights satisfying
(2.5) after deleting zero weights. Theorem 3.1 closes the game. Therefore:

### Corollary 4.1

If the game has no uniform-equilibrium payoff, then for every \(b\) with
\(\mathcal W(b)\ne\varnothing\),

\[
 0\notin\operatorname{conv}\mathcal W(b).
\tag{4.1}
\]

Consequently there are a unit vector \(\theta_b\) and \(\kappa_b>0\) such
that, after choosing the sign of \(\theta_b\),

\[
 \theta_b\mathbin\cdot w\ge\kappa_b
 \qquad(w\in\mathcal W(b)).
\tag{4.2}
\]

For Fin4, failure of (4.2) is witnessed by at most five normalized-motion
families.

This separator is not required to be coordinatewise nonnegative. It is a
local motion costate, not automatically an instance of the nonnegative
social-weight chamber.

### 4.2 Exact description of the motion set

The use of asymptotically exact, rather than exact, roots makes the boundary
of \(\mathcal W(b)\) elementary.

Write

\[
 s_i=r_i(\{i\}).
\]

Put

\[
 J(b)=\{j:b_j=s_j\}.
\]

Then, whenever \(b\ge P\) and \(b_i\ge s_i\) for every player,

\[
 \boxed{
 \mathcal W(b)
 =\operatorname{conv}\{r(\{j\})-b:j\in J(b)\}.}
\tag{4.3}
\]

Here the convex hull of the empty set is empty. In particular,

\[
 \mathcal W(b)\ne\varnothing
 \quad\Longleftrightarrow\quad
 b\ge P,\quad b_i\ge s_i\ \text{for every }i
 \ \text{and}\ 
 J(b)\ne\varnothing.
\tag{4.4}
\]

Moreover, for every binding coordinate \(j\),

\[
 r(\{j\})-b\in\mathcal W(b).
\tag{4.5}
\]

For the nontrivial inclusion from left to right, take a defining sequence
\(q_n\). Vanishing joint absorption forces every marginal Quit probability
to zero. Normalize the marginal hazards by their sum and pass to a simplex
limit \(\pi\). The conditional stationary law of \(q_n\) puts asymptotically
all its mass on singleton coalitions: conditional collision mass is
\(O(\sum_iq_{n,i})\). Hence

\[
 u(q_n)\longrightarrow\sum_j\pi_jr(\{j\}).
\tag{4.6}
\]

If \(\pi_j>0\), player \(j\) Quits with positive probability along a
subsequence at a nonnegligible fraction of total hazard. Its supported-Quit
inequality and the vanishing support error give \(s_j\ge b_j\). The
supported-Continue inequalities give \(b_i\ge s_i\) for every player, so
\(j\in J(b)\). Therefore \(\pi\) is supported on \(J(b)\), proving that
every element of \(\mathcal W(b)\) lies in the right side of (4.3).

Conversely, fix any probability vector \(\pi\) supported on \(J(b)\), and
give player \(j\) Quit probability \(h\pi_j\). The total hazard is \(O(h)\).
For every active \(j\), both endpoint values agree at \(h=0\); all endpoint
differences are uniformly \(O(h)\). For an inactive player, only Continue is
prescribed, and its endpoint inequality at \(h=0\) is weakly favorable.
Thus these roots are support-\(C h\) Nash for one reward-dependent finite
constant \(C\), their absorption is asymptotic to \(h\), and their
conditional stationary payoff tends to \(\sum_j\pi_jr(\{j\})\). This proves
the reverse inclusion in (4.3).

For the extreme point \(\pi_j=1\), the support error can be read explicitly.
Let \(q_h\) give only player \(j\) Quit probability \(h\). Player \(j\)'s
two endpoint values are exactly equal. For \(i\ne j\), only Continue is
prescribed, and

\[
 Q_i(q_h;b)-C_i(q_h;b)
 =(1-h)(s_i-b_i)
   +h\bigl(r_i(\{i,j\})-r_i(\{j\})\bigr)
 \le 2Mh.
\tag{4.7}
\]

Thus \(q_h\) is support-\(2Mh\) Nash at the fixed tail \(b\), its absorption
is \(h\), and its conditional stationary payoff is exactly \(r(\{j\})\).
Letting \(h\downarrow0\) proves (4.5) directly.

Consequently, in a no-UE table every binding cap cluster has the explicit
finite inequalities

\[
 \theta_b\mathbin\cdot\bigl(r(\{j\})-b\bigr)\ge\kappa_b
 \qquad(b_j=s_j).
\tag{4.8}
\]

If every singleton inequality is strict, \(\mathcal W(b)=\varnothing\): this
is precisely the robust all-Continue approximate-root chamber, not a hidden
small-charge direction.

Because (4.3) is already convex, the unrestricted common-tail test needs at
most \(|J(b)|\) canonical singleton directions, hence at most four in Fin4.
More strongly, convex cancellation already gives a *single* family with
vanishing normalized motion. Indeed, if

\[
 b=\sum_{j\in J(b)}\pi_jr(\{j\}),
\tag{4.9}
\]

take the root whose Quit hazards are \(h\pi_j\). Its absorption is
\(h+O(h^2)\), its support error is \(O(h)\), and its conditional absorbing
payoff is \(b+O(h)\). Consequently

\[
 \|T_{q_h}(b)-b\|_\infty=O(h^2)
 =O(h)\,a(q_h).
\tag{4.10}
\]

Since \(b\ge P\), the fixed tail is Simon-rational at error zero. Choosing
one positive error of order \(h\) that dominates both the support defect and
the normalized motion instantiates
`HasArbitrarilySmallQuittingNormalizedMotionRows`. The checked theorem
`stationarilyGenerated_of_arbitrarilySmallNormalizedMotionRows` therefore
consumes (4.9) without the periodic construction.

Thus Theorem 3.1 is not a stronger unrestricted existence interface. A
source-restricted list of motions cannot rescue that distinction: once its
convex cancellation is known, (4.3) constructs the synthetic one-row product
root from the reward table and the common tail alone.

Finally, if \(b=B\) is the cap coordinate of an attained positive global
minimum semantic pair of debt \(D_*>0\), the checked theorem
`minimumTerminalSemantic_singletonMargin` gives

\[
 B_i-r_i(\{i\})\ge D_*>0\qquad(i\in I).
\tag{4.11}
\]

Hence \(J(B)=\varnothing\) and

\[
 \mathcal W(B)=\varnothing.
\tag{4.12}
\]

This is stronger than separation: no sequence of positive-absorption roots
with vanishing support error can converge to the positive-minimum cap. Any
approximate-forward construction must first move its tail a nonvanishing
distance away from that cap, or use a different payoff coordinate than the
minimum cap. That macroscopic cap/source seam is exactly what the local
normalized analysis does not construct.

## 5. Bounded exact paths become ballistic

Suppose

\[
 v_{n+1}=T_{q_n}(v_n)
\]

is one infinite exact support-Nash Bellman path in the reward cube, assume

\[
 v_n\ge P\qquad\text{coordinatewise for every }n,
\]

and suppose

\[
 \sum_n a(q_n)<\infty.
\tag{5.1}
\]

Then

\[
 \|v_{n+1}-v_n\|_\infty\le2M a(q_n),
\]

so \(v_n\to b\). If positive absorption occurs infinitely often, every
cluster point of

\[
 w_n={v_{n+1}-v_n\over a(q_n)}
 =u(q_n)-v_n
\tag{5.2}
\]

belongs to \(\mathcal W(b)\).

Under no uniform payoff, (4.2) implies, after discarding a finite prefix,

\[
 \theta_b\mathbin\cdot(v_{n+1}-v_n)
 \ge {\kappa_b\over2}a(q_n)
\tag{5.3}
\]

on every positive-absorption row. Thus the bounded-capacity tail is
one-sided in a fixed scalar direction. It is not recurrent hidden at smaller
scale.

This explains why bounded exact capacity alone does not manufacture the
approximate packet: one needs a source operation producing an opposing
normalized motion at the **same limiting tail**, or a consumer for the
separator. A horizontal response at another cap does not yet do either.

If absorption is eventually zero, the path instead enters a literal
zero-charge exact-root tail. That is the separate inert boundary.

### 5.1 Literal cap-lifted source orbits

This applies without an orientation change to the checked cap-lifted orbit,
whose rows have \(\eta=0\).
For an actual terminal profile \(\sigma\),
`quittingCapLiftedPunishmentFloorOrbit` has value

\[
 v_n=B(\sigma_n),
 \]

where \(\sigma_{n+1}\) is obtained by literally prefixing \(\sigma_n\) by
the selected exact cap--Nash root, and its checked policy identity is

\[
 v_{n+1}=T_{q_n}(v_n).
\tag{5.4}
\]

Thus the preceding separation is not merely about an abstract orientation of
Nash--Bellman edges.  On every cap-lifted source orbit of a no-UE table whose
positive-absorption rows occur infinitely often, the cap increments are
eventually one-sided in one fixed scalar direction after normalization by
root absorption.  The orbit still retains the literal original suffix with
positive product survival when it starts above the positive global minimum.

What is missing is an operation at the same cap cluster producing an opposing
normalized asymptotically exact root motion. The retained horizontal paid row
is not such a root, and its gain is not root absorption charge.

### 5.2 Exact trace-friction consequence

There is nevertheless a source-facing quantitative consequence. Fix one
finite phase count \(L\), independent of \(n\), and consider a cyclic cap
chart with tails \(b_{n,k}\), exact roots \(q_{n,k}\), and horizontal rebase
seams

\[
 \ell_{n,k}
 =b_{n,k+1}-T_{q_{n,k}}(b_{n,k}),
 \qquad b_{n,L}=b_{n,0}.
\tag{5.5}
\]

Assume \(b_{n,k}\to b\) for every phase, all positive root absorptions tend
to zero, and the corresponding normalized motions have cluster points in
\(\mathcal W(b)\). Normalize only phases with positive absorption;
zero-absorption phases have zero Bellman increment and contribute zero to the
charge sum. Under no UE, (4.2) and finite compactness give eventually

\[
 \theta_b\mathbin\cdot
 {T_{q_{n,k}}(b_{n,k})-b_{n,k}\over a(q_{n,k})}
 \ge {\kappa_b\over2}
\tag{5.6}
\]

for every positive-absorption phase. Summing the exact cyclic identity

\[
 0=\sum_k\bigl(T_{q_{n,k}}(b_{n,k})-b_{n,k}
                    +\ell_{n,k}\bigr)
\]

therefore yields

\[
 \boxed{
 \theta_b\mathbin\cdot\sum_k\ell_{n,k}
 \le-{\kappa_b\over2}\sum_k a(q_{n,k}).}
\tag{5.7}
\]

Thus a source rebase cycle at one cap cluster cannot hide its seams at
little-o of root charge.  Either the roots supply the convex
circulation consumed by Theorem 3.1, or every actual cyclic rebase pays a
fixed first-order signed trace friction. This is an exact obstruction, not a
consumer: the present source atlas has no theorem converting the left side
of (5.7) into chronological charge or finite rank.

## 6. Exact bounded-capacity regression

The two-player moving-successor family already used as a capacity regression
has a strictly separated normalized motion.

Choose \(d<0<c\) and rewards

\[
 r(\{0\})=(0,d),\qquad
 r(\{1\})=(d,0),\qquad
 r(\{0,1\})=(c,c).
\]

At equal hazards \(t\), the exact Bellman tail and successor are

\[
 y_i^t={t(c-d)\over1-t},
 \qquad
 x_i^t=tc.
\]

The root absorption is

\[
 a_t=1-(1-t)^2=2t-t^2,
\]

and

\[
 {x^t-y^t\over a_t}
 \longrightarrow (d/2,d/2).
\tag{6.1}
\]

Hence the normalized-motion cluster set is the singleton
\(\{(d/2,d/2)\}\), strictly separated from zero. The literal forward
successor recursion is determined by

\[
 y^{t_{n+1}}=x^{t_n},
 \qquad
 t_{n+1}={t_nc\over c-d+t_nc}.
\tag{6.2}
\]

Because \(d<0\), one has

\[
 {t_{n+1}\over t_n}\longrightarrow {c\over c-d}<1.
\]

Thus the compatible hazards decay geometrically in the genuine forward
direction and the total exact charge is finite.

This game is in a solved two-player regime and is not a counterexample. It is
an exact boundary test showing that:

\[
 \text{moving-source matching}+\text{small exact roots}
 \not\Longrightarrow
 \text{normalized circulation}.
\]

The example therefore cannot be repaired by source matching alone.  In view
of Section 4.2, the missing Fin4 input must instead move to a different tail
with controlled source semantics, or consume the separator there.

## 7. Relation to the maintained question

This sharpens the moving-successor analysis in
[PAIRED_HULL_REVIEW__MOVING_SUCCESSOR_TWO_ROW_AND_FIXED_CHART_CAPACITY.md](PAIRED_HULL_REVIEW__MOVING_SUCCESSOR_TWO_ROW_AND_FIXED_CHART_CAPACITY.md).
That note correctly shows that verbatim reuse of one root loses quadratic
cheapness. The present theorem shows that phase roots need not come from one
literal source chain once a common limiting tail and convex normalized-motion
cancellation are available: the periodic Bellman chart itself supplies
literal successor matching.

It does not answer
[FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md](../archive/FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md)
unconditionally. Rather, it corrects the interpretation of the finite
normalized-motion alternative in that question:

1. convex cancellation of finitely many unrestricted common-tail motions is
   already the checked one-row normalized-motion branch;
2. at a positive global-minimum cap there are no such motions because of the
   strict singleton moat; and
3. away from that cap, the remaining alternative is to consume the explicit
   binding-singleton separator or the signed trace friction (5.7).

Accordingly, searching the hard source for five unrelated opposing motions at
the minimum cap is futile. The missing source operation is a macroscopic,
source-faithful move to a different tail together with renewable control, or
a consumer for the robust-inert/separated chamber.

## 8. Sources inspected

- QuittingFiniteForwardPacket and
  quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets in
  UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean;
- quittingRootSuccessorPayoff_sub_tail_eq_absorption_mul_stationary_sub and
  the normalized-motion stationary compiler in
  UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/NormalizedMotionStationaryPrefixProducer.lean;
- quittingCapLiftedPunishmentFloorOrbit and its literal prefix/policy
  identities in
  UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean;
- isQuittingRootSupportApproxNash_of_tail_close in
  UniformEquilibrium/Quitting/Projective/Lasso.lean;
- FaceCirculationCertificate and its finite-closing consumer in
  UniformEquilibrium/Quitting/Circulation/SingletonFaceCirculation.lean and
  MultiOwnerFaceCirculationFiniteClosing.lean;
- the fixed-chart and periodic cap-cocycle calculations in
  [PAIRED_HULL_REVIEW__MOVING_CAP_CHART_COCYCLE_AND_FORWARD_LIFT.md](PAIRED_HULL_REVIEW__MOVING_CAP_CHART_COCYCLE_AND_FORWARD_LIFT.md); and
- the exact two-player moving-successor regression in
  [CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md](CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md).
- `QuittingSimonRationalPayoffAt` in
  `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/SuppliedCorrespondence.lean`;
- `HasArbitrarilySmallQuittingNormalizedMotionRows` and
  `stationarilyGenerated_of_arbitrarilySmallNormalizedMotionRows` in
  `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/NormalizedMotionStationaryPrefixProducer.lean`;
  and
- `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`.

## 9. Nonclaims and next falsifiable test

- The finite motion-family condition is not a new source interface in the
  unrestricted common-tail setting: if it holds, a single synthetic product
  row already enters the checked compiler.
- The separator may have mixed signs and therefore is not itself a social
  payoff weight or a terminal consumer.
- Asymptotically exact roots at different limiting tails cannot be combined
  by this theorem.
- Positive actual marked-row absorption is not exact-root absorption and does
  not enter the theorem without a root-typing adapter.
- The theorem constructs an abstract exact-Bellman packet; it does not join
  the actual profiles from which the phase caps may have been read.

The next concrete test is source-facing:

> Can a source-attached paid/reset operation move from the strictly inert
> positive-minimum cap to a different rational tail and renew there, with its
> macroscopic cap seam paid by chronological charge or a finite rank? If it
> cannot, can the binding-singleton separator at the new tail price that
> failure?

Either outcome would strictly advance the bounded-capacity branch.
