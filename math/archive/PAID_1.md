The supplied data split into two incompatible objects:

$$
\begin{array}{c|c|c}
\text{object} & \text{absorption / singleton law} & \text{Nash compatibility}\\ \hline
\text{softened product root} & \text{positive, in fact absorption }1
  & \text{uniformly defective}\\
\text{exact root at its complete cap} & 0
  & \text{exact, but all Continue.}
\end{array}
$$

The finite path never puts positive charge and exact source compatibility on the same object. This can be made quantitative.

## 1. The minimum source lies in a strict all-Continue basin

Write \(s_i=r_i(\{i\})\). From the two supplied inequalities,

$$
B_i-s_i\ge D_*,
\qquad
d_i=B_i-U_i,
$$

we obtain

$$
U_i-s_i
  =(B_i-s_i)-d_i
  \ge D_*-d_i
  =\sum_{j\ne i}d_j
  >0.
\tag{1}
$$

Thus the prescribed payoff is strictly above every own singleton payoff. More generally, on the complete debt homotopy

$$
v^t:=B-t(B-U)=B-td,
\qquad 0\le t\le1,
$$

one has

$$
v_i^t-s_i
  =(B_i-s_i)-t d_i
  \ge D_*-d_i
  =\sum_{j\ne i}d_j>0.
\tag{2}
$$

For \(t<1\), the global-minimum prefix budget for an exact root \(x\) against \(v^t\) gives

$$
(1-t)D_*\,A(x)
   \le D(z)-D_*
   =0,
\tag{3}
$$

where \(A(x)\) is the root absorption probability. Since \(D_*>0\), this forces \(A(x)=0\), hence \(x\) is all Continue.

At \(t=1\), the minimum-simplex equality alternative says that a non-all-Continue exact root could only be a solo debt gate: for some \(i\),

$$
d_i(z)=0,
\qquad
U_i=s_i.
$$

Both equalities are excluded by full debt and (1). Therefore:

$$
\boxed{\text{All Continue is the unique exact product root against every }
       v^t,\ 0\le t\le1.}
\tag{4}
$$

Compactness of the root simplex, continuity of the endpoint payoffs, and the uniform gap in (2) then give an open neighborhood \(\mathcal T\) of the whole segment \(\{v^t:0\le t\le1\}\) on which all Continue remains the unique exact root.

There is also a quantitative version. After shrinking to a relatively compact tube, there is \(c_{\mathcal T}>0\) such that

$$
\operatorname{Def}(v,x)\ge c_{\mathcal T}A(x)
\qquad
(v\in\mathcal T),
\tag{5}
$$

where \(\operatorname{Def}\) is total root Nash defect. Near all Continue, this follows directly from the uniform singleton gap; away from all Continue, it follows by compactness and uniqueness of the exact root.

Consequently, local approximate roots cannot retain fixed positive charge:

$$
\operatorname{Def}(v_n,x_n)\longrightarrow0,\quad v_n\in\mathcal T
\quad\Longrightarrow\quad
A(x_n)\longrightarrow0.
\tag{6}
$$

## 2. The complete cap-leakage ledger

Let

$$
z^a=(U^a,B^a),\qquad
D^a=\sum_i d_i^a,\qquad
E_a=D^a-D_*
$$

be the successive complete semantic pairs, and let \(p_a\) be the mover on edge \(a\). Put

$$
g_a:=U^{a+1}_{p_a}-U^a_{p_a}>0.
$$

Because only \(p_a\)'s strategy changes, its unrestricted cap is literally unchanged:

$$
B^{a+1}_{p_a}=B^a_{p_a}.
$$

Therefore its debt falls by exactly its payoff gain:

$$
d^{a+1}_{p_a}-d^a_{p_a}=-g_a.
\tag{7}
$$

Define the complete spectator leakage

$$
L_a:=\sum_{j\ne p_a}
  \bigl(d_j^{a+1}-d_j^a\bigr).
$$

Then the exact debt identity is

$$
\boxed{
L_a=g_a+E_{a+1}-E_a.
}
\tag{8}
$$

This includes all changes of all other unrestricted caps; no cap coordinate has been discarded.

Edgewise, only an edge starting on the minimum fibre immediately yields \(L_a\ge g_a\). But summing the entire path gives a stronger global ledger:

$$
\boxed{
\sum_a L_a
   =\sum_a g_a+E_m
   \ge\sum_a g_a.
}
\tag{9}
$$

Thus every unit of cumulative paid gain is financed by cumulative spectator-debt creation, with the final excess debt added on top. This is the wrong sign for a terminal consumer: the payment is stored as new exploitability, not as admissible absorption charge.

## 3. Exact affine classification of the first fibre exit

Consider one softening starting from a minimum-fibre node, with scale \(t\). In the fixed endpoint-polynomial cell, every \(U_j(t)\), every selected \(B_j(t)\), and hence \(D(t)\), is affine in \(t\). Therefore

$$
g(t)=\beta t,
\qquad
D(t)=D_*+\lambda t
\tag{10}
$$

for constants \(\beta>0\) and \(\lambda\ge0\). The nonnegativity of \(\lambda\) is exactly global minimality.

There are only two possibilities.

### Fibre edge

If \(\lambda=0\), the entire sufficiently short edge remains on the minimum fibre. Its complete leakage is

$$
L(t)=\beta t=g(t),
$$

and the sure-core cardinality decreases by one.

### Strict-leakage edge

If \(\lambda>0\), every positive softening leaves the minimum fibre, with

$$
E(t)=\lambda t,
\qquad
L(t)=(\beta+\lambda)t.
\tag{11}
$$

In particular,

$$
\frac{E(t)}{g(t)}=\frac{\lambda}{\beta}
$$

is scale-independent. Nothing in the supplied assumptions bounds this ratio from above or makes the excess second order.

Because \(U(t)\to U\) and \(B(t)\to B\), sufficiently small strict-leakage endpoints satisfy

$$
U(t),B(t)\in\mathcal T.
$$

Hence their exact prescribed-payoff roots and exact cap roots are all Continue. Their cap lifts have

$$
A=0,
\qquad
\text{cap displacement}=0.
\tag{12}
$$

So the first off-fibre leaf is precisely a **paid but inert complete source**.

## 4. The singleton endpoint is uniformly non-Nash

Suppose all but \(k\in K\) have been softened. Its singleton mass is

$$
\mu(\{k\})
 =
 \left(\prod_{p\in K\setminus\{k\}}\theta_p\right)
 \left(\prod_{j\notin K}(1-q_j)\right)
 >0.
\tag{13}
$$

This is a genuine terminal-law atom.

It is nevertheless separated from every admissible root. Let

$$
\underline d:=\min_{p\in K}d_p(z)>0.
$$

At the original root, each \(p\in K\) has another sure-quitting opponent, so its Continue-minus-Quit endpoint difference is exactly \(d_p(z)\). After shrinking the common neighborhood, continuity gives

$$
C_p-Q_p\ge \frac{\underline d}{2}
\tag{14}
$$

whenever \(p\) has been softened and another original sure quitter remains. Taking every \(\theta_p\le \tfrac12\), the softened player still Quits with probability at least \(1/2\). Replacing its root action by pure Continue therefore gains at least

$$
(1-\theta_p)(C_p-Q_p)
 \ge \frac{\underline d}{4}.
\tag{15}
$$

Thus every post-first-softening product root in the path has a tail-independent Nash defect bounded below by

$$
c_0:=\frac{\underline d}{4}>0.
\tag{16}
$$

In particular, the terminal singleton endpoint is not even an \(o(1)\)-root Nash profile as the softening scales tend to zero.

There is an obvious literal source-matched restart attempt: soften the last sure quitter \(k\) by a small \(\eta>0\), and put the original minimum profile after the all-Continue outcome. That construction really does return to the exact original behavioral source on its survival branch. But it still fails.

Indeed, choose one previously softened \(p\). As \(\eta\to0\), its endpoint comparison converges to the comparison with \(k\) sure, which is bounded below by (14). Its Quit probability remains at least \(1/2\). Hence, for all sufficiently small \(\eta\),

$$
\operatorname{Def}_p
 \ge c_1>0
\tag{17}
$$

for a constant independent of \(\eta\). The unrestricted cap can only increase this deviation gain.

So the literal restart has correct provenance but a fixed Nash defect.

## 5. The exact mismatch

The terminal leaf therefore has the following exact profile:

$$
\begin{aligned}
&\textbf{Raw softened root:}
&&\mu(\{k\})>0,\quad A=1,\quad
  \operatorname{Def}\ge c_0;\\[2mm]
&\textbf{Exact root at }U^m\textbf{ or }B^m:
&&\operatorname{Def}=0,\quad A=0,\quad
  \text{root}=\text{all Continue}.
\end{aligned}
\tag{18}
$$

Equation (5) rules out repairing this mismatch by nearby approximate roots. Fixed positive charge would retain fixed positive defect.

For common softening scale \(t\), the mismatch is especially visible:

$$
g_a=O(t),\qquad
E_m=O(t),\qquad
\mu(\{k\})=O\!\left(t^{|K|-1}\right).
\tag{19}
$$

For \(|K|\ge3\), the singleton atom is of strictly higher order than the paid and leakage terms. For \(|K|=2\), it is first order, but (15) still prevents it from becoming an admissible charged root.

## 6. Exhaustion of the finite path

After stopping at the first strict fibre exit, or continuing only while the path remains on the minimum fibre, the supplied construction has exactly two possible leaves:

$$
\boxed{
\begin{array}{ll}
\text{A.}&
\text{A minimum-fibre point with one sure quitter, a positive singleton atom,}\\
&\text{full positive debt, and an inert exact cap root};\\[1mm]
\text{B.}&
\text{A strict off-minimum point with }E>0,\text{ a paid sibling edge,}\\
&\text{and again an inert exact cap root.}
\end{array}}
\tag{20}
$$

The sure-core cardinality is a valid finite counter for the static softenings, but it is not a renewable proof rank:

* in branch A it reaches its terminal value without a consumer;
* in branch B it leaves the minimum fibre and replaces the discrete counter by an arbitrarily small real excess;
* resetting by the exact all-Continue root is the identity and renews the original rank without spending debt or charge;
* the raw roots with positive charge are not Nash-compatible.

## Verdict on the five requested conclusions

The supplied configuration is **not consumed** by this path.

1. The softened profiles are not terminal approximate Nash profiles; they retain the fixed deviation gain (15)–(17), although their payoffs may converge to \(U\).

2. No uniform-equilibrium payoff follows.

3. No positive cumulative admissible-payoff return follows. Every exact path starting locally from \(U^a\) or \(B^a\) is the constant all-Continue path and has cumulative charge zero. A nonlocal incoming edge from outside \(\mathcal T\) is not supplied.

4. The sure-core counter terminates, but its terminal outputs are the two nonconsumers in (20), not consumers of types 1–3.

5. The calculations do not contradict a positive terminal exploitability gap. Global minimality is exactly compatible with the leakage identity \(L_a=g_a+E_{a+1}-E_a\).

Nor is an explicit positive-gap reward table produced here. Therefore the valid result is a sharp **no-consumer theorem for the product-base paid singleton-exit mechanism**, not one of the five requested global alternatives. The remaining implication is genuinely nonlocal:

$$
\text{paid inert endpoint in the minimum tube}
\quad\Longrightarrow\quad
\text{incoming charged return or renewable complete-source regeneration}.
$$

Nothing in the stated hypotheses supplies that implication.

This is a mathematical obstruction result, not a new checked Lean declaration; I made no repository change or completion claim after inspecting the exact source state, consistent with the project runbook. 
