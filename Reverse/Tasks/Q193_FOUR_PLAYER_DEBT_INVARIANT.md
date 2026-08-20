# Question 193: A coupled positive-debt invariant for Q-admissible four-player tables

## Semantic dynamics

Let \(I=\{1,2,3,4\}\) and let \(r(S)\in\mathbb Q^I\) be specified for every
nonempty \(S\subseteq I\). A semantic state is a pair
\(z=(u,b)\in\mathbb R^I\times\mathbb R^I\), with debt

\[
d_i(z)=b_i-u_i,\qquad D(z)=\sum_i d_i(z).
\]

For a product mixed action \(x\), write \(q_i=x_i(\mathrm Q)\),
\(c_i=1-q_i\), and

\[
p^x_{-i}(A)=
\prod_{j\in A}q_j\prod_{j\notin A\cup\{i\}}c_j
\qquad(A\subseteq I\setminus\{i\}).
\]

For a continuation vector \(v\), put

\[
\begin{aligned}
Q_i(x_{-i})&=\sum_Ap^x_{-i}(A)r_i(A\cup\{i\}),\\
C_i(x_{-i};v_i)&=p^x_{-i}(\varnothing)v_i+
\sum_{\varnothing\ne A}p^x_{-i}(A)r_i(A),\\
F_i(x;v_i)&=q_iQ_i(x_{-i})+c_iC_i(x_{-i};v_i).
\end{aligned}
\]

Define \(T_x(u,b)=(u',b')\) by

\[
u'_i=F_i(x;u_i),\qquad
b'_i=\max\{Q_i(x_{-i}),C_i(x_{-i};b_i)\}.
\]

Let \(e_\infty\) be the semantic state of perpetual Continue. The compact
attainable semantic carrier is

\[
\mathcal K=\overline{\{T_we_\infty:w\text{ is a finite word of product
mixed actions}\}}.
\]

For \(\delta>0\), a positive-debt invariant is a set
\(\mathcal B\subseteq\mathbb R^I\times\mathbb R^I\) satisfying

\[
e_\infty\in\mathcal B,\qquad
z\in\mathcal B\Longrightarrow T_xz\in\mathcal B
\quad\text{for every product }x,\qquad
z\in\mathcal B\Longrightarrow D(z)\geq\delta.
\tag{1}
\]

No closedness of \(\mathcal B\) is required. Such a set exists exactly when
\(D\geq\delta\) throughout \(\mathcal K\). Hence a positive instance of (1)
proves that the game has no uniform-equilibrium payoff.

## Algebraic search filter

Normalize the singleton comparison matrix by

\[
M_{ij}=r_i(\{j\})-r_i(\{i\}),\qquad M_{ii}=0,
\]

and form the corrected core

\[
I_0=I,\qquad
I_{n+1}=\{i\in I_n:\exists j\in I_n,\ j\ne i,\ M_{ij}\leq0\},
\qquad I_*=\bigcap_n I_n.
\]

Any four-player table without a uniform-equilibrium payoff must satisfy:

- \(I_*\ne\varnothing\), necessarily with \(|I_*|=3\) or \(4\);
- the principal matrix \(M_*\) is standard \(Q\): for every right-hand side
  \(q\), the LCP \(w=q+M_*z\), \(w,z\geq0\), \(w_iz_i=0\), is solvable;
- \(M_*\) has no homogeneous simplex solution.

For \(|I_*|=3\), the two directed-cycle sign orientations and positive
determinant give an exact classification. Full-core four-by-four examples
also exist, so this filter is nonvacuous and is not itself evidence for a
positive debt floor.

## Known fences on the invariant

Every invariant satisfying (1) obeys

\[
0<\delta\leq\sum_i\max\{0,r_i(\{i\})\}.
\]

It cannot be coordinatewise order-rectangular: independent recombination of
attained prescribed and cap coordinates forces the zero-debt diagonal point
\((s,s)\), where \(s_i=\max\{0,r_i(\{i\})\}\). It also cannot depend only on
the debt vector \(b-u\). Indeed, saturation along complete fixed-debt fibres,
together with prefix invariance, permits a calibrated product prefix which
contracts the total debt below any positive floor. These no-gos apply without
a finite-complexity bound.

Thus a successful invariant must couple absolute prescribed-payoff and cap
levels; a union of debt-only polyhedra, a debt-only semialgebraic set, or an
axis-aligned coordinate box cannot work.

## Question

Does there exist a rational four-player reward table passing the algebraic
filter and a finitely described coupled set \(\mathcal B\) satisfying (1) for
some explicit \(\delta>0\)?

## Acceptance criterion

An affirmative answer must give the full reward table, not only its singleton
matrix, and a finite description of \(\mathcal B\) using coupled conditions on
\(u\) and \(b\). It must prove containment of \(e_\infty\), invariance under
every product mixed action, and the positive floor with an exact rational or
algebraic value of \(\delta\).

A negative answer must prove that no set satisfying (1) exists for every
four-player table passing the algebraic filter. Because (1) is logically
equivalent to a positive global semantic floor, this would settle the
four-player existence problem. Ruling out another uncoupled template class is
useful pruning but does not answer this question.

## Answer

The semantic recursion admits a strong reduction, but it does **not** presently close the full-core (4\times4) branch. What follows is exact:

1. every invariant can be reduced to a scalar Bellman barrier coupling total debt to the absolute cap vector (b);
2. no table with (|I_*|=3) can have a positive debt floor;
3. there are rational full-core tables passing the filter for which an explicit rational projective lasso forces (D\to0);
4. the remaining full-core matrices can contain genuine zero-cost pivot deadlocks, so a universal negative proof requires an additional charged-return theorem.

Thus the requested affirmative construction or universal negative theorem is not obtained. The results below strictly reduce the unresolved case.

## 1. Exact cap–debt reduction

Put
[
P(x)=\prod_i c_i
]
and let
[
G_i(x)=\sum_{\varnothing\ne S\subseteq I}
\Pr_x(S),r_i(S).
]
Then
[
F_i(x;v_i)=P(x)v_i+G_i(x).
]

Define the autonomous cap map
[
\Gamma_x(b)*i=\max{Q_i(x*{-i}),C_i(x_{-i};b_i)}
]
and the one-stage cap-game regret
[
\rho_i(x,b)
===========

\Gamma_x(b)*i-
\bigl(q_iQ_i(x*{-i})+c_iC_i(x_{-i};b_i)\bigr).
]
Since
[
q_iQ_i+c_iC_i(x_{-i};b_i)=P(x)b_i+G_i(x),
]
we obtain
[
\boxed{
d_i(T_xz)=P(x)d_i(z)+\rho_i(x,b)
}
]
and hence
[
\boxed{
D(T_xz)=P(x)D(z)+\rho(x,b),
\qquad
\rho(x,b)=\sum_i\rho_i(x,b)\ge0.
}
\tag{2}
]

In particular, the update of ((b,D)) is autonomous:
[
(b,D)\longmapsto
\bigl(\Gamma_x(b),,P(x)D+\rho(x,b)\bigr).
\tag{3}
]

This gives an exact normal form for all possible coupled invariants.

Let (s_i=\max{0,r_i({i})}), so that (e_\infty=(0,s)). A cap set
(C\subseteq\mathbb R^4) and a function (\phi:C\to\mathbb R) define
[
\mathcal B_{C,\phi}
===================

{(u,b):b\in C,\ D(u,b)\ge\phi(b)}.
]
This set is invariant whenever
[
s\in C,\qquad
\phi(s)\le\sum_i s_i,
\tag{4}
]
[
\Gamma_x(C)\subseteq C,
\tag{5}
]
and
[
\boxed{
\phi(\Gamma_x(b))
\le
P(x)\phi(b)+\rho(x,b)
\qquad(b\in C,\ x\in[0,1]^4).
}
\tag{6}
]

Moreover, this form loses no generality. Given any invariant (\mathcal B) with floor (\delta), let
[
C={b:\exists u,\ (u,b)\in\mathcal B},
\qquad
\phi(b)=\inf{D(u,b):(u,b)\in\mathcal B}.
]
Then (\phi\ge\delta), and (5)–(6) follow from (2). Consequently:

[
\boxed{
\text{The invariant search may be restricted to }D\ge\phi(b).
}
]

Thus individual prescribed-payoff coordinates need not be tracked separately. The necessary coupling is between total debt and the absolute cap vector.

---

## 2. The diffuse singleton-block operator

Write
[
a_i=r_i({i}),\qquad t_i=b_i-a_i.
]
Starting from (e_\infty), one has
[
t_i=(-a_i)_+\ge0.
]

Fix a player (j) and (\alpha\in(0,1]). For each (m), prepend (m) identical stages in which only (j) may Quit, with probability
[
\varepsilon_m=1-\alpha^{1/m}.
]
The probability that (j) survives the entire block is exactly (\alpha).

For (i\ne j), put
[
A_{ij}=r_i({i,j})-a_i.
]
A single stage updates the cap clearance by
[
t_i^+
=====

\max\bigl{
\varepsilon_mA_{ij},
(1-\varepsilon_m)t_i+\varepsilon_mM_{ij}
\bigr}.
\tag{7}
]
Iterating (7) gives
[
\begin{aligned}
t_i^{(m)}
=\max\Bigl{&
(1-\varepsilon_m)^mt_i+
\bigl(1-(1-\varepsilon_m)^m\bigr)M_{ij},\
&
\max_{0\le \ell<m}
\bigl[
(1-\varepsilon_m)^\ell\varepsilon_mA_{ij}
+
\bigl(1-(1-\varepsilon_m)^\ell\bigr)M_{ij}
\bigr]
\Bigr}.
\end{aligned}
]
Since (\varepsilon_m\to0) and ((1-\varepsilon_m)^m=\alpha),
[
t_i^{(m)}
\longrightarrow
\bigl[\alpha t_i+(1-\alpha)M_{ij}\bigr]_+.
]
For the clock player,
[
t_j^{(m)}=t_j.
]

Thus the limiting singleton-block cap operator is
[
\boxed{
\begin{aligned}
(\Lambda_{j,\alpha}t)*j&=t_j,\
(\Lambda*{j,\alpha}t)*i
&=\bigl[\alpha t_i+(1-\alpha)M*{ij}\bigr]_+,
\qquad i\ne j.
\end{aligned}}
\tag{8}
]

Although pair rewards occur in every finite approximation, their contribution is the (\varepsilon_mA_{ij}) term and disappears in the block limit. All higher-coalition rewards are absent entirely.

The prescribed payoffs over the block satisfy
[
u_j^+=\alpha u_j+(1-\alpha)a_j,
]
[
u_i^+=\alpha u_i+(1-\alpha)r_i({j}),
\qquad i\ne j.
]
Consequently, setting
[
y_i=\alpha t_i+(1-\alpha)M_{ij},
]
we obtain the exact limiting debt formula
[
\boxed{
D^+
===

\alpha D
+
(1-\alpha)t_j
+
\sum_{i\ne j}[-y_i]_+.
}
\tag{9}
]

The block is therefore **zero-cost** precisely when
[
t_j=0,\qquad
\alpha t_i+(1-\alpha)M_{ij}\ge0
\quad(i\ne j);
\tag{10}
]
in that case
[
D^+=\alpha D.
\tag{11}
]

Every (\Lambda_{j,\alpha}) preserves (\mathcal K): it is a limit of finite prefix words, and (\mathcal K) is closed and prefix-invariant. The case (\alpha=0) is obtained by subsequently taking (\alpha\downarrow0).

---

## 3. All three-player cores have zero global debt floor

Suppose (|I_*|=3). By the stated classification, after relabeling its matrix has the form
[
M_*=
\begin{pmatrix}
0&-a&b\
c&0&-d\
-e&f&0
\end{pmatrix},
\qquad
a,b,c,d,e,f>0,
\tag{12}
]
with
[
\det M_*=bcf-ade>0.
\tag{13}
]

### Reset to a one-coordinate cap

For arbitrary (t\ge0), use the ideal blocks
[
\Lambda_{1,0},\qquad
\Lambda_{3,0},\qquad
\Lambda_{2,0}.
]
On the three core coordinates,
[
(t_1,t_2,t_3)
\stackrel{\Lambda_{1,0}}{\longmapsto}
(t_1,c,0)
\stackrel{\Lambda_{3,0}}{\longmapsto}
(b,0,0)
\stackrel{\Lambda_{2,0}}{\longmapsto}
(0,0,f).
\tag{14}
]
The reset may add a finite amount of debt, but after it the core clearance is
[
A(H)=(0,0,H),\qquad H=f>0.
]

### The zero-cost cycle

Starting at (A(H)=(0,0,H)), define
[
\alpha_1(H)=\frac{e}{H+e},
\qquad
H_2=\frac{cH}{H+e}.
]
Clocking player (1) gives
[
(0,0,H)\longmapsto(0,H_2,0)
]
with zero additive debt.

Next set
[
\alpha_3(H_2)=\frac{d}{H_2+d},
\qquad
H_1=\frac{bH_2}{H_2+d}.
]
Clocking player (3) gives
[
(0,H_2,0)\longmapsto(H_1,0,0).
]

Finally set
[
\alpha_2(H_1)=\frac{a}{H_1+a}.
]
Clocking player (2) gives
[
(H_1,0,0)\longmapsto(0,0,\Phi(H)),
]
where
[
\boxed{
\Phi(H)
=======

\frac{bcf,H}
{\bigl(bc+a(c+d)\bigr)H+ade}.
}
\tag{15}
]

Every one of these three blocks satisfies (10), so one cycle multiplies (D) by
[
r(H)=\alpha_1(H)\alpha_3(H_2)\alpha_2(H_1)<1.
\tag{16}
]

The positive fixed point of (\Phi) is
[
\boxed{
H_*=
\frac{bcf-ade}{bc+a(c+d)}>0.
}
\tag{17}
]
Since (\Phi) is increasing and
[
\Phi(H)-H
=========

\frac{H\bigl(bcf-ade-(bc+a(c+d))H\bigr)}
{\bigl(bc+a(c+d)\bigr)H+ade},
]
every orbit (H_{n+1}=\Phi(H_n)), (H_0>0), converges monotonically to (H_*).

At the fixed cycle,
[
r(H_*)=\frac{ade}{bcf}<1.
\tag{18}
]
Hence (r(H_n)) is eventually bounded above by a constant strictly below (1), and therefore
[
D_n\longrightarrow0.
]

### The fourth player does not obstruct the cycle

Let (k\notin I_*). At the iteration where (k) is deleted, all three core players remain. Therefore
[
M_{kj}>0
\qquad(j\in I_*).
\tag{19}
]
The fourth clearance coordinate consequently stays nonnegative under every core clock:
[
t_k^+
=====

\alpha t_k+(1-\alpha)M_{kj}>0.
]
It contributes neither a reflection charge nor an owner charge, since (k) is never clocked.

We have proved:

[
\boxed{
|I_*|=3
\quad\Longrightarrow\quad
\min_{z\in\mathcal K}D(z)=0.
}
\tag{20}
]

Thus **no three-player-core table passing the filter can admit the requested invariant**.

---

## 4. A full-core rational filtered table with an exact contracting lasso

The same obstruction is not confined to three-player cores.

Consider
[
M=
\begin{pmatrix}
0&-2&3&1\
-1&0&-1&2\
-2&2&0&-2\
-2&-1&1&0
\end{pmatrix}.
\tag{21}
]
Every row has a negative off-diagonal entry, so (I_*=I).

Choose
[
a=
\left(-\frac54,,1,,1,,-\frac14\right)
]
and define the singleton rewards by (r_i({j})=a_i+M_{ij}):
[
\begin{aligned}
r({1})&=\left(-\frac54,,0,,-1,,-\frac94\right),\
r({2})&=\left(-\frac{13}4,,1,,3,,-\frac54\right),\
r({3})&=\left(\frac74,,0,,1,,\frac34\right),\
r({4})&=\left(-\frac14,,3,,-1,,-\frac14\right).
\end{aligned}
\tag{22}
]
For every coalition (S) with (|S|\ge2), set
[
r(S)=(0,0,0,0).
\tag{23}
]
Equations (22)–(23) are the complete rational reward table.

### Verification of the algebraic filter

The principal determinants of orders (2,3,4) are respectively
[
(-2,6,2,2,2,2),\qquad
(-10,9,10,2),\qquad
30.
\tag{24}
]
They are all nonzero, and every column has a negative entry. Hence a nonzero homogeneous complementary solution cannot exist: a support of size at least two would contradict nonsingularity of its principal block, while a singleton support would require a nonnegative column.

For (LCP(\mathbf1,M)), singleton supports are inconsistent. Exact support enumeration gives the following obstruction for every larger support:

[
\begin{array}{c|ccccccccccc}
S&
12&13&14&23&24&34&
123&124&134&234&1234\ \hline
\text{obstruction}&
w_4=-\frac32&
z_3=-\frac13&
z_4=-1&
z_2=-\frac12&
z_4=-\frac12&
z_3=-1&
w_4=-\frac32&
z_4=-\frac13&
z_3=-\frac25&
z_2=-3&
z_2=-\frac12
\end{array}
\tag{25}
]
so (z=0,w=\mathbf1) is its only solution.

For completeness, this implies the (Q)-property directly. Define
[
F_M(x)=x^+-Mx^-.
]
Solutions of (F_M(x)=q) are in bijection with solutions of (LCP(q,M)), via
[
w=x^+,\qquad z=x^-.
]
The homogeneous result makes (F_M) proper. At (q=\mathbf1), its unique preimage is (x=\mathbf1), where (F_M) is locally the identity, so its proper degree is (+1). The degree remains (+1) for every target (q), hence every (q) has a preimage. Thus (M) is standard (Q).

### Rational zero-cost lasso

Here
[
s=(0,1,1,0),
\qquad
t(e_\infty)=s-a=
\left(\frac54,0,0,\frac14\right).
]
Now apply the following three ideal singleton blocks:

[
\begin{aligned}
\Lambda_{2,,4/5}:
\quad&
\left(\frac54,0,0,\frac14\right)
\longmapsto
\left(\frac35,0,\frac25,0\right),[1ex]
\Lambda_{4,,5/6}:
\quad&
\left(\frac35,0,\frac25,0\right)
\longmapsto
\left(\frac23,\frac13,0,0\right),[1ex]
\Lambda_{3,,3/4}:
\quad&
\left(\frac23,\frac13,0,0\right)
\longmapsto
\left(\frac54,0,0,\frac14\right).
\end{aligned}
\tag{26}
]

At each step, the clock owner has zero clearance and every updated coordinate is nonnegative. Hence every block has zero additive charge. One cycle multiplies the debt by
[
\frac45\cdot\frac56\cdot\frac34=\frac12.
]
Since (D(e_\infty)=2),
[
D_n=2^{1-n}\longrightarrow0.
\tag{27}
]

This is a full-core rational table passing the complete algebraic filter, but it has **no** positive-debt invariant.

---

## 5. Why the full-core universal argument is still missing

A natural attempted theorem would say that every full-core (Q), (R_0) matrix admits a projective lasso of the form (10). That statement is not justified.

For example, consider
[
N=
\begin{pmatrix}
0&3&-1&3\
2&0&1&-3\
2&-2&0&-1\
-1&-2&1&0
\end{pmatrix}.
\tag{28}
]
It also passes the (Q), (R_0), full-core tests. Its principal determinants are
[
(-6,2,3,2,-6,1),\qquad
(10,-3,5,8),\qquad
25,
]
and the same exact (LCP(\mathbf1,N)) degree certificate applies.

Starting from (t=0),
[
\Lambda_{1,1/2}(0)=(0,1,1,0),
]
and then
[
\Lambda_{4,3/4}(0,1,1,0)
========================

\left(\frac34,0,\frac12,0\right).
\tag{29}
]
At the latter state, the zero coordinates are (2) and (4). But

* clocking (2) immediately makes coordinate (4) negative, because (N_{42}=-2);
* clocking (4) immediately makes coordinate (2) negative, because (N_{24}=-3);
* clocking (1) or (3) incurs an owner charge because their clearances are positive.

Thus this reachable boundary point has no nontrivial zero-cost outgoing singleton pivot. It does not prove a positive floor—small charged moves or genuinely mixed product actions may still return with asymptotically vanishing cost—but it proves that the three-core lasso argument cannot simply be iterated through every full-core matrix.

### An exact charged return for the same matrix

The zero-cost deadlock does not prevent exact charged recurrence elsewhere in
the cap space.  Put

\[
A=\left(\frac34,0,\frac14,0\right)
\]

and apply the singleton blocks

\[
(2,\tfrac89),\qquad
(3,\tfrac12),\qquad
(1,\tfrac23),\qquad
(4,\tfrac34).
\]

The resulting cap-clearance cycle is

\[
\begin{aligned}
A
&\longmapsto (1,0,0,0)\\
&\longmapsto (0,\tfrac12,0,\tfrac12)\\
&\longmapsto (0,1,\tfrac23,0)\\
&\longmapsto A.
\end{aligned}
\tag{30}
\]

Only the first block has positive additive charge.  Its reflection charge is
\(2/9\), coming from coordinate \(4\); the other owner and reflection charges
vanish.  The survival product after that charge is

\[
\frac12\cdot\frac23\cdot\frac34=\frac14.
\]

Consequently the complete word acts on total debt by

\[
D\longmapsto \frac29D+\frac1{18},
\tag{31}
\]

whose unique fixed point is \(D=1/14\).  Repetition gives the exact formula

\[
D_k=\frac1{14}+\left(\frac29\right)^k
  \left(D_0-\frac1{14}\right).
\tag{32}
\]

Thus any cap–debt lower-barrier inequality valid for these limiting blocks,
with a domain containing \(A\), must assign \(A\) a lower bound at most
\(1/14\).  This is a local certificate test, not a global upper bound for
every reward completion: \(A\) is different from the deadlock point in (29),
and membership of a full semantic state above \(A\) in the attainable carrier
still has to be established.  Other singleton words and genuinely mixed
product roots may also force a smaller debt.

## Conclusion

The exact status is:

[
\boxed{
\begin{array}{l}
\text{All }|I_*|=3\text{ cases have }\min_{\mathcal K}D=0.[1mm]
\text{Many full-core filtered matrices also have explicit contracting lassos.}[1mm]
\text{No rational table with a proved positive coupled barrier is obtained.}[1mm]
\text{No universal negative theorem for all full-core matrices is proved.}
\end{array}}
]

The remaining statement needed for a negative answer is a **charged projective-return theorem**: every full-core four-dimensional (Q), (R_0) singleton matrix, together with every reward completion, must admit a sequence whose cumulative reflection/owner charge is negligible relative to its survival contraction. Conversely, an affirmative example must defeat precisely that mechanism and supply a finitely described positive solution of the cap-space Bellman inequality (6).
