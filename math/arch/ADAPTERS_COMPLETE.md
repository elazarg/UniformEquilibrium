The strongest correct result has two parts.

1. There is a finite proof-relevant grammar whose admitted traces compile to actual behavioral stopping laws, with a genuine projective compactness theorem.
2. The grammar cannot admit every exact selected-root construction. A rational four-player table gives a trace-visible same-source maximal-root operation whose graph is not closed. That obstruction survives arbitrary compact witnesses, summable finite-macro decoders, and every bounded ranked enlargement satisfying the required terminal and backward-consumer conditions.

The second part supplies the requested negative answer.

---

# 1. The actual-law category

Let

$$
\overline{\mathbb N}=\mathbb N_0\cup\{\infty\},
\qquad
\mathcal L=\left\{\mu\in \ell^1(\overline{\mathbb N}):
\mu\ge 0,\ \|\mu\|_1=1\right\}.
$$

An actual profile is

$$
\Sigma_I=\mathcal L^I,
\qquad
d_\Sigma(\sigma,\sigma')
 =\sum_{i\in I}\|\mu_i-\mu_i'\|_1.
$$

Every \(\mu\in\mathcal L\) has an actual behavioral realization. Writing

$$
S_\mu(n)=\mu(\{n,n+1,\ldots,\infty\}),
$$

use the hazard

$$
h_\mu(n)=
\begin{cases}
\dfrac{\mu(n)}{S_\mu(n)},&S_\mu(n)>0,\\[4pt]
0,&S_\mu(n)=0.
\end{cases}
$$

Then the resulting stopping time has law \(\mu\), including its exact Never mass.

The use of the \(\ell^1\) metric is deliberate. Weak convergence of pure dates
\(\delta_n\to\delta_\infty\) does not preserve undiscounted quitting payoffs. By contrast, \(\ell^1\)-convergence uniformly preserves all counterfactual terminal laws.

Let \(\Lambda(\sigma)\) be the complete first-quitting-time/coalition law, and let

$$
\Lambda_i(\sigma,\tau_i)
 =\Lambda(\sigma[i\leftarrow\tau_i]).
$$

The product-measure inequality and contraction under pushforward give

$$
\sup_{\tau_i\in\mathcal L}
\left\|
\Lambda_i(\sigma,\tau_i)
-\Lambda_i(\sigma',\tau_i)
\right\|_1
\le
\sum_{j\ne i}\|\mu_j-\mu_j'\|_1.
\tag{1}
$$

Thus, if all rewards are bounded by \(R\),

$$
\sup_{\tau_i}
\left|
U_i(\sigma[i\leftarrow\tau_i])
-U_i(\sigma'[i\leftarrow\tau_i])
\right|
\le
R\sum_{j\ne i}\|\mu_j-\mu_j'\|_1.
\tag{2}
$$

In particular, the unrestricted cap

$$
B_i(\sigma)
=
\sup_{\tau_i\in\mathcal L}
U_i(\sigma[i\leftarrow\tau_i])
$$

satisfies the same bound. Equations (1)–(2) quantify over every behavioral replacement, including Never and arbitrarily late stopping.

The elementary operations are continuous in this metric on their displayed domains.

For instance, product-root prefixing by \(x\in[0,1]^I\) is

$$
(P_x\mu_i)(0)=x_i,\qquad
(P_x\mu_i)(n+1)=(1-x_i)\mu_i(n),
$$

including

$$
(P_x\mu_i)(\infty)=(1-x_i)\mu_i(\infty),
$$

and

$$
\|P_x\mu_i-P_y\nu_i\|_1
\le
2|x_i-y_i|+\|\mu_i-\nu_i\|_1.
\tag{3}
$$

For a depth-\(k\) suffix, let

$$
s_i^k(\mu_i)=\mu_i(\{k,k+1,\ldots,\infty\}).
$$

On the domain \(s_i^k\ge \rho>0\),

$$
\left\|
\operatorname{Suf}_k(\mu_i)
-\operatorname{Suf}_k(\nu_i)
\right\|_1
\le
\frac{2}{\rho}\|\mu_i-\nu_i\|_1.
\tag{4}
$$

Finite concatenation and complete unilateral replacement are similarly exact.

A freely varying family of arbitrary replacements is not compact in this strategic metric. Consequently, a replacement that varies in a limiting argument must either be fixed by trace restriction, range over a certified compact \(\ell^1\)-family, or be handled by the summable decoder below. This restriction is necessary, not cosmetic.

---

# 2. Proof-relevant ports

A port is a pair

$$
P=(X,s),
$$

where \(X\) is compact metrizable and

$$
s:X\longrightarrow \Sigma_I^m
$$

is a continuous map to a finite tuple of actual source profiles. The tuple may include marked continuations, literal repaired sources, or counterfactual profiles.

Every displayed semantic quantity is required to be its exact value on \(s(x)\). Whenever such quantities are trace-visible, they must be continuous on \(X\), or must be produced by a decoder carrying an explicit convergence budget.

The initial port is a singleton. Hence its actual source is fixed.

The grammar has the following finite collection of constructors:

$$
\mathsf G ::=
\mathsf{CW}
\mid
\mathsf{SD}
\mid
\mathsf{Case}
\mid
\mathsf{Rank}
\mid
\mathsf{PostRank}
\mid
(\mathsf G;\mathsf G).
$$

Elementary finite macros are special cases of \(\mathsf{CW}\).

---

# 3. Constructor CW: compact witness and continuous compiler

A `CW` edge from \(P=(X,s)\) consists of:

* a compact witness space \(W\);
* a closed relation

  $$
  R\subseteq X\times W;
  $$
* totality:

  $$
  \pi_X(R)=X;
  $$
* a continuous actual compiler

  $$
  C:R\longrightarrow\Sigma_I^{m'};
  $$
* a continuous visible-label map;
* a finite proof object showing that \(C(x,w)\) is obtained from \(s(x)\) by the displayed legal elementary macro.

The child port is

$$
P'=(R,C).
$$

The witness remains in the trace. In particular, no selector theorem is being silently invoked.

If the operation is set-valued, this constructor records a member of the closed relation. If the operation claims a unique selected output, its selected graph must itself be closed.

Because \(R\) is compact, every visible source/label/child graph produced by a `CW` edge is compact and hence closed.

---

# 4. Constructor SD: summable finite-macro decoder

A summable decoder consists of compact finite code spaces

$$
Z_n\subseteq X\times W_0\times\cdots\times W_{n-1}
$$

with continuous surjective restrictions

$$
r_{n+1,n}:Z_{n+1}\to Z_n.
$$

Its complete code space is the compact inverse limit

$$
Z_\infty=\varprojlim Z_n.
$$

For every \(n\), there is a continuous actual approximation

$$
\sigma_n:Z_n\to\Sigma_I^m.
$$

Every extension \(z_{n+1}\in Z_{n+1}\) carries a finite legal macro certificate

$$
\gamma_n(z_{n+1}):
\sigma_n(r_{n+1,n}z_{n+1})
\rightsquigarrow
\sigma_{n+1}(z_{n+1}).
$$

There are explicit uniform budgets

$$
d_\Sigma\bigl(
\sigma_{n+1}(z_{n+1}),
\sigma_n(r_{n+1,n}z_{n+1})
\bigr)
\le \varepsilon_n,
\qquad
\sum_{n=0}^{\infty}\varepsilon_n<\infty.
\tag{5}
$$

Every limit-visible annotation \(\lambda_n\), including every LawMin error, has a corresponding budget

$$
d_\lambda(\lambda_{n+1},\lambda_n)\le \alpha_n,
\qquad
\sum_n\alpha_n<\infty.
\tag{6}
$$

If exact minimization is claimed at the limit, the recorded minimization errors must satisfy

$$
\delta_n^{\mathrm{LM}}\longrightarrow 0
\tag{7}
$$

along this same code, not along a separately chosen source sequence.

For \(z\in Z_\infty\), equation (5) gives an actual limit

$$
D(z)=\lim_{n\to\infty}\sigma_n(z|_n)\in\Sigma_I^m,
$$

with

$$
d_\Sigma(D(z),\sigma_n(z|_n))
\le
E_n,
\qquad
E_n:=\sum_{j\ge n}\varepsilon_j.
\tag{8}
$$

The convergence is uniform in \(z\), so \(D:Z_\infty\to\Sigma_I^m\) is continuous.

## Reach budgets

Suppose a suffix or conditional operation at stage \(n\) is intended to survive in the decoded trace. If its reach observable has Lipschitz constant \(L\), the decoder must record

$$
\operatorname{Reach}(\sigma_n(z|_n))\ge \rho_n
$$

and

$$
\rho_n-L E_n>0.
\tag{9}
$$

Then

$$
\operatorname{Reach}(D(z))
\ge \rho_n-L E_n>0.
$$

Thus no conditional object survives after its reach witness has disappeared.

## Closed source provenance

The provenance object is not merely the closure of a finite-descendant relation. It is the full inverse-limit ancestry relation

$$
\begin{aligned}
\mathsf{Prov}_D
=
\bigl\{&
\bigl(
s(x),
(\sigma_n,\gamma_n)_{n\ge 0},
D(z)
\bigr):
\\
&z=(x,w_0,w_1,\ldots)\in Z_\infty,
\\
&\gamma_n
\text{ starts exactly at }\sigma_n
\text{ and ends exactly at }\sigma_{n+1}
\bigr\}.
\end{aligned}
\tag{10}
$$

This is the continuous image of the compact space \(Z_\infty\), after retaining the finite path certificates as code coordinates. Therefore it is compact and closed. Its projection

$$
\mathsf{Anc}_D
\subseteq
\Sigma_I^m\times\Sigma_I^m
$$

is also closed.

Every decoded descendant therefore has one displayed actual ancestry from the exact initial source. It is not merely semantically equivalent to some descendant.

By (1)–(2), the decoded profile also preserves the complete unrestricted-response kernel uniformly.

---

# 5. Constructor Rank: corrected bounded ranked recursion

A rank inequality by itself is insufficient. The complete package is as follows.

Fix \(K<\infty\). For every \(0\le k\le K\), let \(X_k\) be a compact rank-\(k\) node space.

There are compact certificate spaces and closed terminal relations

$$
T_k\subseteq X_k\times C_k.
$$

For every \(k\), fix a compact metrizable outcome carrier \(Y_k\). Every
visible terminal outcome and every visible backward output is an actual trace
port.

Crucially, there is an explicit terminal consumer

$$
\operatorname{consume}_k:
T_k\longrightarrow Y_k.
\tag{11}
$$

The consumer is continuous and is implemented by the compact-witness or
summable-decoder constructor. It cannot hide an arbitrary discontinuous
choice at rank zero.

This is the required map

$$
\operatorname{Terminal}(N)\longrightarrow\operatorname{Outcome}(N).
$$

For every \(\ell<k\), there is a closed successor relation

$$
S_{k\ell}
\subseteq
X_k\times W_{k\ell}\times X_\ell.
\tag{12}
$$

The relation includes a `CW` or `SD` proof that the displayed \(X_\ell\)-node is an actual child of the exact parent source.

Completeness means

$$
\pi_{X_k}
\left(
T_k\cup\bigcup_{\ell<k}S_{k\ell}
\right)
=X_k.
\tag{13}
$$

For every successor branch there is a trace-safe backward compiler

$$
\operatorname{back}_{k\ell}:
S_{k\ell}
\times_{X_\ell}
(X_\ell\times Y_\ell)
\longrightarrow
Y_k.
\tag{14}
$$

The backward compiler is itself implemented by `CW` or `SD`; it is not an arbitrary pointwise map.

## Ranked closure theorem

Define recursively the complete outcome relation

$$
O_k\subseteq X_k\times Y_k.
$$

At rank zero,

$$
O_0=
\left\{
\bigl(x,\operatorname{consume}_0(x,c)\bigr):
(x,c)\in T_0
\right\}.
$$

For \(k>0\),

$$
\begin{aligned}
O_k={}&
\left\{
\bigl(x,\operatorname{consume}_k(x,c)\bigr):
(x,c)\in T_k
\right\}
\\
&\cup
\bigcup_{\ell<k}
\left\{
\left(
x,
\operatorname{back}_{k\ell}(x,w,x',y')
\right):
\begin{array}{l}
(x,w,x')\in S_{k\ell},\\
(x',y')\in O_\ell
\end{array}
\right\}.
\end{aligned}
\tag{15}
$$

Then every \(O_k\) is compact, closed, and total over \(X_k\).

Indeed, by induction \(O_\ell\) is compact. The fiber product

$$
S_{k\ell}\times_{X_\ell}O_\ell
$$

is a closed subset of a compact product, hence compact. Its image, together
with the retained parent coordinate \(x\), under the continuous backward
compiler is compact. The terminal graph is compact for the same reason.
Equation (15) is a finite union of compact sets. Totality over \(X_k\)
follows from (13) and the induction hypothesis.

This is precisely where closed branch graphs and trace-safe child/backward maps are needed. A decreasing rank proves only finite termination; it does not imply that selected children survive limits.

---

# 6. Pointwise ranked producers

After one actual limiting node \(x_\infty\) has already been reconstructed, a pointwise producer may be used with:

* an initial rank \(r(x_\infty)\in\mathbb N\);
* strict decrease at every child;
* an actual child construction;
* a consumer for every terminal certificate;
* a backward compiler for every child outcome.

This is the preceding ranked theorem on the singleton parent space

$$
X=\{x_\infty\}.
$$

No continuity in an external source parameter is required, because there is no longer an external parameter.

Such a producer is not trace-visible before \(x_\infty\) has been reconstructed. It cannot retroactively replace an edge that was required to occur in every finite truncation.

---

# 7. Projective compactness theorem

Let \(\mathcal G\) be a grammar term from a fixed singleton initial port. Let

$$
E_n
$$

be the space of proof-relevant executions truncated at visible depth \(n\). Every witness, branch tag, ancestry certificate, reach certificate, and LawMin error belongs to the execution object.

Composition is by closed fiber products. Finite case splits are finite disjoint unions. Consequently:

$$
E_n\ \text{is compact for every }n,
$$

and the restriction maps

$$
\pi_{n+1,n}:E_{n+1}\to E_n
$$

are continuous.

Consider one sequence

$$
e_m\in E_{n_m},
\qquad
n_m\longrightarrow\infty,
\tag{16}
$$

all beginning at the same initial port. This is one common sequence of executions; one is not permitted to use unrelated sequences for different trace addresses.

Assume that every noncompact numerical annotation is covered by a decoder budget such as (6), and in particular that the LawMin errors occurring in (16) converge along the same extraction. Exact LawMin conclusions additionally require limit error zero.

For each fixed depth \(d\), the restrictions

$$
\pi_{n_m,d}(e_m)\in E_d
$$

have a convergent subsequence. A diagonal extraction gives one subsequence \(m_j\) and points

$$
e^{(d)}\in E_d
$$

such that, simultaneously for every \(d\),

$$
\pi_{n_{m_j},d}(e_{m_j})
\longrightarrow e^{(d)}.
\tag{17}
$$

Continuity of restriction yields

$$
\pi_{d+1,d}(e^{(d+1)})=e^{(d)}.
\tag{18}
$$

Hence \((e^{(d)})_{d\ge0}\) is one compatible inverse-limit execution.

Every `SD` controller track occurring in this family has one code \(z\in Z_\infty\), not one independently chosen code at each depth. Its actual controller is \(D(z)\). Every other source in the trace is obtained from this controller or one of its exact descendants by the displayed legal compilers.

Closedness of `CW`, equation (10) for `SD`, and the ranked closure theorem imply that every limiting visible edge is legal. Equation (9) preserves every required reach floor. Equations (1)–(2) pass all unrestricted unilateral behavioral comparisons to the limit.

Therefore:

> **Projective realization theorem.**
> Every sequence (16) admitted by the grammar has a subsequence converging to one compatible family of legal actual executions. Each decoded controller track has one actual behavioral stopping-law limit, and all finite trace sources descend from that same controller through the recorded legal operations.

If the finite executions are literally nested,

$$
e_{m+1}|_{n_m}=e_m,
$$

the extraction is unnecessary; they already define the compatible inverse-limit code.

---

# 8. Instantiation of the non-elementary operations

The listed quitting-game operations fit the grammar under the following exact hypotheses.

| Operation                | Correct adapter                                                                                                                                                     |
| ------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Arbitrary exact cap root | Record the root as a `CW` witness in a closed root relation; prefixing is the continuous compiler.                                                                  |
| Optimized root           | `CW` only after proving that the optimized-root relation is closed. Storing a selected output is not enough.                                                        |
| Moving-law minimizer     | `CW` when the feasible actual-law correspondence is compact in the strategic metric and has the recovery property needed for a closed argmin graph; otherwise `SD`. |
| Compact limit witness    | `SD`, unless an actual limit compiler has independently been proved continuous. Weak semantic compactness alone is insufficient.                                    |
| Source regeneration      | `CW` for one finite legal macro; `SD` for summably many macros. The ancestry relation must be (10).                                                                 |
| Finite case split        | A finite closed tagged cover. Open strict branches require a positive margin witness or must be postponed until after a pointwise limit.                            |
| Renewable transition     | The complete `Rank` package (11)–(14), not merely a rank inequality.                                                                                                |

For example, suppose \(X,Q\) are compact, \(F_x\subseteq Q\) are nonempty feasible sets, \(F\subseteq X\times Q\) has closed graph and is lower hemicontinuous, and \(f:X\times Q\to\mathbb R\) is continuous. Then the minimizer graph

$$
M=
\left\{
(x,q):
q\in F_x,\ 
f(x,q)=\min_{q'\in F_x}f(x,q')
\right\}
\tag{19}
$$

is closed.

Indeed, if \(x_n\to x\), \(q_n\to q\), and \(q_n\) minimizes at \(x_n\), closedness gives \(q\in F_x\). For any \(y\in F_x\), lower hemicontinuity supplies \(y_n\in F_{x_n}\) with \(y_n\to y\), and

$$
f(x_n,q_n)\le f(x_n,y_n).
$$

Taking limits proves \(f(x,q)\le f(x,y)\).

Without the recovery property, a new better feasible point may appear only at the limiting source. That is exactly the failure exploited below.

If the terminal consumers land in the disjoint union

$$
\begin{aligned}
\mathcal Y_r={}&
\mathsf{ApproxNashWithOneLimitPayoff}(r)
\\
&\sqcup\mathsf{PositiveChronologicalReturn}(r)
\\
&\sqcup\mathsf{ConsumedRenewableExit}(r)
\\
&\sqcup\mathsf{PositiveGapCertificate}(r),
\end{aligned}
\tag{20}
$$

then the ranked and projective theorems compile one member of \(\mathcal Y_r\). The grammar cannot, by itself, prove that every construction has terminal consumers of these four kinds; that is game-specific mathematical content.

---

# 9. A rational four-player obstruction

We now define a precise trace-visible construction that no admitted adapter can realize.

Let

$$
I=\{a,b,c,d\}.
$$

For every nonempty quitting coalition \(S\), define the rational reward table

$$
r_a(S)=
\begin{cases}
1,&b\in S\text{ and }a\notin S,\\
0,&\text{otherwise},
\end{cases}
$$

$$
r_b(S)=
\begin{cases}
-1,&b\in S,\\
1,&a\in S\text{ and }b\notin S,\\
0,&a\notin S\text{ and }b\notin S,
\end{cases}
$$

and, for \(p\in\{c,d\}\),

$$
r_p(S)=
\begin{cases}
-1,&p\in S,\\
0,&p\notin S.
\end{cases}
\tag{21}
$$

The all-Never payoff is zero.

For \(t\in[0,1]\), let the literal source profile \(\sigma_t\) be

$$
\mu_a=\mu_c=\mu_d=\delta_\infty,
\qquad
\mu_b=t\delta_1+(1-t)\delta_\infty.
\tag{22}
$$

Thus \(b\) quits at date \(1\) with probability \(t\), while everyone else plays Never.

The compact total parent port is

$$
\left([0,1],\ t\longmapsto\sigma_t\right).
$$

It contains the full source family, rather than merely one selected sequence
\(t_n\downarrow0\).

The prescribed payoff vector is

$$
U(\sigma_t)=(t,-t,0,0).
\tag{23}
$$

The unrestricted cap vector is

$$
B(\sigma_t)=(t,0,0,0).
\tag{24}
$$

Player \(a\) can receive \(1\) only when \(b\) quits first without \(a\), an
event of probability at most \(t\); Never attains \(t\). Player \(b\) obtains
zero by Never and \(-1\) whenever it is the first quitter, while \(a\) never
quits in the source. Each passive player obtains zero by Never and a
nonpositive payoff under every replacement. Thus (24) is the cap over every
finite stopping date, every mixed stopping law, and Never.

Now prefix the literal continuation \(\sigma_t\) by a product root on the compact face

$$
x(q)=(q,0,0,0),
\qquad
0\le q\le \frac12.
$$

Thus \(a\) quits at the first prefixed stage with probability \(q\), and all other players continue to the literal source \(\sigma_t\).

Write the resulting actual profile as

$$
P_q\sigma_t.
$$

The continuation reach is

$$
1-q\ge\frac12.
\tag{25}
$$

There is therefore a uniform positive reach floor.

At the prefixed root, players \(c\) and \(d\) strictly prefer Continue: their
Quit payoff is \(-1\) and their Continue payoff is zero. Player \(b\) also
strictly prefers Continue: its Quit payoff is \(-1\), whereas its Continue
payoff is \(q\ge0\). Player \(a\)'s Quit payoff is zero and its Continue payoff
is its continuation cap \(t\). Consequently \(x(q)\) is an exact cap--Nash
root if and only if

$$
qt=0.
\tag{26}
$$

Define the exact same-source cap-root relation on the displayed
uniform-reach face

$$
\mathcal R
=
\left\{
(t,q)\in[0,1]\times
\left[0,\frac12\right]:
qt=0
\right\}.
\tag{27}
$$

This relation is closed.

Now require the **greatest** root on this displayed face:

$$
q^{\max}(t)
=
\max\{q:(t,q)\in\mathcal R\}.
$$

Explicitly,

$$
q^{\max}(t)
=
\begin{cases}
0,&t>0,\\[2mm]
\dfrac12,&t=0.
\end{cases}
\tag{28}
$$

Its graph is not closed. Taking \(t_n=1/n\),

$$
(t_n,q^{\max}(t_n))
=
\left(\frac1n,0\right)
\longrightarrow
(0,0),
$$

but

$$
q^{\max}(0)=\frac12.
$$

The child profiles also expose the failure:

$$
P_0\sigma_{1/n}
\longrightarrow
P_0\sigma_0
\quad\text{in }\ell^1,
\tag{29}
$$

whereas the required child at \(t=0\) is

$$
P_{1/2}\sigma_0\ne P_0\sigma_0.
\tag{30}
$$

This is not a vanishing-reach phenomenon: equation (25) gives reach at least
\(1/2\). It is not source switching: every child uses the literal displayed
continuation \(\sigma_t\). The continuation values in (26) are the
unrestricted caps in (24), not stationary or bounded-horizon substitutes.

The discontinuity is also visible in the full terminal semantic trace. Along
\(t_n\downarrow0\), the selected child has player \(b\)'s prescribed payoff
and cap tending to zero. At \(t=0\), the required child
\(P_{1/2}\sigma_0\) gives player \(b\) prescribed payoff and cap \(1/2\).
Indeed, for every \(q,t\),

$$
U_b(P_q\sigma_t)=q-(1-q)t,
\qquad
B_b(P_q\sigma_t)=q.
\tag{31}
$$

For the cap, Continue at the prefixed root and then Never attains \(q\): it
earns \(1\) exactly when \(a\) quits there. Quitting at that root earns
\(-1\), and after joint continuation every finite quit earns \(-1\), so no
behavioral replacement does better.

There is also one fixed initial port. Start from \(\sigma_0\) and use the elementary unilateral replacement

$$
\delta_\infty
\longmapsto
t\delta_1+(1-t)\delta_\infty
$$

for player \(b\). This produces the entire compact source family \(\sigma_t\) from one actual initial source.

Define the online construction \(\mathfrak M\) to be:

1. choose the displayed replacement parameter \(t\);
2. construct the literal source \(\sigma_t\);
3. expose the greatest exact cap--Nash root on the fixed face
   \(x(q)=(q,0,0,0)\), \(0\le q\le1/2\), in the finite trace;
4. prefix the literal source by \(q^{\max}(t)\);
5. expose the resulting child profile.

The maximal root and its child are required in every truncation reaching step 3. They are not post-limit annotations.

---

# 10. Why none of the three adapter kinds can realize \(\mathfrak M\)

The following closure invariant applies to the whole grammar.

> **Closed-output invariant.**
> For a compact parent port, every complete trace-visible output relation produced by `CW`, `SD`, finite composition, finite closed case split, or bounded `Rank` is compact and therefore closed.

For `CW`, this is the continuous image of the compact witness relation.

For `SD`, the complete code space \(Z_\infty\) is compact and the decoder is continuous by the uniform summability bound.

For `Rank`, it is the ranked closure theorem.

Composition uses closed fiber products, and finite case splits use finite unions.

Arbitrary additional compact witnesses do not change the conclusion: existential projection of a compact proof space remains compact.

Applying the invariant to the visible pair \((t,q)\), any admitted realization of \(\mathfrak M\) would make

$$
\{(t,q^{\max}(t)):t\in[0,1]\}
$$

closed. Equation (28) shows that it is not.

Equivalently, if an adapter has a compact proof space \(E\), a continuous surjection

$$
p:E\to[0,1],
$$

and a continuous output \(o:E\to[0,\tfrac12]\), exactness and uniqueness force

$$
o(e)=q^{\max}(p(e)).
$$

Since \(p\) is a quotient map, this would make \(q^{\max}\) continuous. It is not.

Therefore:

### No compact-witness adapter

No compact recorded witness, closed legal relation, and continuous actual compiler can realize the exact online maximal selector.

### No summable decoder

A summable decoder has a compact inverse-limit code and a continuous decoded visible output. If its root labels were not covered by a summable visibility budget, they would not be trace-safe. With the required budget, its output graph is closed, contradicting (28).

A merely pointwise convergent sequence of continuous approximations to \(q^{\max}\) is irrelevant: it has no uniform summable tail and fails the requested projective trace theorem.

### No bounded ranked enlargement

Suppose a bounded ranked enlargement claims to realize \(\mathfrak M\), possibly through terminal branches, successor branches, and backward consumers. By the ranked closure theorem, its complete compiled output relation is closed. Exactness would make that relation the graph of \(q^{\max}\), contradicting (28).

This argument includes every terminal certificate and every backward compiler. Adding more rank tags or terminal outcomes cannot change the topological conclusion while their tagged relations and compilers remain trace-safe.

A compactified search witness such as \(n\in\mathbb N\cup\{\infty\}\), intended to certify \(t\ge1/n\), also fails: as \(t_n\downarrow0\) and \(n\to\infty\), closedness forces the \(q=0\) branch to survive at \(t=0\), where it is not maximal.

---

# 11. Scope of the obstruction

The obstruction applies to an **exact same-source, constrained
absorption-maximal cap-root edge that is visible in the finite trace**. The
constraint is the fixed compact face \(x(q)=(q,0,0,0)\), \(0\le q\le1/2\),
which supplies the uniform continuation-reach floor.

It does not rule out:

* recording the whole closed root relation (27) and choosing the nonmaximal root \(q=0\);
* approximate maximal roots whose decoded visible output is not required to
  equal the exact maximizer at zero error;
* restricting the source family to \(t\ge\eta>0\) or to \(t=0\);
* proving additional hypotheses that make the optimizer relation closed;
* applying the discontinuous selector pointwise after one source \(t\) has already been reconstructed.

The last option does not implement \(\mathfrak M\). In \(\mathfrak M\), the selected root and prefixed child are needed in finite downstream traces. Deferring the choice and then replacing the limiting value \(0\) by \(1/2\) would change the finite trace’s limiting child from (29) to (30), violating restriction compatibility.

Likewise, a uniformly summable decoder whose maximality errors tend to zero
and whose visible roots converge would recover the exact maximizer graph in
the limit, so it remains impossible. The exception above permits only an
actually approximate output or a pointwise post-limit choice, not an exact
decoded realization of \(\mathfrak M\).

---

# Conclusion

The corrected `CW`/`SD`/`Rank` grammar gives actual executable adapters, closed ancestry, surviving reach witnesses, full unrestricted-deviation control, and one common limiting controller. The ranked theorem requires all of the terminal map, closed tagged branch relations, actual child compilers, and trace-safe backward compilers; strict rank decrease alone is not sufficient.

The rational four-player table (21), together with the online constrained
maximal exact cap-root construction (22)–(31), proves that the universal
adapter request is false. Its selector graph is nonclosed despite exact
literal provenance, a uniform \(1/2\) reach floor, and caps computed against
every behavioral replacement. Consequently it admits neither a closed compact
adapter, nor a summably decoded trace realization, nor any bounded renewable
ranked enlargement with trace-safe terminal and backward consumers.
