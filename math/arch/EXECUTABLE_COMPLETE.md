The residual splits into two distinct questions:

1. whether the proposed syntax is closed under composition and coherent diagonals; and
2. whether the concrete Fin4 producers actually supply the certificates required by that syntax.

The first question has a complete positive answer. The second does not become automatic: exact optimized-root selection already supplies a tightly supported same-source obstruction. The cleanest completion is therefore a **normal-form theorem** for all admitted trace edges, followed by an exact audit of which quitting-game operations instantiate it.

The attached correction already contains the essential two-sorted distinction between trace adapters and post-limit control adapters, as well as the common-execution condition needed to obtain one controller.  The elementary total-variation reconstruction and unrestricted-cap continuity are the base case. 

# 1. Compact executable normal form

Let

$$
K=\mathbb N\sqcup\{\infty\},
\qquad
\mathsf S=\Delta(K)^I,
\qquad
\mathsf S_p=\mathsf S^p,
$$

with the sum total-variation metric.

A **compact executable normal-form adapter**

$$
A:p\rightsquigarrow q
$$

consists of the following data.

1. A compact metrizable witness space \(W_A\).

2. A closed domain

$$
D_A\subseteq \mathsf S_p\times W_A.
$$

3. A continuous actual compiler

$$
G_A:D_A\longrightarrow\mathsf S_q.
$$

4. A closed relation

$$
\mathcal R_A
\subseteq
\mathsf S_p\times W_A\times\mathsf S_q
$$

containing the graph of \(G_A\), together with a theorem

$$
\mathcal R_A(s,w,y)
\Longrightarrow
y\text{ is the named legal behavioral operation applied to }s.
\tag{1}
$$

5. When source provenance is relevant, a closed relation

$$
\mathcal A_A
\subseteq
\mathsf S_p\times W_A\times\mathsf S_q
$$

containing the graph of \(G_A\), together with a theorem that membership in \(\mathcal A_A\) implies the intended literal ancestry.

6. A modulus \(\omega_A\) such that

$$
d_q\!\left(G_A(s,w),G_A(s',w')\right)
\le
\omega_A\!\left(d_p(s,s')+d_{W_A}(w,w')\right),
\tag{2}
$$

with \(\omega_A(t)\to0\) as \(t\downarrow0\).

The distinction between \(\mathcal R_A\) and mere output actuality is important. A point of \(\mathsf S_q\) is an actual standalone behavioral packet, but (1) proves that it was obtained by the named operation from the named input.

# 2. Finite proof-relevant grammar

The trace-visible grammar is

$$
\begin{aligned}
E::={}&
\mathsf{Elem}
\mid
\mathsf{ClosedSelect}
\mid
\mathsf{Decode}
\mid
\mathsf{FiniteCase}\\
&\mid
\mathsf{TraceRank}_K
\mid
E;E
\mid
E\otimes E .
\end{aligned}
\tag{3}
$$

Here \(K\in\mathbb N\) is part of the program label. A pointwise ranked producer is a separate control constructor and is not a trace edge.

## Theorem 1 — normal-form elimination

Every finite expression \(E\) in (3) has a compact executable normal-form adapter

$$
\mathcal N(E).
$$

The construction is effective from the certificates carried by the grammar expression.

## Proof

### Elementary edges

Finite prefixing, concatenation, complete replacement, and fixed-depth positive-reach suffixing have the required actual compilers and moduli by the elementary theorem.

### Closed selection

This is already in normal form. In particular, a selected exact cap root has witness space \([0,1]^I\), a closed exact-root relation, and literal prefixing as compiler.

### Composition

Suppose \(A:p\rightsquigarrow q\) and \(B:q\rightsquigarrow r\) are in normal form. Take

$$
W_{B\circ A}=W_A\times W_B
$$

and

$$
\begin{aligned}
D_{B\circ A}
=
\{(s,w_A,w_B):\;&(s,w_A)\in D_A,\\
&(G_A(s,w_A),w_B)\in D_B\}.
\end{aligned}
\tag{4}
$$

This is closed because \(D_A,D_B\) are closed and \(G_A\) is continuous. Define

$$
G_{B\circ A}(s,w_A,w_B)
=
G_B(G_A(s,w_A),w_B).
\tag{5}
$$

The legal-operation theorem is the literal composition of the two operation theorems. Closed ancestry is obtained by substituting the continuously determined intermediate output into the second ancestry relation.

A modulus is

$$
\omega_{B\circ A}(t)
=
\omega_B\!\left(t+\omega_A(t)\right).
\tag{6}
$$

### Product

For \(A_1:p_1\rightsquigarrow q_1\) and \(A_2:p_2\rightsquigarrow q_2\), use the product witness, product domain, and product compiler. With sum metrics one may take

$$
\omega_{A_1\otimes A_2}(t)
=
\omega_{A_1}(t)+\omega_{A_2}(t).
\tag{7}
$$

### Finite cases

Let \(B\) be the finite tag set. For branch \(b\), let \(W_b\) and \(D_b\) be its witness space and closed domain. Use the finite disjoint union

$$
W=\coprod_{b\in B}W_b.
\tag{8}
$$

It is compact. The union of the branch domains is closed because the components of a finite disjoint union are clopen. The compiler is branchwise.

This explains why the **complete tagged branch relation** must be closed. Recording the Boolean result of an open test does not suffice.

### Summable decoder

Suppose

$$
M_n:D\longrightarrow\mathsf S_q
$$

are certified finite macros and

$$
d(M_{n+1}(\xi),M_n(\xi))\le c_n,
\qquad
\sum_n c_n<\infty.
\tag{9}
$$

Write \(C_N=\sum_{n\ge N}c_n\). Then

$$
D_\infty(\xi)=\lim_n M_n(\xi)
$$

is an actual stopping-law packet and

$$
d(D_\infty(\xi),M_N(\xi))\le C_N.
\tag{10}
$$

If \(M_N\) has modulus \(\omega_N\), then

$$
d(D_\infty(\xi),D_\infty(\xi'))
\le
2C_N+\omega_N(d(\xi,\xi')).
\tag{11}
$$

Thus a modulus for the decoder is the monotone regularization of

$$
\omega_{\mathrm{dec}}(t)
=
\inf_N\left(2C_N+\omega_N(t)\right).
\tag{12}
$$

The decoder becomes a normal-form adapter by taking \(G=D_\infty\). Its graph is closed. Its legal-operation theorem is supplied by the recorded closed ancestry relation:

$$
\mathcal A(s,z,M_n(s,z))
\quad\forall n
$$

and hence, by closedness,

$$
\mathcal A(s,z,D_\infty(s,z)).
\tag{13}
$$

This is the source-faithful decoder from the correction. 

### Bounded trace-visible rank

Consider a \(\mathsf{TraceRank}_K\) certificate. Ranks lie in

$$
\{0,\ldots,K\},
$$

branch tags are finite, complete tagged terminal and successor relations are closed, and every selected child and visible backward map is already trace-safe.

Every selected execution has a strictly decreasing rank sequence and therefore length at most \(K\). There are only finitely many possible rank-and-tag skeletons. For each skeleton:

* take the finite product of its compact branch witnesses;
* compose its trace-safe child and backward adapters;
* intersect the corresponding closed tagged relations.

This gives one normal adapter for each skeleton. Their finite disjoint union gives the normal adapter for the whole ranked construction.

Thus bounded trace-visible rank adds no new topological primitive: after certification it is a finite union of finite compositions of normal adapters. ∎

# 3. Explicit decoder reach budgets

For a stopping law \(\mu_i\), define survival to depth \(h\) by

$$
s_{i,h}(\mu_i)
=
\mu_i(\{h,h+1,\ldots,\infty\}).
$$

Then

$$
|s_{i,h}(\mu_i)-s_{i,h}(\nu_i)|
\le
\|\mu_i-\nu_i\|_1.
\tag{14}
$$

Suppose a decoded output has a suffix reach floor \(\alpha>0\), and let

$$
e_N(\delta)=2C_N+\omega_N(\delta).
$$

If

$$
e_N(\delta)\le\frac{\alpha}{2},
\tag{15}
$$

then the finite decoder approximation and every input within distance \(\delta\) retain reach at least \(\alpha/2\). On that domain the suffix modulus is

$$
\|\operatorname{Suf}_h\mu_i-
  \operatorname{Suf}_h\nu_i\|_1
\le
\frac{4}{\alpha}\|\mu_i-\nu_i\|_1.
\tag{16}
$$

For a fixed downstream diagram, let \(L_e\) be the product of the preceding edge constants before suffix edge \(e\), whose required reach is \(\alpha_e\). It suffices to choose \(N\) and then \(\delta\) so that

$$
L_e e_N(\delta)\le\frac{\alpha_e}{2}
\qquad
\text{for every downstream suffix }e.
\tag{17}
$$

This supplies the requested explicit error/reach order:

1. fix the finite downstream diagram;
2. choose \(N\) so the decoder tail \(C_N\) meets all inequalities (17);
3. choose the outer input tolerance using the single finite macro \(M_N\).

No all-depth modulus appears.

# 4. Coherent diagonal theorem

Let

$$
P_1\preceq P_2\preceq\cdots
$$

be restriction-compatible finite rooted diagrams in the grammar. Let

$$
\mathcal E_m
$$

be one actual execution of \(P_m\), with the interpretation that for every fixed \(k\), the restrictions

$$
\mathcal E_m|_{P_k},
\qquad m\ge k,
$$

are executions of the same named diagram \(P_k\).

Assume:

* every initial and exogenous stopping-law input has finite-coordinate and Never-coordinate limits and eventual finite-tail tightness;
* all elementary suffix floors are displayed;
* shared edge occurrences retain the same syntax and source-port names;
* every occurrence carries its compact witness;
* LawMin errors converge, and converge to zero whenever exact limiting minimality is claimed;
* every triangular decoder has uniformly vanishing inner tails and convergent fixed inner columns.

## Theorem 2 — one actual direct-limit execution

There is a subsequence \(m_j\), one actual limiting initial packet \(s_\infty\), and compatible actual executions

$$
\mathcal E_\infty^k
\quad\text{of }P_k
$$

such that

$$
\mathcal E_\infty^{k+1}|_{P_k}
=
\mathcal E_\infty^k
\tag{18}
$$

and

$$
\operatorname{Tr}_{P_k}
  (\mathcal E_{m_j}|_{P_k})
\longrightarrow
\operatorname{Tr}_{P_k}(\mathcal E_\infty^k)
\tag{19}
$$

in total variation at every source port.

Consequently the union

$$
\mathcal E_\infty=\bigcup_k\mathcal E_\infty^k
$$

is one actual execution of the countable direct-limit diagram.

When there is one initial port, every finite trace starts from the same actual behavioral controller \(s_\infty\).

## Proof

Tight fusion first reconstructs the initial and exogenous stopping laws in total variation.

The union of the diagrams has countably many named edge occurrences. By Theorem 1, occurrence \(e\) has a compact witness space \(W_e\). The countable product

$$
\prod_e W_e
$$

is compact metrizable. Equivalently, repeated extraction followed by the usual diagonal subsequence makes every persistent witness converge; finite tags become eventually constant automatically.

Fix \(k\). Induct over a topological ordering of \(P_k\). At an edge \(e\):

* its input ports already converge;
* its recorded witness converges;
* the closed domain relation keeps the limiting input and witness legal;
* the continuous compiler gives convergence of the actual output;
* the closed legal and ancestry relations preserve operation semantics and source provenance.

This proves (19). Shared ports in \(P_k\) and \(P_{k+1}\) are limits of the same restricted execution sequence, proving (18). Total-variation continuity then gives convergence of terminal laws, prescribed payoffs, complete pure-time obstacles, and unrestricted behavioral caps. ∎

This is a normalization-strengthening of the coherent-diagonal theorem in the attached document: all trace-visible rank and decoder syntax has first been reduced to one closed-compiler form. The original common-execution and one-controller conclusions are retained. 

# 5. Pointwise rank after reconstruction

A pointwise ranked producer at an actual node \(N\) consists of

$$
\rho(N)\in\mathbb N,
$$

a terminal consumer

$$
\mathsf{consume}_N:
\mathsf{Terminal}(N)\to\mathsf{Outcome}(N),
\tag{20}
$$

and a dispatch

$$
\begin{aligned}
\mathsf{dispatch}(N)\in
&\ \mathsf{Terminal}(N)\\
&\sqcup
\sum_{N'}
[\rho(N')<\rho(N)]
\times
\mathsf{Exec}(N,N')
\times
(\mathsf{Outcome}(N')\to\mathsf{Outcome}(N)).
\end{aligned}
\tag{21}
$$

Natural-number induction gives an outcome after at most \(\rho(N)\) nonterminal steps. This rank may be discontinuous because it is run once, after Theorem 2 has produced one actual node. It cannot appear as a selected child inside the compact trace unless it is separately normalized by \(\mathsf{TraceRank}_K\).

# 6. Instantiation of the quitting-game operations

The non-elementary operations in the question fit the grammar as follows.

| Quitting-game operation             | Executable adapter                                                                     |
| ----------------------------------- | -------------------------------------------------------------------------------------- |
| Recorded selected exact cap root    | \(\mathsf{ClosedSelect}\)                                                              |
| Maximal or optimized root           | \(\mathsf{ClosedSelect}\) only on a domain with comparison transport                   |
| Moving-law minimizer                | \(\mathsf{ClosedSelect}\) on one uniform tight carrier, with recorded convergent error |
| Compact limit witness               | \(\mathsf{Decode}\)                                                                    |
| Source-faithful regeneration        | finite certified macro or \(\mathsf{Decode}\) with closed ancestry                     |
| Finite role/support/coalition split | \(\mathsf{FiniteCase}\) with complete closed tagged branches                           |
| Visible renewable recursion         | bounded \(\mathsf{TraceRank}_K\)                                                       |
| Post-limit renewable recursion      | pointwise \(\mathsf{RankProducer}\)                                                    |

## Selected exact roots

The exact-root inequalities are polynomial in the root \(x\) and continuous in the cap vector \(B(\mu)\). Since \(B\) is total-variation continuous,

$$
\{(\mu,x):x\text{ is an exact cap root of }\mu\}
$$

is closed. Literal prefixing satisfies

$$
d(T_x\mu,T_y\nu)
\le
d(\mu,\nu)+2\sum_i|x_i-y_i|.
\tag{22}
$$

Thus selected exact roots are admitted without assuming a continuous selector.

## Optimized roots

For a compact feasible correspondence \(F(s)\), closed graph is not enough. One also needs comparison transport:

$$
s_m\to s,\ a\in F(s)
\Longrightarrow
\exists a_m\in F(s_m),\ a_m\to a.
\tag{23}
$$

This is the inner-semicontinuity condition required to transport every limiting competitor. It implies that limits of selected maximizers remain maximizing.

## Moving-law minimizers

If all feasible laws lie in one carrier

$$
\mathcal L_T
=
\left\{
\rho:
\sum_{n>N}\rho(n)\le T(N)\ \forall N
\right\},
\qquad T(N)\downarrow0,
$$

then \(\mathcal L_T\) is compact in total variation. Closed graph, comparison transport, and

$$
\varepsilon_m\to\varepsilon
$$

give a limiting \(\varepsilon\)-minimizer. Exact minimality requires \(\varepsilon=0\).

## Finite case splits

A strict test such as “absorption \(>0\)” is not closed. A trace-safe positive branch must carry a displayed floor

$$
\operatorname{Abs}(x)\ge\delta>0
$$

with \(\delta\) fixed in that occurrence, or its zero-boundary case must be included in a closed overlapping branch. Merely recording the word “positive” is not an adapter.

## Regeneration

A semantic or law cluster point is not a regeneration. Regeneration is admitted only when:

* it is a finite actual macro;
* it is the total-variation output of a summable decoder; or
* it is a post-limit lower-rank child with an actual child compiler and backward outcome compiler.

The current Fin4 atlas correctly requires literal sources, complete laws, marked dates, quantitative floors, and the exact successor operation rather than only semantic points. 

A strict decrease of real debt is not a renewable rank. The finite support, positive-debt support, hard-face, phase, and attempt digits proposed in the atlas are rank candidates; chronology depth, approximation error, and strict real-valued debt decrease are not. 

# 7. A concrete terminal consumer using an optimized cap root

The optimized-root obstruction does not prevent pointwise or restricted-domain use. The following table gives a complete positive instance.

Take two players and

$$
r(\{1\})=(0,1),\qquad
r(\{2\})=(1,-1),\qquad
r(\{1,2\})=(0,-1),
$$

with

$$
r(\varnothing)=(0,0).
\tag{24}
$$

Let both players initially play Never:

$$
\mu^0=(\delta_\infty,\delta_\infty).
$$

Its cap vector is

$$
B(\mu^0)=(0,0).
$$

The exact cap roots are

$$
\{(q,0):0\le q\le1\}.
$$

Their one-stage absorption probability is \(q\), so the unique absorption-maximal exact root is

$$
x^\star=(1,0).
$$

Prefixing by \(x^\star\) produces

$$
\bar\nu=(\delta_0,\delta_\infty),
$$

with payoff

$$
U(\bar\nu)=(0,1).
\tag{25}
$$

For player \(1\), every complete replacement gives payoff \(0\), so

$$
B_1(\bar\nu)=0.
$$

For player \(2\), Never or any stopping date after date \(0\) gives payoff \(1\); quitting at date \(0\) gives \(-1\). Hence

$$
B_2(\bar\nu)=1.
$$

Therefore

$$
B(\bar\nu)=U(\bar\nu)=(0,1).
\tag{26}
$$

Thus \(\bar\nu\) is an exact all-behavior terminal Nash profile. The constant sequence \(\bar\nu,\bar\nu,\ldots\) gives terminal approximate Nash profiles with the single payoff \((0,1)\).

As an adapter, this is a \(\mathsf{ClosedSelect}\) on the closed singleton domain \(\{\mu^0\}\). It does not assert that maximal roots form a trace-safe correspondence on a neighborhood. The project’s terminal-to-uniform consumer then turns the exact terminal Nash payoff into a uniform-equilibrium payoff. 

# 8. A rank-stable no-go for coherent maximal-root returns

The maximal-root example can be strengthened from “the maximal-root graph is not closed” to a no-go that simultaneously records exact source, positive reach, literal suffix provenance, strategic trace error, and ranked reconstruction.

For \(z>0\), set

$$
\mu_1^z=\delta_\infty,
\qquad
\mu_2^z=z\delta_0+(1-z)\delta_\infty.
\tag{27}
$$

Then

$$
B(\mu^z)=(z,0).
$$

The unique absorption-maximal exact root is

$$
x^z=(0,0).
$$

Let

$$
y^z=T_{x^z}\mu^z.
$$

This inserts one all-Continue date. Consequently,

$$
\operatorname{Reach}_1(y^z)=1
\tag{28}
$$

and the literal depth-one suffix is exactly the original source:

$$
\operatorname{Suf}_1(y^z)=\mu^z.
\tag{29}
$$

As \(z\downarrow0\),

$$
\mu^z\to\mu^0,
\qquad
y^z\to y^\infty,
$$

where \(y^\infty\) is the all-Never profile.

Now consider an exact cap root at \(\mu^0\). It has the form

$$
x=(q,0).
$$

Its absorption probability is \(q\). Hence an exact root that is \(\varepsilon\)-maximal for absorption satisfies

$$
q\ge1-\varepsilon.
\tag{30}
$$

Let

$$
y_q=T_x\mu^0.
$$

Its depth-one reach is

$$
\operatorname{Reach}_1(y_q)=1-q\le\varepsilon.
\tag{31}
$$

Moreover,

$$
U_2(y_q)=B_2(y_q)=q.
\tag{32}
$$

At the limiting pre-root trace \(y^\infty\),

$$
U_2(y^\infty)=B_2(y^\infty)=0.
$$

Define the strategic trace distance

$$
d_{\mathrm{str}}(y,y')
=
\max_i
\left\{
|U_i(y)-U_i(y')|,
|B_i(y)-B_i(y')|
\right\}.
$$

Then

$$
d_{\mathrm{str}}(y_q,y^\infty)
\ge q
\ge1-\varepsilon.
\tag{33}
$$

## The coherent maximal-root-return construction

Fix \(\alpha>0\). An
\((\varepsilon,\eta,\alpha)\)-coherent maximal-root return at the limiting source is a pair \((x,y)\) such that:

1. \(x\) is an exact cap root of the exact source \(\mu^0\);
2. \(x\) is \(\varepsilon\)-maximal for absorption;
3. \(y=T_x\mu^0\);
4. \(\operatorname{Reach}_1(y)\ge\alpha\);
5. \(\operatorname{Suf}_1(y)=\mu^0\);
6. \(d_{\mathrm{str}}(y,y^\infty)\le\eta\).

Every prelimit source \(\mu^z\), \(z>0\), has an exact instance with

$$
\varepsilon=\eta=0,\qquad \alpha=1.
$$

At the limit, however:

* condition 4 is impossible whenever

  $$
  \varepsilon<\alpha
  \tag{34}
  $$

  by (31);
* even after dropping the reach condition, condition 6 is impossible whenever

  $$
  \varepsilon+\eta<1
  \tag{35}
  $$

  by (33).

This gives the following exact impossibility theorem.

## Theorem 3 — no coherent maximal-root-return adapter

For any fixed \(\alpha>0\), there is no universal adapter for coherent absorption-maximal exact-root returns that has any of the following forms:

1. a compact recorded witness, closed legal relation, and continuous actual compiler;
2. a summable finite-macro decoder with vanishing maximality and trace errors;
3. a bounded trace-visible ranked adapter;
4. a pointwise natural-valued ranked producer whose terminal consumers and backward compilers claim to produce an
   \((\varepsilon,\eta,\alpha)\)-coherent return with
   \(\varepsilon<\alpha\) or \(\varepsilon+\eta<1\).

### Proof

The first alternative would preserve the legal relation along

$$
(\mu^z,x^z,y^z)\to(\mu^0,(0,0),y^\infty),
$$

but no legal limiting output satisfies (34)–(35).

A summable decoder has one actual limiting output. Closed exact-source and ancestry relations would force that output to satisfy the same-source prefix and suffix requirements. Vanishing decoder errors eventually satisfy (34) and (35), again impossible.

A bounded trace-visible rank normalizes to a compact executable adapter by Theorem 1.

For a pointwise rank, let the outcome type be the type of coherent returns just defined. If terminal consumers and backward compilers existed, natural-number induction would produce an inhabitant of that outcome type. Equations (31) and (33) prove that the type is empty. ∎

This obstruction uses:

* finite-support actual sources;
* total-variation convergence;
* exact same-source caps and roots;
* a displayed reach floor;
* literal suffix-back provenance; and
* unrestricted behavioral caps.

It does not exclude a rank that **abandons the return objective** and terminates through another valid game-theoretic consumer. In this particular table, the sure-absorption maximal root is itself the exact terminal Nash profile constructed in Section 7. Such a terminal branch is a valid alternative producer, but it is not a reconstruction of the failed coherent-return edge.

The simpler nonclosed maximal-root graph and its fixed payoff-and-cap discrepancy are already recorded in the attached correction. 

# 9. Exact implication for the Fin4 construction

The grammar now completely classifies the non-elementary proof obligations, but it does not manufacture their certificates.

For the current source-preserving Fin4 construction:

* literal marked-row suffixes with retained reach floors are elementary;
* complete owner repairs and pure endpoint replacements are elementary;
* recorded exact cap roots are closed selected edges;
* finite player, coalition, endpoint, and role stabilization is a finite recorded case split;
* a moving minimum-law choice is trace-safe only after proving one common tail envelope and comparison transport;
* a source regeneration obtained through compactness is executable only after a summable total-variation decoder and closed ancestry theorem;
* a maximal-root regeneration cannot be admitted universally;
* strict semantic-debt descent is not a renewable rank;
* support, positive-debt-support, hard-face, phase, and open-attempt descent may form a pointwise rank only when every child construction, terminal consumer, and backward compiler is supplied.

The atlas’s own source-completeness requirement matches this conclusion: it retains actual behavioral sources, stopping laws, marked dates, floors, and exact successor operations, rather than treating a law or semantic cluster point as a recursive node. 

Thus the maximal correct conclusion is:

$$
\boxed{
\begin{array}{l}
\text{Every construction admitted by the grammar has one coherent actual}\\
\text{direct-limit realization, and with one initial port one controller;}\\[1mm]
\text{the optimized-root table above gives an exact terminal Nash payoff;}\\[1mm]
\text{but an exact coherent maximal-root-return edge has no universal}\\
\text{closed, decoded, trace-ranked, or outcome-preserving ranked adapter.}
\end{array}}
$$

What remains for the general Fin4 producer is no longer an architectural ambiguity. Each surviving regeneration or recurrent branch must prove one of the concrete certificates above; a semantic limit, an optimized root label, or a strict real debt decrease alone cannot enter the executable trace.
