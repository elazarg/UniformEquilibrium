# Proof-relevant executable grammar

## Status

This is a sufficient ordinary-mathematics schema. It is not a producer from
arbitrary quitting-game data, and it is not asserted to be the largest
possible executable grammar.

Fix a finite nonempty player set \(I\) and a bounded quitting reward table
\(r\), with the standard all-Never payoff

$$
r_i(\varnothing)=0
\quad(i\in I).
$$

Put

$$
R=\max\left\{
\max_{i,\varnothing\ne S}|r_i(S)|,\,
0
\right\}.
$$

The elementary stopping-law reconstruction and tight-fusion results are
developed in EXECUTABLE_COMPACT_STATE.md. The present note classifies
additional proof-relevant adapters.

The correction forces a two-sorted grammar.

A **trace adapter** is allowed inside the compact executable diagram and must commute with the stopping-law limit. A **control adapter** may use well-founded rank to prove an outcome from one already reconstructed actual node, but it is not automatically a trace edge. A rank transition can be promoted to a trace adapter only after its selected-child relation also receives a closed-limit or executable-decoder certificate.

This distinction is necessary. The elementary tight-fusion theorem applies
only to one common restriction-compatible sequence of executions and leaves
every non-elementary edge to a separate adapter theorem. With one initial
port, its limit is one controller.

# 1. Ambient source category

Let

$$
K=\mathbb N\sqcup\{\infty\},
\qquad
\mathsf S:=\Delta(K)^I,
$$

with

$$
d(\mu,\nu):=\sum_{i\in I}\|\mu_i-\nu_i\|_1.
\tag{1}
$$

Finite packets of source ports are finite powers of \(\mathsf S\). All compact auxiliary parameters are carried in compact metric spaces.

The elementary theorem supplies exact semantics and a fixed-program modulus for:

$$
\mathsf{Elem}
=
\{\text{finite prefix/concatenation},
\text{ complete replacement},
\text{ positive-reach fixed-depth suffix}\}.
$$

We now add two syntactic classes:

$$
\mathsf{TraceEdge}
\qquad\text{and}\qquad
\mathsf{RankProducer}.
$$

Only `TraceEdge` constructors may occur internally in the diagrams covered by the coherent-diagonal theorem.

# 2. The finite proof-relevant grammar

The trace grammar is

$$
\begin{aligned}
E::={}&
\mathsf{Elem}
\mid \mathsf{ClosedSelect}
\mid \mathsf{Decode}
\mid \mathsf{FiniteCase}\\
&\mid E;E
\mid E\times E .
\end{aligned}
\tag{2}
$$

The named non-elementary operations are instances as follows:

$$
\begin{array}{c|c}
\text{operation} & \text{required constructor}\\
\hline
\text{recorded selected exact root}
  & \mathsf{ClosedSelect}\\
\text{robust maximal/optimal root}
  & \mathsf{ClosedSelect}\text{ with comparison transport}\\
\text{moving-law minimizer}
  & \mathsf{ClosedSelect}\text{ on a tight carrier, with comparison transport and a recorded error}\\
\text{compact limit witness}
  & \mathsf{Decode}\\
\text{source-faithful regeneration}
  & \mathsf{ClosedSelect}\text{ or }\mathsf{Decode}\\
\text{trace-visible ranked transition}
  & \mathsf{TraceRank},\text{ defined from the trace grammar}.
\end{array}
\tag{3}
$$

There is no opaque `Regenerate`, `TakeLimit`, `ChooseMaximum`, or `DecreaseRank` constructor.

## 2.1 Closed selected adapters

A \(\mathsf{ClosedSelect}\) certificate from \(p\) input ports to \(q\) output ports consists of:

1. a compact witness space \(W\);
2. a closed relation

   $$
   R\subseteq \mathsf S^p\times W;
   \tag{4}
   $$
3. an actual behavioral compiler

   $$
   G:R\longrightarrow \mathsf S^q;
   \tag{5}
   $$
4. a typed legal-edge relation \(\mathsf{Legal}_a\) and a theorem

   $$
   (s,w)\in R
   \Longrightarrow
   \mathsf{Legal}_a(s,w,G(s,w));
   \tag{5a}
   $$
5. a fixed-program modulus

   $$
   d(G(s,w),G(s',w'))
   \le
   \omega_G\!\left(d(s,s')+d_W(w,w')\right);
   \tag{6}
   $$
6. when source provenance matters, a closed ancestry relation

   $$
   \mathsf{Anc}
   \subseteq
   \mathsf S^p\times W\times\mathsf S^q
   \tag{7}
   $$

   such that

   $$
   \mathsf{Anc}(s,w,G(s,w))
   \tag{8}
   $$

   and membership in \(\mathsf{Anc}\) implies the intended source-faithful relation.

Membership of the output in \(\mathsf S^q\) proves only that it is an actual
standalone stopping-law packet. The legal-edge theorem (5a) is what proves
that it is the named operation applied to the named input. The ancestry
condition cannot be replaced by a textual source label. If the intended
ancestry relation is not closed, the adapter must use a stronger closed
subrelation or a decoder carrying an explicit recovery theorem.

### Lemma 1 — closed selected-edge limit

Suppose

$$
s_m\to s,\qquad w_m\to w,
\qquad R(s_m,w_m).
$$

Then

$$
R(s,w),
\qquad
G(s_m,w_m)\to G(s,w),
\tag{9}
$$

and

$$
\mathsf{Anc}(s,w,G(s,w))
\tag{10}
$$

whenever the ancestry certificate is present.

This is immediate from closedness, the modulus, and closedness of \(\mathsf{Anc}\).

## 2.2 Finite recorded case splits

A \(\mathsf{FiniteCase}\) adapter has a finite branch set \(B\), with a closed-selected or decoded adapter \(E_b\) on each branch. The branch tag \(b\) is recorded.

For each \(b\), its full branch relation

$$
P_b\subseteq
\text{input}\times\text{branch witnesses}
\tag{10a}
$$

must be closed in the declared ambient carrier, and the relations \(P_b\)
must cover the adapter domain. Branches may overlap on boundaries. Every
\(E_b\) is a trace-safe grammar expression of smaller syntax height on
\(P_b\), with all of its own witnesses and legal-edge certificates.

For a fixed program, \(b\) is fixed before its continuity estimate. Along an outer sequence of executions, a subsequence makes \(b\) constant. The branch predicate itself must be closed. An open test such as \(g(s)>0\) does not become legal merely because its Boolean result is recorded; one must supply a closed branch relation or route the boundary through another certified branch.

# 3. The surviving selected-root and optimization adapters

## 3.1 Recorded exact cap roots

Let

$$
\mathsf{Root}(\mu,x)
\tag{11}
$$

mean the following. Against the opponents' product root \(x_{-i}\), let
\(Q_i(x_{-i})\) be player \(i\)'s expected payoff from Quit, and let
\(C_i(x_{-i};B_i(\mu))\) be its expected payoff from Continue, using
\(B_i(\mu)\) when every opponent Continues. Then

$$
x_i\bigl(Q_i-C_i\bigr)\ge0,
\qquad
(1-x_i)\bigl(C_i-Q_i\bigr)\ge0
\quad(i\in I).
\tag{11a}
$$

Because \(B\) is continuous in total variation and the root inequalities are polynomial in \(x\) and continuous in \(B(\mu)\),

$$
\{(\mu,x):\mathsf{Root}(\mu,x)\}
\tag{12}
$$

is closed.

The compiler is literal prefixing:

$$
G(\mu,x)=T_x\mu.
\tag{13}
$$

Its estimate is

$$
d(T_x\mu,T_y\nu)
\le
d(\mu,\nu)+2\sum_{i\in I}|x_i-y_i|.
\tag{14}
$$

Hence a recorded selected exact root is a \(\mathsf{ClosedSelect}\) edge. No selector continuity is asserted or needed.

## 3.2 Robust compact argmin and argmax

Let \(A\) be compact, and let \(F(s)\subseteq A\) be a nonempty feasible correspondence. Assume:

$$
\operatorname{graph}(F)
=
\{(s,a):a\in F(s)\}
\quad\text{is closed},
\tag{15}
$$

and the comparison-transport property

$$
s_m\to s,\ a\in F(s)
\Longrightarrow
\exists a_m\in F(s_m),\ a_m\to a.
\tag{16}
$$

Let \(f\) be continuous.

If

$$
a_m^\star\in\arg\max_{a\in F(s_m)}f(s_m,a),
\qquad
a_m^\star\to a^\star,
\tag{17}
$$

then

$$
a^\star\in\arg\max_{a\in F(s)}f(s,a).
\tag{18}
$$

Indeed, closedness gives feasibility. For any \(a\in F(s)\), choose \(a_m\) by (16), use

$$
f(s_m,a_m^\star)\ge f(s_m,a_m),
$$

and pass to the limit.

Thus maximal roots are trace-safe on any domain on which their exact-root correspondence satisfies comparison transport. Closed graph alone is insufficient.

## 3.3 Tight moving-law minimizers with explicit error limits

For a tail envelope \(T(N)\downarrow0\), let

$$
\mathcal L_T
=
\left\{
\rho\in\Delta(K):
\sum_{n>N}\rho(n)\le T(N)
\text{ for every }N
\right\}.
\tag{19}
$$

This is compact in total variation.

Let \(F(s)\subseteq\mathcal L_T\) be nonempty, with closed graph and comparison transport. Let

$$
\Phi:\{(s,\rho):\rho\in F(s)\}\to\mathbb R
$$

be continuous.

An execution records both a law \(\rho_m\) and an error \(\varepsilon_m\ge0\), satisfying

$$
\rho_m\in F(s_m),
\qquad
\Phi(s_m,\rho_m)
\le
\inf_{\eta\in F(s_m)}\Phi(s_m,\eta)+\varepsilon_m.
\tag{20}
$$

For use as a grammar witness, the error is either prescribed convergent
exogenous data or is stored in one declared compact interval
\([0,E]\). It is not an unbounded hidden witness coordinate.

### Lemma 2 — closed approximate-minimizer relation

Suppose

$$
s_m\to s,
\qquad
\rho_m\to\rho,
\qquad
\varepsilon_m\to\varepsilon.
\tag{21}
$$

Then

$$
\rho\in F(s)
\tag{22}
$$

and

$$
\Phi(s,\rho)
\le
\inf_{\eta\in F(s)}\Phi(s,\eta)+\varepsilon.
\tag{23}
$$

For \(\eta\in F(s)\), comparison transport supplies \(\eta_m\in F(s_m)\) with \(\eta_m\to\eta\). Pass to the limit in

$$
\Phi(s_m,\rho_m)
\le
\Phi(s_m,\eta_m)+\varepsilon_m.
$$

In particular, an exact limiting minimizer requires

$$
\varepsilon_m\longrightarrow0.
\tag{24}
$$

Without a specified error limit, one obtains at most a bound with \(\limsup_m\varepsilon_m\).

# 4. Source-faithful summable decoding

This is the correct adapter for compact limit witnesses and asymptotic regeneration.

Let \(X\subseteq\mathsf S^p\) be a closed actual input domain, let \(Z\) be compact, and let

$$
W\subseteq \mathsf S^p\times Z
\tag{25}
$$

be closed and contained in \(X\times Z\). Ambient closedness ensures that an
outer limiting input remains in the decoder domain.

For every \(n\), let

$$
M_n:W\to\mathsf S^q
\tag{26}
$$

be an actual finite trace program already certified by lower grammar clauses. Assume:

$$
d(M_{n+1}(\xi),M_n(\xi))\le c_n
\quad(\xi\in W),
\tag{27}
$$

where

$$
\forall n,\quad c_n\ge0,
\qquad
\sum_{n=0}^{\infty}c_n<\infty.
\tag{28}
$$

Write

$$
C_N:=\sum_{n\ge N}c_n.
\tag{29}
$$

For each fixed \(N\), \(M_N\) has its own fixed-program modulus

$$
d(M_N(\xi),M_N(\xi'))
\le
\omega_N(d_W(\xi,\xi')),
\tag{30}
$$

computed using only the finitely many suffix depths and reach floors appearing in \(M_N\).

Finally, the adapter records a closed ancestry relation

$$
\mathsf{Anc}
\subseteq
X\times Z\times\mathsf S^q
\tag{31}
$$

such that

$$
\mathsf{Anc}(s,z,M_n(s,z))
\quad\text{for every }n.
\tag{32}
$$

The certificate includes the semantic theorem

$$
\mathsf{Anc}(s,z,y)
\Longrightarrow
y\text{ is a legal source-faithful successor of }s.
\tag{33}
$$

## Theorem 3 — executable source-faithful decoder

The limit

$$
D(s,z):=\lim_{n\to\infty}M_n(s,z)
\tag{34}
$$

exists in total variation and is an actual stopping-law packet. Moreover,

$$
d(D(s,z),M_N(s,z))\le C_N,
\tag{35}
$$

and

$$
d(D(\xi),D(\xi'))
\le
2C_N+\omega_N(d_W(\xi,\xi')).
\tag{36}
$$

The output retains provenance:

$$
\mathsf{Anc}(s,z,D(s,z)).
\tag{37}
$$

### Proof

Equation (27) makes \(M_n(\xi)\) Cauchy. The space of actual probability laws is closed in \(\ell^1(K)\), so its limit is actual. Summing (27) gives (35).

For (36), insert \(M_N(\xi)\) and \(M_N(\xi')\) between the two decoded outputs.

For ancestry, fix \((s,z)\). By (32),

$$
(s,z,M_n(s,z))\in\mathsf{Anc}
$$

for every \(n\). The triples converge to \((s,z,D(s,z))\), so closedness gives (37). ∎

## Explicit downstream error and reach budget

Suppose a downstream fixed program \(H\) has stopping-law Lipschitz constant \(L_H\). Replacing \(D\) by its executable truncation \(M_N\) incurs at most

$$
L_H C_N
\tag{38}
$$

in stopping-law error and at most the corresponding strategic bound

$$
R\,L_H C_N
\tag{39}
$$

per payoff or cap coordinate, up to the finite player-count factor already present in the elementary estimates.

If a downstream suffix has required reach floor \(\alpha>0\), choose \(N\) and the outer input tolerance so that the propagated reach error is below \(\alpha/2\). Then both the decoded execution and its finite approximation remain in the legal suffix domain.

The order of quantifiers is:

1. fix the finite downstream program;
2. choose \(N\) so that \(C_N\) is small enough;
3. use the modulus of that one finite \(M_N\).

No modulus over all decoder depths is required.

A triangular outer sequence may use \(c_{m,n}\) provided

$$
\sup_m\sum_{n\ge N}c_{m,n}\longrightarrow0.
\tag{40}
$$

It must additionally prove outer convergence for every fixed inner column:
for each fixed \(N\), the certified macro \(M_{m,N}\) and all its displayed
witnesses converge to the corresponding limiting \(M_N\). Uniform tail
summability alone does not identify the outer limit.

# 5. Rank: the corrected pointwise theorem

A rank adapter must first be formulated as a control theorem, not as a continuity theorem.

Let \(\mathcal N\) be a set of actual source-attached nodes. For each \(N\in\mathcal N\), let:

$$
\rho(N)\in\mathbb N,
\tag{41}
$$

$$
\mathsf{Terminal}(N)
\quad\text{and}\quad
\mathsf{Outcome}(N)
\tag{42}
$$

be the terminal-certificate and outcome types.

The missing datum in the earlier formulation is the terminal consumer

$$
\mathsf{consume}_N:
\mathsf{Terminal}(N)\longrightarrow\mathsf{Outcome}(N).
\tag{43}
$$

For every \(N\), the renewable dispatch supplies either a terminal certificate or an actual lower-rank child:

$$
\mathsf{dispatch}(N)
\in
\mathsf{Terminal}(N)
\;\sqcup\;
\sum_{N'\in\mathcal N}
\left[
\rho(N')<\rho(N)
\right]
\times
\mathsf{Exec}(N,N')
\times
\left(
\mathsf{Outcome}(N')\to\mathsf{Outcome}(N)
\right).
\tag{44}
$$

Here \(\mathsf{Exec}(N,N')\) certifies an actual legal behavioral construction of \(N'\) from \(N\).

## Theorem 4 — pointwise ranked producer

Every node \(N\) has an outcome in \(\mathsf{Outcome}(N)\). Any recursive execution uses at most \(\rho(N)\) nonterminal transitions.

### Proof

Induct on \(\rho(N)\).

In the left branch of (44), apply \(\mathsf{consume}_N\).

In the right branch, the child has smaller rank. Apply the induction hypothesis at \(N'\), and then the recorded backward map

$$
\mathsf{Outcome}(N')\to\mathsf{Outcome}(N).
$$

Strict descent in \(\mathbb N\) bounds the path length. ∎

## Corollary 5 — renewable exit

There is no nonempty nonterminal component \(C\subseteq\mathcal N\) such that every \(N\in C\) has a legal selected successor in \(C\).

Choose a node in \(C\) of minimum rank. Its successor in \(C\) has strictly smaller rank, a contradiction.

This proves a renewable well-founded exit for every subsystem carrying the data (41)–(44).

# 6. Rank decrease does not imply a coherent diagonal

The failure occurs already at rank one.

Take rank-tagged one-player nodes

$$
\mathcal N=
\{P_\mu:\mu\in\mathsf S\}
\sqcup
\{C_\nu:\nu\in\mathsf S\},
\qquad
\rho(P_\mu)=1,
\quad
\rho(C_\nu)=0.
\tag{44a}
$$

Give every node the singleton outcome type. Every \(C_\nu\) has the singleton
terminal certificate and its unique terminal consumer, and every successor
has the unique backward map between singleton outcomes. Dispatch \(P_\mu\)
to \(C_{F(\mu)}\), where

$$
F(\mu)=
\begin{cases}
\delta_0,&\mu(0)>0,\\
\delta_\infty,&\mu(0)=0.
\end{cases}
\tag{45}
$$

The actual child certificate may be complete replacement of the sole
player's stopping law. Thus all pointwise rank data, including (43), are
present.

Set

$$
\mu_m=
\frac1m\delta_0+
\left(1-\frac1m\right)\delta_\infty.
\tag{46}
$$

Then

$$
\mu_m\longrightarrow\delta_\infty
\quad\text{in total variation},
\tag{47}
$$

but

$$
F(\mu_m)=\delta_0
\quad\text{for every }m,
\qquad
F(\delta_\infty)=\delta_\infty.
\tag{48}
$$

Hence

$$
\|F(\mu_m)-F(\delta_\infty)\|_1=2.
\tag{49}
$$

So a strict natural-valued rank, an actual child compiler, and terminal consumers do not imply closedness or continuity of the child trace.

This gives the exact repair:

> A pointwise `RankProducer` may be invoked only after one actual limiting node has already been reconstructed, unless its child relation is separately certified as trace-safe.

# 7. Trace-visible ranked adapters

Rank may occur internally in a coherent diagram under a stronger constructor.

A \(\mathsf{TraceRank}(K)\) certificate has ranks in

$$
\{0,\ldots,K\}.
$$

For each rank \(k\):

1. the rank-\(k\) node relation is closed;
2. terminal and successor branch tags range over a finite set and are recorded;
3. for every terminal tag, the complete tagged terminal relation is closed;
4. every successor branch chooses some \(\ell<k\);
5. for every successor tag and child rank, the complete relation containing
   the parent, tag, compact branch witness, and selected child is closed;
6. the selected child inside that closed branch relation is produced by a
   \(\mathsf{TraceEdge}\), not merely by an arbitrary actual map;
7. if terminal outputs or backward compilers themselves appear as trace
   ports, they too are \(\mathsf{TraceEdge}\) constructions and belong to the
   corresponding closed tagged relation.

Thus a branch tag is not merely recorded; its legality at the parent is part
of the closed witnessed relation. Open dispatch tests are excluded.

The initial rank is fixed in the program label. More generally, a uniformly bounded recorded rank may vary along executions, because a subsequence makes it constant. An unbounded rank sequence has no generic trace-diagonal theorem.

## Theorem 6 — finite-rank trace closure

A \(\mathsf{TraceRank}(K)\) construction is trace-safe.

### Proof

Induct on \(K\).

At rank zero, only closed terminal branches are possible.

At rank \(k>0\), pass to a subsequence on which the finite branch tag and
child rank \(\ell<k\) are constant. Compactness supplies a limit of the
recorded branch witnesses. The selected child's certified trace edge first
produces a convergent actual child from the convergent parent and branch
witnesses. Closedness of the complete tagged relation, now including that
child limit, preserves legality of the chosen branch. Apply the induction
hypothesis at rank \(\ell\).

Since every path has length at most \(K\), only finitely many trace-safe compositions occur. ∎

Thus there are two valid uses of rank:

$$
\boxed{
\begin{array}{ll}
\text{post-limit rank discharge:}
&\text{pointwise data (41)--(44) suffice};\\[1mm]
\text{rank child visible in the diagonal trace:}
&\mathsf{TraceRank}(K)\text{ is required}.
\end{array}}
\tag{50}
$$

# 8. Corrected coherent-diagonal theorem

Let

$$
P_1\preceq P_2\preceq\cdots
\tag{51}
$$

be increasing finite rooted diagrams built from:

$$
\mathsf{Elem},
\quad
\mathsf{ClosedSelect},
\quad
\mathsf{Decode},
\quad
\mathsf{FiniteCase},
\quad
\mathsf{TraceRank}(K).
\tag{52}
$$

A pointwise `RankProducer` may occur only as a terminal obligation to be discharged after reconstruction.

## Common-execution hypothesis

There must be one sequence

$$
\mathcal E_m
\tag{53}
$$

where \(\mathcal E_m\) is an actual execution of \(P_m\). For every fixed \(k\) and \(m\ge k\),

$$
\mathcal E_m|_{P_k}
\tag{54}
$$

is the \(m\)-th execution of the same named diagram \(P_k\).

This does not require \(\mathcal E_m|_{P_k}\) to equal \(\mathcal E_k\). It does prohibit choosing a completely unrelated source family separately for each requested depth.

Assume:

1. every initial and exogenous law input has finite-coordinate and Never-coordinate limits and eventual finite-tail tightness;
2. every persistent elementary suffix has its recorded positive reach floor;
3. the discrete syntax and source-port names agree under restriction;
4. all selected roots and compact witnesses are recorded;
5. every tight law-selection occurrence uses one fixed tail envelope;
6. for every LawMin occurrence,

   $$
   \varepsilon_{m,e}\to\varepsilon_e;
   \tag{55}
   $$

   exact limiting minimization requires \(\varepsilon_e=0\);
7. every decoder has a common summable or uniformly summable triangular seam budget, fixed-depth reach budgets, and a closed ancestry relation;
8. every visible rank construction is a bounded \(\mathsf{TraceRank}\).

## Theorem 7 — coherent executable diagonal for the certified grammar

There is one subsequence \(m_j\), one actual limiting initial packet \(s_\infty\), and for every \(k\) one actual execution \(\mathcal E_\infty^k\) of \(P_k\), such that

$$
\mathcal E_\infty^{k+1}|_{P_k}
=
\mathcal E_\infty^k,
\tag{56}
$$

and

$$
\operatorname{Tr}_{P_k}
\bigl(
\mathcal E_{m_j}|_{P_k}
\bigr)
\longrightarrow
\operatorname{Tr}_{P_k}
\bigl(
\mathcal E_\infty^k
\bigr)
\tag{57}
$$

in total variation at every source port and therefore in terminal laws, payoffs, complete unilateral obstacles, and unrestricted behavioral caps.

If there is one initial port, every \(\mathcal E_\infty^k\) has the same initial behavioral profile \(s_\infty\). It is one controller, not one controller per \(k\).

### Proof

The elementary tight-fusion theorem reconstructs all initial and exogenous law inputs in total variation.

The union of the finite diagrams has countably many named edge occurrences. Their recorded witnesses lie in:

* finite sets for branch tags;
* \([0,1]^I\) for selected roots;
* the specified compact parameter spaces for closed selectors;
* compact tight-law carriers for LawMin;
* compact witness spaces for decoders;
* compact branch-witness spaces for trace-visible rank;
* finite rank sets for trace-visible rank.

Use successive subsequence extraction and then the standard diagonal subsequence so that every persistent witness converges and every finite tag stabilizes. The assumed LawMin errors retain their specified limits.

Fix \(k\). Induct over the finite topological order of \(P_k\).

* Elementary edges commute with the limit by tight fusion.
* Closed-selected edges commute by Lemma 1.
* Exact selected roots are a closed-selected instance.
* Robust optimizers remain optimal by comparison transport.
* LawMin edges remain \(\varepsilon_e\)-minimal by Lemma 2.
* Decoders commute with the outer limit by (36), produce actual laws, and preserve ancestry by (37).
* Finite cases remain in their stabilized closed branch.
* Trace-visible rank constructions commute by Theorem 6.

Thus every limiting port is actual and every limiting edge remains legal.

Restriction compatibility of the syntax and recorded witnesses yields (56). Since the root law was reconstructed once before the edge induction, all finite diagrams share the same root controller. Continuity of terminal laws and unrestricted caps follows from their total-variation estimates. ∎

# 9. Terminal and ranked consumers

## 9.1 Terminal approximate Nash profiles with one payoff

Suppose the common root sequence satisfies

$$
U(s_m)\to v
\tag{58}
$$

and

$$
B_i(s_m)-U_i(s_m)\le\eta_m,
\qquad
\eta_m\downarrow0.
\tag{59}
$$

Theorem 7 gives one actual root \(s_\infty\). Total-variation continuity gives

$$
U(s_\infty)=v
\tag{60}
$$

and

$$
B_i(s_\infty)-U_i(s_\infty)\le0.
$$

The reverse inequality is automatic because the prescribed strategy is one of the unilateral replacements. Therefore

$$
B_i(s_\infty)=U_i(s_\infty)
\quad(i\in I).
\tag{61}
$$

So \(s_\infty\) is an exact all-behavior terminal Nash profile. In particular, the constant sequence \(s_\infty,s_\infty,\ldots\) gives terminal approximate Nash profiles with the one limiting payoff \(v\).

After applying the canonical stopping-law-to-behavior compiler, the checked
terminal-to-uniform selection theorem
quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact gives \(v\)
as a uniform-equilibrium payoff. It is in
UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean.
This is a consumer of the supplied coherent
vanishing-terminal-debt family; it does not produce that family from an
arbitrary reward table.

## 9.2 Post-limit renewable exit

Let \(N_\infty\) be any actual limiting node carrying a pointwise `RankProducer`. Theorem 4 applies directly to \(N_\infty\). It yields a finite actual legal chain ending at a consumed terminal state, with at most \(\rho(N_\infty)\) nonterminal transitions.

No continuity of the selected children is required because the rank recursion
is now run once, from the one already reconstructed actual node. The conclusion
concerns the dispatch-selected chain, not every otherwise legal transition.

# 10. Precisely scoped maximal-root obstruction

The earlier two-player example proves a no-go only for the exact same-source maximal-root trace relation.

Take

$$
r(\{1\})=(0,1),
\qquad
r(\{2\})=(1,-1),
\qquad
r(\{1,2\})=(0,-1),
\qquad
r(\varnothing)=(0,0).
\tag{62}
$$

Let

$$
\mu_1^z=\delta_\infty,
\qquad
\mu_2^z=z\delta_0+(1-z)\delta_\infty.
\tag{63}
$$

Then

$$
\mu^z\to\mu^0
\quad\text{in total variation},
\tag{64}
$$

and the cap vector is

$$
B(\mu^z)=(z,0).
\tag{65}
$$

The exact cap-root sets are

$$
F(\mu^z)=
\begin{cases}
\{(0,0)\},&z>0,\\[1mm]
[0,1]\times\{0\},&z=0.
\end{cases}
\tag{66}
$$

For maximal one-stage absorption,

$$
a(x)=1-(1-x_1)(1-x_2),
$$

the unique selected maximal roots are

$$
x^z=(0,0)\quad(z>0),
\qquad
x^0=(1,0).
\tag{67}
$$

The exact same-source traces for \(z>0\) converge to the all-Never output \(\nu^\infty\), where

$$
U_2(\nu^\infty)=B_2(\nu^\infty)=0.
\tag{68}
$$

Every exact maximal-root successor of the limit source uses \((1,0)\), producing \(\bar\nu\) with

$$
U_2(\bar\nu)=B_2(\bar\nu)=1.
\tag{69}
$$

Hence the exact maximal-root trace relation is not closed, and every exact
same-source maximal repair has payoff-and-cap trace discrepancy \(1\).

There is a slightly stronger same-source approximate statement. At \(\mu^0\), an exact root \(x=(x_1,0)\) that is \(\varepsilon\)-maximal for absorption must satisfy

$$
x_1\ge1-\varepsilon.
\tag{70}
$$

Its output satisfies

$$
U_2=B_2=x_1\ge1-\varepsilon.
\tag{71}
$$

Thus for same-source \(\varepsilon_m\)-maximal exact-root repairs with
\(\varepsilon_m\to0\), the payoff-and-cap discrepancy from the limiting
all-Never trace tends to one.

The obstruction does **not** rule out:

* approximate root equations rather than exact roots;
* restricted domains avoiding the bifurcation point;
* a discontinuous pointwise maximal selector when no trace continuity is claimed;
* reconstruction at a modified source;
* a different optimization objective;
* a construction-specific decoder that proves a different source-faithful relation.

Its exact conclusion is:

> The graph of “prefix this actual source by an exact absorption-maximal cap root of the same source” is not universally closed, and it has no universally vanishing-error same-source trace reconstruction.

# 11. Final theorem boundary

A corrected sufficient generic architecture is:

$$
\boxed{
\begin{aligned}
\text{trace phase: }&
\mathsf{Elem}
+\mathsf{ClosedSelect}
+\mathsf{Decode}
+\mathsf{FiniteCase}
+\mathsf{TraceRank};\\
\text{control phase: }&
\mathsf{RankProducer}\text{ applied after actual reconstruction}.
\end{aligned}}
\tag{72}
$$

It proves all of the following.

1. Recorded selected exact roots, robust compact optimizers, and tight
moving-law minimizers with closed graph, comparison transport, and a
convergent recorded error have closed executable limit semantics.

2. A summable decoder produces an actual continuous stopping-law output, with explicit truncation, downstream strategic, and reach budgets.

3. Source-faithful decoding is valid only with an explicit closed ancestry relation whose membership implies the intended provenance.

4. A decreasing natural rank plus terminal and backward consumers proves pointwise termination, but not child-trace continuity.

5. Rank transitions may be visible in a coherent diagonal only when their selected child relations are themselves trace-safe and the visible rank is bounded and recorded.

6. A common increasing sequence of executions admits one global witness
subsequence and a compatible family of actual executions of all finite
diagrams. With one initial port, this gives one controller.

7. Vanishing unrestricted terminal exploitability with one payoff limit
yields an exact all-behavior terminal Nash profile and hence a
uniform-equilibrium payoff.

8. Every pointwise ranked subsystem has a renewable well-founded exit along
its dispatch-selected successor relation.

9. Bare exact same-source maximal-root traces cannot be admitted universally;
the explicit two-player table gives a fixed payoff-and-cap trace
discrepancy.

The separate law-level example in VANISHING_REACH_SUFFIX_NO_GO.md shows why
positive-reach suffixing cannot be graph-closed after forgetting its reach
and exact-source witness.

What remains construction-specific is sharply isolated: each Fin4
regeneration, maximal-root restriction, compact witness, and proposed
renewable rank must instantiate one of these certificates. A regeneration
label or a strict rank inequality alone supplies none of the missing trace
semantics.
