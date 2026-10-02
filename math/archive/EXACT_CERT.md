The decisive requirement is a finite certificate that controls **all accuracies**, rather than certificates obtained separately at each accuracy. I can give such a certificate language for fixed ultimately periodic strategy formats, with a terminating compiler to rational finite-menu laws. **I have not proved that this language covers every zero-gap table, and I have not obtained a positive-gap table. Thus the construction below does not complete either requested alternative.**

The precise partial result is useful because its missing step is a coverage theorem—not an unproved assertion about unrestricted deviations or tail truncation.

## 1. A decidable all-accuracy zero certificate

Fix integers \(h\ge0\) and \(L\ge1\). Consider profiles consisting of \(h\) initial rows followed by an endlessly repeated block of \(L\) rows. Their parameters are

$$
x\in[0,1]^{4(h+L)}.
$$

Let \(p_x\) denote the resulting actual independent behavioral profile, and define

$$
F_{r,h,L}(x)=E_r(p_x).
$$

I will prove that \(F_{r,h,L}\) has an effectively constructible semialgebraic graph, **including its boundary values**. Consequently the sentence

$$
\boxed{
\Psi_{r,h,L}:\qquad
\forall \rho>0\ \exists x\in[0,1]^{4(h+L)}
\quad F_{r,h,L}(x)<\rho
}
\tag{1}
$$

is decidable by exact quantifier elimination over real closed fields. Such quantifier-elimination algorithms are available with algebraic correctness proofs; no numerical optimization is needed. ([arXiv][1])

A certificate can therefore be just the finite pair \((h,L)\), with the verifier regenerating (1) from \(r,h,L\) and deciding its truth. Alternatively, a proof-carrying certificate can include a finite first-order derivation of (1) from the axioms of real closed fields, checked syntactically.

**Acceptance proves \(\eta(r)=0\).** More specifically, it certifies the terminating rational finite-law procedure in Section 3.

This test does not require an exact periodic equilibrium: the infimum within the fixed format may be zero without being attained.

## 2. Exact unrestricted semantics of the format

For a row \(q\in[0,1]^4\), write

$$
P_q(S)=\prod_{j\in S}q_j\prod_{j\notin S}(1-q_j),
\qquad
c(q)=P_q(\varnothing),
$$

$$
a_i(q)=\sum_{\varnothing\ne S\subseteq I}P_q(S)r_i(S).
$$

For opponents alone, put

$$
P_{q,-i}(T)=
\prod_{j\in T}q_j
\prod_{\substack{j\notin T\\j\ne i}}(1-q_j),
\qquad
\lambda_i(q)=P_{q,-i}(\varnothing),
$$

$$
g_i(q)=
\sum_{\varnothing\ne T\subseteq I\setminus\{i\}}
P_{q,-i}(T)r_i(T),
$$

$$
k_i(q)=
\sum_{T\subseteq I\setminus\{i\}}
P_{q,-i}(T)r_i(T\cup\{i\}).
$$

Thus \(g_i\) is the immediate expected reward when \(i\) Continues, and \(k_i\) is the expected reward when \(i\) Quits. These are rational polynomials in \(q\).

### The periodic tail

For the repeated block \(q^0,\ldots,q^{L-1}\), define

$$
\alpha_s=\prod_{t<s}c(q^t),
\qquad C=\alpha_L,
\qquad
A_i=\sum_{s<L}\alpha_s a_i(q^s).
$$

Its prescribed payoff is exactly

$$
V_i=
\begin{cases}
A_i/(1-C),&C<1,\\[2mm]
0,&C=1.
\end{cases}
\tag{2}
$$

The second branch is essential: \(C=1\) means every row is all-Continue. The equation \(V_i=A_i+CV_i\) alone would incorrectly permit arbitrary tail payoffs.

For each player, separately define the **opponent-deleted** survival quantities

$$
\beta_{i,s}=\prod_{t<s}\lambda_i(q^t),
\qquad
\Lambda_i=\beta_{i,L},
\qquad
H_i=\sum_{s<L}\beta_{i,s}g_i(q^s),
$$

$$
K_{i,s}
=
\sum_{t<s}\beta_{i,t}g_i(q^t)
+\beta_{i,s}k_i(q^s).
$$

Quitting deterministically at date \(nL+s\), with \(0\le s<L\), gives

$$
G_i(nL+s)
=
H_i\sum_{\ell=0}^{n-1}\Lambda_i^\ell
+\Lambda_i^n K_{i,s}.
\tag{3}
$$

When \(\Lambda_i<1\), this equals

$$
\frac{H_i}{1-\Lambda_i}
+
\Lambda_i^n
\left(K_{i,s}-\frac{H_i}{1-\Lambda_i}\right).
$$

Its supremum over \(n\) is therefore the larger of the first-period value \(K_{i,s}\) and the limiting value \(H_i/(1-\Lambda_i)\). Never gives precisely that limiting value. Hence the unrestricted cap of the periodic tail is

$$
D_i=
\begin{cases}
\displaystyle
\max\left\{
\frac{H_i}{1-\Lambda_i},
K_{i,0},\ldots,K_{i,L-1}
\right\},
&\Lambda_i<1,\\[3mm]
\max\{0,r_i(\{i\})\},
&\Lambda_i=1.
\end{cases}
\tag{4}
$$

In the second branch every opponent literally plays Never. Every finite quitting date gives \(r_i(\{i\})\), whereas Never gives zero.

Equations (3)–(4) cover arbitrary unbounded stopping laws: against fixed opponents, the deviator’s payoff is the average of its deterministic-date payoffs. Randomizing over those dates cannot increase their supremum.

### Adding the prefix

Initialize \((u_i,b_i)=(V_i,D_i)\). Process the \(h\) prefix rows backwards using

$$
u_i\longleftarrow a_i(q)+c(q)u_i,
$$

$$
b_i\longleftarrow
\max\{k_i(q),\,g_i(q)+\lambda_i(q)b_i\}.
\tag{5}
$$

The second equation takes the better of Quit now and Continue followed by an unrestricted response. It remains exact when survival is zero and when a continuation supremum is not attained.

At the beginning of the prefix,

$$
F_{r,h,L}(x)=\max_i(b_i-u_i).
\tag{6}
$$

This proves the claimed semialgebraic representation. For example, the division in (2) is encoded on its positive-denominator branch by

$$
C<1,\qquad (1-C)V_i=A_i,
$$

while \(C=1\) is encoded separately by \(V_i=0\). Each maximum is expressed by inequalities against every candidate and equality to at least one candidate. All formulas are finite and use rational coefficients.

## 3. A terminating compiler to rational finite-menu laws

Suppose the verifier accepts \((h,L)\). Given rational \(\varepsilon>0\), use the following procedure.

### Select rational rows

Enumerate rational parameter vectors in the fixed cube until exact evaluation of (2)–(6) finds

$$
F_{r,h,L}(x)<\varepsilon/2.
\tag{7}
$$

This search terminates. Sentence (1) gives a real witness with error below \(\varepsilon/4\). Preserve its zero coordinates in the periodic block. On that zero-pattern stratum, all branches \(C=1\) and \(\Lambda_i=1\) remain fixed, and every other denominator remains positive locally. Thus \(F\) is continuous there. Rational points are dense in that stratum, so a rational witness satisfying (7) exists.

This argument does **not** assume continuity across the all-Continue boundary.

### Truncate finite tail mass, retaining Never

For the selected rational rows, let

$$
a_j^{\mathrm{pre}}=\prod_{t<h}(1-x_j^t),
\qquad
s_j=\prod_{t<L}(1-q_j^t).
$$

After \(K\) full periods, the mass of player \(j\)’s stopping law assigned to **finite dates at or beyond** \(h+KL\) is

$$
\tau_j(K)=
\begin{cases}
a_j^{\mathrm{pre}}s_j^K,&s_j<1,\\
0,&s_j=1.
\end{cases}
\tag{8}
$$

When \(s_j=1\), all surviving mass is already Never; it must not be counted as finite tail mass.

Search for an integer \(K\ge1\) such that

$$
4\sum_j\tau_j(K)\le\varepsilon/2.
\tag{9}
$$

This terminates because every nonzero term in (8) decays geometrically.

Set \(N=h+KL\). Keep all marginal stopping masses before \(N\), and move their remaining finite mass to Never. Explicitly,

$$
p_j^{(K)}(t)
=
x_j(t)\prod_{v<t}(1-x_j(v))
\quad(0\le t<N),
$$

$$
p_j^{(K)}(\mathrm{Never})
=
\prod_{v<N}(1-x_j(v)).
\tag{10}
$$

These are four rational probability laws on the requested finite menu, with \(N\ge1\).

### Full-error bound

Couple each original stopping time with its truncated version by changing it only when it lies in that player’s finite tail. Since rewards lie in \([-1,1]\),

$$
|U_i(p_x)-U_i(p^{(K)})|
\le 2\sum_j\tau_j(K).
\tag{11}
$$

For **every** replacement law of player \(i\), couple only the opponents. Uniformly over that replacement,

$$
\left|
U_i(\tau_i,p_{x,-i})
-
U_i(\tau_i,p^{(K)}_{-i})
\right|
\le 2\sum_{j\ne i}\tau_j(K).
$$

Taking unrestricted suprema preserves this bound:

$$
|B_i(p_x)-B_i(p^{(K)})|
\le 2\sum_{j\ne i}\tau_j(K).
\tag{12}
$$

Combining (11)–(12),

$$
|E_r(p_x)-E_r(p^{(K)})|
\le4\sum_j\tau_j(K).
\tag{13}
$$

Equations (7), (9), and (13) give

$$
\boxed{E_r(p^{(K)})<\varepsilon.}
$$

The coupling argument includes simultaneous quitting, preemption, Never, and every arbitrarily late unilateral deviation. No relaxed outcome distribution is substituted for a product law.

## 4. The unproved implication needed for a complete decision

What has been proved is

$$
\boxed{
\exists h,L\ \Psi_{r,h,L}
\quad\Longrightarrow\quad
\eta(r)=0,
}
\tag{14}
$$

with an exact finite verifier and a terminating all-accuracy compiler.

Combining this verifier search with the existing complete positive-gap semidecision would terminate on every positive-gap table and every zero-gap table satisfying (14)’s premise. The existing scale-resolution result already establishes the positive-gap side; it explicitly does not supply a finite zero decision. 

To turn this combination into item 2, one would still need

$$
\boxed{
\eta(r)=0
\quad\Longrightarrow\quad
\exists h,L\ \Psi_{r,h,L},
}
\tag{15}
$$

or a different, demonstrably complete zero-certificate language.

Finite-menu approximation does not establish (15). It supplies

$$
\forall\varepsilon>0\ \exists h,L,x,
$$

whereas (15) requires

$$
\exists h,L\ \forall\varepsilon>0\ \exists x.
$$

Here \(h,L\) may depend on \(r\), but not on the requested accuracy. I have no justified interchange of those quantifiers. **That coverage implication remains unproved in this answer; neither a globally terminating decision algorithm nor a counterexample certificate has been established.**

[1]: https://arxiv.org/abs/1609.02879 "[1609.02879] Elementary recursive quantifier elimination based on Thom encoding and sign determination"
