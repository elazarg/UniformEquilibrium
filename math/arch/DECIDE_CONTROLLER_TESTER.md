# Effective certification of the Fin4 controller--tester value

## Status

The normalized rational shell bracket, interval-tree checker, strict-margin
completeness, per-scale stage search, and global positive-counterexample
semidecision are already checked in the Research modules. The arbitrary-
rational normalization wrapper, uniform computability statement, and
rational-open-cover theorem below are sound ordinary-mathematics syntheses;
they are not yet named checked declarations.

Three facts determine what can presently be claimed:

1. the carrier minimum is exactly the infimum of literal exploitability over all behavioral profiles;
2. escape-aware finite-clock shells approximate that infimum with explicit error \(24/N\), while retaining Never and controlling arbitrarily late stopping;
3. each shell has an exact rational interval-tree proof system.

Together they give a **finite, independently checkable certificate class complete for every positive rational Fin4 value**, and an exact terminating approximation algorithm for \(\eta(r)\). They do **not** yet prove \(\eta(r)=0\) universally or exhibit a concrete table with \(\eta(r)>0\).

## The effective certification theorem

Let \(r\) be a rational four-player quitting table. Put

$$
M(r):=\max\left(1,\max_{S,i}|r_i(S)|\right),
\qquad \bar r:=r/M(r).
$$

Let \(\operatorname{Verify}_{\mathrm{norm}}\) be the checked Boolean
single-shell tree verifier for normalized rational tables. Define

$$
\operatorname{Verify}(r,N,a,\mathcal T)
:=
\operatorname{Verify}_{\mathrm{norm}}
\left(\bar r,N,\frac{a}{M(r)},\mathcal T\right).
$$

This is a decidable relation

$$
\operatorname{Verify}(r,N,a,\mathcal T)\in\{\mathrm{true},\mathrm{false}\},
$$

where \(N\ge1\), \(a\in\mathbb Q\), and \(\mathcal T\) is a finite rational binary box tree, with the following properties.

### Soundness

$$
\operatorname{Verify}(r,N,a,\mathcal T)=\mathrm{true}
\quad\Longrightarrow\quad
a\le \eta(r).
\tag{1}
$$

In particular, if \(a>0\), then \(\mathcal T\) is a finite exact certificate that

$$
\eta(r)>0.
$$

The implication (1) has no positive-gap premise.

### Completeness

For every rational \(a<\eta(r)\), there are \(N\) and a finite tree \(\mathcal T\) such that

$$
\operatorname{Verify}(r,N,a,\mathcal T)=\mathrm{true}.
\tag{2}
$$

Consequently,

$$
\boxed{
\eta(r)>0
\iff
\exists N\ge1\;\exists a\in\mathbb Q_{>0}\;\exists\mathcal T,\quad
\operatorname{Verify}(r,N,a,\mathcal T)=\mathrm{true}.
}
\tag{3}
$$

Thus positivity of the controller–tester value is recursively enumerable for
each fixed rational table, with finite exact witnesses. The current source
contains the normalized executable shell problem, rational checker,
strict-margin completeness theorem, and exact per-scale resolver. The
displayed arbitrary-rational wrapper is the additional construction needed to
state the result at this scope.

## Proof

### 1. Identification with literal all-behavior exploitability

For an actual behavioral profile \(\sigma\), write

$$
\Phi_r(\sigma)=\bigl(U^r(\sigma),B^r(\sigma)\bigr),
$$

where

$$
B_i^r(\sigma)
=
\sup_{\tau_i}
U_i^r\bigl(\sigma[i\leftarrow\tau_i]\bigr)
$$

uses every complete behavioral replacement, including Never and every arbitrarily late stopping law.

Since \(\sigma_i\) itself is an allowed replacement,

$$
B_i^r(\sigma)\ge U_i^r(\sigma).
$$

Let

$$
E(u,b)=\max\left\{0,\max_{i<4}(b_i-u_i)\right\}.
$$

For the canonical terminal-semantic carrier,

$$
\mathcal K_r=\overline{\{\Phi_r(\sigma):\sigma\text{ behavioral}\}}.
$$

The function \(E\) is continuous. Hence

$$
\begin{aligned}
\eta(r)
&=\min_{z\in\mathcal K_r}E(z)\\
&=\inf_{\sigma}E\bigl(\Phi_r(\sigma)\bigr)\\
&=\inf_{\sigma}
\max\left\{0,\max_{i<4}
\left[B_i^r(\sigma)-U_i^r(\sigma)\right]\right\}.
\end{aligned}
\tag{4}
$$

Thus the carrier value is exactly the literal unrestricted terminal-exploitability infimum used by the finite-clock construction.

The normalization used in the verifier is sound because, if

$$
M=\max\left(1,\max_{S,i}|r_i(S)|\right),
\qquad
\bar r=r/M,
$$

then

$$
\eta(r)=M\eta(\bar r).
\tag{5}
$$

It therefore suffices to construct certificates for normalized tables
satisfying \(\|\bar r\|_\infty\le1\). A normalized certificate at threshold
\(a/M\) proves the original lower bound \(a\), and if \(a<\eta(r)\) then
\(a/M<\eta(\bar r)\), so normalized strict-margin completeness supplies the
same tree required by the wrapper. Exact homogeneity of payoffs, behavioral
caps, profile exploitability, and its global infimum is established together
with the reward-robustness theorem.

### 2. Escape-aware finite-clock shells

Throughout Sections 2--4, \(r\) denotes the normalized table \(\bar r\), and
\(a\) denotes the normalized threshold \(a/M(r)\). Accordingly,
\(\operatorname{Verify}\) in those sections means
\(\operatorname{Verify}_{\mathrm{norm}}\). The arbitrary-rational theorem is
recovered by the scaling argument after (5).

Fix \(N\ge1\), and put

$$
T_N=8N+1,
\qquad
\rho_N=\frac{12}{N}.
\tag{6}
$$

Let \(C_N(r)\) be the set of semantic pairs of literal product stopping-law profiles whose marginals are supported on

$$
\{0,\ldots,T_N-1\}\cup\{\infty\}.
$$

An additional date \(T_N\) carries zero on-profile mass but is retained among the pure-deviation candidates.

For fixed finite-clock opponents, every unilateral behavioral payoff is affine in the deviator’s stopping law. Its supremum is therefore the supremum over pure stopping times

$$
t\in\mathbb N\cup\{\infty\}.
$$

All finite \(t\ge T_N\) are payoff-equivalent to the auxiliary date \(T_N\), while Never remains distinct. Consequently the unrestricted cap at a finite-clock center is exactly

$$
B_i(x)=
\max_{q\in\{0,\ldots,T_N,\infty\}}
U_i\bigl(x[i\leftarrow q]\bigr).
\tag{7}
$$

This is not a bounded-clock tester restriction: equation (7) is the true supremum over all behavioral replacements against that center.

Define the outer shell

$$
O_N(r)=
\left\{
z:\exists c\in C_N(r),\ 
\|z-c\|_\infty\le\rho_N
\right\}.
\tag{8}
$$

The escape-aware quantile compression gives, for every actual profile \(\sigma\), a center \(c_N\in C_N(r)\) satisfying

$$
\left\|
\Phi_r(\sigma)-c_N
\right\|_\infty
\le \rho_N.
\tag{9}
$$

Crucially, this estimate includes both prescribed payoffs and unrestricted caps. The proof uses forward and reverse transport of pure stopping times, and retains the Never atom exactly. Since \(O_N(r)\) is closed, (9) also gives

$$
\mathcal K_r\subseteq O_N(r).
\tag{10}
$$

Let

$$
A_N(r)=\min_{z\in O_N(r)}E(z),
\qquad
V_N(r)=\min_{c\in C_N(r)}E(c).
\tag{11}
$$

Every center is an actual profile, while every carrier point belongs to the outer shell. Hence

$$
A_N(r)\le \eta(r)\le V_N(r).
\tag{12}
$$

The objective \(E\) is \(2\)-Lipschitz in the semantic sup norm: if both \(u_i\) and \(b_i\) move by at most \(\rho\), then \(b_i-u_i\) moves by at most \(2\rho\). Therefore

$$
V_N(r)-A_N(r)\le 2\rho_N=\frac{24}{N}.
\tag{13}
$$

Combining (12)–(13),

$$
\boxed{
\eta(r)-\frac{24}{N}
\le A_N(r)
\le\eta(r)
\le V_N(r)
\le A_N(r)+\frac{24}{N}.
}
\tag{14}
$$

The all-Continue boundary \(e_\infty\) is not omitted: it is the center with all four Never masses equal to one. Arbitrarily late finite stopping is represented by the auxiliary date, and Never remains a separate candidate. The finite-clock hierarchy and its exact \(24/N\) bracket are documented and connected to actual unrestricted behavioral profiles in the formalization record.

### 3. The finite algebraic shell problem

For rational normalized \(r\), \(A_N(r)\) is the minimum of an explicit finite rational polynomial/max system.

There are \(8N+3\) atoms per marginal: the active dates, the auxiliary date, and Never. The system has

$$
16+4(8N+3)=32N+28
$$

real variables:

* eight coordinates for the shell point \((u,b)\);
* eight coordinates for its finite-clock center \((\widehat u,\widehat b)\);
* four marginal mass vectors.

There are 16 equalities:

$$
\begin{array}{ll}
4 & \text{simplex-sum equations},\\
4 & \text{zero auxiliary-mass equations},\\
4 & \widehat u_i=U_i(x),\\
4 & \displaystyle\prod_q\bigl(\widehat b_i-D_{i,q}(x)\bigr)=0.
\end{array}
\tag{15}
$$

Here \(D_{i,q}(x)\) is the payoff from pure deviation \(q\). The cap equations are accompanied by

$$
\widehat b_i-D_{i,q}(x)\ge0
$$

for every candidate \(q\). Thus the product equation forces at least one candidate to attain \(\widehat b_i\), while the inequalities force it to dominate all candidates. Hence \(\widehat b_i\) is exactly the maximum in (7).

There are

$$
2\cdot4(8N+3)+16=64N+40
$$

required-nonnegative rows: mass nonnegativity, cap-upper inequalities, and the sixteen signed coordinate inequalities encoding the shell radius.

The objective is

$$
\max\{0,b_0-u_0,\ldots,b_3-u_3\}.
\tag{16}
$$

On the actual carrier the extra zero does nothing because all debts are nonnegative. The executable expression system and these dimensions are defined directly in the rational single-shell module.

### 4. Exact finite tree certificates

A certificate is a finite binary tree of rational coordinate splits. At each leaf, exact rational interval evaluation must establish one of:

1. some equality interval omits zero;
2. some required-nonnegative expression has interval upper endpoint \(<0\);
3. the objective interval has lower endpoint at least \(a\).

Child boxes are reconstructed from the root and split path, so a certificate cannot insert unrelated boxes.

Suppose a real feasible assignment is followed down an accepted tree. It cannot terminate at a leaf of type 1 or 2. Therefore it terminates at a type-3 leaf, where its objective is at least \(a\). Induction over the tree proves

$$
\operatorname{Verify}_{\mathrm{norm}}(r,N,a,\mathcal T)
\Longrightarrow
a\le A_N(r).
\tag{17}
$$

Together with (12), this proves soundness (1). The checker and its tree-induction soundness theorem use rational arithmetic only and are independent of the search procedure that generated the tree.

For completeness, suppose

$$
a<A_N(r).
\tag{18}
$$

At every point of the compact rational root box, one of the following holds:

* an equality is nonzero;
* a required-nonnegative expression is strictly negative;
* the point is feasible, and its objective is at least \(A_N(r)>a\).

Rational polynomial/max interval extensions shrink to the exact point value as box diameters tend to zero. Hence every point has a sufficiently small neighborhood on which one of the three leaf reasons verifies. Compactness gives a finite subcover, and sufficiently deep rational midpoint subdivision produces a finite accepted tree.

This establishes strict-margin completeness:

$$
a<A_N(r)
\Longrightarrow
\exists\mathcal T,\ 
\operatorname{Verify}_{\mathrm{norm}}(r,N,a,\mathcal T)=\mathrm{true}.
\tag{19}
$$

Now let \(a<\eta(r)\). Choose \(N\) so that

$$
\frac{24}{N}<\eta(r)-a.
$$

By (14),

$$
A_N(r)\ge \eta(r)-\frac{24}{N}>a.
$$

Equation (19) then yields the required tree. This proves completeness (2) and equivalence (3).

## A terminating exact stage search at every scale

For a normalized rational table, there is a productive two-sided algorithm
for each rational \(\varepsilon>0\).

Set

$$
N(\varepsilon)
=
\left\lfloor\frac{96}{\varepsilon}\right\rfloor+1.
\tag{20}
$$

Then

$$
\frac{24}{N(\varepsilon)}<\frac{\varepsilon}{4}.
\tag{21}
$$

Run in parallel:

* the exact lower-tree search at threshold \(\varepsilon/4\);
* an enumeration of rational finite-clock profile codes whose exact unrestricted exploitability is below \(3\varepsilon/4\).

This process always terminates.

Indeed, if

$$
A_N(r)>\frac{\varepsilon}{4},
$$

strict lower-search completeness returns a tree. Otherwise,

$$
V_N(r)
\le A_N(r)+\frac{24}{N}
<
\frac{\varepsilon}{2}.
$$

Rational finite-clock profiles are dense among finite-clock centers, and finite-clock unrestricted exploitability is a finite maximum of continuous rational expressions. Thus the upper enumeration eventually finds an actual product profile \(\sigma_\varepsilon\) satisfying

$$
\operatorname{Expl}_r(\sigma_\varepsilon)
<
\frac{3\varepsilon}{4}.
\tag{22}
$$

Every output therefore has one of the exact meanings

$$
\boxed{
\frac{\varepsilon}{4}\le\eta(r)
}
\tag{23}
$$

or

$$
\boxed{
\exists \sigma_\varepsilon,\quad
\operatorname{Expl}_r(\sigma_\varepsilon)
<
\frac{3\varepsilon}{4}.
}
\tag{24}
$$

The implemented resolver uses exactly (20), independently verifies both output types, and proves termination for every normalized rational Fin4 table and positive rational scale.

Running it at \(\varepsilon_k=2^{-k}\) gives the fixed-table fork:

* if \(\eta(r)>0\), choose \(k\) with \(3\varepsilon_k/4<\eta(r)\); then an upper output is impossible, so a finite lower certificate is emitted;
* if \(\eta(r)=0\), no positive lower certificate can verify, and the process emits actual finite-clock profiles with exploitability tending to zero.

A lower certificate at \(\varepsilon\) proves the cap bound \(\eta(r)\ge\varepsilon/4\). Because a cap supremum need not be attained, an actual tester deviation is obtained at every strictly smaller level; in particular,

$$
\forall\sigma\ \exists i,\tau_i,\qquad
U_i^r(\sigma[i\leftarrow\tau_i])
-
U_i^r(\sigma)
>
\frac{\varepsilon}{8}.
\tag{25}
$$

Thus the output controls literal behavioral testers rather than merely cap numbers.

## Stronger derived consequences

The following two consequences are obtained by combining the checked shell, lower-certificate, upper-enumeration, and robustness results. They are not merely numerical heuristics.

### \(\eta(r)\) is uniformly computable for rational tables

First suppose \(r\) is normalized. Given rational \(\delta>0\), choose \(N\)
with

$$
g=\frac{24}{N}<\delta.
$$

Dovetail over rational \(a<b\), lower trees, and rational finite-clock profile
codes. Accept a tuple when the lower tree's exact Boolean checker verifies at
threshold \(a\), the profile code's exact checker verifies exploitability
below \(b\), and

$$
b-a<\delta.
$$

Such a tuple necessarily exists. Choose a small rational \(e>0\) with

$$
g+2e<\delta,
$$

then choose

$$
A_N(r)-e<a<A_N(r),
\qquad
V_N(r)<b<V_N(r)+e.
$$

Lower-tree completeness supplies the first certificate, and rational
upper-profile completeness supplies the second. Their checker soundness gives

$$
a\le A_N(r)\le\eta(r)
\le\operatorname{Expl}_r(\sigma)<b,
\qquad
b-a<\delta.
\tag{26}
$$

For an arbitrary rational table, compute \(M(r)\), apply the normalized
procedure to \(\bar r\) at accuracy \(\delta/M(r)\), and rescale the resulting
interval by \(M(r)\). Hence \(\eta(r)\) is a computable real, uniformly in a
rational four-player table. This still does not make the exact predicate
\(\eta(r)=0\) decidable: arbitrarily narrow certified intervals do not
generally decide whether a nonnegative computable real is exactly zero.

### Finite certificates cover every positive real table

For arbitrary real tables,

$$
|\eta(r)-\eta(q)|
\le
2\|r-q\|_\infty.
\tag{27}
$$

For a fixed profile, every prescribed payoff and every deviating payoff changes by at most \(\|r-q\|_\infty\); hence each debt changes by at most twice that amount. Taking the maximum and then the profile infimum proves (27). This exact \(2\)-Lipschitz theorem is formalized directly.

Associate to every arbitrary rational table \(q\) carrying a verified,
rescaled certificate

$$
\operatorname{Verify}(q,N,a,\mathcal T)=\mathrm{true},
\qquad a>0,
$$

the rational open ball

$$
B_\infty\left(q,\frac a4\right).
$$

If \(r\) belongs to this ball, then

$$
\eta(r)
\ge \eta(q)-2\|r-q\|_\infty
>
a-\frac a2
=
\frac a2>0.
\tag{28}
$$

Conversely, suppose \(\eta(r)=\alpha>0\). Choose a rational table \(q\) with

$$
\|r-q\|_\infty<\frac{\alpha}{16}.
$$

Then

$$
\eta(q)>\frac{7\alpha}{8}.
$$

Choose a rational \(a\) with

$$
\frac{\alpha}{2}<a<\eta(q).
$$

By certificate completeness, \(q\) has a finite verified lower tree at level \(a\), and

$$
\|r-q\|_\infty
<
\frac{\alpha}{16}
<
\frac a4.
$$

Therefore

$$
\boxed{
\{r:\eta(r)>0\}
=
\bigcup_{\operatorname{Verify}(q,N,a,\mathcal T)}
B_\infty\left(q,\frac a4\right),
}
\tag{29}
$$

where the union ranges over arbitrary rational centers carrying finite
rescaled certificates with \(a>0\).

This is a recursively enumerable rational-open cover of the entire positive-value locus, not merely of rational positive tables. For a computable real table supplied with certified rational error bounds, membership in one of these balls gives a finite exact positive certificate.

## What remains unresolved

No concrete rational table with an accepted positive tree is currently supplied, and the construction does not prove that one exists. Nor does absence of output at finitely many scales prove \(\eta(r)=0\). The repository’s own exact-search record explicitly distinguishes its complete positive semidecision from a solution of the Fin4 conjecture and states that no positive table has been produced.

Thus the outcome is:

$$
\boxed{
\text{finite exact positivity certificates are complete for Fin4,}
}
$$

together with exact approximation of \(\eta(r)\), but neither direct alternative 1 nor a concrete instance of alternative 2 has yet been established.
