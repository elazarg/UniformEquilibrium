The quantifier loss splits into two parts. **Time, accuracy, witness identity, terminal law, and payoff can be coordinated simultaneously.** What remains is a genuine cross-face continuation problem: the selected equilibrium source on one deleted face need not be the restriction, suffix, or continuation of the source selected on a larger face.

## 1. Uniformly recenter every witness at time \(0\)

Put

$$
M:=\max\left(1,\max_{\varnothing\ne S\subseteq I,\ i\in I}|r_i(S)|\right),
\qquad
\rho:=\frac{\gamma}{2M}.
$$

Every terminal payoff lies in \([-M,M]\), so every unilateral gain is at most \(2M\); hence \(0<\rho\le 1\).

Fix a proper nonempty block \(B\), write \(J=I\setminus B\), and let \(\sigma\) be a terminal \(\varepsilon\)-Nash profile of the induced \(J\)-player game. Let \(\widehat\sigma\) be its ambient quiet lift.

Suppose \(d\in B\) gains at least \(\gamma\) by quitting deterministically at date \(t\). Let

$$
p_t:=\Pr_\sigma(\text{no player of }J\text{ quits before }t),
$$

and let \(\sigma^{[t]}\) be the child profile obtained by shifting the all-Continue suffix at date \(t\) back to date \(0\).

For an outsider \(d\), write

$$
G_d(s;\tau):=
U_d\!\left(\widehat\tau^{\,d\to s}\right)-U_d(\widehat\tau).
$$

The histories before \(t\) are identical under \(d\)'s prescribed Never strategy and its deviation \(Q_t\). Conditioning on reaching \(t\) therefore gives the exact factorization

$$
G_d(t;\sigma)=p_t\,G_d(0;\sigma^{[t]}).
\tag{1}
$$

Since \(G_d(0;\sigma^{[t]})\le 2M\),

$$
p_t\ge \frac{\gamma}{2M}=\rho.
\tag{2}
$$

Moreover,

$$
G_d(0;\sigma^{[t]})
=\frac{G_d(t;\sigma)}{p_t}
\ge \frac{\gamma}{p_t}
\ge \gamma.
\tag{3}
$$

Thus every late witness can be replaced by an **immediate** witness, without reducing its gain, at a suffix reached with probability uniformly bounded below by \(\rho\).

### The suffix remains approximately Nash

Take \(j\in J\) and an arbitrary behavioral replacement \(\tau_j\) in the suffix game. Splice it into the original strategy after date \(t\), while following \(\sigma_j\) before \(t\). The spliced and prescribed profiles agree unless the all-Continue history reaches \(t\). Consequently,

$$
p_t\left[
U_j(\tau_j,\sigma^{[t]}_{-j})
-
U_j(\sigma^{[t]})
\right]
\le \varepsilon.
$$

Using \(p_t\ge\rho\),

$$
U_j(\tau_j,\sigma^{[t]}_{-j})
-
U_j(\sigma^{[t]})
\le \frac{\varepsilon}{\rho}.
\tag{4}
$$

Hence \(\sigma^{[t]}\) is terminal \(\varepsilon/\rho\)-Nash against **all behavioral deviations**, not merely deterministic times.

Given a desired output error \(\eta>0\), apply the outsider theorem to an input profile with

$$
\varepsilon_0:=\frac12\min\{\rho\eta,\gamma\}.
$$

Then \(\varepsilon_0<\gamma\), and the recentered suffix is terminal \(\eta\)-Nash.

This proves:

> **Uniform reached-face normalization.**
> For every proper nonempty block \(B\) and every \(\eta>0\), there exist
>
> $$
> d_{B,\eta}\in B,\qquad
> \tau_{B,\eta}\text{ on }I\setminus B,
> $$
>
> such that:
>
> 1. \(\tau_{B,\eta}\) is terminal \(\eta\)-Nash;
> 2. it is an all-Continue suffix of an actual child profile, reached with probability at least \(\rho\);
> 3. in its ambient quiet lift, \(d_{B,\eta}\) gains at least \(\gamma\) by quitting at date \(0\).

So unbounded witness times are not a cardinal-reduction obstruction.

## 2. Simultaneous selection over all blocks

Let \(\eta_k\downarrow0\), and perform the normalization above for every proper nonempty \(B\).

There are finitely many blocks, and the vector

$$
\bigl(d_{B,\eta_k}\bigr)_B
$$

takes values in the finite set \(\prod_B B\). Passing to one subsequence fixes **all** outsider identities simultaneously:

$$
d_{B,\eta_k}=d_B
\qquad\text{for every }B\text{ and every retained }k.
$$

All witness times are already \(0\).

For each \(B\), retain jointly:

* the child terminal law \(\mu_{B,k}\);
* the date-zero product root \(q_{B,k}\);
* the ambient prescribed payoff \(u_{B,k}\);
* the child unrestricted cap vector \(c_{B,k}\);
* the pre-recentering reach probability \(p_{B,k}\in[\rho,1]\).

These belong to a finite product of compact simplices and boxes. A further common subsequence therefore gives limits

$$
(\mu_B,q_B,u_B,c_B,p_B).
$$

For every survivor \(j\in J=I\setminus B\),

$$
0\le c_{B,k}(j)-u_{B,k}(j)\le\eta_k,
$$

so

$$
c_B(j)=u_B(j).
\tag{5}
$$

Thus the limit is a zero-debt point of the child terminal-semantic/law carrier.

If

$$
Q_d(q):=
\sum_{A\subseteq J}
\Pr_q(A)\,r_d(A\cup\{d\})
$$

is the payoff from \(d\)'s immediate Quit against root \(q\), then continuity of this finite polynomial and the selected inequalities give

$$
Q_{d_B}(q_B)-u_B(d_B)\ge\gamma.
\tag{6}
$$

The limit need not be attained by one actual behavioral profile. Its provenance is nevertheless exact: it is a joint semantic/law limit of actual suffixes, every one reached with probability at least \(\rho\). No stopping-law mass is silently lost.

Hence the full pointwise quantifier can be strengthened to the simultaneous statement

$$
\exists (d_B,z_B)_{B}
\quad
\forall B:
\quad
d_B\in B,\quad
z_B\in\mathcal E_{I\setminus B}^{\,\mathrm{reached},\rho},
\quad
G^{0}_{d_B}(z_B)\ge\gamma,
\tag{7}
$$

where \(\mathcal E_J\) denotes the zero-debt terminal-semantic/law face for the induced \(J\)-player game.

This coordinates everything that can be coordinated **inside each face**.

## 3. The exact remaining incompatibility

Suppose \(d_B\in B\), and compare the two selected faces

$$
J=I\setminus B,
\qquad
K=J\cup\{d_B\}
=I\setminus(B\setminus\{d_B\}).
$$

Minimality supplies a zero-debt source \(z_{B\setminus\{d_B\}}\) for the \(K\)-player game. But it supplies no relation between that source and \(z_B\):

$$
z_{B\setminus\{d_B\}}
\not\equiv
\text{an extension, suffix, or continuation of }z_B.
$$

In particular:

* changing \(d_B\) from Never to immediate Quit at \(z_B\) absorbs at the current root; it does not produce a continuation state;
* restricting a \(K\)-player equilibrium to \(J\) need not remain a \(J\)-player equilibrium;
* extending a \(J\)-player equilibrium by an arbitrary \(d_B\)-strategy need not control the old players’ unrestricted deviations.

The current minimal-counterexample development explicitly fences proper-restriction existence at precisely this point: it gives an equilibrium of the restricted game but no excluded-player payoff coordinates or ambient joining inequalities.

Let \(F_K(z_B)\) denote the set of \(K\)-player profiles satisfying whatever exact extension conditions are demanded by \(z_B\). If

$$
F_K(z_B)\cap\mathcal E_K=\varnothing,
$$

compactness may give a positive constrained gap

$$
\inf_{x\in F_K(z_B)} e_K(x)>0,
\tag{8}
$$

where \(e_K\) is maximum terminal exploitability. But minimality gives

$$
\inf_{x\in X_K}e_K(x)=0.
\tag{9}
$$

Equation (8) is therefore not a child counterexample. It is only a gap on one extension fiber. Turning it into (9) with a positive lower bound requires a profilewise retraction or compiler from arbitrary \(K\)-profiles into that fiber while preserving all behavioral deviations. That map is absent.

### A quantitative regression: extension-fiber failure need not create a game gap

Consider the two-player table

$$
r(\{1\})=(-1,1),\qquad
r(\{2\})=(-2,1),\qquad
r(\{1,2\})=\left(-\frac32,0\right).
\tag{10}
$$

The singleton game on player \(1\) has the unique exact equilibrium Never, because quitting yields \(-1\) while Never yields \(0\).

Now constrain the parent to profiles in which player \(1\) plays Never. Let \(p\) be the probability that player \(2\) eventually quits, and \(p_0\) its probability of quitting at date \(0\).

Player \(2\)'s debt is

$$
d_2=1-p.
$$

Player \(1\)'s immediate-Quit gain is

$$
\left(-1-\frac12p_0\right)-(-2p)
=
2p-1-\frac12p_0
\ge \frac32p-1.
$$

Therefore every profile extending the child equilibrium satisfies

$$
e(\sigma)
\ge
\max\left\{1-p,\frac32p-1\right\}
\ge \frac15.
\tag{11}
$$

So the extension fiber has a certified positive gap.

Nevertheless the parent has an exact behavioral equilibrium:

* player \(1\) quits at date \(0\);
* player \(2\) continues at date \(0\) and would quit at date \(1\).

Player \(1\)'s alternatives yield respectively \(-1\), \(-3/2\), or \(-2\); player \(2\) gets \(1\), while joining at date \(0\) gives \(0\). Hence parent exploitability is \(0\).

Thus even a strict quantitative failure to extend a child equilibrium does **not** yield a child gap or a parent counterexample. This regression does not negate an argument that uses the assumed parent gap essentially; it proves that compact separation of incompatible faces is insufficient on its own.

## 4. The precise certificate needed for consequence 3

Let \(G_1,\ldots,G_m\) be finitely many strictly smaller quitting games, and let \(e_G(x)\) denote maximum exploitability against unrestricted behavioral deviations.

A genuine finite-child reduction needs a compiler

$$
L:\prod_{a=1}^m X(G_a)\longrightarrow X(r)
$$

and a finite \(C>0\) satisfying the profilewise inequality

$$
e_r\bigl(L(x_1,\ldots,x_m)\bigr)
\le
C\max_{1\le a\le m}e_{G_a}(x_a)
\qquad
\text{for every tuple }(x_a).
\tag{12}
$$

This one inequality gives both directions required in consequence 3.

If every child has terminal approximants \(e_{G_a}(x_{a,k})\to0\), then

$$
e_r(L(x_{1,k},\ldots,x_{m,k}))\to0,
$$

and compact terminal semantics supplies a parent uniform-equilibrium payoff.

Conversely, if \(e_r\ge\gamma\) for every parent profile, then (12) gives

$$
\max_a e_{G_a}(x_a)\ge\frac{\gamma}{C}
\quad\text{for every tuple}.
$$

Since the child coordinates are independent,

$$
\inf_{(x_a)}\max_a e_{G_a}(x_a)
=
\max_a\inf_{x_a}e_{G_a}(x_a),
$$

so some child inherits a positive gap at least \(\gamma/C\).

This is the exact finite-family version of the repository’s `UniformScoreReduction`: a target profile is translated back to a source profile and target audit score dominates a fixed positive multiple of source audit score. The current module proves the logical transport results but deliberately does not construct the cardinal reduction.

The quiet lifts cannot satisfy (12). For arbitrarily small \(\eta\),

$$
e_{I\setminus B}(\tau_{B,\eta})\le\eta,
\qquad
e_r(\widehat{\tau}_{B,\eta})\ge\gamma.
\tag{13}
$$

Therefore any valid reduction must be nonlocal: it must combine or transform several child profiles, rather than select one proper-face equilibrium and lift it quietly.

## 5. What singleton blocks yield after full coordination

The singleton-survivor faces admit one further exact extraction.

Write

$$
s_i:=r_i(\{i\}).
$$

### Case \(s_i\ge0\)

In the one-player game on \(\{i\}\), let \(i\)'s quitting time be uniform on \(\{1,\ldots,N\}\). This is an exact terminal equilibrium.

For \(d\ne i\), put

$$
a_{di}:=s_d-r_d(\{i\}).
$$

If \(d\) quits at \(k\in\{1,\ldots,N\}\), its gain is

$$
G_d(k)
=
\frac{N-k}{N}a_{di}
+
\frac1N\left(r_d(\{i,d\})-r_d(\{i\})\right).
\tag{14}
$$

At date \(0\), its gain is exactly \(a_{di}\); after \(N\), it is \(0\).

If \(a_{di}<\gamma\) for every \(d\ne i\), finiteness of \(I\) gives a strict margin below \(\gamma\). Since the collision term in (14) has absolute value at most \(2M/N\), sufficiently large \(N\) would leave every outsider and every deterministic time with gain \(<\gamma\), contradicting the operational outsider conclusion. Hence

$$
s_i\ge0
\quad\Longrightarrow\quad
\exists d\ne i:
\quad
s_d-r_d(\{i\})\ge\gamma.
\tag{15}
$$

The resulting witness can be taken at date \(0\).

### Case \(s_i<0\)

The unique one-player equilibrium is Never. Its ambient quiet lift is all-Never, so the outsider conclusion gives

$$
\exists d\ne i:\quad s_d\ge\gamma.
\tag{16}
$$

Thus all singleton-block witnesses can be selected simultaneously as a quantitative directed graph: every nonnegative-singleton player \(i\) has an edge to some \(d\) satisfying (15); every negative-singleton player points to a bottom state, and the bottom state points to a player satisfying (16). This finite serial graph contains a directed cycle.

This is stronger than one isolated solo-pressure inequality, but it still gives no cardinal bound: directed cycles may have arbitrary length. The repository already contains actual arbitrary-cardinality cyclic singleton-passport and passive-background regressions showing that witness-closed kernels need not have size four.

There is an even simpler game-facing warning. For every finite \(I\), let

$$
r_i(S)=\mathbf 1_{\{i\in S\}}.
\tag{17}
$$

For every proper block, every survivor profile, every \(d\in B\), immediate Quit gives \(d\) gain exactly \(1\) over its quiet-lift payoff. All blocks can therefore use fixed identities and time \(0\), with no accuracy dependence at all. Yet “everyone quits at date \(0\)” is an exact parent equilibrium. Perfectly coordinated outsider data do not by themselves encode the positive interior gap.

## 6. Consequences for the four requested outcomes

The reached-source theorem removes all artificial quantifier incompatibility:

$$
\boxed{\text{block, accuracy, outsider identity, witness time, payoff, law, and actual suffix provenance}}
$$

can be selected simultaneously. The residual is exactly:

$$
\boxed{\text{no profilewise, deviation-preserving transition between the selected face sources}.}
$$

From the supplied hypotheses I do not obtain any of the four terminal outcomes:

1. There is no proof here that a cardinal-minimal counterexample has at most four players. With the proved one-, two-, and three-player cases, that statement is exactly the open larger-to-four reduction, not a weaker corollary. The current formal development proves this equivalence explicitly.

2. No fixed cardinal bound appears: the selected singleton graph and the general face-choice function both admit arbitrarily long witness cycles.

3. A constructive reduction is now isolated to the exact compiler inequality (12). Quiet lifts are quantitatively ruled out by (13), and incompatibility of selected extension fibers yields only constrained gaps such as (11).

4. No reward table with a certified positive unrestricted behavioral gap is produced. Published work as of April 2026 still records ordinary quitting games with at least four players as unresolved, while characterizing only selected absorption-path classes. ([Springer Nature][1])

The strongest valid conclusion is therefore a reduction of the cardinal problem to one sharply stated seam:

> **Every proper face has a fixed, immediate, uniformly reached outsider obstruction at a zero-debt semantic source. A cardinal descent requires converting these separately realized sources into a profilewise score-dominating compiler. Neither witness selection nor failure of direct extension supplies that compiler.**

Repository-state assertions above were checked under the project runbook’s exact-source and provenance discipline. 

[1]: https://link.springer.com/article/10.1007/s00182-026-00982-6 "The APS approach for undiscounted quitting games | International Journal of Game Theory | Springer Nature Link"
