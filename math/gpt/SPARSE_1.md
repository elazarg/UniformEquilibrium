## What the displayed data actually imply

The sparse certificates do not add a new executable structure. In fact, certificates 2–4—and even the stated “no social costate” assumption—already follow from certificate 1 and the fact that \(\mu\) is a source law.

Put

$$
x(\omega)=\bar r(\omega)-s,
\qquad
a=U-s=\sum_{\omega}\mu(\omega)x(\omega).
$$

Certificate 1 says

$$
a_i\ge D_*-d_i=\sum_{j\ne i}d_j.
\tag{1}
$$

Since \(\sum_i d_i=D_*>0\), this immediately gives

$$
a_i+d_i=B_i-s_i\ge D_*,
\tag{2}
$$

and at most one coordinate of \(a\) can vanish. Indeed, if \(a_i=0\), then (1) forces \(d_i=D_*\) and hence \(d_j=0\) for every \(j\ne i\). Consequently,

$$
\sum_i (U_i-s_i)\ge 3D_*.
\tag{3}
$$

This has three consequences.

### 1. All sparse laws can already be chosen from the source support

Let \(J\subseteq I\), \(|J|\ge2\). Because at most one coordinate of \(a\) vanishes,

$$
a_J\in \mathbb R_+^J\setminus\{0\}.
$$

But

$$
a_J=\sum_{\omega\in\operatorname{supp}\mu}
\mu(\omega)x_J(\omega),
$$

so \(a_J\) belongs to the conic hull of the projected source vectors
\(x_J(\omega)\). Conic Carathéodory in \(\mathbb R^J\) gives outcomes
\(\omega_1,\ldots,\omega_m\in\operatorname{supp}\mu\), with
\(m\le |J|\), and coefficients \(c_k>0\) such that

$$
a_J=\sum_{k=1}^m c_kx_J(\omega_k).
$$

After normalizing \(c_k\), one obtains a probability law \(\nu_J\), supported on at most \(|J|\) points of \(\operatorname{supp}\mu\), satisfying

$$
\mathbb E_{\nu_J}\bar r_i\ge s_i\quad(i\in J),
$$

with a strict inequality for some \(i\in J\).

Thus certificate 3 can be strengthened:

$$
\boxed{\text{Every }\nu_J,\ |J|\ge2,\text{ may be chosen from }\operatorname{supp}\mu.}
$$

The changed weights remain the entire problem.

### 2. The no-costate condition is automatic

Let \(\theta\ge0\) have at least two positive coordinates. From (1),

$$
\begin{aligned}
\theta\cdot(U-s)
&\ge \sum_i\theta_i(D_*-d_i)\\
&=D_*\sum_i\theta_i-\theta\cdot d\\
&\ge
D_*\left(\sum_i\theta_i-\max_i\theta_i\right)>0.
\end{aligned}
\tag{4}
$$

Since

$$
\theta\cdot(U-s)
=
\sum_\omega
\mu(\omega)\,
\theta\cdot(\bar r(\omega)-s),
$$

some source outcome has positive \(\theta\)-surplus. If that outcome is Never, then

$$
-\theta\cdot s>0,
$$

and hence \(\theta\cdot s<0\). Otherwise a nonempty coalition \(S\) satisfies

$$
\theta\cdot(r(S)-s)>0.
$$

So the asserted absence of a multi-coordinate closing costate follows from certificate 1.

### 3. Certificate 4 is just the sixteen-outcome pigeonhole bound

There are sixteen terminal outcomes, including Never. By (4), one of them satisfies

$$
\mu(\omega)\,
\theta\cdot(\bar r(\omega)-s)
\ge
\frac{D_*
\left(\sum_i\theta_i-\max_i\theta_i\right)}{16}.
$$

Thus certificate 4 is also automatic.

The net result is:

$$
\boxed{
\text{The entire sparse-boundary package adds no information beyond
the source inequality (1).}}
\tag{5}
$$

In particular, the simultaneous presence of \(\mu\) and the sparse laws does not itself supply a source chronology, a product-root factorization, or an incentive-compatible return.

---

## Why source-supported sparsification still does not execute

Here is an explicit four-player example showing the exact failure.

Let every singleton reward vector be zero, so \(s=0\), and let every nonsingleton coalition have reward vector \(\mathbf 1=(1,1,1,1)\).

Use the behavioral profile:

* at date \(1\), players \(0\) and \(1\) quit independently with probability \(1/2\), while \(2,3\) Continue;
* after all Continue, players \(2,3\) quit surely at date \(2\).

Its terminal law is

$$
\mu(\{0\})=\mu(\{1\})
=\mu(\{0,1\})=\mu(\{2,3\})=\frac14.
$$

Hence

$$
U=\frac12\mathbf 1.
$$

For this profile,

$$
d_0=d_1=0,\qquad d_2=d_3=\frac14,\qquad D=\frac12,
$$

and the displayed source inequality holds:

$$
U_i-s_i\ge D-d_i.
$$

The source-supported sparse law

$$
\nu=\frac12\delta_{\{0,1\}}+\frac12\delta_{\{2,3\}}
$$

has payoff \(\mathbf1>s\). Nevertheless, \(\nu\) is not the terminal law of any behavioral profile.

To see this, suppose \(\{0,1\}\) occurs with positive probability at some live date. At its product root, \(q_0,q_1>0\). Since \(\{0\}\) and \(\{1\}\) must have zero probability, necessarily

$$
q_0=q_1=1.
$$

Since supersets of \(\{0,1\}\) must also have zero probability,

$$
q_2=q_3=0.
$$

That root therefore terminates surely in \(\{0,1\}\), leaving no probability for a later \(\{2,3\}\). The same argument excludes the reverse order, and both coalitions cannot occur at the same product root. Hence the sparse reweighting is not behavioral.

This example does **not** have a positive global minimum—All Never is an exact equilibrium. Its purpose is narrower and exact: even source-supported sparsification plus the paid-source inequality does not produce an executable law.

Execution is not enough either. For example, set \(s=0\),

$$
r(\{0,1\})=\mathbf1,
\qquad
r_0(\{1\})=2,
$$

and prescribe players \(0,1\) to quit surely at date \(1\). The terminal law
\(\delta_{\{0,1\}}\) is a product-root law and its payoff strictly dominates \(s\), but player \(0\) gains \(1\) by Continuing, leaving player \(1\) to quit alone. Thus payoff admissibility does not imply Nash compatibility.

---

## The minimum has a uniform all-Continue moat

The cap information actually works against the usual rare-hazard serialization.

Let

$$
M=\max_{i,S}|r_i(S)|.
$$

For a product root \(q\), write

$$
c_i(q)=\prod_{j\ne i}(1-q_j).
$$

If player \(i\) Continues and subsequently uses a suffix best response, their value is

$$
C_i^B(q_{-i})
=
c_i(q)B_i+
\sum_{\emptyset\ne T\subseteq I\setminus\{i\}}
p_{-i}^q(T)r_i(T).
$$

If they Quit at the root, their value is

$$
Q_i(q_{-i})
=
c_i(q)s_i+
\sum_{\emptyset\ne T\subseteq I\setminus\{i\}}
p_{-i}^q(T)r_i(T\cup\{i\}).
$$

By (2),

$$
B_i-s_i\ge D_*.
$$

Consequently,

$$
\begin{aligned}
C_i^B-Q_i
&=
c_i(B_i-s_i)
+\sum_{T\ne\emptyset}p_{-i}^q(T)
 \bigl(r_i(T)-r_i(T\cup\{i\})\bigr)\\
&\ge c_iD_*-2M(1-c_i).
\end{aligned}
$$

Therefore, whenever

$$
1-c_i(q)\le
\frac{D_*}{2(D_*+2M)},
$$

one has

$$
C_i^B(q_{-i})-Q_i(q_{-i})\ge\frac{D_*}{2}.
\tag{6}
$$

So every sufficiently small product root lies in a neighborhood where the unique cap branch for every player is Continue. In that neighborhood, if \(T_qz\) denotes prefixing \(z\) by \(q\), then

$$
D(T_{th}z)
=
D_*+
t\sum_i h_i
\left[
(U_i-s_i)-(D_*-d_i)
\right]
+O(t^2).
\tag{7}
$$

Every first-order coefficient in (7) is nonnegative. Arbitrary coalition rewards appear only in the quadratic and higher collision terms.

This rules out the tempting argument “serialize the sparse law using very small hazards.” Such a construction remains inside the moat (6); it does not make the prescribed Quit actions best responses. Any successful construction has to use a nonlocal source block or explicitly consume higher-order collision structure.

---

## The missing interface

A source-matched return requires time-labelled data that are absent from the hypotheses. For actual source profiles \(\sigma_n\), one needs at least

$$
\mu_n(t,S)
=
\rho_{n,t}\,p_{q_{n,t}}(S),
$$

together with the all-Continue successor semantic states \(z_{n,t+1}\) and the Bellman cap recursion at each root. A valid consumer must extract actual intervals \([a_n,b_n)\) for which:

$$
z_{n,a_n}\longrightarrow z^\sharp,
\qquad
z_{n,b_n}\longrightarrow z^\sharp
$$

or else the second limit is a child of strictly smaller rank;

the full, unreweighted block law carries the admissible payoff charge; and the cap continuation is controlled either by exact source matching or by vanishing player-deleted reach.

Outcome-level densities also have a precise product obstruction. At one interior product root, an absolutely continuous change of law is another product root only when its density \(L(S)\) has the form

$$
L(S)=C\prod_{i\in S}a_i.
$$

Equivalently, every Boolean rectangle satisfies

$$
L(A)L(A\cup\{i,j\})
=
L(A\cup\{i\})L(A\cup\{j\}).
\tag{8}
$$

With zeros, the target support must additionally be a subcube. Failure of (8), or failure of the subcube condition, is the minimal source-attached nonprojective principal that a finite-rank descent would have to carry. A terminal-outcome law \(\nu_J\) contains none of the date-by-date densities needed to test (8).

## Conclusion

The displayed certificates do not prove any of alternatives 1–3. They reduce exactly to the already-known paid-source inequality, and the two natural adapters—source-supported reweighting and rare-hazard serialization—are respectively invalid and blocked by the uniform cap moat.

This is not an explicit positive-gap counterexample: the examples above deliberately isolate the adapter failures and have global minimum \(0\). The remaining mathematical task is precisely a new trace theorem converting the time-labelled source roots and Bellman caps into either an actual charged return or a fixed finite-rank nonprojective descent. No such theorem follows from \((U,B,\mu,\nu_J)\) alone.
