# Question 188: Paid root-or-tail transport of a reached-row gain

## Setting

Let \(I\) be a nonempty finite player set. At every stage each player chooses
Continue or Quit. If the nonempty set \(S\subseteq I\) Quits, play stops with
payoff \(r(S)\in\mathbb R^I\); if nobody ever Quits, the payoff is \(0\).

For a behavioral profile \(\sigma\), let

\[
U_i(\sigma)=\text{its terminal payoff},\qquad
B_i(\sigma)=\sup_{\tau_i}U_i(\tau_i,\sigma_{-i}),
\]

and set \(d_i=B_i-U_i\) and \(D=\sum_i d_i\). Let

\[
\mathcal K=\overline{\{(U(\sigma),B(\sigma)):\sigma
\text{ is behavioral}\}},\qquad
D_*=\min_{(u,b)\in\mathcal K}\sum_i(b_i-u_i)>0.
\]

Consider an actual stage \(t\) of a profile \(\sigma\). Let \(h>0\) be the
probability that \(t\) is reached, \(x\) the product mixed action played there,
and \(v\) the payoff of the literal continuation after unanimous Continue.
Write \(q_j=x_j(\mathrm Q)\), \(c_j=1-q_j\), and, for
\(A\subseteq I\setminus\{i\}\),

\[
p^x_{-i}(A)=
\prod_{j\in A}q_j\prod_{j\notin A\cup\{i\}}c_j.
\]

Player \(i\)'s pure Quit and Continue values are

\[
\begin{aligned}
Q_i(x_{-i})&=\sum_Ap^x_{-i}(A)r_i(A\cup\{i\}),\\
C_i(x_{-i};v_i)&=p^x_{-i}(\varnothing)v_i+
\sum_{\varnothing\ne A}p^x_{-i}(A)r_i(A).
\end{aligned}
\]

Put

\[
F_i(x;v_i)=q_iQ_i+c_iC_i,\qquad
\rho_i(x;v_i)=\max\{Q_i,C_i\}-F_i(x;v_i).
\]

Replacing only player \(i\)'s action at this reached row by a better pure
endpoint and then following the original continuation is a legal behavioral
deviation with exact gain

\[
G=h\rho_i(x;v_i).
\]

Assume \(G>0\).

## Known fences

- If a repaired row keeps both \(x\) and \(v\) and is
  \(\varepsilon\)-Nash, then \(G\leq\varepsilon\). In particular, the same
  root--continuation pair cannot be an exact Nash--Bellman edge.
- Appending an exact suffix after the unchanged non-Nash source does not erase
  the retained deviation. For every \(\varepsilon<G\), the unchanged source is
  not terminal \(\varepsilon\)-Nash.
- If \(z=(u,b)\) is prefixed by a root which is Nash against the cap \(b\),
  every debt coordinate is multiplied by the joint Continue probability.
  Along a finite word of such roots,

  \[
  \sum_t(1-c(x_t))\leq
  \log\frac{D(\text{terminal tail})}{D_*}.
  \]

  Thus an arbitrarily long exact cap-Nash word cannot carry unbounded
  cumulative absorption. For nonexact words, the corresponding account
  contains the accumulated Nash errors.

These facts close all repairs which preserve the literal root and tail. They
do not compare a profitable root--continuation pair with a different root or
a different continuation state.

## Question

Can a positive reached-row gain be transported through a change of root or
tail in a quantitatively state-matched way?

A positive solution should start from the displayed data and, with a constant
\(\alpha>0\) depending only on the finite reward table, produce at least one of
the following:

1. a reachable semantic pair \(z'\in\mathcal K\) with
   \(D(z')\leq D_*-\alpha G\);
2. terminal \(\varepsilon\)-Nash profiles for every \(\varepsilon>0\); or
3. a finite or periodic Nash--Bellman chronology which changes the root or
   tail, returns to its initial semantic state, and turns the original gain
   into a telescoping inequality \(0\geq\alpha G\).

A negative solution should instead give an explicit nonnegative potential
\(\Phi\) and a precisely defined class of changed-root or changed-tail
transports for which

\[
G\leq
\Phi(z_{\rm in})-\Phi(z_{\rm out})
+\sum_s\varepsilon_s
\]

holds, where \(\varepsilon_s\) are the Nash errors of the intervening rows.
The class must strictly contain same-root, same-continuation repair and
include both a root-only change and a tail-only change. The potential must be
bounded on \(\mathcal K\), so that the inequality has a genuine telescoping
consequence.

Merely splitting changed transports into further cases, or reproving the
same-root, same-continuation bound \(G\leq\varepsilon\), does not answer the
question.

## Answer

The hinge is whether the transport changes player (i)’s **opponent environment**. With the opponents fixed, there is an exact bounded potential. Changing the opponents introduces an uncontrolled best-response-envelope drift.

This gives a negative solution in the requested sense.

## 1. The transport class

Write (\sigma^{[t]}) for the shifted profile beginning at stage (t), conditional on reaching (t), and (\sigma^{[t+1]}) for the continuation after unanimous Continue at (t).

Define

[
\beta_i:=B_i(\sigma^{[t+1]}).
]

Since the literal continuation strategy is feasible,

[
\beta_i\ge v_i.
]

The full conditional best-response value at the reached row is therefore

[
\widehat B_i
:=
\max\bigl{
Q_i(x_{-i}),
C_i(x_{-i};\beta_i)
\bigr}.
\tag{1}
]

Consider any behavioral profile (\tau) satisfying

[
\tau_{-i}=\sigma_{-i},
\qquad
\tau_i^s=\sigma_i^s\quad\text{for all }s<t.
\tag{2}
]

Thus (\tau) may arbitrarily change player (i)’s action at the reached row, player (i)’s whole continuation after that row, or both, but it does not change the opponents or the prefix before (t).

Let (y_i) be player (i)’s Quit probability at (t) under (\tau), and let

[
w_i:=U_i(\tau^{[t+1]}).
]

Put (\widetilde x=(y_i,x_{-i})). Define the reached conditional Nash error of the transported fragment by

[
E_t(\tau)
:=
h\left[
\widehat B_i-F_i(\widetilde x;w_i)
\right].
\tag{3}
]

This is nonnegative. Indeed, because the opponents are unchanged,

[
B_i(\tau^{[t]})
===============

# B_i(\sigma^{[t]})

\widehat B_i.
]

## 2. The potential

For the marked player (i), define

[
\boxed{\quad
\Phi_i(u,b):=b_i-u_i=d_i(u,b).
\quad}
\tag{4}
]

It is nonnegative on (\mathcal K).

Let

[
\underline r_i
==============

\min\bigl({0}\cup{r_i(S):\varnothing\ne S\subseteq I}\bigr),
\qquad
\overline r_i
=============

\max\bigl({0}\cup{r_i(S):\varnothing\ne S\subseteq I}\bigr).
]

Every prescribed payoff and every unilateral best-response payoff lies in
([\underline r_i,\overline r_i]). Hence

[
0\le \Phi_i(z)\le \overline r_i-\underline r_i
\qquad(z\in\mathcal K).
\tag{5}
]

Thus (\Phi_i) is bounded by a constant depending only on the finite reward table.

## 3. Paid transport inequality

Let

[
z_{\rm in}=z(\sigma),
\qquad
z_{\rm out}=z(\tau).
]

Then

[
\boxed{\quad
G
\le
\Phi_i(z_{\rm in})-\Phi_i(z_{\rm out})
+
E_t(\tau).
\quad}
\tag{6}
]

### Proof

The source conditional payoff is

[
U_i(\sigma^{[t]})=F_i(x;v_i).
]

Since (\beta_i\ge v_i) and (C_i(x_{-i};\cdot)) is nondecreasing,

[
\max{Q_i(x_{-i}),C_i(x_{-i};v_i)}
\le \widehat B_i.
]

Consequently,

[
\begin{aligned}
\frac Gh
&=
\max{Q_i(x_{-i}),C_i(x_{-i};v_i)}
---------------------------------

F_i(x;v_i)
\
&\le
\widehat B_i-F_i(x;v_i)
\
&=
F_i(\widetilde x;w_i)-F_i(x;v_i)
+
\left[\widehat B_i-F_i(\widetilde x;w_i)\right].
\end{aligned}
\tag{7}
]

The two profiles agree before (t), so

[
U_i(\tau)-U_i(\sigma)
=====================

h\left[
F_i(\widetilde x;w_i)-F_i(x;v_i)
\right].
\tag{8}
]

Moreover, (\tau_{-i}=\sigma_{-i}), and therefore

[
B_i(\tau)=B_i(\sigma).
]

Hence

[
U_i(\tau)-U_i(\sigma)
=====================

# d_i(z_{\rm in})-d_i(z_{\rm out})

\Phi_i(z_{\rm in})-\Phi_i(z_{\rm out}).
\tag{9}
]

Multiplying (7) by (h) and using (3), (8), and (9) proves (6). ∎

The coefficient of (G) is exactly (1); there is no table-dependent loss.

## 4. Exact root-error plus tail-error decomposition

Let

[
\widetilde c_i=1-y_i,
\qquad
c_{-i}=\prod_{j\ne i}c_j.
]

Define the new root’s cap-Nash error by

[
\eta_{i,t}(\tau)
:=
\widehat B_i
------------

\left[
y_iQ_i(x_{-i})
+
\widetilde c_i C_i(x_{-i};\beta_i)
\right].
\tag{10}
]

Because

[
C_i(x_{-i};\beta_i)-C_i(x_{-i};w_i)
===================================

c_{-i}(\beta_i-w_i),
]

the error in (3) has the exact decomposition

[
\boxed{\quad
E_t(\tau)
=========

h,\eta_{i,t}(\tau)
+
h,\widetilde c_i c_{-i},(\beta_i-w_i).
\quad}
\tag{11}
]

The two terms have precise meanings:

* (h\eta_{i,t}) is the reached cap-Nash error of the changed root.
* (h\widetilde c_i c_{-i}(\beta_i-w_i)) is the surviving best-response debt of the changed tail.

Thus a root-only change can leave unpaid tail debt, while a tail-only change can leave unpaid root error.

### Same root and same continuation

Taking

[
y_i=q_i,\qquad w_i=v_i
]

gives the original root and tail. Then (6) becomes

[
G\le E_t(\sigma),
]

which is the same-root, same-continuation fence.

### Root-only change

Taking (w_i=v_i) and arbitrary (y_i) gives

[
G
\le
\Phi_i(z_{\rm in})-\Phi_i(z_{\rm out})
+
h\eta_{i,t}(\tau)
+
h\widetilde c_i c_{-i}(\beta_i-v_i).
\tag{12}
]

### Tail-only change

Taking (y_i=q_i) and arbitrarily replacing only (i)’s continuation gives

[
G
\le
\Phi_i(z_{\rm in})-\Phi_i(z_{\rm out})
+
h\eta_{i,t}(\tau)
+
h c_i c_{-i}(\beta_i-w_i).
\tag{13}
]

Hence the class strictly contains the literal unchanged repair and genuinely includes both root-only and tail-only changes.

In particular, if (\tau^{[t]}) is an (\varepsilon)-best response for (i) against the unchanged opponents, then

[
E_t(\tau)\le h\varepsilon,
]

and therefore

[
\Phi_i(z_{\rm out})
\le
\Phi_i(z_{\rm in})-G+h\varepsilon.
\tag{14}
]

So the reached-row gain can always be converted, up to an arbitrarily small error, into a decrease of the marked player’s own semantic debt.

## 5. Expansion into intervening row errors

Let (z_s^\tau) be the semantic pair of the shifted profile (\tau^{[s]}). At row (s), let (a_s) be its product root and set

[
\gamma_s:=\prod_{j\in I}\bigl(1-a_{s,j}(\mathrm Q)\bigr).
]

Let (\eta_{i,s}) be the cap-Nash error of player (i) at that row:

[
\eta_{i,s}
==========

## \max{Q_i((a_s)*{-i}),C_i((a_s)*{-i};b_i^{s+1})}

\Bigl[
a_{s,i}(\mathrm Q)Q_i((a_s)*{-i})
+
a*{s,i}(\mathrm C)C_i((a_s)_{-i};b_i^{s+1})
\Bigr].
\tag{15}
]

The exact debt recursion is

[
d_i(z_s^\tau)
=============

\eta_{i,s}
+
\gamma_s d_i(z_{s+1}^\tau).
\tag{16}
]

Set

[
H_t=h,
\qquad
H_{s+1}=H_s\gamma_s.
]

Iterating (16) gives, for every (N>t),

[
E_t(\tau)
=========

# h,d_i(z_t^\tau)

\sum_{s=t}^{N-1}H_s\eta_{i,s}
+
H_Nd_i(z_N^\tau).
\tag{17}
]

Thus, with

[
\varepsilon_s:=H_s\eta_{i,s},
\qquad
\varepsilon_N:=H_Nd_i(z_N^\tau),
]

the requested form is

[
\boxed{\quad
G
\le
\Phi_i(z_{\rm in})-\Phi_i(z_{\rm out})
+
\sum_{s=t}^{N}\varepsilon_s.
\quad}
\tag{18}
]

For a finite chronology ending in an exact tail, (\varepsilon_N=0). For a periodic chronology whose per-period joint-Continue product is strictly below (1), boundedness of (d_i) implies (H_Nd_i(z_N^\tau)\to0), so (18) holds with the infinite sum of reached row errors.

If the per-period product is (1), every row in the period is all-Continue. Then the residual debt need not vanish. This is exactly the all-Continue semantic plateau: it cannot be removed by pretending that the row errors telescope.

## 6. Genuine telescoping consequence

For any finite chain of such transports, with the same marked player and unchanged opponent environment,

[
\sum_{k=0}^{m-1}G_k
\le
\Phi_i(z_0)-\Phi_i(z_m)
+
\sum_{k,s}\varepsilon_{k,s}.
\tag{19}
]

Using (5),

[
\sum_{k=0}^{m-1}G_k
\le
\overline r_i-\underline r_i
+
\sum_{k,s}\varepsilon_{k,s}.
\tag{20}
]

For a closed or periodic semantic chain (z_m=z_0),

[
\sum_{k=0}^{m-1}G_k
\le
\sum_{k,s}\varepsilon_{k,s}.
\tag{21}
]

Thus an exact closed transport in this class would indeed give

[
0\ge G
]

for a single positive ticket.

## 7. Why this does not yield a global (D_*)-contradiction

The fixed-opponent condition is essential. If a transport changes (\sigma_{-i}), then (B_i) changes, and

[
\Phi_i(z_{\rm in})-\Phi_i(z_{\rm out})
======================================

U_i(\tau)-U_i(\sigma)
+
B_i(\sigma)-B_i(\tau).
\tag{22}
]

Equivalently,

[
U_i(\tau)-U_i(\sigma)
=====================

\Phi_i(z_{\rm in})-\Phi_i(z_{\rm out})
+
B_i(\tau)-B_i(\sigma).
\tag{23}
]

The envelope-drift term (B_i(\tau)-B_i(\sigma)) has no sign and is not controlled by the Nash errors of the displayed roots. Likewise, even when (d_i) drops by almost (G), the other debts (d_j), (j\ne i), may increase:

[
D(z_{\rm out})-D(z_{\rm in})
============================

-\bigl[\Phi_i(z_{\rm in})-\Phi_i(z_{\rm out})\bigr]
+
\sum_{j\ne i}\bigl[d_j(z_{\rm out})-d_j(z_{\rm in})\bigr].
\tag{24}
]

Therefore the displayed local datum does not by itself imply (D(z_{\rm out})<D_*), nor does this certificate transport through arbitrary all-player Nash–Bellman root or tail changes.

The exact negative conclusion is: **a reached-row gain is fully transportable through arbitrary changes of the marked player’s root and tail under a fixed opponent environment, with bounded potential (\Phi_i=d_i); the only unpaid amount is the cap-Nash/root-plus-tail error of the transported fragment. The missing object for the global argument is control of opponent-induced envelope drift.**

# Followup answer

The previous fixed-opponent restriction was substantive: it forced (B_i) to remain unchanged. Once opponents may change, a profitable literal row deviation can be converted into continuation option value without creating any Nash error at the changed row.

There is, however, an exact opponent-aware accounting. The missing quantity is a **residual continuation debt**. Controlling that residual gives a bounded potential theorem; without controlling it, no semantic-potential theorem can cover arbitrary opponent changes.

## 1. Two exact decompositions of semantic debt

For a semantic tail (z=(u,b)\in\mathcal K) and an arbitrary product root (y), let (T_yz) denote the rooted semantic pair. No coordinate of (y) is fixed; in particular, every opponent may change.

Write

[
c(y)=\prod_{j\in I}y_j(\mathrm C).
]

For player (j), abbreviate

[
\begin{aligned}
Q_j^y&=Q_j(y_{-j}),\
C_{j,u}^y&=C_j(y_{-j};u_j),\
C_{j,b}^y&=C_j(y_{-j};b_j).
\end{aligned}
]

Besides the literal row error

[
\rho_j(y;z)
===========

## \max{Q_j^y,C_{j,u}^y}

\bigl[y_j(\mathrm Q)Q_j^y+y_j(\mathrm C)C_{j,u}^y\bigr],
\tag{1}
]

define the cap-Nash error

[
\eta_j(y;z)
===========

## \max{Q_j^y,C_{j,b}^y}

\bigl[y_j(\mathrm Q)Q_j^y+y_j(\mathrm C)C_{j,b}^y\bigr],
\tag{2}
]

and the hidden continuation-option surcharge

[
\kappa_j(y;z)
=============

## \max{Q_j^y,C_{j,b}^y}

\max{Q_j^y,C_{j,u}^y}.
\tag{3}
]

All three are nonnegative. The nonnegativity of (\kappa_j) follows from (b_j\ge u_j).

There are two exact debt identities:

[
\boxed{
d_j(T_yz)=\rho_j(y;z)+\kappa_j(y;z)
}
\tag{4}
]

and

[
\boxed{
d_j(T_yz)=\eta_j(y;z)+c(y)d_j(z).
}
\tag{5}
]

Indeed,

[
d_j(T_yz)
=========

## \max{Q_j^y,C_{j,b}^y}

F_j(y;u_j),
]

which gives (4). For (5), add and subtract the prescribed mixed action evaluated against the cap (b_j). The resulting continuation term is

[
\begin{aligned}
y_j(\mathrm C)\bigl(C_{j,b}^y-C_{j,u}^y\bigr)
&=
y_j(\mathrm C)
\prod_{\ell\ne j}y_\ell(\mathrm C)(b_j-u_j)\
&=c(y)d_j(z).
\end{aligned}
]

These identities already include arbitrary changes of opponents at the root and arbitrary changes of all players in the tail.

### Immediate one-row comparison

Suppose, after conditioning on reaching the marked row, the source is (T_xz), with literal gain

[
g=\rho_i(x;z)=G/h.
]

Let an arbitrary changed root-tail pair be (T_yw). Then (4) gives the exact equality

[
\boxed{
g
=

d_i(T_xz)-d_i(T_yw)
+\rho_i(y;w)
+\kappa_i(y;w)-\kappa_i(x;z).
}
\tag{6}
]

This is the term missing from the previous answer. Opponent changes are harmless precisely when they do not increase (\kappa_i), or when that increase is paid elsewhere.

In particular, if

[
\kappa_i(y;w)\le \kappa_i(x;z),
\tag{7}
]

then

[
g\le d_i(T_xz)-d_i(T_yw)+\rho_i(y;w).
\tag{8}
]

This already permits:

* a root-only change (y\ne x,\ w=z), including arbitrary opponent-root changes;
* a tail-only change (y=x,\ w\ne z), including arbitrary opponent-tail changes;
* simultaneous changes of root and tail.

But the multirow formulation below is strictly broader: it permits an increase in (\kappa) at one row if the resulting continuation debt is later discharged.

---

## 2. Exact error–residual splitting of an arbitrary changed chronology

Let (\tau) be an arbitrary behavioral profile. It may alter every opponent at the marked root and at every later stage. Let

[
z_s^\tau=(u^s,b^s)
]

be the semantic pair of its suffix beginning at stage (s), and let (y^s) be its product root at that stage. Thus

[
z_s^\tau=T_{y^s}z_{s+1}^\tau.
]

Put

[
C_0^\tau=1,
\qquad
C_s^\tau=\prod_{\ell<s}c(y^\ell).
\tag{9}
]

So (C_s^\tau) is the probability, under (\tau), of reaching stage (s).

Fix a set (J\subseteq I) containing the marked player (i), and define the potential

[
\boxed{
\Phi_J(u,b)=\sum_{j\in J}(b_j-u_j).
}
\tag{10}
]

The choices (J={i}) and (J=I) give respectively

[
\Phi_{{i}}=d_i,
\qquad
\Phi_I=D.
]

For a finite settlement date (m), pass through stages (0,\ldots,m-1) using the cap decomposition (5), and settle at stage (m) using the literal decomposition (4). Define

[
\begin{aligned}
E_{J,m}(\tau)
&=
\sum_{s=0}^{m-1}
C_s^\tau
\sum_{j\in J}\eta_j(y^s;z_{s+1}^\tau)
\
&\quad+
C_m^\tau
\sum_{j\in J}\rho_j(y^m;z_{m+1}^\tau),
\tag{11}[1ex]
R_{J,m}(\tau)
&=
C_m^\tau
\sum_{j\in J}\kappa_j(y^m;z_{m+1}^\tau).
\tag{12}
\end{aligned}
]

Then iteration of (5), followed by (4) at stage (m), gives

[
\boxed{
\Phi_J(Z(\tau))=E_{J,m}(\tau)+R_{J,m}(\tau).
}
\tag{13}
]

Here:

* (E_{J,m}) is a sum of reached cap-Nash errors at the intervening rows, followed by a reached literal Nash error at the settlement row;
* (R_{J,m}) is the debt still hidden in the continuation option when settlement occurs.

There is also an infinite-pass version. Define

[
E_{J,\infty}(\tau)
==================

\sum_{s=0}^{\infty}
C_s^\tau
\sum_{j\in J}\eta_j(y^s;z_{s+1}^\tau),
\tag{14}
]

and

[
R_{J,\infty}(\tau)
==================

\lim_{m\to\infty}C_m^\tau\Phi_J(z_m^\tau).
\tag{15}
]

The limit exists because

[
C_m^\tau\Phi_J(z_m^\tau)
========================

## \Phi_J(Z(\tau))

\sum_{s<m}C_s^\tau\sum_{j\in J}\eta_j(y^s;z_{s+1}^\tau)
]

is nonnegative and decreasing. Again,

[
\boxed{
\Phi_J(Z(\tau))
===============

E_{J,\infty}(\tau)+R_{J,\infty}(\tau).
}
\tag{16}
]

If the changed chronology absorbs almost surely, (C_m^\tau\to0), and the boundedness of (\Phi_J) implies

[
R_{J,\infty}(\tau)=0.
\tag{17}
]

Thus every almost-surely absorbing changed chronology—including one that alters every opponent—is completely accounted for by its Nash–Bellman row errors.

---

## 3. The opponent-aware paid-transport theorem

Let

[
z_{\rm in}=Z(\sigma)
]

be the semantic pair of the original full profile. Since the displayed one-row deviation is legal,

[
G\le d_i(z_{\rm in})\le \Phi_J(z_{\rm in}).
]

Define the source reserve

[
\boxed{
S_J:=\Phi_J(z_{\rm in})-G\ge0.
}
\tag{18}
]

Let (\tau) be a changed profile. It may change all players at and after stage (t); the theorem in fact remains valid even if it also changes earlier roots. Let (z_{\rm out}=Z(\tau)), and choose either a finite or infinite error–residual split

[
\Phi_J(z_{\rm out})=E_J(\tau)+R_J(\tau).
]

Call the transport **(J)-paid** when

[
\boxed{
R_J(\tau)\le S_J.
}
\tag{19}
]

Then

[
\boxed{
G
\le
\Phi_J(z_{\rm in})-\Phi_J(z_{\rm out})
+
E_J(\tau).
}
\tag{20}
]

### Proof

Using (\Phi_J(z_{\rm out})=E_J+R_J),

[
\begin{aligned}
\Phi_J(z_{\rm in})-\Phi_J(z_{\rm out})+E_J
&=
\Phi_J(z_{\rm in})-R_J\
&\ge
\Phi_J(z_{\rm in})-S_J\
&=G.
\end{aligned}
]

No fixed-opponent equality is used. ∎

More strongly, the exact deficit is

[
\boxed{
G-
\bigl[
\Phi_J(z_{\rm in})-\Phi_J(z_{\rm out})+E_J
\bigr]
======

R_J-S_J.
}
\tag{21}
]

Therefore condition (19) is not merely sufficient. For this potential and this row-error account, it is necessary and sufficient.

This is the precise answer to what opponent changes cost: they are free as far as the transport inequality is concerned except for the residual debt (R_J) they leave after the intervening Nash errors have been charged.

---

## 4. Relation to the original reached row

The source reserve has an explicit chronology interpretation.

Let (x^s) be the roots of (\sigma), let (H_s) be the probability of reaching stage (s), and (H_t=h). Apply the finite split to the source, settling at its marked stage (t). For (J\ni i),

[
\begin{aligned}
\Phi_J(z_{\rm in})
&=
\sum_{s<t}H_s
\sum_{j\in J}\eta_j(x^s;z_{s+1}^\sigma)
\
&\quad+
h\sum_{j\in J}
\bigl[
\rho_j(x;z_{t+1}^\sigma)
+
\kappa_j(x;z_{t+1}^\sigma)
\bigr].
\end{aligned}
\tag{22}
]

Since (G=h\rho_i(x;z_{t+1}^\sigma)),

[
\begin{aligned}
S_J
&=
\sum_{s<t}H_s
\sum_{j\in J}\eta_j(x^s;z_{s+1}^\sigma)
\
&\quad+
h\sum_{j\in J\setminus{i}}\rho_j(x;z_{t+1}^\sigma)
+
h\sum_{j\in J}\kappa_j(x;z_{t+1}^\sigma).
\end{aligned}
\tag{23}
]

Thus the reserve consists exactly of:

1. earlier reached cap-Nash errors;
2. the other players’ literal row errors at the marked row, if (J\ne{i});
3. the hidden continuation-option debt at the marked row.

An opponent-changing target may use this reserve, but not more.

For (J={i}) and (t=0), condition (19) reduces to the simple condition

[
R_i(\tau)\le \kappa_i(x;z_{1}^\sigma).
\tag{24}
]

Immediate settlement in the new root-tail pair gives exactly the surcharge-nonincreasing condition (7).

---

## 5. The class contains genuine opponent root and tail changes

The class is not a disguised fixed-opponent class.

### Same root and same continuation

Take (\tau=\sigma) and settle at the marked row. Then its residual is contained in the source reserve by (23). Hence the literal unchanged repair is included.

At (t=0), (J={i}), the split is simply

[
d_i(z_{\rm in})=\rho_i(x;z_1^\sigma)+\kappa_i(x;z_1^\sigma),
]

and (G=\rho_i). Thus the unchanged row gives equality in (20).

### Root-only opponent change

Keep the tail fixed and replace only the product root at stage (t), including any or all opponent probabilities.

A particularly broad subcase is obtained by making some player quit surely at that root. Then the new joint Continue probability is zero. Pass through that root using the cap decomposition. All continuation residual is killed:

[
R_J=0.
]

Consequently the root-only change is automatically paid, independently of how strongly the opponents’ actions alter the collision distribution. The entire cost appears as the cap-Nash error of the changed root.

### Tail-only opponent change

Keep the root at stage (t) fixed and replace the entire continuation after unanimous Continue. Every opponent may change at every future stage.

If the new tail absorbs almost surely, then its survival factor tends to zero and

[
R_{J,\infty}=0.
]

Hence every such tail-only change is paid. More generally, a tail with positive Never probability is still paid whenever its surviving semantic debt fits in the source reserve.

### Simultaneous root and tail changes

Nothing in (11)–(19) requires either component to remain fixed. The changed roots (y^s), collision distributions, continuation payoffs, and continuation envelopes are all unrestricted. Only the final unspent residual is constrained.

---

## 6. Boundedness and telescoping

For each player (j), put

[
\underline r_j
==============

\min\bigl({0}\cup{r_j(S):S\ne\varnothing}\bigr),
]

[
\overline r_j
=============

\max\bigl({0}\cup{r_j(S):S\ne\varnothing}\bigr).
]

Every prescribed payoff and every unilateral best-response payoff lies in

[
[\underline r_j,\overline r_j].
]

Therefore

[
0\le \Phi_J(z)
\le
\sum_{j\in J}(\overline r_j-\underline r_j)
\qquad(z\in\mathcal K).
\tag{25}
]

Now consider a chain of (J)-paid transports

[
z^0\longrightarrow z^1\longrightarrow\cdots\longrightarrow z^N
]

carrying positive tickets (G_0,\ldots,G_{N-1}), with row-error budgets (E_0,\ldots,E_{N-1}). Summing (20),

[
\boxed{
\sum_{k<N}G_k
\le
\Phi_J(z^0)-\Phi_J(z^N)
+
\sum_{k<N}E_k.
}
\tag{26}
]

Hence

[
\sum_{k<N}G_k
\le
\sum_{j\in J}(\overline r_j-\underline r_j)
+
\sum_{k<N}E_k.
\tag{27}
]

If the semantic chronology closes,

[
z^N=z^0,
]

then

[
\boxed{
\sum_{k<N}G_k\le\sum_{k<N}E_k.
}
\tag{28}
]

In particular, an exact closed paid chronology gives

[
0\ge \sum_{k<N}G_k.
]

This is the requested genuine telescoping consequence.

---

## 7. Connection with (D_*)

Taking (J=I) gives

[
\Phi_I=D.
]

For every paid transport,

[
\boxed{
G\le D(z_{\rm in})-D(z_{\rm out})+E_I.
}
\tag{29}
]

If (D(z_{\rm in})=D_*), then (D(z_{\rm out})\ge D_*), so

[
\boxed{
E_I\ge G.
}
\tag{30}
]

Thus no exact paid opponent-changing transport can leave a minimum state. More generally, if

[
D(z_{\rm in})\le D_*+\delta,
]

then

[
E_I\ge G-\delta.
\tag{31}
]

Consequently, producing an exact target chronology with zero residual would give option 1 of the question with coefficient (1):

[
D(z_{\rm out})\le D(z_{\rm in})-G.
]

The obstruction is exactly that an arbitrary opponent change may leave a residual exceeding (D(z_{\rm in})-G).

---

## 8. Periodic Nash–Bellman chronologies

Suppose a Nash–Bellman word of length (L) returns to the same semantic state (z). Let

[
C=\prod_{s<L}c(y^s)
]

be its per-period survival probability, and let

[
e_J
===

\sum_{s<L}C_s
\sum_{j\in J}\eta_j(y^s;z_{s+1})
]

be its reached cap-error over one period.

The exact debt recursion over a period is

[
\Phi_J(z)=e_J+C\Phi_J(z).
\tag{32}
]

If (C<1), infinite repetition has

[
R_{J,\infty}=0,
\qquad
E_{J,\infty}=\frac{e_J}{1-C}.
]

A positive source ticket transported around the closed cycle therefore satisfies

[
G\le \frac{e_J}{1-C},
]

or equivalently

[
\boxed{
(1-C)G\le e_J.
}
\tag{33}
]

If every root is exact cap-Nash, (e_J=0), and hence (G=0).

If (C=1), every root in the period is unanimous Continue. Then the infinite residual is

[
R_{J,\infty}=\Phi_J(z).
]

For a positive ticket,

[
S_J=\Phi_J(z)-G<R_{J,\infty},
]

so the chronology is not paid. This is precisely the positive-debt all-Continue plateau; it is not a Nash-error telescoping chronology.

---

## 9. Why the residual cannot be omitted

A two-player example shows that changing an opponent can move all literal gain into hidden continuation value while preserving the same semantic pair and creating zero row error.

Let

[
I={1,2},
]

and set

[
r({1})=(0,0),\qquad
r({2})=(0,0),\qquad
r({1,2})=(1,0).
]

Consider the source profile (\sigma) whose first root is

[
(\mathrm C,\mathrm Q).
]

Then play terminates with coalition ({2}), so

[
U(\sigma)=(0,0).
]

Player (1) can switch to Quit, producing coalition ({1,2}), and gain (1). Thus

[
B(\sigma)=(1,0),
\qquad
d_1(\sigma)=1,
\qquad
G=1.
]

At this source row,

[
\rho_1=1,
\qquad
\kappa_1=0.
]

Now define (\tau) by inserting a unanimous-Continue root and then following (\sigma):

[
(\mathrm C,\mathrm C)\quad\text{followed by }\sigma.
]

The semantic pair is unchanged:

[
U(\tau)=(0,0),
\qquad
B(\tau)=(1,0).
]

At the newly inserted row, however,

[
Q_1=0,
\qquad
C_{1,u}=0,
\qquad
C_{1,b}=1.
]

Therefore

[
\rho_1'=0,
\qquad
\eta_1'=0,
\qquad
\kappa_1'=1.
]

The changed opponent—player (2)—has moved from Quit to Continue. The immediate gain has disappeared, the new root is exact cap-Nash, and the semantic state is identical, but one unit of residual continuation debt remains.

Any inequality that treats the inserted exact row as the whole transport and omits residual debt would say

[
1
\le
\Phi(z)-\Phi(z)+0
=================

0
]

for every potential depending only on the semantic pair.

The paid accounting instead records

[
S_1=0,
\qquad
R_1=1,
]

so the transport is correctly rejected as unpaid. If one unfolds the tail by one more row, the original literal error (1) reappears in (E), and the accounting becomes valid.

This example has (D_*=0); it is not a counterexample under the global positive-gap hypothesis. Its role is to prove that the local opponent-changing transport identity necessarily contains a residual term. The assumption (D_*>0) does not alter identities (4)–(5); eliminating this mechanism in the hypothetical counterexample regime requires an additional global argument forcing (R\le S).

## Conclusion

The fully opponent-aware statement is:

[
\boxed{
G
\le
\Phi_J(z_{\rm in})-\Phi_J(z_{\rm out})
+\sum_s\varepsilon_s
}
]

for every changed-root or changed-tail chronology—allowing arbitrary opponent changes—whose unspent residual semantic debt is at most

[
\Phi_J(z_{\rm in})-G.
]

Here

[
\Phi_J(z)=\sum_{j\in J}(b_j-u_j)
]

is nonnegative and bounded on (\mathcal K), and the (\varepsilon_s) are reached literal or cap-Nash errors of the intervening rows.

For this potential and error account, the condition is sharp:

[
G-
\left[
\Phi_J(z_{\rm in})-\Phi_J(z_{\rm out})
+\sum_s\varepsilon_s
\right]
=======

## R_{\rm out}

\bigl(\Phi_J(z_{\rm in})-G\bigr).
]

Thus opponent changes are not themselves the obstruction. The obstruction is precisely their ability to leave more hidden continuation debt than the source gain leaves available as reserve.

# Followup 2

The correct status is **an obstruction identity, not a transport theorem**.

The substantive statement proved was

[
G-\Bigl(\Phi(z_{\rm in})-\Phi(z_{\rm out})+\sum_s\varepsilon_s\Bigr)
====================================================================

R_{\rm out}-\bigl(\Phi(z_{\rm in})-G\bigr),
\tag{1}
]

where (R_{\rm out}) is the unspent continuation debt. This identifies exactly what opponent changes can do: they can convert the reached-row gain into future option value. But declaring a transport “paid” when

[
R_{\rm out}\le \Phi(z_{\rm in})-G
\tag{2}
]

does not establish (2); it merely names the condition equivalent to the desired inequality.

The previous response therefore established only:

1. arbitrary opponent changes admit exact debt accounting;
2. root error, tail error, and surviving continuation debt can be separated;
3. a bounded potential telescopes once the residual is independently controlled.

It did **not** establish that any useful opponent-changing transport has the required residual control.

## Why the gap is especially sharp on the minimum fiber

Take (\Phi=D) and suppose

[
D(z_{\rm in})=D_*,
\qquad
G>0.
]

The available reserve is

[
S=D_*-G.
]

For any exact changed chronology, the accumulated Nash error is zero, so its decomposition is

[
D(z_{\rm out})=R_{\rm out}.
]

Since (z_{\rm out}\in\mathcal K),

[
R_{\rm out}=D(z_{\rm out})\ge D_*.
]

Consequently,

[
R_{\rm out}-S
\ge
D_*-(D_*-G)
===========

G.
\tag{3}
]

Thus no exact transport starting at a minimum state can be “paid” in the sense of the previous answer. The accounting inequality becomes

[
G\le D_*-D(z_{\rm out}),
]

which is impossible because (D(z_{\rm out})\ge D_*).

For an approximate changed chronology, the same calculation gives

[
\sum_s\varepsilon_s\ge G.
\tag{4}
]

So the certificate says that any paid opponent-changing transport from the minimum fiber must already spend at least the entire gain as Nash error. That cannot produce descent, an exact return, or terminal (\varepsilon)-Nash profiles with (\varepsilon\to0).

## The actual unresolved statement

Let

[
\Delta(\mathcal T)
:=
R_{\rm out}(\mathcal T)
-----------------------

\bigl(D(z_{\rm in})-G\bigr)
\tag{5}
]

for an opponent-changing transport (\mathcal T). The exact accounting is

[
G
=

D(z_{\rm in})-D(z_{\rm out})
+
\sum_s\varepsilon_s
+
\Delta(\mathcal T).
\tag{6}
]

The hard problem is to eliminate or exploit the positive defect (\Delta). One needs a theorem of the following form:

[
\boxed{
\begin{array}{l}
\text{Given a reached-row gain }G>0,\text{ either}[1mm]
\text{(a) some changed transport has }\Delta\le0;\
\text{(b) the persistent defects }\Delta>0\text{ can be carried around a finite or periodic}\
\qquad\text{chronology and cancel telescopically;}\
\text{(c) persistent residual option value yields terminal }\varepsilon\text{-Nash profiles.}
\end{array}}
\tag{7}
]

Nothing in the previous response proves any branch of (7).

## Why a different scalar potential alone is unlikely to fix this

An opponent change can replace an immediate deviation opportunity by an equivalent future opportunity while preserving the semantic pair. On an all-Continue Nash–Bellman prefix,

[
T_{\mathrm{allC}}(u,b)=(u,b)
]

whenever (b_j\ge r_j({j})) for every (j). Inserting such a root:

* changes the chronology and potentially all displayed opponent actions;
* preserves the semantic state;
* has zero cap-Nash error;
* transfers the relevant debt entirely into the tail.

Hence any inequality using only a bounded state potential and the errors of the newly inserted exact rows would read

[
G
\le
\Phi(z)-\Phi(z)+0,
]

unless the future residual is retained as a separate charge. This is not peculiar to the choice (\Phi=D) or (\Phi=d_i); it is an observability problem. The semantic state records the option value but not the chronological location where that value will become an explicit row gain.

## Precise conclusion

The opponent-aware accounting is useful only as the following reduction:

[
\boxed{
\text{opponent-changing transport problem}
\quad\Longleftrightarrow\quad
\text{residual continuation-debt discharge problem}.
}
]

It does not solve that discharge problem. In particular, it provides neither

[
D(z')\le D_*-\alpha G,
]

nor terminal (\varepsilon)-Nash profiles, nor a closed chronology yielding

[
0\ge \alpha G.
]

Calling it a negative solution was therefore too strong. It is a sharp localization of the missing step: **one must show that opponent-created continuation option value cannot remain indefinitely unspent, or else convert its persistence into equilibrium or a closed-charge contradiction.**

## Last followup

That is the decisive correction. The previous “paid transport” construction is **not** a solution of either requested branch. It merely rewrites the desired inequality as a condition on the residual, and on the minimum fiber that condition forces the gain to reappear as Nash error.

## 1. The exact minimum-fiber no-go identity

Suppose the source semantic state satisfies

[
D(z_{\rm in})=D_*.
]

For an arbitrary opponent-changing chronology, let

[
E:=\sum_s\varepsilon_s\ge 0
]

be its accumulated reached cap-Nash errors, and let (R\ge0) be its surviving tail debt. The exact Bellman accounting is

[
D(z_{\rm out})=E+R.
\tag{1}
]

Now suppose one somehow proves the residual reduction

[
R\le D_*-\alpha G
\tag{2}
]

for some (\alpha>0). Then

[
\boxed{
E-\alpha G
==========

\bigl[D(z_{\rm out})-D_*\bigr]
+
\bigl[D_*-\alpha G-R\bigr].
}
\tag{3}
]

Both terms on the right are nonnegative. Therefore

[
\boxed{E\ge \alpha G.}
\tag{4}
]

More strongly, if either the target lies strictly above the minimum fiber or the residual bound is strict, then

[
E>\alpha G.
]

Thus a reduction of the residual by (\alpha G) does not reduce total debt. It creates at least (\alpha G) of explicit row error.

Equivalently, define the residual discharge

[
\delta:=D_*-R.
]

Then (1) gives

[
\boxed{
E-\delta=D(z_{\rm out})-D_*\ge0.
}
\tag{5}
]

Hence

[
\delta\le E.
\tag{6}
]

Every unit removed from the residual ledger must be entered into the Nash-error ledger before the result can be a semantic state in (\mathcal K).

The best possible case is

[
R=D_*-\alpha G,\qquad
E=\alpha G,\qquad
D(z_{\rm out})=D_*.
\tag{7}
]

That is pure conversion of residual debt into explicit error, with no descent at all.

## 2. The proposed “paid” condition was tautological

For the total-debt potential (\Phi=D),

[
\alpha G
\le
D(z_{\rm in})-D(z_{\rm out})+E
\tag{8}
]

and (D(z_{\rm out})=E+R) imply

[
D(z_{\rm in})-D(z_{\rm out})+E
==============================

D(z_{\rm in})-R.
]

Therefore

[
\boxed{
\alpha G
\le
D(z_{\rm in})-D(z_{\rm out})+E
\iff
R\le D(z_{\rm in})-\alpha G.
}
\tag{9}
]

Defining the admissible transports by the right-hand condition is simply defining them to be the transports for which the desired inequality holds. It gives no independent strategic mechanism.

At a minimum state, (9) combines with (4) to say only

[
\alpha G\le E.
\tag{10}
]

So the bounded-potential inequality has no useful telescoping content beyond the accumulated error.

## 3. Consequences for the three requested outcomes

### Descent

Using (1),

[
D_*-D(z_{\rm out})
==================

# (D_*-R)-E

\delta-E
\le0.
\tag{11}
]

Residual control alone therefore cannot produce

[
D(z_{\rm out})\le D_*-\alpha G.
]

To obtain actual descent one would need

[
\delta-E\ge\alpha G,
\tag{12}
]

or equivalently

[
E+R\le D_*-\alpha G.
\tag{13}
]

But (E+R=D(z_{\rm out})\ge D_*). Thus proving (12) for an actual reachable chronology would already be the desired contradiction. It cannot follow from the debt decomposition itself.

### Terminal (\varepsilon)-Nash profiles

Suppose the changed chronologies have errors (E_n\to0). Equation (5) gives

[
D_*-R_n\le E_n,
]

and hence

[
R_n\ge D_*-E_n\longrightarrow D_*.
\tag{14}
]

Thus low-error transports cannot discharge a fixed positive fraction of (G). In particular, for fixed (G>0),

[
R_n\le D_*-\alpha G
]

is impossible once (E_n<\alpha G).

So the residual argument cannot approach equilibrium: as the Nash errors vanish, essentially all of the positive minimum debt must survive in the tail.

### Closed or periodic return

If the changed chronology returns to its initial semantic state, then

[
D(z_{\rm out})=D(z_{\rm in})=D_*.
]

Equation (1) gives

[
E+R=D_*.
]

Consequently, the residual bound (2) implies

[
E\ge\alpha G.
\tag{15}
]

The purported telescoping inequality reduces to

[
\alpha G\le E,
]

not

[
0\ge\alpha G.
]

An exact return would have (E=0), but then (R=D_*), so the residual bound fails. Exactness and positive residual discharge are mutually exclusive unless the assumptions have already been contradicted by some additional theorem.

## 4. The same issue near, rather than exactly on, the minimum fiber

Let

[
D(z_{\rm in})=D_*+e,
\qquad e\ge0.
]

Suppose

[
R\le D(z_{\rm in})-\alpha G.
]

Set

[
s:=D(z_{\rm in})-\alpha G-R\ge0.
]

Then

[
\boxed{
E
=

\alpha G-e
+
\bigl[D(z_{\rm out})-D_*\bigr]
+s.
}
\tag{16}
]

Therefore

[
E\ge \alpha G-e.
\tag{17}
]

This has a clear interpretation:

* if (e<\alpha G), most of the transported gain must become error;
* if (e\ge\alpha G), an exact transport can at most spend the source’s pre-existing excess above (D_*);
* it still cannot cross below (D_*).

Thus away from the minimum fiber, a residual reduction can represent ordinary descent toward the minimum. It does not derive anything from the local gain that exceeds the already available excess (e).

## 5. Proper-subset debt potentials merely move debt between players

The previous response also considered

[
\Phi_J(z)=\sum_{j\in J}d_j(z)
]

for (J\subsetneq I). Such a potential can decrease under an exact opponent-changing transport, but this does not help with (D_*).

At a minimum state,

[
D(z_{\rm out})-D(z_{\rm in})\ge0.
]

Writing (J^c=I\setminus J),

[
\bigl[\Phi_J(z_{\rm out})-\Phi_J(z_{\rm in})\bigr]
+
\bigl[\Phi_{J^c}(z_{\rm out})-\Phi_{J^c}(z_{\rm in})\bigr]
\ge0.
]

Hence, if

[
\Phi_J(z_{\rm out})
\le
\Phi_J(z_{\rm in})-\alpha G,
]

then necessarily

[
\Phi_{J^c}(z_{\rm out})
\ge
\Phi_{J^c}(z_{\rm in})+\alpha G.
\tag{18}
]

The gain has been transported into other players’ debt. Opponent changes can therefore use three interchangeable stores:

[
\text{marked-player debt},\qquad
\text{other-player debt},\qquad
\text{explicit Nash error}.
]

A potential tracking only one store does not produce global descent.

## 6. What an actual opponent-changing transport theorem must do

Residual control is not the missing theorem. The missing theorem must prevent the gain from being absorbed into **either**

1. Nash errors;
2. surviving tail debt;
3. other players’ debt.

There are only a few structurally different ways to accomplish this.

### Net-discharge theorem

One could produce a chronology satisfying both

[
R\le D_*-\alpha G
]

and an independent error estimate

[
E\le \beta G,
\qquad
\beta<\alpha.
]

Then

[
D(z_{\rm out})
==============

E+R
\le
D_*-(\alpha-\beta)G,
]

contradicting minimality.

The crucial word is **independent**. The error upper bound cannot be derived from the same debt decomposition, because that decomposition gives the opposite estimate (E\ge\alpha G).

### Gain-preserving transport

Instead of treating the residual as debt to be discharged, one could extract from it a new literal reached-row gain (G') together with a concrete deviation witness. The transport would have to carry

[
(\text{state},\text{marked deviation},\text{positive charge})
]

rather than only ((u,b)).

The continuation option would then become a new ticket, not a Nash error. A finite return of the marked ticket could potentially yield the requested signed telescoping contradiction.

This requires more information than ((u,b)). The coordinate (b_i) records only the value of an optimal deviation; it does not record:

* which behavioral deviation realizes or approximates it;
* at which row its advantage appears;
* on which quitting coalitions the advantage is supported;
* how that deviation’s payoff changes when opponents change.

Those are precisely the data lost in a semantic-only transport.

### Persistent-residual-to-equilibrium theorem

A third possibility is to prove that if low-error opponent-changing transports necessarily retain

[
R\approx D_*,
]

then the persistent tail option can be realized by a consistent family of strategies yielding terminal (\varepsilon)-Nash profiles.

That would be a separate compactness or strategy-selection theorem. The identity (D=E+R) does not provide it.

## 7. Correct status of the follow-up

The valid result is limited to:

[
\text{opponent changes}
\quad\Longrightarrow\quad
\text{exact decomposition into error, residual debt, and cross-player debt}.
]

It identifies where the gain can disappear. It does not prevent disappearance into any of those stores.

More precisely:

[
\boxed{
\text{Residual discharge at a minimum state is bounded above by the Nash error created.}
}
]

Therefore the previous residual-bound proposal does not merely lack a proof. **Even granted, it is insufficient unless accompanied by a strictly smaller independent error bound.**

So Question 188 remains unresolved by this line of accounting. A genuine solution must transport the **literal deviation witness or its eventwise charge**, rather than attempting to transport only the scalar semantic debt.
