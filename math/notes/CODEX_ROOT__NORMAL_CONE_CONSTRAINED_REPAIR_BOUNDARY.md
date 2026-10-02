# Normal-cone constrained repair boundary for endpoint monodromy

Author: external proposal supplied in conference; recorded by CODEX_ROOT

## Current status

This is a proof draft and a precise producer target, not an export. It corrects
the false inference that a positive prescribed clock implies endpoint
complementarity. Exact complementarity is available only on an interior
constrained face; a binding lower face instead supplies exact normal work and
an actual own-strategy debt drain.

The supplied constrained-repair consumer is plausible ordinary mathematics
under its explicit quantitative hypotheses. The missing theorem is production
of such a repair, with cross-coordinate leakage control, from a literal
common-host or complementary-pair endpoint cycle at a positive-minimum source.

## 1. Corrected anchor--clock lemma

Let \(s_o=r_o(\{o\})\). Suppose pinned source values satisfy

\[
u_{n,o}-s_o\ge\Delta>0
\tag{1}
\]

and the exact block account has the form

\[
(\kappa_n+a_n)(v_{n,o}-s_o)
=
\kappa_n(u_{n,o}-s_o)+r_n,
\qquad
\frac{|r_n|}{\kappa_n+a_n}\to0.
\tag{2}
\]

Here \(a_n>0\) is the owner exposure and \(\kappa_n\) is the source pin or seam
scale. If

\[
v_{n,o}-s_o\to0,
\tag{3}
\]

then

\[
\Delta\frac{\kappa_n}{\kappa_n+a_n}
\le
|v_{n,o}-s_o|
+
\frac{|r_n|}{\kappa_n+a_n},
\]

so

\[
\frac{\kappa_n}{a_n}\to0.
\tag{4}
\]

Condition (3) does not follow from \(a_n>0\). It follows when the owner is
interior in an exact Nash row, or when the endpoint error is
\(o(a_n)\). Ordinary endpoint error tending to zero is insufficient.

If opponent exposure \(b_n=o(a_n)\) and all remaining block error is also
\(o(a_n)\), choose \(L_n\) with

\[
L_na_n\to\infty,
\qquad
L_n(b_n+e_n+\kappa_n)\to0.
\]

Repeating the finite block \(L_n\) times and then invoking an
\(o\)-punishment makes every nonowner's probability of reaching the suffix
vanish, while punishment normality controls the owner. This is the valid
finite-prefix exceptional-owner consumer.

## 2. Exact finite constrained repairs

Fix an actual terminal tail, a finite prefix horizon \(H\), one free player
\(f\), and a lower tremble \(\ell>0\). At every prefix row constrain

\[
q_f\in[0,1],
\qquad
q_i\in[\ell,1]\quad(i\ne f).
\tag{5}
\]

For a fixed continuation payoff, the one-row product game is continuous and
affine in each player's own coordinate. A mixed Nash point on these compact
intervals exists. Backward iteration over the finite horizon constructs an
actual source-matched block with exact Bellman recursion and exact constrained
row Nash conditions.

Let

\[
g_{t,i}=Q_{t,i}-C_{t,i}
\]

be Quit minus Continue at a row. Exact constrained Nash gives the normal-cone
conditions

\[
\begin{array}{rcl}
q_{t,i}=\ell_i&\Longrightarrow&g_{t,i}\le0,\\
\ell_i<q_{t,i}<1&\Longrightarrow&g_{t,i}=0,\\
q_{t,i}=1&\Longrightarrow&g_{t,i}\ge0,
\end{array}
\tag{6}
\]

where \(\ell_f=0\) and \(\ell_i=\ell\) otherwise.

At a binding lower face, deleting the constrained tremble is a legal
own-strategy change with exact local gain

\[
\ell_i(-g_{t,i})\ge0.
\tag{7}
\]

Thus a positive clock is classified correctly:

- interior exposure gives exact complementarity;
- upper-face exposure is pure Quit; and
- lower-face exposure carries exact normal work.

## 3. Unique-owner scaling

Let \(w_{n,t}\) be row reach and put

\[
A_{n,i}=\sum_{t<H_n}w_{n,t}q_{n,t,i},
\qquad
W_n=\sum_{t<H_n}w_{n,t}.
\]

Suppose \(p\) is the unique exposure owner:

\[
A_{n,j}=o(A_{n,p})\quad(j\ne p).
\tag{8}
\]

Every constrained player satisfies \(A_{n,j}\ge\ell_nW_n\). If at least one
constrained player remains besides \(p\), then

\[
\ell_nW_n=o(A_{n,p}).
\tag{9}
\]

The total lower-face normal work attributable to \(p\) is bounded by

\[
\sum_{t:q_{n,t,p}=\ell_n}
w_{n,t}\ell_n|g_{n,t,p}|
\le2M\ell_nW_n
=o(A_{n,p}).
\tag{10}
\]

Interior rows have zero endpoint difference. Under the stated unique-owner
and bounded-reward estimates, upper-face rows evaluate at the singleton anchor
up to \(o(A_{n,p})\). Hence the owner endpoint error is
\(o(A_{n,p})\), except when the owner is the only constrained player. In that
last case freeing it exposes exact complementarity or the binding normal work
directly.

This is the noncircular replacement for “positive clock implies
complementarity.”

## 4. Exact periodic lower-face debt drain

At one recurring phase, hold all opponents and the rest of the period fixed.
Let \(q\) be the player's Quit probability, \(Q\) its payoff upon quitting,
\(C\) its expected absorbing payoff after continuing and before return, and
\(S<1\) the probability of returning to the same phase. Then

\[
V(q)
=
\frac{qQ+(1-q)C}{1-(1-q)S}.
\tag{11}
\]

Writing \(N=Q(1-S)-C\), direct subtraction gives

\[
V(q)-V(0)
=
\frac{qN}
{(1-S)(1-(1-q)S)}.
\tag{12}
\]

If a constrained equilibrium selects \(q=\ell\) at the lower face, then
\(N\le0\), and removing the tremble gives exact gain

\[
V(0)-V(\ell)
=
\frac{\ell(-N)}
{(1-S)(1-(1-\ell)S)}.
\tag{13}
\]

Only that player's strategy changes, so its behavioral cap is unchanged and
its terminal debt falls by exactly (13).

## 5. Supplied-chain support descent

Let \(z_*\) be a minimum point and
\(A=\{i:d_i(z_*)>0\}\). Suppose actual semantic chains
\(z_{n,0},\ldots,z_{n,T_n}\) start near \(z_*\), and while
\(d_p>C_0a_n\) satisfy uniformly

\[
d_p(z_{n,m+1})
\le d_p(z_{n,m})-ca_n+Ca_n^2,
\tag{14}
\]

\[
D(z_{n,m+1})
\le D(z_{n,m})+C_Da_n^2,
\tag{15}
\]

and, for initially inactive \(q\),

\[
d_q(z_{n,m+1})
\le d_q(z_{n,m})+a_n\rho_n,
\qquad \rho_n\to0.
\tag{16}
\]

Assume the estimates persist for \(O(a_n^{-1})\) steps. Stop when
\(d_p\le C_0a_n\). Then the stopping time is \(O(a_n^{-1})\);
the total-debt increase is \(O(a_n)\); initially inactive debts remain
\(o(1)\); and \(d_p\to0\). Every semantic cluster point \(z'\) satisfies

\[
D(z')=D_*,
\qquad
\operatorname{supp}_+d(z')
\subseteq
\operatorname{supp}_+d(z_*)\setminus\{p\}.
\tag{17}
\]

The existing minimum-fiber re-extraction machinery can consume this supplied
support-drop endpoint. The theorem does not produce estimates (14)--(16).

## 6. Horizontal cycles do not produce the repair formally

There are four-player product-root gain functions with a strict common-host
pure endpoint cycle but only all-Continue as a mixed Nash root. A representative
family is

\[
G_0(x)=2\left(1-\prod_{j=1}^3(1-x_j)\right)-1,
\]

\[
G_1(x)=2x_0x_3(1-x_2)-1,
\quad
G_2(x)=2x_0x_1(1-x_3)-1,
\quad
G_3(x)=2x_0x_2(1-x_1)-1.
\tag{18}
\]

The pure coalitions have a strict common-host cycle, while multiplying the
necessary positive-coordinate Nash inequalities contradicts
\(\prod_{j=1}^3x_j(1-x_j)\le(1/4)^3\). Thus all outsiders Continue, and then
player zero also Continues.

These gains can be realized by coalition reward differences. The resulting
all-Continue profile is an exact equilibrium, so its minimum debt is zero.
The example does not refute a positive-minimum producer. It proves only that
a horizontal common-host cycle does not by itself force a nontrivial
product-root repair.

## Exact remaining producer

For a source-anchored constrained repair define cumulative lower-face normal
work

\[
\mathcal W_n
=
\sum_{t,i:q_{n,t,i}=\ell_{n,i}}
w_{n,t}\ell_{n,i}(-g_{n,t,i}).
\]

The remaining theorem is:

\[
\boxed{
\begin{array}{c}
\text{literal common-host or complementary-pair endpoint cycle}\\
+\text{ positive-minimum actual-source provenance}\\
\Longrightarrow\\
\text{a source-anchored exact constrained repair with}\\
\mathcal W_n=o(\text{exposure}),\\
\text{or an active lower-face drain satisfying (14)--(16).}
\end{array}}
\tag{19}
\]

The first branch feeds the anchor--clock punishment consumer. The second feeds
minimum-fiber support descent.

The missing quantitative step is cross-coordinate leakage control:

\[
D_{\rm after}\le D_{\rm before}+O(a_n^2),
\qquad
d_q^{\rm after}\le d_q^{\rm before}+o(a_n)
\]

for initially inactive coordinates, uniformly through
\(O(a_n^{-1})\) repetitions.

## Nonclaims

This note does not:

- produce the constrained repair from an atlas cycle;
- prove the leakage estimates;
- consume common-host or complementary-pair monodromy;
- establish a new well-founded rank without the supplied chain estimates; or
- prove terminal approximation or uniform-payoff existence.
