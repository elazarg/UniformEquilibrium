The hinge is whether the target-side exact charge is **renewable**. The Bellman identities show that it need not be: repeated exact-root charges are summable under global minimality, while the same-source law contribution can survive with a positive floor. Thus alternative 1 reduces to alternatives 2 or 3, but it does not itself eliminate the chamber.

Here is the precise reduction.

## 1. Root calculus

For a product root \(q=(q_i)_{i\in I}\), write

$$
c(q)=\prod_i(1-q_i),
\qquad
s_i(q)=\prod_{k\ne i}(1-q_k).
$$

Thus \(c(q)\) is joint survival through the row, whereas \(s_i(q)\) is survival after deleting player \(i\).

For a continuation payoff \(v\), let \(F_i(q;v)\) be player \(i\)'s prescribed one-row payoff, including continuation \(v_i\) if everyone continues. Let

$$
G_i(q_{-i};v_i)
$$

be the maximum of the one-row Quit value and the one-row Continue value, where Continue leads to \(v_i\) if all opponents continue. For a tail semantic pair \(y=(u,b)\), prefixing \(q\) gives

$$
u_i'=F_i(q;u),
\qquad
b_i'=G_i(q_{-i};b_i).
$$

Define the local cap regret

$$
\ell_i(q;b)
  :=G_i(q_{-i};b_i)-F_i(q;b)\ge 0.
$$

Because replacing \(u_i\) by \(b_i\) in the prescribed continuation affects \(F_i\) only on joint survival,

$$
\boxed{
d_i(q\star y)=\ell_i(q;b)+c(q)d_i(y).
}
\tag{1}
$$

Hence, with \(L(q;b)=\sum_i\ell_i(q;b)\),

$$
\boxed{
D(q\star y)=L(q;b)+c(q)D(y).
}
\tag{2}
$$

If \(q\) is an exact product root against \(b\), then \(\ell_i(q;b)=0\) for every \(i\), and therefore

$$
\boxed{
d(q\star y)=c(q)d(y),\qquad
D(q\star y)=c(q)D(y).
}
\tag{3}
$$

This identity uses joint survival \(c(q)\), not any deleted-player survival.

## 2. The full-debt minimum is rigid on the whole debt box

Write \(x=(u,b)\). From (F3),

$$
u_i-r_i(\{i\})
  =b_i-r_i(\{i\})-d_i
  \ge D_*-d_i
  =\sum_{k\ne i}d_k>0.
\tag{4}
$$

Consequently all Continue is a strict root not only against \(b\), but also against \(u\).

There is a stronger fact.

### Debt-box rigidity lemma

For every vector \(v\) satisfying

$$
u_i\le v_i\le b_i\qquad(i\in I),
$$

the all-Continue root is the **only** product Nash root of the one-stage game with continuation \(v\).

#### Proof

Let \(q\) be a product Nash root against \(v\), and prefix it to \(x\). Since increasing player \(i\)'s continuation from \(v_i\) to \(b_i\) can increase their one-row best-response value by at most \(s_i(q)(b_i-v_i)\),

$$
G_i(q_{-i};b_i)
 \le G_i(q_{-i};v_i)+s_i(q)(b_i-v_i).
$$

Since \(q\) is Nash against \(v\),

$$
G_i(q_{-i};v_i)=F_i(q;v).
$$

Also,

$$
F_i(q;u)=F_i(q;v)-c(q)(v_i-u_i).
$$

Therefore

$$
d_i(q\star x)
 \le s_i(q)(b_i-v_i)+c(q)(v_i-u_i).
\tag{5}
$$

Writing \(v_i=u_i+\lambda_i d_i\), with \(0\le\lambda_i\le1\), gives

$$
d_i(q\star x)
 \le
\bigl(s_i(q)(1-\lambda_i)+c(q)\lambda_i\bigr)d_i
\le s_i(q)d_i.
\tag{6}
$$

If \(q\ne0\), choose \(k\) with \(q_k>0\). For every \(i\ne k\),

$$
s_i(q)\le 1-q_k<1.
$$

All four debts at \(x\) are positive, so (6) yields

$$
D(q\star x)<\sum_i d_i=D_*,
$$

contradicting global minimality. Hence \(q=0\). ∎

In particular:

$$
\boxed{
\text{all Continue is the unique exact root both at }u\text{ and at }b.
}
\tag{7}
$$

Thus no direct one-stage-root contradiction follows from (F1)–(F3). On the contrary, those hypotheses produce an entire Nash-rigid box between \(u\) and \(b\).

## 3. What the exact-root charge in alternative 1 actually does

Let \(R^{(0)}\) be a response endpoint with \(d_j(R^{(0)})\) small, and let \(A^{(0)}\) be its same-source sibling. Recursively choose a maximal-absorption exact product root \(q_m\) at the literal cap of \(R^{(m)}\), and prefix the same root to both siblings:

$$
R^{(m+1)}=q_m\star R^{(m)},
\qquad
A^{(m+1)}=q_m\star A^{(m)}.
$$

Put

$$
c_m=c(q_m),\qquad
P_m=\prod_{\ell<m}c_\ell.
$$

By (3),

$$
D(R^{(m)})=P_mD(R^{(0)}),
\qquad
d_j(R^{(m)})=P_m d_j(R^{(0)}).
\tag{8}
$$

Because every actual profile and every semantic limit has debt at least \(D_*\),

$$
P_mD(R^{(0)})\ge D_*.
$$

Since \(D(R^{(0)})\le 8M\),

$$
\boxed{
P_m\ge \frac{D_*}{D(R^{(0)})}
       \ge\frac{D_*}{8M}>0.
}
\tag{9}
$$

If \(\chi\) is the retained signed terminal-law contribution between the two siblings, then prefixing the same root adds identical root-absorption law to both endpoints. Hence

$$
\chi_m=P_m\chi_0.
\tag{10}
$$

So the signed contribution also has a positive floor.

Writing \(a_m=1-c_m\), (9) implies

$$
\sum_m a_m<\infty,
\qquad
a_m\longrightarrow0.
\tag{11}
$$

Moreover, the exact charges telescope:

$$
\sum_{m<N} a_mD(R^{(m)})
 =
\sum_{m<N}\bigl(D(R^{(m)})-D(R^{(m+1)})\bigr)
 =
D(R^{(0)})-D(R^{(N)}).
\tag{12}
$$

Therefore the total exact charge is bounded by

$$
D(R^{(0)})-D_*.
$$

There are now precisely two possibilities:

$$
D(R^{(m)})\longrightarrow D_*,
$$

in which case \(d_j\to0\) and the positive same-source law marker survives, giving the advertised reset-rigid limit; or

$$
D(R^{(m)})\longrightarrow D_\infty>D_*,
\tag{13}
$$

while the maximal selected absorptions tend to zero and the signed contribution remains nonzero. This is exactly the strictly off-minimum two-level inert state.

Thus alternative 1 is rigorously reduced to alternatives 2 or 3. It is not by itself a terminal consumer or a well-founded descent.

A scalar regression illustrates the issue. Take \(D_*=1\), \(D(R^{(0)})=2\), and

$$
c_m=\exp(-2^{-m-3}).
$$

Then

$$
P_\infty
 =\exp\left(-\sum_{m\ge0}2^{-m-3}\right)
 =e^{-1/4},
$$

and hence

$$
D_\infty=2e^{-1/4}>1,
\qquad
a_m\to0,
\qquad
\chi_\infty=e^{-1/4}\chi_0\ne0.
$$

This is not a reward-table counterexample. It shows that the scalar exact-charge argument permits precisely the off-minimum regression and cannot serve as a rank.

## 4. Nash roots against the actual payoff also do not close the branch

There is a second useful prefix operation. Let \(y=(u,b)\), with debt vector \(d=b-u\), and let \(q\) be a product Nash root against the **actual** continuation payoff \(u\). Then

$$
G_i(q_{-i};b_i)
 \le G_i(q_{-i};u_i)+s_i(q)d_i
 =F_i(q;u)+s_i(q)d_i.
$$

Consequently,

$$
\boxed{
d_i(q\star y)\le s_i(q)d_i(y).
}
\tag{14}
$$

In particular, every zero-debt coordinate remains zero.

At an off-minimum endpoint with excess

$$
E(y)=D(y)-D_*,
$$

global minimality implies, for every such root,

$$
\boxed{
\sum_i\bigl(1-s_i(q)\bigr)d_i(y)\le E(y).
}
\tag{15}
$$

Otherwise (14) would give a profile below \(D_*\).

This supplies another descent whenever an actual-payoff Nash root exposes positive debt to an opponent's quitting hazard. But it can stall for exactly the deleted-clock reason in the question.

For example, suppose only player \(k\) carries debt \(D>0\), and a Nash root against \(u\) has

$$
q_k=h>0,\qquad q_i=0\quad(i\ne k),
$$

with

$$
u_k=r_k(\{k\}).
$$

Then \(s_k(q)=1\), although \(c(q)=1-h\). At the cap \(b_k=u_k+D\), player \(k\)'s local regret is \(hD\), so (1) gives

$$
d_k(q\star y)
 =hD+(1-h)D
 =D.
\tag{16}
$$

The prescribed tail is reached only with probability \(1-h\), but after deleting player \(k\)'s own hazards, the tail is reached with probability \(1\). Repeating these roots can drive joint tail reach to zero while leaving player \(k\)'s unrestricted cap completely intact.

Equation (16) is the exact local form of the chronological obstruction specified in the question. Neither the positive atom nor joint reach controls it.

## 5. The remaining implication

The supplied inputs therefore establish the following reduction:

$$
\boxed{
\begin{aligned}
\text{full-debt positive-law minimum}
\Longrightarrow\;&
\text{reset-rigid minimum}
\\
&\text{or a same-source packet }(A_n,R_n,j)
\text{ with}
\\[-2mm]
&d_j(R_n)\to0,\qquad
D(R_n)\to D_*+\delta,\ \delta>0,
\\
&\text{a nonvanishing signed terminal-law contribution,}
\\
&\text{and vanishing maximal cap-root absorption.}
\end{aligned}
}
\tag{17}
$$

A complete positive proof still requires the following statement.

### Off-minimum inert-collapse lemma

Every packet in the second branch of (17) must yield at least one of:

1. an extension-compatible finite or asymptotic exact chronology returning to the minimum fibre while retaining positive joint reach and the signed contribution;
2. a simultaneous upper bound on all three nonmover cap leakages, allowing the responder replacement to lower total debt;
3. a Nash–Bellman chronology in which an opponent of every remaining debtor is persistent, so that deleted-player survival as well as joint survival vanishes; or
4. a genuine renewable finite-rank exit.

The paid-fork theorem does not prove this lemma. It controls the responder's gain and the prescribed joint reach at the first disagreement, but it does not control the three other unrestricted caps after the complete strategy change. Formula (16) shows why joint reach alone cannot substitute for that control. Likewise, switching the deep response tail back to its sibling destroys the exactness of the roots selected at \(B(R_n)\).

Accordingly, (F1)–(F3) have not yet been shown incompatible with the terminal exploitability witness. The exact-root arm can be reduced rigorously to the reset-rigid arm or to the off-minimum inert-collapse lemma, but the latter remains a genuine unproved implication. The regressions above are not an explicit four-player counterexample, so they do not constitute the requested negative answer either.

## Followup

The off-minimum alternative can be sharpened substantially. In the non-strict-cap branch, the positive full-debt margin forces an additional player label, a source-matched payoff atom, and an actually reached curvature fork. The other three unrestricted caps can then be eliminated exactly by a sure-quit Nashification.

Write

$$
s_i:=r_i(\{i\}).
$$

Let \(A_n\) denote the same-source sibling converging to the full-debt minimum \(x=(U,B)\), and let

$$
R_n=(u^R_n,b^R_n)
$$

be the response endpoint. Fix the responding coordinate \(j\), so that

$$
d_j(R_n)\longrightarrow0.
$$

Because \(A_n\) and \(R_n\) differ only in player \(j\)'s complete strategy,

$$
b^R_{n,j}=B_j(A_n)\longrightarrow B_j.
\tag{18}
$$

In particular, by (F3),

$$
b^R_{n,j}-s_j\ge \frac{D_*}{2}
\tag{19}
$$

for all sufficiently large \(n\).

## 1. The full-debt minimum has a uniform singleton moat

Define

$$
\alpha_i:=U_i-s_i.
$$

Then (F3) gives

$$
\alpha_i
=(B_i-s_i)-d_i(x)
\ge D_*-d_i(x)
=\sum_{\ell\ne i}d_\ell(x)>0.
\tag{20}
$$

Hence

$$
\alpha:=\min_i\alpha_i>0.
\tag{21}
$$

This is stronger than merely saying that all Continue is Nash against \(U\): each player strictly prefers the continuation payoff \(U_i\) to quitting alone, by a uniform amount.

## 2. Vanishing maximal cap roots either have a binding label or a strict moat

Let \(q^n\) be a maximal-absorption exact product root against \(b^R_n\), and put

$$
c_n:=\prod_i(1-q^n_i),
\qquad
a_n:=1-c_n.
$$

We are in the off-minimum branch \(a_n\to0\).

For player \(i\), write

$$
\chi_{n,i}:=\prod_{\ell\ne i}(1-q^n_\ell).
$$

Suppose \(q^n_k>0\). Since \(a_n\to0\), eventually \(q^n_k<1\), and exact complementarity makes player \(k\) indifferent between Quit and Continue at the cap \(b^R_n\). If \(p^n_{-k}(A)\) is the probability that exactly the opponents in \(A\) quit, then

$$
\chi_{n,k}(b^R_{n,k}-s_k)
=
\sum_{\varnothing\ne A\subseteq I\setminus\{k\}}
p^n_{-k}(A)
\bigl(r_k(A\cup\{k\})-r_k(A)\bigr).
\tag{22}
$$

Therefore

$$
\left|b^R_{n,k}-s_k\right|
\le
\frac{2M(1-\chi_{n,k})}{\chi_{n,k}}
\le
\frac{2Ma_n}{1-a_n}
\longrightarrow0.
\tag{23}
$$

After a subsequence, one fixed active label \(k\) can be used. By (19), necessarily

$$
k\ne j.
\tag{24}
$$

If instead \(q^n=0\) eventually, then all Continue is exact against \(b^R_n\). Either some fixed coordinate satisfies

$$
b^R_{n,k}-s_k\longrightarrow0,
\tag{25}
$$

or there is an \(\eta>0\) such that

$$
b^R_{n,i}-s_i\ge\eta
\qquad(i\in I)
\tag{26}
$$

eventually. In the latter case, (23) shows that no sufficiently small nonzero exact root exists. Since \(q^n\) was chosen with maximal absorption, all Continue is eventually the unique exact root.

Thus the off-minimum branch has the exhaustive refinement

$$
\boxed{
\begin{array}{l}
\text{uniform strict cap moat and unique all-Continue root},\\
\text{or a fixed }k\ne j\text{ with }b^R_{n,k}-s_k\to0.
\end{array}}
\tag{27}
$$

## 3. A binding label produces source-matched curvature

Assume the second arm of (27). Since \(A_n\to x\),

$$
u^A_{n,k}\longrightarrow U_k.
$$

Together with (20) and \(b^R_{n,k}\to s_k\), this gives, after discarding finitely many terms,

$$
\boxed{
u^A_{n,k}-b^R_{n,k}\ge\frac{\alpha}{2}.
}
\tag{28}
$$

Since \(u^R_{n,k}=b^R_{n,k}-d_k(R_n)\),

$$
u^A_{n,k}-u^R_{n,k}
=
u^A_{n,k}-b^R_{n,k}+d_k(R_n)
\ge\frac{\alpha}{2}.
\tag{29}
$$

This already yields an aligned terminal-law atom. Let \(\mu^A_n,\mu^R_n\) be the complete terminal laws of the two same-source siblings. Then

$$
u^A_{n,k}-u^R_{n,k}
=
\sum_{\varnothing\ne T\subseteq I}
\bigl(\mu^A_n(T)-\mu^R_n(T)\bigr)r_k(T).
$$

There are only \(15\) nonempty coalitions. Hence, after another subsequence, one fixed coalition \(T\) satisfies

$$
\boxed{
\bigl(\mu^A_n(T)-\mu^R_n(T)\bigr)r_k(T)
\ge\frac{\alpha}{30}.
}
\tag{30}
$$

Thus the binding player \(k\) is simultaneously:

* distinct from the response owner \(j\);
* the coordinate whose response cap approaches its singleton reward;
* the recipient of a fixed same-source payoff loss;
* the observer of a fixed signed terminal-law atom.

This removes the previous recipient–incidence mismatch.

## 4. The curvature is at an actually reached root

First suppose \(q^n_k>0\). Exactness of \(q^n\) at the cap gives

$$
Q_k(q^n_{-k})
=
C_k(q^n_{-k};b^R_{n,k}).
\tag{31}
$$

Against the actual response payoff,

$$
Q_k(q^n_{-k})
-
C_k(q^n_{-k};u^R_{n,k})
=
\chi_{n,k}d_k(R_n).
\tag{32}
$$

Hence, in the literal profile \(q^n::R_n\), changing player \(k\)'s current mixed action to pure Quit has exact gain

$$
\begin{aligned}
g^R_{n,k}
&=(1-q^n_k)\chi_{n,k}d_k(R_n)\\
&=c_n d_k(R_n).
\end{aligned}
\tag{33}
$$

Against the source sibling, the same root has the opposite conditional orientation:

$$
\begin{aligned}
C_k(q^n_{-k};u^A_{n,k})
-
Q_k(q^n_{-k})
&=
\chi_{n,k}\bigl(u^A_{n,k}-b^R_{n,k}\bigr)\\
&\ge (1-a_n)\frac{\alpha}{2}.
\end{aligned}
\tag{34}
$$

Thus the fork is located at literal time \(0\), with joint reach exactly \(1\). There is no deleted-survival substitution.

If \(q^n=0\) and (25) holds, pure Quit from the response profile has gain

$$
s_k-u^R_{n,k}
=
d_k(R_n)-(b^R_{n,k}-s_k).
\tag{35}
$$

Consequently, after a subsequence, exactly one of the following occurs:

$$
d_k(R_n)\longrightarrow0,
\tag{36}
$$

so both \(j\) and \(k\) have asymptotically zero debt, or there is a \(\beta>0\) such that

$$
d_k(R_n)\ge\beta,
\tag{37}
$$

and the literal root-time deviation in (33) or (35) gains at least \(\beta/2\).

We therefore obtain

$$
\boxed{
\begin{array}{l}
\text{two fixed zero-debt coordinates},\\
\text{or a source-matched, target-cap-compatible root-time curvature fork.}
\end{array}}
\tag{38}
$$

## 5. The curvature is renewable under exact target-side descent

The quantity in (28) has an exact transport law.

Let \(w=x_0x_1\cdots x_{m-1}\) be any finite word in which every \(x_t\) is an exact product root against the current cap of the prefixed response endpoint. Let

$$
P(w):=\prod_{t<m}c(x_t).
$$

Prefix the same word to \(A_n\) and \(R_n\). Exact cap-Nash recursion gives

$$
D(w::R_n)=P(w)D(R_n),
\tag{39}
$$

and, because the root-absorption rewards cancel between the two siblings,

$$
\boxed{
U_k(w::A_n)-B_k(w::R_n)
=
P(w)\bigl(u^A_{n,k}-b^R_{n,k}\bigr).
}
\tag{40}
$$

Global minimality implies

$$
P(w)D(R_n)\ge D_*.
$$

Since \(D(R_n)\le8M\),

$$
P(w)\ge\frac{D_*}{8M}.
\tag{41}
$$

Combining (28), (40), and (41),

$$
\boxed{
U_k(w::A_n)-B_k(w::R_n)
\ge
\frac{\alpha D_*}{16M}.
}
\tag{42}
$$

The same common-prefix calculation gives

$$
U_k(w::A_n)-U_k(w::R_n)
=
P(w)\bigl(u^A_{n,k}-u^R_{n,k}\bigr),
\tag{43}
$$

so the signed terminal-law difference also retains a fixed positive floor.

Thus this is not a one-use atom. It is a genuine exact-prefix passport: every exact target-side descent that remains above the global floor retains a fixed source-versus-response curvature.

## 6. Exact control of the other three unrestricted caps

The root-time fork can be normalized into a profile having only one debtor.

Fix the selected player \(k\). Consider the finite three-player game among

$$
J:=I\setminus\{k\}
$$

in which \(k\) is fixed to Quit and the players in \(J\) choose Quit or Continue. If the quitting subset of \(J\) is \(A\), the terminal coalition is \(A\cup\{k\}\).

Let \(y\) be a mixed Nash equilibrium of this finite three-player game. Write \(p_y(A)\) for the product probability of \(A\subseteq J\), and put

$$
p_0:=p_y(\varnothing).
$$

Construct an actual behavioral profile \(W\) as follows:

* at time \(0\), player \(k\) quits surely and the other three players use \(y\);
* after unanimous Continue, everyone plays Never.

For every \(\ell\ne k\), absorption occurs at time \(0\) regardless of \(\ell\)'s unilateral strategy, because \(k\) remains a sure quitter. Since \(y\) is Nash on the \(k\)-Quit face,

$$
d_\ell(W)=0
\qquad(\ell\ne k).
\tag{44}
$$

Let

$$
\lambda_k:=\max\{0,s_k\}.
$$

Player \(k\)'s Quit and Continue values are

$$
Q_k(y)
=
\sum_{A\subseteq J}p_y(A)r_k(A\cup\{k\}),
\tag{45}
$$

and

$$
C_k(y)
=
p_0\lambda_k
+
\sum_{\varnothing\ne A\subseteq J}p_y(A)r_k(A).
\tag{46}
$$

The use of \(\lambda_k\) is exact: after \(k\) Continues and all three opponents Continue, those opponents play Never, so \(k\)'s unrestricted continuation cap is precisely \(\max\{0,s_k\}\).

Therefore

$$
D(W)=d_k(W)=\bigl[C_k(y)-Q_k(y)\bigr]_+.
\tag{47}
$$

Since \(W\) is an actual profile, global minimality yields

$$
D(W)\ge D_*.
$$

Hence the positive part in (47) is active and

$$
\boxed{
p_0(-s_k)_+
+
\sum_{\varnothing\ne A\subseteq J}
p_y(A)\bigl(r_k(A)-r_k(A\cup\{k\})\bigr)
\ge D_*.
}
\tag{48}
$$

This is an unrestricted-cap statement, not a one-stage surrogate: all three other debts are exactly zero and \(k\)'s complete behavioral cap is exactly (47).

Equation (48) has a quantitative finite split.

Either

$$
p_0(-s_k)_+\ge\frac{D_*}{2},
\tag{49}
$$

which implies

$$
s_k\le-\frac{D_*}{2},
\qquad
p_0\ge\frac{D_*}{2M},
\tag{50}
$$

or

$$
\sum_{\varnothing\ne A\subseteq J}
p_y(A)
\bigl[r_k(A)-r_k(A\cup\{k\})\bigr]_+
\ge\frac{D_*}{2}.
\tag{51}
$$

There are seven nonempty subsets of \(J\). Thus in the second case one fixed nonempty \(A\subseteq J\) satisfies

$$
\boxed{
p_y(A)
\bigl(r_k(A)-r_k(A\cup\{k\})\bigr)
\ge\frac{D_*}{14}.
}
\tag{52}
$$

In particular,

$$
r_k(A)-r_k(A\cup\{k\})
\ge\frac{D_*}{14},
\qquad
p_y(A)\ge\frac{D_*}{28M}.
\tag{53}
$$

This is a literal time-\(0\) atomic leave wall: coalition \(A\cup\{k\}\) has fixed reached mass, and player \(k\) strictly prefers to leave it.

## 7. The source curvature can also be retained through the sure-quit wall

Append \(A_n\), respectively \(R_n\), after the same sure-\(k\) root \((1,y)\). Call the two profiles \(W^A_n,W^R_n\).

Their prescribed payoff vectors and complete terminal laws are identical, because \(k\) quits surely. All coordinates other than \(k\) again have zero debt. For \(k\), global minimality forces Continue to be its strictly better cap endpoint in \(W^R_n\), with excess at least \(D_*\). Therefore

$$
\begin{aligned}
B_k(W^A_n)-B_k(W^R_n)
&=
p_0\bigl(B_k(A_n)-B_k(R_n)\bigr)\\
&\ge
p_0\bigl(u^A_{n,k}-b^R_{n,k}\bigr).
\end{aligned}
$$

Using (28),

$$
\boxed{
B_k(W^A_n)-B_k(W^R_n)
\ge p_0\frac{\alpha}{2}.
}
\tag{54}
$$

Thus:

* if \(p_0>0\), the source-matched terminal-law difference has been converted into a fixed **one-coordinate cap fork between two profiles with exactly the same prescribed payoff and terminal law**;
* if \(p_0=0\), the continuation is completely removed and (52) is a purely finite sure-absorption wall.

## Revised frontier

The strictly off-minimum endpoint is therefore no longer an undifferentiated inert state. It has the following exhaustive refinement:

$$
\boxed{
\begin{array}{ll}
\textbf{(M)}&
\text{A uniform strict cap moat, with all Continue the unique exact root;}\\[1mm]
\textbf{(Z)}&
\text{Two fixed coordinates }j,k\text{ have debt tending to zero;}\\[1mm]
\textbf{(C)}&
\text{A renewable source-matched curvature fork at literal reach }1,\\
&\text{followed by a sure-quit profile whose other three unrestricted debts}\\
&\text{are exactly zero;}\\[1mm]
\textbf{(N/L)}&
\text{A fixed negative-singleton/Never wall, or a fixed positive-mass}\\
&\text{coalition from which the selected owner strictly prefers to leave.}
\end{array}}
\tag{55}
$$

This removes both chronological ambiguities from the binding branch:

* no opponent-deleted reach is substituted for joint reach;
* no uncontrolled leakage remains in the other three caps after the final sure-quit normalization.

It does not yet eliminate the full-debt chamber. The remaining mathematical implication is now narrower: consume the strict unique-all-Continue cap moat, or turn the fixed table-level wall in (49)–(53) into a reset-rigid return, a proper-player deletion, or a renewable owner transition.
