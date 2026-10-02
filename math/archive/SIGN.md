The decisive issue is whether **the carrier generated from all-Never can have a positive global minimum**, not merely whether some prefix choices contract debt. I can prove a restrictive form for such a minimum, but **I have not proved that it is impossible, nor constructed a table with \(\eta(r)>0\)**.

Here is the strongest conclusion I can establish directly from your prefix operators.

## Rigidity of a hypothetical positive minimum

Write

$$
E(u,b)=\max_i(b_i-u_i),\qquad s_i=r_i(\{i\}),
$$

and suppose \(\eta=\eta(r)>0\). Let \(z=(u,b)\in K_r\) attain this minimum.

Then

$$
\boxed{
b_i-u_i=\eta\quad\text{for every }i,
\qquad
\eta\sum_{i=0}^{3}\frac1{b_i-s_i}\le1.
}
\tag{1}
$$

In particular,

$$
\boxed{u_i>s_i\quad\text{for every }i.}
\tag{2}
$$

There is also a root-equilibrium exclusion: for every continuation vector \(v\) satisfying

$$
u\le v\le b
$$

coordinatewise, **all-Continue is the only Nash equilibrium of the one-stage game with continuation payoff \(v\)**.

These assertions concern the actual global minimum on \(K_r\); they do not assume that it is realized by a behavioral profile.

### 1. Every cap has a positive singleton margin

Put

$$
c=\pi_x(\varnothing),\qquad
c_{-i}=\pi_{x,-i}(\varnothing).
$$

Thus

$$
c_{-i}-c=x_i c_{-i}=\pi_x(\{i\}).
$$

Fix \(0<\delta<\eta\), and choose a Nash equilibrium \(x\) of the finite one-stage game with continuation

$$
v=b-\delta\mathbf1.
$$

Such an equilibrium exists by the finite-game Nash theorem. ([PNAS][1])

Let \(F_i(x,v)\) denote its prescribed payoff. Root Nash gives

$$
F_i(x,v)=\max\{Q_i(x),C_i(x,v)\}.
$$

Since

$$
C_i(x,b)=C_i(x,v)+\delta c_{-i},
$$

the prefixed cap satisfies

$$
b_i'\le F_i(x,v)+\delta c_{-i}.
$$

Meanwhile,

$$
u_i'=F_i(x,v)+c(u_i-v_i).
$$

Consequently,

$$
b_i'-u_i'
\le c(b_i-u_i)+\delta(c_{-i}-c)
=c(b_i-u_i)+\delta\pi_x(\{i\}).
\tag{3}
$$

If \(x\ne0\), then \(c<1\), and (3) yields

$$
E(T_xz)
\le c\eta+\delta(1-c)
<\eta,
$$

contradicting prefix invariance and global minimality.

Therefore the selected equilibrium must be all-Continue. Its Nash inequalities imply

$$
b_i-\delta\ge s_i.
$$

Letting \(\delta\uparrow\eta\), we obtain

$$
b_i-s_i\ge\eta>0
\quad\text{for every }i.
\tag{4}
$$

### 2. Every coordinate debt equals the maximum

Suppose some player \(k\) has

$$
b_k-u_k<\eta.
$$

Prefix a root in which only \(k\) quits, with probability \(t>0\).

By (4), Continue strictly beats Quit in every player’s cap-based root comparison at \(t=0\). For sufficiently small \(t\), therefore, the cap recursion continues to use its Continue branch. Direct substitution gives

$$
b_j'-u_j'=(1-t)(b_j-u_j)
\qquad(j\ne k),
\tag{5}
$$

and

$$
b_k'-u_k'
=(b_k-u_k)+t(u_k-s_k).
\tag{6}
$$

For sufficiently small positive \(t\), (6) remains strictly below \(\eta\), while every quantity in (5) is also strictly below \(\eta\). This contradicts minimality. Hence

$$
b_i-u_i=\eta
\qquad(i=0,1,2,3).
\tag{7}
$$

### 3. The harmonic inequality

Set

$$
g_i=b_i-s_i>0.
$$

For a vector \(h\in[0,\infty)^4\), consider the small root

$$
x_i(t)=t h_i.
$$

Again, the cap recursion uses Continue for all sufficiently small \(t\). Its exact debt identity is

$$
b_i'(t)-u_i'(t)
=c(t)\eta+x_i(t)\bigl(C_i(x(t),b)-Q_i(x(t))\bigr).
$$

Differentiating at zero gives

$$
\left.\frac{d}{dt}(b_i'(t)-u_i'(t))\right|_{t=0}
=h_i g_i-\eta\sum_j h_j.
\tag{8}
$$

Choose \(h_i=1/g_i\). Every derivative in (8) becomes

$$
1-\eta\sum_j\frac1{g_j}.
$$

If this number were negative, every debt would fall below \(\eta\) for sufficiently small positive \(t\). Therefore

$$
\eta\sum_j\frac1{g_j}\le1,
$$

proving (1).

All four summands are positive. Thus each satisfies \(\eta/g_i<1\), so \(g_i>\eta\). Using (7),

$$
u_i-s_i=g_i-\eta>0,
$$

which proves (2).

### 4. No absorbing Nash root anywhere between \(u\) and \(b\)

Let \(u\le v\le b\), and let \(x\) be root Nash against \(v\). The same comparison used in (3) gives

$$
\begin{aligned}
b_i'-u_i'
&\le c(v_i-u_i)+c_{-i}(b_i-v_i)\\
&=c\eta+\pi_x(\{i\})(b_i-v_i)\\
&\le c_{-i}\eta
\le\eta.
\end{aligned}
\tag{9}
$$

Thus \(T_xz\) is another global minimizer. By (7), all its debts must equal \(\eta\). Equation (9), together with \(\eta>0\), forces

$$
c_{-i}=1\qquad\text{for every }i.
$$

With four players this implies \(x=0\).

So a positive minimizer is not merely a point where one particular Nash-root selection stalls: **every exact Nash-root selection stalls throughout the entire continuation box \([u,b]\)**.

## A quantitative consequence

Define the coordinatewise payoff upper bounds

$$
M_i=\max\bigl(\{0\}\cup\{r_i(S):S\ne\varnothing\}\bigr).
$$

Since \(b_i\le M_i\), a positive minimum must satisfy

$$
\eta\sum_i\frac1{M_i-s_i}\le1.
$$

Consequently, when all denominators are positive,

$$
\boxed{
\eta(r)\le
\left(\sum_{i=0}^{3}\frac1{M_i-r_i(\{i\})}\right)^{-1}.
}
\tag{10}
$$

If \(M_i=s_i\) for even one player, (4) is impossible, and therefore

$$
\boxed{\eta(r)=0.}
$$

This proves the sign for the subclass where some player’s own singleton payoff is that player’s largest payoff, including the Never outcome. It does not cover arbitrary tables.

## Why this still does not settle the requested sign

The preceding minimization argument uses compactness, nonnegative debts, and invariance under **every** root. It does not use the all-Never anchor beyond obtaining those properties. That omission is substantive: those properties alone permit positive minima.

For example, consider the explicit four-player table

$$
r_i(S)=2-\mathbf1_{\{i\in S\}}
\qquad(S\ne\varnothing).
\tag{11}
$$

Define

$$
C=\left\{(u,b):
b=2\mathbf1,\quad
0\le u_i\le2,\quad
\sum_i u_i\le7
\right\}.
$$

This is compact and has

$$
E(u,b)\ge\frac14.
$$

For every product root \(x\),

$$
b_i'=2,\qquad
u_i'=2(1-c)-x_i+cu_i.
$$

Therefore

$$
\sum_i u_i'
\le8(1-c)-\sum_i x_i+7c
\le7,
$$

where the last inequality uses \(1-c\le\sum_i x_i\). The coordinate bounds are also preserved. Hence

$$
T_x(C)\subseteq C
\qquad\text{for every }x.
$$

At its minimum,

$$
u=\tfrac74\mathbf1,\qquad b=2\mathbf1,
$$

all four debts equal \(1/4\), and the harmonic inequality is an equality. Thus the rigidity conditions above are compatible with a positive invariant-set minimum.

**This is not a negative certificate for your question:** here

$$
e_{\mathrm{Never}}=(0,\mathbf1)\notin C.
$$

Indeed, the game in (11) has an exact terminal Nash profile: one player quits immediately and everyone else plays Never. Its prescribed payoff is \(1\) for the quitter and \(2\) for everyone else, with no profitable unilateral replacement. Thus its actual \(\eta(r)\) is zero.

The remaining step is precisely to exploit **generation from \(e_{\mathrm{Never}}\)** to exclude a positive, fully balanced global minimum of \(K_r\). The arguments above do not establish that step. They give neither the universal diagonal intersection nor the anchored positive-gap invariant set required to answer the question.

[1]: https://www.pnas.org/doi/10.1073/pnas.36.1.48 "Equilibrium points in n-person games"

---

The missing step is global: **lowering current exploitability need not preserve the possibility of lowering it further by prefixes—even when starting from all-Never.** I verified this obstruction explicitly. I also obtained a quantitative strengthening of the minimum-debt argument, but **I have not proved the requested universal zero value or constructed a counterexample to it**.

Here are the precise results, including where the attempted completion fails.

## 1. A quantitative, actual-prefix improvement

Write

$$
d_i=b_i-u_i,\qquad E=\max_i d_i,\qquad m=\min_i d_i.
$$

For every \(z=(u,b)\in K_r\), with \(R>0\) and \(E>0\), there is a product root \(x\) satisfying

$$
\boxed{
E(T_xz)\le E-\frac{E(E-m)}{16R}.
}
\tag{1}
$$

This is an improvement by a genuine permitted root, not an operation on fictitious continuation values. In particular, if \(z\) comes from a finite stopping-law profile, so does the improved state.

Consequently,

$$
\boxed{
E(z)-\eta(r)\ge
\frac{E(z)\bigl(E(z)-\min_i d_i(z)\bigr)}{16R}.
}
\tag{2}
$$

Thus, under a hypothetical positive gap, every state with a zero-debt coordinate satisfies the strict separation

$$
\boxed{
E(z)\ge \eta(r)+\frac{\eta(r)^2}{16R}.
}
\tag{3}
$$

### Proof

Put \(s_i=r_i(\{i\})\) and \(g_i=b_i-s_i\).

**Case A: some \(g_i\le E/6\).**

Choose a Nash equilibrium \(x\) of the finite one-stage game with continuation

$$
v=b-\frac E2\mathbf1.
$$

Existence follows from the finite-game Nash theorem. ([JSTOR][1])

Let \(c=\pi_x(\varnothing)\) and \(a_j=\pi_{x,-j}(\varnothing)\). The root Nash equalities, together with the unrestricted cap recursion, give

$$
d_j(T_xz)
\le c\,d_j+\frac E2(a_j-c).
$$

Since \(a_j-c=\pi_x(\{j\})\le1-c\),

$$
E(T_xz)\le E-\frac E2(1-c).
\tag{4}
$$

For the player \(i\) chosen above, Quit’s advantage over Continue against all-Continue opponents in this auxiliary game is

$$
\kappa=s_i-v_i=\frac E2-g_i\ge\frac E3.
$$

If \(x_i=1\), then \(1-c=1\). Otherwise Continue is a best response, so

$$
0\ge Q_i(x)-C_i(x,v)
\ge a_i\kappa-2R(1-a_i).
$$

Therefore

$$
1-c\ge1-a_i\ge\frac{\kappa}{2R+\kappa}
\ge\frac{E}{6R+E}.
$$

Combining this with (4) and \(E\le2R\),

$$
E(T_xz)
\le E-\frac{E^2}{2(6R+E)}
\le E-\frac{E^2}{16R}.
$$

Because \(E-m\le E\), this implies (1).

**Case B: every \(g_i>E/6\).**

Choose \(k\) with \(d_k=m\), put \(\Delta=E-m\), and prefix the root

$$
x_k=t:=\frac{\Delta}{12R+E},
\qquad x_j=0\quad(j\ne k).
$$

For \(j\ne k\), the difference between its Continue and Quit cap branches is

$$
C_j(x,b)-Q_j(x)
=(1-t)g_j+
t\bigl(r_j(\{k\})-r_j(\{j,k\})\bigr).
$$

Hence

$$
C_j(x,b)-Q_j(x)
\ge(1-t)\frac E6-2Rt
=\frac m6\ge0.
$$

The Continue branch therefore determines each such cap. It also determines player \(k\)’s cap because \(g_k>0\). Thus

$$
d_j(T_xz)=(1-t)d_j\quad(j\ne k),
$$

and

$$
d_k(T_xz)=(1-t)m+t g_k.
$$

Since \(g_k\le2R\) and \(t(2R+\Delta)\le\Delta\),

$$
d_k(T_xz)\le(1-t)E.
$$

It follows that

$$
E(T_xz)\le(1-t)E
=E-\frac{E(E-m)}{12R+E}
\le E-\frac{E(E-m)}{16R}.
$$

This proves (1). Prefix invariance gives (2), and \(m=0\) gives (3). \(\square\)

The bound supplies a quantitative version of the previous rigidity result: near a positive global minimum, **all four debts must be close to the same positive number**. It does not supply a decrease once they have become equal.

## 2. Strict descent from all-Never can enter a positive-gap prefix region

The following example makes the selection problem operational, rather than merely a concern about unattainable semantic states.

Use the four-player reward table

$$
r_i(S)=2-\mathbf1_{\{i\in S\}}
\qquad(S\ne\varnothing).
\tag{5}
$$

Thus every quitter receives \(1\), and every nonquitter receives \(2\).

Its all-Never state is

$$
e_{\mathrm{Never}}=(0,\mathbf1),
\qquad E(e_{\mathrm{Never}})=1.
$$

Now prefix the legitimate product root

$$
x=(1/2,1/2,1/2,1/2).
$$

The resulting **actual finite profile** has

$$
u_i=2\left(1-\frac1{16}\right)-\frac12=\frac{11}{8},
$$

and

$$
b_i=\max\left\{1,\,
2\left(1-\frac18\right)+\frac18\right\}
=\frac{15}{8}.
$$

Therefore

$$
\boxed{E(T_xe_{\mathrm{Never}})=\frac12<1.}
\tag{6}
$$

Nevertheless, **no sequence of further product-root prefixes can reduce its exploitability below \(1/8\)**.

To prove this, define

$$
C=
\left\{
(u,b)\in[-2,2]^4\times[-2,2]^4:
u_i\le b_i,\quad
b_i\ge\frac{15}{8},\quad
\sum_i u_i\le7
\right\}.
\tag{7}
$$

The state in (6) belongs to \(C\).

For any new root \(y\), write

$$
a_i=\pi_{y,-i}(\varnothing),
\qquad c=\pi_y(\varnothing).
$$

In game (5),

$$
Q_i(y)=1,\qquad
C_i(y,b)=2(1-a_i)+a_i b_i.
$$

Thus, whenever \(b_i\ge15/8\),

$$
b_i'
\ge2(1-a_i)+a_i\frac{15}{8}
=2-\frac{a_i}{8}
\ge\frac{15}{8}.
\tag{8}
$$

Moreover, every terminal coalition has total payoff

$$
\sum_i r_i(S)=8-|S|\le7.
$$

Consequently,

$$
\sum_i u_i'
\le7(1-c)+c\sum_i u_i
\le7.
\tag{9}
$$

The coordinate bounds and \(u'\le b'\) are also preserved. Hence \(C\) is closed and invariant under **every** product root.

Finally, every point of \(C\) satisfies

$$
E(u,b)
\ge\frac14\sum_i(b_i-u_i)
\ge\frac14\left(4\cdot\frac{15}{8}-7\right)
=\frac18.
\tag{10}
$$

This is not a counterexample to the conjecture. In this same game, having player \(0\) quit immediately and everyone else play Never gives

$$
u=b=(1,2,2,2),
$$

an exact terminal Nash profile. Therefore \(\eta(r)=0\).

What the example establishes is the sharper obstruction

$$
\boxed{
\begin{gathered}
\text{start at }e_{\mathrm{Never}},\\
\text{make a strict exploitability-decreasing legal prefix},\\
\text{arrive at an actual profile whose entire future prefix hull}\\
\text{has a fixed positive exploitability floor}.
\end{gathered}}
$$

## 3. What remains unproved

Define the future-prefix value

$$
H(z)=\inf_{\text{finite root words }w}E(T_wz).
$$

The example gives

$$
H(e_{\mathrm{Never}})=0,
\qquad
H(T_{(1/2,\ldots,1/2)}e_{\mathrm{Never}})\ge\frac18,
$$

despite the strict decrease in current exploitability from \(1\) to \(1/2\).

Thus the quantitative descent theorem cannot simply be iterated to solve the sign question: **a decrease in \(E\) can increase \(H\)**. The all-Never anchor does not automatically survive as a useful property of the selected continuation.

A completion must either establish a root-word selection that reaches arbitrarily small \(E\), or exclude positive **global** minima by an argument that goes beyond these prefix-descent estimates. I have established neither. The universal claim \(\eta(r)=0\) remains unproved here, and the invariant set above deliberately does **not** contain \(e_{\mathrm{Never}}\), so it is not the negative certificate you requested.

[1]: https://www.jstor.org/stable/1969529?utm_source=chatgpt.com "Non-Cooperative Games"
