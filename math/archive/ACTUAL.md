The paid comparison controls the mover’s debt, while a strict decrease of \(D\) also requires control of the other three debts. I obtained an exact prefix estimate and a quantitative constraint on the retained minimum, but **not the requested construction of \(\pi\)**.

The prefix estimate is stronger than ordinary cap–Nash contraction: it permits an auxiliary continuation strictly below the cap vector, with its cost accounted for exactly.

## 1. A shifted-cap prefix estimate

Write

$$
\alpha_j=r_j(\{j\}).
$$

Fix an **actual** continuation profile \(x\), and set

$$
u=U(x),\qquad b=B(x),\qquad d=b-u.
$$

For a scalar \(h\ge 0\), consider the finite one-stage game whose nonempty-coalition rewards are \(r(S)\) and whose all-Continue payoff is

$$
v=b-h\mathbf 1.
$$

Choose a mixed Nash equilibrium \(q\) of this finite game. Such an equilibrium exists by the finite-game Nash theorem. ([JSTOR][1])

Construct the actual profile

$$
\pi=q\triangleright x:
$$

play \(q\) at date zero and, following all-Continue, play the original product law \(x\), shifted by one date. **The actual continuation is \(x\), not the auxiliary vector \(v\).**

Define

$$
c=\prod_k(1-q_k),\qquad
c_{-j}=\prod_{k\ne j}(1-q_k),\qquad
\xi_j=q_jc_{-j},\qquad
\xi=\sum_j\xi_j.
$$

Thus \(\xi_j\) is the probability that exactly player \(j\) quits at the new root.

Then

$$
\boxed{\quad
d_j(\pi)\le c\,d_j(x)+h\,\xi_j,
\qquad
D(\pi)\le cD(x)+h\xi
             \le cD(x)+h(1-c).
\quad} \tag{1}
$$

### Proof, including the unrestricted caps

Against \(q_{-j}\), let \(Q_j\) be the payoff from quitting at the root, and write

$$
C_j(y)=H_j+c_{-j}y
$$

for the payoff from continuing when the continuation value is \(y\). Here \(H_j\) includes the rewards from nonempty opponent coalitions at the root.

Root Nash optimality gives

$$
K_j:=\max\{Q_j,C_j(v_j)\}
=q_jQ_j+(1-q_j)C_j(v_j).
$$

For the actual prefixed profile,

$$
U_j(\pi)
=q_jQ_j+(1-q_j)C_j(u_j)
=K_j+c(u_j-v_j).
$$

Its full behavioral cap is exactly

$$
B_j(\pi)=\max\{Q_j,C_j(b_j)\}. \tag{2}
$$

Indeed, a deviator either quits at the root or continues and then uses an arbitrary replacement law against \(x_{-j}\). The supremum in the second branch is \(b_j\); its attainment is unnecessary.

Since \(b_j-v_j=h\ge0\),

$$
B_j(\pi)\le K_j+c_{-j}h.
$$

Using \(u_j-v_j=h-d_j(x)\), subtraction yields

$$
d_j(\pi)
\le c\,d_j(x)+(c_{-j}-c)h
=c\,d_j(x)+\xi_jh.
$$

Summing proves (1).

Moreover, **equality holds in the first inequality whenever \(q_j<1\)**: Continue is then a best response in the auxiliary root game, and increasing its continuation value from \(v_j\) to \(b_j\) increases the cap by exactly \(c_{-j}h\).

## 2. A quantitative constraint imposed by the global infimum

Put \(\delta=D_*>0\). For an arbitrary actual \(x\), write

$$
\Delta=D(x)-\delta\ge0.
$$

Choose any \(0<h<\delta\) and an auxiliary root equilibrium as above.

No player can quit surely at that equilibrium. Otherwise \(c=0\), and (1) gives

$$
D(\pi)\le h<\delta,
$$

already the requested contradiction.

Consequently every player has Continue in support. From the global lower bound and (1),

$$
\delta\le cD(x)+h(1-c),
$$

so

$$
\boxed{\quad
1-c\le\frac{\Delta}{D(x)-h}.
\quad} \tag{3}
$$

Root optimality now bounds the original caps. Fix \(j\) and put

$$
z_j=b_j-\alpha_j.
$$

The Quit-minus-Continue payoff difference in the auxiliary game is

$$
c_{-j}(h-z_j)
+\sum_{\varnothing\ne S\subseteq I\setminus\{j\}}
p_{q_{-j}}(S)
\bigl(r_j(S\cup\{j\})-r_j(S)\bigr).
$$

It is nonpositive because Continue is optimal. Each reward difference is at least \(-2M\), hence

$$
c_{-j}(h-z_j)\le2M(1-c_{-j}).
$$

Using \(c_{-j}\ge c>0\) and (3),

$$
\boxed{\quad
B_j(x)-\alpha_j
\ge h-\frac{2M\bigl(D(x)-\delta\bigr)}{\delta-h},
\qquad 0<h<\delta.
\quad} \tag{4}
$$

This applies to **every actual product law**, with its unrestricted caps.

### Applying it to the retained, possibly unattained minimum

Use precisely the supplied sequence \(p^n\), for which

$$
D(p^n)\longrightarrow\delta,\qquad B(p^n)\longrightarrow b_*.
$$

For fixed \(h<\delta\), (4) gives

$$
b_{*,j}-\alpha_j\ge h.
$$

Letting \(h\uparrow\delta\),

$$
\boxed{\qquad
b_{*,j}\ge r_j(\{j\})+D_*
\quad\text{for every }j.
\qquad} \tag{5}
$$

This conclusion does not replace \(z_*\) by an attained minimum.

There is also a direct exclusion statement at \(z_*\). For every \(h<D_*\), the auxiliary root game with continuation

$$
b_*-h\mathbf1
$$

has **only the all-Continue equilibrium**. Otherwise, retain a non-all-Continue equilibrium \(q\) and prepend it to the actual profiles \(p^n\). The exact formulas for \(U\) and \(B\) in (2) are continuous in the tail’s semantic coordinates, so their limiting total debt would be at most

$$
cD_*+h\xi
\le cD_*+h(1-c)<D_*.
$$

A sufficiently large finite \(n\) would therefore give an actual contradiction.

Thus the auxiliary-game construction itself identifies, rather than removes, the all-Continue stall at the minimum.

## 3. Punishment normality does not make a low-cap replacement inexpensive

Equation (4), with \(h=\delta/2\), yields

$$
B_j(x)-\alpha_j
\ge \frac{\delta}{2}
-\frac{4M}{\delta}\bigl(D(x)-\delta\bigr).
$$

Consequently,

$$
B_j(x)\le\alpha_j+\eta
\quad\Longrightarrow\quad
\boxed{\;
D(x)\ge
\delta+\frac{\delta^2}{8M}
-\frac{\delta\eta}{4M}.
\;} \tag{6}
$$

Punishment normality supplies actual opponent laws with cap at most
\(\alpha_j+\eta\), for every \(\eta>0\). But under the positive-infimum hypothesis, (6) places every such profile a definite distance **above** the minimum as \(\eta\downarrow0\).

This is a quantitative obstruction to treating a punishment replacement as a free repair. It is not a contradiction: the hypotheses allow punishment profiles to have that excess debt.

## 4. Exact accounting for the supplied paid switch

Return now to the supplied endpoint \(p\). Let

$$
m_s=p_i(\{s\})>0,\qquad G=Lg\ge\frac{\delta}{16}.
$$

For \(0\le\theta\le m_s\), make the actual mass transfer

$$
p_i^\theta=p_i+\theta(\delta_t-\delta_s),
\qquad p_{-i}^\theta=p_{-i}.
$$

Because the mover’s opponents remain unchanged,

$$
B_i(p^\theta)=B_i(p),
\qquad
d_i(p^\theta)=d_i(p)-\theta G. \tag{7}
$$

The other debts admit an exact expression too. For \(j\ne i\) and a pure time \(z\), define

$$
f_j(z)=U_j(z,p_{-j}),
$$

and

$$
e_j(z)=
U_j(z,\delta_t,p_{-(i,j)})
-
U_j(z,\delta_s,p_{-(i,j)}).
$$

Writing \(\bar e_j=\int e_j(z)\,dp_j(z)\), multilinearity gives

$$
d_j(p^\theta)-d_j(p)
=
\sup_z\bigl(f_j(z)+\theta e_j(z)\bigr)
-\sup_z f_j(z)
-\theta\bar e_j. \tag{8}
$$

Both suprema include every finite date and Never.

Therefore this particular construction succeeds exactly when

$$
\boxed{\quad
\sum_{j\ne i}
\left[
\sup_z(f_j(z)+\theta e_j(z))
-\sup_z f_j(z)
-\theta\bar e_j
\right]
<
\theta G-\bigl(D(p)-D_*\bigr).
\quad} \tag{9}
$$

The survival floors establish that \(G\) is a genuine, quantitatively reached comparison. They do not themselves bound the terms in (8). Also, \(m_s\) has no supplied quantitative lower bound: the lower bound on \(d_i(p)\) need not be carried by the particular atom at \(s\).

I have not derived (9), or an alternative strict-descent construction, from the retained minimum, coalition atom, and paid-row data. In particular, the finite replacement ancestry supplies no identity equating the endpoint’s caps with \(b_*\).

**What is proved here is the actual shifted-cap prefix estimate (1), the global near-minimum bound (4), and the retained-minimum cap floor (5). The requested paid-row consumer remains unproved; this is not a negative answer to the conjecture.**

[1]: https://www.jstor.org/stable/1969529 "Non-Cooperative Games"
