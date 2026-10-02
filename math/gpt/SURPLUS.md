The added costate hypothesis does not consume the escape branch. On the only hard branch, it is already forced by the positive-minimum plateau—and in fact every nonzero nonnegative static costate is excluded. What remains is precisely a missing **escape-to-exact-Nash–Bellman promotion theorem**.

Let

$$
D_*:=D(z),\qquad N:=|I|.
$$

## 1. The zero-minimum branch gives outcome 2

Suppose first that \(D_*=0\). Since the semantic pairs of \(\sigma_n\) converge to \(z\),

$$
D(\sigma_n)\longrightarrow 0,
\qquad
U(\sigma_n)\longrightarrow u.
$$

Every coordinate debt is nonnegative, so

$$
0\le d_i(\sigma_n)\le D(\sigma_n).
$$

Hence, for every unilateral behavioral replacement \(\tau_i\),

$$
U_i(\tau_i,\sigma_{n,-i})-U_i(\sigma_n)
   \le B_i(\sigma_n)-U_i(\sigma_n)
   \le D(\sigma_n).
$$

Thus \(\sigma_n\) is a terminal \(D(\sigma_n)\)-Nash profile and its payoff converges to the single vector \(u\). This is exactly outcome 2.

The rest of the argument therefore concerns \(D_*>0\).

## 2. In the positive branch, outcome 1 is impossible and the supplied table already has an abstract gap

Global minimality gives, for every actual profile \(\sigma\),

$$
D(\sigma)\ge D_*.
$$

Consequently outcome 1 cannot occur.

Moreover,

$$
\max_i d_i(\sigma)\ge \frac{D_*}{N}.
$$

Choose \(i\) attaining this lower bound. Since \(B_i(\sigma)\) is the supremum over actual behavioral replacements, there is a replacement \(\tau_i\) such that

$$
U_i(\tau_i,\sigma_{-i})-U_i(\sigma)
   > d_i(\sigma)-\frac{D_*}{2N}
   \ge \frac{D_*}{2N}.
$$

Therefore the supplied table satisfies

$$
\boxed{
\forall \sigma\ \exists i,\tau_i:\quad
U_i(\tau_i,\sigma_{-i})-U_i(\sigma)
   >\frac{D_*}{2N}.
}
\tag{1}
$$

So the hard branch is already a conditional all-behavior positive-gap table. It is not outcome 4 as stated because the entries of \(r\) have not been exhibited and the global lower bound \(D_*>0\) has been assumed rather than certified by a finite table-specific certificate.

## 3. The no-costate condition is redundant

At a positive global minimum, the minimum-plateau theorem gives, for every \(i\),

$$
u_i\ge s_i,
\qquad
D_*\le b_i-s_i.
\tag{2}
$$

It also says that all Continue is an exact Nash self-loop at \(u\).

Since \(d_i=b_i-u_i\), (2) implies

$$
u_i-s_i
  =(b_i-s_i)-d_i
  \ge D_*-d_i
  \ge0.
\tag{3}
$$

If \(u_i=s_i\), then (3) forces \(d_i\ge D_*\). But \(d_i\le\sum_jd_j=D_*\), so

$$
d_i=D_*,
\qquad
d_j=0\quad(j\ne i).
$$

Applying (3) to \(j\ne i\) then gives

$$
u_j-s_j\ge D_*>0.
$$

Thus:

$$
\boxed{\text{At most one coordinate satisfies }u_i=s_i.}
\tag{4}
$$

Now suppose that \(\theta\ge0\) has at least two positive coordinates and

$$
\theta\cdot(r(S)-s)\le0
\qquad\text{for every nonempty }S.
$$

Write \(q=m^*(\mathrm{Never})\). Since \(u\) is the reward moment of \(m^*\),

$$
\begin{aligned}
\theta\cdot u
 &=\sum_S m^*(S)\,\theta\cdot r(S)\\
 &\le \sum_Sm^*(S)\,\theta\cdot s\\
 &=(1-q)\theta\cdot s\\
 &\le\theta\cdot s,
\end{aligned}
\tag{5}
$$

where the last inequality uses \(s\ge0\) and \(\theta\ge0\).

But (4), together with the fact that \(\theta\) has at least two positive coordinates, gives

$$
\theta\cdot(u-s)>0,
$$

contradicting (5). Therefore the stated no-costate property follows automatically from \(D_*>0\).

There is a stronger conclusion. Suppose a one-coordinate costate existed, say

$$
r_i(S)\le s_i\qquad\text{for every }S.
$$

Because \(s_i\ge0\), every terminal outcome—including Never—then pays player \(i\) at most \(s_i\). Hence

$$
B_i(\sigma_n)\le s_i
\qquad\text{for every }n,
$$

and therefore \(b_i\le s_i\). This contradicts the singleton margin

$$
D_*\le b_i-s_i.
$$

Thus, without using the additional costate assumption,

$$
\boxed{
\not\exists\,\theta\ge0,\ \theta\ne0:
\quad
\theta\cdot(r(S)-s)\le0
\quad\text{for all }S.
}
\tag{6}
$$

By finite-dimensional strict separation, (6) is equivalent to the existence of a probability vector \(\lambda\) on the nonempty coalitions such that

$$
\boxed{
\sum_S\lambda_S r_i(S)>s_i
\qquad(i\in I).
}
\tag{7}
$$

Equation (7) is the strongest purely static consequence: there is a correlated coalition lottery strictly above the singleton vector in every coordinate.

It is not yet a behavioral construction.

## 4. The same sequence does yield an actual deep charged block

Let

$$
A:=\sum_S e(S)R(S)
  =\delta+\sum_i\bigl(b_i-B_i(\bar\sigma)\bigr)>0.
$$

The escape account proves the nonnegative cap drops and the exact identity, but explicitly does not produce a downstream consumer.

Nevertheless, the escape can be localized into an actual finite chronological block.

Let \(p_n(t,S)\) be the probability under \(\sigma_n\) that the first quitting coalition is \(S\) at date \(t\). For a fixed cutoff \(T\), finite-cut convergence gives

$$
\sum_{t<T,S}p_n(t,S)R(S)
 \longrightarrow
\sum_{t<T,S}\bar p(t,S)R(S).
$$

Total terminal-law convergence gives

$$
\sum_{t,S}p_n(t,S)R(S)
 \longrightarrow
\sum_Sm^*(S)R(S).
$$

Subtracting,

$$
\lim_n\sum_{t\ge T,S}p_n(t,S)R(S)
 =
 \sum_Sm^*(S)R(S)
 -
 \sum_{t<T,S}\bar p(t,S)R(S).
$$

As \(T\to\infty\), the right-hand side tends to

$$
\sum_S\bigl(m^*(S)-m(S)\bigr)R(S)=A.
$$

Hence, for every prescribed depth \(T_0\), there are \(T\ge T_0\), an index \(n\), and a finite \(L>T\) such that

$$
\sum_{t=T}^{L-1}\sum_Sp_n(t,S)R(S)>\frac A4.
\tag{8}
$$

This is a literal finite block of the original actual profile \(\sigma_n\), not merely escaped mass.

Let

$$
M_R:=\max_S |R(S)|>0.
$$

Equation (8) implies that the unconditional absorption mass in this block is at least \(A/(4M_R)\). Conditioning on survival to \(T\) can only increase that bound. Therefore the actual suffix block has cumulative absorption probability—and hence cumulative raw root charge—at least

$$
\boxed{\kappa:=\frac{A}{4M_R}>0.}
\tag{9}
$$

Thus the same realizing sequence supplies cofinally deep, source-matched, actual finite blocks with a fixed positive charge floor.

## 5. Why this is still not an admissible-payoff return

Two fields remain missing, and neither is supplied by the static separation.

First, the roots in the block obtained above are arbitrary prescribed roots. A punishment-floor admissible edge requires an **exact Nash–Bellman edge**, and its charge is the literal root absorption mass. The checked relation is a decoder for such exact paths; it makes no strategic-producer or reachability claim.

This distinction is particularly sharp at \(z\): every exact Nash root against the prescribed coordinate of a positive minimum is collision-free, and any singleton quitter must carry the entire total debt.  Consequently, if the positive escaped surplus is carried by a nonsingleton coalition, exact Nashification at the same minimum tail necessarily removes that collision. If it is carried by a singleton, one still lacks an endpoint return and a source-preserving connector to the corresponding critical face.

Second, (7) is a correlated lottery, not a product stopping-law or Nash–Bellman chronology. The distinction can already be seen statically. Put \(s=0\) for three labels and set

$$
\begin{aligned}
r(\{1,2\})&=(2,2,-1),\\
r(\{1,3\})&=(2,-1,2),\\
r(\{2,3\})&=(-1,2,2).
\end{aligned}
$$

Their sum is \((3,3,3)\), so for every nonzero \(\theta\ge0\), at least one of these three coalitions has positive \(\theta\)-value. Thus there is no nonzero static costate. The uniform lottery on the three pairs has expectation \((1,1,1)\).

But it is not the absorption law of one product root: positive mass on all three pairs forces all three quit probabilities to lie strictly between zero and one, which also forces positive singleton and triple mass. If one additionally sets

$$
r(\{1,2,3\})=(3,-1,-1),
$$

then an escaped law concentrated on the triple has positive social reward \(1\), while being unrelated coordinatewise to the Farkas lottery. This example is only an algebraic obstruction to the proposed inference, not a positive-gap quitting-game counterexample.

A dual argument does not repair the mismatch automatically. Across a chronological cut, the later costate is reweighted and pulled back by the survival adjoint; it is generally not the original static \(\theta\). The existing flow–costate identity explicitly separates this transported algebra from downstream strategic feasibility.  Thus failure of a charged return would have to be shown to produce a *constant* nonnegative costate satisfying the displayed coalition inequalities. The present hypotheses do not provide that collapse.

Nonnegative singleton rewards do solve the final refusal problem once an absorbing exact Nash–Bellman cycle has been obtained: the nonnegative-singleton disjunct makes every coordinate admissible, and the periodic profile is then a terminal approximate equilibrium against all behavioral deviations.  The missing step is the production of that exact cyclic chronology.

## 6. Exact residual theorem required

The escape branch would close with the following promotion theorem.

There must be a fixed \(\kappa>0\) such that the cofinally deep actual blocks from (9) yield one of:

$$
\begin{array}{ll}
\text{(a)}&
\text{an actual profile with }D<D_*;\\[2mm]
\text{(b)}&
\text{for every }\eta>0,\text{ a source-attached finite path of exact}\\
&
\text{punishment-floor Nash--Bellman edges with charge at least }\kappa,\\
&
\text{whose initial and terminal prescribed payoffs are }\eta\text{-close};\\[2mm]
\text{(c)}&
\text{a source-preserving transition to a strictly smaller finite rank.}
\end{array}
\tag{10}
$$

Failure of all three would then have to produce a nonzero **static** nonnegative costate. Current flow duality only produces transported, potentially signed costates, so that last implication is precisely the unproved part.

Accordingly, the exact conclusion from the stated data is

$$
\boxed{
D_*=0\Longrightarrow\text{outcome 2},
}
$$

whereas if \(D_*>0\),

$$
\boxed{
\text{outcome 1 is impossible, the given table has gap }
\frac{D_*}{2|I|},
\text{ and the no-costate hypothesis is automatic.}
}
$$

The same escaped law does produce the actual uniformly charged blocks in (8)–(9), but not their exact Nash–Bellman certification or endpoint return. Replacing that missing certification by either the positive coalition \(S\) or the Farkas lottery (7) would conflate terminal-law closure with current product-root absorption—the precise step excluded by the question’s boundary.
