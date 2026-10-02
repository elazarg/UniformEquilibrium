The quantification over **all finite player sets** is decisive here. Adding one player can make (A) hold—with exact row perfection and every-tail termination—while preserving whether approximate equilibria exist.

The result I can establish is:

> **Reduction theorem.** The universal assertion (R) is equivalent to unrestricted approximate-equilibrium existence for finite quitting games. This remains true when (A) is strengthened to require a single stationary, exactly row-perfect witness that terminates after every restart. The witness can have positive survival probability through every finite date.

This is not a proof or refutation of (R). The reduction below establishes its logical strength, with explicit bounds against all behavioral deviations.

## 1. Add a player whose quitting rewards everyone else

Start with an **arbitrary** quitting game \(G=(I,r,z)\), with \(I\ne\varnothing\). Set

$$
L_i:=\min\bigl(\{z^i\}\cup\{r^i(S):\varnothing\ne S\subseteq I\}\bigr),
$$

$$
H_i:=\max\bigl(\{z^i\}\cup\{r^i(S):\varnothing\ne S\subseteq I\}\bigr),
\qquad
W_i:=H_i-L_i,\qquad W:=\max_iW_i.
$$

Fix \(K>0\).

Construct a game \(\widehat G\) with players

$$
\widehat I=I\cup\{\star\}.
$$

Its Never payoff is

$$
\widehat z^i=z^i\quad(i\in I),\qquad \widehat z^\star=0.
$$

For every nonempty \(S\subseteq\widehat I\), define

$$
\widehat r^i(S)=
\begin{cases}
r^i(S),&\star\notin S,\\
H_i,&\star\in S,
\end{cases}
\qquad(i\in I),
\tag{7}
$$

and

$$
\widehat r^\star(S)=
\begin{cases}
0,&\star\notin S,\\
-K,&\star\in S.
\end{cases}
\tag{8}
$$

Thus player \(\star\) can guarantee zero by choosing Never, and loses \(K\) whenever she participates in the terminal coalition. Whenever she does participate, every original player receives her highest possible payoff.

The construction preserves rationality when the original table and \(K\) are rational.

## 2. The enlarged game always satisfies (A), exactly

Fix any \(\alpha\in(0,1]\). At every date prescribe

$$
q_n^\star=\alpha,\qquad q_n^i=0\quad(i\in I).
\tag{9}
$$

Every restarted tail terminates almost surely, with terminal coalition \(\{\star\}\). Hence, for every \(n\),

$$
\gamma_n^i=H_i\quad(i\in I),
\qquad
\gamma_n^\star=-K.
\tag{10}
$$

For an original player \(i\),

$$
Q_n^i
=(1-\alpha)r^i(\{i\})+\alpha H_i
\le H_i,
$$

whereas

$$
C_n^i=\alpha H_i+(1-\alpha)\gamma_{n+1}^i=H_i,
\qquad V_n^i=H_i.
$$

Since her prescribed action is Continue, all four requirements in (5) hold with error zero.

For player \(\star\),

$$
Q_n^\star=-K,\qquad
C_n^\star=\gamma_{n+1}^\star=-K,\qquad
V_n^\star=-K.
$$

Again, all four requirements hold with error zero.

Consequently, **the same sequence witnesses (A) for every positive error**.

Moreover,

$$
a_{m,N}=(1-\alpha)^{N-m}.
$$

Taking \(\alpha=\tfrac12\) gives positive survival through every finite date and termination after every restart. Taking \(\alpha=1\) gives immediate termination after every restart. Taking arbitrarily small \(\alpha>0\) gives exact row-perfect witnesses with arbitrarily small stationary quitting probabilities.

This is not rescued by the all-Continue alternative: if all Continue is not an equilibrium of \(G\), it is not an equilibrium of \(\widehat G\), because the original singleton and Never payoffs are unchanged.

## 3. Every approximate equilibrium of the enlarged game projects to one of the original game

Let

$$
\widehat\sigma=(\sigma,\rho^\star)
$$

be an arbitrary behavioral profile of \(\widehat G\). Here \(\sigma\) consists of the original players’ strategies.

Represent these strategies by independent stopping laws, as in the question. Let \(T_i\) be the original players’ stopping times, let

$$
T:=\min_{i\in I}T_i,
$$

and let \(T_\star\) be the added player’s stopping time. Define

$$
\mathcal D:=\{T_\star<\infty,\ T_\star\le T\},
\qquad p:=\Pr(\mathcal D).
$$

Thus \(\mathcal D\) is precisely the event that \(\star\) belongs to the terminal coalition.

Let \(Y_i\) be the original-game terminal payoff obtained from the original stopping times, including \(z^i\) when \(T=\infty\). Coupling the two games using these same stopping times gives

$$
\widehat Y_i
=
Y_i+\mathbf 1_{\mathcal D}(H_i-Y_i).
$$

Since \(L_i\le Y_i\le H_i\),

$$
0\le U_i^{\widehat G}(\widehat\sigma)-U_i^G(\sigma)
\le W_i p.
\tag{11}
$$

Meanwhile,

$$
U_\star^{\widehat G}(\widehat\sigma)=-Kp.
$$

Player \(\star\)’s best-response value is exactly zero: all her possible payoffs are nonpositive, and Never guarantees zero. Therefore her unilateral gain is exactly

$$
d_\star^{\widehat G}(\widehat\sigma)=Kp.
\tag{12}
$$

Now suppose \(\widehat\sigma\) is a terminal \(\delta\)-Nash equilibrium. Equation (12) implies

$$
p\le \frac{\delta}{K}.
\tag{13}
$$

Fix an original player \(i\) and **any** unilateral behavioral deviation \(\tau^i\). Apply the same coupling to the deviating profile. Adding \(\star\) can only increase player \(i\)’s payoff, so

$$
U_i^G(\tau^i,\sigma^{-i})
\le
U_i^{\widehat G}(\tau^i,\widehat\sigma^{-i}).
\tag{14}
$$

**No bound on the probability of \(\mathcal D\) under the deviation is needed.** That probability may become large. The comparison remains valid because \(\star\)’s intervention gives the deviator her maximal payoff rather than a punishment.

Combining (11), (13), (14), and the equilibrium inequality in \(\widehat G\),

$$
\begin{aligned}
U_i^G(\tau^i,\sigma^{-i})
&\le U_i^{\widehat G}(\tau^i,\widehat\sigma^{-i})\\
&\le U_i^{\widehat G}(\widehat\sigma)+\delta\\
&\le U_i^G(\sigma)+W_i p+\delta\\
&\le U_i^G(\sigma)+\left(1+\frac{W_i}{K}\right)\delta.
\end{aligned}
$$

Thus

$$
\boxed{
\widehat\sigma\text{ is }\delta\text{-Nash}
\quad\Longrightarrow\quad
\sigma\text{ is }\left(1+\frac WK\right)\delta\text{-Nash}.
}
\tag{15}
$$

This controls unrestricted deviations, including arbitrarily late stopping and Never.

Conversely, any terminal \(\delta\)-Nash profile \(\sigma\) of \(G\) lifts to a terminal \(\delta\)-Nash profile

$$
(\sigma,\mathrm{Never})
$$

of \(\widehat G\). Every original player’s payoff and deviation payoffs are unchanged, while \(\star\) already obtains her maximal payoff zero.

Hence

$$
\boxed{
G\text{ has approximate equilibria}
\iff
\widehat G\text{ has approximate equilibria}.
}
\tag{16}
$$

The same argument also preserves existence of an exact terminal Nash equilibrium.

## 4. Quantitative preservation of a positive gap

Write

$$
e_G(\sigma):=\max_i\bigl(B_i^G(\sigma)-U_i^G(\sigma)\bigr),
\qquad
g(G):=\inf_\sigma e_G(\sigma).
$$

The proof actually gives, for every enlarged profile,

$$
d_i^G(\sigma)
\le
d_i^{\widehat G}(\widehat\sigma)
+\frac{W_i}{K}d_\star^{\widehat G}(\widehat\sigma).
\tag{17}
$$

Together with the Never lift, this yields

$$
\boxed{
\frac{g(G)}{1+W/K}
\le g(\widehat G)\le g(G).
}
\tag{18}
$$

In particular, if the original table, including \(z\), lies in \([-1,1]\), choose \(K=1\). The enlarged table also lies in \([-1,1]\), and

$$
g(\widehat G)\ge \frac{g(G)}3.
$$

So any positive-gap counterexample can be converted into one satisfying (A), without losing the positive gap.

## What this establishes about (R)

Assume (R) for every finite player set. Given arbitrary \(G\), construct \(\widehat G\). Section 2 supplies its exact row-perfect witnesses. Applying (R) and then (15) produces terminal \(\eta\)-Nash equilibria of \(G\) for every \(\eta>0\).

The reverse implication is immediate: universal approximate-equilibrium existence implies (R). Therefore

$$
\boxed{
\text{Universal (R)}
\iff
\text{every finite quitting game has approximate terminal equilibria}.
}
$$

In particular, **the five-player case of (R) already contains the unrestricted four-player existence problem**, even with a fixed exact stationary source and no nonterminating restarted tails.

The mechanism is specific: row perfection allows \(\star\) to regard “Continue now, then follow the prescribed strategy” as worth \(-K\), although the complete deviation Never guarantees zero. Giving everyone else maximal rewards when \(\star\) quits ensures that this artificial source cannot make approximate-equilibrium existence easier.

The unresolved part of this response is the truth of (R) itself. The reduction proves neither universal existence nor an explicit counterexample; it shows that the stated source hypothesis does not reduce the universal existence problem, even after eliminating null-tail and accumulated-error issues.
