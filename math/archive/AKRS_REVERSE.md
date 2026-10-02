The decisive distinction is between the **null-tail defect** and the strategic content of S.3. The null-tail defect can be removed completely. What remains is not a smaller AKRS lemma: as a theorem schema over all finite quitting games, the reverse S.3 implication is equivalent to the full approximate-equilibrium existence problem.

## 1. Nonterminating restarted tails force the all-Continue equilibrium

First consider one fixed \(\varepsilon\)-perfect S.3 witness \(x=(q_n)\).

### Lemma 1

Suppose

$$
a_{0,\infty}(x)=0
$$

but \(x\) does not have every-tail termination. Then

$$
r^i(\{i\})\le z^i+\varepsilon
\qquad\text{for every }i\in I.
\tag{8}
$$

### Proof

Choose \(m\) with \(a_{m,\infty}(x)>0\). Since

$$
a_{0,\infty}=a_{0,m}a_{m,\infty}=0,
$$

we have \(a_{0,m}=0\), so \(c(q_t)=0\) for some \(t<m\). On the other hand, \(a_{m,\infty}>0\) implies \(c(q_t)>0\) for every \(t\ge m\). There is therefore a last index

$$
L:=\max\{t:c(q_t)=0\}.
$$

The product

$$
P:=\prod_{t=L+1}^{\infty}c(q_t)
$$

is strictly positive. For \(n>L\),

$$
a_{n,\infty}
=
\frac{P}{\prod_{t=L+1}^{n-1}c(q_t)}
\longrightarrow 1.
\tag{9}
$$

Because \(a_{n,\infty}\le c(q_n)\le1\), this also gives

$$
c(q_n)\longrightarrow1.
$$

For each player \(j\),

$$
q_n^j\le 1-c(q_n),
$$

and hence

$$
q_n^j\longrightarrow0.
\tag{10}
$$

Let

$$
M_i:=\max_{\varnothing\ne S\subseteq I}
       |r^i(S)-z^i|.
$$

The total finite-terminal mass of the tail restarted at \(n\) is
\(1-a_{n,\infty}\), so

$$
|\gamma_n^i(x)-z^i|
\le M_i\bigl(1-a_{n,\infty}(x)\bigr)
\longrightarrow0.
\tag{11}
$$

By (10), the opponents’ row distribution converges to all Continue. Therefore

$$
Q_n^i(x)\longrightarrow r^i(\{i\}).
\tag{12}
$$

The first row-perfectness inequality is

$$
Q_n^i(x)\le V_n^i(x)+\varepsilon
          =\gamma_n^i(x)+\varepsilon.
$$

Letting \(n\to\infty\) and using (11)–(12) proves (8). ∎

### Corollary 2: the literal null-tail gap closes

Under S.3, exactly one of the following holds:

1. the all-Continue profile is an exact terminal Nash equilibrium; or
2. for every sufficiently small \(\varepsilon>0\), there is an S.3 witness having every-tail termination.

Indeed, suppose non-every-tail witnesses exist for a sequence
\(\varepsilon_k\downarrow0\). Lemma 1 gives

$$
r^i(\{i\})\le z^i+\varepsilon_k
$$

for every \(k\), and hence \(r^i(\{i\})\le z^i\). Against opponents who always Continue, any behavioral strategy of player \(i\) gives a convex combination of \(r^i(\{i\})\) and \(z^i\), so it cannot improve upon \(z^i\). Thus all Continue is an exact equilibrium.

Otherwise non-every-tail witnesses are absent below some positive error, and the witnesses supplied by S.3 at those errors necessarily terminate from every restarted tail.

So **null histories are not the remaining obstruction**.

---

## 2. A universal exact-S.3 padding construction

Let \(G=(I,r,z)\) be an arbitrary finite quitting game. Assume \(I\ne\varnothing\); the empty-player case is vacuous.

For each old player \(i\), put

$$
H_i:=\max\Bigl(\{z^i\}\cup
     \{r^i(S):\varnothing\ne S\subseteq I\}\Bigr),
$$

$$
L_i:=\min\Bigl(\{z^i\}\cup
     \{r^i(S):\varnothing\ne S\subseteq I\}\Bigr),
\qquad
W_i:=H_i-L_i,
$$

and let \(W:=\max_iW_i\).

Fix \(P>0\), add one new player \(d\), and define a quitting game
\(\widehat G\) on

$$
\widehat I=I\cup\{d\}.
$$

Its Never payoff is

$$
\widehat z^i=z^i\quad(i\in I),
\qquad
\widehat z^d=0.
$$

For a nonempty terminal coalition \(T\subseteq\widehat I\), write
\(S=T\cap I\).

If \(S\ne\varnothing\), define

$$
\widehat r^i(T)=r^i(S)\quad(i\in I),
\qquad
\widehat r^d(T)=0.
\tag{13}
$$

The only terminal coalition with \(S=\varnothing\) is \(\{d\}\); define

$$
\widehat r^i(\{d\})=H_i\quad(i\in I),
\qquad
\widehat r^d(\{d\})=-P.
\tag{14}
$$

This is the one-new-player instance of the passive-padding construction already represented in the formal development.  Its checked quantitative gap theorem has the same \(P/(P+W)\) factor obtained below.

### Proposition 3: the padded game satisfies a much stronger form of S.3

At every stage let

$$
q_n^d=1,
\qquad
q_n^i=0\quad(i\in I).
\tag{15}
$$

This is a stationary sequence, and every restarted tail terminates at its first row.

At every stage \(n\),

$$
\widehat\gamma_n^i=H_i\quad(i\in I),
\qquad
\widehat\gamma_n^d=-P.
$$

For an old player \(i\),

$$
C_n^i=V_n^i=H_i,
\qquad
Q_n^i=r^i(\{i\})\le H_i.
$$

For the new player,

$$
Q_n^d=C_n^d=V_n^d=-P.
$$

Consequently every row satisfies all four conditions in (5) with error exactly zero.

Thus \(\widehat G\) has a **single stationary, exact, every-tail-terminating row-perfect sequence**. In particular, it satisfies S.3 for every choice of \(\varepsilon_0>0\).

The original game \(G\) is completely hidden behind the new player’s locally credible but globally suicidal repeated Quit action.

---

## 3. Approximate equilibria retract quantitatively

For a behavioral profile \(\widehat\sigma\) of \(\widehat G\), let
\(\sigma\) be its projection to \(G\): at every survival date, every old player uses the same Quit probability as under \(\widehat\sigma\), and the new player is discarded.

Let

$$
\alpha
:=
\Pr_{\widehat\sigma}
  (\text{the terminal coalition is }\{d\}).
\tag{16}
$$

### Dummy-player estimate

The prescribed payoff of \(d\) is

$$
\widehat U_d(\widehat\sigma)=-P\alpha.
$$

If \(d\) deviates to Continue forever, her payoff is exactly zero:

* when an old player eventually quits, (13) pays \(d\) zero;
* when nobody quits, \(\widehat z^d=0\).

Hence, if

$$
\widehat e:=E_{\widehat G}(\widehat\sigma)
$$

denotes the maximal unrestricted unilateral gain at \(\widehat\sigma\), then

$$
P\alpha\le\widehat e.
\tag{17}
$$

### Old-player comparison

Couple the projected game and the padded game using exactly the same random actions for all old players, continuing to sample those actions counterfactually after a dummy-only termination.

Outside the event in (16), the old player’s payoff is exactly the same in the two games. On that event, the padded payoff is \(H_i\), while the projected game’s eventual payoff lies in \([L_i,H_i]\). Therefore

$$
U_i^G(\sigma)
\le
U_i^{\widehat G}(\widehat\sigma)
\le
U_i^G(\sigma)+\alpha W_i.
\tag{18}
$$

Now take an arbitrary behavioral deviation \(\tau_i\) in \(G\), and lift it to the same date-dependent strategy \(\widehat\tau_i\) in \(\widehat G\). Again, a dummy-only termination replaces the projected eventual payoff by its upper bound \(H_i\). Consequently

$$
U_i^G(\tau_i,\sigma^{-i})
\le
U_i^{\widehat G}
   (\widehat\tau_i,\widehat\sigma^{-i}).
\tag{19}
$$

Using (18), (19), and the definition of \(\widehat e\),

$$
\begin{aligned}
U_i^G(\tau_i,\sigma^{-i})
&\le
U_i^{\widehat G}
   (\widehat\tau_i,\widehat\sigma^{-i})\\
&\le
U_i^{\widehat G}(\widehat\sigma)+\widehat e\\
&\le
U_i^G(\sigma)+\alpha W_i+\widehat e\\
&\le
U_i^G(\sigma)
+\widehat e\left(1+\frac{W_i}{P}\right).
\end{aligned}
$$

Taking the supremum over \(\tau_i\) and then the maximum over old players gives

$$
\boxed{
E_G(\sigma)
\le
\left(1+\frac WP\right)
E_{\widehat G}(\widehat\sigma).
}
\tag{20}
$$

Equivalently,

$$
\boxed{
E_{\widehat G}(\widehat\sigma)
\ge
\frac{P}{P+W}\,
E_G(\sigma).
}
\tag{21}
$$

This is an unrestricted behavioral-strategy estimate; no stationarity, bounded stopping time, or supplied-profile assumption is being made.

---

## 4. Equivalence with the full approximate-equilibrium problem

Write \(\mathsf{AE}(G)\) for terminal approximate-equilibrium existence and
\(\mathsf{S3}(G)\) for the hypothesis in the question.

At each player cardinality \(n\),

$$
\boxed{
\begin{array}{c}
\text{R-S.3 for every \((n+1)\)-player game}
\\[2mm]\Longrightarrow\\[2mm]
\text{approximate-equilibrium existence for every \(n\)-player game}.
\end{array}}
\tag{22}
$$

Indeed, apply R-S.3 to the padded game \(\widehat G\), which satisfies exact stationary every-tail S.3. Given \(\eta>0\), choose a padded profile with

$$
E_{\widehat G}(\widehat\sigma)
\le
\eta\,\frac{P}{P+W}.
$$

Its projection satisfies \(E_G(\sigma)\le\eta\) by (20).

The converse implication at the universal level is tautological: if every finite quitting game has approximate equilibria, then in particular every game satisfying S.3 has them. Hence

$$
\boxed{
\left[
\forall G,\ \mathsf{S3}(G)\Rightarrow\mathsf{AE}(G)
\right]
\iff
\left[
\forall G,\ \mathsf{AE}(G)
\right].
}
\tag{23}
$$

In fact, the left side can be strengthened drastically without changing this equivalence:

> Every finite quitting game admitting one stationary, exactly row-perfect, every-tail-terminating sequence has approximate equilibria.

The padding above already satisfies that stronger premise.

There is also an exact negative transport. If an original game satisfies

$$
E_G(\sigma)\ge\gamma
\qquad\text{for every }\sigma,
$$

then its padded game satisfies exact every-tail S.3 and, by (21),

$$
E_{\widehat G}(\widehat\sigma)
\ge
\frac{P}{P+W}\gamma
\qquad\text{for every }\widehat\sigma.
\tag{24}
$$

Thus an explicit counterexample to general approximate-equilibrium existence would immediately give the explicit S.3 counterexample requested in the question, with one additional player. Conversely, an S.3 counterexample is already a general quitting-game counterexample.

---

## 5. Why the normalized theorem does not cover the padding

Subtracting \(z^i\) from every outcome of player \(i\) sets the Never payoff to zero and shifts \(Q_n^i,C_n^i,V_n^i,\gamma_n^i\) by the same amount. It therefore preserves both (5) and every unilateral gain. Arbitrary \(z\) is harmless.

The unit-singleton normalization is different. A positive affine transformation preserves the sign of

$$
r^i(\{i\})-z^i.
$$

For the added player,

$$
\widehat r^d(\{d\})-\widehat z^d=-P<0,
$$

so no preference-preserving normalization turns this coordinate into the unit-singleton condition.

The same point appears through punishment normality. In the normalized padded game, \(d\) can always guarantee zero by Never, while opponents who always Continue hold her best-response value to zero. Thus

$$
\operatorname{Pun}_d(\widehat r)=0
>
-P=\widehat r^d(\{d\}),
$$

so \(d\) is abnormal.

The current formal source contains a direct theorem proving R-S.3 when every player is punishment-normal, using literal initial absorption rather than every-tail termination.  An abnormal player necessarily has a negative singleton payoff and a nonpositive punishment value, with other singleton exits lying above her punishment floor.  The padding shows that this abnormal-player residue can encode an arbitrary quitting game.

Consequently, any unresolved instance can be reduced to the regime

$$
\text{some positive singleton gap}
\quad+\quad
\text{some abnormal negative-singleton player}.
$$

If all singleton gaps are nonpositive, all Continue is exact. If every player is normal, the existing normal-player compiler applies. The mixed abnormal regime is precisely where the general problem survives.

## Conclusion

The mathematical resolution of the purported “null-tail gap” is:

$$
\boxed{
\begin{array}{l}
\text{Non-every-tail S.3 witnesses at vanishing errors force the exact}\\
\text{all-Continue equilibrium. Hence null histories can be eliminated.}
\end{array}}
$$

But after that repair,

$$
\boxed{
\text{unrestricted reverse S.3}
\quad\text{is equivalent, universally, to}\quad
\text{general finite quitting-game approximate-equilibrium existence}.
}
$$

So adding every-tail termination does not settle the unrestricted statement: the one-player padding already satisfies exact stationary every-tail perfection. The remaining issue is the abnormal negative-singleton player, not the restarted-tail convention.

The current repository frontier likewise records an all-normal consumer but no universal consumer and no counterexample, and the AKRS errata classifies the unrestricted reverse implication as a genuine gap rather than a proved theorem or a known false statement.   The source and status were checked against the current repository rather than a remembered revision, following the supplied runbook. 
