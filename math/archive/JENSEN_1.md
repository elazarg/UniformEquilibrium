The two residuals behave differently.

Residual A is fully consumable: its escaped tail can be replaced by an exact periodic restart because the source pair makes every post-row history unreachable under every unilateral replacement.

Residual B does not admit the same surgery. More sharply, its persistent response edge has only finite **returnable charge**. The exact prefix scaling gives a nonzero charge holonomy between two asymptotic tracks; reusing the same edge cannot produce a charged near-return.

## 1. Residual A: exact screened restart

Write \(L_n=m_n+1\). Construct a periodic source profile \(\widehat F_n\) by repeating the live-root word of \(F_n\) through date \(m_n\):

$$
\widehat F_n(t)=F_n(t\bmod L_n)
$$

on the unique live history. Equivalently, after the marked row, the profile restarts its own first block.

### Screened-tail invariance

For every player \(j\) and every behavioral replacement \(\tau_j\),

$$
U_j(\tau_j,\widehat F_{n,-j})
=
U_j(\tau_j,F_{n,-j}).
\tag{1}
$$

Indeed, if play survives to \(m_n\), the pure quitting coalition is the pair \(C\). At most one member of \(C\) is controlled by the deviator \(j\), so some member of \(C\setminus\{j\}\) still quits surely at \(m_n\). Thus, under every unilateral replacement, play terminates no later than \(m_n\). Everything after \(m_n\) is strategically null.

Consequently, not only prescribed payoffs but all unrestricted caps and the complete terminal law are preserved:

$$
U(\widehat F_n)=U(F_n),\qquad
B(\widehat F_n)=B(F_n),\qquad
D(\widehat F_n)=D(F_n),
\tag{2}
$$

and hence

$$
D(\widehat F_n)\longrightarrow D_*.
\tag{3}
$$

This does not infer anything about the original \(T_n\). It replaces \(T_n\) on histories which are unreachable even after an arbitrary unilateral behavioral replacement.

### The paid target

Let \(\widehat G_n\) be obtained from \(\widehat F_n\) by changing only \(p\)'s prescribed action at the first marked row \(m_n\). After that row, retain the literal tail \(\widehat F_n\).

Then:

$$
\text{post-row tail of }\widehat G_n
=
\widehat F_n
\quad\text{literally}.
\tag{4}
$$

Thus the continuation state after the charged row is the exact source, not merely another minimum point.

All the marked-row data survive:

$$
\Pr_{\widehat F_n}
  (\text{terminal coalition }C\text{ at }m_n)
=
\Pr_{F_n}
  (\text{terminal coalition }C\text{ at }m_n)
\ge\lambda;
\tag{5}
$$

\(q\)'s local defect remains zero, because both of \(q\)'s endpoint choices at a pure pair row leave a nonempty quitting coalition, and therefore do not inspect the tail.

Let

$$
G_n:=U_p(\widehat G_n)-U_p(\widehat F_n).
$$

The source-pair screen shows that the tail replacement does not change this payoff difference, so

$$
G_n\ge g.
\tag{6}
$$

Since \(\widehat F_n\) and \(\widehat G_n\) differ only in \(p\)'s own strategy,

$$
B_p(\widehat G_n)=B_p(\widehat F_n).
$$

Therefore the debt subtraction is exact:

$$
d_p(\widehat G_n)
=d_p(\widehat F_n)-G_n
\le d_p(\widehat F_n)-g.
\tag{7}
$$

The routed coalition and its entire reached mass are unchanged, because the roots through \(m_n\) are unchanged. These exact gain, debt-subtraction, mass-routing and one-date-update identities are the same identities already used by the forced-pair adapter.

Equations (3)–(7) give a **source-attached positively charged exact return**:

$$
\boxed{
\widehat F_n
\;\xrightarrow[\text{one date}]{\text{charge }\ge g,\;\text{mass }\ge\lambda}\;
\widehat G_n
\;\longrightarrow\;
\widehat F_n .
}
$$

The final arrow is literal continuation equality. It is stronger than a near-return. Hence Residual A satisfies item 2, and the stated all-behavior chronological consumer yields item 1 after taking a subsequence on which \(U(\widehat F_n)\) converges.

The assumption

$$
D(T_n)\ge D_*+\delta
$$

has been completely consumed: the escaped tail is erased, rather than incorrectly declared minimal.

---

## 2. Residual B: exact radial charge-capacity identity

Apply the same prefix roots to \(S_n\), and denote the resulting sibling by \(S_{n,k}\). Put

$$
\Delta_n:=U_i(R_n)-U_i(S_n)\ge h,
$$

and

$$
\Delta_{n,k}
  :=U_i(R_{n,k})-U_i(S_{n,k}).
$$

By the supplied common-prefix scaling,

$$
\Delta_{n,k}=q_{n,k}\Delta_n.
\tag{8}
$$

The exact debt identities likewise give

$$
D(R_{n,k})=q_{n,k}D(R_n).
\tag{9}
$$

Because every payoff and cap lies in \([-M,M]\),

$$
0\le D(R_n)\le 8M.
$$

The uniform off-minimum condition therefore implies

$$
q_{n,k}
\ge
\frac{D_*+\delta}{D(R_n)}
\ge
\frac{D_*+\delta}{8M}
=:q_0>0.
\tag{10}
$$

Thus the pointwise sibling gain and the atom indeed remain macroscopic:

$$
\Delta_{n,k}\ge q_0h,
\qquad
\text{atom mass}\ge q_0a.
\tag{11}
$$

The exact prefix scaling and the late-atom/no-total-variation conclusions are checked by the fixed-tail prefix-ray and clock-escape developments.

### Persistent charge is not renewable charge

For \(k<\ell\), equations (8)–(9) give

$$
\Delta_{n,k}-\Delta_{n,\ell}
=
(q_{n,k}-q_{n,\ell})\Delta_n,
\tag{12}
$$

and

$$
D(R_{n,k})-D(R_{n,\ell})
=
(q_{n,k}-q_{n,\ell})D(R_n).
\tag{13}
$$

Consequently,

$$
\boxed{
\Delta_{n,k}-\Delta_{n,\ell}
=
\frac{\Delta_n}{D(R_n)}
\bigl(D(R_{n,k})-D(R_{n,\ell})\bigr).
}
\tag{14}
$$

This is the relevant capacity identity.

Let

$$
q_{n,\infty}:=\lim_{k\to\infty}q_{n,k}.
$$

By (10), \(q_{n,\infty}\ge q_0\). Hence the limiting sibling gap is still positive:

$$
\Delta_{n,\infty}
:=q_{n,\infty}\Delta_n
\ge q_0h.
\tag{15}
$$

The natural source-return commutator is

$$
S_{n,k}
\longrightarrow R_{n,k}
\longrightarrow R_{n,\ell}
\longrightarrow S_{n,\ell}.
$$

The first horizontal switch gains \(\Delta_{n,k}\); the final reverse switch costs \(\Delta_{n,\ell}\). Its net \(i\)-charge is therefore exactly

$$
\Delta_{n,k}-\Delta_{n,\ell}.
\tag{16}
$$

But

$$
\sup_{\ell>k}
  \bigl(\Delta_{n,k}-\Delta_{n,\ell}\bigr)
=
\Delta_{n,k}-\Delta_{n,\infty}
\longrightarrow0
\quad(k\to\infty).
\tag{17}
$$

Thus:

$$
\boxed{
\text{the edge value stays }\ge q_0h,
\quad
\text{but the amount recoverable after returning to the source track tends to }0.
}
$$

The fixed positive edge cannot be harvested once at every depth. It is the same option pushed farther into the future.

### Omitting the reverse switch does not close the path

After passing to a common semantic subsequence, let the two tracks have limits \(s_\infty\) and \(r_\infty\). Equation (15) gives

$$
(r_\infty)_i^{U}-(s_\infty)_i^{U}\ge q_0h.
\tag{18}
$$

Therefore the tracks do not have a common semantic endpoint. In particular, a path which takes the positive switch but omits the eventual reverse switch remains separated from its source by a fixed amount in \(i\)'s prescribed payoff.

So the same edge has an exact dichotomy:

$$
\begin{array}{c|c}
\text{omit the reverse switch}
  & \text{endpoint separation }\ge q_0h,\\[1mm]
\text{include the reverse switch cofinally}
  & \text{net charge }\longrightarrow0.
\end{array}
\tag{19}
$$

Compactness does not remove this dichotomy. Total-variation noncompactness prevents identifying the two limiting strategy tracks, while their semantic payoff gap already prevents identifying even their semantic pairs.

### Other-player cap leakage

For \(j\ne i\), write

$$
\Gamma_{n,k}^j
:=
B_j(R_{n,k})-B_j(S_{n,k}).
$$

A forward switch at depth \(k\), followed by a reverse switch at depth \(\ell\), has net \(j\)-cap displacement

$$
\Gamma_{n,k}^j-\Gamma_{n,\ell}^j.
\tag{20}
$$

One can take a subsequence on which the bounded vectors \(\Gamma_{n,k}\) converge. That makes (20) small for large \(k,\ell\), but by (17) it simultaneously makes the net charge small. There is no estimate of the form

$$
\sum_{j\ne i}
  \bigl(\Gamma_{n,k}^j-\Gamma_{n,\ell}^j\bigr)_+
=o\!\left(
  \Delta_{n,k}-\Delta_{n,\ell}
 \right)
\tag{21}
$$

in the supplied data.

This is exactly where an argument based only on prescribed-payoff scaling would leave unrestricted cap leakage uncontrolled.

---

## 3. What B does force

Let \(r,s\) be the two players outside \(\{o,i\}\). Uniformly in \(k\),

$$
d_o(R_{n,k})+d_i(R_{n,k})
=
q_{n,k}\bigl(d_o(R_n)+d_i(R_n)\bigr)
\longrightarrow0
$$

as \(n\to\infty\). Hence

$$
d_r(R_{n,k})+d_s(R_{n,k})
\ge D_*+\delta-o(1).
$$

After one common subsequence, one fixed player \(r\notin\{o,i\}\) satisfies

$$
d_r(R_{n,k})
\ge
\frac{D_*+\delta}{2}-o(1)
\tag{22}
$$

on a cofinal set of indices. Pure-time extremality of the quitting-game cap then gives a whole-strategy deviation of \(r\) with a fixed positive gain.

Equation (22), however, is not yet a consumer. The missing operation is now precise:

> **Second-port localization problem.** Convert the fixed debt in (22) into a literal source-attached finite macro which either:
>
> 1. reaches a screened pair and hence the exact restart construction of §1; or
> 2. produces a second escaped clock together with a closed two-clock provenance relation and an upper bound on every previously exposed cap increment.

Merely choosing \(r\)'s best response does not provide either condition. It may reopen \(o\)'s and \(i\)'s debts, and the profitable part may escape to another unbounded clock without sharing the first atom’s source.

---

## 4. A diagnostic table for the remaining obstruction

The clock mechanism in B, by itself, is compatible with an exact equilibrium. Consider the four-player table

$$
r_0(S)=r_1(S)=
 \mathbf 1_{\{0,1\}\subseteq S},
$$

and, for \(j=2,3\),

$$
r_j(S)=
 \mathbf 1_{\{0,1,j\}\subseteq S}.
$$

Let \(R_N\) have players \(0,1\) quit together at date \(N\), while \(2,3\) Never quit. Then

$$
U(R_N)=(1,1,0,0),\qquad
B(R_N)=(1,1,1,1),
$$

so

$$
d(R_N)=(0,0,1,1),\qquad D(R_N)=2.
$$

Let \(S_N\) delay player \(0\)'s quit from \(N\) to \(N+1\). The switch \(S_N\to R_N\) gains exactly \(1\) for player \(0\), and \(R_N\) has the pair atom \(\{0,1\}\) with mass \(1\).

Arbitrary all-Continue prefixes are exact cap-Nash roots against the cap vector \((1,1,1,1)\). They have \(q=1\), shift the pair atom to infinity, preserve debt \(2\), and give precisely the two-track holonomy above.

But all four players quitting immediately is an exact Nash profile, so this table has

$$
D_*=0.
$$

It is not the requested positive-gap counterexample. It shows that the escaped-clock geometry itself supplies no contradiction: the positive global minimum must be used through a new source-attached port, not merely through the scalar lower bound \(D\ge D_*+\delta\).

## Conclusion

$$
\boxed{\text{Residual A is consumed completely by screened periodic restart.}}
$$

It yields a literal source-attached charged exact return and therefore enters the all-behavior chronological consumer.

For Residual B, the strongest valid conclusion is the exact holonomy/capacity identity (14). It proves that the existing persistent edge is not renewable:

$$
\boxed{
\text{no reverse edge}
\Rightarrow\text{fixed endpoint separation},
\qquad
\text{reverse cofinally}
\Rightarrow\text{vanishing net charge}.
}
$$

Thus B still requires a genuinely new source-attached second port or a two-clock cap-controlled regeneration theorem. The present checked frontier likewise records consumption of this law-limit/prefix residual as an open producer rather than an established chronological consumer.
