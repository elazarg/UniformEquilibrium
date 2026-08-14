# Question 191: Singleton-tight minimum-face iteration

## Setting

Let \(I\) be a finite player set with at least two players, and let
\(r(S)\in\mathbb R^I\) be bounded quitting rewards. For a behavioral profile
\(\sigma\), write \(U(\sigma)\) for terminal payoff and \(B(\sigma)\) for the
coordinatewise best-response value. Put

\[
\mathcal K=\overline{\{(U(\sigma),B(\sigma)):\sigma
\text{ is behavioral}\}},
\qquad
d_i(u,b)=b_i-u_i,
\qquad
D(u,b)=\sum_i d_i(u,b).
\]

Assume \(p=(u,b)\in\mathcal K\) is a global minimizer with
\(D(p)=D_*>0\). Assume there is a unique debtor \(h\):

\[
d_h(p)=D_*,\qquad d_j(p)=0\quad(j\ne h),
\]

and that the owner is singleton-tight,

\[
u_h=r_h(\{h\}).
\]

At such a minimum point, every outsider satisfies the exact singleton
clearance inequality

\[
u_j-r_j(\{j\})\geq D_*\qquad(j\ne h).
\]

The set \(I\setminus\{h\}\) is nonempty. Define

\[
G=\max_{j\ne h}
\bigl[r_j(\{h,j\})-r_j(\{h\})\bigr]_+
\]

and choose

\[
0<q\leq\frac{D_*}{D_*+G}.
\]

Let \(x\) be the product row in which \(h\) Quits with probability \(q\) and
every outsider Continues surely.

## Question

Does this candidate row iterate on the same singleton-tight minimum face?
More precisely, prove or refute the following chain.

1. The row \(x\) is exact Nash against the prescribed payoff of \(p\).
   In particular, prove that singleton tightness makes \(h\) indifferent and
   that every \(j\ne h\) satisfies

   \[
   Q_j-C_j
   =(1-q)\bigl(r_j(\{j\})-u_j\bigr)
   +q\bigl(r_j(\{h,j\})-r_j(\{h\})\bigr)
   \leq0.
   \]
2. If \(p_{n+1}=T_xp_n\) and \(p_0=p\), then every \(p_n\) belongs to
   \(\mathcal K\), has total debt \(D_*\), has \(h\) as its unique debtor, and
   remains singleton-tight at \(h\).
3. The same fixed \(q>0\) therefore makes \(x\) exact Nash against every
   prescribed payoff \(u^{(n)}\).
4. The finite prefixes \(T_x^np\) converge to the semantics of the stationary
   profile which repeats \(x\).
5. The limiting outsider inequalities are

   \[
   r_j(\{h\})-r_j(\{j\})\geq D_*\qquad(j\ne h).
   \]

   If \(r_h(\{h\})\geq0\), the stationary profile is an exact terminal Nash
   profile, including against the owner's deviation to never Quit.

Here \(T_x\) is the semantic prefix operator: its prescribed coordinate is
the payoff from playing \(x\) and then using the old prescribed payoff after
unanimous Continue, while its cap coordinate permits a current pure endpoint
choice and then uses the old best-response cap.

## Acceptance criterion

An affirmative answer must prove all five steps, including arbitrary
behavioral deviations in the stationary limit; one-row complementarity alone
is insufficient. A counterexample must satisfy every displayed hypothesis,
including membership of \(p\) in the compact semantic carrier and global
minimality. It must identify the first failed step. An arbitrary algebraic
pair \((u,b)\) outside the carrier is not a counterexample.

## Answer

**Status: strict narrowing, not a complete affirmative or negative answer.**
The finite-prefix iteration, its full semantic limit, the stationary
best-response calculation against arbitrary behavioral deviations, and the
exact equality criterion below are proved in
[`Research/Quitting/SingletonTightMinimumFaceIteration.lean`](../../Research/Quitting/SingletonTightMinimumFaceIteration.lean).  What is not
proved is that the retained owner cap must vanish.  No example satisfying the
positive-global-minimum hypotheses and violating that equality is known
either.  Thus the acceptance criterion is not yet met: the five-step question
has been reduced exactly to the scalar condition (b_h=0).

There are two different limits here:

[
\lim_{n\to\infty}T_x^n p
]

is a limit of finite-prefix semantic pairs, whereas the stationary profile repeating (x) replaces the old tail by eternal repetition. They agree on prescribed payoffs and outsider caps, but the owner’s best-response cap need not agree. This is the first obstruction.

Write

[
a_i:=r_i({h}),\qquad
s_j:=r_j({j}),\qquad
t_j:=r_j({h,j})\quad(j\ne h).
]

Thus (a_h=u_h) and (b_h=a_h+D_*).

## 1. The row is exact Nash against (u)

For (h), all opponents Continue. Its two pure endpoints are

[
Q_h=a_h,\qquad C_h=u_h=a_h.
]

Thus singleton tightness makes (h) exactly indifferent.

For an outsider (j), Continue gives

[
C_j=(1-q)u_j+q a_j,
]

while Quit gives

[
Q_j=(1-q)s_j+q t_j.
]

Consequently,

[
Q_j-C_j
=(1-q)(s_j-u_j)+q(t_j-a_j).
]

Using (u_j-s_j\ge D_*),

[
\begin{aligned}
Q_j-C_j
&\le -(1-q)D_*+q[t_j-a_j]*+\
&\le -(1-q)D**+qG.
\end{aligned}
]

The choice of (q) is equivalent to

[
qG\le (1-q)D_*,
]

so (Q_j-C_j\le0). Since (j) is prescribed to Continue, it is playing a best response. Hence Step 1 is correct.

## 2–3. The fixed row really does iterate on the minimum face

First, (T_x\mathcal K\subseteq\mathcal K). Indeed, if semantic pairs of actual profiles (\sigma_m) converge to (z\in\mathcal K), prefixing every (\sigma_m) by the fixed finite row (x) gives actual profiles whose semantic pairs are (T_xz_m). The one-root formulas are affine followed by finite maxima, hence continuous, so (T_xz_m\to T_xz).

Suppose inductively that

[
u_h^{(n)}=a_h,\qquad
b_h^{(n)}=a_h+D_*,
]

and, for (j\ne h),

[
b_j^{(n)}=u_j^{(n)}.
]

Since (p_n\in\mathcal K), has total debt (D_*), and has the same unique-debtor singleton-tight form, the stated singleton-clearance lemma applies again:

[
u_j^{(n)}-s_j\ge D_*\qquad(j\ne h).
]

Therefore the calculation from Step 1, with (u_j) replaced by (u_j^{(n)}), again shows that the same fixed (q) makes (x) exact Nash against (u^{(n)}).

The prescribed coordinates satisfy

[
u_h^{(n+1)}
=q a_h+(1-q)u_h^{(n)}
=a_h
]

and

[
u_j^{(n+1)}
=q a_j+(1-q)u_j^{(n)}.
]

For (h), because a deviating (h) can Continue through the root with probability one,

[
b_h^{(n+1)}
=\max{a_h,b_h^{(n)}}
=b_h^{(n)}
=a_h+D_*.
]

For (j\ne h),

[
b_j^{(n+1)}
===========

\max\left{
(1-q)s_j+qt_j,;
q a_j+(1-q)b_j^{(n)}
\right}.
]

The second entry equals (u_j^{(n+1)}), and exactness gives that the first is no larger. Hence

[
b_j^{(n+1)}=u_j^{(n+1)}.
]

It follows that

[
d_h(p_{n+1})=D_*,
\qquad
d_j(p_{n+1})=0\quad(j\ne h).
]

Thus (D(p_{n+1})=D_*), (h) remains the unique debtor, and singleton tightness remains exact. Steps 2 and 3 are correct.

Explicitly,

[
u_j^{(n)}
=a_j+(1-q)^n(u_j-a_j),
\qquad
b_j^{(n)}=u_j^{(n)},
]

while

[
u_h^{(n)}=a_h,\qquad b_h^{(n)}=a_h+D_*.
]

## 4. The first failed identification

The finite-prefix semantic pairs therefore converge to

[
\bar p=(\bar u,\bar b),
]

where

[
\bar u_i=a_i=r_i({h}),
]

and

[
\bar b_h=a_h+D_*,
\qquad
\bar b_j=a_j\quad(j\ne h).
]

Since (\mathcal K) is closed, (\bar p\in\mathcal K), and (D(\bar p)=D_*).

Now consider the actual stationary profile (\sigma^x) which repeats (x) forever. Under its prescribed play, (h) eventually Quits with probability one, so

[
U_i(\sigma^x)=a_i.
]

The outsider best-response values can be computed against arbitrary behavioral deviations. For (j\ne h), set

[
\ell_j:=(1-q)s_j+qt_j.
]

The limiting singleton clearance gives

[
a_j-s_j\ge D_*,
]

and hence

[
\ell_j-a_j
=(1-q)(s_j-a_j)+q(t_j-a_j)
\le -(1-q)D_*+qG
\le0.
]

Consider any behavioral deviation by (j). At every surviving date, if (j) chooses Quit, its conditional expected terminal payoff is exactly (\ell_j): with probability (1-q) it Quits alone, and with probability (q) it Quits simultaneously with (h). If (j) Continues and (h) Quits, its payoff is (a_j).

Because (q>0), termination occurs almost surely. Thus for some (\lambda\in[0,1]), the deviation payoff has the form

[
\lambda \ell_j+(1-\lambda)a_j\le a_j.
]

Therefore

[
B_j(\sigma^x)=a_j\qquad(j\ne h).
]

For (h), all outsiders Continue forever. Under any behavioral deviation, either (h) eventually Quits, yielding (a_h), or it never Quits, yielding (0). Hence

[
B_h(\sigma^x)=\max{a_h,0}.
]

The actual stationary semantic pair is consequently

[
\left(
(a_i)*{i\in I},
\left(\max{a_h,0},(a_j)*{j\ne h}\right)
\right).
]

Comparing with (\bar p), Step 4 holds exactly when

[
a_h+D_*=\max{a_h,0}. \tag{*}
]

That equality is not among the displayed hypotheses.

The mechanism is precise. In every finite prefix, a deviating (h) may Continue through all (n) copies of (x) and then use the old tail deviation worth (b_h=a_h+D_*). Therefore the owner cap is never multiplied by ((1-q)^n). In the infinite stationary profile, however, there is no old tail. Continuing through every copy means never Quitting, whose terminal payoff is (0). The supremal deviation value does not commute with sending the tail to infinity.

This is the phantom-continuation obstruction.

Global minimality gives only one side of ((*)). Since the stationary profile is an actual profile in (\mathcal K),

[
D_*\le D(\sigma^x)
=\max{a_h,0}-a_h
=[-a_h]_+.
]

Because (D_*>0), this already implies

[
a_h<0,
\qquad
D_*\le -a_h,
\qquad
b_h=a_h+D_*\le0.
]

Thus, in every nonvacuous instance of the stated hypotheses,

[
\bar p=\operatorname{Sem}(\sigma^x)
\quad\Longleftrightarrow\quad
b_h=0
\quad\Longleftrightarrow\quad
D_*=-r_h({h}).
]

If instead

[
D_*<-r_h({h}),
]

then (b_h<0), while the stationary owner cap is (0), and Step 4 fails.

## 5. Limiting clearance and stationary Nash verification

Taking limits in the clearance inequalities gives

[
r_j({h})-r_j({j})
=a_j-s_j
\ge D_*
\qquad(j\ne h),
]

so the first assertion of Step 5 is correct.

The arbitrary-deviation calculation above proves that every outsider’s stationary best-response value is exactly (a_j).

For (h), every deviation payoff is a convex combination of (a_h) and (0). Therefore, if (a_h\ge0),

[
B_h(\sigma^x)=a_h=U_h(\sigma^x),
]

including for the deviation that never Quits. Hence the stationary profile is an exact terminal Nash profile.

In fact, this conditional case contradicts (D_*>0), because it produces an actual semantic pair with total debt zero. Thus the hypotheses themselves force (r_h({h})<0).

## Conclusion

The minimum-face iteration itself works:

[
\boxed{\text{Steps 1, 2, and 3 are valid.}}
]

The limiting outsider inequalities and the full behavioral-deviation verification in Step 5 are also valid.

The first invalid inference is the unconditional form of Step 4. What is proved is

[
T_x^n p\longrightarrow
\left(
r({h}),
\bigl(r_h({h})+D_*,(r_j({h}))_{j\ne h}\bigr)
\right),
]

whereas the repeated stationary profile has owner cap

[
\max{r_h({h}),0}.
]

They coincide only under the additional transversality condition

[
r_h({h})+D_*=0.
]

A literal counterexample satisfying the positive-global-gap hypothesis would therefore require a genuine positive-gap quitting game realizing the strict case (r_h({h})+D_*<0). The stated assumptions neither supply such an example nor rule that strict case out. Thus the exact result here is a reduction of the proposed chain to the missing condition (b_h=0), rather than an affirmative proof of all five steps.
