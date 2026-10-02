# Geometric tail compression and simultaneous pivot repair

Identity: CODEX_ROOT.

## Mathematical content and scope

Against fixed finite nonpivot stopping laws, a geometric replacement of the
pivot's remaining finite clock preserves the complete prescribed terminal
coalition law and weakly decreases every unrestricted response cap. The
result eliminates the infinite-dimensional pivot optimization in favor of a
finite linear program, including its nonattained zero-first-atom boundary.

The self-contained [reviewed theorem and signed-payoff extension](../exports/GEOMETRIC_PIVOT_TAIL_COMPRESSION_AND_EXACT_REPAIR_LP.md)
give the complete formulas, exact example, and boundary tests. Independent
checks are in the [RENY review](../feedback/GEOMETRIC_COMPRESSION__BY_CODEX_RENY.md)
and [HILBERT review](../feedback/GEOMETRIC_COMPRESSION__BY_CODEX_HILBERT.md).
These are ordinary-mathematics results; this note asserts no Lean validation.

The geometric distribution is the conditional finite component of the
pivot's stopping law. With positive Never mass it is not a constant
behavioral hazard. For arbitrary signed own-singleton rewards, all three
late cap endpoints are needed; the positive-pivot absorption conclusion
requires its separate positive-singleton hypothesis.

In the canonical four-player normalization, vanishing optimized values
over three finite opponent laws are equivalent to the finite-menu selection
target. Selecting those three laws remains open. Neither convexity of that
outer search, convergence to zero, a renewable debt rank, nor UE follows
from solving the pivot's linear program.

## Original submission

The relevant distinction is between changing the pivot’s **distribution over outcomes** and changing only the **timing of its remaining singleton outcome**. The second operation admits an exact simultaneous improvement theorem.

**Any pivot tail against three fixed finite stopping laws can be replaced by one geometric tail, preserving every prescribed payoff and weakly decreasing every player’s unrestricted regret.** Consequently, the best possible pivot-only repair is a finite linear program—not an optimization over arbitrary infinite strategies.

This does not yet prove that the three opponent laws can be selected so that the repair value tends to zero. It does give an exact way to optimize the disturbance to those players, and a complete repair of the particular source from the previous answer.

## 1. Geometric compression improves all four debts simultaneously

Work in the canonical normalization

$$
r_0(\{0\})=1,\qquad r_j(\{j\})=0\quad(j=1,2,3).
$$

Fix the three nonpivot laws \(p_1,p_2,p_3\), supported on

$$
\{0,\ldots,N-1,\mathrm{Never}\}.
$$

Allow the pivot’s law \(\mu\) to be completely arbitrary. Write

$$
\lambda=\Pr_\mu(N\le T_0<\infty),\qquad
\nu=\Pr_\mu(T_0=\infty).
$$

Suppose \(\lambda>0\). Let \(t_*\ge N\) be its first positive late atom, and put

$$
\alpha=\Pr_\mu(T_0=t_*),\qquad h=\frac{\alpha}{\lambda}.
$$

Replace the pivot’s late finite law by

$$
\boxed{
\Pr_{\widetilde\mu}(T_0=N+\ell)
=\lambda h(1-h)^\ell
\quad(\ell\ge0).
}
\tag{1}
$$

Keep its probabilities before \(N\), and its Never probability \(\nu\), unchanged.

### Theorem

This replacement satisfies

$$
U_i(\widetilde\mu,p_{-0})=U_i(\mu,p_{-0})
\qquad(i=0,1,2,3),
\tag{2}
$$

and

$$
B_i(\widetilde\mu,p_{-0})\le B_i(\mu,p_{-0})
\qquad(i=0,1,2,3).
\tag{3}
$$

For the pivot, equality holds in (3).

### Proof

The prescribed terminal coalition law is unchanged. Whenever another player stops before \(N\), the two pivot laws behave identically for determining the outcome. If all three opponents choose Never, the pivot still quits alone with the same probability, or never quits with the same probability. This proves (2).

The pivot’s best-response cap depends only on its opponents, which were not changed.

Fix a nonpivot \(j\). Put

$$
a_j=r_j(\{0\}),\qquad b_j=r_j(\{0,j\}),\qquad
d_j=\prod_{\ell\notin\{0,j\}}p_\ell(\mathrm{Never}).
$$

Let \(A_j\) be the expected reward from opponents stopping before \(N\), when \(j\) Continues until then.

For a deterministic deviation stopping at \(t\ge N\), let

$$
F_t=\Pr_\mu(N\le T_0<t),\qquad f_t=\Pr_\mu(T_0=t).
$$

Its payoff is exactly

$$
A_j+d_j(a_jF_t+b_jf_t).
\tag{4}
$$

The remaining event gives \(j\) its own singleton reward, which is zero.

Under the new geometric tail, stopping at \(N+\ell\) gives

$$
A_j+d_j\left[
\bigl(1-(1-h)^\ell\bigr)a_j\lambda
+(1-h)^\ell b_j\alpha
\right].
\tag{5}
$$

Thus every new late deviation payoff lies between

$$
A_j+d_jb_j\alpha
\quad\text{and}\quad
A_j+d_ja_j\lambda.
\tag{6}
$$

Both endpoints were already available against the old law: the first by quitting at \(t_*\), the second by Never.

Deviations before \(N\) are unchanged. Taking the supremum proves (3). ∎

This handles negative spectator rewards as well as positive collision rewards. It does not discard preemption: preemption opportunities are included in (4). Rather, the geometric replacement makes every new late payoff a convex combination of two old deviation payoffs.

The same argument works without the zero-singleton normalization. One then retains three endpoints: the first late quitting payoff, the limit of arbitrarily late finite quitting payoffs, and Never.

## 2. An exact linear program for simultaneous pivot-only repair

The preceding theorem eliminates the infinite strategy search.

Keep \(p_1,p_2,p_3\) fixed. Introduce variables

$$
\mu_0,\ldots,\mu_{N-1},\lambda,\nu,\alpha,z
$$

with

$$
\mu_t,\lambda,\nu\ge0,\qquad
\sum_{t<N}\mu_t+\lambda+\nu=1,\qquad
0\le\alpha\le\lambda,\qquad z\ge0.
\tag{7}
$$

Here \(\lambda\) is the pivot’s late finite mass, \(\nu\) its Never mass, and \(\alpha\) the first atom of its geometric tail.

For the pivot, let \(Q_t\) be its payoff from quitting at \(t<N\), and let \(W_0\) be its Never payoff against the fixed opponents. Set

$$
D_0=\prod_{j=1}^3p_j(\mathrm{Never}),\qquad
L_0=W_0+D_0.
$$

Its unrestricted cap is the constant

$$
B_0=\max\{Q_0,\ldots,Q_{N-1},L_0\},
\tag{8}
$$

and its prescribed payoff is the affine function

$$
U_0=\sum_{t<N}\mu_tQ_t+\lambda L_0+\nu W_0.
\tag{9}
$$

For a nonpivot \(j\), write \(s_j=p_j(\mathrm{Never})\). Let \(\pi_{j,t}\) denote its payoff from quitting at \(t<N\), and let \(A_j\) have the meaning used above. Both are affine functions of the pivot variables. Its prescribed payoff is

$$
U_j
=
\sum_{t<N}p_j(t)\pi_{j,t}
+s_j\bigl(A_j+d_ja_j\lambda\bigr).
\tag{10}
$$

For a genuine geometric tail, its full cap is exactly

$$
\boxed{
B_j=
\max\left\{
\max_{t<N}\pi_{j,t},\
A_j+d_ja_j\lambda,\
A_j+d_jb_j\alpha
\right\}.
}
\tag{11}
$$

Therefore minimize \(z\), subject to (7) and

$$
\begin{aligned}
B_0-U_0&\le z,\\
\pi_{j,t}-U_j&\le z &&(j=1,2,3;\ t<N),\\
A_j+d_ja_j\lambda-U_j&\le z &&(j=1,2,3),\\
A_j+d_jb_j\alpha-U_j&\le z &&(j=1,2,3).
\end{aligned}
\tag{12}
$$

Every constraint is linear.

Let its optimum be \(z_*(p_{-0})\). Then

$$
\boxed{
z_*(p_{-0})
=
\inf_{\sigma_0}E_r(\sigma_0,p_{-0}),
}
\tag{13}
$$

where the infimum on the right includes **every behavioral pivot replacement**.

One inequality follows from geometric compression. For the other, an optimizer with \(0<\alpha\le\lambda\) is implemented by (1). The only nonliteral boundary is \(\alpha=0<\lambda\). Replace it by a sufficiently small positive \(\alpha\): prescribed payoffs do not change, and each cap increases by at most \(M\alpha\), where

$$
M=\max_{i,S}|r_i(S)|.
$$

Thus the LP optimum is always approached by actual profiles.

### A finite-menu consumer, with the actual menu verified

Truncate an implementing geometric tail after \(K\) atoms, moving its remaining mass

$$
\beta=\lambda(1-h)^K
$$

to Never. This changes only the pivot law, by total variation \(\beta\). Consequently,

$$
E_r(\text{truncated profile})
\le z_*+\eta+4M\beta,
\tag{14}
$$

where \(\eta\) accounts for replacing a zero-\(\alpha\) optimizer by a positive one.

This is an unrestricted cap bound, so it verifies Nash error on every displayed finite menu containing the law.

There is also an absorption bound. From (8)–(9),

$$
B_0-U_0\ge \nu D_0,
$$

and hence any feasible LP point satisfies

$$
\nu D_0\le z.
\tag{15}
$$

Display the truncated law on a deadline

$$
L=N+K+H.
$$

Then

$$
\boxed{
R_p(L-H)=D_0(\nu+\beta)\le z+\beta.
}
\tag{16}
$$

Thus **a sequence of these LP values tending to zero supplies the requested finite-menu producer directly**, including early absorption and unrestricted verification of the actual displayed menu. No unrestricted approximate equilibria are assumed as input.

What remains is selecting the three finite opponent laws so that their LP values tend to zero.

## 3. For the previous source, the optimal pivot-only repair is still defective

The LP gives a sharp answer on the explicit table from the preceding response.

Fix its nonpivot laws:

$$
\Pr(T_1=\tau)=\frac47,\qquad
\Pr(T_2=\tau)=\frac17,\qquad
T_3=\mathrm{Never},
$$

with the remaining masses assigned to Never. Here \(\tau=N-1\).

For an arbitrary pivot replacement, aggregate its law into

$$
u=\Pr(T_0<\tau),\quad
v=\Pr(T_0=\tau),\quad
w=\Pr(\tau<T_0<\infty),\quad
n=\Pr(T_0=\infty).
$$

These nonnegative quantities sum to one.

Its unrestricted pivot debt is exactly

$$
d_0=\frac{186u+18v+18n}{49}.
\tag{17}
$$

Meanwhile, player \(1\)’s gain from switching to Never is

$$
G_1=\frac{-20v+176w+8n}{49}.
\tag{18}
$$

Therefore

$$
\begin{aligned}
E_r
&\ge \frac{98}{107}d_0+\frac9{107}G_1\\
&=\frac{1584+16644u+252n}{5243}\\
&\ge\boxed{\frac{1584}{5243}}.
\end{aligned}
\tag{19}
$$

This lower bound covers **all pivot strategies**, not just finite, stationary, or geometric ones.

It is attained. Take

$$
\Pr(T_0=\tau)=\frac{88}{107},
$$

and put the remaining mass \(19/107\) into a geometric tail of conditional hazard \(1/2\), beginning at \(\tau+1\). The full debt vector is

$$
\boxed{
\left(
\frac{1584}{5243},
\frac{1584}{5243},
\frac{1203}{5243},
0
\right).
}
\tag{20}
$$

Hence

$$
z_*(p_{-0})=\frac{1584}{5243}\approx0.302117,
$$

independently of the deadline.

In particular, allowing arbitrary early pivot dates and arbitrary late pivot distributions does not fix this source while its opponents remain unchanged.

## 4. Two subsequent replacements finish that example

The optimum in (20) identifies an actual repair sequence for the example.

First replace player \(1\)’s law by Never. This is an unrestricted best response: its Never payoff is \(7\), and neither its finite-prefix deviations nor its geometric-tail collision deviations exceed \(7\).

Then replace player \(2\)’s law by Never. Against the now-fixed pivot law and the other two Never players, its Never payoff is \(7\). Quitting with the pivot pays \(5\), and quitting alone pays zero, so Never is an unrestricted best response.

Keep the pivot law unchanged. The resulting profile has all three opponents playing Never, and the pivot quits almost surely with hazards

$$
0\quad(t<\tau),\qquad
\frac{88}{107}\quad(t=\tau),\qquad
\frac12\quad(t>\tau).
$$

This is an **exact terminal Nash profile**:

The pivot obtains its singleton payoff \(1\), its full cap. Player \(1\) obtains \(7\); its largest current collision opportunity is bounded by

$$
8\cdot\frac{88}{107}=\frac{704}{107}<7,
$$

and the subsequent conditional collision payoff is \(8/2=4<7\). Player \(2\) obtains \(7\), while a collision pays only \(5\). Player \(3\) obtains zero and cannot gain by quitting.

The fixed payoff is therefore

$$
(1,7,7,0).
$$

These are horizontal strategy replacements, not Nash–Bellman charges. The example closes because the two Never replacements do not reactivate a profitable deviation for a player already repaired.

---

The general advance is **geometric compression plus a complete simultaneous pivot-repair LP**, with an explicit finite-menu and absorption consumer. The unresolved step is now precise: prove that changing the three opponent laws can drive \(z_*(p_{-0})\) to zero. The example’s two-step elimination does not establish a general decreasing rank; in an arbitrary table, a Never replacement can reactivate an earlier player’s deviation. I have not proved that this reactivation can always be controlled.
