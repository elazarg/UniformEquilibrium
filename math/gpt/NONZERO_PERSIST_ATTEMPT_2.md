The decisive distinction is **recurrence**, not merely nonzero activity. Compactness can select a minimal exact-spine component; minimality then turns any nonzero root in that component into a nonsummable marginal clock. The only zero-persistent minimal component is a literal constant all-Continue phantom.

This gives a clean abstract selector. It does **not yet** prove the boxed Fin4 implication, because the current positive-minimum provenance has not been shown to define a closed shift-invariant exact-spine family excluding that phantom. The strengthened attached theorem consumes every nonempty-persistence outcome, so under a hypothetical Fin4 counterexample every exact bounded canonical spine has all four marginal streams summable.

## 1. Compact minimal-component selection

Let \(\mathscr P_r\) be the space of all exact bounded Nash–Bellman spines in the canonical reward cube. An element is

$$
z=((v_t,x_t))_{t\ge 0}.
$$

Let \(S:\mathscr P_r\to\mathscr P_r\) be the left shift, and define the continuous total marginal activity

$$
h(z):=\sum_{i\in I}\Pr_{x_0}(i\text{ Quits}).
$$

The payoff cube and product-root simplex are compact, while Bellman equality and exact root Nash are closed conditions. Hence \(\mathscr P_r\) is compact and \(S\) is continuous; this is the same compact exact-spine system underlying the canonical spine construction and phantom regression.

### Theorem 1 — persistent spine or phantom

Let \(K\subseteq\mathscr P_r\) be nonempty, compact, and forward shift-invariant:

$$
S(K)\subseteq K.
$$

Then exactly the following useful alternative holds:

$$
\boxed{
\begin{aligned}
&\exists z\in K,\ \exists i\in I,\quad
  \sum_{t=0}^{\infty}\Pr_{x_t}(i\text{ Quits})=\infty;\\
&\text{or}\\
&\exists b\in\mathbb R^I,\quad
  ((b,C),(b,C),\ldots)\in K,
  \qquad r_i(\{i\})\le b_i\quad(\forall i).
\end{aligned}}
\tag{A}
$$

Here \(C\) denotes the pure all-Continue root.

### Proof

Choose a nonempty minimal compact forward-invariant subset \(M\subseteq K\). Such an \(M\) exists by the usual nested-intersection argument.

Suppose first that \(h\) is not identically zero on \(M\). Choose \(z^\ast\in M\) and \(\delta>0\) such that

$$
h(z^\ast)>\delta.
$$

Set

$$
U:=\{z\in M:h(z)>\delta\}.
$$

For every \(z\in M\), the closure of its forward orbit is a nonempty compact forward-invariant subset of \(M\), and hence equals \(M\) by minimality. Thus every forward orbit meets \(U\). Equivalently,

$$
M=\bigcup_{n\ge0}S^{-n}(U).
$$

Compactness gives \(L<\infty\) such that

$$
M=\bigcup_{n=0}^{L}S^{-n}(U).
\tag{1}
$$

Apply (1) to \(S^{m(L+1)}z\). For every \(m\), some date

$$
t_m\in[m(L+1),\,m(L+1)+L]
$$

satisfies \(h(S^{t_m}z)>\delta\). The displayed intervals are disjoint, so

$$
\sum_{t=0}^{\infty}h(S^t z)=\infty.
\tag{2}
$$

Since

$$
h(S^t z)=\sum_{i\in I}q_{t,i}
$$

and \(I\) is finite, (2) implies that one fixed \(i\) satisfies

$$
\sum_tq_{t,i}=\infty.
$$

This is the first branch of (A).

Otherwise \(h\equiv0\) on \(M\). Every root in every spine in \(M\) is therefore all-Continue. Bellman equality gives

$$
v_t=F_C(v_{t+1})=v_{t+1},
$$

so every such spine is a constant sequence \(((b,C),(b,C),\ldots)\). Exact Nash at \(C\) is equivalent to

$$
r_i(\{i\})\le b_i
$$

for every player. Each such constant spine is itself a closed invariant singleton. Minimality therefore forces \(M\) to consist of exactly one of them. This proves the second branch. ∎

### Source-facing corollary

The desired Fin4 implication would follow immediately from:

> Construct, from the positive-minimum source, a nonempty compact shift-invariant family \(K_r\subseteq\mathscr P_r\) containing no constant all-Continue spine.

No optimization of labels is then needed. The minimal-component theorem supplies one spine with divergent total marginal activity, and finiteness of \(\operatorname{Fin}4\) supplies one fixed persistent label.

This also explains why ordinary compact exact-spine existence is insufficient: its selected invariant family contains the canonical phantom.

---

## 2. Every all-summable exact spine converges to a phantom

The preceding phantom is not merely an artificial fixed point. It is forced into the shift closure of every all-summable spine.

### Theorem 2 — phantom omega-limit

Let \((v_t,x_t)\) be a bounded exact Nash–Bellman spine and suppose

$$
\sum_tq_{t,i}<\infty
\qquad(\forall i).
\tag{3}
$$

Then there is a payoff vector \(b\) such that

$$
v_t\longrightarrow b,\qquad x_t\longrightarrow C,
\tag{4}
$$

and, in the full spine product topology,

$$
S^n((v,x))\longrightarrow ((b,C),(b,C),\ldots).
\tag{5}
$$

Moreover,

$$
r_i(\{i\})\le b_i
\qquad(\forall i),
\tag{6}
$$

so the limit is itself an exact phantom spine.

### Proof

Let

$$
\alpha_t:=1-\prod_i(1-q_{t,i})
$$

be the one-stage absorption probability. The union bound gives

$$
0\le\alpha_t\le\sum_iq_{t,i},
$$

hence \(\sum_t\alpha_t<\infty\).

If terminal rewards and spine values are bounded by \(K\), Bellman equality gives

$$
v_t-v_{t+1}
=
\mathbb E\!\left[
  \mathbf 1_{\{\text{some Quit}\}}
  \bigl(r(Q_t)-v_{t+1}\bigr)
\right],
$$

and therefore

$$
\|v_t-v_{t+1}\|_\infty\le 2K\alpha_t.
\tag{7}
$$

Thus \((v_t)\) has finite total variation and converges to some \(b\).

Every nonnegative summable marginal tends to zero, so \(x_t\to C\). For each fixed offset \(k\),

$$
v_{n+k}\to b,\qquad x_{n+k}\to C,
$$

which proves (5). Closedness of exact root Nash, applied to

$$
x_t\text{ Nash against }v_{t+1},
$$

shows that \(C\) is exact Nash against \(b\). This is equivalent to (6). ∎

The repository already proves related coordinatewise value convergence from summable clocks; the point here is the stronger whole-shift conclusion (5): **every closed tail-stable provenance class containing an all-summable spine also contains its phantom boundary**.

### Rigidity at the Fin4 minimum plateau

The checked Fin4 no-uniform-payoff reduction produces a positive minimum semantic plateau \(z=(u,b)\) such that

$$
r_i(\{i\})<u_i
\qquad(\forall i),
$$

and all-Continue is the unique exact root at \(u\). In fact uniqueness persists on an open neighborhood of the full debt segment from \(u\) to \(b\).

Consequently, if an all-summable exact spine has limit \(u\), then it is not merely eventually close to the phantom: it is the literal phantom from time zero.

Indeed, for all sufficiently large \(t\), \(v_{t+1}\) lies in the uniqueness neighborhood, so \(x_t=C\) and \(v_t=v_{t+1}\). Convergence forces the late values to equal \(u\). Backward induction using uniqueness at \(u\) then gives

$$
v_t=u,\qquad x_t=C
\quad(\forall t).
\tag{8}
$$

Thus a successful source selector must do one of two genuinely nonlocal things:

1. exclude the source plateau phantom from its shift closure; or
2. retain a restart/return mark that is not lost under shifts and compact limits.

Finite-dimensional terminal semantic or coalition-law provenance alone does not do this, because all-Continue prefixing fixes those data.

---

## 3. A finite normalized-return criterion that is sufficient

There is also a sharp finite-block formulation. It isolates exactly what kind of source restart would produce the requested persistent chronology.

An exact Nash–Bellman block \(B\) consists of

$$
w_0,y_0,w_1,y_1,\ldots,y_{L-1},w_L
$$

with

$$
w_k=F_{y_k}(w_{k+1}),
\qquad
y_k\text{ exact Nash against }w_{k+1}.
$$

Define its total marginal charge and endpoint seam by

$$
H(B):=\sum_{k<L}\sum_i\Pr_{y_k}(i\text{ Quits}),
\qquad
\Delta(B):=\|w_L-w_0\|_\infty.
\tag{9}
$$

### Theorem 3 — normalized near-returns amplify to persistence

Suppose there are uniformly bounded exact blocks \(B_n\) such that

$$
H_n:=H(B_n)>0,
\tag{10}
$$

their two endpoints converge to one common vector,

$$
w^n_0\to b,\qquad w^n_{L_n}\to b,
\tag{11}
$$

and

$$
\frac{\Delta(B_n)}{H_n}\longrightarrow0.
\tag{12}
$$

Then, for every \(\varepsilon>0\), there is one bounded infinite root chronology \((x_t)\) and payoff annotation \((v_t)\) such that:

$$
\sum_t
\left\|v_t-F_{x_t}(v_{t+1})\right\|_\infty<\varepsilon,
\tag{13}
$$

the sum of its one-stage root-Nash errors is below \(\varepsilon\), and

$$
\exists i\in I,\qquad
\sum_t\Pr_{x_t}(i\text{ Quits})=\infty.
\tag{14}
$$

The player in (14) is one fixed label on the whole literal chronology.

### Proof

Pass to a subsequence so rapidly that

$$
\frac{\Delta(B_n)}{H_n}+\Delta(B_n)<2^{-n}\varepsilon_0
\tag{15}
$$

and

$$
\|w^{n}_{L_n}-w^{n+1}_0\|_\infty
<2^{-n}\varepsilon_0,
\tag{16}
$$

where \(\varepsilon_0\) is chosen below \(\varepsilon\) by a fixed numerical factor.

Repeat \(B_n\)

$$
m_n:=\left\lceil\frac1{H_n}\right\rceil
$$

times. Each group then carries charge

$$
m_nH_n\ge1.
\tag{17}
$$

To close two consecutive copies, replace the terminal continuation \(w^n_{L_n}\) at the last root by \(w^n_0\). Bellman evaluation is \(1\)-Lipschitz in the continuation, so the Bellman defect at this seam is at most \(\Delta(B_n)\).

If a root is exact Nash at continuation \(w\), replacing \(w\) by \(w'\) makes it at worst a \(2\|w-w'\|_\infty\)-Nash root: both the prescribed root payoff and an arbitrary unilateral root payoff change by at most \(\|w-w'\|_\infty\). Hence the root-Nash error at the seam is at most \(2\Delta(B_n)\).

The total internal seam cost in group \(n\) is bounded by

$$
m_n\Delta(B_n)
\le
\frac{\Delta(B_n)}{H_n}+\Delta(B_n).
\tag{18}
$$

The seam from the last copy of group \(n\) to the first copy of group \(n+1\) costs at most the quantity in (16). Equations (15)–(18) show that all Bellman and Nash errors are absolutely summable, and their total can be made below \(\varepsilon\).

On the other hand, (17) yields

$$
\sum_t\sum_i\Pr_{x_t}(i\text{ Quits})=\infty.
$$

Since there are finitely many players, at least one fixed player has a divergent marginal series. ∎

Absolute summability in (13) is stronger than the probability-weighted summability requested in the question. Never and arbitrarily late behavioral deviations are not truncated: the only approximation is in the local Bellman/Nash seams, and its complete accumulated budget is finite.

An exact return \(w_L=w_0\) is the zero-error special case; repeating one positive-charge exact block then gives an exact periodic persistent spine.

---

## 4. Direct connection to the current exact-cap ray

The existing strict-ray object carries semantic pairs \(z_t\), roots \(x_t\), and caps

$$
c_t:=z_t^2
$$

satisfying

$$
c_{t+1}=F_{x_t}(c_t),
\qquad
x_t\text{ exact Nash against }c_t.
\tag{19}
$$

Its roots have positive but summable marginal activity.

Therefore every forward segment \(a\le t<b\), when read backwards,

$$
c_b,\ x_{b-1},\ c_{b-1},\ldots,x_a,\ c_a,
$$

is an exact Nash–Bellman block. Its charge and seam are

$$
H[a,b]
=
\sum_{t=a}^{b-1}\sum_iq_{t,i},
\qquad
\Delta[a,b]=\|c_b-c_a\|_\infty.
\tag{20}
$$

Hence the following finite statement would close the new residual:

$$
\boxed{
\exists\,a_n<b_n,\quad
H[a_n,b_n]>0,\quad
c_{a_n},c_{b_n}\to c_\infty,\quad
\frac{\|c_{b_n}-c_{a_n}\|_\infty}{H[a_n,b_n]}\to0.
}
\tag{NR}
$$

By Theorem 3, `(NR)` gives a summable-error spine with a fixed persistent label. The strengthened unique-persistent theorem or the two-label chronological compiler then closes the table.

Convergence \(c_t\to c_\infty\) alone does **not** imply `(NR)`. The scalar model

$$
c_{t+1}-c_t=h_td,\qquad
h_t>0,\qquad
\sum_th_t<\infty,
$$

has

$$
\frac{|c_b-c_a|}{\sum_{t=a}^{b-1}h_t}=|d|
$$

on every interval. This is precisely the ballistic normalized-flow obstruction; it cannot be removed by a subsequence argument.

The present positive-root return theorem obtains a fresh minimum-law handoff or an off-minimum descent when a positive exact root exists at the cap limit, but it explicitly does not provide a quantitative return rate or renewable rank.  The source-preserving forced-pair construction likewise retains literal tails and positive paid gains, but makes no target-side Nash–Bellman or return assertion.

---

## 5. Why a raw all-summable orbit cannot suffice

A hypothetical terminal exploitability witness already gives a finite common charge capacity for every exact punishment-floor path.  In fact every arbitrary infinite exact punishment-floor orbit then has summable absorption and summable individual marginal hazards.

So a proof cannot extract persistence from one raw counterexample-side exact orbit. It must use the positive-minimum source to do something that the capacity theorem does not permit:

* construct a genuine renewable exact return;
* construct normalized near-returns `(NR)` and use summable seams;
* or produce a source-defined compact shift-invariant exact-spine family excluding every phantom.

This agrees with the current toolkit boundary: the cap-pump, exact packet-amplification, and positive-cycle consumers are present, but no theorem orients the source data into the required exact renewable path.

## Resulting residual

The selection question is now equivalent, for the current source architecture, to the following sharper statement:

$$
\boxed{
\begin{array}{c}
\textbf{Fin4 normalized-return/source-hull lemma:}\\[2mm]
\text{from every positive-minimum hard source, either}\\
\text{produce exact positive-charge blocks satisfying `(NR)`,}\\
\text{or construct a compact tail-stable exact-spine hull}\\
\text{that contains no constant all-Continue phantom.}
\end{array}}
$$

The first route gives a summable-error persistent chronology by Theorem 3. The second gives an exact persistent spine by Theorem 1.

What remains unproved is exactly this source-to-return step. Compactness, positive finite atoms, nonzero roots on unrelated blocks, and convergence of cap values do not supply it. The zero-persistent alternative has otherwise been reduced completely to a literal phantom fixed component.

## Followup 1

The review corrections are necessary. With them, the compactness and amplification layer is sound. The remaining source implication, however, does **not** follow from the current Fin4 source objects: the exact obstruction is the horizontal source-regeneration seam. The available estimates price that seam only linearly in the exact hazard charge, whereas amplification needs a little-\(o\) estimate or a sign-safe centered compiler.

The attached unique-persistent theorem already consumes exactly one persistent label under punishment normality, while the two-label compiler consumes every larger persistent set. Thus a hypothetical Fin4 counterexample forces all four marginal clocks to be summable on every exact canonical spine.  The checked implementation of the exact unique-persistent compiler is now in `NormalUniquePersistentNashBellmanSpine.lean`.

## 1. Correct compact minimal-component theorem

Let \(\mathscr S_r\) be the compact space of bounded exact Nash–Bellman spines and let

$$
S:\mathscr S_r\to\mathscr S_r
$$

be the left shift. For \(z=((v_t,x_t))_{t\ge0}\), put

$$
h(z):=\sum_{i\in I}\Pr_{x_0}(i\text{ Quits}).
$$

### Theorem 1

Let \(K\subseteq\mathscr S_r\) be nonempty and compact, with \(S(K)\subseteq K\). Let \(M\subseteq K\) be a minimal nonempty compact forward-invariant subset.

Then precisely one of the following holds for this chosen \(M\).

1. Every \(z\in M\) has divergent total marginal hazard:

   $$
   \sum_{t=0}^{\infty}h(S^tz)=\infty.
   $$

   Consequently, for every \(z\in M\), some fixed player \(i=i(z)\) satisfies

   $$
   \sum_{t=0}^{\infty}\Pr_{x_t}(i\text{ Quits})=\infty.
   $$

2. \(M\) is a singleton constant phantom:

   $$
   M=\{((b,C),(b,C),\ldots)\},
   $$

   where \(C\) is the all-Continue root and

   $$
   r_i(\{i\})\le b_i\qquad(i\in I).
   $$

These alternatives are exclusive for the selected minimal component \(M\), but they are **not** exclusive for the ambient family \(K\): different minimal components of \(K\) may realize different branches.

### Proof

Suppose \(h\not\equiv0\) on \(M\). Choose \(z_\ast\in M\) and \(\delta>0\) such that \(h(z_\ast)>\delta\), and set

$$
U:=\{z\in M:h(z)>\delta\}.
$$

For each \(z\in M\), the closure of its **forward** orbit,

$$
\overline{\{S^nz:n\ge0\}},
$$

is a nonempty compact forward-invariant subset of \(M\). Minimality therefore makes it equal to \(M\). Thus the forward orbit of every point of \(M\) is dense in \(M\), and in particular meets \(U\). Hence

$$
M=\bigcup_{n\ge0}S^{-n}(U).
$$

Compactness gives \(L<\infty\) such that

$$
M=\bigcup_{n=0}^{L}S^{-n}(U).
\tag{1}
$$

Apply (1) to \(S^{m(L+1)}z\). For each \(m\), some

$$
t_m\in[m(L+1),m(L+1)+L]
$$

has \(h(S^{t_m}z)>\delta\). These intervals are disjoint, so

$$
\sum_t h(S^tz)=\infty.
$$

Since \(I\) is finite,

$$
\sum_t\sum_i q_{t,i}=\infty
$$

forces one fixed coordinate series \(\sum_tq_{t,i}\) to diverge.

If instead \(h\equiv0\) on \(M\), every root in every spine in \(M\) is all Continue. Bellman equality gives \(v_t=v_{t+1}\), so every point of \(M\) is a constant phantom. Each such phantom is itself a compact forward-invariant singleton; minimality therefore forces \(M\) to be one singleton. Exact root Nash at all Continue is equivalent to \(r_i(\{i\})\le b_i\).

No backward-orbit density is used.

---

## 2. Correct shift-limit phantom theorem

### Theorem 2

Let \(z=((v_t,x_t))_{t\ge0}\) be a bounded exact Nash–Bellman spine and suppose

$$
\sum_t q_{t,i}<\infty
\qquad(i\in I).
\tag{2}
$$

Then there exists \(b\in\mathbb R^I\) such that

$$
v_t\longrightarrow b,\qquad x_t\longrightarrow C,
\tag{3}
$$

and

$$
S^nz\longrightarrow ((b,C),(b,C),\ldots)
\tag{4}
$$

in the product topology. Moreover \(C\) is exact root Nash against \(b\), hence

$$
r_i(\{i\})\le b_i\qquad(i\in I).
\tag{5}
$$

Thus the orbit closure of \(z\) contains a phantom singleton minimal component. This says nothing about other components of a larger family containing \(z\).

### Proof

Let

$$
\alpha_t:=1-\prod_i(1-q_{t,i})
$$

be the root absorption probability. Then

$$
0\le\alpha_t\le\sum_iq_{t,i},
$$

so \(\sum_t\alpha_t<\infty\).

If all rewards and spine values are bounded in norm by \(K\), Bellman equality gives

$$
\|v_t-v_{t+1}\|_\infty\le 2K\alpha_t.
\tag{6}
$$

Therefore \((v_t)\) has finite total variation and converges to some \(b\). Every summable nonnegative marginal tends to zero, so \(x_t\to C\). For each fixed \(k\),

$$
v_{n+k}\to b,\qquad x_{n+k}\to C,
$$

which proves (4). Closedness of exact root Nash then makes \(C\) exact Nash against \(b\).

This is the correct phantom conclusion: a **shift limit** and hence a minimal component of the orbit closure, not an assertion that the whole source family is phantom.

---

## 3. Explicit normalized-return amplification constant

Let an exact block \(B_n\) be

$$
w^n_0,y^n_0,w^n_1,\ldots,
y^n_{\ell_n-1},w^n_{\ell_n},
$$

with

$$
w^n_k=F_{y^n_k}(w^n_{k+1}),
\qquad
y^n_k\text{ exact Nash against }w^n_{k+1}.
$$

Put

$$
H_n:=\sum_{k<\ell_n}\sum_i
   \Pr_{y^n_k}(i\text{ Quits})>0,
$$

$$
D_n:=\|w^n_{\ell_n}-w^n_0\|_\infty.
$$

Assume

$$
\frac{D_n}{H_n}\longrightarrow0,
\qquad
w^n_0\longrightarrow b,
\qquad
w^n_{\ell_n}\longrightarrow b.
\tag{7}
$$

### Theorem 3

For every \(\eta>0\), one can select a subsequence and concatenate repeated copies of its blocks into a bounded infinite chronology whose total Bellman residual is at most \(S\), whose total root-Nash residual is at most \(2S\), and whose total marginal hazard diverges, where

$$
S\le
\sum_n\left(\frac{D_n}{H_n}+E_n\right)
\tag{8}
$$

and

$$
E_n:=\|w^n_{\ell_n}-w^{n+1}_0\|_\infty.
$$

The subsequence can be selected so that

$$
\boxed{
\sum_t\operatorname{BellmanResidual}_t+
\sum_t\operatorname{NashResidual}_t
\le
3\sum_n\left(\frac{D_n}{H_n}+E_n\right)
<\eta.
}
\tag{9}
$$

Thus the explicit raw seam constant is \(3\).

### Proof

Take

$$
m_n:=\left\lceil\frac1{H_n}\right\rceil.
$$

Repeat \(B_n\) exactly \(m_n\) times. The charge of group \(n\) is

$$
m_nH_n\ge1.
\tag{10}
$$

At a seam of size \(d\), only the tail used by the preceding final root is replaced.

The Bellman map is \(1\)-Lipschitz in the continuation, so the Bellman residual contributed by the seam is at most \(d\).

For root Nash, both the prescribed-root payoff and every unilateral alternative payoff change by at most \(d\). An exact root therefore becomes a \(2d\)-Nash root. Hence the Nash residual is at most \(2d\).

There are \(m_n-1\) internal seams of size \(D_n\), followed by one cross-group seam of size \(E_n\). Therefore

$$
\sum_t\operatorname{BellmanResidual}_t
\le
\sum_n\bigl((m_n-1)D_n+E_n\bigr)
\le
\sum_n\left(\frac{D_n}{H_n}+E_n\right),
\tag{11}
$$

and

$$
\sum_t\operatorname{NashResidual}_t
\le
2\sum_n\left(\frac{D_n}{H_n}+E_n\right).
\tag{12}
$$

Because both endpoints converge to \(b\), and \(D_n/H_n\to0\), a subsequence can be chosen so that the right side of (9) is below any prescribed \(\eta\).

By (10),

$$
\sum_t\sum_iq_{t,i}=\infty,
$$

so one fixed player is persistent on the literal concatenated root sequence.

### Downstream routing

This chronology is not declared exact. It is a summable-residual Nash–Bellman chronology.

Its output goes first to the summable-residual consumer. The tail residual budget tends to zero because both residual series are summable. After extracting fixed labels across the finite set of players:

* if exactly one player is persistent, the summable-residual extension of the unique-persistent argument, together with that player’s punishment normality, produces the singleton uniform payoff;
* if at least two players are persistent, the same literal roots satisfy the two-label survival conditions, while the residual tails supply the vanishing discrepancy and forcing budgets required by chronological shadowing.

Thus the amplification theorem does not bypass punishment normality. It produces persistence plus a summable local error ledger; the one-label and two-label consumers finish the two respective cases.

The exact version of the one-label consumer and its unrestricted behavioral-deviation scope are recorded in the attached reviewed proof and its current Lean implementation. 

---

## 4. Reversing strict-ray segments

For a forward exact cap ray \(z_t\) with roots \(x_t\),

$$
z_{t+1}=T_{x_t}z_t,
\qquad
x_t\text{ exact Nash against }z_t^2.
$$

Exact cap-Nash transport gives

$$
z_{t+1}^2=F_{x_t}(z_t^2).
\tag{13}
$$

Hence a finite forward segment \(a\le t<b\), when read backwards,

$$
z_b^2,\ x_{b-1},\ z_{b-1}^2,\ldots,
x_a,\ z_a^2,
$$

is a literal exact Nash–Bellman block. This reversal is justified specifically by

$$
(\text{semantic prefix})^2
=
\text{root successor payoff at the old cap},
$$

not merely by semantic prefixing or by root Nash against some unrelated continuation. The exact envelope transport and debt-scaling identities are in `TerminalCapNashEndpointTransport.lean`; the strict-ray wrapper stores the same forward cap-Nash data.

---

## 5. Two sufficient source targets

The source problem has now been reduced to two sufficient targets, not to an equivalence.

### Target A: normalized exact-block returns

Construct exact source-provenant blocks satisfying (7). Theorem 3 then gives arbitrarily small summable-residual persistent chronologies.

A stronger convenient producer criterion is **unbounded exact-block hazard capacity on one compact source carrier**. The current exact-block capacity theorem says that unbounded capacity gives, at every positive radius, an exact block with hazard charge at least \(1\) and endpoints within that radius. Compactness then selects blocks whose two endpoints converge to one common \(b\), so (7) follows without repetition.  The underlying compact charged-return argument is the finite-cover theorem in `CompactFiniteChargedReturn.lean`.

### Target B: a phantom-free minimal-component hull

Construct a nonempty compact forward-invariant source hull of exact spines and prove that none of its minimal components is a constant all-Continue phantom. Theorem 1 then gives a persistent exact spine directly.

It is enough to exclude phantom **minimal components**. The hull itself may contain phantom points alongside a persistent component.

---

## 6. Why the present source data do not yet produce either target

The obstruction is quantitative and exact.

For a paid cap port, let

$$
A:=\text{total exact cap-root absorption},
\qquad
\Delta:=\text{initial-to-limit cap displacement}.
$$

The checked estimate is

$$
\Delta\le 2R\,A,
\tag{14}
$$

where \(R\) is the reward bound. This is only

$$
\Delta=O(A).
$$

Normalized-return amplification requires

$$
\Delta=o(A),
\tag{15}
$$

or a centered/sign-safe replacement for (15). Repeating such a block approximately \(1/A\) times turns (14) only into a bounded seam cost; it does not make that cost tend to zero. The cap-port trichotomy proves a charged near-return when \(\Delta=0<A\), quantitative debt descent when \(\Delta>0\), and literal inertness when \(A=0\).

In the inert branch,

$$
A=0,
$$

every selected exact cap root is literally all Continue, and the paid first-disagreement row can be shifted arbitrarily far without loss. But that shifted paid row is an actual behavioral comparison, not an exact Nash–Bellman root. It therefore supplies provenance and positive gain but no marginal hazard for the desired spine.

The normalized-passport orbit cannot repair this: its finite prefix words are deliberately arbitrary product roots with no Nash condition. Its compact minimizer therefore cannot be substituted into Theorem 3 as an exact-block producer.

The renewable endpoint construction likewise retains exact minimum sources and finite support descent, but its own statement explicitly leaves the horizontal source seam without a backward compiler. It can consume source-independent terminal conclusions, but it cannot concatenate the parent and child chronologies into one Nash–Bellman path.

Finally, the minimum semantic fibre itself cannot provide a phantom-free hull: punishment normality makes the whole Fin4 minimum fibre uniformly singleton-separated, and its prescribed projection lies in a neighborhood on which all Continue is the unique exact root.

---

## 7. Exact remaining producer lemma

The source completion needed for the boxed Fin4 implication is now:

$$
\boxed{
\begin{array}{l}
\textbf{Centered source-return lemma.}\\[1mm]
\text{For every infinite same-residual Fin4 source trace avoiding the existing}\\
\text{uniform-payoff exits, either there are source-provenant exact blocks }B_n\\
\text{with }H_n>0,\ \Delta(B_n)/H_n\to0,\text{ and common endpoint cluster;}\\
\text{or the trace generates a compact exact-spine hull with no phantom}\\
\text{minimal component.}
\end{array}}
\tag{16}
$$

The current source objects prove neither disjunct. In particular:

* quantitative debt descent does not by itself give a renewable well-founded scalar rank;
* inert stall retains a positive behavioral row but has zero exact hazard;
* the existing linear cap-motion estimate does not give the little-\(o\) seam needed by Theorem 3; and
* the regenerated minimum source is separated from its parent by a horizontal full-replacement seam which is not a Nash–Bellman edge.

So the abstract selector and normalized-return amplifier are complete after the review corrections, but the source-to-return/phantom-free-hull implication remains unproved. Claiming the final Fin4 selector at this point would silently assume precisely (16).

# Followup 2

# Bounded-capacity marked two-port saturation

The correct replacement for the discarded Target A/B route is a **marked source–target fibre product**. A target-only terminal law is insufficient: it forgets which part of its \(A\)-mass is the historical paid row and forgets the source profile from which that row was obtained. The exact-spine persistence lane is already consumed and leaves precisely the zero-persistent boundary, so it plays no further role here.

The existing ingredients already give:

* bounded finite exact Nash–Bellman hazard capacity in every hypothetical Fin4 counterexample;
* a target-only law-tight saturation hull and its positive-debt all-Continue minimum face;
* actual canonical paid rows with a fixed payer \(p\), fixed source and target coalitions, positive marked mass and gain, zero target \(p\)-debt, and the complete post-row tail;
* compact chronological marked laws that retain clock, root, continuation and coalition data.

The first two are checked in the bounded-capacity and law-tight minimum-face modules.    The paid endpoint supplies literal whole-profile \(p\)-debt cancellation and preserves its post-mark behavioral tail.  Its strict compact origin retains uniform positive marked-mass and gain floors.

## 1. The actual upstream two-port datum

After one fixed-action subsequence, let

$$
\sigma_n^- ,\qquad \sigma_n^+
$$

be respectively the canonical source and paid-target profiles. There are fixed coalitions \(B\neq A\), a fixed payer \(p\), and marked dates \(t_n\) such that:

$$
\sigma_n^+
=
\sigma_n^-[p\leftarrow\text{the paid endpoint strategy}],
$$

all opponents of \(p\) are literally unchanged, and conditional on reaching \(t_n\),

$$
B\quad\text{occurs under }\sigma_n^-,
\qquad
A\quad\text{occurs under }\sigma_n^+.
$$

Here \(A=B\triangle\{p\}\). Because the action has been frozen and the endpoint is strictly profitable,

$$
\Delta:=r_p(A)-r_p(B)>0.
$$

Write

$$
m_n:=\Pr_{\sigma_n^\pm}(\text{reach }t_n),
\qquad
g_n:=U_p(\sigma_n^+)-U_p(\sigma_n^-).
$$

Then, exactly,

$$
g_n=m_n\Delta. \tag{1}
$$

If \(\mu_n^\pm\) are the complete terminal-outcome laws, their difference is not merely an inequality:

$$
\boxed{\mu_n^-=\mu_n^+-m_n\delta_A+m_n\delta_B.} \tag{2}
$$

The source and target have the same opponents, hence the same unrestricted behavioral cap for \(p\). The checked paid-endpoint identities therefore give

$$
d_p(\sigma_n^+)=0,
\qquad
d_p(\sigma_n^-)=g_n. \tag{3}
$$

The post-\(t_n\) behavioral tail is literally common to both ports.

Let

$$
D_*=\inf_\sigma D(\sigma)>0
$$

and let

$$
\rho=\frac{D_*}{D_{\mathrm{ray}}}>0
$$

be the canonical ray survival floor. On the strict endpoint subsequence, compactification gives fixed bounds

$$
m_n\ge \rho^2,
\qquad
g_n\ge \frac{\rho D_*}{3}. \tag{4}
$$

These are the existing canonical endpoint floors, not newly assumed estimates.

## 2. Chronological coupling, rather than two unrelated laws

For each \(n\), form a probability coupling \(\Gamma_n\) of the source and target chronological marked laws.

Every absorption strictly before \(t_n\) is paired diagonally: the two profiles are identical there. The terminal marked event is paired as

$$
(\text{clock}_n,\text{source root},\text{tail}_n,B)
\quad\leftrightarrow\quad
(\text{clock}_n,\text{target root},\text{tail}_n,A)
$$

with mass \(m_n\).

Let \(\mathcal T_{p,B,A}\) be the set of event pairs with:

$$
\begin{aligned}
&\text{equal clocks},\\
&\text{equal post-row tails},\\
&\text{roots equal off }p,\\
&\text{source coalition }B,\quad\text{target coalition }A.
\end{aligned}
$$

The event space is compact; coalition labels are discrete; and these equality conditions are closed. Thus, after one shared subsequence,

$$
\Gamma_n\Longrightarrow \Gamma_0.
$$

The couplings are supported on

$$
\operatorname{Diag}\cup\mathcal T_{p,B,A},
$$

a closed set. Since the coalition-pair coordinate \((B,A)\) is clopen,

$$
m_0:=\Gamma_0(\mathcal T_{p,B,A})
=\lim_n m_n\ge\rho^2>0. \tag{5}
$$

Consequently the limit still contains a genuine historical paid event; it is not merely a terminal law having some unrelated positive \(A\)-coordinate.

The chronological-law infrastructure already provides compactness of laws recording clocks, roots, continuation vectors and coalitions.  Its jump-limit theorem also shows that a positive nonterminal chronological jump has one shared finite-stage approximation and one limiting product root.

After simultaneously compactifying the source semantic/law points, write the resulting datum as

$$
\xi_0=(z_0^-,z_0^+,\theta_0,\Gamma_0),
$$

where \(\theta_0\) is the common post-mark joint tail. Then

$$
\begin{gathered}
d_p(z_0^+)=0,\\
d_p(z_0^-)=g_0=\Delta m_0>0,\\
b_p(z_0^-)=b_p(z_0^+),\\
D(\theta_0)=D_*,\\
D_0:=D(z_0^+)>D_*.
\end{gathered} \tag{6}
$$

The strict inequality is the strict canonical endpoint residual.

## 3. Common-prefix compiler

For a product root \(x\), let

$$
c(x)=\prod_i x_i(C).
$$

There is a continuous common-prefix map

$$
\Phi_x(z^-,z^+,\theta,\Gamma)
=
(T_xz^-,T_xz^+,\theta,\operatorname{Pref}_x\Gamma).
$$

On the chronological coupling, \(\operatorname{Pref}_x\) adds the common date-zero absorption events diagonally and sends every old event clock \(s\) to

$$
(1-c(x))+c(x)s.
$$

Hence the paid-toggle mass satisfies the exact identity

$$
m(\Phi_x\xi)=c(x)m(\xi). \tag{7}
$$

The actual source-to-target payoff gain obeys the same equation:

$$
g(\Phi_x\xi)=c(x)g(\xi). \tag{8}
$$

Suppose \(x\) is exact Nash against the target cap \(b^+\). Exact cap-Nash transport gives

$$
D(T_xz^+)=c(x)D(z^+). \tag{9}
$$

It also preserves target \(p\)-zero:

$$
d_p(T_xz^+)=c(x)d_p(z^+)=0. \tag{10}
$$

Because the two ports have the same \(p\)-cap, the \(p\)-coordinate optimality of \(x\) is the same on the source port. Therefore

$$
d_p(T_xz^-)=c(x)d_p(z^-)=c(x)g(\xi)=g(\Phi_x\xi). \tag{11}
$$

Thus common exact target prefixing preserves the entire two-port contract, not only the target law.

## 4. The marked two-port saturation hull

Let \(\mathscr P\) be the compact closure of all actual paired descendants of the fixed paid-row family under common finite root prefixes.

Define \(\mathscr H^\pm\) as the intersection of all closed subsets of \(\mathscr P\) which:

1. contain \(\xi_0\);
2. consist of target-\(p\)-zero states;
3. are closed under \(\Phi_x\) whenever \(x\) is exact Nash against the displayed target cap;
4. are closed under a debt-nonincreasing same-law replacement only when the replacement has a source-port lift in \(\mathscr P\) preserving \(\theta,\Gamma,m,g\).

The fourth clause is the essential correction. The target-only law-tight hull allows every lower-debt replacement in the same complete-law fibre. The paired hull allows one only when the complete marked source port survives that replacement.

The ambient paired carrier itself satisfies these clauses, so \(\mathscr H^\pm\) is nonempty and compact.

Let

$$
D^\pm:=\min_{\xi\in\mathscr H^\pm}D(z^+_\xi)
$$

and let \(\mathscr F^\pm\) be its minimum level set.

### Historical charge survives the whole saturation

Every point \(\xi\in\mathscr H^\pm\) satisfies

$$
\boxed{
D(z^+_\xi)m_0\le D_0m(\xi),
\qquad
D(z^+_\xi)g_0\le D_0g(\xi).
} \tag{12}
$$

Indeed:

* both sides scale by \(c(x)\) under an exact common prefix;
* a paired same-law replacement can only decrease the left-hand debt while leaving \(m\) and \(g\) unchanged;
* the relations are closed and hold with equality at \(\xi_0\).

Since every target semantic pair lies in the ordinary carrier,

$$
D(z^+_\xi)\ge D_*.
$$

Therefore every face point retains explicit positive floors:

$$
m(\xi)\ge \frac{D^\pm}{D_0}m_0
\ge \frac{D_*}{D_0}\rho^2>0, \tag{13}
$$

and

$$
g(\xi)\ge \frac{D^\pm}{D_0}g_0
\ge
\frac{D_*}{D_0}\frac{\rho D_*}{3}>0. \tag{14}
$$

In particular, on the face,

$$
d_p(z^+_\xi)=0,
\qquad
d_p(z^-_\xi)=g(\xi)>0. \tag{15}
$$

This is the desired coupling of the upstream paid port to the downstream \(p\)-zero state.

### The target face has only all Continue

Let \(\xi\in\mathscr F^\pm\), and let \(x\) be exact Nash against its target cap. Then \(\Phi_x\xi\in\mathscr H^\pm\), so minimality and (9) give

$$
D^\pm\le D(\Phi_xz^+)=c(x)D^\pm.
$$

Since \(D^\pm\ge D_*>0\) and \(c(x)\le1\),

$$
c(x)=1.
$$

A product root has joint Continue probability one only when every player Continues surely. Hence

$$
\boxed{
x\text{ exact Nash against the target cap}
\iff x=C.
} \tag{16}
$$

Thus \(\mathscr F^\pm\) is a genuine \(p\)-zero all-Continue face carrying a positive historical paid jump and its source companion.

This is stronger than the target-only atom-cone statement: (13) concerns the marked off-diagonal mass of \(\Gamma\), not the undifferentiated terminal coordinate \(\mu^+(A)\).

## 5. Relation to the existing target-only face

Let \(\mathscr H^+\) be the corresponding target-only \(p\)-zero law-tight hull, and write

$$
D^+=\min_{z\in\mathscr H^+}D(z).
$$

For every target-only invariant set, its inverse image under the target projection is a valid paired invariant set. Therefore

$$
D^+\le D^\pm. \tag{17}
$$

There is now an exact exhaustive alternative.

### Coupled-face arm

If

$$
D^\pm=D^+,
$$

then every paired minimizer projects to the pre-existing target-only minimum face. Hence the upstream paid row is coupled to that precise downstream face, with the quantitative retained floors (13)–(15).

### Positive lift-gap arm

If

$$
D^+<D^\pm,
$$

define

$$
\kappa:=D^\pm-D^+>0. \tag{18}
$$

Then no target point within \(\kappa\) of the target-only minimum debt admits a marked source-port lift in the paired saturation hull. More strongly, the compact target projection of \(\mathscr F^\pm\) and the compact target-only face are disjoint, so their metric distance is positive.

This is an exact **marked-lift obstruction certificate**:

$$
\boxed{
(\mathscr H^+,\mathscr H^\pm,D^+,D^\pm,\kappa).
} \tag{19}
$$

It identifies the missing operation precisely: some target-only law-tight debt reduction cannot preserve the historical paid event, its source law, and its unilateral source–target relation.

## 6. What bounded capacity rules out

Let \(C<\infty\) bound the hazard charge of every finite exact Nash–Bellman block in the canonical payoff box; this exists in every hypothetical Fin4 counterexample.

Any compiler that converted the horizontal paid seam into an exact positive-charge block returning to the same target cap would contradict this bound. If such a block had charge \(h>0\), then concatenating it \(N\) times would give an exact block of charge \(Nh>C\).

Therefore:

$$
\boxed{
\text{the two-port coupling can be static or one-way, but cannot close into
a positive-charge exact return.}
} \tag{20}
$$

This explains why the coupled face is compatible with bounded capacity. Its only target exact root is all Continue; the positive charge is stored in the historical horizontal paid port, not in an exact Nash–Bellman edge.

In the positive lift-gap arm, the terminal exploitability witness, the finite capacity bound, and the compact separation datum (19) form a sound compact counterexample-certificate schema:

* the exploitability witness certifies the all-behavior terminal gap;
* bounded capacity excludes an exact returned-block bypass;
* \(\kappa>0\) excludes a source-preserving law-tight lift.

It is **not yet a finite rational certificate**. Such a certificate would additionally need finite representations of the two closed hulls, or a finite barrier separating them, and an effective capacity barrier rather than only the existential bound.

## 7. Residual after the coupling

The live strict residual is now one object, not two disconnected limits:

$$
\boxed{
\begin{array}{c}
\text{compact marked source--target face }\mathscr F^\pm,\\
d_p(z^+)=0,\qquad d_p(z^-)=g>0,\\
m\ge \dfrac{D_*}{D_0}\rho^2,\qquad
g\ge \dfrac{D_*}{D_0}\dfrac{\rho D_*}{3},\\
\text{common minimum post-row tail},\\
\text{target exact-root set }=\{C\},\\
\text{bounded exact-block capacity}.
\end{array}}
\tag{21}
$$

The remaining branch is exactly the equality-versus-positive-lift-gap test \(D^\pm=D^+\) or \(D^\pm>D^+\). It is no longer a compactness recurrence problem, a persistent-label selection problem, or a request for another normalized return.

The repository currently contains the separate bounded-capacity, saturation-face, paid-row and chronological-law components, but not this combined marked two-port structure or theorem. Under the project’s validation standard, the construction above is therefore a mathematical result and Lean handoff, not yet a compiled or axiom-audited declaration.
