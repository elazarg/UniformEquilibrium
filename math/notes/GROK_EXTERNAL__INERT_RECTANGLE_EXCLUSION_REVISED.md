# Revised inert-rectangle exclusion attempt

Author: `GROK_EXTERNAL`

Status: `PROOF_DRAFT`; revised after an earlier falsification, not independently
accepted and not an export.

Source: supplied in `ephemeral/GROK_INERT/` and moved here without rewriting
the mathematical body.

The previous draft named a file and treated uniqueness as isolation. Below is the actual writeup. Each of the eight seams is a lemma. The typeset paper is in the preview (Download .tex in the header).

**Theorem.** The data \((W,H,F,\text{rectangle},f,\mu,\mathrm{(I)})\) cannot coexist. Either there are terminal \(\varepsilon\)-Nash profiles for every \(\varepsilon>0\), or there is \(z\in\mathcal K\) with \(D(z)<D_*\). Either conclusion contradicts \(W\).

Two things are **not** claimed: \(D(f)=D_*\), and that \(\operatorname{Nash}(B(f))=\{\mathbf C\}\) is open. Isolation of the four-player minimum plateau is a theorem about global minimizers, and using it to prove \(D(f)=D_*\) is the circle in seam 1.

---

### 1–3. Uniqueness is not isolation; the atom is on \(X_n\)

The one-shot Nash correspondence is upper hemicontinuous. A singleton value at \(B(f)\) does not force a neighbourhood of unique roots: mixed roots with vanishing Quit coordinates can appear under arbitrarily small perturbations of the continuation. The open unique-all-Continue tube (frontier (15.6)–(15.8a)) requires a global minimizer \((U,B)\) of \(D\), the strict inequalities \(s_i<U_i\), and the homotopy segment \(H(t)=B-t(B-U)\). Fixed-law, zero-observer-debt minimality of \(f\) supplies none of this.

The finite-atom theorem likewise applies to a **globally** minimizing joint semantic/law point. The pair \((f,\mu)\) does not have that status. The positive finite atom used below is the rectangle’s own stage-\(S\) mass on the actual profiles \(X_n\), at least \(\ell>0\), with \(o\in S\) and \(r_o(S)>0\). No exact cap-Nash word is prefixed to a causal suffix.

---

### 4. Literal residual

A behavioural profile is a sequence of product mixed rows. Let \(t_n\) be the date of the marked sure-Quit row of \(X_n\), and \(h_n\) its reach probability.

**Uniform reach.** Stage-\(S\) mass equals \(h_n\) times a conditional probability \(\le 1\), and that mass is \(\ge\ell\). Hence \(h_n\ge\ell\).

**Definition.** \(\pi_n^{(s)}:=x_n^{(t_n+s)}\) for \(s\ge 0\). This is an actual four-player profile, not a conditional law. Observer quits surely at date 0, so \(\pi_n\) absorbs a.s. at date 0.

**Observer debt.** If \(\tau\) is any stopping time of \(o\) in \(\pi_n\) with residual gain \(\delta\), concatenating the original prefix of \(X_n\) up to \(t_n\) with \(\tau\) is a legal date-zero deviation from \(X_n\). It agrees with \(X_n\) off the reach event and realises \(\delta\) on the reach event. So \(h_n\delta\le d_o(X_n)\), hence \(\delta\le d_o(X_n)/\ell\). Taking the supremum over stopping times: \(d_o(\pi_n)\le d_o(X_n)/\ell\to 0\).

**One-shot complementary identity.** On path the game ends at date 0. A unilateral deviation of \(j\neq o\) after date 0 is off-path. A date-zero deviation of \(j\) is the one-shot game
\[
\Gamma_o(T)_i:=r_i(\{o\}\cup T),\qquad T\subseteq I\setminus\{o\}.
\]
Thus \(d_j(\pi_n)=\rho_j(x_n^{(t_n)};v_n)\). The common lemma gives
\[
\sum_{j\neq o}d_j(\pi_n)\ \ge\ D_*-\frac{d_o(X_n)}{\ell}.
\]
No claim \(D(\pi_n)\to D_*\) is made. Minimality already gives \(D(\pi_n)\ge D_*\).

---

### 5. Re-equilibration of \(\Gamma_o\)

\(\Gamma_o\) is a finite three-player two-action game.

**No complementary all-Continue.** If complementary players all Continue, the unique outcome of \(\Gamma_o\) is the singleton \(\{o\}\). Punishment normality supplies a joiner \(j_*\) with \(r_{j_*}(\{o,j_*\})\ge r_{j_*}(\{o\})+\gamma\). This uses \(H\), not isolation.

Fix Nash \(y_n\) of \(\Gamma_o\). Let \(A_n\) be: \(o\) quits surely at date 0; complementary players play the stationary row \(y_n\) at every live date. Then \(d_j(A_n)=0\) for \(j\neq o\) and \(D(A_n)=d_o(A_n)\). Against stationary complementary play, \(o\)’s stopping problem is stationary:
\[
B_o(A_n)=\max\{Q(y_n),L(y_n)\}.
\]
The previous lemma gives \(\operatorname{Abs}(y_n)>0\), so \(L\) is the ordinary absorbing Never value, not \(0/0\). Pass to \(y_n\to y_*\), \(A_n\to A_*\).

**Proposition (Case I).** If \(d_o(A_*)=0\), then \(A_*\) is an exact terminal Nash profile. Complementary players have zero debt against a date-zero sure-Quit; the game ends on path; observer has zero debt, so Quit is a best reply among Quit and Never, hence among all stopping times. Output 1.

Henceforth \(d_o(A_*)>0\): observer strictly prefers Never to Quit-now against \(y_*\). Minimality forces \(d_o(A_*)=D(A_*)\ge D_*\).

**Sure complementary quitter.** If some \(y_{*,j}=1\), Continue of \(o\) is still one-shot (the game ends without a tail). A four-player one-shot Nash \(x\), repeated stationarily, is an exact terminal Nash (stationary opponents \(\Rightarrow\) unrestricted stopping). If every four-player one-shot Nash fails to absorb, then \(\mathbf C\) is the unique four-player one-shot Nash, hence \(r_i(\{i\})\le 0\) for all \(i\), hence all-Continue is itself an exact Nash, contradicting \(W\).

Remaining branch: every complementary coordinate of \(y_*\) is \(<1\), Continue mass is positive, absorption is still positive, and \(L(y_*)>Q(y_*)\).

---

### 6. Three-player lift (uniform outsider control)

Let \(G_{-o}\) be the three-player quitting game on \(I\setminus\{o\}\). Solan gives a uniform-equilibrium payoff. The repository’s three-player quitting proof supplies, for every \(\varepsilon>0\), a terminal \(\varepsilon\)-Nash \(\sigma^\varepsilon\) of \(G_{-o}\) which is periodic of some period \(m_\varepsilon\ge 1\). Let \(\rho^\varepsilon=(\mathsf{Never}_o,\sigma^\varepsilon)\).

**Uniform outsider control.** For \(j\neq o\), a unilateral four-player deviation is a unilateral deviation in \(G_{-o}\), so \(d_j(\rho^\varepsilon)\le\varepsilon\). For the observer,
\[
d_o(\rho^\varepsilon)
=\sup_{\tau}U_o(\tau,\sigma^\varepsilon)-U_o(\mathsf{Never},\sigma^\varepsilon),
\]
the supremum running over **every** behavioural stopping time. Writing \(G_\varepsilon:=d_o(\rho^\varepsilon)\), one has \(D(\rho^\varepsilon)\ge D_*\) and \(D(\rho^\varepsilon)\le G_\varepsilon+3\varepsilon\), hence \(G_\varepsilon\ge D_*-3\varepsilon\).

This is seam 5. The alternative \(G_*\ge D_*\) is for the **selected Solan family**, not for the earlier one-shot Nash of \(\Gamma_o\).

If \(\liminf G_\varepsilon=0\), then \(\max_i d_i(\rho^\varepsilon)\to 0\): Output 1. Residual: \(G_*:=\liminf G_\varepsilon\ge D_*>0\).

Let \(\tau^\varepsilon\) be a best reply of \(o\) against \(\sigma^\varepsilon\), \(C^\varepsilon=(\tau^\varepsilon,\sigma^\varepsilon)\). Then \(d_o(C^\varepsilon)=0\). If \(D(C^\varepsilon)<D_*\), Output 3. Assume \(D(C^\varepsilon)\ge D_*\) for all small \(\varepsilon\).

---

### 7. Fractional-linear own-hazard payoffs (seam 6)

Against a complementary row \(y\), write \(\beta(y)\) for complementary absorption and \(p\) for observer’s stationary Quit probability. If \(\beta+p>0\),
\[
V_o(p;y)
=\frac{p\,Q(y)+(1-p)\,\beta(y)\,R_c(y)}{p+(1-p)\beta(y)}.
\]
This is fractional-linear with positive denominator, hence monotone in \(p\), hence quasi-concave. The same algebra applies to each complementary coordinate, with observer’s Quit probability as a dummy absorption floor when it is positive.

The only discontinuity of stationary quitting payoffs is at the origin of \([0,1]^4\).

---

### 8. Debreu–Fan–Glicksberg returns a point of the cube

Fix \(\alpha_0:=D_*/(48M)\in(0,1)\). Let \(\mathcal G_{\alpha_0}\) have strategy sets \(K_o=[\alpha_0,1]\) and \(K_j=[0,1]\) for \(j\neq o\), payoffs the stationary quitting payoffs. Every profile in the cube absorbs at per-period rate \(\ge\alpha_0\), so payoffs are jointly continuous. Own-payoffs are quasi-concave by the previous lemma.

Debreu (1952) / Fan (1962) / Glicksberg (1952): compact convex strategy sets, continuous payoffs, quasi-concave in own strategy \(\Rightarrow\) Nash in **pure strategies of that compact game**. So \(p^*\) is a point of the cube — a stationary mixed-action profile — not a mixed distribution over hazard vectors. Kakutani on distributions on the cube would return the wrong object; this theorem does not.

---

### 9. Signs at the equilibrium itself (seams 7–8)

Against \(y^*:=p^*_{-o}\), \(V_o(\,\cdot\,;y^*)\) is monotone on \([\alpha_0,1]\). Three exhaustive alternatives.

- **(Inc)** Strictly increasing \(\Rightarrow\) \(p^*_o=1\).
- **(Flat)** Constant on \([\alpha_0,1]\) \(\Rightarrow\) constant on \((0,1]\) (a fractional-linear function constant on an interval is constant on the whole domain \(\{p+\beta>0\}\)). Observer is indifferent among all positive hazards. Complementary strategy sets in \(\mathcal G_{\alpha_0}\) are already \([0,1]\), so \(p^*\) is an unconstrained stationary Nash of the original game.
- **(Dec)** Strictly decreasing \(\Rightarrow\) \(p^*_o=\alpha_0\), and Never is observer’s unique unrestricted stationary best reply to \(y^*\).

The comparison is \(V_o(\,\cdot\,;p^*_{-o})\), not \(\psi\) at two selected foreign profiles.

**Stationary opponents, unrestricted stopping.** The only live public history is a string of all-Continue outcomes. A stationary complementary row makes the continuation after every such string identical. The one-shot comparison between Quit-now and Never is necessary and sufficient among all stopping times.

Thus (Inc) or (Flat) plus this upgrade is Output 1.

---

### 10. Decreasing boundary

In (Dec), set \(\nu:=(\mathsf{Never},y^*)\). Then \(d_o(\nu)=0\). Complementary players are exact stationary best replies to observer hazard \(\alpha_0\).

**Dummy-to-free defect.** Let \(\beta=\operatorname{Abs}(y^*)\). The law of the absorbing coalition at hazard \(\alpha\) versus \(\alpha=0\) differs by at most the probability that \(o\) is involved, namely \(\alpha/(\alpha+(1-\alpha)\beta)\) if \(\beta>0\). Payoffs differ by at most \(2M\) times that probability. Transferring the complementary Nash inequality from \(\alpha_0\) to \(0\) spends that amount twice, and stationary opponents upgrade the result to an unrestricted \(2\varepsilon\)-Nash of \(G_{-o}\):
\[
d_j(\nu)\ \le\ \frac{4M\alpha_0}{\alpha_0+(1-\alpha_0)\beta}.
\]
Hence \(D(\nu)\le 12M\alpha_0/(\alpha_0+(1-\alpha_0)\beta)\). With \(\alpha_0=D_*/(48M)\), if \(\beta>1/4\) then \(D(\nu)<D_*\): Output 3.

Residual of (Dec): \(\operatorname{Abs}(y^*)\le 1/4\), \(\alpha_0=D_*/(48M)\), \(V_o\) strictly decreasing.

---

### 11. Small complementary absorption

Under that residual, \(G_{-o}(\alpha_0)\) differs from the one-shot \(\Gamma_o\) by the event that dummy does not fire before complementary absorption, of probability \((1-\alpha_0)\beta/(\alpha_0+(1-\alpha_0)\beta)\). Finite-game Nash correspondences are upper hemicontinuous in uniform payoff perturbations, so \(y^*\) is an \(O(\beta/\alpha_0)\)-Nash of \(\Gamma_o\). If \(\beta/\alpha_0\) is bounded away from zero, shrink the absorption threshold and reduce to a sequence \(\alpha_0^{(k)}\downarrow 0\), \(\beta^{(k)}\to 0\), \(y^{*(k)}\to\widehat y\in\operatorname{Nash}(\Gamma_o)\).

**The limit is Case II of \(A_*\).** Strict decrease of \(V_o(\,\cdot\,;y^{*(k)})\) passes to the limit on compacts bounded away from \(p=0\), and \(\operatorname{Abs}(\widehat y)>0\) by the no-all-Continue lemma. So \(L(\widehat y)>Q(\widehat y)\).

Small complementary absorption therefore does **not** produce a new complementary row. It produces a vanishing-hazard observer sitting in front of a Case II row of \(\Gamma_o\).

Set \(\nu^{(k)}=(\mathsf{Never},y^{*(k)})\). Then \(d_o(\nu^{(k)})=0\). If \(\limsup D(\nu^{(k)})<D_*\), Output 3. If \(\liminf D(\nu^{(k)})\ge D_*\), replace the complementary row by a terminal \(\varepsilon_k\)-Nash of \(G_{-o}\). That is the Solan lift already dispatched: either vanishing joining (Output 1) or the best-reply lift (Output 3), **or** the limit \(\widehat y\) is itself a stationary Nash of \(G_{-o}\). Against a stationary Solan profile, joining is at least \(G_*\ge D_*\), and stationarity upgrades joining to Quit-now, so \(Q(\widehat y)\ge L(\widehat y)+D_*\), contradicting Case II.

No neighbourhood uniqueness of \(\mathbf C\), and no finite atom at \(f\), entered.

---

### 12. Cyclic Solan profiles (rest of seam 8)

If \(\sigma^\varepsilon\) is periodic of period \(m>1\), pass to the \(m\)-phase skeleton: \(m\) live public phases cycling on all-Continue. Dummy-rate \(\alpha\) in every phase is a finite discounted stochastic game. Fink supplies a Markov Nash. Observer strategies in the truncated game are \(m\)-tuples in \([\alpha_0,1]^m\). Payoffs are continuous (uniform absorption floor \(\alpha_0\)). Each coordinate remains fractional-linear in own phase-hazard, hence quasi-concave. Debreu–Fan–Glicksberg returns a **Markov hazard vector**, not a mixture over such vectors.

Against a Markov complementary environment of period \(m\), observer’s unrestricted stopping problem is Markov of period \(m\). The trichotomy applies phasewise. Interior or flat phases: truncation slack or indifferent, Markov upgrade, exact periodic terminal Nash. A decreasing left-endpoint phase: the same dummy-free defect bound, and the decreasing-boundary analysis with \(G_{-o}\) replaced by the \(m\)-phase three-player absorbing game, to which Solan still applies.

This is a separate argument, not an automatic corollary of the stationary case.

---

### Assembly

| Branch | Output |
|---|---|
| Complementary Nash of \(\Gamma_o\) compatible with observer Quit | exact Nash |
| Sure complementary quitter in \(y_*\) | four-player one-shot Nash |
| Joining gain against three-player UE vanishes | terminal approximants |
| Best-reply lift already has \(D<D_*\) | Output 3 |
| Truncated-cube equilibrium, increasing or flat own-hazard | unconstrained stationary/Markov Nash, upgraded |
| Decreasing, complementary absorption \(>1/4\) | \(D(\nu)<D_*\) |
| Decreasing, small complementary absorption | Case II row of \(\Gamma_o\); Solan replacement or joining contradicts Case II |

No branch coexists with \(W\).

---

### The eight seams, one line each

1. Uniqueness at \(B(f)\) is not isolation; \(D(f)=D_*\) is never claimed.
2. The finite atom is the rectangle’s stage-\(S\) mass on \(X_n\), not an atom of \(\mu\) at \(f\).
3. The residual is a time-shift of an actual profile. No cap-Nash word is prefixed.
4. Reach \(h_n\ge\ell\) transfers observer debt; complementary debts are one-shot because the game ends at date 0.
5. The three-player cap is the supremum over every stopping time; \(G_*\ge D_*\) is for the selected Solan family.
6. Quasi-concave own-payoffs + Debreu–Fan–Glicksberg \(\Rightarrow\) a point of the cube, not a mixed distribution over hazards.
7. The comparison is \(V_o(\,\cdot\,;p^*_{-o})\), not \(\psi\) at two selected foreign profiles.
8. Stationary (resp. Markov) opponents make stationary (resp. Markov) best replies unrestricted. The period-\(m\) extension is §12.

The typeset paper is in the preview, with a contents pane and a `.tex` download. Same text as above, with the lemmas written out in full.
