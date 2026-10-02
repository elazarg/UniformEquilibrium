# Executable compact state: audited theorem core

## Status

The exact stopping-law semantics, the split Late/Never compactification, the
program-dependent continuity estimates, the tight-fusion theorem for rooted
elementary operation diagrams, and the late-mass capacity obstruction below
are sound ordinary mathematics. The clock/tester semantic nonattainment
example is already present in checked form in
`PositiveDebtTerminalSemanticNonattainment.lean`; the additional content here
is its split-clock and summable-recovery-budget formulation.

This note does **not** prove that arbitrary regeneration, limit-witness, or
endogenously selected-root edges form a closed executable program language.
Each such edge requires its own closed-limit or reconstruction theorem. Nor
does the note produce a tight vanishing-debt family from an arbitrary reward
table. The terminal-Nash result is a consumer of supplied tight coherent
data.

The hinge is to separate three objects that cannot safely be identified:

$$
\text{exact stopping-law source}
\quad\longrightarrow\quad
\text{compact finite-program trace}
\quad\longrightarrow\quad
\text{executable diagonal realization}.
$$

The compact trace may contain boundary points representing stopping mass that has escaped to arbitrarily late finite dates. Such a point is not automatically an actual behavioral source. The project’s existing nonlocality analysis identifies precisely this failure of ordinary inverse-limit compactness and the need for tightness, defect variables, or a recovery theorem.  Absorption paths provide a different compactification, parametrized by cumulative absorption probability rather than calendar time; the construction below instead keeps calendar-time stopping laws and exposes their escape defect explicitly. ([arXiv][1])

The results below give a positive reconstruction theorem for an elementary
program grammar and a negative theorem showing why an actuality or tightness
passport cannot be omitted.

# 1. Exact stopping-law semantics

Write

$$
K:=\mathbb N\sqcup\{\infty\}.
$$

Before absorption, there is one public live history at each date. Hence a behavioral strategy of player \(i\) is equivalent to a probability law

$$
\mu_i\in\Delta(K)
$$

for its quitting time \(T_i\). Explicitly, if \(x_i^t\) is the conditional probability of quitting at date \(t\), then

$$
\mu_i(t)=x_i^t\prod_{s<t}(1-x_i^s),
\qquad
\mu_i(\infty)=\prod_{s\ge 0}(1-x_i^s).
\tag{1}
$$

Conversely, putting

$$
s_i(t):=\mu_i(\{t,t+1,\ldots,\infty\}),
$$

the law is executed by

$$
x_i^t=
\begin{cases}
\mu_i(t)/s_i(t),&s_i(t)>0,\\
0,&s_i(t)=0.
\end{cases}
\tag{2}
$$

Thus every law used below has an explicit behavioral compiler.

For a profile \(\mu=(\mu_i)_{i\in I}\), take the \(T_i\)'s independently. Let

$$
m(T):=\min_i T_i,
$$

and define the terminal coalition

$$
\Gamma(T)=
\begin{cases}
\{i:T_i=m(T)\},&m(T)<\infty,\\
\varnothing,&m(T)=\infty.
\end{cases}
$$

Allowing a bounded payoff \(r(\varnothing)\) covers an arbitrary Never payoff; the usual quitting-game convention is \(r(\varnothing)=0\). Put

$$
R:=\max_{i,S}|r_i(S)|
$$

and

$$
U_i(\mu):=
\mathbb E_\mu[r_i(\Gamma(T))].
\tag{3}
$$

## Complete unilateral obstacle

For \(i\in I\) and \(t\in K\), define

$$
V_i^\mu(t):=
U_i(\delta_t,\mu_{-i}).
\tag{4}
$$

Every behavioral replacement \(\rho_i\in\Delta(K)\) satisfies

$$
U_i(\rho_i,\mu_{-i})
=
\sum_{t\in K}\rho_i(t)V_i^\mu(t).
\tag{5}
$$

Consequently the unrestricted behavioral cap is exactly

$$
B_i(\mu)
=
\sup_{\rho_i\in\Delta(K)}
U_i(\rho_i,\mu_{-i})
=
\sup_{t\in K}V_i^\mu(t).
\tag{6}
$$

This includes Never and every arbitrarily late deterministic stopping time; no stationary or bounded-horizon restriction has been made.

There is also a genuine late-finite boundary value. Let

$$
M_{-i}:=\min_{j\ne i}T_j
$$

and, on \(M_{-i}<\infty\), let \(A_{-i}\) be the first opponent coalition. Then

$$
\begin{aligned}
V_i^\mu(n)
={}&
\mathbb E\!\left[
r_i(A_{-i})\,\mathbf 1_{\{M_{-i}<n\}}
\right]\\
&+
\mathbb E\!\left[
r_i(A_{-i}\cup\{i\})\,\mathbf 1_{\{M_{-i}=n\}}
\right]
+
r_i(\{i\})\Pr(M_{-i}>n).
\end{aligned}
\tag{7}
$$

Since \(\Pr(M_{-i}=n)\to0\), dominated convergence gives

$$
V_i^\mu(n)\longrightarrow
V_i^\mu(\omega):=
\mathbb E\!\left[
r_i(A_{-i})\,\mathbf 1_{\{M_{-i}<\infty\}}
\right]
+
r_i(\{i\})\Pr(M_{-i}=\infty).
\tag{8}
$$

By contrast,

$$
V_i^\mu(\infty)=
\mathbb E\!\left[
r_i(A_{-i})\,\mathbf 1_{\{M_{-i}<\infty\}}
\right]
+
r_i(\varnothing)\Pr(M_{-i}=\infty).
\tag{9}
$$

Thus Late and Never are different strategic actions whenever

$$
r_i(\{i\})\ne r_i(\varnothing)
\quad\text{and}\quad
\Pr(M_{-i}=\infty)>0.
$$

Introduce the split compactification

$$
\widehat K:=
(\mathbb N\cup\{\omega\})\sqcup\{\infty\},
\tag{10}
$$

where \(n\to\omega\), while \(\infty\) is isolated. The response obstacle extends continuously to \(\widehat K\), and

$$
B_i(\mu)=\max_{t\in\widehat K}V_i^\mu(t).
\tag{11}
$$

The value at \(\omega\) may be the cap even when no actual finite date attains it.

---

# 2. The finite elementary-program trace state

An **elementary program** \(P\) is a finite rooted directed acyclic diagram.
Its initial ports are actual stopping-law profiles. Every other port is
obtained from earlier ports by one of:

* a fixed finite prefix or concatenation;
* complete unilateral replacement by an exogenous actual stopping law; or
* suffixing at a fixed depth on a specified positive-reach domain.

All discrete labels and depths are fixed as part of the diagram. Prefix roots
and exogenous replacement laws may vary along an approximating family, but
are then explicit program inputs. A diagram may have several independent
initial ports, in which case its realization is a coherent packet of actual
profiles rather than one controller.

The labels include, before any estimate is requested:

* every finite prefix word;
* every replacement law;
* every suffix depth;
* every named continuation or source port;
* every selected product root;
* every reach condition;
* every exogenous law-valued input.

Regeneration relations, rank transitions, limit witnesses, and roots selected
only implicitly by auxiliary equations are not elementary edges. They may be
adjoined only after a separate theorem proves that the relevant relation is
closed or supplies an executable limit adapter.

Let \(V(P)\) be the finite set of source nodes occurring while executing \(P\).

For each node \(v\), retain:

$$
\mathcal Z_v=
\left(
(\widehat\mu_{v,i})_{i\in I},
\lambda_v,
(V_{v,i})_{i\in I},
(B_{v,i})_{i\in I}
\right),
\tag{12}
$$

where:

1. \(\widehat\mu_{v,i}\in\Delta(\widehat K)\) is the split compactified stopping law;
2. \(\lambda_v\in\Delta(2^I)\) is the complete terminal-coalition law;
3. \(V_{v,i}\in[-R,R]^{\widehat K}\) is the complete unilateral obstacle;
4. \(B_{v,i}\in[-R,R]\) is the unrestricted cap.

For an actual law, \(\widehat\mu_{v,i}(\omega)=0\). The extra mass

$$
e_{v,i}:=\widehat\mu_{v,i}(\omega)
\tag{13}
$$

is precisely late-finite escape mass in compact limits.

The ambient finite-program carrier is

$$
\mathcal C_P
=
\prod_{v\in V(P)}
\left[
\Delta(\widehat K)^I
\times
\Delta(2^I)
\times
\prod_{i\in I}[-R,R]^{\widehat K}
\times
[-R,R]^I
\right].
\tag{14}
$$

It is compact and metrizable.

For every actual legal execution \(s\) of \(P\), let

$$
\operatorname{Tr}_P(s)\in\mathcal C_P
\tag{15}
$$

be its exact trace. Define

$$
X_P:=
\overline{
\{\operatorname{Tr}_P(s):
s\text{ is an actual legal execution of }P\}
}.
\tag{16}
$$

This is the compact semantic part of the state.

If \(P\preceq Q\), meaning that \(Q\) extends \(P\), forgetting the additional nodes gives a continuous restriction map

$$
\pi_{QP}:X_Q\longrightarrow X_P.
\tag{17}
$$

Hence \((X_P,\pi_{QP})\) is a projective family.

A point of \(X_P\) alone is **not** declared executable. The full state is

$$
(x,\Pi),
\qquad x\in X_P,
\tag{18}
$$

where \(\Pi\) is one of the following passports.

### Actual passport

It contains the exact stopping laws at the named source ports, operation labels, reach proofs, and the equations showing that \(x=\operatorname{Tr}_P(s)\).

### Tight-fusion passport

It contains a sequence of actual traces, coherent on all previously introduced nodes, together with the tail and reach data used in the reconstruction theorem below.

### Ranked-regeneration passport

It contains an actual regeneration constructor, a renewable well-founded rank
\(\rho\), a terminal consumer, and a backward compiler, with the selected
successor carrying a rank \(\rho'<\rho\). This is a pointwise control passport:
it may be run after one actual node has been reconstructed.

No transition in a proof is licensed merely because two compact points lie in
a closed graph. It must be backed by one of these passports. The tight-fusion
theorem below covers the elementary grammar only. A pointwise
ranked-regeneration passport is an external control adapter, not a
trace-visible edge and not a consequence of that theorem. To occur inside a
compact diagonal, its complete tagged terminal and successor relations and
all visible child/backward outputs need the stronger closed trace certificate
specified in GRAMMAR.md.

---

# 3. Exact operation semantics

All basic operations act directly on stopping laws.

## Finite prefixing and concatenation

Let \(x^0,\ldots,x^{L-1}\) be a finite product word. For player \(i\), set

$$
d_i^x(t)
=
x_i^t\prod_{s<t}(1-x_i^s),
\qquad
c_i^x
=
\prod_{s<L}(1-x_i^s).
\tag{19}
$$

Prefixing a continuation law \(\mu_i\) gives

$$
(\operatorname{Pref}_x\mu_i)(t)
=
d_i^x(t),
\quad t<L,
\tag{20}
$$

$$
(\operatorname{Pref}_x\mu_i)(L+n)
=
c_i^x\mu_i(n),
\tag{21}
$$

and

$$
(\operatorname{Pref}_x\mu_i)(\infty)
=
c_i^x\mu_i(\infty).
\tag{22}
$$

This is implemented behaviorally by playing the displayed word and then using the continuation compiler (2). Finite block concatenation is the same operation.

## Complete unilateral replacement

For a replacement law \(\rho_i\),

$$
\operatorname{Rep}_{i,\rho_i}(\mu)
=
(\rho_i,\mu_{-i}).
\tag{23}
$$

This changes the player’s complete strategy, not merely a bounded prefix.

## Positive-reach suffix

For depth \(h\), define

$$
s_i^\mu(h)
=
\mu_i(\{h,h+1,\ldots,\infty\}).
\tag{24}
$$

If all \(s_i^\mu(h)>0\), conditioning on joint survival to \(h\) preserves independence and yields

$$
(\operatorname{Suf}_h\mu_i)(n)
=
\frac{\mu_i(h+n)}{s_i^\mu(h)},
\qquad
(\operatorname{Suf}_h\mu_i)(\infty)
=
\frac{\mu_i(\infty)}{s_i^\mu(h)}.
\tag{25}
$$

Thus positive-reach suffix selection has exact source-level semantics.

A root chosen by solving an auxiliary equation need not depend continuously on the state. The chosen root itself is therefore part of the program label or passport. The prefix operation is continuous in the pair “selected root, continuation”; no continuous global root selector is assumed.

---

# 4. Program-dependent quantitative stability

For an actual law \(\mu\), define its late finite tail

$$
\tau_\mu(N):=
\sum_{n>N}\mu(n).
\tag{26}
$$

For two actual laws define the finite-cylinder discrepancy

$$
\Delta_N(\mu,\nu)
=
|\mu(\infty)-\nu(\infty)|
+
\sum_{n=0}^{N}|\mu(n)-\nu(n)|.
\tag{27}
$$

Then

$$
\boxed{
\|\mu-\nu\|_1
\le
\Delta_N(\mu,\nu)
+
\tau_\mu(N)+\tau_\nu(N).
}
\tag{28}
$$

In particular, if both tails are at most \(\eta\),

$$
\|\mu-\nu\|_1
\le
\Delta_N(\mu,\nu)+2\eta.
\tag{29}
$$

This is the elementary bridge from compact finite coordinates to the noncompact total-variation topology.

## Strategic Lipschitz estimates

For profile laws \(\mu,\nu\),

$$
\left\|
\bigotimes_i\mu_i-
\bigotimes_i\nu_i
\right\|_1
\le
\sum_i\|\mu_i-\nu_i\|_1.
\tag{30}
$$

Therefore

$$
|U_i(\mu)-U_i(\nu)|
\le
R\sum_j\|\mu_j-\nu_j\|_1.
\tag{31}
$$

For the complete obstacle,

$$
\sup_{t\in\widehat K}
|V_i^\mu(t)-V_i^\nu(t)|
\le
R\sum_{j\ne i}\|\mu_j-\nu_j\|_1.
\tag{32}
$$

Taking maxima gives

$$
|B_i(\mu)-B_i(\nu)|
\le
R\sum_{j\ne i}\|\mu_j-\nu_j\|_1.
\tag{33}
$$

Thus one total-variation estimate on the opponents controls **every** unilateral behavioral replacement, including Never and stopping dates beyond every fixed calendar cutoff.

There is also a sharper program-local late-date estimate. Put

$$
\theta_i^\mu(N)
:=
\Pr_\mu(N<M_{-i}<\infty).
\tag{34}
$$

For every \(t>N\), the actions \(t\) and \(\omega\) differ only when the opponents’ first finite stop is after \(N\). Hence

$$
|V_i^\mu(t)-V_i^\mu(\omega)|
\le
2R\,\theta_i^\mu(N).
\tag{35}
$$

Consequently

$$
\boxed{
0
\le
B_i(\mu)
-
\max\left\{
V_i^\mu(0),\ldots,V_i^\mu(N),
V_i^\mu(\omega),V_i^\mu(\infty)
\right\}
\le
2R\,\theta_i^\mu(N).
}
\tag{36}
$$

This is the precise sense in which no modulus uniform over every suffix depth is needed: after the finite program and player are fixed, one chooses one cutoff controlling the entire later stopping menu.

## Lipschitz constants for program operations

For a fixed prefix word \(x\),

$$
\|\operatorname{Pref}_x\mu_i-
  \operatorname{Pref}_x\nu_i\|_1
\le
\|\mu_i-\nu_i\|_1.
\tag{37}
$$

If the words \(x,y\) also vary,

$$
\|\operatorname{Pref}_x\mu_i-
  \operatorname{Pref}_y\nu_i\|_1
\le
\|\mu_i-\nu_i\|_1
+
2\sum_{t<L}|x_i^t-y_i^t|.
\tag{38}
$$

This follows by coupling the two finite Bernoulli words with common uniforms.

For suffixes, if

$$
s_i^\mu(h),s_i^\nu(h)\ge\alpha>0,
$$

then

$$
\boxed{
\|\operatorname{Suf}_h\mu_i-
  \operatorname{Suf}_h\nu_i\|_1
\le
\frac{2}{\alpha}\|\mu_i-\nu_i\|_1.
}
\tag{39}
$$

Indeed, conditioning and normalizing a restriction of mass at least \(\alpha\) has \(2/\alpha\) Lipschitz constant.

For every fixed finite elementary program \(P\), composing these constants
gives a finite, explicitly computable number \(L_P(\alpha)\). For example, the
coarse bound

$$
L_P(\alpha)
\le
\prod_{\substack{e\text{ suffix edge}\\\text{of }P}}
\max\left\{1,\frac{2}{\alpha_e}\right\}
\tag{40}
$$

suffices when the prefix words and replacement laws are fixed.

Let \(\mathcal L(P)\) be the finite set of initial and exogenous law-valued
inputs used by \(P\). Choose cutoffs \(N_{\ell,i}\) and tail bounds
\(\eta_{\ell,i}\) after \(P\) is fixed. Assume that, for both packets and
every \((\ell,i)\),

$$
\tau_{\mu_{\ell,i}}(N_{\ell,i}),
\tau_{\nu_{\ell,i}}(N_{\ell,i})
\le \eta_{\ell,i}.
$$

If the operation parameters are fixed and the two input packets satisfy the
same reach margins, define

$$
E_P(\mu,\nu):=
\sum_{\ell\in\mathcal L(P)}
\sum_{i\in I}
\left(
\Delta_{N_{\ell,i}}(\mu_{\ell,i},\nu_{\ell,i})
+
2\eta_{\ell,i}
\right),
\tag{41}
$$

then at every program node \(v\),

$$
\sum_i
\|\mu^v_i-\nu^v_i\|_1
\le
L_P(\alpha)\,E_P(\mu,\nu),
\tag{42}
$$

and therefore

$$
\boxed{
\max_{v,i}
\left\{
|U_i(\mu^v)-U_i(\nu^v)|,\,
|B_i(\mu^v)-B_i(\nu^v)|
\right\}
\le
R\,L_P(\alpha)\,E_P(\mu,\nu).
}
\tag{43}
$$

This is the required quantitative stability modulus. It is program-dependent, depends on only finitely many reach margins and tail cutoffs, and makes no demand uniform over unrequested calendar depths.

If finite prefix words, replacement laws, or selected roots also vary, the
right side must additionally contain their explicit total-variation or
finite-dimensional parameter errors, such as the second term in (38). No
continuity of an unrecorded endogenous selector is asserted.

---

# 5. Executable diagonal reconstruction

The noncompact part of the architecture is controlled by the following passport.

## Tight-fusion hypotheses

Let

$$
P_1\preceq P_2\preceq\cdots
$$

be an increasing sequence of rooted elementary programs actually requested by
a construction, with one common restriction-compatible sequence of actual
executions. Let \(s_m\) denote the full execution packet: actual initial
ports, exogenous law inputs, and every varying finite prefix/root parameter
needed to execute \(P_m\). If there is one initial port, its controller is the
root component of \(s_m\).

For every initial port and every exogenous law-valued input \(a\), player
\(i\), and finite date \(n\), assume:

### Coordinate coherence

Once \(a\) appears,

$$
\mu^{m,a}_i(n)
\quad\text{and}\quad
\mu^{m,a}_i(\infty)
$$

converge as \(m\to\infty\).

### Eventual uniform tightness at that port

For every \(\varepsilon>0\), there is a cutoff \(N=N(a,i,\varepsilon)\), fixed after \(a,i,\varepsilon\) are requested, such that

$$
\sup_{m\ge m_0(a,i,\varepsilon)}
\tau_{\mu^{m,a}_i}(N)
\le\varepsilon.
\tag{44}
$$

There is no common cutoff over all future ports or suffix depths.

### Reach margins

For every suffix edge \(e\) that eventually appears, its conditioning masses are eventually bounded below by a fixed

$$
\alpha_e>0.
\tag{45}
$$

### Literal operation coherence

The rooted diagrams, discrete labels, and depths agree under restriction from
\(P_{m+1}\) to \(P_m\). Every varying finite prefix/root parameter converges
in its finite-dimensional parameter space. Every exogenous replacement or
continuation law satisfies the same coordinate-coherence and tightness
hypotheses as an initial port, equivalently converges in total variation to an
actual law. Every non-elementary edge is excluded or carries a separately
proved closed-limit executable adapter.

## Theorem 1 — tight-fusion reconstruction

Under these hypotheses there is one actual limiting packet \(s_\infty\) of
initial ports such that, for every fixed \(k\),

$$
\operatorname{Tr}_{P_k}(s_m)
\longrightarrow
\operatorname{Tr}_{P_k}(s_\infty)
\tag{46}
$$

in all stopping-law, terminal-law, obstacle, payoff, and unrestricted-cap coordinates.

Moreover, every elementary program operation in \(P_k\) is realized by the
corresponding actual behavioral operation on \(s_\infty\). If the rooted
diagram has one initial port, this is one actual behavioral controller. With
several independent initial ports, it is one coherent packet of actual
controllers.

### Proof

Fix an initial port or exogenous law input \(a\) and player \(i\). Let

$$
\mu_i^a(n):=\lim_m\mu_i^{m,a}(n),
\qquad
\mu_i^a(\infty):=
\lim_m\mu_i^{m,a}(\infty).
\tag{47}
$$

For every \(\varepsilon>0\), choose \(N\) from (44). Passing to the limit in the finite partial sum gives

$$
\sum_{n\le N}\mu_i^a(n)+\mu_i^a(\infty)
\ge
1-\varepsilon.
$$

Every finite partial sum of the limiting coordinates is also at most one.
Thus the full limiting mass is at most one, while the displayed inequality
gives the reverse bound as \(\varepsilon\downarrow0\). Therefore

$$
\sum_{n\in\mathbb N}\mu_i^a(n)+\mu_i^a(\infty)=1.
\tag{48}
$$

Thus no mass remains at \(\omega\), and \(\mu_i^a\) is an actual law on \(K\).

Using the same \(N\), finite-coordinate convergence and the uniform tail bound imply

$$
\|\mu_i^{m,a}-\mu_i^a\|_1\longrightarrow0.
\tag{49}
$$

Compile each \(\mu_i^a\) to an actual hazard sequence using (2).

Prefixing, replacement, and concatenation commute with these limits by
(37)–(38). Positive-reach suffixing commutes by (39) and the fixed reach
margin. A topological induction over the rooted finite diagram therefore
shows that all derived node laws are the literal laws obtained by executing
the elementary program on the reconstructed initial ports. A non-elementary
edge is covered only by its separately supplied adapter.

Finally, (31)–(33) imply convergence of terminal payoffs, complete obstacles,
and unrestricted caps. Program restriction coherence ensures that the packet
reconstructed for \(P_{k+1}\) restricts to the same packet already
reconstructed for \(P_k\). Therefore one limiting execution realizes the
entire increasing family. ∎

This is stronger than selecting a new source independently for every depth.
With one initial port it constructs one behavioral controller for the whole
requested elementary diagonal.

---

# 6. A terminal-Nash consumer

The architecture has a direct global consumer.

## Theorem 2 — tight coherent vanishing debt yields one terminal Nash profile

In the setting of Theorem 1, suppose there is a vector \(v\in\mathbb R^I\) and numbers \(\varepsilon_m\downarrow0\) such that at the initial source node

$$
U(s_m)\longrightarrow v
\tag{50}
$$

and

$$
B_i(s_m)-U_i(s_m)\le\varepsilon_m
\qquad(i\in I).
\tag{51}
$$

Then the reconstructed source \(s_\infty\) satisfies

$$
U(s_\infty)=v
\tag{52}
$$

and

$$
B_i(s_\infty)=U_i(s_\infty)
\qquad(i\in I).
\tag{53}
$$

Hence \(s_\infty\) is an exact all-behavior terminal Nash profile. In particular, the constant sequence \(s_\infty,s_\infty,\ldots\) supplies terminal approximate Nash profiles with the one limiting payoff \(v\).

### Proof

Theorem 1 and (31)–(33) give

$$
U_i(s_m)\to U_i(s_\infty),
\qquad
B_i(s_m)\to B_i(s_\infty).
$$

Taking limits in (51),

$$
B_i(s_\infty)-U_i(s_\infty)\le0.
$$

The reverse inequality always holds because the prescribed strategy of player \(i\) is one of the behavioral replacements over which \(B_i\) takes its supremum. Thus equality holds. Equation (52) follows from (50). ∎

This proves the first requested consumer whenever the finite-program producer supplies a tight coherent vanishing-debt family. It does not assert that every reward table automatically supplies such a family.

---

# 7. Exact obstruction to omitting the passport

The tightness condition is not a technical convenience. Projective coherence
of all fixed finite cylinder tests, even together with exact terminal payoffs
and unrestricted caps, does not imply executable realization.

First, there is a general capacity obstruction.

## Lemma 3 — late-mass budget obstruction

Let \(\widehat\mu\in\Delta(\widehat K)\), with late mass

$$
e:=\widehat\mu(\omega).
$$

Let \(\beta_\infty\ge0\) and \(\beta_n\ge0\), with

$$
\sum_{n\in\mathbb N}\beta_n<\infty.
$$

Suppose an actual law \(\nu\in\Delta(K)\) is required to satisfy

$$
|\nu(n)-\widehat\mu(n)|\le\beta_n
\quad(n\in\mathbb N)
$$

and

$$
|\nu(\infty)-\widehat\mu(\infty)|\le\beta_\infty.
$$

Then necessarily

$$
\boxed{
e\le
\beta_\infty+\sum_{n\in\mathbb N}\beta_n.
}
\tag{54}
$$

### Proof

Since \(\nu\) has no \(\omega\)-mass,

$$
\begin{aligned}
e
&=
1-\widehat\mu(\infty)-\sum_n\widehat\mu(n)\\
&=
\sum_n\bigl(\nu(n)-\widehat\mu(n)\bigr)
+
\bigl(\nu(\infty)-\widehat\mu(\infty)\bigr).
\end{aligned}
$$

Take absolute values and use the displayed coordinate bounds. ∎

A compact late atom therefore requires enough total chronological error budget to be distributed back over actual finite dates. Coordinatewise errors tending to zero are not sufficient information; their total capacity matters.

## Theorem 4 — finitely compatible cylinder states with no executable diagonal

Consider two players, a clock \(c\) and an atom tester \(a\), with

$$
r(\{c\})=(-1,0),\qquad
r(\{a\})=(0,0),\qquad
r(\{c,a\})=(0,1),
\tag{55}
$$

and \(r(\varnothing)=(0,0)\).

For each \(n\ge1\), let:

* \(a\) play Never;
* \(c\) stop uniformly on \(\{0,\ldots,n-1\}\).

Then:

$$
U(\sigma^n)=(-1,0),
\tag{56}
$$

$$
B_c(\sigma^n)=0,
\qquad
B_a(\sigma^n)=\frac1n.
\tag{57}
$$

The corresponding compact root traces, including any fixed finite family of
clock coordinates and the full terminal semantic pair, have a coherent limit
whose root coordinates are

$$
\widehat\mu_c=\delta_\omega,
\qquad
\widehat\mu_a=\delta_\infty,
\tag{58}
$$

and whose semantic pair is

$$
z=
\bigl(
U=(-1,0),\,
B=(0,0)
\bigr).
\tag{59}
$$

This coherent compact state has no actual behavioral realization.

The same clock/tester semantic nonattainment appears in the project’s terminal-semantic analysis; the proof below also gives the stronger program-budget formulation. 

### Computation of the trace

The prescribed terminal coalition is always \(\{c\}\), giving (56).

Player \(c\) can replace its strategy by Never and obtain \(0\), while every finite stopping time gives \(-1\). Hence \(B_c=0\).

If player \(a\) quits at date \(t<n\), it receives \(1\) exactly when \(c\) also stops at \(t\), which has probability \(1/n\). All other outcomes give \(a\) payoff \(0\). Hence \(B_a=1/n\).

For every fixed finite date \(t\),

$$
\mu_c^n(t)=\frac1n\longrightarrow0,
\qquad
\mu_c^n(\infty)=0.
$$

All unit mass therefore converges to the separate late point \(\omega\), proving (58).

### Failure of exact realization

Suppose an actual profile \(\sigma\) realized (59). Since \(c\)'s payoff is \(-1\) only at coalition \(\{c\}\) and is \(0\) at all other outcomes,

$$
U_c(\sigma)=-1
$$

forces terminal coalition \(\{c\}\) with probability one. In particular, \(c\)'s stopping law is a probability law on the countable set \(\mathbb N\). It therefore has an atom:

$$
\mu_c(t_0)>0
$$

for some \(t_0\).

If \(a\) replaces its complete strategy by quitting at \(t_0\), its expected payoff is exactly

$$
\mu_c(t_0)>0,
$$

because it receives \(1\) on the tie \(T_c=t_0\), and \(0\) otherwise. Thus

$$
B_a(\sigma)>0,
$$

contradicting the target cap \(B_a=0\). Therefore no actual profile realizes the coherent state.

### A fixed error surviving a summable diagonal budget

Set

$$
\beta_t:=2^{-t-2},
\qquad
\sum_{t\ge0}\beta_t=\frac12.
\tag{60}
$$

For every finite set \(F\subseteq\mathbb N\) and every \(\delta>0\), choose \(n\) so large that

$$
\frac1n<\delta
\quad\text{and}\quad
\frac1n\le\min_{t\in F}\beta_t.
\tag{61}
$$

Then \(\sigma^n\) simultaneously satisfies:

$$
\mu_c^n(t)\le\beta_t
\quad(t\in F),
$$

$$
U_c(\sigma^n)=-1,
\qquad
B_a(\sigma^n)<\delta.
\tag{62}
$$

Thus every fixed finite family of root clock-coordinate and terminal-semantic
probes can be satisfied to arbitrarily small semantic error. No claim is made
here for arbitrary suffix, regeneration, rank, limit-witness, or
endogenous-selector requirements.

However, any one actual profile \(\sigma\) satisfying

$$
\mu_c(t)\le\beta_t
\qquad\text{for every }t
\tag{63}
$$

has

$$
\Pr(T_c<\infty)
=
\sum_t\mu_c(t)
\le\frac12.
$$

Consequently

$$
U_c(\sigma)
=
-\Pr(\Gamma=\{c\})
\ge
-\Pr(T_c<\infty)
\ge-\frac12.
\tag{64}
$$

Its prescribed payoff therefore remains at distance at least

$$
\boxed{\frac12}
\tag{65}
$$

from the finitely compatible target \(-1\).

Already at the cylinder level, this gives the decisive quantifier separation:

$$
\forall\text{ finite probe families }F\;
\exists\text{ actual source }\sigma_F
$$

holds, even with arbitrary accuracy, while

$$
\exists\text{ one actual source realizing the diagonal}
$$

fails by a fixed amount. This narrower statement suffices to refute the claim
that compact coordinate coherence alone guarantees an executable diagonal.

---

# 8. Audited conclusion and remaining question

The proved core is:

1. The split trace records complete terminal semantics, finite dates, Never,
   and the nonattained Late response boundary.
2. Prefixing, convergent complete replacement, positive-reach fixed-depth
   suffixing, and concatenation have exact law semantics and a computable
   modulus after one finite rooted elementary diagram is fixed.
3. Coordinate coherence plus eventual finite-tail tightness at every initial
   or exogenous law input reconstructs one actual total-variation limit.
   Elementary operations commute with that limit. With one initial port this
   gives one controller; with several it gives one coherent controller packet.
4. If the reconstructed root profiles have vanishing debt and one limiting
   payoff, the limit is an exact all-behavior terminal Nash profile.
5. Compact coordinate coherence without tightness is insufficient. The
   clock/tester example has finitely compatible cylinder traces but no actual
   semantic realization; any recovery with the displayed summable coordinate
   budget loses at least \(1/2\) in payoff.

The unproved architectural step is to equip every non-elementary edge used by
the Fin4 construction—especially regeneration, limit witnesses, and
endogenous root selection—with either a closed-limit executable trace adapter
or a pointwise renewable rank applied after actual reconstruction. A ranked
child that is itself visible in the compact trace additionally needs the
closed tagged branch certificate specified in GRAMMAR.md. The theorem here
does not produce those adapters and does not produce tight vanishing-debt
source data. Thus it answers the reconstruction and obstruction parts of the
sufficient-state problem, but not the arbitrary-game producer problem.

No modulus uniform over all future calendar depths is needed for the proved
elementary theorem: the cutoff and reach-dependent modulus is chosen only
after the finite diagram is fixed. What remains nonautomatic is production or
consumption of late mass and certification of the non-elementary edges.

[1]: https://arxiv.org/abs/2012.04369 "Absorption Paths and Equilibria in Quitting Games"
