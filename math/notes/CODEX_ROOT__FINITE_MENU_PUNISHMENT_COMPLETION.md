# Finite-menu punishment convergence and same-prefix tail completion

Maintainer: CODEX_ROOT. Author: external proof supplied in gpt/COMPLETION.md.

Status: ordinary mathematics with independent PASS reviews by CODEX_RENY and
CODEX_SKEPTIC, including explicit attempts to falsify the full-deviation claim.
This is a durable internal copy of the original proof, not an early-absorption
producer or a solution of UE. No new Lean declaration is claimed.

The assembled completion and generic early-absorption characterization has
passed two whole-packet independent reviews, by CODEX_RENY and CODEX_HILBERT,
and is frozen in
[the final export](../exports/FINITE_MENU_PUNISHMENT_COMPLETION_AND_EARLY_ABSORPTION_CHARACTERIZATION.md).
Its SHA-256 is
`c8861a4160c0bf77da4fff22e2961b6cf63980e70656e4277b73edf8b15c3ef6`.
Both reviewers confirmed the final bytes after the three administrative
header/provenance/link changes; the proof and all mathematical statements
were unchanged. The final link check passed. This records a completed
mathematical gate, not Lean implementation or a source-existence theorem.

Independent reviews:
[CODEX_RENY](../feedback/COMPLETION__BY_CODEX_RENY.md) and
[CODEX_SKEPTIC](../feedback/COMPLETION__BY_CODEX_SKEPTIC.md).

## Scope and review clarification

The game has a nonempty finite player set, independent behavioral strategies,
bounded terminal rewards, zero reward on Never, and unrestricted unilateral
behavioral deviations. The finite-menu source is only approximately Nash
against its own displayed menu. The completion retains the entire pre-cut
profile and chooses one punishment target before play, without detecting a
deviation.

No substantive repair was required. In the punishment-convergence proof below,
the finite-cap convergence sentence uses this explicit fact. Truncating each
opponent's finite stopping dates at least H to Never leaves EVERY retained
pure-date test a<H exactly unchanged. The Never payoff changes by at most

    2M ∑[j≠i] Pr(H≤T_j<∞),

which tends to zero. The finite maximum therefore converges to the supremum
of all finite-date tests together with Never. Pointwise convergence of an
arbitrary changing test family would not suffice.

The final boundary example uses two nontrivial stopping clocks, not two
players with nontrivial strategic preferences: the second displayed payoff
coordinate is identically zero. This wording distinction changes none of its
payoff calculations or its counterexample to unchanged tail extension.

Two immediate consequences checked in the review are worth keeping visible:

- A finite-menu e-Nash source at deadline N satisfies the unconditional floor
  U_i ≥ P_i − ω(N) − e. No no-UE or exact-spine hypothesis is used.
- A positive unrestricted terminal exploitability gap forces a uniform
  positive reach into one bounded final window for every sufficiently accurate
  finite-menu Nash source. This holds for any finite player count and all
  reward signs. It does not construct a source violating that floor.

The novelty relative to the inspected repository interfaces is the
finite-menu source comparison and quantitative completion, not the already
available stationary punishment equality. The original proof follows in full.

## Retained proof

Small joint survival does not imply small survival under every unilateral deviation. The finite-menu route therefore needs a tail-completion argument, rather than an unchanged extension of the displayed law.

That completion can be proved quantitatively. **I have not proved the early-absorption producer, constructed the arbitrarily charged forward packets, or excluded the inert chamber.** The result below closes only the completion step.

## Quantitative completion of a finite-menu equilibrium

Write

$$
M=\max_{i,S\ne\varnothing}|r_i(S)|.
$$

For player \(i\), let

$$
m_i(H)=
\inf_{p_{-i}}
\max_{\tau_i\in\{0,\ldots,H-1,\mathrm{Never}\}}
U_i(\tau_i,p_{-i})
$$

be the punishment value in the \(H\)-date finite-menu game. The infimum ranges over independent opponent stopping-time laws on that menu. Set

$$
\omega(H)=\max_i\bigl(P_i-m_i(H)\bigr)_+.
$$

The following statement holds for any finite number of players.

**Theorem.** Suppose \(p\) is finite-menu \(e\)-Nash at its actual deadline \(N\), \(N\ge H\), and

$$
R_p(N-H)<\rho.
$$

For every \(\eta>0\), there is a behavioral profile \(\widehat p\), agreeing with \(p\) before date \(N-H\), whose unrestricted terminal exploitability satisfies

$$
\boxed{
E_r(\widehat p)
\le
e+2M\rho+
\max\!\left\{2M\sqrt{\rho},\ \omega(H)+\eta\right\}.
}
\tag{1}
$$

Moreover,

$$
\omega(H)\longrightarrow0.
\tag{2}
$$

Only one punishment continuation is needed. Its intended target is selected from \(p\) before play; the construction does not require observing who deviated.

### Proof of the completion bound

Put \(t=N-H\), and define the individual and opponent-deleted survival probabilities

$$
s_j=\Pr_p(T_j\ge t\text{ or }T_j=\mathrm{Never}),
\qquad
D_i=\prod_{j\ne i}s_j.
$$

Then \(R_p(t)=\prod_j s_j\). For distinct players \(i,j\),

$$
D_iD_j
=
R_p(t)\prod_{k\ne i,j}s_k
\le R_p(t)<\rho.
\tag{3}
$$

Consequently, **at most one player has \(D_i>\sqrt{\rho}\)**.

If there is no such player, replace the continuation from \(t\) onward by all-Never.

Otherwise, let \(i_*\) be that unique player. Choose an actual behavioral punishment profile against \(i_*\) with unrestricted cap at most

$$
P_{i_*}+\eta,
$$

and use it from date \(t\) onward. Complete the prescribed strategy of \(i_*\) there arbitrarily, for example by Never. Equation (3) gives

$$
D_j<\sqrt{\rho}\qquad(j\ne i_*).
\tag{4}
$$

This defines \(\widehat p\). Since prescribed play changes only after joint survival to \(t\),

$$
\left|U_i(\widehat p)-U_i(p)\right|
\le 2M R_p(t)<2M\rho.
\tag{5}
$$

Let \(B_i^N(p)\) denote the best-response cap on the original displayed menu. Finite-menu Nash gives

$$
B_i^N(p)\le U_i(p)+e.
\tag{6}
$$

For any player \(j\) whose deleted survival satisfies \(D_j\le\sqrt{\rho}\), changing the continuation can increase its unrestricted cap by at most

$$
2M D_j\le2M\sqrt{\rho}.
\tag{7}
$$

To see this directly, a deviation quitting before \(t\) has exactly its old payoff. A deviation continuing to \(t\) encounters the changed continuation only when every opponent survives to \(t\), an event of probability \(D_j\). The old finite menu contains Never, so it supplies a comparison action whose conditional tail payoff is at least \(-M\); every new conditional tail payoff is at most \(M\).

It remains to control the exceptional player \(i_*\). Conditional on all its opponents surviving to \(t\), their original remaining stopping laws form a product law on the \(H\)-date menu. The exceptional player’s best response on that remaining menu therefore yields at least

$$
m_{i_*}(H).
$$

The new punishment continuation instead gives it at most \(P_{i_*}+\eta\).

More explicitly, let \(L_i\) be the expected payoff from opponents quitting before \(t\), when player \(i\) continues until \(t\). Then

$$
B_i^N(p)\ge L_i+D_i m_i(H),
$$

whereas every new deviation continuing until \(t\) gives at most

$$
L_i+D_i(P_i+\eta).
$$

Deviations quitting before \(t\) are unchanged. Hence

$$
\begin{aligned}
B_{i_*}(\widehat p)
&\le B_{i_*}^N(p)
  +D_{i_*}\bigl(P_{i_*}+\eta-m_{i_*}(H)\bigr)_+\\
&\le B_{i_*}^N(p)+\omega(H)+\eta.
\end{aligned}
\tag{8}
$$

These bounds cover unrestricted behavioral deviations: before absorption, every live public history is the all-Continue history, so a unilateral strategy is a stopping-time law, and its payoff is a mixture of deterministic quitting-time and Never payoffs.

Combining (5)–(8) proves (1). ∎

## Why the finite-menu punishment values converge

This step does not assume approximate equilibria.

Fix \(i\). For an opponent product root \(y\), write

$$
Q_i(y)=\text{payoff from quitting now},
$$

$$
A_i(y)=
\sum_{\varnothing\ne S\subseteq I\setminus\{i\}}
p_y(S)r_i(S),
\qquad
c_i(y)=p_y(\varnothing).
$$

Define the scalar operator

$$
\Phi_i(x)=
\min_y\max\{Q_i(y),\,A_i(y)+c_i(y)x\}.
\tag{9}
$$

Backward induction gives

$$
m_i(0)=0,\qquad m_i(H+1)=\Phi_i(m_i(H)).
\tag{10}
$$

The operator is nondecreasing and \(1\)-Lipschitz, and preserves \([-M,M]\). Its iterates from \(0\) are monotone: their direction is determined by whether \(\Phi_i(0)\) is above or below \(0\). Thus

$$
m_i(H)\longrightarrow \ell_i,
\qquad
\Phi_i(\ell_i)=\ell_i.
\tag{11}
$$

We show \(\ell_i=P_i\).

**First, \(\ell_i\le P_i\).** Fix any infinite opponent profile. Truncate each opponent’s stopping law at \(H\), replacing later stopping times by Never. The resulting finite-menu best-response cap converges to the original unrestricted cap: every fixed finite quitting-time payoff is eventually unchanged, and the payoff from Never converges because the probability of an opponent’s finite quit after \(H\) tends to zero.

Each such finite-menu cap is at least \(m_i(H)\). Passing to the limit, then taking the infimum over infinite opponent profiles, gives \(\ell_i\le P_i\).

**Conversely, \(P_i\le\ell_i\).** Fix \(x>\ell_i\). Nonexpansiveness gives

$$
\Phi_i(x)\le x.
$$

Choose a minimizing product root \(y\) in (9). Thus

$$
Q_i(y)\le x,\qquad A_i(y)+c_i(y)x\le x.
\tag{12}
$$

If \(c_i(y)<1\), stationary repetition of \(y\) has unrestricted unilateral cap

$$
\max\left\{
Q_i(y),\frac{A_i(y)}{1-c_i(y)}
\right\}\le x.
$$

Therefore \(P_i\le x\).

If \(c_i(y)=1\), every opponent Continues. Equation (12) implies \(r_i(\{i\})\le x\). When \(x\ge0\), the all-Never opponent profile has cap

$$
\max\{r_i(\{i\}),0\}\le x.
$$

The remaining case \(x<0\) cannot occur: \(c_i(y)=1\) would imply \(\Phi_i(x)=x\), and monotonicity would then give

$$
m_i(H)=\Phi_i^H(0)\ge\Phi_i^H(x)=x
$$

for every \(H\), contradicting \(\ell_i<x\).

Hence \(P_i\le x\) for every \(x>\ell_i\), proving \(P_i=\ell_i\) and therefore (2). ∎

## What this establishes—and what it does not

Given the proposed finite-menu producer, choose

$$
e<\varepsilon/4,\qquad \eta<\varepsilon/8,
$$

then choose \(H\) with \(\omega(H)<\varepsilon/8\), and choose \(\rho\) sufficiently small that

$$
2M\rho<\varepsilon/4,
\qquad
2M\sqrt{\rho}<\varepsilon/4.
$$

Its output would then yield an actual terminal \(\varepsilon\)-Nash profile by (1). Thus the producer really requires only the stated finite-menu error; unrestricted terminal regret need not be supplied as an extra hypothesis.

The targeted punishment is essential to this argument. For example, take two strategically active players, with the other two players always receiving zero, and set

$$
r(\{1\})=(1,0),\qquad
r(\{2\})=(2,0),\qquad
r(\{1,2\})=(0,0)
$$

in the active coordinates. Extend these rewards by ignoring the inactive players’ membership, assigning zero when neither active player quits.

At any deadline \(N\ge2\), let player 1 quit at date \(0\), and let player 2 choose \(N-1\) and Never with probability \(1/2\) each. This is exact Nash on its displayed menu: player 1 obtains \(1\), earlier finite quitting dates also give \(1\), the last date gives \(1/2\), and Never gives \(1\). Prescribed survival after date \(0\) is zero. Nevertheless, adding date \(N\) gives player 1 payoff \(3/2\). Small prescribed survival therefore does not justify keeping the original tail unchanged.

**The missing producer remains missing.** Nothing in the completion proof forces an actual finite-menu Nash law to satisfy \(R_p(N-H)<\rho\), and nothing constructs successive positive-charge roots at their literal moving Bellman values. It therefore does not consume \((B)\), supply a renewable rank, or establish the requested conclusion.
