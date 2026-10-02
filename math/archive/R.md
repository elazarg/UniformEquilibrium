I have not proved or refuted **(R)**. I have established a quantitative reduction showing that, as universally quantified in the question, **(R) is equivalent to approximate-equilibrium existence for all finite quitting games**.

This equivalence remains true even when the source in (A) is a **single fixed stationary, exactly \(0\)-perfect profile**, every restarted tail terminates geometrically, and every finite live history has positive probability. Thus the reduction does not use nonterminating null tails.

The construction also preserves positive exploitability gaps and, with an appropriate parameter, preserves the global infimum of total deviation debt exactly.

## 1. An extension of an arbitrary quitting game

Start with an arbitrary quitting game

$$
G=(J,r,z),
$$

where \(J\) is finite and nonempty. Choose \(M>0\) such that

$$
|r^i(S)|\le M,\qquad |z^i|\le M
$$

for all original players \(i\) and nonempty coalitions \(S\subseteq J\).

Add one player, denoted \(\dagger\), and choose a parameter \(K>0\). Define the extended game \(\widehat G_K\) on

$$
\widehat J=J\cup\{\dagger\}
$$

by

$$
\widehat z=(z,0)
$$

and, for every nonempty \(S\subseteq\widehat J\),

$$
\widehat r(S)=
\begin{cases}
\bigl(r(S),0\bigr),&\dagger\notin S,\\[2mm]
\bigl(M\mathbf 1_J,-K\bigr),&\dagger\in S.
\end{cases}
\tag{7}
$$

Thus, whenever the additional player belongs to the terminal coalition, every original player receives the upper bound \(M\), while the additional player receives \(-K\). If the additional player never quits, the original game is unchanged and her own payoff is zero.

The additional player therefore has a payoff-maximizing strategy against **every** opponents’ profile: Continue forever.

Nevertheless, this game has an exact row-perfect absorbing source.

## 2. A fixed, stationary, exactly row-perfect source

At every date prescribe

$$
q^\dagger=\frac12,
\qquad
q^i=0\quad(i\in J).
\tag{8}
$$

Call this stationary sequence \(x\). Its survival probabilities are

$$
a_{m,N}(x)=2^{-(N-m)}.
$$

Consequently, every restarted tail terminates, and every finite live history has positive probability.

Only the additional player ever quits. Hence the actual restarted-tail payoff is, for every \(m\),

$$
\gamma_m(x)=\bigl(M\mathbf 1_J,-K\bigr).
\tag{9}
$$

For the additional player,

$$
Q^\dagger=-K,\qquad
C^\dagger=\gamma_{m+1}^\dagger=-K,\qquad
V^\dagger=-K.
\tag{10}
$$

Both supported actions are exactly optimal in the one-stage game.

For an original player \(i\),

$$
Q^i
=\frac12 M+\frac12 r^i(\{i\})
\le M,
\tag{11}
$$

whereas

$$
C^i=V^i=M.
\tag{12}
$$

The only supported action of this player is Continue, and it is exactly optimal.

Thus **all four inequalities in (5) hold with \(\varepsilon=0\)**. The same sequence witnesses (A) for every positive error and any positive threshold.

Notice also that this construction preserves the obstruction to all Continue being an equilibrium. If

$$
r^i(\{i\})>z^i
$$

in the original game, the identical inequality holds in the extension. We have not made the question trivial by arranging that all Continue solves the extended game.

Of course, the source (8) is not itself an equilibrium: the additional player improves from \(-K\) to \(0\) by continuing forever. That observation alone would merely repeat the supplied-profile objection. The important part is the following statement about **every profile of the extended game**.

## 3. Every approximate equilibrium of the extension yields one of the original game

For any game \(H\), write

$$
d_i^H(\sigma)=B_i^H(\sigma)-U_i^H(\sigma),
\qquad
E_H(\sigma)=\max_i d_i^H(\sigma).
$$

Let

$$
\widehat\sigma=(\sigma,\sigma^\dagger)
$$

be an arbitrary behavioral profile of \(\widehat G_K\). Here \(\sigma\) is the profile obtained by deleting the additional player.

Let

$$
\alpha
:=
\Pr_{\widehat\sigma}
\bigl(\dagger\text{ belongs to the terminal quitting coalition}\bigr).
\tag{13}
$$

### The additional player’s debt measures the exceptional event exactly

By construction,

$$
U_\dagger^{\widehat G_K}(\widehat\sigma)=-K\alpha.
$$

Every possible payoff of this player is either \(-K\) or \(0\), and Continue forever guarantees zero. Therefore

$$
B_\dagger^{\widehat G_K}(\widehat\sigma)=0
$$

and

$$
d_\dagger^{\widehat G_K}(\widehat\sigma)=K\alpha.
\tag{14}
$$

In particular, an \(\eta\)-equilibrium must satisfy

$$
\alpha\le\frac{\eta}{K}.
\tag{15}
$$

### Removing the additional player changes prescribed payoffs only on that event

Couple the original and extended plays by using the same complete stopping laws for all original players. Let \(Y_i\) be player \(i\)’s realized payoff in the original game.

If the additional player does not belong to the extended game’s terminal coalition, the two realized payoffs agree. If she does belong to it, the extended payoff is \(M\), whereas

$$
-M\le Y_i\le M.
$$

This includes the possibility that the original play never terminates.

Consequently,

$$
0\le
U_i^{\widehat G_K}(\widehat\sigma)-U_i^G(\sigma)
\le 2M\alpha.
\tag{16}
$$

### The comparison also holds under every unilateral deviation

Fix an original player \(i\) and any complete behavioral replacement \(\tau^i\). Apply the same coupling after replacing that player’s law in both games.

The additional player can only replace the original realized payoff by the upper bound \(M\). Thus

$$
U_i^G(\tau^i,\sigma^{-i})
\le
U_i^{\widehat G_K}(\tau^i,\widehat\sigma^{-i})
\tag{17}
$$

for **every** such replacement, including arbitrarily late stopping and Never.

Taking suprema gives

$$
B_i^G(\sigma)\le B_i^{\widehat G_K}(\widehat\sigma).
\tag{18}
$$

Combining (14), (16), and (18), we obtain the playerwise inequality

$$
\boxed{
d_i^G(\sigma)
\le
d_i^{\widehat G_K}(\widehat\sigma)
+\frac{2M}{K}\,
d_\dagger^{\widehat G_K}(\widehat\sigma)
\qquad(i\in J).
}
\tag{19}
$$

This is the required comparison over unrestricted behavioral deviations. In particular,

$$
\boxed{
E_G(\sigma)
\le
\left(1+\frac{2M}{K}\right)
E_{\widehat G_K}(\widehat\sigma).
}
\tag{20}
$$

Taking \(K=M\) keeps all extended rewards in the same interval \([-M,M]\) and gives the particularly simple conclusion

$$
\boxed{
\text{Every terminal }\eta\text{-equilibrium of }\widehat G_M
\text{ projects to a terminal }3\eta\text{-equilibrium of }G.
}
\tag{21}
$$

There is no assumption here about stationarity, support, absorption, or the form of the approximate equilibrium being projected.

## 4. The precise equivalence with unrestricted existence

Let \(\mathcal Q\) denote the assertion

$$
\text{Every finite quitting game has a terminal }\eta
\text{-Nash equilibrium for every }\eta>0.
$$

Let \(\mathcal R\) denote the universal assertion requested in the question:

$$
\text{For every finite quitting game, (A) implies approximate-equilibrium existence.}
$$

Then

$$
\boxed{\mathcal R\iff\mathcal Q.}
\tag{22}
$$

The implication \(\mathcal Q\Rightarrow\mathcal R\) is immediate.

For the converse, take an arbitrary game \(G\) and form \(\widehat G_M\). Section 2 proves that \(\widehat G_M\) satisfies (A), using a fixed exactly row-perfect stationary source. Under \(\mathcal R\), for any \(\eta>0\), the extended game has a terminal \(\eta/3\)-equilibrium. Its restriction to the original players is a terminal \(\eta\)-equilibrium by (21). Since \(G\) was arbitrary, \(\mathcal Q\) follows.

The player-count relation is worth stating precisely:

$$
\boxed{
(R)\text{ for all }(n+1)\text{-player games}
\ \Longrightarrow\
\text{approximate-equilibrium existence for all }n\text{-player games}.
}
\tag{23}
$$

In particular, the five-player instance of the proposed implication already contains unrestricted four-player existence.

Moreover, the extension preserves zero Never payoffs and rationality. If the original game has \(z=0\), rational rewards in \([-1,1]\), and we choose \(M=K=1\), then the extension also has zero Never payoff and rational rewards in \([-1,1]\). Its exact source payoff is simply

$$
(1,\ldots,1,-1).
$$

### Positive gaps transfer as well

Define

$$
E_*(G):=\inf_\sigma E_G(\sigma).
$$

The projection estimate gives

$$
E_*(\widehat G_K)
\ge
\frac{E_*(G)}{1+2M/K}.
\tag{24}
$$

Conversely, extending any original profile by instructing the additional player to Continue forever preserves every original player’s deviation debt and gives the additional player zero debt. Therefore

$$
E_*(\widehat G_K)\le E_*(G).
\tag{25}
$$

Together,

$$
\boxed{
\frac{E_*(G)}{1+2M/K}
\le E_*(\widehat G_K)
\le E_*(G).
}
\tag{26}
$$

Thus any positive-gap quitting game would produce, explicitly, a positive-gap game satisfying (A). This is a counterexample **transfer theorem**, not an explicit counterexample: it still requires a positive-gap original game.

## 5. Even fully mixed witnesses terminating under every deviation do not remove the reduction

The same extended game admits a stronger family of sources. For

$$
0<t<\frac12,
$$

use the stationary row

$$
q^\dagger=1-t,
\qquad
q^i=t\quad(i\in J).
\tag{27}
$$

Let \(n=|J|\) and

$$
b_t=(1-t)^n.
$$

The joint all-Continue probability is

$$
c_t=t b_t<\frac12.
\tag{28}
$$

Every coordinate is strictly between zero and one.

For the additional player, the actual stationary payoff satisfies

$$
\gamma^\dagger
=-(1-t)K+t b_t\gamma^\dagger,
$$

so

$$
\gamma^\dagger
=-K\frac{1-t}{1-tb_t}.
\tag{29}
$$

Her pure-action values are

$$
Q^\dagger=-K,
\qquad
C^\dagger=b_t\gamma^\dagger.
$$

Their difference is

$$
C^\dagger-Q^\dagger
=
K\frac{1-b_t}{1-tb_t}
\le 2Knt,
\tag{30}
$$

using \(1-(1-t)^n\le nt\) and \(1-tb_t\ge1/2\).

For an original player \(i\), under either pure action the additional player quits at the current row with probability \(1-t\), giving payoff \(M\). Conditional on her continuing, the remaining terminal or continuation payoff lies in \([-M,M]\). Hence

$$
Q^i,C^i\in[M-2Mt,M].
\tag{31}
$$

Since \(V^i\) is a convex combination of these two numbers,

$$
|Q^i-V^i|\le2Mt,
\qquad
|C^i-V^i|\le2Mt.
\tag{32}
$$

It follows that every row is playerwise \(\varepsilon_t\)-perfect, with

$$
\boxed{
\varepsilon_t=2t\max\{M,Kn\}\longrightarrow0.
}
\tag{33}
$$

These sources terminate not only under prescribed play, but under **every unilateral behavioral deviation**. Indeed, after deleting any one player, the remaining stationary opponents still have a strictly positive probability of quitting at every date. Their survival probability tends geometrically to zero.

Nevertheless, the additional player’s full deviation debt is

$$
d_\dagger
=
K\frac{1-t}{1-tb_t}
\longrightarrow K.
\tag{34}
$$

Thus the same arbitrary-game extension satisfies (A) through fully mixed stationary sources with all of the following properties simultaneously: uniform geometric termination under prescribed play, termination under every unilateral deviation, and row-perfection errors tending to zero.

The source still need not approach equilibrium. Here the additional player’s deviation to Never does **not** cause infinite play: the original players eventually quit, giving her zero. The problem is accumulated small one-stage gains rather than a positive-probability Never outcome.

Since the projection theorem remains unchanged, restricting (R) to games admitting these stronger sources would still imply \(\mathcal Q\).

## 6. Exact preservation of the global minimum total debt

There is also a direct connection to the total-debt formulation.

Write

$$
D_G(\sigma)=\sum_{i\in J}d_i^G(\sigma),
\qquad
D_*(G)=\inf_\sigma D_G(\sigma).
$$

Summing (19) gives

$$
D_G(\sigma)
\le
\sum_{i\in J}d_i^{\widehat G_K}(\widehat\sigma)
+\frac{2Mn}{K}\,
d_\dagger^{\widehat G_K}(\widehat\sigma).
\tag{35}
$$

Therefore, if

$$
K\ge2Mn,
$$

then

$$
D_G(\sigma)\le D_{\widehat G_K}(\widehat\sigma).
\tag{36}
$$

Taking infima yields

$$
D_*(G)\le D_*(\widehat G_K).
$$

The reverse inequality follows by extending original profiles with the additional player’s Never strategy. Hence

$$
\boxed{
K\ge2M|J|
\quad\Longrightarrow\quad
D_*(\widehat G_K)=D_*(G).
}
\tag{37}
$$

So an arbitrary quitting game can be embedded into one having a fixed, exact, geometrically absorbing row-perfect source **without changing its global infimum of total deviation debt at all**.

## What this establishes—and what remains

The published absorption-path characterization states the reverse (S.3) implication and follows it with the stronger supplied-profile assertion in Theorem 3.5. Under the precise row-only definition in this question, that stronger assertion fails, so it cannot supply the missing argument for (R). ([Springer][1])

The reduction above goes beyond another supplied-profile counterexample: it controls **every possible equilibrium candidate and every behavioral deviation** in the extended game. It proves that the universally quantified implication (R), even with substantially stronger source conditions, contains unrestricted finite quitting-game existence.

**The unresolved step is still the yes-or-no resolution of (R).** What is established here is the quantitative equivalence, the preservation of positive gaps, and the exact preservation of minimum total debt—not a proof of universal existence or an explicit positive-gap game.

[1]: https://link.springer.com/article/10.1007/s10107-022-01807-6 "Absorption paths and equilibria in quitting games | Mathematical Programming | Springer Nature Link"


----

**You are right. The main result of my previous answer is already in the repository.** I inspected the source at commit `d85bd96edf7d1805e2717975dfcc5c963cd67e21`. The differences are in the padding construction and some additional source properties—not in the universal equivalence or the reduction to unrestricted quitting-game existence. I should not have presented that equivalence as new progress.

## 1. The repository already contains the exact main result

The relevant paper-facing file is:

`Literature/AshkenaziGolanKrasikovRainerAndSolan2024.lean`.

It explicitly records that reverse S.3 is universally equivalent to general finite-quitting terminal approximate-equilibrium existence. It also states the restricted stationary-exact, every-restart version, with the same one-added-player cardinality shift emphasized in my answer. The declaration is:

```lean
universal_stationaryExactEveryRestartSource_iff_terminalApproximateExistence
```

This delegates to the integrated proof rather than merely recording a paper claim.

The underlying file is:

`UniformEquilibrium/Quitting/Classification/Existence/ReverseSequentiallyPerfectAbsorbingHardness.lean`.

It contains both:

```lean
universalReverseSequentiallyPerfectAbsorbing_iff_universalApproximateEquilibriumExistence

universalStationaryExactEveryRestartSource_iff_approximateExistence
```

Their proof bodies perform the same reduction I gave: add one player, obtain an absorbing exact row-perfect source, apply the hypothesized implication to the enlarged game, and project approximate equilibria back to the original game. They also handle the empty player set.

There is **no hidden difference in the equilibrium notion**. The underlying definition

```lean
QuittingPayoffTable.ReverseSequentiallyPerfectAbsorbing
```

is precisely

$$
\text{sequentially row-perfect absorbing witnesses at every positive error}
\;\Longrightarrow\;
\text{terminal approximate-equilibrium existence}.
$$

It retains arbitrary Never payoffs and unrestricted behavioral deviations. The literature file’s small-error threshold formulation is connected to this every-positive-error formulation by `hasSmallAbsorbingSequentiallyPerfectProfiles_iff_table`. Thus the threshold in your (A) does not distinguish my result from the repository’s.

## 2. Even the quantitative reduction was already present

The same integrated file contains:

```lean
QuittingPayoffTable.oneDummyPadding_project_exploitability_le
```

In mathematical notation, it proves

$$
E_G(\operatorname{proj}\widehat\sigma)
\le
\left(1+\frac{W}{K}\right)E_{\widehat G}(\widehat\sigma),
\tag{1}
$$

where \(K>0\) is the added player’s penalty and

$$
W=\max_i\left(
\max\bigl(\{z_i\}\cup\{r_i(S):S\ne\varnothing\}\bigr)
-
\min\bigl(\{z_i\}\cup\{r_i(S):S\ne\varnothing\}\bigr)
\right).
$$

The canonical width includes Never, through normalization by subtracting \(z\).

My multiplier \(1+2M/K\) is the corresponding coarser range-bound form, since \(W\le 2M\) under my assumptions.

The global-infimum comparisons were already present too, in:

`UniformEquilibrium/Quitting/Terminal/PassivePlayerPaddingExploitabilityRetraction.lean`.

The declarations

```lean
retractionFactor_mul_quittingTerminalExploitabilityInf_le_padding
quittingTerminalExploitabilityInf_padding_le
```

give, for one added player,

$$
\frac{K}{K+W}E_*(G)
\le E_*(\widehat G)
\le E_*(G).
\tag{2}
$$

That is the same positive-gap preservation mechanism as in my answer.

So neither “the comparison covers every behavioral deviation” nor “positive gaps transfer quantitatively” was a new distinction.

## 3. The actual construction differences

### Collision payoffs

The repository’s padding and mine are not identical payoff tables.

Write \(R\) for a nonempty coalition of original players, and \(\dagger\) for the added player. Let

$$
u_i=\max\bigl(\{z_i\}\cup\{r_i(S):S\ne\varnothing\}\bigr).
$$

The repository’s one-player padding has:

$$
\widehat r(R)=(r(R),0),\qquad
\widehat r(R\cup\{\dagger\})=(r(R),0),\qquad
\widehat r(\{\dagger\})=(u,-K).
\tag{3}
$$

Thus an original quitter takes priority: simultaneous quitting by the added player does not overwrite the original coalition’s payoff and does not penalize the added player. The relevant source declarations explicitly state these three cases.

My construction instead used

$$
\widetilde r(R)=(r(R),0),\qquad
\widetilde r(R\cup\{\dagger\})=(M\mathbf1,-K),\qquad
\widetilde r(\{\dagger\})=(M\mathbf1,-K).
\tag{4}
$$

Here the added player takes priority in a collision.

Accordingly, the exceptional event in the repository is **added-player-only absorption**; in my construction it is **any absorption containing the added player**. Both events are controlled by the added player’s deviation to Never. This changes the coupling’s event, but not its logical purpose.

### Sure quitting versus geometrically distributed quitting

The repository’s displayed source uses

$$
q^\dagger=1,\qquad q^i=0\quad(i\text{ original}),
$$

at every stage. It proves exact row perfection and termination after every restart for that source.

My source used \(q^\dagger=1/2\). But **this modification works directly in the repository’s padding as well**; it does not require my changed collision payoffs.

Indeed, fix any \(h\in(0,1)\), prescribe \(q^\dagger=h\), and let all original players Continue. Every restarted payoff is

$$
(u,-K),
$$

and survival through \(N\) rows is \((1-h)^N\). For an original player \(i\), under the repository’s collision convention,

$$
Q_i=r_i(\{i\})\le u_i=C_i=V_i.
$$

For the added player,

$$
Q_\dagger=C_\dagger=V_\dagger=-K.
$$

Thus positive probability of every finite live history and geometric every-tail termination are elementary strengthening properties of the existing construction. They do not mark a substantive advance.

### Fully mixed sources

The fully mixed family in my previous answer is a genuine difference in the **source restriction**:

$$
q^\dagger=1-t,\qquad q^i=t.
$$

My collision convention makes both pure-action payoffs of each original player approach \(M\), allowing positive probability on both actions while row errors vanish.

That argument does **not** transfer unchanged to the repository’s padding. There, as \(t\downarrow0\),

$$
Q_i\longrightarrow r_i(\{i\}),
\qquad
C_i\longrightarrow u_i.
$$

When \(r_i(\{i\})<u_i\), the supported Quit action has a nonvanishing loss. The altered collision payoffs remove that particular obstruction.

The precise distinction is therefore:

> My construction extends the hardness reduction to a narrower class of games admitting fully mixed, vanishing-error stationary sources that terminate under every unilateral deviation.

That is an additional property of the reduction’s sources. It neither proves (R) nor produces an approximate equilibrium in the original game. I should have identified it as such, rather than allowing it to make the already-known equivalence sound new.

## 4. The total-debt equality also does not require a new mechanism

I did not find a named total-debt equality in the inspected padding files. But the equality from my answer follows from the repository’s padding too, with a sharper sufficient penalty. Here is the derivation, distinct from a claim that an additional Lean declaration was checked.

For the repository’s padding, set

$$
\ell_i=\min\bigl(\{z_i\}\cup\{r_i(S):S\ne\varnothing\}\bigr),
\qquad w_i=u_i-\ell_i.
$$

For any padded profile \(\widehat\sigma\), let \(\sigma\) be its projection and let \(\alpha\) be the probability of added-player-only absorption.

The same payoff comparison used in the repository’s quantitative projection proof gives

$$
0\le U_i^{\widehat G}(\widehat\sigma)-U_i^G(\sigma)\le w_i\alpha,
\qquad
B_i^G(\sigma)\le B_i^{\widehat G}(\widehat\sigma).
$$

The proof there explicitly compares both prescribed payoffs and arbitrary old-player deviations.

The added player’s debt is exactly \(K\alpha\). Consequently,

$$
d_i^G(\sigma)
\le d_i^{\widehat G}(\widehat\sigma)+w_i\alpha,
$$

and hence

$$
D_G(\sigma)
\le
\sum_{i\text{ original}}d_i^{\widehat G}(\widehat\sigma)
+\alpha\sum_iw_i.
$$

If

$$
K\ge\sum_iw_i,
$$

then

$$
D_G(\sigma)\le D_{\widehat G}(\widehat\sigma).
$$

Conversely, extending an original profile with the added player’s Never strategy preserves all original debts and gives the added player zero debt. Taking infima in both directions yields

$$
\boxed{D_*(\widehat G)=D_*(G)
\quad\text{when }K\ge\sum_iw_i.}
\tag{5}
$$

So even this additional conclusion is a direct consequence of the existing padding argument, not a different way of resolving the original question.

## 5. What the comparison says about (R)

The literature file carefully distinguishes the equivalence theorem from a proof of its two sides. It also contains a positive theorem,

```lean
terminatingTails_and_rowPerfection_imply_subgameEquilibrium_or_stationaryEquilibrium
```

but that theorem assumes `QuittingUnitSoloExit reward` and zero Never payoff. Your question imposes no such own-singleton restriction. In particular, the added player in both padding constructions has own-singleton payoff \(-K\) and Never payoff \(0\), so that positive theorem cannot be applied to these sources.

**The corrected assessment is: my previous answer rediscovered the repository’s existing hardness equivalence and quantitative projection, added a fully mixed-source variant, and did not resolve (R).** There is no substantive difference in the main result to defend. This was a source comparison, not a fresh Lean compilation or axiom audit.


----

I have not closed the universal implication **(R)**. I did obtain a quantitative refinement of the existing normal-source construction: **an actual source-preserving repair in which every player but one has \(O(\varepsilon\log(1/\varepsilon))\) debt, and the remaining player has a square-root error plus one explicit abnormality term.** The square-root exponent is optimal for payoff-preserving repair, even for fully mixed stationary sources.

The abnormality term remains the obstruction; I am not treating this as a proof of (R).

## 1. A source-preserving repair with one exceptional player

Let

$$
s_i:=r^i(\{i\}),\qquad
P_i:=\inf_{\sigma^{-i}}\sup_{\tau^i}
U_i(\tau^i,\sigma^{-i}),
$$

where the opponents’ laws are independent and the deviation is unrestricted. Define

$$
\alpha_i:=(P_i-s_i)_+.
$$

Thus \(\alpha_i=0\) precisely when player \(i\) is punishment-normal.

Choose \(M>0\) such that

$$
|r^i(S)-z^i|\le M
$$

for every player and terminal coalition. Write

$$
d_i(\sigma):=\sup_{\tau^i}U_i(\tau^i,\sigma^{-i})-U_i(\sigma).
$$

**Theorem.** Suppose \(x=(q_t)\) is initially absorbing and every row is playerwise \(\varepsilon\)-perfect against its actual restarted tail, where

$$
0<\varepsilon<2M.
$$

Set

$$
\theta:=\frac{\varepsilon}{2M}.
$$

Define the individual and opponent-deleted survival probabilities

$$
S_i(t):=\prod_{k<t}(1-q_k^i),
\qquad
b_i(t):=\prod_{j\ne i}S_j(t).
$$

Let \(K\) be the first positive integer such that \(S_i(K)\le\theta\) for some player, choose any such player \(i_*\), and put

$$
\beta:=b_{i_*}(K).
$$

There is a finite \(T\ge K\) and an actual behavioral profile \(\sigma\) agreeing with \(x\) before \(T\), such that

$$
\boxed{\|U(\sigma)-U(x)\|_\infty\le\varepsilon,}
\tag{7}
$$

and, for every \(j\ne i_*\),

$$
\boxed{
d_j(\sigma)
\le
2\varepsilon\log\frac{2M}{\varepsilon}+3\varepsilon,
}
\tag{8}
$$

while

$$
\boxed{
d_{i_*}(\sigma)
\le
\beta\alpha_{i_*}
+2\sqrt{2M\varepsilon}
+2\varepsilon\log\frac{2M}{\varepsilon}
+4\varepsilon.
}
\tag{9}
$$

The appended tail is either all Continue or one fixed, independently chosen punishment profile for \(i_*\). No public randomization or correlated choice of tails is used.

In particular, defining

$$
f_M(\varepsilon):=
2\sqrt{2M\varepsilon}
+2\varepsilon\log\frac{2M}{\varepsilon}
+4\varepsilon,
$$

we have

$$
E(\sigma)\le \beta\alpha_{i_*}+f_M(\varepsilon).
\tag{10}
$$

The existing repository compiler already proves approximate existence from all-player punishment normality and (A). Its displayed construction controls a bounded delayed scan by its length. The refinement here charges that scan by **opponent survival**, giving the explicit square-root estimate above. I have not formalized this refinement in Lean.

## 2. Proof

Subtract \(z^i\) from every payoff coordinate, including Never. This changes every prescribed and deviating payoff by the same constant, preserves row perfection and deviation debts, and leaves \(P_i-s_i\) unchanged. We may therefore prove the theorem with \(z=0\) and all rewards bounded in absolute value by \(M\).

### The finite-deviation accounting identity

For player \(i\), let

$$
A_i(t):=
\sum_{\varnothing\ne T\subseteq I\setminus\{i\}}
p_{q_t}^{-i}(T)\,r^i(T)
$$

be the expected current reward when \(i\) Continues. Define

$$
L_i(t):=\sum_{k<t}b_i(k)A_i(k)
$$

and

$$
W_i(t):=L_i(t)+b_i(t)\gamma_t^i(x).
$$

Thus \(W_i(t)\) is the payoff from Continuing through the first \(t\) dates and then resuming the prescribed strategy. This identity uses the actual restarted tail, including at histories that were null under prescribed play.

The Bellman identity gives

$$
W_i(t+1)-W_i(t)
=
b_i(t)\bigl(C_t^i-\gamma_t^i\bigr).
\tag{11}
$$

The row inequalities imply two useful bounds:

$$
C_t^i-\gamma_t^i\le\varepsilon
\tag{12}
$$

and

$$
C_t^i-\gamma_t^i\le 2\varepsilon q_t^i.
\tag{13}
$$

For (13), the claim is immediate when \(q_t^i=0\). Otherwise, the supported-Quit inequality and the upper Continue inequality give

$$
C_t^i-Q_t^i\le2\varepsilon,
$$

and

$$
C_t^i-\gamma_t^i=q_t^i(C_t^i-Q_t^i).
$$

The payoff \(F_i(t)\) from the pure deviation that quits at date \(t\) is

$$
F_i(t)=L_i(t)+b_i(t)Q_t^i.
$$

Consequently,

$$
F_i(t)\le W_i(t)+\varepsilon.
\tag{14}
$$

### The first individual-survival crossing

Initial absorption and finiteness of the player set imply that at least one individual survival probability tends to zero. Hence \(K\) exists.

By its minimality,

$$
S_j(K-1)>\theta
\qquad(j\in I).
$$

Using \(q\le-\log(1-q)\), we obtain

$$
\sum_{t<K-1}q_t^j
\le \log\frac1\theta.
$$

Apply (13) before the last row and (12) on that last row. For every player and every \(t\le K\),

$$
W_j(t)\le U_j(x)+\Lambda,
\qquad
\Lambda:=2\varepsilon\log\frac1\theta+\varepsilon.
\tag{15}
$$

At the crossing,

$$
a_{0,K}\le\theta,
$$

and, for every \(j\ne i_*\),

$$
b_j(K)\le S_{i_*}(K)\le\theta.
\tag{16}
$$

This is why there is only one exceptional player: after \(K\), every other player reaches the remaining tail with probability at most \(\theta\), even when that player deviates.

### The exceptional player’s delayed scan

Abbreviate \(i=i_*\), and set

$$
h:=\varepsilon+\sqrt{2M\varepsilon},
\qquad
c:=\frac{h-\varepsilon}{2M}
=\sqrt{\frac{\varepsilon}{2M}}.
$$

Thus \(0<c<1\).

Starting at \(K\), stop at the first date \(T\) at which either

$$
\gamma_T^i\ge P_i-\alpha_i-h
\tag{17}
$$

or

$$
b_i(T)\le\theta.
\tag{18}
$$

I will show both that this stopping rule terminates and that its accumulated error is bounded independently of its duration.

At a date before \(T\), condition (17) fails. Since

$$
P_i-\alpha_i=\min(P_i,s_i)\le s_i,
$$

the Quit inequality gives

$$
Q_t^i\le\gamma_t^i+\varepsilon
<s_i-(h-\varepsilon).
\tag{19}
$$

Let \(H_i(t)\) be the probability that at least one opponent quits at the current row. The reward bound gives

$$
Q_t^i\ge s_i-2M H_i(t).
$$

Together with (19), this yields

$$
H_i(t)>c.
\tag{20}
$$

If the scan never stopped, the opponent-deleted survival probability would therefore decrease geometrically and eventually satisfy (18), a contradiction. Thus \(T<\infty\).

Moreover,

$$
\sum_{t=K}^{T-1}b_i(t)
\le \frac{b_i(K)}c
=\frac{\beta}{c}.
\tag{21}
$$

Using the unweighted one-row bound (12) in the accounting identity (11), we get, throughout the scan,

$$
W_i(t)
\le U_i(x)+\Lambda+\frac{\varepsilon\beta}{c}
\le U_i(x)+\Lambda+\sqrt{2M\varepsilon}.
\tag{22}
$$

This is the quantitative improvement: **a long scan does not cost its length times the row error**. Its cost is weighted by the declining probability that the deviator’s opponents have not yet stopped.

### Installing an actual tail

If (17) holds, choose an actual independent opponents’ profile whose complete best-response cap for \(i\) is at most

$$
P_i+\varepsilon.
$$

Such a profile exists by the definition of the infimum \(P_i\). Complete it to a full profile and append it at \(T\).

A deviation by \(i\) that continues until \(T\) then has payoff at most

$$
L_i(T)+b_i(T)(P_i+\varepsilon).
$$

By (17), this is at most

$$
W_i(T)+b_i(T)(\alpha_i+h+\varepsilon)
\le
W_i(T)+\beta\alpha_i+h+\varepsilon.
\tag{23}
$$

If instead we stop using (18), append all Continue. Any continuation payoff is bounded above by \(M\), so the corresponding bound is

$$
L_i(T)+b_i(T)M
\le W_i(T)+2M\theta
=W_i(T)+\varepsilon.
\tag{24}
$$

Every pure deviation quitting before \(T\) is bounded by (14) and (22). Every deviation continuing into the appended tail is bounded by (23) or (24). Since an arbitrary stopping law is a mixture of pure finite stopping dates and Never, these bounds cover **all complete behavioral deviations**.

Finally, the original and repaired profiles agree before \(T\), and their prescribed tail payoffs lie in \([-M,M]^I\). Hence

$$
\|U(\sigma)-U(x)\|_\infty
\le2M a_{0,T}
\le2M\theta
=\varepsilon.
\tag{25}
$$

Combining (22)–(25), and substituting \(h\) and \(\Lambda\), proves (9).

For a player \(j\ne i\), deviations quitting before \(K\) are bounded by (14)–(15). Any deviation continuing through \(K\) has payoff at most

$$
L_j(K)+b_j(K)M
\le W_j(K)+2M\theta
\le U_j(x)+\Lambda+\varepsilon.
$$

Subtracting the repaired prescribed payoff, using (25), gives

$$
d_j(\sigma)\le\Lambda+2\varepsilon
=
2\varepsilon\log\frac{2M}{\varepsilon}+3\varepsilon,
$$

which proves (8).

## 3. A quantitative restriction on any counterexample satisfying (A)

The theorem gives more than an all-normal corollary.

Suppose a game has a positive global terminal-exploitability floor:

$$
E(\sigma)\ge g>0
\qquad\text{for every actual behavioral profile }\sigma.
\tag{26}
$$

For any supplied row-perfect absorbing source with

$$
f_M(\varepsilon)<g,
$$

the selected first-crossing player necessarily satisfies

$$
\boxed{
\beta\alpha_{i_*}\ge g-f_M(\varepsilon)>0.
}
\tag{27}
$$

Thus that player must be **abnormal**, and the opponents must retain a quantitatively positive probability of surviving the source prefix:

$$
\beta\ge
\frac{g-f_M(\varepsilon)}{P_{i_*}-s_{i_*}}.
\tag{28}
$$

There is also a direct terminal-coalition consequence. Independence gives

$$
\Pr_x\!\left(
i_*\text{ quits before }K,\ 
\text{every opponent continues through }K
\right)
=
(1-S_{i_*}(K))\beta.
$$

On this event, the terminal coalition is exactly \(\{i_*\}\). Therefore

$$
\boxed{
\Pr_x(\text{terminal coalition}=\{i_*\})
\ge
(1-\theta)\,
\frac{g-f_M(\varepsilon)}{P_{i_*}-s_{i_*}}.
}
\tag{29}
$$

This is a statement about the **actual source’s terminal law**, not a synthesized payoff mixture or an unattached response edge.

It does not eliminate the abnormal player. It identifies precisely where a positive gap must survive this repair: a negative singleton-punishment deficit, multiplied by a positive opponent-survival probability.

## 4. The square-root exponent is unavoidable for payoff-preserving repair

Consider the two-player table

$$
z=(0,0),\qquad
r(\{1\})=r(\{2\})=(0,0),\qquad
r(\{1,2\})=(-1,0).
\tag{30}
$$

Both players are punishment-normal: \(P_1=P_2=s_1=s_2=0\).

For \(0<h<1\), use the fully mixed stationary row

$$
q^1=\frac12,\qquad q^2=h.
$$

Its actual payoff is

$$
U_1=-\frac{h}{1+h},\qquad U_2=0.
$$

For player 1,

$$
Q_1=-h,\qquad
C_1=-\frac{h(1-h)}{1+h}.
$$

Consequently,

$$
U_1-Q_1=C_1-U_1=\frac{h^2}{1+h}.
$$

All four row-perfection inequalities hold at

$$
\varepsilon_h:=\frac{h^2}{1+h}.
\tag{31}
$$

Player 2 is indifferent everywhere.

These sources have positive probability of every finite live history, uniformly geometric joint termination, and termination under every unilateral deviation. Nevertheless,

$$
d_1(x^h)=\frac{h}{1+h}\asymp\sqrt{\varepsilon_h}.
$$

More strongly, player 1 can guarantee zero against **any** opponents’ strategy by Never, and all her rewards are nonpositive. Hence

$$
d_1(\sigma)=-U_1(\sigma)
$$

for every profile \(\sigma\).

Any repair satisfying

$$
\|U(\sigma)-U(x^h)\|_\infty\le\varepsilon_h
$$

must therefore satisfy

$$
E(\sigma)\ge
\frac{h}{1+h}-\varepsilon_h
=
\frac{h(1-h)}{1+h}.
\tag{32}
$$

The right-hand side divided by \(\sqrt{\varepsilon_h}\) tends to one.

Thus no \(o(\sqrt\varepsilon)\) bound is possible for a compiler preserving the supplied payoff to accuracy \(O(\varepsilon)\). This establishes the exponent, not the optimal constant in (9).

**This is not a counterexample to (R): all Continue is an exact equilibrium of (30).** The lower bound concerns preserving the source payoff, which your conclusion does not require.

## 5. A correction about the four-player implication

There is an important positive conclusion already supported by the repository:

$$
\boxed{\text{The four-player instance of (R) follows from the existing results.}}
$$

The argument is short. First translate an arbitrary Never payoff to zero by replacing \(r(S)\) with \(r(S)-z\); this preserves all terminal gains and the source hypothesis.

If the translated four-player game had no terminal approximate equilibria, the repository’s counterexample reduction would supply **same-table punishment normality for every player**. This is an explicit field of the residual produced from the no-uniform-payoff hypothesis, not an additional assumption on the source.

The normal-source compiler then consumes (A) and produces terminal approximate equilibria, a contradiction. The composition is already present in
`FinFourQuantitativeFullSupportHardResidual.exists_uniformEquilibriumPayoff_of_sequentiallyPerfectAbsorbing`.

That is a correction to my earlier assessment, **not new mathematics**. It settles the source-to-equilibrium implication in four players; it does not produce (A) for an arbitrary four-player table.

## What is still missing

For the universally quantified question, the construction above leaves

$$
\beta(P_{i_*}-s_{i_*})_+.
$$

It supplies neither a way to remove that term while retaining small debts for the other players, nor a different equilibrium construction in the cases where the term stays positive.

So this pass yields an explicit actual-profile repair, a matching exponent lower bound, and a quantitative restriction on the remaining abnormal-player case. **It does not yet give the requested all-player proof or a counterexample to (R).**
