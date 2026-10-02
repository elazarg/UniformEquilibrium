# Minimum-return payoff headroom and fixed-law rigidity

Author: `CHATGPT_EXTERNAL`

Status: `PROOF_DRAFT`; the later fixed-law rigidity core passed review after
repairs, while the broader minimum-return claim did not pass verbatim.

Source: supplied as `ephemeral/MIN_RET.md` and moved here without rewriting the
mathematical body.

The decisive point is the meaning of **“routes the marked mass without loss.”** Taken in the iterated sense stated in the question—after performing the first \(n\) updates, the \((n+1)\)-st stored frame is still the literal next frame, with its complete tail and stored live mass—there is a simple well-founded quantity that avoids total debt entirely: the payer’s remaining **payoff headroom**.

This makes the packet inconsistent. Cross-coordinate cap circulation cannot repair the payer’s bounded terminal payoff.

## 1. The causal splice

Let

$$
t_0<t_1<t_2<\cdots
$$

be the retained source ranks, interpreted as their actual dates in the fixed causal chronology. Let \(\sigma^0\) be the incoming literal source profile.

Recursively define \(\sigma^{n+1}\) from \(\sigma^n\) by performing at \(t_n\) the stored pure endpoint update of player \(p\) to the fixed action \(a\).

The recursion is legitimate for every \(n\):

1. all previous updates occur strictly before \(t_n\);
2. each update leaves the complete post-\(t_n\) behavioral tail unchanged;
3. the routing field identifies the next stored frame inside the updated chronology, rather than merely inside the original unmodified realizer;
4. the marked mass is transported without loss.

Consequently, when the \(n\)-th update is performed in \(\sigma^n\), it has exactly the stored tail \(T_n\), the stored pair \(\{j,q\}\), the stored endpoint, and the stored actual gain. This is a genuine sequence of behavioral profiles, not a sequence of horizontal semantic comparisons.

This is the only place where the fixed source stream is used.

## 2. The debt subtraction is an actual payoff increase

Write \(u_i(\tau)\) and \(b_i(\tau)\) for terminal payoff and unrestricted terminal cap, and

$$
d_i(\tau)=b_i(\tau)-u_i(\tau).
$$

For player \(p\), changing only its current Boolean action does not change the set of its two endpoint values. Hence the best-response cap of \(p\) is the same on the pair source and on the selected best endpoint:

$$
b_p(\mathrm{paidTarget}_n)=b_p(\mathrm{pairSource}_n).
$$

Using the exact stored debt identity,

$$
d_p(\mathrm{paidTarget}_n)
 =
d_p(\mathrm{pairSource}_n)-g_n,
\qquad
g_n:=\mathrm{actualGain}_p(n),
$$

we get

$$
\begin{aligned}
u_p(\mathrm{paidTarget}_n)-u_p(\mathrm{pairSource}_n)
&=
\bigl(b_p-d_p(\mathrm{paidTarget}_n)\bigr)
 -
\bigl(b_p-d_p(\mathrm{pairSource}_n)\bigr)\\
&=g_n.
\end{aligned}
$$

Because the update is inserted into the literal chronology with the marked mass already included in \(g_n\), the one-date affine splice identity gives

$$
u_p(\sigma^{n+1})-u_p(\sigma^n)=g_n.
$$

The quantitative packet gives

$$
g_n\ge c,
\qquad
c:=\frac{\lambda D_*}{3}.
$$

Since \(\mu>0\), \(\lambda=\mu^2/8>0\); since \(D_*>0\), therefore

$$
c>0.
$$

Thus, for every \(N\),

$$
u_p(\sigma^N)
=
u_p(\sigma^0)+\sum_{n<N}g_n
\ge
u_p(\sigma^0)+Nc.
\tag{1}
$$

No assertion about total debt has been used.

## 3. Payoff headroom is a renewable natural-valued rank

Since the terminal reward table is finite, player \(p\)’s terminal rewards have a finite maximum. Put

$$
M_p
:=
\max\left(
0,\,
\max_{\varnothing\ne S\subseteq \operatorname{Fin}4} r_p(S)
\right).
$$

Every terminal payoff is an expectation of these terminal rewards, so

$$
u_p(\tau)\le M_p
$$

for every behavioral profile \(\tau\).

Define

$$
\mathcal R(\tau)
:=
\left\lceil
\frac{M_p-u_p(\tau)}{c}
\right\rceil
\in\mathbb N .
$$

From the exact payoff increment,

$$
M_p-u_p(\sigma^{n+1})
\le
M_p-u_p(\sigma^n)-c,
$$

and therefore

$$
\mathcal R(\sigma^{n+1})+1
\le
\mathcal R(\sigma^n).
\tag{2}
$$

So \(\mathcal R\) strictly decreases at every retained update.

This rank is renewable because its child is not a newly chosen minimum point:

* the child profile is the literal one-date update of the parent;
* the complete post-date tail is definitionally the stored tail;
* the law is the law of that updated profile;
* the marked mass is carried by the given no-loss route;
* all later ranks remain the stored later ranks;
* the backward compiler is obtained by composing the one-date splice compiler with the incoming backward compiler.

An infinite strictly descending sequence in \(\mathbb N\) is impossible. Equivalently, choosing

$$
N>
\frac{M_p-u_p(\sigma^0)}{c}
$$

in (1) gives \(u_p(\sigma^N)>M_p\), contradicting the terminal reward bound.

Hence the assumed infinite minimum-return packet cannot exist.

## 4. Conclusion

We have proved the stronger statement

$$
\neg\,
\mathrm{Nonempty}
\bigl(
\mathrm{FinFourOwnerCompressedMinimumReturnForcedPairPacket}
\bigr)
$$

for any packet carrying the iterated literal routing asserted in the question. Neither \(D(T_n)\to D_*\) nor the positive-gap witness is needed after that routing coherence is available.

Therefore the positive-gap/minimum-return arm is impossible. In the incoming residual dichotomy, only the uniform-payoff arm remains, so \(r\) has a uniform-equilibrium payoff.

The argument is not “exact own-debt subtraction without cap control.” The strictly decreasing object is

$$
\left\lceil
\frac{\text{maximum terminal payoff of }p
      -\text{actual terminal payoff of }p}
     {\lambda D_*/3}
\right\rceil ,
$$

and it decreases along literal cumulatively updated behavioral profiles. Arbitrary increases in any player’s cap, including later replenishment of \(p\)’s debt, do not increase \(p\)’s terminal payoff headroom.

There is one formalization boundary that should be stated explicitly: a field of the form

$$
\forall n,\ \exists\text{ a separately realized paid child at rank }n
$$

is not enough. The Lean input must expose the iterated compatibility

$$
\mathrm{frame}_{n+1}
  \bigl(\mathrm{update}_n(\mathrm{current}_n)\bigr)
=
\mathrm{storedFrame}_{n+1},
$$

or an equivalent composable routed-child equality. Without that equality, the hypotheses describe unrelated horizontal frames and the proof would be invalid. Under the literal no-loss source-stream hypothesis in the question, the equality is precisely what supplies the contradiction.

## Followup

The original pointwise packet still does not provide a cumulative chronology. The first genuine completion I can justify is instead a **fixed-law rigidity theorem** for the explicit pair-base stationary source. It closes the missing cap-comparison hypothesis in the pair-base reset route without serializing any absorbing row.

It does **not yet consume the whole minimum-return component**, because one unique-all-Continue branch remains. But this is a proved mathematical seam rather than another conditional dispatch.

## 1. Persistent-base fixed-law rigidity

Let \(I\) be finite, let \(B\subseteq I\) with \(|B|\ge 2\), and let \(\sigma_B\) be a profile at which every player in \(B\) quits surely at the first date.

Write

$$
x=(u,b),\qquad \nu
$$

for its terminal-semantic pair and terminal law. Assume every free player is solved:

$$
b_k=u_k \qquad(k\notin B).
\tag{1}
$$

This is exactly the situation supplied by the Fin4 pair-base localization: the two players outside the prescribed pair are solved against unrestricted behavioral deviations, while all positive debt is localized to the pair.

Now let

$$
y=(u,\beta),\qquad \nu
$$

be any point of the joint semantic/law carrier having the **same prescribed payoff and the same terminal law**.

### Theorem

$$
b_i\le \beta_i\qquad\text{for every }i\in I.
\tag{2}
$$

Consequently,

$$
D(x)\le D(y).
\tag{3}
$$

In particular, if some fixed-law minimization also gives \(D(y)\le D(x)\), then

$$
y=x.
\tag{4}
$$

### Proof for free players

For \(k\notin B\), (1) and nonnegativity of semantic debt give

$$
b_k=u_k\le \beta_k.
\tag{5}
$$

The substantive argument concerns \(i\in B\).

### The erasure payoff

Fix \(i\in B\), and choose

$$
j\in B\setminus\{i\}.
$$

Every terminal coalition in the support of \(\nu\) contains \(B\), because all members of \(B\) quit surely at the first date. Hence erasing \(i\) never produces the empty coalition: \(j\) remains.

Define

$$
E_i(\nu)
 :=
 \sum_{S}\nu(S)\,r_i(S\setminus\{i\}).
\tag{6}
$$

For the explicit persistent-base profile, player \(i\) has only two strategically distinct choices:

* quit at the first date, obtaining \(u_i\);
* continue at that date, after which \(j\) still quits surely, obtaining \(E_i(\nu)\).

All later behavior is irrelevant because \(j\)’s first-date Quit already absorbs. Therefore

$$
b_i=\max\{u_i,E_i(\nu)\}.
\tag{7}
$$

### Every same-law carrier point has cap at least \(E_i(\nu)\)

Take actual realizing profiles \(\tau_m\) converging jointly to \((y,\nu)\). Let player \(i\) deviate in \(\tau_m\) to Never.

On every path whose original terminal coalition contains \(j\), the deviation changes the terminal coalition from \(S\) to \(S\setminus\{i\}\):

* play before the terminal date is unchanged;
* at that date \(j\) still quits;
* therefore removing \(i\)’s Quit does not postpone absorption.

The only paths on which this literal erasure coupling can fail are paths whose terminal coalition omits \(j\). Their probability tends to zero because the limiting law \(\nu\) is supported on coalitions containing \(B\).

If \(M\) bounds absolute rewards, this gives

$$
\operatorname{Cap}_i(\tau_m)
\ge
\sum_{S\ni j}\nu_m(S)\,r_i(S\setminus\{i\})
-
M\,\nu_m\{S:j\notin S\}.
\tag{8}
$$

Passing to the limit yields

$$
\beta_i\ge E_i(\nu).
\tag{9}
$$

Semantic debt nonnegativity also gives

$$
\beta_i\ge u_i.
\tag{10}
$$

Combining (7), (9), and (10),

$$
b_i=\max\{u_i,E_i(\nu)\}\le\beta_i.
$$

This proves (2).

Finally, since the prescribed payoff vectors agree,

$$
D(y)-D(x)
 =
 \sum_i(\beta_i-b_i)\ge0.
$$

If the opposite total-debt inequality also holds, every nonnegative summand \(\beta_i-b_i\) has sum zero, so each vanishes. Thus \(\beta=b\), and hence \(y=x\).

\(\square\)

## 2. Application to the Fin4 pair-base reset source

For every prescribed pair \(B\subseteq\operatorname{Fin}4\), the current construction produces an explicit stationary target whose two complementary coordinates are solved and whose terminal exploitability is localized to \(B\), together with an actual paid first-disagreement row.

The pair-base reset alignment then supplies a fixed-law returned point with:

$$
u_{\rm returned}=u_{\rm target},
\qquad
\nu_{\rm returned}=\nu_{\rm target},
\qquad
D({\rm returned})\le D({\rm target}).
\tag{11}
$$

The abandoned rigidity branch had retained exactly one unproved premise:

$$
b_{\rm target}\le b_{\rm returned}.
$$

The theorem above proves that premise from the persistent-pair law itself; it does not need an added cap hypothesis. The existing conditional rigidity statement can therefore be made unconditional.

Hence

$$
{\rm returned}={\rm target}
\tag{12}
$$

as a complete semantic pair, while the terminal law and actual stationary profile remain the original explicit pair-base objects.

This also closes the semantic/payoff alignment seam retained in the reset construction.

## 3. The strengthened exact exit

After substituting (12), the reset-incidence dynamic exit applies directly at the explicit stationary pair-base target. The result is now:

$$
\boxed{
\begin{array}{l}
\text{an actual positive-absorption exact cap root producing}\\
\text{a strict total-debt child of the explicit target,}
\end{array}}
$$

or

$$
\boxed{
\text{all-Continue is the maximal—and hence unique—exact root at the
explicit target cap.}}
$$

There is no intervening compact carrier point and no unproved semantic seam. The positive-root branch is one literal cap prefix attached to the actual paid stationary source, rather than a horizontal comparison between separately realized minimum-return frames. The reset-incidence machinery supplies precisely this positive-root/all-Continue alternative.

This is the corrected route:

$$
\text{terminal gap}
\longrightarrow
\text{explicit pair-base paid profile}
\longrightarrow
\text{fixed-law rigidity}
\longrightarrow
\begin{cases}
\text{actual strict-debt cap child},\\
\text{explicit unique-all-Continue stall}.
\end{cases}
$$

## 4. Why this is not yet the full requested conclusion

Two obstructions remain.

First, the positive-root child has a different terminal law. The rigidity theorem is tied to the persistent-pair law, so it does not automatically regenerate after that prefix. Its decrease is still real-valued rather than a renewable natural-valued rank.

Second, the explicit unique-all-Continue stall has not been contradicted by positive global minimum debt. Purely local data cannot eliminate it: the repository contains a same-table local configuration with a pure paid pair and a unique all-Continue exact cap root; that regression escapes only because its global minimum debt is zero and it has an all-Never equilibrium.

Thus the remaining proposition has been reduced to a substantially sharper form:

> **Explicit pair-base stall problem.**
> In a Fin4 terminal-gap game with \(D_*>0\), can the explicit pair-base stationary target—whose free coordinates are solved, whose debt is supported on the sure-Quit pair, and which carries an actual paid first-disagreement row—have all-Continue as its unique exact cap root?

A negative answer to that proposition produces an actual strict cap child. A renewable treatment of those children, or a direct contradiction in the stall arm, completes the original terminal component.
