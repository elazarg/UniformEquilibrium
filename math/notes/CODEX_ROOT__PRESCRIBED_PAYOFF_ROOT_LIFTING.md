# Prescribed-payoff roots under a unique all-Continue cap

Status: ordinary mathematics independently reviewed. This is a nonterminal
Research reduction, not a solution of the paired unique-cap question and not
an export packet.

Source: `../PAID_CUP_1.md`. Independent checks and strengthening are in
`feedback/PAID_CUP_1__BY_GATE_FALSIFIER.md`,
`feedback/PAID_CUP_1__BY_GATE_SOURCE.md`, and
`feedback/PAID_CUP_1__BY_GATE_STRENGTHENER.md`.

## General root classification

Let \(p=(u,b)\) be a terminal semantic pair with nonnegative debts

\[
d_i=b_i-u_i\ge 0.
\]

For a product root \(x\), write \(s_i(x)\) for the probability that all
opponents of \(i\) Continue and

\[
\Delta_i(v,x)=Q_i(x)-C_i(v,x).
\]

Then

\[
\Delta_i(b,x)=\Delta_i(u,x)-s_i(x)d_i. \tag{1}
\]

Hence, if \(x\) is exact Nash against \(u\) and every player active on Quit
has zero debt, then \(x\) is also exact Nash against \(b\). In particular, if
all Continue is the unique exact root against \(b\), every non-all-Continue
exact root against \(u\) activates a positive-debt player.

For an exact root against \(u\), the checked prefix-debt identity gives

\[
d_i(T_xp)=\bigl(s_i(x)d_i(p)-\pi_i(u,x)\bigr)_+,
\qquad \pi_i(u,x)\ge0. \tag{2}
\]

Therefore every exact root against \(u\) has one of the following outcomes:

1. it is all Continue;
2. \(D(T_xp)<D(p)\); or
3. debt is preserved and there is a unique debtor \(i\), every opponent of
   \(i\) is pure Continue, \(x_i(Q)>0\), the exercise premium is zero, and
   \(u_i=r_i(\{i\})\).

The third arm is thus an exact singleton-tight, zero-premium solo-debtor gate.
It is stronger than merely saying that the root is supported on the unique
debtor. A solo root with positive exercise premium lies in the strict-descent
arm instead.

Because the finite root game against \(u\) has an exact mixed Nash profile,
this yields the correspondence alternative

\[
\begin{aligned}
&\text{an exact prescribed-payoff root with strict debt descent,}\quad\text{or}\\
&\text{an exact singleton-tight solo-debtor equality gate,}\quad\text{or}\\
&\text{all Continue is unique against both }u\text{ and }b.
\end{aligned} \tag{3}
\]

For an actual semantic pair, the strict descent is realized by literal root
prefixing. It need not retain a paid row, reset incidence, fixed law, or a
renewable source packet.

## Fin4 double-port consequence

For the singleton source, the positive-debt support is exactly the singleton
owner. For its literal owner repair, the owner debt is zero and at least one
free player has positive debt. Applying (3) to both sides of the checked
double-unique-cap arm gives:

\[
\begin{aligned}
&\text{strict actual prescribed-payoff debt descent on one side,}\quad\text{or}\\
&\text{a source singleton-owner equality gate,}\quad\text{or}\\
&\text{a repaired unique-debtor singleton equality gate,}\quad\text{or}\\
&\text{all Continue is unique against both prescribed-payoff vectors.}
\end{aligned} \tag{4}
\]

This refines the final arm of the cap-root theorem; it does not replace the
cap-root regeneration theorem, since the two root games have different
continuation vectors and different descendant data.

## Cross-law account

Let \(o\) be the source singleton owner, let \(F\) be the three free players,
and let \(c\) be their one-stage all-Continue probability. Let \(\nu_R\) be
the repaired stationary terminal law on nonempty \(Q\subseteq F\). The
literal stationary definitions imply

\[
\nu_S(\{o\})=c,
\qquad
\nu_S(Q\cup\{o\})=(1-c)\nu_R(Q). \tag{5}
\]

This law transport is not currently exposed as a named checked theorem.
Using \(u_o^R=b_o^S\), the source owner debt is

\[
d_o^S=
c\bigl(u_o^R-r_o(\{o\})\bigr)
+\sum_{\varnothing\ne Q\subseteq F}
 \nu_S(Q\cup\{o\})
 \bigl(r_o(Q)-r_o(Q\cup\{o\})\bigr). \tag{6}
\]

If \(d_o^S\ge\gamma>0\), then either

\[
c\bigl(u_o^R-r_o(\{o\})\bigr)\ge\gamma/2, \tag{7}
\]

or some nonempty \(Q\subseteq F\) satisfies

\[
\nu_S(Q\cup\{o\})
\bigl(r_o(Q)-r_o(Q\cup\{o\})\bigr)\ge\gamma/14. \tag{8}
\]

There are seven nonempty free coalitions, giving the factor \(1/14\).
Negative toggle terms do not invalidate the pigeonhole step.

## Remaining consumer

Neither strict real debt descent nor (7)--(8) is a renewable rank or an
admissible chronological edge. The outstanding task is to consume one of:

- a singleton-tight solo-debtor equality gate;
- the weighted leave-toggle in (8); or
- uniqueness of all Continue at both prescribed payoff vectors,

while preserving enough source data to produce a terminal conclusion,
positive admissible near-return, or well-founded regeneration.

## Relevant checked ingredients

- `quittingTerminalSemanticDebt_prefix_eq_blockAct` and
  `quittingTerminalSemanticDebt_prefix_le` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `quittingTerminalSemantic_minimum_stratum_alternative` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean`;
- `FinFourSingletonBaseSameLawResetProducer.positiveDebtSupport_eq` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/SingletonBaseSameLawResetProducer.lean`;
- `sourceMaximalRegeneration_or_repairedMaximalRegeneration_or_doubleUnique`
  in `Research/Quitting/FinFourPaidCapMaximalDoubleRegeneration.lean`.
