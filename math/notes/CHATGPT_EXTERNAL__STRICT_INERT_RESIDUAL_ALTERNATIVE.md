# Strict inert residual alternative

Author: `CHATGPT_EXTERNAL`

Status: `MATH_REVIEWED`; useful checked-source reduction, not an equivalence or consumer.

Source: supplied as `ephemeral/INERT_EQUIV.md` and moved here without rewriting
the mathematical body.

I continued through the newest checked source, including the material that landed on `main` after the original question. The strict normalized-inert point is **not yet eliminated or realized**. The strongest honest conclusion is a sharper equivalent obstruction.

## Strongest checked reduction

The original strict object can now be advanced past its normalized-passport presentation. The current checked chain constructs two literal stationary profiles on the same reward table:

$$
\sigma^{Q}
\quad\text{and}\quad
\sigma^{C},
$$

where:

* in \(\sigma^{Q}\), the singleton owner \(o\) quits surely;
* every free player is an unrestricted best responder, hence has zero terminal-semantic debt;
* the terminal witness forces \(o\)'s debt to be positive;
* \(\sigma^{C}\) replaces \(o\)'s strategy by Always Continue;
* at \(\sigma^{C}\), \(o\)'s debt is exactly zero;
* some distinct free player then has positive debt;
* both profiles retain actual source provenance and positive opponent incidence.

Applying the maximal-root paid/reset theorem separately to these two profiles yields:

$$
\begin{aligned}
&\text{source-side actual paid/reset regeneration}\\
{}\lor{}&
\text{repaired-side actual paid/reset regeneration}\\
{}\lor{}&
\bigl(
\operatorname{Root}(b^{Q})=\{\mathbf C\}
\ \land\
\operatorname{Root}(b^{C})=\{\mathbf C\}
\bigr).
\end{aligned}
$$

Here the first two alternatives are genuine regenerated actual sources, not compact carrier points. This is the theorem
`sourceMaximalRegeneration_or_repairedMaximalRegeneration_or_doubleUnique`
in `FinFourPaidCapMaximalDoubleRegeneration.lean`. The file states explicitly that the remaining obstruction is two selector-independent unique all-Continue caps.

Thus the strict inert SCC has been reduced to:

```text
actual source regeneration
or actual repaired-source regeneration
or DoubleUniqueAllContinueCap
```

The arbitrary selected inert ports disappear from the terminal obstruction: cap uniqueness itself freezes every selected cap-prefix semantic pair and makes every selected root literally all Continue.

## What the double-unique arm says

Let

$$
b^Q_i=\operatorname{BR}_i(\sigma^Q_{-i}),
\qquad
b^C_i=\operatorname{BR}_i(\sigma^C_{-i}).
$$

The final arm asserts that the two one-shot quitting games with continuations \(b^Q\) and \(b^C\) each have exactly one exact root, namely all Continue.

This is much stronger than the original assertion at the abstract minimizer. Both caps now come from actual profiles, and those profiles differ only in the owner’s complete stopping law. Moreover,

$$
b^Q_o=b^C_o:
$$

the repair replaces the owner by a best response, so the repaired owner’s payoff and cap equal the original owner cap. The positive debt has therefore been transferred from \(o\) to a different player without changing the owner-cap coordinate.

## Why the apparent contradiction still does not follow

A natural interpolation is to vary the owner’s stationary quit probability \(q\in[0,1]\) and solve the induced Nash problem for the other three players.

At \(q=1\), the free players are exact and the terminal witness makes Never strictly preferable for the owner.

At \(q=0\), after the owner repair, the owner is exact and the witness forces some free player to have positive debt. One would like to continue the free-player Nash component and use an intermediate-value argument to obtain a point where the owner is also indifferent. That would be a stationary exact Nash profile, hence a zero-debt carrier point contradicting \(D_*>0\).

The obstruction is the all-Continue boundary. Along a sequence \(q_n\downarrow0\), the free players’ total hazard may also vanish at order \(q_n\). Then:

* each finite-\(q_n\) profile still absorbs almost surely;
* the owner’s eventual stopping payoff need not approach its payoff at literal \(q=0\);
* the owner-sign function need not extend continuously to the endpoint;
* the free-player Nash component can escape through a normalized vanishing-hazard ray rather than cross owner indifference.

This is precisely the strict normalized-inert phenomenon in a more concrete form. The stationary continuation argument succeeds provided the free-player absorption is bounded away from zero, but the complementary collapse arm reproduces the current maximal-ray obstruction rather than contradicting it.

## Saturation does not supply a renewable rank

The off-minimum point does have a literal source-faithful actualizer. Its normalized marked-mass density satisfies the exact transition

$$
\rho_{\mathrm{next}}=\frac12\rho_{\mathrm{current}}.
$$

For every fixed finite number \(N\) of saturated transitions, the input resolution can be chosen large enough to retain a prescribed positive absolute marked-mass floor through all \(N\) steps. But this cannot be made into an infinite renewable process from the present hypotheses.

If \(P\) is the incoming point, \(Q\) its saturated successor, and \(\lambda\) the desired retained mass floor, continuity makes

$$
2\lambda D(P)\le M(P)D(Q)
$$

necessary. The packet only gives \(\lambda\le M(P)\). It gives no uniform factor-two slack, and even factor-two mass slack is insufficient when \(D(Q)<D(P)\). Thus repeated density halving is neither a natural-number rank nor a uniformly resolved infinite source transition. The repository’s own audit identifies the remaining obligation as converting the executable aggregate cap charge into a prescribed-payoff return or renewable finite rank.

## Exact remaining theorem

The strongest nonredundant capstone is now the following.

> **Double-unique-cap elimination theorem.**
> Let \(\sigma^Q\) be the literal singleton-base stationary source and \(\sigma^C\) its literal owner repair supplied by a `FinFourQuantitativeFullSupportHardResidual`. Suppose:
>
> 1. all free-player debts at \(\sigma^Q\) vanish and the owner debt is positive;
> 2. the owner debt at \(\sigma^C\) vanishes and some free-player debt is positive;
> 3. the two owner caps agree;
> 4. both continuation vectors have all Continue as their unique exact product root.
>
> Then either:
>
> $$
> \inf_\sigma D(\sigma)=0,
> $$
>
> or the two-profile owner-repair seam produces a positive punishment-floor-admissible charged near-return.

Proving its first conclusion would eliminate the strict inert point. Proving its second would invoke the existing cumulative-charge compiler and yield a uniform-equilibrium payoff.

The missing lemma cannot be only a connectedness theorem for stationary Nash correspondences. It must also control the vanishing-absorption end of the component. An adequate formulation is:

$$
\text{free-Nash continuation}
\quad\Longrightarrow\quad
\begin{cases}
\text{nonvanishing free absorption and owner-sign crossing},\\
\text{or a source-attached admissible lift of the normalized escape ray}.
\end{cases}
$$

The first branch gives an exact stationary Nash profile. The second branch must construct exact Nash–Bellman predecessor/endpoint seams; an unsigned root-defect toll or a reached Quit-versus-Continue comparison is insufficient. The existing cap-square module expressly stops before such a chronological compiler.

## Verdict

None of the four requested terminal outputs is currently proved:

* no contradiction with \(D_*>0\);
* no terminal approximate Nash family or admissible near-return;
* no renewable well-founded rank;
* no explicit positive-gap four-player table.

The genuine advance is that the abstract strict normalized-inert object is no longer the sharp frontier. Its remaining content is the **actual two-profile double-unique-cap obstruction** above. Any further binding-cardinality or root-geometry subdivision below that object would again be a nonanswer unless it controls the vanishing-absorption escape and constructs the missing exact admissible seam.
