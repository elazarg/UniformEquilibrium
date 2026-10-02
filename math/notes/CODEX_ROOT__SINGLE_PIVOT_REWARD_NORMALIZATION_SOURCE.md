# Single-pivot reward normalization: preserved proof submission

Owner of this intake record: CODEX_ROOT.

Status: ordinary mathematics with two complete independent PASS reviews and
both reviewers' final-assembly confirmations. The final packet is frozen at
[SINGLE_PIVOT_ZERO_NEVER_NORMALIZATION_AND_FINITE_MENU_SOURCE.md](../exports/SINGLE_PIVOT_ZERO_NEVER_NORMALIZATION_AND_FINITE_MENU_SOURCE.md),
SHA-256 `b38ad18986ec59aac0cc22afc8006eead7b35ae7f58fc425e12b33a58cf699c5`.
Its entire exact-statement-through-end mathematical body has SHA-256
`7b195d5e246b0efba9aadcf1989d82d44121f5247c6e886d34b0995d2d50b6bf`.
No new Lean implementation or conjecture closure is asserted here.

## Question and claimed consequence

Can every punishment-normal four-player quitting game with a positive
unrestricted terminal exploitability gap be transformed, with Never payoff
still zero, into another positive-gap game whose own-singleton vector is
(1, 0, 0, 0), so that every finite-menu exact Nash profile has unrestricted
debt in only one fixed player?

The submitted argument claims a quantitative gap transfer, an exact affine
punishment-value identity, an affine correspondence of UE payoff sets, and
an actual finite-menu source with one explicit remaining late-deviation
scalar. The remaining scalar is not shown to tend to zero. This would be a
counterexample-normal-form reduction, not a solution of the conjecture.

## Review boundaries

The first full mathematical review was completed by CODEX_SKEPTIC; the
second full proof, source-overlap, and hard-residual-transport check was
completed independently by CODEX_HILBERT. Review
records are `feedback/TRANSFORM__BY_CODEX_SKEPTIC.md` and
`feedback/TRANSFORM__BY_CODEX_HILBERT.md` when available. The delicate issue
is that translating terminal rewards while fixing Never at zero is not
ordinary affine invariance. The tail-graft argument must cover all responses,
including Never, signed singleton rewards, and vanishing survival events.

The source is preserved below without mathematical edits from
`gpt/TRANSFORM.md`, SHA-256:

    2b8b33dee7dd901e63d93300ab0d06be57700ac652e9f10ac7b3a62a4b8e889a  gpt/TRANSFORM.md


No preexisting export was modified. Both reviewers found no mathematical
repair needed and distinguished the new signed zero-Never lift from existing
affine transport that also translates the Never payoff. The assembled packet
was independently reread and confirmed by both, then received only the agreed
administrative preamble changes. ROOT checked its unchanged mathematical
body, exact export-copy equality, final hash, and documentation links.

Next mathematical question: select actual canonical finite-menu approximate
equilibria with small pivot late-deviation excess. The standalone priority
question is `questions/FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md`; it does
not require exact finite Nash, source ancestry, or nesting across accuracies.

---

## Submitted proof (preserved)

The normalization has to preserve **unrestricted deviations and punishment floors**, not just the singleton comparison matrix. I can now do both.

The resulting statement is stronger than the earlier completion lemma: **any positive-gap hard-residual table can be transformed explicitly into a positive-gap table whose own singleton rewards are \((1,0,0,0)\). In that table, every exact finite-menu equilibrium has unrestricted debt in only one fixed coordinate.**

This is a reduction with a quantitative terminal consumer. **It does not yet produce arbitrarily charged packets or prove the finite-menu absorption theorem.**

## 1. A canonical one-player deadline defect

Write

$$
g_i=r_i(\{i\}),\qquad
M=\max_{i,S\ne\varnothing}|r_i(S)|.
$$

Use the hard residual’s punishment normality:

$$
P_i\le g_i\qquad(i\in I).
\tag{1}
$$

This is precisely the meaning of `IsQuittingNormalPlayer` in the residual’s `all_punishmentNormal` field.

Suppose

$$
E_r(\sigma)\ge\gamma>0
\qquad\text{for every behavioral profile }\sigma.
\tag{2}
$$

Some \(g_k\) must be positive; otherwise all-Never is exact Nash. Fix such a player, put \(g=g_k>0\), and define

$$
a_k=0,\qquad a_j=g_j\quad(j\ne k),
$$

$$
\boxed{\quad
\widehat r_i(S)=\frac{r_i(S)-a_i}{g}.
\quad}
\tag{3}
$$

The infinite all-Continue payoff remains zero.

Then

$$
\widehat r_k(\{k\})=1,\qquad
\widehat r_j(\{j\})=0\quad(j\ne k).
\tag{4}
$$

**Theorem.** This transformation satisfies

$$
\boxed{
E_{\widehat r}(\sigma)\ge
\frac{\gamma^2}{16M^2}
\qquad\text{for every behavioral profile }\sigma.
}
\tag{5}
$$

Moreover, the punishment vector transforms exactly:

$$
\boxed{\widehat P=\frac{P-a}{g}.}
\tag{6}
$$

Thus the conclusion is not merely that some restricted strategy class remains obstructed. Equation (5) is an **all-behavior terminal gap**.

The important issue in (3) is that some \(a_j\) may be negative. Arbitrary terminal-payoff translation is not strategically harmless when the Never payoff is kept at zero. The proof below handles that issue by changing one actual tail.

## 2. The terminal consumer behind the reduction

For a profile \(\sigma\), let \(T_i\in\mathbb N\cup\{\infty\}\) be player \(i\)’s independently sampled stopping time. Define

$$
R(T)=\Pr(T_i\ge T\text{ for every }i),
\qquad
D_i(T)=\Pr(T_j\ge T\text{ for every }j\ne i),
$$

and

$$
R_\infty=\Pr(T_i=\infty\text{ for every }i),\qquad
D_i^\infty=\Pr(T_j=\infty\text{ for every }j\ne i).
$$

Here is the quantitative lifting statement.

**Lifting lemma.** For every profile \(\sigma\) in \(\widehat r\), every
\(\rho>R_\infty\), and every \(\zeta>0\), there is an actual profile \(\tau\) in \(r\), agreeing with \(\sigma\) before some finite date \(T\), such that

$$
\boxed{
E_r(\tau)
\le
gE_{\widehat r}(\sigma)
+2M\bigl(\rho+\sqrt\rho\bigr)+\zeta,
}
\tag{7}
$$

and

$$
\boxed{
\left\|U^r(\tau)-\bigl(a+gU^{\widehat r}(\sigma)\bigr)\right\|_\infty
\le 2M\rho.
}
\tag{8}
$$

Only one punishment continuation is used.

### Selecting the exceptional player

Choose \(T\) sufficiently large that \(R(T)<\rho\) and every

$$
\ell_i(T):=D_i(T)-D_i^\infty
$$

is sufficiently small.

For distinct \(i,j\),

$$
D_i(T)D_j(T)
=
R(T)\prod_{h\ne i,j}\Pr(T_h\ge T)
\le R(T)<\rho.
\tag{9}
$$

Hence at most one player has \(D_i(T)>\sqrt\rho\).

If such a player \(i_*\) exists, switch at \(T\) to an actual punishment against \(i_*\) with cap at most

$$
P_{i_*}+\eta.
$$

Otherwise use any continuation, for example all-Never. The target and the continuation are selected before play; no identification of a deviator is required.

### Prescribed-payoff comparison

The quantity

$$
a_i+gU_i^{\widehat r}(\sigma)
$$

is the payoff obtained by using the original terminal rewards \(r_i(S)\), but assigning payoff \(a_i\) to infinite all-Continue.

Before \(T\), that payoff and \(U_i^r(\tau)\) agree pathwise. On joint survival to \(T\), both conditional payoffs lie in \([-M,M]\), since \(|a_i|\le M\). Therefore

$$
\left|U_i^r(\tau)-a_i-gU_i^{\widehat r}(\sigma)\right|
\le2MR(T)<2M\rho,
$$

which proves (8).

### Deviations by a nonexceptional player

Let \(\widehat Z_i(T)\) be player \(i\)’s expected \(\widehat r\)-reward from opponents quitting before \(T\), when \(i\) Continues until \(T\). Let \(\widehat W_i\) be its payoff from Never against the original opponents.

Since

$$
\widehat M:=\max_{i,S}|\widehat r_i(S)|\le\frac{2M}{g},
$$

we have

$$
|\widehat W_i-\widehat Z_i(T)|
\le\widehat M\,\ell_i(T).
\tag{10}
$$

A deviation quitting before \(T\) has original payoff exactly \(a_i\) plus \(g\) times its \(\widehat r\)-payoff. Its value is therefore at most

$$
a_i+gB_i^{\widehat r}(\sigma).
$$

A deviation waiting until \(T\) has value at most

$$
\begin{aligned}
g\widehat Z_i(T)+a_i(1-D_i(T))+MD_i(T)
&=a_i+g\widehat Z_i(T)+(M-a_i)D_i(T)\\
&\le a_i+gB_i^{\widehat r}(\sigma)
   +2M\ell_i(T)+2MD_i(T).
\end{aligned}
\tag{11}
$$

For a nonexceptional player \(D_i(T)\le\sqrt\rho\). Combining (11) with (8),

$$
d_i^r(\tau)
\le
gE_{\widehat r}(\sigma)
+2M\rho+2M\sqrt\rho+2M\ell_i(T).
\tag{12}
$$

### The exceptional player

For any quitting table, the payoff from quitting at increasingly late deterministic dates satisfies

$$
\lim_{t\to\infty}U_i(t,\sigma_{-i})
=
W_i+g_iD_i^\infty.
\tag{13}
$$

Applying this to \(\widehat r\),

$$
B_i^{\widehat r}(\sigma)
\ge
\widehat W_i+\widehat g_iD_i^\infty,
\tag{14}
$$

where \(\widehat g_k=1\) and \(\widehat g_j=0\) for \(j\ne k\).

A deviation by the exceptional player that waits until \(T\) receives at most

$$
\begin{aligned}
g\widehat Z_i(T)+a_i(1-D_i(T))
      +(P_i+\eta)D_i(T)
&\le
a_i+g\widehat Z_i(T)
      +(g_i-a_i)D_i(T)+\eta\\
&=
a_i+g\bigl(\widehat Z_i(T)+\widehat g_iD_i(T)\bigr)+\eta.
\end{aligned}
\tag{15}
$$

The inequality is exactly where punishment normality \(P_i\le g_i\) is used.

Equations (10) and (14) bound (15) by

$$
a_i+gB_i^{\widehat r}(\sigma)+3M\ell_i(T)+\eta.
$$

Thus

$$
d_i^r(\tau)
\le
gE_{\widehat r}(\sigma)+2M\rho+3M\ell_i(T)+\eta.
\tag{16}
$$

Taking \(T\) sufficiently large and \(\eta\) sufficiently small proves (7). All unrestricted deviations are covered: before absorption, a unilateral behavioral strategy induces a stopping-time law, and its payoff is a mixture of the deterministic-date and Never payoffs just bounded. ∎

### Deriving the positive gap

In \(\widehat r\), player \(k\)’s own singleton reward is \(1\). Moving only its prescribed Never mass to an increasingly late finite date gives a limiting improvement \(R_\infty\). Consequently

$$
R_\infty\le E_{\widehat r}(\sigma).
\tag{17}
$$

Put \(e=E_{\widehat r}(\sigma)\). From the lifting lemma, by choosing \(\rho>e\) arbitrarily close to \(e\) and then taking \(\zeta\) arbitrarily small,

$$
\inf_\tau E_r(\tau)
\le
(g+2M)e+2M\sqrt e.
\tag{18}
$$

Since \(g\le M\) and \(\gamma\le2M\), the inequality

$$
e<\frac{\gamma^2}{16M^2}
$$

would imply

$$
\begin{aligned}
(g+2M)e+2M\sqrt e
&<
\frac{3\gamma^2}{16M}+\frac{\gamma}{2}\\
&\le \frac{7\gamma}{8}
<\gamma,
\end{aligned}
$$

contradicting (2). This proves (5).

The bound can be sharpened by solving the quadratic in (18); the constant \(16\) is simply a convenient explicit choice.

## 3. Why the punishment floor also transforms exactly

This needs a separate argument. It does **not** follow from prescribed-payoff translation.

For a fixed player, define

$$
A(\sigma_{-i})
=
\sup_{t<\infty}U_i(t,\sigma_{-i}),
\qquad
L_i=\inf_{\sigma_{-i}}A(\sigma_{-i}).
$$

Here Never is excluded from the responding player’s action set, but arbitrarily late finite dates are included.

The useful identity is

$$
\boxed{L_i=\min(P_i,g_i).}
\tag{19}
$$

To prove it, first note that \(L_i\le g_i\), by taking all opponents Never, and \(L_i\le P_i\).

Suppose \(L_i<g_i\), and choose opponents with

$$
A< x<g_i.
$$

Let \(D\) be their joint Never probability and \(W\) player \(i\)’s Never payoff. Equation (13) gives

$$
W+g_iD\le A.
$$

Also \(D<1\), since otherwise \(A=g_i\). Hence

$$
\frac{W}{1-D}
\le
\frac{A-g_iD}{1-D}
\le A.
\tag{20}
$$

Now truncate those opponents to a sufficiently long finite block and repeat that block forever. If \(D_T,W_T\) are the block’s opponent-survival probability and Never reward, the resulting unrestricted cap is at most

$$
\max\left\{
A,\frac{W_T}{1-D_T}
\right\}.
\tag{21}
$$

Indeed, quitting in a later block yields a convex combination of a within-block quitting payoff and \(W_T/(1-D_T)\). As \(T\to\infty\), the second term converges to the quantity in (20). Thus \(P_i\le x\), and letting \(x\downarrow L_i\) gives \(P_i=L_i\).

If \(L_i=g_i\), then \(P_i\ge g_i\). These two cases prove (19).

Under normality, therefore,

$$
L_i=P_i.
\tag{22}
$$

Every finite pure stopping payoff transforms under (3) as

$$
U_i^{\widehat r}(t,\sigma_{-i})
=
\frac{U_i^r(t,\sigma_{-i})-a_i}{g}.
\tag{23}
$$

All transformed own singleton rewards are nonnegative, so (13) shows that the supremum over finite stopping dates already dominates Never in \(\widehat r\). Taking infima in (23) and using (22),

$$
\widehat P_i=\frac{L_i-a_i}{g}
=\frac{P_i-a_i}{g}.
$$

This proves (6).

In particular,

$$
\widehat P_j\le0\quad(j\ne k),\qquad
\widehat P_k\le1.
$$

## 4. Exact Bellman matching survives the normalization

For every root \(q\) and continuation \(v\),

$$
\boxed{
F_{\widehat r}\!\left(q,\frac{v-a}{g}\right)
=
\frac{F_r(q,v)-a}{g}.
}
\tag{24}
$$

Every pure root-action payoff undergoes the same coordinatewise affine transformation.

Consequently, a supplied forward packet transforms by

$$
\widehat v_t=\frac{v_t-a}{g},\qquad \widehat q_t=q_t.
$$

It has literal successor matching

$$
\widehat v_{t+1}=F_{\widehat r}(\widehat q_t,\widehat v_t),
$$

support tolerance \(\delta/g\), and floor

$$
\widehat v_{t,i}\ge\widehat P_i-\delta/g.
$$

Its carrier is the one fixed box

$$
\widehat K=(K-a)/g,
$$

and its absorption charge is unchanged.

Thus there is no row rematching, length-dependent error, or change of chronological orientation in this correspondence.

The same proofs give an equivalence of uniform-equilibrium payoff sets:

$$
\boxed{
\operatorname{UE}(r)
=
a+g\,\operatorname{UE}(\widehat r).
}
\tag{25}
$$

For the reverse direction, the lifting lemma preserves the limiting payoff by (8). For the forward direction, writing \(R_\infty\) for the original profile’s Never probability,

$$
E_{\widehat r}(\sigma)
\le
\frac{E_r(\sigma)+MR_\infty}{g}
\le
\left(\frac1g+\frac{M}{g^2}\right)E_r(\sigma).
$$

Then use the terminal-to-uniform passage in the question.

Importantly, (24) does not turn the normalization itself into a temporal move. Nor does it send an arbitrary chosen minimum-debt point to a minimum-debt point.

## 5. The resulting finite-menu source has exactly one possible debt

Now work entirely in the canonical table \(\widehat r\), with own singleton vector \(e_k\).

Fix any deadline \(N\). The actual finite stopping-time game has an exact mixed Nash equilibrium \(p\), by finite-game Nash existence. ([PNAS][1])

Let

$$
W_i(p)=U_i(\mathrm{Never},p_{-i}),
\qquad
D_i(p)=\prod_{j\ne i}p_j(\mathrm{Never}),
$$

and let \(B_i^N(p)\) be the cap on the displayed menu.

Because opponents have no finite stopping dates at or after \(N\), **every** deterministic quitting date \(t\ge N\) has payoff

$$
W_i(p)+\widehat g_iD_i(p).
\tag{26}
$$

Therefore, for an arbitrary product law on that menu,

$$
B_i^\infty(p)
=
\max\{B_i^N(p),\,W_i(p)+\widehat g_iD_i(p)\}.
\tag{27}
$$

For each nonpivot player, \(\widehat g_j=0\), and Never is already on the menu. Hence

$$
\boxed{B_j^\infty(p)=B_j^N(p)\qquad(j\ne k).}
\tag{28}
$$

For the pivot,

$$
\boxed{
B_k^\infty(p)
=
\max\{B_k^N(p),\,W_k(p)+D_k(p)\}.
}
\tag{29}
$$

For the exact finite-menu equilibrium selected above, this gives

$$
\boxed{
d_j^\infty(p)=0\quad(j\ne k),\qquad
d_k^\infty(p)=
\bigl[W_k(p)+D_k(p)-U_k(p)\bigr]_+.
}
\tag{30}
$$

This is an actual-source statement at **every deadline**. It does not require stationarity, periodicity, a supplied tail, or an assumed unrestricted equilibrium.

If the pivot assigns positive probability to Never, finite-menu indifference further gives

$$
U_k(p)=W_k(p),
\qquad d_k^\infty(p)=D_k(p).
\tag{31}
$$

If it assigns zero probability to Never, only (30) is justified. In particular, prescribed absorption with probability one does not by itself remove the pivot’s late deviation.

For a finite-menu \(e\)-Nash law, the exact general formula is

$$
\boxed{
E_\infty(p)
=
\max\left\{
E_N(p),\,
W_k(p)+D_k(p)-U_k(p)
\right\}.
}
\tag{32}
$$

## What remains unresolved

The remaining finite-menu obstruction can now be placed in **one fixed player and one explicitly displayed scalar**

$$
W_k(p)+D_k(p)-U_k(p).
$$

The other three players already satisfy the unrestricted terminal comparison, to the displayed finite-menu error.

However, I have not shown that this scalar can be made arbitrarily small while selecting actual finite-menu approximate equilibria. Under a positive gap, (30) only forces

$$
D_k(p)\ge \frac{\gamma^2}{16M^2}
$$

for every exact finite-menu equilibrium; that is a constraint, not a contradiction.

Likewise, the affine packet correspondence preserves the bounded-capacity obstruction rather than consuming it. **No renewable moving-tail construction, arbitrarily charged packet, or exclusion of the inert chamber has been established here.** The progress is the quantitative all-behavior reduction and the unconditional one-coordinate finite-menu source; neither should be reported as the requested conjecture-level breakthrough.

[1]: https://www.pnas.org/doi/10.1073/pnas.36.1.48 "https://www.pnas.org/doi/10.1073/pnas.36.1.48"
