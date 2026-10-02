# Strict off-minimum positive-root Zeno: killed-face saturation and the two-port wall

**Author:** `CODEX_SOURCE_GATE`  
**Status:** ordinary-mathematical killed-face saturation proved; checked
terminal consumers audited; the strict neutral output remains unconsumed  
**Date:** 2026-08-30

## 1. Question and answer

This note attacks the strict off-minimum positive-root arm left by
`gpt/NONZERO_PERSIST_ATTEMPT_1.md`, Followup 3.  The retained data are:

- a positive global terminal-semantic debt minimum \(D_*>0\);
- an off-minimum downstream endpoint \(T\) with
  \(D(T)>D_*\) and one fixed killed mover \(p\) satisfying \(d_p(T)=0\);
- exact positive cap--Nash prefixes at the downstream port, with summable
  total absorption/hazard in an infinite descent;
- an eventual all-Continue cap root, unique after exact-prefix saturation;
  and
- a positive marked atom at the **upstream** reattached port
  
  
  \[
  \widehat t_n=A_n\triangleright x_n^{\rm mark}\triangleright t_n,
  \]
  
  not in the outcome law of the downstream suffix \(t_n\).

No finite renewable rank follows from these data, and the checked
summable-port consumer does not yield a terminal uniform payoff.  Exact cap prefixing
multiplies every debt coordinate by the same positive survival factor.  It
therefore preserves the killed coordinate, the entire zero/positive debt
support, and the normalized debt vector.  Summability produces an
all-Continue Nash--Bellman port, but the only checked conversion of that port
to a uniform payoff uses a **diagonal** terminal-semantic carrier point.  The
positive global minimum forces every limit in the present chain to retain
total debt at least \(D_*>0\), so the required diagonal point is absent.

The strongest exact positive reduction is a killed-player-face specialization
of the reviewed law-tight cap--Nash saturation hull.  Starting from the
downstream joint-law lift, it produces either:

1. a same-point landing on the global minimum fibre, hence a fresh
   same-residual minimum producer; or
2. a strict off-minimum joint-law point which still has \(d_p=0\), minimizes
   debt on its closed killed-face saturation, and has all Continue as its
   unique exact cap--Nash root.

Thus arbitrary repeated positive-root descent is compressible to one exact
neutral passport.  It is not terminally consumed.  The upstream atom cannot
be added to that passport: it lives at the other port, and the current state
does not contain a continuation-replacement kernel transporting upstream
semantics and unrestricted caps.

No Lean file was changed.

## 2. Exact declarations inspected

The one-step strict return is
`FinFourStrictRayPositiveRootReturn` and its split
`nonempty_minimumLawHandoff_or_offMinimumDescent` in
`Research/Quitting/FinFourProducerAtlas/StrictRayPositiveRootReturn.lean`.
The file explicitly gives no recursive or quantitative consumer in the
off-minimum arm.

The exact scalar and literal-word identities are in
`Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`:

- `quittingTerminalSemanticDebt_maximalCapSemanticPrefixOrbit_eq`;
- `quittingTerminalSemanticDebtSum_maximalCapSemanticPrefixOrbit_eq`;
- `quittingMaximalCapSemanticPrefixOrbit_positiveDebtSupport_eq`;
- `quittingTerminalSemanticDebt_normalized_maximalCapSemanticPrefixOrbit_eq`;
- `minimumDebt_div_sourceDebt_le_maximalCapSemanticPrefixSurvival`; and
- `quittingStageCoalitionMass_maximalCapSemanticPrefixProfile_add`.

The one-step actual-source regeneration is
`QuittingPaidCapLiftedSource.maximalOneStepPaidResetRegeneration_or_uniqueAllContinue`
in `Research/Quitting/PaidCapMaximalOneStepRegeneration.lean`.  The reviewed
finite-iteration ledger is
`notes/CHATGPT_EXTERNAL__NONCOLLAPSING_MAXIMAL_PAID_RESET_ORBIT.md`.

The generic reviewed saturation theorem is exported as
`exports/LAW_TIGHT_CAP_NASH_SATURATION_HULL.md`.  Its load-bearing checked
ingredients are:

- `quittingTerminalSemanticLawCarrier_isCompact`,
  `exists_terminalSemanticLawCarrier_lift`, and
  `quittingTerminalSemanticLawPrefix_mem_carrier` in
  `TerminalSemanticResetIncidenceReturn.lean`;
- `continuous_quittingTerminalSemanticDebt` and
  `continuous_quittingTerminalSemanticDebtSum` in
  `TerminalSemanticEqualityStratum.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `TerminalCapNashEndpointTransport.lean`;
- `exists_isZeroQuittingRootNash` in `Root/NashExistence.lean`; and
- `eq_quittingAllContinueRoot_of_continueMass_eq_one` in
  `Boundary/Analytic/SeamPriceResidual.lean`.

The summable-port API is
`QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort` and
`uniformPayoff_or_summableChargeAllContinuePort` in
`PunishmentFloorInfiniteOrbitChargeDichotomy.lean`.  The extra diagonal
consumer is
`limit_isUniformEquilibriumPayoff_of_endpoint` in
`PositiveJointExactPrefixOrbitDiagonal.lean`, ultimately using
`isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier` in
`UniformPayoffTerminalSemanticCarrier.lean`.

The exact unique-cap stall is recorded by
`exactCapPrefix_joint_eq_self_of_unique_allContinue` and
`capNashRootStack_eq_replicate_allContinue_of_unique_terminalCap` in
`Research/Quitting/UniqueAllContinueCapStackNoGo.lean`.  The superficially
tempting backward rigidity theorem is
`exactNashBellmanPath_eq_anchor_of_tendsto_unique_allContinue` in
`Quitting/Bellman/Finite/AllContinueBasinRigidity.lean`.

Finally, same-point regeneration on the minimum fibre is checked by
`finFourHardResidual_minimumLaw_causalSuffixAtom` in
`TerminalSemanticFinFourMinimumLawFiniteAtom.lean`.

## 3. Exact Zeno ledger and invariant finite data

Let \(Z_k=(U_k,B_k)\) be a composable downstream semantic chain and let
\(x_k\) be exact cap--Nash against \(B_k\).  Write

\[
 Z_{k+1}=P_{x_k}Z_k,
 \qquad c_k=\Pr_{x_k}(\hbox{all Continue}),
 \qquad a_k=1-c_k.
\tag{1}
\]

Assume every step has positive absorption but positive continuation.  Exact
cap Nash gives, for every player \(i\),

\[
 d_i(Z_{k+1})=c_kd_i(Z_k),
 \qquad D(Z_{k+1})=c_kD(Z_k).
\tag{2}
\]

Let \(C_N=\prod_{k<N}c_k\).  Then

\[
 d_i(Z_N)=C_Nd_i(Z_0),
 \qquad D(Z_N)=C_ND(Z_0).
\tag{3}
\]

Global minimality gives

\[
 C_N=\frac{D(Z_N)}{D(Z_0)}
 \ge \kappa:=\frac{D_*}{D(Z_0)}>0.
\tag{4}
\]

Consequently:

\[
 d_i(Z_N)>0\Longleftrightarrow d_i(Z_0)>0,
 \qquad
 \frac{d_i(Z_N)}{D(Z_N)}=
 \frac{d_i(Z_0)}{D(Z_0)}.
\tag{5}
\]

In particular \(d_p(Z_0)=0\) implies \(d_p(Z_N)=0\) for every \(N\).
The complete zero set, positive support, support cardinality, and normalized
debt direction are constant.  No support-cardinality or killed-player rank
decreases.

Moreover \(1-c_k\le -\log c_k\), and (4) yields

\[
 \sum_k a_k\le -\log\kappa<\infty.
\tag{6}
\]

The more general approximate account in Followup 3,

\[
 D_{k+1}=(1-a_k)D_k+\rho_k,
 \qquad \sum_k\rho_k<\infty,
\tag{7}
\]

still gives summable total hazard.  But the killed-face statement is exact
only when the coordinate residual is zero.  If
\(d_p(Z_{k+1})=c_kd_p(Z_k)+\rho_{k,p}\), an approximate step can reintroduce
positive \(p\)-debt.  The killed-face saturation below therefore applies to
the exact limiting cap-prefix operation, not automatically to every finite
approximate actualizer.

Since there are finitely many players, root supports, marked coalitions, and
role labels, a subsequence can keep all those labels constant.  Equations
(5)--(6) permit every such finite datum to remain constant forever while the
positive real debt decreases strictly.  Thus none is a hidden natural-valued
rank.

## 4. Killed-face law-tight saturation

This is the useful nonduplicative specialization of the exported generic
saturation theorem.

Let \(\mathcal C\) be the compact joint semantic/outcome-law carrier and fix
the killed player \(p\).  Define the closed face

\[
 \mathcal C_p=
 \{(X,\mu)\in\mathcal C:d_p(X)=0\}.
\tag{8}
\]

Let \(z_0=(X_0,\mu_0)\in\mathcal C_p\) be a joint-law cluster selected from
the literal downstream targets.  A subset \(A\subseteq\mathcal C_p\) is a
**\(p\)-face law-tight invariant above \(z_0\)** when:

1. \(A\) is ambient closed and contains \(z_0\);
2. if \(z\in A\) and \(x\) is exact cap--Nash at \(z\), then \(P_xz\in A\);
3. if \((X,\mu)\in A\), \((Y,\mu)\in\mathcal C_p\), and
   \(D(Y)\le D(X)\), then \((Y,\mu)\in A\).

The whole face \(\mathcal C_p\) is such an invariant.  Indeed, continuity of
\(d_p\) makes it compact and closed, and exact prefix scaling gives

\[
 d_p(P_xX)=c(x)d_p(X)=0.
\tag{9}
\]

Intersect all such invariants and call the result
\(\widehat{\mathcal H}_p(z_0)\).  It is nonempty, compact, exact-prefix
invariant, and downward same-law closed **within the killed face**.

Let

\[
 D_{H,p}=\min_{z\in\widehat{\mathcal H}_p(z_0)}D(z.1),
\qquad
 \mathcal M_p=\{z\in\widehat{\mathcal H}_p(z_0):D(z.1)=D_{H,p}\}.
\tag{10}
\]

### Theorem 4.1 (killed-face neutralization)

Every \(z=(X,\mu)\in\mathcal M_p\) satisfies:

1. \(d_p(X)=0\);
2. \(D_*\le D_{H,p}\le D(X_0)\);
3. all Continue is the unique exact cap--Nash root at \(X.2\);
4. its semantic/law prefix fixes \(z\); and
5. for every hull point \(Y\) and exact cap root \(x\) there,
   
   \[
   \operatorname{Abs}(x)
   \le\frac{D(Y)-D_{H,p}}{D(Y)}.
   \tag{11}
   \]

#### Proof

Only item 3 is substantive.  If \(x\) is exact at a minimum point, prefix
invariance and (2) give

\[
 D_{H,p}\le c(x)D_{H,p}.
\]

Since \(D_{H,p}\ge D_*>0\) and \(c(x)\le1\), one has \(c(x)=1\).  A product
root with joint Continue mass one is all Continue.  Exact-root existence
then shows all Continue is itself exact and unique.  Its semantic and law
prefixes are identities.  The same inequality at an arbitrary hull point
rearranges to (11).  All other statements follow from construction. `QED`

### Corollary 4.2 (hard-residual output)

For a Fin4 hard residual, exactly one numerical alternative holds.

- If \(D_{H,p}=D_*\), every selected \(z_H\in\mathcal M_p\) is a global
  minimum joint-law point.  The checked same-point theorem
  `finFourHardResidual_minimumLaw_causalSuffixAtom` causalizes this very
  point.  Together with the unchanged residual and the infimum identity, it
  packages a fresh `FinFourMinimumAtomProducer` which still has (p)-debt
  zero.
- If \(D_*<D_{H,p}\), the result is a strict off-minimum, killed-player,
  unique-all-Continue neutral passport.  It is not a minimum producer, a
  behavioral profile, or a terminal approximate equilibrium.

This removes the arbitrary Zeno **sequence** as an independent output.  It
does not remove the strict neutral point.

If \(\mu_0\) itself has a positive finite atom, the debt-weighted atom cone
from `LAW_TIGHT_CAP_NASH_SATURATION_HULL.md` can be intersected into this
construction verbatim, retaining that downstream atom.  Followup 3 does not
supply this premise: its marked atom is upstream.

## 5. Why the checked summable-port consumer does not apply

The cap coordinates of an exact cap-prefix chain form a punishment-floor
Nash--Bellman orbit.  Summability of (6) therefore supplies a checked
`SummableChargeAllContinuePort`.  Its output is exactly:

- convergence of the cap annotations to a vector \(B_\infty\);
- roots converging coordinatewise to all Continue;
- punishment and singleton lower bounds at \(B_\infty\); and
- an exact all-Continue Nash--Bellman self-loop at \(B_\infty\).

This alone is not a uniform payoff.

The checked theorem
`limit_isUniformEquilibriumPayoff_of_endpoint` assumes a
`QuittingPositiveJointPrefixReachPunishmentEndpoint`.  That structure has

\[
 d_i(\text{endpoint})\le0\quad\hbox{for every }i.
\]

Carrier debts are nonnegative, so its endpoint is diagonal.  The proof then
shows

\[
 (B_\infty,B_\infty)
 \in\operatorname{quittingTerminalSemanticCarrier}(r)
\]

and invokes
`isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier`.

In the present branch, (3)--(4) instead give a semantic limit with

\[
 D(U_\infty,B_\infty)
 =\left(\lim_N C_N\right)D(Z_0)
 \ge D_*>0.
\tag{12}
\]

Only \(d_p=0\); at least one other debt coordinate remains positive.  The
available carrier point is \((U_\infty,B_\infty)\), not
\((B_\infty,B_\infty)\).  Thus the exact missing field is not another
summability estimate.  It is diagonal carrier membership, equivalently
vanishing unrestricted terminal debt for **every** player.

The theorem
`uniformPayoff_or_summableChargeAllContinuePort` confirms the boundary: on
the present summable side it returns the port, not the uniform-payoff arm.

## 6. The chronology orientation is wrong for backward rigidity

The checked rigidity theorem
`exactNashBellmanPath_eq_anchor_of_tendsto_unique_allContinue` cannot repair
the gap.  Its chronological hypotheses have the form

\[
 V_t=\operatorname{Succ}(x_t,V_{t+1}),
 \qquad x_t\text{ exact at }V_{t+1},
\tag{13}
\]

and propagate the unique-all-Continue conclusion backward from a late tail.

The descendant orbit has the opposite orientation:

\[
 B_{k+1}=\operatorname{Succ}(x_k,B_k),
 \qquad x_k\text{ exact at }B_k.
\tag{14}
\]

Every finite descendant is realized by the outer-to-inner word

\[
 x_{N-1}\triangleright x_{N-2}\triangleright\cdots
 \triangleright x_0\triangleright t.
\tag{15}
\]

Finite reversal is legitimate because it has a terminal suffix.  An infinite
reverse word has no first root corresponding to a largest index.  Reading
the roots as \(x_0,x_1,\ldots\) instead breaks both the cap matching and the
Bellman recursion.  Hence (13) is not an adapter for (14).

Uniqueness only at the limiting cap is also generally a boundary property,
not an open basin hypothesis.  Positive roots at the nearby caps converge to
all Continue.  The saturation minimizer correctly handles a positive root
which appears only after a limit by closing under it before minimizing; the
backward rigidity theorem does not.

## 7. Fixed-window topology of the outward word

The same orientation gives an exact topology regression.  Let \(P_N\) be the
literal profile in (15).  At a fixed stage \(t<N\), its live root is
\(x_{N-1-t}\).  Since summability implies \(a_k\to0\), for every fixed
horizon \(H\),

\[
 \Pr_{P_N}(\text{absorption in the first }H+1\text{ rows})
 \le \sum_{j=N-1-H}^{N-1}a_j\longrightarrow0.
\tag{16}
\]

Thus every fixed window converges to all Continue.  If the downstream origin
itself contains a finite atom of mass \(b>0\) at suffix stage \(s\), that atom
occurs in \(P_N\) at stage \(N+s\) with mass

\[
 C_Nb\ge\kappa b>0.
\tag{17}
\]

The atom therefore escapes every fixed window while retaining positive
terminal-outcome mass.  This is precisely the non-tight/pure-Never boundary
formalized for the stronger inert case in
`MinimumLawCausalSuffixPureNeverLimit.lean`.

Equation (16) also explains why summability cannot be converted into a
positive-charge moving window: every far-tail window has arbitrarily small
total hazard.  A terminal diagonal argument would have to recover the
semantic mass which escaped to infinity, and the present topology does not.

## 8. The upstream atom is not a downstream atom

Followup 3 has the more severe two-port situation.  Its actual profiles are

\[
 \widehat t_n=A_n\triangleright x_n^{\rm mark}\triangleright t_n.
\tag{18}
\]

The marked coalition and its positive mass are events of
\(\widehat t_n\).  The equality \(d_p(t_n)\to0\), the endpoint \(T\), and the
positive-root cap correspondence are properties of \(t_n\).  The terminal
law of \(t_n\) contains no event at the preceding marked row.

This is not a presentation defect.  At the literal-profile level one may
choose a marked prehistory root which absorbs into a fixed coalition with
probability \(\eta>0\).  Then every reattachment has upstream marked mass at
least \(\eta\), independently of the continuation law.  The downstream
continuation may even be pure Never.  Hence an upstream atom places no local
constraint on the downstream terminal law or cap-root correspondence.

Conversely, reattaching the prehistory changes the semantic pair.  The exact
finite-spine debt formula contains the prehistory's reached cap defects plus
the reach-weighted downstream debt.  Thus \(d_p(t_n)=0\) does not imply
\(d_p(\widehat t_n)=0\).

The joint semantic/outcome-law carrier stores neither the prehistory code nor
a continuation-replacement map for unrestricted best-response caps.  A
downstream exact prefix therefore acts functorially on the downstream joint
point, but there is no well-defined action on the upstream point from those
finite-dimensional coordinates alone.  Same terminal-outcome law is also
not source ancestry.

Accordingly the debt-weighted atom cone cannot be initialized with the
upstream mark while the killed-face constraint is initialized with the
downstream endpoint.  Doing so would silently merge the two ports.

The precise missing producer is an extension-compatible two-port kernel
which stores one compact prehistory code and proves, for every allowed
downstream cap prefix:

1. literal reattachment to the same prehistory/mark;
2. quantitative continuation reach;
3. transport of the complete upstream outcome law; and
4. transport of unrestricted cap coordinates or an explicitly charged cap
   error.

No inspected declaration supplies this kernel.  Without it, the upstream
atom cannot prove diagonal membership, a positive admissible return, or a
finite rank at the killed downstream port.

## 9. Exact scope of the regression

The killed-face saturation is genuinely compatible with the positive-minimum
Fin4 hard residual: it starts from the actual downstream carrier cluster,
uses the residual's positive global minimum, and its equality arm regenerates
the same residual at the selected hull point.  It is stronger than the scalar
example of a decreasing positive real sequence.

It does **not** construct a four-player reward table satisfying the hard
residual and the strict neutral alternative.  Such a table with a fixed
positive exploitability gap would be a negative solution of the maintained
conjecture, and no inspected source supplies one.  The exact negative content
proved here is instead:

- every currently available discrete datum can remain invariant along the
  strict exact orbit;
- the checked summable-port terminal theorem is missing all-player
  diagonalization;
- the checked backward-rigidity theorem has the wrong time orientation;
- the upstream atom and killed downstream debt cannot be combined in the
  current carrier state; and
- closed killed-face saturation reduces all Zeno/restart choices to one
  still-valid strict neutral passport.

Local exact tables in the reviewed saturation and paid/reset notes show that
unique all Continue, positive debt, normality, paid structure, and finite
atoms do not contradict one another at one cap.  Those tables have zero
global minimum and are only local API regressions; they are not promoted here
to hard-residual counterexamples.

## 10. Verdict and next question

No checked terminal consumer accepts the four stated data, and none of their
finite label/support invariants supplies a renewable rank.  The strongest
exact output is

```text
strict off-minimum downstream point with d_p = 0
  -> killed-face exact-prefix saturation
  -> same-point global-minimum regeneration
     or strict p-zero unique-all-Continue neutral passport.

upstream marked atom
  -/-> downstream atom or diagonal carrier membership
  without an extension-compatible two-port cap kernel.
```

The remaining question is no longer how to count infinitely many small
positive roots.  It is:

> Can a Fin4 hard residual contain a strictly off-minimum debt minimizer of a
> closed exact-cap-prefix invariant **killed-mover face**, and can the original
> two-port prehistory be extended functorially to that minimizer?

A negative answer gives same-point minimum regeneration.  A positive answer
must add the two-port kernel above before the retained upstream atom can be
used by any terminal or capacity consumer.
