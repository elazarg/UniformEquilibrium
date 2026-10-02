# Law-tight cap--Nash saturation forces a neutral minimum set

Authors: `CODEX_ADVERSARY`; corrected and assembled by `CODEX_STRENGTHEN`

Independent review:
[CODEX_STRENGTHEN](../feedback/CODEX_ADVERSARY__FIN4_CAP_NASH_SATURATION_HULL__BY_CODEX_STRENGTHEN.md)

Original-author consistency approval:
[CODEX_ADVERSARY](../feedback/CODEX_STRENGTHEN__CAP_NASH_SATURATION_HULL_EXPORT_DRAFT__BY_CODEX_ADVERSARY.md)

## Exact statement

Let \(I\) be a nonempty finite player set and let \(r\) be a bounded
quitting-game reward table. Let

\[
 \mathcal C=
 \operatorname{quittingTerminalSemanticLawCarrier}(r).
\]

A point \(z=(X,\mu)\in\mathcal C\) has:

- a terminal semantic pair \(X=(u,c)\), where \(u_i\) is prescribed terminal
  payoff and \(c_i\) is the supremum against all unilateral behavioral
  replacements; and
- a finite terminal-outcome law
  \[
  \mu:\{\operatorname{none}\}\cup
       \{\operatorname{some}S:\varnothing\ne S\subseteq I\}
       \longrightarrow[0,1].
  \]

Here `none` is joint Never and `some S` records the terminal quitting
coalition. The law does not record stopping dates or a chronological source
trace.

Put

\[
 d_i(X)=c_i-u_i,\qquad D(X)=\sum_{i\in I}d_i(X).
\]

Assume that

\[
 0<D_*\le D(X)\qquad((X,\mu)\in\mathcal C). \tag{1}
\]

Fix an origin \(z_0=(X_0,\mu_0)\in\mathcal C\), a nonempty coalition
\(S_0\), and

\[
 b_0=\mu_0(\operatorname{some}S_0)>0. \tag{2}
\]

For a product root \(x\), let

\[
 q(x)=\operatorname{quittingStationaryContinueMass}(x),
 \qquad a(x)=1-q(x),
\]

and let \(P_x(X,\mu)\) be the joint semantic/outcome-law prefix. A root is
called exact below only when it is exact Nash against the displayed cap
vector \(c=X.2\), not against the prescribed vector \(u=X.1\).

### Theorem A: generic law-tight saturation

There are a nonempty compact set
\(\widehat{\mathcal H}=\widehat{\mathcal H}(z_0)\subseteq\mathcal C\), a
number \(D_H>0\), and a nonempty compact set

\[
 \mathcal M=
 \{(X,\mu)\in\widehat{\mathcal H}:D(X)=D_H\} \tag{3}
\]

with these properties:

1. **Origin and prefix saturation.**
   \(z_0\in\widehat{\mathcal H}\). If \(z\in\widehat{\mathcal H}\) and
   \(x\) is exact cap--Nash at \(z\), then
   \(P_xz\in\widehat{\mathcal H}\).
2. **Downward same-law closure.**
   If \((X,\mu)\in\widehat{\mathcal H}\),
   \((Y,\mu)\in\mathcal C\), and \(D(Y)\le D(X)\), then
   \((Y,\mu)\in\widehat{\mathcal H}\).
3. **Debt-weighted atom cone.** Every \((X,\mu)\) in the hull satisfies
   \[
   D(X_0)\mu(\operatorname{some}S_0)\ge D(X)b_0. \tag{4}
   \]
   Consequently every point of \(\mathcal M\) satisfies
   \[
   \mu(\operatorname{some}S_0)
   \ge\frac{D_H}{D(X_0)}b_0
   \ge\frac{D_*}{D(X_0)}b_0>0. \tag{5}
   \]
4. **Hull and law-fibre minimization.**
   \(D_H\) is the minimum of \(D\) on the hull. Every
   \((X,\mu)\in\mathcal M\) also minimizes debt on its entire
   terminal-outcome-law fibre:
   \[
   D(X)\le D(Y)\qquad((Y,\mu)\in\mathcal C). \tag{6}
   \]
5. **Unique neutral cap root.** At every \((X,\mu)\in\mathcal M\),
   \[
   x\text{ is exact Nash against }X.2
   \quad\Longleftrightarrow\quad
   x=\text{all Continue}. \tag{7}
   \]
   The all-Continue semantic/law prefix fixes \((X,\mu)\) exactly.
6. **Global absorption bound.** For every \((X,\mu)\) in the hull and
   every exact cap--Nash root \(x\) there,
   \[
   a(x)\le\frac{D(X)-D_H}{D(X)}. \tag{8}
   \]
   Every finite exact-prefix chain
   \(z_{n+1}=P_{x_n}z_n\), \(0\le n<N\), in the hull therefore satisfies
   \[
   \sum_{n<N}a(x_n)
   \le\frac{D(z_0.1)-D(z_N.1)}{D_H}
   \le\frac{D(z_0.1)-D_H}{D_H}, \tag{9}
   \]
   where \(z_0\) in (9) is the initial point of this displayed chain.

The set \(\mathcal M\) is called a minimum set. No convexity or
convex-geometric face property is asserted.

### Theorem B: Fin4 regeneration or strict neutral saturation

Let \(I=\operatorname{Fin}4\), let `residual` be a
`FinFourQuantitativeFullSupportHardResidual r bound`, and let
\(z_0=(X_0,\mu_0)\in\mathcal C\) carry the positive atom (2). Then Theorem A
applies with

\[
 D_*=\operatorname{quittingTerminalDebtSumInf}(r)>0. \tag{10}
\]

Exactly one of the following numerical alternatives holds.

1. **Same-point minimum regeneration:** \(D_H=D_*\). Every selected
   \(z_H\in\mathcal M\) is globally minimum over the full semantic carrier.
   The checked same-point causalization theorem produces a
   `QuittingMinimumLawCausalSuffixAtom r zH`. Thus this particular retained
   hull point, not an independently reselected minimum point, packages a
   `FinFourMinimumAtomProducer r bound` whose residual field is the supplied
   `residual`.
2. **Strict neutral saturation:** \(D_*<D_H\le D(X_0)\). The returned
   passport retains the compact minimum set, the atom floor (5),
   same-outcome-law fibre minimality, the exact all-Continue self-loop,
   root uniqueness (7), and the global bound (8).

Every point \(z=(X,\mu)\in\mathcal M\) in the strict alternative has at least
one of the following exhaustive forms:

1. **Full debt support:** \(d_i(X)>0\) for all four players.
2. **Reset-rigid incidence:** some player \(o\) has \(d_o(X)=0\) and positive
   total opponent incidence in \(\mu\). Then there are \(j\ne o\) and a
   same-law point \((R,\mu)\in\mathcal M\), returned by the checked fixed-law
   reset dispatch, such that:
   - \(d_o(R)=0\) and \(D(R)=D_H\);
   - the positive \((o,j)\)-incidence coordinate, opposite-face debt-transfer
     account, and supported strict toggle are retained; and
   - the dispatch's absorbing dynamic exit is impossible, so its exact
     all-Continue fixed-face arm holds.
3. **Singleton/Never binding cycle:** there are a unique zero-debt owner
   \(o\) and \(p>0\) with
   \[
   \mu=p\,\delta_{\operatorname{some}\{o\}}
      +(1-p)\,\delta_{\operatorname{none}}. \tag{11}
   \]
   The owner is cap-binding:
   \[
   X.2_o=r_o(\{o\}). \tag{12}
   \]
   Moreover, the finite nonempty set of cap-binding players contains a
   directed cycle of length at least two. Every edge \(i\to j\) of the cycle
   satisfies
   \[
   j\ne i,\qquad X.2_j=r_j(\{j\}),\qquad
   r_j(\{i,j\})-r_j(\{i\})>0. \tag{13}
   \]

The cycle need not contain the original zero-debt owner. The three forms are
a classification of strict saturation points, not a consumed terminal
trichotomy.

## Definitions and assumptions

A subset \(A\) of the joint carrier is a law-tight exact-cap-prefix invariant
above \(z_0\) when:

1. \(A\) is closed in the ambient finite-dimensional topology;
2. \(A\subseteq\mathcal C\) and \(z_0\in A\);
3. exact cap--Nash of \(x\) at \(z\in A\) implies \(P_xz\in A\); and
4. \((X,\mu)\in A\), \((Y,\mu)\in\mathcal C\), and
   \(D(Y)\le D(X)\) imply \((Y,\mu)\in A\).

Define

\[
 \widehat{\mathcal H}(z_0)=
 \bigcap\{A:A\text{ is such an invariant above }z_0\}. \tag{14}
\]

For distinct players \(o,j\), define

\[
 I_{o,j}(\mu)=
 \sum_{\substack{T:\,j\in T\\j\ne o}}
   \mu(\operatorname{some}T),
 \qquad
 J_o(\mu)=\sum_{j\ne o}I_{o,j}(\mu). \tag{15}
\]

All these incidence quantities are nonnegative. The law coordinate counts a
coalition once for each displayed opponent it contains and forgets timing.

## Proof of Theorem A

### Compact saturation

The family in (14) is nonempty: the whole compact carrier is closed, contains
\(z_0\), is prefix-stable by
`quittingTerminalSemanticLawPrefix_mem_carrier`, and trivially contains every
same-law carrier replacement. An arbitrary intersection of closed sets is
closed. Every defining set contains \(z_0\), so the intersection is nonempty;
as a closed subset of the compact carrier it is compact.

Both invariances pass pointwise to the intersection. If a new exact root
appears only at a limit point of the hull, it is still applied inside every
defining invariant at that limit point. No continuity or lower
hemicontinuity of the exact-root correspondence is used.

### Exact debt and atom scaling

Let \(z=(X,\mu)\in\mathcal C\), let \(x\) be exact Nash against \(X.2\), and
write \(P_xz=(Y,\nu)\). The checked cap--Nash prefix theorem gives

\[
 d_i(Y)=q(x)d_i(X),\qquad D(Y)=q(x)D(X). \tag{16}
\]

For the retained finite atom, the affine law prefix gives

\[
 \nu(\operatorname{some}S_0)
 =
 \operatorname{quittingRootCoalitionMass}(x,S_0)
 +q(x)\mu(\operatorname{some}S_0)
 \ge q(x)\mu(\operatorname{some}S_0). \tag{17}
\]

Let

\[
 K=\{(X,\mu)\in\mathcal C:
 D(X_0)\mu(\operatorname{some}S_0)\ge D(X)b_0\}.
\]

This set is closed and contains \(z_0\). Equations (16)--(17) show prefix
invariance. Downward same-law replacement leaves the left side fixed and
only decreases the right side. Thus \(K\) is one of the sets intersected in
(14), so the whole saturation hull lies in \(K\). This proves (4)--(5).

### Minimum set, law fibre, and root uniqueness

Continuity of \(D\) on the nonempty compact hull gives \(D_H\) and the
nonempty compact minimum set \(\mathcal M\).

Fix \((X,\mu)\in\mathcal M\) and a same-law carrier point \((Y,\mu)\). If
\(D(Y)>D(X)\), (6) is immediate. If \(D(Y)\le D(X)\), downward closure puts
\((Y,\mu)\) in the hull and hull minimality gives \(D(X)\le D(Y)\). This
proves whole-fibre minimality.

Now let \(x\) be exact cap--Nash at \((X,\mu)\in\mathcal M\). Prefix closure
and (16) give

\[
 D_H\le q(x)D_H.
\]

Since \(D_H\ge D_*>0\) and \(q(x)\le1\), one has \(q(x)=1\). The checked
`eq_quittingAllContinueRoot_of_continueMass_eq_one` gives that \(x\) is all
Continue.

Conversely, `exists_isZeroQuittingRootNash` supplies at least one exact Nash
root against \(X.2\); the preceding paragraph identifies it with all
Continue. This proves both directions of (7). The all-Continue outcome-law
prefix is the identity. Its exact cap--Nash property supplies the singleton
inequalities that make the semantic prefix an identity as well.

### Quantitative absorption

At an arbitrary hull point, prefix closure and (16) give

\[
 D_H\le(1-a(x))D(X).
\]

Since \(D(X)>0\), rearranging proves (8). Along a finite exact-prefix chain,

\[
 D(X_n)-D(X_{n+1})=D(X_n)a(x_n)\ge D_Ha(x_n).
\]

Summation telescopes and proves (9).

## Proof of Theorem B

### Same-point regeneration

The hard-residual minimum-source theorem supplies the positive global floor
(10) and a semantic point attaining it. Theorem A gives

\[
 D_*\le D_H\le D(X_0).
\]

If \(D_H=D_*\), every \(z_H=(X_H,\mu_H)\in\mathcal M\) has semantic
projection globally minimizing \(D\). The hypotheses of
`finFourHardResidual_minimumLaw_causalSuffixAtom` therefore hold at this same
joint-law point. Its causal suffix atom, the supplied residual, carrier
memberships, and the equality \(D(X_H)=D_*\) are precisely the data needed to
package a same-residual `FinFourMinimumAtomProducer`.

### Reset-rigid incidence

Assume \(D_*<D_H\), fix \(z=(X,\mu)\in\mathcal M\), and let

\[
 Z=\{i:d_i(X)=0\}.
\]

If \(Z\) is empty, all debts are positive. Otherwise, if some \(o\in Z\) has
\(J_o(\mu)>0\), nonnegativity and finiteness of (15) give a specific
\(j\ne o\) with \(I_{o,j}(\mu)>0\).

Apply the checked fixed-law reset dispatch with a global-minimum semantic
point as source and \(X\) as target. It returns a same-law point
\((R,\mu)\in\mathcal C\) with

\[
 D_*\le D(R)\le D(X)=D_H. \tag{18}
\]

Downward same-law closure puts \((R,\mu)\) in the hull. Hull minimality
reverses the second inequality, so \(D(R)=D_H\) and
\((R,\mu)\in\mathcal M\). Its exact cap root is therefore uniquely all
Continue. The dispatch's absorbing dynamic arm would instead give an exact
prefix in the hull with debt below \(D_H\), which is impossible. Hence the
fixed-face arm and all the stated reset/incidence/toggle data remain.

### Singleton/Never reduction

It remains to suppose \(J_o(\mu)=0\) for every \(o\in Z\). If a finite
coalition \(T\) has positive law mass, then for each \(o\in Z\), \(T\) can
contain no player distinct from \(o\); otherwise a nonnegative incidence
coordinate would be positive. Since \(T\) is nonempty, \(T=\{o\}\).

The retained atom (5) supplies at least one positive finite atom. Two distinct
members of \(Z\) would force that atom to be two different singletons. Hence
\(Z=\{o\}\), and simplex normalization gives (11) for some \(p>0\).

### Singleton/Never cap tightness

We use the following generic lemma.

> If \((X,\mu)\in\mathcal C\),
> \(\mu=p\delta_{\operatorname{some}\{o\}}+
> (1-p)\delta_{\operatorname{none}}\) with \(p>0\), and \(d_o(X)=0\), then
> \(X.2_o=r_o(\{o\})\).

Because the finite-dimensional carrier is the closure of actual
semantic/law points, choose actual behavioral profiles \(\sigma_n\) whose
joint points converge to \((X,\mu)\). Let \(N_{n,i}\) be player \(i\)'s
marginal Never probability and \(F_{n,i}=1-N_{n,i}\).

Joint Never is the product of the marginal Never probabilities, so

\[
 \prod_iN_{n,i}\longrightarrow1-p. \tag{19}
\]

The reward-moment identity gives

\[
 X.1_o=p\,r_o(\{o\}).
\]

Since \(d_o(X)=0\),

\[
 X.2_o=p\,r_o(\{o\}). \tag{20}
\]

If \(p=1\), (12) follows. Suppose \(0<p<1\). Equation (19) gives a common
\(\kappa>0\) such that every \(N_{n,i}\ge\kappa\) eventually.

For \(j\ne o\), the limiting law has zero mass on terminal singleton
\(\{j\}\). Independence gives only the one-sided cylinder inequality

\[
 \Pr_{\sigma_n}(\text{terminal coalition }\{j\})
 \ge
 F_{n,j}\prod_{k\ne j}N_{n,k}. \tag{21}
\]

The right event says that \(j\) stops finitely while every other player
Never stops. It is a subset of the singleton event; equality is not claimed.
The uniform lower bound on the Never factors and (21) imply
\(F_{n,j}\to0\) for every \(j\ne o\).

Let \(M\) bound every reward coordinate in absolute value. If \(o\) deviates
to Quit immediately, its payoff differs from \(r_o(\{o\})\) only if an
opponent also Quits immediately. The absolute error is at most

\[
 2M\sum_{j\ne o}F_{n,j}\longrightarrow0.
\]

If \(o\) deviates to Never, a nonzero payoff requires some opponent to stop
finitely, so its payoff has absolute value at most

\[
 M\sum_{j\ne o}F_{n,j}\longrightarrow0.
\]

Each approximating unrestricted cap dominates both deviations. Passing these
two lower bounds to the convergent cap coordinate yields

\[
 X.2_o\ge\max\{0,r_o(\{o\})\}. \tag{22}
\]

Equations (20), (22), \(p>0\), and \(p<1\) force
\(r_o(\{o\})=X.2_o=0\). This proves (12) in all cases.

### Binding collision cycle

At \(z\in\mathcal M\), all Continue is exact cap--Nash, so every singleton
reward is at most its cap coordinate. Equation (12) makes \(o\) cap-binding.
The checked
`exists_quittingSingletonCollisionGain_pos_of_unique_allContinue` gives,
for every binding player \(i\), a distinct binding successor \(j\) satisfying
(13). Choose one successor for every member of the finite nonempty binding
set. Iterating this self-map and removing the preperiod produces a directed
cycle. No successor is a self-loop, so its length is at least two.

This completes the exhaustive classification.

## Conjecture-facing change

Repeated off-minimum positive cap-root descent no longer requires choosing an
infinite chain, a uniform absorption floor, or a continuous root selection.
Closing simultaneously under exact prefixes, compact limits, newly appearing
exact roots, and downward same-law replacements produces a compact minimum
set. Every positive exact cap root is consumed before minimization; the only
strict output is the neutral passport classified above.

For a Fin4 hard residual, equality with the global minimum regenerates a
causal source at the same retained hull point. Strict inequality is reduced
to the three explicit chambers.

This is a carrier-level reduction. It does not answer
[`FIN4_ACTUAL_PAID_CAP_DESCENT_OR_INERT_STALL.md`](../questions/FIN4_ACTUAL_PAID_CAP_DESCENT_OR_INERT_STALL.md)
or
[`FIN4_MINIMUM_RETURN_CAPSTONE.md`](../questions/FIN4_MINIMUM_RETURN_CAPSTONE.md),
which require an actual paid chronology and complete post-row behavioral
tail.

The remaining strict-saturation consumer is precisely:

> prove \(D_H=D_*\), or turn one of the three strict passport chambers into an
> actual behavioral profile with total unrestricted terminal debt below
> \(D_*\).

No such chamber consumer is claimed here.

## Probability, information, and strategy-class audit

Before absorption there is one live public history at every date. A
unilateral behavioral replacement is therefore represented on payoff-relevant
histories by an arbitrary time-dependent hazard, including Never and
arbitrarily late randomized quitting. The cap coordinate is the supremum over
all such deviations.

Players' behavioral randomizations are independent. Independence is used in
the product-root laws and in the one-sided cylinder inequality (21). The proof
never conditions a cap on a zero-probability event and never interchanges a
supremum with a limit. Two fixed deviations are evaluated on each
approximating profile before their lower bounds are passed to the limiting
cap.

Hull and minimum-set points are carrier objects and need not be realized by
one behavioral profile.

## Boundary tests

1. If \(D_*=0\), a minimum-set exact root may absorb without lowering debt,
   and the positive atom floor disappears.
2. If \(b_0=0\), the cone retains no atom.
3. Approximate cap--Nash roots do not satisfy the exact scaling (16).
4. Nash against the prescribed payoff does not imply cap-debt scaling;
   cap--Nash here does not activate prescribed-payoff plateau theorems.
5. Equal terminal-outcome laws do not imply equal stopping-time laws, marked
   dates, total-variation closeness, or common source ancestry.
6. Downward same-law closure preserves the cone. Upward closure need not.
7. A new exact root appearing at a compact limit is included because every
   defining invariant is tested at the limit point itself.
8. Equality in (21) is generally false because another player can have a
   later counterfactual finite stopping time after \(j\) has ended the game.
9. The binding cycle may occur after a preperiod and need not contain the
   original owner.

## Adapter and consumer

The generic actual-data adapter takes any joint carrier origin with a positive
finite terminal atom. The hull, atom cone, minimum set, root-neutrality, and
absorption estimate are produced, not assumed.

For a `FinFourQuantitativeFullSupportHardResidual`, the checked positive
minimum and same-point causalization supply the Fin4 adapter. The equality arm
enters the existing `FinFourMinimumAtomProducer` interface at the retained
hull point. The strict arm is a typed reduction to three neutral chambers,
not a terminal semantic consumer.

## Source correspondence and novelty

Checked ingredients:

- `quittingTerminalSemanticLawCarrier_isCompact`,
  `terminalSemanticLawCarrier_fst_mem_carrier`,
  `terminalSemanticLawCarrier_mass_mem_stdSimplex`,
  `terminalSemanticLawCarrier_rewardMoment`, and
  `quittingTerminalSemanticLawPrefix_mem_carrier` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`;
- `eq_quittingAllContinueRoot_of_continueMass_eq_one` in
  `UniformEquilibrium/Quitting/Boundary/Analytic/SeamPriceResidual.lean`;
- `finFourHardResidual_minimumLaw_causalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
- `FinFourMinimumAtomProducer` and
  `FinFourMinimumAtomProducer.exists_residual_eq_of_hardResidual` in
  `Research/Quitting/FinFourProducerAtlas/Source.lean`;
- `QuittingTerminalExploitabilityWitness.exists_fixedLaw_resetFace_dispatch`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`;
- `quittingTerminalTotalOpponentIncidenceMass` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceRatio.lean`; and
- `exists_quittingSingletonCollisionGain_pos_of_unique_allContinue` in
  `Research/Quitting/BindingCollisionGainPositivity.lean`.

The checked source contains the one-step scaling, carrier, reset,
causalization, and collision components. It does not form the smallest closed
law-tight invariant, minimize debt on it, or prove neutral root uniqueness
after closure under every newly appearing exact root. Those saturation and
classification statements are the new ordinary mathematics. No literature
claim is invoked.

## Lean handoff

Suggested generic declarations:

```text
IsQuittingLawTightCapNashInvariant
quittingLawTightCapNashSaturationHull
quittingLawTightCapNashSaturationHull_isCompact
quittingLawTightCapNashSaturationHull_prefix_mem
quittingLawTightCapNashSaturationHull_sameLaw_of_debt_le
quittingLawTightCapNashSaturationHull_atomCone
QuittingLawTightCapNashSaturationPassport
```

The invariant family should quantify over ambient-closed subsets of the joint
carrier. Do not define the hull merely as the closure of finite descendants;
that does not automatically handle an exact root appearing only at a limit
cap.

Suggested Fin4 declarations:

```text
finFourLawTightSaturation_minimumProducer_or_strictPassport
exists_positive_opponentIncidenceCoordinate_of_total_pos
terminalSemanticLaw_soloNever_zeroDebt_cap_eq_solo
finFourStrictSaturation_fullDebt_or_resetRigid_or_soloNeverCycle
```

For the singleton/Never lemma, first extract actual approximating profiles
from the finite-dimensional closure. Use the one-sided stopping-law cylinder
inequality and quantitative immediate-Quit/Never deviation bounds.

The strict passport must store the supplied hard residual and the global
minimum source used by the reset dispatch. It must not store a desired
terminal consumer as a field.

## Scope and nonclaims

- No theorem here proves a uniform-equilibrium payoff.
- No hull point is asserted to be an actual behavioral profile.
- No stopping-time tightness, strategic total-variation compactness, or
  ancestry-preserving decoder is produced.
- No paid row, prescribed-payoff Nash root, Bellman return, or admissible
  payoff gain follows from cap-root neutrality.
- The equality arm does not identify its causal atom with the originally
  retained coalition \(S_0\).
- The strict trichotomy is not an exhaustive normal form for all Fin4
  quitting games; it classifies only strict saturation points.
- None of the three strict chambers is consumed.

## Revisit record

Pre-formalization packet SHA-256:
`e85c33517de7613296112f184e2e237b8d76f5f290868140f7bb28eadbd20c0c`.

The generic hull landed in commit
`a6d9376bc90ce1934fe1086aefb827207f7ecfc3`; the minimum equality level,
root rigidity, absorption bound, and finite-chain telescopes landed in
`351bd82d5299158858819171d6e690ced5f69d5a`; singleton/Never cap tightness
landed in `331ae50a0a1d595a976ce87a215da6c0e7657de3`; and the strict carrier
classification landed in `fe12b32b6df5210eabe59d0ca11cba54c77b1ea1`.
The separate globally minimizing source reduction landed in
`5387eb0f8bff075ec9a8debf64755c4f32587087`.

The checked production owners are
`UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashSaturationHull.lean`,
`LawTightCapNashMinimumFace.lean`,
`TerminalSemanticSingletonNeverCapTightness.lean`,
`LawTightCapNashStrictMinimum.lean`,
`LawTightCapNashGlobalMinimumMoat.lean`, and
`FinFourLawTightCapNashStrictMinimum.lean`, under the same Diagnostics
directory.  They provide `quittingLawTightCapNashSaturationHull`, its compact
prefix and same-law closure, atom cone and minimizer, the minimum-face root
and absorption theorems,
`terminalSemanticLaw_singletonNever_zeroDebt_cap_eq_singletonReward`,
`lawTightStrictSaturation_fullDebt_or_resetRigid_or_singletonNeverCycle`, and
the canonical global-source two-chamber theorem.

The generic hull and minimum layers have `M` and `L`; the Fin4 no-uniform-
payoff source adds `A`.  The separate global-minimum packet has branch-local
`C` for singleton/Never deletion only.

The packet's arbitrary-origin numerical split `D_H = D_*` versus
`D_* < D_H` is not packaged.  No same-retained-point causalization constructs
the advertised `FinFourMinimumAtomProducer` while preserving the supplied
residual, and no typed strict passport retains that split and provenance.
Full-debt and reset-rigid chambers remain unconsumed.

Revisit this packet only when the same-point regeneration/strict-passport
split is proved with residual provenance, or a surviving chamber gains a
genuine behavioral or recursive consumer.  Additional wrappers around the
existing hull and minimum declarations do not satisfy the gate.
