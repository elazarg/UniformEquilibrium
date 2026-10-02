# Normalized inertness has one density, then saturation or a linear toll

Author: `CODEX_RIEMANN`

## Status

**Proved in ordinary mathematics from the checked prefix identities.**  The
single-density, feasibility, toll, and canonical-saturation results in
Sections 1--4 were independently reviewed PASS; see
[`feedback/CODEX_RIEMANN__NORMALIZED_INERT_SINGLE_DENSITY_TOLL__BY_CODEX_AMPERE.md`](../feedback/CODEX_RIEMANN__NORMALIZED_INERT_SINGLE_DENSITY_TOLL__BY_CODEX_AMPERE.md).
The density-to-zero trichotomy and exact regression in Sections 5--6 were
added afterward and have not yet received independent review.  This is a
source-facing reduction of the strict normalized-inert arm, not a
terminal consumer.  It proves two facts which are not visible in the generic
two-coordinate passport:

1. for the actual Fin 4 forced singleton-to-pair source, `actualGain` is a
   fixed positive table constant times `markedMass` on the *entire closed
   arbitrary-prefix orbit*, so the gain-density inequality is redundant; and
2. at a strict normalized minimizer, either that single density inequality is
   saturated, or every root below an explicit positive absorption radius
   pays root Nash defect at least `wholeDebt * absorption`.

With the canonical half-density, saturation also forces the minimizer to
retain at most half of the limiting seed's marked mass and actual gain.  This
is a genuine local no-go for sublinear-defect repair at a slack inert point.
It is not a renewable finite rank: positive mass may be halved indefinitely,
and the minimizer is a carrier point rather than a regenerated actual source.

This note continues
[`CODEX_RIEMANN__MINIMUM_REGENERATION_ORIENTATION_AUDIT.md`](CODEX_RIEMANN__MINIMUM_REGENERATION_ORIENTATION_AUDIT.md)
and the PASS audit of the actual normalized-return adapter.

## Question

Let `Q` be the strict `NormalizedInert` point produced from one actual
`FinFourOwnerCompressedMinimumReturnForcedPairPacket`.  What additional
structure does the forced-pair provenance impose on `Q`, beyond generic
unique-all-Continue rigidity?

The answer below is an exact saturation-or-toll alternative.  The remaining
question is whether the saturated face or the linear toll has an executable
source-faithful consumer.

## 1. The fixed pair gap

Fix the singleton owner `j` and the selected outsider `o`.  Put

\[
 \Delta := r_o(\{j,o\})-r_o(\{j\}).
 \tag{1}
\]

The hard-residual selection gives

\[
 \Delta\ge \Gamma>0,
 \tag{2}
\]

where `Gamma` is the terminal exploitability gap.  At every base row of the
normalized forced-pair family, the comparison profile has the pure singleton
`{j}` at the marked date and the target has the pure pair `{j,o}` at the same
date.  Write `L_n` for the live mass reaching that date.

Pureification and forced-pair routing give exactly

\[
 M_n:=\operatorname{markedMass}(P_n)=L_n.
 \tag{3}
\]

Since `j` quits surely in both profiles, the continuation is inaccessible to
`o` under either endpoint action.  Thus the actual whole-profile gain is

\[
 G_n:=\operatorname{actualGain}(P_n)
     =L_n\bigl(r_o(\{j,o\})-r_o(\{j\})\bigr)
     =\Delta M_n.
 \tag{4}
\]

This is an all-behavior profile identity.  It is not a stationary or local
cap estimate.

The checked generic prefix formulas say that a common finite root word with
joint survival `c` replaces `(M_n,G_n)` by `(c M_n,c G_n)`.  Hence every raw
decoration `X` satisfies

\[
 X.\operatorname{actualGain}
   =\Delta X.\operatorname{markedMass}.
 \tag{5}
\]

For completeness, let

\[
 H:=\{X:G(X)=\Delta M(X)\}.
\]

The map `X -> G(X)-Delta M(X)` is continuous, hence `H` is closed.  Equation
(5) puts the raw prefix orbit inside `H`; closure minimality therefore puts
the complete `prefixOrbitCarrier` inside `H`.  Thus:

\[
 \boxed{
 X\in\operatorname{prefixOrbitCarrier}
 \Longrightarrow
 X.\operatorname{actualGain}
   =\Delta X.\operatorname{markedMass}.}
 \tag{6}
\]

In particular the selected convergent passport `P` obeys `G_P=Delta M_P`.
For the canonical half-densities

\[
 m=\frac{M_P}{2D_P},\qquad
 g=\frac{G_P}{2D_P},
 \tag{7}
\]

we therefore have

\[
 g=\Delta m.
 \tag{8}
\]

Since `Delta>0`, on the entire orbit carrier

\[
 gD(X)\le G(X)
 \quad\Longleftrightarrow\quad
 mD(X)\le M(X).
 \tag{9}
\]

Thus the actual Fin 4 normalized slice has **one** scalar passport density,
not two independent ones.  The gain coordinate remains important as literal
source provenance, but it imposes no second geometric constraint.

## 2. Exact prefix ledger at a slice minimizer

Let `Q` minimize whole debt on the single-density slice and write

\[
 D=D(Q),\qquad M=M(Q),\qquad
 s:=M-mD\ge0.
 \tag{10}
\]

For a product root `q`, let

\[
 c=c(q),\qquad a=1-c,
 \qquad R=R(q;B(Q))
 \tag{11}
\]

be its joint Continue mass, absorption, and total root Nash defect against
the whole cap of `Q`.  The checked prefix identities give

\[
 D(q*Q)=cD+R,qquad M(q*Q)=cM.
 \tag{12}
\]

The tail coordinate remains fixed, and prefix closure keeps `q*Q` in the
decorated orbit carrier.  Consequently `q*Q` remains in the normalized slice
if and only if

\[
 m(cD+R)\le cM,
\]

or equivalently

\[
 \boxed{mR\le cs.}
 \tag{13}
\]

Whenever (13) holds, minimality of `Q` and (12) imply

\[
 D\le cD+R,
\]

hence

\[
 \boxed{R\ge aD.}
 \tag{14}
\]

This is an exact variational inequality.  It uses arbitrary roots, not only
exact cap--Nash roots.

There is also a useful global form.  If (13) fails, then
`R>cs/m`.  Splitting on feasibility therefore gives, for every root,

\[
 \boxed{
 R(q;B(Q))\ge
 \min\left\{D(Q)\operatorname{Abs}(q),
 \frac{\operatorname{Cont}(q)[M(Q)-mD(Q)]}{m}\right\}.}
 \tag{14a}
\]

At full absorption the second term is zero, so this statement does not claim
a spurious positive toll.  Below the crossing radius `s/M`, its first term is
the active one and yields the sharper statement in the next section.

## 3. Saturation or an explicit linear absorption toll

The strict inert conclusion supplies `D>D_*>0`, while slice membership and
`m>0` give `M>=mD>0`.  Suppose first that `s>0`, and let `q` be any root with

\[
 a=\operatorname{Abs}(q)\le \frac{s}{M}.
 \tag{15}
\]

If `R<aD`, then

\[
 mR<maD\le (1-a)s=cs.
 \tag{16}
\]

The middle inequality is exactly

\[
 a(mD+s)=aM\le s.
\]

Thus (13) holds, so `q*Q` belongs to the normalized slice, while
`D(q*Q)=cD+R<D`, contradicting minimality.  We have proved the explicit
bound

\[
 \boxed{
 \operatorname{Abs}(q)\le\frac{M-mD}{M}
 \Longrightarrow
 R(q;B(Q))\ge D(Q)\operatorname{Abs}(q).}
 \tag{17}
\]

This includes the edge cases.  If `a=0`, the right side is zero and root
defect is nonnegative.  If `c=0`, condition (15) cannot hold because
`s/M<1` (as `mD>0`).  No division by `c` is used.

If `s=0`, the density is saturated.  We have therefore proved:

\[
 \boxed{
 M(Q)=mD(Q)
 \quad\lor\quad
 \forall q,\ 
 \operatorname{Abs}(q)\le\frac{M(Q)-mD(Q)}{M(Q)}
 \Rightarrow
 R(q;B(Q))\ge D(Q)\operatorname{Abs}(q).}
 \tag{18}
\]

By (6), (8), and (9), the saturated arm simultaneously says

\[
 G(Q)=gD(Q).
 \tag{19}
\]

An equivalent useful contrapositive is:

> If roots `q_n -> C` have positive absorption and
> `R(q_n;B(Q))/Abs(q_n) -> 0`, then the forced-pair passport is saturated at
> `Q` in both its mass and gain coordinates.  Indeed, the absorptions
> eventually lie below the fixed positive radius in (17).

Thus the familiar sublinear-defect root regressions cannot occur at a
strictly slack normalized inert point.  Unique-root rigidity alone does not
give (17); normalized-slice minimality plus density slack is essential.

## 4. Canonical saturation loses at least half the seed mass

The passport limit `P` itself lies in the slice, so minimality gives

\[
 D(Q)\le D_P.
 \tag{20}
\]

If the canonical density (7) is saturated at `Q`, then

\[
 M(Q)=mD(Q)
 \le \frac{M_P}{2D_P}D_P
 =\frac{M_P}{2}.
 \tag{21}
\]

Using (6) gives the identical gain estimate

\[
 G(Q)\le\frac{G_P}{2}.
 \tag{22}
\]

In fact saturation gives the exact proportionality

\[
 \boxed{
 \frac{M(Q)}{M_P}
 =\frac{G(Q)}{G_P}
 =\frac{D(Q)}{2D_P}.}
 \tag{22a}
\]

All denominators are positive.  The half-loss inequalities are precisely
the consequence of (22a) and `D(Q)<=D_P`.

Hence the exact remaining local alternatives can be written

\[
 \boxed{
 \begin{array}{ll}
 \textbf{passport loss:}&
 M(Q)\le M_P/2\ \text{and}\ G(Q)\le G_P/2,\\[1mm]
 \textbf{linear root toll:}&
 R(q;B(Q))\ge D(Q)\operatorname{Abs}(q)
 \ \text{if }\operatorname{Abs}(q)\le
 (M(Q)-mD(Q))/M(Q).
 \end{array}}
 \tag{23}
\]

The first arm records exact density saturation, not merely the displayed
upper bounds.

## 5. Letting the single density tend to zero

The single-density form permits one further exhaustive limit which is hidden
by the canonical half-density statement.

Put

\[
 r_0:=\frac{M_P}{D_P}>0,
 \qquad m_n:=\frac{r_0}{n+2},
 \qquad g_n:=\Delta m_n.
 \tag{24}
\]

The passport `P` is strictly feasible for every `(m_n,g_n)`.  Select a
whole-debt minimizer `Q_n` on each corresponding normalized slice.  If some
`D(Q_n)=D_*`, the checked positive-density actualizer and three-role
regeneration/ascent mechanism apply, so suppose every selected arm is strict.

Write

\[
 D_n=D(Q_n),\qquad M_n=M(Q_n),
 \qquad u_n:=\frac{m_nD_n}{M_n}\in(0,1].
 \tag{25}
\]

Here `M_n>0` follows from `M_n>=m_nD_n` and `D_n>D_*>0`.  Compactness gives a
subsequence `Q_n -> Q_infty`; all its points remain in the same closed
arbitrary-prefix carrier and fixed minimum-tail-debt fibre.

There are two numerical cases.

### 5.1 Nonvanishing normalized utilization

If, after a subsequence, `u_n>=epsilon>0`, then boundedness of `D_n` gives

\[
 0\le M_n\le\frac{m_nD_n}{\varepsilon}\longrightarrow0.
 \tag{26}
\]

Therefore

\[
 M(Q_\infty)=G(Q_\infty)=0.
 \tag{27}
\]

This is the exact vanishing-passport boundary.  It does not retain a causal
atom or paid-gain floor.

### 5.2 Vanishing normalized utilization

Otherwise pass to a subsequence with `u_n -> 0`.  The absorption radius from
(17) is

\[
 \frac{M_n-m_nD_n}{M_n}=1-u_n\longrightarrow1.
 \tag{28}
\]

Fix a product root `q` with `Abs(q)<1`.  Eventually its absorption lies below
this radius, so (17) gives

\[
 R(q;B(Q_n))\ge D_n\operatorname{Abs}(q).
\]

Continuity of the cap coordinate and root defect yields

\[
 R(q;B(Q_\infty))\ge
 D(Q_\infty)\operatorname{Abs}(q).
\]

For a root of absorption one, mix each individual action with an arbitrarily
small probability of pure Continue.  The resulting product roots have
absorption below one and converge to the original root.  A second continuity
limit proves the same inequality at absorption one.  Hence

\[
 \boxed{
 \forall q,\qquad
 R(q;B(Q_\infty))\ge
 D(Q_\infty)\operatorname{Abs}(q).}
 \tag{29}
\]

This is a global one-step Bellman barrier, not merely unique exact-root
rigidity.  It says every arbitrary prefix at this fixed decorated point has
whole debt at least the starting debt:

\[
 D(q*Q_\infty)
 =(1-\operatorname{Abs}(q))D(Q_\infty)+R(q;B(Q_\infty))
 \ge D(Q_\infty).
 \tag{30}
\]

If a cluster point in either construction has `D(Q_infty)=D_*` and
`M(Q_infty)>0`, it is not a new residual.  Choose, for example,

\[
 m'=\frac{M(Q_\infty)}{2D_*},\qquad g'=\Delta m'>0.
\]

Then `Q_infty` is strictly feasible in a positive-density slice and is a
minimizer there by global minimality.  The checked equality-arm actualizer
applies.  Thus the exact density-to-zero alternative is:

\[
 \boxed{
 \begin{array}{l}
 \text{positive-density minimum return},\quad\text{or}\\
 \text{vanishing marked mass and gain},\quad\text{or}\\
 \text{the global fixed-cap barrier (29).}
 \end{array}}
 \tag{31}
\]

The alternatives need not be disjoint; a minimum-return cluster is consumed
first whenever its marked mass is positive.

## 6. Neither boundary currently feeds a compiler

### 6.1 Saturation gives an off-minimum actualizer, not a return

At a saturated strict point, `M=mD>0` and `G=Delta M>0`.  Since the point lies
in the orbit closure, raw source-attached descendants converge to it with
uniform positive marked-mass and gain floors after discarding finitely many
terms.  Thus saturation does have an actualizer in the elementary topological
sense.

But its whole debts converge to `D(Q)>D_*`.  The checked
`QuittingMarkedPairMinimumReturnActualizer` requires the additional equality
`D(Q)=D_*` before it yields the concentrated minimum-return consumer.  The
density equality supplies no such debt equality.  Spending the horizontal
gain still sets the remaining gain coordinate to zero, so the target leaves
every positive-gain density slice.  Therefore saturation produces neither a
boundary return nor horizontal invariance.

### 6.2 The toll has the wrong sign for cumulative charge

The cumulative near-return compilers consume exact punishment-floor edges
whose absorption is useful charge and whose Bellman/Nash error is zero (or is
controlled by a separately vanishing budget).  Inequality (29) says the
opposite: at the unchanged cap, absorption forces at least proportional
positive Nash error.  In particular, for any finite family of roots all
tested against this same cap,

\[
 D(Q_\infty)\sum_t\operatorname{Abs}(q_t)
 \le\sum_t R(q_t;B(Q_\infty)).
 \tag{32}
\]

Consequently a vanishing aggregate root-error budget forces vanishing total
absorption.  This cannot supply the positive cumulative charge required by
the existing compiler.  Equation (32) is deliberately a fixed-cap statement;
it does not pretend that successor-linked displayed caps remain equal to
`B(Q_infty)`.

### 6.3 Exact Fin 4 regression for the barrier interface

The global barrier is consistent with an actual finite quitting game and an
actual positive-debt semantic point.  Let `I=Fin 4` and define

\[
 r_i(S)=
 \begin{cases}
 -1,&i\in S,\\
 0,&i\notin S.
 \end{cases}
 \tag{33}
\]

Let `Q` be the profile in which player `0` Quits surely at date zero and all
others Continue.  Then

\[
 U(Q)=(-1,0,0,0),\qquad B(Q)=(0,0,0,0),
 \qquad D(Q)=1.
 \tag{34}
\]

Against the cap `B(Q)=0`, player `i`'s pure Quit value is always `-1` and its
pure Continue value is always `0`, for every product root.  If `x_i` is its
Quit probability, its exact coordinate root defect is `x_i`.  Hence

\[
 R(q;B(Q))=\sum_i x_i
 \ge 1-\prod_i(1-x_i)
 =\operatorname{Abs}(q)
 =D(Q)\operatorname{Abs}(q).
 \tag{35}
\]

All Continue is the unique exact root.  Nevertheless all-Never is an exact
terminal Nash profile, so the global minimum debt of this table is zero.
This is not a counterexample and does not reproduce the positive forced-pair
gain.  It is a minimal exact regression showing that the global barrier
interface itself is a stall certificate, not a terminal or cumulative-return
consumer.  Any contradiction must use the retained positive-minimum
forced-pair provenance beyond (29).

## 7. What this does and does not consume

This result rules out a proposed third behavior: a strictly slack passport
minimizer admitting arbitrarily small absorbing repairs whose defect is
sublinear in absorption.  It also shows that the generic gain/mass
two-coordinate passport overstates the dimensionality of the actual
forced-pair node.

Neither arm is yet a terminal consumer:

* The toll `R >= aD` is root Nash error, not admissible chronological charge.
  Repeating such roots accumulates error rather than compiling a return.
* Halving a positive real mass is not a well-founded finite rank.  It can
  occur indefinitely with masses tending to zero.
* `Q` lies in the closed arbitrary-prefix carrier and need not be attained.
  Equations (21)--(22) do not themselves regenerate an actual minimum source.
* The historical horizontal paid move sends its remaining gain to zero and
  therefore still exits every positive-density slice.

The next concrete target is correspondingly smaller:

\[
 \boxed{
 \text{consume a saturated single-density inert passport, or convert the
 linear root toll (17) into an executable finite obstruction.}}
\]

## Checked declarations and files used

* `FinFourOwnerCompressedMinimumReturnForcedPairBase.pureSingleton_stageMass_eq_liveMass`,
  `forcedPair_stageMass_eq_liveMass`, `forcedAction_eq_true`,
  `terminalGap_le_forcedOwnerDefect`, and
  `lambda_mul_terminalGap_le_forcedOwnerGain` in
  `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`;
* `QuittingStageAtomConcentratedPacketAdapter.sourceToTargetGain_eq_liveMass_mul_defect`
  in `Research/Quitting/PositiveStageAtomConcentratedPacket.lean`;
* `QuittingMarkedPairDecoratedFamily.rawDecoration_markedMass_eq_prefixSurvival_mul`,
  `rawDecoration_actualGain_eq_prefixSurvival_mul`,
  `prefixMap_wholeDebt_eq_continueMass_mul_add_capDefect`, and
  `prefixMap_mem_carrier` in
  `Research/Quitting/NormalizedPassportPrefixOrbit.lean` and
  `Research/Quitting/NormalizedPassportMinimizer.lean`;
* `FinFourNormalizedReturnSelection.massDensity`, `gainDensity`, and
  `FinFourOwnerCompressedMinimumReturnForcedPairPacket.nonempty_normalizedReturnThreeRole_or_strictInert`
  in `Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean`.

No Lean declaration for (6), (18), (23), or the density-to-zero alternative
(31) is claimed here.
