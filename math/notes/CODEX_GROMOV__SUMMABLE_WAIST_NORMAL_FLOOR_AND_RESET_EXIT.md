# Normal-floor collapse and an exact reset exit from the summable waist

Author: CODEX_GROMOV

## Status

**Ordinary mathematics, not Lean-checked.** Two concrete reductions survive
an adversarial attack on the common summable exact-tail waist.

1. In an all-normal quitting game, a bounded summable exact Nash--Bellman
   tail cannot contain a punishment-floor violation. Thus the checked
   under-floor summability theorem collapses the under-floor horn completely
   in the Fin4 all-normal hard residual; only the floor-safe summable waist
   remains.
2. In the nested terminal-cap-child genealogy, the infinite front-reset arm
   does more than produce negative payoff holonomy. Cofinally, every exact
   product Nash root against the actual child payoff causes a uniformly
   positive semantic-debt drop and has uniformly positive joint absorption.
   Hence that arm supplies literal one-step exact Nash--Bellman exits and
   stays a fixed distance off the global minimum fibre.

The second result is not renewable after the prefix: the resulting child need
not carry the nested cap-clock genealogy. The eventual shifted-cap arm also
remains open. Therefore this note does not consume the whole waist or prove
Fin4 uniform equilibrium.

## Question

Can summability, all-player punishment normality, and the fixed-debtor nested
cap child turn either cap-clock arm into an exact charged chronology or a
renewable finite rank?

## Checked sources inspected

- quittingPunishmentValue_sub_le_continueMass_mul_of_nashBellmanEdge,
  quittingDynamicDebtTail_floorViolation_mono, and
  summable_dynamicDebtTailAbsorptionCharge_of_floorViolation_of_positiveDebt
  in
  UniformEquilibrium/Quitting/Debt/Dynamic/PunishmentFloorViolation.lean;
- QuittingTerminalExploitabilityWitness.exists_terminalGapDynamicDebtTail_summableAbsorption
  in UniformEquilibrium/Diagnostics/Quitting/Debt/ViolationCollapse.lean;
- quittingTerminalSemanticDebt_prefix_eq_blockAct and
  quittingTerminalSemanticDebt_prefix_le in
  UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean;
- finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff
  in
  UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean.

The nested genealogy and signed-holonomy input are the independently reviewed
notes
CODEX_SPINOZA__NESTED_TERMINAL_CAP_CHILD_FIXED_DEBTOR_TRANSPORT and
CODEX_SPINOZA__SIGNED_CAP_CHILD_HOLONOMY_AND_RESET_DICHOTOMY.

## 1. A summable exact tail cannot violate a normal player's floor

Let \(I\) be finite. Let

\[
 (v_t,x_t)_{t\ge0}
\]

be a bounded exact Nash--Bellman tail:

\[
 v_t=F_{x_t}(v_{t+1}),
 \qquad x_t\text{ is exact root Nash against }v_{t+1}.
\]

Write

\[
 a_t=1-\Pr_{x_t}(\text{all Continue}).
\]

Assume \(\sum_t a_t<\infty\). Then no normal player \(i\), meaning

\[
 \chi_i\le r_i(\{i\}),
\]

can satisfy \(v_T(i)<\chi_i\) at any date \(T\).

### Proof

If all rewards and displayed values have absolute value at most \(M\), the
Bellman identity gives

\[
 \lVert v_t-v_{t+1}\rVert_\infty\le2Ma_t.                 \tag{1}
\]

Hence \(v_t\to v_\infty\). Also every marginal Quit probability is at most
\(a_t\), so \(x_t\to\mathbf C\), the all-Continue root. Closedness of exact
root Nash gives

\[
 r_i(\{i\})\le v_\infty(i)                                \tag{2}
\]

for every player \(i\).

If \(v_T(i)<\chi_i\), checked floor-violation propagation says that the same
coordinate remains below the floor and is nonincreasing:

\[
 v_t(i)\le v_T(i)<\chi_i\qquad(t\ge T).                    \tag{3}
\]

Taking limits and using normality gives

\[
 v_\infty(i)<\chi_i\le r_i(\{i\}),                         \tag{4}
\]

contradicting (2).

Thus every bounded summable exact tail in an all-normal game is
coordinatewise floor-safe at every date. Combining this with the checked
violation-collapse theorem shows that the under-floor horn cannot occur in
the Fin4 all-normal counterexample residual: a violation first implies
summability, and summability then contradicts normality.

This does not consume the remaining floor-safe summable tail. Its limit is
the familiar all-Continue phantom, and the actual paid source can still move
to temporal infinity.

## 2. Infinite cap resets cross the singleton wall

Use the nested child notation

\[
 \tau^{n+1}=q^n::\tau^n,
 \qquad
 \zeta^{n+1}=\bar q^n::\zeta^n,
\]

and write

\[
 U^n=U(\tau^n),\qquad W^n=U(\zeta^n),\qquad
 \Delta_i^n=W_i^n-U_i^n.
\]

Suppose the fixed outsider \(j\ne b\) has

\[
 d_j(\zeta^n)\ge\delta>0
\]

at every sufficiently large depth. In the infinite-reset arm, the reviewed
signed-holonomy theorem also gives
\(\Delta_j^\infty\le-\delta/2\). The singleton-wall conclusion below uses
the stronger reset endpoint equation directly, not that displacement sign.

At a reset from depth \(n\) to \(n+1\), Quit0 attains \(j\)'s complete cap.
If \(\bar E_n\) is Quit payoff minus Continue payoff at the barred root, the
exact mixture identity and debt floor give

\[
 d_j(\zeta^{n+1})=(1-h_{n,j})\bar E_n\ge\delta,
 \qquad \bar E_n\ge\delta.                                 \tag{5}
\]

The barred hazards tend to zero and \(W^n\) converges, by the exact affine
recurrence and summability of the marginal hazards. Hence along the infinite
reset subsequence

\[
 \bar E_n\longrightarrow r_j(\{j\})-W_j^\infty.
\]

Taking limits in (5) gives

\[
 W_j^\infty\le r_j(\{j\})-\delta.                          \tag{6}
\]

After increasing the reset depth, therefore,

\[
 W_j^n\le r_j(\{j\})-\delta/2.                             \tag{7}
\]

Thus the reset itself pushes the actual child payoff a fixed distance through
player \(j\)'s singleton wall. Negative holonomy alone would not imply this,
because \(U_j^\infty\) may lie strictly above the singleton reward.

## 3. Singleton-wall separation forces exact debt expenditure

The following quantitative lemma is game-independent.

Let \(y=(W,B)\) be an actual terminal-semantic carrier point with rewards and
\(W\) bounded in absolute value by \(M>0\). Suppose for one player \(j\)

\[
 d_j(y)\ge d_0>0,
 \qquad
 W_j\le r_j(\{j\})-\varepsilon
\]

with \(\varepsilon>0\). Let \(x\) be any exact product Nash root against
\(W\), put \(y'=T_xy\), and write \(A(x)\) for its joint absorption
probability. Then

\[
 D(y)-D(y')\ge
 c(d_0,\varepsilon,M)>0,                                  \tag{8}
\]

where one valid constant is

\[
 c(d_0,\varepsilon,M)
 =\min\left\{
 d_0,\frac{\varepsilon}{2},
 \frac{\varepsilon d_0}{8M}
 \right\}.                                                 \tag{9}
\]

Moreover,

\[
 A(x)\ge\min\left\{1,\frac{\varepsilon}{8M}\right\}.       \tag{10}
\]

### Proof

Let \(s_j(x)\) be the probability that all opponents of \(j\) Continue and
put \(a=1-s_j(x)\). Write \(E_j(x;W)\) for Quit payoff minus Continue payoff.
At all Continue,

\[
 E_j(\mathbf C;W)=r_j(\{j\})-W_j\ge\varepsilon.            \tag{11}
\]

Couple the opponent root with all Continue. On the event that some opponent
Quits, of probability \(a\), each of the Quit and Continue endpoint values
changes by at most \(2M\). Hence

\[
 |E_j(x;W)-E_j(\mathbf C;W)|\le4Ma.                        \tag{12}
\]

The checked exact debt action is

\[
 d_j(y')=
 \left[s_j(x)d_j(y)-\max\{E_j(x;W),0\}\right]_+.           \tag{13}
\]

If \(a\ge\varepsilon/(8M)\), (13) gives

\[
 d_j(y)-d_j(y')\ge a\,d_j(y)
 \ge\frac{\varepsilon d_0}{8M}.                            \tag{14}
\]

If \(a<\varepsilon/(8M)\), (11)--(12) give

\[
 E_j(x;W)>\varepsilon/2,
\]

and (13) gives

\[
 d_j(y)-d_j(y')\ge\min\{d_0,\varepsilon/2\}.              \tag{15}
\]

Every other coordinate debt weakly decreases under an exact prefix. This is
coordinatewise quittingTerminalSemanticDebt_prefix_le, applied to the actual
carrier pair and the exact root. Summing (14)--(15) therefore proves
(8)--(9); the positive loss in coordinate \(j\) cannot be offset by another
coordinate.

For the absorption assertion, the first case has
\(A(x)\ge a\ge\varepsilon/(8M)\). In the second case the strict inequality
\(E_j(x;W)>0\) and exact root Nash force player \(j\) to Quit surely:
positive Continue probability would require Quit to be no better than
Continue. Hence \(A(x)=1\). This proves (10), including the harmless case
\(\varepsilon/(8M)>1\), when the first case is empty.

## 4. Consequence for the infinite-reset arm

At every sufficiently late reset child, take \(d_0=\delta\) and, using (7),
\(\varepsilon=\delta/2\). Finite-game Nash existence supplies an exact root
against its actual payoff. Prefixing that root gives a literal actual
Nash--Bellman edge and decreases total terminal debt by at least

\[
 c_\delta
 =\min\left\{
 \delta,\frac{\delta}{4},\frac{\delta^2}{16M}
 \right\}>0,                                              \tag{16}
\]

and its joint absorption is at least

\[
 a_\delta=\min\left\{1,\frac{\delta}{16M}\right\}>0.       \tag{17}
\]

In particular, if \(D_*\) is the global minimum debt, every sufficiently
late reset child satisfies

\[
 D(\zeta^n)\ge D_*+c_\delta.                               \tag{18}
\]

Otherwise its exact prefix would lie below the global minimum. Thus infinite
front resets cannot lie in, or converge to, the minimum fibre. They produce a
uniformly charged exact temporal exit into the quantitative-debt-descendant
arm.

This is genuine temporal information: unlike the reset itself, the edge in
(16)--(17) is an exact Nash--Bellman prefix on the literal child with both
fixed debt expenditure and fixed physical absorption. It does not yet
solve the project because the descendant need not retain the nested
cap-child passport, so (15) is not presently renewable.

## 5. Surviving obstruction

After these reductions, the two unresolved objects are:

1. the floor-safe summable all-Continue port, where the paid source stays at
   positive far-end reach but escapes every finite front window; and
2. the eventual shifted-cap arm, where both the owner clock and one fixed
   outsider cap are attached to one fixed far suffix, but the intervening
   barred roots have an order-one outsider Nash seam.

The infinite-reset arm no longer belongs to the static-toggle residual: it
has the exact temporal debt-expenditure/absorption edge (16)--(17). Closing the game still
requires either regeneration of the nested passport after that edge or a
consumer for the eventual shifted two-cap packet.

## Next check

In the eventual shifted-cap arm, install the fixed outsider cap already at
the base child and transport the resulting two-cap terminal profile through
the common outer word. Determine whether the two simultaneous far-end cap
updates force a second singleton-wall crossing for one of the two owners, or
whether a four-player reward table can keep every outer root gap bounded away
from such a crossing while satisfying the positive terminal gap.
