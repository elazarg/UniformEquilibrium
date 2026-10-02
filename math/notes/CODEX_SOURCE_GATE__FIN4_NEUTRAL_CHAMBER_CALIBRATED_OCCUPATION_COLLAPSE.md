# Calibrated occupation collapse at a strict neutral cap chamber

**Author:** `CODEX_SOURCE_GATE`  
**Status:** ordinary mathematics proved; source-faithful finite neutral towers
proved; no strict-chamber consumer obtained  
**Date:** 2026-08-30

## 1. Question and answer

This note tests the strict \(p\)-zero, unique-all-Continue output of the
law-tight cap--Nash saturation construction using invariant occupation,
Conley recurrence, viability, and calibrated-subaction ideas.

The test has a sharp answer.  For the **literal chronological orientation**
of an exact cap-prefix edge, total terminal debt already supplies the optimal
calibrated subaction.  If an executable source is obtained by placing an
exact cap--Nash root \(x\) before a continuation, then

\[
 \text{source}=x\triangleright\text{tail},
 \qquad D(\text{source})=q(x)D(\text{tail}),
 \tag{1}
\]

where \(q(x)\) is joint Continue mass.  On a positive-debt carrier, put

\[
 a(x)=1-q(x),\qquad \Phi(z)=-\log D(z).
\]

Then every literal chronological edge \(e\), oriented from source to tail,
satisfies

\[
 \boxed{
 a(e)+\Phi(t(e))-\Phi(s(e))
 =1-q(e)+\log q(e)\le0.}
 \tag{2}
\]

Equality holds exactly at all Continue.  Consequently:

1. every invariant occupation of the compact exact cap-prefix relation has
   zero joint-absorption mean and is supported on semantic self-loops;
2. the invariant-flow optimization value for joint absorption is exactly
   zero, and \(-\log D\) attains its continuous dual;
3. every finite exact cap-prefix return whose source and tail approach the
   same positive-debt state has **vanishing total absorption charge**; and
4. a unique-all-Continue carrier point is a viable neutral fixed point, not
   a state from which Conley or Lyapunov theory forces an exit.

This is not merely a horizontal carrier artifact.  Every joint-carrier point
with unique all-Continue cap root is approximated by arbitrarily deep
**literal, composable, executable** exact cap--Nash blocks all of whose
semantic/law states approach that point and whose total absorption tends to
zero.  If the point has \(d_p=0\) and a positive finite atom, the blocks have
\(p\)-debt tending to zero and retain a uniform positive amount of that same
terminal atom.

Thus the strict chamber does produce a source-provenant invariant occupation,
but it is precisely the neutral Dirac occupation.  It yields neither a
charged near-return nor a renewable finite rank.  To consume the chamber one
must introduce a chronological edge or charge not already priced by the
exact cap-debt cocycle, or prove a terminal theorem directly at the neutral
point.

No explicit positive-global-gap reward table is constructed.  Constructing
one would settle the conjecture negatively.  A checked Fin4 rational table
does realize all the **local** neutral dynamics, including arbitrary-depth
literal neutral towers and positive local debt, while its global minimum is
zero.  The positive-minimum hard-residual premise is therefore kept distinct
from local realizability.

No Lean file or export was changed.

## 2. Exact source boundary

The architecture targets read were:

- `arch/CHRONOLOGICAL_OCCUPATION_DUALITY.md`; and
- `arch/FIN4_NEUTRAL_CHRONOLOGY.md`.

The following checked declarations are the narrow source interface used
below.

### Joint carrier, exact roots, and continuity

- `quittingTerminalSemanticLawCarrier_isCompact`,
  `quittingTerminalSemanticLawPoint_mem_carrier`,
  `quittingTerminalSemanticLawPrefix_mem_carrier`, and
  `quittingTerminalOutcomeLawPrefix_outcomeMass` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`;
- `isClosed_isεQuittingRootEndpointNash_simplex`,
  `isεQuittingRootEndpointNash_of_tendsto`, and
  `isCompact_and_nonempty_setOf_isZeroQuittingRootEndpointNash_root` in
  `UniformEquilibrium/Quitting/Bellman/Finite/EndpointNashClosed.lean`; and
- `continuous_quittingTerminalSemanticPrefixSimplex` in
  `UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedSemanticCarrier.lean`.

The complete-law prefix is given by a finite family of polynomial formulas
in the simplex-root and law coordinates, so it is jointly continuous as
well.  The existing fixed-root continuity theorem is
`continuous_quittingTerminalOutcomeLawPrefix`; joint continuity in the root
is the same finite-coordinate calculation and is used here as ordinary
mathematics, not claimed as a named Lean declaration.

### Debt scaling and literal stacks

- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
- `exists_quittingCapNashRootStack`,
  `quittingTerminalDebtSum_capNashRootStack_eq`,
  `abs_quittingTerminalPayoff_rootStack_sub_terminal_le`, and
  `abs_quittingContinuationBestResponseValue_capNashRootStack_sub_terminal_le`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean`; and
- `capNashStack_absorptionSum_le_log_debtRatio` in the same file.  That
  checked theorem uses the global literal infimum.  Proposition 4 below uses
  the sharper endpoint ratio obtained directly from exact product scaling.

### Saturation minimum and local regressions

- `quittingLawTightCapNashSaturationMinimumFace_rootNash_iff_allContinue`,
  `quittingLawTightCapNashSaturationMinimumFace_allContinue_prefix_eq`, and
  the finite-chain absorption bounds in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashMinimumFace.lean`;
- `QuittingResetIncidenceCapRegression.positive_incidence_and_toggle_but_only_allContinue_capNash`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`; and
- `FourPlayerCyclicPlateauCandidate.phase_debt`, `phase_debtSum`,
  `phase_terminalOutcomeMass_eq_one`, `phase_cap`,
  `phaseZero_allContinue_exactCapNash`, `exactCapNash_forces_allContinue`,
  `root_not_exactCapNash`, and
  `zeroPair_debtSum_eq_zero` in
  `Research/Quitting/FourPlayerCyclicPlateauCandidate.lean`.

The reviewed ordinary-mathematics strict Fin4 classification is in
`exports/LAW_TIGHT_CAP_NASH_SATURATION_HULL.md`.  Only its strict chamber is
being analyzed; no new claim is made that the classification is Lean-checked
beyond the generic hull and minimum-face declarations just listed.

No literature theorem is invoked.

## 3. The actual chronological edge relation

Let \(I\) be finite, \(r\) a quitting reward table, and let

\[
 \mathcal C=
 \operatorname{quittingTerminalSemanticLawCarrier}(r).
\]

A state \(z=(X,\mu)\) stores a terminal semantic pair \(X=(u,c)\) and a
complete time-forgetting terminal-outcome law \(\mu\).  Put

\[
 d_i(z)=c_i-u_i,\qquad D(z)=\sum_i d_i(z).
\]

Assume throughout Sections 3--7 that a fixed \(\delta>0\) satisfies

\[
 D(z)\ge\delta\qquad(z\in\mathcal C).
 \tag{3}
\]

In the Fin4 hard-residual application one takes
\(\delta=D_*>0\).

Use simplex coordinates for a product root.  Define the compact exact-edge
space

\[
 \mathcal E=
 \left\{(s,x,t):
  t\in\mathcal C,
   x\text{ is exact Nash against }t.1.2,
   s=P_x t
 \right\}.
 \tag{4}
\]

The orientation in (4) is important:

\[
 s=x\triangleright t\longrightarrow t.
 \tag{5}
\]

It is the chronological direction from the executable prefixed source to its
displayed continuation.  The saturation construction generates the same
edge by starting with \(t\) and closing under \(t\mapsto P_xt\); that is a
backward **construction** convention, not a reverse chronological edge.

The domain in \(\mathcal C\times\) root-simplex on which \(x\) is exact is
closed.  Joint continuity of the semantic and law prefix maps therefore
makes \(\mathcal E\) compact.  Prefix-carrier invariance puts \(s\) back in
\(\mathcal C\).

Every edge is the finite-dimensional image of the literal operation

\[
 \sigma\mapsto x\triangleright\sigma.
\]

A carrier edge need not have one actual tail realizing its exact displayed
cap.  Proposition 5 below separately proves the stronger literal-block
actualization needed at the neutral chamber; compactness alone is not used as
a source decoder.

## 4. Exact calibrated dissipativity

### Proposition 4.1 (calibrated cap-debt subaction)

For \(e=(s,x,t)\in\mathcal E\), let

\[
 q(e)=\operatorname{quittingStationaryContinueMass}(x),
 \qquad a(e)=1-q(e).
\]

Then \(q(e)>0\), and the continuous function

\[
 \Phi(z)=-\log D(z)
\]

satisfies

\[
 a(e)+\Phi(t(e))-\Phi(s(e))\le0.             \tag{6}
\]

Equality holds if and only if \(x\) is all Continue; in that case \(s=t\).

#### Proof

Exact cap--Nash scaling gives every coordinate identity

\[
 d_i(s)=q(e)d_i(t),
\]

and hence

\[
 D(s)=q(e)D(t).                              \tag{7}
\]

Both debts are at least \(\delta>0\), so \(q(e)>0\).  Taking logarithms in
(7) gives

\[
 \Phi(t)-\Phi(s)=\log q(e).
\]

Thus the left side of (6) is

\[
 1-q+\log q\le0,
\]

with equality exactly at \(q=1\).  A finite product root has joint Continue
mass one exactly when every marginal is pure Continue.  Since this
all-Continue root is exact at \(t\), the checked semantic identity theorem
and the elementary law-prefix formula give \(P_xt=t\).  QED.

### Proposition 4.2 (occupation collapse)

Let \(\pi\) be a Borel probability on \(\mathcal E\) whose source and target
marginals agree:

\[
 s_\#\pi=t_\#\pi.                            \tag{8}
\]

Then

\[
 \int_{\mathcal E}a\,d\pi=0,                \tag{9}
\]

and \(\pi\) is supported on all-Continue semantic self-loops.

#### Proof

Invariance and continuity of \(\Phi\) give

\[
 \int(\Phi\circ t-\Phi\circ s)\,d\pi=0.
\]

Integrating (6) gives \(\int a\,d\pi\le0\).  Since \(a\ge0\), (9) follows.
The zero integral of the continuous nonnegative function \(a\) puts the
support in \(a=0\), and Proposition 4.1 identifies those edges as the
all-Continue diagonal.  `QED`

### Corollary 4.3 (exact occupation dual value)

Suppose the edge space contains one all-Continue self-loop, as it does at
every saturation-minimum point.  For the unconstrained occupation duality of
`CHRONOLOGICAL_OCCUPATION_DUALITY.md`,

\[
 \max_{s_\#\pi=t_\#\pi}\int a\,d\pi
 =\inf_{f\in C(\mathcal C)}
   \max_{e\in\mathcal E}
    \bigl(a(e)+f(t(e))-f(s(e))\bigr)
 =0.                                           \tag{10}
\]

The function \(f=\Phi=-\log D\) attains the right-hand value.  The neutral
Dirac occupation attains the left-hand value.

This is stronger than saying that the positive-mean occupation producer has
not been found.  Positive invariant joint-absorption mean is impossible in
this exact edge system.

## 5. Literal neutral-tower actualization

The preceding occupation theorem is carrier-level.  The next result supplies
the literal chronological provenance required by the architecture files.

For an executable profile \(\sigma\), write

\[
 Z(\sigma)=
 \bigl(
  \operatorname{quittingTerminalSemanticPair}(r,\sigma),
  \operatorname{quittingTerminalOutcomeMass}(r,\sigma)
 \bigr).
\]

### Proposition 5.1 (fixed-depth neutralization)

Let \(z\in\mathcal C\) and assume that all Continue is the unique exact
cap--Nash root against \(z.1.2\).  Let
\(\tau_n\) be any realizing sequence with \(Z(\tau_n)\to z\).

Fix \(L<\infty\).  For every \(n\), recursively choose an exact root
\(x_{n,k}\) and executable profile \(\tau_{n,k+1}\) by

\[
 \tau_{n,0}=\tau_n,
 \qquad
 x_{n,k}\text{ exact against the cap of }\tau_{n,k},
 \qquad
 \tau_{n,k+1}=x_{n,k}\triangleright\tau_{n,k}
 \tag{11}
\]

for \(0\le k<L\).  After passage to a subsequence,

\[
 \max_{0\le k\le L}d\bigl(Z(\tau_{n,k}),z\bigr)\longrightarrow0,
 \tag{12}
\]

and every one of the \(L\) root sequences converges to all Continue.

#### Proof

The root simplex is compact.  Extract a convergent subsequence of
\(x_{n,0}\).  Closedness of exact endpoint Nash and convergence of the tail
caps show that its limit is exact at \(z.1.2\).  Root uniqueness makes the
limit all Continue.  Joint continuity of semantic prefixing and of the
finite-coordinate law prefix then gives

\[
 Z(\tau_{n,1})\to P_{\mathrm{AC}}z=z.
\]

Repeat this argument for \(k=1,\ldots,L-1\), retaining one finite diagonal
subsequence.  Every profile in (11) is literal and executable, and every
displayed edge

\[
 \tau_{n,k+1}\longrightarrow\tau_{n,k}
\]

uses the exact cap of its actual displayed tail.  QED.

### Proposition 5.2 (arbitrarily deep vanishing-charge towers)

Under the assumptions of Proposition 5.1 there are blocks of lengths
\(L_m\to\infty\), with actual profiles

\[
 \tau^{m}_{L_m}\longrightarrow\tau^{m}_{L_m-1}\longrightarrow
 \cdots\longrightarrow\tau^{m}_0,             \tag{13}
\]

and exact cap roots \(x^m_k\) such that

\[
 \max_{k\le L_m}d\bigl(Z(\tau^m_k),z\bigr)\to0,
 \qquad
 \sum_{k<L_m}a(x^m_k)\to0.                    \tag{14}
\]

If \(d_p(z)=0\), then

\[
 \max_{k\le L_m}d_p\bigl(Z(\tau^m_k).1\bigr)\to0.  \tag{15}
\]

If \(z.2(\operatorname{some}S_0)=b>0\), then for all sufficiently large
\(m\), every state in the block satisfies

\[
 \operatorname{quittingTerminalOutcomeMass}
  (r,\tau^m_k)(\operatorname{some}S_0)\ge b/2. \tag{16}
\]

#### Proof

Apply Proposition 5.1 at depth \(L_m=m\).  Choose the realizing-sequence
index far enough that every state is within \(1/m\) of \(z\) and every root
has absorption below \(1/m^2\).  Then the absorption sum is at most \(1/m\).
Continuity of each debt coordinate and of evaluation at the fixed law atom
gives (15)--(16).  QED.

There is no assertion that the blocks for different \(m\) are nested inside
one behavioral profile.  Each individual block is fully composable and
literal.  This is exactly enough to show that the neutral self-loop is in
the finite-window closure of actual chronological blocks; it is not enough
to manufacture an infinite source ancestry.

### Corollary 5.3 (source-provenant neutral occupation)

Put the uniform empirical edge measure on each block (13).  The difference
between its source and target marginals is the two endpoint atoms divided by
\(L_m\), so it tends weakly to zero.  Equations (14) and compactness show that
the empirical measures converge to

\[
 \delta_{(z,\mathrm{AC},z)}.                  \tag{17}
\]

Thus the neutral invariant occupation is a limit of occupations of actual
finite composable blocks.  It is not produced by treating same-law
replacement or minimizer reselection as a temporal edge.

## 6. Exact no-charge theorem for near-returns

The vanishing total charge in Proposition 5.2 can be read directly from the
debt endpoints, without using root convergence.

### Proposition 6.1 (endpoint-ratio charge bound)

For a finite literal exact cap-prefix block as in (13), put

\[
 q_k=q(x_k),\qquad Q=\prod_{k<L}q_k.
\]

Then

\[
 D\bigl(Z(\tau_L)\bigr)=Q D\bigl(Z(\tau_0)\bigr),                \tag{18}
\]

and

\[
 \boxed{
 \sum_{k<L}(1-q_k)
 \le -\log Q
 =\log\frac{D(Z(\tau_0))}{D(Z(\tau_L))}.}       \tag{19}
\]

#### Proof

Iterate exact debt scaling to obtain (18).  Positivity of the global floor
makes every \(q_k\) positive.  Sum \(1-q_k\le-\log q_k\) and use (18).
QED.

### Corollary 6.2 (exact cap-prefix recurrence is necessarily neutral)

If the two endpoints of a sequence of such blocks converge to the same
positive-debt point, then the complete unweighted absorption sum tends to
zero.

Under a reward bound \(M\), the checked literal-stack estimates further give
for every player

\[
 |u_i(\tau_L)-u_i(\tau_0)|
 \le 2M\sum_{k<L}a(x_k),                         \tag{20}
\]

\[
 |c_i(\tau_L)-c_i(\tau_0)|
 \le 4M\sum_{k<L}a(x_k).                         \tag{21}
\]

The complete outcome laws satisfy the elementary coupling bound

\[
 \|\mu_L-\mu_0\|_1
 \le2(1-Q)
 \le2\sum_{k<L}a(x_k).                           \tag{22}
\]

Hence exact cap-prefix semantic/law recurrence is automatically uncharged.
It cannot supply the fixed positive one-edge threshold required by the
positive-charge recurrence consumer.  A successful charged return must use a
different charge, a non-cap exact edge, or a seam whose defect is explicitly
budgeted.

This does not rule out a paid charge located in the old suffix.  It says that
such a suffix mark is not generated or refreshed by the returning cap-prefix
block.  Proposition 5.2 can retain a positive terminal atom while every new
prefix charge vanishes; the atom simply remains in the increasingly remote
suffix.

## 7. Viability, Conley recurrence, and finite rank

Let \(z\) lie in the strict saturation minimum set.  The checked minimum-face
theorem says that the exact-root fibre at \(z\) is the singleton
\(\{\mathrm{AC}\}\), and the corresponding prefix fixes \(z\).  Therefore

\[
 \{z}\quad\text{is a viable invariant set for the exact predecessor
 control.}                                      \tag{23}
\]

It is also a chain-recurrent class: it has an exact semantic self-loop, and
Proposition 5.2 realizes arbitrarily long actual blocks in every
neighborhood of it.

Three consequences are exact.

1. **No forced Conley exit from this relation.**  The neutral point is not
   merely in the chain recurrent set; its exact predecessor action set has
   only the self-loop.  A decomposition theorem can label it recurrent but
   cannot remove it.
2. **No uniform strict continuous Lyapunov drift.**  At the self-loop every
   continuous coboundary is zero.  The natural debt subaction (2) is strict
   exactly on positive-absorption edges and calibrated, rather than strict,
   on the neutral class.
3. **No finite rank from compact semantic observables.**  A continuous map
   from the state space to a finite discrete rank is locally constant near
   \(z\).  The literal towers of Proposition 5.2 eventually remain in that
   one rank cell at every row.  In particular no finite rank built from
   locally stable debt support, atom support, cap chamber, or incidence
   labels is forced to decrease.

A discontinuous rank depending on an enriched exact source code is not ruled
out.  Nor is a rank whose decrease is attached to a new chronological edge
outside (4).  Such a proposal must show that the edge is literal and that
source reconstruction renews the rank; horizontal same-law minimization is
not enough.

Declaring \(z\) terminal would also evade (23), but that is precisely the
missing strict-chamber terminal consumer.  Unique all Continue against the
cap does not make the prescribed payoff coordinate diagonal: in the strict
branch \(D(z)=D_H>D_*>0\).

## 8. Specialization to the strict \(p\)-zero chamber

Let \(I=\operatorname{Fin}4\), assume the positive-minimum hard-residual
data, and take a strict saturation point \(z=(X,\mu)\) with

\[
 D(X)=D_H>D_*>0,
 \qquad d_p(X)=0,                               \tag{24}
\]

all Continue unique exact against \(X.2\), and a retained finite atom

\[
 \mu(\operatorname{some}S_0)\ge b>0.           \tag{25}
\]

The preceding results give a literal actual-data alternative, not merely a
conditional abstract interface:

\[
\begin{array}{c}
\text{arbitrarily deep executable exact cap stacks}\\[2mm]
\text{all semantic/law states }\longrightarrow z\text{ uniformly in the block}\\[1mm]
\max d_p\longrightarrow0,
\quad \min\mu(\operatorname{some}S_0)\ge b/2,
\quad \sum a\longrightarrow0.
\end{array}                                      \tag{26}
\]

Every state in (26) has actual total unrestricted debt at least \(D_*\), and
in fact its debt tends to \(D_H\).  Thus (26) is a genuine literal chronology
inside the conditional positive-gap game.  Its invariant occupation is the
neutral loop and its old suffix atom is not refreshed.

This closes one ambiguity in `FIN4_NEUTRAL_CHRONOLOGY.md`: source provenance
for the **neutral** occupation can be produced.  What cannot be produced from
the same exact cap-prefix relation is positive mean charge or forced rank
exit.  The remaining datum is not compact recurrence.  It is one of:

- a chronological non-cap edge carrying an admissible charge not priced by
  (2);
- an extension-compatible reset/reattachment edge whose cumulative seam is
  controlled; or
- a direct theorem consuming the positive atom and \(p\)-zero cap-neutral
  carrier point.

The two-port warning remains.  If the positive atom belongs only to an
upstream reattached profile and not to the downstream point \(z\), (25) is
unavailable and Proposition 5.2 retains only the downstream law.  The control
argument does not merge the two ports.

## 9. Exact local realizability regressions

### 9.1 Checked reset-incidence regression

`QuittingResetIncidenceCapRegression.positive_incidence_and_toggle_but_only_allContinue_capNash`
gives one literal carrier point with:

- one killed player;
- total debt \(1\);
- opponent incidence \(1\);
- a strict supported membership toggle; and
- all Continue as the only exact cap--Nash root.

Thus incidence, a supported static toggle, positive local debt, and killed
debt do not add an absorbing action to the exact cap-prefix control.

### 9.2 Exact Fin4 neutral towers

The checked `FourPlayerCyclicPlateauCandidate` is an even sharper dynamical
boundary.  At every displayed phase:

- the actual total debt is \(2\);
- the observer and one nonmover have zero debt;
- one finite terminal coalition has outcome-law mass \(1\);
- the cap is the common vector \((1,1,0,0)\); and
- all Continue is the unique exact cap--Nash root.

Prefix the phase profile by all Continue \(L\) times.  Every prefix is a
literal executable chronological row.  Its semantic pair and complete
terminal law are exactly unchanged, every root is exact against the actual
tail cap, every chosen zero-debt coordinate stays exactly zero, the unit atom
stays unit, and total prefix charge is zero.  This realizes arbitrary-depth
neutral towers **exactly**, rather than only in the limit.

The same table also has a paid four-state unilateral strategy-update cycle.
The checked `root_not_exactCapNash` proves that those cycling roots are not
exact cap--Nash roots.  Treating those horizontal updates as chronological
edges would therefore be precisely the orientation/source error forbidden by
the architecture.

Finally, `zeroPair_debtSum_eq_zero` shows that this rational table has global
minimum zero.  It is not a counterexample to the uniform-equilibrium
conjecture and does not realize the positive-global-floor premise (3).  It
proves that the local control geometry supplies no contradiction; any proof
must use the positive global provenance in a way stronger than making
\(-\log D\) well defined.

## 10. Boundary tests and failed implications

1. **Positive floor is essential for global logarithms.**  If the carrier
   reaches \(D=0\), \(-\log D\) is not a continuous global potential.  On
   every compact slice \(D\ge\delta>0\), the argument remains valid.
2. **Root uniqueness is essential for neutral towers.**  Without uniqueness,
   roots selected at approximating caps may converge to a positively
   absorbing exact root at the limit instead of all Continue.
3. **Carrier is not attainment.**  Proposition 5 uses a sequence of actual
   profiles and literal finite blocks.  It does not assert that \(z\) itself
   is one executable behavioral profile.
4. **Finite blocks are not one infinite ancestry.**  The depth-\(m\) blocks
   need not extend one another.  Their empirical occupation limit is valid,
   but no infinite profile is silently assembled.
5. **Approximate cap roots need an error account.**  With
   \(D(s)=qD(t)+\rho\), (2) acquires a residual.  Rowwise errors are
   insufficient unless their aggregate effect is controlled.
6. **Same-law replacement is horizontal.**  Law-tight minimization and reset
   selection may produce useful states, but they are not edges of (4) until
   an executable source/tail seam is proved.
7. **Positive terminal atom is not positive prefix charge.**  The tower may
   keep a fixed atom while all new root hazards vanish; its calendar location
   can escape to infinity.
8. **A code-sensitive rank remains possible.**  The no-rank conclusion
   applies to continuous finite ranks factoring through the compact
   semantic/law state and to any rank required to fall on the neutral
   self-loop.  It does not exclude a new enriched source code with a proved
   well-founded transition.
9. **Local positive debt is not a global exploitability gap.**  The exact
   Fin4 regression has debt \(2\) at the displayed states and debt \(0\)
   elsewhere.  No explicit positive-global-gap table is claimed.

## 11. Verdict and next exact question

Invariant occupation, Conley recurrence, viability, and calibrated-subaction
theory do not consume the strict \(p\)-zero unique-all-Continue saturation
chamber when applied to the exact cap-prefix relation.  They identify its
precise dynamics:

```text
literal exact cap-prefix edge
  -> debt-calibrated dissipativity
  -> every invariant occupation has zero absorption
  -> strict saturation point is a viable neutral self-loop
  -> actual arbitrarily deep neutral towers approximate that loop
  -> retained suffix atom survives, but no charged return or finite rank.
```

The sharp next question is therefore:

> Can the fixed-law reset/toggle data at a strict \(p\)-zero saturation point
> be lifted to one literal chronological edge whose admissible charge is not
> bounded by the cap-debt drop, while preserving the same source ancestry and
> positive atom?

A positive answer would add a genuinely new edge to the control system and
could activate occupation recurrence or a capacity compiler.  A negative
answer would need an exact table- or carrier-level separation theorem.  More
compactification of the present exact cap-prefix relation cannot change its
zero occupation value.
