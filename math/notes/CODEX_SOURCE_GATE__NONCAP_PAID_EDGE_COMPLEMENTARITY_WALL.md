# The non-cap paid edge: causalization succeeds, admissibility does not

**Author:** `CODEX_SOURCE_GATE`  
**Status:** ordinary-mathematics source audit; one source-attached non-cap
row producer identified; exact fixed-fibre use ruled out by checked
complementarity; an approximate finite-forward sufficient condition and a
sharp Fin4 field-independence regression are proved below; no hard-residual
producer or new terminal consumer  
**Date:** 2026-08-30

## 1. Question and verdict

The strict \(p\)-zero neutral chamber retains two pieces of information which
do not belong to the exact cap-prefix cocycle:

1. a complete terminal law with a positive finite atom and a supported
   strict membership toggle; and
2. independently, the finite behavioral payoff-return cycles of
   `CODEX_CEDAR__PAID_ROW_REENTRY.md`, especially Propositions 66--69.

The question is whether either object gives one literal chronological edge
with positive charge which is not already paid by the exact cap-debt drop.

There is a sharp two-part answer.

* **Causalization succeeds.**  A positive law atom has actual profile-owned
  rows.  On the reset face, a retained collision atom gives a cofinal family
  of literal rows with a uniform positive absorption floor.  Their root and
  next shifted tail are co-realized by the same behavior profile.  This is a
  genuine non-cap chronological edge, and its absorption is not governed by
  the cap-Nash debt scaling identity.
* **The existing consumers still do not apply.**  The row is not known to be
  Nash.  If a positive behavioral recovery is attached to that same literal
  root--tail fibre, the checked complementarity theorem says that the fibre
  cannot be an exact Nash--Bellman edge; every approximate repair which keeps
  the root and tail must pay Nash error at least the retained recovery.  The
  static toggle cycle realizes this obstruction with unit absorption and
  Nash defect at least the terminal gap.  Its literal temporal arrows all
  point to the all-Never suffix, not to the next toggle vertex.

Thus the desired strong edge has **not** been produced.  The missing datum is
not another recurrence or compact rank.  It is a root-or-tail-changing,
source-attached connector:

> an exact (or aggregate-error-controlled) punishment-floor block with
> positive end reach, whose front is close to the literal marked source,
> whose terminal suffix is extension-compatible with the next returned
> source, and whose positive charge survives the root/tail change.

For the existing one-edge payoff-closure consumer one must additionally
return, exactly or in payoff, from the connector's current endpoint toward
its tail.  For the Cedar cycle, the reviewed Proposition 69 interface is the
weaker sufficient form: exact floor-admissible paths shadowing all payoff
nodes.  No present declaration constructs those paths.

No Lean file or export was changed.

## 2. Narrow source boundary

The following checked declarations were inspected.

### Law-to-row causalization

In
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`:

- `exists_jointRealizers_finiteWindow_positiveStage_of_lawMass_pos`;
- `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom`; and
- `quittingStageCoalitionMass_literalRootStack_add_length`.

In
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetFaceLawTemporalSplit.lean`:

- `exists_resetFaceLaw_concentrated_or_diffuseWindowPacket`; and
- `exists_resetFaceLaw_concentratedPacket_of_collision`.

In
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionTemporalSplit.lean`:

- `QuittingReprojectionConcentratedPacket`, especially its `stageMass`,
  `semanticPrefix`, and `defect_tendsto` fields.

The elementary charge comparisons used below are
`quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass`,
`quittingLiveMass_le_one`, and
`quittingRootCoalitionMass_le_absorptionMass_of_nonempty`.

### Strategic obstruction on the same literal fibre

In
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiteralActualRow.lean`:

- `quittingLiteralActualRowTail`;
- `quittingLiteralActualRowRoot`; and
- `quittingLiteralActualRowBestEndpointGain`.

In
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiteralSourceReturnNoGo.lean`:

- `QuittingLiteralPositiveActualRowPacket`;
- `gain_eq_liveMass_mul_complementarityResidual`;
- `not_exists_literalNashBellmanEmbedding`;
- `not_occurs_in_exactNashBellmanChronology`; and
- `gain_le_nashError_of_literal_root_tail`.

In
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticMacroscopicAtomNashProvenance.lean`:

- `coalitionMass_mul_minimumDebt_le_tailExcess_add_card_mul_nashError`;
- its actual-profile specialization
  `profileLiveRoot_coalitionMass_mul_minimumDebt_le_tailExcess_add_card_mul_nashError`;
  and
- `singletonMass_mul_otherDebt_le_tailExcess_add_card_mul_nashError`.

These theorems already isolate the exact alternative: macroscopic atom,
small tail excess, and small Nash error cannot coexist over a positive
minimum.

### Fixed-law toggle and behavioral return

In
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`:

- `QuittingFixedLawResetDispatch`;
- `QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch`; and
- `QuittingResetIncidenceCapRegression.positive_incidence_and_toggle_but_only_allContinue_capNash`.

In the toggle subtree:

- `QuittingTerminalExploitabilityWitness.exists_strictToggle_gain` and
  `exists_strictToggleClosedOrbit_from` in `StrictOrbit.lean`;
- `exists_reachableStrictToggleSimpleCycle` in `ReachableSimpleCycle.lean`;
  and
- the explicit source warning and zero-survival calculation in
  `StaticCycleChronologyBarrier.lean`.

The behavioral exact return and its reviewed conditional consumer are
Propositions 66--69 of
`notes/CODEX_CEDAR__PAID_ROW_REENTRY.md`.  Those propositions are ordinary
mathematics, not named Lean declarations.

### Downstream consumers

The exact consumers inspected were:

- `QuittingPositiveAdmissibleReturn` in
  `UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`;
- `QuittingPositiveAdmissiblePayoffClosure` and
  `PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer` in
  `UniformEquilibrium/Diagnostics/Quitting/PaidFirstDisagreementPayoffNearReturn.lean`;
- `QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily` in
  `UniformEquilibrium/Quitting/Projective/CumulativeChargeNearReturn.lean`;
  and
- the summable-error route through `QuittingSummableSeamSource` and
  `QuittingSummableResidualNashBellmanSpine`.

No literature claim is used.

## 3. What the retained law really does produce

Let \(z=(X,\mu)\) be a joint semantic/law carrier point, let \(p\) be the
reset player, and suppose

\[
 d_p(X)=0,
 \qquad \mu(\operatorname{some}S)>0.                 \tag{1}
\]

Joint-carrier membership alone gives profiles \(\sigma_n\) converging jointly
to \(z\), finite cutoffs \(K_n\), and actual dates \(t_n<K_n\) at which

\[
 \Pr_{\sigma_n}(T=t_n,\ Q=S)>0.                       \tag{2}
\]

This is already chronological provenance: at the marked date define

\[
 R_n=\text{live root of }\sigma_n\text{ at }t_n,
 \qquad
 T_n=\operatorname{Sem}(\sigma_n\mid\text{all Continue through }t_n),
\]

where \(T_n\) begins at \(t_n+1\), and let \(C_n\) be the semantic pair at
the live history at \(t_n\).  Then the checked spine identity gives

\[
 C_n=P_{R_n}(T_n).                                     \tag{3}
\]

Equation (3) is a literal chronological edge

\[
 C_n\longrightarrow T_n.                              \tag{4}
\]

Neither endpoint was independently compactified and the tail is not a
counterfactual graft.

For a generic atom, (2) need not have a uniform lower bound: the atom can be
spread over a growing number of calendar rows.  The reset-face temporal
split states exactly this concentrated-versus-diffuse alternative.

### Proposition 3.1 (uniform non-cap row in the collision arm)

Assume in addition that the retained atom \(S\) is a collision.  Then, after
passing through
`exists_resetFaceLaw_concentratedPacket_of_collision`, there are a fixed
nonempty coalition \(A\), a number \(\rho>0\), and cofinally many actual
profile-owned marked rows satisfying (3) and

\[
 \rho
 \le \Pr(T=t_n,Q=A)
 \le \Pr(Q=A\mid T\ge t_n)
 \le a(R_n),                                           \tag{5}
\]

where \(a(R_n)=1-q(R_n)\) is the root absorption mass.

**Proof.**  The concentrated packet supplies

\[
 \rho\le
 L_n\,\Pr(Q=A\mid T\ge t_n),                          \tag{6}
\]

where \(0\le L_n\le1\) is live mass.  Coalition mass is nonnegative, so
(6) and \(L_n\le1\) imply

\[
 \rho\le\Pr(Q=A\mid T\ge t_n).
\]

Since \(A\ne\varnothing\), the checked coalition-to-absorption comparison
gives the last inequality in (5).  The semantic-prefix field of the same
packet is exactly (3).  QED.

This is the requested weak positive result: the fixed-law reset atom can, in
the collision arm, be lifted to a literal source-attached chronological edge
with charge at least \(\rho\), and this charge is not a cap-Nash debt drop.
The root is the actual behavioral root \(R_n\), not a cap selection.

Two qualifications are binding.

1. If the retained atom is a singleton, the checked output is still
   concentrated-or-diffuse.  Positive total law mass alone gives no uniform
   row charge.
2. The concentrated packet controls only the reset owner's normalized local
   defect.  It does not assert that all players' defects vanish, that \(R_n\)
   is exact Nash, or that the prescribed tail payoff is above punishment.

The supported static toggle also does not repair qualification 2.  A strict
cell improvement on the event \(A\) can be canceled by the action comparison
on the other root coalitions.  The fixed-law Bool regression demonstrates
this separation in checked form: positive incidence, a supported strict
toggle, reset debt zero, and positive total debt coexist with all Continue
as the only exact cap root.

## 4. The static toggle cycle becomes a star, not a chronology

The checked strict-toggle orbit has vertices \(S\subseteq I\).  Write
\(\sigma^S\) for the terminal profile in which members of \(S\) Quit at date
zero and all outsiders Never Quit.  Its static update arrow is

\[
 S\xrightarrow{m}S\mathbin\triangle\{m\},              \tag{7}
\]

and the selected player gains at least the terminal gap \(\gamma\).

For every nonempty \(S\), however, the literal temporal decomposition of
\(\sigma^S\) is

\[
 \sigma^S
 =\operatorname{pureSet}(S)\triangleright\sigma^\varnothing
 \longrightarrow\sigma^\varnothing.                  \tag{8}
\]

The root in (8) has absorption one.  The successor is the all-Never suffix,
not \(\sigma^{S\triangle\{m\}}\).  When \(S=\varnothing\), the only literal
decomposition is the all-Continue self-loop at \(\sigma^\varnothing\), with
absorption zero.

The toggle improvement in (7) is instead a unilateral endpoint deviation at
the source row of (8):

- an outsider joins \(S\) by changing Continue to Quit;
- a member leaves a nonsingleton \(S\) by changing Quit to Continue while
  another member still absorbs; or
- the sole member of a singleton leaves to the all-Never tail, whose payoff
  is the static empty-coalition payoff zero.

Hence, for every selected nonempty toggle vertex, the root--tail coordinate
Nash defect of (8) is at least \(\gamma\).  The cycle has therefore produced
a literal non-cap row of charge one, but its price is a fixed Nash defect:

\[
 a(R)=1,
 \qquad \operatorname{Def}_m(R,T)\ge\gamma.            \tag{9}
\]

The static recurrence does not change the target of (8).  It gives a finite
family of defect-bearing arrows into the same all-Never suffix, not a closed
chronological walk.

This also explains the exact statement in
`StaticCycleChronologyBarrier.lean`: a nonempty pure-set root kills every
later static vertex.  The singleton-leave case additionally requires the
actual tail coordinate to equal zero; \(\sigma^\varnothing\) supplies exactly
that value.

## 5. Positive-reach rigidity for the Proposition 66 clock cycle

The more general deterministic pure-time return has the same obstruction in
a form which does not depend on immediate quitting.

### Proposition 5.1 (deterministic suffix rigidity)

Let \(\sigma^\tau\) and \(\sigma^\nu\) be deterministic pure-time profiles,
with clocks in \(\mathbb N\cup\{\infty\}\).  Suppose a literal block of length
\(L\) cuts \(\sigma^\tau\) into a prefix and the exact suffix
\(\sigma^\nu\), and suppose the end reach of the block is positive.  Then
every prefix root is all Continue, end reach is one, and

\[
 \tau_i<\infty\Longrightarrow\tau_i\ge L,
 \qquad
 \nu_i=
 \begin{cases}
   \tau_i-L,&\tau_i<\infty,\\
   \infty,&\tau_i=\infty.
 \end{cases}                                           \tag{10}
\]

In particular the first quitting coalition, terminal law, and terminal
payoff vector are unchanged.

**Proof.**  A deterministic root has joint Continue mass either zero or one.
Positive survival through all \(L\) rows therefore forces every player to
Continue at every prefix date.  Removing those common dates subtracts \(L\)
from every finite clock and leaves Never unchanged.  No absorption occurs in
the prefix, so the terminal outcome is unchanged.  QED.

Every Proposition 66 update changes one player's payoff by at least
\(3\gamma/4\).  Proposition 5.1 therefore rules out a positive-reach literal
chronological block from one displayed update node to the next.  At the
first sure-exit row one can attach the next node as a counterfactual suffix,
but end reach is zero.  The attachment is semantically invisible and does
not transport source ancestry, the retained atom, caps, or future update
nodes.

Thus the exact endpoint payoff return in Proposition 66 is horizontal in
strategy space.  It cannot be converted into a positive-reach chronological
return merely by reindexing its clocks.

## 6. Checked fixed-fibre no-go

Suppose a literal actual row carries a positive best-endpoint behavioral
gain \(g>0\).  The named identity in
`TerminalSemanticLiteralSourceReturnNoGo.lean` is

\[
 g=L\,\operatorname{Def}_i(R,T),                       \tag{11}
\]

where \(L\) is source live mass and \(\operatorname{Def}_i(R,T)\) is the
coordinate root-Nash defect against the actual next shifted tail.

Exact Nash--Bellman complementarity on the same \((R,T)\) fibre forces
\(\operatorname{Def}_i(R,T)=0\).  Consequently:

\[
 \boxed{\text{positive literal gain}
 \quad\Longrightarrow\quad
 \text{no exact embedding preserving source, root, and tail}.} \tag{12}
\]

More quantitatively, if the same root and tail are only
\(\varepsilon\)-Nash, then the checked theorem gives

\[
 g\le\varepsilon.                                      \tag{13}
\]

The unit-charge toggle rows in (9) therefore cannot be repaired on their
literal fibre below error \(\gamma\).  Moving the row arbitrarily far behind
the inert all-Continue prefixes does not attenuate this error: those prefixes
have reach one.

For a macroscopic collision row over a positive minimum \(D_*>0\), the
separate checked provenance inequality says

\[
 \Pr_R(A)D_*
 \le D(T)-D_*+|I|\varepsilon.                          \tag{14}
\]

Thus a positive charged row whose tail returns to the minimum fibre cannot
also have vanishing all-player Nash error.  It must either move its tail a
macroscopic distance in total debt or retain a macroscopic defect.  This is
the exact alternative behind the concentrated reset-row consumer: the
non-cap charge exists, but it is not an unpriced admissible charge.

The singleton form is equally explicit:

\[
 \Pr_R(\{o\})\sum_{i\ne o}d_i(T)
 \le D(T)-D_*+|I|\varepsilon.                          \tag{15}
\]

So a singleton atom needs a complementary-debt collapse, a tail excursion,
or nonvanishing error; positivity of its law coordinate alone is not enough.

## 7. Why no current consumer accepts the produced row

The nearest exact consumers all start strictly after the missing step.

1. `QuittingPositiveAdmissibleReturn` requires an exact punishment-floor
   edge and an exact return path.
2. `QuittingPositiveAdmissiblePayoffClosure` requires an exact
   punishment-floor edge and payoff closure from its current state toward
   its tail payoff.
3. The cumulative near-return family permits charge distributed over an
   unbounded number of rows, but every row is still an exact
   punishment-floor Nash--Bellman edge.
4. The summable-residual route can consume approximate rows only when the
   aggregate Bellman/Nash ledger tends to zero at the requested accuracy.
   A source row satisfying (9) or (13) contributes a fixed error and so does
   not fit that interface.
5. Cedar Proposition 69 supplies the denominator **after** exact
   floor-admissible paths shadow all vertices of the behavioral return.  A
   single literal non-Nash row does not construct any one of those paths.

This is not merely an API mismatch.  Equations (12)--(15) show that the most
natural adapter—keep the actual root and tail, then certify or perturb it as
exact—is mathematically false.  The existing Fin4 exactification regression
in
`notes/CODEX_SOURCE_GATE__CHRONOLOGICAL_C1_C2_CAPACITY_ADAPTER.md`
strengthens the warning: even vanishing rowwise root perturbations over a
long block can lose the entire aggregate charge under exactification.

## 8. Minimal extra field

There are two different ports, and they require different precise additions.

### 8.1 Fixed-law atom port

The collision arm already has source ancestry, a common actual tail, and a
uniform positive non-cap absorption floor.  Its missing field is a
**charge-preserving fibre change**, not causalization:

\[
 (C_n,R_n,T_n)
 \rightsquigarrow
 (\widehat C_n,\widehat R_n,\widehat T_n)               \tag{16}
\]

such that

- \(\widehat R_n\) is exact Nash against \(\widehat T_n.1\);
- \(\widehat T_n.1\) is above the punishment floor;
- \(\inf_n a(\widehat R_n)>0\);
- the front and tail seams in (16) are quantitatively controlled; and
- \(\widehat T_n\) is an actual extension-compatible child, not an
  independently selected cap state.

At least one of root or tail must change by (12).  If the tail remains near
the positive minimum, (14) says the root cannot retain a macroscopic
collision and have small Nash error.  Hence any successful connector must
spend a nontrivial tail excursion and later repay it, or use a genuinely
nonlocal multirow error account.

For a singleton or diffuse law atom, one needs temporal concentration (or a
blockwise aggregate atom charge) before (16).

### 8.2 Behavioral return port

The missing field is **positive-reach continuation compatibility**.  For
each update node one needs a literal block whose end suffix realizes the next
node and whose end reach is bounded away from zero.  Proposition 5.1 proves
that the deterministic clock nodes themselves cannot supply this field.

The already reviewed sufficient replacement is Cedar Proposition 69:
arbitrarily accurate, concatenable, exact floor-admissible payoff shadows of
all returned nodes.  Its off-diagonal ledger then creates a fixed aggregate
absorption denominator automatically.  If one insists on the one-edge
consumer, a uniform bound on the total number of connector rows is also
needed.

These are minimal in the operational sense: delete positive reach and the
next suffix is arbitrary; delete exact/aggregate Nash control and (13) leaves
a fixed profitable deviation; delete floor and no punishment consumer
applies; delete endpoint closure and one positive edge has no lasso.

## 9. Final verdict

The retained non-cap information is not empty.  It gives literal executable
charged rows:

```text
positive reset-face collision law
  -> same-profile concentrated marked row
  -> literal semantic prefix C = P_R(T)
  -> root absorption bounded below independently of cap debt.
```

The static behavioral cycle gives an even sharper local instance:

```text
nonempty toggle vertex
  -> unit-absorption literal row to the all-Never suffix
  -> selected toggle is a root-tail deviation of gain at least gamma
  -> same-fibre exact Nash embedding is impossible.
```

Accordingly the answer to the proposed direct lift is **negative with a
located boundary**.  The inspected data produce no source-attached positive
admissible edge, and no existing downstream consumer fires.  What is missing is one
extension-compatible, charge-preserving exact connector which is allowed to
change the literal root or tail and which comes with a return/closure account.
The neutral-chamber occupation theorem ruled out extracting that connector
from cap recurrence; the present audit rules out extracting it by merely
relabeling the fixed-law toggle or the behavioral payoff cycle.

## 10. Next exact question

The smallest useful producer question is:

> In the concentrated reset-face branch, can the macroscopic actual marked
> row be followed to a tail excursion and then returned by a finite exact
> punishment-floor block whose aggregate absorption stays bounded below and
> whose two endpoint payoff seams tend to zero?

This formulation uses the new non-cap causal row where it is genuinely
available, respects the fixed-fibre complementarity no-go, and feeds the
checked cumulative-charge near-return consumer directly.  A demand that the
same literal root and tail become exact is already refuted by (12).

## 11. Consumer correction: exact Nash rows are not necessary

There is a weaker checked consumer than the exact paths used in Sections 7--8.
`QuittingFiniteForwardPacket` and
`quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets` in
`UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`
ask, for every \(\delta>0\) and raw charge target \(Q\ge0\), for one finite
forward packet

\[
 V_{t+1}=F_{q_t}(V_t)                                   \tag{17}
\]

inside one fixed compact payoff carrier, with:

1. exact Bellman evaluation (17);
2. a common support-local Nash tolerance \(\delta\) at every row;
3. the punishment floor weakened only to \(P-\delta\); and
4. \(\sum_t a(q_t)\ge Q\).

There is no factor equal to the block length in the support-error field.  The
compact charged-closing theorem chooses a close pair only after the producer
has accumulated the requested raw charge.  Thus rows of charge \(O(h)\) and
support error \(O(h)\), iterated an arbitrarily large finite number of times
at a fixed \(h=h(\delta,Q)>0\), are sufficient if their exact Bellman orbit
stays in the common carrier and above \(P-\delta\).

This correction matters in the unique-all-Continue chamber.  The robust moat
in `TerminalSemanticPlateauNashMoat.lean` excludes a fixed positive
absorption scale for roots whose Nash error tends to zero.  It does **not**
exclude unbounded raw charge distributed over arbitrarily many roots whose
individual absorption tends to zero.  Conversely, it does not produce those
roots or keep their moving Bellman successors rational.

The canonical paid row still cannot be used.  Proposition 10.1 of
`CODEX_ADVERSARY__QUANTITATIVE_DESCREENING_COMPLEMENTARITY_BARRIER.md`
shows that its forced owner has defect at least \(\gamma/4\) against every
bounded later continuation.  A support tolerance tending to zero therefore
requires discarding that first root, not merely moving its later tail.

### 11.1 Weakest source-derived moving-prefix condition

For the present ancestry question, the exact minimal strengthening of the
checked packet interface is the following.  Fix the canonical compact reward
box \(K=[-M,M]^I\).  For every \(\delta>0\) and \(Q\ge0\), require:

- one executable behavioral tail \(\tau_0\) selected from the allowed hard-
  source ancestry;
- a finite root word \(q_0,\ldots,q_{H-1}\); and
- recursively prefixed actual profiles

  \[
  \tau_{t+1}=q_t\triangleright\tau_t;                  \tag{17a}
  \]

such that, with \(V_t=U(\tau_t)\),

\[
 q_t\text{ is support-}\delta\text{-Nash against }V_t,
 \qquad V_t\ge P-\delta,                               \tag{17b}
\]

and

\[
 \sum_{t<H}a(q_t)\ge Q.                               \tag{17c}
\]

Call this **source-realized unbounded approximate prefix capacity**.  The
literal prefix identity gives (17) exactly, and terminal payoff boundedness
puts every \(V_t\) in the same \(K\), independent of \(\delta,Q\).  Forgetting
the profiles but retaining their payoff vectors and roots therefore produces
`QuittingFiniteForwardPacket` at every requested accuracy and charge.

This is the weakest operational source condition: it adds only the ancestry
which the public finite-forward packet intentionally forgets.  A one-step
local tangent, a family of unrelated finite prefixes, or a cap-root orbit
does not imply it.  The current strict chamber fails before (17a)--(17c) can
be assembled: its accurate roots are controlled at the envelope \(c\), while
the source-realized tail has prescribed payoff \(u\), and no declaration
realizes \(c\) as a common behavioral continuation.

## 12. A literal two-label quadratic-seam sufficient condition

The following elementary construction identifies a genuinely sufficient
moving-root/tail connector.  It also isolates two data not supplied by the
strict neutral passport.

Let \(M>0\) bound every terminal reward coordinate in absolute value.  Let
\(c\in[-M,M]^I\) satisfy

\[
 c\ge P,
 \qquad r_i(\{i\})\le c_i\quad(i\in I),                \tag{18}
\]

so all Continue is endpoint Nash at \(c\).  Write

\[
 s^i=r(\{i\})\in\mathbb R^I.                           \tag{19}
\]

Assume there are distinct labels \(i,j\), a number \(0<\lambda<1\), and an
actual behavioral tail \(\tau\) whose prescribed payoff is \(c\), such that

\[
 c_i=s^i_i,qquad c_j=s^j_j,qquad
 c=\lambda s^i+(1-\lambda)s^j.                         \tag{20}
\]

The last equality is componentwise.  It is the exact two-port affine balance,
not merely equality in the two owner coordinates.

For \(0<h\le1\), put

\[
 x=h\lambda,qquad y=h(1-\lambda).                     \tag{21}
\]

Let \(R_i(x)\) be the singleton product root in which only \(i\) Quits, with
probability \(x\), and define \(R_j(y)\) similarly.  Starting from \(V_0=c\),
one forward two-row block is

\[
 W=(1-x)V+s^i x,qquad
 T(V)=(1-y)W+s^j y.                                    \tag{22}
\]

These are exact Bellman successor equations.  At the behavioral level they
are literal prefix operations: prepend \(R_i(x)\) and then prepend
\(R_j(y)\) to the same already constructed tail.  Every finite iterate is
therefore one executable extension ancestry of \(\tau\).

### Proposition 12.1 (quadratic seam and renewable raw charge)

Under (18)--(20), for every \(\delta>0\) and \(Q\ge0\) there is an \(h>0\)
and a finite number of repetitions of (22) for which:

\[
 V_{t+1}=F_{q_t}(V_t)\quad\hbox{at every row},          \tag{23}
\]

every root is support-\(\delta\)-Nash against its displayed tail, every value
is at least \(P-\delta\), and

\[
 \sum_t a(q_t)\ge Q.                                   \tag{24}
\]

All payoff vectors stay in the canonical reward box.  The start and every
two-row endpoint remain \(O(h)\)-close to \(c\), uniformly in the number of
blocks.  A single two-row block started exactly at \(c\) has endpoint seam

\[
 \|T(c)-c\|_\infty\le \frac M2 h^2.                    \tag{25}
\]

Consequently these packets satisfy the checked finite-forward-packet
consumer and imply an unrestricted-behavior uniform-equilibrium payoff.

### Proof

Put \(d_i=s^i-c\) and \(d_j=s^j-c\).  Equation (20) says

\[
 \lambda d_i+(1-\lambda)d_j=0.                         \tag{26}
\]

Expanding (22) at \(c\) therefore gives the exact cancellation

\[
 T(c)-c=-xy\,d_i.                                    \tag{27}
\]

Since \(\|d_i\|_\infty\le2M\) and
\(\lambda(1-\lambda)\le1/4\), (25) follows.  The affine map \(T\) has scalar
linear part

\[
 q=(1-x)(1-y),qquad
 A=1-q=h-h^2\lambda(1-\lambda)\ge\frac34h.             \tag{28}
\]

Hence for every \(n\),

\[
 \|T^n(c)-c\|_\infty
 \le\frac{\|T(c)-c\|_\infty}{A}
 \le Mh.                                               \tag{29}
\]

Every intermediate \(i\)-successor in (22) is within
\(Mh+2Mx\le3Mh\) of \(c\).  Bellman successor values are convex combinations
of a preceding value and terminal rewards, so they remain in the reward box.

For the \(i\)-row, the owner's endpoint difference is

\[
 s^i_i-V_i=c_i-V_i,
\]

whose absolute value is at most \(Mh\).  For an outsider \(k\ne i\), only
Continue is played and its Quit-minus-Continue endpoint difference is

\[
 (1-x)(r_k(\{k\})-V_k)
 +x\bigl(r_k(\{i,k\})-r_k(\{i\})\bigr).                \tag{30}
\]

By (18), its positive part is at most \(Mh+2Mx\).  At the \(j\)-row, the
owner's absolute difference and every outsider's positive difference are,
by the same calculation, at most

\[
 Mh+2M(x+y)\le3Mh.                                   \tag{31}
\]

Thus all rows are support-\(3Mh\)-Nash.  Equations (29)--(31) also put every
value above \(P-3Mh\).  Choose \(h>0\) with \(3Mh\le\delta\).

Each two-row block contributes raw absorption \(x+y=h\).  Repeating the block
\(N\) times with \(Nh\ge Q\) proves (24).  The estimates are uniform in
\(N\), so the same \(h\) works for every row of the selected finite packet.
The final conclusion is exactly
`quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets`.
QED

The important scale distinction is now explicit.  The **two-row seam** is
quadratic in its one-block charge, while the support error is only linear.
The checked finite-forward consumer needs no quadratic support estimate: it
needs an arbitrarily small common row tolerance together with arbitrarily
large raw charge.  The affine contraction in (28), not summation of the
one-block seams, keeps the moving source in an \(O(h)\) tube for arbitrarily
many repetitions.

## 13. Why the current neutral data do not instantiate Proposition 12.1

The strict singleton/Never chamber gives owner pins such as

\[
 c_i=r_i(\{i\})
\]

and a directed cycle of positive collision increments.  Cedar Sections
71--72 sharpen that static cycle.  None of those results supplies the
whole-vector affine equation

\[
 c=\lambda r(\{i\})+(1-\lambda)r(\{j\}),              \tag{32}
\]

or its multi-phase `FaceCirculationCertificate` analogue.  Collision
increments use pair rewards; (32) uses every coordinate of two singleton
reward vectors.  Neither set of signs determines the other.

More seriously, the neutral hull supplies \(c\) as the coordinatewise
unrestricted **cap** of a carrier profile whose prescribed payoff is generally
\(u<c\).  It supplies no behavioral tail with prescribed payoff \(c\).
`TerminalCapNashEndpointTransport.lean` states this source boundary
explicitly: no joint realization of the cap vector is asserted.  The exact
identity
`capNash_isZeroNash_at_prescribed_iff_surcharge_eq_liveDebt` in
`PairBasePaidResetEndpointSeam.lean` also shows that cap-Nash does not silently
transfer to the literal prescribed tail.

Thus Proposition 12.1 is an actual producer only after two additional fields:

1. a source-compatible tail realizing the balanced vector \(c\); and
2. a positive whole-vector affine balance (or a general face-circulation
   certificate) which is renewable at every exact Bellman successor.

The current source supplies neither.  This is exactly consistent with the
checked `MultiOwnerFaceCirculationFiniteClosing.lean`: once a
`FaceCirculationCertificate` is given, arbitrarily charged finite forward
packets are already constructed and consumed.  The hard Fin4 source has no
decoder into that certificate.

In fact Proposition 12.1 is **not a genuinely new sufficient certificate
class**.  Under (18)--(20), define one phase with vertex \(c\), mixing weights
\(\lambda\) at \(i\) and \(1-\lambda\) at \(j\), and any contraction ratio in
\((0,1)\).  Equation (20) says that its mixed singleton target is exactly
\(c\), so the phase step closes.  The two owner pins in (20) give the vertex
and target pin fields.  Finally set

\[
 f_k=\max\{P_k,r_k(\{k\})\}.                           \tag{32a}
\]

Equation (18) gives \(f\le c\), while by definition \(f\) dominates both
punishment and every solo value.  These are precisely the fields of a
period-one, two-support `FaceCirculationCertificate`.

Thus Proposition 12.1 is a short literal two-row realization of a known
checked sufficient interface.  Its only additional feature is the assumed
actual tail \(\tau\) with payoff \(c\), which upgrades the abstract forward
packet to explicit source ancestry.  That extra feature is exactly what the
neutral cap passport does not provide.

The relation to Cedar Sections 69--73 is precise.

- Proposition 69 obtains a block denominator after exact payoff shadows have
  been constructed.  Proposition 12.1 instead constructs an approximate
  forward orbit directly and uses finite charged closing.
- Proposition 70 repairs the static floor target, but does not realize its
  cap-lifted vectors as one behavioral tail or connect them by Bellman rows.
- Propositions 71--72 constrain the tight static toggle word and produce
  cross-corner premiums, not (32).
- Proposition 73 starts with an actual carrier and builds exact cap-prefixes.
  In the unique-all-Continue neighborhood those exact prefixes are neutral;
  its collision budget does not construct the approximate singleton
  circulation above.

The adversarial descreening audit gives the complementary local obstruction.
Its canonical nearly-sure paid row cannot be the first accurate row for any
bounded continuation.  Equation (10.9) there says that an exact redesign
must move the continuation to a prescribed switch vector.  At the small
singleton scale used here, the necessary shift can be \(O(h)\), but neither
source realization nor the simultaneous other-player equations follow from
that scalar identity.

## 14. Sharp Fin4 regression for all weaker connector fields

The remaining gap is mathematical, not merely an absent declaration.  The
following four-player table shows that literal ancestry, positive end reach,
floor safety, positive absorption, and exact payoff closure do not imply even
one positive-charge accurate forward row when roots and tails may both vary.

Let \(I=\{0,1,2,3\}\).  For each player \(i\), let \(b_i\) be a nonnegative
function of opponent coalitions, with

\[
 b_1(A)=1_{A=\{2\}},\qquad
 b_2(A)=1_{A=\{1\}},\qquad
 b_0=b_3=0.                                           \tag{33}
\]

For every nonempty terminal coalition \(T\), define

\[
 r_i(T)=
 \begin{cases}
 b_i(T),&i\notin T,\\
 b_i(T\setminus\{i\})-1,&i\in T.
 \end{cases}                                          \tag{34}
\]

This is the three-player dominated-quitting regression of Cedar Sections 27
and 65, padded by the genuine fourth player \(3\).

### Proposition 14.1 (closed charged literal row, but zero approximate capacity)

For the table (33)--(34):

1. the punishment vector is \(P=0\);
2. let the tail be all Never and let players \(1,2\) independently Quit with
   probability \(1/2\) in one prefixed row, while \(0,3\) Continue.  This is
   one literal executable edge with end reach \(1/4\), absorption \(3/4\),
   current payoff \(0\), and tail payoff \(0\).  It is exactly floor-safe and
   payoff-closed;
3. nevertheless, if \(0\le\delta<1/2\), \(V\ge P-\delta\), and a product root
   is support-\(\delta\)-Nash against \(V\), then that root is all Continue;
4. consequently no support-\(\delta\) finite forward packet satisfying the
   punishment-floor field has any positive charge, regardless of how its
   roots and continuation values change.

### Proof

Never gives every player the nonnegative payoff \(b_i(A)\) against any first
opponent coalition \(A\).  Against all-Never opponents the best of Never and
quitting alone is \(\max(0,-1)=0\).  Hence the punishment value is exactly
zero.

For the displayed root, the four possible outcomes of the two independent
marginals are Never, \(\{1\}\), \(\{2\}\), and \(\{1,2\}\), each with
probability \(1/4\).  Directly from (34),

\[
 r(\{1\})=(0,-1,1,0),\quad
 r(\{2\})=(0,1,-1,0),\quad
 r(\{1,2\})=0.                                       \tag{35}
\]

Their expectation, including the zero Never payoff, is zero.  The joint
Continue probability is \(1/4\), proving item 2 with genuine positive reach
to the displayed all-Never child.

Now fix any player \(i\).  Conditional on a nonempty opponent Quit set, (34)
makes Quit worth exactly one less than Continue.  Conditional on no opponent
Quit, the difference is \(-1-V_i\).  If \(p_i^0\) denotes the probability
that every opponent of \(i\) Continues, the endpoint difference is therefore

\[
 D_i=-1-p_i^0V_i.                                     \tag{36}
\]

Since \(V_i\ge-\delta\),

\[
 D_i\le-1+\delta< -\delta.                            \tag{37}
\]

If player \(i\) assigned positive probability to Quit, support-local Nash
would require \(-\delta\le D_i\), contradicting (37).  Every Quit marginal
is zero, proving item 3.  Item 4 follows row by row; exact Bellman recursion,
compactness, and changing later tails cannot create absorption once every
support-\(\delta\) root is all Continue.  QED

This regression satisfies every weaker connector field named above, including
literal end-child compatibility rather than a counterfactual zero-reach tail.
It also survives the corrected finite-forward-packet target.  It does **not**
satisfy the positive-minimum hard-residual hypotheses: all Never is a terminal
equilibrium and the global debt minimum is zero.  Therefore it is not a
counterexample to the Fin4 conjecture.  Its exact force is field independence:
any hard-residual proof must use a global datum which excludes this joining-
dominated geometry, not just ancestry, floors, charge, and payoff shadowing.

## 15. Updated connector verdict

The three requested attacks now have exact outcomes.

1. **Finite exact two-root construction:** the canonical paid root is ruled
   out against every later tail, and a small binding-owner singleton row at
   the neutral cap is immediately nonexact when its collision successor has
   positive joining gain.  No current source field solves the simultaneous
   switch-vector equations needed after moving both roots and tails.
2. **Approximate connector:** Proposition 12.1 proves a literal renewable
   two-row construction.  Its seam is \(O(h^2)\), its common support error is
   \(O(h)\), and it already suffices for the checked approximate aggregate
   compiler.  The precise missing inputs are source realization of the cap
   and whole-vector affine balance.
3. **No-go:** Proposition 14.1 satisfies all weaker chronological fields and
   still has zero approximate rational capacity below error \(1/2\).  It is
   sharp at the requested interface but deliberately lies outside the
   positive-minimum/terminal-gap branch.

Thus allowing both root and tail to change removes the fixed-fibre logical
contradiction, but it does not close the source adapter.  The smallest live
hard-residual question is now:

> Does the strict Fin4 neutral passport produce a source-realized moving
> payoff orbit with arbitrarily large raw absorption and uniformly vanishing
> support error, equivalently a renewable approximate circulation which
> excludes the dominated-quitting regression of Proposition 14.1?

This is strictly weaker than exact Nashification and strictly stronger than a
single quadratic tangent row at a frozen cap.
