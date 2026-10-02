# Full-debt moat, exact-prefix entrance, and actual-reach witness reselection

Status: ordinary mathematics assembled from named checked declarations; the
floor adapter, uniform prefix-entrance estimate, full-support persistence
estimate, and actual-reach witness-reselection theorem are not yet packaged
as Lean declarations. This is a strict reduction, not a uniform-equilibrium
proof. An earlier version incorrectly described the opponents-only
`liveMass` of the inherited paid row as joint reach. Sections 4, 6, 7, and 11
now keep the two probabilities separate.

## Question and outcome

Let $z=(u,c)$ be a positive global minimizer of terminal-semantic total debt
for a four-player quitting game, and suppose its full-debt arm holds:

\[
d_i(z):=c_i-u_i>0\qquad(i\in \operatorname{Fin}4).
\]

Assume the hard-residual source data, in particular a terminal exploitability
witness and punishment normality for every player. Suppose a source-faithful
finite literal block has starting profile $\sigma$, its semantic pair tends
to $z$, and its positive full weighted cap-defect ledger has already been
localized to a block-internal
`QuittingPaidFirstDisagreementRow`. What does the global singleton moat buy?

It buys four exact facts.

1. Every sufficiently source-near block profile is uniformly above the
   behavioral punishment floor. Hence the literal paid row enters
   `QuittingPaidRowFloorSafeSource` without changing its profile, row, or
   observer.
2. The checked marked exact-orbit alternative can be applied to that same
   profile. On the no-uniform-payoff branch it necessarily produces a
   summable all-Continue semantic port, and the entrance to the unchanged
   original suffix has a **uniform**, not merely orbit-dependent, positive
   joint-reach floor. The inherited row inside that suffix still has only an
   opponents-only `liveMass` floor.
3. Every semantic pair along each sufficiently near marked orbit remains in
   the full-debt chamber. Thus this route does not create a no-entry support
   transition.
4. Independently of the inherited weighted-ledger row, any positive-debt
   coordinate admits a new ordered pure-time pair whose source witness is
   chosen from a quantitatively large low-value part of the prescribed
   stopping law. Choosing its earliest supported element supplies the missing
   own-survival factor. At a debt floor `delta`, the resulting paid row has
   gain at least `delta/4` and actual joint reach at least
   `delta^2/(32 M^2)`. This defeats the deleted-observer conditioning-escape
   regression by witness reselection. It does not by itself make the marked
   cuts compatible across the outward-prefix ancestry.

The positive retained law atom is what supplies the source-faithful deep
chronology upstream. Once the positive weighted ledger and block-internal paid
row have been extracted, the atom is not an additional hypothesis in the
port argument below.

The actual Fin4 source is attached as follows. In
`finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber`, the hull origin
is a positive global semantic minimizer and belongs to its hull. Hence every
hull minimum has debt both at most and at least the origin debt, is itself a
global minimizer, and retains the selected positive finite atom. The earlier
singleton/Never elimination reduces its checked three-arm classification to
the full-debt and reset-rigid arms. This note starts in the former arm.

## 1. Two quantitative margins at a full-debt global minimum

Write

\[
D_*:=D(z)=\sum_i d_i(z)>0,
\qquad s_i:=r_i(\{i\}),
\qquad p_i:=\text{the behavioral punishment value of }i.
\]

The checked `minimumTerminalSemantic_singletonMargin` gives

\[
D_*\le c_i-s_i.                                           \tag{1}
\]

Since $c_i=u_i+d_i(z)$,

\[
u_i-s_i\ge D_*-d_i(z)=\sum_{j\ne i}d_j(z).                \tag{2}
\]

Punishment normality from
`FinFourQuantitativeFullSupportHardResidual.all_punishmentNormal` says

\[
p_i\le s_i.                                                \tag{3}
\]

Consequently

\[
u_i-p_i\ge \sum_{j\ne i}d_j(z).                           \tag{4}
\]

Define the two strictly positive finite-dimensional margins

\[
m:=\min_i\sum_{j\ne i}d_j(z)>0,
\qquad
\delta:=\min_i d_i(z)>0.                                  \tag{5}
\]

The first is a punishment-floor moat; the second is a debt-support moat.
Both are genuinely strict only because all four debts are positive. The
separately checked terminal-gap sign also selects some $a$ with
$s_a\ge\gamma>0$, so (2) gives the useful positive-payoff passport

\[
u_a\ge \gamma+\sum_{j\ne a}d_j(z)>\gamma.                 \tag{6}
\]

## 2. The block-internal paid row is floor-safe

Let \(\sigma_n\) be literal starting profiles of source-faithful blocks and
assume

\[
X_n:=\operatorname{Sem}(\sigma_n)\longrightarrow z.       \tag{7}
\]

For all sufficiently large $n$,

\[
|U_i(\sigma_n)-u_i|<m/2\qquad\text{for every }i.           \tag{8}
\]

Equations (4) and (8) imply

\[
p_i<U_i(\sigma_n)-m/2<U_i(\sigma_n).                      \tag{9}
\]

Thus any positive-gain

```text
row_n : QuittingPaidFirstDisagreementRow reward sigma_n observer_n gain_n
```

packages, with no profile replacement, as a
`QuittingPaidRowFloorSafeSource`. If the weighted-ledger extraction gives

\[
g_n\ge g_0>0,
\qquad
\operatorname{row}_n.\mathrm{start}<L_n,
\qquad
\operatorname{row}_n.\mathrm{liveMass}\ge \ell_0>0,       \tag{10}
\]

all three facts remain available externally alongside the checked source
object. The current structure does not store $L_n$ or common block ancestry,
but it retains the exact same `row_n` as `source.row`.

This is the direct local proof from the chosen full-debt point. There is also
a stronger already checked route which needs only near-minimal total debt.
The theorem
`exists_open_exactAllContinueTube_and_debtMoat_minimumFiber` gives an open
payoff tube containing the prescribed projection of the entire compact
minimum fibre and an \(\varepsilon>0\) such that every carrier pair (X) with

\[
D(X)<D_*+\varepsilon                                      \tag{11}
\]

has (X^u) in that tube. All-Continue is an exact root throughout the tube,
so the singleton inequalities give

\[
p_i\le s_i\le X^u_i.                                      \tag{12}
\]

Therefore the weighted-ledger blocks described in Section 15.7 of
`CODEX_STRENGTHEN__FINITE_SOURCE_FAITHFUL_CHRONOLOGICAL_QUOTIENT_NO_GO.md`
are floor-safe as soon as their literal starting semantic pairs have debt
tending to (D_*). Convergence to one preselected point is unnecessary for
the floor adapter. It is needed only for the coordinatewise full-support
persistence result in Section 5 below.

There is a mandatory start-versus-tail distinction. The ledger identity

\[
\Lambda=D(X_0)-P D(X_L)                                   \tag{13}
\]

and near-minimality of the terminal tail (D(X_L)\to D_*) do **not** imply
that the receiving profile (X_0) carrying the extracted paid row is near
the minimum fibre. The positive ledger is precisely an additional term in
that identity, and any further excess of (D(X_0)) is uncontrolled. Thus a
theorem assuming only a near-minimum terminal tail cannot enter
`QuittingPaidRowFloorSafeSource` from the global moat. It must additionally
retain one of:

- (D(X_0)<D_*+\varepsilon);
- (X_0^u) in the checked all-Continue tube; or
- the punishment-floor inequality directly.

All port conclusions below use this receiving-profile hypothesis. The exact
time-escape regression in Section 7 then shows that even this strengthened
input is still insufficient for a return.

## 3. Exact marked orbit and the no-UE branch

Apply
`QuittingPaidRowFloorSafeSource.exists_markedExactOrbit_alternative_of_witness`
to a sufficiently late block. It returns a
`QuittingPaidRowMarkedExactOrbit` whose zeroth profile is literally
\(\sigma_n\). There are two alternatives:

1. a uniform-equilibrium payoff; or
2. a summable-charge all-Continue port, a semantic all-Continue self-loop,
   and positive limiting reach of the unchanged paid suffix.

The hard residual contains the terminal exploitability witness, so its
`not_exists_uniformEquilibriumPayoff` eliminates the first alternative. The
second alternative is therefore unconditional inside the proposed
counterexample branch.

This already improves on the older cap-port handoff: the paid source is not
reselected after compactness. It is the literal zeroth profile of the exact
orbit, and `profiles_succ` prefixes every selected exact root to that same
profile chain.

## 4. Uniform quantitative entrance to the unchanged suffix

The checked `nonempty_positivePaidSuffixReach_of_terminalWitness` proves only
that each summable orbit has some positive limiting suffix reach. In the
present counterexample setting this can be strengthened uniformly over all
floor-safe paid sources and all selected exact orbits.

Let

\[
M:=\operatorname{quittingRewardBound}(r),
\qquad
q:=\frac{\gamma}{4M},
\qquad
\eta:=q^4.                                                  \tag{14}
\]

The terminal gap forces $M>0$. At every exact punishment-floor root, the
checked
`exactFloorRoot_quitProbability_le_one_sub_terminalGap_div_four_mul`
gives, for every player,

\[
\Pr_i(C)\ge q.                                              \tag{15}
\]

Hence the one-row joint continuation mass $c_t$ and absorption mass
\(a_t=1-c_t\) satisfy

\[
c_t\ge\eta>0,
\qquad 0\le a_t\le1-\eta.                                  \tag{16}
\]

Put

\[
B:=\operatorname{quittingPunishmentFloorPrefixChargeBound}(r).
\]

Every finite truncation of the orbit is a
`QuittingPunishmentFloorFinitePrefix`, so
`QuittingTerminalExploitabilityWitness.prefixCharge_le` gives

\[
\sum_{t<H}a_t\le B\qquad(H\in\mathbb N).                   \tag{17}
\]

For $0\le a\le1-\eta$, integration of $1/(1-x)\le1/\eta$ on
\([0,a]\) gives

\[
-\log(1-a)\le a/\eta.                                      \tag{18}
\]

Combining (17)--(18),

\[
\prod_{t<H}c_t
=\prod_{t<H}(1-a_t)
\ge \exp\!\left(-\frac1\eta\sum_{t<H}a_t\right)
\ge \rho_*:=e^{-B/\eta}>0.                                \tag{19}
\]

Thus the entrance to the original unchanged suffix is reached through every
finite marked prefix with the same game-dependent **joint** lower bound
\(\rho_*\), independent of the block, the exact-root selection, and $H$.

In particular, if (10) holds then the original internal first-disagreement
date has absolute **deleted-observer/opponents-only** reach at least

\[
\rho_*\ell_0>0.                                            \tag{20}
\]

This is not the actual joint reach of the prescribed profile to the row: one
must still multiply by the observer's own survival inside the unchanged
suffix. The inherited row structure contains no lower bound for that factor.

Likewise, lifting the two row deviations through a common exact prefix by
following the prescribed prefix behavior and switching only in the unchanged
suffix preserves a behavioral deviation gap at least \(\rho_*g_0\). This is
an unrestricted behavioral deviation statement. It is not a claim that the
lifted strategies are pure times from the new global origin, nor that the
prescribed observer itself survives to the row.

The estimate (19), absent from the current checked port structure, is a small
formalizable strengthening. It uses both checked ingredients: the marginal
terminal-gap cap and the canonical exact-prefix capacity. Summability alone
would not give a uniform lower bound across a family of orbits.

## 5. Full debt persists along the entire exact port

The same near-minimum source cannot generate a debt-support descent inside
the marked orbit.

By semantic convergence and global minimality, for all sufficiently large
$n$,

\[
|d_i(X_n)-d_i(z)|<\delta/4\quad(\forall i),
\qquad
0\le D(X_n)-D_*<\delta/4.                                  \tag{21}
\]

Let $Y_{n,t}$ be the semantic pair of the $t$-th marked profile. The
checked `QuittingPaidRowMarkedExactOrbit.debt_antitone` gives

\[
d_i(Y_{n,t})\le d_i(X_n).                                  \tag{22}
\]

All $Y_{n,t}$ are actual carrier points, so global minimality gives

\[
D(Y_{n,t})\ge D_*.                                         \tag{23}
\]

The coordinate losses in (22) are nonnegative and their sum is

\[
\sum_i\bigl(d_i(X_n)-d_i(Y_{n,t})\bigr)
=D(X_n)-D(Y_{n,t})
\le D(X_n)-D_*<\delta/4.                                  \tag{24}
\]

Each individual loss is therefore less than \(\delta/4\). Equations
(21)--(24) imply, uniformly in $t$,

\[
d_i(Y_{n,t})>d_i(z)-\delta/2\ge\delta/2>0.                 \tag{25}
\]

So every selected exact orbit stays strictly inside the full-debt chamber.
There is no inactive debt label which can enter, and no positive-debt support
rank can drop. The full-debt hypothesis makes the exact port floor-safe, but
it simultaneously rules out the hoped-for support transition near the
minimum.

## 6. Two distinct remaining obstructions for the inherited row

The weighted-ledger localization says the row starts before the end $L_n$
of the original literal block. After $H$ exact roots are prefixed, that same
row sits behind those $H$ new dates. Its deleted-observer reach stays at least
the positive quantity in (20), but its actual joint reach may still vanish
because the prescribed observer can quit before the internal row. Even when
an additional own-survival field makes the actual reach positive, its
calendar location tends to infinity as $H\to\infty$.

This is compatible with the checked summable semantic port. Product-topology
convergence sees every fixed finite window of the increasingly prefixed
profiles, while the positive-mass paid suffix escapes beyond that window.
The semantic carrier remembers limiting payoff/cap data; it does not turn the
drifting suffix into an attained finite-date row or an admissible return.

Accordingly, the inherited source-faithful paid row plus the full-debt moat
does **not** force a terminal consumer or reset-rigid transition. Before the
witness reselection of Section 11, it lacks both observer survival and an
extension-compatible absolute cut. Section 11 repairs the first deficiency,
but not the second. The remaining chronological field is:

> Convert an actually reached paid cut behind a bounded-capacity summable
> exact predecessor orbit into either a bounded-calendar admissible return or
> a terminal approximate-Nash profile, while preserving the outward-prefix
> ancestry. Equivalently, prevent positive paid response mass from escaping
> only by shifting to infinity.

Any proposed consumer must use one of the following genuinely additional
data.

- a return/rebasing map which moves the paid row back to bounded calendar
  time while preserving the exact-floor ancestry;
- a time-tightness/attainment theorem for the positive reached cut; or
- a theorem that the block-internal paid defect forces nonsummable exact
  absorption, contradicting the uniformly bounded prefix capacity.

The existing fields prove none of these. In particular, `row.start < L_n`
is relative to the original suffix block, not to the ever earlier root of the
marked exact orbit.

## 7. Exact all-Continue entrance-law regression

The preceding temporal objection is not merely a failure to find the right
compactness argument. It has a literal source-attached regression.

**Theorem 7.1 (exact time-escape regression; ordinary mathematics).** Let
\(\sigma\) be a behavioral profile satisfying

\[
p_i\le s_i\le U_i(\sigma)\qquad(\forall i),                \tag{26}
\]

and carrying a positive-gain paid first-disagreement row. Iterated pure
all-Continue prefixing produces arbitrarily deep exact punishment-floor
Nash--Bellman prefixes for which the complete terminal semantic pair,
terminal outcome law, paid gain, paid live mass, and entrance reach are all
constant, while the paid date tends to infinity. If the terminal law has a
positive finite atom, the prefixed behavioral profiles converge pointwise to
all-Continue although every terminal law retains that atom.

**Proof.** The construction and each identity follow below.

Let \(\sigma\) be any one of the sufficiently near literal paid-block
profiles from Section 2, let \(v=U(\sigma)\), and let

```text
row : QuittingPaidFirstDisagreementRow reward sigma observer gain
```

have positive gain. By (12), all-Continue is an exact Nash root against
\(v\). Its Bellman successor is exactly \(v\), by
`quittingRootSuccessorPayoff_allContinueRoot_eq`. Thus the constant data

\[
v_t=v,
\qquad r_t=\text{all-Continue}                             \tag{27}
\]

form an exact punishment-floor Nash--Bellman orbit. Define actual profiles
recursively by

\[
\sigma^{(0)}=\sigma,
\qquad
\sigma^{(H+1)}=\mathrm{allContinue}\mathbin\oplus\sigma^{(H)}.
                                                                    \tag{28}
\]

These are outward prefix extensions, exactly in the orientation of
`QuittingPaidRowMarkedExactOrbit.profiles_succ`. They are not consecutive
future suffixes of one behavioral profile.

For every \(H\):

1. the first \(H\) dates are pure all-Continue;
2. after those dates the continuation is literally \(\sigma\);
3. the terminal outcome law and prescribed payoff are exactly those of
   \(\sigma\), since deterministic waiting changes no time-forgetting
   terminal outcome;
4. the unrestricted cap and hence the complete terminal-semantic pair are
   unchanged: continuing reaches the original cap, while quitting during an
   inserted row yields only the singleton reward, which is at most \(v_i\)
   and hence at most the original cap;
5. the shifted paid row has the same gain and opponents-only live mass, with
   \(\operatorname{start}^{(H)}=H+\operatorname{row.start}\); and
6. the entrance reach to the unchanged paid block is exactly one. The actual
   joint reach from that entrance to the row is whatever it was in
   \(\sigma\), and need not be one or be uniformly positive in a family.

If the original block has a positive finite terminal atom, then every
\(\sigma^{(H)}\) has exactly the same positive atom. Nevertheless, for every
fixed calendar date \(t\), the live root of \(\sigma^{(H)}\) at \(t\) is
all-Continue once \(H>t\). Hence the behavioral profiles converge pointwise
to the all-Continue profile, while their time-forgetting terminal laws remain
constant and retain the positive finite atom. The atom and paid row have
escaped to infinity in calendar time, not in outcome-law space.

This proves three no-go statements.

- Uniform positive suffix-entrance reach does not contradict terminal-law
  compactness or the retained minimum-law atom; this example has reach one
  and an exactly constant terminal law.
- Recentring at the paid row recovers the same suffix \(\sigma\) for every
  \(H\), but erases the distinct absolute cuts. It does not turn the outward
  prefix family into one forward right-extending Nash--Bellman spine.
- Any decoder whose state consists only of the semantic pair, terminal law,
  paid row, and entrance reach cannot detect \(H\). Those data are identical
  for every member of the family, although the absolute paid date diverges.

The minimal extra datum is therefore an extension-compatible absolute cut or
a genuine return/restart edge to a bounded-time copy of the paid suffix. A
moving-window theorem must prove compatibility of these cuts under forward
suffix restriction; choosing a new origin separately for every \(H\) is the
same invalid orientation reversal exposed by the `WITNESS_1` reviews.

The common compact clock in
`CODEX_ADVERSARY__TYPED_CHRONOLOGICAL_RESPONSE_TRACE.md` does not add this
datum. On the regression family it correctly retains the constant terminal
law and cap trace, but the shifted paid block converges to a clock endpoint.
Compact order is preserved; bounded absolute calendar location is not. This
is exactly why typed trace compactness is a shadowing theorem rather than an
executable recentering theorem.

This regression is conditional on a supplied floor-safe paid block, but that
is exactly the object produced in the present full-debt source branch by the
weighted-ledger localization and the minimum-fibre moat. It is not a quitting
game counterexample and makes no claim that the paid block itself is a
terminal equilibrium. This completes the proof of Theorem 7.1.

## 8. Relation to the independent reset dispatch

There is also a checked static transition from any positive debtor at a Fin4
global minimum:
`QuittingTerminalExploitabilityWitness.exists_finFour_prescribedOwner_resetDispatch`.
The stronger pair-base version
`exists_finFour_pairBasePaidResetDispatch_payoffAligned` supplies a unit
incidence reset target, a full-gap paid row, and exact prescribed-payoff
alignment; `FinFourPairBasePaidResetTarget.returned_eq_of_fixedLawResetDispatch`
identifies its reset-face minimizer with the literal stationary target.

Those targets are independently selected stationary profiles. They are not
the block-internal row above and carry no common root-word ancestry. Their
debt excess over $D_*$ is uncontrolled. Consequently they do not repair the
time-escape obstruction in Section 6. If such a reset target happened to have
debt $D_*$,
`QuittingFixedLawResetDispatch.allContinue_of_target_debt_le_source` would
force the reset-rigid all-Continue branch; the missing upper bound on target
debt is exactly what prevents that conclusion.

## 9. Checked declarations and files inspected

- `minimumTerminalSemantic_singletonMargin` in
  `TerminalSemanticAuxiliaryNashBudget.lean`;
- `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal` and
  `exists_open_exactAllContinueTube_and_debtMoat_minimumFiber` in
  `TerminalSemanticFinFourMinimumFiberIsolation.lean`;
- `FinFourQuantitativeFullSupportHardResidual.all_punishmentNormal` and the
  terminal exploitability witness fields in
  `Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`;
- `QuittingPaidFirstDisagreementRow`, especially `gain_le_liveMass`, in
  `TerminalSemanticPaidFirstDisagreement.lean`;
- `QuittingPaidRowFloorSafeSource`,
  `QuittingPaidRowMarkedExactOrbit.debt_antitone`,
  `nonempty_positivePaidSuffixReach_of_terminalWitness`, and
  `exists_markedExactOrbit_alternative_of_witness` in
  `StoppingLaw/Endpoint/PaidRowExactPortAlternative.lean`;
- `exactFloorRoot_quitProbability_le_one_sub_terminalGap_div_four_mul` in
  `Collision/Toggles/TerminalGapExactRootMarginalCap.lean`;
- `QuittingPunishmentFloorInfiniteOrbit.toFinitePrefix` in
  `Quitting/Bellman/Finite/PunishmentFloorInfiniteOrbit.lean`;
- `QuittingTerminalExploitabilityWitness.prefixCharge_le` in
  `Quitting/Terminal/TerminalExploitabilityWitness.lean`;
- `exists_finFour_prescribedOwner_resetDispatch` in
  `TerminalSemanticFinFourPrescribedOwnerResetAlignment.lean`; and
- `exists_finFour_pairBasePaidResetDispatch_payoffAligned`,
  `returned_eq_of_fixedLawResetDispatch`, and
  `allContinue_of_target_debt_le_source` in the pair-base reset and fixed-law
  minimum-target modules.

The temporal-orientation audit also used
`notes/CODEX_ADVERSARY__TYPED_CHRONOLOGICAL_RESPONSE_TRACE.md` and the two
independent `WITNESS_1` reviews. Those are ordinary conference mathematics,
not checked declarations.

## 10. Formalization-sized statements

The ordinary proof above naturally separates into three small declarations.

```text
fullDebtMinimum_eventually_punishmentFloorSafe_of_semanticTendsto
terminalWitness_uniform_paidSuffixReach_lowerBound
nearFullDebtMinimum_markedExactOrbit_debtSupport_eq_univ
paidRow_allContinuePrefix_timeEscapeRegression
positiveDebt_exists_actualReach_paidFirstDisagreementRow
positiveDebt_exists_commonPrefix_profitableStoppingLawFork
```

The second should state the explicit bound (19), not merely positivity. The
third should retain the quantitative lower bound (25). The last two should
state the constants in (29) and (40), keep Never in the stopping-time type,
and distinguish an actually reached response fork from an actual absorption
event. None of these declarations should claim a UE conclusion or a
chronological return.

## 11. Positive debt reselects an actually reached paid response cut

Revision 6 of `fable/NONLOCAL_RECENTERING_ATTACK.md` and its review correctly
object that the inherited paid row supplies only deleted-observer reach. That
objection is fatal for that particular row, but it does not survive a
reselection which uses the prescribed stopping law and the positive debt.

### Theorem 11.1 (debt-to-actual-reach paid-row selection)

Let \(\sigma\) be any behavioral profile, let \(i\) be a player, and put

\[
 M=\operatorname{quittingRewardBound}(r),\qquad
 d_i=B_i(\sigma)-U_i(\sigma).
\]

Suppose \(d_i\ge\Delta>0\). Then \(M>0\), and there are two deterministic
quit-time/Never choices \(s,r\in\mathbb N\cup\{\infty\}\) and

```text
row : QuittingPaidFirstDisagreementRow reward sigma i (Delta/4)
```

such that:

1. \(s\) is in the positive support of the prescribed stopping law of
   \(\sigma_i\);
2. the prescribed own-survival probability of \(i\) through `row.start` is
   at least \(\Delta/(4M)\);
3. `row.liveMass`, the opponents-only survival through `row.start`, is at
   least \(\Delta/(8M)\); and therefore
4. the actual joint probability under \(\sigma\) of being alive at
   `row.start` is at least

\[
 \boxed{\frac{\Delta^2}{32M^2}}.                         \tag{29}
\]

The conclusion is a genuinely actually reached **response cut**. It is not a
claim that the prescribed action at that cut realizes the counterfactual paid
edge as an actual absorbing coalition.

### Proof

For \(q\in\mathbb N\cup\{\infty\}\), write

\[
 f(q)=\operatorname{quittingPureTimeDeviationPayoff}
       (r,\sigma,i,q),qquad C=B_i(\sigma),               \tag{30}
\]

and let \(\nu\) be `quittingBehaviorStoppingLaw reward (sigma i)`. The
checked pure-time envelope and prescribed stopping-law disintegration give

\[
 C=\sup_q f(q),qquad U_i(\sigma)=\mathbb E_\nu f.        \tag{31}
\]

All values and the cap lie in \([-M,M]\). Hence

\[
 0\le C-f(q)\le2M,qquad
 \mathbb E_\nu[C-f]=d_i\ge\Delta.                        \tag{32}
\]

Let

\[
 A=\{q:C-f(q)\ge\Delta/2\}.
\]

If \(a=\nu(A)\), splitting the expectation in (32) gives

\[
 \Delta\le \mathbb E_\nu[C-f]
 \le 2Ma+\Delta/2,
\]

and therefore

\[
 a\ge\Delta/(4M).                                       \tag{33}
\]

This also proves \(M>0\). Choose a receiving choice \(r\) with

\[
 f(r)>C-\Delta/4;                                       \tag{34}
\]

the usual `lt_csSup_iff` argument supplies it even when the cap is not
attained.

Now select the source choice \(s\) as follows. If \(A\) contains a finite
positive-\(\nu\)-mass atom, take the least such finite time. Otherwise all the
positive mass in \(A\) is at Never and take \(s=\infty\). In the first case,
every positive-mass bad choice is either at a finite time at least \(s\), or
is Never. Thus the prescribed own-survival probability through \(s\) is at
least \(a\). In the second case \(\nu(\infty)=a\), and (34) forces \(r\) to be
finite; own survival through \(r\) is at least the Never mass. In both cases,
if \(t=\min(s,r)\), with Never ordered after every finite time, then

\[
 \Pr_{\sigma_i}(i\text{ has not quit before }t)
 \ge a\ge\Delta/(4M).                                   \tag{35}
\]

By the definitions of \(A\) and \(r\),

\[
 f(r)-f(s)>\Delta/4.                                    \tag{36}
\]

Apply
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` with gain
\(\Delta/4\), source witness \(s\), and receiving witness \(r\). Its
chronology gives `row.start = t`. Its division-free field
`gain_le_liveMass` gives

\[
 \operatorname{row.liveMass}\ge
 \frac{\Delta/4}{2M}=\frac{\Delta}{8M}.                 \tag{37}
\]

Finally
`quittingSurvivalPrefix_eq_opponentSurvivalWeight_mul_own` factors the actual
joint survival through `row.start` as (37) times (35), proving (29). QED.

### Proposition 11.2 (a literal profitable fork at the same reached cut)

The same construction can be made into one executable behavioral deviation,
not just a pair of counterfactual pure times. Let \(\nu|_A\) denote the
subprobability obtained by restricting the prescribed law to the bad set, and
define

\[
 \widetilde\nu=\nu-\nu|_A+a\delta_r.                    \tag{39}
\]

This is a probability law: all removed mass is put on the good receiving
choice \(r\), which is not in \(A\). Realize it by
`quittingStoppingLawBehaviorStrategy` and replace only player \(i\). Exact
stopping-law affinity gives

\[
 \begin{aligned}
 U_i(\sigma[i\leftarrow\widetilde\nu])-U_i(\sigma)
 &=\int_A(f(r)-f(q))\,d\nu(q)\\
 &>a\Delta/4
 \ge \frac{\Delta^2}{16M}.                             \tag{40}
 \end{aligned}
\]

Moreover the original and deviating stopping laws agree at every choice
strictly before \(t=\min(s,r)\). Because the original own-survival through
\(t\) is positive, a stopping law uniquely determines all its hazard rows
strictly before \(t\). Hence the original and deviating live-root profiles
are literally identical before `row.start = t`, and differ first at that cut
itself: if \(t=s\) bad mass is removed there, while if \(t=r<s\) the removed
mass is inserted there. They also have identical opponents. Combining this common-prefix
fact with (29) produces a source-attached fork with:

```text
literal common chronological prefix to t
+ actual joint source reach at t >= Delta^2/(32 M^2)
+ unrestricted behavioral payoff gain > Delta^2/(16 M).
```

This is the strongest honest answer to “can an actual car carry the gain?”
available from the present data: it is an actually reached profitable
**fork**, with both branches sharing the literal past. It still need not put
positive prescribed absorption mass at the cut, so it is not an absorption
car in the train-decomposition sense, and it is not an exact Nash--Bellman
edge.

### Corollary 11.3 (the conditioning-escape example is reselectable)

In Section 6 of
`CODEX_MINER__ACTUAL_PAID_FIRST_DISAGREEMENT_SUFFIX_COMPACTIFICATION.md`, the
chosen supported pair is `source=n+1`, `receiving=n`; its own-survival factor
is \(\varepsilon_n\). But the prescribed date-zero atom has the same bad
value and mass \(1-\varepsilon_n\). The construction above chooses the
earliest bad source, namely date zero, and the same cap receiver at date
\(n\). The resulting paid row starts at zero and has joint reach one. Thus
that regression refutes arbitrary support-pair selection, not the
debt-aware earliest-bad selection.

### Corollary 11.4 (application to the hard residual and full-debt arm)

At any profile where the terminal witness supplies a behavioral gain at
least \(\gamma\), the corresponding semantic debt is at least \(\gamma\).
Theorem 11.1 therefore gives a paid response cut of gain \(\gamma/4\) and
actual reach at least \(\gamma^2/(32M^2)\). This conclusion needs only the
terminal gap, not all-coordinate full debt.

For the stronger full-debt source sequence of this note, semantic convergence
to \(z\) and (5) give, for every player and all sufficiently large \(n\),

\[
 d_i(\operatorname{Sem}(\sigma_n))\ge\delta/2.
\]

Applying Theorem 11.1 with \(\Delta=\delta/2\) produces, for every label,

\[
 \text{gain}\ge\delta/8,qquad
 \text{actual reach}\ge\delta^2/(128M^2).               \tag{38}
\]

Hence any sequence of these selected dates has the exact bounded/cofinal
split required by Theorem 4.2 of `NONLOCAL_RECENTERING_ATTACK.md`: bounded
dates give a one-sided marked object, while cofinal dates give a full
recentered kernel with summable inert past. The deleted-observer typing
problem is solved for the **reselected** row.

The remaining limitation is chronological, not probabilistic. The selection
is made separately on each literal source profile. It does not show that the
selected cuts are nested under the source's outward-prefix maps, and the
later pure-time witness may itself escape after recentering. Even in the
all-Continue regression, selection is merely equivariant in the backward
direction: adding one outward prefix shifts the selected cut one date to the
right. That is not a forward suffix edge. Thus (38) is valid input to the
ordinary compact-kernel theorem, but is not yet an input to a checked
Nash--Bellman return, finite-forward packet, or uniform-equilibrium consumer.

### Checked source attachment for Theorem 11.1

- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `Quitting/Paths/BehaviorStoppingPayoff.lean`;
- `quittingStoppingLawBehaviorStrategy` and
  `quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy` in
  `Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`;
- `quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect` in
  `Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`;
- `quittingBehaviorStoppingLaw_some_toReal`,
  `quittingHazardStopMass_eq_survival_mul_stop`, and
  `quittingHazardNeverMass_le_survival` in
  `Quitting/Paths/BehaviorStoppingLaw.lean`;
- `quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff` in
  `TerminalSemanticPositiveSlopeRectangle.lean`;
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` and
  `QuittingPaidFirstDisagreementRow.gain_le_liveMass` in
  `TerminalSemanticPaidFirstDisagreement.lean`; and
- `quittingSurvivalPrefix_eq_opponentSurvivalWeight_mul_own` in
  `Quitting/Paths/SurvivalPrefixBridge.lean`.

The countable bad-set mass estimate, least-supported-bad-time selection, and
combined constant (29) are ordinary mathematics not yet represented by a
named Lean declaration.
