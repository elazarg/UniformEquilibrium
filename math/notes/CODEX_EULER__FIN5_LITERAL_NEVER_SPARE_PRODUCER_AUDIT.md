# Fin5 literal-Never spare: conditional theorem and producer audit

**Author:** CODEX_EULER  
**Status (2026-08-25):** conditional deletion theorem `PASS`; literal omitted
label bridge `PROVED`; exhaustive support-descent producer `OPEN`.  Sections
8--11 independently reviewed `PASS` after the scope and quantitative repairs
recorded below in
[`CODEX_MINER`](../feedback/CODEX_EULER__FIN5_LITERAL_NEVER_SPARE_PRODUCER_AUDIT__BY_CODEX_MINER.md).
The
punishment-floor test is unnecessary for the semantic minimum/support
conclusion.  Failures of the conservative `g/kappa/q` tests are not semantic
alternatives.  Sections 8--9 add the exact literal two-reset bridge and a
paid-port handoff for one genuine deletion failure.  Section 11 proves a
stronger uniform handoff: under the terminal gap, every actual deletion
endpoint has a same-source paid row of the full gap and hence feeds the same
checked summable port.

## 1. Question and exact scope

Let `I = Fin 5`, let `reward` be one fixed quitting reward table, and let

\[
  x_0 \longrightarrow x_1 \longrightarrow x_2
\]

be supplied literal behavioral profiles in that same game.  Write
`X_k = Sem(x_k)`,

\[
 d_i^k=B_i(x_k)-U_i(x_k),\qquad
 D_0=\sum_i d_i^0,\qquad
 A_0=\{i:d_i^0>0\}.
\]

Assume `X_0` globally minimizes total terminal-semantic debt and `D_0>0`.
Suppose a four-label certificate omits `w`, and put

\[
  y_w=x_2[w\leftarrow \mathrm{Never}].
\]

The first question is whether the finite sufficient tests in
[`CHATGPT_EXTERNAL__FIN5_LITERAL_NEVER_SPARE_SUPPORT_DESCENT.md`](CHATGPT_EXTERNAL__FIN5_LITERAL_NEVER_SPARE_SUPPORT_DESCENT.md)
really imply that `Sem(y_w)` is another global minimizer with smaller
positive-debt support.  The second, harder question is whether the checked
four-role data produce such a `w`, or turn every failure into terminal
approximation, an admissible exact return, or a maintained rank decrease.

All caps below are over unrestricted complete behavioral deviations.  No
stationary or bounded-controller restriction is used.

## 2. Sources inspected

The narrow source audit used the following checked declarations.

1. `exists_twoMatchedHalfResets_or_firstExcessCharge` in
   `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawGlobalRetention.lean`.
   Its non-excess arm supplies two literal composable half-reset profiles,
   their reset movers/positive debt recipients, and pointwise survival of
   every terminal atom.
2. `exists_counterexampleLocalFourRoleCertificate` in
   `Research/General/FourRoleObstructionReduction.lean`.  It supplies at most
   four selected labels, but on a `SameLawResetCluster` obtained as a limit;
   it does not supply the preceding literal two-reset chain.
3. `exists_fourRoleTransferDefectWindow_or_threeCycle_disjointEdge` in
   `UniformEquilibrium/Diagnostics/Quitting/OneActiveTransferDefectGraph.lean`.
   This is a finite path/defect-edge alternative, not a behavioral-profile
   deletion theorem.
4. `exists_omitted_transferDefectRole_or_sameProfileClockDebtCharge` and
   `exists_omitted_transferDefectRole_of_alignedMinimumRoot` in
   `UniformEquilibrium/Diagnostics/Quitting/OneActiveAlignedRankCollapse.lean`.
   These align an omitted transfer-window label with a supplied clock/root,
   but do not return the five deletion quantities below.
5. `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
   `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`,
   `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
   `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`,
   and `QuittingPaidCapLiftedSource.nonempty_summablePort` in
   `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`.
   These are the checked consumers used only in Section 9.
6. `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
   `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean` and
   `HasTerminalExploitabilityGap` in
   `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.  These give
   the exact arbitrary-profile stopping-law disintegration used in Section 11.
7. The downstream calculation in [`../CAP-PORT-NO.md`](../../CAP-PORT-NO.md).
   It shows that a paid summable cap port has a genuine inert all-Continue
   stall and therefore cannot itself be called a discharge or closure.

Thus there is currently no single checked declaration whose output record is
the literal chain, the four-role omission, and the `g/kappa/q` deletion data.
The conditional theorem remains meaningful when these objects are supplied,
but its item (1) is an ordinary-mathematics composition premise, not presently
one named checked adapter.

## 3. Exact pathwise deletion formulas

Let `mu_2` be the complete terminal-outcome law of `x_2`, extend a reward at
the empty outcome by zero, and define, exactly as in the external note,

\[
m_i^w=\min_{T\subseteq I\setminus\{w\}}
       \bigl(\bar r_i(T)-r_i(\{w\})\bigr),
\]

\[
g_i^w=\sum_{\varnothing\ne T\subseteq I\setminus\{w\}}
 \mu_2(T\cup\{w\})
 \bigl(r_i(T)-r_i(T\cup\{w\})\bigr)
 +\mu_2(\{w\})m_i^w,
\]

and, for `i != w`,

\[
\kappa_i^w=\max\left(0,
 \max_{\varnothing\ne T}\bigl[r_i(T)-r_i(T\cup\{w\})\bigr],
 \max_T\bigl[\bar r_i(T)-r_i(\{w\})\bigr]\right),
\]

\[
q_i^w=\max(0,d_i^2+\kappa_i^w-g_i^w).
\]

### Lemma 3.1 (prescribed-payoff lower bound)

For every player `i`,

\[
 U_i(y_w)-U_i(x_2)\ge g_i^w. \tag{3.1}
\]

**Proof.** Couple the complete stopping laws and change only `w`'s stopping
time to infinity.  If `w` ties a nonempty first coalition `T`, the new first
coalition is `T` and the coordinate change is
`r_i(T)-r_i(T union {w})`.  If `w` is uniquely first, the later outcome of
the other four laws is some `T`, including the empty outcome, and the change
is at least `m_i^w`.  Every path on which `w` is not in the first coalition is
unchanged.  Taking expectations gives (3.1).  This argument includes Never
and arbitrarily late stopping.  QED.

### Lemma 3.2 (unrestricted cap upper bound)

For every `i != w`,

\[
 B_i(y_w)\le B_i(x_2)+\kappa_i^w, \tag{3.2}
\]

whereas

\[
 B_w(y_w)=B_w(x_2). \tag{3.3}
\]

**Proof.** Fix an arbitrary complete behavioral deviation of `i` before
coupling.  The same two event classes as above show pathwise that deleting
`w` raises this deviator's payoff by at most `kappa_i^w`.  The bound is
uniform in the deviation, so taking the supremum proves (3.2).  Player `w`'s
cap depends only on the opponents' laws, which are identical at `x_2` and
`y_w`; this proves (3.3).  QED.

### Corollary 3.3 (conditional support descent)

Assume

\[
 w\in A_0,\qquad g_w^w\ge d_w^2,\qquad
 \sum_{i\ne w}q_i^w\le D_0,\qquad
 q_j^w=0\quad(j\notin A_0). \tag{3.4}
\]

Then

\[
 D(\operatorname{Sem}(y_w))=D_0,
 \qquad
 \operatorname{supp}^{+}d(\operatorname{Sem}(y_w))
 \subseteq A_0\setminus\{w\}. \tag{3.5}
\]

In particular the positive-debt support cardinality strictly decreases.

**Proof.** Since `y_w` is itself an admissible deviation of `w`,

\[
 U_w(y_w)-U_w(x_2)\le B_w(x_2)-U_w(x_2)=d_w^2.
\]

Lemma 3.1 and (3.4) give the reverse inequality, hence equality.  Lemma 3.2
then gives `d_w(y_w)=0` and `d_i(y_w)<=q_i^w` for every `i != w`.  Therefore
`D(y_w)<=D_0`.  The literal pair `Sem(y_w)` belongs to the terminal-semantic
carrier, so global minimality of `Sem(x_0)` gives `D_0<=D(y_w)`.  Equality
follows, as does the support inclusion from the last condition in (3.4).
Because `w in A_0`, the inclusion is strict in cardinality.  QED.

This proves the conditional theorem against unrestricted deviations.

### Repair 3.4 (the floor condition is not a theorem hypothesis)

The condition `U_w(x_2)>=P_w` is not used in Corollary 3.3 and should not be
listed among the conditions needed for semantic minimum/support descent.  It
only proves that the `w` coordinate stays above its punishment floor along
the homotopy from `x_2` to `y_w`: the cap of `w` is constant,
`U_w(y_w)=B_w(x_2)>=P_w`, and the prescribed payoff is affine.

Even with this condition, the note does **not** prove an all-player
floor-admissible homotopy: it assumes no floor inequalities for the other
four coordinates.  Accordingly “`w` is below floor” is not a failed support
descent arm.  It matters only to a later floor-edge consumer that has not
been supplied.

## 4. Strongest exact finite alternative at the literal deletion

The conservative quantities should be separated from the realized semantic
changes.  Define

\[
 \Delta_i^w=U_i(y_w)-U_i(x_2),\qquad
 K_i^w=B_i(y_w)-B_i(x_2).
\]

Then exactly

\[
 d_w(y_w)=d_w^2-\Delta_w^w,
 \qquad
 d_i(y_w)=d_i^2+K_i^w-\Delta_i^w\quad(i\ne w). \tag{4.1}
\]

Moreover `Delta_i^w>=g_i^w`, `K_i^w<=kappa_i^w`, and global minimality gives

\[
 D(y_w)\ge D_0. \tag{4.2}
\]

Consequently, for every omitted `w`, the literal deletion endpoint satisfies
the following inclusive alternative:

1. `w notin A_0` (the omitted label was not an active minimum debtor);
2. `d_w(y_w)>0` (literal Never does not close its debt);
3. `D(y_w)>D_0` (the deletion leaves the minimum fiber);
4. some `j notin A_0` has `d_j(y_w)>0` (a source-inactive coordinate is
   activated); or
5. `Sem(y_w)` is a global minimizer and its positive-debt support is contained
   in `A_0\{w}`.

If (1)--(4) all fail, (5) follows directly from (4.1)--(4.2), and its support
cardinality is strictly smaller.  Unlike failures of the `g/kappa/q` tests,
these four residuals are statements about the actual same-table profile
`y_w`.

This is the strongest exact exhaustive **deletion-endpoint** result obtained
here.  It is separate from the unconditional paid-cap-port trichotomy in
Section 11: a support-deletion endpoint also has a paid port and hence also
lies in exactly one of the three port arms.  Thus the five clauses above and
the three port arms do not form a single mutually exclusive partition.
Present checked
consumers do not turn residual (2), an arbitrary off-minimum deletion in (3),
or the support exchange in (4) into terminal approximation, an admissible
return, or another well-founded rank decrease.

## 5. Why failures of the sufficient tests are not branches

The implications

\[
 \Delta_i^w\ge g_i^w,\qquad K_i^w\le\kappa_i^w,
 \qquad d_i(y_w)\le q_i^w
\]

are one-sided.  Therefore

\[
 g_w^w<d_w^2,\qquad \sum q_i^w>D_0,\qquad q_j^w>0
\]

do not imply, respectively, residual (2), residual (3), or actual activation
of `j`.  The extrema in `m` and `kappa` can be attained on terminal coalitions
which have zero probability against the fixed opponents.

### Exact rational null-event regression

Let the labels be `i=0`, `v=1`, `u=2`, `h=3`, and `w=4`.  At `x`, player `w`
Quits surely at date zero, player `v` Quits surely at date one, and the other
three players Never quit.  Let `y=x[w<-Never]`.  Fix an integer `K>2`.

For player `w`, set

\[
r_w(\{w\})=0,\quad r_w(\{v\})=1,\quad
r_w(\{v,w\})=0,\quad r_w(\{u\})=-K,
\]

and set every other payoff relevant to a unilateral stopping time of `w`
against these opponents at most one.  Then

\[
U_w(x)=0,\quad B_w(x)=B_w(y)=1,\quad U_w(y)=1.
\]

Thus `d_w(x)=1`, deletion closes `w` exactly, but
`g_w^w<=-K<d_w(x)` because the minimum in `m_w^w` sees the unreachable
coalition `{u}`.

For player `i`, set all rewards attainable against the displayed opponents
to zero, while setting

\[
r_i(\{u\})=K,\qquad r_i(\{u,w\})=0.
\]

The opponent `u` Never quits, so unrestricted deviations of `i` still give

\[
U_i(x)=B_i(x)=U_i(y)=B_i(y)=0.
\]

Nevertheless `kappa_i^w>=K`, hence `q_i^w>=K`: the conservative budget and
inactive-coordinate tests can fail although the actual debt of `i` remains
zero.

For an equality-fiber local check, assign player `h`

\[
r_h(\{w\})=0,\quad r_h(\{h,w\})=1,\quad
r_h(\{v\})=0,\quad r_h(\{h\})=2,
\]

with all other payoffs attainable by `h` against the displayed opponents no
larger than the shown maxima.  Then unrestricted pure-time extremality gives

\[
d_h(x)=1,\qquad d_h(y)=2,\qquad
D(x)=D(y)=2,
\]

and the actual support drops from `{w,h}` to `{h}`, even though the displayed
`g` and `q` sufficient tests fail.

To make this a complete rational reward table, set every reward coordinate
not explicitly displayed above equal to zero.  In particular the qualifications
“relevant payoff at most one” and “attainable payoff no larger than the shown
maximum” then hold literally.  Against `x`, the only possible first outcome
under a unilateral deviation by `h` is `{w}` or `{h,w}`; against `y`, it is
`{h}`, `{v}`, or `{h,v}`.  The corresponding statement for `i` has only the
same finite list with `i` in place of `h`.  Hence the cap computations above
already cover every unrestricted randomized stopping law by convex averaging
of its pure stopping-time outcomes.

This is an exact same-table behavioral regression for the logical direction
of the proposed tests.  It is deliberately **not** claimed to be a positive
global-minimum counterexample: producing an explicit Fin5 reward table with
the full terminal-exploitability/global-positive-minimum source hypotheses
would itself be a negative resolution of the open conjecture.  Thus the
regression invalidates treating test failure as a semantic branch; it does
not falsify the conditional theorem under its full hypotheses.

## 6. Producer verdict

The literal-Never deletion theorem is valid, after removing the irrelevant
floor condition from its semantic conclusion.  It is a supplied-object
verifier and a genuine support-rank decrease when (3.4) is met.

The requested universal producer is not established:

* omission of `w` is label incidence only and does not imply `w in A_0`;
* `g_w^w>=d_w^2` is not produced by either literal reset theorem;
* `sum q_i^w<=D_0` and the inactive `q` conditions use worst-case extrema and
  are not necessary conditions for actual descent;
* below-floor `w` is irrelevant to semantic support descent, while a genuine
  all-player floor path needs additional hypotheses; and
* none of the checked declarations above consumes the exact realized
  residuals (2)--(4).

The right next producer statement must be formulated using the exact
`Delta/K/d(y_w)` data, or must add attainment/support restrictions that turn
the conservative extrema into actual events.  Proving that every exact
residual (1)--(4) is consumed would be a substantive Fin5 conjecture-facing
theorem; it cannot be inferred from four-role cardinality alone.

## 7. Review request

Please independently check:

1. the unique-first/tie decomposition in Lemma 3.1;
2. the arbitrary-deviation supremum passage in Lemma 3.2;
3. removal of the punishment-floor hypothesis from Corollary 3.3;
4. the exact realized alternative in Section 4;
5. the unrestricted pure-time cap calculations in the null-event regression;
   and
6. the source-interface distinction among the three checked declaration
   families in Section 2.

## 8. Literal two-reset to omitted-label bridge

The provenance split in Section 2 does **not** obstruct the elementary
omitted-label selection once the ordinary four labels have been placed on the
literal non-excess reset output.  The following finite bridge is exact.

### Proposition 8.1 (literal omitted-label bridge)

Suppose
`exists_twoMatchedHalfResets_or_firstExcessCharge` is in its non-excess arm.
Write `a` for the first mover, `b` for the positive recipient/second mover,
and `c` for the positive recipient of the second reset.  Let `ell` be any
fourth label supplied by the incidence/toggle readout, and put

\[
L=\{a,b,c,\ell\}\subseteq\operatorname{Fin}5.
\]

Then there is `w notin L`.  Moreover the literal complete stopping law of `w`
is identical in `x_0`, `x_1`, and `x_2`.

**Proof.**  The finite set `L` has cardinality at most four, whereas
`Fin 5` has cardinality five, so its complement is nonempty.  The first
literal profile update changes only `a`; the second changes only `b`.
Since `w` is distinct from both, function-update evaluation gives

\[
x_0(w)=x_1(w)=x_2(w).
\]

Thus `y_w=x_2[w<-Never]` is an actual third unilateral update on the same
reward table and literal profile chain.  No cluster-limit or abstract-path
identification is needed for this statement.  QED.

This bridges the literal reset output to an omitted label, but deliberately
does not assert any deletion inequality for that label.

### Corollary 8.2 (active spare or proper ambient support)

For the same role set `L`, either

\[
\exists w\in A_0\setminus L,
\]

or

\[
A_0\subseteq L,\qquad |A_0|\leq4<5.                  \tag{8.1}
\]

In particular, if the selected positive minimum has full debt support, every
omitted label is active and the inactivity obstruction disappears.

This is a strict reduction from the ambient full-support rank five to a
proper active support when the second branch occurs.  It is **not** a
minimum-fiber transition between two carrier pairs and therefore should not
be substituted for `HasMinimumFiberSupportRankDescent`, whose checked output
requires a new tangent family at a strictly smaller-support endpoint.

## 9. A genuine closure failure has an actual paid-source consumer

Although failure of `g_w>=d_w^2` has no semantic meaning, the exact residual

\[
d_w(y_w)>0                                            \tag{9.1}
\]

does.  It produces a source-matched paid row without any stationary
restriction.

### Proposition 9.1 (Never residual to paid cap-lifted port)

Assume (9.1), and fix `eta` with `0<eta<d_w(y_w)`.  Then there is a finite
pure stopping time `t` such that

\[
U_w(y_w[w\leftarrow t])-U_w(y_w)
   >d_w(y_w)-\eta>0.                                  \tag{9.2}
\]

Consequently the checked first-disagreement decoder gives a
`QuittingPaidFirstDisagreementRow` on the literal source `y_w`, with observer
`w` and any fixed gain below `d_w(y_w)-eta`.  Pairing that row with the
original positive global minimum constructs a `QuittingPaidCapLiftedSource`,
and `QuittingPaidCapLiftedSource.nonempty_summablePort` supplies its exact
summable-absorption cap port.

**Proof.**  Against the fixed opponent profile `y_w[-w]`, every complete
behavioral strategy of `w` induces a probability law on
`Option Nat`, and its terminal payoff is the expectation of the corresponding
pure-time payoffs.  The supremum of an average is bounded by the supremum of
its atoms.  Equivalently, use the checked exact identity
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`.  Since the baseline
prescribed law is literally Never and its gap to the unrestricted cap is
`d_w(y_w)>0`, the definition of supremum gives a pure time with (9.2).  Never
itself cannot realize the strict gain, so `t` is finite.  Apply
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` with source
witness `Never` and receiving witness `t`.  The definition of
`QuittingPaidCapLiftedSource` asks only for an attained paid row and an
independently supplied positive global minimum, both now available.  QED.

This consumes the **actual** closure failure into the checked paid-port lane.
It does not produce a cumulative exact return: the current paid-port theorem
has summable absorption and an all-Continue semantic port, while the frontier
still lacks a source-matched restart or positive admissible return.  Hence
Proposition 9.1 is a precise handoff, not completion of the user-requested
cumulative-return alternative.

## 10. Updated producer boundary

The automatic literal bridge is true, so no negative construction to that
bridge exists.  The exact consequences now are:

1. inactive omitted labels force the role-supported proper-rank alternative
   (8.1), with the stated warning that this is not an endpoint descent;
2. an active omitted label satisfying the exact deletion conditions gives the
   strict minimum-fiber support descent of Section 4;
3. exact failure to close the deleted label gives the attained paid-source
   handoff of Proposition 9.1; and
4. the remaining genuine residuals are strict off-minimum debt after deletion
   and actual activation of a source-inactive coordinate.

No checked theorem found in the bounded search turns residual (4) into a
cumulative exact return or a new tangent-family support-rank descent.  The
ordinary first-entry point on the deletion homotopy is not, by itself, a
`HasQuittingStoppingLawFlatSupportEntry`: that checked predicate requires a
normalized flat tangent column extracted at the positive-minimum base.  Thus
identifying these two notions would be an invalid provenance shortcut.

## 11. Uniform paid-port source unification for every deletion endpoint

The preceding residual split can be simplified at the behavioral interface.
The fixed positive terminal gap produces an attained paid first-disagreement
row at **every** actual profile.  Unlike Proposition 9.1, the source strategy
need not be Never and neither pure-time witness need be finite.

### Lemma 11.1 (exact two-pure-time span at an arbitrary profile)

Let `sigma` be any behavioral profile in a finite quitting game.  Assume

\[
  0<\gamma,
  \qquad
  \operatorname{HasTerminalExploitabilityGap}(r,\gamma).
\]

Then there are a player `j` and two pure stopping times
`sourceTime, receivingTime : Option Nat` such that

\[
 V_j(\mathrm{receivingTime})-
 V_j(\mathrm{sourceTime})\geq\gamma,                 \tag{11.1}
\]

where `V_j(q)` is player `j`'s payoff after replacing only its strategy in
`sigma` by the pure-time strategy `q`.  In particular the two times are
distinct, and the checked decoder returns a
`QuittingPaidFirstDisagreementRow r sigma j gamma`.

**Proof.**  Apply the terminal-gap hypothesis at `sigma`, obtaining `j` and a
behavioral replacement `tau` with

\[
 U_j(\sigma[j\leftarrow\tau])-U_j(\sigma)\geq\gamma.
                                                               \tag{11.2}
\]

Let `mu_tau` be the complete stopping law of `tau`, and let `mu_sigma` be the
complete stopping law of the prescribed strategy `sigma(j)`.  The exact
checked disintegration
`quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime`, applied once
to `tau` and once to `sigma(j)`, gives

\[
 U_j(\sigma[j\leftarrow\tau])=\mathbb E_{\mu_\tau}V_j,
 \qquad
 U_j(\sigma)=\mathbb E_{\mu_\sigma}V_j.              \tag{11.3}
\]

Take the product of the two countable probability laws.  If (11.1) failed for
every pair of support atoms, then the bounded random variable

\[
 (q,s)\longmapsto V_j(q)-V_j(s)
\]

would be strictly below `gamma` at every positive-mass atom.  A probability
mass function has a nonempty support.  Choose one positive product atom; the
nonnegative deficit `gamma-(V_j(q)-V_j(s))` is strictly positive there.
Boundedness makes the deficit integrable, so its expectation is strictly
positive.  Hence

\[
 \mathbb E_{\mu_\tau}V_j-\mathbb E_{\mu_\sigma}V_j<\gamma,
\]

contrary to (11.2)--(11.3).  Thus a support pair satisfying (11.1) exists.
Since `gamma>0`, its two coordinates differ.  Now apply
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` with these
source and receiving witnesses.  This proof covers finite times and Never on
either side; it does not replace the countable stopping laws by a finite
horizon.  QED.

The strict-average step is essential.  Merely approximating the unrestricted
cap by a pure time would generally lose an arbitrary `eta`; comparing the
attained deviation law to the attained prescribed law yields the full weak
gain `gamma`.

### Corollary 11.2 (uniform source unification for the deletion alternatives)

Assume the Fin5 terminal witness supplies the fixed positive gap `gamma` and
the positive global semantic minimum `X_0`.  For every omitted label `w`, let
`y_w=x_2[w<-Never]`, with no deletion inequality assumed.  Lemma 11.1 applied
at the literal profile `y_w` produces an attained same-source paid row of gain
`gamma`.  Pairing this row with `X_0` gives a
`QuittingPaidCapLiftedSource`; the checked theorem
`QuittingPaidCapLiftedSource.nonempty_summablePort` supplies an exact
summable-absorption cap port.  For each selected port, the checked theorem
`QuittingPaidCapLiftedSource.exactTrichotomy` gives an unconditional,
pairwise-disjoint alternative:

1. `ChargedNearReturn`;
2. `QuantitativeDebtDescent`; or
3. `InertStall`.

This trichotomy applies independently of which deletion-endpoint clause in
Section 4 holds.  In particular the support-deletion endpoint is not a fourth
port arm, and support descent may coexist with any one of these three arms.

Consequently all genuine actual-profile outcomes of the deletion test feed
one uniform checked **source interface**:

* failure to close the omitted player's debt;
* strict total-debt increase `D(Sem(y_w))>D_0`;
* activation at `y_w` of a coordinate inactive at `X_0`; and
* the successful minimum-fiber support-deletion endpoint itself.

The player selected by Lemma 11.1 need not be the omitted label, the newly
activated label, or either reset mover.  This is a consumer, not an incidence
alignment theorem.  It also consumes the inactive-omission branch of
Corollary 8.2 at its actual endpoint without pretending that
`|A_0|<=4` alone is a maintained descent.

### Exact remaining obstruction

Corollary 11.2 removes the distinction among conservative SC4/SC5 failures at
the paid-source interface: only the actual endpoint debts/support matter, and
every endpoint reaches the same paid summable-port theorem with the same
gain `gamma`.  Its status is **source unification only**.

Indeed the exact downstream cap-port calculation has three exhaustive,
pairwise-disjoint arms for the selected port.
Positive cumulative absorption with zero cap displacement feeds the checked
cumulative near-return compiler.  Positive cap displacement `rho` gives the
checked quantitative semantic-debt decrement

\[
 D(\operatorname{Sem}(y_w))-D_\infty
 \geq D_0\,\rho/(2R),
 \qquad R=\operatorname{quittingRewardBound}(r),       \tag{11.4}
\]

in the positive-displacement arm.  Here the left endpoint is the debt of the
actual source `Sem(y_w)`, whereas the multiplier is the debt `D_0` of the
independently supplied global minimum.  It would be wrong off the minimum
fiber to replace the left side by `D_0-D_infinity`.  If
`E_w=D(Sem(y_w))-D_0`, global minimality and (11.4) give

\[
 0\leq D_\infty-D_0
 \leq E_w-D_0\rho/(2R)<E_w.                           \tag{11.5}
\]

This is a strict decrease of off-minimum excess on the selected slice, but is
not a well-founded decrement uniformly as `rho` tends to zero across
restarts.  The division in (11.4) is used only in the positive-displacement
arm, where the checked estimate `rho<=2 R A` forces `R>0`.  Zero total
absorption is the literal inert stall: every selected
root is all Continue, while cap, prescribed payoff, debt, and the losslessly
shifted paid row all stay quantitatively constant.  The paid row does not
contradict this last arm because it concerns pure-time deviations of the
literal prescribed profile, whereas the roots are Nash against the cap
annotation.  The missing coordinatewise continuation-option surcharge
identity is not supplied here.

### Corollary 11.3 (minimum-fiber sources force the inert port under a witness)

Put `z_w=Sem(y_w)`.  Under the positive terminal-gap counterexample witness,

\[
 D(z_w)=D_0 \quad\Longrightarrow\quad
 \operatorname{InertStall}(\text{the selected port from }y_w). \tag{11.6}
\]

Indeed the charged arm produces a uniform-equilibrium payoff, contradicting
the terminal-gap witness.  In the quantitative arm, (11.4) gives
`D_infinity<D(z_w)=D_0`, while the checked port limit remains in the terminal
semantic carrier; this contradicts global minimality.  Therefore only the
inert arm remains.  No failure of strict support descent is needed.  The
minimum-fiber classification (11.6) and the support conclusion of Section 4
are logically independent facts about the same actual deletion endpoint.

Therefore Section 11 does **not** prove terminal approximation, cumulative
exact return, or a well-founded rank decrease.  No checked result identifies
the limiting carrier pair with the original deletion source, eliminates the
inert stall using the four-role/minimum data, makes the positive-displacement
slices into a maintained rank, or restarts the Fin5 construction at the port.
The unresolved producer is a single port-to-return/restart or inert-stall
elimination problem, not separate SC4 and SC5 cases.

### Why the supplied Fin5 data do not yet eliminate the inert stall

The literal reset/omission data remain attached to the suffix `y_w`.  In the
inert arm, prefixing an all-Continue root merely delays that suffix, so these
data persist but impose no positive absorption on the cap-Nash selector.  The
positive global minimum `X_0` is a separate carrier point; it supplies the
lower debt bound needed by the cap lift, not an equality between the cap and
prescribed coordinates of `y_w`.  Finally, the observer selected by Lemma
11.1 is unconstrained relative to the four role labels and the deleted label.

Accordingly none of the supplied fields implies the missing surcharge
identity

\[
 -\Delta_i(B(y_w),\mathbf C)=B_i(y_w)-U_i(y_w),
\]

nor a positive absorption probability for the selected exact cap root.  The
ambient proper-support alternative in Corollary 8.2 also lives at `X_0`; it is
not a comparison between `X_0` and the cap-port limit.  Thus there is no
legitimate inherited natural-valued rank on which to charge a sequence of
positive but shrinking cap displacements.  Eliminating the inert arm requires
a new source-matched surcharge, root-positivity, or restart theorem; it is not
a further consequence of SC4/SC5 bookkeeping.

## 12. Delta review request

Please independently falsify Sections 8--11, especially:

1. literal profile provenance in Proposition 8.1;
2. the distinction between ambient `|A_0|<=4` and a maintained endpoint rank;
3. the product-stopping-law strict-average argument in Lemma 11.1;
4. use of the full weak gap `gamma` rather than `gamma-eta`;
5. same-profile paid-row provenance at each `y_w`; and
6. the precise nonclaim that a paid summable port is not a cumulative exact
   return or a new minimum-fiber descent.
