# Anchored Jensen dichotomy: active singleton passport or separated response square

Author: `CODEX_JOULE`

## Status

Ordinary mathematics, not checked in Lean.  The theorem below independently
audits and strengthens
`SERIAL_ENDPOINT_AUDITOR__VANISHING_JENSEN_CLOCK_COMPRESSION.md`.

The vanishing-loss arm is valid and yields actual near-minimum concentrated
singleton profiles.  The complementary arm is source-attached but not fully
co-localized: on the same strict subsequence it retains the original
near-minimum profile, a uniformly separated class of mass-good deterministic
clocks, and one fixed outsider with two named pure-time responses (including
`Never`), a positive commuting-square charge, and vanishing debt at the
selected response endpoints.  The averaging argument does **not** prove that
the receiving clock of that square is mass-good, finite, or uniformly
off-minimum.  Independent review found this quantifier limitation, which is
retained explicitly below.

The complementary arm is not a return theorem.  Its exact additional output
is a uniform separation statement: every supported deterministic clock which
carries the singleton mass floor stays a fixed distance above the minimum.
The checked paid-cap lift then gives quantitative debt descent or literal
inert stall; neither branch co-realizes the original minimum source, marked
atom, and response square.  That is the smallest remaining co-realization.

This is an internal theorem and audit.  It is not a uniform-equilibrium
theorem, is not Lean-checked, and is not an export.

## 1. Self-contained anchored setting

Fix a Fin4 quitting reward table.  For an actual behavioral profile `P`, put

\[
 U_k(P)=\text{prescribed terminal payoff of }k,
 \qquad
 B_k(P)=\sup_{\tau_k}U_k(P[k\leftarrow\tau_k]),
\]

where the supremum is over unrestricted complete behavioral deviations, and

\[
 d_k(P)=B_k(P)-U_k(P),\qquad D(P)=\sum_kd_k(P).
\]

Let

\[
 D_*=\inf\{D(P):P\text{ an actual behavioral profile}\}>0.
\tag{1.1}
\]

Let `sigma_n` be actual profiles and `a_n` finite anchor dates such that

\[
 e_n:=D(\sigma_n)-D_*\longrightarrow0.
\tag{1.2}
\]

Fix one owner `j`.  Assume that the source singleton mass on dates at or
after the anchor has a uniform floor:

\[
 M_n:=\sum_{t\ge a_n}
   \Pr_{\sigma_n}(\text{terminal }\{j\}\text{ at }t)\ge\mu,
 \qquad 0<\mu\le1.
\tag{1.3}
\]

Condition the owner's stopping law after survival to `a_n`.  Its conditional
law is a probability `alpha_n` on

\[
 \{a_n,a_n+1,\ldots\}\cup\{\infty\}.
\]

For finite `t`, let `P_{n,t}` be the actual profile which:

- copies every player, including `j`, strictly before `a_n`;
- makes `j` Continue from `a_n` through `t-1` and Quit surely at `t`;
- copies `j` after `t` (an unreachable choice under the component); and
- leaves every opponent literally unchanged.

Let `P_{n,infinity}` make `j` Never after the anchor while copying the same
prefix.  Positive `M_n` implies that the owner's survival probability at the
anchor is positive, so this conditional law is well defined.

This is a genuine mixture of complete behavioral stopping laws:

\[
 \sigma_n=\int P_{n,t}\,d\alpha_n(t)
\tag{1.4}
\]

in terminal-law semantics.  The equality holds after replacing any fixed
player other than `j` by any complete behavioral deviation.  The anchored
form is stronger than date-zero disintegration: every component retains the
literal source prefix through `a_n-1`.

For finite `t`, define

\[
 m_{n,t}:=\Pr_{P_{n,t}}
   (\text{terminal }\{j\}\text{ at }t),
 \qquad m_{n,\infty}:=0.
\tag{1.5}

The singleton tail disintegrates exactly:

\[
 M_n=\int m_{n,t}\,d\alpha_n(t).
\tag{1.6}

## 2. Exact Jensen ledger

Every prescribed payoff is affine in (1.4):

\[
 U_k(\sigma_n)=\int U_k(P_{n,t})\,d\alpha_n(t).
\tag{2.1}
\]

The owner's cap is unchanged because all of its opponents are unchanged:

\[
 B_j(P_{n,t})=B_j(\sigma_n).
\tag{2.2}
\]

For an outsider `i != j`, every fixed deviation payoff is affine, and taking
the supremum gives

\[
 B_i(\sigma_n)\le\int B_i(P_{n,t})\,d\alpha_n(t).
\tag{2.3}
\]

Put

\[
 J_{n,i}:=\int B_i(P_{n,t})\,d\alpha_n(t)-B_i(\sigma_n)\ge0,
 \qquad
 J_n:=\sum_{i\ne j}J_{n,i}.
\tag{2.4}
\]

Payoff affinity and (2.2) give the exact total identity

\[
 \boxed{
 \int\bigl(D(P_{n,t})-D_*\bigr)\,d\alpha_n(t)
 =e_n+J_n.}
\tag{2.5}
\]

This uses unrestricted behavioral caps.  Pure-time responses enter later
only through the exact theorem that their supremum equals the unrestricted
cap; no stationary-cap substitution occurs.

## 3. The exhaustive source-attached dichotomy

Define the supported mass-good clock set

\[
 G_n:=\{t<\infty:\alpha_n(t)>0, m_{n,t}\ge\mu/2\}
\tag{3.1}
\]

and

\[
 \delta_{n,t}:=D(P_{n,t})-D_*\ge0,
 \qquad
 a_n^*:=\inf_{t\in G_n}\delta_{n,t}.
\tag{3.2}
\]

From (1.6), exactly as in the audited note,

\[
 \alpha_n(G_n)\ge
 \beta:=\frac{\mu}{2-\mu}>0.
\tag{3.3}
\]

Thus `G_n` is nonempty.

### Theorem 3.1 (anchored active-passport/separated-square dichotomy)

After passing to a strict subsequence, one of the following two alternatives
holds.

#### A. Active concentrated singleton passport

There are supported finite clocks `t_n in G_n` such that

\[
 D(P_{n,t_n})\longrightarrow D_*,
 \qquad
 m_{n,t_n}\ge\mu/2.
\tag{3.4}
\]

All these actual profiles retain the source before `a_n` and retain every
opponent completely.  After one further subsequence, one fixed player has an
actual complete behavioral deviation at `P_{n,t_n}` whose payoff gain is at
least

\[
 \boxed{\mu D_*/16.}
\tag{3.5}
\]

#### B. Uniformly separated mass-good clocks and a fixed response square

There are constants `eta,g>0`, one fixed outsider `i != j`, supported clock
pairs `s_n,t_n`, pure response times `q_n^- ,q_n^+` in
`Nat union {Never}`, and errors `epsilon_n -> 0` such that:

1. the original source profiles still satisfy (1.2)--(1.3);
2. every supported mass-good clock is uniformly off the minimum:

   \[
   \boxed{t\in G_n\Longrightarrow D(P_{n,t})\ge D_*+\eta;}
   \tag{3.6}
   \]

3. writing

   \[
   V_{n,u}(q):=U_i(P_{n,u}[i\leftarrow Q_q]),
   \tag{3.7}
   \]

   the receiving edge and the full commuting-square charge obey

   \[
   V_{n,t_n}(q_n^+)-V_{n,t_n}(q_n^-)\ge g,
   \tag{3.8}
   \]

   \[
   \boxed{
   [V_{n,t_n}(q_n^+)-V_{n,t_n}(q_n^-)]
   -[V_{n,s_n}(q_n^+)-V_{n,s_n}(q_n^-)]\ge g;}
   \tag{3.9}
   \]

4. both selected responses are approximately cap-attaining at their own
   clock components:

   \[
   d_i(P_{n,t_n}[i\leftarrow Q_{q_n^+}])\le\varepsilon_n,
   \qquad
   d_i(P_{n,s_n}[i\leftarrow Q_{q_n^-}])\le\varepsilon_n;
   \tag{3.10}
   \]

5. the two named responses have a finite first-disagreement date `r_n`; if
   the receiving owner clock `t_n` is finite, then

   \[
   r_n\le t_n.
   \tag{3.11}
   \]

The supported clocks `s_n,t_n` in the square need not belong to `G_n`.
In particular, `t_n` may be `Never`, and (3.6) does not imply that its
component is off-minimum or carries the singleton mass floor.  Independently,
every clock in `G_n` carries the fixed singleton mass floor and the literal
gain conclusion (3.5), but the present argument does not put that gain and
the response square on the same component.

The four corners in (3.9) are actual profiles.  The owner-clock and outsider-
response replacements commute because `i != j`; every corner has the same
literal pre-anchor prefix and the same two named unilateral replacements.

### Proof

If `liminf a_n^*=0`, choose a strict subsequence and `t_n in G_n` with
`delta_(n,t_n)->0`.  This gives (3.4).

At the suffix beginning at `t_n`, owner `j` Quits surely at the first root,
so the joint all-Continue mass is zero.  The arbitrary-root cap decomposition
therefore gives

\[
 D(\text{marked suffix})
 =\sum_k\operatorname{Def}_k(B(\text{post-tail}),q_n)\ge D_*.
\tag{3.12}
\]

Some coordinate has cap defect at least `D_*/4`.  The marked live probability
is at least the singleton stage mass `mu/2`.  If the selected coordinate is
not `j`, the sure quitter screens the continuation and a literal Boolean
endpoint realizes the defect.  If it is `j`, prescribe Continue at the mark
and use an unrestricted post-mark response within `D_*/8` of its tail cap.
Splicing that deviation after the unchanged past gives gain at least

\[
 (\mu/2)(D_*/4-D_*/8)=\mu D_*/16.
\]

Finite pigeonhole fixes the gaining player, proving Alternative A.  This
localization uses only membership in `G_n`, not the convergence in (3.4).
Hence the fixed-gain conclusion is also available at any selected mass-good
component in Alternative B; what is absent there is near-minimality and
co-localization with the Jensen square.

Otherwise, after a strict subsequence there is `eta>0` such that
`a_n^*>=eta`, which is (3.6).  Equations (2.5) and (3.3) imply

\[
 e_n+J_n
 \ge\int_{G_n}\delta_{n,t}\,d\alpha_n(t)
 \ge\beta\eta.
\tag{3.13}
\]

Since `e_n->0`, eventually

\[
 J_n\ge\beta\eta/2.
\tag{3.14}
\]

There are three outsiders.  At each rank one of them satisfies

\[
 J_{n,i_n}\ge\beta\eta/6.
\tag{3.15}
\]

Pass to a subsequence fixing `i_n=i`, and put

\[
 h:=\beta\eta/6,
 \qquad g:=h/2=\beta\eta/12.
\tag{3.16}
\]

Choose `epsilon_n->0` with `epsilon_n<=h/4`.  For every supported clock `u`,
choose a pure time `q_{n,u}` whose payoff is within `epsilon_n` of
`B_i(P_{n,u})`.  This is valid for the unrestricted cap by pure-time
extremality, and `Never` is included.

Let `T,S` be independent with law `alpha_n`.  Fixed-response affinity in the
owner's stopping-law mixture gives

\[
 \mathbb E_{T,S}V_{n,T}(q_{n,S})
 =\mathbb E_S U_i(\sigma_n[i\leftarrow Q_{q_{n,S}}])
 \le B_i(\sigma_n),
\tag{3.17}
\]

whereas

\[
 \mathbb E_TV_{n,T}(q_{n,T})
 \ge\int B_i(P_{n,t})\,d\alpha_n(t)-\varepsilon_n.
\tag{3.18}
\]

Hence some supported pair `s_n,t_n` satisfies

\[
 V_{n,t_n}(q_{n,t_n})-V_{n,t_n}(q_{n,s_n})
 \ge J_{n,i}-\varepsilon_n\ge h-\varepsilon_n.
\tag{3.19}
\]

Set `q_n^-=q_(n,s_n)` and `q_n^+=q_(n,t_n)`.  Approximate optimality at the
source clock gives

\[
 V_{n,s_n}(q_n^+)-V_{n,s_n}(q_n^-)\le\varepsilon_n.
\tag{3.20}
\]

Equations (3.19)--(3.20) imply (3.8)--(3.9), and approximate optimality gives
(3.10).  The checked first-disagreement decoder applied to (3.8) gives the
named row.  If its first disagreement were strictly after a finite receiving
owner clock `t_n`, both outsider responses would agree through the sure Quit
of `j` at `t_n`; absorption there would make their payoffs equal.  This
contradicts (3.8), proving (3.11) in the finite-clock case.  When
`t_n=Never`, the decoder still gives a finite first disagreement because the
two response payoffs differ, but there is no natural-valued receiving-clock
bound.  `QED`

## 4. The exact paid-cap consumer does not restore co-realization

Alternative B is stronger than a paid-row output, but its paid row can also
be sent through the strongest checked generic consumer.

Choose a compact-carrier minimum semantic pair of debt `D_*`.  For every
rank, the first-disagreement row and this minimum define a
`QuittingPaidCapLiftedSource`.  The checked summable-port constructor and
`QuittingPaidCapLiftedSource.exactTrichotomy` return exactly one of:

1. charged cumulative payoff near-return;
2. quantitative cap-displacement debt descent; or
3. literal inert stall.

The first arm already contains a uniform-equilibrium payoff.  By
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`, it
is incompatible with `D_*>0`.  After a subsequence, Alternative B therefore
also carries either quantitative debt descent at every rank or inert stall at
every rank.

This composition is not the missing return.

- In the descent arm, the lower-debt object is a compact semantic-port limit.
  It is not an actual regenerated profile and carries no equality to the
  original anchored source, mass-good owner clock, or singleton atom.  The
  positive drop may tend to zero because no cap-displacement floor is forced.
- In the inert arm, every selected cap prefix is literally all Continue and
  the paid row shifts without loss, but the semantic pair stays equal to the
  selected receiving component.  That component is not known to be
  mass-good or off-minimum.  No marked-mass/minimum return is created.

Thus the positive Jensen branch has been consumed as far as the checked
generic port permits.  What remains is exactly the source/atom co-realization,
not positive curvature, response selection, or first-disagreement decoding.

## 5. Exact Fin4 boundary regression

The following rational actual-profile example shows that no minimum-fiber
clock-support descent or mass-good/minimum co-selection follows from the
mixture identities alone.

Take four players `j,i,d_2,d_3`.  Dummies receive zero at every terminal and
play `Never`.  Active players `j,i` receive one exactly when both belong to
the quitting coalition, and zero otherwise.  Each active player independently
chooses deterministic date zero or date one with probability one half.  This
law is realized by an ordinary behavioral hazard: Quit with probability one
half at zero and, conditional on survival, Quit surely at one.

At the source profile, each active player's expected payoff is `1/2`.  Against
the opponent's two equiprobable dates, every unrestricted behavioral stopping
law has matching probability at most `1/2`; quitting at either pure date
attains it.  Thus every coordinate debt is zero and

\[
 D(\sigma)=D_*=0.
\tag{5.1}
\]

The terminal singleton `{j}` occurs exactly when `j` chooses zero and `i`
chooses one, so it has mass

\[
 \mu=1/4.
\tag{5.2}
\]

Disintegrate `j` into its two deterministic clocks.  At either component the
prescribed payoff of `i` is `1/2`, while `i` can match the now deterministic
clock and obtain one.  The owner remains debt-free.  Hence

\[
 D(P_0)=D(P_1)=1/2,
 \qquad J=1/2.
\tag{5.3}
\]

The date-zero component has singleton `{j}` stage mass `1/2`; the date-one
component has singleton mass zero because `i` has already stopped or stops
simultaneously.  Therefore the only mass-good supported component is a fixed
distance `1/2` above the minimum.

Let the outsider responses be pure dates zero and one.  On `P_0` their
payoffs are respectively one and zero; on `P_1` they are zero and one.  The
oriented receiving gain is one and the commuting-square charge is

\[
 (1-0)-(0-1)=2.
\tag{5.4}
\]

Both correct response endpoints have zero outsider debt.  The owner clock has
support two at the minimum, while every one-clock support reduction is off the
minimum.  Thus even a minimum source, a positive singleton atom, exact
behavioral caps, a fixed response square, and the smallest possible nontrivial
clock support do not force a minimum-fiber support drop.

This regression is not a positive-minimum counterexample: (5.1) has `D_*=0`.
It shows precisely that a theorem producing a finite-rank alternative in
Alternative B must use strict positivity of the minimum in a new way.  It
cannot be a consequence only of affinity, Jensen convexity, singleton mass,
or global minimality.  Its two-date cap calculations are the symmetric
version of the checked `StoppingLawMixtureKink` regression.

## 6. Attachment to the current minimum-singleton source

The theorem is not merely a supplied-profile abstraction.  For a current
Fin4 minimum-law singleton source, use the one chronology supplied by
`FinFourMinimumAtomProducer.nonempty_chronology` in
`Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`.
Set

\[
 \sigma_n=
 \operatorname{prefixedProfile}
   (\text{chronology.profiles}_n,\text{chronology.roots}_n),
 \qquad
 a_n=|\text{chronology.roots}_n|.
\tag{6.1}
\]

The structure field `FinFourMinimumAtomChronology.prefix_debt_tendsto`,
together with
`quittingTerminalDebtSum_eq_terminalSemanticDebtSum`, gives (1.2).  The
theorem `FinFourMinimumAtomChronology.tendsto_prefixedTailMass` and the fixed
singleton identity give (1.3) after discarding finitely many ranks.  The
anchored deterministic completions copy the entire retained root word
literally, unlike a date-zero pure-clock replacement.

This attachment preserves actual profiles, the original source chronology,
all opponents, and the full literal prefix.  It does **not** claim that the
copied root stack remains cap--Nash for a changed clock component.  The
checked theorem `FinFourOwnerCompressedSingletonEndpoint.rootStack_nash` is
explicitly stated only over the unmodified suffix, and changing the owner's
future clock may change other players' unrestricted caps.

Thus Theorem 3.1 is an actual-data exhaustive theorem at the
empty-corner/active-passport seam.  Alternative A is a genuine concentrated
near-minimum output.  Alternative B is a source-attached separated response
square, not a fresh generic paid row.

## 7. Smallest missing co-realization

Alternative B supplies two actual source-attached objects on the same outer
rank, but does not make them the same deterministic-clock component:

* every mass-good clock is uniformly off-minimum and carries the fixed
  executable gain from Section 3; and
* some supported pair carries the fixed separated response square with
  vanishing endpoint debt.

The missing co-realization is to choose the receiving clock of the square in
`G_n`, or to transport the square to a member of `G_n`, while retaining its
charge and endpoint optimality.  Equivalently, current data do not produce a
supported owner clock which simultaneously satisfies

\[
 m_{n,t}\ge\mu/2
 \quad\text{and}\quad
 D(P_{n,t})\longrightarrow D_*.
\tag{7.1}
\]

The response square may live on a mass-poor clock, or on a mass-good clock
which is uniformly off minimum.  The cap-lifted descent limit can lose the
actual clock and atom; the inert lift never leaves the off-minimum semantic
pair.  Therefore the exact next theorem must supply one of only two new
operations:

1. **source-faithful return/reprojection:** turn the separated square into
   actual profiles approaching `D_*` while retaining the anchored prefix, a
   fixed singleton stage mass, and the two named response labels (or the
   resulting fixed executable gain); or
2. **intrinsic finite-rank transition:** from the uniform separation (3.6),
   produce a strictly lower source rank which is invariant under rebasing and
   whose child again carries an actual minimum-source adapter.

The existing first-disagreement row, generic paid-cap trichotomy, normalized
passport minimizer, and response-chord compactification do not provide either
output.  In particular, a compact lower-debt point without the atom is not a
regeneration, and a paid row whose source clock is mass-poor is not an active
passport.

## 8. Declarations and files inspected

- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`;
- `quittingTerminalPayoff_stoppingLawMixture_eq` and
  `quittingContinuationBestResponseValue_stoppingLawMixture_le` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`;
- `quittingTerminalSemanticDebt_stoppingLawMixture_le` and
  `quittingTerminalSemanticDebt_stoppingLawMixture_eq_self` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/TerminalSemanticStoppingLawDebtConvexity.lean`;
- `quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeRectangle.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`;
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
- `QuittingPaidCapLiftedSource.nonempty_summablePort` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`;
- `QuittingPaidCapLiftedSource.exactTrichotomy` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`;
- `quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff` and
  `quittingTerminalDebtSum_eq_terminalSemanticDebtSum` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
- `exists_quittingAnchoredSingletonClockCompression` in
  `Research/Quitting/AnchoredSingletonClockCompression.lean`;
- `FinFourMinimumAtomProducer.nonempty_chronology`,
  `FinFourMinimumAtomChronology.tendsto_prefixedTailMass`, and
  `FinFourOwnerCompressedSingletonEndpoint.rootStack_nash` in
  `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`;
- the exact two-date cap calculations in namespace `StoppingLawMixtureKink`
  in `Research/Quitting/StoppingLawMixtureWitnessStrata.lean`; and
- the normalized-passport and response-chord boundary summarized by the
  named declarations in `docs/FRONTIER.md` and `docs/TOOLKIT.md`.

## 9. Requested check

Please check the conditional stopping-law mixture identity with the common
pre-anchor strategy, the lower bound (3.13), the response-square orientation
and constants in (3.16)--(3.20), and the claim that (3.11) follows whenever
the receiving owner clock is finite.  The substantive open question is
whether strict positive minimum debt, beyond supplying the cap-lift budget,
forces either of the two operations in Section 7.
