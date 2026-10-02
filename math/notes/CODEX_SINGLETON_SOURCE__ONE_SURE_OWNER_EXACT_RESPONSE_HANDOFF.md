# One-sure product minima have an exact owner-response handoff

Identity: CODEX_SINGLETON_SOURCE  
Date: 2026-08-31  
Status: **ordinary mathematics proof; two independent PASS reviews.** The
standalone cap and incidence content is retained in
`revisit/ONE_SURE_PRODUCT_MINIMUM_EXACT_OWNER_RESPONSE_HANDOFF.md`. The former
descent route is superseded by the checked finite-clock paid-port reduction.

Post-export research delta: Section 4A below strengthens the equality arm to
a **self-dispatch** whose returned semantic pair is definitionally the literal
response target.  Section 9 gives a bounded-calendar response construction,
removes persistent mixed zero-debt timing as a separate residual, and applies
cap Jensen to the pure same-stage cycle.  These deltas have not yet received
an independent review and are not part of the frozen export.

## 1. Question and input

Assume the Fin4 hard-residual contradiction regime and let

\[
 z=(U,B),\qquad D(z)=D_*>0,
\]

be an attained global minimum of terminal semantic debt.  Suppose the
attaining profile is the finite padded-product profile

1. all players Continue at the padding date;
2. one product root \(q\) is played;
3. after all Continue at that root, everyone plays Never.

Assume that the maximal sure-quitter core is the singleton

\[
 K=\{k\},\qquad q_k=1,\qquad q_j<1\quad(j\ne k),
\tag{1.1}
\]

and that the minimum is full-debt:

\[
 d_i(z)>0\qquad(i\in\operatorname{Fin}4).
\tag{1.2}
\]

This is exactly the positive-singleton boundary produced at the end of the
former reviewed sure-core descent in
[`ZERO_SINGLETON_BEHAVIORAL_LAW_PRODUCT_BASE_AND_SURE_CORE_DESCENT.md`](../formalized/ZERO_SINGLETON_BEHAVIORAL_LAW_PRODUCT_BASE_AND_SURE_CORE_DESCENT.md).
That superseded route's boundary was much stronger than an arbitrary positive singleton atom:
the whole semantic pair, the law, the unique absorbing product date, and the
post-root Never continuation are attained by one literal profile.

The question is what can be obtained without discarding that source.

## 2. Exact complete cap of the sure owner

### 2.1 The entrance padding is dispensable before the final softening

The reviewed entrance theorem used an all-Continue padding row.  Its stronger
no-padding form is valid.  At the original product-law entrance there are at
least two sure quitters, so prescribed play absorbs at the product root, and
after any one player deviates at least one opponent still Quits surely.  The
one-root-followed-by-Never cap is therefore \(\max\{Q_i,C_i\}\), whereas the
padded cap is \(\max\{s_i,Q_i,C_i\}\).  The strict minimum margin makes
\(s_i\) nonbinding, so removing the padding preserves the complete semantic
pair and law exactly.

Repeating that product root stationarily is also semantically identical:
prescribed absorption is at the first date, and every unilateral deviation
still faces an opponent who Quits at the first date.  Thus the stronger
formalization target should be the product root followed by Never (and its
stationary repetition), with the padded statement retained as a corollary.

After the sure-core rank reaches one, removing the padding is still harmless
for the displayed attained minimum because the padding option \(s_i\) is
strictly below \(B_i\).  However, when the sole sure owner deviates to
Continue, the all-opponents-Continue branch can be reached.  The literal
post-root Never continuation and the next-date singleton option must then be
kept in the cap calculation below.

Write

\[
 s_i=r_i(\{i\}).
\]

Against the opponents' product marginals \(q_{-i}\), define

\[
 Q_i=
 \sum_{A\subseteq I\setminus\{i\}}
 p_{q_{-i}}(A)r_i(A\cup\{i\}),
\tag{2.1}
\]

and

\[
 C_i=
 \sum_{\varnothing\ne A\subseteq I\setminus\{i\}}
 p_{q_{-i}}(A)r_i(A)
 +p_{q_{-i}}(\varnothing)\max\{0,s_i\}.
\tag{2.2}
\]

Here \(Q_i\) is attained by Continuing through the padding row and Quitting
at the product root.  The value \(C_i\) is attained by Continuing at the
product root and then, if every opponent also Continued, either Quitting alone
at the next date when \(s_i\geq0\), or playing Never when \(s_i<0\).

With the padding retained, these three pure choices exhaust the complete
behavioral cap:

\[
 B_i=\max\{s_i,Q_i,C_i\}.
\tag{2.3}
\]

Indeed, a deviator may Quit at the padding date, giving \(s_i\), or Continue
to the unique product date.  At that date arbitrary private behavioral
randomization is a convex combination of Quit and Continue.  Conditional on
Continue and opponent survival, the opponents subsequently play Never, so
every future stopping law is a convex combination of a singleton Quit payoff
\(s_i\) and Never payoff zero.  This includes arbitrarily late stopping and
Never; no stationary restriction is being used.

The checked global-minimum singleton moat gives

\[
 B_i-s_i\geq D_*>0.
\tag{2.4}
\]

Thus the padding-date Quit is strictly suboptimal and the identical unpadded
profile has cap

\[
 B_i=\max\{Q_i,C_i\}.
\tag{2.5}
\]

For the sure owner \(k\), prescribed play Quits at the product root, hence

\[
 U_k=Q_k.
\tag{2.6}
\]

Full debt and (2.5) imply the strict identity

\[
 B_k=C_k>Q_k,
 \qquad
 C_k-Q_k=d_k(z)>0.
\tag{2.7}
\]

## 3. Literal exact debt-killing response

Let \(\widehat\sigma\) be the actual profile obtained by replacing only
player \(k\)'s complete strategy with the response attaining \(C_k\):

* Continue at the padding row and at the product root;
* if the opponents absorb at the product root, accept that terminal outcome;
* if all opponents Continue, Quit alone at the next date when \(s_k\geq0\),
  and otherwise play Never.

All opponents, calendar dates, product marginals, and the literal post-root
continuation are retained.  Since only player \(k\)'s strategy changes, its
unrestricted best-response cap is unchanged.  Equations (2.6)--(2.7) give

\[
 U_k(\widehat\sigma)-U_k(\sigma)
 =C_k-Q_k=d_k(z)>0,
\tag{3.1}
\]

\[
 B_k(\widehat\sigma)=B_k(\sigma),
 \qquad
 d_k(\widehat\sigma)=0.
\tag{3.2}
\]

Thus this is an exact complete-behavioral paid edge which kills the mover's
debt.  It is not inferred from positive singleton mass and it does not require
clock compression.

Let

\[
 \widehat z=\operatorname{Sem}(\widehat\sigma).
\]

Carrier minimality gives

\[
 D(\widehat z)\geq D_*.
\tag{3.3}
\]

Therefore exactly one of the following holds:

1. \(D(\widehat z)>D_*\): a literal off-minimum paid target;
2. \(D(\widehat z)=D_*\): an attained positive global minimum with the
   killed coordinate \(d_k(\widehat z)=0\).

The leakage identity is exact:

\[
 D(\widehat z)-D_*
 =-d_k(z)+
   \sum_{j\ne k}\bigl(d_j(\widehat z)-d_j(z)\bigr).
\tag{3.4}
\]

Hence the equality arm transfers exactly all of \(k\)'s old debt to the
other three coordinates.  No coordinatewise leakage control follows.

## 4. Same-target reset-rigid handoff on the equality arm

Assume \(D(\widehat z)=D_*\).  The target is not replaced by an unrelated
minimum realizer.  Adjoin its actual terminal law and use the literal joint
point

\[
 \widehat Z=
 \bigl(\widehat z,\operatorname{Law}(\widehat\sigma)\bigr).
\tag{4.1}
\]

There is in fact positive opponent incidence for the killed owner at this
same target.  Put

\[
 a_{-k}=1-\prod_{j\ne k}(1-q_j).
\tag{4.2}
\]

If \(a_{-k}>0\), this is exactly the probability that the target law's finite
terminal contains an opponent of \(k\).  The repository's total opponent
incidence counts a coalition once per opponent it contains, so it is at least
\(a_{-k}\), not generally equal to it.  Positivity is all the reset theorem
requires.

If \(a_{-k}=0\), every opponent Continues surely at the product root.  When
\(s_k\geq0\), the response law is the pure singleton \(\{k\}\), so
\(U_k(\widehat z)=B_k(\widehat z)=s_k\), contradicting the global-minimum
moat \(B_k-s_k\geq D_*>0\).  When \(s_k<0\), the response law is pure Never,
contradicting the checked theorem that every Fin4 hard-residual global-minimum
joint law has a positive finite atom.  Therefore

\[
 a_{-k}>0.
\tag{4.3}
\]

This direct incidence calculation is stronger than merely selecting some
finite atom after the fact.

It also has a uniform version.  Let \(R>0\) bound all rewards in absolute
value.  The set of global-minimum joint-law points is compact.  Under the
Fin4 hard residual, every point in that set has positive total finite mass;
hence continuity gives a table-dependent constant

\[
 \lambda_{\rm fin}>0
\tag{4.4}
\]

which lower-bounds total finite mass at every global-minimum joint law.  If
\(s_k<0\), the target's only finite outcomes are the nonempty opponent
coalitions at the product root, so \(a_{-k}\geq\lambda_{\rm fin}\).  If
\(s_k\geq0\), equations (2.2), (2.7), and the singleton moat give

\[
 D_*\leq C_k-s_k
 =\sum_{\varnothing\ne A\subseteq I\setminus\{k\}}
   p_{q_{-k}}(A)\bigl(r_k(A)-s_k\bigr)
 \leq 2R a_{-k}.
\]

Consequently every equality target satisfies the uniform incidence floor

\[
 a_{-k}\geq
 \min\left\{\lambda_{\rm fin},\frac{D_*}{2R}\right\}>0.
\tag{4.5}
\]

Because only seven nonempty opponent coalitions are possible in Fin4, one
literal product-root atom has mass at least \(a_{-k}/7\).  Terminal
exploitability then attaches a table-dependent positive strict-toggle gap to
some member or outsider at that atom.  This is a quantitative static passport;
it is not by itself a profitable unilateral deviation, because the remaining
root coalitions can contribute endpoint gains of the opposite sign.

Re-anchor the law-tight cap--Nash saturation construction at the same literal
joint point \(\widehat Z\).  Since the origin belongs to its own hull and is a
global minimum on the entire carrier, \(\widehat Z\) itself is a hull
minimum.  Moreover, no exact cap--Nash prefix can move it.  Exact prefixing by
a root with joint Continue probability \(c\) scales total debt to \(cD_*\);
global minimality and \(D_*>0\) force \(c=1\), hence the root is all Continue
and both semantic pair and law are unchanged.  Same-law debt-nonincreasing
replacements remain on the global minimum fibre.

The checked positive-incidence reset theorem can now be applied directly to
the killed coordinate \(k\), using (3.2) and (4.3).  It supplies a reset-rigid
same-law return with \(\widehat Z\) as the retained point and origin.  Equally,
one may invoke the complete strict classification.  Its three formal chambers
are full debt, reset-rigid, and a singleton/Never binding cycle.  At
\(\widehat Z\):

* the full-debt chamber is impossible by \(d_k(\widehat z)=0\);
* the singleton/Never chamber is impossible by the global singleton moat
  \(B_i-s_i\geq D_*>0\), exactly as in
  `FinFourLawTightCapNashStrictMinimum.lean`.

Therefore the equality target enters the reset-rigid chamber, with
\(\widehat Z\) as its retained source origin.  The classification may select
additional same-law reset data, but it does not reselect the incoming target
or its law.

### 4A. The equality target itself is already the returned reset point

The fixed-law minimizer used above is unnecessary in this special equality
arm.  One can instantiate `QuittingFixedLawResetDispatch` with

\[
 \operatorname{returned}=\widehat z
\tag{4.6}
\]

literally.

The joint-carrier and reset fields are (4.1) and (3.2).  Both debt-order
fields are equalities because

\[
 D(z)=D(\widehat z)=D_*.
\]

The transfer field is also equality: from \(d_k(\widehat z)=0\),

\[
 \sum_{j\ne k}\bigl(d_j(\widehat z)-d_j(z)\bigr)
 =d_k(z).
\tag{4.7}
\]

Positive incidence and the terminal exploitability witness give the supported
toggle.  It remains only to verify the static all-Continue exit.  Choose any
exact product Nash root \(x\) against \(B(\widehat z)\).  Exact prefixing
scales total debt by its joint Continue probability \(c(x)\):

\[
 D(T_x\widehat z)=c(x)D_*.
\]

The prefixed point lies in the carrier, so global minimality gives
\(D_*\leq c(x)D_*\).  Since \(D_*>0\) and \(c(x)\leq1\), one has
\(c(x)=1\), hence \(x\) is all Continue.  Thus all Continue is exact Nash
against the displayed target cap.  Its prefix fixes \(\widehat z\) exactly.

Consequently the equality output retains not merely the same law but the same
literal finite-clock profile externally, while its reset-rigid packet may take
the returned pair to be \(\widehat z\) itself.  This removes a source-selection
seam.  It does **not** create a zero-set rank: a later best response can still
reactivate the killed coordinate, as Section 6.2 shows.  The known renewable
maximum-debt finite-clock response chain therefore applies directly, but its
bounded-order cycles and adjacent-deadline escape remain horizontal rather
than Nash--Bellman chronological paths.

## 5. Fin4 handoff theorem

Combining the reviewed sure-core contraction with Sections 2--4 gives the
source-faithful finite transition

\[
\boxed{
\begin{array}{c}
\text{attained zero-singleton full-debt product minimum}
\\[1mm]\Longrightarrow\\[1mm]
\text{off-minimum paid target}
\quad\lor\quad
\text{reset-rigid minimum}.
\end{array}}
\tag{5.1}
\]

At most three minimum-to-minimum sure-core softenings precede the final owner
response in Fin4.  Every edge is an actual unilateral behavioral replacement
and retains a literal backward payoff gain.  The last equality branch is
re-anchored at the exact response target rather than at a newly selected
minimum realization.

This is a finite-rank transition, not a terminal consumer.  The two outputs
are precisely existing open waist components:

* the off-minimum paid edge still needs a charged return, a renewable descent,
  or a terminal compiler;
* the reset-rigid minimum still needs a zero-preserving response/return or a
  contradiction from its static fixed-law geometry.

Thus the positive-singleton boundary of the sure-core descent introduces no
new independent atlas component.  It contracts to the existing two-component
waist, but does not consume either component.

## 6. Sharp boundary and regression tests

### 6.1 Why an arbitrary singleton atom is insufficient

For a generic source profile with positive aggregate singleton mass, the mass
may be spread over arbitrarily many dates.  Clock compression can expose one
date and preserve the owner's cap, but changing the owner can create
first-order debt in the other coordinates.  None of (2.3), (2.6), or (2.7)
is available without the attained padded-product geometry.

### 6.2 The equality arm cannot be declared a support drop

Equation (3.4) permits

\[
 (d_k,d_a,d_b,d_c)=(\delta,\alpha,\beta,\gamma)
 \longmapsto
 (0,\alpha+\delta,\beta,\gamma).
\]

Total debt stays at \(D_*\), but no previously zero coordinate need remain
zero after another player's future response.  The reset-rigid classification
records the obstruction; it does not prove renewable zero-set growth.

The following exact two-date regression shows that this rotation can occur
under one literal best response, not merely at the level of abstract debt
vectors.  Use two active players \(k,p\), with rewards

\[
\begin{array}{c|ccc}
 &\{k\}&\{p\}&\{k,p\}\\ \hline
k&0&2&1\\
p&0&0&1
\end{array}
\tag{6.1}
\]

and Never payoff zero.  In profile \(\sigma\), player \(k\) Continues at
date zero, player \(p\) Quits, and both are prescribed to Quit at date one on
the unreached all-Continue history.  Then

\[
 U(\sigma)=(2,0),\qquad B(\sigma)=(2,1),
 \qquad d(\sigma)=(0,1).
\tag{6.2}
\]

Player \(p\)'s exact best response changes only its date-zero action to
Continue and retains its date-one Quit.  The resulting profile \(\rho\)
terminates in \(\{k,p\}\) at date one and satisfies

\[
 U(\rho)=(1,1),\qquad B(\rho)=(2,1),
 \qquad d(\rho)=(1,0).
\tag{6.3}
\]

Thus the mover gains exactly one and kills its debt, total debt remains one,
and the old zero coordinate is reactivated by exactly one.  Against the
common displayed cap \((2,1)\), all Continue is the unique exact product
root: player \(k\) strictly prefers Continue against either action of \(p\),
and then \(p\) strictly prefers Continue against \(k\)'s Continue.

The numerical singleton moats with putative floor one also hold:

\[
 B_k-r_k(\{k\})=2,
 \qquad
 B_p-r_p(\{p\})=1.
\tag{6.4}
\]

Passive players embed the timing and cap-switching calculation in Fin4.
This is not a positive-global-minimum hard-residual table—indeed the
two-player game has equilibrium debt zero elsewhere.  It proves the sharp
local no-go: literal chronology, exact cap attainment, exact debt killing,
equal total debt, singleton moats, and unique all-Continue cap roots do not
force preservation of earlier zeros.  Any renewable zero-set theorem must
use genuinely global source information beyond those fields.

### 6.3 One-sure geometry is essential

With two sure quitters, a sure owner who Continues is screened by the other
sure quitter and the continuation term in (2.2) vanishes.  This is the earlier
sure-core softening regime.  With no sure quitter, positive singleton mass
alone does not identify one owner's prescribed payoff with \(Q_i\).  The
one-sure case is exactly the boundary at which the explicit response above is
both complete and source-faithful.

### 6.4 Reselecting a singleton-base Nash point loses the minimum comparison

It is tempting to fix the sure owner \(k\), solve the induced game among the
other players, and invoke the existing singleton-base stationary dispatch.
That is not a source-faithful continuation of the argument.

Already with one active outsider \(j\), take

\[
 r_k(\{k\})=r_k(\{k,j\})=0,
 \qquad
 r_k(\{j\})=R>0,
\]

and make \(j\) indifferent between joining and not joining the sure owner.
Then every marginal \(q_j\in[0,1]\) is an induced Nash point, while the sure
owner's Continue premium is \(Rq_j\).  Reselecting the induced Nash point
\(q_j=1\) can therefore increase this premium arbitrarily relative to a
source point with \(q_j\) small.  Passive extra players embed the calculation
in Fin4.

This is not a hard-residual counterexample; it isolates the missing
comparison.  Compact induced-Nash existence supplies a stationary object but
does not show its total debt is at most the incoming \(D_*\), preserve the
incoming law, or carry a backward compiler.  The exact response (3.1) avoids
that reselection, but ends at the established off-minimum/reset waist.

### 6.5 Through-mark ledgers do not further consume this child

The through-mark option-budget split

\[
 C\leq 2M\,\mathrm{Sing}+E
\]

is valuable for producing a generic singleton-clock or literal endpoint-work
alternative.  At the present child it is strictly weaker than the available
data: the singleton atom occurs at one known root and the complete owner
response has exact gain \(d_k(z)\).  The ledger does not control the other
three cap changes after that response.  Its exact-stack estimate likewise
confirms that a near-minimum cap--Nash prefix cannot supply macroscopic
absorption.  It therefore routes generic sources toward this waist but does
not consume the attained one-sure node.

## 7. Narrow Lean-facing inputs

The ordinary-mathematics adapter uses these checked ingredients:

* `minimumTerminalSemantic_singletonMargin`;
* `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum`;
* debt scaling under exact cap--Nash prefixing;
* `lawTightStrictSaturation_fullDebt_or_resetRigid_or_singletonNeverCycle`;
* the singleton/Never exclusion argument in
  `finFour_noUniformPayoff_exists_lawTightGlobalMinimumMoatTwoChamber`.

The missing implementation work is local:

1. the exact padded-product owner cap formula (2.3);
2. the literal response profile and identities (3.1)--(3.2);
3. re-anchoring the law-tight strict-minimum classifier at the supplied
   equality target.

No chronological compactness, arbitrary intervention coupling, or source
reprojection theorem is required.

## 8. Next question

Can the extra explicit law of \(\widehat\sigma\)—opponent product absorption
at one date, followed only by one possible owner singleton deadline or
Never—exclude the reset-rigid equality arm, or force its supported strict
toggle to be executable on the same two-date chronology?

## 9. A bounded-calendar canonical response chain

The adjacent-record-deadline arm in the more general finite-clock response
trichotomy is avoidable by a different exact tie convention. This does not
consume reset rigidity, but it sharpens its renewable obstruction to a finite
horizontal cycle.

### Proposition 9.1

Let \(\sigma_0\) be an actual finite-clock profile in Fin4 whose terminal
semantic pair is a positive global minimum of total debt \(D_*>0\). Let
\(H_0\) bound the finite support of every player's stopping law in
\(\sigma_0\).

There is a recursively defined sequence of actual profiles with exactly one
of the following outcomes.

1. Some step is a unilateral exact best response of gain at least \(D_*/4\)
   whose target has total debt strictly above \(D_*\).
2. Every target remains a global minimum, all stopping laws remain supported
   on

   \[
   \{0,\ldots,H_0+1\}\cup\{\infty\},
   \]

   and two profiles in the sequence are literally equal. The intervening
   segment is a finite horizontal exact-best-response cycle. Every edge has
   gain at least \(D_*/4\) and kills its mover's debt.

In particular, unbounded adjacent deadline escape is not intrinsic to the
minimum response construction.

### Proof

For a finite-clock profile \(\sigma\) and player \(i\), let \(H_{-i}\) be
the largest finite date in the support of any opponent's stopping law, with
the evident empty-support convention. Against \(\sigma_{-i}\), all pure
stopping times strictly later than \(H_{-i}\) have exactly the same payoff:
if an opponent stops by \(H_{-i}\), the outcome has already been determined;
if every opponent survives, \(i\) eventually Quits alone. Thus the complete
behavioral cap is attained among

\[
 0,1,\ldots,H_{-i}+1,\infty.
\tag{9.1}
\]

This includes arbitrary privately randomized behavioral strategies because
their terminal payoff against fixed opponents is a convex combination of the
pure-time payoffs.

At each global-minimum state choose a player of maximum debt, using a fixed
player tie order. Its debt is at least \(D_*/4\). Replace it by a pure
cap-attaining time from (9.1), with the following fixed response tie rule:

> whenever Never and a finite time are both cap-attaining, choose Never.

The mover's opponents are unchanged, so its cap is unchanged. The literal
payoff gain is exactly its old debt and its target debt coordinate is zero.
Global minimality says that the target total debt is at least \(D_*\). A
strict inequality gives arm 1; in the equality case repeat.

It remains to prove the uniform horizon bound. Maintain the invariant that
each player's current strategy is either its original strategy from
\(\sigma_0\), a pure stopping time in
\(\{0,\ldots,H_0+1\}\), or Never. Suppose the opponents of the current mover
have no finite support after \(H_0\). Then (9.1) supplies a response no later
than \(H_0+1\), or Never.

Otherwise some opponent has finite support at \(H_0+1\). Such an opponent
cannot still be using its original strategy, so it was previously replaced
and now Quits **surely** at \(H_0+1\). Conditional on reaching that date,
opponent absorption is therefore certain. Every later pure stopping time of
the mover has exactly the same complete terminal law as Never. The tie rule
selects Never rather than \(H_0+2\). This proves the invariant by induction.

Only finitely many profiles satisfy the invariant: each coordinate is either
its one fixed original strategy, one of finitely many pure times, or Never.
An infinite equality sequence therefore repeats a literal profile. Positive
edge gain excludes a self-loop, so the repeated segment is a nontrivial
horizontal cycle. This proves arm 2.

### Consequence

The exact reset waist can be stated more narrowly:

\[
\boxed{
\text{off-minimum paid response}
\quad\lor\quad
\text{finite source-attached horizontal best-response cycle}.}
\tag{9.2}
\]

The second arm preserves more than compact recurrence: every profile, mover,
deadline, complete cap, terminal law, and backward payoff gain is literal,
and every vertex remains at total debt \(D_*\).

It is still not a chronological return. Consecutive vertices are alternative
whole-strategy profiles, not successive dates of one play. A general finite
normal-form game may have a strict best-response cycle, so finiteness alone
does not orient (9.2). The remaining Fin4 question is whether the stopping-time
order structure plus the hard-principal/robust-reversal table geometry makes
this particular minimum cycle consumable. Without such a theorem, declaring
the cycle a Nash--Bellman return repeats the known horizontal-versus-vertical
category error.

### Proposition 9.2 (pure recurrent cycles localize to one stage)

Suppose every strategy occurring on the repeated segment of Proposition 9.1
is a pure stopping time or Never. Then the earliest finite stopping date is
constant around the cycle, and every edge toggles exactly one member of the
nonempty quitter coalition at that common date. Consequently the repeated
segment projects to a literal strict Boolean toggle cycle in the terminal
reward table.

#### Proof

At every cycle vertex \(\sigma\), global minimality gives the strict singleton
moat

\[
 B_i(\sigma)-s_i\ge D_*>0.
\tag{9.3}
\]

Consider the exact best-response edge of mover \(i\), and let
\(m_{-i}\) be the earliest finite stopping time of its opponents. If the new
pure stopping time of \(i\) were strictly earlier than \(m_{-i}\), it would
terminate surely in the singleton \(\{i\}\). Its payoff would be \(s_i\).
Because it is an exact best response, this would give
\(B_i(\sigma)=s_i\), contradicting (9.3). Hence the response time is at least
\(m_{-i}\), or is Never.

It follows that the earliest finite date of the whole profile never decreases
along an edge. The all-Never pure profile cannot be a positive global minimum:
against all-Never opponents each cap is \(\max\{s_i,0\}\), and (9.3) is
incompatible with positive total debt. Thus every cycle vertex has a finite
earliest date. Since the literal profile eventually returns to itself, the
nondecreasing earliest date must be constant around the cycle.

Now a profitable pure-time change can alter the mover's payoff only at that
common earliest date. An outsider must move to that date and join the current
quitter coalition. A current quitter may move later only while another
quitter remains, thereby leaving the coalition. Moving strictly before the
date is excluded by (9.3), and changing between two later dates leaves the
already absorbed outcome unchanged. Therefore every edge is exactly

\[
 S\longrightarrow S\triangle\{i\},
 \qquad
 r_i(S\triangle\{i\})>r_i(S),
\tag{9.4}
\]

with both coalitions nonempty.

#### Existing downstream dispatch

A simple cycle extracted from (9.4) is an input to the reviewed
four-player strict-toggle cycle semantic dispatch. That theorem gives either

1. an unrestricted uniform-equilibrium payoff from a persistent-base or
   interior stationary product solution; or
2. one of its exact semialgebraic residuals: a uniformly positive induced-face
   deviation excess on every face-game Nash point, or failure of the displayed
   interior stationary Bellman/passive system with compact-interior
   separation.

Thus the **fully pure** horizontal-cycle arm is not an unstructured reset
residual. It reaches an existing finite table-specific dispatch. The dispatch's
negative arms are not yet consumers.

The remaining provenance issue is now explicit. A recurrent chain may retain
an original non-pure finite-clock strategy for a player whose debt is zero
whenever the response selector considers it. Such a player supplies a fixed
random timing background, so a positive response gain is an average of
coalition comparisons rather than one literal comparison (9.4). Purifying
that zero-debt strategy preserves its own payoff but may raise other caps and
leave the minimum fibre. Proposition 9.2 therefore does not silently cover
that mixed-background case.

### Proposition 9.3 (mixed backgrounds purify or expose an off-minimum paid port)

The mixed-background case admits an exact finite split. Starting from any
actual finite-clock global-minimum profile of positive debt, after at most four
zero-or-positive exact best-response purifications one obtains either

1. an actual off-minimum finite-clock profile together with a complete
   unilateral best response of gain at least \(D_*/4\); or
2. an actual **pure-time** global-minimum profile.

In the second arm, Propositions 9.1--9.2 apply without the mixed-background
caveat. Thus every finite-clock positive minimum produces

\[
\boxed{
\text{an off-minimum source-attached paid response}
\quad\lor\quad
\text{a same-stage strict-toggle cycle at global minima}.}
\tag{9.5}
\]

#### Proof

Let \(\sigma\) be the current finite-clock global-minimum profile and choose
a player \(h\) whose stopping law is not pure.

If \(d_h(\sigma)>0\), the finite-clock cap argument (9.1) supplies a pure
exact best response. Replace \(h\) by it. The mover gains exactly its debt
and becomes pure. If the target remains at debt \(D_*\), continue. If it is
off minimum, use the paid-port construction below.

Suppose instead that \(d_h(\sigma)=0\). Write the finite stopping law of \(h\)
as a probability distribution \(\pi\) on pure dates and Never. Against the
fixed opponents, every pure-time payoff is at most \(B_h(\sigma)\), while
their \(\pi\)-average is

\[
 U_h(\sigma)=B_h(\sigma).
\]

Consequently every pure time in the positive support of \(\pi\) is itself
cap-attaining. Replacing \(h\) by any such support point is an exact best
response of gain zero and leaves \(h\)'s cap and debt unchanged. There are
only finitely many support points. Choose one whose completed profile has
least total debt. Global minimality gives either

\[
 D(\sigma[h\leftarrow q])=D_*
\]

or

\[
 D(\sigma[h\leftarrow q])>D_*.
\]

In the equality case \(h\) has become pure and the construction continues.
Notice that another old zero coordinate may be reactivated; no zero-set claim
is being made.

In the strict case put \(\tau=\sigma[h\leftarrow q]\). It is an actual
finite-clock off-minimum profile. Choose a player \(p\) of maximum debt in
\(\tau\). Since

\[
 D(\tau)>D_*,
\]

one has

\[
 d_p(\tau)\ge \frac{D(\tau)}4>\frac{D_*}4.
\]

Against finite-clock opponents, \(p\)'s cap is attained by a pure date or
Never. Replacing \(p\) by that response is a literal complete behavioral
edge of gain \(d_p(\tau)>D_*/4\), and its first-disagreement decomposition
is an actual paid-row passport on the same off-minimum source.

Every minimum-fibre purification permanently replaces one non-pure coordinate
by a pure one, and later selected responses are also pure. Hence after at most
four such steps, either the strict arm has occurred or the resulting global
minimum is fully pure. This proves the first assertion.

Starting from the pure minimum, run Proposition 9.1. All descendants remain
pure-time/Never profiles. An off-minimum response gives the first arm of
(9.5); otherwise finite recurrence and Proposition 9.2 give the second.

#### Jensen interpretation and exact boundary

For the zero-debt mixture above, the cap-Jensen identity gives

\[
 \mathbb E_\pi D(\sigma[h\leftarrow q])
 =
 D_*+\sum_{k\ne h}J_k(\sigma,h),
\qquad J_k(\sigma,h)\ge0.
\tag{9.6}
\]

If every \(J_k=0\), every positive-support completion is a global minimum and
every old zero debt is preserved pointwise. If some Jensen gap is positive,
the average completion debt is strictly above \(D_*\); this is precisely the
cap-switching mechanism by which purification can enter the strict arm.
Proposition 9.3 does not assert that every completion is then off minimum. It
selects a minimum completion when one exists and otherwise accepts the
off-minimum paid port.

This split is compatible with the checked full-chord cap-switch theorem. That
theorem can localize a supplied cap switch to a paid pure-time row and survival
floors, but it does not consume the resulting paid row. Proposition 9.3 adds
the finite source selection needed to remove persistent mixed timing as a
separate reset-rigid obstruction; it does not claim that the remaining
off-minimum paid port is solved.

### Proposition 9.4 (a two-free-player common-base cycle is impossible)

Let a same-stage strict-toggle cycle from Proposition 9.2 have common base

\[
 B=\bigcap_\ell S_\ell\ne\varnothing
\]

and exactly two free players

\[
 F=\left(\bigcup_\ell S_\ell\right)\setminus B,
\qquad |F|=2.
\]

If every cycle vertex is a global minimum of positive total debt \(D_*\),
then such a cycle is impossible.

#### Proof

The two-dimensional Boolean face has four vertices. A simple strict cycle on
it must visit all four and orient them as the strict best-response square of
the two free players. The induced \(2\times2\) game therefore has no pure
Nash equilibrium. Its Nash equilibrium \(x\) is completely mixed, so every
face vertex has positive product probability.

Construct one actual product-root profile \(\sigma_x\):

1. every member of \(B\) Quits surely at the root;
2. the two free players use \(x\), and players outside \(B\cup F\) Continue;
3. if the root is all Continue, use the literal tail of the cycle's
   \(B\)-vertex.

The last clause is relevant only when \(B\) is a singleton and both free
players Continue. At every other nonempty face vertex absorption screens the
tail from every unilateral deviation. Thus the four pure specializations of
\(\sigma_x\) have exactly the same prescribed payoffs and complete behavioral
caps as the four supplied cycle vertices. Denote their semantic pairs by
\(z_R\), \(R\subseteq F\).

For every player \(i\), condition an arbitrary complete response on the two
free root actions. Maximum and expectation give

\[
 B_i(\sigma_x)
 \le
 \sum_{R\subseteq F}\Pr_x(R) B_i(z_R).
\tag{9.7}
\]

For a free player, its own prescribed root action is omitted from the
conditioning of its cap. This causes no mismatch: \(B_i(z_R)\) depends only
on its opponents, hence is the same for the two values of its own bit once
the common tail is fixed. Prescribed payoff is affine:

\[
 U_i(\sigma_x)
 =
 \sum_{R\subseteq F}\Pr_x(R) U_i(z_R).
\tag{9.8}
\]

Consequently

\[
 D(\sigma_x)
\le
\sum_R\Pr_x(R)D(z_R)
=D_*.
\tag{9.9}
\]

The profile is an actual carrier point, so global minimality gives the reverse
inequality. Hence equality holds in (9.9), and in every coordinatewise
cap-Jensen inequality used to derive it.

At the completely mixed Nash point \(x\), each free player's two root actions
are indifferent and optimal. A free player's unilateral deviation cannot
remove the sure base, so no post-root stopping strategy adds another option.
Therefore

\[
 d_i(\sigma_x)=0
\qquad(i\in F).
\tag{9.10}
\]

Coordinatewise equality in (9.7)--(9.9) now gives

\[
 0=d_i(\sigma_x)
 =\sum_R\Pr_x(R)d_i(z_R)
\qquad(i\in F).
\tag{9.11}
\]

Every product weight is positive and every debt is nonnegative, so each free
player has zero debt at every face vertex. But each free player moves on the
strict square. At the source of one of its strict edges, the displayed target
strategy is a legal unilateral response with positive gain, so that source
debt is positive. This contradicts (9.11).

#### Fin4 consequence

For a pure recurrent Fin4 cycle, the existing Boolean geometry gives either
a common host or complementary pair vertices. Proposition 9.4 removes every
common-base case with two free players. Hence a surviving common-host cycle
must have

\[
 |B|=1,\qquad |F|=3,
\tag{9.12}
\]

so all three nonhosts genuinely vary. The other surviving topology has empty
common base and includes complementary pairs. These are exactly the cases in
which the face product law necessarily introduces off-cycle coalitions, so
the Jensen average in (9.9) no longer uses only known global-minimum vertices.

This is a strict topological reduction, not a consumer of (9.12) or of the
complementary-pair topology.

### Proposition 9.5 (face-support obstruction)

The preceding Jensen argument has a useful form that identifies exactly what
remains in the singleton-host case. Let \(B\ne\varnothing\) and let \(F\) be
disjoint from \(B\). Fix one literal continuation tail, and for every
\(R\subseteq F\) let \(z_R\) be the semantic pair of the profile whose root
quitter set is \(B\cup R\), with all players outside \(B\cup F\) Continuing.
Let \(\mathcal C\subseteq 2^F\) be the vertex set of a strict toggle cycle.

For any Nash point \(x\) of the induced binary game on \(F\), write
\(\operatorname{supp}(x)\) for the Cartesian support of its product law. It
is impossible that

\[
 D(z_R)=D_*\quad(R\in\operatorname{supp}(x))
 \qquad\text{and}\qquad
 \operatorname{supp}(x)\cap\mathcal C\ne\varnothing.
\tag{9.13}
\]

Indeed, form the actual product-root profile with sure base \(B\), free rates
\(x\), and the fixed tail. Conditioning a complete response on the free root
actions gives the same cap-Jensen inequality as (9.7), while prescribed
payoff is affine. Under the first condition in (9.13), global minimality
forces equality coordinatewise. Every free player has zero debt at the
induced Nash point because a sure base remains after its unilateral
replacement. Hence that player has zero debt at every pure vertex in the
product support. A cycle vertex in the support has a strict outgoing edge by
one of the free players, giving that mover positive debt there, a
contradiction.

This statement uses no chronological interpretation of the horizontal cycle.
It is a convexity obstruction inside one common-tail root face.

For a singleton host in Fin4, \(|F|=3\). A simple cycle using all three free
coordinates has length six or eight.

* A Hamiltonian eight-cycle is impossible: every induced Nash support is
  contained in the cycle, so (9.13) applies.
* For a six-cycle, either some pure profile at one of the two omitted cube
  vertices is off minimum, or every induced Nash product support is contained
  in those two omitted vertices. In the latter case its support has dimension
  at most one: if the omitted vertices are adjacent their union is an edge,
  and otherwise their only Cartesian subcubes are singletons. At the
  corresponding global-minimum product profile all three free-player debts
  vanish. Since Fin4 has no outsider, the singleton host is the only debtor
  and has debt exactly \(D_*\).

Thus the surviving singleton-host cycle yields the sharper alternative

\[
 \boxed{
 \text{an actual off-minimum pure face profile}
 \quad\lor\quad
 \text{a one-sure-host global minimum with only the host indebted}.}
\tag{9.14}
\]

The second arm returns to the exact owner-response handoff of Sections 2--4:
the host has a complete response of gain \(D_*\), whose target is either off
minimum or another reset-rigid minimum. This is a real reduction of the cycle
geometry, but not yet a rank decrease, because the equality target can
re-enter the same one-sure-host waist. The empty-base/complementary-pair
topology is not covered: without a sure base, a unilateral response may expose
the continuation, and the common-tail cap-Jensen identification needs
additional source data.

### Proposition 9.6 (the canonical cycle has no singleton vertex)

The max-debt response rule in Proposition 9.1 excludes singleton vertices
altogether. If the current pure profile terminates in \(\{i\}\), then

\[
 U_i=s_i.
\]

The positive-minimum singleton moat gives

\[
 d_i=B_i-s_i\ge D_*.
\]

Since all debts are nonnegative and sum to \(D_*\), this is equality and
every other coordinate has zero debt. Thus \(i\) is the unique max-debt player
selected by the canonical rule. Any exact response of positive gain must move
its stopping time strictly after the singleton date. The earliest stopping
date therefore strictly increases on this edge. That is impossible on the
recurrent segment, where Proposition 9.2 proved the earliest date constant.

Consequently every coalition on the canonical cycle has cardinality at least
two. In the singleton-host case, the free-face empty vertex (the host alone)
is absent. A three-dimensional simple cycle using all three free coordinates
is therefore a six-cycle omitting the empty vertex and either one adjacent
vertex or the opposite vertex; the Hamiltonian case is already excluded.
Combined with Proposition 9.5, the minimum Nash support in the no-off-minimum
arm lies in that one- or zero-dimensional omitted set. Independently of which
omitted support the Nash point uses, the omitted empty-face profile itself is
an attained host-only minimum whenever it is not off minimum. At that
host-only point the host is again the sole debtor of size \(D_*\), exactly the
owner-response waist.

The remaining empty-base cycle consists entirely of coalitions of size two,
three, or four. This is the precise unconsumed static object. The checked
same-stage monodromy impossibility does not by itself remove it: that dispatch
declares a pair vertex terminal, whereas the present max-debt response chain
may leave the pair by an outsider join. Conversely, serializing the cycle as
successive sure-absorption rows would kill survival at its first vertex. A
consumer must therefore use its common minimum-source data or the Fin4 hard
reward geometry, not reinterpret the horizontal edges as play dates.
