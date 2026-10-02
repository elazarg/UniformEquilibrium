# Fin4 tropical two-Never sources descend to an off-minimum paid port

Authors: `CODEX_SNELL`, `CODEX_SPINOZA`

Independent reviews:
[chronological descent by CODEX_SPINOZA](../feedback/CODEX_SNELL__TROPICAL_TWO_NEVER_CHRONOLOGICAL_SUPPORT_DESCENT__BY_CODEX_SPINOZA.md),
[chronological descent by CODEX_NEGATIVE_CERTIFICATE](../feedback/CODEX_SNELL__TROPICAL_TWO_NEVER_CHRONOLOGICAL_SUPPORT_DESCENT__BY_CODEX_NEGATIVE_CERTIFICATE.md),
[singleton collar by CODEX_SNELL](../feedback/CODEX_SPINOZA__SINGLETON_DESCENT_REACTIVATION_OFFMINIMUM_COLLAR__BY_CODEX_SNELL.md),
[support-four exit by CODEX_SPINOZA](../feedback/CODEX_SNELL__TROPICAL_SUPPORT_FOUR_TWO_OWNER_ENDPOINT_EXIT__BY_CODEX_SPINOZA.md),
[support-four exit by CODEX_NEGATIVE_CERTIFICATE](../feedback/CODEX_SNELL__TROPICAL_SUPPORT_FOUR_TWO_OWNER_ENDPOINT_EXIT__BY_CODEX_NEGATIVE_CERTIFICATE.md)

## Exact statement

Let \(I=\operatorname{Fin}4\), and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a bounded quitting reward table. Never pays zero. Behavioral
randomizations are independent across players and dates conditional on public
survival, and a unilateral deviator may replace its complete behavioral
strategy, including by any finite pure quitting time or literal Never.

Assume the game has no ordinary uniform-equilibrium payoff. Apply the
reviewed period-one tropical source theorem
[`FIN4_PERIOD_ONE_TROPICAL_TWO_NEVER_REDUCTION.md`](FIN4_PERIOD_ONE_TROPICAL_TWO_NEVER_REDUCTION.md).
After passage to its supplied subsequence, it gives actual stationary
profiles \(\sigma_n\) with hazards \(x_{n,i}\in(0,1)\),

\[
 h_n:=\sum_i x_{n,i}\longrightarrow0,
 \qquad \lambda_{n,i}:=x_{n,i}/h_n\longrightarrow\lambda_i,       \tag{1}
\]

and, with

\[
 s_i=r_i(\{i\}),\qquad A_{ik}=r_i(\{k\})-s_i,
 \qquad K=\operatorname{supp}\lambda,                             \tag{2}
\]

a constant \(\kappa>0\) satisfying

\[
 \sum_k\lambda_kA_{ik}\ge\kappa\quad(i\in I),
 \qquad
 \sum_k\lambda_kA_{ik}=\kappa\quad(i\in K).                     \tag{3}
\]

The set \(K\) has cardinality two, three, or four.

Let \(D\) be total debt on the compact terminal-semantic carrier, let

\[
 D_*:=\min D>0,
 \qquad \mathcal F:=\{z:D(z)=D_*\}.                              \tag{4}
\]

Then, after a further subsequence, there are actual profiles

\[
 \sigma_n=\rho_n^0,\rho_n^1,\ldots,\rho_n^{m-1},\rho_n^m,
 \qquad 2\le m\le4,                                               \tag{5}
\]

fixed player labels, and constants \(c,\delta>0\) such that, for every
sufficiently large finite \(n\):

1. each edge in (5) changes one player's complete strategy and is attained
   by a literal endpoint strategy, either Never or Quit at date zero;
2. that endpoint is the player's exact cap over every behavioral deviation
   at the edge's actual source and has strictly positive gain;
3. every profile in (5) is the literal child of its predecessor; in
   particular, no two response siblings are identified as chronology;
4. the last edge \(\rho_n^{m-1}\to\rho_n^m\) is Quit at date zero by one
   fixed player \(b\), has gain at least \(c\), and its source semantic pair
   satisfies

   \[
    D(\rho_n^{m-1})\ge D_*+\delta;                                \tag{6}
   \]

5. for every semantic cluster point \(y\) of
   \(\rho_n^{m-1}\),

   \[
    B_b(y)=s_b,
    \qquad B_b(z)-B_b(y)\ge D_*\quad(z\in\mathcal F);             \tag{7}
   \]

6. the last edge is a quantitative first-disagreement row at date zero:
   the row is reached with probability one, and at its source the mover's
   Continue probability, the opponents' joint Continue probability, and the
   joint all-Continue probability are each at least \(1/2\); after the joint
   all-Continue outcome the literal continuation is again
   \(\rho_n^{m-1}\).

The chain length can be chosen as follows:

- \(|K|=2\): one Never deletion reaches a diffuse singleton source, followed
  by the final Quit-now blocker, so \(m=2\);
- \(|K|=3\): two successive Never deletions reach a diffuse singleton source,
  followed by the final blocker, so \(m=3\);
- \(|K|=4\): two successive Never deletions reach a two-owner child. A third
  Quit-now edge may already be final. Otherwise a third Never deletion reaches
  a diffuse singleton and the fourth edge is the final blocker, so
  \(m\in\{3,4\}\).

Thus every support-cardinality residue of the period-one tropical theorem is
reduced to one actual source-attached, all-behavior-cap, off-minimum paid row.
The source ancestry in (5) begins at the unconditional tropical source
\(\sigma_n\). It is not asserted to begin at an actual minimum-fibre realizer.

## Conjecture-facing change

The period-one tropical reduction previously supplied two profitable Never
deviations as siblings at one actual source and left three support-cardinality
cases. The reviewed chronological descent first converted those siblings into
successive exact cap updates, but support four still stopped at two owners and
the duplicated-cyclic regression showed that a removed owner could reactivate.

This packet removes both residues:

- an origin-independent hard-column theorem charges every actual diffuse
  singleton descendant by a fixed Quit-now blocker and locates that source at
  a positive-minimum cap collar; and
- a weighted two-owner endpoint theorem sends the support-four child either
  directly to the same Quit-now collar or through one further Never deletion
  to a genuine diffuse singleton.

Consequently the entire tropical branch reaches the off-minimum paid-row /
source-reentry waist. Relative to
[`FIN4_QUANTITATIVE_PAID_PORT_CONSUMER.md`](../questions/FIN4_QUANTITATIVE_PAID_PORT_CONSUMER.md),
the remaining obligation is narrower and explicit: attach the tropical
genealogy to a complete minimum-fibre source, or consume the off-minimum paid
row without such a reprojected ancestry. The packet does not solve that
remaining consumer.

## Definitions and assumptions

For every nonempty \(B\subseteq K\), define \(\sigma_n^B\) by retaining the
source stationary strategy of every player in \(B\) and every zero-share
outsider, while replacing every player in \(K\setminus B\) by literal Never.
Put

\[
 \Lambda_B=\sum_{k\in B}\lambda_k,
 \qquad
 V_i(B)=\frac{\sum_{k\in B}\lambda_kr_i(\{k\})}{\Lambda_B}.       \tag{8}
\]

Every \(\sigma_n^B\) used below is an actual almost-surely absorbing
stationary profile. Zero-share outsiders keep their exact source hazards and
have total hazard \(o(h_n)\); they are not silently deleted.

For \(j\in B\) with \(B\setminus\{j\}\ne\varnothing\), define

\[
 Q_{n,j}^B=
 U_j(\sigma_n^B[j\leftarrow\operatorname{QuitAt}0]),
 \qquad
 N_{n,j}^B=
 U_j(\sigma_n^B[j\leftarrow\operatorname{Never}]).                \tag{9}
\]

The complete cap is

\[
 B_j(\sigma_n^B)=
 \sup_{\beta_j}U_j(\sigma_n^B[j\leftarrow\beta_j]),               \tag{10}
\]

where the supremum is over every behavioral strategy of player \(j\), not
only stationary or bounded-clock deviations.

The normalized singleton matrix in (2) has zero diagonal. Under the no-uniform
hypothesis, the checked Fin4 full-normal-core theorem and the checked
standard-Q-side theorem imply

\[
 \neg\operatorname{HasHomogeneousSimplexSolution}(A).             \tag{11}
\]

The positive minimum \(D_*>0\) in (4) is the minimum of the continuous total
debt function on the compact closure of literal prescribed-payoff / complete
cap pairs. It follows from the checked positive-minimum theorem under the
same no-uniform hypothesis.

## Source correspondence

The arbitrary-table actual source, the vanishing hazards, (1)--(3), and the
support alternatives are the reviewed export
[`FIN4_PERIOD_ONE_TROPICAL_TWO_NEVER_REDUCTION.md`](FIN4_PERIOD_ONE_TROPICAL_TWO_NEVER_REDUCTION.md).
That theorem in turn uses the unconditional producer in
[`ENDOGENOUS_SOFT_CYCLIC_BLOCK_ESCAPE.md`](ENDOGENOUS_SOFT_CYCLIC_BLOCK_ESCAPE.md).

The chronological subset calculation was independently reviewed in
[`CODEX_SNELL__TROPICAL_TWO_NEVER_CHRONOLOGICAL_SUPPORT_DESCENT.md`](../notes/CODEX_SNELL__TROPICAL_TWO_NEVER_CHRONOLOGICAL_SUPPORT_DESCENT.md),
frozen SHA-256
`c80fa19901274cbf07e189124872008ed4850286bf618e81ef2246f4e014aba9`.

The origin-independent singleton collar was independently reviewed in
[`CODEX_SPINOZA__SINGLETON_DESCENT_REACTIVATION_OFFMINIMUM_COLLAR.md`](../notes/CODEX_SPINOZA__SINGLETON_DESCENT_REACTIVATION_OFFMINIMUM_COLLAR.md),
frozen SHA-256
`89fb408340a6f20b9650a7a9bc34a19303287ff0cec7be9f881dacacc3154800`.

The support-four two-owner exit was independently reviewed in
[`CODEX_SNELL__TROPICAL_SUPPORT_FOUR_TWO_OWNER_ENDPOINT_EXIT.md`](../notes/CODEX_SNELL__TROPICAL_SUPPORT_FOUR_TWO_OWNER_ENDPOINT_EXIT.md),
frozen SHA-256
`0ca3860f9359cc3ca7039ee7aeff8d73bdb1bb276f4bc44e0e3f547cb2b8fb3f`.

Named checked Lean declarations used by the proof are:

- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` in
  `UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`;
- `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff` in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`;
- `singletonLCPFeasible_reindexMatrix_iff` and
  `exists_negative_entry_in_column_of_noHomogeneous` in the LCP matrix files;
- `quittingTerminalSemanticCarrier_isCompact` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `continuous_quittingTerminalSemanticDebtSum` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean`; and
- `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`.

No checked declaration already contains the chronological ordered-pair
selection, the support-four two-owner sign dispatch, or their composition
with the origin-independent singleton collar.

## Proof

### Stationary endpoint envelope

Fix \(j\in B\) with \(B\setminus\{j\}\ne\varnothing\), and let \(a_n<1\)
be the opponents' one-row joint Continue probability. By stationarity, a pure
Quit at time \(t\in\mathbb N\) gives exactly

\[
 (1-a_n^t)N_{n,j}^B+a_n^tQ_{n,j}^B.                              \tag{12}
\]

The term \(Q_{n,j}^B\) includes simultaneous opponent quits in the selected
row. Never and Quit at zero attain the two endpoints. Thus every pure-time
payoff lies in their closed interval, and behavioral pure-time extremality
gives the exact finite-profile identity

\[
 B_j(\sigma_n^B)=\max\{Q_{n,j}^B,N_{n,j}^B\}.                    \tag{13}
\]

This is the only strategy-class reduction in the proof, and it covers every
unilateral behavioral deviation.

### Subset law and Never gain

For fixed nonempty \(B\subseteq K\), retained leading owners have row hazard
\(h_n\Lambda_B+o(h_n)\); zero-share outsiders have total hazard \(o(h_n)\),
and collisions have row mass \(O(h_n^2)\). Infinite stationary repetition
normalizes that one-row absorbing law. Hence the first quitting coalition
converges in total variation to

\[
 \Pr(\{k\})=\lambda_k/\Lambda_B\quad(k\in B),                     \tag{14}
\]

and

\[
 U_i(\sigma_n^B)\longrightarrow V_i(B).                          \tag{15}
\]

For \(j\in B\),

\[
 Q_{n,j}^B\longrightarrow s_j,
 \qquad N_{n,j}^B\longrightarrow V_j(B\setminus\{j\}).          \tag{16}
\]

The barycentric identity

\[
 V_j(B)=\frac{\lambda_j}{\Lambda_B}s_j+
 \frac{\Lambda_B-\lambda_j}{\Lambda_B}V_j(B\setminus\{j\})      \tag{17}
\]

therefore gives

\[
 V_j(B\setminus\{j\})-V_j(B)=
 \frac{\lambda_j\sum_{k\in B\setminus\{j\}}\lambda_kA_{jk}}
 {\Lambda_B(\Lambda_B-\lambda_j)}.                               \tag{18}
\]

Whenever the numerator is positive, (13), (16), and strict separation imply
that literal Never is the exact complete cap for all sufficiently large
finite \(n\), and the update to \(\sigma_n^{B\setminus\{j\}}\) has strictly
positive gain. “Exact cap” here is finite-\(n\); only (18) is a limiting
formula.

### Ordered chronological descent

At \(B=K\), equations (3) and (18) give, for every \(i\in K\), the positive
source Never gain limit

\[
 \frac{\lambda_i\kappa}{1-\lambda_i}.                             \tag{19}
\]

Thus, when \(|K|=2\), either support owner can make one exact-cap Never
update, leaving a genuine diffuse singleton source.

Suppose \(|K|\ge3\). Fix \(j\in K\). Since

\[
 \sum_{k\in K\setminus\{j\}}\lambda_kA_{jk}=\kappa              \tag{20}
\]

has at least two summands, they cannot all be at least \(\kappa\). Choose a
fixed \(i\ne j\) with

\[
 \lambda_iA_{ji}<\kappa.                                         \tag{21}
\]

First update \(i\) to Never. At its literal child take
\(B=K\setminus\{i\}\). Player \(j\)'s numerator in (18) is now

\[
 \sum_{k\in K\setminus\{i,j\}}\lambda_kA_{jk}
 =\kappa-\lambda_iA_{ji}>0.                                      \tag{22}
\]

Thus \(j\)'s Never strategy is the exact complete cap at the actual first
child for all large \(n\), with gain tending to

\[
 \frac{\lambda_j(\kappa-\lambda_iA_{ji})}
 {(1-\lambda_i)(1-\lambda_i-\lambda_j)}>0.                        \tag{23}
\]

For support three, the two updates leave a diffuse singleton. For support
four, they leave the actual two-owner child treated below. The fixed labels
and the two eventual tails can be intersected, so the chronology holds for
every \(n\) on one common tail.

### Origin-independent singleton blocker and collar

The no-uniform hypothesis yields full normal core and homogeneous
infeasibility on the normal principal matrix. Reindexing along the full-core
identification gives (11) for the full matrix \(A\). Its diagonal is zero, so
for every column \(k\) there is \(b(k)\ne k\) with

\[
 A_{b(k),k}<0.
\]

Fix these choices and put

\[
 g_0:=\min_k(-A_{b(k),k})>0.                                     \tag{24}
\]

Consider any actual stationary one-leading-owner descendant \(\tau_n\) whose
owner \(k\) has hazard \(q_n>0\), with \(q_n\to0\), while every other
retained positive hazard has total \(o(q_n)\). Its terminal law converges to
\(\delta_{\{k\}}\). Against \(b=b(k)\), the Never endpoint tends to
\(r_b(\{k\})\), while Quit at zero tends to \(s_b\). Since

\[
 s_b-r_b(\{k\})=-A_{bk}\ge g_0,                                  \tag{25}
\]

the stationary endpoint envelope makes Quit at zero the exact unrestricted
cap for all large \(n\), with gain at least \(g_0/2\).

Let \(y\) be a semantic cluster point of these singleton descendants. Then

\[
 U_b(y)=r_b(\{k\}),\qquad B_b(y)=s_b.                             \tag{26}
\]

For every \(z\in\mathcal F\), the checked singleton-margin theorem gives

\[
 D_*\le B_b(z)-s_b=B_b(z)-B_b(y).                                 \tag{27}
\]

Thus no such \(y\) lies in \(\mathcal F\). Compactness of the cluster set
and continuity of \(D\) give a constant \(\delta>0\) such that (6) holds on
one tail. This argument depends only on the literal one-leading-owner
hypotheses, not on whether the singleton came from initial support two, three,
or four.

### Two-owner endpoint exit for support four

At the support-four child, let the remaining pair be \(B=\{p,k\}\), put
\(\Lambda=\lambda_p+\lambda_k\), and write that actual child as \(\tau_n\).
The other two players are literally Never; there are no lower-order active
outsiders. Its terminal law converges to

\[
 \frac{\lambda_p}{\Lambda}\delta_{\{p\}}+
 \frac{\lambda_k}{\Lambda}\delta_{\{k\}}.                        \tag{28}
\]

For active owner \(p\), the two endpoint and prescribed limits are

\[
 Q_{n,p}\to s_p,\qquad N_{n,p}\to s_p+A_{pk},\qquad
 U_p(\tau_n)\to s_p+\frac{\lambda_k}{\Lambda}A_{pk}.              \tag{29}
\]

Therefore:

- if \(A_{pk}>0\), Never is the exact complete cap for all large \(n\), its
  gain tends to \((\lambda_p/\Lambda)A_{pk}>0\), and the literal child is a
  genuine diffuse singleton source owned by \(k\);
- if \(A_{pk}<0\), Quit at zero is the exact complete cap, with gain tending
  to \(-(\lambda_k/\Lambda)A_{pk}>0\).

The same statements hold with \(p,k\) interchanged. A negative cross entry
therefore gives the final Quit-now edge and (27) directly. A positive cross
entry gives one Never child, to which the singleton blocker applies.

It remains only to consider

\[
 A_{pk}=A_{kp}=0.                                                  \tag{30}
\]

Define \(\mu\) by

\[
 \mu_p=\lambda_p/\Lambda,\qquad
 \mu_k=\lambda_k/\Lambda,\qquad
 \mu_a=0\quad(a\notin B).                                        \tag{31}
\]

Then \((A\mu)_p=(A\mu)_k=0\). If both removed outsiders also had
\((A\mu)_a\ge0\), the vector \(\mu\) would be a homogeneous simplex
solution: \(\mu\ge0\), its mass is one, \(A\mu\ge0\), and
\(\mu_a(A\mu)_a=0\) for every player. This contradicts (11). Hence one fixed
removed outsider \(b\notin B\) has

\[
 R_b:=(A\mu)_b=
 \frac{\lambda_pA_{bp}+\lambda_kA_{bk}}{\Lambda}<0.               \tag{32}
\]

That player is literally Never at \(\tau_n\), so

\[
 U_b(\tau_n)=N_{n,b}\to s_b+R_b,
 \qquad Q_{n,b}\to s_b.                                          \tag{33}
\]

Quit at zero is therefore its exact complete cap for all large \(n\), with
gain tending to \(-R_b>0\), and (27) applies. This exhausts support four.

### Final paid-row bounds and ancestry

The final selected response in every branch is Quit at date zero. At its
source the mover is either stationary with hazard tending to zero or already
literal Never. Its source Continue probability therefore tends to one. Every
opponent hazard at that row also tends to zero, so opponent and joint source
Continue probabilities tend to one. On a common tail all three are at least
\(1/2\), the row is reached with probability one, and the strict limiting
gain has a fixed positive half-limit lower bound \(c\). After the joint
all-Continue outcome, stationarity makes the continuation literally the same
source.

Every earlier edge was installed on the actual preceding child. Thus the
final row retains a finite chain of complete unilateral replacements from the
same tropical source \(\sigma_n\), proving (5)--(7).

## Boundary tests

### The duplicated-cyclic reactivation regression

On `Option (Fin 3)`, let the checked duplicated-cyclic matrix restrict on the
three distinct core labels to

\[
 \begin{pmatrix}
 0&-1&2\\
 2&0&-1\\
 -1&2&0
 \end{pmatrix},                                                   \tag{34}
\]

with the fourth coordinate duplicating coordinate zero. Give the three core
labels hazards \(h\), the duplicate hazard \(h^2\), singleton rewards from
this matrix, and all nonsingleton coalitions reward zero. The normalized law
is uniform on the three core labels and \(\kappa=1/3\). Every core player's
source Never gain tends to \(1/6\). After any first Never deletion, the unique
profitable second Never deletion has gain tending to one, but it leaves a
singleton owner \(k\) with \(A_{ik}=-1\) for the first removed player \(i\).
That player reactivates by an exact-cap Quit-now response of gain tending to
one.

This table has all-Never as an exact terminal Nash profile, so its true global
minimum debt is zero. It proves that support descent is not renewable from
the local matrix/tropical data alone and that the positive-minimum collar is
essential. It does not falsify the theorem.

### The two-owner zero-cross boundary

If (30) holds and every outsider residual in (32) is nonnegative, (31) is
exactly a homogeneous simplex witness. Thus strict homogeneous infeasibility
is the sharp algebraic condition forcing the outsider Quit response in the
zero-cross branch. Equality cannot be repaired by a sign convention.

### Nonsingleton rewards and collisions

Arbitrary nonsingleton reward coordinates occur in Quit-now endpoints only
when an opponent quits simultaneously, and in stationary terminal laws only
through collisions. Their probabilities are \(O(h_n)\) after normalization
at every fixed nonempty leading support. Bounded rewards make their payoff
effect vanish, while all response selections use strict limiting signs.

### Sure-Quit targets are not regenerated diffuse sources

The final Quit-now target has terminal law tending to \(\delta_{\{b\}}\), but
deleting \(b\) exposes the former stationary owner or owners. The target is
therefore not a new diffuse one-owner source. This is the exact ancestry
failure that blocks naive renewal.

## Adapter and consumer

The actual-data adapter is the reviewed period-one theorem: for an arbitrary
Fin4 table, choose any soft errors tending to zero and apply its unconditional
period-one producer. Under the counterexample hypothesis, that theorem
selects the fixed subsequence satisfying (1)--(3). No LCP vector, minimum
profile, support, response clock, or cap is supplied by hand.

The present packet then constructs the literal chain (5) and its final
off-minimum paid row. It preserves full behavioral caps, terminal laws,
stationary continuations, fixed labels, and source chronology.

Its downstream target is the maintained off-minimum/source-reentry arm of
[`FIN4_QUANTITATIVE_PAID_PORT_CONSUMER.md`](../questions/FIN4_QUANTITATIVE_PAID_PORT_CONSUMER.md).
It supplies the physical paid row and the quantitative debt-transition side,
but not that question's required ancestry from an actual minimum source. No
checked consumer presently turns the tropical-source ancestry plus (6)--(7)
into a positive charged near-return, a renewable rank, or a terminal
approximate Nash sequence. The exact remaining bridge is a source-reprojection
block from the sure-Quit target or the tropical source to a minimum-attached
genealogy with sublinear seam error.

## Lean handoff

A narrow formalization can be split into four declarations.

1. `quittingStationarySubset_neverGain_limit`: formalize (14)--(18), taking
   the actual hazard sequence and its normalized limit as data.
2. `exists_chronological_twoNever_supportDescent`: formalize (19)--(23), with
   explicit eventual finite-\(n\) exact cap statements and fixed labels.
3. `exists_quitNow_collar_of_stationary_singletonDescendant`: combine the
   full-core no-homogeneous reindex, negative-column theorem, endpoint cap,
   singleton margin, compact cluster set, and continuity of total debt.
4. `exists_endpointExit_of_stationary_twoOwnerChild`: formalize (28)--(33),
   especially the zero-cross construction of the homogeneous witness.

The composition theorem should take the exported period-one tropical source
object and return the finite list of literal profile updates, the final mover,
positive constants, exact cap equalities, row-zero reach bounds, and collar
inequalities. It must not add a minimum-source ancestry field that the proof
does not produce.

Useful exact tests are the duplicated-cyclic regression, the checked
paired-singleton matrix for a negative-cross two-owner endpoint, and a
zero-cross pair whose nonnegative outsider residuals explicitly construct the
forbidden homogeneous witness.

## Scope and nonclaims

- This is reviewed ordinary mathematics, not yet a Lean theorem.
- The source profiles are the actual stationary profiles returned by the
  period-one producer. The theorem does not classify all approximate roots.
- Every cap claim is exact at sufficiently large finite \(n\). The displayed
  gain formulas are limits used only to select a common tail and fixed positive
  lower bounds.
- Caps cover unrestricted behavioral deviations through the checked pure-time
  extremality theorem.
- Zero-share outsiders are retained until a literal update changes them.
- The proof does not lift a two- or three-player equilibrium and never treats
  response siblings as temporal play.
- The off-minimum collar is a state separation, not an additive budget. Debt
  may return to the minimum fibre through an uncharged seam.
- The final source has finite replacement ancestry from the tropical source,
  not from an actual minimum-fibre realizer. Therefore the packet does not by
  itself instantiate every field of the quantitative paid-port question.
- The sure-Quit target is not a regenerated diffuse singleton source.
- No terminal approximate Nash profile, uniform-equilibrium payoff,
  Nash--Bellman near-return, or renewable rank is claimed.
