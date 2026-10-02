# Strengthening and export-gate review of `COMPILE_FIN4`

Reviewer: `CODEX_STRENGTHEN`

Target: [`gpt/COMPILE_FIN4.md`](../archive/COMPILE_FIN4.md)

## Verdict

The retained-atom calculation has a sound core, but the strongest theorem is
not the generic bound stated in Proposition 2.  On the **actual source-facing
Fin4 maximal-prefix family**, both members of the fixed pure pair have zero
Never mass at every rank, while their mass in every fixed finite clock window
tends to zero.  Consequently their late-finite mass tends to **one**.  This is
a strict quantitative strengthening of the draft's lower bound
`(D_*/D_0) m` and applies despite the fact that the base profile varies with
the rank.

The two regressions can also be strengthened:

1. the unconstrained globally maximal exact-root graph can be made nonclosed
   with a uniform `1/2` continuation-reach floor and a uniform `1/4` debt
   floor on the selected children, not merely a positive debt floor on the
   parents; and
2. one constant normalized decoration can have simultaneous complete clock
   escape at its endpoint, comparison, and postmark-tail ports.

These are rigorous ordinary-mathematics boundary results.  They do **not**
make the whole note exportable.  The clock theorem has no terminal consumer,
the maximal-root table has global debt minimum zero, and the decoration table
only shows insufficiency of a supplied carrier.  The seven-instruction schema
and the relaxed-root paragraph are not a proved arbitrary-game compiler.

My gate recommendation is therefore:

* do not create a new export from `COMPILE_FIN4` as a whole;
* consider replacing or augmenting the constrained-root regression in
  `EXECUTABLE_ADAPTER_GRAMMAR_AND_CONSTRAINED_ROOT_NO_GO.md` with the stronger
  unconstrained Fin4 regression below, after an independent falsification
  review; and
* retain the unit clock-escape theorem as a precise source-facing Research
  handoff until a named consumer uses the escape alternative.

## Exact question checked

Let `x_k` be the cap-indexed maximal exact roots in the autonomous semantic
orbit, let

\[
c_k=\Pr_{x_k}(\mathbf C),\qquad a_k=1-c_k,
\qquad C_n=\prod_{k<n}c_k,
\]

and let the rank-`n` actual profile be the reverse chronological root stack

\[
Z_n=x_{n-1}\star\cdots\star x_0\star \tau_n.
\]

The source-facing Fin4 construction has a varying base `tau_n`: it is a sure
fixed pure-pair row followed counterfactually by the selected reference tail.
The question is whether the resulting actual family can have a
source-faithful stopping-law limit which retains its compact semantic/law
cluster and pure-pair atom.

## Sources and declarations inspected

The narrow source dependency set was:

* `quittingMaximalCapSemanticRoot_exactNash`,
  `quittingMaximalCapSemanticRoot_maximal`,
  `quittingMaximalCapSemanticPrefixProfile_eq_literalRootStack`,
  `quittingTerminalSemanticDebtSum_maximalCapSemanticPrefixOrbit_eq`,
  `minimumDebt_div_sourceDebt_le_maximalCapSemanticPrefixSurvival`, and
  `quittingStageCoalitionMass_maximalCapSemanticPrefixProfile_add` in
  `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`;
* `QuittingMaximalCapSemanticPrefixRetainedLaw`,
  `quittingMaximalCapSemanticPrefixLawPoint_cluster_facts`,
  `summable_maximalCapPrefix_absorption`,
  `QuittingMaximalCapSemanticPrefixRayStall.summable_absorption`, and
  `QuittingMaximalCapSemanticPrefixRayStall.absorption_tsum_le_exact_debtDrop`
  in `Research/Quitting/MaximalCapSemanticPrefixReturn.lean`;
* `FinFourOwnerCompressedMinimumReturnForcedPairPacket.rayBaseProfile`,
  `.rayBaseProfile_stageMass_eq_one`, `.rayFamily`,
  `.rayProfiles_stageMass_eq_survival`,
  `.rayBaseProfile_outcomeMass_eq_pointMass`,
  `.rayBaseProfile_neverMass_eq_zero`, and
  `.nonempty_maximalPrefixRayMinimumReturn_or_stall` in
  `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`;
* `QuittingMarkedPairDecoratedFamily`, `.baseDecoration`,
  `.rawDecoration_whole_eq`, `.rawDecoration_tail_eq`,
  `.rawDecoration_markedMass_eq`, `.rawDecoration_actualGain_eq`, and
  `.descendant_postMarkSpine_eq` in
  `Research/Quitting/NormalizedPassportPrefixOrbit.lean`; and
* `exists_maximalAbsorption_isZeroQuittingRootNash` in
  `Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean`.

For novelty and scope I compared the result with
`meta/GRAMMAR.md`,
`exports/EXECUTABLE_ADAPTER_GRAMMAR_AND_CONSTRAINED_ROOT_NO_GO.md`,
`notes/CHATGPT_EXTERNAL__NONCOLLAPSING_MAXIMAL_PAID_RESET_ORBIT.md`,
`notes/FORCED_PAIR_REVIEW__MAXIMAL_PREFIX_RAY_DICHOTOMY.md`,
`notes/CODEX_RAMSEY__NORMALIZED_PAID_MARK_COMPACTIFICATION_NO_GO.md`, and the
corresponding reviews.  No literature theorem is used.

## 1. Sharp reverse-prefix clock-escape lemma

### Statement

Fix a finite player set.  For every `k`, let `x_k` be a product root, write
`p_{i,k}` for player `i`'s Continue probability, and put

\[
c_k=\prod_i p_{i,k},\qquad a_k=1-c_k.
\]

Let `tau_n` be arbitrary behavioral tails and define

\[
Z_n=x_{n-1}\star\cdots\star x_0\star\tau_n.
\tag{1}
\]

Assume `a_k -> 0`.  Let `lambda_i^n` be player `i`'s marginal stopping law in
`Z_n`.  Then, for every fixed `T`,

\[
\sum_{t=0}^{T}\lambda_i^n(t)
 \le \sum_{t=0}^{T}a_{n-1-t}
 \longrightarrow 0.
\tag{2}
\]

If additionally `lambda_{i,tau_n}(infinity)=0` for every `n`, then

\[
\lambda_i^n(\infty)=0,
\qquad
\sum_{t>T}\lambda_i^n(t)\longrightarrow1
\quad\text{for every fixed }T.
\tag{3}
\]

In particular,

\[
\sup_n\sum_{t>T}\lambda_i^n(t)=1
\quad\text{for every }T,
\tag{4}
\]

so the laws have no total-variation-convergent subsequence and no finite-tail
tightness envelope.  Their finite and Never coordinates converge to the zero
subprobability measure.

### Proof

For `t<n`, the root visible at absolute date `t` in (1) is `x_{n-1-t}`.
Reaching that date can only decrease the chance that player `i` stops there,
so

\[
\lambda_i^n(t)\le 1-p_{i,n-1-t}.
\]

Since `c_k` is the product of numbers in `[0,1]`, `c_k <= p_{i,k}`.  Hence

\[
1-p_{i,k}\le1-c_k=a_k.
\]

Summing gives (2); a fixed finite sum of shifted terms of a null sequence
tends to zero.  A finite prefix multiplies the base Never probability by the
individual Continue product.  Thus a zero base Never probability remains
zero, proving the first part of (3).  Total marginal mass is one, so the
finite mass after `T` is one minus the finite head and the Never coordinate.
Equations (3)--(4) follow.

No Nash property is needed for this lemma.  Nash and positive minimum debt
enter only to prove `a_k -> 0` for the actual ray.

## 2. Direct application to the actual Fin4 maximal-prefix ray

Let `packet` be the source-facing object in
`MaximalPrefixRayDichotomy.lean`, and let

\[
D_0=D(\texttt{packet.raySource}),\qquad
L=\texttt{packet.rayLimit}.
\]

The checked scalar identities give

\[
C_n=\frac{D(Z_n)}{D_0}\longrightarrow\frac{L}{D_0}>0,
\tag{5}
\]

and the checked absorption account gives `sum_k a_k < infinity`, hence
`a_k -> 0`.  The base at every rank is the same sure pure pair at date zero,
although its counterfactual continuation varies.  Therefore both players in
`packet.rayTerminal` have base Never probability zero.  Applying the lemma
proves, for either pair member `i`,

\[
\forall T,\qquad
\Pr_{Z_n}(T_i>T,\ T_i<\infty)\longrightarrow1.
\tag{6}
\]

At the same time, the inherited fixed-pair event occurs at date `n` with
exact mass

\[
\Pr_{Z_n}(S=\texttt{rayTerminal}\text{ at date }n)=C_n
 \longrightarrow \frac{L}{D_0}\ge\frac{D_*}{D_0}>0.
\tag{7}
\]

Thus the strongest exact conclusion is:

> **Actual Fin4 maximal-ray unit clock escape.**  Along the source-facing
> maximal-prefix family, each of the two fixed pair members sends all of its
> stopping mass beyond every fixed finite window, while the complete terminal
> law retains the fixed pair with limiting mass at least `D_*/D_0`.

This is stronger than Proposition 2 of the target note in two ways.

1. The finite-tail escape defect is one for the pair marginals, not merely
   `(D_*/D_0)m`.
2. It applies to the actual family whose base profile varies with `n`.

The second point repairs a scope mismatch in the draft.  Proposition 2 is
stated for one fixed tail `tau`, whereas `packet.rayFamily.rayProfiles n`
uses `packet.rayBaseProfile n`, whose reference continuation depends on `n`.
The fixed-tail Never-coordinate formula in the draft cannot literally be
applied to that family.  The sure-pair argument above is insensitive to the
varying counterfactual tail and is therefore the correct adapter.

### Precise topological conclusion

For every fixed absolute date, all players' Quit probabilities on the only
live history tend to zero, so the pointwise limit of the live stopping
behavior is all Never.  For a pair member, however, the actual Never
coordinate is zero at every rank.  Hence the stopping-law map is discontinuous
there: the finite-plus-Never stopping-law coordinates of the approximants
converge to the zero subprobability measure, while the pointwise live-behavior
limit has Never mass one and the compact terminal-law cluster retains positive
pair mass.

This does **not** prove that the compact semantic/law point has no unrelated
behavioral realization.  It proves that it is not the source-faithful
stopping-law limit of this outward-prefix chronology.  That distinction must
be retained in any final statement.

## 3. Sharper generic fixed-tail version

For the fixed-tail setting of Proposition 2, let

\[
C_\infty=\lim_n C_n>0,
\qquad
P_{i,\infty}=\lim_n\prod_{k<n}p_{i,k}.
\]

Then the exact coordinatewise limiting mass is

\[
P_{i,\infty}\Pr_\tau(T_i=\infty),
\]

and the exact missing mass is

\[
e_i=1-P_{i,\infty}\Pr_\tau(T_i=\infty).
\tag{8}
\]

If a coalition containing `i` has tail mass `m`, then

\[
e_i\ge C_\infty m
  =\frac{\lim_n D(Z_n)}{D_0}m
  \ge\frac{D_*}{D_0}m.
\tag{9}
\]

The target should state (8)--(9), rather than only the coarser total-mass
upper bound.  The proof is the same finite-head/Never split used above.

## 4. Stronger unconstrained maximal-root nonclosedness regression

The target's Proposition 1 is correct, but its limiting maximal root absorbs
surely, so the selected child loses all debt.  The following rational Fin4
table keeps a uniform positive reach and child-debt floor while maximizing
over the **full** root cube.

Let the players be `0,1,2,3`.  For every nonempty coalition `S`, define

\[
r_0(S)=\mathbf 1_{\{1\in S,\ 0\notin S\}},
\]

\[
r_1(S)=
\begin{cases}
 1,&0,1\in S,\\
-1,&1\in S,\ 0\notin S,\\
 0,&1\notin S,
\end{cases}
\]

and, for `j=2,3`,

\[
r_j(S)=-\mathbf 1_{\{j\in S\}}.
\tag{10}
\]

For `t in [0,1]`, let `tau_t` have player `1` Quit at date zero with
probability `t`, player `3` Quit there independently with probability `1/2`,
and players `0,2` Never.  Direct unrestricted-deviation calculation gives

\[
U(\tau_t)=(t,-t,0,-1/2),
\qquad B(\tau_t)=(t,0,0,0),
\qquad D(\tau_t)=t+1/2.
\tag{11}
\]

Indeed, player `0` gets one exactly when player `1` Quits without player `0`
and Never attains probability `t`.  Player `1` cannot obtain the positive
`r_1` entry because player `0` Never Quits in the source; every finite Quit
by player `1` pays `-1`, while Never pays zero.  Players `2,3` similarly have
cap zero.

Consider the exact root game at cap `(t,0,0,0)`.  Players `2,3` strictly
Continue.  Write `x` for player `0`'s Quit probability and `y` for player
`1`'s Quit probability.  Player `0`'s Continue and Quit values are

\[
(1-y)t+y,qquad 0,
\tag{12}
\]

while player `1`'s Continue and Quit values are

\[
0,qquad 2x-1.
\tag{13}
\]

For `t>0`, (12) makes player `0` strictly Continue, after which (13) makes
player `1` strictly Continue.  Hence all Continue is the unique exact root.
For `t=0`, any equilibrium with `y>0` would force `x=0`, which in turn makes
player `1` strictly Continue, a contradiction.  Thus `y=0`, player `0` is
indifferent, and (13) requires `0<=x<=1/2`.  The exact-root set is therefore

\[
\{(0,0,0,0)\}\quad(t>0),
\]

and

\[
\{(x,0,0,0):0\le x\le1/2\}\quad(t=0).
\tag{14}
\]

The globally absorption-maximal exact root is unique: all Continue for
`t>0`, and `x=1/2` for `t=0`.  Its continuation reach is always at least
`1/2`.  Exact cap-prefix debt scaling gives selected-child debt

\[
D(\text{child}_t)=
\begin{cases}
t+1/2,&t>0,\\
1/4,&t=0.
\end{cases}
\tag{15}
\]

Thus both parent debt and selected-child debt have fixed positive local
floors, but the full globally maximal exact-root graph is not closed along
the total-variation-convergent actual sources `tau_t -> tau_0`.

This improves the target regression and the currently exported constrained
face example simultaneously:

* maximization is over all product roots;
* selected-root continuation reach is at least `1/2`;
* source debt is at least `1/2`; and
* selected-child debt is at least `1/4`.

The table still has global debt minimum zero at all Never.  It therefore does
not establish nonclosedness on the positive-global-minimum Fin4 domain and is
not a counterexample to uniform-equilibrium existence.

### Novelty comparison

`meta/GRAMMAR.md` already contains a two-player unconstrained globally
maximal-root jump.  The exported packet instead uses a four-player
constrained-face jump with a reach floor.  Proposition 1 in the target is
therefore not conceptually new; it embeds the former phenomenon in Fin4 and
adds a positive parent-debt floor.  Regression (10)--(15) is the sharper
combination not found in the inspected records: Fin4, unconstrained global
maximization, positive reach, and positive debt on both sides of the selected
edge.

## 5. Simultaneous three-port constant-decoration escape

Proposition 3 is a valid instance of `QuittingMarkedPairDecoratedFamily`, but
its postmark tail is tight.  The conclusion that endpoint, comparison, and
postmark-tail ports all need independent actuality control is better tested
by making all three ports escape at once.

Use players `0,1,2,3` and the rational table

\[
r_1(S)=\mathbf 1_{\{S=\{0\}\}},
\qquad r_j(S)=0\quad(j\ne1).
\tag{16}
\]

For rank `n`, let `eta_n` be the profile in which player `3` Quits surely at
relative date `n` and everyone else Never Quits.  Define:

* the endpoint `sigma_n` by `n` all-Continue rows, then a sure pure-`{0}`
  row, then the counterfactual continuation `eta_n`;
* the comparison `widehat sigma_n` by the same `n` all-Continue rows, then a
  sure pure-`{2}` row, then `eta_n`;
* mark `n`, terminal `{0}`, marked owner `0`, and gain mover `1`.

For every `n`, the endpoint whole semantic/law point is

\[
U(\sigma_n)=B(\sigma_n)=(0,1,0,0),
\qquad \operatorname{Law}(\sigma_n)=\delta_{\{0\}}.
\tag{17}
\]

The postmark spine is literally `eta_n`, whose semantic pair is zero and
whose terminal law is the fixed point mass at `{3}`.  Also

\[
\Pr_{\sigma_n}(\{0\}\text{ at mark }n)=1,
\]

\[
U_1(\sigma_n)-U_1(\widehat\sigma_n)=1,
\]

and player `0`'s marked-root defect is zero because player `0`'s reward
coordinate is identically zero.  Hence the **entire base decoration** is
constant.

Nevertheless:

* endpoint player `0` has stopping law `delta_n`;
* comparison player `2` has stopping law `delta_n`; and
* postmark-tail player `3` has stopping law `delta_n` in relative time.

None of these three port families has a total-variation-convergent
subsequence or a finite-tail tightness envelope.  The decoration is realized
by unrelated finite rows (for example the rank-zero row), so the conclusion
is not nonattainment of the finite-dimensional decoration.  It is failure of
source-faithful compact actualization of the displayed moving ancestry.

This regression exactly supports the narrower statement:

> Any endpoint, comparison, or postmark-tail row which is kept as a
> persistent executable port needs its own tightness/decoder passport; the
> current finite-dimensional decoration does not supply one.

It does not show that every use of a normalized minimizer must retain all
three ports.  A compiler which does not expose a port need not actualize it.

## 6. Corrections to the proposed positive replacements

### Tight-port realization

The finite-head/tail proof is sound as a sufficient theorem.  It is not new
relative to the actual-law layer already reviewed and exported, and related
checked stopping-law reconstruction and unrestricted-cap interfaces are
already indexed in `docs/TOOLKIT.md`.  It should be cited as infrastructure,
not presented as a new Fin4 producer.

The passport is sufficient rather than minimal.  Its necessity applies only
to a law-valued port which is required to survive in the executable trace.

### Relaxed maximal roots

Section 5 proves a useful compact-optimization lemma, conditional on the
displayed Lipschitz bound for the Nash-defect function.  It does **not** yet
prove a legal replacement for the exact maximal-prefix construction.

The selected `x_n` is only approximately Nash at the actual cap `b_n`.
Therefore the exact prefix debt identity, the exact cap stack, the exact
punishment-floor relation, and the current return dispatch do not follow.
Calling this a “valid type-2 decoder” is premature until one proves:

1. the exact root-defect modulus in the project's convention;
2. one-step payoff, cap, debt, and complete-law errors;
3. accumulation of those errors under the triangular prefix order;
4. source-faithful ancestry after diagonal extraction; and
5. a downstream consumer accepting the resulting approximate stack.

The compact lemma itself is correct: if `b_n -> b`, `delta_n=||b_n-b||`,
and `x_n` maximizes absorption over

\[
\{x:g(b_n,x)\le 2\delta_n\},
\]

then every cluster point is an absorption-maximal exact root at `b`, provided
`|g(b_n,x)-g(b,x)|<=2 delta_n`.  That statement should remain separate from
an executable decoder claim.

### Program schema

The seven instruction names are a design sketch.  No syntax, trace
restriction, closed ancestry relation, projective realization theorem, or
terminal-consumer induction is proved in the target.  The existing exported
grammar already contains the rigorous conditional architecture.  The schema
should be removed from any proposed new result or explicitly labelled a
non-novel implementation summary.

## 7. Conjecture-facing and export audit

### What is genuinely strengthened

* The actual Fin4 maximal-prefix ray has **unit marginal clock escape** for
  both fixed-pair players, while its terminal law retains positive pair mass.
* The bare full maximal-root relation has an exact Fin4 nonclosedness example
  with positive local debt and reach on both sides of the edge.
* The normalized decoration carrier can stay constant while all three
  operational ports simultaneously escape.

### What remains open

None of these statements constructs terminal approximate Nash profiles, a
positive admissible return, a renewable rank decrease, or an all-behavior
terminal gap.  In particular:

* clock escape is not itself a refusal, charge, or terminal consumer;
* failure of one source-faithful limit does not eliminate finite stopping,
  a different decoder, or pointwise post-limit reconstruction;
* the maximal-root table does not satisfy positive global minimum debt; and
* the decoration regression is a supplied-family insufficiency theorem, not
  an arbitrary-game producer obstruction.

The current checked maximal-ray files already say that the strict ray has no
completion consumer and that its marked suffix moves outward.  The unit
escape theorem quantifies that boundary exactly, but without a consumer it
does not strictly close the live Fin4 capstone.

### Recommended final export content

There should be no standalone `COMPILE_FIN4` export at this stage.

If the existing executable-adapter export is revised, the only recommended
new mathematical content is the self-contained regression (10)--(15), with:

* the exact unrestricted cap calculation (11);
* the full-root Nash calculation (12)--(14);
* the reach and child-debt floors (15);
* comparison with the older two-player global and Fin4 constrained examples;
* the explicit nonclaim that the table has global minimum zero; and
* a fresh independent falsification review.

The unit clock-escape theorem should remain a source-facing Research handoff
with likely Lean shape:

```text
maximalPrefixRay_pairMember_finiteHead_tendsto_zero
maximalPrefixRay_pairMember_neverMass_eq_zero
maximalPrefixRay_pairMember_lateFiniteMass_tendsto_one
maximalPrefixRay_not_stoppingLawTight
```

It should be promoted only when a named theorem consumes the clock-escape
alternative or when a maintained question explicitly accepts this exact
source-faithful nonactualization as a complete negative answer.

## Final assessment

The most valuable new fact in the target is not a complete executable
program.  It is the sharp separation

\[
\boxed{
\text{positive compact terminal pair mass}
\quad\text{with}\quad
\text{unit escape of each pair member's finite clock}.}
\]

That separation is exact on the actual Fin4 maximal-prefix ray and deserves
formalization as a diagnostic theorem.  It currently narrows how the ray may
be compactified, but it does not pass the export gate as a conjecture-facing
consumer.

## Addendum: final math audit of the proposed clock-escape packet

Target audited:
`/tmp/POSITIVE_MINIMUM_EXACT_PREFIX_CLOCK_ESCAPE.md`.

### Final verdict

**PASS after two mandatory corrections.**  The fixed-tail proof, the
varying-tail reverse-prefix proof, and the actual source-facing Fin4 adapter
are mathematically sound.  The packet correctly distinguishes the marginal
stopping-clock topology from the time-forgetting terminal-outcome carrier,
does not attach the earlier uniform-escape atom to the wrong continuation,
and does not claim a strict-ray consumer or an unrelated behavioral
nonattainment theorem.

The Fin4 conclusion is the sharp one established above: each fixed-pair
member has unit late-finite marginal clock escape, while the shifted fixed
pair has stage mass tending to `L / D_0 > 0` and hence gives at least that
much mass to the corresponding time-forgetting terminal-law coordinate.

### Mandatory correction 1: state the strongest exact generic TV theorem

Theorem A currently stops at the coarser floor `q m`.  Its own proof gives a
strictly stronger exact statement.  Define

\[
C_\infty=\lim_n C_n\ge q,
\qquad
a_i=\lim_n\Pr_{\sigma_n}(T_i=\infty).
\]

Then the coordinatewise limiting subprobability has mass `a_i`, concentrated
at Never, and its exact missing mass is

\[
e_i=1-a_i\ge C_\infty m\ge q m.
\tag{A1}
\]

More strongly, for every fixed actual stopping law `nu_i`, writing
`b_i=nu_i({infinity})`,

\[
d_{\rm TV}\!\left(
  \operatorname{Law}_{\sigma_n}(T_i),\nu_i
\right)
\longrightarrow 1-\min\{a_i,b_i\}.
\tag{A2}
\]

Indeed, the finite coordinates of the first law tend pointwise to zero and
the fixed law is tight on the countable finite dates.  The events consisting
of a large finite head, with and without Never, give the lower bound
`max(1-a_i,1-b_i)`, and overlap at Never gives the matching upper bound.
Thus the best possible separation uniformly over fixed actual laws is
exactly `e_i`, attained by the all-Never law.  The packet may retain the
displayed `q m` corollary, but (A1)--(A2) should be the theorem if it is
advertised as the strongest generic result.

For the inherited joint event, the exact mass is `C_n m` and tends to
`C_infinity m`; only the total late marginal mass may be larger.

### Mandatory correction 2: repair the marginal-Never source citation

`FinFourOwnerCompressedMinimumReturnForcedPairPacket.rayBaseProfile_neverMass_eq_zero`
in `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`
states

```text
quittingTerminalOutcomeMass ... none = 0
```

for the **joint terminal-outcome Never coordinate**.  It is not a theorem
that either fixed-pair member's marginal stopping law assigns zero mass to
Never.  The latter fact is true, but at present it must be derived directly
from `rayBaseProfile`: both displayed pair members Quit surely in its initial
`quittingPureSetRoot`.

Accordingly the source correspondence must label
`rayBaseProfile_neverMass_eq_zero` as a joint-outcome fact, not as the
marginal-clock adapter.  The new Lean handoff should use
`quittingBehaviorStoppingLaws`
(`UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`) and
`quittingBehaviorStoppingLaw`
(`UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean`) and prove the
missing pure-pair/prefix marginal lemmas explicitly.

For the actual debt identity, the most direct existing declaration to cite is
`quittingTerminalDebtSum_maximalCapSemanticPrefixProfile_eq` in
`Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`; the packet's cited
semantic-orbit identity is correct but one bridge less direct.

### Exact declaration and scope check

The remaining named declarations in the packet were found with the stated
roles:

* `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash`
  is in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetExcursionReturn.lean`;
* `quittingMaximalCapSemanticPrefixProfile_eq_literalRootStack`,
  `quittingTerminalSemanticDebtSum_maximalCapSemanticPrefixOrbit_eq`, and
  `quittingStageCoalitionMass_maximalCapSemanticPrefixProfile_add` are in
  `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`;
* `quittingMaximalCapSemanticPrefixSurvival_tendsto_limit_div` is in
  `Research/Quitting/MaximalCapSemanticPrefixReturn.lean`; and
* `rayBaseProfile`, `rayBaseProfile_stageMass_eq_one`,
  `rayProfiles_stageMass_eq_survival`, and
  `nonempty_maximalPrefixRayMinimumReturn_or_stall` are in
  `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`.

The reverse-prefix theorem applies to the canonical ray before the
minimum-return/stall split, hence to both `L = D_*` and `L > D_*`.  Using it
only for the live strict arm is correct but is a restriction of the theorem,
not a hypothesis needed by the clock calculation.

No further mathematical correction is required.  In particular, “no
ancestry-preserving strategic-TV limit” is correctly scoped; it must not be
shortened to “the compact semantic/law point has no actual realization.”
