# A law-tight positive face with a finite atom and unique cap root can have UE

**Author:** `CODEX_SOURCE_GATE`  
**Status:** proved ordinary mathematics; exact source/API audit; not Lean-checked;
no Fin4 hard-residual consumer; the singleton/Never no-go now includes a
literal positive law-tight minimum-face provenance  
**Date:** 2026-08-31

## 1. Question and answer

The checked law-tight saturation construction supplies, after a suitable
origin and positive debt floor have been given, a compact hull, a positive-
debt minimum equality level set, a retained finite law atom, and a unique
all-Continue exact root against every minimum-face cap.  The live question is
whether the retained atom and the hard-residual signs consume this apparently
inert face.

There are two exact conclusions.

1. The exposed **local face fields do not imply a contradiction or terminal
   consumer**, even after adding four-player punishment normality and strictly
   positive solo rewards.  Section 3 gives a rational Fin4 game in which the
   entire law-tight hull is one positive-debt point, its law is a unit finite
   atom, and its cap has unique all-Continue root, while the game has an exact
   unrestricted-behavior terminal Nash profile and hence a uniform-equilibrium
   payoff.
2. The marked two-port construction proposed in
   `gpt/NONZERO_PERSIST_ATTEMPT_2.md`, Followup 2, is not produced by the
   current paid-row and chronological-law APIs.  Its target projection
   comparison is conditionally valid only after resolving a conflation between
   the checked unrestricted law-tight hull and a new \(p\)-zero-restricted
   hull.  Even if the new paired carrier were supplied, its output is a
   strengthened inert object, not a terminal consumer.

The regression does **not** satisfy the positive global debt infimum or a
terminal exploitability witness.  It therefore does not model the whole hard
residual and is not a counterexample to the conjecture.  Its force is exact
field independence: a proof in the hard branch must use global-minimum/
terminal-gap data through a new operation tying the historical atom to an
executable profitable or charged edge.

## 2. Exact checked source boundary

The following interfaces were inspected.

- `quittingLawTightCapNashSaturationHull`,
  `quittingLawTightCapNashSaturationHull_atomCone`, and
  `exists_quittingLawTightCapNashSaturationHull_minimum_retaining_atom` in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashSaturationHull.lean`;
- `quittingLawTightCapNashSaturationMinimumFace_rootNash_iff_allContinue`,
  `quittingLawTightCapNashSaturationMinimumFace_allContinue_prefix_eq`, and
  the finite absorption telescopes in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashMinimumFace.lean`;
- `lawTightStrictSaturation_fullDebt_or_resetRigid_or_singletonNeverCycle`
  and `finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber` in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashStrictMinimum.lean`
  and
  `UniformEquilibrium/Diagnostics/Quitting/FinFourLawTightCapNashStrictMinimum.lean`;
- `exists_finFourHardResidual_minimumLaw_causalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`;
- `QuittingMinimumLawCausalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLawCarrierCausalization.lean`;
- `QuittingFixedLawResetDispatch` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`;
- `quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
  and the exact cap-prefix debt-scaling declarations in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
- `QuittingPaidFirstDisagreementRow` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
- `PositiveTotalSlopeFullReplacement.mover_debt_eq_zero` and the
  full-replacement gain identities in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PositiveTotalSlopeFullReplacement.lean`;
- `quittingPunishmentValue_le_max_solo` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean` and the definition
  `IsQuittingNormalPlayer` in
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`;
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- `isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR`
  in `UniformEquilibrium/Quitting/Punishment/SoloCycleCompletion.lean`;
- `collisionForm`, `hazard_eq_zero_of_isNash`, and
  `eq_allContinueRoot_of_isNash` in
  `UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskyCapLimitRootUniqueness.lean`;
- `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts` in
  `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`;
- `QuittingChronologicalEvent`, its compact probability-measure space, and
  the chronological-law compactification in
  `UniformEquilibrium/Quitting/AbsorptionPath/ChronologicalMarkedRootSequenceLaw.lean`
  and
  `RootSequenceAbsorbingCompletionChronologicalLimit.lean`.

The hard source composition is real, although no single declaration packages
all of it.  A `FinFourQuantitativeFullSupportHardResidual` supplies a globally
minimizing joint semantic/law point, positive literal debt infimum, and a
`QuittingMinimumLawCausalSuffixAtom`.  Choosing that object's coalition gives
the supplied positive atom needed by the saturation theorem.  Since the
origin is already globally minimizing, it is also a hull minimum.  The
minimum-face theorem then forces the unique all-Continue cap root.

What the composition does **not** do is turn the suffix atom into a prefix
root atom.  The causal-suffix structure says explicitly that the positive
stage lies inside each suffix profile after the arbitrarily deep cap--Nash
stack.  At a positive global minimum, those cap roots have vanishing aggregate
absorption and become all-Continue on the equality face.  No checked field
makes the retained historical atom an exact Nash--Bellman edge.

## 3. Exact Fin4 regression

Let \(I=\operatorname{Fin}4\).  For a nonempty coalition \(T\subseteq I\)
and player \(i\), define the rational terminal reward

\[
r_i(T)=
\begin{cases}
2,&i\notin T\text{ and }T=I\setminus\{i\},\\
1,&i\notin T\text{ and }T\ne I\setminus\{i\},\\
1,&i\in T\text{ and }(T=\{i\}\text{ or }T=I),\\
0,&i\in T\text{ and }\{i\}\subsetneq T\subsetneq I.
\end{cases}                                             \tag{3.1}
\]

Every terminal coordinate lies in \([0,2]\).  The Never payoff is, as in the
project model, zero.

### Theorem 3.1 (singleton law-tight face with UE)

For the table (3.1), let \(\sigma^I\) be the profile in which all four
players Quit at date zero.  Let

\[
 z=(u,c)=\operatorname{Sem}(\sigma^I),
 \qquad \mu=\operatorname{Law}(\sigma^I).
\]

Then:

1. \(u_i=1\), \(c_i=2\), and \(d_i(z)=1\) for every \(i\), so
   \(D(z)=4>0\);
2. \(\mu(I)=1\), so \((z,\mu)\) retains a finite atom of mass one;
3. all Continue is the unique exact product-root Nash equilibrium against
   \(c\);
4. the complete-law fibre of \(\mu\) in the joint semantic/law carrier is the
   singleton \(\{(z,\mu)\}\);
5. consequently

   \[
   \mathscr H:=
   \operatorname{quittingLawTightCapNashSaturationHull}
     (r,(z,\mu))=\{(z,\mu)\};                           \tag{3.2}
   \]

   its minimum equality level set is the same singleton, has positive debt
   four, retains the unit atom, and has the unique all-Continue prefix
   identity;
6. all four players are punishment-normal and have solo reward one; and
7. for every fixed \(a\in I\), the profile in which only \(a\) Quits at date
   zero is an exact terminal Nash profile against every unrestricted
   behavioral unilateral deviation.  Its payoff is the all-ones vector, which
   is therefore a uniform-equilibrium payoff.

### Proof

At \(\sigma^I\), every player receives \(r_i(I)=1\).  If player \(i\)
alone changes the date-zero action to Continue, the other three still Quit
and the player receives

\[
r_i(I\setminus\{i\})=2.
\]

No terminal payoff exceeds two, so the complete behavioral best-response cap
is exactly two.  This proves item 1.  Item 2 is literal absorption at date
zero.

Fix an arbitrary product root and condition on the opponents' Quit coalition
\(A\subseteq I\setminus\{i\}\).  If \(A=\varnothing\), player \(i\)'s Quit
payoff is the solo value one while Continue leads to tail value two.  If
\(A\ne\varnothing\), (3.1) gives

\[
r_i(A\cup\{i\})=r_i(A)-1.                              \tag{3.3}
\]

Thus the Quit-minus-Continue endpoint difference is exactly \(-1\), for
every player and every opponents' product marginal.  Any positive Quit
probability violates exact support optimality.  All Continue is exact, hence
it is the unique exact root against \(c\).  This proves item 3.

For item 4, take any joint-carrier point with law \(\mu=\delta_I\).  The
checked reward-moment identity forces its prescribed vector to equal
\(r(I)=\mathbf1\).  To identify its cap, approximate it by actual profiles
\(\sigma_n\) whose semantic pairs and complete laws converge to the point.
For a fixed \(i\), replace player \(i\)'s strategy by always Continue.  On
every original path whose terminal coalition is \(I\), the pre-action history
up to the terminal date is unchanged, all three opponents still Quit there,
and the deviator receives two at \(I\setminus\{i\}\).  On every other path
the deviator receives a nonnegative terminal or Never payoff.  Hence

\[
\operatorname{Cap}_i(\sigma_n)
\ge2\Pr_{\sigma_n}(T=I).
\]

The right side tends to two, while the reward bound gives the reverse cap
bound two.  Every cap coordinate in the limiting fibre is therefore two.
The fibre is the claimed singleton.

Now the singleton set \(\{(z,\mu)\}\) is itself a closed law-tight cap--Nash
invariant: it belongs to the carrier; its only exact root is all Continue,
whose semantic and law prefixes are identities; and every same-law
replacement in the carrier is the same point by item 4.  Since the canonical
hull contains its origin and is contained in every such invariant, (3.2)
follows.  Item 5 is immediate.

For item 6, the solo reward is one.  The checked general bound

\[
P_i\le\max\{r_i(\{i\}),0\}=1
\]

therefore gives punishment normality for every player, because
`IsQuittingNormalPlayer` is exactly the inequality between the punishment
value and that player's solo payoff.

Finally fix \(a\).  The sure singleton \(\{a\}\) pays one to every player.
If \(a\) refuses at date zero, all opponents Continue forever; every later
solo exit pays one and Never pays zero.  The owner cannot exceed one.  If an
outsider \(i\ne a\) also Quits at date zero, the proper collision payoff is
zero, whereas Continue pays one; after date zero the game has already
absorbed.  Thus no arbitrary behavioral replacement gains.  This is an exact
terminal Nash profile.  The checked theorem
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` gives the
uniform payoff \(\mathbf1\).  QED

### Exact scope

The singleton Nash profile has total debt zero, so

\[
\inf_\sigma D(\sigma)=0.                               \tag{3.4}
\]

Accordingly, (3.2) is a positive minimum **of its saturation hull**, not a
positive global carrier minimum.  The table also has negative singleton
collision increments:

\[
r_k(\{a,k\})-r_k(\{a\})=-1
\qquad(a\ne k).                                        \tag{3.5}
\]

Thus it preserves punishment normality and positive solos but not the
terminal-gap collision signs.  An example satisfying the entire hard
residual and UE is impossible by definition.  The missing extra field is not
another static face decoration: it is the global positive-infimum/terminal-
gap provenance, together with a new source-preserving operation that couples
its collision or paid signs to the retained atom.

## 4. Followup 2: upstream identity audit

Followup 2 starts from profiles \(\sigma_n^-\), \(\sigma_n^+\), fixed
coalitions \(B,A=B\triangle\{p\}\), a reach \(m_n\), and claims

\[
g_n=m_n(r_p(A)-r_p(B)),                                \tag{4.1}
\]

\[
\mu_n^- = \mu_n^+ -m_n\delta_A+m_n\delta_B,           \tag{4.2}
\]

and

\[
d_p(\sigma_n^+)=0,\qquad d_p(\sigma_n^-)=g_n.         \tag{4.3}
\]

These identities are mathematically correct for a **binary attained paid
port** having all of the following additional fields:

- the two actual profiles differ only in player \(p\)'s action at one reached
  history;
- conditional on reaching that history, all opponents' simultaneous action
  is one fixed coalition, so the entire reached mass changes exactly from
  \(B\) to \(A\);
- both ports absorb at that row, with no residual later event; and
- the target strategy attains player \(p\)'s full behavioral cap.

The checked `QuittingPaidFirstDisagreementRow` does not supply this object.
It stores one receiving profile, two pure-time witnesses, an opponents'
survival weight, and the exact scalar identity

\[
U_p(\text{receiving witness})-U_p(\text{source witness})
=\text{liveMass}\times\text{reachedGain}.              \tag{4.4}
\]

Its requested `gain` is only bounded above by the left side.  The reached
gain is a difference between Quit-now value and a later stopping value,
averaged over the opponents' row and continuation.  The structure does not
assert a fixed \(B/A\) coalition toggle, an exact two-atom law difference, or
attainment of the unrestricted cap.

The full-replacement lane supplies a different part of the desired picture.
Changing one player's complete strategy preserves that player's cap because
the opponents are fixed; its checked gain identity is

\[
g=d_p(\text{source})-d_p(\text{endpoint}),             \tag{4.5}
\]

and exact-diagonal cluster extraction can give endpoint debt zero.  It does
not say that the complete terminal laws differ by one fixed atomic toggle at
one row.  No checked adapter co-realizes (4.2), (4.4), and the zero endpoint
debt on one common subsequence.  The stated lower floors
\(m_n\ge\rho^2\) and \(g_n\ge\rho D_*/3\) were likewise not found as fields
of one named checked paid-port object.

Therefore equations (4.1)--(4.3) are a new producer hypothesis, not a
consequence of the cited paid-row API.

## 5. Followup 2: compact marked coupling audit

The existing compact chronological event records

\[
(\text{absorption clock},\text{product root},
  \text{continuation payoff vector},\text{coalition}). \tag{5.1}
\]

It does **not** record a behavioral post-row tail, a source profile, a target
profile, or a unilateral source--target coupling.  Its compact
probability-measure space consequently does not by itself provide the
proposed \(\Gamma_n\).

One can certainly define a probability law on pairs of the compact events.
To obtain the claimed carrier, however, one must additionally prove:

1. both marginals are the chronological laws of the two actual ports;
2. the off-diagonal support has the required common-history interpretation;
3. the semantic/law endpoints and the coupling arise from the same profiles;
4. common behavioral-tail ancestry survives the closure; and
5. the common-prefix operation preserves all four consistency relations.

None is a field of the current chronological-law compactification.  Replacing
the behavioral tail by the continuation payoff vector in (5.1) makes equality
closed but loses literal tail ancestry.  Keeping the complete behavioral tail
requires a new compact coding and a proof that the relevant semantic and
coupling graph is closed; terminal payoff and best-response envelopes are not
automatically continuous in an unqualified behavioral product topology.

There is also a smaller topology correction.  The proposed toggle set
\(\mathcal T_{p,B,A}\) includes equality of real clocks, roots off \(p\), and
continuation vectors.  It is closed, but it is not clopen merely because its
coalition coordinates are discrete.  Weak convergence therefore does not
give

\[
\Gamma_0(\mathcal T)=\lim_n\Gamma_n(\mathcal T)
\]

as claimed.  If genuine couplings with a uniform mass floor on this one fixed
closed set were available, Portmanteau would still give the sufficient
one-sided conclusion

\[
\Gamma_0(\mathcal T)\ge
\limsup_n\Gamma_n(\mathcal T)>0.                       \tag{5.2}
\]

Thus the equality is false as a topology assertion, while positive retention
would survive after the larger producer gap was repaired.

## 6. Followup 2: prefix algebra and the \(p\)-zero projection

The target prefix algebra is correct.  If \(x\) is exact Nash against the
target cap, checked cap-prefix transport gives

\[
D(T_xz^+)=c(x)D(z^+),
\qquad d_p(T_xz^+)=c(x)d_p(z^+).                       \tag{6.1}
\]

The marked mass and a genuinely co-realized horizontal gain would also scale
by \(c(x)\) under a common literal prefix.  For the source coordinate, equality
of the two ports' player-\(p\) caps is enough to transfer player \(p\)'s
endpoint optimality, but the named total debt-scaling theorem requires a full
root-Nash hypothesis at the relevant cap.  A separate coordinate lemma is
needed if only the \(p\)-cap is shared.

Conditional on a correctly defined compact paired carrier and invariant
operations, the cone calculation

\[
D(z^+)m_0\le D_0m,\qquad D(z^+)g_0\le D_0g            \tag{6.2}
\]

is sound: exact prefixing scales both sides, admissible replacement decreases
only the left debt, and the inequalities are closed.

The comparison with the target-only face needs more care.  The checked
`quittingLawTightCapNashSaturationHull` is **not** a \(p\)-zero hull.  Its
same-law replacement clause accepts every total-debt-nonincreasing
replacement.  Such a replacement may decrease other coordinates while
introducing positive \(p\)-debt.  Hence the set of \(p\)-zero points is not
known to be invariant under that checked clause.

There are two honest formulations.

1. Compare the paired hull to the existing unrestricted target hull.  For
   every unrestricted target invariant \(K\), the inverse image
   \(\pi_+^{-1}(K)\) inside a genuinely \(p\)-zero paired ambient carrier is a
   paired invariant.  Then

   \[
   \mathscr H^\pm\subseteq\pi_+^{-1}(\mathscr H^+),
   \qquad D^+\le D^\pm.                                \tag{6.3}
   \]

   This comparison is valid, but \(\mathscr H^+\) should not be called
   \(p\)-zero.
2. Define a new target-only \(p\)-zero hull whose replacement operation is
   explicitly restricted to \(p\)-zero replacements.  Then (6.3) needs a new
   inverse-image proof against that altered operation.  It is not the
   pre-existing minimum face.

Followup 2 currently mixes these formulations.  Its inequality can be saved,
but the assertion that equality attaches the port to the **pre-existing
\(p\)-zero face** is not justified as written.

## 7. Final verdict on the proposed paired face

Even granting the stronger binary paid port and the missing compact carrier,
the proposed minimum argument proves only:

- positive historical off-diagonal marked mass;
- a source companion with positive player-\(p\) debt;
- a target with zero player-\(p\) debt; and
- unique all-Continue exact target roots.

The paid mass remains a horizontal historical comparison, not charge of an
exact Nash--Bellman edge.  The equality arm is therefore a strictly decorated
version of the same inert minimum face.  The positive lift-gap arm says that
some target-only debt reduction has no marked source lift; it gives neither a
renewable finite rank nor a terminal strategy.  Calling the terminal witness,
existential capacity bound, and non-effective separation a counterexample
certificate does not add a new conclusion: the terminal witness already
assumes the all-behavior positive-gap branch, and no finite table or terminal
consumer is produced.

The smallest useful missing field is one of the following, on the **same
co-realized paired object**:

1. a literal exact or support-vanishing Nash--Bellman connector carrying a
   fixed fraction of the marked mass;
2. an extension-compatible operation that turns the lift gap into a strictly
   decreasing finite rank; or
3. a behavioral-tail compactification whose limit marked port feeds an
   existing unrestricted-deviation terminal consumer.

Without one of these, the marked two-port construction is architectural
validation only.  It does not consume the saturation face.

## 8. Concrete next question

Can the hard-residual singleton collision theorem be attached to the
*specific reached history* supporting the causal suffix atom, so that one
fixed player has a support-small root deviation of positive absolute reach at
that history?  Table (3.1) shows that punishment normality, positive solos,
positive hull debt, a unit atom, and unique all-Continue root do not imply such
a collision.  Followup 2 shows that remembering a historical paid comparison
does not make it an exact root edge.  A same-history collision attachment is
the first extra field not eliminated by either no-go.

## 9. Post-integration audit of the strict-minimum trichotomy

The subsequently integrated declarations
`lawTightStrictSaturation_fullDebt_or_resetRigid_or_singletonNeverCycle` and
`finFour_noUniformPayoff_exists_lawTightStrictMinimumChamber` are a genuine
source improvement: under the literal Fin4 no-uniform-payoff hypothesis they
now produce the positive minimum and classify it into the three named
chambers.  They do not, however, change the consumer boundary.  In
particular, a binding-collision cycle is a cycle of **blockers of positive
solo cap roots**, not a Nash--Bellman singleton cycle.

### 9.1 Exact singleton/Never chamber regression

There is a sharper UE regression matching every exposed local field of the
third chamber.  Identify the four players cyclically and write
$p(i)=i-1\pmod 4$.  For every nonempty terminal coalition $T$, put

\[
r_i(T)=
\begin{cases}
-1,&i\notin T,\\
0,&T=\{i\},\\
0,&i\in T\text{ and }T\setminus\{i\}=\{p(i)\},\\
-3,&i\in T\text{ and }T\setminus\{i\}\ne\varnothing,
\ T\setminus\{i\}\ne\{p(i)\}.
\end{cases}                                            \tag{9.1}
\]

All table rewards are nonpositive and every solo self-reward is zero.  Thus
every unrestricted behavioral cap is at most zero.  At a profile where all
opponents Continue surely at date zero, a player can secure zero by Quitting
there alone, so every cap at that profile is exactly zero.

Against the zero cap, player $i$'s Quit-minus-Continue difference,
conditional on the opponents' Quit coalition $A$, is

\[
\Delta_i(A)=
\begin{cases}
0,&A=\varnothing,\\
1,&A=\{p(i)\},\\
-2,&\text{otherwise}.
\end{cases}                                             \tag{9.2}
\]

All Continue is the unique exact product-root Nash.  Here is a short proof,
included because uniqueness is the nontrivial part of the regression.  Let
$q_i$ be the Quit marginal of an exact root and suppose some $q_i>0$.
If $q_{p(i)}=0$, player $i$'s supported-Quit inequality forces every
other opponent marginal to vanish; then $i$ is the sole positive marginal,
and its successor has a strictly positive Quit difference while Continue is
played surely, a contradiction.  Hence predecessor-closure makes all four
marginals positive.  The positive singleton-predecessor event in (9.2) then
forces every marginal to be strictly below one.  Put
$a_j=q_j/(1-q_j)>0$.  After dividing player $i$'s supported-Quit
inequality by the positive all-opponents-Continue product and retaining just
one bad singleton term, one gets

\[
a_{p(i)}\ge 2a_{p^2(i)}.                               \tag{9.3}
\]

Multiplying (9.3) over the four players says
$\prod_j a_j\ge16\prod_j a_j$, impossible.  Thus every $q_i=0$.

Fix an owner $o$ and $0<s<1$.  Let $o$ Continue at date zero, Quit at date
one with probability $s$, and otherwise Never Quit; every other player
always Continues.  Every player can Quit alone at date zero, so the cap is
zero.  The joint semantic/law point has

\[
\mu=s\delta_{\{o\}}+(1-s)\delta_{\mathrm{Never}},
\qquad c=0,
\qquad u_o=0,\quad u_i=-s\ (i\ne o).                  \tag{9.4}
\]

Consequently $d_o=0$, every other debt equals $s>0$, and total debt is
$3s>0$.  It has positive singleton/Never support, a unique zero-debt owner,
cap binding, and the unique all-Continue cap root.  Moreover every player is
cap-binding, and

\[
r_i(\{p(i),i\})-r_i(\{p(i)\})=1,                     \tag{9.5}
\]

so the binding-collision graph contains the directed four-cycle.

Nevertheless the all-Continue behavioral profile is an exact terminal Nash
profile with payoff zero: against opponents who never Quit, every unilateral
behavior produces either the player's zero solo reward or Never payoff zero.
It therefore gives a uniform-equilibrium payoff.  Every player is also
punishment-normal, since
`quittingPunishmentValue_le_max_solo` gives $P_i\le0$.

Thus this point instantiates every field of
`QuittingSingletonNeverBindingCycleChamber` while the game has UE.  It does
**not** instantiate the external minimum-face provenance used by the
trichotomy: moving the owner's random Quit to date zero gives a same-law
profile at which some nonpredecessor cap coordinates fall to their prescribed
payoffs, hence lowers total debt.  The regression also has global debt
infimum zero.  Its exact force is that the chamber structure and its finite
directed binding cycle are not by themselves a terminal consumer; any use of
the third arm must genuinely exploit the separately supplied face-minimum
provenance.

### 9.2 The smallest direct terminal consumer

The smallest checked terminal consumer for the third chamber is not the
binding cycle.  It is one positive proper solo row at the support owner
$o$, exact endpoint Nash against the **singleton payoff vector**:

\[
0<h(Q),\qquad
\operatorname{EndpointNash}
  \bigl(\operatorname{SoloRoot}(o,h),r(\{o\})\bigr).  \tag{9.6}
\]

The hard residual already gives punishment normality
$P_o\le r_o(\{o\})$.  Therefore (9.6) feeds the checked theorem
`isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR`
in `UniformEquilibrium/Quitting/Punishment/SoloCycleCompletion.lean` and
immediately contradicts the no-uniform-payoff hypothesis.

This pinpoints the adapter gap exactly.  The chamber supplies root uniqueness
against its displayed cap $c$, while (9.6) is Nash against the full vector
$r(\{o\})$.  Indeed, every edge $o\to j$ of the binding cycle proves that
**every** positive solo-$o$ root fails Nash against $c$: player $j$ has
zero cap defect and strictly positive joining gain.  Thus replacing $c$ by
the singleton continuation vector is essential; a cap-root reinterpretation
cannot prove (9.6).

### 9.3 Smallest genuine renewable rank for the reset arm

For a face point $z$, define the finite rank

\[
R(z)=4-\bigl|\{i:d_i(z)=0\}\bigr|.                    \tag{9.7}
\]

A genuinely renewable reset consumer needs only a same-face successor
$z'$ satisfying:

1. the same complete law (hence the same retained positive atom);
2. every zero debt of $z$ remains zero at $z'$; and
3. one coordinate with positive debt at $z$ has zero debt at $z'$.

Then $R(z')<R(z)$.  The strict trichotomy reapplies at $z'$; full debt
support is impossible because an old zero was preserved.  Since the minimum
has positive total debt, not all four coordinates can become zero.  Hence on
Fin4 this connector can fire only finitely many times and exits the
reset-rigid arm into the singleton/Never chamber after at most two successful
connector moves.
This is a genuine discrete rank, not a real-valued descent or compactness
reformulation.

The checked `QuittingFixedLawResetDispatch` falls exactly one compound field
short: it resets the **already zero** owner, does not assert preservation of
the other zero coordinates, and its transfer inequality may increase the
other debts.  Its supported strict toggle does not select a new zero-debt
owner.  Therefore strict zero-set extension in (9.7) is a precise new
connector requirement, not a consequence of the current dispatch.

Among the three chambers, (9.6) is the smallest available terminal consumer.
The monotone-new-zero connector is the smallest honest renewable finite rank.
The full-debt arm still requires chronological source attachment: positivity
of four static carrier debts does not select a persistent hazard label or an
actual Nash--Bellman spine.

## 10. Minimum-face provenance still does not supply the singleton consumer

Section 9.1 deliberately stopped short of the external minimum-face field.
The following exact rational regression closes that loophole.  It has a
singleton canonical law-tight hull, so its displayed singleton/Never point is
literally a positive hull minimum and minimizes debt over its whole same-law
carrier fibre.  Nevertheless neither the positive solo endpoint in (9.6) nor
a same-law debt decrease exists.  The game also has an explicit stationary
uniform equilibrium.

This is ordinary mathematics, not a new Lean declaration.  Its root
calculation is the same exact collision-form calculation checked for
`FinFourOwnerRiskyCapLimitRootUniqueness.eq_allContinueRoot_of_isNash`.

### 10.1 Rational reward table

Let the players be $0,1,2,3$, put

\[
 c=(0,0,0,1),
\]

and, for an opponent coalition $A$, define the additive membership gains

\[
\begin{aligned}
 g_0(A)&=1_{1\in A}-2\,1_{2\in A}+\tfrac1{100}1_{3\in A},\\
 g_1(A)&=1_{0\in A}-2\,1_{2\in A},\\
 g_2(A)&=\tfrac25(1_{0\in A}+1_{1\in A})
          -\tfrac{39}{100}1_{3\in A},\\
 g_3(A)&=-1_{0\in A}-1_{1\in A}+1_{2\in A}.
\end{aligned}                                                   \tag{10.1}
\]

Define passive rewards $a_i$ on opponent coalitions by
$a_i(\varnothing)=c_i$, by

\[
 a_1(\{0\})=-1,\qquad a_2(\{0\})=-\tfrac25,
 \qquad a_3(\{0\})=1,                                      \tag{10.2}
\]

and on every other nonempty opponent coalition by

\[
 a_0=-\tfrac{99}{25},\qquad a_1=-\tfrac92,
 \qquad a_2=\tfrac{99}{50},\qquad a_3=-\tfrac{11}{3}.       \tag{10.3}
\]

For each nonempty terminal coalition $T$, set

\[
 r_i(T)=a_i(T\setminus\{i\})
       +1_{i\in T}\,g_i(T\setminus\{i\}).                 \tag{10.4}
\]

This specifies every coordinate of the finite reward table by rational
numbers.

### 10.2 The singleton/Never point and the cap root

Let player $0$ Quit at date zero with probability $1/2$, and, after date-
zero survival, let every player Continue forever.  Players $1,2,3$ also
Continue at date zero.  The resulting terminal law and prescribed payoff are

\[
 \mu=\tfrac12\delta_{\{0\}}+\tfrac12\delta_{\mathrm{Never}},
 \qquad
 u=(0,-\tfrac12,-\tfrac15,\tfrac12).                        \tag{10.5}
\]

The unrestricted behavioral cap is exactly $c$.  Player $0$ always gets
zero.  Players $1$ and $2$ can Quit at date zero and get zero whether or
not player $0$ Quits, since both their solo and their $\{0,i\}$ rewards are
zero.  Continuing gives respectively $-1/2$ and $-1/5$.  Player $3$
gets $1$ by Continuing at date zero and Quitting at date one after survival:
an earlier owner exit pays $r_3(\{0\})=1$, while survival pays the solo
reward $1$.  Quitting immediately gives only $1/2$.  Thus

\[
 d=c-u=(0,\tfrac12,\tfrac15,\tfrac12),
 \qquad D=\sum_i d_i=\tfrac65.                              \tag{10.6}
\]

The owner $0$ is the unique zero-debt player and all four singleton caps
bind.  The gains

\[
 g_1(\{0\})=1,\quad g_2(\{1\})=\tfrac25,\quad
 g_3(\{2\})=1,\quad g_0(\{3\})=\tfrac1{100}              \tag{10.7}
\]

give the binding cycle $0\to1\to2\to3\to0$.

Against cap $c$, passive rewards cancel coalition by coalition.  If $q_i$
is player $i$'s Quit probability, the four Quit-minus-Continue endpoint
differences are exactly

\[
 \Gamma(q)=
 \left(
 q_1-2q_2+\tfrac1{100}q_3,
 q_0-2q_2,
 \tfrac25(q_0+q_1)-\tfrac{39}{100}q_3,
 -q_0-q_1+q_2
 \right).                                                  \tag{10.8}
\]

The exact complementarity enumeration for (10.8) has only $q=0$.  This is
the rational collision-form enumeration used by
`eq_allContinueRoot_of_isNash`; its proof depends on (10.8), not on the
passive part of `sharpReward`.  Hence all Continue is the unique exact root
against $c$.

All four players are punishment-normal.  Their singleton rewards are the
nonnegative coordinates of $c$, and
`quittingPunishmentValue_le_max_solo` gives
$P_i\le\max(0,c_i)=c_i$.

### 10.3 Exact minimization over the complete-law fibre

Let $(\widehat u,\widehat c,\mu)$ be any point of the joint terminal-semantic
carrier with the same complete law (10.5).  The reward-moment identity fixes
$\widehat u=u$.  We claim coordinatewise that

\[
 \widehat c_i\ge c_i.                                      \tag{10.9}
\]

To see this at the carrier boundary, take one common realizing sequence of
behavioral profiles.  Its joint Never mass tends to $1/2$, so every
player's marginal Never probability is eventually bounded below.  For each
outsider $j\ne0$, the singleton-$j$ law mass tends to zero.  Independence
of the four stopping times then forces the outsider's total finite stopping
probability to tend to zero.  This is the same quantitative argument used in
`terminalSemanticLaw_singletonNever_zeroDebt_cap_eq_singletonReward`.

For coordinates $0,1,2$, immediate Quit therefore has limiting payoff
zero: absent the vanishing outsider events it produces either the relevant
solo or the $\{0,i\}$ pair, both worth zero.  Thus
$\widehat c_0,\widehat c_1,\widehat c_2\ge0$.

For coordinate $3$, in the $n$-th realizing profile choose a deterministic
date $t_n$ at which player $0$'s stopping atom is at most $1/n$, and
Quit at $t_n$ if the game has survived.  If player $0$ stopped earlier,
the payoff is $r_3(\{0\})=1$; if player $0$ stops later or Never, the
payoff is the solo value $1$.  The only losses come from the selected
simultaneous owner atom and the vanishing finite stopping masses of players
1 and 2.  Boundedness of the finite reward table makes their total payoff
error tend to zero.  Hence $\widehat c_3\ge1$, proving (10.9).

It follows that every same-law carrier point has debt at least $6/5$, and
equality forces $\widehat c=c$.  Thus the displayed point is the unique
semantic point in its law fibre with debt at most $6/5$.  This rules out the
requested same-law debt-lowering contradiction even before invoking hull
minimality.

### 10.4 The canonical hull and minimum face are singletons

Take the displayed point $z=((u,c),\mu)$ as origin.  The singleton set
$\{z\}$ is a law-tight cap--Nash invariant:

1. it is closed, lies in the joint carrier, and contains its origin;
2. every exact cap root is all Continue by (10.8), and its semantic and law
   prefixes fix $z$; and
3. every same-law replacement of debt at most $6/5$ equals $z$ by
   Section 10.3.

Since the canonical hull is the intersection of all such invariants and
always contains its origin,

\[
 \mathcal H(r,z)=\{z\}.                                    \tag{10.10}
\]

Consequently $z$ is a literal
`IsQuittingLawTightCapNashSaturationMinimum`, its minimum equality level set
is $\{z\}$, its minimum debt is the positive number $6/5$, and its finite
singleton atom has mass $1/2$.  This supplies exactly the external
minimum-face provenance that Section 9.1 omitted.

### 10.5 The proposed solo terminal consumer still fails

The singleton payoff vector at the support owner is

\[
 r(\{0\})=(0,-1,-\tfrac25,1).                              \tag{10.11}
\]

At every positive solo-$0$ root, player $1$'s Continue payoff is $-1$,
both when player $0$ Quits and on root survival with continuation vector
(10.11).  Quitting gives zero, both alone and together with player $0$.
Thus player $1$'s deviation gain is exactly $1$ for every positive owner
hazard.  No positive solo-$0$ root is endpoint Nash against (10.11), so the
checked consumer in (9.6) cannot be obtained from minimum-face provenance.

### 10.6 An explicit stationary uniform equilibrium

The regression is not a counterexample to the conjecture.  Let every player
Quit independently with probability $1/2$ at every surviving date and put

\[
 v=(-\tfrac{99}{25},-4,\tfrac{41}{25},-3).                 \tag{10.12}
\]

For each player, every coefficient in (10.1) occurs in four of the seven
nonempty opponent coalitions.  Hence

\[
 \sum_{A\ne\varnothing}g_i(A)=v_i-c_i.                    \tag{10.13}
\]

Since the eight opponent coalitions are equiprobable, (10.13) says that Quit
and Continue have the same one-step value against continuation $v$.  A
direct sum of the rewards in (10.2)--(10.4) gives

\[
 \sum_{\varnothing\ne T\subseteq I}r_i(T)=15v_i
 \qquad(i=0,1,2,3).                                       \tag{10.14}
\]

Equation (10.14) is precisely the Bellman equation: the empty root coalition
has probability (1/16), as does each of the fifteen nonempty coalitions.
Thus the half-hazard product root is exact Nash against its own continuation
payoff and reproduces $v$.

This stationary profile absorbs each stage with probability $15/16$.
Against any unrestricted history-dependent unilateral deviation, the three
stationary opponents alone make survival through $N$ stages at most
$(1/8)^N$.  One-step optimality and the bounded terminal rewards therefore
give the usual dynamic-programming inequality, while the remaining horizon
error tends to zero geometrically.  Hence $v$ is an unrestricted-behavior
uniform-equilibrium payoff.

### 10.7 Sharp conclusion

The added field requested after Section 9 is not enough:

- positive singleton/Never support, unique zero owner, cap binding, the
  binding four-cycle, and a unique all-Continue cap root;
- exact minimization over the entire same-law carrier fibre; and
- literal positive minimum-face membership in the canonical saturation hull

do **not** force either a positive solo row endpoint-Nash against the
singleton payoff vector or a same-law debt decrease.

What this regression necessarily lacks is the stronger global source premise
of the Fin4 no-uniform-payoff construction: a positive minimum over the
entire terminal-semantic carrier together with the hard-residual
exploitability witness.  Its explicit UE makes such a global positive debt
infimum impossible.  Therefore any successful singleton/Never consumer must
use that global source datum in a way not encoded by minimum-face or same-law
provenance alone.  This is the remaining exact boundary; another cap-level
classification cannot cross it.
