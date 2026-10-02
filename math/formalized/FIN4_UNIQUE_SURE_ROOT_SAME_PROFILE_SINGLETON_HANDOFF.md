# A unique-sure exact root enters the same-profile singleton handoff

Authors: CODEX_NEGATIVE_CERTIFICATE

Independent reviews:
[CODEX_SPINOZA](../feedback/CODEX_NEGATIVE_CERTIFICATE__UNIQUE_SURE_RESET_SINGLETON_HANDOFF__BY_CODEX_SPINOZA.md)
and
[CODEX_HAHN](../feedback/CODEX_NEGATIVE_CERTIFICATE__UNIQUE_SURE_RESET_SINGLETON_HANDOFF__BY_CODEX_HAHN.md).

## Exact statement

Let \(I=\operatorname{Fin}4\), let \(r\) be a bounded quitting reward table,
and let \(\mathcal W\) be a terminal exploitability witness with

\[
 \Gamma=\mathcal W.\operatorname{terminalGap}>0.
\]

Let \(u\in\mathbb R^I\), and let \(q\) be an exact independent product Nash
root of the one-stage quitting game whose all-Continue payoff is \(u\).
Suppose that \(k\in I\) is the unique sure quitter:

\[
 q_k=1,\qquad q_i<1\quad(i\ne k).                              \tag{1}
\]

Write \(\widehat q\) for stationary repetition of \(q\), and define its
literal owner repair

\[
 \widehat q^{-k}
 =\widehat q[k\leftarrow\operatorname{Never}].
\]

Put \(F=I\setminus\{k\}\). There is a mixed point

\[
 z\in\operatorname{quittingPersistentBaseNashSet}
       (r,\{k\},F)                                             \tag{2}
\]

whose persistent-base root is exactly \(q\). The checked prescribed-owner
theorem therefore supplies one \(\delta_k>0\) and a
QuittingSingletonBaseStationaryHandoff at this same point \(z\), with all of
the following consequences.

1. The handoff source profile is exactly \(\widehat q\).
2. Every \(i\ne k\) has zero complete behavioral debt at \(\widehat q\), and

   \[
   d_k(\widehat q)\ge\delta_k.                                 \tag{3}
   \]

3. The owner repair is exactly
   \(\widehat q\to\widehat q^{-k}\). It attains \(k\)'s complete behavioral
   cap, gains at least \(\delta_k\), and leaves

   \[
   d_k(\widehat q^{-k})=0.                                    \tag{4}
   \]

4. There is a player \(j\ne k\) such that

   \[
   d_j(\widehat q^{-k})\ge\Gamma,                              \tag{5}
   \]

   and the exact repaired profile \(\widehat q^{-k}\) carries a literal
   QuittingPaidFirstDisagreementRow for \(j\) of gain \(\Gamma\).
5. For every \(M>0\) satisfying
   \(\lvert r_i(S)\rvert\le M\) for all \(i,S\), the same repaired profile
   carries the checked QuittingPaidEndpointAtom for \(j\), with its
   quantitative mass and reward fields.
6. At the repaired profile, either every prescribed payoff coordinate lies
   above its punishment value, or a displayed player \(i\ne k\) lies
   strictly below punishment.

In the first arm of item 6, \(\widehat q^{-k}\) is the literal initial source
of the checked infinite exact-prefix orbit. Every root on that orbit is exact,
every semantic successor is the literal prefix of its predecessor, and

\[
 \operatorname{Abs}(q_t)\longrightarrow0.                    \tag{6}
\]

For every fixed positive absorption threshold, the checked
charged-payoff-recurrence premise is false on this orbit.

When \(q\) is the limiting root from the vanishing-survival arm of
FIN4_FIRST_EXACT_ROOT_SURVIVAL_OR_UNIQUE_SURE_RESET, this construction uses
that exact \(q\) and the exact stationary profile \(\widehat q\). It does not
reselect a different induced Nash point.

## Conjecture-facing change

The vanishing-survival arm of the first-root theorem ended at an actual
stationary profile with one sure debtor and a literal Never cap. This packet
shows that this local object is already accepted by a checked Fin4 consumer:
its free marginals are the same singleton-base induced Nash point, its Never
edge is the checked owner repair, and its exact child carries a distinct
full-gap debtor, paid row, and paid endpoint atom.

Relative to
[FIN4_QUANTITATIVE_PAID_PORT_CONSUMER.md](../questions/FIN4_QUANTITATIVE_PAID_PORT_CONSUMER.md),
the unique-sure local response is no longer an unnamed reset residue. It
enters the same-profile singleton handoff and then either exposes a localized
punishment-floor failure or starts the checked floor-safe exact-prefix orbit.

The result does not solve the question. The stationary source
\(\widehat q\) was constructed by repeating a compact limiting root; it is
not a literal finite descendant of the original tropical source sequence.
In the floor-safe branch, the resulting exact orbit has vanishing absorption
and no fixed charged payoff recurrence. These are the remaining source-entry
and inert-orbit seams.

## Definitions and assumptions

An exact product root is an ordinary independent mixed-strategy Nash profile
of the finite one-stage Quit/Continue game. The arbitrary vector \(u\) is
used only on the all-Continue outcome. There is no private recommendation or
correlated signal.

The persistent-base induced game with base \(\{k\}\) lets each free player
in \(F\) choose Quit or Continue. Its terminal coalition is \(\{k\}\) union
the set of free quitters. Its Nash set is encoded by
quittingPersistentBaseNashSet.

For a behavioral profile \(\sigma\), complete debt is

\[
 d_i(\sigma)
 =\sup_{\beta_i}
    U_i(\sigma[i\leftarrow\beta_i])-U_i(\sigma),
\]

where \(\beta_i\) ranges over every unilateral behavioral strategy, including
randomized and arbitrarily late stopping and literal Never.

The QuittingSingletonBaseStationaryHandoff records the stationary source,
literal owner repair, zero free-source debts, positive owner debt and repair
gain, zero repaired-owner debt, a distinct full-gap repaired debtor, a paid
row, and the repaired-profile punishment-floor dispatch. The
QuittingPaidEndpointAtom refines the paid row with an exact endpoint and
terminal atom; it does not restrict deviations to bounded clocks.

## Source correspondence

The input unique-sure reset is the reviewed theorem
[CODEX_NEGATIVE_CERTIFICATE__FIRST_EXACT_ROOT_SURVIVAL_AND_UNIQUE_SURE_RESET.md](../notes/CODEX_NEGATIVE_CERTIFICATE__FIRST_EXACT_ROOT_SURVIVAL_AND_UNIQUE_SURE_RESET.md),
frozen SHA-256
e24671f378ca5cbb1395a5601f903112b86907e6c8f866dfbd12f9c2546873d5.

The theorem reviewed before standalone assembly is
[CODEX_NEGATIVE_CERTIFICATE__UNIQUE_SURE_RESET_SINGLETON_HANDOFF.md](../notes/CODEX_NEGATIVE_CERTIFICATE__UNIQUE_SURE_RESET_SINGLETON_HANDOFF.md),
frozen SHA-256
50a0dd1ba1da57fa9f88331bc0fb31ec96162429d1e5cf80b2e6ddb6266fe6eb.

The induced finite game is defined in
UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean.
The converse endpoint adapter
mem_quittingPersistentBaseNashSet_of_free_endpointNash is in
LargePersistentBaseDeletionAdapter.lean.

The same-point handoff is
QuittingTerminalExploitabilityWitness.exists_prescribedOwner_stationaryHandoff
in PrescribedOwnerStationaryHandoff.lean. Its source, update, cap, debt,
paid-row, and floor fields are in LargeBaseStationarySemanticHandoff.lean.

The endpoint atom is
QuittingSingletonBaseStationaryHandoff.paidEndpointAtom in
LargeBasePaidEndpointAtomDispatch.lean. The exact orbit and the two
no-uniform consequences in (6) are
QuittingSingletonBaseStationaryHandoff.repairedExactInfiniteOrbit,
QuittingTerminalExploitabilityWitness.repairedExactOrbit_absorption_tendsto_zero,
and
QuittingTerminalExploitabilityWitness.not_repairedExactOrbit_chargedPayoffRecurrence
in LargeBasePaidEndpointExactStack.lean.

The new ordinary mathematics is only the bridge from an arbitrary exact root
against an arbitrary continuation payoff, with one sure coordinate, to the
same point of the persistent singleton-base Nash set. A narrow search of the
collision/toggle subtree found no checked declaration already stating this
bridge.

## Proof

### The free marginals form the same induced Nash point

Encode the three marginals \(q_i\), \(i\in F\), as one point \(z\) of the
mixed binary polytope. The persistent-base extension fixes \(k\) to pure
Quit, retains exactly these free marginals, and has no outside player.
Equation (1) therefore gives

\[
 \operatorname{quittingPersistentBaseRoot}(\{k\},F,z)=q.      \tag{7}
\]

Fix \(i\in F\). Under either pure current-action deviation by \(i\), player
\(k\) still Quits surely. The current row therefore absorbs, so the
all-Continue payoff \(u_i\) is never used. The two endpoint payoffs against
the arbitrary tail \(u\) equal the two endpoint payoffs in the finite binary
game induced by persistent base \(\{k\}\).

Exact root Nash says both pure endpoint payoffs are at most the prescribed
root payoff. This holds for every free player. Since expected utility is
affine in each binary mixed action, these are exactly the mixed Nash
inequalities of the induced game. Hence (2) holds. Equivalently, after the
sure-player screening rewrites, these are the hypotheses of
mem_quittingPersistentBaseNashSet_of_free_endpointNash.

### The checked handoff applies at that exact point

Apply
QuittingTerminalExploitabilityWitness.exists_prescribedOwner_stationaryHandoff
to \(\mathcal W\) and the preselected owner \(k\). It returns
\(\delta_k>0\), uniform over all points of the singleton-base induced Nash
set, and a QuittingSingletonBaseStationaryHandoff at each such point. Apply
its universal clause to the particular \(z\) from (2).

By (7), the handoff source root is \(q\). Its stationary source profile is
therefore definitionally \(\widehat q\), not a new or reselected profile.
The source_free_semantics and source_owner_debt fields give zero debt for
every \(i\ne k\) and prove (3).

The checked identity
update_quittingSingletonBaseStationaryProfile_owner_alwaysContinue identifies
the repaired profile with the unilateral replacement of \(k\) by Always
Continue, which is literal Never in the quitting game. Thus the repaired
profile is exactly \(\widehat q^{-k}\).

The fields repaired_owner_payoff_eq_source_cap,
repaired_owner_cap_eq_payoff, and repaired_owner_gain show that the update
attains \(k\)'s old cap, gains at least \(\delta_k\), and has zero repaired
owner debt. This proves (4). The fields outsideDebtor_ne_owner, outside_debt,
and paid_row select \(j\ne k\), prove (5), and supply the full-gap paid row
at the exact repaired profile.

### Endpoint atom and floor dispatch

Choose \(M>0\) satisfying the stated reward bound. Apply
QuittingSingletonBaseStationaryHandoff.paidEndpointAtom to the same handoff.
It produces the endpoint atom for \(j\) at \(\widehat q^{-k}\), without
changing the source, observer, or opponent strategies. The stationary cap
used in its proof equals the complete behavioral best-response value by
pure-time extremality.

The handoff field floor_dispatch gives item 6. The repaired owner \(k\) is
already at least its punishment value, so a failure of the all-player floor
condition names a free player and is necessarily distinct from \(k\).

### The floor-safe exact orbit

In the floor-safe arm, apply
QuittingSingletonBaseStationaryHandoff.repairedExactInfiniteOrbit. Its initial
semantic pair is the literal semantic pair of \(\widehat q^{-k}\), and each
successor is obtained by prefixing the selected exact root against the
preceding prescribed payoff.

The witness theorem repairedExactOrbit_absorption_tendsto_zero gives (6).
For every positive threshold, the theorem
not_repairedExactOrbit_chargedPayoffRecurrence rules out the fixed-charge
payoff-recurrence premise. These statements concern the same actual exact
orbit; no compactly reselected source is substituted. This completes the
proof.

## Boundary tests

### Arbitrary continuation payoff is genuinely harmless only for free players

The sure action of \(k\) screens every free-player current deviation from
\(u\), which is why (2) follows. The owner inequality is not used in this
bridge. Without a sure persistent player, the all-Continue payoff enters the
free endpoint comparisons and the induced-game conclusion can fail.

### Unique sure is inherited, not required by the checked consumer

The singleton handoff accepts induced Nash points on boundary faces where a
free coordinate may also be pure Quit. Uniqueness is supplied by the
first-root survival theorem and gives positive opponent Continue mass there;
it is not silently added as a hypothesis of the prescribed-owner theorem.

### Reactivation is the repaired paid child, not a contradiction

The exact matching-pennies regression in the first-root packet has a unique
sure owner whose Never deletion makes an outsider strictly prefer Quit0.
That behavior is consistent with (5): the checked handoff is designed to
select a full-gap outside debtor after the owner repair. The example
falsifies renewal of the unique-sure form, not the same-profile handoff.

### Floor failure is not silently repaired

The exact-orbit construction requires the all-player punishment floor. In
the other dispatch arm this theorem stops at the named under-punishment free
coordinate. It does not claim that repairing that player preserves the paid
row, the endpoint atom, or another sure-owner source.

### Vanishing absorption is not approximate equilibrium

Equation (6) holds under a terminal exploitability witness. Every profile on
the exact orbit remains subject to the fixed terminal gap. Root absorption
tending to zero is an inert boundary, not an unrestricted terminal
equilibrium certificate.

### Compact source entry is not chronology

When this theorem consumes the root from the first-root packet, the finite
literal profiles are \(\rho_n=q_n::\tau_n\). The stationary
\(\widehat q\) is obtained by repeating their limiting root. It is an actual
profile, but in general it equals neither \(\rho_n\) nor \(\tau_n\), and no
literal update edge from those finite profiles to \(\widehat q\) is claimed.

## Adapter and consumer

The actual-data adapter is the vanishing-survival arm of
FIN4_FIRST_EXACT_ROOT_SURVIVAL_OR_UNIQUE_SURE_RESET. It supplies the exact
limiting root \(q\), unique sure owner \(k\), actual stationary repetition
\(\widehat q\), and terminal witness.

The bridge (2) passes those exact marginals to the checked prescribed-owner
consumer. The owner repair, outside debt, paid row, endpoint atom, and floor
dispatch are co-realized at the same source and its literal Never child.
There is no independent Nash-point selection.

The output is a strict narrowing, not a terminal conclusion. It either
localizes a punishment-floor failure at the repaired child or enters the
literal floor-safe exact-prefix orbit. The first branch lacks a
packet-preserving floor repair. The second has vanishing absorption and lacks
a charged return. In addition, the stationary source remains separated from
the finite tropical prefix sequence by the source-entry seam.

## Lean handoff

The only new core declaration should be a root-restriction adapter of the
form

\[
\begin{split}
 &q_k=\operatorname{pureQuit},\quad
 \operatorname{IsZeroQuittingRootNash}(r,u,q)\\
 &\Longrightarrow
 \operatorname{restrictToFree}(q)
 \in\operatorname{quittingPersistentBaseNashSet}
       (r,\{k\},I\setminus\{k\}).
\end{split}
\]

Prove it by screening the arbitrary tail from every free endpoint, then apply
mem_quittingPersistentBaseNashSet_of_free_endpointNash. A second extensional
lemma should identify stationary repetition of \(q\) with
quittingSingletonBaseStationaryProfile at the encoded point.

All later conclusions are compositions of named checked declarations. The
formal statement must retain the difference between the finite profiles
which produced the root limit and the stationary profile constructed from
that limit.

## Scope and nonclaims

- This is reviewed ordinary mathematics, not yet a Lean theorem.
- The same-profile handoff begins at the stationary repetition of the exact
  root; it does not create a finite descendant of the tropical sources.
- The owner Never edge is literal and cap-attaining. No later return to a
  singleton-base source is proved.
- The outside debt, paid row, and endpoint atom are co-realized at the
  repaired child, but they do not imply floor safety.
- In the floor-safe arm, the exact-prefix orbit is chronological. Its
  absorption tends to zero, and every fixed charged-payoff recurrence is
  excluded under the witness.
- No source-entry interpolation, summable seam, renewable rank, terminal
  approximate Nash profile, or uniform-equilibrium payoff is proved.
