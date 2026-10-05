# Independent review: zero-singleton child selection

Reviewer: CODEX_MORSE.

Claim checked: the section **Zero-singleton child selection** in
`notes/CODEX_KREIN__INDEPENDENT_STOPPING_LAW_SELECTION.md`, including the
five-kind withdrawal consequence, finite laws, and fixed parent target.
This is a mathematical and source-scope review. No Lean compilation was run.

Verdict: the proof is correct at its stated existence/selected-family scope.
There is no unresolved mathematical objection. Its genuine implementation
increment is a selected ORIGINAL-child family with joint-Never probability
tending to zero when a child own singleton is merely nonnegative, followed
by the original-table quiet-lift consumer. The bare UE-existence extension
is also an elementary closure corollary of implemented strict-positive
consumers; the exact reduction below prevents overstating its novelty.

## Source and strategic-scope audit

I inspected the following actual declarations and their definitions:

- `QuittingThreePlayerStrategyClass.of_card_le_three` in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazardAllSigns.lean`,
  and `StationaryOrSmallHazardTerminalEquilibrium` in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazard.lean`.
  The source applies to every signed reward table on at most three players
  at every strictly positive terminal accuracy. Both output arms contain
  actual profiles and unrestricted behavioral terminal Nash inequalities.
- `WithdrawalFutureJoinRewardCertificate`, `neverExcess`, and `debtWeight`
  in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`.
  The five kinds have precisely the sum/maximum coefficients stated in the
  note, and the certificate has no supplied strategic witness.
- `withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
  This retains the original child debt plus the original residual times
  actual joint-Never mass. The different kinds can be chosen independently
  for different outsiders.
- `quittingGame_exists_uniformPayoffWitnesses_of_finFour_withdrawalFutureJoinFamily`
  and `quittingGame_exists_uniformEquilibriumPayoff_of_finFour_withdrawalFutureJoinFamily`
  in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`.
  Both retain a STRICTLY positive child singleton hypothesis. The stronger
  supplied-target theorem in that file retains the same strict hypothesis.
- `quietLift_fixedTarget_of_withdrawalFutureJoin_absorbingStationary` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalAbsorbingStationaryChild.lean`.
  This accepts a supplied absorbing exact stationary child. It does not
  produce the child's absorption from a zero singleton, so it does not
  subsume the new selected family.
- `quittingTerminalExploitability_censored_le` in
  `UniformEquilibrium/Quitting/Paths/LateFiniteStoppingLawCensor.lean`, and
  `quittingGame_uniformPayoffWitnesses_of_terminalNash_tendsto` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
  These supply, respectively, the all-deviation finite-law conversion and
  the SAME-family uniform-horizon witnesses after selecting a fixed limit.
- `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables` in
  `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.
  This is the existing reward-closure theorem used in the overlap comparison
  below, not an additional unproved continuity assertion.

There is no unproduced child profile, favorable child target, tail law,
absorption assumption, or compatible pivot optimizer in the proof. The
existence source internally selects each perturbed child profile. Other
outsiders being Never means that each individual outsider test is exactly
the child-plus-that-outsider game. A child unilateral deviation cannot make
the other outsiders quit. This justifies simultaneous quiet lifting.

The proof actually works for ANY finite parent player set with a retained
child of cardinality between one and three and any finite number of quiet
outsiders satisfying the displayed inequalities. Fin4 is the relevant
specialization, not a necessary dimension bound in the perturbation or
quiet-lift calculation. No claim is made for an arbitrary larger child.

## The potentially delicate steps are valid

Let Q be the product of child Never masses. If player j has own singleton
v>0, move only that player's Never mass to a finite date T, keeping every
original finite atom. On the branch where the replaced mass is selected,
finite opponent absorption before T has unchanged payoff. The probability
of any finite opponent stopping at or after T tends to zero. On joint
Never, the replacement changes zero to v. Thus the expected gain converges
to vQ. Every finite replacement is legal and bounded by that player's
unrestricted debt, proving d_j>=vQ. No maximizing date is assumed.

After adding delta only to j's own singleton, choose perturbed-child
exploitability at most delta^2. The source has v=s_j+delta>=delta, so
Q<=delta. Restoring the original reward table changes ANY payoff in
coordinate j by a quantity in [0,delta]. Therefore the difference between
two such changes is at most delta, and original exploitability is at most
delta^2+delta. The coefficient delta here is correct; a factor two is not
needed for this one-sided perturbation.

For the elementary F/J system, the pathwise comparison covers all cases:
child absorption before the test date, at that date, later at a finite date,
and joint Never. The child comparison is the private pushforward
T_i |-> min(T_i,t). On the Never event the missing scalar inequality is
exactly the residual rho, hence the outsider bound is

    d_k <= sum_i lambda_ki d_i + rho_k Q.

This argument neither correlates the actual strategies nor interchanges
expectation with a strategy supremum: it proves a bound for every fixed
outsider date first, then takes the supremum, including Never. The five-kind
extension reuses the corresponding existing original-table debt theorem;
no perturbed certificate or perturbed security floor enters that proof.

Censoring late finite atoms to Never changes prescribed payoff by at most
2M*tau. A fixed deviator's payoff depends only on the opponents' laws, so
its change is bounded uniformly by the same 2M*tau. Taking the supremum
therefore gives the stated 4M*tau full-regret bill. The finite censoring
need not preserve the exact Q<=delta estimate because the parent error
bound is already controlled directly after censoring.

Choose a sequence delta tending to zero and censoring errors tending to
zero. Compactness extracts one limit of the ORIGINAL parent payoff vectors.
The family-level terminal-to-uniform theorem then selects members of these
same finite quiet laws for all sufficiently long horizons. This supplies
one fixed parent target before the requested accuracy. It does not fix an
arbitrary child target supplied in advance.

## Implementation overlap: all five existence classes are closure classes

This is a material scope comparison, not an objection to the proof.

For the advance-only F/J rows, increasing s_j=r_j({j}) by delta changes
no join difference. The future difference s_j-r_j(A) increases by delta
when A!={j} and remains zero when A={j}. Thus the SAME finite F/J weights
still certify the perturbed parent table. It now has a positive child
singleton. The already implemented strict-positive existence consumer and
the already implemented reward-closure theorem immediately imply existence
for the original nonnegative-singleton table.

The same conclusion holds for all five kinds with an explicit parent
perturbation. Let mu_kj be outsider k's withdrawal weight on child j. Set

    r^delta_j({j}) = r_j({j}) + delta,
    r^delta_k({j}) = r_k({j}) + mu_kj*delta   (each outsider k),

and leave every other coordinate of every coalition unchanged. The child
restriction is exactly the child's own-singleton perturbation in the note.

I checked the relevant raw definitions in
`PatientWithdrawalRaw.lean`, `DeadlineWithdrawalRaw.lean`,
`DeadlineWithdrawalSecurityLP.lean`,
`DeadlineWithdrawalRestartPointwiseCore.lean`, and
`DeadlineWithdrawalSecurityMixedPointwise.lean`, all under
`UniformEquilibrium/Quitting/Classification/QuietExtension/`.

For recipient j, the patient floor is nondecreasing because its sole
changed entry is max(s_j,0); the passive entries are unchanged. The zero
floor is unchanged. In the security LP, only the singleton upper bound
increases, so every previously feasible hazard/value remains feasible;
the security optimum and both its zero truncation and zero-floor maximum
are nondecreasing. Every other recipient's floor is unchanged. Consequently
each kind's withdrawal gain is unchanged except at A={j}, where it decreases
by at most delta.

For a future or join row with A={j}, outsider k's left side decreases by
mu_kj*delta. The right side decreases by at most this amount. For the other
future rows the advance term improves and withdrawal terms are unchanged;
all other join rows are unchanged. The SAME weights and kinds therefore
certify r^delta. The omitted Never row imposes no further obligation.
Moreover r^delta converges uniformly to r, since the finitely many original
weights are fixed. Applying the old strict-positive producer at r^delta
and the old reward-closure theorem proves the bare existence conclusion.

Thus the proposed result is not a new mechanism beyond closure of the
implemented F/J classes. I found no declaration in the inspected source
family that already states the nonnegative-singleton selected-family
conclusion. A short export can legitimately fill that exact implementation
gap, with the useful output E_child->0 AND Q->0 in the ORIGINAL child,
and with finite quiet witnesses retained through target selection. It
should be described as a selected-family/closed-boundary corollary, not as
an independent breakthrough on the surviving arbitrary-table Fin4 case.

## Exact attempted falsifiers and the fixed-target boundary

The author's negative-sign example is correct. More generally, with one
child receiving -a on every terminal coalition and an outsider receiving
b on every terminal coalition, where a,b>0, zero weights satisfy F/J. If
the child's total finite stopping mass is p, quiet debts are ap and
b(1-p), whose maximum is at least ab/(a+b). The unrestricted parent has
an equilibrium with the outsider quitting, so this is exactly a failure
of the requested quiet source, not a negative game.

The distinction from preservation of an arbitrary child target is also
substantive. Here is an explicit boundary test. Use two retained children
1,2 with rewards

    r_child({1})=(0,1),
    r_child({2})=(1,0),
    r_child({1,2})=(0,0).

Their all-Never profile is an exact child equilibrium with target (0,0).
Give an outsider payoff 1 at EVERY nonempty parent coalition; give the
children arbitrary payoffs, for example zero, on coalitions containing
that outsider. Zero weights satisfy F/J and both child own singletons
are zero.

No family of quiet parent approximate equilibria can preserve child target
(0,0). Indeed, write f_i for child i's finite stopping probability, and
u_i for its quiet payoff. Never gives child 1 payoff f_2 and child 2 payoff
f_1, so their debt inequalities give f_2<=u_1+epsilon and
f_1<=u_2+epsilon. If u_1,u_2 and epsilon tend to zero, both f_i tend to
zero. Then Q=(1-f_1)(1-f_2) tends to one, while the outsider's debt is
exactly Q. This contradicts parent exploitability tending to zero.

There are nevertheless exact quiet equilibria for the same table: one
child quits immediately and the other Never, yielding selected child target
(0,1) or (1,0), with outsider payoff one. This verifies both the positive
claim and why its target must be selected rather than prescribed. A fourth
dummy quiet outsider with zero reward pads the example to Fin4 without
altering any calculation.

## Review conclusion

The selected-law theorem and its same-original-table five-kind consequence
are sound; all strategic inputs are produced. Finite-support witnesses and
one fixed target are justified. The sign threshold is sharp for this quiet
architecture. The missing scope is precisely nonnegative-singleton child
selection in the current production family, and not the general Fin4
existence conjecture. The mathematical overlap with strict-positive reward
closure should be stated in any handoff so the small implementation increment
is not presented as a newly discovered hard existence mechanism.
