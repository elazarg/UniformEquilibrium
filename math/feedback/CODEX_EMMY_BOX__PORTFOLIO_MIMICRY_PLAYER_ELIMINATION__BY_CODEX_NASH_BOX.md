# Bounded independent check: portfolio mimicry is a capped-clock subcone

Reviewer: CODEX_NASH_BOX.

Scope: Proposition 1's pathwise comparison and Section 7's exact containment.
This is not a full fixture, degree, robustness, or export audit.

I read `CappedClockParentRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`
and the consumer
`quittingGame_exists_uniformEquilibriumPayoff_of_finFour_cappedClockCertificate`
in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockFinFourExistence.lean`.

Reindex the eliminated player as `none`, survivors as `some d`, and set the
certificate's `weight d = a_d`. With `s_i = r_i({i})`, the supplied conditions
give exactly the required three rows:

- (Q) at the empty coalition is `s_e <= sum_d a_d s_d`, the Never row.
- Subtracting (P) at nonempty A from that inequality gives
  `s_e-r_e(A) <= sum_d a_d (s_d-r_d(A))`, the future row.
- Subtracting (P) at nonempty A from (Q) at A gives
  `r_e(A+e)-r_e(A) <= sum_d a_d (r_d(A+d)-r_d(A))`, the join row.

Thus the original proposed certificate is a literal subcone, with no
slack, payoff shift, or strategy selection required. The existing Fin4
consumer already gives the claimed original-game existence conclusion.

The pathwise gain proof also survives the main possible falsifiers. If the
old first date precedes t, all donor changes are inert. Otherwise donor d's
separate experiment has first coalition A+d, even when d already belongs
to A. Joint Never is covered by (Q) at the empty coalition and zero baseline
payoffs. Each experiment changes only one donor's own stopping law; sharing
the probability space in the proof does not introduce correlation in play.
Pure-time extremality then covers complete behavioral deviations.

Verdict: the domination proof is valid ordinary mathematics on this bounded
check, and the no-new-coverage conclusion is correct. No independent review
of the rational fixture or its matrix inventory is claimed.
