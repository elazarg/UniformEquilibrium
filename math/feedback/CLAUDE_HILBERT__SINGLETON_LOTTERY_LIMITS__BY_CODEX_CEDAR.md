# Feedback on singleton-lottery limits

Reviewer: `CODEX_CEDAR`

Reviewed note: `notes/CLAUDE_HILBERT__SINGLETON_LOTTERY_LIMITS.md`

Status: `VALID_WITH_TWO_EXPLICIT_SCOPE_QUALIFICATIONS`

## Scope of this review

I independently checked the chronology-relevant claims requested by the
coordinator:

1. Proposition 6, the collapse of exact solo-periodic certificates with
   vanishing total per-period hazard to a singleton-mixture certificate;
2. the quantitative proportional-refusal lower bounds in Propositions 4 and
   5 for the FTV and Solan--Vieille tables; and
3. the relationship of those claims to player-deleted survival and to the
   checked behavioral pure-time extremality theorem.

I did not audit the broader architecture-completeness discussion or the open
nonproportional Solan--Vieille question.

Files refreshed before review:

- `notes/CLAUDE_HILBERT__SINGLETON_LOTTERY_LIMITS.md`;
- `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md` (Proposition 13);
- `UniformEquilibrium/Quitting/Cycles/SoloPeriodicBlockCompiler.lean`;
- `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`;
- `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`; and
- `Literature/FleschThuijsmanAndVrieze1997.lean`.

No Lean build was run.  All positive findings below are ordinary mathematics
or static checks of the named declarations.

## 1. Proposition 6 survives falsification

The claimed collapse is valid.  Let `H_n=sum_k h_(n,k)` be the total hazard in
one period and let `lambda_(n,k)` be the eventual singleton-exit owner law from
phase `k`.  Positive absorption somewhere in a repeated finite period makes
each `lambda_(n,k)` a probability distribution.  The exact renewal identity

`lambda_k = h_k delta_(w_k) + (1-h_k) lambda_(k+1)`

gives

`||lambda_k-lambda_(k+1)||_1 <= 2h_k`.

Following the directed cyclic arc between any two phases and telescoping gives
`||lambda_k-lambda_j||_1 <= 2H_n`.  Thus changing period lengths do not create
a chronology loophole: the bound uses the whole per-period budget, not the
maximum phase hazard.

Choose one base phase in each certificate and a convergent subsequence of its
exit laws, with limit `w*`.  If `w*_a>0`, then owner `a` occurs at a
positive-hazard phase eventually.  Its certificate anchor says

`s_a=(R lambda_(k+1))_a`,

and the total-variation bound gives `(Rw*)_a=s_a`.  For an arbitrary player
`j`, a phase owned by someone else has the join cap

`h r({owner,j})_j+(1-h)s_j
 <= h r({owner})_j+(1-h)(R lambda_(k+1))_j`.

Since `h<=H_n -> 0`, this yields `s_j<=(Rw*)_j`.  If no such spectator phase
exists, `j` owns every phase and its anchor gives equality instead.  Hence
`w*` is exactly an SMC.

One compactness sentence should be added to make the varying schedules fully
literal: because the player set is finite, first pass to a subsequence on
which the set of labels appearing in the period is fixed (or make the same
finite diagonal choice player by player).  Then the spectator/owner dichotomy
above is uniform.  This is a proof-detail repair, not a counterexample.

The consequent positive lower bound on total hazard for the two tables is
also logically valid: if the infimum were zero, a sequence with `H_n -> 0`
would contradict their already proved absence of an SMC.

## 2. FTV proportional-refusal bound

The exact algebra and minimization directions in Proposition 4 check.

- `P_i=mu_i+3mu_(i-1)` and proportional refusal gives
  `D_i=[3mu_(i-1)+(1-T)]/(1-mu_i)`.
- Clearing the denominator gives the stated residual
  `1-T-mu_i+mu_i^2+3mu_i mu_(i-1)`.
- Summing gives
  `3-4T+T^2+e_2 <= 3epsilon`.
- On a fixed simplex slice, `e_2=(T^2-sum_i mu_i^2)/2` is concave, so its
  minimum over the floor polytope is at a vertex.  In the range
  `3/4<u/T<=4/3`, zero-coordinate vertices are infeasible and the two-tight
  floor vertex has, up to cyclic permutation,
  `((4u'-3)/7,(9-5u')/7,(u'+1)/7)` and
  `e_2=(8u'-3u'^2-3)/7`.
- The resulting lower bound is decreasing in `T`, so using `T=1` has the
  claimed direction.  Substitution gives
  `23epsilon >= 2-2hbar-3(epsilon+hbar)^2`; the `hbar<=1/50`,
  `epsilon<=1/12` contradiction is numerically and exactly consistent.

The FTV reward rows used in the floor and refusal calculations match the
named simp declarations in `FleschThuijsmanAndVrieze1997.lean`.

## 3. Solan--Vieille proportional-refusal bound

Proposition 5 also checks.

- The table makes every relevant solo deviation and two-player collision pay
  the deviating quitter exactly `1`, so no small-hazard floor correction is
  needed.
- Summing the four refusal residuals gives
  `4-5T+a^2+b^2+6P_A+6P_B <= 4epsilon`.
- For fixed pair mass `a`, the floor interval yields
  `P_A >= (u-a)(4a-u)/9`.  When `a>u` the right side is negative and hence
  merely weak, but remains a valid lower bound; this does not reverse the
  later argument.
- Because the coefficient of `a^2+b^2` after substitution is negative, one
  correctly uses the *maximum* of that convex expression on
  `[2u/5,T-2u/5]`, attained at an endpoint.
- The resulting `G(T)` is decreasing, and `G(1)` gives exactly
  `74epsilon+28epsilon^2>=2`.  In fact the inequality forces a value strictly
  larger than `1/38`, so the stated exclusion of a `1/38`-Nash profile is safe.

The singleton and pair-row identities agree with `soloReward_eval`,
`soloReward_self`, and `boundaryReward_cappedJointExit` in
`SolanVieilleBoundaryTable.lean`.

## 4. Pure-time and deleted-survival qualification

The named theorem
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`
(`BehaviorPureTimeExtremality.lean`) really does identify the supremum over all
unilateral behavioral strategies with the supremum over deterministic finite
quit times plus `Never`.  Thus no strategy-class gap is hidden in using the
explicit floor and refusal deviations.  Indeed, the lower-bound contradiction
only needs those pure deviations; extremality supplies the exact converse
audit when describing the full best-response value.

The displayed late-quit formula needs one short limiting argument that is not
currently written.  A finite quit time can collide with that date's scheduled
owner, whereas the formula displays a solo residual payoff.  Under the
player-deleted clock, the unconditional collision atom at date `t` is at most
the passive first-exit atom `m'_t`.  Since `sum_t m'_t<=1`, `m'_t->0`.
Therefore the finite-time payoff converges to

`sum_(a!=i) mu'^(i)_a r({a})_i + (1-Q_i)s_i`,

and the formula is a legitimate lower bound on the pure-time supremum.  This
closes the apparent collision objection, but should be stated.

The proportionality identity is substantially stronger than the survival
data in the chronological-debt producer.  It identifies the complete
player-deleted exit law with one scalar renormalization of the original exit
law.  By contrast, the atom-access interfaces separately bound joint and
player-deleted survival at chosen deadlines and do not serialize the accessed
atoms into such a deleted-clock law.  Therefore Propositions 4--5 are exact
no-gos for the proportional architecture, not a chronological-shadowing
producer or a no-go for arbitrary source profiles.  This distinction is
correctly acknowledged in Hilbert's Section 7.

Finally, Noether's literal sequential renewal is only approximately
proportional: deleting a scheduled owner inflates later within-round masses.
Hilbert states that the lower bounds transfer with an `O(c)` loss, but does not
write the constants.  The transfer is plausible because Noether fixes
`kappa=min_i(1-w_i)>0` and bounds the mass distortion by `O(c/kappa)`, but the
exact quantitative claim about that construction should remain marked
unproved until the error is propagated through every refusal inequality.

## Verdict

The exact Propositions 4--6 are valid ordinary mathematics under their stated
proportional/certificate hypotheses.  I found no counterexample in the
boundary cases.  Two additions are needed for an export-quality proof:

1. write the vanishing collision-atom lemma behind the late-quit limit and the
   finite subsequence choice in Proposition 6; and
2. either quantify the `O(c)` transfer to Noether's ordered renewal or keep it
   explicitly outside the proved claims.

The chronology lesson is sound but negative: vanishing *total per-period*
hazard erases phase order and collapses to a static SMC, while player-deleted
proportionality is an additional global datum absent from the current
atom-access seam.
