# Independent review of the sharp finite-deadline ceiling attempt

Reviewer: CODEX_HILBERT. Status: the mathematical claims in Sections 1–5
pass this bounded independent review as ordinary mathematics, not as
Lean-checked results. The exact per-deadline ceiling is stronger than the
inspected checked scalar envelope. No new conjecture-closing mechanism was
found beyond the already known exact-deadline architecture barrier.

Reviewed in full:

- `gpt/ATTEMPT_SHARP_FINITE_DEADLINE_CEILING.md`;
- `gpt/ATTEMPT_RESPONSE.md`;
- `gpt/ATTEMPT_check_deadline_ceiling.py`.

The copied Euler attempt is not independently re-audited here. The current
formalized record and named production declarations, rather than that
older copy, determine the comparison baseline. No claim of literature-wide
novelty is made; the external APS reference is not an input to any proof
reviewed below.

## 1. Exact claim and quantifier boundary

For a bounded finite quitting table, infinite all-Continue pays zero. The
finite timing menu is {0,…,K−1,Never}, with independent private mixed
stopping laws. Every unilateral behavioral deviation is evaluated in the
full terminal game, not just in that menu. The claim is

    ∀ finite-menu exact Nash p, E(p) ≤ M C_K,

where C_K is the maximum over 0≤x≤1 of

    g_K(x) = [1/x + (1/2) Σ_{m<K} ((1+x)/2)^m]⁻¹

for x>0, with g_K(0)=0. On normalized Fin4 tables, both the worst-selector
and best-selector worst-table values equal C_K. The attaining table may
depend on K through a maximizing x. Separately, one fixed rational table
at x=1/2 obstructs every deadline with every exact Nash selector, but has
unrestricted exploitability infimum zero.

These are terminal and architecture statements. They do not assert that
the K-stage average-payoff game has the same Nash set, or that every actual
behavioral profile has positive debt.

## 2. Upper bound: the weighted recurrence is valid

Fix a positive-debt player. Let a be opponent Never mass and h_t the law of
the earliest finite opponent exit. Finite Nash gives U as the maximum of the
permitted pure-date payoffs. Pure-time extremality gives B=max(U,L), where
L is the common payoff of every omitted finite date. Thus d=L−U>0 and
d≤as. This forces s>0 and hence M>0, so x=s/M lies in (0,1].

For date t, the comparison has four disjoint events:

- opponents exit before t: the two outcomes coincide;
- opponents exit at t: the payoff difference is at most 2M;
- opponents exit after t but finitely: the difference is at most M−s;
- opponents all Never: both pure finite choices yield s.

Consequently d/M≤2h_t+(1−x)Σ_{u>t}h_u. Writing H_t=Σ_{u≥t}h_u gives
H_t≥d/(2M)+((1+x)/2)H_{t+1}, with H_K=0. Its geometric backward iteration,
combined with a≥d/(Mx), gives exactly g_K. No inequality direction is
reversed and no profile or deviation cap attainment outside the finite menu
is assumed. The all-Continue one-player edge case simply has zero h_t and
cannot have positive debt at finite Nash.

The derivative test is correct: its sign is the sign of
1−(x²/4)Σ_{m=1}^{K−1}m((1+x)/2)^{m−1}. This is strictly positive for
K≤3. For K≥4 the subtracted expression is strictly increasing from zero
past one, giving the claimed unique interior maximum. The geometric-series
formula and the x=1 removable endpoint are correct. The monotone compact
convergence argument establishes C_K→1/4 without exchanging an unverified
pointwise limit with a maximum.

I did not continue constant optimization or derive additional hierarchy
cutoffs from this improvement.

## 3. Sharpness and unrestricted caps

The table specifies all nonempty coalitions, including dummy-only ones.
With dummies Never, player 2 receives zero exactly on a matching active
stopping time, including both Never, and −1 otherwise. Player 1's uniform
law therefore makes every permitted response of player 2 indifferent.

For player 1, the table simultaneously saturates both reward bounds in the
datewise inequality: collision changes reward from −1 to 1, and later
opponent exit changes singleton reward x to 1. The geometric opponent law
has a=δ/x and h_t=(δ/2)ρ^(K−1−t), where δ=g_K(x). It normalizes exactly
and satisfies

    2h_t+(1−x)Σ_{u>t}h_u=δ=xa.

Hence all allowed finite dates and Never have the same value, and every
omitted finite date gains δ. Player 2 cannot improve at an omitted date:
it then never matches player 1 and receives −1, below −K/(K+1).
Dummies receive zero and can never gain. Thus the full debt vector is
(δ,0,0,0), not merely a lower bound from one omitted deviation.

Pure-time extremality covers every independent behavioral deviation. No
common random seed, correlation device, or observation of opponents'
sampled stopping times is introduced.

## 4. Uniqueness survives the off-path-dummy stress test

The proof correctly establishes positive survival before appealing to
conditional tail Nash; this is the important distinction from an invalid
rootwise-only uniqueness argument.

At a reached date, a dummy that quits with positive probability receives a
strictly negative contribution on that event and never a positive payoff.
Never yields zero. Thus no dummy quits at a reached date, even if the active
players absorb there surely.

If player 1 quits surely, player 2 uniquely prefers joining. Both surely
quitting makes player 1 prefer Continue, so player 1's hazard is below one.
If player 2 quits surely, player 1 continues and player 2 gets −1. Consider
player 2's complete deviation to Never against the remaining literal laws.
If player 1 fails to belong to the first finite coalition with positive
probability, that deviation produces zero there and improves. Otherwise
player 1 belongs to a first finite coalition almost surely. One permitted
finite date t has a positive probability of this event. Quitting at t then
gives zero on that positive-probability collision and never less than −1
elsewhere, again improving. Arbitrary off-path dummy exits are retained in
this dichotomy; they are not discarded.

All players therefore Continue with positive probability at the root. The
conditional independent suffix is exact finite timing Nash: any profitable
conditional complete strategy can be spliced after the reached all-Continue
history, producing positive ex ante gain. Backward induction is legitimate.

Given tail values u_n<x and v_n>−1, the root differences have strict
thresholds

    q=(x−u_n)/(2+x−u_n),  p=(1+v_n)/(2+v_n).

Both lie strictly between zero and one. Boundary roots are excluded by the
strict opposite-player response signs, so this is the only mixed root.
The payoff recursions and their displayed closed forms satisfy the initial
condition and these strict inequalities. The resulting laws agree with
Section 3. Every finite survival history is reached, forcing every dummy
finite atom to zero. Thus uniqueness holds for complete finite timing laws,
not only for one backward-induction construction or its payoff.

The known old fixed-prefix counterexample cannot be transplanted to this
table. In the pure profile (Never,0,1,Never), player 2 receives −1, but
switching to Never leaves a dummy-only coalition and gives player 2 zero.
The gain is exactly 1. This explicitly distinguishes the new table's
dummy-only reward from the different table in
`FixedPrefixTimingNashNonuniqueness.lean`.

## 5. Uniform payoff elsewhere on the same table

In the comparison family player 2 quits at date zero, player 1 chooses
uniformly from {1,…,L}, and dummies Never. The prescribed payoff is exactly
(1,−1,0,0). Players 1, 3, and 4 already obtain their maximal rewards.
Player 2 obtains zero only by matching one atom of player 1 and obtains −1
otherwise; its best gain is 1/L. Every pure date and Never is accounted for.

Under an arbitrary player-2 deviation, player 1 still forces absorption by
date L. Thus replacing terminal reward by the H-stage average changes
player 2's payoff by at most L/H under the note's stated convention. The
other players cannot improve beyond their prescribed maximal payoff.
Choosing L first and H thereafter proves a fixed uniform-equilibrium payoff.
The possible one-period convention shift is explicitly allowed in the note.

This proof is independent of exact-deadline Nash selection and does not use
the global conjecture. It defeats, on the attaining table itself, the false
inference from a positive exact-deadline barrier to positive global debt.

## 6. Source comparison and actual novelty

The current formalized record is
`formalized/FINITE_DEADLINE_NASH_QUARTER_CEILING_AND_FIXED_PREFIX_BARRIER.md`.
I inspected the following named source declarations and their relevant
definitions/proofs, using the same concrete route rather than a full tree
survey:

- `QuittingFiniteDeadlineNashProfile.debt_le_date_charge`,
  `QuittingFiniteDeadlineNashProfile.debt_div_le_factor_at_solo_ratio`, and
  `finiteDeadlineNashDebtFactor` in
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingNashDebt.lean`.
  The first already supplies the datewise inequality; the scalar envelope
  subsequently sums away its timing geometry. The new argument retains
  that geometry as a recurrence and obtains a genuinely stronger ceiling.
- `timingNash_unique_and_payoff`,
  `existsUnique_finiteDeadlineTimingNash`,
  `finiteDeadlineTimingNash_exploitability_eq_hardDeadlineDebt`, and
  `quarter_lt_finiteDeadlineTimingNash_exploitability` in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashUniqueness.lean`.
  These already cover every exact selector for the distinct old hard table.
- `tendsto_finiteDeadlineTimingNashWorstExploitability_succ_quarter` in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashWorstCase.lean`.
  This already identifies the asymptotic worst-table/worst-selector value.
- The reward definition, `hardDeadlineDebt_gt_quarter`,
  `comparisonProfile_exploitability`, and
  `comparisonTarget_isUniformEquilibriumPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashBarrier.lean`.
  These already establish the qualitative same-table separation between bad
  unique exact deadline Nash and a successful off-path-punishment family.
- `nonUniqueNashProfile_isNash` and
  `prefixTimingGame_not_existsUniqueNash` in
  `UniformEquilibrium/Diagnostics/Quitting/FixedPrefixTimingNashNonuniqueness.lean`.
  This is the authoritative correction for the different fixed-prefix table,
  not a refutation of the new parametric table's uniqueness argument.

The exact formula for C_K, the matching parametric table, and equality of
the finite-K best-selector and worst-selector minimax values are new
relative to these inspected results. The qualitative impossibility of
escaping the quarter barrier by choosing a better exact deadline selector
is not new: the old checked hard table already has unique Nash for every K.
Neither the new geometric equality nor its uniqueness proof supplies a
structural operation reducing unrestricted debt outside this method. This
is useful sharp architecture information, not a new closure route.

## 7. Computational evidence and small presentation issue

I reran the supplied standard-library exact-arithmetic script. It passed
72 deadline profiles and 72 punishment profiles, including the displayed
unrestricted pure-time caps, geometric equalities, and finite-horizon
checks. The script correctly disclaims a proof of uniqueness or general
equilibrium existence; those require the mathematical arguments above.

From the repository's math directory the actual command is

    python gpt/ATTEMPT_check_deadline_ceiling.py

The imported note's unprefixed `python check_deadline_ceiling.py` command
does not match the local filename. Its response also retains attachment
links from the originating environment; neither issue affects the proof.

No Lean file was created, changed, or built; no export or formalization
request was made. The bounded review is complete. There is no mathematical
objection left open here, and no reason from this result alone to continue
optimizing constants in place of the separate robust-reach source work.
