# Strengthening and package audit: all-player escape social-surplus account

Reviewer: `NOTE_MINING_STRENGTHENER`

Source reviewed:
[`CHATGPT_EXTERNAL__ALL_PLAYER_ESCAPE_SOCIAL_SURPLUS_ACCOUNT.md`](../notes/CHATGPT_EXTERNAL__ALL_PLAYER_ESCAPE_SOCIAL_SURPLUS_ACCOUNT.md)

## Verdict

### Mathematics: PASS, and the theorem is stronger than stated

The escaped-mass sign, prescribed-payoff moment, unrestricted-cap
lower-semicontinuity, and debt-jump identity are correct.  They use neither
attainment of a best response nor continuity of the cap.  Positivity of the
global minimum is unnecessary.

The strongest clean unweighted consequence is:

> If every own singleton reward is nonnegative and every nonempty coalition
> has nonpositive social reward, then every point of the terminal-semantic
> carrier is weakly debt-dominated by an actual behavioral profile.
> Consequently the carrier minimum value is attained by an actual profile,
> whether that value is positive or zero.

At a minimum, all cap drops vanish coordinatewise and escaped mass can be
supported only on zero-social-reward coalitions.  If every coalition has
**strictly** negative social reward, the particular minimum carrier point is
itself realized, not merely its minimum value.

There is also a sharp sign-general cap estimate.  A negative singleton reward
can make the reconstructed cap jump upward, but by at most

```text
opponentsAllNeverProbability * (-singletonReward)_+.
```

The two-player test below attains this bound exactly.

### Current source packet: FAIL pending replacement-level repairs

The note abbreviates the compact-outcome proof, does not expose the
carrier-to-law-limit adapter, retains unnecessary `D_* > 0` wording, omits
the sharp negative-singleton test, and does not state the stronger equality
consequences.  It should not be copied verbatim to `exports/`.

### Corrected package: conditional PASS at the export gate

A replacement packet containing Sections 1--8 below is a complete structural
reduction of the named all-nonproper minimum seam.  Its actual-data adapter is
unconditional, and in the positive-minimum branch its actual minimizer enters
the checked actual-profile paid-cap trichotomy and is forced into the literal
inert-stall arm.  This is not a uniform-payoff theorem.

If the conference requires every export to close one of the currently listed
`questions/` rather than to narrow the checked all-nonproper seam, the packet
still fails gate 4 and should be formalized in `Research` only.  The strict
PASS condition is therefore: the final packet must name the all-nonproper
source theorem and the actual-minimum inert-stall transition as the precise
boundary it changes; it must not advertise minimum attainment as UE.

## 1. Exact escape account, with no minimum hypothesis

Let `I` be a finite nonempty player set.  For every nonempty coalition
`S`, let `r(S) in Real^I` be its terminal reward; all Never pays zero.

Let `sigma_n` be actual behavioral profiles with

```text
Sem(sigma_n) = (U^n,B^n) -> z=(u,b).
```

After a common subsequence, suppose the complete stopping law of each player
converges weakly on `N union {infinity}` to `mu_i`, and every coordinate of
the finite complete terminal-outcome law `m_n` converges to `mStar`.
Reconstruct the actual behavioral profile `barSigma` from the independent
laws `(mu_i)`, and let `m` be its terminal-outcome law.  For nonempty `S` put

```text
e(S) = mStar(S) - m(S).
```

Then:

```text
e(S) >= 0                                                     (1)

sum_(S nonempty) e(S)
  = m(Never) - mStar(Never)
  <= m(Never).                                                (2)

u_i - U_i(barSigma) = sum_S e(S) r_i(S).                     (3)
```

In particular a nonzero escape packet is possible only at the joint
all-Never boundary.  The numbers `e(S)` are subsequential relaxation-defect
coordinates.  They are not fixed-date atoms of `barSigma`.

For a player `i`, write

```text
q_i = product_(j != i) mu_j({infinity}),
s_i = r_i({i}),
kappa_i = q_i * (-s_i)_+.
```

Then the sharp sign-general cap estimate is

```text
B_i(barSigma) <= b_i + kappa_i.                               (4)
```

Consequently, with the signed cap drop

```text
Delta_i = b_i - B_i(barSigma),
```

one always has

```text
Delta_i >= -kappa_i.                                         (5)
```

If `s_i >= 0`, then `kappa_i=0`, so

```text
Delta_i >= 0.                                                (6)
```

Finally define the social reward

```text
R(S) = sum_i r_i(S).
```

The debt jump is the exact identity

```text
D(Sem(barSigma)) - D(z)
  = sum_S e(S) R(S) - sum_i Delta_i.                          (7)
```

Equations (1)--(5) require no global minimum and no positivity assumption on
any debt value.

### Weighted strengthening

The same proof works for nonnegative weights `w_i`.  Define

```text
D_w(u,b) = sum_i w_i (b_i-u_i),
R_w(S)   = sum_i w_i r_i(S).
```

Then

```text
D_w(Sem(barSigma))-D_w(z)
  = sum_S e(S)R_w(S)-sum_i w_i Delta_i.                       (8)
```

Only coordinates with `w_i>0` need the nonnegative-singleton hypothesis in
the sign consequences below.  The ordinary theorem is `w_i=1`.  This
weighted abstraction is mathematically free, but it need not delay the first
Lean implementation.

## 2. Proof of the escaped-mass sign

Fix nonempty `S` and a finite horizon `T`.  The event that the first terminal
coalition is `S` at a date at most `T` depends on finitely many stopping-law
point masses.  Those masses converge under weak convergence on the one-point
compactification, so

```text
Pr_barSigma(S occurs by T)
  = lim_n Pr_sigma_n(S occurs by T)
  <= liminf_n m_n(S)
  = mStar(S).
```

Letting `T` increase and using monotone convergence gives
`m(S)<=mStar(S)`.  Equivalently, the exact-`S` terminal event is open in the
finite product compactification and Portmanteau gives the same inequality.

Both `m` and `mStar` are probability laws on Never plus the finitely many
nonempty coalitions.  Summing the finite coordinates gives (2).  Since all
Never pays zero, taking the finite reward moment gives (3).

No independence is lost in the limit: a finite product of the limiting
marginal laws is again the stopping-clock law of the reconstructed behavioral
profile.

## 3. Cap proof without hidden cap continuity

For fixed finite `t`, let `V_i^n(t)` be the payoff when `i` deterministically
quits at `t` against `(sigma_n)_{-i}`, and define `barV_i(t)` against
`barSigma_{-i}`.  Fixed finite-time continuity gives

```text
V_i^n(t) -> barV_i(t).
```

Since `B_i(sigma_n)>=V_i^n(t)` and `B_i(sigma_n)->b_i`,

```text
sup_(t finite) barV_i(t) <= b_i.                              (9)
```

Exact pure-time extremality for arbitrary behavioral deviations gives

```text
B_i(barSigma) = sup_(t finite or Never) barV_i(t).            (10)
```

The late-finite/Never identity is

```text
lim_(t->infinity) barV_i(t)
  = barV_i(Never) + q_i s_i.                                 (11)
```

If some opponent is proper, `q_i=0`; if all opponents are nonproper, (11) is
the checked nonproper-opponent identity.  Thus (11) holds without assuming
that every limit clock is nonproper.

Let `A_i=sup_(t finite) barV_i(t)`.  Equation (11) gives

```text
barV_i(Never) <= A_i + q_i(-s_i)_+.
```

Combining this with (9)--(10) proves (4).  When `s_i>=0`, Never is weakly
approximated from above by finite quitting dates, so `B_i(barSigma)=A_i` and
the cap cannot jump upward.

This proof never asserts that the cap supremum is attained and never
interchanges a limit with a supremum as an equality.  It uses only the
one-sided inequality `sup_t lim_n <= liminf_n sup_t` for fixed finite times.

## 4. Minimum and strict-nonattainment consequences

Assume now that `z` minimizes `D` on the terminal-semantic carrier.  Since
`barSigma` is actual, its semantic pair belongs to the carrier, hence the
left side of (7) is nonnegative.  Under nonnegative own singletons,

```text
sum_S e(S)R(S) >= sum_i Delta_i >= 0.                         (12)
```

If **no actual behavioral profile attains the minimum debt value** `D(z)`,
put

```text
delta = D(Sem(barSigma))-D(z) > 0.
```

Then the exact strict account is

```text
sum_S e(S)R(S) = delta + sum_i Delta_i > sum_i Delta_i >= 0. (13)
```

Thus some coalition in the actual escaped support has positive social
reward.  Nonattainment of the particular semantic point `z` is not enough
for strictness: another actual point may attain the same minimum value.

There is a quantitative finite extraction.  If `n=card I`, all rewards have
absolute value at most `M`, and `M>0`, then among the at most `2^n-1`
nonempty coalitions there is an `S` with

```text
e(S)R(S) >= delta/(2^n-1),
e(S) >= delta / ((2^n-1)*n*M),
R(S)>0.                                                       (14)
```

Also, because `sum_S e(S)<=1`, some escaped-support coalition satisfies

```text
R(S) >= sum_S e(S)R(S) >= delta.                             (15)
```

The first inequality in (14) follows by discarding nonpositive terms before
finite pigeonhole.  These constants are the direct worst-case constants; no
event mass at one fixed date is claimed.

## 5. The sign chamber, equality structure, and strict chamber

Assume

```text
r_i({i}) >= 0                 for every i,
R(S) <= 0                     for every nonempty S.           (16)
```

For **any** carrier point `z`, the actual-data construction above gives

```text
D(Sem(barSigma)) <= D(z).                                    (17)
```

Thus an arbitrary carrier minimizer has an actual minimum-value
representative.  No hypothesis `D_*>0` is used.

At a minimum, equality must hold throughout.  Hence

```text
Delta_i=0                                        for every i,
e(S)>0 -> R(S)=0.                                            (18)
```

So all cap coordinates are preserved, and any remaining semantic mismatch is
carried solely by a zero-social-reward escaped packet.

If the aggregate signs are strict,

```text
R(S)<0 for every nonempty S,                                 (19)
```

then (18) forces `e=0`.  Equations (3) and (18) then give

```text
Sem(barSigma)=z.
```

Therefore every globally minimizing carrier point is itself behaviorally
attained under (19).  Under weak signs (16), only attainment of the minimum
value is automatic.

The weighted versions replace `R` by `R_w`; coordinatewise cap equality in
(18) requires positive weights.

## 6. Actual-data adapter

The theorem is not conditional on a supplied convergent law sequence.
For any `z` in `quittingTerminalSemanticCarrier reward`:

1. use `nonempty_terminalSemanticSelectedLawLimit_of_mem_carrier` to select
   an actual realizing sequence and a common weak limit of all compactified
   stopping laws;
2. pass to a further subsequence in the finite terminal-outcome simplex;
3. reconstruct `barSigma` with
   `quittingCompactStoppingLawProfile`; and
4. apply Sections 1--3.

Equivalently, first use `exists_terminalSemanticLawCarrier_lift`, realize the
joint semantic/law point, and compactify its marginal stopping laws.  The
latter route keeps the displayed `mStar` definitionally attached to the
joint carrier point.

Consequently (17) is an actual-data theorem for every finite reward table
satisfying (16), not a verifier for an externally supplied bubble.

## 7. Consumer and exact conjecture-facing scope

The direct consumer of (17) is carrier-minimum attainment.  In the zero
minimum branch, the existing
`exists_uniformEquilibriumPayoff_of_hasZeroMinimumTerminalSemanticDebt`
already gives a uniform-equilibrium payoff; this is not new.

In the positive-minimum/no-uniform-payoff branch, the output is an actual
profile on the minimum fibre.  A positive terminal gap supplies a
`QuittingActualProfileTerminalGapPaidCapPort`, and

```text
QuittingActualProfileTerminalGapPaidCapPort.inertStall_of_minimumFiber
```

in
`StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean` forces its port
into the literal inert-stall arm.  Thus the sign chamber gives the honest
transition

```text
all-nonproper nonattainment seam
  -> actual minimum profile
  -> exact-minimum inert paid-cap stall.
```

It does not consume that inert stall and does not prove UE when the minimum
is positive.  Outside the sign chamber, (13) outputs a strict
positive-social-surplus escape packet, for which no checked terminal consumer
is known.

## 8. Boundary tests

### Negative singleton: the cap penalty is sharp

Take two players `i,j`.  Give player `i` reward `-1` at every nonempty
terminal coalition; give player `j` arbitrary bounded rewards.  Let `i` play
Never and let `j` quit deterministically at date `n`.

Every response of `i` receives `-1`, so `B_i(sigma_n)=-1`.  The limiting
profile is all Never, against which Never gives `0`; hence

```text
B_i(barSigma)=0 > -1=lim B_i(sigma_n).
```

Here `q_i=1`, `s_i=-1`, and the upward cap jump equals
`q_i(-s_i)_+=1`.  Thus (4) is sharp and the nonnegative-singleton sign cannot
be deleted from (6).

### No global-minimum provenance

The source note's two-player table with `c` uniform on `0,...,n` and `a`
Never has nonnegative own singleton rewards, a nonattained semantic limit of
debt one, and both laws converging to Never.  All Never has debt zero.  This
shows that positive debt, nonattainment, and all-player escape do not imply
(12); global minimum provenance is essential.

### Positive social reward is not itself a consumer

The reviewed four-player positive-social-bubble regression has a unit escaped
pair bubble with social reward `2`, a literal paid row, and unique
all-Continue cap roots, yet the cap drop is `5` and the actual all-Never debt
is zero.  It realizes

```text
D(allNever)-D(bubblePoint)=2-5=-3.
```

Thus a positive escaped social moment does not by itself orient an exact cap
root, return, or debt descent.  Minimum provenance is exactly what reverses
the scalar inequality.

### Subsequence and chronology boundary

The escaped coordinates may depend on the selected terminal-law subsequence.
Positive `e(S)` gives eventual mass in the complete `S` outcome of the actual
approximants, but not a common finite date, Nash--Bellman edge, or prescribed
chronology.  Any later consumer must add that data rather than rename the
bubble as an atom of `barSigma`.

## 9. Source and novelty audit

Checked ingredients:

- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `Cycles/BehaviorPureTimeExtremality.lean`;
- `quittingTerminalPayoff_update_finiteTime_le_of_lawLimit`,
  `quittingTerminalPayoff_update_finiteTime_tendsto_never_add_singleton`,
  `nonempty_terminalSemanticSelectedLawLimit_of_mem_carrier`, and
  `exists_terminalSemanticSelectedLawLimit_with_all_nonproper` in
  `Terminal/OpponentTightTerminalSemanticRealization.lean`;
- `terminalSemanticLawCarrier_rewardMoment` and
  `exists_terminalSemanticLawCarrier_lift` in
  `Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`; and
- the minimum/UE equivalence in
  `Terminal/PositiveMinimumSemanticDebt.lean`.

The existing opponent-tight implementation proves full semantic continuity
when a suitable proper clock remains and reduces a nonattained minimum with
nonnegative singletons to an all-nonproper selected law limit.  It does not
contain the escaped finite-outcome inequalities, the cap penalty (4), the
debt account (7), the strict packet (13)--(15), or the actual-debt-dominator
and equality theorems (17)--(19).  Narrow searches found no duplicate in
`UniformEquilibrium/`, `Research/`, `formalized/`, or `exports/`.

## 10. Lean handoff

The implementation should prove primitive sequence theorems before packaging
an account structure.  Suggested shapes are:

```text
quittingTerminalOutcomeMass_limitProfile_le_jointLimit
  -- m(S) <= mStar(S) for nonempty S

sum_quittingTerminalEscapeMass_eq_neverMass_sub

quittingTerminalPayoff_target_sub_limitProfile_eq_escapeMoment

quittingContinuationBestResponseValue_limitProfile_le_target_add_negSingleton
  -- Bbar_i <= b_i + q_i*(-r_i({i}))_+

quittingTerminalSemanticDebtSum_limitProfile_sub_eq_escapeSocialMoment_sub_capDrop
```

Then expose the actual-data statements:

```text
exists_actualProfile_debtSum_le_of_mem_carrier_of_singleton_nonneg_of_social_nonpos

exists_actualProfile_attains_minimumDebt_of_singleton_nonneg_of_social_nonpos

exists_actualProfile_realizes_minimumPoint_of_singleton_nonneg_of_social_neg

exists_positiveSocialEscape_of_minimumValue_not_actual
```

For the quantitative strict theorem, use a finite positive-part sum rather
than divide by the escaped total mass.  Require `M>0` before the mass bound.

The first cap theorem can be assembled from the checked fixed-finite-time
upper bound and a general late-finite/Never lemma.  For the latter, split on
whether some opponent limiting law is proper: opponent tightness handles that
case, while the existing all-nonproper identity handles the complement.

Do not put `e(S)>=0`, the reward-moment identity, or the desired cap inequality
into assumptions of a structure.  Construct them from joint convergence.

## Final PASS/FAIL conditions

Mathematical content passes now.  A final packet passes only if it:

1. removes `D_*>0` from the master and attainment theorems;
2. proves the finite-outcome escape sign and total-mass identity explicitly;
3. reconstructs the actual limiting behavioral profile from weak marginal
   laws;
4. proves unrestricted cap control without cap attainment or assumed cap
   continuity;
5. distinguishes nonattainment of the minimum **value** from nonattainment of
   one carrier point;
6. includes the negative-singleton sharpness test and the no-minimum test;
7. states attainment of the value, and exact point attainment only under
   strict aggregate signs;
8. gives the unconditional carrier actual-data adapter; and
9. names the actual-minimum inert-stall transition while explicitly retaining
   its open consumer.

Absent item 9, the result is a strong Research theorem but fails the current
export consumer gate.  Even with item 9, it must be labelled a structural
reduction, never a proof of the quitting-game conjecture.
