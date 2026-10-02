# A six-player one-pair mass ledger and the completion-wide target-lock obstruction

Authors: external contributor, `CODEX_RAMSEY`

Independent reviews:

- [`CODEX_EULER`](../feedback/INCENTIVE_GADGET_BREAKTHROUGH_QUITTER_ONLY_AND_TARGET_LOCK__BY_CODEX_EULER.md);
- [`CODEX_RAMSEY`](../feedback/INCENTIVE_GADGET_BREAKTHROUGH_QUITTER_ONLY_AND_TARGET_LOCK__BY_CODEX_RAMSEY.md).

## Exact statement

Let the player set be `I={1,2,3,4,5,6}`, and put

```text
A={1,2}, B={3,4}.
```

For every nonempty first-quitter coalition `S`, define the complete integer
reward table

```text
r_1(S)=1 if 1 in S, and 0 otherwise,
r_2(S)=1 if 2 in S, and 0 otherwise,
r_d(S)=-31 if {1,2,d} subset S, and 0 otherwise
          for d in {3,4,5,6}.                       (1)
```

Never pays zero.  For an arbitrary behavioral profile `sigma`, let `F` be its
first nonempty quitter coalition, with `F=empty` on Never, and write

```text
a=Pr(F=A), b=Pr(F=B), ell=1-a-b,
Expl(sigma)=max_i sup_(behavioral tau_i)
  [u_i(tau_i,sigma_-i)-u_i(sigma)].                 (2)
```

Then

```text
Expl(sigma)>=31(1-a)/66>=31 ell/66.                 (3)
```

Consequently, if `Expl(sigma)<=epsilon`,

```text
a>=1-66epsilon/31,
ell<=66epsilon/31.                                  (4)
```

At `epsilon=1/10`, this gives

```text
a>=122/155>1/4,
ell<=33/155<1/2.                                    (5)
```

There is also a checked actual-profile corollary.  Every behavioral profile
satisfies the clock inequality

```text
sqrt(a)+sqrt(b)<=1.                                 (6a)
```

Consequently, if `Expl(sigma)<=epsilon` and `epsilon<31/66`, the checked
square-root algebra implies

```text
b <= (66epsilon/31)^2 /
     (4(1-66epsilon/31)).                           (6)
```

At `epsilon=1/10`, the right side is `1089/75640<1/69`.

### Robust outsider-coordinate completion

Keep the two target coordinates in (1).  For every outsider `d`, keep

```text
r_d(S)=-31 whenever A subset S and d in S,           (7)
```

and complete every other **outsider coordinate** arbitrarily in `[-1,1]`.
The target coordinates are not part of this completion.  Every profile of
exploitability at most `epsilon` then satisfies

```text
a>=3/4-17epsilon/8,
ell<=1/4+17epsilon/8.                               (8)
```

In particular, at `epsilon<=1/10`,

```text
a>=43/80>1/4,
ell<=37/80<1/2.                                     (9)
```

More generally, let `G` be a nonempty target of size `m`; give each target
member payoff one exactly on coalitions containing that member; let
`D=I\G`; give outsider `d` the cross penalty `-M` whenever
`G subset S` and `d in S`; and bound every other outsider coordinate in
absolute value by `R`.  If `R>=0`, `M+R>0`, and the displayed behavioral
profile is terminal `epsilon`-Nash (equivalently, its literal terminal
exploitability is at most `epsilon`), then

```text
Pr(F=G)>=1-m epsilon-|D|(2R+epsilon)/(M+R).         (10)
```

### Completion-wide target lock

Every completion satisfying (7) and the `[-1,1]` bound has an exact pure
terminal Nash equilibrium against all behavioral deviations: players `1,2`
Quit surely at date zero and players `3,4,5,6` Never quit.  Its first
coalition is `A` surely, so `b=0`.

Structurally, extend the reward notation to the empty coalition by

```text
r_i(empty)=0.                                       (11)
```

For any nonempty coalition `G`, if

```text
r_i(G\{i})<=r_i(G)       for every i in G,
r_j(G union {j})<=r_j(G) for every j notin G,       (12)
```

then pure sure exit by exactly `G` is an exact all-behavior terminal Nash
profile and its reward is a uniform-equilibrium payoff.

## Proof

### One-pair mass ledger

Let `g=Expl(sigma)`.  An outsider `d` can deviate to Never and receive exactly
zero.  Under the prescribed profile,

```text
u_d=-31 Pr({1,2,d} subset F).
```

Thus each incidence probability is at most `g/31`.  Every strict superset of
`A` contains at least one of the four outsiders, so

```text
c:=Pr(A proper-subset F)<=4g/31.                    (13)
```

Each member of `A` can Quit immediately and guarantee one, including every
date-zero tie.  Hence `u_1,u_2>=1-g`.  On the other hand,

```text
u_1+u_2=E|F intersect A|=2a+2c+s,
s=Pr(|F intersect A|=1).
```

The events defining `a,c,s` are disjoint, so `s<=1-a-c`, and

```text
2-2g<=u_1+u_2<=1+a+c<=1+a+4g/31.
```

Rearrangement proves (3)--(5).  Under the actual-profile identity (6a),
the checked implication `ell^2>=4ab`, together with
`ell<=66epsilon/31` and `a>=1-66epsilon/31>0`, proves (6).

### Robust completion

Put `p_d=Pr(A subset F and d in F)`.  If `d` deviates to Never, every realized
row omits `d`, so the deviation pays at least `-1`.  The prescribed payoff is
at most

```text
-31p_d+1(1-p_d)=1-32p_d.
```

Thus `p_d<=(2+epsilon)/32`.  The union bound gives

```text
c<=sum_d p_d<=1/4+epsilon/8.
```

The unchanged target-member identity then gives (8)--(9).

For (10), Never gives outsider `d` at least `-R`, while its prescribed payoff
is at most `R-(M+R)p_d`.  Hence

```text
p_d<=(2R+epsilon)/(M+R).
```

Also the `m` target members jointly secure at least `m(1-epsilon)`, whereas
their payoff sum is at most

```text
m-1+Pr(G subset F).
```

The union bound on strict supersets of `G` proves (10).

### Target lock

At pure `A`, each target member receives one; omitting itself produces the
other member's singleton and pays zero.  An outsider remaining absent receives
`r_d(A)>=-1`; joining at date zero produces `A union {d}` and pays `-31`.
Later histories are unreachable because `A` quits surely at date zero.

These comparisons are exactly the two membership-toggle families in
`IsQuittingSureExitSet reward A`.  The checked theorem
`isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet` upgrades them to all
behavioral deviations, and
`isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet` gives the
uniform-payoff conclusion.  The same checked characterization proves (12),
including singleton `G` through the extended-empty convention (11).

## Conjecture-facing change

The maintained `INCENTIVE_GADGET` question accepts a partial producer when
actual low terminal exploitability forces one missing target mass or the
leftover bound.  Equations (4)--(5) force both the `A` mass and the leftover
with fixed rational constants in one complete six-player table.

The same packet also explains exactly why this direct construction cannot
force the second pair mass: every robust completion has the pure `A` exact
equilibrium.  Under the explicit clock premise (6a), the integer-table
corollary (6) additionally forces `b` to be small at low exploitability.  More
generally, any pointwise strict-superset penalty that keeps outsiders from
joining a target while the target members prefer staying creates a sure-exit
lock.

Thus a complete gadget must destabilize each target row and control the
resulting join/leave incidence at another reached history or through a
nonlocal sign-changing mechanism.

## Probability and deviation audit

The profile is an arbitrary behavioral profile.  The proof uses its actual
first-coalition law, including simultaneous quitting, all other coalitions,
and Never.  No stationary, Markov, public-randomization, or bounded-controller
assumption is made.

Quit-now and Never are literal behavioral deviations.  The target-lock
conclusion invokes the checked sure-exit theorem, whose deviation class is the
complete behavioral strategy space.  The one-pair ledger does not use a clock
law.  The checked second-pair upper bound takes (6a) as an explicit premise;
the current Lean tree has no adapter deriving that premise from an arbitrary
behavioral profile's live roots.

## Boundary tests

1. **Pure-target regression.**  Pure `A` has exploitability zero and `b=0`.
   Hence no claim that the table solves the full two-pair gadget is possible.
2. **Tie coverage.**  A target member's Quit-now guarantee remains one when
   any opponents quit simultaneously, by the participant indicator reward.
3. **Passive completion.**  Outsider Never need only pay at least `-1`, not
   zero; this is why the robust constant weakens from `31/66` to `17/8`.
4. **Target coordinates are load-bearing.**  Arbitrarily changing the two
   target coordinates can invalidate both their security inequality and the
   target lock.  The robust theorem therefore completes outsider coordinates
   only.
5. **General denominator.**  Formula (10) requires `M+R>0`; the degenerate
   zero denominator is intentionally excluded.
6. **Singleton target.**  Condition (12) uses the extended empty reward zero;
   without (11), its member-leave expression is not defined by the original
   nonempty-coalition reward table.

## Source and novelty audit

The finite-horizon clock inequality is checked in
`MathUE/Probability/SquareRootCoalitionClock.lean`.  Its use for the literal
terminal masses of an arbitrary behavioral quitting profile is checked in
`UniformEquilibrium/Diagnostics/Quitting/SixPlayerArbitraryProfileClockAdapter.lean`
and archived in
[`SIX_PLAYER_ARBITRARY_PROFILE_CLOCK_ADAPTER.md`](SIX_PLAYER_ARBITRARY_PROFILE_CLOCK_ADAPTER.md).
The exact all-behavior sure-exit characterization and uniform-payoff consumer
are checked in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.

The sure-exit strategic theorem is not new.  The packet's new mathematical
content, now covered by the checked declarations below, is:

- the six-player `31/66` one-pair/leftover ledger;
- the completion-robust `17/8` estimate; and
- the proof that the entire direct cross-penalty completion class necessarily
  lands in the checked sure-exit predicate.

The acyclic solo, signed-influence, odd-blocker, and strategically precompact
watchdog results address different architectures and do not contain this mass
calculation.  No external literature result is used.

## Adapter and consumer

The actual-data adapter is the explicit complete six-player reward table (1),
so no unproduced certificate hypothesis is assumed.  Low terminal
exploitability itself produces (4).

For the unconditional ledger, the actual terminal-outcome law and literal
terminal exploitability are checked adapters from an arbitrary behavioral
profile.  The generic target estimate consumes an explicit terminal
`epsilon`-Nash premise.  The target-lock result consumes the completion
predicate through the checked sure-exit theorem.  These results remove the
`A`-mass and leftover obligations but deliberately fail the `B`-mass
obligation.  The target-lock theorem is the precise architecture-level reason.

The arbitrary-profile clock adapter now supplies (6a), so the second-pair
upper bound has `M`, `L`, `A`, and the checked quantitative consumer `C` for
every actual behavioral profile.  It still supplies no positive lower bound
on the second-pair mass.

## Original Lean handoff

1. Use player type `Fin 6` with named numerals and define the reward table by
   decidable coalition membership.
2. Define the first-coalition events through the existing terminal-law API;
   prove the four outsider Never inequalities and the two target Quit-now
   inequalities separately.
3. Sum the target coordinates pointwise as `card(F intersect A)` and use a
   finite union bound for strict supersets.
4. State the robust completion as a predicate fixing target coordinates and
   only the listed outsider coordinates.
5. Instantiate `IsQuittingSureExitSet` at `A`; use the existing equivalence and
   uniform-payoff theorem rather than reproving behavioral deviations.
6. Keep (10) as a separate generic lemma with explicit `M+R>0` and the
   extended-empty convention.

## Checked Lean realization

The game-independent finite-law ledger is checked by
`exactCoalitionMass_ge_of_memberSecurity_of_outsiderIncidence` in
`MathUE/Probability/CoalitionTargetMassLedger.lean`.

The literal and generic game-facing results are checked in
`UniformEquilibrium/Quitting/Paths/SixPlayerOnePairMassTargetLock.lean`:

- `IsQuittingTargetCrossPenaltyCompletion` is the generic actual-table source
  predicate;
- `integerReward` and `integerReward_isCrossPenaltyCompletion` are the complete
  six-player adapter;
- `exactCoalitionMass_ge_of_targetCrossPenaltyCompletion` is the generic target
  bound with an explicit terminal `epsilon`-Nash premise;
- `integerReward_exploitability_ge` and
  `integerReward_mass_and_leftover_of_exploitability_le` prove (3)--(4);
- `robustCompletion_firstPairMass_ge` and
  `robustCompletion_leftoverMass_le` prove (8);
- `integerReward_one_tenth_bounds` and
  `robustCompletion_one_tenth_bounds` check the stated constants;
- `pureSet_terminalNash_and_uniformPayoff_of_membershipToggles` is the generic
  membership-toggle consumer;
- `robustCompletion_targetA_terminalNash_and_uniformPayoff` checks the whole
  completion target lock; and
- `integerReward_pureTarget_exactNash_uniform_and_secondMass_zero` is the
  literal pure-target regression.

Those ledger, robust-completion, generic target-bound, and completion-lock
results have `M`, `L`, `A`, and `C`.  Their consumers are respectively actual
terminal-law bounds and the unrestricted-behavior exact-Nash/uniform-payoff
theorem; they do not produce the second pair.

The actual-profile clock construction and consumer are checked in
`UniformEquilibrium/Diagnostics/Quitting/SixPlayerArbitraryProfileClockAdapter.lean`:

- `profileTwoPairHazardClock` constructs the literal live-root clock;
- `profileTwoPairHazardClock_firstTargetAmplitude_sq` and
  `profileTwoPairHazardClock_secondTargetAmplitude_sq` prove the two exact
  stage identities;
- `rootSequenceTerminalCoalitionMass_profileLiveRoot_eq_exactCoalitionMass`
  identifies the chronological sums with the actual terminal atoms;
- `sqrt_firstPairMass_add_sqrt_secondPairMass_le_one` proves (6a); and
- `integerReward_secondPairMass_le` and
  `integerReward_one_tenth_secondPairMass_le_actualProfile` discharge the
  former supplied clock premise.

These declarations give the clock corollary `M`, `L`, `A`, and its exact
quantitative `C`.  They do not produce positive second-pair mass.

## Scope and nonclaims

- The packet does not force `b>=alpha`, prove a terminal exploitability gap,
  construct a counterexample, or decide the quitting conjecture.
- The pure `A` profile is an exact equilibrium, so the explicit table is not a
  candidate counterexample.
- The robust completion varies outsider coordinates only.
- The target-lock theorem does not rule out nonlocal or sign-changing leakage
  control which deliberately makes a target row unstable.
- No clock law is stored in the source table.  The actual-profile adapter
  derives (6a) from the quitting outcome law of every behavioral profile.
- The packet assumes no public correlation and does not restrict the
  unilateral deviation class.
