# Fully screened prefixes cannot survive exact finite timing re-equilibration

Author: `CODEX_AMPERE`

Independent reviews:

- [CODEX_RIEMANN](../feedback/CODEX_AMPERE__FULLY_SCREENED_TIMING_NASH_RETURN_FLOOR__BY_CODEX_RIEMANN.md)
- [CODEX_ROOT](../feedback/CODEX_AMPERE__FULLY_SCREENED_TIMING_NASH_RETURN_FLOOR__BY_CODEX_ROOT.md)

## Exact statement

This note gives a quantitative positive-gap consequence for the sole fully
screened Zeno arm isolated in
`CODEX_AMPERE__ACTUAL_ZENO_DELETED_SURVIVAL_PASSPORT.md`.

Replace a finite screened prefix by an exact mixed Nash equilibrium of the
finite timing game whose all-Never outcome returns to the **literal retained
tail**.  In the Fin4 hard residual, the retained minimum tail lies uniformly
above every player's punishment value.  Then the timing equilibrium cannot
remain screened: its all-player return probability has a fixed positive
lower bound depending only on the terminal gap, reward bound, and not on the
horizon.

The proof is exact against unrestricted behavioral deviations.  If the joint
return mass tended to zero, the terminal gap would select one exceptional
deleted-survival host.  Replacing the tail by that host's punishment would
make the host harmless, while the identity

\[
H_iH_h\le M
\]

makes every other player harmless.  This would produce terminal approximate
Nash profiles, contradicting the fixed gap.

Thus naive finite timing-game Nashification is rigorously classified:

\[
\boxed{
\text{terminal approximants}
\quad\lor\quad
\text{a finite exact timing-Nash block with fixed positive joint return}.}
\]

Under a counterexample witness only the second arm remains.  This is an exact
universal constraint on every re-equilibrated timing block, but it is **not
yet an admissible return**.  Indeed the all-`infinity` timing profile is already
a strict equilibrium under the same singleton separation and gives the
trivial all-Continue identity block.  The nontrivial blocks are Nash relative
to the tail's prescribed payoff `U`, not its cap `B`, and their equilibrium
payoff need not equal the returned payoff.  Calling the return probability a
completed chronology would be unsupported.

## Conjecture-facing change

The sole fully screened actual Zeno arm cannot be preserved by exact finite timing-game Nashification. Under the positive terminal gap and the source's uniform punishment separation, every equilibrium of every such finite timing game has a horizon-independent positive probability of returning all players to the exact retained tail. Thus the remaining obstruction is no longer escaping timing under Nashification, but prescribed-payoff/cap closure of a uniformly returning nonidentity block. The identity all-Continue equilibrium shows why the return floor alone is not a consumer.

## Question

Does positive global-minimum/terminal-gap provenance force unrestricted cap
witnesses in a fully screened prefix to localize before the invisible mark?
Can one instead replace the prefix by a finite timing-game Nash equilibrium
while preserving the vanishing deleted-survival clocks?

The answer to the second question is no, quantitatively.  The cap witness need
not localize at one premark date; it localizes only to one **tail-return host**.

## Sources and overlap

- `notes/CODEX_AMPERE__ACTUAL_ZENO_DELETED_SURVIVAL_PASSPORT.md`;
- `notes/CODEX_FERMAT__FINITE_DEADLINE_NASH_HORIZON_ESCAPE.md`;
- `notes/CODEX_MINER__FINITE_DEADLINE_NASH_ESCAPE_CERTIFICATE_FORMALIZATION_PACKET.md`;
- `notes/CODEX_AMPERE__FINITE_FIXATION_SPECTATOR_COMPRESSION_AND_HOST_ROTATION.md`;
- `Research/Quitting/FiniteDeadlineTimingNashDebtHierarchy.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingNashDebt.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`; and
- the punishment-normal and minimum-fiber singleton-separation fields of the
  maintained Fin4 hard residual.

The classical finite-deadline construction uses all-Continue payoff zero and
shows that a gap can hide immediately beyond each horizon.  The result here
instead assigns an arbitrary actual retained tail to the all-Never timing
action, proves the exact tail-debt transport `d_i <= H_i d_i(tail)`, and uses
punishment separation to derive a uniform **joint return** floor.  The earlier
finite-host theorem fixes one player's finite clock and re-equilibrates the
others.  Here all four timing laws are re-equilibrated, and the positive-gap
argument itself selects the exceptional host.

## 1. Finite timing game returning to an actual tail

Let `I` be finite and nonempty, let rewards have absolute value at most
`R>0`, and let `tau` be an actual behavioral tail.  Fix a horizon `N`.  Define
a finite strategic game with pure actions

\[
A_N=\{0,1,\ldots,N-1,\infty\}.
\]

If some player chooses a finite action, the earliest time and its minimizing
coalition determine the quitting reward.  If every player chooses `infinity`,
the payoff is

\[
U(\tau).
\tag{1}
\]

Let `mu` be any independent mixed Nash equilibrium of this finite game.  Its
standard behavioral hazard realization plays the finite timing law for `N`
dates and, on the all-Continue history, resumes `tau` literally.  Denote this
actual grafted profile by

\[
\sigma=\mu*\tau.
\]

Put

\[
S_i:=\mu_i(\infty),\qquad
M:=\prod_iS_i,
\qquad
H_i:=\prod_{j\ne i}S_j.
\tag{2}
\]

Here `M` is the probability of returning jointly to `tau`, while `H_i` is the
probability that a deviation of player `i` reaches the tail before any
opponent quits.

## 2. Exact unrestricted tail-debt transport

Let `u_i` be player `i`'s equilibrium payoff in the finite timing game.  The
behavioral realization gives

\[
U_i(\sigma)=u_i.
\tag{3}
\]

Every arbitrary behavioral deviation of player `i` has two types of pure
components:

1. quit at one of the finite dates before `N`; or
2. Continue through the block and, if every opponent also survives, use an
   arbitrary behavioral deviation in `tau`.

The first components are finite pure actions of the timing game and have
payoff at most `u_i`.  The second component differs from the timing action
`infinity` only on the event that all opponents choose `infinity`, of
probability `H_i`; on that event its maximal improvement is `d_i(tau)`.
Therefore

\[
\boxed{d_i(\mu*\tau)\le H_i d_i(\tau).}
\tag{4}
\]

This quantifies over the complete behavioral strategy class.  It does not
assume a best response is attained: take suprema after the displayed bound.
Since every payoff belongs to `[-R,R]`,

\[
d_i(\mu*\tau)\le2R H_i.
\tag{5}
\]

## 3. The gap selects a deleted-survival host

Assume the reward table has a terminal exploitability witness

\[
\max_i d_i(\rho)\ge\gamma>0
\qquad\text{for every behavioral profile }\rho.
\tag{6}
\]

Apply (6) to `sigma=mu*tau`.  Equations (4)--(5) give one player `h` with

\[
H_h d_h(\tau)\ge\gamma,
\qquad
\boxed{H_h\ge\eta:=\frac{\gamma}{2R}.}
\tag{7}
\]

For any `i != h`, the exact product identity gives

\[
H_iH_h=M\prod_{k\ne i,h}S_k\le M,
\]

and hence

\[
\boxed{H_i\le\frac{M}{\eta}.}
\tag{8}
\]

Thus if joint return were small, every player except one would already have
small access to any replacement tail.

## 4. Punishment completes the exceptional host

Assume the retained tail has a uniform punishment separation: there are
numbers `chi_i` and `kappa>0` such that

\[
U_i(\tau)\ge\chi_i+\kappa
\qquad(i\in I),
\tag{9}
\]

and for every player `i` there is an actual punishment profile `pi_i` with

\[
B_i(\pi_i)\le\chi_i+\kappa/2.
\tag{10}
\]

In the Fin4 hard residual, punishment normality gives
`chi_i <= r_i({i})`, while the positive-minimum singleton separation gives
`U_i(tau) >= r_i({i})+Delta/2` on sufficiently late retained tails.  Thus
(9)--(10) hold uniformly after taking `kappa` below that fixed separation.

Replace `tau` after the same timing block by the selected host punishment:

\[
\widehat\sigma:=\mu*\pi_h.
\]

The prescribed payoff changes only on the event that **all** players choose
`infinity`, so

\[
|U_i(\widehat\sigma)-u_i|\le2RM.
\tag{11}

For the host, every finite quitting action is still bounded by `u_h` by Nash
optimality.  The Continue-through-the-block action is no better than its old
timing-game value because

\[
B_h(\pi_h)\le\chi_h+\kappa/2<U_h(\tau).
\]

Hence

\[
B_h(\widehat\sigma)\le u_h,
\qquad
d_h(\widehat\sigma)\le2RM.
\tag{12}
\]

For `i != h`, a tail deviation can improve on its old timing action by at
most `2R H_i`.  Combining this with (11) gives

\[
d_i(\widehat\sigma)\le2R(H_i+M)
 \le2RM\left(1+\frac1\eta\right).
\tag{13}
\]

Therefore

\[
\boxed{
\max_i d_i(\widehat\sigma)
\le2RM\left(1+\frac1\eta\right).}
\tag{14}
\]

This is a literal terminal profile, not a candidate semantic annotation.

## 5. Uniform positive joint-return floor

Apply the terminal gap (6) once more, now to `widehat sigma`.  Using
`eta=gamma/(2R)` in (14) gives

\[
\gamma
 \le2RM\left(1+\frac{2R}{\gamma}\right).
\]

Thus every mixed Nash equilibrium of every finite timing game returning to a
punishment-separated retained tail satisfies

\[
\boxed{
M\ge
m_0:=\frac{\gamma^2}{2R(\gamma+2R)}>0.}
\tag{15}
\]

In particular every `S_i` is positive and

\[
H_i=\frac{M}{S_i}\ge M\ge m_0
\qquad(i\in I).
\tag{16}
\]

This is the exact answer to the proposed finite-Nash repair: it cannot retain
the fully screened deleted-survival vector.  It instead manufactures a
source-attached finite block that returns jointly to the same literal tail
with probability at least `m_0`, uniformly in its horizon and in the selected
mixed Nash equilibrium.

Equivalently, without assuming the global witness, any sequence of such
timing equilibria whose joint return tends to zero yields the explicit
terminal approximants `mu_n*pi_(h_n)` after fixing a host subsequence.

## 6. What the return floor does and does not consume

This construction re-equilibrates directly in front of the postmark tail; it
discards the old pure-pair marked row and is therefore not itself a raw point
of the normalized decorated prefix orbit.  It retains a literal pointer and
return to the same minimum tail, but not the marked-pair decoration.

The result is stronger than another unpaid terminal atom as a **no-go for
screened Nashification**:

- `M` is the probability of returning with **all** players to the exact
  retained minimum tail, not the mass of an unrelated terminal coalition;
- the block is a genuine finite strategic Nash equilibrium relative to the
  prescribed continuation `U(tau)`;
- all finite planned deviations are controlled simultaneously; and
- the floor is uniform over horizons and equilibrium selections.

It is not by itself a producer of useful motion.  Under (9), the pure
all-`infinity` profile is already a strict timing-game Nash equilibrium:
unilaterally quitting at any finite date gives the singleton reward, strictly
below `U_i(tau)`.  This equilibrium has `M=1` and is just a finite list of
all-Continue roots before the unchanged tail.  Thus existence of a block
satisfying the floor is tautological; the content of (15) is that **no other
equilibrium selection can stay screened either**.

Moreover, the nontrivial blocks are still not existing admissible return
objects.  If `A(mu)` is
the finite-absorption contribution, then

\[
u=A(\mu)+M U(\tau).
\tag{17}
\]
\]

There is no reason for `u=U(tau)`.  Nor is `mu` Nash against the cap vector
`B(tau)`: the missing cap premium is exactly the tail debt transported by the
deleted reaches.  Repeating the block changes its continuation payoff and can
destroy its finite-game Nash inequalities.

Thus any attempted nontrivial Nashification leaves the finite residual:

\[
\boxed{
\begin{array}{c}
\text{a finite timing-Nash block, literal tail }\tau,\\
M\ge m_0,\quad u=A(\mu)+M U(\tau),
\end{array}
}
\tag{18}
\]

together with the question whether it can be converted into

- a prescribed-payoff fixed point/near-return;
- a cap-Nash charged return; or
- a renewable minimum-source regeneration.

The theorem prevents the fully screened clock from surviving re-equilibration,
but it does not prove that Nashification is close to the original screened
word.  Indeed equilibrium selection can move discontinuously and can restore
large Never mass.  The zero-minimum table in Section 5 of
`CODEX_AMPERE__ACTUAL_ZENO_DELETED_SURVIVAL_PASSPORT.md` already illustrates
this: for the positive-debt pure-singleton tail, the all-`infinity` timing
profile is a Nash equilibrium, so `M=1`, even though the supplied raw prefix
words have every deleted reach tending to zero.

## 7. Consequence for the fully screened branch

The original screened raw words still need not contain a fixed profitable
stage.  A pure-time cap witness can be a diffuse Never/avoidance gain spread
over the entire word, exactly as in the standard horizon-escape examples.
The valid localization statement is instead:

\[
\boxed{
\text{after exact finite timing re-equilibration, the obstruction returns
to the literal minimum tail with fixed all-player mass}.}
\]

Therefore a successful timing-game consumer would have to select a
**nonidentity** block satisfying (18) and close its prescribed payoff/cap
seam.  The theorem supplies neither such a selection nor useful charge.  It
rigorously rules out the hope that ordinary exact Nashification will remain
close to the discarded screened word.

## Adapter and consumer

A future actual-data adapter must use the complete tail semantic coordinate of
the normalized source decorations, not total-debt convergence alone.  It must
derive one uniform punishment gap and preselected approximate punishment
profiles from minimum-fiber singleton separation and punishment normality, and
it must compile each mixed finite timing equilibrium into the literal root-word
certificate below.  No such Fin4 adapter is checked here.

The generic output excludes screened timing-Nash blocks under the supplied
certificate and separation hypotheses.  It is consumed into an admissible
return only if a further theorem selects a nonidentity block and closes its
prescribed-payoff or cap seam.  No such downstream consumer is checked here.

## Lean-facing boundary

The mathematical core separates cleanly into:

```text
finiteTimingNash_graft_terminalDebt_le_deletedReach_mul_tailDebt
finiteTimingNash_graft_punishment_debt_le
terminalGap_finiteTimingNash_jointReturn_ge
```

The producer must retain the mixed timing laws, their literal behavioral
realization, the actual returned tail, joint/deleted return probabilities,
and finite-game Nash inequalities.  It should not claim equality of the block
payoff and tail payoff, Nash against `B(tau)`, or chronological recurrence.

The generic retained-tail graft, debt-transport, punishment, and joint-return
floor declarations are checked in Lean.  The mixed timing-equilibrium producer
and the Fin4 actual-source adapter described above are not checked.

## Nonclaims

- Existence of a uniformly returning block is not progress by itself; the
  all-Continue identity block already qualifies.
- No fixed profitable premark date is produced.
- The Nash timing word need not resemble the original screened word.
- The re-equilibrated block sits before the retained postmark tail and does
  not preserve the normalized orbit's pure-pair marked row.
- A lower bound on joint return is not called a payoff near-return.
- No positive-gap table is constructed.

## Formalization record

The mathematical no-go core is formalized by two production diagnostics
modules.  It is a conditional generic theorem, not a Fin4 source adapter.

1. `UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingNash.lean`
   defines `quittingRetainedTailFiniteTimingGraft` as a literal finite root
   stack followed by an arbitrary behavioral tail.
   `IsQuittingRetainedTailFiniteTimingNash` records exactly the supplied
   finite-stop and pass-through pure timing comparisons; it does not construct
   them from a mixed finite game.
2. `quittingPureTimeBehaviorStrategy_absolute_eq_continueDeviation` and
   `quittingPureTimeDeviationPayoff_retainedTail_eq_of_lt` prove exact time
   rebasing and early-stop tail independence.
   `quittingPureTimeDeviationPayoff_absolute_sub_pass_eq` and
   `quittingPureTimeDeviationPayoff_absolute_sub_crossTailPass_eq` give the
   exact player-deleted-survival scaling for late deviations, while
   `quittingRetainedTailFiniteTimingGraft_payoff_sub_eq_jointReturn_mul` gives
   exact prescribed-payoff scaling by joint return.
3. `IsQuittingRetainedTailFiniteTimingNash.pureTimePayoff_le` bounds every
   deterministic stopping time.  The theorem
   `IsQuittingRetainedTailFiniteTimingNash.debt_le_deletedReturn_mul_tailDebt`
   then takes the supremum and obtains the full unrestricted behavioral debt
   bound without assuming a best response is attained.
4. `IsQuittingRetainedTailFiniteTimingNash.replacementBestResponseValue_le`,
   `hostPunishmentDebt_le`, and `punishmentDebt_le` treat a literal replacement
   tail.  The selected host has debt at most `2 * R` times joint return; every
   other coordinate has debt at most `2 * R` times the sum of its
   player-deleted return and joint return.
5. `UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingReturnFloor.lean`
   proves `HasTerminalExploitabilityGap.exists_debt_ge` and the bounded-debt
   host selector
   `IsQuittingRetainedTailFiniteTimingNash.exists_host_gap_le_two_mul_bound_mul`.
   The capstone `terminalGap_retainedTailFiniteTimingNash_jointReturn_ge` uses
   `mul_opponentSurvival_le_jointSurvival_of_ne` and a second application of
   the terminal gap to prove the literal bound

   ```text
   gamma ^ 2 / (2 * R * (gamma + 2 * R))
     <= quittingLiteralRootStackJointSurvival roots.
   ```

   `terminalGap_retainedTailFiniteTimingNash_jointReturnFloor_pos` proves the
   displayed floor is strictly positive when `gamma > 0` and `R > 0`.

Evidence seals:

- **M:** PASS.  The arbitrary-tail graft identities, unrestricted debt
  transport, exceptional-host punishment argument, deleted-survival product
  estimate, and exact return-floor arithmetic match the reviewed proof.
- **L:** PASS.  Every declaration named above is checked Lean under the stated
  imports.  Promotion checks include direct and named builds, the diagnostics
  reader and full build, regenerated exhaustive axiom audit, trust,
  documentation, import-graph and unit checks, duplicate-proof and
  derivable-telescope checks, and source-width/diff hygiene.  Important axiom
  prints use only `propext`, `Classical.choice`, and `Quot.sound`.
- **A:** NOT SEALED.  The theorem accepts the root word, exact pure timing
  comparisons, retained behavioral tail, coordinatewise separation, and
  punishment profiles.  No declaration constructs this certificate from a
  mixed finite timing equilibrium or from the actual Fin4 screened source.
- **C:** NOT SEALED.  The conclusion is only a positive joint-return mass
  floor.  No theorem selects a nonidentity block, identifies its payoff with
  the tail payoff, proves cap Nash, regenerates a minimum source, or compiles
  an admissible return.

The checked theorem is generic over every finite player type.  It does not
assert that the timing roots resemble an incoming screened word or preserve a
marked pure pair.  Joint return is neither a marked density nor a payoff
return.  The all-Continue identity block is not excluded.  No chronology,
recurrence, terminal approximation, uniform-equilibrium payoff, positive-gap
table, or Fin4 contradiction is produced.  The mathematical provenance
remains this packet and its linked independent reviews; no external paper
theorem is imported.
