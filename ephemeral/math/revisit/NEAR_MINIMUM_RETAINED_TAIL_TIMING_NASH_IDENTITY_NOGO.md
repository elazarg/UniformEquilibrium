# Near-minimum retained-tail timing Nash is the identity

Author: `CODEX_ROOT`

Independent review: [timing-identity audit](../feedback/CODEX_ROOT__NEAR_MINIMUM_RETAINED_TAIL_TIMING_NASH_IDENTITY_NOGO__BY_TIMING_IDENTITY_REVIEW.md)

The generic rigidity core is checked in Lean, with stronger constants than
the cardinality-averaged presentation below.
`nonidentity_exactRoot_uniformOpponentAbsorption_ge` gives every coordinate
the same opponent-absorption floor `kappa / (kappa + 2 * M)`.
`nearMinimum_rootNashAgainstPayoff_eq_allContinue` uses the explicit threshold
`excess < kappa * D_* / (2 * M)`, and
`nearMinimum_literalExactRootStack_eq_replicate_allContinue` propagates the
identity backward through any supplied `IsQuittingLiteralExactRootStack`.
These declarations are in
`Research/Quitting/NearMinimumRetainedTailTimingNashIdentity.lean` and have
`M` and `L`, but no Fin4 `A` or `C`.

The packet is not fully formalized as written.  No checked theorem identifies
the mixed payoff of the retained-tail finite timing game with its behavioral
graft, transfers mixed Nash optimality to every positive-Never conditional
suffix and current root, or constructs the exact credible root stack consumed
by the checked rigidity theorem.  Consequently the mixed-law identity theorem
and the Fin4 minimum-source/punishment/return-floor composition remain open.
Revisit this packet when that source compiler is checked; the generic root and
supplied-stack core needs no repair.

## Question

The checked retained-tail timing theorem shows that, in a positive-gap game,
every exact finite timing equilibrium in front of a punishment-separated
minimum tail has a fixed positive probability of jointly returning to that
tail.  Could a nonidentity equilibrium then supply a uniformly charged return
block?

The answer is no sufficiently close to the positive minimum.  Positive joint
return makes the finite timing equilibrium recursively visible at every date,
while minimum-debt contraction and singleton separation force every visible
one-stage Nash root to be all Continue.

## 1. Robust one-stage rigidity

Let `I` be finite with `2 <= |I|`.  Let rewards have absolute value at most
`R>0`.  Let `D_*>0` be the global infimum of total terminal debt over actual
behavioral profiles (equivalently over the maintained carrier).  Let `tau` be
an actual behavioral tail satisfying

\[
 D(\tau)\le D_*+\varepsilon
\tag{1}
\]

and the uniform singleton separation

\[
 U_i(\tau)\ge r_i(\{i\})+\kappa
 \qquad(i\in I),\qquad \kappa>0.
\tag{2}
\]

Define

\[
 c:=\frac{\kappa}{2R+\kappa},
 \qquad
 \beta:=\frac{c}{|I|-1}\in(0,1].
\tag{3}
\]

Let `q` be an exact product Nash root for the one-stage quitting game with
continuation payoff `U(tau)`.  If

\[
 \varepsilon<\frac{\beta}{1-\beta}D_*,
\tag{4}
\]

with the right side interpreted as positive infinity when `beta=1`, then

\[
 \boxed{q=\mathbf C.}
\tag{5}
\]

### Proof

Write

\[
 H_i(q)=\prod_{j\ne i}(1-q_j)
\tag{6}
\]

for player `i`'s opponent-Continue probability.  Because `q` is root Nash
against the actual prescribed continuation `U(tau)`, its coordinate root
defects vanish.  The checked arbitrary-root debt transport bound therefore
gives

\[
 d_i(q*\tau)\le H_i(q)d_i(\tau).
\tag{7}
\]

Suppose `q` is nonidentity and select a player `j` with `q_j>0`.  Since Quit
is in player `j`'s support, its Quit endpoint is at least as good as Continue.
On the event that every opponent Continues, Quit minus Continue is at most

\[
 r_j(\{j\})-U_j(\tau)\le-\kappa.
\]

On the complementary event the endpoint difference is at most `2R`.
Consequently

\[
 0\le-\kappa H_j(q)+2R(1-H_j(q)),
\]

and hence

\[
 1-H_j(q)\ge c.
\tag{8}
\]

In particular, some opponent `k != j` satisfies

\[
 q_k\ge\beta.
\tag{9}
\]

Now every player has a quantitative opponent-absorption floor.  If `i` is a
participant (`q_i>0`), the same support argument gives

\[
 1-H_i(q)\ge c\ge\beta.
\tag{10}
\]

If `i` is not a participant, the participant `k` from (9) is one of its
opponents, so

\[
 1-H_i(q)\ge q_k\ge\beta.
\tag{11}
\]

Thus `H_i(q)<=1-beta` for every player.  Summing (7), using global
minimality for the actual profile `q*tau`, and then (1), yields

\[
 D_*
 \le D(q*\tau)
 \le(1-\beta)D(\tau)
 \le(1-\beta)(D_*+\varepsilon).
\tag{12}
\]

Condition (4) makes the last quantity strictly smaller than `D_*`, a
contradiction.  Therefore `q` is all Continue.

The same proof applies to a carrier minimum point and its semantic prefix,
provided the maintained arbitrary-root bound and prefix closure are used in
the carrier.  The actual-tail version is sufficient for the source chronology.

## 2. Every finite retained-tail timing Nash is the identity

For a positive integer `N`, define the retained-tail finite timing game
`Gamma_N(tau)` explicitly.  Player `i` chooses an action in

\[
 \{0,\ldots,N-1,\infty\}.
\]

The earliest finite declared time and its minimizing coalition give the
ordinary quitting reward.  If every declaration is `infinity`, the payoff is
the actual prescribed tail payoff `U(tau)`.  A mixed strategy profile is the
independent product of the players' marginal timing laws.  Its behavioral
hazard realization plays those laws for `N` live dates and resumes `tau`
literally on joint survival.

Assume that every exact mixed Nash law of every `Gamma_N(tau)` has positive
joint `infinity` probability.  Then, under the hypotheses and threshold of
Section 1, the unique Nash equilibrium of every `Gamma_N(tau)` is pure
all-`infinity`.

### Proof

Use induction on `N`.  For `N=1`, a mixed timing law is exactly a product root
against continuation payoff `U(tau)`, so Section 1 applies.

Let `mu` be a Nash law of `Gamma_N(tau)`, `N>1`.  Write

\[
 x_i=\mu_i(0),\qquad C_i=1-x_i.
\]

Positive joint `infinity` mass implies `mu_i(infinity)>0` for every `i`, and
hence `C_i>0`.  Define the conditional shifted tail law on
`{0,...,N-2,infinity}` by

\[
 \bar\mu_i(t)=\frac{\mu_i(t+1)}{C_i},
 \qquad
 \bar\mu_i(\infty)=\frac{\mu_i(\infty)}{C_i}.
\tag{13}
\]

We need two elementary normal-form facts.

First, `bar mu` is Nash in `Gamma_(N-1)(tau)`.  If player `i` could improve
there by replacing `bar mu_i` with another timing law `rho_i`, replace only
the conditional tail of `mu_i` by `rho_i`, keeping its current probability
`x_i` unchanged.  The original and modified whole-game strategies agree if
`i` Quits at the current date and agree whenever an opponent absorbs there.
Their payoff difference is the alleged shorter-game gain multiplied by

\[
 \prod_j C_j>0.
\tag{14}
\]

That would contradict Nash optimality of `mu`.

Second, the current product root `x` is Nash in the Boolean one-stage game
whose continuation payoff is the prescribed payoff of the behavioral graft
`bar mu * tau`.  Hold player `i`'s conditional law `bar mu_i` fixed and change
only its current Quit probability.  This is an admissible mixed timing law in
`Gamma_N(tau)`, and its payoff difference is exactly the corresponding
one-stage root payoff difference.  Nash optimality of `mu` therefore gives
the root-Nash inequalities for every player.

By the induction hypothesis, `bar mu` is pure all-`infinity`.  Its behavioral
graft is a finite string of all-Continue roots followed by `tau`, so its
prescribed payoff is exactly `U(tau)`.  The current root `x` is therefore a
one-stage Nash root against `U(tau)`, and Section 1 makes it all Continue.
Equation (13) then reconstructs `mu` as pure all-`infinity`.

This proof also explains the positive-return hypothesis.  If some declared
Never mass is zero, the multiplier (14) can vanish and a normal-form timing
equilibrium may carry arbitrary noncredible later play.  Positive joint return
removes exactly that branch.

## 3. Fin4 counterexample-regime consequence

The following is the complete ordinary-mathematics adapter from the maintained
Fin4 hard residual.  It is not claimed to be a checked Lean composition.

Let `source` be the maintained positive-minimum Fin4 source.  Choose one
actual chronology of tails `tau_n` whose terminal semantic pairs converge to
the source point.  Then

\[
 D(\tau_n)\to D_*>0.
\tag{15}
\]

The checked uniform minimum-fiber isolation theorem supplies `Delta>0` such
that at the minimum point

\[
 U_i-r_i(\{i\})\ge\Delta
\qquad(i\in\operatorname{Fin}4).
\tag{16}
\]

Prescribed-payoff convergence makes, for all sufficiently large `n`,

\[
 U_i(\tau_n)\ge r_i(\{i\})+\frac{3\Delta}{4}.
\tag{17}
\]

Fix such an `n` so late that the excess in (15) also satisfies the threshold
(4), with `kappa=3 Delta/4` (or any smaller fixed positive value).

Punishment normality gives player values `chi_i<=r_i({i})`.  By the definition
and checked stationary approximation of the punishment value, choose for each
player one actual stationary punishment profile `pi_i` satisfying

\[
 B_i(\pi_i)\le\chi_i+\frac\Delta8.
\tag{18}
\]

Because the player set is finite, all four choices are made simultaneously.
Equations (17)--(18) imply the return-floor theorem's separation hypotheses
with, for example, its parameter `kappa_floor=Delta/4`:

\[
 U_i(\tau_n)\ge\chi_i+\kappa_{\rm floor},
 \qquad
 B_i(\pi_i)\le\chi_i+\frac{\kappa_{\rm floor}}2.
\tag{19}
\]

Now fix any horizon `N` and choose a mixed Nash equilibrium `mu` of the finite
normal-form game `Gamma_N(tau_n)`.  Realize each marginal timing law by its
literal finite hazard sequence.  Nash optimality against every finite pure
date and the `infinity` action gives exactly the supplied finite-timing
comparisons in `IsQuittingRetainedTailFiniteTimingNash`: early pure dates are
the finite actions of `Gamma_N(tau_n)`, while the pass-through action is its
`infinity` action and resumes the literal tail.  The product of the root-word
joint Continue masses telescopes to

\[
 \prod_i\mu_i(\infty),
\tag{20}
\]

the mixed law's joint `infinity` probability.

Apply `terminalGap_retainedTailFiniteTimingNash_jointReturn_ge` with the
terminal gap, (19), the actual punishment profiles, the hazard word, and the
retained tail `tau_n`.  It gives

\[
 \prod_i\mu_i(\infty)
 \ge
 \frac{\gamma^2}{2R(\gamma+2R)}>0.
\tag{21}
\]

Thus every Nash equilibrium of every `Gamma_N(tau_n)` satisfies the positive
joint-return hypothesis of Section 2.  Sections 1--2 prove that it is pure
all-`infinity`.

Summarizing the supplied project facts used by this construction:

1. positive-minimum singleton separation supplies one uniform `kappa>0` on
   sufficiently late actual minimum-source tails;
2. those tails satisfy `D(tau_n)->D_*>0`;
3. punishment normality supplies the uniform tail-punishment separation used
   by the checked retained-tail return-floor theorem; and
4. the terminal exploitability witness makes every finite retained-tail
   timing Nash have joint return at least

   \[
   \frac{\gamma^2}{2R(\gamma+2R)}>0.
   \]

\[
\boxed{
 \text{every finite timing Nash returning to }\tau_n
 \text{ is the pure all-Continue identity block}.}
\tag{22}
\]

Thus exact finite timing-game Nashification cannot produce a nonidentity
charged return at a sufficiently near-minimum retained tail.  The remaining
timing-Nash selection problem is not merely unresolved: in the positive-gap
minimum-source regime its desired branch is absent.

This strengthens the checked return-floor no-go.  Once the tail is sufficiently
near minimum, the identity law is the only timing equilibrium to which that
positive floor applies.  Its joint return equals `1`; no equality with the
numerical lower bound is asserted.

## Probability, agency, and strategy-class audit

- Root actions are independent product Quit/Continue actions.
- `q` is Nash against the prescribed continuation payoff `U(tau)`, not the
  semantic cap `B(tau)`.
- Equation (7) controls the complete behavioral terminal debt after the root;
  it is not restricted to one-stage deviations.
- The support argument uses only the two pure root endpoints.  Mixed root
  participation is handled because every positive-probability action is a
  best response in a finite Nash equilibrium.
- The finite timing conclusion uses normal-form mixed timing laws and their
  exact behavioral hazard realization.  Positive declared Never mass gives
  the hypotheses of the checked conditional-tail Nash recursion.
- `Never`, unbounded dates, and arbitrary behavioral tail deviations remain
  inside `d_i(tau)` in (7).

## Boundary tests

1. **No positive minimum.**  The two-player retained-tail regression in
   `CODEX_KOLMOGOROV__FINITE_DEADLINE_PROJECTIVE_BOUNDARY.md` has uniform
   singleton separation and unique all-`infinity` timing Nash, but global
   minimum zero.  It is compatible with the theorem and shows why a local
   statement alone is not conjecture-facing.
2. **No singleton separation.**  If `U_j(tau)=r_j({j})`, one player may mix
   alone without requiring any opponent participation; (8) fails exactly.
3. **Tail not near minimum.**  The contraction in (12) may be paid by the
   initial excess.  The threshold (4) is therefore essential.
4. **Zero joint return.**  A normal-form timing equilibrium can hide
   noncredible later play when some declared Never mass is zero.  Section 2
   uses the checked positive return floor precisely to exclude this branch.

## Source audit and Lean handoff

The proof is designed to use:

- the arbitrary-root coordinate bound of the form
  `d_i(prefix) <= rootDefect_i + opponentContinue_i * d_i(tail)`;
- the root-Nash specialization in which `rootDefect_i=0`;
- `timingLawTail_isNash_of_isNash_of_positiveContinue` and
  `timingLaw_eq_of_current_tail_eq` in
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingRecursion.lean`
  as zero-tail analogues of the retained-tail recursion proved in Section 2;
- `terminalGap_retainedTailFiniteTimingNash_jointReturn_ge` in
  `UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingReturnFloor.lean`;
- the hard residual's uniform minimum-fiber singleton separation and
  punishment data.

The current Fin4 library also has the qualitative neighborhood theorem
`exists_finFour_minimumFiberIsolation_and_debtMoat_of_no_uniformPayoff`,
which already forces all Continue as the unique root in a sufficiently small
minimum-fiber tube.  Section 1's new content is the explicit generic modulus
(3)--(4).  Sections 2--3 additionally turn positive joint return into a
normal-form finite-timing identity theorem.

The checked declarations are:

```text
nonidentity_exactRoot_uniformOpponentAbsorption_ge
nearMinimum_rootNashAgainstPayoff_eq_allContinue
nearMinimum_literalExactRootStack_eq_replicate_allContinue
```

The remaining handoff is the retained-tail mixed-law compiler:

```text
isRetainedTailTimingNash_tail_of_positiveNever
isRetainedTailTimingNash_currentRoot_of_positiveNever
nearMinimum_retainedTailFiniteTimingNash_eq_allInfinity
FinFourMinimumAtomProducer.
  retainedTailFiniteTimingNash_eq_allInfinity_eventually
```

The first two missing declarations must be proved from the mixed-payoff/graft
identity rather than by rewriting the continuation payoff to zero.  The
finite identity theorem should accept positive joint return as a hypothesis;
the Fin4 adapter should construct the mixed-law hazard word and punishment
profiles and obtain that hypothesis from the checked terminal-gap return
floor.

## Exact limitation

This is a negative architecture theorem.  It does not produce terminal
approximants, an admissible return, or support descent.  It proves that exact
finite timing Nashification at the retained near-minimum tail cannot be the
missing producer: all such blocks are eventually the literal identity.

The remaining structural route must use the supplied non-Nash chronological
charge, a constrained/nonexact controller, or a different source-attached
operation.


## Conjecture-facing change

The checked retained-tail timing theorem previously proved only that exact finite timing re-equilibration cannot remain fully screened: every equilibrium has a fixed positive probability of returning to the retained near-minimum tail. That left open the possibility of selecting a nonidentity, uniformly charged timing block and closing its payoff seam.

This packet removes that possibility. Near enough to the positive minimum, global debt minimality and singleton separation force every one-stage Nash root against the prescribed tail payoff to be all Continue. The checked positive joint-return floor makes every date of a finite timing equilibrium recursively credible, so the one-stage rigidity propagates backward through the entire timing game. The unique finite timing equilibrium is the all-Continue identity block at every horizon.

Thus exact retained-tail timing Nashification is decisively excluded as a producer in the Fin4 counterexample regime. The missing chronology must use the supplied non-Nash charge, a constrained/approximate controller, or a different source-attached operation.

## Adapter and consumer

The adapter starts from an arbitrary sufficiently late actual tail in the maintained Fin4 minimum-source chronology. It uses the checked uniform minimum-fiber singleton gap, chooses actual stationary punishment profiles approximating each punishment value, realizes an arbitrary mixed Nash law of the retained-tail finite timing game as a literal root word, and invokes the checked joint-return floor.

The output is a negative architecture consumer: every such timing law is proved equal to the identity. It closes the proposed nonidentity timing-block branch; it does not produce UE by itself.

## Lean handoff summary

The unchecked composition isolates the following additions:

```text
isRetainedTailTimingNash_tail_of_positiveNever

isRetainedTailTimingNash_currentRoot_of_positiveNever

nearMinimum_retainedTailFiniteTimingNash_eq_allInfinity

FinFourMinimumAtomProducer.
  retainedTailFiniteTimingNash_eq_allInfinity_eventually
```

The retained-tail recursion must be proved from the mixed-payoff/graft identity; the existing timing-law tail-Nash theorem is only its zero-continuation analogue. The Fin4 adapter must explicitly construct the punishment profiles and identify hazard-word joint survival with the product of mixed-law Never masses.

## Scope and nonclaims

- This is a no-go for exact finite timing Nashification, not a proof of terminal approximants or UE.
- It does not exclude constrained, approximate, correlated, or deliberately non-Nash finite controllers.
- It does not turn cumulative suffix-cap charge into prescribed-payoff charge.
- It does not consume observer rotation or cross-coordinate cap leakage.
- The Fin4 adapter and retained-tail recursion are reviewed ordinary mathematics, not yet Lean-checked declarations.
