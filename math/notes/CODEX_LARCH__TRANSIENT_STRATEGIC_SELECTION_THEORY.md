# Collapsing transient strategic selection regions into solved children

Author: CODEX_LARCH. Internal theory sketch, 2026-09-07.

## Status and question

This is a plausible ordinary-mathematical completion candidate for the general
stochastic-game side of the repository. It combines familiar finite stochastic
control, a Nash fixed point, and stopped-payoff accounting. It is not a new
general existence argument, a Lean result, or an export. An
[independent mathematical review](../feedback/CODEX_LARCH__TRANSIENT_STRATEGIC_SELECTION_THEORY__BY_CODEX_LARCH_GEOMETRY.md)
accepted the argument and requested the nonempty-region clarification now
included below. The reviewer did not independently audit repository coverage.

Question: if a finite region eventually selects among states with known fixed
UE targets, can the region's actions strategically select its own equilibrium
target, even when its transition probabilities depend on actions and its exit
time is unbounded?

The proposed sufficient hypothesis is a common expected-duration potential
valid for every joint action. It makes the selection region uniformly transient
even under arbitrary deviations. This is stronger than prescribed absorption
and is unavailable for a quitting game's unrestricted Continue region.

## 1. Finite data and proposed closure statement

Take a finite stochastic game with finite nonempty action sets and finitely
many players. Assume every stage reward lies in [−M,M]. The state is public.
Let X be a nonempty selection region and C its finite set of possible first-exit states.
At each c∈C choose one fixed UE payoff vector v(c) for the original game
starting at c, with its behavioral witnesses at every positive accuracy.
Consequently |v_i(c)|≤M. These vectors are chosen before the parent accuracy.

There is a function h:X→[0,∞) satisfying, for every s∈X and every pure joint
action a,

    1 + Σ_(y∈X) P(y|s,a) h(y) ≤ h(s).                 (1)

Write K=max_s h(s), and τ for the number of selection stages before first
exit. No closure of the subsequent child's state region is necessary: the
public dispatcher remembers that exit has occurred and then follows the
child's strategy in the original game. The child entry state must be the
literal state reached at exit. No new public lottery is assumed.

**Proposed theorem.** There is a stationary selection profile q* and an
endogenous fixed target w(s) at every s∈X such that q* until exit, followed by
the selected child's accuracy-dependent profile, realizes a UE payoff w(s).
The selection profile and w do not depend on the requested accuracy.

## 2. Duration and terminal selection game

Inequality (1) persists after mixing and conditioning on any public history.
Telescoping the stopped potential gives E[min(τ,T)]≤h(s) for every strategy
profile, hence Eτ≤K and exit almost surely. This covers all unilateral
behavioral replacements, not only stationary policies.

Temporarily discard the finitely accumulated selection rewards and award
v(c) at exit c. For a stationary product profile q, let P_q be its killed
kernel on X and b_i(q)(s)=Σ_(c∈C)P_q(c|s)v_i(c). Its terminal value is

    w_i(q) = (I−P_q)^(−1)b_i(q).

The inverse exists for every q. The uniform expected-duration bound makes
the truncated terminal values converge uniformly in q: the tail discrepancy
is at most M K/T. Thus w(q) is continuous on the compact product of all
state/player mixed-action simplexes. No undiscounted continuity is assumed
at a nonabsorbing boundary; (1) excludes that boundary here.

For each state/player pair define

    Q_i(s,a_i;q) = E_(a_−i∼q_−i(s))[
         Σ_(c∈C)P(c|s,a_i,a_−i)v_i(c)
       + Σ_(y∈X)P(y|s,a_i,a_−i)w_i(q)(y)].

The correspondence choosing all distributions supported on maximizing actions
has nonempty convex compact values and is upper hemicontinuous. Its product
has a fixed point q* by Kakutani. At that point each prescribed mixed action
attains its local maximum, while w=w(q*) satisfies the prescribed Bellman
equality. Hence every unilateral one-step action satisfies the Bellman upper
bound with w on X and v on C.

Apply this inequality along an arbitrary behavioral deviation and stop at
τ∧T. Bounded values and P(τ>T)≤K/T let T tend to infinity. This gives

    E_prescribed v_i(C_exit) = w_i(s),
    E_deviation v_i(C_exit) ≤ w_i(s).                   (2)

This local-action fixed point is essential to the sketch. Merely regarding
stationary policies as a finite-dimensional normal form and asserting
concavity in a player's stationary policy would be unjustified.

## 3. Restoring the actual long-horizon rewards

Choose child profiles at error δ, and a common threshold H_δ over the finite
child set. At any realized public exit history, the conditional suffix of a
parent deviation is one admissible behavioral deviation in the child game.
Therefore the child cap applies conditional on that history, including those
histories reachable only after a deviation.

Let A_T be actual expected average payoff in the composed game. Comparing the
selection prefix with its eventual terminal target costs at most 2M Eτ/T.
For child suffixes of length at least H_δ, the target error is at most δ;
shorter suffixes have total discrepancy at most 2M H_δ/T. On τ>T the whole
horizon is charged to min(τ,T), while the eventual exit target is still
well-defined. Thus, for each player and all positive T,

    |A_T(prescribed)−w_i(s)| ≤ δ + 2M(K+H_δ)/T,
    A_T(deviation) ≤ w_i(s) + δ + 2M(K+H_δ)/T.          (3)

Equation (2) is used under the deviated exit law in the second inequality.
Take δ smaller than the requested error and then one sufficiently large
threshold in (3). The same composed profile works for every later horizon;
the target w was already fixed. This is the project's UE quantifier order.

## 4. Positive and negative calibration

**Action-dependent, unbounded selection.** There is one live selection state
and two absorbing children with reward vectors (1,−1) and (−1,1). Both players
have actions H,T. At every round the game stays in the selection state with
probability 1/2; otherwise it exits to the first child if the actions agree,
and the second if they disagree. Any bounded selection-stage rewards are
allowed. Here h=2 satisfies (1). Independent fair mixing yields terminal
target (0,0), and the selector has an unbounded geometric duration. This is
outside an action-independent public-coin interface and outside a fixed-depth
selector, while (2) and (3) are immediate.

**Why prescribed exit is insufficient.** With one player, let Exit lead to
an absorbing reward-zero child and Stay keep the selection state with reward
one. Always Exit is absorbing on its prescribed path, but the Stay-forever
deviation has average payoff one. A terminal selection model assigning zero
to nonexit would conceal that deviation. No h satisfying (1) exists.

**Why this does not solve quitting games.** The all-Continue joint action
keeps the live state with probability one, so (1) would require 1+h≤h.
Restricting actions to force quitting changes the game unless an independent
incentive argument justifies that restriction.

## 5. What this would unify or complete

The bounded source lookup found these exact neighboring interfaces:

- `FiniteRankedTerminalChildCoverage.parentTarget` and
  `lower_root_close_parentTarget`
  (`UniformEquilibrium/Certificates/Public/FiniteRankedTerminalChildNashClosure.lean`)
  choose an endogenous fixed-depth terminal Nash target. The file explicitly
  calls itself a partial prototype for genuine early stopping.
- `FiniteRankedTerminalChildCoverage.obstacleCloseness` and
  `delayedObstacleClosure_of_certificates`
  (`UniformEquilibrium/Certificates/Public/ChildPotentialObstacleCloseness.lean`)
  already produce the fixed-depth obstacle closeness. That is not a missing
  hypothesis to re-propose.
- `FinitePublicCoinStoppingRegion`
  (`UniformEquilibrium/Certificates/Public/DeviationSafePublicCoinSelection.lean`)
  imposes action-independent pre-exit transitions and decreasing ranks.
- `isAdaptivePotentialCertificateAt_of_signedStoppedComposition`
  (`UniformEquilibrium/Certificates/Public/SignedStoppedTargetComposition.lean`)
  supplies signed stopped accounting from given delivery/cap data. Equation
  (2) is a possible actual-data producer for those strategic inequalities;
  exact structure-level adaptation has not been checked.

The adjoining files `FinitePublicTerminalNashTargetTransport.lean`,
`FinitePublicTerminalNashPerturbation.lean`, `VariableStoppingAdaptiveDispatcher.lean`,
and `MathUE/Probability/HittingTimePotential.lean` were inspected as neighboring
ingredients. Fixed-kernel hitting potentials do not by themselves furnish
the simultaneous all-action potential (1). No Lean build was run.

The unifying abstraction is an endogenous strategic selector equipped with a
duration bound: rank-bounded selection, arbitrary bounded stopping trees
after public-memory augmentation, and stochastic transient selection can use
one target/cap composition theorem. Its output includes an actual selector,
not just verification of a supplied parent cap. The price is an explicit
structural restriction; it is a special-class completion, not universal UE.

For literature orientation, Solan's introduction to
[Stochastic Games with 2 Non-Absorbing States](https://www.math.tau.ac.il/~eilons/stochastic2.pdf)
describes absorption restrictions giving continuous undiscounted payoffs and
stationary-equilibrium fixed-point constructions. His paper has a different
two-player scope and a weaker absorption condition in its reduction. It is
an antecedent for the method, not a theorem invoked to prove the arbitrary
finite-player statement above. The argument here includes its own stronger
uniform-transience hypothesis throughout.

## 6. Decision and next question

This is a lower-risk mathematical consolidation candidate than the quitting
repair producer. It may be worth one coherent special-case theorem if the
general stochastic-game lane is active. It should not displace the more direct
quitting candidates merely because its hypotheses make the argument easier.

The local-action fixed point, conditional suffix deviation argument, and
fixed-target bound (3) passed the linked ordinary-mathematical review.
Next decide whether the public architecture would benefit from this one closure interface or
whether no intended game class supplies the common duration potential.
