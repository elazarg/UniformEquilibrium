# A single dominant anchor gives an unrestricted stationary escape

**Owner:** CODEX_EULER  
**Status:** independently reviewed and exported as
[`SINGLE_ANCHOR_INDUCED_NASH_ARBITRARY_COMPLETION_ESCAPE.md`](../exports/SINGLE_ANCHOR_INDUCED_NASH_ARBITRARY_COMPLETION_ESCAPE.md);
not yet Lean-checked as a packaged theorem  
**Question:** after the persistent-pair no-go, how much of the first target
pair must a two-target-pair incentive gadget actually change?

## 1. Result

Let `I` be a nonempty finite player set, fix `a in I`, and put
`F = I \ {a}`.  Let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow \mathbb R^I
\]

be an arbitrary quitting reward table.  Form the finite binary game on `F`
in which the anchor `a` quits surely and a free action profile with quitter
set `Q subseteq F` pays free player `j`

\[
 u_j(Q)=r_j(\{a\}\cup Q).
\]

Choose a mixed Nash equilibrium `x` of this induced game and define

\[
 Q_a(x)=\mathbb E_x\,r_a(\{a\}\cup Q).
\tag{1.1}
\]

### Theorem 1.1 (induced-Nash dominant-anchor escape)

Suppose

\[
 Q_a(x)\ge 0,
 \qquad
 Q_a(x)\ge r_a(T)
 \quad(\varnothing\ne T\subseteq F).
\tag{1.2}
\]

Then the stationary profile in which `a` quits surely at every live date and
the free players use the stationary product root `x` is an exact terminal
Nash profile against **all behavioral deviations**.  Consequently its payoff
is a uniform-equilibrium payoff.

The condition is existential in the induced equilibrium: it is enough that
one induced Nash point `x` satisfies (1.2).

### Corollary 1.2 (one literal membership coordinate suffices)

If one player has the literal membership coordinate

\[
 r_a(S)=\mathbf 1_{\{a\in S\}}
 \qquad(\varnothing\ne S\subseteq I),
\tag{1.3}
\]

then the game has an exact stationary terminal Nash profile against all
behavioral deviations and hence a uniform-equilibrium payoff, with every
other player's complete reward coordinate arbitrary.

Indeed every induced Nash point has `Q_a(x)=1`, while every nonempty coalition
excluding `a` pays `a` zero.

### Corollary 1.3 (next two-target-pair architecture)

In the checked six-player architecture with first pair `A={1,2}` and second
pair `B={3,4}`, modifying only one member of `A` is still insufficient if the
other member retains its literal membership coordinate.  The unchanged
member is the anchor in Corollary 1.2; all five remaining coordinates,
including its former partner, the complete second pair, and both passive
players, may be changed arbitrarily.

Thus a viable completion in this architecture must change **both** first-pair
coordinates away from literal membership.  More generally, it must avoid the
following dominant-anchor screen for every candidate anchor `a`: for every
induced complement Nash `x`, either

\[
 Q_a(x)<0
 \quad\text{or}\quad
 r_a(T)>Q_a(x)\text{ for some nonempty }T\subseteq I\setminus\{a\}.
\tag{1.4}
\]

Equation (1.4) is a necessary architecture condition, not a producer of the
two target masses.  In particular, it applies to the requested fixed-gap
table because the checked terminal-gap equivalence turns such a gap into
nonexistence of any uniform-equilibrium payoff.

## 2. Proof against unrestricted deviations

Let `q` be the stationary root with `q_a=1` and free marginals `x`.

### 2.1 Free players

Fix `j in F` and replace its complete behavioral strategy arbitrarily.  The
anchor still quits at date zero with probability one, so only `j`'s date-zero
Quit/Continue choice can affect its payoff.  Conditional on either pure
choice, the payoff is exactly the corresponding pure-action payoff in the
finite induced game.  A random date-zero action is a convex combination of
the two.  Nash optimality of `x` therefore bounds every behavioral
replacement of `j` by its prescribed payoff.

### 2.2 The anchor

Now replace the anchor by an arbitrary behavioral strategy and keep all free
players stationary at `x`.  At every live history, before current actions are
realized, the free quitter set again has the same product law as `Q` in
(1.1).

If the anchor quits at that date, its conditional expected payoff is exactly
`Q_a(x)`.  If it continues and a nonempty free coalition `T` quits, its payoff
is `r_a(T)<=Q_a(x)`.  If everybody continues, the same experiment restarts.
If nobody ever quits, its payoff is zero, again at most `Q_a(x)`.

Here is the exact cap calculation.  Write `O` for the probability that every
free player Continues and `C` for the unconditional contribution of nonempty
free quitter coalitions to the anchor's payoff.  If `O<1`, the Never endpoint
is

\[
 N_a(x)=\frac{C}{1-O}\le Q_a(x),
\]

because every reward averaged in `C/(1-O)` is at most `Q_a(x)`.  The Quit
endpoint is exactly `Q_a(x)`, hence the full unilateral cap
`max(Q_a(x),N_a(x))` equals `Q_a(x)`.  If `O=1`, all free players Continue
surely and the full-rate boundary cap is
`max(0,r_a({a}))=Q_a(x)`.  This checks both stationary-cap branches without
any contraction assumption.  The checked theorem
`quittingTerminalPayoff_update_stationary_le_fullRateUnilateralCap` now bounds
every arbitrary behavioral replacement by `Q_a(x)`.  The prescribed profile
pays `a` exactly `Q_a(x)`, so the bound is tight.

### 2.3 Uniform-payoff conclusion

Sections 2.1--2.2 prove exact terminal Nash in the unrestricted behavior
class.  The checked terminal-to-uniform compiler
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` then gives a
uniform-equilibrium payoff.  Equivalently, the anchor calculation proves

\[
 \operatorname{FullCap}_a(q)\le Q_a(x),
\]

and the induced Nash inequalities prove the analogous bounds for each free
player, so
`isεAsymptoticNash_stationary_iff_fullRateUnilateralCap_le` applies with
`epsilon=0`.

## 3. Why this is strictly stronger than the persistent-pair theorem

The reviewed persistent-base escape requires at least two sure base members;
then a deviating base member is preempted at date zero by another base member.
The present theorem permits a singleton base.  The anchor can postpone
quitting, so its complete stopping problem must be controlled.  Condition
(1.2) does exactly that: every preemption payoff and Never are below the
constant payoff from quitting at any live date.

For literal membership, the argument is especially rigid: every terminal
outcome pays the anchor either zero or one, while prescribed sure Quit pays
one.  No timing or diffuse-clock deviation can improve on it.

Theorem 1.1 also allows substantial changes to the anchor coordinate.  It
need not be a membership indicator, and its rewards on coalitions containing
`a` may vary arbitrarily; only the induced expectation and the excluded-face
upper bounds in (1.2) matter.

## 4. Boundary and falsification tests

### 4.1 All free players Continue

If `x` is the all-Continue induced Nash point, then
`Q_a(x)=r_a({a})`.  The anchor may quit at any finite time or Never.  The
boundary branch of `quittingStationaryFullRateUnilateralCap` is
`max(0,r_a({a}))`, which equals `Q_a(x)` under (1.2).

### 4.2 Free absorption before the anchor

The argument does not assume that the free root contracts.  When a nonempty
free coalition preempts, its realized reward to `a` is bounded pointwise by
`Q_a(x)`.  Hence conditioning on the first free absorption cannot increase
the anchor's value.

### 4.3 Mixed induced equilibrium

No pure free action is selected.  The finite induced game may be
matching-pennies-like.  The proof uses only existence of a mixed Nash and the
stationarity/product law used to define `Q_a(x)`.

### 4.4 The hypothesis is not automatic after both first coordinates change

If `Q_a(x)<0`, Never is a profitable anchor deviation.  If some excluded
coalition pays more than `Q_a(x)`, delaying can be profitable when the free
players realize that coalition.  Thus the proof does not eliminate arbitrary
two-pair tables; it identifies the precise preemption/negative-value escape
that the next architecture must deliberately create for every possible
anchor.

## 5. Exact source and novelty audit

Inspected:

- `quittingPersistentBaseNashSet_nonempty`,
  `isNash_of_mem_quittingPersistentBaseNashSet`, and
  `quittingPersistentBaseRoot_free_purePayoff_le` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`;
- `quittingStationaryFullRateUnilateralCap` and
  `quittingTerminalPayoff_update_stationary_le_fullRateUnilateralCap`, and
  `isεAsymptoticNash_stationary_iff_fullRateUnilateralCap_le` in
  `UniformEquilibrium/Quitting/Stationary/FullRateStationaryVerifier.lean`;
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`;
- the persistent-base semantic compilers in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`
  and `PersistentBaseSemanticDispatch.lean`; and
- the six-player target definitions and existing pure-target lock in
  `UniformEquilibrium/Quitting/Paths/SixPlayerOnePairMassTargetLock.lean`.

The existing persistent-base certificate requires base cardinality at least
two and therefore does not package Theorem 1.1.  The existing pure-target lock
requires outsider join signs at the selected pure target and does not allow
the arbitrary complement re-equilibration used here.  A narrow symbol/phrase
search found no checked singleton-anchor theorem with the induced-Nash
dominance condition (1.2).

## 6. Scope and next test

This is an unrestricted-strategy impossibility theorem for a strictly larger
two-target-pair completion class.  It is not an all-behavior gap table and it
does not solve the general incentive-gadget question.

The next viable architecture must modify both coordinates of the first pair
so that every induced complement equilibrium exposes either a negative
sure-Quit value or a strictly better excluded-face preemption reward, while
still preserving the checked first-pair mass and leftover inequalities.  The
sharp next finite test is therefore to ask whether those two necessary anchor
failures are compatible, in one complete rational table, with the existing
`31/66` ledger for both members of the first pair.
