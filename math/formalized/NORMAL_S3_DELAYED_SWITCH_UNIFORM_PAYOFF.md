# Punishment-normal sequentially perfect absorption yields a uniform payoff

Author: `CODEX_SOURCE_GATE`

Independent reviews:
[CODEX_STRENGTHEN](../feedback/CODEX_SOURCE_GATE__CHRONOLOGICAL_C1_C2_CAPACITY_ADAPTER__BY_CODEX_STRENGTHEN.md)
and
[CODEX_ADVERSARY](../feedback/CODEX_SOURCE_GATE__CHRONOLOGICAL_C1_C2_CAPACITY_ADAPTER__BY_CODEX_ADVERSARY.md).

This packet is a reviewed ordinary-mathematics proof.  The delayed-switch
theorem itself has not yet been checked in Lean.  The phase-switch consumers
and the other named declarations used below are checked under their stated
imports.

## Exact statement

Let \(I\) be a nonempty finite player set.  At each live date, every player
independently chooses Continue or Quit.  The first nonempty coalition
\(S\subseteq I\) of players choosing Quit ends the game and pays
\(r(S)\in\mathbb R^I\).  If every player Continues forever, the payoff is
zero.  Behavioral strategies may depend on the complete public history and
may use private randomization.

For player \(i\), let

\[
 a_i=r_i(\{i\})
\]

be its solo-Quit payoff.  Let \(\chi_i\) be its behavioral punishment value:
the infimum, over opponent profiles, of player \(i\)'s best-response terminal
payoff.  Assume every player is punishment-normal,

\[
 \chi_i\le a_i\qquad(i\in I).                              \tag{1}
\]

Assume branch S.3: for every \(\eta>0\), there is a sequence
\(x=(x_t)_{t\ge0}\) of independent product rows such that:

1. the sequence is completely absorbing,
   \[
   \prod_{t<n}\prod_{i\in I}x_{t,i}(C)\longrightarrow0;
   \]
2. writing \(V_t^i\) for player \(i\)'s terminal payoff from the literal
   sequence starting at date \(t\), and writing \(Q_t^i,C_t^i\) for its
   payoffs from forcing respectively Quit or Continue at row \(t\) and then
   following the literal continuation, every row is \(\eta\)-perfect:
   \[
   Q_t^i\le V_t^i+\eta,
   \qquad C_t^i\le V_t^i+\eta,                             \tag{2}
   \]
   and every endpoint used with positive probability is at least
   \(V_t^i-\eta\).

Then there is one fixed payoff \(v\in\mathbb R^I\) which is a uniform-
equilibrium payoff of the quitting game.  Equivalently, for every requested
accuracy there is one behavioral profile, independent of the later horizon,
whose expected payoff is close to \(v\) and whose gain from every unilateral
behavioral replacement is small at every sufficiently long finite horizon.

The same conclusion follows if branch S.3 is supplied in its checked
equivalent well-supported form
`QuittingWellSupportedAbsorbingSequenceExistence`.

## Conjecture-facing change

The existing checked support-witness compiler asks for punishment-value
individual rationality at an already selected survival switch.  S.3 alone
does not supply that field, and exact rowwise perfection alone does not imply
global Nash optimality.  This result removes the missing individual-
rationality hypothesis when all players are punishment-normal.

The new step is a finite delayed-switch dichotomy.  After the first own-
survival crossing, either the selected player's continuation reaches its
punishment floor within a bounded number of rows, or every failure to do so
spends a fixed amount of opponent-absorption probability.  In the latter
case, the selected player's deleted survival becomes small.  The initial
own-survival crossing already makes every other player's deleted survival
small.

In particular,
`FinFourQuantitativeFullSupportHardResidual.all_punishmentNormal` supplies
(1).  Hence a four-player hard residual cannot also satisfy S.3.  The theorem
does not construct S.3 from arbitrary game data or from the hard residual.

## Definitions and assumptions

Fix a root sequence \(x\).  Write

\[
 q_{i,t}=x_{t,i}(Q),
 \qquad
 S_i(u,n)=\prod_{k<n}(1-q_{i,u+k})                         \tag{3}
\]

for player \(i\)'s own survival during the \(n\) rows starting at \(u\).
Write

\[
 D_i(u,n)=
 \prod_{k<n}\prod_{j\ne i}(1-q_{j,u+k})                  \tag{4}
\]

for survival after deleting player \(i\), and

\[
 J(u,n)=\prod_{k<n}\prod_j(1-q_{j,u+k})                  \tag{5}
\]

for joint survival.  These are finite-product probabilities on the unique
live all-Continue history.  In particular,

\[
 D_i(0,u+n)=D_i(0,u)D_i(u,n).                             \tag{6}
\]

Let

\[
 M=\max_{S,i}|r_i(S)|.
\]

Thus every finite terminal payoff lies in \([-M,M]\), and the Never payoff
zero lies there as well.

At row \(t\), let the continuation vector after the row be \(V_{t+1}\).
The literal terminal recursion is

\[
 V_t=F_{x_t}(V_{t+1}),                                    \tag{7}
\]

which is the declaration
`quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector`.
Consequently the mixed successor payoff appearing in the row-perfectness
predicate is exactly \(V_t\), so the first inequality in (2) has the displayed
orientation.

The support-local error of the sequence is at most

\[
 \alpha=2\eta,                                             \tag{8}
\]

by `supportApproxNash_of_quittingRowεPerfect`.  For player \(i\), define the
finite ledger

\[
 L_i(n)=\sum_{t<n}(C_t^i-V_t^i).                          \tag{9}
\]

The support condition implies the checked one-row bound

\[
 C_t^i-V_t^i\le\alpha q_{i,t}.                            \tag{10}
\]

It also gives Quit regret at most \(\alpha\) at every row.

## Proof

### 1. Parameter choice

Fix a desired terminal Nash error \(\varepsilon>0\), put
\(B=\max\{1,2M\}\), and choose

\[
 0<d\le
 \min\left\{\frac12,\frac B2,
              \frac{\varepsilon}{4(3+7M)}\right\}.       \tag{11}
\]

Set

\[
 \theta=r_0=\ell=\zeta=d,
 \qquad c=\frac{r_0}{2B}.                                \tag{12}
\]

Then \(0<\theta<1\), \(0<c<1\), and

\[
 \ell+r_0+\zeta+7M\theta
 =d(3+7M)\le\varepsilon/4.                               \tag{13}
\]

Choose \(L\in\mathbb N\) such that

\[
 (1-c)^L\le\theta.                                       \tag{14}
\]

Only after \(L\) is fixed, choose \(\eta>0\) such that

\[
 \eta\le r_0/2,
 \qquad 2\eta\le\ell\theta,
 \qquad (2L+4)\eta<\varepsilon/2.                        \tag{15}
\]

Invoke S.3 at this \(\eta\) and put \(\alpha=2\eta\).  The order of choices
is noncircular.

### 2. The first support-survival switch

Complete absorption and finiteness of \(I\) imply that some own-survival
product crosses \(\theta\).  Let \(s\) be the first integer for which there
is a player \(p\) with

\[
 S_p(0,s)\le\theta.                                      \tag{16}
\]

Choose such a \(p\).  Before \(s\), every player's own survival is larger
than \(\theta\).  The elementary product-sum inequality

\[
 S_i(0,n)\left(1+\sum_{t<n}q_{i,t}\right)\le1            \tag{17}
\]

and (10), together with \(\alpha\le\ell\theta\), give the
clock-collapse bounds

\[
 L_i(n)\le\ell+\alpha\quad(n\le s),
 \qquad
 \operatorname{QuitRegret}_i(t)\le\alpha\quad(t<s).      \tag{18}
\]

This is exactly the content used from
`quittingSupportApproxNash_survivalSwitchPackage`.

### 3. A bad row spends opponent absorption

Call a date \(t\ge s\) good for \(p\) if

\[
 V_t^p\ge\chi_p-r_0.                                     \tag{19}
\]

Suppose instead that \(t\) is bad.  By the Bellman identity (7) and the
no-profitable-Quit clause of row perfectness,

\[
 Q_t^p\le V_t^p+\eta.
\]

Using badness, normality, and \(\eta\le r_0/2\),

\[
 Q_t^p\le V_t^p+\eta
       <\chi_p-r_0+\eta
       \le a_p-r_0/2.                                    \tag{20}
\]

Let \(A_{p,t}\) be the probability that at least one opponent of \(p\)
Quits at row \(t\).  When every opponent Continues, forcing \(p\) to Quit
pays \(a_p\); on the complementary event both payoffs are bounded by \(M\).
Therefore

\[
 |Q_t^p-a_p|\le2M A_{p,t}\le B A_{p,t}.                  \tag{21}
\]

Equations (20)--(21) imply

\[
 A_{p,t}>\frac{r_0}{2B}=c.                               \tag{22}
\]

When \(M=0\), the same inequalities say that a bad row is impossible; no
division by \(M\) is used.

### 4. The finite delayed-switch dichotomy

Inspect exactly the \(L\) rows

\[
 s,s+1,\ldots,s+L-1.
\]

If one is good, let \(T\) be the first good date.  Otherwise set
\(T=s+L\).  Since each additional row contributes at most \(\alpha\) to
each ledger, (18) gives, in either case,

\[
 L_i(n)\le\ell+(L+1)\alpha\quad(n\le T),
 \qquad
 \operatorname{QuitRegret}_i(t)\le\alpha\quad(t<T).      \tag{23}
\]

In the all-bad case, every opponent-Continue factor for \(p\) in these
\(L\) rows is less than \(1-c\).  With the exact start/fuel convention (4),

\[
 D_p(s,L)\le(1-c)^L\le\theta.                            \tag{24}
\]

The product split (6) then gives

\[
 D_p(0,T)=D_p(0,s)D_p(s,L)\le\theta.                     \tag{25}
\]

For a different player \(i\ne p\), its deleted-survival product contains
all of player \(p\)'s own Continue factors.  Hence

\[
 D_i(0,T)\le S_p(0,T)\le S_p(0,s)\le\theta.              \tag{26}
\]

Thus (25) is supplied by the bad-row opponent clock, while (26) is supplied
by the initial own-survival clock.  These are distinct reach arguments.

### 5. Consumption when a good row occurs

At a good \(T\),

\[
 \chi_p\le V_T^p+r_0.                                    \tag{27}
\]

The checked near-punishment selection
`exists_quittingTargetClosedTail_le_of_punishmentValue_le` supplies one
actual target-closed tail \(y\).  Its opponents are stationary; the target
uses an actual cap-attaining, possibly time-dependent response.  It satisfies

\[
 \operatorname{Val}_p(y,0)\le V_T^p+r_0+\zeta.           \tag{28}
\]

Target closedness alone caps only \(p\).  Apply explicitly
`exists_quittingPhaseSwitchPunishCap_of_targetClosedTail` to the same tail
\(y\).  It gives one cap vector \(K\) such that every player's arbitrary
hazard deviation against this same tail is at most \(K_i\), with

\[
 K_p=\operatorname{Val}_p(y,0),
 \qquad K_i\le M\quad(i\in I).                           \tag{29}
\]

The marked player's joint reach satisfies

\[
 J(0,T)\le S_p(0,T)\le S_p(0,s)\le\theta,                \tag{30}
\]

and, for every \(i\ne p\), the deleted reach satisfies (26).

Use the literal phase-switch profile which follows \(x_0,\ldots,x_{T-1}\)
and then follows \(y\).  The checked theorem
`isεAsymptoticNash_quittingPhaseSwitchProfile_marked`, with

\[
 \begin{aligned}
 \text{ledgerCap}&=\ell+(L+1)\alpha,\\
 \text{quitRegretCap}&=\alpha,\\
 \text{continuationSlack}&=r_0+\zeta,\\
 \text{targetJointReach}&=\text{otherReach}=\theta,
 \end{aligned}                                            \tag{31}
\]

bounds the marked player's regret by

\[
 \ell+(L+2)\alpha+r_0+\zeta+2M\theta,                    \tag{32}
\]

and every unmarked player's regret by at most

\[
 \ell+(L+2)\alpha+5M\theta
 +\theta(\max\{K_i,0\}+M)
 \le\ell+(L+2)\alpha+7M\theta.                           \tag{33}
\]

### 6. Consumption when all inspected rows are bad

Now (25)--(26) give \(D_i(0,T)\le\theta\) for every player.  Attach the
explicit all-Continue root sequence as the tail.  Against that tail, any
player's arbitrary hazard deviation has terminal value at most \(M\), so use
the constant tail cap

\[
 K_i=M
\]

and punishment error zero.

The checked truncated-prefix estimate
`quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_plan_ledger_le`
applied to (23) gives plan error

\[
 \ell+(L+2)\alpha+5M\theta.                               \tag{34}
\]

The ordinary checked consumer
`isεAsymptoticNash_quittingPhaseSwitchProfile` adds at most

\[
 \theta(\max\{M,0\}+M)=2M\theta,                          \tag{35}
\]

because \(M\ge0\).  The total regret is therefore at most

\[
 \ell+(L+2)\alpha+7M\theta.                               \tag{36}
\]

### 7. Error conclusion and fixed payoff

Since \((L+2)\alpha=(2L+4)\eta<\varepsilon/2\), equations
(13), (32)--(33), and (36) are all strictly below \(\varepsilon\).  Thus for
every \(\varepsilon>0\) there is a terminal \(\varepsilon\)-Nash profile.
The two phase-switch consumers quantify over an arbitrary behavioral strategy
of the deviating player, so this conclusion covers unrestricted unilateral
behavioral replacement.

Finally,
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
selects a convergent subsequence of the resulting terminal payoff vectors and
returns one fixed uniform-equilibrium payoff \(v\).  The S.3 sequence, switch,
marked player, and tail may depend on \(\varepsilon\); the selected payoff
does not depend on the later requested uniform accuracy.

## Probability, deviation, and uniformity audit

- All prescribed rows use the independent product randomization of the
  quitting model.  The constructed profile is a literal finite prefix of one
  S.3 root sequence followed by one actual tail.
- Equations (3)--(6), (24)--(26), and (30) are finite-product probabilities
  on the unique live public history.  No conditional probability at a
  zero-reach history is used.
- Both phase-switch consumers quantify over an arbitrary behavioral strategy
  for the deviating player.  Their live-hazard reduction covers stationary
  and nonstationary deviations, finite and unbounded stopping, arbitrarily
  late Quit, and Never.
- The profiles may vary with the terminal error.  The checked terminal-to-
  uniform selection fixes the payoff before the later equilibrium accuracy
  and horizon threshold are chosen.

## Boundary tests

1. **One player.**  Opponent absorption is zero.  A bad row would contradict
   (20)--(21), so the construction necessarily enters the good branch.
2. **Zero reward bound.**  When \(M=0\), \(B=1\) and all parameter choices
   remain valid.  A bad row is again impossible before any division.
3. **Abnormal exact-row regression.**  In
   `ErrorExponentRefutation.lean`, a two-player sequence absorbs at its first
   row and is exactly row-perfect but has terminal regret one.  The affected
   player has solo payoff \(-1\) and punishment value zero, so (1) fails.
   This shows that normality is essential to the bad-row charge implication
   used by this compiler.  It does not show that normality is necessary for
   uniform-payoff existence: that regression itself has a stationary
   equilibrium.
4. **Slow absorption.**  No uniform absorption floor is assumed.  The first
   clock may occur arbitrarily late.  Only the number \(L\) of rows inspected
   after that crossing is bounded.

## Source correspondence and novelty

The S.3 definitions are
`QuittingSequentiallyεPerfectAbsorbingExistence` and
`QuittingPlayerRowεPerfect` in
`UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean`.  The
equivalent support-local form and its factor-two adapter are in
`UniformEquilibrium/Quitting/Classification/Existence/WellSupportedAbsorbingSequence.lean`.

The checked support-witness consumer
`HasQuittingCompletelyAbsorbingSupportWitnessPackage` assumes punishment-
value individual rationality at the already selected switch.  The present
theorem does not assume that field.  Its new ordinary mathematics is (20)--
(26): normality turns every failure of individual rationality into opponent
absorption, and a finite delayed scan either finds a good boundary or clears
all deleted-survival clocks.

The terminology S.3 comes from Solan and Vieille, *Quitting games*,
Mathematics of Operations Research 26 (2001), and from Ashkenazi-Golan,
Krasikov, Rainer, and Solan, *Absorption paths and equilibria in quitting
games*, Mathematical Programming (2022).  This proof does not use the latter
paper's printed Theorem 3.5.  Its unqualified conversion of sequential
perfection to a fixed error exponent is refuted by the checked declaration
`not_quittingSequentialPerfectionErrorExponent` in
`UniformEquilibrium/Quitting/Classification/ErrorExponentRefutation.lean`.
The present normal delayed-switch result is neither that false conversion nor
the 2001 stationary-alternative statement.

The two independent reviews explicitly attempted to falsify the local
charge, the two distinct reach arguments, the behavioral strategy scope, the
one-player case, and the \(M=0\) case.  Both passed the corrected theorem.

## Adapter and consumer

The actual-data adapter is direct:

\[
 \text{S.3 root sequence at selected }\eta
 \longmapsto
 \text{finite delayed-switch prefix and actual tail}.     \tag{37}
\]

No compact cap atlas, chronological limit, shared cross-accuracy ancestry,
or exactification of approximate rows is used.  In the good branch, the tail
is the checked target-closed punishment tail; in the all-bad branch, it is the
explicit all-Continue sequence.

The downstream semantic consumer is
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
It consumes the terminal approximate Nash profiles produced at every error
and returns the fixed uniform payoff.

## Lean handoff

A narrow formalization can use four declarations.

```text
opponentAbsorptionMass_gt_of_normal_of_rowPerfect_of_not_individualRational

exists_normalSupportDelayedSwitch

exists_terminalNash_of_all_normal_of_sequentiallyPerfectAbsorbing

exists_uniformEquilibriumPayoff_of_all_normal_of_sequentiallyPerfectAbsorbing
```

The delayed-switch structure should return explicit \(p,s,T\), the bounds
\(s\le T\le s+L\), ledger and Quit-regret bounds through \(T\), the target
joint and unmarked deleted reaches, and the disjunction

```text
quittingPunishmentValue reward p <= V T p + r0
or
forall i, quittingOpponentSurvivalWeight roots i 0 T <= theta.
```

The all-bad proof should use
`quittingOpponentSurvivalWeight roots p s L` and the exact product-split
lemma, rather than encoding an endpoint where a fuel argument is expected.

Likely checked dependencies are:

- `supportApproxNash_of_quittingRowεPerfect`;
- `quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector`;
- `abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass`;
- `quittingSupportApproxNash_survivalSwitchPackage`;
- `quittingOpponentSurvivalWeight_add`;
- `exists_quittingTargetClosedTail_le_of_punishmentValue_le`;
- `exists_quittingPhaseSwitchPunishCap_of_targetClosedTail`;
- `quittingRootSequenceHazardTerminalValue_quittingTruncatedRoots_le_of_plan_ledger_le`;
- `isεAsymptoticNash_quittingPhaseSwitchProfile_marked`;
- `isεAsymptoticNash_quittingPhaseSwitchProfile`; and
- `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`.

The first two proposed declarations contain the new mathematics.  The latter
two should reuse the checked strategic consumers and must not encode terminal
Nash or the uniform payoff as input structure fields.

## Scope and nonclaims

- This is a special-case existence theorem conditional on S.3 and
  punishment normality.  It does not prove that every quitting game satisfies
  S.3.
- It rules out S.3 inside a putative all-normal hard residual, but does not by
  itself eliminate that residual.
- It does not assert that an arbitrary sequentially approximately perfect
  absorbing profile is itself approximately Nash; the output modifies the
  profile after a finite prefix.
- It does not assume or prove stationary punishment for the target.  Only the
  target tail's opponents are stationary; the target response may be
  time-dependent.
- The new theorem is not yet Lean-checked.  No `L`, `A`, or `C` seal is
  claimed for it.

## Lean formalization record

Pre-formalization packet SHA-256:
`05cb9fb3186488ecf20e5440b07d9c2613cd6517b746ebbe15c2bdc727258be9`.

The implementation landed in commit
`26ecaa9f881562388f2c9861df3c6bf0c51dceb2`.

The coordinate-bound same-tail cap is
`exists_quittingPhaseSwitchPunishCap_of_targetClosedTail_of_coordinateBound`
in
`UniformEquilibrium/Quitting/Paths/SupportWitnessReduction.lean`.
The original canonical-bound declaration
`exists_quittingPhaseSwitchPunishCap_of_targetClosedTail` retains its public
type and delegates to that theorem.

The generic delayed-switch compiler is in
`UniformEquilibrium/Quitting/Classification/Existence/NormalSequentiallyPerfectAbsorbingUniformPayoff.lean`.
Its principal declarations are
`opponentAbsorptionMass_gt_of_normal_of_rowPerfect_of_not_individualRational`,
`quittingLedger_add_le_of_supportApproxNash`,
`quittingOpponentSurvivalWeight_le_pow_of_absorption_gt`,
`NormalSupportDelayedSwitch`,
`exists_normalSupportDelayedSwitch`,
`exists_isεAsymptoticNash_of_normalSupportDelayedSwitch`,
`exists_terminalNash_of_all_normal_of_sequentiallyPerfectAbsorbing`,
`exists_terminalNash_of_all_normal_of_wellSupportedAbsorbing`,
`exists_uniformEquilibriumPayoff_of_all_normal_of_sequentiallyPerfectAbsorbing`,
and
`exists_uniformEquilibriumPayoff_of_all_normal_of_wellSupportedAbsorbing`.

The Fin4 companion is in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/NormalSequentiallyPerfectAbsorbingUniformPayoff.lean`.
Its checked declarations are
`FinFourQuantitativeFullSupportHardResidual.exists_uniformEquilibriumPayoff_of_sequentiallyPerfectAbsorbing`,
`FinFourQuantitativeFullSupportHardResidual.exists_terminalNash_of_wellSupportedAbsorbing`,
`FinFourQuantitativeFullSupportHardResidual.exists_uniformEquilibriumPayoff_of_wellSupportedAbsorbing`,
`FinFourQuantitativeFullSupportHardResidual.not_sequentiallyPerfectAbsorbing_of_no_uniformEquilibriumPayoff`,
and
`FinFourQuantitativeFullSupportHardResidual.not_wellSupportedAbsorbing_of_no_uniformEquilibriumPayoff`.

The quantitative compiler retains the bad-row charge
`r0 / (2 * max 1 (2 * M))`, the corresponding geometric survival bound,
and the exact final `7 * M` reach coefficient under a supplied coordinate
reward bound.

Evidence seals are `M` and `L`, with source-conditional `A` and conditional
terminal/uniform-payoff `C`. The adapter starts from a supplied
`QuittingSequentiallyεPerfectAbsorbingExistence` or equivalent
`QuittingWellSupportedAbsorbingSequenceExistence`; no checked theorem here
produces either interface from arbitrary game data, approximate equilibria,
the corrected Simon fourth output, or a Fin4 hard residual.

The implementation does not prove unconditional S.3, eliminate the Fin4 hard
residual without the explicit source hypothesis, prove that the original
source profile is terminal Nash, produce a stationary equilibrium or
stationary target response, extend to general stochastic games, or close
AGKRS Theorem 3.4. The finite prefix, selected player, source sequence, and
punishment tail may depend on the requested error; only the final payoff is
fixed by terminal-to-uniform compact selection.
