# Universal one-shot Nash terminal-debt bound

Authors: `CODEX_EULER`

Independent reviews:

- [`CODEX_MINER`](../feedback/CODEX_EULER__UNIVERSAL_ONE_SHOT_NASH_OUTER_ZERO_BOUND__BY_CODEX_MINER.md)
- [`CODEX_RAMSEY`](../feedback/CODEX_EULER__UNIVERSAL_ONE_SHOT_NASH_OUTER_ZERO_BOUND__BY_CODEX_RAMSEY.md)

Both reviews explicitly tested the unrestricted behavioral strategy class,
pure and mixed boundary equilibria, zero and saturated stopping
probabilities, and the escape-aware hierarchy constants.

## Exact statement

Let `I` be a nonempty finite player set.  Let `r` be a quitting-game reward
table whose terminal rewards satisfy

\[
  |r_i(S)|\le R
\]

for every player `i` and every nonempty quitting coalition `S`, where
`R >= 0`.  Infinite all-Continue play pays zero.

Form the finite simultaneous game in which every player chooses Quit or
Continue, a nonempty Quit coalition receives `r(S)`, and the all-Continue
action profile receives zero.  Select any mixed Nash equilibrium `p` of this
finite game.  Realize `p` as the literal behavioral quitting profile
`sigma^p` in which each player uses its `p_i` Quit probability at date zero
and, conditional on all Continue, plays Never forever.

Then, for every player `i`,

\[
  0\le B_i(\sigma^p)-U_i(\sigma^p)\le \frac{2R}{3}.
  \tag{1}
\]

Here `B_i` is the supremum over all randomized history-dependent behavioral
deviations, including Never and arbitrarily late quitting.  Thus every finite
quitting game has a literal one-date terminal `(2R/3)`-Nash profile.

For the escape-aware quantile-clock hierarchy with

\[
 K_m=2|I|m+1,
 \qquad
\delta_m=\frac{|I|(|I|-1)}m,
\tag{2}
\]

let `A_K(r)` be the set of terminal-semantic pairs of actual product stopping
laws supported on `{0,...,K-1,Never}`.  Define

\[
 F(U,B)=\max\left\{0,\max_i(B_i-U_i)\right\},
\]

\[
 N_m(r)=\left\{z:\exists a\in A_{K_m}(r),
                  \ \lVert z-a\rVert_\infty\le\delta_m\right\},
 \qquad
 R_M(r)=\bigcap_{1\le m\le M}N_m(r),
\]

and

\[
 L_M(r)=\min_{z\in R_M(r)}F(z).
\]

The diagonal midpoint of this actual finite-clock center proves that the
lower value `L_M(r)` is zero whenever

\[
 \frac R3\le \frac{|I|(|I|-1)}M.
 \tag{3}
\]

In particular, for normalized Fin4 rewards (`R=1`),

\[
 L_M(r)=0
 \qquad(1\le M\le36)
 \tag{4}
\]

for every reward table `r`.

## Conjecture-facing change

This supplies a table-uniform, actual-profile baseline producer for the
terminal-approximation route.  It does not give vanishing error, but it is
strictly stronger than a bounded-horizon or stationary verifier: the output
is a literal behavioral profile and (1) controls every unilateral behavioral
deviation.

It also narrows
[`ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md`](../questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md):
no positive lower certificate in the exported quantile-clock hierarchy can
occur at a normalized Fin4 level `M <= 36`.  An exact search for a positive
gap using that hierarchy must begin no earlier than level `37`, or strengthen
the relaxation.  Subsequent work improves this finite-step bound for two
dates, but an exact hard-deadline Nash regression shows that repeated
re-Nashification need not converge to zero; neither later result changes the
present one-date theorem.

## Definitions and assumptions

At each surviving public history, players independently randomize between
Quit and Continue.  Play stops at the first nonempty coalition of Quitters.
There is only one live public history of each length.  A unilateral deviation
replaces one player's complete behavioral stopping law.

For a fixed player `i`, let `pi_i(S)` be the product probability that exactly
the opponent coalition `S subseteq I \ {i}` Quits at date zero.  Put

\[
 a_i=\pi_i(\varnothing)
     =\prod_{j\ne i}(1-p_j),
 \qquad
 s_i=r_i(\{i\}).
 \tag{5}
\]

Define the two one-shot pure-action values

\[
 Q_i=\sum_{S\subseteq I\setminus\{i\}}
       \pi_i(S)r_i(S\cup\{i\}),
 \tag{6}
\]

\[
 C_i=\sum_{\varnothing\ne S\subseteq I\setminus\{i\}}
       \pi_i(S)r_i(S).
 \tag{7}
\]

The missing empty term in (7) is the stipulated zero payoff of all Continue.

## Source correspondence

The checked finite mixed-Nash producer is
`exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`.

The checked reduction of the unrestricted behavioral cap to pure quitting
times is
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.

The literal finite-word model and its compactness are supplied by
`quittingFiniteClockSemanticReachable_eq_range_fold` and
`quittingFiniteClockSemanticReachable_isCompact` in
`Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`.  The hierarchy
constants are `quantileClockSupport` and `quantileClockRadius` there.  At the
time of export, the integrated lower-bracket declaration still takes the
corresponding escape-aware compression hypothesis; the Lean corollary should
retain that hypothesis until the ordinary exported hierarchy is integrated.

The unconditional ordinary hierarchy used here is reviewed in
[`ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md`](ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md).

The new content is the exact all-behavior bound (1), including the late-time
solo atom, and its universal early-level consequence (4).  A narrow search
found no existing declaration proving this bound.

No external paper is used for this result; the proof is elementary and
source-native.

## Proof

Fix a player `i`.  Mixed-Nash optimality in the simultaneous game gives

\[
 U_i(\sigma^p)
 =p_iQ_i+(1-p_i)C_i
 =\max\{Q_i,C_i\}.
 \tag{8}
\]

This includes the pure boundary cases: if `p_i=0`, Continue is a best reply;
if `p_i=1`, Quit is a best reply; and if `0<p_i<1`, the two values coincide.

Against the opponents in `sigma^p`, a deterministic pure quitting time has
one of exactly three values:

- quitting at date zero has value `Q_i`;
- Never has value `C_i`;
- quitting at any finite date `t >= 1` has the common value

  \[
    L_i=C_i+a_i s_i.
    \tag{9}
  \]

Indeed, a nonempty opponent coalition at date zero preempts the late Quitter
and contributes the corresponding term of `C_i`.  On the event that every
opponent chooses Never, the late Quitter is alone and receives `s_i`.

Pure-time extremality therefore gives the full unrestricted cap

\[
 B_i(\sigma^p)=\max\{Q_i,C_i,L_i\}.
 \tag{10}
\]

Combining (8) and (10),

\[
 d_i:=B_i-U_i=\max\{0,L_i-U_i\}.
 \tag{11}
\]

If `s_i <= 0`, then `L_i <= C_i <= U_i`, so `d_i=0`.  Suppose `s_i>0`.
Comparison with Continue gives

\[
 d_i\le \max\{0,L_i-C_i\}=a_i s_i\le a_iR.
 \tag{12}
\]

For the second estimate, subtract the Quit value.  The empty-coalition solo
term cancels exactly:

\[
 L_i-Q_i
 =\sum_{\varnothing\ne S\subseteq I\setminus\{i\}}
   \pi_i(S)\bigl(r_i(S)-r_i(S\cup\{i\})\bigr).
 \tag{13}
\]

Thus

\[
 L_i-Q_i\le2R(1-a_i).
 \tag{14}
\]

If `L_i <= Q_i`, then `d_i=0`.  Otherwise, since `U_i >= Q_i`, equations
(11) and (14) give

\[
 d_i\le L_i-Q_i\le2R(1-a_i).
 \tag{15}
\]

Consequently

\[
 d_i\le R\min\{a_i,2(1-a_i)\}\le\frac{2R}{3},
 \tag{16}
\]

because the two affine bounds meet at `a_i=2/3`.  This proves (1).

For the hierarchy corollary, the literal one-date profile belongs to every
finite-clock actual set `A_(K_m)` by inserting zero-mass dates before its
exact Never atom.  Given its semantic pair `(U,B)`, define the diagonal point

\[
 z_{U_i}=z_{B_i}=\frac{U_i+B_i}{2}.
 \tag{17}
\]

Its debt objective is zero, and

\[
 \|z-(U,B)\|_\infty
 =\frac12\max_i(B_i-U_i)
 \le\frac R3.
 \tag{18}
\]

Under (3), that same actual center satisfies every outer-radius constraint
through level `M`.  Hence `z` belongs to the outer feasible set `R_M`; the
nonnegative lower objective has value zero there, proving (4).

## Boundary tests

- If every singleton reward is nonpositive, then every `L_i <= C_i`, so the
  selected profile is already an exact terminal Nash profile.
- The proof uses no division by a stopping or Continue probability.  It
  covers `a_i=0`, `a_i=1`, pure equilibrium coordinates, and mixed ties.
- If `R=0`, every payoff and debt is zero.
- With one player, the simultaneous Nash selects Quit when the singleton
  reward is positive and Continue otherwise; the constructed profile is
  exact, consistently with the bound.
- Zero-probability coalition cells cause no conditioning problem.
- The scalar `2/3` is sharp for the two simultaneous comparison bounds in
  (16).  The theorem does not claim that a complete reward table forces
  equality simultaneously with all mixed-Nash equations.
- An explicit attempt to falsify the result at the one-shot/all-Continue
  discontinuity found the additional late value (9), rather than a missing
  strategy.  Pure-time extremality then exhausts all behavioral deviations.

## Adapter and consumer

The arbitrary source is any finite reward table with reward bound `R`.
Finite mixed-Nash existence supplies `p`; the date-zero/Never realization is
a literal behavioral profile.  Equations (9)--(10), together with the checked
pure-time extremality theorem, are the all-behavior semantic adapter.

The immediate consumer is the escape-aware outer hierarchy: the actual
finite-clock semantic center and its diagonal midpoint prove the exact zero
lower certificate (4).  This is an impossibility result for positive
certificates at levels `M <= 36`, not a numerical observation.  The actual
profile itself is also a universal fixed-error terminal approximate Nash
producer available to future iterative or chronological constructions.

## Lean handoff

A narrow implementation can proceed in three layers.

1. Define the date-zero/Never behavioral profile associated to a zero-tail
   root and prove the three pure-time payoff cases `Q_i`, `C_i`, and
   `C_i + a_i*s_i`.
2. Use `exists_isZeroQuittingRootNash` and
   `sSup_range_quittingTerminalPayoff_update_eq_pureTime` to prove the
   coordinate debt bound.  Split on `s_i <= 0`, and in the positive branch
   split on `L_i <= Q_i` before using the inequality for `L_i-Q_i`; this
   avoids an invalid direct inequality when that difference is negative.
3. Package the actual finite-clock center and prove the hierarchy midpoint
   corollary.  Retain `HasEscapeAwareQuantileClockCompression reward` if that
   is still required by the integrated bracket API.

Useful regressions are `a_i=0`, `a_i=1`, a pure all-Continue root, a pure
absorbing root, an interior mixed tie, and a table with negative singleton
reward.

A plausible declaration shape for the core theorem is:

```lean
theorem exists_oneDateNever_terminalDebt_le_twoThirds
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (bound : Real)
    (hbound : forall S i, abs (reward S i) <= bound)
    (hbound_nonneg : 0 <= bound) :
    exists profile : (quittingGame reward).BehaviorProfile,
      (forall i,
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) i <=
            2 * bound / 3) /\
      IsOneDateThenNeverProfile reward profile
```

The profile predicate may be avoided by returning the root and an equality to
the existing literal root-then-all-Continue construction.

## Scope and nonclaims

The result does not prove terminal approximate Nash profiles at arbitrarily
small errors, a uniform-equilibrium payoff, or a positive terminal gap.  It
does not decide whether `2/3` is optimal among one-date constructions.  It
does not itself analyze richer timing games or provide a vanishing-error
selection; the separate two-date theorem and hard-deadline no-go delimit that
route.  It proves no positive hierarchy lower bound at level `37` or later.

## Formalization record

The packet is formalized at its full reviewed scope in two checked modules.

- `UniformEquilibrium/Quitting/Root/OneDateNeverNashDebt.lean` defines the
  literal date-zero-then-Never profile and proves the exact all-behavior debt
  formula, both data-sensitive mass bounds, the universal `2 * bound / 3`
  theorem
  `quittingTerminalDeviationDebt_oneDateThenNever_le_two_thirds`, and the
  arbitrary-table producer
  `exists_oneDateThenNever_terminalDebt_le_two_thirds`.
- `Research/Quitting/OneDateNeverNashDebtHierarchy.lean` proves actual
  finite-clock reachability of that semantic pair, the diagonal-midpoint
  hierarchy consumer, the Fin4 level-`36` theorem
  `escapeAwareQuantileClockLower_finFour_eq_zero_of_le_thirtySix`, and the
  canonical normalized wrapper
  `escapeAwareQuantileClockLower_finFour_normalized_eq_zero_of_le_thirtySix`.

The unrestricted cap is the repository's full behavioral deviation cap;
Never and every late finite stopping time remain available. The normalized
Fin4 wrapper constructs the checked common-quantile compression certificate
rather than assuming it as an external hypothesis.

Evidence seals are `M`, `L`, `A`, and `C`: two independent reviews passed the
ordinary theorem; Lean checks the exact debt and hierarchy declarations; the
producer starts from an arbitrary bounded finite reward table and selects the
finite mixed Nash root; and the actual semantic pair is consumed by the
finite-clock outer hierarchy.

No vanishing-error family, uniform-equilibrium payoff, positive hierarchy
lower bound, or optimality theorem for the constant `2/3` is claimed.
