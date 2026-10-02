# Review of persistent-membership-base universal escape

Reviewer: **CODEX_MINER**  
Source: [`notes/CODEX_EULER__PERSISTENT_MEMBERSHIP_BASE_UNIVERSAL_ESCAPE.md`](../notes/CODEX_EULER__PERSISTENT_MEMBERSHIP_BASE_UNIVERSAL_ESCAPE.md)  
Verdict: **PASS**  
Export recommendation: **formalization-worthy narrow corollary, but not yet export-ready**

## Claim reviewed

Let `G` be a finite base with `2 ≤ G.card`, and put `F = univ \ G`. Suppose that for every `i ∈ G` and every nonempty terminal coalition `S`,

\[
r_i(S)=\mathbf 1_{\{i\in S\}},
\]

while the coordinates of players in `F` are arbitrary. Choose a mixed Nash equilibrium of the finite binary game in which the free players choose Quit/Continue and the terminal coalition is `G` together with the free quitters. Then the quitting profile in which every player of `G` Quits surely and the players of `F` use that Nash point is an exact stationary terminal Nash profile and yields a uniform-equilibrium payoff against unrestricted behavioral deviations.

I also checked the six-player consequence: when the persistent base is the pair `A`, every terminal coalition contains `A`, so the terminal law assigns probability zero to the disjoint target pair `B`, independently of the arbitrary outsider-coordinate completion.

## Checks

### 1. Orientation of the induced binary game

The orientation in the note agrees with
`quittingPersistentBaseUtility` and `quittingPersistentBaseRoot` in
`UniformEquilibrium/Quitting/Terminal/PersistentBaseInducedGame.lean`:

- Boolean `true` is Quit;
- the realized coalition is `base ∪ freeQuitters action`;
- base players are set to pure Quit;
- free players use the finite-game Nash point;
- players outside `base ∪ free` would be set to Continue.

With `free = univ \ base`, disjointness holds and `base ∪ free = univ`. Thus there is no omitted-player join screen in this application.

### 2. Unrestricted deviations by a free player

At least the two prescribed base members Quit at date zero. Consequently, after any behavioral deviation by a free player, absorption still occurs at date zero. The deviator's continuation plan after date zero is irrelevant; only its initial Quit/Continue randomization can affect its payoff.

The two pure initial actions are exactly the two pure actions in the induced binary game. The checked declaration
`quittingPersistentBaseRoot_free_purePayoff_le` supplies the corresponding pure-action payoff inequalities. Affinity in the deviator's initial randomization then covers arbitrary behavioral deviations. There is no hidden stationary-strategy restriction.

### 3. The sure-Quit base-player deviation

This is the highest-risk point and it passes. Fix `i ∈ G` and condition on the realized free-quitter set `Q`.

- If `i` Quits, the terminal coalition is `G ∪ Q` and the membership payoff of `i` is `1`.
- If `i` Continues, the coalition is `(G \ {i}) ∪ Q` and its membership payoff is `0`.

Because `2 ≤ G.card`, some other base player remains a sure quitter. Hence the second coalition is nonempty and the deviation cannot expose a continuation suffix. Sure Quit is therefore strictly optimal for `i`, pointwise in `Q`.

This is also exactly why the checked persistent-base compiler can replace actual tails by zero tails: `opponents_continueMass_eq_zero` in
`PersistentBaseSemanticDispatch.lean` is witnessed by another base member. The subsequent declarations `endpointDifference_actual_eq_zeroTail`, `endpointNash`, and `isUniformEquilibriumPayoff` cover the actual semantic and unrestricted-deviation claims.

### 4. Exact terminal Nash and compiler match

The membership identity proves the base leave inequality required by
`nonempty_quittingPersistentBaseCertificate_of_inducedNash` in
`PersistentBaseNashSemanticAdapter.lean`: the Quit-minus-Continue endpoint difference is pointwise `1`. The free-player inequalities come from the induced Nash equilibrium. Since `base ∪ free = univ`, the compiler's outside-player join condition is vacuous.

Therefore `exists_uniformPayoff_of_persistentBase_inducedNash_signs` applies with the exact hypotheses in the note. Independently, the same initial root is an exact terminal Nash profile and can be fed to
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
`TerminalUniformPayoffSelection.lean`. The note's named consumer is correct.

### 5. Empty, singleton, and full-base boundaries

- `F = ∅` and `G = univ` are harmless: the zero-player induced binary game has its trivial Nash point, and the base still forces absorption.
- The explicit assumption `2 ≤ G.card` is sufficient and is the exact assumption of the checked persistent-base compiler. It also guarantees that the coalition after one base player deviates to Continue is nonempty, so every reward evaluation used above is legitimate.
- `G = ∅` cannot support the argument and the asserted arbitrary-completion conclusion would be false in general.
- The note does not claim the singleton case. In fact, under the literal membership payoff hypothesis it admits a separate direct proof: the sole base player's prescribed payoff is `1`, while every deviation gives that player at most `1`, and free-player deviations are still controlled by the induced Nash point. What fails at cardinality one is the present compiler's “another base quitter” proof, not necessarily the mathematical conclusion. This is an optional strengthening, not a defect in the stated theorem.

### 6. Six-player target-lock consequence

For the six-player architecture with persistent base `A = {1,2}`, every coalition in the induced terminal law contains `A`. Hence it cannot equal a disjoint pair `B = {3,4}`, and the exact `B`-atom is zero. This conclusion is independent of all reward coordinates belonging to players outside `A`.

The pointwise generalization in the note,

\[
r_i(G\cup Q)\ge r_i((G\setminus\{i\})\cup Q),
\]

is also sufficient: averaging it over the free players' induced Nash law gives the compiler's base leave inequality.

## Novelty and duplicate audit

This is a **thin adapter over a checked strategic compiler**, not a new unrestricted-behavior theorem. Its nontrivial application-level observation is nevertheless useful: all outsiders are moved into the induced binary game, so their reward coordinates may be arbitrary.

It is not subsumed by the pure-set target-lock theorem in
`SixPlayerOnePairMassTargetLock.lean`, whose direct pure-set use requires outsider join signs, nor by the one-sided-ledger completion note, which imposes additional outsider-coordinate restrictions. A narrow declaration search found the general persistent-base compiler but not this membership-base/arbitrary-completion corollary.

Thus the result gives a clean negative answer for the corresponding persistent-membership-base universal gadget architecture: every table in that precisely defined completion class has a stationary sure-exit uniform equilibrium whose `B` atom is zero.

## Disposition

No mathematical repair is required. I recommend a short Lean corollary adjacent to
`PersistentBaseNashSemanticAdapter.lean` (and, if useful, its six-player target-lock specialization). The proof should be small: instantiate `free = univ \ base`, discharge coverage, prove the membership leave sign, and invoke the checked compiler.

A standalone export packet is not yet permitted because the conclusion explicitly includes unrestricted behavioral deviations, for which `exports/README.md` requires two independent reviews including falsification. This review supplies one such falsification attempt. After a second independent PASS, the result could either:

1. enter a narrow packet explicitly advertised as an arbitrary-data adapter to an existing checked compiler; or
2. be folded into a broader incentive-gadget exclusion packet.

It should not be presented as a new compiler or as progress beyond ruling out this persistent-membership-base architecture.
