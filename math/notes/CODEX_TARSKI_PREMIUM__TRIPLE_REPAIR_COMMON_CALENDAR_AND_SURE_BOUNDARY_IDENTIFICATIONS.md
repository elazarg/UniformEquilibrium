# Triple repair: two precise identifications with existing routes

Author: CODEX_TARSKI_PREMIUM.

Status: completed bounded ordinary-mathematics test, not independently
reviewed or Lean-checked. No new producer, counterexample to the quitting
conjecture, or export is claimed. Both proposed constructions below reduce
to existing routes; their missing selection steps are not repackaged.

## 1. Actual probability and the routine partial repair

There are four independent complete stopping laws on Nat∪{Never}, signed
terminal rewards bounded by M, and Never payoff zero. Write U_i for actual
payoff, B_i for the cap over ALL behavioral replacements, d_i=B_i−U_i,
and E=max_i d_i. Pure finite dates and Never compute every cap.

Against one fixed finite outsider law, repairing the other three players to
full terminal error ε is routine. Select an actual ε-equilibrium of their
induced three-player tail game, and use actions consisting of the original
finite head dates and following that tail. The resulting finite three-player
head game has a mixed Nash point. Each head payoff integrates the original
outsider's actual same-date coalitions. Every late response differs from
the tail action only on the event that the outsider chose Never and both
other strategic players chose the tail; its gain is at most ε times that
event probability. No survival denominator is used. Finite truncation with
a smaller initial error yields finite outputs. This is the earlier pair
adapter with three strategic players, not new conjecture progress.

It does not quiet-lift an unchanged child: the repaired triple responds to
the outsider's actual finite head. Nevertheless, its existence alone does
not bound the outsider's complete cap.

## 2. Same-calendar coupling is exactly finite-menu Nash

Assume the canonical singleton vector (1,0,0,0), and put
A_N={0,…,N−1,Never}, X_N=∏_i Δ(A_N), N≥1. All objectives below still
use the original full caps, including the missing late pivot response N.

For p∈X_N the following are equivalent:

1. Players 1,2,3 are full terminal Nash against the SAME actual p, and
   p_0 globally minimizes E(q_0,p_−0) over q_0∈Δ(A_N).
2. p is an exact Nash equilibrium of the finite timing game on A_N.

Proof, 1 implies 2. The nonpivots are already menu best responding. Suppose
the pivot has a positive menu improvement b. Its full debt d_0 is then
positive and equals E(p), because all other debts vanish. Mix its law by
a sufficiently small α>0 toward that improving menu response. Its cap is
unchanged and its debt falls by αb. Each other complete gain is affine in
the pivot law, so every other debt is at most 2Mα. Choosing α small enough
makes the entire E strictly below d_0, contradicting pivot optimality.

Proof, 2 implies 1. The nonpivot late finite payoff equals its Never payoff:
the only distinguishing event has everyone else Never and pays its own
singleton zero. Thus their menu optimality is full optimality. The pivot
has U_0(p) equal to its menu cap, so no other A_N law increases its payoff.
Its full B_0 is fixed when its own law varies; consequently every candidate
has pivot debt at least d_0(p)=E(p). This proves its global same-calendar
full-E optimality. The zero-debt case is included.

This is an exhaustive equivalence, not an arbitrary bad fixed point.
[HILBERT's canonical boundary table](CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md)
has, at credit zero, a unique exact finite-menu Nash law of full debt 3/8
at EVERY N. Hence every output of construction 1 on that table has the same
nonvanishing debt. The table has an actual infinite periodic equilibrium;
this is a failure of the specified exact common-calendar coupling only.

If pivot optimization instead ranges over ALL actual laws, construction 1
would force full Nash: whenever the pivot is the sole positive debtor,
mixing toward a sufficiently good complete response strictly lowers E by
the same argument. Existence of this stronger jointly coupled object does
not follow from the finite correspondence. A late pivot atom changes the
nonpivots' same-date joining comparisons, as the existing
[full LP/finite nonpivot coupling](CODEX_RENY__PIVOT_LP_AND_FINITE_NONPIVOT_BEST_REPLY_COUPLING.md)
already demonstrates. Approximate triple Nash plus approximate unrestricted
pivot optimality remains distinct from merely solving that finite coupling.

## 3. A sure outsider retains two independent boundary obligations

Now singleton signs are arbitrary. Let outsider o Quit surely at one row;
let its complementary triple independently mix at that row, with product
coalition probabilities P(S), S⊆J=I\{o}. Let σ be their ACTUAL conditional
tail after they all Continue. The outsider's prescribed value and its full
Continue value are respectively

    Q_o=Σ_(S⊆J) P(S) r_o(S∪{o}),
    C_o=Σ_(∅≠S⊆J) P(S) r_o(S)+P(∅)B_o(σ).

Its full debt is (C_o−Q_o)_+. The first term of C_o is the literal
stay-out-versus-join boundary comparison, not a suffix error.

For a free player i, the outsider still stops at the row after any deviation
of i. Thus its two complete endpoints are exactly joining versus staying
out, using r_i(S∪{o,i}) and r_i(S∪{o}) for the other free players' current
coalition S. The hidden tail cannot fix a profitable new join at that row.
Selecting a mixed Nash point of this induced binary game checks precisely
those three players' FULL incentives.

Let v_o be the unrestricted punishment value. A near-punishing actual σ
can replace B_o(σ) by at most v_o+ε. It does not supply Q_o≥C_o(v_o).
Selecting an induced triple Nash point satisfying that last inequality is
exactly a Nash root against the coordinatewise punishment vector with a
sure quitter: only o can expose continuation, so the other punishment
coordinates are irrelevant at that root. This is the established instant-
punishment branch, not a new sure-anchor existence criterion.

A finite earlier head does not erase either displayed last-row obligation.
Transporting a conditional error to the original profile requires its
literal joint reach. No positive reach or small cutoff error is inferred
solely from having a sure deadline.

## 4. Narrow source correspondence and stopping point

Inspected declarations under their imports:

- `quittingGame_exists_uniformEquilibriumPayoff_threePlayer` in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`;
  together with the already inspected terminal all-errors converse, this
  supplies the actual tail in Section 1, not its outsider cap.
- `quittingInstantPunishmentεEquilibriumExistence_iff_sureQuitterPunishmentVectorNashRoot`
  in `UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterCharacterization.lean`.
- `quittingPunishmentSureRootTarget_isUniformEquilibriumPayoff_and_floor`
  in `UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterPayoff.lean`.
- The induced dominance and membership definitions in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingleAnchorArbitraryCompletionEscape.lean`.

The bounded comparison read
[the cardinal-minimal question](../questions/CARDINAL_MINIMAL_OUTSIDER_CONSUMER.md),
[SPINOZA's host-release failure](CODEX_SPINOZA__HOST_RELEASE_THREE_PLAYER_NASH_LIFT_SIGN_REVERSAL.md),
the finite coupling and canonical regression cited above, and the theorem
and source scope of the frozen
[adaptive unchanged-child no-go](../exports/ADAPTIVE_CHILD_EQUILIBRIUM_EXTENSION_NO_GO.md).
Those unchanged-child and arbitrary selected-source no-gos are not
substituted for a positive global minimum.

Both tested branches are stopped. The remaining substantive task is a
source-derived joint selection changing all required laws while controlling
the complete outsider response, not another proof of partial repair,
finite-menu Nash existence, or the instant-punishment characterization.
