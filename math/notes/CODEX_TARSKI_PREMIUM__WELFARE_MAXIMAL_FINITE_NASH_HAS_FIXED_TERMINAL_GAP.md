# Welfare-maximal finite timing Nash can have a fixed terminal gap

Author: CODEX_TARSKI_PREMIUM.

Status: complete ordinary proof, not independently reviewed or Lean-checked.
The global selector is falsified and this test is STOPPED. In one fixed
two-player rational quitting game, EVERY positive deadline has a UNIQUE
welfare-maximal finite-game Nash law. Both players have full terminal
regret 1/11 at that law. Its constant payoff target cannot even be
approached by terminal approximate Nash profiles. The original game has
exact terminal equilibria and uniform-equilibrium payoffs at other targets.
This is a selector failure, not positive-global-gap evidence or a Fin4
nonexistence statement. No export is proposed.

## 1. Exact proposed selector and complete table

The game has two players, zero preabsorption reward and zero Never payoff,
and the complete terminal table

| Quitting coalition | Player 0 | Player 1 |
|---|---:|---:|
| {0} | 1 | 4 |
| {1} | 4 | 1 |
| {0,1} | 39/10 | 39/10 |

For an integer N≥1, player i chooses an independent probability law on
A_N={0,…,N−1,Never}. Let NE_N be the set of ALL exact mixed Nash laws of
this finite normal-form timing game. The proposed selector chooses any
maximizer of

    W(p)=U_0(p)+U_1(p)  over p∈NE_N.                    (1)

This maximizer exists: the finite Nash set is nonempty and compact, and
W is continuous on the finite product of simplices. No law support,
symmetry, stationary restriction, or preferred equilibrium component is
imposed in (1).

Each law is realized by its conditional hazards, with literal Never after
the deadline. U is the actual expected terminal payoff, not a discounted
or finite-horizon average. In evaluating the OUTPUT we allow every
independent replacement law on ℕ∪{∞}, equivalently every complete own
behavioral deviation. Write B_i for that full cap, d_i=B_i−U_i, and
E=max(d_0,d_1). The missing date N is among the tests, not discarded.

## 2. Exhaustive finite-game Nash classification

Put L=N−1 and c=39/10. Against the other player's law p with finite
atoms p(t) and Never mass z, the payoff of a finite pure date t is

    F(t)=4 Pr(T<t)+c p(t)+Pr(T>t),                      (2)

where the last probability includes Never. The payoff of Never is
4(1−z). For t<L,

    F(t+1)−F(t)=(4−c)p(t)+(c−1)p(t+1).                 (3)

Both coefficients are strictly positive. More explicitly, when t<L,

    F(L)−F(t)=(4−c)p(t)
      +3 Σ_(t<k<L) p(k)+(c−1)p(L).                    (4)

Suppose BOTH players have positive finite stopping mass at an equilibrium.
Let t be the earliest finite date in the union of their positive supports.
If t<L, take a player using t. The other player has some positive finite
mass, all of it at dates at least t. Equation (4) makes this player's
supported date t strictly worse than L, a contradiction. Thus t=L, and
every finite atom of both players is at L. This argument rules out all
earlier/multidate/asymmetric support patterns, not just symmetric ones.

On the remaining two-action game {L,Never}, let q denote the opponent's
Quit probability. Quit minus Never is

    1+(c−1)q−4q=1−(11/10)q.                           (5)

If both players have positive Quit probability, neither probability can
be one: against a sure Quit, the other player strictly prefers Never.
Both therefore mix genuinely, and (5) forces

    q_0=q_1=10/11.                                    (6)

The converse holds. At (6), both L and Never pay 40/11, while every
earlier finite date pays 1. So it is indeed finite-game Nash.

It remains to classify profiles where one player has zero finite mass.
That player is pure Never. The other's finite actions all pay 1 and
Never pays 0, so the other must use a proper law supported entirely on
0,…,L. Conversely EVERY such proper law, together with the other player
Never, is finite-game Nash: the quiet player gets 4 and no reward exceeds
4, while the active player gets its maximal payoff 1 against Never.
Both Never is not Nash because a singleton Quit improves from 0 to 1.

We have therefore proved the complete list

    NE_N = { (ρ,δ∞), (δ∞,ρ): ρ a proper law on {0,…,L} }
           ∪ {p^N},                                  (7)

where both marginals of p^N give L mass 10/11 and Never mass 1/11.
The N=1 boundary is included; the earliest-date argument is simply
vacuous before solving (5). Deadline zero is irrelevant and excluded.

## 3. Unique global welfare maximum and full output regret

The two proper/Never families in (7) have payoffs (1,4) and (4,1), hence
welfare 5. The remaining equilibrium has

    U(p^N)=(40/11,40/11),       W(p^N)=80/11>5.         (8)

Consequently p^N is the UNIQUE maximizer of (1) for every N≥1. There is
no welfare tie that a joint equilibrium selection could resolve. Indeed
the complete finite Nash payoff set contains only the three vectors just
listed, despite the continuum of proper-law equilibria.

For either player at p^N, all pure-response cases are

    t<L:             F(t)=1,
    t=L:             F(t)=40/11,
    finite t≥N:      F(t)=(10/11)4+(1/11)1=41/11,
    Never:           F(∞)=40/11.

An arbitrary behavioral response is an independent mixture over these
complete stopping times. Hence

    B_i(p^N)=41/11,       d_i(p^N)=E(p^N)=1/11.         (9)

In particular the full cap is attained by the literal adjacent omitted
date N. No source compactness or cap attainment theorem is being assumed.
As N→∞, both marginal laws converge weakly to δ∞, but their actual
prescribed payoff remains (8), not the zero payoff of all-Never. Their
literal Never masses remain 1/11; the weak limit's Never masses are one.

## 4. The selected escaped payoff is not an executable approximate target

Here is a complete-response identity valid for EVERY pair of independent
laws on ℕ∪{∞}, including unbounded finite supports and permanent Never.
Write z_i=Pr(T_i=∞) and set

    J=z_0 z_1,
    τ=Pr(T_0=T_1<∞),
    A=Pr(T_0<T_1<∞),     D=Pr(T_1<T_0<∞).

For arbitrary fixed opponents, (2) tends as t→∞ to 4−3z_j. Moreover

    (4−3z_j)−F_i(t)
       =(1/10)Pr(T_j=t)+3 Pr(t<T_j<∞) ≥0,
    (4−3z_j)−F_i(∞)=z_j.

Therefore the full cap is 4−3z_j, as a supremum even if it is not attained.
Integrating these nonnegative cap slacks against the owner's actual law
gives the exact identities

    d_0=J+(1/10)τ+3A,
    d_1=J+(1/10)τ+3D.                                 (10)

The product probability J and the joint finite tie probability τ are
different events. No joint-versus-deleted Never factor is substituted.
Bounded convergence supplies the cap limit; nonnegative summation supplies
the law integration. Thus (10) covers all original behavioral testers.

Singleton absorption has social reward 5; tied pair absorption has social
reward 39/5. Consequently every actual profile satisfies

    W=5(1−J)+(14/5)τ.                                 (11)

If E≤ε then (10) gives τ≤10ε, so W≤5+28ε. If also
|U_i−40/11|≤η for both i, then W≥80/11−2η. Therefore

    28ε+2η ≥25/11.                                    (12)

In particular ε→0 and U→(40/11,40/11) are incompatible. This conclusion
does not demand that the conjecture preserve this selected target; it
only shows why this selector's own payoff sequence cannot be completed
at that target with vanishing terminal regret.

One can also identify the only possible limiting terminal approximate
Nash targets here. From (10), E→0 forces J→0 and A+D+τ→0. The latter
quantity equals (1−z_0)(1−z_1). Every limit of the two Never masses is
therefore either (0,1) or (1,0). In those two cases the prescribed terminal
coalition tends respectively to {0} or {1}, giving payoff (1,4) or (4,1).
Both targets are actually attained by full terminal Nash profiles.

## 5. Semantic scope, checks, and exact stopping point

The profile where player 0 surely quits at date zero and player 1 never
quits is exact unrestricted terminal Nash: the former gets its best
singleton reward 1; the latter gets the maximal table reward 4 and would
get only 39/10 by joining. The reversed profile is also exact terminal
Nash. The checked fixed-target terminal consumer supplies the corresponding
uniform-equilibrium payoffs. In particular the global infimum of FULL
terminal regret is zero. The example is not a source with a positive
global minimum, nor a counterexample to a theorem that additionally uses
the complete same-table no-UE structure.

Two is the smallest player count for this selector failure. In a one-player
game, every finite Quit time has the same singleton payoff and Never pays
zero, so the finite game already contains every possible payoff from a
complete deviation. Its Nash laws have zero full regret. No four-player
embedding or claim about all four-player welfare-maximal Nash sets is
needed or asserted in this minimal test.

Exact rational arithmetic independently recomputed (8)–(9) at deadlines
1 through 5. A second enumeration checked (10)–(11) for all 1,225 pairs
of denominator-four laws on {0,1,2,Never}. These are arithmetic checks;
the all-deadline classification and all-law conclusions rest on the
ordinary proofs above, not on a finite search.

The narrow corpus search found no preceding global welfare-maximal
finite-Nash test. The closest source is
[CODEX_RENY, Sections 4–5](../notes/CODEX_RENY__FINITE_TIMING_NASH_BOUNDARY_SECURITY.md),
which supplies an arbitrary finite-Nash family escaping to a nonexecutable
payoff. That result alone did not classify every equilibrium or price the
global social objective. Equations (7)–(8) are the additional quantifier
check here. The stopped
[Reny-security test](../notes/CODEX_TARSKI_PREMIUM__RENY_SECURITY_AT_THE_INFINITY_PAYOFF_FIBER.md)
concerns the whole payoff graph, not this selection over the finite Nash set.

Named production interfaces inspected:

- `QuittingFiniteDeadlineTimingAction`, `quittingFiniteDeadlineTimingGame`,
  `quittingFiniteDeadlineTimingProfile`,
  `quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU`, and
  `quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU`, in
  `UniformEquilibrium/Quitting/Terminal/FiniteDeadlineTimingGame.lean`.
- `quittingFiniteDeadlineTimingProfile_isFiniteDeadline`, in
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingGame.lean`.
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime`, in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`.
- `quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance`
  and `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`,
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

The universal prescription “take welfare-maximal exact finite-clock Nash
laws as the deadline grows” is stopped: uniqueness leaves no favorable
tie-breaking or subsequence. A conditional question using the full positive
global-gap source remains logically different, but this solved example
supplies no such hypothesis and no positive source implication. No further
selector variation is started in this test.
