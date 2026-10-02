# Independent audit of `FOUR_PLAYER_INERT.md`

Reviewer: `CODEX_MINER`

Date: 2026-08-26

Source reviewed: [`../FOUR_PLAYER_INERT.md`](../../FOUR_PLAYER_INERT.md)

Conference transcription reviewed:
[`notes/CHATGPT_EXTERNAL__FIN4_INERT_PAID_MASS_RECTANGLE.md`](../notes/CHATGPT_EXTERNAL__FIN4_INERT_PAID_MASS_RECTANGLE.md)

## Verdict

**REVISE the supplied note's interface claim; PASS the quantitative
paid-mass/rectangle calculation and the six-state local regression.  Keep
internal; do not export.**

Equations (10)--(28) are mathematically correct under the granted hypotheses
used in the note.  The move-only-paid-mass profile is an actual behavioral
profile, the debt-transfer constants are correct, and the resulting pure-time
rectangle family has the stated product-law and untouched-survival floors.
Every row of the four-player example, every reset arrow, the unique
all-Continue cap root, the strict singleton margins, and the all-Never
equilibrium check also pass.

The mandatory correction is semantic/interface-level.  The conclusion is not
a `FinFourSingletonBaseResetRepairPaidCapDoublePort`, a
`QuittingFixedLawResetDispatch`, or a pair of
`QuittingPaidCapLiftedSource.InertStall`s.  It is a family of two sequential
profitable behavioral replacements and positive four-profile terminal-law
rectangles.  It feeds the generic rectangle-atom decoder, but supplies none of
the common-law reset, exact cap--Nash, punishment-floor, positive-minimum,
repair, or regenerated-source fields required by the maintained reset/double-
port consumers.  The imported conference note has already adopted most of
this qualification and is a more accurate statement of the result than the
boxed phrase “positive two-reset terminal-law packet” in the supplied source.

## Scope of this audit

The source begins after the unnamed package (1)--(5) has been stated.  I could
not check the asserted equivalence between existence of that package and a
four-player counterexample because the package itself is not present in the
supplied file.  The audit below is conditional on the hypotheses actually
used in Sections 1--3:

- four players and `|r_i(S)| <= M`;
- `gamma > 0` and actual profiles `sigma_n` with
  `D(sigma_n) -> D_*`;
- a debtor `o_n` with `d_{o_n}(sigma_n) >= gamma`; and
- the global lower bound `D(actual profile) >= D_*`.

The literature/open-problem assertion in the first paragraph is not needed
for, and is not included in, the mathematical verdict.

## 1. Stopping-law mass bound (10)--(12)

Fixing `o` after a finite-label subsequence is valid.  Pure-time extremality
gives a `gamma/8`-optimal `q_n` without assuming attainment of the supremum;
`q_n` may be `Never`.  Hence

\[
  F(q_n)-\int F(s)\,d\mu(s)\ge 7\gamma/8.
\]

On `A_n` the integrand is at most `2M`, and outside `A_n` it is strictly less
than `gamma/2` (using `<= gamma/2` only weakens the estimate).  Therefore

\[
  \alpha_n\ge {3\gamma\over16M-4\gamma}.
\]

Since a debt is at most `2M`, `0 < gamma <= 2M`; in particular `M>0` and
`16M-4gamma >= 8M>0`.  Cross-multiplication then gives

\[
 {3\gamma\over16M-4\gamma}\ge {\gamma\over8M}.
\]

Thus (10) is correct, including its boundary at `gamma=2M`.

For every `s in A_n`, `q_n != s`.  The first pure-time disagreement is
finite even if one of them is `Never`.  Exact common-prefix factorization and
the `2M` reached-payoff bound imply

\[
 h_{o,n}(s)\ge\gamma/(4M).
\]

Integrating over `A_n` proves (12).  Countability of `Option Nat` permits a
finite subset retaining any prescribed fraction below the total, in
particular one half.  No selected-atom lower bound or supremum attainment is
being smuggled into this step.

## 2. Moving only paid mass and debt transfer (13)--(18)

Because `q_n` is not in `A_n`,

\[
 \nu=\mu|_{A_n^c}+\alpha_n\delta_{q_n}
\]

is visibly a probability law; even without using that observation, its total
mass is one.  Every probability law on `Option Nat` is behaviorally
realizable in the quitting game, so `rho_n` is actual.  Payoff affinity gives
the exact identity in (14), not merely an inequality.

The continuation best-response cap of `o` depends only on the opponents'
strategies, so it is invariant under replacement of `o`'s own strategy.  This
proves the exact debt change (15).  From

\[
 D(\rho_n)\ge D_*,\qquad
 D(\sigma_n)\le D_*+\gamma^2/(32M),\qquad
 g_n\ge\gamma^2/(16M)
\]

one obtains the aggregate opponent increase in (17).  With exactly three
opponents, (18) follows, and another finite-label subsequence fixes `j != o`.
All signs and constants pass.

There is also an implicit useful fact: the second replacement is itself
profitable.  Since debt is nonnegative,

\[
 d_j(\rho_n)\ge\gamma^2/(96M),
\]

and the choice of `p_n` yields

\[
 U_j(x_{11})-U_j(x_{01})
 \ge {\gamma^2\over96M}-{\gamma^2\over200M}
 \ge {\gamma^2\over200M}.
\]

This justifies describing `sigma_n -> rho_n -> x_11` informally as two paid
behavioral replacements.  It does not make either arrow an exact one-stage
product-Nash or punishment-floor edge.

## 3. Rectangle and localization (19)--(28)

The repeated definition of `x_00` in Section 1.3 is only a typographical
duplication.

Approximate optimality at `rho_n` and the cap upper bound at `sigma_n` give

\[
 d_j(x_{01})-d_j(x_{00})\le R_n+\varepsilon.
\]

The constant calculation is

\[
 {1\over96}-{1\over200}={13\over2400}\ge {1\over200},
\]

so (21) is correct.

Expanding the law
`nu = mu|A^c + alpha delta_q` in all four corners gives exactly

\[
 R_n=\int\!\int_{A_n}\Delta_n(a,s)
       \,d\mu_{o,n}(s)d\mu_{j,n}(a).
\]

There is no missing factor `alpha_n`: it is already the integral of the
constant `q_n` term over `A_n`.  Since `Delta <= 4M` on `P_n` and
`Delta < theta` off `P_n`, while the integration domain has mass at most one,

\[
 {\gamma^2\over200M}
 \le 4M(\mu_j\otimes\mu_o)(P_n)+{\gamma^2\over400M},
\]

which proves (24).

For `(a,s) in P_n`, both pure-time pairs differ.  Before their earliest
disagreement, `j` and `o` have the same deterministic actions in all four
corners.  Earlier absorption by either untouched player is common to all four
corners and cancels.  Factoring their joint survival gives (25), and the
conditional four-corner payoff is bounded by `4M`; hence (26).  Taking a
finite subset of at least half the product mass gives

\[
 {1\over2}{\gamma^2\over1600M^2}
 {\gamma^2\over1600M^2}
 ={\gamma^4\over5{,}120{,}000M^4},
\]

so (27) also passes.  The “actual reached mass” here should continue to mean
the latent source-law mass of the selected pure-time pairs times the actual
untouched-player survival.  It is not cap-root absorption or mass on a single
punishment-floor chronology.

For four players there are fifteen nonempty coalitions.  The Never outcome
has zero reward, and the fifteen reward-weighted signed rectangle atoms sum
to `Delta >= theta`.  Therefore one is at least `theta/15`, proving (28).
This is a **signed reward-weighted rectangle atom**.  Nonzero signed mass does
ensure that its coalition occurs in at least one literal corner, but (28)
does not say:

- that the coalition has positive mass in the reset target rather than a
  different corner;
- that `o` or `j` belongs to it;
- that its sign is a profitable target-edge sign;
- that it is the earliest-disagreement row selected in (25); or
- that it satisfies any local Nash or punishment-floor inequality.

Those distinctions are material downstream.

## 4. Exact interface and novelty audit

The closest checked results are:

- `exists_opponent_prescribedAtom_or_deviationRectangleAtom_of_totalSlope`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeAtom.lean`;
- `exists_absorbingTerminalPayoffRectangleAtom` and
  `exists_rectangleAtom_and_targetEdgeAtom_of_mixedDebtSlope` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeRectangle.lean`;
- `exists_positive_causalStage_of_positive_pureTimeRectangleAtom` and
  `exists_positive_causalStage_and_actualTerminalMass_of_rectangleCharge` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPureTimeRectangleDisintegration.lean`;
- `QuittingFixedLawResetDispatch` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`;
- `QuittingPaidCapLiftedSource` and its `SummablePort` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`;
- `QuittingPaidCapLiftedSource.InertStall` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`;
  and
- `FinFourSingletonBaseResetRepairPaidCapDoublePort` and
  `sourceDescent_or_repairedDescent_or_doubleInert` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/SingletonBaseResetRepairPaidCapDoublePort.lean`.

The checked total-slope decoder already converts a compensated debt transfer
under a literal stopping-law reset into a prescribed-law atom or a same-
deviation rectangle atom.  The generic rectangle theorem already atomizes
any positive four-profile rectangle, and the pure-time disintegration file
already explains how a positive pure-time atom has a causal stage and actual
mass in one endpoint.  Thus the existence of a positive rectangle/atom is
not new.

What is genuinely sharper in the supplied calculation is the **positive-
measure family**: a common receiving time for a uniformly positive mass of
paid source times, followed by a positive-measure set of same-orientation
pure-time squares and the explicit integrated reach bound (27).  I found no
checked declaration packaging those simultaneous mass floors.

However, no maintained reset consumer accepts only those fields:

1. `QuittingFixedLawResetDispatch` requires a common retained terminal law, a
   zero-debt reset owner, minimum-to-returned debt inequalities, opponent
   incidence, and an exact dynamic cap dispatch.  The rectangle family does
   not provide them.
2. `QuittingPaidCapLiftedSource` requires a positive global minimum and one
   actual paid first-disagreement row; its `InertStall` additionally concerns
   the canonical exact cap-prefix roots and their lossless shifted row.  The
   two strategy replacements in Section 1 are not those roots.
3. The Fin4 double port is a very specific singleton source/owner-repair pair
   with two independently selected summable cap ports.  The four corners
   `x_00,x_01,x_10,x_11` do not constitute that structure.
4. A positive signed rectangle atom is deliberately weaker than a
   source-matched profitable target edge.  The existing alignment and
   state-match regressions prevent silently identifying the two.

Accordingly, “lands directly in the repository's positive-slope four-profile
interface” is true only for the generic rectangle/atom layer.  “A packet
accepted by the reset/double-port frontier” is false.  The result does not
contract either survivor in
`questions/FIN4_HARD_RESIDUAL_SEMANTIC_CLOSURE.md` or
`questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`.

Nearby internal work already records the same conversion wall, notably
`CHATGPT_EXTERNAL__HIDDEN_RESET_VALUE_OF_INFORMATION_PASSPORT.md`,
`CODEX_EULER__FIN4_INERT_PAID_ROW_FULL_REACH_NONCONVERSION.md`, and the
stronger source/repair-aligned regression
`CODEX_RAMSEY__FIN4_DOUBLE_INERT_LAW_BRIDGE_PLATEAU_SEPARATION.md`.
The six-cycle below is a clean additional cyclic illustration, but it does
not replace those globally aligned packets.

## 5. Six-state four-player table

I recomputed unrestricted behavioral caps, not merely the displayed pure
switches.  Because player 4 quits surely at date zero at every `sigma^k`, a
mobile player's deviation is completely determined, for payoff purposes, by
its date-zero Quit probability; later behavior is irrelevant.  Its payoff is
therefore a convex combination of the join and leave endpoints.  Player 4's
best deviation is Continue at date zero, yielding zero.  This verifies the
debt table exactly:

\[
\begin{array}{c|c|c}
k&U(\sigma^k)&d(\sigma^k)\\ \hline
0&(0,1,1,-1)&(1,0,0,1)\\
1&(1,0,0,-1)&(0,0,1,1)\\
2&(0,0,1,-1)&(0,1,0,1)\\
3&(0,1,0,-1)&(1,0,0,1)\\
4&(1,0,0,-1)&(0,0,1,1)\\
5&(0,0,1,-1)&(0,1,0,1).
\end{array}
\]

Every arrow in (35) changes one player between date-zero Quit and Never,
gives that player exactly one, changes its debt from one to zero, transfers
unit debt to the next mobile player, and preserves total debt two.  The sixth
arrow returns to the identical behavioral profile, so this is a genuine
cycle, not just a semantic cycle.  All six terminal coalitions are
nonsingletons and all displayed comparison rows have start zero, live mass
one, and reached gain one.  Both temporal orientations occur; this is allowed
by the Boolean `receivingEarlier` field of
`QuittingPaidFirstDisagreementRow`.

The cap-root proof is also correct.  For player 4, Continue always pays zero,
whereas Quit pays `-2` alone and `-1` in a collision, so Continue strictly
dominates against every product of the other actions.  Once player 4
continues, every mobile player's Quit action pays `-4`, while Continue pays
zero on someone else's exit and its nonnegative continuation coordinate when
all continue.  Hence all-Continue is the unique exact product Nash root.
Prefixing it is literally inert and preserves the suffix semantics.

The singleton margins in (36) are strict.  At all-Never, a finite unilateral
stop gives `-4` to a mobile player or `-2` to player 4, while Never gives zero.
This proves an exact equilibrium against unrestricted behavioral deviations.
Debts are nonnegative, so its actual semantic pair forces `D_*=0`.

This last fact is not cosmetic: the example cannot instantiate a maintained
`QuittingPaidCapLiftedSource`, whose structure contains
`minimum_pos : 0 < D(minimum)`, and therefore cannot instantiate its
`InertStall` or the checked Fin4 paid-cap double port.  “Exact inertness” in
the example must mean only local invariance under the unique all-Continue cap
root.  Claims that it realizes unspecified “operational parts of (2)--(5)”
should either reproduce those conditions or be replaced by the explicit
properties verified above.

## 6. Required revision and recommendation

The following replacement is accurate:

> The hypotheses force fixed labels and a finite positive-measure family of
> actual pure-time four-profile rectangles.  The first behavioral replacement
> moves only uniformly paid prescribed-law mass; both sequential replacements
> are profitable, the rectangles have a uniform positive orientation, and the
> selected family has a uniform source-weighted reach floor.  This is a
> quantitative strengthening of the generic positive-slope rectangle input,
> but it is not a fixed-law reset, cap-Nash edge, or maintained double port.

The six-state model supports the local no-go exactly as scoped: following
paid behavioral resets need not define a well-founded rank.  It says nothing
against a theorem using positive global minimum, terminal exploitability, or
the full Fin4 hard residual.

Because the new positive-measure refinement currently has no named consumer
and the local example lies outside the maintained positive-minimum class, this
packet does not contract a conjecture-facing frontier.  Keep it as a reviewed
internal result after the interface wording is repaired; do not export at
this stage.
