# The relative-boundary producer: owner-solo certification and the refined exceptional object

Date: 2026-08-03.  Context: the positive branch of the exact dynamic-debt
split (`28df2d0`), the provenance and quantitative residual-depth-one packet
(`4600601`, `0ab9d31`), and the certified-boundary scalar reinsertion core
(`801095a`). Companion Lean experiments in this directory:
`UniformEquilibrium/Quitting/Punishment/OwnerSoloCertification.lean` and
`QuittingReinsertionPenaltyBound.lean`.

## 1. Chain-geometry insufficiency

The machine-checked two-player vanishing counterexample
(`UniformEquilibrium/Quitting/Debt/Dynamic/ExactDynamicDebtVanishingCounterexample.lean`, table
`QC ↦ (1,0)`, `CQ ↦ (3,−1)`, `QQ ↦ (2,1)`) forces every positive-length
zero-boundary exact Nash–Bellman chain through exactly two values: the trap
`(3/2, 0)` at every live date and `0` at the boundary.  Its uniform
equilibrium payoff `(1, 0)` is **not in that set**.  Consequence: no
producer that only compactifies, re-roots, reverses, or otherwise takes
limits of zero-boundary chain data can be complete — the certificate value
must be injected from outside the chain geometry.  Any proposed producer
architecture should be tested against this fact first.

## 2. Certify the owner's deviation

Q129 identifies the positive-debt owner's optimal deviation: Continue
through the prefix, then take the terminal solo option.  The producer move
tested here is to *promote that deviation to prescribed play*: the owner's
solo stationary root at rate `p ∈ (0,1]`.  Its terminal payoff vector is

    (q_i for the owner, r_j({i}) for each opponent j)

— exactly the value of the deviation whose exploitability the debt
measured.  The exact certification criterion is machine-checked
(`isεAsymptoticNash_soloStationary_exact`):

- owner: `0 ≤ q_i = r_i({i})` (the provenance layer forces `0 < q_i` for a
  positive-debt owner);
- each opponent `j ≠ i`:  `(1−p)·r_j({j}) + p·r_j({i,j}) ≤ r_j({i})`.

Under these, the solo root is an **exact** terminal Nash equilibrium, and a
new generic delivery lemma
(`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact`,
generalizing the counterexample's hand-rolled ending) makes its own
terminal payoff a uniform-equilibrium payoff.

Counterexample instantiation (nonvacuity probe): owner 1, opponent 2 has
`(1−p)(−1) + p(1) = 2p − 1 ≤ 0 = r_2({1})` iff `p ≤ 1/2`.  So the feasible
rate set is `(0, 1/2]`, and the repo's known stationary equilibrium at
`p = 1/2` is its boundary point.  The criterion is neither vacuous nor
slack.

## 3. The dichotomy and the refined exceptional object

Machine-checked capstone
(`uniformPayoff_or_universalJoining_of_positiveDebt`): positive exact
dynamic debt for `owner` at any live date of any admissible zero-boundary
chain implies

- **either** `quittingSoloReward reward owner` is a uniform-equilibrium
  payoff (the game is closed),
- **or** for every rate `p ∈ (0,1]` some opponent `j` strictly prefers
  quitting against the owner's solo rate:
  `r_j({i}) < (1−p)·r_j({j}) + p·r_j({i,j})`
  (`QuittingSoloJoiningObstruction`).

The positive-debt exceptional object therefore refines to: projective
exact-debt tail, fixed owner `i` with `q_i > 0`, summable opponent clock,
positive-mass full-set terminal advantage packet, **and a universal joining
obstruction against the owner's solo family**.

Witness structure of the obstruction (affine in `p`):

- at `p = 1`: some `j` with `r_j({i,j}) > r_j({i})` — a strict sure-quit
  joiner (machine-checked extraction,
  `exists_sure_joiner_of_universalJoining`);
- as `p → 0⁺`: by finiteness of opponents, some fixed `j` with
  `r_j({j}) ≥ r_j({i})` — a weak preemptor (machine-checked by the finite
  minimum-gap theorem `exists_weak_preemptor_of_universalJoining`);
- feasibility of the left branch is a one-variable rational LP, so the
  whole dichotomy is decidable per owner from the table.

## 4. Consumer completion: the depth-free mismatch penalty

On the landed Q131 scalar core, the sharp penalty bound is
machine-checked
(`quittingFiniteRelativeBoundaryExploitability_le_debt_add_penalty`):

    exploitability(error) ≤ debt + (χ − P)·error⁺ + P·(−error)⁺ ≤ debt + |error|

with `P` full prescribed survival and `χ ≥ P` opponent-only survival, and
no dependence on prefix length.  Together with the in-flight exact-match
identity (`exploitability(0) = debt`), the scalar consumer of certified
boundary reinsertion is complete: any certified tail splices into any exact
prefix at cost `debt + mismatch`.

## 5. Consequences for the producer search

1. **Positive route.**  The producer now has a concrete first candidate
   drawn from the debt object itself, and a decidable test for it.  When
   the solo family fails, escalation candidates in order of expressiveness:
   set-First certificates (`S ∋ i` quits at once; finitely many `S`,
   table-decidable), pair/set stationary mixtures (the sure-joiner `j`
   suggests engineering `j`'s indifference — the Solan–Solan LCP
   landscape), then the periodic/rotation families (Q121 accuracy-indexed
   density; FTV shows rotation can be genuinely necessary).  A useful next
   theorem would make one escalation step exact: from the universal joining
   obstruction, either a pair-stationary certificate exists or a further
   quantified obstruction holds.

2. **Negative route.**  A four-player barrier candidate must now pass a
   sharper filter, all semialgebraic in the table: (i) positive optimized
   zero-boundary debt (the chain layer), and (ii) universal joining
   obstruction for every owner the provenance layer can force.  This is a
   concrete, implementable screen for the direct search — tables failing
   either test are closed by landed or newly checked compilers.

3. **Composition gap (open).**  The joining obstruction has not yet been
   composed with the summable-clock/packet structure of the extracted tail.
   The packet says opponents place terminal mass on full-set quits the
   owner would rather ride than join; the obstruction says some opponent
   wants to join the owner's exit.  Whether these two forces can be played
   against each other (e.g. to build the pair-stationary certificate or to
   force a contradiction with chain optimality) is the sharpest next
   mathematical question — proposed as the Q132 seed.

4. **Repair cycles must carry continuation certificates.** A useful lasso is
   not a cycle of player names or incentive signs. Each phase must carry an
   actual finite block and a payoff/cap pair ((w^k,\beta^k)). If the block's
   playerwise summary is ((A_i^k,T_i^k,\chi_i^k,B_i^k,P^k)), chronological
   compatibility and credibility require

   \[
   w_i^k=B_i^k+P^k w_i^{k+1},
   \]

   \[
   \max\{A_i^k,T_i^k+\chi_i^k(w_i^{k+1}+\beta_i^{k+1})\}
   \le w_i^k+\beta_i^k.
   \]

   Exact cycles take (eta^k=0). They must retain the full terminal-packet
   action and scale, verify every quitter's Bellman inequality directly, and
   have playerwise opponent contraction or an explicit exceptional-owner
   stationary/First closure. This is the correct escalation after the solo
   LP fails.

## 6. Status and caveats

- Both experiment files pass `lake env lean` against the current working
  tree. Their provenance and reinsertion dependencies are committed and
  publicly imported; the owner-solo and penalty wrapper files themselves
  remain experiments pending production promotion.
- The dichotomy certifies from a single owner; distinct owners at distinct
  dates each get their own instance.
- Nothing here is umbrella-routed or committed; these are experiments
  pending review under the program's usual audit discipline.
