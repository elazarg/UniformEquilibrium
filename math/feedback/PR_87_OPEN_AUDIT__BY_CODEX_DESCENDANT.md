# PR #87 open audit

Reviewer: `CODEX_DESCENDANT`  
Date: 2026-08-31  
Recommendation: **close as superseded; do not merge or cherry-pick**

## Scope inspected

PR #87, `Collapse Fin4 law-tight minimum to full debt or reset rigidity`, has
head `5c263084f499ee53b8cdced1e740345b096a5373` and was based on
`bdbfe5b7047067c36197f25fb34bc8ab981798b2`.  It adds
`FinFourLawTightCapNashMinimumFiberCollapse.lean` and imports that leaf directly
from the diagnostics umbrella.

I compared its theorem and proof with current main at `831e82a`, in
particular:

* `LawTightCapNashGlobalMinimumMoat.lean`;
* `FinFourLawTightCapNashStrictMinimum.lean`;
* `TerminalSemanticFinFourMinimumFiberIsolation.lean`;
* the current diagnostics umbrella, axiom audit, and generated frontier/toolkit
  entries; and
* commit `5387eb0`, `Reduce law-tight global minima to two chambers`.

## Mathematical verdict on the PR

The PR's mathematical argument is sound.

1. The selected hull minimum has debt at most the hull origin because the
   origin belongs to the hull.
2. The origin globally minimizes carrier debt, so the hull minimum has debt at
   least the origin debt.
3. Hence the selected hull minimum is itself a positive global minimum.
4. Punishment normality and the global-minimum strict-singleton theorem give
   prescribed payoff strictly above every own singleton reward.
5. In the singleton/Never branch, the owner has zero debt and cap equal to its
   singleton reward.  Therefore its prescribed payoff also equals that reward,
   contradicting the strict inequality.

This correctly deletes the singleton/Never binding-cycle chamber and leaves
only full positive-debt support or the same-law reset-rigid chamber.  It does
not consume either surviving chamber and supplies no behavioral realization,
chronology, terminal approximation, or uniform-equilibrium payoff.

## Current-main overlap

The result has already landed in a more modular and quantitatively stronger
form.

`lawTightCapNashMinimum_globalMinimumOriginDebtMoat` proves the generic hull
inheritance theorem and the quantitative cap moat

\[
D(\mathrm{origin})\le B_i(\mathrm{minimum})-r_i(\{i\})
\]

for every player.  The Fin4 capstone
`finFour_noUniformPayoff_exists_lawTightGlobalMinimumMoatTwoChamber` retains:

* origin and selected minimum;
* positive origin and minimum debt;
* the positive finite atom;
* global minimality of both semantic points;
* equality of their debts;
* the quantitative singleton moat; and
* exactly the same full-debt/reset-rigid dichotomy.

The PR's only superficially different output is the strict prescribed-payoff
inequality.  It is not unique information on current main:
`exists_finFour_minimumFiberIsolation_and_debtMoat_of_no_uniformPayoff`
supplies a uniform positive prescribed-payoff singleton gap on the entire
global minimum fibre, as well as an open unique-all-Continue cap tube and a
positive carrier debt moat.  Thus current main strictly subsumes both the
branch deletion and the extra strict-payoff field.

Current main also integrates the result through
`Diagnostics/Quitting/All.lean`, `AxiomAudit.lean`, `docs/FRONTIER.md`, and
`docs/TOOLKIT.md`.  The PR instead adds a second competing leaf and a direct
umbrella import, which would duplicate the already maintained theorem surface.

## Checks and branch status

At the PR head:

* exact-source artifact check passed;
* Lean setup and the changed Lean targets passed;
* documentation, unit tests, experiment registry, import graph, duplicate,
  reward-bound, order-hypothesis, and telescope checks passed;
* both CI jobs ultimately failed at the trust scan; and
* the PR has no reviews and remains a draft.

The trust failure is not needed to decide disposition, because the complete
mathematical content is already on current main under the maintained module
names and theorem API.  Rebasing this old branch would create duplication,
not recover missing mathematics.

## Remaining gaps

Closing PR #87 loses no live route.  The exact unresolved mathematics remains
the consumption of the two surviving chambers:

* full positive-debt support; and
* reset-rigid same-law minimum.

PR #87 contains no consumer, renewable rank, counterexample certificate, or
source-chronological connector for either arm.

## Recommendation

Close PR #87 as superseded by commit `5387eb0` and subsequent minimum-fibre
isolation work.  There is no useful commit or declaration to transplant.
