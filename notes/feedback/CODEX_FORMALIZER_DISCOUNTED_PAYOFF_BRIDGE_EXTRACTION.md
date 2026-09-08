# Discounted quitting payoff bridge extraction

## Scope

This is an ownership/dependency extraction, not a theorem redesign. The scratch
source `ephemeral/formalization/DiscountedQuittingPayoffBridgeAstra.lean` copies
the existing declarations below unchanged into the proposed canonical module
`UniformEquilibrium/Quitting/Bellman/Discounted/PayoffBridge.lean`. Its only
imports are discounted Fink and quitting root continuation. It has no analytic
germ, curve-selection, or polynomial Bellman dependency.

## Exact production delta for the root integrator

In `UniformEquilibrium/Quitting/Boundary/Analytic/Germ.lean`:

1. Add `import UniformEquilibrium.Quitting.Bellman.Discounted.PayoffBridge`.
2. Remove the four declarations `instFintypeStateQuittingGame`,
   `instFintypeActQuittingGame`, `instDecidableEqActQuittingGame`, and
   `instNonemptyActQuittingGame`, together with their now-empty subsection
   heading. Keep the subsequent germ-existence declaration and its heading.
3. Remove `discountedAuxEU_quittingGame_some`,
   `expect_transition_quittingGame_none`, and
   `discountedAuxEU_quittingGame_none`, including their attached docstrings and
   `omit` commands. Keep `section OneStage`, its reward variable, the subsequent
   `isεQuittingRootEndpointNash_zero_iff_of_rootRecursion`, and `end OneStage`.
4. Do not keep aliases or duplicate instances: imports preserve the exact names.

The dependent scratch `DiscountedQuittingBellmanLiftAstraV2.lean` replaces its
import of `Boundary.Analytic.Germ` with the new `PayoffBridge` and an explicit
`UniformEquilibrium.VanishingDiscount.Bellman.Variety` import. All declaration
bodies remain unchanged from the checked lift.

## Timeless header correction

Replace the opening paragraph about previously disjoint layers and obsolete
short filenames with:

> This module relates analytic Bellman germs of quitting games to their
> stationary root identities, exact endpoint complementarity, and analytic
> quit and absorption rates.

Replace the scope bullet saying germ existence does not regularize a given
sequence with:

> General analytic germ existence chooses an endpoint. The separate theorem
> `exists_analyticBellmanGerm_of_mem_closure_positiveDiscount`
> (`UniformEquilibrium/VanishingDiscount/Bellman/SpecifiedEndpointGerm.lean`)
> retains a supplied complete assignment literally when it lies in the closure
> of positive-discount polynomial Bellman solutions. A root-only source must
> still supply the complete assignment and that closure witness.

This correction does not claim that every supplied root is an analytic endpoint,
nor that a selected germ preserves an arbitrary external payoff target.
