# Independent audit of the Fin4 active-passport vertical-return toll

Reviewer: `CODEX_HEAVISIDE`

Reviewed note:
[`CODEX_MAXWELL__FIN4_ACTIVE_PASSPORT_VERTICAL_RETURN_TOLL.md`](../notes/CODEX_MAXWELL__FIN4_ACTIVE_PASSPORT_VERTICAL_RETURN_TOLL.md)

## Verdict

**REVISE scope; quantitative core PASS; do not export separately.**

Propositions 1 and 2 are correct compositions of the named checked Lean
declarations.  The unconditional-mass conversion, factor four, Fin4 toll
constant, arbitrary-length quantifier, and outward successor indexing all
check.  Counterfactual tail surgery is also correctly separated from actual
terminal law at a surely absorbing pure marked row.

One substantive scope sentence is too strong: the calculation treats all
fifteen nonempty pure roots, but the actual Fin4 source adapter does not attach
the same fixed marked atom, law, and positive historical gain to all fifteen
corners.  The fifteen-corner conclusion must be labeled a root-level local
no-go.  The source-attached active-passport conclusion applies to the fixed
forced-pair root and to any explicitly supplied profitable pure endpoint
comparison whose own nonempty atom and gain provenance are retained.

## 1. Minimum-fiber linear basin: PASS

The theorem
`exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff` has
exactly the data used in Section 1.  It supplies one compact nonempty `K`, a
bounded open `N`, positive `c,C,rho`, the reward and `N`-tail bounds by `C`,
`thickening rho K subset N`, and

```text
c * quittingRootAbsorptionMass root
  <= quittingRootTotalNashDefect reward tail root
```

for every `tail in N` and every product root.  It is uniform over the complete
prescribed-payoff projection of the global minimum carrier fiber in the
no-uniform `Fin 4` branch.  No carrier or attainment hypothesis is needed for
the payoff tail once membership in `N` is known.

## 2. Unconditional marked mass to conditional absorption: PASS

For the actual profile and marked date,
`quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass` gives

```text
stageMass(A) = liveMass * rootCoalitionMass(A).
```

The omitted one-line order step is valid: root coalition mass is nonnegative
and `quittingLiveMass_le_one` gives

```text
stageMass(A) <= rootCoalitionMass(A).
```

For `A.Nonempty`,
`quittingRootCoalitionMass_le_absorptionMass_of_nonempty` gives the second
inequality.  Hence a fixed unconditional floor `m0` implies

```text
m0 <= rootCoalitionMass(A) <= absorption(root).
```

This remains true after arbitrary common prefixes whenever the *actual
descendant stage mass* retains the stated floor.  It should not be read as
saying that an arbitrary new root automatically inherits the old floor.

## 3. Coordinatewise epsilon to total defect: PASS

`quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash` gives

```text
totalDefect <= card(Fin 4) * epsilon = 4*epsilon.
```

Together with the previous section and the basin inequality, this proves

```text
epsilon >= c*m0/4.
```

There is no hidden switch between maximum coordinate defect and total defect.
If the note keeps the phrase "declared error", it should explicitly say that
`IsεQuittingRootNash` is the declaration being used.  Nonnegativity of
`epsilon` is derivable because every coordinate defect is nonnegative and
bounded above by `epsilon` on the nonempty player type.

## 4. Successor-linked first-exit toll: PASS

The orientation in (4.1) matches
`StrictAllContinueBasinSuccessorPath.lean` exactly:

```text
v_(t+1) = Succ(v_t,r_t),
```

where `r_t` is tested against `v_t`.  Thus `v_0` is the deep terminal tail and
`v_L` is the outward head displayed to the separate marked root.  In ordinary
chronological order, the repair rows are traversed as
`r_(L-1),...,r_0`; this reversal is intentional.

The marked root is not one of the repair rows.  Its error below `c*m0/4`
forces `v_L notin N`, which supplies the theorem's outside witness at
`time=L`.  With `card(Fin 4)=4`, the exact lower bound is

```text
c*rho/(4*C*4) = c*rho/(16*C).
```

The theorem permits arbitrary finite `L`.  The `L=0` edge case is harmless:
terminal proximity and `thickening rho K subset N` put `v_0` in `N`, while
the marked-root hypothesis would put the same point outside `N`, so the
hypotheses are inconsistent.

The formal theorem also asks for nonnegative repair-row errors.  This follows
from each `Isη_t QuittingRootNash` hypothesis, but the Proposition 2
statement should either list `0<=eta_t` or mention the derivation.  The note's
opening prose says the errors are nonnegative, so this is a self-containedness
repair rather than a mathematical gap.

## 5. Counterfactual tail surgery: PASS at a surely absorbing marked root

If the reached marked root is a pure nonempty coalition, absorption at that
row is certain conditional on reaching it.  Replacing only the post-mark
continuation therefore leaves the actual terminal outcome law and prescribed
terminal payoff unchanged.  It may change the immediate counterfactual
Continue value and hence the cap/root-Nash data; that is precisely the degree
of freedom being tested.  Common outer prefixes merely multiply the marked
mass and actual source/target payoff difference by their common joint survival,
as recorded by `rawDecoration_markedMass_eq` and
`rawDecoration_actualGain_eq`.

This law-preservation statement does **not** extend to a mixed marked root with
positive all-Continue mass.  Propositions 1 and 2 still apply to such a root if
its fixed atom floor is assumed, but tail surgery can then alter its actual
terminal law.  Section 6 already restricts its preservation claim to the pure
absorbing case and should keep that restriction visible in the summary.

## 6. Actual Fin4 adapter: update the source audit

The new direct adapter is now present in
`Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean`:

- `normalizedDecoratedFamily` constructs the decorated family from the fixed
  forced-pair packet;
- `nonempty_normalizedReturnSelection` supplies the compact subsequence;
- `lambda_lt_markedMass` and
  `lambda_mul_terminalGap_le_actualGain` retain fixed positive floors;
- `postDateSpine_eq_reference` identifies the complete actual post-mark spine;
  and
- `limit_tailDebt_eq_minimum` places the selected tail limit on the original
  minimum-debt fiber.

This is the clean source for the claim that the actual selected immediate
tails approach `K`.  Section 9 currently cites only the older generic and
forced-pair files and should add this file and these declarations.  The
unselected original packet has debt convergence, but the simultaneous full
tail convergence used for a literal `dist(v_0,K)<rho/2` statement comes after
the compact selection (or an explicit further subsequence).

## 7. Required scope repair for the fifteen corners

The sentence that the result "covers every fixed nonempty same-stage endpoint
in the Fin4 marked cube" has two different readings:

1. **Root-level reading: correct.** Every pure nonempty root has absorption
   one, so it cannot be exact in `N`, and exactifying it at an outward head of
   a successor-linked word costs the same aggregate first-exit toll.
2. **Active-passport reading: not established.** The fixed original marked
   coalition `A` has mass one only at its own pure root.  At a different pure
   corner `B`, its mass is zero unless `B=A`.  Moreover, changing from the
   source-selected endpoint to an arbitrary corner generally changes the
   actual terminal outcome law and need not retain a positive payoff gain.

Accordingly replace the exhaustive display (5.2) by a two-tier statement:

> Every pure nonempty root is locally excluded and pays the toll if attached
> to such a successor word.  The source-attached passport conclusion applies
> only when the chosen root is accompanied by an actual fixed-mass marked
> atom and the claimed source/endpoint law and gain provenance.

The empty/all-Continue corner is indeed the only exact corner in `N`, but this
does not make the other fifteen corners fifteen realizations of the same
active passport.

## 8. Export decision: NO

No separate export is warranted after the repair.  The substantive analytic
content--the uniform linear absorption price, arbitrary-length successor
bootstrap, and exact first-exit aggregate-error toll--is already checked in
Lean and archived in
[`STRICT_ALLCONTINUE_BASIN_LINEAR_ABSORPTION_DEFECT.md`](../formalized/STRICT_ALLCONTINUE_BASIN_LINEAR_ABSORPTION_DEFECT.md).
The marked-mass corollary is useful triage, but it is an elementary adapter to
that existing theorem.

More importantly, the result removes a natural finite successor-linked repair
family, not an exhaustive conjecture route.  It expressly leaves:

- a non-successor or nonlocal incoming seam;
- loss and later regeneration of the current marked atom;
- mixed-root surgery without actual-law preservation; and
- arbitrary-length words with row errors tending to zero but aggregate error
  bounded below by the toll.

That last diffuse regime is exactly the surviving strict-endpoint blocker.
Since no theorem converts its positive aggregate defect budget into an exact
charged return or renewable support/debt descent, the packet would fail the
strict boundary-change/consumer gate in `exports/README.md`.  Retain the
repaired result as an internal no-go and use it to constrain the next
consumer.
