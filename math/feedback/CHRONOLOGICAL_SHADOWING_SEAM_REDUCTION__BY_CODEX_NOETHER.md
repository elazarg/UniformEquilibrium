# Export-gate review of chronological shadowing seam reduction

Reviewer: `CODEX_NOETHER`

Reviewed packet: `exports/CHRONOLOGICAL_SHADOWING_SEAM_REDUCTION.md`.

## Verdict

**REVISE before retaining in `exports/`.**  Theorems A and B are valid,
self-contained ordinary mathematics and do strictly narrow the conditioned-
packet seam obligation.  Their proofs, unrestricted-cap semantics, clock
quantifiers, and constants check.  I found no mathematical objection to
Theorem C either.

The packet nevertheless misses the export gate as written for one material
novelty reason: Theorem C's semantic endpoint is already supplied by the
checked `QuittingInfinitePathHazardScaledResidualCertificate` compiler, and
the packet names no downstream consumer that needs the chronological
certificate translation rather than that direct result.  A structure-level
repackaging without a distinct consumer is not a strict conjecture-boundary
change.  The clean repair is to remove Theorem C from this export (retaining
it in Cedar's note), retitle the packet around summable seams/rigidity, add one
explicit positive Theorem A regression, and make the small source-reference
repairs below.  Theorems A--B then qualify as a narrow reduction.

This is a revise verdict, not demotion of the seam result.

## 1. Mathematical audit of Theorem A

For successor pairs `X=(u,b)` and `Y=(u',b')`, the prescribed prefix differs
by exactly `J(u-u')`.  The cap prefix is

```text
H_i(z)=max(Q_i,C_i+O_i z),
```

so it is globally `O_i`-Lipschitz, including a maximizing-branch switch.
Subtracting prescribed payoff gives the stated debt estimate.  At an internal
row the candidate recursion is exact; at seam `k` this yields

```text
|P_(k,i)|<=A_(k,i),
|E_(k,i)|<=A_(k,i)+B_(k,i).
```

Every finite calendar interval intersects only a subset of the seams, so the
global `l1` budgets imply the required absolute prescribed discrepancy.
Generated secant weights lie in `[0,1]`; hence every adverse direct-forcing
sum is at most the absolute direct-defect budget.  Bounded prescribed values
and bounded nonnegative debt also bound candidate caps.  Initial debt and the
two literal survival assumptions give the remaining certificate fields.

The flattening order, every-suffix quantifiers, and constant `eta` are all
correct.  No candidate pair is silently assumed executable.

## 2. Mathematical audit of Theorem B

The actual infinite suffix pair obeys the exact prefix recursion.  Iterating
the prescribed difference recurrence leaves a boundary term weighted by
joint survival; iterating the cap difference recurrence leaves one weighted
by player-deleted survival.  Both terminal differences are uniformly bounded,
so item 5 kills them.  Dropping earlier weights in `[0,1]` proves (7)--(8),
and debt subtraction proves (9).

Applying the positive actual-debt floor to the literal concatenated profile,
using candidate-debt nonnegativity, gives (11).  Under Theorem A, initial debt
and total seam price contribute at most `eta` each per player, so
`Delta<=2|I|eta`.  The result correctly says that bounded artificial seams
already carry endpoint-strength semantic content; it does not claim a source
producer.

## 3. Mathematical audit of Theorem C

The diagonal prefix debt `g_(t,i)` is nonnegative because the prescribed
mixed action is a convex combination of the two pure current actions while
the cap takes their maximum.  Exact prescribed Bellman evaluation kills the
prescribed defect, zero candidate debt makes the direct defect `-g`, and the
generated secant satisfies `0<=s<=O`.  Therefore

```text
w g <= eta*w*(1-O) <= eta*w*(1-s)=eta*(w-w'),
```

which telescopes from every calendar start and through every finite horizon.
The `O=0` and `O=1` boundaries are handled without division.  Thus Theorem C
is valid ordinary mathematics.

Validity is not the export issue.  The packet itself records that
`QuittingInfinitePathHazardScaledResidualCertificate.isεAsymptoticNash_and_delivers`
(`UniformEquilibrium/Quitting/Paths/HazardScaledResidualCompiler.lean`)
already reaches the semantic endpoint from the hazard-scaled residual datum.
The only claimed increment is translation into
`QuittingChronologicalDebtShadowingCertificate`, but no actual adapter or
consumer is named which can use that structure while the checked direct
compiler cannot use the same root/value/gap hypotheses.  Theorem C is also
seam-free, so the phrase that it can be combined with Theorem A's source-
matching boundary is not presently a proved composition.

Under export gate 4/6, that is insufficient novelty.  Either omit Theorem C,
or supply a genuinely distinct checked consumer/source interface for which
the certificate translation changes the live obligation.  The current packet
supplies no such interface, so omission is the honest repair.

## 4. Why Theorems A--B do strictly narrow the boundary

Theorem A changes the named conditioned-reprojection obligation from uniform
control at every row to:

1. exact arbitrary-candidate Bellman recursion inside finite literal blocks;
2. two countable coordinatewise `l1` seam budgets; and
3. the already-separated literal clock fields.

The existing `QuittingChronologicalDebtData.exactOfRoots` does not do this:
it forces the candidate debt to be the actual concatenated profile's debt,
whereas Theorem A permits nonsemantic candidate blocks with artificial small
initial debt.  Theorem B then exactly measures the unavoidable semantic toll.
This is a precise reduction and a sharp diagnostic of that same live source
problem, even though production of the seam data remains open.

The source audit correctly distinguishes the same-profile finite-window and
reset-reprojection declarations from a summably matched sequence of moving
block endpoints.  No paper overlap is claimed.

## 5. Remaining packet repairs

1. **Add a positive Theorem A regression.**  The boundary section currently
   contains good falsifiers and necessity tests but no explicit finite table
   instantiating the arbitrary-candidate seam constructor.  A minimal exact
   test uses the zero-reward two-player game and sure-absorption product rows:
   `J=O_i=0` makes each block source independent of an arbitrary bounded
   donated endpoint, so summable nonzero donated endpoint seams coexist with
   zero actual defects, zero initial debt, and immediate joint/deleted clock
   death.  State it fully, or give a more informative positive seam example.
2. **Correct formula (1) notation.**  In a quitting row, forced Quit absorbs,
   and the opponent-absorption contribution under forced Continue is also
   terminal.  Thus `Q_i` and `C_i` do not read successor prescribed payoff
   `u`; write `Q_i(q)` and `C_i(q)`, leaving only `O_i(q)b_i` as the cap's
   successor dependence.
3. **Name the noncompositionality declaration.**  The boundary test cites only
   `TerminalSemanticCommonWitnessNoncompositionality.lean`.  Project policy
   requires a declaration name and file.  Supply the exact declaration(s), or
   make the example self-contained in the packet.
4. **Retitle after removing Theorem C.**  A title such as “Summable artificial
   seams compile chronological shadowing” accurately describes the qualifying
   result and avoids advertising the duplicate normalized-gap endpoint.
5. **Keep the source-production nonclaim.**  The current packet is correct
   that no checked declaration maps arbitrary atom access to summably matched
   blocks.  Do not add an `A` seal or imply that independent frozen packets
   form one reached chronology.

## 6. Probability, deviation, and consumer audit

The packet correctly fixes product randomization at each row, the unique live
public history, simultaneous Quit coalitions, Never mass, and unrestricted
behavioral deviations.  The cap is a supremum over the deviator's complete
behavioral strategy and need not be attained.  The max-affine one-row recursion
therefore has the right strategy-class scope.

For Theorem A, the downstream declaration
`quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors`
is the right named consumer, and
`QuittingChronologicalDebtShadowingCertificate.isAsymptoticNash` supplies the
all-behavior terminal endpoint.  Together with the two-label survival adapter,
this is a complete consumer chain for supplied seam data.  It does not supply
the missing source data.

## Final gate recommendation

**REVISE:** keep Theorems A--B; remove Theorem C from the export; add one exact
positive seam test; repair the two source references.  After those bounded
changes, the packet makes a strict, independently reviewed reduction of the
conditioned-packet/chronological-shadowing boundary and is appropriate for
`exports/`.  Without them, the combined packet overclaims novelty through an
already checked hazard-scaled semantic compiler.

