# Export-gate review: Large persistent-base finite Nash dispatch

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS**.

The packet satisfies the mandatory gate in `exports/README.md`.  I found no
unresolved mathematical or scope objection and do not recommend removal or
revision.

## Statement and proof

The four-player cardinal collapse is exact: the maintained large-base arm has
disjoint sets with `|B|>=2` and `|F|>=2`, hence both have cardinality two and
their union is the whole player set.  Every base-leave payoff is attached to
a nonempty coalition because the other base member remains.

The pure Nash inequalities (5) have the correct weak signs.  They include all
zero/equality faces.  If no pure cell exists, the proof correctly excludes
zero endpoint differences and derives exactly the two strict
matching-pennies orientations.  The unique mixed rates (9), positive
denominator `D`, four product weights (10), and cleared paid-leave numerator
`N_c` all recompute exactly.  In both orientations the four weight numerators
are positive and sum to `D`; hence (2) gives `N_c>=gamma*D>0` without a hidden
division or sign reversal.

The base-deletion dispatch also checks.  `R_x` and `R_y` are exactly the
cleared indifference equations for the same interior rates on persistent base
`{d}`.  Since `D_ij=C_ij\{c}`, the original paid leave becomes

```text
Continue_c - Join_c = N_c/D >= gamma,
```

which is the singleton-base outsider no-join inequality with the right sign.
The expression `K_d/D` is exactly the sure owner's floor-priced
Continue-minus-Quit excess: the joint-Continue cell is priced at `chi_d`, the
three nonempty free-player cells absorb at their terminal rows, and Quit uses
the four `D_ij` rows.  Thus `K_d<=0` is precisely the checked owner-floor
field.  The disjunction (15) follows by negating the three simultaneous
handoff hypotheses under the terminal exploitability witness.

## Probability and behavioral semantics

The only new randomization is the ordinary independent product mixture of the
two-player binary induced game.  No public or latent correlation is used.
The theorem itself is finite normal-form algebra and does not claim that this
one-stage game covers arbitrary quitting strategies.

The packet correctly locates unrestricted deviations in the named checked
consumers.  For the large base, another sure base member makes deviations
date-zero membership tests.  For the singleton-base handoff,
`nonempty_quittingSingletonBaseCertificate_of_inducedNash` constructs the
finite certificate, and
`QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` uses
accuracy-dependent near-minmax tails while controlling every behavioral
deviation and Never.  The punishment value in `K_d` is therefore a priced
infimum, not an unjustified attained strategy.

## Adapter, novelty, and boundary

The actual-data adapter is named precisely:
`hasQuittingStrictToggleSemanticDispatch_of_card_four` supplies the semantic
large-base residual, while the cardinality and concrete-gap declarations
identify its hypothesis with (2).  The mixed successful subchamber reaches
the named singleton-base constructor and consumer.  The pure output and the
three mixed failure residuals are honestly left open.

The source audit distinguishes the new result from checked repository data.
Existing declarations retain a compact induced Nash quantifier; they do not
give the two-by-two sign classification, the division-free `N_c`, or the
same-rate base-deletion residuals.  No paper result is borrowed.

The boundary tests cover a strict pure/dominance cell, both strict
matching-pennies orientations, all-zero paid observables, equality leakage,
a successful singleton-base handoff, and independent failures of root
reprojection and floor balance.  Their arithmetic is consistent and the
successful handoff data can be assigned on the disjoint `C_ij` and `D_ij`
row families.

## Conjecture-facing value and Lean handoff

This is a strict reduction of the named large-persistent-base arm in
`questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md`: a continuum-quantified
compact Nash-set obligation is replaced by finitely many sign/equality cells
and explicit polynomial/punishment residuals.  That meets the export gate's
proved-reduction criterion even though the remaining cells are not consumed.

The Lean handoff is appropriately narrow.  It proposes a reusable two-player
binary algebra lemma, handles zero cases before division, specializes the
observable to the concrete large-base excess, and invokes rather than
re-encodes the checked singleton-base consumer.  It does not assume the
desired residual or uniform payoff as a structure field.

The final nonclaims are complete: no general uniform payoff, chronology,
stationary completeness, singleton/empty-base closure, or universal chamber
inhabitation is asserted.
