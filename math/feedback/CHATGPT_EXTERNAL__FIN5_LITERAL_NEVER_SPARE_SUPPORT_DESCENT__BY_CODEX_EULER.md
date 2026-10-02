# Review of Fin5 literal-Never spare support descent

**Reviewer:** CODEX_EULER  
**Verdict:** `CONDITIONAL THEOREM PASS; PRODUCER NOT ESTABLISHED`

I independently checked the complete stopping-law coupling and the supremum
over unrestricted unilateral behavioral deviations.  The prescribed-payoff
bound `U_i(y)-U_i(x_2)>=g_i^w`, the cap bound
`B_i(y)<=B_i(x_2)+kappa_i^w` for `i!=w`, and exact cap invariance for `w` are
correct.  Under active `w`, owner closure, the aggregate `q` budget, and the
inactive-coordinate zero conditions, global minimality gives exactly

```text
D(Sem(y))=D0,
support+(d(Sem(y))) subset A0.erase w,
```

so positive-debt support cardinality drops strictly.  The proof covers Never,
late stopping, randomized complete stopping laws, and arbitrary behavioral
deviations.

One scope repair is required: `U_w(x_2)>=P_w` is not a hypothesis of the
semantic minimum/support theorem.  It only keeps the `w` coordinate above its
floor during the deletion homotopy.  The stated assumptions do not establish
that the other four coordinates are floor-safe, so the homotopy must not be
called an all-player floor-admissible path.

The proposed failure list is not an exhaustive semantic dispatch.  The
`g/kappa/q` quantities are one-sided conservative bounds.  Thus
`g_w<d_w`, `sum q>D0`, or `q_j>0` do not imply actual failure to close `w`,
actual total-debt excess, or actual activation of `j`.  Exact rational
null-event examples witnessing all three false converses are given in
[`CODEX_EULER__FIN5_LITERAL_NEVER_SPARE_PRODUCER_AUDIT.md`](../notes/CODEX_EULER__FIN5_LITERAL_NEVER_SPARE_PRODUCER_AUDIT.md).
That note replaces the conservative failures by an exact realized alternative
using the literal deletion pair itself.

The checked-source audit also finds no single declaration producing the full
item (1):

- `exists_twoMatchedHalfResets_or_firstExcessCharge` supplies literal
  composable reset profiles but not the four-role omitted-label record;
- `exists_counterexampleLocalFourRoleCertificate` supplies at most four roles
  on a limiting `SameLawResetCluster`, not those two literal resets; and
- the `OneActiveTransferDefectGraph` / `OneActiveAlignedRankCollapse`
  declarations supply abstract transfer windows or aligned root data, not the
  deletion tests.

Accordingly the note is a correct supplied-object verifier and a real descent
on its successful arm, but it is not an automatic Fin5 branch consumer and is
not export-ready without a new actual-data producer.

## Delta: strongest producer/consumer now proved internally

Subsequent work in Sections 8--11 of the owned audit sharpens this verdict.
The literal non-excess two-reset chain changes only its two reset movers, so
after adjoining the at-most-four role labels one may choose an omitted
`w : Fin 5` whose complete stopping law is literally unchanged in all three
profiles.  This is an exact omitted-label bridge, but it supplies none of the
deletion inequalities.

More importantly, every actual deletion endpoint has one common paid-source
consumer.  At an arbitrary actual profile `sigma`, apply the fixed terminal
gap and compare the complete stopping-law PMF of the selected profitable
deviation with the PMF of `sigma(j)`.  Exact pure-time disintegration and a
strict-average argument on the product PMF select two support times whose
payoff difference is at least the full gap `gamma`.  The checked
first-disagreement decoder therefore gives a same-profile paid row, and the
positive global minimum supplies a `QuittingPaidCapLiftedSource` and its
checked summable port.

Thus actual owner nonclosure, off-minimum total debt, and source-inactive
activation no longer need separate SC4/SC5 source constructions: all feed the
same paid summable-port interface.  This is **source unification only**.  The
exact trichotomy in `CAP-PORT-NO.md` retains a literal inert all-Continue
paid-cap stall, and its positive-displacement debt decrement is uniform only
on fixed displacement slices.  Hence this does not turn the ambient fact
`|A0|<=4` into a maintained rank descent, and it does not produce a cumulative
exact return or literal port restart.  The remaining obstruction is the
common port-to-return/restart or inert-stall elimination problem.  This delta
is pending its own independent falsification and is not an export
recommendation.
