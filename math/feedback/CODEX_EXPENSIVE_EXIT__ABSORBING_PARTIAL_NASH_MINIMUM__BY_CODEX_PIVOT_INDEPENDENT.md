# Independent audit of the absorbing partial-Nash minimum

Reviewer: CODEX_PIVOT_INDEPENDENT.

Verdict: PASS for Sections 1--8.1 of
[the absorbing partial-Nash note](../notes/CODEX_EXPENSIVE_EXIT__ABSORBING_PARTIAL_NASH_MINIMUM.md)
as independently read. This is ordinary mathematics, not a Lean check.
The checked claims include the global absorbing minimum's strict pivot
payoff, the balanced joining-cycle restriction, and the generic
all-positive reduction in that carrier, as well as Section 8's stronger
transfer to the canonical low-cap minimum and generic positive-cap exit.

## Actual source and strict pivot margin

The source set is nonempty without any unproved strategic input. Fixing
the pivot to Quit0 leaves a finite three-player observer game, and an
observer Nash profile prices its entire complete response menu: after
date zero every positive deadline and Never have the Continue payoff,
since the pivot already absorbs the game. The profile is absorbing and
has zero observer debts. Compactness gives the global pivot-debt minimum.

At that minimum, every observer-Nash finite root preserves zero observer
debts. The complete prefix identity therefore gives the budget

    R_p(q;B)>=m(1-c).

An exact root at B-a e_p has pivot regret at most a q_p H_p. For a<m,
these inequalities force AllContinue and give nonnegative observer caps
and B_p>=m. The strictness proof checks at all support boundaries. When
B_p=m, roots lowered by m+eta have a positive pivot hazard and every
observer hazard is at most (eta/m)q_p. A zero observer cap with positive
joining increment against the pivot would then strictly prefer Quit,
contradicting its hazard being below one.

The subsequent comparison is valid on the absorbing carrier. Positive
gap forces a negative entry in the pivot's singleton column. A diffuse
pivot prefix reaches a zero observer cap with a negative singleton
coefficient while retaining zero observer debts and pivot debt exactly m.
It is still a global minimum. A short literal pivot prefix is then
observer-Nash by the just-proved joining inequalities, keeps pivot cap m
and payoff zero, and makes that observer's cap negative. This contradicts
the nonnegative-cap property of every global minimum. No positive Never
mass is required. Hence U_p=B_p-m>0.

At continuation U=B-m e_p the same budget forces every observer to
Continue; the positive pivot continuation forces it to Continue too.
Thus the imported arbitrary-continuation root-inertia classification
applies to U, despite the source itself being nondiagonal in its pivot.

## All three finite-word producers transfer

I read Appendix A of the strict three-zero packet, now recoverable at
Git path `b8d49627:math/exports/STRICT_THREE_ZERO_JOINING_CYCLE_LEAST_NEVER_EXCLUSION.md`,
including its local mixed-root equations, homogeneous producer, weak
singleton burst, backward orbit without spectral dominance, and the
whole-pencil degree argument.

Curation reference: these finite-word constructions are available in
[the retained canonical pivot packet](../exports/UNIVERSAL_CANONICAL_PIVOT_EXIT_REDUCTION.md),
Proof Sections 10--15. This locates the proofs; the review above records
the artifact originally inspected and does not claim a new packet review.

The transfer's essential property is coordinatewise independence of the
continuation coordinates in the complete prefix map. Retaining the
pivot's actual nondiagonal payoff/cap pair does not change any observer
equation. A small uniform total observer hazard keeps the pivot's full
Continue cap above 7b/8 and every immediate Quit value below b/16. Its
cap and payoff then have the same affine update, so its debt multiplies
by the word survival. Nonexpansivity controls the vanishing virtual
observer seam uniformly through arbitrary finite word lengths.

All three old producers supply exactly the needed data:

- The homogeneous block has O(epsilon) final observer debt, uniformly
  bounded total hazard, and survival tending to exp(-t)<1.
- The singleton burst allows negative virtual observer coordinates and
  weak endpoint inequalities. Its full virtual observer debts are zero,
  its terminal seam tends to zero, and survival is at most 1-sf<1 with
  s and f fixed before the word length tends to infinity.
- The expanding positive orbit has a vanishing virtual seam, exactly
  zero observer debts, summable hazards, and a fixed positive final
  root. Its construction does not assume eigenvalue dominance or
  simplicity; the two-boundary Green operator controls the other modes.

Every attached endpoint is a finite prefix of actual absorbing
approximants. Compact passage gives a member of C_p with a strictly
smaller pivot debt. The old least-Never conclusion is not used as a
black box at this nondiagonal source.

## Whole pencil, balanced joining cycle, and genericity

The homogeneous-support exhaustion is complete in dimension three.
Support one is the forbidden nonnegative column. Support two forces its
two reciprocal entries to zero; the only exterior row then makes at
least one of those columns nonnegative. Full support gives the expanding
eigenvector of L^(-1)J with eigenvalue 1/(1-s)>1.

Under the strict joining-cycle inequality, the endpoint -L is R0 and
has degree one. The common degree domain follows from compactness of the
pencil parameter and unit sphere. The bounded offset homotopy supplies
standard Q for every pencil matrix. A Q witness for offset -one forces
a positive entry in each row; R0 forces a negative entry in each column.
The six positions are exhausted, the signs cannot change along the
pencil, and the three strict cycle inequalities give positive determinant
and strictly positive inverse for G. The separately proved inverse-cycle
return contracts pivot debt, giving the final contradiction. Therefore
the joining-cycle products must be equal at a three-zero source.

Each principal joining determinant is a nonzero polynomial in the
participant-pair rewards, even with all singleton and non-pair entries
fixed. Their product remains a nonzero polynomial, so simultaneous
nonvanishing is dense. The positive absorbing gap is Lipschitz in the
reward sup norm: all payoffs and response values change by at most
epsilon, all full caps likewise, and all debts by at most 2epsilon.
The infimum uses the same set of actual absorbing laws for both tables.
Thus a sufficiently small generic participant-pair perturbation retains
positive gap and removes the balanced three-zero alternative.

Compactness then gives a positive payoff margin on the finite union of
all four global minimizing sets. Its disjointness from the canonical
low-cap face is exact; compactness also makes the pivot-debt separation
strict, not merely pointwise.

## Novelty and remaining limitation

The absorbing global minimum and its strict pivot payoff are substantive
new source content. They are not direct instances of the nonabsorbing
least-Never or Never-penalized minima. In particular the old positive-Never
selector cannot be invoked on this absorbing carrier; the diffuse-to-zero
then literal-root comparison is the new replacement.

There is a useful qualification: the same three finite-word transfers
would also work at the older partial-Nash minimum of d_p+r nu. While
the pivot Continues, both d_p and nu multiply by the same survival c,
so that objective contracts too. Therefore generic all-positive
partial-Nash existence without specifying the absorbing carrier is not
the new increment. The exact stronger content is its global absorbing
minimization, strict payoff in that carrier, and separation from the
canonical low-cap source.

These results do not consume the all-positive global minimum and do not
settle Fin4. No Lean/Lake command, git mutation, or frozen-export edit was
performed for this review.

## Canonical low-cap transfer and generic positive-cap exit

I independently read the exact added Sections 8 and 8.1. Their stronger
consumer is valid and retains the original F_p minimum. The previous
global C_p transfer alone did not ensure a low cap at the expanding-ray
endpoint; the new strict joining-cycle sign supplies exactly that missing
condition.

Under (-L)^(-1)>>0, every v>>0 has at least one negative coordinate of
Lv. Otherwise v=L^(-1)Lv<=0. For an expanding eigenvector
L^(-1)Jv=rho v, the fixed final root is q_0=a v+O(a^2), and its exact
virtual output is

    Q(q_0)=a Jv+O(a^2)=a rho Lv+O(a^2).

A sufficiently small fixed a therefore gives a strictly negative output
cap at that observer, with fixed negative margin. The full-cap seam
error tends to zero while this endpoint stays fixed. Its compact actual
limit has zero observer debts, a negative observer cap, and contracted
pivot debt. It belongs to F_p, so its comparison is legal.

The other producers also retain a low cap: a homogeneous block leaves
an active observer cap zero in the limit; a singleton burst keeps its
mover cap zero; the positive-inverse cycle ends with two zero observer
caps. Thus every part of the strict-cycle whole-pencil argument returns
to F_p. An inert collapsed root game at B consequently forces det L=0.

For a generic perturbation with all four principal joining determinants
nonzero, every canonical source therefore admits some nonzero exact root
at B. This root need not be the limit of the previously selected q_n.
Its survival is positive by the absorbing gap, and every successor cap
is positive by F_p minimality; otherwise its contracted pivot debt gives
a forbidden low-cap competitor. The canonical paid return then gives
the same expensive-exit inequality for this chosen root.

The change of root is permitted and does not change the source or its
minimum. The perturbation claim concerns the generic table, not a root
or uniform positive margin transported back to the original table. This
is a genuine unification of the canonical alternatives for a generic
positive-gap contradiction. It still leaves the positive-cap exit as
an unconsumed obligation.
