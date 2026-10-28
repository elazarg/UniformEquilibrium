# Final adversarial export-gate review: joint three-player finite return

Reviewer: GLOBAL_BLOCK_REVIEW, independent of the triple producer's authorship.
Reviewed artifact: `math/exports/THREE_OWNER_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md`.
SHA-256: `79bd388307da01b41d6f9b1ec8cdbc5ed130d00e464250ff1ee35533f62e1f65`.
Repository source inspection: HEAD `9e73dd0bacf12c25f50e8aaca13fdd37897a69d5`.
Ordinary mathematics and exact computation; no Lean command or tracked edit.

## Verdict

**PASS. No unresolved mathematical, source-adapter, or export-gate objection.**
The packet proves a complete raw-table existence criterion and supplies an
exact example outside the explicitly audited earlier producer domains. It
produces every strategic input needed by its full behavioral and original
uniform-payoff conclusion. It is not an arbitrary-Fin4 theorem or a claim
that every conceivable earlier nonstationary mechanism fails.

I read the entire preceding 748-line candidate and the complete changed
raw statement. Reversing exactly the three approved raw-sign edits in the
final bytes reconstructs SHA
`f615c8b30444fef9437cae9508daf56aab8985ad6223d268e5eb27cbd29301a4`.
Thus all unchanged proof, example, census, coverage and handoff text is covered
by the full read; the broadened statement was separately checked adversarially.

The full Section 6 selector audit also has its independent coverage review.
I read that report, examined the census logic and reran its exact calculation.
My review independently checks the generic construction, complete-deviation
consumer, example and stability scope, rather than replacing that coverage
review with a numerical spot check.

## 1. Raw equations, denominator signs, and the broadened statement

Direct coalition enumeration gives, before division by 1+lambda,

    Quit0 = -s*b + lambda*((1-b)*zeta0+b*Z0(023)),
    Continue0 = -beta*b+(1-b)*U0
                 +lambda*((1-b)*k+b*Z0(23)),
    Quit2 = x*(f+eta)+lambda*((1-x)*c+x*Z2(023)),
    Continue2 = x*f+(1-x)*U2
                 +lambda*(-(1-x)*h+x*Z2(03)).

Their equalities give exactly the packet's a0,a2 and actual continuations.
Player3's Continue numerator is e*b-x*D. Its Quit offer is exactly
b*(J0+J1*b)/D after the physical substitution. Therefore both values vanish;
adding player3's positive hazard without this second equality would fail.

The raw linear equation selects b uniquely; J1!=0 is retained. The quadratic
W is precisely (1+lambda) times the cross-multiplied row2 affine-return
identity. W is required nonzero, leaving at most two real candidates, and a
positive selected lambda gives a proper hazard z. These are finite algebraic
reward tests, not supplied strategic or continuation witnesses.

The relaxation in the final statement is sound. No sign of beta,e,f,s,eta,
C or T is used after their algebraic definitions. D need only be nonzero;
its sign never orients an inequality in the proof. Physical b,x automatically
force e!=0 with the same sign as D. The actual guards X0<k and 0<tau<1 imply
X0<U0<k, supplying the upper bound needed in the wash. Positivity of U0,U2,
X1,X2 is tested on the actual values. The row1 denominator
1-(1-tau)H is strictly positive. All other divisions use retained positive
quantities, or the expressly nonzero D and J1.

The retained k,g,h>0, A>g and c>0 are genuinely used by the wash and return;
the packet does not silently discard them. Generic roots need not be simple.
Simplicity is used only for the particular open-neighborhood conclusion.

## 2. Prefix and both finite return branches

The prefix interval is sufficient even when X0<0. With B=max(-X0,0), its
lower bound gives a*H0>(1-a)B and therefore
Y0>a*max(zeta0,0). Its upper bounds give Y1>0 and Y2>c*a. These are exactly
the three quiet-player comparisons; player3 is indifferent at value zero.
No empty date is inserted at the negative X0 annotation.

For j<=0, the aggregate return mass is strictly between zero and one.
Every intermediate annotation lies between U and Y, whose outer coordinates
are positive and row1 coordinates nonnegative. Splitting a fixed aggregate
mass into N identical hazards, with q=1-(1-mass)^(1/N), makes each hazard
arbitrarily small while preserving the exact aggregate. This supplies a
finite subdivision meeting both quiet0 and quiet2 bounds. Quiet1's negative
joining reward and player3's indifference complete the comparisons.

For j>0, the affine identity and prefix positivity imply U0>k*j/g and j<g.
The regular wash preserves 0<v<g and s>k*v/g. Its row2 guard is preserved
with strict improvement even from equality: after clearing the positive
denominator, the new slack contains h*v+c*g*v/A>0. The displayed geometric
formula therefore reaches a legal final hazard v_n/g after finitely many
steps. The final endpoint has positive outer coordinates, zero row1, and
lies on the same affine line. Its parameter X1/(X1+g)>a gives a proper
remaining aggregate return, handled by the same finite subdivision.

This verifies the weak wash boundary, j=0, arbitrarily negative X0, arbitrary
finite unused rewards, and both signs of the relaxed algebraic bases. The
argument supplies a finite cycle for every table passing the raw tests.

## 3. Complete behavioral deviations and original own levels

The explicit K threshold bounds every positive term in the joint quiet1
Quit offer and leaves a strictly negative margin. All three active joint
players are exactly indifferent. Together with the solo-date checks, these
are complete one-date Bellman inequalities at every phase of the cycle.

At the joint date, a deviating player0 faces player2's hazard b; player2
faces player0's hazard x; each other player faces both. Thus every complete
unilateral behavior faces opponents-only absorption at least min(x,b)>0
per period. This bound is independent of the deviator's history, randomization,
or choice to Never. It implies geometric survival and finite expected
absorption time uniformly over all such deviations.

Bounded Bellman unrolling consequently proves the full cap bound and identifies
the annotations with actual terminal payoffs. It does not infer a complete
cap merely from on-support indifference. Native-to-original shifts are valid
because prescribed play and every unilateral replacement absorb almost surely;
literal original Never remains zero. Uniform O(1/T) terminal-versus-average
error follows from the same opponents-only bound. The fixed profile and fixed
target kappa+Y supply the original uniform-equilibrium contract. A direct
regret comparison may add two such error bounds; the packet claims no
incorrect numerical constant.

## 4. Exact example and full-dimensional stability

The independent exact checker retained at
`/tmp/TRIPLE_STABILITY_EXACT_CHECK.py` was inspected and run. It uses symbolic
identities and exact Fraction interval arithmetic, without floating assertions.
It confirms the raw b,x, both row3 zeros, owner0/2 identities, and

    W(lambda)/P(lambda)=319/12656828795288418000>0.

The stated quadratic has the required endpoint signs and positive derivative
on the rational bracket. Its selected root is unique and simple there.
The checker verifies cyclic transport modulo that quadratic, every bound
in (10), the target box, q_f,q_r in (0,1), V2>.144, 3*q_r<.14, the first
wash guard, and the quiet1 positive-term estimate proving K>=2 sufficient.
The remaining exact comparisons follow directly from the checked raw identities
and strict margins. No unknown optimizer or numerical root is a proof input.

All sixty original reward coordinates may vary. Native conversion is affine;
the selected linear and quadratic roots remain well defined and simple, and
all physical inequalities and quiet margins are strict. Keeping a and q fixed
while recomputing q_f=(j-g*q)/(g*(1-q)) and q_r as printed preserves the
row1 equalities and affine closure even when g changes. The neighborhood
claim holds at every fixed K>=2 and finite p, including K=2: the actual raw
threshold (6) has strict slack, even though the convenient label K>=2 need
not itself persist under perturbation. The radius may depend on the table.
No neighborhood exclusion of every earlier theorem is claimed.

Section 5's limitation is exact: proper solo3 phases propagate the forced
zero row3 value around the single-joint cycle, and proper mixing at that
joint date forces BOTH P3=0 and Q3=0. It is correctly restricted to the
specified architecture and does not purport to rule out multiple joint dates.

## 5. Coverage and export significance

The complete table has all 60 entries, with its construction scope K>=2 and
arbitrary p separated from the nonredundancy scope K>=1000,p=0,own levels1.
The old two-owner identity orientation has a unique physical cubic root,
whose quiet3 offer is 108/4735>0. Its failure is strict, and all 24 old role
assignments, including the named sign relaxations, are accounted for.

I independently reran
`python /tmp/CANONICAL_TRIPLE_STATIONARY_CHECK_4D.py --uniform-k 0 10`.
It closes all 80 stationary patterns in 692 nodes and all 65 sure-root
patterns in 167 nodes. Inspection confirms exact rational coefficients,
valid relaxed K inequalities, closed-box Bernstein rejection, inverse
combinations, justified origin-cube exclusion, and no acceptance of an
unresolved box. The full-cap lower vector and sure-root sign argument price
arbitrary actual punishment tails, not merely stationary repetition.

The independent coverage report verifies the literal coefficient reconstruction,
all listed finite selectors, weight domains, and 14 child Farkas contradictions.
The packet states their limited scope correctly: no arbitrary child-specific
strategic lift, unspecified perturbation neighborhood, or all conceivable
nonstationary mechanism is asserted excluded. The stationary approximate-limit
argument is also consistent with the negative singleton entries and nonzero
principal determinants. A per-table stationary regret floor is not presented
as an all-behavior gap.

Within those explicit audited domains the example establishes new raw-table
coverage, beyond the earlier quiet-player guard. Together with the finite
raw adapter and full consumer, this is sufficient conjecture-facing progress
for the special-class export gate; it is more than a supplied-cycle verifier
or a stronger conclusion on an already shown covered example.

## 6. Source correspondence, self-containment, and handoff

I inspected the exact declarations
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`) and
`quittingGame_fixedProfile_uniformPayoffWitnesses_of_terminalNash_exact`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
The packet supplies their needed actual continuation, terminal Nash, and
fixed-target content. It does not claim the new producer is already in Lean.
All named source paths in Section 7 were confirmed tracked.

Every strategic witness is produced: b, lambda, x,z, X,U,Y, the prefix,
finite wash length, final wash hazard, return subdivision, periodic profile,
and fixed payoff. None is assumed behind a certificate field. The packet
contains its literal table, interval instructions, necessary raw criteria,
and complete finite census specification; the scratch checkers above are
supporting review evidence, not unprovided packet dependencies.

The Lean handoff names appropriate existing interfaces and the new algebraic,
finite-cycle and rational-certificate work. Negative annotations are correctly
kept adjacent to their scheduled roots. Probability mode, stopping semantics,
original Never payoff, and full unilateral agency are explicit. No conditional
export exception or unproduced strategic input is needed. The final broadened
bytes are ready for the coordinator's freeze, subject to the separately
completed routine integrity and placement checks.
