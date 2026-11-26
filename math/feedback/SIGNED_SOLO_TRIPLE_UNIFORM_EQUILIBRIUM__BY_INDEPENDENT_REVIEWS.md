# Independent reviews of the signed solo/triple equilibrium producer

**Two independent mathematical and source-gate reviews: PASS.** The
[frozen raw producer](../exports/SIGNED_SOLO_TRIPLE_UNIFORM_EQUILIBRIUM.md)
has SHA256 `b7681968d39775dfa7e086bbbe95c5b4085681cc34632f86ad63c040b4ef0ac8`.
The [source audit](SIGNED_SOLO_TRIPLE_UNIFORM_EQUILIBRIUM__SOURCE_AUDIT.md)
records the complete named prior-producer comparisons. This is an ordinary
existence-class export; no conditional exception or strategic input is assumed.
The new content is the signed direct return and its finite raw selection test.
The linear/quadratic elimination mechanism itself is reused and generalized.

# Independent signed solo/triple producer review

Reviewer: PIVOT_CONTACT_EXTENSION. Verdict: **PASS for mathematical soundness
and for admission as a new raw existence-class producer**, at the exact bytes
below. Ordinary mathematical review; no Lean build or formalization was run.
I attempted to falsify the algebra, negative-value comparisons, unilateral
semantics, source normalization, selector completeness, and claimed additional
coverage. I found no unresolved mathematical objection.

## Exact artifact

Candidate:
`math/exports/SIGNED_SOLO_TRIPLE_UNIFORM_EQUILIBRIUM.md`

SHA256:
`b7681968d39775dfa7e086bbbe95c5b4085681cc34632f86ad63c040b4ef0ac8`.

I read the complete statement, proof, boundary fixture, source correspondence,
and embedded program. I reran the exact certificate and independently
reconstructed its F polynomial and discriminant from the literal table. I
also reran the full completion producer-screen program and read its source
map and independent complete weak-role audit. This review does not transfer
to changed proof bytes automatically.

## The result actually established

The raw algorithm chooses roles (r,j,k,o), solves one nonsingular two-by-two
linear system, enumerates at most two real roots of an explicit nonzero
quadratic-or-lower polynomial, and checks physical hazards and four endpoint
inequalities. Every passing table has an actual two-period equilibrium with
supports {r} and {r,j,k}. Its original fixed payoff is a uniform-equilibrium
payoff against every unilateral behavioral replacement. No future payoff,
actual tail, recurrence, source attainment, or equilibrium certificate is
assumed as a strategic input.

Within the stated nondegenerate proper-hazard architecture, the selector is
also complete. It is not complete for arbitrary Fin4 games, longer calendars,
singular central systems, identically zero F, zero/sure hazards, or both
L coefficients vanishing. The packet explicitly retains those limitations.

## Algebra checked independently

1. For x=a/(1-a), y=c/(1-c), the common owner's two phase-B equalities are
   Z_r(rj)x+Z_r(rk)y+Z_r(rjk)xy=0 and
   Gamma_rj x+Gamma_rk y+Z_r(jk)xy=0. Dividing by xy gives the displayed
   matrix M on u=1/x,v=1/y, including the reversed order of its pair entries.
   Thus u,v>0 produces proper a,c and exactly Q_r=P_r=0. This is a raw solve,
   not an assumption that these indifferences can be attained.

2. With X_i=Q_i(b), Y_i=s Gamma_ir+(1-s)X_i, the phase-B active equality is
   Q_i-P_i-d_i(1-b)Y_i=Phi_i-s L_i=0. The determinant elimination is
   Phi_k L_j-Phi_j L_k=(1-b)F. If one L is nonzero, F=0 solves BOTH equations;
   when the other L vanishes its Phi must also vanish. No division by that
   vanishing coefficient is used.

3. Writing Q_j=A+Bz,Q_k=D+Ez proves exact cancellation of the cubic
   coefficients in F. The polynomial has degree at most two, including
   linear and nonzero-constant specializations. A nonzero constant has no
   candidate roots. A simple root and L_i!=0 persist under small raw changes.

4. For the quiet player o, H_o=C and the two policy equations are
   X_o=P_o+C Y_o and Y_o=s Gamma_or+(1-s)X_o. These give the stated positive
   denominator 1-C(1-s). At phase A the three quiet Quit offers are precisely
   s Z_i({i,r}), even when their values are negative. At phase B the sole
   quiet comparison is Q_o<=X_o. These are all four inequalities; no missing
   inequality is smuggled into a positivity assumption.

5. At each mixing player's phase, Quit and Continue both equal the supplied
   value. Hence its prescribed policy recursion follows from the same
   equalities, rather than from a separate fixed-point assumption.

For the boundary table I independently obtain

    M=[-2,-6;1,-2], (u,v)=(19/5,2/5),
    a=5/24, c=5/7,
    56448 F(b)=175496570 b^2-12603641 b+64295,
    discriminant=113717558584281.

The exact root isolation interval and negative derivative select the smaller
root unambiguously. The program checks all active gaps identically modulo
that polynomial, all four quiet gaps strictly negative by rational intervals,
and every opponents-only product strictly between zero and one. The displayed
negative phase-A value for owner3 is real, not a sign typo: its quiet Quit
value is still strictly lower. In particular the profile is not subject to
a fictitious free zero-payoff response while its opponents are absorbing.

## Actual strategies and all-behavior semantics

All randomization in the construction is independent and private. At every
pair of live dates each player faces a positive prescribed opponents-only
absorption probability: r faces j or k at phase B; j,k,o face r at phase A.
The product bound is independent of any complete behavioral replacement.
It remains valid for arbitrary private randomness and history dependence,
since at a live date there is one public live history and the prescribed
opponents can use independent fresh phase hazards.

The annotation remainder therefore tends to zero geometrically. This proves
that X,Y are the actual terminal payoffs. Unrolling the local maximum
inequalities prices every full deviating strategy, including Never; it is
not restricted to deviations with the same period or memory.

The original normalization is correct for arbitrary signed own levels
kappa_i. Only absorbing rewards are shifted. Every unilateral profile
absorbs almost surely because of opponents-only contraction, so the same
constant kappa_i is added to both prescribed and deviated terminal rewards.
Equivalently the root formulas obey Q_i^R=Q_i^Z+kappa_i and
P_i^R=P_i^Z+(1-H_i)kappa_i, matching continuation value+kappa_i.
No strategic equivalence with nonabsorbing profiles or shifted live rewards
is asserted.

The expected absorption time is bounded uniformly over deviators by 2/delta.
The uniform O(1/T) terminal-versus-average error therefore gives one fixed
payoff target and the same profile for all accuracies. The two exact compiler
statements inspected in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`
are `isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`.
Their hypotheses are exactly policy recursion, local root Nash, and each
opponent-cycle product less than one. The new raw proof produces all three.

Necessity within the architecture also holds. All prescribed hazards are
proper, so each phase is reached with positive probability. A profitable
conditional response would give a profitable complete response. Thus
terminal Nash gives local Nash at both phases. The solo mixing owner's
own-zero Quit value forces X_r=Y_r=0; its other active phase forces P_r=Q_r=0.
The nonsingular M solve then recovers a,c, and the remaining mixed contacts
recover F(b)=0 and s. All remaining comparisons are precisely the four tests.

## Robustness, freedom, and the export gate

At the literal table the central (P_r,Q_r) Jacobian determinant is -10.
The remaining two active equations have determinant
-(1-b)P'(b)/56448, strictly nonzero. Together with the strict physical/quiet
inequalities these give an actual raw open neighborhood, not just a
certificate-space neighborhood. Own-singleton subtraction is linear and
continuous, so the class is open in all sixty original reward coordinates.

I checked the stated unbounded freedoms by their actual outcome supports.
For each active recipient, none of the eight coalitions containing the
permanently quiet player o can occur under that recipient's unilateral
replacement, giving twenty-four unused original reward coordinates. For
recipient o, increasing any of the seven nonempty rewards outside o raises
its policy values without changing Quit offers; lowering any of its seven
nonsingleton participant rewards lowers Quit offers without changing policy
values. These are valid simultaneous one-sided directions. Arbitrary
recipientwise terminal shifts remain valid by the same absorption argument.
They are not claims of arbitrary two-sided freedom in every coordinate.

Additional coverage is concrete. I read the complete source-overlap audit
at `math/feedback/SIGNED_SOLO_TRIPLE_UNIFORM_EQUILIBRIUM__SOURCE_AUDIT.md`
and reran `math/experiments/FIN4_SIGNED_PIVOT_COMPLETION_CHECK.py` on the SAME
fifteen rows. It excludes all80 nonzero stationary patterns, all65 sure-first
patterns with arbitrary actual punishment caps, the named complete persistent
base selectors, all14 universal child quiet-lift selections, full coefficient
weight/quotient selections, all15 global marked tests in the stated reward
boxes, and the named pair/return prerequisites. These are bounded named
producer exclusions, not a no-UE or a failure of every conceivable verifier.
The new producer's exact equilibrium is fully consistent with them.

I separately inspected the full raw hypothesis list of
`math/exports/THREE_OWNER_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md`. That producer
already contains shared-owner elimination and a quadratic root, but requires
positive intermediate U0,U2 and a positive-endpoint wash. The old full-role
audit is essential: under every relabeling, its two remaining weak roles
fail respectively with x=-2 or C<0 and a0<0, making U0=C+lambda a0<0 for
all lambda>0. Thus this is not merely a stronger periodic conclusion on the
same already covered original table. Direct signed endpoint comparisons
supply the new part. The raw simple-root neighborhood proves that this
additional existence result extends beyond a single exact datum.

I affirm the ordinary existence-class export gate; no exceptional conditional
admission is needed. The finite raw algorithm is the actual-data adapter,
and the checked periodic compiler is an appropriate downstream consumer.
The result narrows the earlier surviving raw set and resolves the audited
completion by an explicit absorbing equilibrium. It does not close arbitrary
Fin4, or justify retaining that completion as an unresolved counterexample.

# Final mathematical and source-gate review of the signed solo/triple producer

Status: PASS for promotion of the exact raw producer below. This is a new
existence-class result, not an exceptional conditional admission. I read the
whole 400-line packet, independently reconstructed its raw selector, executed
its complete embedded exact program, and reconciled the prior complete
source screens with the now-solved fixture. No unresolved objection remains
within the precise scope stated here. No Lean, Git, worktree, or tracked edit
was used by this reviewer.

## Final reviewed bytes

- Producer:
  `math/exports/SIGNED_SOLO_TRIPLE_UNIFORM_EQUILIBRIUM.md`,
  SHA256 `b7681968d39775dfa7e086bbbe95c5b4085681cc34632f86ad63c040b4ef0ac8`.
- Prepared source audit:
  `math/feedback/SIGNED_SOLO_TRIPLE_UNIFORM_EQUILIBRIUM__SOURCE_AUDIT.md`,
  SHA256 `87533f92b6666212f2563bc1f338e487061cd6da94fd3bfb69bf3f2a056f4c2c`.
- Retained complete source-screen checker:
  `math/experiments/FIN4_SIGNED_PIVOT_COMPLETION_CHECK.py`, SHA256
  `0b4c126ec0ec9001a5c6a82a2cdf8863984d0972174c4bb65df6ba0727c45f10`.
- The program embedded completely in the producer has SHA256
  `ef63702aca47596c05e734d188ed92998f5a2ad3ec9f94653b1b8fa384f8b123`
  when extracted with its final newline. It matches the separately run exact
  two-phase checker and passed again after extraction from the final packet.

Changing the mathematics or raw data requires review of the changed bytes.
The earlier global-rigidity conditional admission was withdrawn separately;
this affirmative judgment does not reinstate that packet.

## Actual theorem and produced inputs

The inputs are the sixty finite original rewards and one of24 role assignments.
An invertible raw2x2 matrix computes two inverse odds and their hazards a,c.
A nonzero polynomial of degree at most two supplies a finite list of candidate
b values. A nonzero L determines s. All physical bounds and four remaining
endpoint inequalities are then finite arithmetic tests on these computed
quantities. Both continuation vectors are explicit formulas. Hence the raw
criterion does not encode a strategy, favorable equilibrium, selected child,
minimum, cap realization, or desired conclusion as an assumption.

All strategic witnesses are produced: four proper active hazards, the entire
two-phase independent law, both actual value vectors, all active contacts,
all quiet inequalities, playerwise opponent contraction, and the fixed
original payoff target before accuracy. There are no unproduced strategic
inputs and no need for the export gate's conditional exception.

The finite test is also necessary within the EXACT nondegenerate proper
solo-r / overlapping-triple{r,j,k} architecture. It makes no completeness
claim for arbitrary quitting games, degenerate matrix/polynomial cases,
sure or zero hazards, or longer return schedules.

## Algebra, semantics, and attempted falsification

I checked the M column orientation by dividing the central owner's Q=P=0
identities by xy with x=a/(1-a),y=c/(1-c). The unknowns are indeed
u=1/x,v=1/y. For j,k, the contact equation is exactly Phi_i-s L_i=0.
The two-equation determinant is (1-b)F(b), so a single nonzero L suffices,
including the case the other L vanishes. The identically-zero F and both-L
zero cases are explicitly excluded rather than divided through silently.

Using independent arbitrary affine symbols for Q_j,Q_k,P_j,P_k, I verified
the cubic coefficient of F cancels identically. Reconstructing Q and P from
the literal completed rewards independently of the provided F coefficient
claim gave exactly

    56448 F(b)=175496570 b^2-12603641 b+64295,

and the same rational expression for s as the packet. The discriminant is
113717558584281, agreeing with the displayed radical formula.

I checked that the quiet-player denominator1-C(1-s) is positive and that
its recurrence uses C=H_o, since o is always quiet. The four inequalities
are exactly the three phase-A quiet comparisons and the phase-B outsider
comparison. No comparison or free-zero-response assumption is lost at the
negative native values Y3 and X0.

The exact embedded calculation passed every active equality modulo the
quadratic, every strict quiet inequality via rational interval bounds, the
nonzero active Jacobian, and all four opponent-cycle contraction tests.
The reported decimal bounds are outward exact decimal rationals. As an
additional negative test, the other quadratic root lies in(66/1000,67/1000):
P changes from negative to positive there with positive derivative, while
the displayed s numerator is negative and denominator positive throughout.
Thus that second candidate is correctly rejected by s>0. Selecting an
arbitrary real root would not be valid; the stated test does not do so.

Every unilateral response faces geometric opponents-only absorption. This
identifies the annotations with actual terminal payoffs and makes the local
maximum inequalities bound EVERY complete behavioral replacement, including
Never. Since every such deviated profile absorbs, adding each own level
kappa_i back to nonempty rewards adds the same constant to its full terminal
payoff. This validates arbitrary signed own levels without shifting original
live/Never payoffs. A geometric expected-absorption bound gives the uniform
finite-horizon estimate with one fixed target and the same prescribed profile.

For necessity, all live phases have positive reach under proper hazards.
A profitable conditional one-stage replacement would contradict exact Nash.
The phase-A central indifference forces both central native values zero;
phase B then forces Q=P=0. The remaining active and quiet conditions recover
precisely the raw test. This proves the claimed restricted iff.

The open-class statement follows from the nonzero matrix determinant,
positive inverse odds, simple selected polynomial root, one nonzero L,
proper hazards and strict quiet inequalities; each persists locally.
Normalization is linear in all60 original coordinates. The unbounded
freedoms are correctly counted:3 active recipients times8 coalitions
containing the quiet player gives24 unused coordinates; the quiet recipient
has7 passive increases and7 nonsingleton participant decreases. These latter
changes improve only its appropriate side of the comparisons. They do not
make every remaining reward freely variable in both directions.

## Existing source and concrete new coverage

I inspected both exact periodic certificate declarations in
`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`:
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`.
They require policy recursion, all local root Nash conditions, and each
player's opponent-cycle contraction for supplied cycles and values. They
contain no raw hazard producer and no nonnegative-value premise. The new
construction supplies every field and should reuse this compiler.

The prepared audit retains the exact comparisons previously checked against
actual source statements, now explicitly labeling the fixture SOLVED:
all80 nonzero stationary supports and65 sure-first support patterns with
arbitrary actual punishment tails; all persistent base/free/Nash selections;
all14 proper universal child-lift selectors; all weights on the stated
ledger/floor domains; all14 nondiscrete response partitions; all finite
roles and the stated weak/closure return variants. The exact screen checker
passed with2071 stationary and294 actual-punishment Bernstein nodes.
The tail floor uses R=Z+1 and min(-1,outside Z), not an assumed zero floor.
None of those tests purported to exclude all dynamic strategies or a
favorable selected child equilibrium, so the new result does not refute them.

The closest old raw producer is THREE_OWNER_JOINT_RETURN, whose role
(0,2,3,1) produces the same central elimination a=5/24,c=5/7. Its c>0
hypothesis is actual participant premium J31=-4/5, and its positive outer
continuation hypothesis is the new negative Y3. The exact all24-role weak
screen excludes every alternate role too. The general scalar solo-return
note still needs positive outer endpoints. Thus the new contribution is
the signed DIRECT return, not the already available linear/quadratic algebra.
In particular J31 is a negative participant premium, NOT a negative joining
increment: J31-Gamma31=1/5. This distinction matters in source comparisons.

Additional inspected raw sources do not supply the example: the explicit
implemented overlapping-period-three affine cylinder requires reciprocal
positive singleton pairs; the current matrix has none. Fixed cyclic-child
families require an everywhere-negative pivot column; every current column
has a positive entry. Child013 does have cyclic signs but fails the actual
passive inverse-row test. Every triple fails the collision-box theorem's
six-positive-joining premise. The positive-passive triple producer is
stationary and fails the complete census. The audit states each exact scope
and makes no claim about unspecified maximal qualitative neighborhoods or
every conceivable existing UE theorem.


## Admission decision and limits

I affirm the ordinary new-existence-class gate. The theorem constructs an
absorbing equilibrium on a raw class containing a fully specified table
outside the compared implemented and accepted producers, with a full60
open neighborhood and explicitly stated unbounded freedoms. This is a
concrete positive source-to-UE chain, not another conditional minimum
restriction or merely a supplied-certificate verifier. The nondegenerate
architecture classification is additional useful scope, not a completeness
claim for arbitrary Fin4. The packet is self-contained and embeds its exact
boundary checker; the detailed source-overlap evidence belongs outside it.

General Fin4 remains open. No new L/A/C seal is asserted: the new producer
is ordinary mathematics pending formalization, although the named semantic
consumer already exists. The coordinator must still check tracked reference
availability and perform final placement checks before promotion; those
repository mutations/checks were outside this reviewer's authorized role.
