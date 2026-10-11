# Independent bounded check of the macroscopic periodic return

Reviewer: CODEX_NASH_BOX.

Frozen source: `CODEX_EMMY_BOX__MACROSCOPIC_PERIODIC_ROOT_RETURN.md`,
SHA256 `bbe0c087476a57d9f110d71b5980fa5bd98b8af9b80068b108f379a1cf90b2e4`.

Scope: actual full-deviation/target closure, the56-coordinate/upper-only
grand transfer, and the relevant whole-source coverage. CODEX_TURING_BOX
separately checks the interval arithmetic, AD, elimination and IFT source.
I do not duplicate that numerical certificate audit. This review found
no objection to the actual strategy consumer conditional on those exact
source inequalities, but found DECISIVE existing raw-class containment.
The periodic strategy can remain valuable internal constructive mathematics;
it does not establish a newly excluded counterexample class.

## 1. Actual full responses and one fixed target

The reverse order of the236 prefix roots is essential and is correctly
stated. The assigned values satisfy the literal prescribed Bellman
identity, and each player-deleted root has at least one opponent hazard
above10^-5. Therefore its opponent survival over n dates is at most
(1-10^-5)^n, independently of the replacing player's whole law. The
assigned continuation remainder tends to0. This identifies the values
with actual terminal policy payoffs; no terminal annotation is left over.

At a physical root, both forced action endpoints are at most its assigned
value, with equality for every prescribed action. Iterating these scalar
inequalities against fixed opponents proves the cap for every finite
deadline. For Never, bounded assigned values and deleted contraction
remove the final remainder. On the only live public history, every
complete private behavioral replacement induces a distribution on its
first Quit date and Never, independently of the opponents' private seeds.
Integration therefore covers full behavior, not merely periodic, Markov
or bounded-memory deviations.

Uniform finite-horizon control follows from that SAME opponent-survival
bound. The absorption delay has a common finite mean for every complete
replacement, so terminal payoff differs from finite average by O(M/N),
uniformly over those replacements. The reward bound M may depend on all
sixty finite input coordinates. The initial actual target and the profile
are fixed before accuracy. Arbitrarily negative finite grand entries may
increase M but do not invalidate the uniform-equilibrium conclusion.

This matches the literal hypotheses of
`quittingTerminalDeviationDebt_cyclicBehaviorProfile_le_card_mul_error_div_opponentAbsorption`
in `UniformEquilibrium/Quitting/Cycles/PeriodicApproximateNashDeviationCap.lean`:
local Nash is against ACTUAL next cyclic values, and the denominator is
player-deleted absorption. The declaration was inspected in place. It is
a supplied-cycle consumer, not the236-root source producer.

## 2. Perturbation and upper-only grand coordinates

The active root equations and prescribed values involve only proper rows:
support size is at most3, and an active recipient faces at most two
quitting opponents. Grand rewards appear only in the inactive recipient's
Quit endpoint at triple roots, with nonnegative product coefficient.
Lowering such a coordinate cannot change the policy evaluation or any
active equation and can only improve its inactive inequality.

At the symmetric proper-row center, writing K=R^-1 F gives
F_r=R^(r+1) K R^-r, so the236-prefix composition is K^4. The displayed
fourth-power derivative bound is therefore used at the fixed point, where
it is appropriate; it need not bound arbitrary products along unrelated
off-center iterates. Invertibility of DH-I and local active equations
gives a56-coordinate neighborhood. Literal perturbed rows must be solved
quarter by quarter; the source does say this and does not falsely rotate
an asymmetric perturbation. Strict hazard/margin inequalities survive a
shrinking of that neighborhood. A proxy grand row near(-10,-10,-10,-10)
then gives the claimed four unbounded LOWER rays. I found no agency,
target or monotonicity gap in this transfer, conditional on the separately
audited nonsingularity certificate.

## 3. Decisive containment in the existing boxed-charge producer

The implemented raw criterion was inspected directly:

- `quittingTrapInsertedPremiumSum`, `quittingTrapLeaveSum` and
  `QuittingTrapChargeCoefficients` in
  `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`;
- `QuittingTrapChargeCoefficients.threshold_of_cardinality_four` in
  `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeOdds.lean`;
- `HasBoxedQuittingNashCharges` in
  `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeReturn.lean`;
- `exists_uniformEquilibriumPayoff_of_boxedQuittingNashCharges` in
  `UniformEquilibrium/Quitting/Classification/Existence/BoxedQuittingNashChargesUniformPayoff.lean`.

The matching ordinary raw theorem is in
`BOXED_NASH_CHARGES_UNIFORM_EQUILIBRIUM.md`. No build was run here;
the exact declaration and its imports, not an author label, supply the
implemented criterion used in this calculation.

For the fixed table, the ONLY participant rewards above their own
singleton1 are r_i({i-1,i})=2. Consequently a premium trap must contain
the predecessor of every one of its members. The directed4-cycle forces
the only trap to be A=I. There are no missing smaller-trap obligations.

For EVERY nonempty proper T subset I, the actual inserted-premium and
outsider-insertion leave sums are

| T | P_I(T) | L_I(T) |
| --- | --- | --- |
| any singleton | -2 | -3 |
| any two-element set | -4 | -4 |
| three-element set missing i | -11-i | -11-i |

For example at singleton{j}, the three outsiders have inserted premiums
1,-2,-1 and leave gaps2,-1,-4. At a two-set, each outsider's joining
triple pays-1 versus its own1 or its passive pair payoff1. At a three-set,
the sole outsider joins the grand coalition, paying-10-i instead of1.
This uses OUTSIDER INSERTION, not withdrawal of a current participant.

Take d=2, g=3, ell=11, tau=1. All coefficient fields hold, and with
M=13 the exact strict threshold is

    C_4=4sqrt(2)*(3+22)=100sqrt(2)>56=sum_i s_i+4M.

Thus the existing actual raw producer already gives a uniform-equilibrium
payoff for this fixed table. This is a whole raw-certificate application,
not a favorable selected root or a failed trial selection.

The overlap also persists on an EXPLICIT neighborhood with the same
unbounded-grand quantifier. Suppose every proper coordinate differs by
less than1/10 from the displayed table, and every grand coordinate is
at most-10+1/10. The only premium trap remains I: the high directed pair
premiums remain positive and every other participant premium negative.
For that trap,

    |T|=1:  P<=-7/5, L<=-12/5;
    |T|=2:  P<=-18/5, L<=-18/5;
    |T|=3:  P<=-54/5, L<=-54/5.

Let M be the maximum absolute reward of this PARTICULAR finite input.
Choose d=1,g=2,ell=10,tau=1/(M+1). The negative penultimate premiums
are at most this positive tau. Since M>=0 and sum s_i<22/5,

    C_4=4sqrt(M+1)*(2+10(M+1))
       >=40(M+1)^(3/2)>4M+22/5>4M+sum s_i.

All hypotheses of the same implemented raw producer hold. There is no
need for a uniform bound over the grand rays: its existential tau is
chosen for the finite input table. This covers a genuine neighborhood
of the center times all four proposed lower rays. An unknown larger IFT
radius is not evidence of new coverage beyond this existing class.

There is a second exact containment, relevant to a proposed one-column
grand repair. The upper-average arm of
`MIXED_SUPPORT_UPPER_OR_CHARGE_UNIFORM_EQUILIBRIUM.md` permits nonnegative
weights with SOME zero coordinates. With the original proper rows and
grand coordinate0 changed to2, weights(1,1,1,1) give its forced-Quit
upper sums0 on empty,-2 on singletons,-5 on adjacent pairs,-6 on opposite
pairs,-5 on the triple missing0,-17-i on the other triples missing i,
and-38 on grand. Thus that modification is still covered.

In fact changing ONLY grand coordinate0 to ANY finite value cannot
separate this fixture from the whole upper-average criterion: weights
(0,1,1,1) ignore that coordinate. Their singleton sums are(-2,0,-1,-3),
their adjacent-pair sums(-3,-3,-3,-6) in cyclic order starting01,
their opposite-pair sums-5,-4, their triple sums-6,-16,-17,-18 indexed
by the missing player, and their grand sum is-39. All are nonpositive.
The full4-trap is still the only trap. This is a whole allowed-weight
selection, not an inference from the failure of unweighted boxed leave.

## 4. Other bounded comparisons and stationary source repair

The named four-singleton, four-joint, rectangle and passive-ray exclusions
in the source are compatible with their literal hypotheses. In particular
the paired singleton identities fix the favorite matching; for the named
singleton word, global owner-equation uniqueness fixes golden hazards,
and either orientation has a cross participant cap at most1, violated by
the directed reward2. The four-joint rate restriction likewise conflicts
with favorite-pair Quit1-b versus Continue>=4b, because actual full Nash
values are nonnegative (Never receives only nonparticipant rewards0,1,4).
These comparisons do not rescue novelty after Section3's actual overlap.

There is a separate needed correction to the positive-inverse comparison.
The exported coalition-jackpot mechanism includes selected PAIRS, and
every player here has one positive pair participant reward2. Negative
triples alone therefore do NOT exclude that entire theorem. I independently
checked the exact no-stationary argument in CODEX_TURING_BOX's Section25.1
as a repair: all support counts0–4 are covered. For three active players,
its equations imply b<1/2,c<1/4 and simultaneously Q_1>1/2 and
Never_1<=c<1/4. For full support, exact symbolic expansion gives precisely
the displayed positive sum of four residual polynomials, including its
quadratic square decomposition and all higher coefficients. The sure-root
argument is also valid for arbitrary continuation: mate and predecessor
must Continue, successor must Quit, then the original sure owner withdraws.

Thus there is no exact stationary terminal Nash at the center. This
excludes every source whose ACTUAL conclusion would be such a profile,
including the whole positive-inverse stationary producer, independently
of any unknown large-scale threshold. It is not a no-UE theorem and does
not conflict with boxed-charge existence or the proposed236-calendar.

## Verdict

Actual full-cap/target/upper-grand consumer: no objection under the source
certificate being independently checked elsewhere. Raw novelty: CLOSED
by the exact boxed-charge containment above. Retain the explicit strategy
as internal constructive mathematics if its arithmetic gate passes;
do not promote this as a new reward-class exclusion. No further raw-class
survey is needed to establish this verdict.
