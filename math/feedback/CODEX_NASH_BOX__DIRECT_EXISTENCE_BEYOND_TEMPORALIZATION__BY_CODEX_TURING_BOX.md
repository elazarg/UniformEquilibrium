# Bounded check of the entire-correspondence limit-order calculation

Reviewer: CODEX_TURING_BOX.

Status: ordinary mathematical bounded PASS of Section 6's M_N calculation.
This is not a review of the robust terminal-table perturbation theorem,
the discontinuous-game source audit, a Lean check or an export gate.

## Claim checked

For the fixed rational table in Section 2 and F_N={0,...,N-1,Never}, let
M_N(delta) be the minimum ORIGINAL complete terminal exploitability over
all private-bonus vectors b=(0,b_1,b_2,b_3) in {0} times [0,delta]^3 and
all exact Nash profiles of the auxiliary finite game. The bonus is paid
for the player's privately planned Never action, regardless of when an
opponent absorbs. The claims checked are

    for fixed N: lim_{delta down to 0} M_N(delta)=18/49,
    for fixed delta>0: inf_{N>=1} M_N(delta)=0.

The scope is this solved table and this entire finite correspondence.

## Compactness, objective and fixed-menu limit

For fixed N the product of four F_N simplexes is compact. Each auxiliary
payoff is a continuous polynomial in the product probabilities and bonus
parameters. Its finite pure-action best-response inequalities define a
closed Nash graph. Every bonus parameter has a finite-game equilibrium,
so the joint feasible set in the compact bonus box is nonempty and compact.

The ORIGINAL full cap is indeed a finite maximum, not a menu cap in
disguise. Once all prescribed opponents' finite dates precede N, every
pure date at or beyond N has the same value

    original Never response + own singleton reward
                              * product opponent Never masses.

It therefore suffices to include that one late value along with the finite
menu values and Never. All are polynomial in the fixed finite profile.
Consequently the full maximum-debt objective is continuous and its stated
minimum is attained.

I checked only the delta=0 specialization of Section 2's finite-Nash
classification needed here. Its final core root is (2/7,4/7,1/7), with
dummy Never, giving continuation values (31/7,19/7,34/7,31/49). The
displayed exhaustive earlier-root support inequalities force all-Continue
against this continuation. The positive-reach argument permits backward
induction on every date. Thus the original finite-menu equilibrium is
unique and all finite action occurs at the final root. Its only omitted
full gain is the pivot's product (1-4/7)(1-1/7)=18/49. Nonpivot late values
equal their Never values because their own singletons are zero.

Now take any sequence of bonuses tending to zero and corresponding
minimizers. A convergent profile subsequence has a zero-bonus exact Nash
limit by the closed finite graph. Continuity of the ORIGINAL FULL objective
forces the limiting gap to 18/49. The zero-bonus vector remains feasible
at every delta, furnishing the reverse bound. This proves the fixed-N
limit without any uniform-in-N compactness assertion.

## Positive-bonus joint-menu limit

For N with 1/N<=delta, prescribe pivot uniform on all N finite dates and
every other player Never, with b_1=1/N and b_2=b_3=0. The pivot receives
1 and has no better original or augmented action. Player 1's finite date
t has original value (7t+8)/N, maximized at 7+1/N, exactly its augmented
Never payoff. Player 2's finite value (7t+5)/N never exceeds its Never
payoff 7. Dummy finite values are -1/N and Never is zero. These exhaust
the finite auxiliary pure actions and establish exact auxiliary Nash.

The ORIGINAL full regret is exactly 1/N, solely at player 1. Every late
nonpivot date agrees with its original Never response, and the pivot's
opponents Never, so it has no omitted late gain. Hence
0<=M_N(delta)<=1/N for arbitrarily large N, proving the second claim.

## Verdict and scope

Both displayed iterated limits follow. This evaluates the best point of
the ENTIRE auxiliary correspondence; an arbitrary bad equilibrium branch
does not falsify it. It also changes the menu jointly with bonus accuracy,
so a fixed-menu perturbation limit is not an obstruction. No universal
table producer or completeness of private-Never exactification follows.
No mathematical objection was found within this bounded claim.

## Independent adversarial review of Section 8's large-pair producer

Reviewed whole-file SHA256:
`ca9581a7fbdd79331ac1d4b443a0eab02fc0455eca2d599486b2120b23fd534f`.
This new review concerns Section 8 only. Verdict: **PASS for the ordinary
producer, its uniform bounded-data quantifiers, complete behavioral terminal
Nash, fixed-profile UE, and finite-menu approximation.** No Lean check or
exhaustive coverage conclusion is assigned. The original review above is
unchanged.

### Pole cancellation and actual stationary equations

I independently formed the exact opponent coalition probabilities and checked
the actual policy identity, rather than beginning with the limiting field.
Writing D_i=1-(1-q_i)alpha_i>0, substitution of

    U_i=[q_i Q_i+(1-q_i)B_i]/D_i

gives D_i(Q_i-B_i-alpha_i U_i)=(1-alpha_i)Q_i-B_i exactly.
Thus the owner's own hazard really cancels out of H_i; no missing q_i or
discount factor appears in (S3). If H_i=0 and all rates are proper, both
endpoints and the actual policy value coincide.

At q=theta z, the only singular rewards in Q_i are the three pair
participant rewards theta^(-1)+c_i(ij). Their exact singleton-opponent
probabilities contain theta, yielding precisely the cancellation (S4).
The pair rewards in B_i are PASSIVE coordinates for recipient i and hence
remain bounded; none carries an overlooked theta^(-1) term. All larger
coalition rewards are also bounded. Consequently Q_i is polynomial,
1-alpha_i and B_i are divisible by theta, and H_i/theta is polynomial
jointly in theta,z and all sixty parameter coordinates as encoded in the
statement. Independent symbolic expansion with distinct arbitrary symbols
for the bounded coefficients confirms this divisibility for every player.

At theta=0 the exact limit is

    (sum_(j!=i)z_j)^2-sum_j Gamma_ij z_j.

I independently checked z_i=1/9, every entry of (S7), determinant-833/27,
the eigenvalues1,-17/3,7/3,7/3, and all sixteen entries of the claimed
inverse (S8) by rational arithmetic. In particular there is no omitted
factor3 or4 in the scaling q=z/M.

### Uniformity over the ENTIRE coefficient box

The quantifier order really is for every FIXED finite R, there exist
delta,M0 working for all44 bounded coefficients, all allowed singleton
perturbations, and every M>M0. The proof is valid for this order.

For each c in [-R,R]^44, choose a product neighborhood

    (-eta_c,eta_c) × singleton_ball(delta_c) × W_c

contained in its implicit-function parameter domain, where W_c is open
around c. The local solution can be kept in (1/18,1/6)^4. Finitely many
W_c cover the entire compact coefficient cube. The minimum of their
positive eta_c and delta_c is positive and furnishes common theta and
singleton tolerances. Any allowed coefficient vector lies in at least
one chosen W_c, so a solution exists for every allowed parameter triple.
Local selectors need not agree on overlaps: neither continuous global
selection nor uniqueness is asserted. Increase M0 to ensure theta z_i<1.

This also handles R=0. No bound uniform over arbitrarily growing R is
claimed; that would not follow from the argument and is unnecessary.
The use of theta=0 is solely polynomial continuation, not the assertion
that the all-Never zero-hazard profile has the limiting payoff.

An exact R=0 check supports the scale. With reference singletons, pair
participants M and all other nonsingletons zero, equal hazards q have

    H_i=q(1-q)^2[(3-3q+q^2)(1-q+3Mq)-4].

The bracket is-1 at q=0 and3M-4 at q=1, so for M>4/3 it has an
interior zero. Its rescaled equation tends to z(9z-1)=0, with the
positive branch1/9. This is a test of the limiting calculation, not a
replacement for the uniform44-parameter argument.

### Complete agency, Never and fixed original-game payoff

For each fixed produced table, every q_i lies in (0,1). Joint survival
is strictly below1, and every player's opponent-only survival alpha_i
is strictly below1. Therefore the actual policy is uniquely evaluated by
its geometric series. Iterating both local endpoint equalities bounds every
complete behavioral deviation with remainder of order alpha_i^t. A deviator
may change every future action, choose an arbitrarily late deadline or
Never; the opponents still absorb almost surely and their geometric tail
vanishes. No stationary-deviation or bounded-memory restriction is used.

I inspected both named contracting declarations under their imports in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`:
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`.
Their actual hypotheses are produced by (S3), the positive rates and
stationary policy evaluation. They yield exactly the claimed unrestricted
terminal Nash and the actual fixed stationary uniform-payoff target.
Alternatively the geometric opponent tail controls terminal-to-average
error directly for every complete deviation. Bounds can depend on the
fixed original table and its M; no horizon-uniform bound over all M is
needed for UE.

### Censoring, fixed-table scale and exact fixture checks

For censoring dates greater than N, each geometric tail has mass at most
exp(-(N+1)/(18M)). Coupling old and new independent clocks changes each
prescribed payoff by at most2K times the sum of four tails, and each
complete unilateral payoff by at most2K times the sum of the three opponent
tails, uniformly over the replacing law. Thus new full regret is at most
14K times the common tail bound; the stated16K is valid. This comparison
retains late deadlines and Never and is not merely a menu-Nash argument.

For a fixed original table, fix an allowed representation M and then choose
N according to the requested accuracy; there is no permission to change
that original table's M while claiming approximation of the same game.
The sentence 'choosing N and M as appropriate for the fixed table' should
be read this way or tightened to avoid suggesting back-transport. This is
a wording clarification, not an objection to the proof.

I checked the complete fixture (S10). Its four distinct blocked pair joins
are12,03,23,13; every pair still has an unblocked outsider with gain1.
Every triple has its stated participant with leave gain2. Grand withdrawal
and all-Never deviations are profitable as stated. A deterministic first
date later than zero is preempted by some receiver below its own singleton.
For each triple quiet child, taking T=child minus its unique bad participant
gives outsider gain1 against sole donor gain-2. Pairs and singleton children
also fail the cited nonnegative join comparison over ALL weights. These
are valid bounded exclusions, not an exhaustive source-coverage audit or
a claim that the game lacks mixed stationary equilibria.

No mathematical objection to Section 8's source-to-UE chain remains within
this independent review. Coverage beyond the exact fixture tests above is
reserved for the separately assigned review.

## Section 12: independent producer and bounded whole-selection review

Reviewed snapshot: whole-notebook SHA-256
`e474baaaa03aa84fe6cc620e530a1b4c4132254fda2583f1b60ca269d7c20f79`.
Scope: Section 12 only. Verdict: PASS for its ordinary mathematical
source-to-terminal-Nash-to-fixed-uniform-payoff argument, the implicit-function
extension, and the finite named source exclusions below. This is not a Lean
check, exhaustive novelty theorem, stationary nonexistence result, or proof
that every older unquantified IFT neighborhood is disjoint.

The claim checked is a raw four-player producer with the printed sixteen
paired singleton entries, twelve participant-pair upper bounds, and thirty-two
arbitrary finite coordinates. Its schedule is the chronological owner word
`(0,2,1,3)`, with independent proper owner hazard
`q=(sqrt(5)-1)/2`. Deviations replace complete private laws, including all
finite deadlines, unbounded laws and Never. The output is exact terminal Nash
at every phase and the same profile witnesses each fixed phase target as a
uniform-equilibrium payoff. The neighborhood version perturbs the sixteen
singletons, permits twelve pair coordinates to decrease without bound, and
leaves the same thirty-two coordinates arbitrary.

### Actual values, all local endpoints, and all unused rewards

I reconstructed the geometric four-phase evaluation from the raw singleton
rows, rather than treating the displayed continuation vector as supplied.
With `c=1-q` and `H=(3+sqrt(5))/2`, it gives exactly

    U0=(1,H,c,1), U2=(1,c,1,H),
    U1=(H,1,1,c), U3=(c,1,H,1).

All sixteen coordinate residuals `U_t-q*r({j_t})-c*U_(t+1)` are zero.
Each owner has value one immediately before and after its coin. For the
twelve inactive endpoints, solving `c+q*r_i({i,j_t})<=U_ti` gives:

| owner phase | inactive recipient: pair cap |
| --- | --- |
| 0 | 1:T, 2:0, 3:1 |
| 2 | 0:1, 1:0, 3:T |
| 1 | 0:T, 2:1, 3:0 |
| 3 | 0:0, 1:1, 2:T |

Here `T=(5+sqrt(5))/2`. These are exactly the twelve printed pair
participant bounds, including their asymmetric cross-pair orientation.
At the strict completion the four mate endpoint gaps are
`(7-3*sqrt(5))/4>0`, and the other eight gaps are
`(sqrt(5)-1)/4>0`. No endpoint is missing.

Every unilateral replacement can meet at most one scheduled opponent at
any live date. Thus its terminal coalition has size at most two; in a pair
the deviator is a participant. All twelve passive pair, sixteen triple and
four grand recipient entries are genuinely irrelevant to the deviator's
own payoff, even under simultaneous Quit and arbitrary history-dependent
behavior. They need only be finite for a table-specific reward bound.

### Complete caps, Never and the horizon quantifiers

Deleting any player leaves three independent proper coins per four dates,
so its opponent survival is bounded by `(c^3)^floor(n/4)` from every phase.
The two endpoint inequalities give a bounded Bellman supersolution for
every replacement. Iteration leaves a remainder bounded by twice a finite
table reward bound times that opponent survival. This vanishes also for
Never and unbounded complete laws. The actual prescribed profile attains
its exact evaluated values, hence full terminal regret is zero.

The same opponent clock bounds the selecting time of every replacement.
Summing its survival gives at most `4/(1-c^3)`; the stated extra one in
`C=1+4/(1-c^3)` safely handles indexing of the selecting date. Therefore
terminal-to-average error is at most `M*C/N` for prescribed play and for
every complete replacement, with `M` fixed from the original finite table.
The full finite-horizon gain bound `2*M*C/N` follows. This proves one fixed
phase target before accuracy, with one fixed profile for all accuracies;
it does not require any closure or target-preservation assumption.

I inspected the actual hypotheses of
`quittingSubBellmanValue_le_superSolution_of_survival_zero` and
`quittingCyclicHazardTerminalValue_le_add_of_quitError_and_continueUpperBound`
in `UniformEquilibrium/Quitting/Cycles/CyclicSupersolution.lean`, and
`finiteAverage_delivery_le_of_opponentLiveCesaro_bound` and
`finiteAverage_deviation_gain_le_of_exact_terminalNash_and_opponentLiveCesaro_bound`
in `UniformEquilibrium/Quitting/Cycles/PeriodicFiniteHorizonRate.lean`.
The ordinary proof supplies their relevant semantic hypotheses; no new Lean
adapter or build is claimed by this review.

### Owner field and implicit-function quantifiers

Independent symbolic expansion of the actual policy evaluation gives
`(1-P)*(U_(t+1),j_t-1)=F_t` with exactly the printed field. Exposing the
three other clocks and then the returning owner's clock proves the same
identity for arbitrary nearby singleton rows, replacing one by that
owner's own singleton. Thus zeros are actual owner indifferences, not
zeros of a field with an independently chosen continuation value.

At the golden root I obtain the circulant offsets
`A=-2-q`, `B=2-q`, `D=3*q-2`, and determinant

    det J=(-2205+945*sqrt(5))/2 < 0.

The four row eigenvalues are the stated `q-2`, `3*(2-q)`, and
`-(2-q)+/-4*q*i`. The claimed field and determinant therefore agree
exactly, not just numerically. Properness and all twelve strict inactive
gaps persist on an open neighborhood of the sixteen singleton entries
and twelve pair entries. Choose one smaller common radius there. For
upper-only pair data, compare to the proxy table with every relevant pair
entry at its strict-completion value plus that radius. The policy's values
depend only on singletons; decreasing a pair entry only decreases its
positive-coefficient inactive Quit endpoint. This proves the full
unbounded-below twelve-coordinate conclusion. Arbitrarily large unused
finite rewards affect only the table-specific horizon constant, not IFT,
the selected hazards, policy evaluation, or endpoint inequalities.

### Entire sure-owner and child-certificate screens

I explicitly reconstructed all pure-opponent gain rows of every induced
sure-owner game. For owner `j`, its mate and the noncollider other than
`kappa(j)` each have gain tuple `(-1/2,-1,-1,-2)` against the four actions
of their other two nonowners. These strict pointwise signs imply strict
dominance against every mixed product law. Both must Continue in ANY
induced mixed equilibrium. The remaining player then has gain `1/2`
and must Quit. Thus the complete induced Nash set really is the single
point printed in (12.6), for each of the four possible owners.

At that point the owner's Quit-minus-Continue is `-1/2`, and the
all-opponents-Continue mass is zero. No punishment value can repair it.
For a partial free set the free Nash conditions and omitted players'
no-join inequalities extend to a full induced Nash profile. For bases
of size at least two, all base leave, free Nash and outsider join signs
would make a full zero-tail one-shot Nash root with a sure owner, already
excluded. This checks whole selection, not a finite sample of pure roots.
The corresponding literal definitions and adapter were read in
`UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean` and
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`:
`quittingPersistentBaseUtility`, `quittingPersistentBaseNashSet`,
`quittingPersistentBaseRoot`,
`nonempty_quittingPersistentBaseCertificate_of_inducedNash`, and
`exists_uniformPayoff_of_persistentBase_inducedNash_signs`.

For every nonempty proper child, the four-cycle `kappa` provides a member
`j` whose positive collider lies outside. At the child row `{j}`, that
outsider's joining gain is `1/2`; every child's advance donor gain is
zero or `-1/2`. Nonmember withdrawal gains vanish. The sole member's
withdrawal gain is its chosen floor minus one. Patient floor is at most
one; deadline/cancellation floor is at most zero; evaluated security uses
an explicit minimum with zero; terminal security uses a maximum of a
nonpositive zero floor and an LP value at most its singleton one.
All five gains are therefore nonpositive, including singleton children.
No nonnegative donor weights can dominate the positive join row.

This matches `WithdrawalFutureJoinKind.gain` and
`WithdrawalFutureJoinRewardCertificate.join_row` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`.
I read the actual restart and LP-floor definitions in
`PatientWithdrawalRaw.lean`, `DeadlineWithdrawalRaw.lean`,
`DeadlineWithdrawalRestartPointwiseCore.lean`,
`DeadlineWithdrawalSecurityMixedPointwise.lean`, and
`DeadlineWithdrawalSecurityLP.lean` in that same directory. In particular
the terminal-security floor is NOT assumed nonpositive: the singleton LP
bound is indispensable and correctly used here. This validates the
all-child F/J-only exclusions and hence their stronger N/F/J variants.

### Balanced cycles and the other finite named comparisons

The balanced-certificate exclusion is valid for arbitrary finite owner
words, not just the displayed word. From a positive owner phase, both
nonmate coordinates become strictly greater than one. Until another
positive owner appears, repeated positive old-owner phases preserve its
own coordinate one and further increase those two coordinates. The first
different positive owner must therefore be the mate, where its reward
four forces the old owner's next coordinate below one. Opponent divergence
ensures that first different owner exists. This contradicts the actual
`soloFloor` field in both `BalancedSingletonCycleCertificate` and its
`WithBounds` version, inspected in
`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`.
Zero-hazard phases do not affect the argument. The signed source's positive
predecessor Hamiltonian cycle is also impossible for the two-transposition
positive singleton graph; I checked `SignedFourCycleSingletonData` in
`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`.
The new calendar indeed escapes a certificate restriction, not the actual
full deviation inequalities.

The additional literal raw screens in Section 12.7 also pass bounded
inspection under every relabeling. In `PairedCycleSchedule.lean`, the
actual `RawRegion.eq_partner_of_singleton_lt` conflicts with two below-own
opponents per recipient. In `CrossedMatchingPhaseSource.lean`, the strict
and weak favorite caps would require `7/2<=1`; the inverse source forces
a cross scheduled partner and still caps the mate this way. In
`BelowSingletonJointPhaseSource.lean`, exact scheduled singleton identities
force scale one, and `premium<-1` forces negative joining reward, whereas
each cross pair has a positive participant joining reward `1/2`.
The two-pair join-cap export fails its joining-versus-partner condition
for every partition (mate `7/2<4`; a negative cross participant `-1/2<0`).

I inspected the singleton hypotheses in
`UniformEquilibrium/Quitting/Paths/TwoPairGroupExclusion.lean` and
`TwoPairCrossMassRewardExclusion.lean`: any designated pair has a mate
singleton with strictly positive pair-average surplus, while either
designated recipient has its positive mate singleton surplus three.
These contradict the respective required nonpositive singleton rows.
Finally the two four-joint exported literal reward regions do not contain
this fixture: favorite participant `7/2` is too far from the first
export's five with its radius at most `1/2`, and fails the second export's
exact favorite participant identities. The singleton graph forces any
admissible relabeling to preserve the favorite matching. These are
stated-region exclusions only; the earlier mechanisms are not claimed
incapable of finding some other equilibrium in this solved table.

No mathematical objection remains within this bounded review. In
particular this review does not upgrade the finite named comparisons to
an exhaustive classification of all source interfaces or all older
qualitative local neighborhoods.

### Standalone incorporation check

Checked the complete standalone
`notes/CODEX_NASH_BOX__FOUR_SINGLETON_PHASE_UNIFORM_EQUILIBRIUM.md`,
SHA-256
`678acf8b57673b513b9660ee41b52401fe5fac8d9fc8b688b2c84f8e7e464829`.
Verdict: PASS for faithful incorporation of the reviewed Section 12
producer, upper-only/arbitrary-coordinate strengthening, and its stated
source quantifiers. The raw twelve bounds, all four values, actual owner
field and Jacobian are unchanged. The neighborhood hazards can indeed
be kept in `(1/2,3/4)` by shrinking the IFT radius around the golden
root. Every deleted cycle then survives with probability less than
`(1/2)^3=1/8`, so the newly explicit uniform constants `rho=1/8` and
`C=1+4/(1-rho)=39/7` are valid. Arbitrary finite unused coordinates
change only the table-specific reward bound, not these constants.
The selecting-date convention is stated explicitly and agrees with the
extra one in the horizon constant. No new transcription or soundness
objection found. The separately reviewed quotient comparison is retained
with its positive-inverse/negative-determinant distinction; this final
check is not a repeat of the independent broad coverage audit.

## Section 13: bounded assessment of literal-two-clock resonance

Reviewed the Section13 text in
`notes/CODEX_NASH_BOX__DIRECT_EXISTENCE_BEYOND_TEMPORALIZATION.md`, SHA-256
`89e2aad1e34a48d50b88aed980846a36e1ac4ad9aa1ffa0a9bbe6b19134bed6a`.
This is one bounded adversarial ordinary-mathematics assessment, not a
new full export audit or a proof that the remaining source has zero loss.
The foundational constrained-source/record-hull check is saved under
`feedback/CODEX_EMMY_BOX__SINGLE_OWNER_COMPACTIFICATION__BY_CODEX_TURING_BOX.md`.

Verdict: no objection found to the claimed whole-correspondence
at-least-three-proper conclusion under its GLOBAL terminal-gap, generic
reward and nonresonant-rate hypotheses. I specifically checked nonperiodic
activity blocks, weak record ties, proper labels lost at compact limits,
and whether one bad branch was being mistaken for a full correspondence.

### Compactification before combinatorics is necessary and valid

At the chosen rate, bounded-proper and owner-only-proper exits contradict
the GLOBAL positive gap. Every finite date then has positive joint reach.
Finite owner-cap attainment gives an exact full-Nash reached record tail,
so it is likewise impossible. The owner finite deadline values are
strictly below their Never limit and have infinitely many strict records.

Take a hypothetical point with exactly two proper labels a,b, allowing
every other label an arbitrary improper law rather than literal Never.
Its reached record tails remain in the SAME compact exact correspondence.
Each other label's positive Never mass makes its tail converge to literal
Never in total variation. At a compact cluster the owner remains proper
by K_delta; if b became improper, the owner-only-proper exit would apply.
If it became bounded proper, the bounded exit would apply. Thus the
cluster has precisely a,b unbounded proper and every other label literal
Never. This removes the improper finite parts EXACTLY before applying
two-player formulas. No numerical tail approximation is inserted into
an exact resonance identity.

The same bookkeeping at the integer minimum of proper count over ALL
correspondence points preserves every proper label of that minimum.
There is no unsupported closedness claim for the proper-law set.

### The all-calendar two-clock case analysis checks

For the literal-two-clock point, I independently obtain

    f(t)=u+S_b(t)[s-u+y_t(A-s)],
    g(t)=v+S_a(t)[s_b-v+x_t(B-s_b)].

Because b is a full best reply with unbounded support, its supported
deadlines have cap equal to their limiting Never value v. Every b-active
date therefore has x_t=lambda=(v-s_b)/(B-s_b). The generic inequalities
and unbounded properness force 0<lambda<1. Every such date is an owner
weak record, since positive owner atoms must be weak records under the
exact envelope equality. No strong record is inferred merely from
positive hazard.

If s>u, any b-quiet date would have f(t)>u, impossible on the Never-only
owner-cap face. Thus all dates are b-active and have owner hazard lambda.
Two strict records give the forbidden resonance with k=d.

For s<u and A<s, a b-active date after a quiet date strictly decreases
f, so cannot be a weak record. Consequently the active set is an initial
block. Unbounded properness of b forces this block to be all dates;
again two strict records give k=d. An arbitrary initial quiet prefix
cannot precede its first active atom in this case.

For s<A<u, a quiet date after an active date L increases f by
S_b(L)y_L(u-A)>0. Since the active date was already a weak record,
that first quiet date is a strict record; subsequent quiet dates form
the current maximum plateau. The next active date increases it by
S_b(H)y_H(A-s)>0 and is strict. Thus any finite active block has strict
records at its start and the first quiet date after it, while every
date inside has owner hazard lambda. An infinite block contains
infinitely many strict records because f(t)<u tends to u. Both cases
give a forbidden resonance; no periodicity or bounded quiet-gap premise
is used.

For A>u>s, the quiet baseline after an active date L lies BELOW f(L)
by S_b(L)y_L(A-u)>0. Every following quiet date before the next b atom
has the same baseline, so is not even a weak record and has owner hazard
zero. Discard the finite prefix before the first b atom. Two later
strict records H<K are b-active; owner survival between them is precisely
(1-lambda)^k, where k>=1 counts the b-active dates in[H,K). Binding at
both strict records gives c^(K-H)=(1-lambda)^k, again forbidden. This
also covers unbounded quiet gaps and weak active record plateaus.

These cases exhaust pairwise-distinct s,u,A. The countable forbidden
rate set can be avoided arbitrarily close to1 AFTER the raw table is
fixed and BEFORE any constrained equilibrium is selected.

### Quantifiers, perturbation and significance

A sup-norm reward perturbation of size epsilon changes each prescribed
or unilateral payoff by at most epsilon, hence full exploitability by
at most2epsilon, uniformly over ALL complete independent profiles.
A genuine positive gap survives a sufficiently small perturbation.
If no singleton were positive, all-Never would already be exact full
Nash; thus a counterexample has a positive-singleton owner that can be
kept positive while avoiding the finitely many raw pair equalities.
This preserves original Never0 and does not assume row-translation
invariance. The resulting generic table then admits a sufficiently
small nonresonant rate with the claimed whole-correspondence conclusion.

The reduction is real at the SOURCE level: it rules out EVERY exact
constrained source with only two proper labels, including profiles with
improper finite-mass outsiders, not merely one selected stationary branch.
Combined with minimal proper-count compactification and the companion
hull construction, it produces a three/four-proper uniformly terminating
record-invariant source for any suitably perturbed hypothetical gap table.

It does NOT yet eliminate a raw reward-table counterexample class or
prove UE: the existence of such a three/four-proper source is not a
contradiction. A solved table with a bad three-proper branch and a good
one-proper branch does not refute the theorem, whose hypothesis is a
GLOBAL gap and whose minimization ranges over the ENTIRE correspondence.
Conversely such a bad branch cannot establish the remaining global
selection obstruction. The next substantive obligation is a legal joint
operation on the produced at-least-three-proper source, not a further
description of arbitrary constrained equilibria.
