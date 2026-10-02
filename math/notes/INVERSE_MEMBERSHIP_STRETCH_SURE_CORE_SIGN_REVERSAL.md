# Inverse membership stretch forces sure-core sign reversal

Author: CODEX_TARSKI_PREMIUM. The all-player-ties argument is due to
CODEX_HILBERT; the short strict-half argument was independently supplied by
CODEX_NOETHER_SUPPORT.

Independent reviews:
[CODEX_NOETHER_SUPPORT](../feedback/CODEX_TARSKI_PREMIUM__INVERSE_STRETCH_EXCLUDES_SIGN_COHERENT_SURE_CORE_MINIMA__BY_CODEX_NOETHER_SUPPORT.md),
[CODEX_FRECHET_CYCLE](../feedback/CODEX_TARSKI_PREMIUM__INVERSE_STRETCH_EXCLUDES_SIGN_COHERENT_SURE_CORE_MINIMA__BY_CODEX_FRECHET_CYCLE.md).

This is ordinary mathematics narrowing the reconstructed singleton-fiber
worst-table source. It is not a new equilibrium-existence class, a
Lean-checked declaration, or a proof of the full Fin4 conjecture. The
comparison uses the ORIGINAL maximizing table and an UNPADDED actual root;
no frozen-coordinate reward normal is assumed.

## 1. Exact source, table correspondence, and question

There are four players I. A reward table gives a number in [−1,1] to each
owner i at every nonempty coalition S. Never pays zero. Profiles use
independent complete stopping laws and admit every unilateral behavioral
response. Let s_i=r_i({i}), let U_i be the prescribed terminal payoff,
and let B_i be the supremum of terminal payoff over all complete unilateral
behavioral responses by i. Write d_i=B_i−U_i, E=max_i d_i, and

    η(r)=inf_(all actual independent profiles p) E_r(p),
    Ω=max_(r∈[−1,1]^60) η(r).

Use the actual construction of
[the singleton-fiber source reduction](../exports/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md),
not merely an arbitrary tuple with its listed contact inequalities:

1. r* is an ORIGINAL full-cube maximizing table with η(r*)=Ω>0.
2. Fix the construction's 0<α<Ω/8. In each owner's pair of reward
   coordinates (B,B∪{i}), ∅≠B⊆I\{i}, move the larger toward1 and the
   smaller toward−1 by fraction α. Leave equal pairs unchanged.
3. Freeze these56 stretched coordinates. The resulting table r has freely
   reselected own singletons, possibly different from those of r*.
   It is the fixed maximizing limit in that fiber, with

       η(r)=m>0,       m≤Ω.

The same α and ORIGINAL r* belong to the source construction. They are
retained here as provenance, not reconstructed from arbitrary final contact
fields. The source also has strict pure nonsingleton regret separation;
the proof below does not need an additional use of that separation.

Suppose the zero-singleton/zero-Never source arm is realized by a product
root q∈[0,1]^I at DATE ZERO, followed by Never, with at least two sure quitters.
Its complete semantic pair is a global minimum at r:

    E_r(q)=m.

This is an UNPADDED actual profile. The product-base strict-margin theorem
supplies this realization. A silently padded source cannot simply be
evaluated at r*, because its new early singleton caps could change when
the four singleton parameters change. No such padded comparison is used.

Let K={i:q_i=1}, so |K|≥2. A root draw X∈{0,1}^I is sampled independently
under q. Its support is a finite product set; coordinates with probability
zero or one have just their actually supported action. At every unilateral
intervention, at least one member of K other than the deviator remains
sure at date zero. Therefore every full response payoff is a convex
combination of the two expected membership endpoints at that date.
Later dates and Never have the
same Continue endpoint. There is no earlier date.

## 2. The sign-coherence hypothesis and conclusion

For each i choose a membership action b_i∈{0,1} maximizing its expected
endpoint payoff against q_−i at the FINAL table r, where1 means Quit.
Define, for every opponent configuration z of positive
q_−i-probability, the directed endpoint difference

    c_i(z)=r*_i(S(z,b_i))−r*_i(S(z,1−b_i)),             (1)

where S(z,a) is the coalition of Quit players after inserting action a
for i. Both coalitions are nonempty because an unchanged sure opponent
remains. Hence (1) only uses the56 stretched coordinates, never an own
singleton. The same is true at r.

The branch hypothesis is

    c_i(z)≥0 for EVERY i and EVERY supported z.           (2)

Thus the source-best action is weakly better pointwise on the optional
players' supported configurations, rather than only after averaging them.
Equivalently, one may test (2) at r: the stretch preserves the sign of
every directed edge. Zero edges are allowed.

**Theorem.** The actual source of Section1 cannot satisfy (2). More
precisely, assuming (2) produces one supported pure root whose full
terminal regret at r is zero, contradicting η(r)=m>0.

For a THREE-sure root there is only one optional player. Its own opponent
configuration is deterministic, so its best-action direction is
automatically coherent. The hypothesis therefore reduces to the following
particularly concrete test: every sure player's Continue-minus-Quit
payoff difference is nonnegative at BOTH supported actions of the optional
player. The conclusion says that at least one sure owner must instead
have a strictly negative difference at one action and a strictly positive
difference at the other. Its average remains the positive minimum debt.

For a TWO-sure root, (2) also imposes coherence on the two optional players'
source-best actions. That stronger hypothesis is explicit; no such
condition follows merely from averaged best-response optimality.

## 3. Two global-minimum facts used in the proof

These facts concern MAXIMUM debt, not minimum total debt.

First, every coordinate of a positive global MAX minimum equals its
maximum. We include the complete ordinary-mathematics argument from
[HILBERT's note](../notes/CODEX_HILBERT__GLOBAL_MAXIMUM_MINIMUM_ALL_PLAYER_TIES.md).
At an actual minimum with value m>0, the checked MAX singleton margin
B_i−s_i≥m and d_i≤m imply U_i≥s_i for every i. To apply that declaration,
the actual semantic pair belongs to the semantic carrier; its lower bound
against all actual pairs extends to their closure by continuity of maximum
debt. Thus an attained actual infimum is a carrier minimum as required.
Suppose d_k<m. Add one initial date at which only k Quits, with probability
h; on survival use
the entire original independent profile shifted by one date. This is an
actual independent-law operation, not a mixture of publicly selected
profiles. Its complete response caps give

    d'_k=d_k+h(U_k−s_k),
    d'_j=max((1−h)(s_j−U_j)
                 +h(r_j({k,j})−r_j({k})), (1−h)d_j),  j≠k.

For k the full cap is max(s_k,B_k)=B_k. For j≠k the two cap branches
are Quit at the new date or Continue then use any complete old response;
the latter includes Never. Thus these formulas retain EVERY behavioral
tester and do not require a best-response maximizer. Unit reward bounds
give d'_k≤d_k+2h and the first branch for j≠k is at most2h. Choose

    0<h<min(1, (m−d_k)/2, m/2).

Every displayed branch is then strictly below m, contradicting the
global infimum. Consequently d_i=m for all four owners. The argument
applies separately to r and r*. Its all-player-tie conclusion is ordinary
mathematics, not a claimed checked Lean declaration.

Second, at a positive global minimum for a four-player unit-cube table,

    m<1/2.                                               (3)

The same checked margin and B_i≤1 give s_i≤1−m for all i. At the
actual all-Never profile the full cap is max(0,s_i), its prescribed payoff
is zero, and therefore its full regret is

    a=max_i (s_i)_+ ≥ m.

If a=m, all-Never is itself an actual global minimum. Since a=m>0 and
there are finitely many owners, some i has s_i=a>0 and full cap B_i=s_i
there. This contradicts that minimum's checked moat B_i−s_i≥m>0.
Hence

    m<a≤1−m,

which proves (3). This argument, independently observed by
CODEX_NOETHER_SUPPORT, requires neither a fresh gradient certificate nor
transported multipliers, and works at either table once its actual global
minimum has been identified. No quantitative refinement is needed.

## 4. Undoing the stretch at the SAME actual root

For c≥0 the directed edge transform is

    T_α(c)=0                         if c=0;
           (1−α)c+2α                if c>0.              (5)

On [0,2], T_α(c)≥c, with equality precisely when c=0 or c=2.
Both endpoint facts are important: equal reward pairs remain equal, while
the pair (−1,1) is already saturated.

Put β_i=Pr_q(X_i≠b_i). All-player ties at r give d_i(r,q)=m>0, so
β_i>0. Because (2) holds pointwise, b_i is a best action at BOTH tables.
Independence and the complete two-endpoint response formula give

    d_i(r*,q)=β_i E_(q_−i)[c_i],
    d_i(r,q) =β_i E_(q_−i)[T_α(c_i)]=m.                 (6)

Thus EVERY original debt is at most m. This calculation genuinely covers
the old full caps: the SAME root q at date zero has at least two sure
quitters, so old own-singleton coordinates and every declared post-root
tail are irrelevant to every unilateral response.

Using the ORIGINAL worst table and the fiber's upper bound now yields

    Ω=η(r*)≤E_(r*)(q)≤m≤Ω.                              (7)

All values in (7) are equal. In particular q is an actual positive global
minimum at r*, and the old all-player-tie theorem forces

    d_i(r*,q)=d_i(r,q)=m       for every i.                (8)

This is the genuinely global step. No local/contact-only fixture and no
normality in the56 frozen reward coordinates can replace (7).

## 5. Equality produces an actual pure exact equilibrium

In (6), β_i>0 and every supported opponent configuration has positive
probability. The losses T_α(c_i)−c_i are nonnegative term by term.
Equation (8) therefore forces, for every supported configuration,

    c_i(z)∈{0,2}.                                        (9)

The same directed values occur at r, since both0 and2 are unchanged by
stretching. Define the event

    A_i={X_i≠b_i and c_i(X_−i)=2}.

For each pure draw X in the source's product support, every full response
still meets another sure quitter. Its exact owner-i regret is therefore
2·1_(A_i)(X). A player currently using its better action has zero debt;
a player using the other action has debt equal to its endpoint gap0 or2.
No new test after the root can produce a third endpoint.

Equation (6) now says Pr_q(A_i)=m/2 for every i. Consequently

    E_q[Σ_i 1_(A_i)] = 2m < 1.                          (10)

The random variable inside this expectation is a nonnegative INTEGER on
a finite support. If every supported root draw belonged to at least one
A_i, its expectation would be at least1. Hence some supported pure draw
x satisfies x∉A_i for all four owners. At its actual date-zero pure root,
followed by Never, EVERY full regret is zero. At least two members of K
still quit surely, so its terminal coalition is nonempty and the full
response calculation remains valid at this pure endpoint.

This is an actual strict competitor at BOTH r and r*, not a played mixture
over source profiles: the two tables have the same relevant directed gaps
0 or2 at this supported vertex. It contradicts either η(r)=m>0 or
η(r*)=Ω>0. Thus the source's strict pure nonsingleton floor is entrance
context, not a necessary hypothesis of this consumer. It is exact terminal
Nash; its prescribed play and every unilateral response absorb at date zero
because a sure opponent remains. The argument requires only the terminal
contradiction, not a new
uniform-payoff compiler.

## 6. Probability, agency, and exact boundary tests

The game ends at the first nonempty simultaneous Quit coalition. Before
absorption the only public history is continued play; no public random
signal or mediator is added. A player's full behavioral law is represented
by a private stopping clock on ℕ∪{Never}, and the four prescribed clocks
are independent. An unrestricted deviator may replace its entire law.
Conditioning its private randomization on the surviving history does not
give a third date-zero action: its complete payoff is still a mixture of
the Quit and Continue endpoints whenever a sure opponent remains.

The solo prefix in Section3 uses one player's private coin and the actual
old continuation laws. The product draw in Section5 is used only to prove
that a deterministic supported vertex exists; no correlated lottery over
vertices is implemented.

### 6.1 Zero and saturated edges

For every 0<α<1, a zero directed edge remains zero. A positive edge c<2
strictly increases by α(2−c), while the saturated edge c=2 is unchanged.
For example, α=1/4 sends c=1 to5/4 and sends c=0,2 to themselves.
At α=0 the saturation inference fails, so the strict positive stretch
hypothesis cannot be dropped.

### 6.2 An exact successful finite-vertex count

Here and in the next test, define a complete unit-cube table by the
following convention: on every specified owner membership pair assign
preferred reward +1 and opposite reward −1 when its directed gap is2;
assign both rewards zero when its gap is0. All unspecified pairs and all
four own singletons are zero. Different owners' pairs are different reward
coordinates, and each owner's specified opponent configurations give
disjoint pairs, so this is a consistent complete reward table.

Let owners0,1 be sure, take preferred actions b=(0,0,1,1), and let the
independent optional bits satisfy q_2=1/2 and q_3=3/4. Give both core owners
gap2 exactly at optional configuration00. Give owner2 gap2 exactly when
x_3=0 and owner3 gap2 exactly when x_2=0. All remaining supported gaps are
zero. Then all four losing events are the SAME event00, of probability1/8.
Each mixed-root debt is1/4, and the expected number of losing owners is1/2.
Every supported optional vertex other than00 has full regret zero.
This checks the constructive counting step, not positive global
attainment: indeed all Never is also exact Nash at this table.

### 6.3 The strict-half obstruction is substantive

For a negative boundary test from FRECHET's independent review, retain
sure owners0,1, let both optional bits be fair, and take b=(0,0,1,0).
Set the positive directed gaps by

    c_0=2 exactly when (x_2,x_3)=(1,0);
    c_1=2 exactly when (x_2,x_3)=(1,1);
    c_2=2 exactly when x_3=0;
    c_3=2 exactly when x_2=0.

Use the preceding whole-table convention. The mixed root has all four
debts1/2, but its supported pure debt vectors are

    (0,0): (0,0,2,0);       (0,1): (0,0,0,2);
    (1,0): (2,0,0,0);       (1,1): (0,2,0,0).

Every vertex has exactly one losing owner. Thus the non-strict bound
m≤1/2 cannot replace (3) in the finite count. This is not a counterexample
to the theorem: all own singletons are zero, so all Never has full regret
zero and the displayed mixed root is NOT a positive global minimum.

### 6.4 Averaged coherence does not suffice

Let one owner's directed old gap be2 with probability2/5 and −1/2 with
probability3/5. Its positive mean is1/2, but its stretched mean is

    1/2−9α/10.

Undoing the stretch increases that positive averaged gap. A selected
averaged best action therefore does not justify Section4. This is an
exact local algebra test, not a purported global-source counterexample.

### 6.5 Timing, singleton, and support boundaries

With two sure quitters at date zero, changing any own-singleton rewards
does not change the two endpoints of any owner's full cap. This fails if
one silently prepends a date: an outsider whose two screened endpoints
are zero can Quit at the new earlier date and receive its own singleton.
Changing that singleton from0 to1 changes its padded cap from0 to1.
Likewise, with just one sure quitter the sure owner's own Quit endpoint
can itself be its reselected singleton. Neither modification is admitted
by the theorem's old-table comparison.

No division by an optional action probability occurs. A coordinate with
probability0 or1 contributes only its supported action; every selected
vertex retains all members of K. Equal edges, absent optional actions,
signed own singletons, and an optional best action equal to Continue are
all covered. If a three-sure source had a pure optional action, the
pointwise conditions would be automatic after all-player ties; the
contradiction therefore also forces that remaining hazard to lie strictly
between0 and1.

## 7. Actual-data adapter, consumer, and source correspondence

The named live obligation narrowed here is consumption of the
zero-Never, zero-singleton sure-core realization of the reconstructed
positive worst-table source. This is not an assertion that every
near-minimizing source has those zero masses.

The upstream ordinary-mathematics input is the reviewed
[membership-stretch and singleton-fiber source reduction](../exports/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md).
Its construction retains one original full-cube maximizing r*, the same
positive α, and the 56 stretched coordinates while maximizing over the
four own singletons. The resulting fixed table r has positive value
m≤Ω. Those concrete relations, not just a tuple of multiplier inequalities,
are the inputs used here. The strict pure nonsingleton floor, same-weight
pressure, and positive owner weights of that source are not needed again
by this particular consumer.

For a supplied joint semantic/law carrier point at the final table with
zero Never and all singleton masses, a positive global MAX minimum gives
strict cap-singleton margins. The checked declaration
`exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin`
in
`UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`
then provides ONE unpadded root-then-Never profile with at least two sure
quitters, preserving the ENTIRE prescribed-payoff/full-cap pair and
terminal law. Its objective is therefore the same actual minimum m.
This is the entrance to Section1; no cap preservation is inferred merely
from payoff equality. The neighboring weak-margin padded realization
cannot silently replace this declaration.

The checked MAX margin used in Section3 is
`minimumTerminalSemantic_exploitabilitySingletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`.
It applies with signed own singletons and a minimum against the whole
semantic carrier. The extension from an attained actual infimum to that
carrier is explained in Section3. The all-player-ties conclusion itself
is not being attributed to this declaration: its complete ordinary proof
is included.

The screened pure endpoint is also exactly the semantic content of
`quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card`
in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.
The result is tail-independent with at least two sure quitters; Section1
derives the needed full-response formula directly for mixed roots too.

The new consumed output is a contradiction under pointwise coherence,
equivalently a necessary supported preference reversal in every such
realized source. With exactly three sure players, some sure owner's
Continue-minus-Quit gap is strictly positive at one supported optional
action and strictly negative at the other. With two sure players, at
least one owner's source-best direction is negative at a supported
opponent configuration and positive at another; this owner can be one
of the optional players. The theorem does not transfer the original
calendar-labelled multipliers to the reconstructed root.

The narrow source audit found no existing declaration expressing this
inverse-stretch comparison and supported-vertex consumer. This is not an
exhaustive priority claim. No paper theorem or historical equilibrium
existence class is used; the finite probability and affine cap arguments
are given completely here.

## 8. Narrow Lean handoff

The following are intended theorem shapes, not claims that these new
declarations already exist. Use the project's actual semantic pair,
product-root, and carrier definitions; no new structure should assume
the sought sign reversal, all-player ties, or a successful vertex.

1. **All-player ties at an attained positive MAX minimum.** Inputs are a
   unit-cube reward table, an actual profile whose semantic pair minimizes
   maximum debt over the carrier, and positive minimum. Output:
   every complete debt equals that maximum. Use the named checked
   singleton margin and the complete solo-prefix formulas in Section3.

2. **Strict-half bound in the unit cube.** Inputs are a reward table on
   Fin4 with all coordinates in [−1,1] and an attained positive global
   maximum-debt minimum m. Output m<1/2. The only new comparison is the
   actual all-Never semantic pair; no multiplier selection is needed.

3. **Inverse-stretch sure-core consumer.** Finite data are r*, r, α, q,
   and binary best actions b. Assumptions state the literal signed
   membership stretch on each nonempty opponent set; arbitrary own
   singleton coordinates; η(r*)=Ω>0; η(r)=m>0 with m≤Ω; at least two
   coordinates q_i=1; and the root-then-Never full objective equal to m.
   For every i and every positive-product-weight opponent configuration,
   assume the directed old gap toward b_i is nonnegative. Prove False
   by constructing a supported vertex with zero full debt at both tables.
   The source construction supplies these r*, r, α relations; a source
   structure must not replace them by only the final table's stationarity.

4. **Carrier adapter and three-sure corollary.** Apply the checked
   strict-margin product-base realization to a zero-Never/zero-singleton
   carrier minimum, then the preceding consumer. If exactly three
   coordinates are sure, conclude the fourth is genuinely mixed and
   produce a sure owner with opposite strict signs at its two optional
   configurations. Coherence of optional owners is NOT automatic in
   the two-sure theorem.

Useful finite definitions are the product support of q, the two endpoint
coalitions S(z,a), the signed membership stretch with a separate zero
case, and the indicator of a supported losing action on a saturated edge.
The finite counting lemma is simply that a nonnegative integer-valued
random variable of expectation below1 vanishes at some positive-weight
point. Its output is a deterministic vertex; do not compile the proof
distribution as correlated play.

The exact fixtures in Section6 test the {0,2} equality case, critical
half-boundary, signed mean failure, and one-row padding seam. Narrow
formalization checks should begin with the finite endpoint/stretch/count
lemmas, then the actual solo-prefix and carrier adapter. No existing Lean
implementation or build is supplied by this packet.

## 9. Scope

The result strictly narrows the actual reconstructed worst-table source:
a sign-coherent at-least-two-sure realization is impossible. It does not
prove all minimizing sources have zero Never/singleton mass, prove
attainment for arbitrary full-cap semantic points, preserve old tester
weights through realization, establish a new raw-table UE class, or
consume the sign-reversing branch. That remaining branch requires a
genuine full-response improvement using further source information.

The source's strict pure-coalition separation is not a hidden premise:
the constructed pure vertex already contradicts positive global value
at either table. Conversely, the original-table provenance and
unrestricted global minima are essential to the proof. Contact-only,
fixed-calendar, SUM-minimum, or arbitrarily selected solved-profile data
do not justify the comparison in (7).
