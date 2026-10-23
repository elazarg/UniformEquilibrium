# Sure incoming roots and proper-law limits realize global partial-Nash minima

Owner: CODEX_PIVOT_REVIEW.

Status: complete ordinary proof, not Lean-implemented and not an export.
The sure-root argument was independently proposed by the calendar-adversary
subagent and checked by CODEX_PIVOT_REVIEW. Its scalar-cap and prefix steps
are proved below. The proper-limit argument is an adaptation of inspected
checked declarations whose original minimum telescope is different. This
does not prove that every global partial-Nash minimum is realized, does not
make the pivot proper, and does not settle Fin4.

## 1. Question and model

There are finitely many players, at least two. Each chooses an independent
complete stopping law on N union {Never}. The first finite stopping date
pays the whole simultaneous quitting coalition; all-Never pays zero. Write
r_i(S) for the reward of player i at nonempty coalition S, and assume

    r_i({i})=0 for every i,       |r_i(S)|<=M, M>=1.

U_i is the prescribed terminal payoff and B_i is the supremum over EVERY
complete unilateral replacement law, equivalently every finite deadline
and Never. Set d_i=B_i-U_i. Let K be the closure of the payoff/full-cap
pairs of actual absorbing independent profiles.

The global partial-Nash problem for pivot p is

    C_p={X in K:d_i(X)=0 for i!=p},
    m=min_(X in C_p) d_p(X)>0.

The [incoming collision theorem](CODEX_OBSERVER_PATH__GLOBAL_MINIMUM_INCOMING_COLLISION.md)
produces X=prefix_q(Y) at a positive global minimum, with Y in K and a
nonzero product root q. It allows both sure and nonsure roots. Can the
sure branch, or a proper weak law limit, actually realize the minimum?

The answers to these two restricted realization questions are yes. The
sure-root result in fact does not require minimality or positive debt.

## 2. Every scalar cap in its closure is attained

Fix player k. Let mu range over all independent complete laws of the
OTHER players, with no absorption requirement, and define

    b_k(mu)=sup_(complete k laws) U_k(law,mu).

Its range is a closed interval [alpha_k,R_k], where

    alpha_k<=0,       R_k=max_(nonempty S) r_k(S)>=0.       (2.1)

First, compactify each private law on the one-point compactification of
N. This is a compact space of probability laws. A fixed finite deadline t
has continuous payoff f_t(mu): its value depends only on finitely many
finite atoms and their complementary tail probabilities. Own singleton
zero also gives

    f_t(mu) -> U_k(Never,mu) as t -> infinity.

Indeed, the only remaining branch on which a late deadline differs from
Never has all opponents later than t; its eventual singleton payment is
zero. Bounded convergence, or the exact inspected finite-time limit
declaration, gives the assertion. Pure-law extremality therefore yields

    b_k(mu)=sup_(t in N) f_t(mu).

Thus b_k is lower semicontinuous on the compact opponent-law space and
attains its minimum alpha_k. All opponents Never gives cap zero, proving
alpha_k<=0.

Every terminal reward and the Never reward are at most R_k, so b_k<=R_k.
Choose a coalition S attaining R_k. Have every opponent in S quit at date
zero and every other opponent Never. If k is in S, its date-zero response
obtains R_k; if k is outside S, its Never response obtains R_k. The case
S={k} is covered by all opponents Never and own singleton zero. Hence R_k
is an attained scalar cap, not merely an upper bound.

Let mu^- and mu^+ attain alpha_k and R_k. For 0<=t<=1 mix EACH opponent's
private laws independently:

    mu_j(t)=(1-t)mu_j^-+t mu_j^+.

The common parameter t is deterministic and introduces no public or
cross-player randomization. The product distributions are continuous in
total variation. Uniformly over EVERY response law of k, the payoff
difference between parameters t and s is at most

    2M*(number of opponents)*|t-s|.

The same bound holds for the suprema b_k. The intermediate value theorem
therefore supplies every value in [alpha_k,R_k]. This proves (2.1), and
in particular proves that any limit of actual scalar cap values is
attained by some actual independent opponent laws.

For nonnegative target caps there is an even simpler finite-calendar
realizer. Interpolate all-Never opponents to the pure maximizing profile
above, using only Quit at zero and Never. The cap is the maximum of its
date-zero and Never values; every later deadline has the Never value by
own singleton zero. This continuous path starts at zero and ends at R_k.
No finite-support assertion is needed for negative target caps.

## 3. A sure incoming root realizes the entire pair

For a product root q write

    H_i=product_(j!=i)(1-q_j),       c=product_j(1-q_j).

Let Q_i be its forced-Quit endpoint and P_i its passive nonempty-opponent
payoff. The exact full-cap and payoff prefix formulas are

    U'_i=q_i Q_i+(1-q_i)P_i+c U_i,
    B'_i=max(Q_i,P_i+H_i B_i).                         (3.1)

Suppose Y belongs to K, c(q)=0, and X=prefix_q(Y). Then X is the exact
payoff/full-cap pair of an ACTUAL ABSORBING independent profile.

If at least two owners are sure, H_i=0 for every i. Both vectors in
(3.1) are independent of the entire tail pair. Follow q by any actual
tail, for example all-Never.

If exactly one owner k is sure, H_i=0 for every i!=k. All prescribed
payoffs and every cap other than B'_k are again independent of the tail.
The remaining cap depends on the tail only through the one scalar B_k(Y).
This scalar is a limit of actual cap values because Y belongs to K.
Section 2 supplies actual independent opponent laws with precisely that
cap. Add an arbitrary law for k, and prefix this actual tail by q. Formula
(3.1) now reproduces EVERY payoff and full cap of X. The sure root makes
this profile absorbing, regardless of the tail's absorption behavior.

No Nash condition, minimum property, particular sign of B_k(Y), or
attainment of a maximizing response is used in this proof. Replacing the
tail by all-Never without matching the scalar cap would in general be
incorrect in the unique-sure-owner case.

The same conclusion holds for a finite word containing any sure root:
first realize its suffix beginning at that sure root, then prefix the
earlier finite word. Thus a nonrealized carrier point cannot have ANY
exact finite-word factorization through a sure root.

## 4. Two refinements at a partial-Nash minimum

Suppose X in C_p attains m>0 and has a unique sure incoming owner k.

If k is an observer, its sure Quit value is already its output cap:
B_k(X)=U_k(X)=Q_k. Hence the scalar-minimizing opponent laws from Section 2
are sufficient; they can only decrease the Continue endpoint, while Quit
continues to attain the output cap. Every other payoff and cap is fixed.

If k=p, then U_p(X)=Q_p and B_p(X)=Q_p+m>Q_p. The Continue branch in
(3.1) is strictly higher than Quit. Global minimality forces

    B_p(Y)=alpha_p<=0.                                  (4.1)

Otherwise replace the tail by a scalar-minimizing cap realizer. All
observer pairs and all prescribed payoffs remain unchanged, while the
pivot cap decreases strictly: even if it crosses to the Quit branch,
the new maximum is strictly below the old strictly larger Continue
branch. This gives an actual absorbing point of C_p below m, impossible.
In this case the realization already has a proper pivot, because the
pivot itself quits surely at the initial date.

When the sure owner is an observer, Section 3 supplies a proper observer,
not necessarily a proper pivot. Changing the pivot's later law can change
the sure observer's cap under its Continue deviation. That change cannot
be silently discarded merely because play absorbs immediately.

## 5. A proper weak law limit realizes a global C_p minimum

Let actual absorbing profiles have pairs tending to X in C_p with
d_p(X)=m, and let their compact stopping laws converge weakly to lambda.
If ANY lambda_k is proper, then lambda is an actual absorbing profile
and its entire semantic pair is X.

The checked partial realization theorem gives exact convergence of U
and of every cap except possibly k's. For the exceptional cap, each
fixed finite deadline at lambda has value at most B_k(X), by finite-time
continuity. Own singleton zero and the deadline-to-Never limit from
Section 2 then give

    B_k(lambda)<=B_k(X).                               (5.1)

If k is an observer, prescribed payoff is already U_k(lambda)=U_k(X)=
B_k(X). The elementary bound B_k(lambda)>=U_k(lambda) forces equality.
If k=p, all observer pairs are already exact, so the actual absorbing
pair of lambda belongs to C_p. Global minimality yields
d_p(lambda)>=m=d_p(X); since U_p is exact, this reverses (5.1) and again
forces equality. No coordinate is left unmatched.

The inspected declaration
`target_cap_le_of_proper_minimum_lawLimit` instead assumes a whole-carrier
TOTAL-debt minimum. That telescope is not the present C_p hypothesis.
The preceding argument is the required adaptation, rather than an
unqualified application of that declaration.

## 6. Exact remaining nonrealization boundary

For the all-positive global minima covered by the incoming collision
theorem, one now has the following alternative:

- The minimum has an actual absorbing realization; this is not a finite
  support or proper-pivot representation theorem.
- If it has no such realization, its produced incoming collision is
  nonsure, its tail Y belongs to C_p, and

      0<c<1,       m=R_p+c d_p(Y),       d_p(Y)>=m.

  Every compact weak law limit of an absorbing realizing sequence is
  all-improper. No exact finite-word factorization can contain a sure
  root.

In fact EVERY nonzero incoming root at such an all-positive minimum has
automatic macroscopic activity. Put mu=min_(i!=p) B_i(X)>0. A sole pivot
root of size t in (0,1) would have a tail in C_p and satisfy

    m=t B_p(X)+(1-t)d_p(Y)>m,

using B_p(X)>m. A sure sole pivot would give U_p(X)=0. Hence every
nonzero incoming root has an active observer i. Its zero output debt
forces zero root regret and Q_i(q)=B_i(X)>=mu. Own singleton zero gives

    |Q_i(q)|<=M*(1-H_i)<=M*sum_(j!=i) q_j.

Thus every nonzero incoming root has sum_i q_i>=mu/M. This is a bound
for ALL exact incoming factorizations, not merely the extracted one.

There is also a uniform nonsure margin at each fixed nonrealized X.
The set

    D_X={(q,Y) in [0,1]^I times K:prefix_q(Y)=X}

is compact by continuity of (3.1). Section 3 rules out q_i=1 throughout
D_X. Therefore some eta(X)>0 bounds EVERY incoming factorization by
q_i<=1-eta(X), hence c(q)>=eta(X)^|I|. This is a compactness consequence
of the actual realization theorem, not an assumption on a selected root.
If an entire compact minimum fiber has no realized point, the same
argument gives one uniform eta for that fiber.

What still prevents recursive unrolling is exact: the produced tail can
have debt STRICTLY ABOVE m, so it need not have the positive payoff/cap
margins used by the incoming theorem. Reanchoring at that tail changes
the minimization target. Calendar compression cannot assume away a
diffuse suffix, and an infinite word whose survival stays positive does
not give an absorbing realization. Neither obstruction is resolved here.

The next question is whether global minimality forces a return to the
minimum fiber, or a debt-lowering whole-law substitution, along these
uniformly nonsure incoming collisions. The sure branch no longer needs
a compactness or support-compression argument.

## 7. Global unrolling and a terminal minimum with a strict tail-debt gap

There is one genuine global-minimum improvement to the usual unrolling
test. Suppose X_0 is a global C_p minimum and there is an infinite exact
chain

    X_t=prefix_(q_t)(X_(t+1)),       X_t in K,
    product_(t<n) c(q_t) -> 0.                         (7.1)

Then X_0 has an actual absorbing realization. The later X_t need not
themselves be minimum points.

Use q_t as the literal independent behavioral root at date t. Its joint
survival tends to zero by (7.1), so this is an absorbing profile. Iterating
the exact payoff equation shows that its first n dates have the prescribed
head payoff of X_0 with a remainder bounded by M times that survival.
The actual payoff is therefore exactly U(X_0).

Each fixed finite deadline uses only finitely many of these roots. The
exact full-cap recursion along that finite prefix bounds its payoff by
B_i(X_0). Own singleton zero makes the actual Never payoff the limit of
these finite deadlines. Thus the ACTUAL complete cap obeys

    B_i(actual)<=B_i(X_0) for every i.                  (7.2)

For observers, U_i(actual)=U_i(X_0)=B_i(X_0) and B_i(actual)>=U_i(actual)
force equality. The actual pair consequently belongs to C_p, and its
pivot debt is at most m by (7.2). Global minimality forces equality for
the pivot as well. This proves full actual realization.

For an arbitrary carrier pair, vanishing joint survival does not alone
prove equality of all caps: a player can remove its own stopping hazard
by deviating. Here (7.2) is the only direct cap conclusion, and zero
observer debt plus GLOBAL minimality repair exactly that missing step.
No vanishing deleted-player survival is assumed.

Now let M_p be the compact fiber of global C_p minima and suppose every
point in M_p has positive observer caps and positive pivot payoff. These
are the generic sources already proved in the expensive-exit note. By
compactness and the preceding activity estimate, the positive constant

    delta=min_(X in M_p, i!=p) B_i(X)/M

bounds the activity of EVERY nonzero incoming root at every X in M_p.
The incoming collision theorem supplies at least one such root at every
source; only this existence part of that theorem is needed here.

Starting from ANY minimum X_0 in M_p that has no actual absorbing
realization, one can reach a nonrealized X_* in M_p along a finite chain
of nonzero minimum-to-minimum incoming factorizations, and find
kappa>0 such that EVERY nonzero incoming factorization of X_* obeys

    X_*=prefix_q(Y), Y in K, q!=0
        implies c(q)>0, Y in C_p, d_p(Y)>=m+kappa.       (7.3)

To prove this, consider the compact relation on M_p consisting of edges
X -> Y with a nonzero root q and X=prefix_q(Y). It is compact because
nonzeroness here is equivalent to the closed activity bound at least
delta. Every
infinite edge chain starting at X_0 has

    product_(t<n)c(q_t)<=exp(-n*delta) -> 0,

and therefore realizes X_0 by (7.1)--(7.2), contrary to the supposition.
There cannot even be arbitrarily long finite chains STARTING AT X_0:
compactness and a diagonal subsequence of their nodes and roots would
produce an infinite one. Hence a maximum-length finite chain from X_0
has a terminal node X_* admitting no edge to another minimum. This node
is nonrealized too: an actual absorbing realization of X_* followed by
the preceding finite prefix would realize X_0. Realized and nonrealized
minima elsewhere in the fiber are allowed to coexist.

The set of all nonzero factorizations (q,Y) of this fixed X_* is
nonempty by the incoming theorem and compact by the prefix formulas.
It has no sure root by Section 3. Zero observer output debt and c>0
force Y in C_p. Terminality means d_p(Y)>m for every one of these tails;
compactness makes the difference uniformly positive, proving (7.3).

This is a produced strict obstruction, not an assumption that the tail
is a minimum. It also gives the exact root-regret deficit

    R_p(q;B(Y))<=m*(1-c(q))-kappa*c(q).                 (7.4)

The uniform nonsure margin from Section 6 bounds c(q) away from zero, so
the deficit in (7.4) is uniformly strict for the selected source. The
outgoing minimum bound at X_* has the opposite direction, but is priced
at B(X_*), and an incoming root need not remain observer-Nash there.
Equating these different continuation-cap annotations would be invalid.

Thus every nonrealized global minimum has a finite incoming reduction
to a nonrealized minimum for which EVERY nonzero incoming collision
has a uniformly higher-debt tail and a uniformly deficient incoming pivot
regret. A closing substitution must consume that source; recursive
minimum-to-minimum unrolling has already been exhausted by the selection.

## 8. Inspected source and overlap

The source inspection was narrow and used:

- `quittingTerminalSemanticPair_partial_eq_of_proper_lawLimit`,
  `quittingTerminalPayoff_update_finiteTime_le_of_lawLimit`, and
  `target_cap_le_of_proper_minimum_lawLimit` in
  `UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`;
- `quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton`
  in `UniformEquilibrium/Quitting/Terminal/CompactStoppingLawCapUpperBound.lean`;
- `quittingTerminalSemanticPair_rootThenContinuation` and
  `continuous_quittingTerminalSemanticPrefix` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- the existing two-sure-root realization results, including
  `exists_twoSureProductRootThenNever_realizing_semantics_of_strictSingletonMargin`,
  in `UniformEquilibrium/Diagnostics/Quitting/ProductRootLimitCapSandwich.lean`,
  and its carrier wrappers in
  `UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`;
- `quittingPunishmentValue_eq_stationaryPunishmentValue` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`, which equates
  infima and explicitly does not assert general attainment.

The scalar interval argument handles the unique-sure-root case without
the extra two-sure or strict-singleton-margin assumptions. This is an
ordinary source-realization result. It does not add a raw UE table class,
replace the existing canonical positive-cap exit packet, or establish
proper-pivot/finite-calendar realization of every global minimum.
