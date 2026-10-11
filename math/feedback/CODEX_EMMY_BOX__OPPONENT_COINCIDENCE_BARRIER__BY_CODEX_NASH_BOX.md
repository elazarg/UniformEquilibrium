# CODEX_NASH_BOX: bounded adversarial check of collision necessity

## Scope and verdict

Checked Section 3.4 of
`notes/CODEX_EMMY_BOX__OPPONENT_COINCIDENCE_BARRIER.md`, frozen whole-file
SHA256 `aa1165532b0e8dffb56813b40cea82a2778eafbd1027b111b75cda5317bc2d05`.
Section 3.3 was read for its suppression convention, not independently
audited. This is an ordinary mathematical review, not Lean verification.

**PASS: no mathematical objection found to the stated uniform collision
necessity theorem.** For each M >= 4 and zeta > 0, over the entire bounded
raw-table class with singleton columns I+4P and incoming adjacent-pair
recipient reward at least 1+zeta, some gamma(M,zeta)>0 satisfies
FULL exploitability + actual first-terminal-collision probability >= gamma
for every independent complete private-clock profile.

This is a necessary strategy-mode constraint, not a positive exploitability
bound or a reward-table exclusion from the UE conjecture. In particular its
collision term cannot be dropped. No exhaustive source-novelty claim was
reviewed.

## Quadratic identity and complete-deviation ledger

Independently checked AR=-15I and symbolically expanded the four complete
axis identities (7j). Since the residual polynomial vanishes on each axis
as a polynomial in that axis coordinate, every surviving monomial contains
two distinct hazard variables. On the compact reward/value box, assigning
such a monomial to one of those pairs gives its claimed O(d) bound: all
remaining hazard factors are at most one and q_i q_j <= d. No square-root
collision estimate is being hidden here.

The suppression inequality (7l) is valid for complete deviations. In a
finite selected window suppress exactly the old i-hazards whose old
Continue value exceeds old Quit value. The performance-difference identity
uses the changed joint reach J'_t and the *old* continuation value:

    gain = sum_selected J'_t q_i(t) (C_it-Q_it).

Here J'_t >= J_t, and
q_i(U_ti-Q_it)_+ = q_i(1-q_i)(C_it-Q_it)_+.
Consequently this gain dominates the finite left side of (7l). Monotone
convergence of the nonnegative sums gives the infinite bound. Hazards equal
to one cause no difficulty because U_ti-Q_it=0 there. Negative terms in
(7m) are bounded using J_t(Q_it-U_ti)<=eta and
sum_t J_t sum_i b_it <= 1; positive terms are bounded by the four
suppression ledgers. Thus the asymmetric interval [-eta,4eta] and the
120eta term in (7o) are sound.

Also |Q_i-1| <= (M+1) sum_(j!=i) q_j and
sum_i q_i sum_(j!=i) q_j = 2 sum_(i<j) q_i q_j <= 12d,
which verifies (7n) and the displayed collision coefficient. The infinite
boundary is controlled by an actual legal replacement: keep every finite
own atom and move only its private Never atom to deadline H, then H tends
to infinity. Its limiting improvement is the joint Never probability rho,
because own singleton reward is one and all finite opponent tails vanish.
Thus rho <= eta. The bound |F(U)| <= 20M^2+15 then supplies exactly the
last term of (7o).

## Calendar compactness, not merely weak payoff convergence

The induction over finite dates is valid. At any limiting positive joint
reach, match-prefix replacements bound every conditional full regret by
eta_n/J_nt. Conditional collision probability and joint Never mass vanish
as well. The actual terminal-law decomposition therefore places U_t in H,
while applying (7o) to that actual conditioned profile gives F(U_t)=0.

There are two important closed-boundary exclusions:

- If q_t=0, full Quit inequalities give U_t >= 1 coordinatewise. Writing
  g=U_t-1, one has g>=0, sum g=1, and
  F(U_t)=g^T(I-4P)g-3 <= -2, a contradiction.
- If a sole hazard is one, its successor's prescribed value is zero,
  whereas its joining replacement pays at least 1+zeta.

Thus each successive finite joint reach remains positive. Once this has
constructed all finite limiting roots, their data lie in the stated
compact root-inequality set. The first exclusion supplies a uniform
positive lower hazard. Successor optimality gives
(1-p)V_(j+1) >= 1+zeta*p with V_(j+1)<=4, hence
p<=3/(4+zeta)<1. The resulting geometric joint termination is justified;
it is not being inferred from weak closure of proper clock laws.

Iterating the exact recursion now identifies U_t with the *actual* values
of these limiting independent clocks. For arbitrary complete behavioral
replacements, truncate their terminal reward after H to zero. Backward
induction applies the limiting root inequalities, using 0<=U_H as the
terminal comparison. The truncated rewards converge boundedly to the
actual finite-or-Never reward. This proves unrestricted terminal Nash,
even when deleting the deviator's clock would destroy geometric opponent
termination. It does not require the deviating profile to retain the old
joint-reach bound.

## First-owner-change contradiction

At a mixed sole-j root, both current and next j values are one. If the
first later different owner is j+1, its own-root value one is discounted
strictly below one by the intervening j-only hazards, while its earlier
Quit endpoint exceeds one. If the new owner is j-1, the old j value stays
one through the intervening j roots, but at the new root j can join for
more than one. Both cases contradict a full replacement inequality.
Hence every change is to the opposite mate. If there is no later change,
the same outsider argument already contradicts Nash. With repeated mate
changes both remaining players receive zero on every actual terminal
singleton, whereas a successor can join a positive j-root for strictly
more than one. This rules out the entire extracted one-owner calendar,
not only a periodic word or a bounded-gap schedule.

## Exact checks and inspected declaration scope

An independent integer first-absorption calculation on the saved twelve-
and thirteen-date profiles reproduces the two beta fractions printed in
Section 3.4 exactly:

    176504962032139/2500000000000000,
    12860868170899/200000000000000.

Opened the literal declarations
`pairedFacePotential_boundedCompletion_face_drift` and
`pairedFacePotential_boundedCompletion_not_fullRoot` in
`UniformEquilibrium/Quitting/Examples/PairedFacePotentialBoundedCompletion.lean`,
and `translated_face_drift_ge_one` in
`MathUE/Analysis/Examples/PairedFacePotential.lean`. Their supplied-potential
face/full-root statements do not themselves assert this all-profile
collision bound. This narrow comparison does not certify absence of a
different existing proof elsewhere.
