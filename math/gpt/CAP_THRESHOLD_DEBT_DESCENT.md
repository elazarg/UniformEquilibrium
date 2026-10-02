# Finite cap-threshold descent and a quadratic minimum-margin collar

## Status and exact contribution

This note proves an ordinary-mathematics finite-prefix descent theorem. A
repeated solo hazard is stopped at the first outsider cap threshold. Until
that stopping point, every outsider's **complete** response cap stays on the
Continue branch, so the entire total-debt evolution is an exact affine
identity. One auxiliary Nash root then gives a quantified decrease.

The construction yields:

1. For an arbitrary actual source, a finite literal prefix with final total
   debt bounded by an explicit function of the original debt and one cap
   margin. It needs no cap-attaining response and performs no horizontal
   replacement of an old stopping law.
2. At a positive global minimum, the stronger margin
   `B_i-s_i >= D_* + D_*^2/(8M)` for every nonnegative-singleton player.
   A smaller table-dependent joining-loss constant can replace `2M`.
3. An explicit finite-law selector under weak coordinate payoff exclusion
   `min_i(U_i-s_i)<=0`, without a uniform negative deficit or a nondegenerate
   averaging weight. The rational version has an explicit quadratic inverse-
   accuracy date bound.

The auxiliary-root ledger and the below-singleton absorption estimate are
existing inputs, credited in Section 9. The new step is the finite first-cap-
threshold block and its exact debt budget, together with its composition into
these conclusions. The qualitative weak-exclusion result can also be obtained
from the existing minimum-margin and singleton-tight-face arguments; its mere
qualitative statement is not claimed as a newly solved reward class.

This does not prove arbitrary four-player UE or produce a counterexample. It
has not been formalized in Lean or independently reviewed. The accompanying
script checks exact finite instances, not the universal theorem. No repository
file was changed, committed, or pushed.

## 1. Full behavioral semantics

Let I be a finite player set with n>=2. At a live date, players independently
choose Continue or Quit. The first nonempty quitting coalition S pays r(S);
Never pays zero. Fix M>0 with |r_i(S)|<=M and write s_i=r_i({i}).

A strategy is an independent stopping law on N union {Never}. For an actual
profile p, define

    U_i = expected terminal payoff,
    B_i = supremum over every complete unilateral replacement law,
    d_i = B_i-U_i,     D = sum_i d_i,
    L_i = B_i-s_i.

Caps include all finite times, arbitrarily late finite times, Never, and all
private randomization. In particular, U_i and B_i lie in [-M,M]. No best-
response attainment is assumed.

For a product root q define

    c = product_i(1-q_i),     a = 1-c,
    beta_i = product_(j!=i)(1-q_j),
    pi_i = q_i beta_i.

Let Q_i be its Quit endpoint and H_i its absorbing contribution conditional
on i choosing Continue. Literal prefixing gives

    U'_i = q_i Q_i + (1-q_i)(H_i+beta_i U_i),
    B'_i = max(Q_i,H_i+beta_i B_i).                    (1)

The second equation is an identity for the unrestricted supremum. Its Continue
branch permits every old complete response, including Never.

Let K be the closure of actual pairs (U,B). It is compact, the displayed
finite-prefix maps preserve K, and D is continuous. All finite algebra below
therefore also holds on K. Prefixing a fixed word to approximants of a carrier
point gives its prefixed carrier point; it does not claim realization of an
arbitrary carrier point by one actual profile.

## 2. Two existing auxiliary-root facts

Choose h>=0 and an independent exact Nash root against the auxiliary
continuation v=B-h*1. The root is then prefixed to the **actual old profile**,
not to the annotation v. The existing auxiliary-prefix inequality gives

    d'_i <= c d_i + pi_i h,
    D' <= D-a(D-h).                                   (2)

For an approximate auxiliary root, let g_i be ordinary mixed-root regret:

    g_i = max(Q_i,H_i+beta_i v_i)
          - [q_i Q_i+(1-q_i)(H_i+beta_i v_i)].

Exactly the same algebra yields

    d'_i <= c d_i + pi_i h + g_i,
    D' <= D-a(D-h)+sum_i g_i.                         (3)

To see the coordinate identity behind the inequality, write w_i for the mixed
root payoff at v. Then B'_i<=w_i+g_i+beta_i h, whereas
U'_i=w_i+c(h-d_i). Their difference gives (3).

If some v_j<=s_j-delta with delta>0, endpoint subtraction gives

    Q_j-(H_j+beta_j v_j)
       >= beta_j delta-2M(1-beta_j)
       >= delta-(2M+delta)a.                         (4)

Consequently every exact auxiliary Nash root has

    a >= delta/(2M+delta).                           (5)

Otherwise Quit is strictly preferable for j, forcing q_j=1 and a=1, a
contradiction. If max_i g_i<=delta/4, the corresponding bound is

    a >= delta/[2(2M+delta)].                        (6)

Indeed, smaller absorption would make j's endpoint gain greater than
delta/2 while q_j<=a<1/2, giving mixed regret greater than delta/4.

No bound on the auxiliary coordinates v_i is needed in (4).

## 3. Finite cap-threshold descent

A strict singleton preemptor of owner i is a player j!=i with

    ell_i := s_j-r_j({i}) > 0.

The local theorem permits arbitrary signed singleton rewards. The
nonnegative-singleton assumption enters later, when the absence of such a
preemptor is converted into an equilibrium alternative.

### Theorem 1: literal finite-prefix bound

Fix an actual source p with D>0 and an owner i having a strict singleton
preemptor. Set

    C = max(D,L_i),
    k(C) = 3 C^2/(32M+6C).

There exists a finite word w of independent product roots such that

    D(w::p) <= C-k(C).                               (7)

Every root is literally prefixed to the preceding actual profile. The word
consists of a repeated solo-i root and, possibly, one auxiliary Nash root.
It has at most

    1 + ceil([32(M+C)/C] log(4M/ell_i))              (8)

rows. An empty word is allowed when the current debt already satisfies the
bound. Any known positive lower bound on the preemptor gap may be substituted.

In particular, if L_i<=D, then

    D(w::p) <= D-3D^2/(32M+6D).                      (9)

The same conclusions hold on K by finite-prefix closure.

### Proof

Choose

    theta = C/[32(M+C)],    rho=1-theta,
    z = 4M theta <= C/8,    h=C/2.                  (10)

Notice 0<theta<1/32 and 0<k(C)<C/2.

If D<=h, the empty word suffices. Otherwise, if some cap already satisfies
B_j-s_j<=z, skip directly to the auxiliary step below.

It remains to consider D>h with every L_j>z. Repeatedly prefix the solo root
q_i=theta, q_j=0 for j!=i. Stop at the first m>=1 at which some outsider cap
satisfies B_j^(m)-s_j<=z.

**No outsider cap reset occurs before, or on, the threshold-crossing step.**
For j!=i put a_j=r_j({i}) and

    Q_j = rho s_j + theta r_j({i,j}) <= s_j+2M theta.

As long as the old cap satisfies B_j>s_j+z, its Continue cap endpoint obeys

    rho B_j+theta a_j >= B_j-2M theta
                       > s_j+2M theta >= Q_j.       (11)

Thus the Continue branch in (1) is strictly selected at every required step.
Owner i's cap is unchanged, since its cap is max(s_i,B_i)=B_i. Therefore,
for all steps through the first threshold crossing,

    U_i^(m) = s_i+rho^m(U_i-s_i),
    B_i^(m) = B_i,

    U_j^(m) = a_j+rho^m(U_j-a_j),
    B_j^(m) = a_j+rho^m(B_j-a_j),       j!=i.        (12)

Subtracting gives the central exact ledger:

    D_m = rho^m D+(1-rho^m)L_i <= C.                (13)

Individual debts need not decrease. In particular, the owner's debt can rise.
Equation (13), not coordinatewise monotonicity, controls the full expense.

**The threshold is reached in finitely many rows.** For the fixed preemptor,
a_j=s_j-ell_i. Were the threshold not yet reached, (12) would give

    B_j^(m)-s_j <= -ell_i+2M rho^m.

Since rho^m<=exp(-theta m), the right side is negative once
m>=ceil(theta^(-1) log(4M/ell_i)). This contradicts remaining above z>0.
Hence the claimed first-hit time exists and satisfies (8).

At the threshold, if D_m<=h, stop: (7) already holds. Otherwise choose any
exact auxiliary Nash root against

    v=B^(m)-h*1.

The low cap gives v_j<=s_j+z-h<=s_j-3C/8. By (5), this root has

    a >= a_0 := 3C/(16M+3C).

Since h<D_m<=C, (2) yields

    D_final <= D_m-a(D_m-h)
            <= D_m-a_0(D_m-h)
            <= C-a_0(C-h)
             = C-k(C).

The last comparison uses 1-a_0>=0. This proves (7). The initially low-cap
case is the identical auxiliary step with m=0. QED.

### Rational approximate-root version

All solo rows and their stopping test are rational for rational source data.
At the final auxiliary step, choose a rational root satisfying

    max_i g_i <= k(C)/(4n).                          (14)

Since k(C)<C/2 and n>=2, this tolerance is below (3C/8)/4. Equation (6)
gives a>=a_0/2, while the total root-error budget is at most k(C)/4.
Replacing the last calculation above by (3) gives

    D_final <= C-k(C)/4
             = C-3C^2/(128M+24C).                   (15)

If the construction stops before the auxiliary step, the same bound holds.

An accepted rational root exists by finite-game Nash existence and continuity.
More quantitatively, with all Boolean-game payoffs bounded in absolute value
by R, ordinary root regret is 4Rn-Lipschitz in the sup norm of q. An exact
Nash root has a rational grid neighbor with error at most the tolerance in
(14) on a grid of mesh at most that tolerance divided by 4Rn. Testing the
finite grid in rational arithmetic terminates. This is an effective existence
argument, not an efficient solver claim.

## 4. The unblocked singleton alternative

Suppose s_i>=0 and owner i has no strict singleton preemptor, so

    r_j({i}) >= s_j             for all j!=i.        (16)

Let only i quit, with a stationary hazard t>0. Its terminal payoff and cap
are s_i. For an outsider j, put a_j=r_j({i}) and
J_j=(1-t)s_j+t r_j({i,j}). Its prescribed payoff is a_j and its complete cap
is max(a_j,J_j): a pure quit at time k has payoff

    [1-(1-t)^k]a_j+(1-t)^k J_j,

and Never pays a_j. Consequently every player's unrestricted regret is at
most 2Mt. This proves terminal approximate Nash at every accuracy, hence UE.
Other players' singleton rewards may be signed in this infinite-profile
argument.

When all s_j>=0, truncating the solo profile after K rows also yields an
explicit finite selector. Owner regret is at most M(1-t)^K. Outsider caps
are at most a_j+2Mt, while prescribed payoff is
[1-(1-t)^K]a_j and a_j>=s_j>=0. Thus

    E <= 2Mt+M(1-t)^K.                              (17)

This elementary alternative is not claimed as a new equilibrium mechanism.
It establishes that a hypothetical counterexample with nonnegative singletons
has a strict singleton preemptor for every owner. For finite I one can then
use a common positive gap

    ell = min_i max_(j!=i)(s_j-r_j({i})) > 0.        (18)

## 5. A quadratic margin at every positive global minimum

Let D_*=min_(X in K) D(X)>0. The existing minimum singleton-margin theorem
says

    B_i-s_i >= D_*                                 (19)

at every minimizer. The finite first-hit construction makes this strict with
an explicit amount.

### Theorem 2: quadratic collar

At every positive global minimizer, for every i whose singleton satisfies
s_i>=0,

    B_i-s_i >= D_* + D_*^2/(8M),                    (20)

and therefore

    U_i-s_i >= D_*-d_i+D_*^2/(8M)
              >= D_*^2/(8M) > 0.                  (21)

This holds for any finite player set, not just four players. No hypothesis
about a full-debt or reset-rigid source is needed.

### Proof

Fix such an i. Section 4 shows that i must have a strict singleton preemptor;
otherwise D_*=0. Fix a minimizer X and put L_i=B_i-s_i>=D_*.

Take a sequence theta->0 of positive solo-i hazards. Use the first-hit
construction of Section 3 with threshold z=4M theta, omitting its final
auxiliary root. Choose theta small enough that all initial cap margins exceed
z. Every resulting first-hit point Y_theta lies in K and obeys

    D_* <= D(Y_theta) <= L_i.                       (22)

The upper bound is exactly (13). At a crossing coordinate j!=i, the crossing
cap lies between s_j+2M theta and s_j+4M theta by (11) and the stopping rule.
There are finitely many j and K is compact. Passing to a subsequence gives
one j and Y in K with

    B_j(Y)=s_j,     D_*<=D(Y)<=L_i.                 (23)

This is a limit of literal finite prefixes, not an assertion that a new
profile realizes Y's full semantics.

Choose an exact Nash root at B(Y)-(D_*/2)*1. Its j annotation is
s_j-D_*/2, so (5) gives a>=D_*/(4M+D_*). Since D(Y)>=D_*, the ledger and
global minimality imply

    D_* <= D(prefix Y)
         <= [4M/(4M+D_*)]D(Y)
              + [D_* /(4M+D_*)](D_*/2).

Rearranging yields

    D(Y) >= D_*+D_*^2/(8M).

Combine this with (23) to get (20), then subtract d_i to get (21). QED.

### Arbitrary signed Fin4 tables

For four players the repository theorem
`exists_singletonColumnBlockerCertificate_of_fourPlayer_noUniform`
supplies a strict singleton preemptor for every owner from the bare no-UE
hypothesis, without assuming nonnegative singleton rewards. Positive minimum
debt is equivalent to that hypothesis. The proof of Theorem 2 uses s_i>=0
only to obtain the preemptor through Section 4; the first-hit and auxiliary
arguments themselves have no singleton-sign restriction. Consequently, for
**every signed Fin4 table**, every positive global minimizer satisfies
(20)--(21) in all four coordinates. This extension uses the cited existing
four-player counterexample reduction, not a new proof of that reduction.

### Sharper table-dependent joining-loss constant

Define

    Lambda_j = max_(nonempty T subset I\{j})
                    [r_j(T)-r_j(T union {j})]_+,
    Lambda = max_j Lambda_j <= 2M.

If Lambda=0, the all-Quit row is already exact terminal Nash for n>=2.
Otherwise the proof above permits Lambda in place of 2M in (4)--(6), giving

    B_i-s_i >= D_*+D_*^2/(4 Lambda).                (24)

For a fixed owner i, one can further replace Lambda by
max_(j!=i) Lambda_j, since its threshold-crossing coordinate is an outsider.
If that maximum is zero, the hypothetical positive minimum is contradicted
directly by the auxiliary root with absorption one.

### Payoff-only quantitative consequence

Assume all s_i>=0 and put

    rho_pay = max(0, sup_(actual p) min_i(U_i(p)-s_i)).

The continuous minimum-coordinate functional has the same supremum on the
closure of actual payoffs. Equation (21) implies

    D_* <= sqrt(8M rho_pay),                         (25)

with the sharper sqrt(4 Lambda rho_pay) available when Lambda>0.
This is a bound on the infimum of total complete regret, not cap preservation
under a payoff realization. In particular, rho_pay=0 forces D_*=0. For Fin4,
the arbitrary-signed extension above gives (25) without singleton-sign
restrictions as well. The constructive finite algorithm below is stated with
nonnegative singletons so that its unblocked alternative is supplied directly.

## 6. Finite selection under weak coordinate payoff exclusion

Assume all singleton rewards are nonnegative and only the following weak
condition:

    For every actual finite-word profile p,
        min_i(U_i(p)-s_i) <= 0.                     (WE)

There is no uniform negative kappa and no requirement that two or more
coordinates receive positive weight in a separating functional.

### Theorem 3: explicit rational finite selector

For rational tables satisfying (WE), one can construct actual finite laws
with total unrestricted regret at most any prescribed rational epsilon>0.
If every owner is preempted, define

    D_0=sum_i s_i,
    C_0=(128M+24D_0)/3,
    ell as in (18).

For 0<epsilon<D_0, a sufficient date bound is

    N_epsilon <= ceil(C_0/epsilon)
      * (1+ceil([32(M+D_0)/epsilon] log(4M/ell))).    (26)

The laws use these finite dates plus Never. The bound is O(epsilon^(-2))
for a fixed table. It is a date-count bound, not a bit-complexity bound.
If D_0=0, all-Never is exact. If an owner is unblocked, use (17) instead.

### Construction and convergence

Start from all-Never. At each actual finite source, compute U,B,D exactly.
When D>epsilon, choose an i with U_i<=s_i, supplied by (WE). Then

    L_i=B_i-s_i<=d_i<=D.

The rational version of Theorem 1 has C=D and produces the next actual
finite source with

    D_(k+1) <= D_k-3D_k^2/(128M+24D_k)
             <= D_k-D_k^2/C_0.                     (27)

All new rows are prefixed to the entire preceding word. No continuation is
replaced by an unrelated payoff realizer, and the three nonpivot laws are
not selected independently from different source profiles.

Unless debt becomes zero, reciprocal iteration gives

    1/D_(k+1) >= 1/D_k+1/C_0,
    D_k <= C_0 D_0/(C_0+kD_0).                     (28)

Thus ceil(C_0/epsilon) phases suffice. During a nonterminal phase,
epsilon<D_k<=D_0, so (8) is bounded by the second factor of (26).
An exact real-root construction has the sharper decrease in (9) and the
phase constant (32M+6D_0)/3; the rational guarantee is stated separately.

A sufficient rational grid bound for the auxiliary search uses R=M+D_0,
since h=D_k/2<=D_0/2. The finite-source cap calculation consists of the
listed dates, one finite date after the cutoff, and Never. Randomizing a
complete deviation cannot beat the maximum of these pure-time values.

### Canonical Fin4 pivot selection

When s=(1,0,0,0), D_0=1. Take the three nonpivot laws from the constructed
finite profile. Its prescribed pivot law is a feasible competitor for the
full-regret pivot-repair optimization, so that LP's value is at most epsilon.
This is an actual selected three-law family under (WE), not a claim that an
arbitrary own-payoff best response by the pivot preserves every other cap.

### One fixed uniform payoff

For a fixed N-date profile, prescribed finite-average payoff differs from
terminal payoff by at most M(N+1)/H. With nonnegative singleton rewards, all
unilateral deviations have average payoff at most their terminal cap plus
the same error: deviations past the cutoff face only their nonnegative solo
reward on the opponent-Never event. Thus finite-horizon gains are bounded by

    D + 2M(N+1)/H.

A cluster point of the bounded prescribed payoff vectors supplies one fixed
uniform-equilibrium payoff. This is the existing terminal-to-uniform selection
step, not an additional claim of exact equilibrium or every-suffix equilibrium.

## 7. Exact finite regression

The checker specifies a complete canonical four-player table as follows:
initially set r_i(S)=s_i if i belongs to S and r_i(S)=-1 otherwise, with
s=(1,0,0,0). Override exactly

    r({1,2})=(1,1,1,1),
    r({0,1,2})=(2,-1,-1,-1).

Here M=2. The root (0,1,1,0) followed by Never has

    U=(1,1,1,1),    B=(2,1,1,1),    D=1.

Choose owner 0. The construction uses theta=1/96 and z=1/12. Every outsider
cap remains on the Continue branch for exactly 59 solo prefixes before the
first threshold crossing. At that crossing,

    B_j=-1+2(95/96)^59 = approximately 0.07825122041116128,
    D=1 exactly.

The final all-Quit root is exact Nash against B-(1/2)*1 and reduces total
debt to zero. The general finite theorem only promises a decrease of 3/70.

This table already has a pure all-Quit equilibrium. It is solely a regression
for the cap-threshold and complete-debt calculations, not a newly solved
class or evidence that the algorithm always terminates on arbitrary tables.

The script independently evaluates the first-absorption payoff sums and every
pure-time response class for the resulting finite word. These caps equal the
backward-recursion caps exactly. It also checks 300 seeded random rational
finite profiles and auxiliary-prefix ledgers, 30 further signed-table actual
first-hit blocks (the longest has 129 solo rows), and 16 instances of the
quadratic-collar algebra, all using Fraction arithmetic. Neither finite
testing nor the example replaces the proofs above.

Reproduce with:

    python verify_cap_threshold.py

The generated `verification.json` records the exact fractions and checks.

## 8. The remaining obstruction

Theorem 1 is unconditional at an actual source once an owner with a strict
singleton preemptor is selected. Its useful uniform-decrease region is

    min_i(B_i-s_i) <= D.

Outside it, the exact solo block can increase debt towards the selected
L_i. Its bound is C-k(C), with C=max(D,L_i), not D-k(D). The subsequent
auxiliary root is not proved to return to the useful region. Condition (WE)
supplies that return at every actual source; arbitrary canonical Fin4 tables
need not satisfy it.

At a hypothetical positive minimum, Theorem 2 locates the obstruction more
sharply: every cap margin lies at least D_*^2/(8M) beyond the old D_* plateau
boundary, and every prescribed coordinate lies strictly above its singleton.
This does not eliminate the remaining strict-interior region or identify a
general recurrence/rank on it.

## 9. Source correspondence and verification scope

Read-only repository reference:

    elazarg/UniformEquilibrium
    88709a1034da3738fcb35ca10fc2cea45bad808d

Files actually inspected include:

- `AGENTS.md` and `docs/FRONTIER.md`;
- `UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDebt.lean`, especially
  `quittingTerminalSemanticDebt_prefix_le_auxiliaryNash`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`,
  especially `minimumTerminalSemantic_singletonMargin` and the auxiliary moat;
- `UniformEquilibrium/Diagnostics/Quitting/CompleteCapSingletonLimitCollar.lean`;
- `Reverse/Tasks/Q191_SINGLETON_TIGHT_MINIMUM_FACE.md`, including its complete
  answer and reference to the singleton-tight-face implementation;
- the opening portion of
  `Research/Quitting/TerminalSemanticWeightedDebtAxisInsertion.lean`, including
  its cap-Continue identity and cap-gap neighborhood bound;
- `UniformEquilibrium/Quitting/Classification/LCP/FourPlayerSingletonColumnBlockers.lean`;
- `UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`.

The supplied `AUXILIARY_CAP_DESCENT_AND_EXACT_LIMITS(2).md` already gives (2),
its approximate-root extension, (4)--(6), quantitative selectors under strict
payoff deficit or nondegenerate group exclusion, and the relevant uniform
transfer. Those are not being claimed anew.

The existing singleton-tight minimum-face argument already addresses the
exact equality boundary at a global minimizer. Here the source need not be
minimum, debts need not be concentrated on one owner, the solo rows are not
asserted Nash, and the output is a controlled finite prefix on the literal
source. The first-hit budget (13) and the resulting quantitative collar and
weak-exclusion finite algorithm are the additional conclusions derived here.
The source comparison is limited; it establishes no literature-wide priority.

No Lean compiler, axiom audit, full export gate, or independent proof review
was run. All mathematical status in this note is ordinary mathematics.
