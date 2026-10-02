# Future withdrawal and patient-reset quiet extension

## Result and status

This note derives a finite raw-table sufficient condition for ordinary uniform
equilibrium. It enlarges the supplied capped-clock criterion by charging an
outsider's gain to two kinds of legal child deviations: advancing a quit, and
replacing future quitting by sufficiently late quitting or Never.

The main theorem controls complete terminal deviations for every actual child
profile. Three-player existence supplies the child in its four-player
application; no good child profile, favorable continuation, or return is an
input. An explicit canonical single-pivot table passes the new test while every
old proper-child capped-clock test fails. These strict separations persist on a
full sixty-dimensional reward neighborhood. Throughout that neighborhood the
full singleton matrix is R0 of degree +1, and there is no non-discrete
stationary-response-invariant partition.

This is a new mathematical extension relative to the supplied frontier, not a
proof of the general four-player conjecture or a claim of publication priority.
The new results have not been formalized or checked in Lean. The accompanying
standard-library Python verifier checks the exact rational fixture, its finite
certificates, and clock-order regressions; it does not check the general proof.

## 1. Model and finite raw data

Let I be finite and nonempty. Nonempty first quitting coalition A pays r(A) in
R^I; live play and Never pay zero. All strategies and unilateral replacements
are arbitrary independent private laws on N union {infinity}. Infinity means
Never and follows every finite date. The unique live public history is repeated
all-Continue, so this is exactly the behavioral strategy space.

For an actual profile p define U_i(p), B_i(p), d_i(p)=B_i(p)-U_i(p), and
E(p)=max_i d_i(p), with B_i the supremum over every complete unilateral law.
Let s_i=r_i({i}). The finite reward table is bounded; no cap attainment is
assumed.

Choose a nonempty proper child S subset I. Its rewards are the restrictions to
recipients and nonempty coalitions in S. All outsiders will use Never. For each
child i define the finite quantities

    a_i = max(0,s_i),
    c_i = min( {a_i} union
               {r_i(B): empty != B subset S\{i}} ).             (1)

The minimum is always over a nonempty finite set, including when S={i}.
Define a lower bound on the gain from withdrawing from a first coalition:

    ell_i(A) = 0,                              if i not in A;
               r_i(A\{i})-r_i(A),             if i in A, |A|>=2;
               c_i-s_i,                        if A={i}.       (2)

For an outsider k choose nonnegative weights lambda_ki and mu_ki, i in S.
Require

    N_k: s_k <= sum_i lambda_ki s_i + sum_i mu_ki a_i;          (3)

    F_k,A:
      s_k-r_k(A)
        <= sum_i lambda_ki [s_i-r_i(A)]
             + sum_i mu_ki ell_i(A);                          (4)

    J_k,A:
      r_k(A union {k})-r_k(A)
        <= sum_i lambda_ki [r_i(A union {i})-r_i(A)]
             + sum_i mu_ki ell_i(A),                          (5)

for every nonempty A subset S. Weights need not sum to one. In a three-player
child there are six weight variables and fifteen scalar inequalities, in
addition to weight nonnegativity. Compute (1) first: for a fixed table this is
an ordinary finite linear feasibility problem in the weights. No empty
terminal reward is introduced.

Setting every mu to zero recovers exactly the original capped-clock test.
The improvement in (5) is that a child's profitable LEAVING move may pay for
an outsider's JOINING move. The singleton case in (2) retains all possible
hidden later coalitions rather than treating withdrawal as a known zero payoff.

## 2. Main theorem

**Theorem 1 (complete terminal comparison).** Under (3)-(5), every actual
independent child profile p has a quiet parent lift Lp satisfying

    d_k(Lp) <= sum_(i in S) (lambda_ki+mu_ki) d_i(p)   (k outside S),
    d_i(Lp) = d_i(p)                                   (i in S). (6)

In particular, for

    K = max(1, max_(k outside S) sum_i(lambda_ki+mu_ki)),

one has E(Lp)<=K E(p).

The raw inequalities are necessary and sufficient for the universal
TERMINAL POINTWISE LIMIT inequality of the two specified response operations
in Section 3. They are not necessary for UE or for a compiler using other
operations.

**Theorem 2 (fixed targets and raw four-player existence).** Every child
uniform-equilibrium payoff extends to a parent uniform-equilibrium payoff,
with the same child coordinates. In particular, if |I|=4 and some nonempty
proper child passes (3)-(5) for every outsider, the original table has one
fixed ordinary uniform-equilibrium payoff. No strategic object is required
as an extra hypothesis: games with at most three players supply the child.

The parent target precedes epsilon. For every epsilon>0 there are one actual
independent behavioral profile and one horizon threshold controlling every
larger horizon and every complete unilateral deviation. Outsiders use Never.

**Theorem 3 (Never-row relaxation).** If only (4)-(5) hold, put

    b_k = max(s_k - sum_i lambda_ki s_i - sum_i mu_ki a_i, 0),
    p_infinity = Pr(all child clocks are Never).

Then

    d_k(Lp) <= sum_i(lambda_ki+mu_ki)d_i(p) + b_k p_infinity.   (7)

If some j in S has s_j>0, the last term is at most (b_k/s_j)d_j(p).
Thus the fixed-target conclusion also holds without (3) when a child own
singleton is positive. This relaxation is terminal, not an evaluation-by-
evaluation finite-horizon assertion.

## 3. Legal responses and the pointwise proof

Fix an outsider k and suppress its index on the weights. Let Z be its proposed
clock, independent of the child tuple T. For each child i consider separate
unilateral experiments; a common Z is only a proof coupling, not a public
random signal.

### 3.1 Advancing a quit

Use

    A_i(T_i,Z)=min(T_i,Z).                                 (8)

This is the original capped-clock response. Its law is independent of all
unchanged opponents.

### 3.2 Patient replacement of future quitting

For an integer L>=1 define P_i^L(T_i,Z) as follows:

    if Z=infinity or T_i<Z: keep T_i;
    otherwise, if s_i>=0: use the finite date Z+L;
    otherwise: use Never.                                 (9)

This is a legal private response for every finite L. It depends only on the
player's sampled old clock, a separately sampled Z, and the known table.
It never queries another player's unrevealed clock. It is not necessarily a
pure delay of the old clock: it may replace an old Never by a late finite
quit. That feature is needed for the a_i term in (3).

At s_i>=0, the sequence of laws in (9) can converge weakly to Never while its
terminal payoff on all-Never opponents remains s_i. We use limits of the
actual payoff inequalities, not the payoff of that limiting law. In
particular Never is never assigned reward s_i.

Let tau be the original child first date and A its coalition when finite.
For a fixed finite outsider deadline t, there are four relevant cases.

**Child absorption before t.** If tau<t, the first coalition is unchanged in
all experiments, including (9). Every gain is zero.

**A join at t.** If tau=t<infinity, the outsider gain is
r_k(A union {k})-r_k(A). Advancing child i gives
r_i(A union {i})-r_i(A). A future replacement of a child outside A changes
nothing. If i belongs to A and |A|>=2, it leaves A\{i} at the same date,
so its gain is the exact second line of (2). If A={i}, let B be the first
later opponent coalition. For every fixed tuple, as L tends to infinity,
its new payoff tends to r_i(B) when that coalition is finite, and to a_i
when every opponent chooses Never. The limiting gain is at least c_i-s_i.
Consequently (5) proves the desired gain comparison.

**An outsider preempts later child absorption.** If t<tau<infinity, its gain
is s_k-r_k(A). Advancing child i gives s_i-r_i(A). Under (9), a child
outside A eventually leaves the original first coalition unchanged: its
new finite date, if any, eventually exceeds tau. A member of a nonsingleton
A leaves A\{i}. The singleton member has the same later-coalition/a_i
alternative just described. Thus (4) proves the comparison.

**Joint Never.** If tau=infinity and t<infinity, the outsider gets s_k;
advancing child i gives s_i; (9) gives a_i. This is exactly (3).

If t=infinity every operation leaves the original outcome unchanged.

Writing G_k for the outsider gain, G_i^A for the advancing gain, and G_i^{P,L}
for the patient-reset gain, these cases prove, for every deterministic tuple,

    G_k <= sum_i lambda_i G_i^A + sum_i mu_i lim_(L->infinity) G_i^{P,L}.
                                                                    (10)

The limits exist pointwise by the finite/never case split. All gains are
bounded in absolute value by twice a reward bound.

### 3.3 Integration and unrestricted caps

Integrate (10) over independent (T,Z). Bounded convergence applies separately
to each of the finitely many patient-reset terms. For every finite L,

    E[G_i^{P,L}]<=d_i(p),           E[G_i^A]<=d_i(p),

because each is an actual unilateral replacement against the original child
opponents. Hence the same upper bound holds for the limiting expected gain.
Nonnegative weights give the outsider bound in (6), uniformly over its
complete proposed law. Taking that outsider supremum is now legitimate.
No expectation/supremum interchange or cap attainment has been used.

Child payoffs and caps are unchanged by deterministic outsider Never, on
path and under every child deviation. This proves the other part of (6).

### 3.4 Necessity for this particular pointwise compiler

Joint Never and a finite t recover (3). To recover a future row (4), put
exactly A at date 1 and take t=0. For |A|>=2 the withdrawal values are exact.
For A={i}, select the hidden later opponent outcome attaining (1), using a
coalition at date 2 if its reward attains the minimum, and all opponents Never
if a_i attains it. To recover (5), put A at date zero and take t=0, with the
same later-coalition choice for a singleton. These deterministic laws recover
every necessary row. This proves the stated pointwise characterization.

## 4. Never correction, strategy production, and fixed uniform targets

If (3) is omitted, (10) acquires only the extra error b_k on joint Never
when Z is finite. Its expectation is at most b_k p_infinity, proving (7).
For any child j, cap its old clock at a deterministic date L. On every tuple
with an original finite first outcome, its gain eventually vanishes. On
joint Never its gain is s_j. Bounded convergence and the complete cap give

    s_j p_infinity <= d_j(p).                             (11)

For s_j>0 this gives Theorem 3.

For fixed targets, start with child uniform approximants delivering one
specified v_S. Fixed-profile bounded convergence of Cesaro payoffs to terminal
payoffs, applied also to each fixed complete deviation, makes them terminal
approximate equilibria with target v_S. This step does not interchange a
limit and a response supremum. Quiet lifting and (6) make their parent
terminal regrets tend to zero. Select a convergent subsequence of the bounded
outside terminal payoff vectors. The resulting full vector v is fixed,
restricts to v_S, and is approached by actual terminal approximate equilibria.
The existing fixed-target terminal-to-uniform theorem yields parent UE at v.

For the target-free four-player conclusion one may instead take child
terminal errors tending to zero, apply (6), and use the existing terminal
all-errors equivalence. The child theorem is unconditional for arbitrary
signed three-player quitting tables. It is a dependency, not a conclusion
of this note.

For rational rewards, (1) is rational and the weight system is an exact
rational LP. Whenever it is feasible it has rational feasible weights.
Given a positive rational requested terminal error epsilon, enumerate
rational independent child laws on consecutive calendars
{0,...,N-1,Never}. Scan all pure replies 0,...,N and Never. This finite scan
is the COMPLETE terminal cap: every finite date after N-1 is outcome-equivalent
to N, while Never remains separate. Accept a child law with E<epsilon/K
and quietly lift it. Child existence, complete finite-law approximation,
and rational density on a fixed calendar prove termination. No calendar,
bit-complexity, or practical runtime bound is asserted.

## 5. A stronger evaluation statement for plain cancellation

There is an alternative without a patient limit. Replace (1) by

    c_i^cancel = min( {0} union {r_i(B): empty != B subset S\{i}} ),

use its corresponding ell_i in (4)-(5), and replace (3) by the OLD Never row
s_k<=sum_i lambda_i s_i. The second response is now exactly

    C_i(T_i,Z)=T_i if T_i<Z, and Never otherwise.           (12)

Under these variant hypotheses, for every nonincreasing
f:N union {infinity}->[0,1] with f(infinity)=0, one has

    d_k^f(Lp)<=sum_i(lambda_i+mu_i)d_i^f(p).                (13)

Terminal, finite-horizon Cesaro, and normalized discounted evaluations are
included. To check the signed singleton case, a later reward with weight
f(t')<=f(tau) is at least f(tau)c_i^cancel: negative later rewards become
less negative when discounted, and positive ones are at least zero.
For t<tau, let n=s_k-sum lambda_i s_i and let f_A be the left-minus-right
residual in the future row. The evaluated residual is at most

    [f(t)-f(tau)] n + f(tau) f_A <=0.

The other cases are immediate nonnegative multiples of the relevant rows.
Integration proves (13). This is a separate sufficient variant: the stronger
patient-reset terminal test must not silently be used evaluation by evaluation.
The explicit center table below passes both variants. Its whole neighborhood
is admitted by the patient-reset terminal theorem.

## 6. Exact canonical separation table

Coalition strings denote sets. Use this ORIGINAL table with zero Never payoff:

| A | r_0 | r_1 | r_2 | r_3 |
|---|---:|---:|---:|---:|
| 0 | 1 | 3 | -1 | -1 |
| 1 | 4 | 0 | -1 | -1 |
| 01 | 2 | 4 | -1 | -3 |
| 2 | 0 | -1 | 0 | 3 |
| 02 | 2 | -1 | -2 | -4 |
| 12 | 0 | -2 | 1 | 5 |
| 012 | -3 | 0 | 0 | 0 |
| 3 | 0 | -1 | 3 | 0 |
| 03 | 2 | -1 | -1 | -6 |
| 13 | 0 | 1 | -1 | 3 |
| 013 | 1 | 0 | 1 | -4 |
| 23 | 0 | -1 | 1 | 1 |
| 023 | 1 | -1 | 0 | -6 |
| 123 | 0 | 0 | 0 | 3 |
| 0123 | 1 | 0 | -1 | 1/2 |

Call it r*. Its own singleton vector is exactly (1,0,0,0), and every reward
has magnitude at most six. Choose S={0,1,2}, outsider 3, and

    lambda=(0,0,3),                 mu=(1/2,0,0).          (14)

Here a=(1,0,0), c=(0,-1,-1), and the patient Never-row slack is 1/2.
In coalition order 0,1,01,2,02,12,012 the future and join slacks are

    F: (3/2,2,1,3,1,2,3/2),
    J: (3/2,2,5,2,1,2,1).                               (15)

Thus EVERY actual child profile has the complete bound

    d_3(Lp)<= (1/2)d_0(p)+3d_2(p),
    E(Lp)<= (7/2) E(p).                                 (16)

The main new comparison is visible at A={0,1,2}. The outsider gains 1/2
by joining. Every old capped-clock child join has gain zero, because every
child already belongs to A. But player 0 can withdraw, changing its reward
from -3 to r_0({1,2})=0. Half its gain pays 3/2, more than the outside gain.
The remaining rows in (15) make this local observation a UNIVERSAL compiler,
including singleton withdrawals and hidden later clocks.

### 6.1 Every old proper-child test fails

For an old test on child T and outsider k, its join row at A subset T is

    r_k(A union {k})-r_k(A)
      <= sum_(i in T) lambda_i [r_i(A union {i})-r_i(A)], lambda>=0.

The following table gives a single infeasible row for every nonempty proper T.
Coefficients are ordered by increasing child labels.

| T | k | A | old child coefficients | outside gain |
|---|---:|---|---|---:|
| 0 | 1 | 0 | (0) | 1 |
| 1 | 2 | 1 | (0) | 2 |
| 01 | 2 | 01 | (0,0) | 1 |
| 2 | 0 | 2 | (0) | 2 |
| 02 | 1 | 02 | (0,0) | 1 |
| 12 | 0 | 2 | (-1,0) | 2 |
| 012 | 3 | 012 | (0,0,0) | 1/2 |
| 3 | 0 | 3 | (0) | 2 |
| 03 | 1 | 03 | (0,0) | 1 |
| 13 | 0 | 13 | (0,0) | 1 |
| 013 | 2 | 01 | (0,0,-1) | 1 |
| 23 | 0 | 23 | (0,0) | 1 |
| 023 | 1 | 023 | (0,0,0) | 1 |
| 123 | 0 | 123 | (0,0,0) | 1 |

Every right side is nonpositive, while every left side is positive. These
are exact one-row dual certificates, not LP solver failure reports. They
also defeat the old version with the Never row omitted. The zeros are
structural membership zeros, so they remain zero under reward perturbation.

### 6.2 Full and quotient degree tests do not admit this table

Its singleton matrix is

    Gamma = [ 0  3 -1 -1
              3  0 -1 -1
             -1 -1  0  3
             -1 -1  3  0 ],

    det Gamma=45,
    Gamma^{-1}=(1/15)[2 7 3 3; 7 2 3 3; 3 3 2 7; 3 3 7 2]. (17)

The inverse is strictly positive. For a homogeneous complementary solution,
nonzero nonnegative slack would give an everywhere positive primal vector,
forcing slack zero; zero slack forces primal zero. Hence Gamma is R0.
At right-hand side -1 the unique LCP solution is Gamma^{-1}1=1, with
zero slack and index sign(det Gamma)=+1. Thus its LCP degree is +1.

For the stationary residual Delta_i=(1-alpha_i)Q_i-H_i, at q=(1,1,1,1),

    Delta(q)=(1,1,-2,1/2).                              (18)

Any invariant block containing two indices with different displayed values
fails the raw residual identity. The only possible non-discrete partition
left is {0,1}|{2}|{3}. At q=(0,0,1,0), which is constant on these blocks,

    Delta_0(q)=2,             Delta_1(q)=-1.              (19)

That partition also fails. Thus only the discrete partition is response
invariant, and its degree is +1. These statements do not identify an outsider
with another strategic player or average their coins.

### 6.3 Other bounded comparisons and an honest positive check

Every reciprocal off-diagonal pair in (17) has the same strict sign. The
necessary escort condition Gamma_ij<=0<=Gamma_ji is therefore impossible,
so no balanced singleton cycle of the class in the supplied notes exists,
on the parent or any child. Each principal triple also has a row whose two
off-diagonal entries are negative; it cannot have an entrywise nonnegative
inverse, since that row times a nonnegative inverse could not produce its
positive identity diagonal entry.

Uniform stationary hazards tending to zero have terminal payoff tending
to the average singleton vector, equal here to s+(1/4)1. Therefore some
actual profile has every payoff strictly above its singleton. This rejects
all the listed payoff-exclusion conditions. The sure pair 01 has both
active Quit payoffs above their own singletons, rejecting product-low.

No deterministic behavioral profile is terminal Nash. Each nonempty first
coalition has a membership toggle, retaining a nonempty coalition, with
payoff gain at least one; the exact checker verifies all fifteen. The
all-Never profile admits the pivot's gain one. These same toggles work at
any deterministic first date and do not depend on hidden later clocks.

The center nevertheless has an EASY exact mixed equilibrium: use date-zero
Quit probabilities

    q=(1/2,2/5,1,0),

and Never afterwards. Direct full reply scans give

    U=B=(0,-1,-2/5,7/10).                                (20)

Player 2's sure quit screens every other player's late replies. For player 2,
Quit0 pays -2/5, every strictly positive finite deadline pays -7/10, and Never
also pays -7/10. Thus (20) does not discard the sure owner's counterfactual
tail. It is also a uniform-payoff profile by the finite-law comparison.
The fixture is not claimed to evade the general stationary verifier or every
other known sufficient criterion. Its role is strict, robust separation of
the explicit raw classes, not evidence of global exploitability.

## 7. A full sixty-dimensional solved neighborhood

**Theorem 4.** Every table r with

    ||r-r*||_infinity < 1/100                            (21)

has an ordinary uniform-equilibrium payoff and satisfies, for every actual
child p on {0,1,2}, the SAME terminal comparison (16). Every old proper-child
capped-clock test fails there. Its full singleton matrix is R0 of degree +1,
and no non-discrete partition satisfies the stationary residual identity.

All sixty terminal coordinates may vary independently; Never remains zero.

**New certificate.** The maps s_i, a_i and c_i change by at most delta under
entrywise reward distance delta: max and a finite minimum are 1-Lipschitz in
the sup norm of their entries. Each ell_i changes by at most 2delta. With
(14), the Never-row slack changes by at most (1+3+1/2)delta=(9/2)delta;
a future or join slack changes by at most 2(1+3+1/2)delta=9delta.
The center margins 1/2 and 1 in (15) therefore remain strictly positive
under (21). Theorem 1 supplies (16), and three-player existence supplies UE.

**Old tests.** In Section 6.1 structural zeros remain zero, the only negative
coefficients are -1 and remain negative, and outside gains start at least
1/2 and change by at most 2delta. Every listed obstruction persists.

**Full degree.** Let B=Gamma^{-1}. Its induced infinity norm is one and its
smallest entry is 2/15. For the perturbed singleton matrix,
||Gamma'-Gamma||_infinity<=6delta. The inverse series gives

    ||(Gamma')^{-1}-B||_infinity <= 6delta/(1-6delta)
                                  < 3/47 < 2/15.

Thus its inverse remains strictly positive. The segment from Gamma to Gamma'
is invertible by the same norm bound, so its determinant remains positive.
The R0 and unique-LCP-solution argument from Section 6.2 gives degree +1.

**Partitions.** At a fixed product q, Q_i changes by at most delta, H_i by
at most (1-alpha_i)delta, so Delta_i changes by at most 2delta. A difference
between two residuals changes by at most 4delta. At (18), all unequal values
are separated by at least 1/2; the exceptional pair has gap three at (19).
These exact witnesses therefore exclude every non-discrete partition throughout
(21).

The same reciprocal signs exclude balanced singleton cycles and the triple
inverse test throughout this neighborhood. The strict pure-deviation gains,
the absorbing pair violating product-low, and the attainable positive
singleton surpluses persist as well. For the latter use the perturbed
singleton average, whose surplus is at least 1/4-2delta, then a sufficiently
small positive common stationary hazard.

Common positive scaling by 1/7 places the center and this neighborhood
strictly inside the unit reward cube. The center's own singleton vector then
is (1/7,0,0,0); it need not remain numerically unit-pivot after scaling.
Every actual gain and the raw inequalities scale correctly, including a_i
and c_i. No terminal-only translation is used as a strategic equivalence.

## 8. What this changes and what it does not

The enlarged test is finite, executable on rational data, and has an actual
all-behavior consumer. It enlarges the UNION over all old proper-child tests,
not merely one chosen child's feasible weight set. The open separation lies
inside the degree-one/no-useful-response-quotient region and in canonical
single-pivot coordinates at its center.

Every hypothetical four-player counterexample must fail this enlarged test
for every proper child. An infeasible enlarged LP, however, is not a
counterexample certificate: it excludes only this particular quiet-extension
mechanism. The supplied adaptive unchanged-child no-go example still prevents
any claim that a universal unchanged-child compiler follows from this extension.

This theorem does not consume the arbitrary positive-gap minimum, the
single-pivot strict-pressure source, all bounded-capacity blocks, or every
full robust polynomial. It supplies no cardinal reduction to four players
and no normal form for general stochastic games. The main universal
four-player existence obligation remains unproved here.

## 9. Existing source interfaces and new formalization boundary

The existing starting criterion and the independent min-clock coupling are
in the supplied CAPPED_CLOCK_DEVIATION_DOMINATION_AND_QUIET_EXTENSION.md.
The new ingredients are (1)-(5), the future patient-reset operations, their
pointwise limiting comparison, and the strict separation family. The
plain-cancellation variant is separately proved in Section 5.

The following existing declarations provide the semantic interfaces:

- `quittingBehaviorStoppingLaws_update`,
  `quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws`, and
  `quittingBehaviorDeviationPayoffCap_eq_pureTime`
  (`UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`).
- `quittingGame_exists_uniformEquilibriumPayoff_threePlayer`
  (`UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`).
  Its exact statement and direct imports were read through GitHub at commit
  `5aac30ad2553dadd5895dc79fbc4f1f5680d7570`. No compilation or transitive
  axiom audit was run in this session.
- `prod_stoppingLaw_none_mul_singleton_le_terminalDebt`
  (`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`).
- `exists_finiteDeadlineTimingProfile_approximation`
  (`UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`).
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` and
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).

The source correspondence for the other declarations is retained from the
supplied notes; their complete dependency closures were not reaudited here.
The raw matrix and partition comparisons use the degree convention in the
supplied STATIONARY_RESPONSE_QUOTIENT_DEGREE_ESCAPE.md, with its existing
classical R0 degree account. They are not additional premises of Theorem 1.

A narrow Lean implementation should prove the private-law pushforwards and
the bounded-convergence limit first, then the raw row comparison, complete
regret estimate, and child consumer. The limit is of actual response PAYOFFS,
not a fictitious stopping action after Never. The comparison must remain
against the original child opponents; no modified nonmover cap is assumed.

## 10. Reproduction

Run

    python VERIFY_PATIENT_RESET_QUIET_EXTENSION.py

The script has no third-party dependencies and uses exact fractions. It checks:
all fifteen new row margins; a one-row rejection certificate for each of
fourteen old proper-child tests; 625 terminal patient-reset clock-order cases;
3,125 plain-cancellation/monotone-weight cases; the complete finite-law caps
in (20); and the singleton and partition witness arithmetic.

With three child clocks and one proposed outside deadline, at most four
distinct finite dates occur. Rank relabeling preserves the terminal first
coalition, the comparisons in the clock operations, and the limiting
patient-reset outcomes. Thus the enumerated order types cover every
deterministic comparison pattern for this fixture. For the plain-cancellation
variant, monotone values on four ordered dates are nonnegative combinations
of the enumerated prefix-indicator weights. The general proof is nevertheless
the explicit case analysis above, not an inference from random testing.

No Lean source was added, compiled, committed, or pushed in this session.
