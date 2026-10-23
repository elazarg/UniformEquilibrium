# A dual barrier for singleton grafts retaining the old cap menu

Identity: CODEX_COORDINATOR.

Status: complete internal ordinary-mathematical argument; independent review
requested. This is a restriction on a descent mechanism, not a new excluded
counterexample class, an exhibited positive-gap game, or a solution of Fin4.
Section 3 proves the box support-function identity and separation argument.
Nonnegative-direction optimality produces one dual vector
which controls EVERY finite or infinite singleton-only graft with an empty
boundary query, including signed singleton drift, inactive ENDs and subsequent
changes in cap activity.
No separate export is proposed without a substantive coverage assessment.

## 1. Question and original source

Can a sufficiently long, nonperiodic or switching singleton-only tail, with
the old full cap menu retained by an empty boundary query, escape an original
minimum after every small nonnegative diffuse graft fails?
The answer is no. The small-direction conditions already have a global
dual certificate against this entire class. An escape must use joint first-
quitting coalitions, change the old prefix, or change its offered cap menu.

Fix a finite player set I (the application has four players), a finite
native reward table Z with Z_i({i})=0, and zero live and AllNever payoffs.
Complete private clocks are independent. Their only observations before
absorption are continued play. Let U_i, B_i, e_i and N_i denote prescribed
payoff, the full unilateral behavioral cap, the pure Never response value,
and ORIGINAL Never probability. Every finite deadline and literal Never
belongs to the cap menu. Consequently B_i>=U_i and B_i>=e_i.

The original compact carrier is the closure of these actual coordinates,
retaining N and e rather than relabeling escaping finite mass as Never.
Fix positive theta_i and lambda, and the objective

    F(Y)=SUM_i theta_i(B_i-U_i)+lambda nu,
    nu=PRODUCT_i N_i.

For the original raised game r_i(C)=theta_i[Z_i(C)+t], this is its exact
full SUM debt with lambda=t SUM_i theta_i. The finite-response cap shift
and the original Never term are both retained. Assume N_i>0 for every i.
Define

    H_i=nu/N_i,
    kappa_i=(B_i-e_i)/H_i >=0,
    E={i:kappa_i=0},
    Gamma_ij=Z_i({j}), Gamma_ii=0,
    alpha_i=theta_i/N_i if i in E, and alpha_i=0 otherwise.

The sole variational premise for the theorem is

    SUM_i alpha_i (Gamma x)_i^+ - theta dot Gamma x
        >=lambda SUM_j x_j,             for every x>=0.       (1)

Every unrestricted global minimum with positive original Never masses
satisfies (1), by the complete diffuse-graft argument in Part II of
`../exports/FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md`.
For clarity, its full-graft formula and first variation are restated below.
One need not assume global minimality in the theorem: (1) alone suffices.

## 2. Exact graft semantics

Let Q be any actual independent tail. Insert an empty finite test before
its occupied dates. This changes no prescribed payoff or Never mass and
ensures its full native cap b_i satisfies

    b_i>=0, b_i>=u_i,                                 (2)

where u_i is its prescribed native payoff. Appending Q to each owner's
original Never branch independently gives

    U_i'=U_i+nu u_i,
    B_i'=max(B_i,e_i+H_i b_i),
    N_i'=N_i N_i^Q.

All old responses remain available. New responses have old Never value plus
the deleted-opponent factor H_i times the corresponding Q response. The
empty boundary response is also included. Thus this maximum prices the
ENTIRE cap, not a chosen finite inventory. It gives

    [F(Y graft Q)-F(Y)]/nu
      =SUM_i (theta_i/N_i)(b_i-kappa_i)^+
           -theta dot u-lambda(1-nu_Q).               (3)

The boundary query is part of the operation. Without it, an immediate first
tail atom can remove the old late response: a response at that same date
joins the atom, and later responses come after it. The old cap need not
remain available if it had no earlier attainer. Such an attachment can have
a negative conditional tail cap and does not satisfy (2) or necessarily (3).
It must be analyzed directly; the theorem does not exclude it. If an earlier
old finite response already attains the old cap, retaining that response may
instead justify the same maximum formula with the positive part of the tail
cap, without inserting an extra empty date.

For an infinite old calendar, censor an increasingly late finite tail to
original Never, add an empty boundary, and graft. Coupling bounds every
prescribed payoff and every response error by twice the reward bound times
the censored mass. The same bound controls the supremum. Diagonal actual
realizers give (3) at any point of the original augmented carrier and for
any tail which is a limit of actual tails. This is a closure operation,
not an assertion that an abstract limiting calendar is executable.

For a small diffuse word with total finite masses rho x_i, complete-query
limits give u=rho Gamma x+O(rho^2), b_i=rho(Gamma x)_i^++O(rho^2),
and 1-nu_Q=rho SUM x+O(rho^2). A fixed inactive kappa_i>0 clips its
cap increment to zero for all sufficiently small rho. Dividing (3) by
rho at a global minimum produces (1). No finite response attainer or
uniform inactive margin across minima is assumed.

## 3. One dual vector for all directions

Let

    K=PRODUCT_i[-theta_i,alpha_i-theta_i].

This is a nonempty compact box, including a singleton coordinate
z_i=-theta_i whenever i is END-inactive. For any vector y,

    max_(z in K) z dot y=SUM_i alpha_i y_i^+-theta dot y.

**Dual lemma.** Condition (1) is equivalent to the existence of one z in K
such that

    Gamma^T z>=lambda 1, entrywise.                   (4)

The reverse implication follows immediately by evaluating the support
function at that z. For the forward implication, suppose the compact convex
set Gamma^T K-lambda 1 does not meet the closed positive orthant. Strong
separation gives a nonzero x with

    sup_(z in K) x dot (Gamma^T z-lambda 1)
       <inf_(w>=0) x dot w.

The right side is finite only if x>=0, and then it is zero. This contradicts
(1). The strict separator exists because a compact set and a disjoint
closed set have positive distance. This proves the lemma without selecting
a different dual vector for each direction.

If Gamma v=e_h with v>=0 nonzero, (4) gives z_h>=lambda SUM v>0.
Hence h is END-active, and the box upper bound gives

    theta_h(1/N_h-1)>=lambda SUM v.

This recovers the forced-owner and finite-mass bound from the earlier
inverse-column argument. It is not additional source coverage by itself.

## 4. Global coalition bound and complete singleton-tail exclusion

Fix the SAME z supplied by (4). Put c_i=theta_i+z_i. Then
0<=c_i<=alpha_i. Equation (2) implies

    alpha_i b_i-c_i u_i>=0.                           (5)

Indeed c_i u_i<=c_i b_i<=alpha_i b_i. For i in E, the cap term
in (3) is exactly alpha_i b_i; outside E it is nonnegative whereas
alpha_i=0. Consequently (3) and (5) give the global estimate

    [F(Y graft Q)-F(Y)]/nu
       >= z dot u-lambda(1-nu_Q).                     (6)

Let p_C be the probability that Q's FIRST finite quitting coalition is C.
All probabilities are under its prescribed independent laws. Then

    u=SUM_(C nonempty) p_C Z(C),
    SUM_C p_C=1-nu_Q.

Therefore

    F(Y graft Q)-F(Y)
      >=nu SUM_C p_C [z dot Z(C)-lambda].             (7)

Every singleton margin is nonnegative by (4). In particular, if the first
finite coalition is a singleton almost surely on absorption, the original
full SUM cannot decrease. This includes arbitrary finite or countable
singleton calendars, any actual tail with no simultaneous first quitting,
and every diffuse or switching limit with vanishing first-collision mass.
There is no sign restriction on Gamma x along that tail; END may lose and
regain activity. Neither a period bound nor a fixed phase word is imposed.

For the closure claim, append the finite vector (p_C)_C to the realizing
sequence and pass to a convergent subsequence. Its linear payoff identity
and total-mass identity pass to the limit, as do (3), (6) and (7). Thus no
arbitrary retained-clock execution or convergence of a chosen query is used.

More quantitatively let

    K_multi=max(0,max_(|C|>=2) [lambda-z dot Z(C)]),
    p_multi=SUM_(|C|>=2) p_C.

Then

    F(Y graft Q)-F(Y)>=-nu K_multi p_multi.            (8)

Any strict improvement must give positive first-absorption probability to
at least one multiowner coalition satisfying z dot Z(C)<lambda. If the
decrease is at least eta>0, K_multi>0 and

    p_multi>=eta/(nu K_multi).

If every multiowner margin is nonnegative, (7) blocks ALL appended tails,
including colliding ones. This is a sufficient tail certificate, not a
claim that the source is a global minimum under arbitrary prefix changes.

## 5. Exact original-law boundary control

The following fixture distinguishes all singleton tails from joint tails
at a point satisfying every local diffuse test. It is NOT a positive-A
source: an absorbing equilibrium is explicitly given.

Take

    Gamma=[[0,-9,-6,7],[-6,0,4,7],[7,8,0,-1],[-1,-3,9,0]].

Its determinant is7345. Specify all60 native rewards by the disjoint rules:
Z_i(C)=0 if i in C; if i is absent, use Gamma_ij for C={j}, use3 for
|C|=2, and use0 for |C|=3. Each player puts probability1/2 at date1
and probability1/2 at Never, with date0 empty. All native full caps are
END-active:

    e=B=(1,14,23,14)/8, U=e/2, N_i=1/2, nu=1/16.

The only response prices are early0, occupied-date0, and late/Never e_i.
Use theta_i=1 and lambda=1, so the actual raise is t=1/4. The exact vector

    z=(536,775,1832,829)/7345

satisfies Gamma^T z=1 and lies in[-1,1]^4. Even2z lies strictly within
the box and has Gamma^T(2z)=2, so every nonzero local diffuse direction
has a strict margin against lambda=1. The theorem blocks EVERY singleton-
only appended tail retaining the empty boundary, not just the finitely many
checker fixtures.

Nevertheless let Q put all four owners at one sure common date. All its
prescribed, finite-response and Never payoffs are zero: unilateral absence
leaves a passive triple paying0, and participation pays0. Thus u=b=0,
nu_Q=0. Formula (3) gives the strict decrease -1/16. With z above, the
grand-coalition margin is exactly -1, and (7) is equality for this Q.
Native A=0 because Q itself is an absorbing exact terminal Nash profile.
The raised game also has this absorbing equilibrium. The old point is
therefore correctly identified as locally resistant to all diffuse grafts
but not a global minimum. It is not portrayed as a Fin4 counterexample.

The standalone exact checker is
`../experiments/CODEX_COORDINATOR__SINGLETON_GRAFT_DUAL_BARRIER_CHECK.py`.
It checks the complete60-coordinate table, all pure responses, the inverse
and dual data,24 disjoint singleton calendars with signed intermediate
passive drift, and the joint-tail escape. Universal scope comes from the
proof above, not this finite enumeration.

## 6. Source audit, overlap and next research step

Inspected exact definitions and declarations:

- `quittingTerminalSemanticPair`, `quittingTerminalSemanticDebt` and
  `quittingTerminalSemanticCarrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `quittingTerminalDebtSumInf`,
  `quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum` and
  `quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
  in `UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean`.

This was static source inspection. No Lean command or new formalized theorem
is claimed. The native/raised identities and actual-source graft construction
are the existing source reduction cited in Section1. The support-function
identity has prior use in END_CAP_DROP_EARLIER_MAXIMIZER_NECESSITY; its signed
withdrawals change the old prefix and are not blocked by this theorem.
COLLISION_FREE_NATIVE_TAIL_ABSORPTION_MINIMUM_REDUCTION instead constructs
absorbing approximations from a zero-debt native source. That is a different
operation and hypothesis, not a singleton graft at a fixed positive minimum.

This theorem does not shrink the mathematical counterexample class beyond
the established minimum inequalities. It converts them into a global
limitation of one proposed proof mechanism. The concrete next question is
whether coalitions with a negative dual margin can be assembled into an
actual beneficial joint tail with all response caps priced, or whether a
change of prefix laws or an immediate attachment with signed conditional
caps can cross this barrier. A proof must reprice any old queries lost by
such an attachment rather than carrying their old cap across unchanged.
