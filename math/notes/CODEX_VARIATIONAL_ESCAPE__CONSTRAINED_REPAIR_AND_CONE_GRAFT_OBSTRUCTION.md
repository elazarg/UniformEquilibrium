# Joint observer repair cannot delete the distinguished clock at the constrained source

Identity: CODEX_VARIATIONAL_ESCAPE.

Status: proved ordinary mathematics, internal. This note gives two complete
obstructions for the actual positive absorbing-debt source: deleting the
distinguished owner after jointly repairing all three other debts cannot
match the constrained global optimum; and controlled diffuse tails that
retain the old cap menu and have nonnegative singleton drift cannot lower
the original SUM.
Neither statement is a UE counterexample or a closure theorem. No positive
absorbing-debt game is exhibited. The complete all-END source packet remains
unchanged.

## 1. Exact source and the constrained problem

Let Z be a bounded four-player quitting table with Z_i({i})=0. All live and
literal Never rewards are zero. Private complete stopping laws are independent;
every unilateral replacement, including Never, is allowed. Let

    M=max(1,max |Z_i(C)|),
    H=closure{(U(P),B(P),N(P),e(P)): P actual},
    d_i=B_i-U_i, nu=product_i N_i,
    A=inf{sum_i d_i(P): P actual, nu(P)=0}.

Here B is the full response supremum, N is the ORIGINAL Never vector and e
is the native pure-Never response. The compact carrier H retains all these
coordinates. This is not the space of actual laws with an exact constraint
imposed before taking a closure.

Assume A>0 and Gamma invertible, with

    Gamma_ii=0, Gamma_ij=Z_i({j}),
    v=Gamma^(-1)e_h>0, S=sum_i v_i, k=S-v_h>0.             (1)

The strict-column source theorem supplies (1) from A>0 in Fin4. Nothing
below changes Z. Define the compact feasible sets

    C={Y in H: d_i(Y)=0 for every i!=h},
    C_N={Y in C: N_h(Y)=1},
    J_r(Y)=d_h(Y)+r nu(Y),
    m(r)=min_C J_r, m_N(r)=min_(C_N) J_r.                  (2)

Both sets are nonempty because they contain actual AllNever. For r>0,

    0<=m(r)<=m_N(r)<=r.                                   (3)

Two identities from actual laws pass continuously to H:

    d_i>=N_i(B_i-e_i),
    A<=sum_i d_i+14M nu^(1/4).                            (4)

The first follows by decomposing the owner's prescribed law into its Never
mass and its finite conditional law, whose payoff is at most B_i. The second
redirects the smallest original Never mass to a finite date: the own debt
changes by at most 2M N_i and each other debt by at most 4M N_i. Therefore
every point of C with J_r<=r and 0<r<A has

    nu>=c_r=((A-r)/(14M))^4>0.                            (5)

In particular all ORIGINAL marginal Never masses are positive. At such a
point the three zero-debt observers automatically have B_i=e_i by (4).

### The compact problem retains the original obstruction

For every r>0, m(r)>0 if and only if A>0. One direction follows from (4): a
zero minimum would have every debt zero and nu=0. Conversely A=0 gives a
sequence of actual absorbing profiles with total debt tending to zero. A
compact subsequence has all debts zero and nu=0, and belongs to C. Thus an
example with a strictly positive GLOBAL constrained minimum on this carrier
would itself exhibit the original positive absorbing-debt obstruction.
Solved arbitrary-profile controls cannot falsify a theorem restricted to
this positive global source.

### Exact lexicographic access

Fix observer weights w_i in [1,2], let W=sum_(i!=h) w_i, and put

    theta_h=epsilon, theta_i=w_i (i!=h),
    t=epsilon*r/(W+epsilon).

The ORIGINAL raised SUM, with no approximation, is

    F_epsilon(Y)=sum_(i!=h) w_i d_i(Y)+epsilon J_r(Y).       (6)

Let Y_epsilon minimize (6). Comparing with a minimizer X of (2) gives
F_epsilon(Y_epsilon)<=epsilon m(r). Hence observer debts tend to zero and
every compact limit Y belongs to C. Dividing by epsilon and using their
nonnegativity gives J_r(Y)<=m(r), so Y is a GLOBAL constrained minimizer.
Furthermore

    sum_(i!=h) w_i d_i(Y_epsilon)=o(epsilon).               (7)

Indeed J_r(Y_epsilon) tends to m(r) along each convergent subsequence, and
the quotient in (7) is at most m(r)-J_r(Y_epsilon). This establishes exact
global constrained minimality, not just a candidate zero-observer profile.
For 0<r<A, (3)--(4) give a source-uniform positive Never bound for sufficiently
small epsilon; the existing cone-weight proof then forces all ENDs. The
direct argument below proves all-END and the mass bound for EVERY constrained
minimum, independently of which limits (6) selects.

## 2. A complete tail that preserves all three observer debts

For T>=0 use independent truncated exponential clocks of rates v_i on
[0,T], with Never probabilities exp(-v_i T). This is a compact limit of
actual discrete private-clock profiles. To implement it, divide [0,T] into
finer cells and use the independent hazards 1-exp(-v_i Delta) at their
calendar dates, with empty dates before and after. Prescribed collision
probabilities and the collision probability of ANY forced finite response
are uniformly O(max Delta). Arbitrary bounded coalition rewards therefore
contribute vanishing errors. Finite-deadline responses converge uniformly
to the displayed integrals; late responses converge to the endpoint. Thus
the construction controls the FULL cap, not only a fixed response menu.

Writing Q_T for this point of the original native carrier, a finite response
at time y has payoff

    F_i(y)=(Gamma v)_i integral_0^y exp(-(S-v_i)s) ds.

The prescribed payoff is

    U_i(Q_T)=(Gamma v)_i integral_0^T exp(-Ss) ds.

Consequently all three observers have EXACT compact-limit coordinates

    B_i(Q_T)=e_i(Q_T)=U_i(Q_T)=0,       i!=h,               (8)

whereas

    b(T)=B_h(Q_T)=e_h(Q_T)=(1-exp(-kT))/k,
    u(T)=U_h(Q_T)=(1-exp(-ST))/S,
    nu(Q_T)=exp(-ST), N_i(Q_T)=exp(-v_iT).                 (9)

The finite-word approximants need not have literally zero observer debts
for arbitrary higher rewards; their exact zero limits in (8) are what is
used. No claim of an actual continuous-time strategy is required.

For any old Y in H, the complete original graft on its old Never branches
obeys, with H_i=product_(j!=i)N_j,

    U_i'=U_i+nu U_i(Q_T),
    B_i'=max(B_i,e_i+H_i B_i(Q_T)),
    N_i'=N_i N_i(Q_T), e_i'=e_i+H_i e_i(Q_T).              (10)

Finite-prefix realizers, an empty boundary response and diagonal limits
implement (10) in the SAME original carrier. Old prefix responses and every
new finite or Never response are accounted for by its maximum.
The old cap is retained by this construction. Immediate attachment of a
first atom without the boundary test is a different operation: it can remove
old END queries when no earlier query attains that cap. Formula(10) does
not silently apply to that operation. All constrained comparisons below
use the specified feasible graft, so their global-minimum conclusions do
not require excluding any other operation.

Because B_i>=e_i, (8)--(10) show that every observer's prescribed payoff AND
full cap are unchanged. Therefore grafting Q_T maps C into C exactly. This
is a joint change of all four complete laws that preserves all three
observer constraints; it is not the invalid frozen-observer thinning.

## 3. Every constrained minimum is all-END and has a finite distinguished clock

Let Y minimize J_r on C, with 0<r<A. By (5), all N_i>0 and the observers are
END-active. If B_h>e_h, then for all sufficiently small T the last maximum
in (10) leaves B_h unchanged. It follows that

    J_r(Y graft Q_T)-J_r(Y)
      =-nu[u(T)+r(1-exp(-ST))]<0,

a contradiction. Hence h too is END-active. At every constrained minimum,
the exact whole-tail increment is therefore

    J_r(Y graft Q_T)-J_r(Y)
      =nu[b(T)/N_h-u(T)-r(1-exp(-ST))].                  (11)

Its derivative at T=0 is nu[1/N_h-1-rS]. Thus EVERY constrained minimum
obeys

    N_h<=1/(1+rS),  f_h>=rS/(1+rS)>0.                   (12)

This is an actual global constrained-minimum theorem. There is no generic
parameter qualification and no assertion that a selected constrained
minimum must be one common source as r or the observer weights vary.

For completeness the entire scalar tail optimization is explicit: the
derivative of the bracket in (11) is

    exp(-ST)[exp(v_hT)/N_h-1-rS].

It is nonnegative for every T>=0 exactly when (12) holds. Thus no repeated
forward axis-tail graft improves a constrained minimum after its first
variation has imposed (12).

## 4. Strict separation from EVERY jointly repaired deletion

Define the explicit positive function

    Phi(r)=v_h/[S k] * [1-(1+rS)^(-k/v_h)], r>0.          (13)

It is the minimum of b(T)-u(T)+r exp(-ST), attained at

    T_star=log(1+rS)/v_h.

Its derivative in r is (1+rS)^(-S/v_h)<1; Phi(0)=0. Hence

    0<Phi(r)<r.                                         (14)

Starting the same tail at AllNever also gives the unconditional benchmark
m(r)<=Phi(r). It implies m(r)<=log(1+rS)/S, but the explicit Phi benchmark
is sharper; no separate novelty is claimed for that weaker logarithmic bound.

Choose ANY minimizer Y_N of J_r on C_N. Its observers have zero debt and
N_h=1. The equality U_h=e_h holds on this face: it follows by continuity
from |U_h-e_h|<=2M(1-N_h). Since H_h=nu, (10) gives the exact identity

    d_h'=max(d_h,nu b(T))-nu u(T).

In particular,

    J_r(Y_N graft Q_T)-J_r(Y_N)
       <=nu[b(T)-u(T)-r(1-exp(-ST))].                    (15)

By (3)--(5), nu(Y_N)>=c_r. Put T=T_star in (15). The graft is feasible in
C, so

    m_N(r)-m(r)>=c_r [r-Phi(r)]>0,        0<r<A.          (16)

This is the complete answer to the deletion proposal at this source.
Starting from ANY global constrained minimum, change all three observers'
laws arbitrarily, enforce their debts to be zero again, and set h to Never.
The resulting point lies in C_N and has objective at least the strictly
larger number m_N(r). Thus such a repair cannot even MATCH the original
minimum, let alone strictly improve it. All three observer laws may change
together; every original behavioral response is still included.

The conclusion is conditional on the actual A>0 source, not on an arbitrary
profile pretending to have a positive gap. It does not contradict global
minimality: the profitable construction starts on the deletion face and
REINTRODUCES h. It rules out this proposed closure mechanism. It supplies
no positive-A example and no proof that A>0 is possible.

## 5. All positive-drift cone grafts have monotone original SUM

There is a second complete architecture obstruction. Fix an original
raised-table global minimum with positive Never, all native ENDs active,
weights theta_i>0, and b=t sum_i theta_i>0. Its thin-word first variation is

    sum_i theta_i (Gamma x)_i^+/N_i
      >=sum_i theta_i (Gamma x)_i+b sum_i x_i,
                for every x>=0.                         (17)

Consider ANY locally integrable hazard control x(s)>=0 such that

    a(s)=Gamma x(s)>=0       for almost every s.          (18)

Append its diffuse tail on the old Never branches, retaining the old cap
menu by the empty-boundary construction of Section2. Step approximants can
be chosen inside this convex cone by interval averaging; the same uniform
finite-response estimates used above implement every finite interval in
the original compact carrier. Let S(s)=sum_i x_i(s). The exact graft state
obeys almost everywhere

    N_i'=-x_i N_i, nu'=-S nu,
    U_i'=nu a_i, e_i'=(nu/N_i)a_i,
    B_i'=e_i', d_i'=nu a_i(1/N_i-1).                     (19)

Here the prime on B_i denotes its derivative, not a new cap value. Every
tail response is nondecreasing in its testing time because a_i>=0, and
the old cap equals old e_i, so END remains active throughout. These facts
justify the FULL-cap equation in (19).

Set p_i(s)=theta_i(1/N_i(s)-1). Every p_i is nondecreasing. On the cone (18),
(17) is exactly

    p(0) dot a >=b S.

Therefore the true raised original SUM has derivative

    D_r'(s)=nu(s)[p(s) dot a(s)-b S(s)]>=0.              (20)

The final inequality uses both a_i>=0 and p_i(s)>=p_i(0); it is not a new
minimum assumption about the moving tail. It follows that EVERY finite
controlled graft in this cone is nondecreasing in the original objective.
For an infinite tail, apply this statement to every finite truncation.
All native payoff/cap coordinates are bounded; their endpoint limits or
compact subsequences stay in the same carrier. The objective bound passes
to the limit, including zero-survival boundaries. No division by zero at an
unreached endpoint is used.

This includes arbitrary switching, repeated axis tails, time-varying rates,
and all directions x with Gamma x nonnegative, not merely a fixed ray.
For constrained tails preserving the three observer coordinates by (8),
the axis invariant is precisely N_h<=1/(1+rS). Repeating that repair tail
only decreases N_h further and cannot reverse the inequality.

Within this attachment operation, a successful diffuse tail would have to
use a negative singleton drift somewhere, so that END can acquire slack
and later responses can spend it. Other operations can change the old
finite part or attach an immediate first atom that removes boundary queries.
Positivity of Gamma u alone does not supply a nonlocal descent after (17).

This last necessary alternative is not a sufficient escape. A subsequently
derived box-dual argument rules out singleton-only grafts that retain the
old cap menu, including signed and switching drift. It does not cover an
immediate attachment that removes the old boundary queries and permits
negative conditional caps. Its full scope is recorded in
CODEX_COORDINATOR__SINGLETON_GRAFT_DUAL_BARRIER.md.
Thus (19)--(20) are retained as explicit state dynamics, not as
the strongest surviving tail obstruction.

## 6. Checks, reuse, and remaining question

The existing all-END proof already recorded (9) as a nonlinear diagnostic
and proved the complete graft and thin-word inequality. The present new
uses are the exact GLOBAL constrained problem, its equivalence with A>0,
the every-minimum theorem, strict separation (16) for joint observer repair,
and the full controlled-cone monotonicity theorem (20). No novelty of
exponential clocks, envelope differentiation, or scalar convexity is claimed.

The note
CODEX_FIXED_COLUMN_VARIATION__FULL_CAP_THINNING_RENT.md Section9 proves the
different frozen-observer rent obstruction and records the missing joint
repair budget. Equation(16) shows that budget is not merely unproved: at
the genuine constrained global minimum it has the opposite strict sign.
The earlier fixed-clock deleted-tail note does not price this source.

Section10 of that same owned note provides a complete exact calibration of
joint deletion, with the literal matrix and table used by the checker here:

    Gamma=[[0,-1,1,1],[2,0,-1,-1],[-1,2,0,-1],[-1,2,-1,0]],
    Z_i(C)=0 if i in C, and sum_(j in C) Gamma_ij otherwise.

Its strict inverse column is v=(1,1,1,1). The actual one-date profile with
all four quitting probabilities 1/5 has all ENDs active, all observers'
full debts zero, and J_(1/2)=153/625. Over ALL jointly repaired observer
laws with h Never, including the original compact zero-observer fiber,
the exact minimum is m_N(1/2)=1/2. The proof forces every first finite
coalition to be {1} and retains a quantitative error bound for compact
realizers. This solved table has A=0 and unrestricted compact m(1/2)=0.
It therefore illustrates joint-deletion failure without pretending that
the displayed positive-Never profile is a global positive-A minimum.

Inspected exact source declarations are
quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum and
quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff in
UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean, and
quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff and
quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile
in UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean.
No Lean command or edit was performed. The strict-column/all-END source and
its earlier component files are unchanged.

The owned exact checker is
math/experiments/CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_GRAFT_CHECK.py.
It checks the scalar optimization algebra, rational complete-clock
realizations in an explicitly specified sixty-entry control, the full graft
including every pure response class, and switched positive-cone dynamics.
Its controls make no positive-A claim. The universal inequalities are
proved above, not inferred from the checks.

The next substantive question is an operation using genuine multiple-player
first coalitions, changing the old finite prefix, or attaching an immediate
first atom that removes old boundary queries, while controlling every full
observer cap. Joint deletion at the zero-observer global source cannot
serve as that operation by (16). The stronger box-dual obstruction prevents
merely changing singleton drift signs from providing an escape while the
old cap menu and empty boundary are retained.
