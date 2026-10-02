# Withdrawal and deadline quiet extensions

## 1. Exact statement and conjecture-facing change

Let I be a finite nonempty player set and let r(A) in R^I be an arbitrary
real reward vector for each nonempty A ⊆ I. First simultaneous quitting
absorbs the game; live play and infinite all-Continue (Never) pay zero.
Randomization is independent and private, and unilateral deviations are
unrestricted behavioral strategies.

Choose a nonempty proper child S ⊂ I. The child game restricts rewards
to nonempty coalitions and recipients in S. The quiet lift Lp of a child
profile p appends deterministic Never for every outsider. Write
s_i=r_i({i}), and define complete terminal regret by

    U_i(p) = terminal expected payoff,
    B_i(p) = sup_τ U_i(τ,p_-i),    d_i(p)=B_i(p)-U_i(p),
    E(p)=max_i d_i(p),            D(p)=sum_i d_i(p).

The supremum is over every behavioral replacement. All quantities are
finite because the reward table is finite. The same notation with
superscript f denotes the evaluated payoffs defined in Section 2.

This packet gives two distinct finite reward-table criteria:

- **Future patient withdrawal:** advancing a quit or replacing all future
  quitting by a sufficiently late quit or Never. Its complete terminal
  regret coefficients are lambda_ki+mu_ki.
- **Deadline withdrawal:** advancing clocks later than a deadline or
  withdrawing just its atom. These events are disjoint, giving the sharper
  coefficients max(a_ki,b_ki), with a bound at every nonincreasing
  absorption evaluation. Explicit stationary security values further
  improve the singleton withdrawal floors.

The criteria are incomparable even for a fixed child. Neither is a
strategy-class completeness claim. Both include the advancing-only
capped-clock criterion as a specialization, and both produce parent
uniform-equilibrium payoffs from literal finite reward data in Fin4.
The distinct raw cones, their exact strict class examples, and the
security-floor improvement are ordinary mathematics to be formalized.
The existing behavioral, low-cardinality, and fixed-target consumers are
identified in Section 12.

### 1.1 Finite floors and withdrawal gains

Put

    u_i=max(0,s_i),
    l_i^P=min({u_i} union {r_i(B): empty!=B subset S\{i}}),
    l_i^0=min({0} union {r_i(B): empty!=B subset S\{i}}).

Each minimum has a nonempty finite domain, even for a one-player child.
For a vector z of singleton continuation floors define, for nonempty A⊆S,

    W_i^z(A)=0,                             if i not in A;
             r_i(A\{i})-r_i(A),            if i in A and |A|>=2;
             z_i-s_i,                      if A={i}.

No empty-coalition reward is used.

### 1.2 Patient-withdrawal criterion and theorem

For every outsider k, choose lambda_ki,mu_ki>=0 such that

    (P-N) s_k <= sum_i lambda_ki s_i + sum_i mu_ki u_i;

    (P-F_A) s_k-r_k(A)
        <= sum_i lambda_ki [s_i-r_i(A)] + sum_i mu_ki W_i^(l^P)(A);

    (P-J_A) r_k(A union {k})-r_k(A)
        <= sum_i lambda_ki [r_i(A union {i})-r_i(A)]
             + sum_i mu_ki W_i^(l^P)(A).

Both coalition families range over every nonempty A⊆S, and every sum
ranges over i∈S. Then, for every actual independent child profile,

    d_k(Lp) <= sum_i (lambda_ki+mu_ki)d_i(p),
    d_i(Lp) = d_i(p)                                  (i in S).    (P)

Thus E(Lp)<=K_P E(p), where

    K_P=max(1,max_(k outside S) sum_i(lambda_ki+mu_ki)).

The rows are necessary and sufficient for the universal terminal
pointwise limiting comparison of the specified operations in Section 3,
with those fixed weights. They are not necessary for all quiet extensions
or for uniform equilibrium. This criterion is terminal: its numerical
bound is not asserted evaluation by evaluation.

There is a separate all-evaluation cancellation variant. Replace l^P
by l^0 in P-F and P-J and replace P-N by
s_k<=sum_i lambda_ki s_i. Then (P) holds for every evaluation f of
Section 2 with d_i replaced by d_i^f.

### 1.3 Deadline-withdrawal criterion and theorem

For every outsider k, choose a_ki,b_ki>=0 such that

    (D-N) s_k <= sum_i a_ki s_i;

    (D-F_A) s_k-r_k(A) <= sum_i a_ki [s_i-r_i(A)];

    (D-J_A) r_k(A union {k})-r_k(A)
        <= sum_i a_ki [r_i(A union {i})-r_i(A)]
             + sum_i b_ki W_i^(l^0)(A).

For every child profile and every evaluation f of Section 2,

    d_k^f(Lp) <= sum_i max(a_ki,b_ki)d_i^f(p),
    d_i^f(Lp) = d_i^f(p)                              (i in S).    (D)

In particular E_f(Lp)<=K_D E_f(p), with

    K_D=max(1,max_(k outside S) sum_i max(a_ki,b_ki)).

The corresponding sum-debt bound is

    D_f(Lp)<=sum_(i in S)[1+sum_(k outside S) max(a_ki,b_ki)]d_i^f(p).

D-N,F,J are necessary and sufficient for the terminal pathwise weighted
cap-and-atom-withdrawal inequality in Section 4. The security-enhanced
variants in Section 5 are sufficient criteria, without a claimed converse.

For a three-player child, either basic criterion has six nonnegative
weight variables and fifteen scalar reward inequalities. Computing the
finite floors first makes it a linear feasibility problem in the weights.
Setting all withdrawal weights to zero gives the same advancing-only
N,F,J conditions and their complete all-evaluation comparison. Its proof
is included in Sections 3 and 4, not assumed separately.

### 1.4 Uniform payoffs and strategic inputs

Under either criterion, every specified child uniform-equilibrium payoff
v_S extends to some parent uniform-equilibrium payoff v with v|S=v_S.
The same conclusion holds under the terminal Never-row relaxations in
Section 6 when a child own singleton is strictly positive.

For I with four players and any nonempty proper S, the corresponding raw
criterion alone implies existence of a parent uniform-equilibrium payoff.
The one-, two-, and three-player existence theorems supply the child for
every restricted signed reward table. No good child profile, continuation,
absorption schedule, or punishment witness is an additional premise.

The finite row-adapter consists only of restricting the reward table,
computing its floors, and finding nonnegative weights satisfying one of
the stated systems. Theorems (P) and (D) control every actual child
profile, not merely an assumed special strategy. Section 6 produces the
fixed parent target from the existing child and terminal consumers.
For rational data, Section 7 gives a terminating enumeration of actual
finite independent laws at every requested positive terminal error.

## 2. Information, clock laws, and evaluations

Before absorption, the only public history at date t is t repetitions of
all-Continue. A behavioral strategy specifies a conditional hazard h_i(t)
on that history. Its first-Quit law is

    Pr(T_i=t)=h_i(t) product_(n<t)(1-h_i(n)),
    Pr(T_i=Never)=lim_N product_(n<N)(1-h_i(n)).

Conversely, a law on N∪{Never} gives these hazards by conditioning on
survival, with arbitrary values on unreachable histories. Independent
private randomization gives independent clocks. This correspondence holds
for complete unilateral replacements as well as prescribed strategies.
No player observes another's future private clock.

For a deterministic tuple T, let tau=min_i T_i. If tau is finite, the
first coalition is A={i:T_i=tau}; otherwise the payoff is zero. For any
nonincreasing f:N∪{Never}->[0,1], with f(Never)=0, define

    U_i^f(p)=E[f(tau)r_i(A)],

interpreting the integrand as zero on joint Never. Terminal evaluation
uses f(t)=1 at every finite t. Under the zero-payoff quitting-stage
convention, horizon H>=1 gives f_H(t)=max(H-t-1,0)/H. Normalized discount
factor d∈(0,1) gives f_d(t)=d^(t+1). All such payoffs and response gains
are bounded by a finite reward bound or twice that bound.

A uniform-equilibrium payoff v is one fixed vector such that, for every
ε>0, one profile p and one threshold H₀ satisfy, for all H>=H₀,

    max_i |U_i^(f_H)(p)-v_i| <= ε,     E_(f_H)(p) <= ε.

The profile and threshold may depend on ε; the target may not.

## 3. Future patient withdrawal and cancellation

Fix an outsider k and suppress its index on the weights. For a proposed
outsider law, take an independent clock Z with that law. Each child
summand below is a separate unilateral experiment against the unchanged
original child opponents.

The advancing response is A_i(T_i,Z)=min(T_i,Z). For integer L>=1 the
patient response P_i^L keeps T_i when Z=Never or T_i<Z. Otherwise it uses
the finite date Z+L if s_i>=0 and uses Never if s_i<0. This response is
legal: it depends only on the player's original clock, its independently
sampled replica Z, and the known table.

The patient operation may turn an old Never into a finite quit. When
opponents all use Never and s_i>=0, its terminal payoff is s_i for every
finite L, even though its clock laws may converge weakly to Never.
The argument uses limits of actual payoffs and never assigns s_i to
Never itself.

### 3.1 Deterministic terminal comparison

Fix a finite outsider deadline t and an original child tuple. Let tau
be its first date, with first coalition A when finite.

- If tau<t, all first outcomes are unchanged and all gains vanish.
- If tau=t, the outsider joins A. Advancing child i produces the join
  gain r_i(A∪{i})-r_i(A). A patient response of a nonmember changes
  nothing. A member of a nonsingleton A leaves A\{i} at the same date.
  For A={i}, the limiting new payoff is r_i(B) if the first later
  opponent coalition B is finite, and u_i if all opponents use Never.
  Its limiting gain is therefore at least l_i^P-s_i. P-J proves the
  weighted comparison.
- If t<tau<Never, the outsider preempts and gains s_k-r_k(A).
  Every advancing child quits alone at t and gains s_i-r_i(A).
  A patient response of a nonmember eventually leaves the original
  first outcome unchanged. Members have exactly the same withdrawal
  alternatives as in the preceding case. P-F proves the comparison.
- On joint child Never, the outsider gains s_k, advancing gains are
  s_i, and patient gains are u_i. This is P-N.

At t=Never all operations are the identity. Thus, writing G for gains,

    G_k <= sum_i lambda_i G_i^A
                  + sum_i mu_i lim_(L->infinity) G_i^(P,L).    (3.1)

Every patient gain has a pointwise limit and absolute value at most twice
a reward bound. Bounded convergence allows integration of (3.1) over
independent (T,Z). For each finite L, each child term is the gain from
an actual complete replacement and is at most d_i(p) in expectation.
The same upper bound holds for its limiting expectation. Nonnegative
weights therefore bound every proposed outsider law by the right side
of (P). Taking its supremum proves (P).

A common Z is only a proof coupling among different unilateral
counterfactuals; no correlated child profile is played. Child payoffs
and full caps are unchanged by outsiders prescribing Never.

To prove necessity for (3.1), joint Never recovers P-N. Put exactly A
at date 1 and the outsider deadline at zero to recover P-F; put A at
date zero to recover P-J. For a singleton A={i}, select a hidden later
opponent coalition attaining l_i^P, or all opponents Never if u_i
attains the minimum. This makes the singleton lower bound exact.

### 3.2 The separate all-evaluation cancellation variant

Replace the patient operation by C_i(T_i,Z)=T_i if T_i<Z, and Never
otherwise; at Z=Never this still leaves every clock unchanged. Use l^0
and the old Never row specified in Section 1.2.

For a singleton withdrawal, a later opponent reward r_i(B) at tau'
is at least f(tau)l_i^0 after evaluation: if r_i(B)>=0 use l_i^0<=0;
if r_i(B)<0 use f(tau')<=f(tau) and r_i(B)>=l_i^0. Never also satisfies
the lower bound. Nonsingleton withdrawals occur at the unchanged first
date. For t<tau, put

    n=s_k-sum_i lambda_i s_i,
    F_res=s_k-r_k(A)-sum_i lambda_i[s_i-r_i(A)]
                                  -sum_i mu_i W_i^(l^0)(A).

The evaluated outside-minus-child residual is at most

    [f(t)-f(tau)]n+f(tau)F_res <= 0.

All other cases are nonnegative multiples of the corresponding row.
Integration gives the cancellation variant of (P), evaluation by
evaluation. This proof does not justify using the patient floor or its
enlarged Never row at finite horizons; Section 8 gives an exact falsifier.

## 4. Deadline-only withdrawal and the maximum coefficient

For finite t define

    C_t(x)=min(x,t),
    R_t(x)=Never if x=t, and x otherwise.

At t=Never use the identity for both. Let G_i^C,G_i^R be their separate
evaluated gains. The deterministic comparison is

    G_k <= sum_i [a_i G_i^C+b_i G_i^R].                       (4.1)

If the child absorbs before t, all gains vanish. If t is before finite
child absorption at tau with coalition A, withdrawal has no effect.
Set alpha=s_k-sum_i a_i s_i and psi=r_k(A)-sum_i a_i r_i(A).
The residual equals

    f(t)alpha-f(tau)psi
       =[f(t)-f(tau)]alpha+f(tau)[alpha-psi] <= 0

by D-N and D-F. On joint child Never, D-N applies directly.

At t=tau, a nonmember joins under C_t and is unchanged under R_t.
A member is unchanged under C_t. Withdrawal from a nonsingleton first
coalition leaves the other members at t. A singleton withdrawal reveals
a later opponent coalition or Never; its evaluated gain is at least
f(t)(l_i^0-s_i), by the nonpositive-floor argument of Section 3.2.
D-J proves (4.1). Taking t=Never gives zero throughout.

The same terminal necessity witnesses as above recover D-N and D-F;
for D-J put A at date zero and choose the later singleton outcome
attaining l_i^0. This establishes the stated pointwise characterization.

For c_i=max(a_i,b_i)>0, form one randomized private replacement:

- on T_i<t, keep the clock;
- on T_i>t, advance to t with probability a_i/c_i;
- on T_i=t, withdraw to Never with probability b_i/c_i.

Keep the original clock in the remaining probabilities. For c_i=0 or
t=Never use the identity. The two nontrivial events are disjoint.
Conditional on the entire original tuple,

    c_i E[gain of this replacement | T]
                           = a_i G_i^C+b_i G_i^R.             (4.2)

Both probabilities lie in [0,1]; their sum need not be at most one
because they apply on different private-clock events. Given an outsider
law, sample a private independent Z and use t=Z in this construction.
This is a legal independent child response. Integrating (4.1)-(4.2)
and bounding its gain by d_i^f(p) gives (D) after the outsider supremum.

The same proof applies separately to every outsider. Coalitions containing
two outsiders never occur in these unilateral experiments and are
unrestricted by either criterion.

## 5. Stationary-security improvement of deadline withdrawal

For each child i, solve the finite two-variable linear program

    maximize v,
    0<=h<=1,     v<=s_i,
    v<=(1-h)r_i(B)+h r_i(B union {i})
                    for every empty!=B subset S\{i}.         (5.1)

Adding -M<=v<=M for a reward bound M makes the feasible region compact
without changing its optimal value V_i: v=-M is feasible, and v<=s_i<=M.
Put gamma_i=max(l_i^0,V_i).

In D-J, replacing l_i^0 by gamma_i gives the same complete terminal
bound (D). Replacing it by gamma_i^-=min(gamma_i,0) gives the same
bound for every nonincreasing evaluation. D-N and D-F remain unchanged.

### 5.1 Actual terminal security plans

For feasible h>0, repeated own hazard h guarantees v against every
opponent plan. Condition on any deterministic first opponent date L and
coalition B. Every earlier own stop pays s_i>=v. Conditional on survival
to L, the expected payoff is (1-h)r_i(B)+h r_i(B∪{i})>=v.
If all opponents use Never, the own geometric clock stops almost surely
and pays s_i. Averaging proves the guarantee for arbitrary independent
opponent laws.

If an optimum has h=0, positive h approaching zero give guaranteed values
approaching V_i, by continuity of the finitely many affine expressions.
The floor l_i^0 is guaranteed exactly by Never. Thus gamma_i is
arbitrarily closely guaranteed by actual private plans. For rational data
one can choose rational optimizing hazards when positive; at a zero
optimizer, a sufficiently small positive rational hazard attains any
strictly requested approximation.

Modify R_t only on T_i=t: instead of Never, install a fresh such plan
starting at t+1. A nonsingleton first coalition still absorbs at t after
the owner leaves. At a singleton first coalition the restart guarantees
gamma_i-eta against the conditional future opponent laws. These remain
independent; the preceding argument also works for every deterministic
future opponent tuple. The advance and restart events remain disjoint.
The comparison acquires at most eta sum_i b_i error. First bound each
actual response gain by its full cap, then let eta tend to zero. This
gives the exact numerical terminal regret bound without assuming an
attained security value or response cap.

### 5.2 A nonpositive security floor for all evaluations

The bound gamma_i^- is attained by a suitable positive stationary hazard
or by Never. If gamma_i=l_i^0, use Never. If an LP optimum is attained
at h=0 with V_i<=0, its constraints imply V_i<=l_i^0. If V_i>0 is attained
there, all passive rewards are positive and Never guarantees zero.
In the remaining case an optimal positive hazard guarantees V_i and
therefore gamma_i^-.

For a positive hazard and v<=0, each own-only stopping reward is at least
v, and the conditional same-date mixture at a first opponent stop is at
least v. Evaluating either at a later date u>t keeps its payoff or mean
at least f(t)v, since f(u)<=f(t) and v<=0. The probabilities of these
branches sum to one, including almost-sure own stopping on opponent
Never. For a Never plan, nonabsorption gives zero>=f(t)v.
This proves the evaluated restart bound and hence the all-f improvement.

For example, s_i=0, passive reward -1 and joint reward 1 against a single
opponent give l_i^0=-1, while h=1/2 gives V_i=0. The evaluated floor
strictly improves to zero. In contrast, s_i=1, passive reward 1 and joint
reward 0 give V_i=1 only at h=0. Positive hazards guarantee 1-h, whereas
Never pays zero on opponent Never. Positive terminal security must not
be assigned to Never or to a finite-horizon restart.

## 6. Never correction, fixed targets, and Fin4 production

If a criterion's Never row is omitted, its terminal comparison changes
only on joint child Never. Write p_infinity=Pr(all child clocks Never).
For patient withdrawal put

    e_k=max(s_k-sum_i lambda_ki s_i-sum_i mu_ki u_i,0).

Then d_k(Lp)<=sum_i(lambda_ki+mu_ki)d_i(p)+e_k p_infinity.
For deadline withdrawal, including its security improvements, put

    e_k=max(s_k-sum_i a_ki s_i,0).

Then d_k(Lp)<=sum_i max(a_ki,b_ki)d_i(p)+e_k p_infinity.
The cancellation variant has the analogous latter correction with a=lambda.
These errors vanish if p_infinity=0.

For every child j, cap its clock at deterministic dates L tending to
infinity. On every originally finite first outcome the gain eventually
vanishes. On joint Never it is s_j. Bounded convergence and the full cap
therefore give

    s_j p_infinity <= d_j(p).                              (6.1)

A positive s_j converts the correction into (e_k/s_j)d_j(p), giving a
fixed amplification constant. Without that sign or a separate Never
bound, no removal of the error is asserted. These relaxations are
terminal, not evaluation-by-evaluation consequences of a positive singleton.

Now fix a child UE target v_S. The existing target-preserving entrance
theorem in Section 12 supplies child profiles p_n with terminal errors
tending to zero and U(p_n) tending to v_S. Its direct justification is
also simple: for one fixed profile and each fixed deviation, bounded
convergence sends the long-horizon payoff and Nash inequalities to their
terminal limits. Only after this passage is the conclusion quantified
over every deviation; no supremum and limit are interchanged.

Quiet lift the profiles. Child coordinates and regrets are unchanged,
and the applicable bound makes every parent terminal regret tend to
zero. The outside terminal vectors lie in a fixed compact reward cube.
Choose a subsequence on which they converge, defining v_out. Then the
full terminal vectors converge to one fixed v=(v_S,v_out), and their
full Nash errors vanish. The existing
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`
gives UE at v. Moreover,
`quittingGame_isUniformεEquilibrium_of_terminalNash` preserves the same
prescribed profile while allowing any strictly larger error. Choose one
sufficiently accurate quiet lift from the sequence and enlarge its horizon
threshold also to obtain delivery near v. Thus outsiders can remain
Never in every selected uniform profile, including the terminal-only
patient and relaxed cases.

For a nonempty proper child of Fin4, its size is one, two or three.
Relabel it by a Unique type, Bool, or Fin 3 respectively and apply the
corresponding unconditional existence declaration in Section 12.
Relabeling merely renames actions, histories, rewards, independent laws,
and unilateral deviations. Thus every table satisfying one of the raw
criteria has the required child target and strategies; no open strategic
producer is assumed.

## 7. Exact rational feasibility and actual finite-law enumeration

For rational rewards, the finite floors are rational. The security LP has
rational optimal values and rational optimizers: an optimizing vertex
solves a finite rational linear system, with redundant bounds available
as in Section 5. The weight conditions are finite rational linear
inequalities and have rational feasible weights whenever feasible.
This last assertion follows by eliminating variables using rational
linear bounds and then choosing rational values in the resulting nonempty
intervals, including equality endpoints.

For a rational Fin4 table passing a criterion, compute its rational regret
factor K, including a positive-singleton Never correction when used.
Given positive rational terminal tolerance ε:

1. Dovetail calendar lengths N>=0 and rational probability denominators,
   enumerating product child laws on {0,...,N-1,Never}.
2. Compute each player's reply values at EVERY date 0,...,N and Never,
   including dates assigned zero prescribed mass.
3. Accept a child law with E<ε/K and append outsider Never laws.

After N-1 every opponent has already quit or has selected Never, so every
finite reply date >=N has the same terminal value as N. Randomized
responses average the pure-date responses. Thus this is the unrestricted
terminal cap, not merely a menu cap. At N=0 the reply set is {0,Never}.

The existing full-cap finite-law approximation theorem and child UE give
a real finite-menu child law with regret strictly below ε/K. On a fixed
consecutive calendar, all payoffs and tested pure replies are finite
polynomials in the probabilities; their finite maximum is continuous.
Rational density preserves the strict inequality. The dovetail therefore
terminates. No runtime, bit-complexity, or uniform calendar bound is asserted.

For a specified real child target, the existing target-preserving finite-menu
theorem supplies mathematical approximants satisfying payoff and regret
bounds simultaneously. The target-free rational enumeration above does not
claim to compute an arbitrary real target or preserve it without target data.

## 8. Exact boundaries and incomparable raw cones

### 8.1 Patient withdrawal without a deadline-withdrawal certificate

Let S={0}, outsider 1, and use the complete two-player table

    r({0})=(-1,-1),     r({1})=(0,0),     r({0,1})=(0,0).

Patient weights lambda=0, mu=1 pass: u_0=l_0^P=0, so its N row is
0<=0 and both F and J are 1<=1. The deadline-withdrawal F row is
the impossible inequality 1<=0. Its security enhancement does not
change F and cannot repair this obstruction.

### 8.2 Deadline withdrawal without a patient certificate

Let S={0,1}, outsider 2, and

| A | r_0 | r_1 | r_2 |
|---|---:|---:|---:|
| 0 | 0 | 0 | 0 |
| 1 | -1 | 0 | 0 |
| 2 | 0 | 0 | 0 |
| 01 | -2 | 0 | 0 |
| 02 | 0 | 0 | -1 |
| 12 | 0 | 0 | 0 |
| 012 | 0 | 0 | 1 |

Deadline weights a=(0,0), b=(1,0) pass. All F and N bounds are zero;
the three J inequalities are respectively -1<=-1, 0<=0, and 1<=1.
For the patient criterion, P-F at {0} is 0<=-mu_0 and forces mu_0=0.
P-J at {0,1} is 1<=mu_0 and forces mu_0>=1. Thus no patient weights
work. The raw cones are incomparable, not merely differently normalized.

### 8.3 The patient coefficient is not an all-evaluation bound

Let S={0,1}, outsider 2, and

| A | r_0 | r_1 | r_2 |
|---|---:|---:|---:|
| 0 | 1 | 0 | 1 |
| 1 | 2 | 0 | 1 |
| 2 | 0 | 0 | 1 |
| 01 | 1 | 0 | 0 |
| 02 | 0 | 0 | 1 |
| 12 | 0 | 0 | 1 |
| 012 | 0 | 0 | 1 |

Patient lambda=(0,0), mu=(1,0) passes because u_0=l_0^P=1,
the singleton W_0 is zero and W_0({0,1})=1. Prescribe both children
to quit surely at date 1. At horizon H=3, child 0 has prescribed
payoff 1/3 and complete cap 2/3: Quit0 gives 2/3, while Never or a
strictly later quit reveals the opponent reward 2 at weight 1/3.
Its regret is 1/3. The quiet outsider has prescribed payoff zero and
regret 2/3, attained by Quit0. Thus its regret exceeds the patient
right side. For discount factor d∈(0,1), these two regrets are
max(d-d²,d²) and d, again a strict violation. At terminal evaluation
both regrets equal one, as (P) predicts.

### 8.4 Never protection cannot be silently discarded

Take one child with s_0=0 and all its rewards zero. Let outsider 1 have
s_1=r_1({0})=r_1({0,1})=1. Both criteria's F and J rows hold with
zero weights, but the all-Never child profile has zero regret and the
quiet parent lift has outside regret one. Its Never correction is
exactly one. No positive child singleton is available.

### 8.5 Sparse supported dates do not give a complete cap scan

Let child a prescribe Never and child b quit at dates 0 and 2 equally.
Set r_a({a})=1, r_a({b})=0, r_a({a,b})=-1 and all b rewards zero.
The pure reply values for a are

| Date | 0 | 1 | 2 | 3 | Never |
|---|---:|---:|---:|---:|---:|
| Payoff | 0 | 1/2 | -1/2 | 0 | 0 |

Testing only the supported dates 0,2, one post-calendar date and Never
would miss the profitable reply at date 1. Section 7's consecutive
calendar includes every gap and therefore has the claimed complete cap.

## 9. A strict patient-withdrawal class and its open neighborhood

Use the following literal four-player table r*, with Never payoff zero.
Coalition strings denote sets.

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

The singleton vector is (1,0,0,0). For S={0,1,2}, outsider 3, choose

    lambda=(0,0,3),       mu=(1/2,0,0).

Here u=(1,0,0), l^P=(0,-1,-1), and the P-N slack is 1/2.
In coalition order 0,1,01,2,02,12,012, the exact row slacks are

    P-F: (3/2,2,1,3,1,2,3/2),
    P-J: (3/2,2,5,2,1,2,1).

Consequently every actual child profile satisfies

    d_3(Lp)<=(1/2)d_0(p)+3d_2(p),     E(Lp)<=(7/2)E(p).       (9.1)

At A={0,1,2}, the outsider gains 1/2 by joining, whereas every advancing
child join gain is zero. Withdrawing player 0 gains
r_0({1,2})-r_0({0,1,2})=3; half of that gain pays for the outside gain.
The other rows make this a universal comparison, not a local illustration.

### 9.1 Every advancing-only proper-child test fails

For a child T and outsider k, the advancing-only J row at A⊆T has
coefficients r_i(A∪{i})-r_i(A), i∈T. The following one-row obstructions
cover every nonempty proper T; child coefficients use increasing labels.

| T | k | A | Child coefficients | Outside gain |
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

A nonnegative weighted right side is nonpositive, while its required
outside lower bound is positive. This also excludes the advancing-only
variant omitting its Never row.

### 9.2 A full sixty-coordinate reward neighborhood

Every table r with ||r-r*||_infinity<1/100 satisfies (9.1) with the same
weights and has a UE payoff. All sixty coordinates can vary independently;
Never stays zero.

Indeed s_i, u_i and l_i^P are 1-Lipschitz in the entrywise reward norm;
each W_i changes by at most 2delta. The P-N slack changes by at most
(1+3+1/2)delta=(9/2)delta. Each P-F or P-J slack changes by at most
2(1+3+1/2)delta=9delta. These changes are smaller than the respective
center margins 1/2 and 1. The raw criterion and the child theorem give UE.

In the obstruction table, zero coefficients are structural membership
zeros and remain zero. The only negative coefficients start at -1 and
remain negative, while the positive outside gains start at least 1/2
and change by at most 2delta. All fourteen obstructions therefore persist.
This is a strict open enlargement of the union of advancing-only
proper-child tests, not merely an improvement for one selected child.

### 9.3 An actual positive strategy example

At the center, prescribe date-zero Quit probabilities

    q=(1/2,2/5,1,0),

and Never afterwards. Direct finite product expectation gives the following
complete response values; all positive finite deadlines are equivalent.

| i | Prescribed U_i | Quit0 | Never | Finite date >0 |
|---|---:|---:|---:|---:|
| 0 | 0 | 0 | 0 | 0 |
| 1 | -1 | -1 | -1 | -1 |
| 2 | -2/5 | -2/5 | -7/10 | -7/10 |
| 3 | 7/10 | -4/5 | 7/10 | 7/10 |

Thus the profile is exact terminal Nash. In particular, the sure quitter's
counterfactual late and Never responses are included. The profile-preserving
uniformization theorem makes the same profile uniform at its terminal
payoff. This explicit strategy is not an input to the raw class theorem.

## 10. A strict deadline-withdrawal class and its open neighborhood

Define the integer table R below, then define a new literal table

    r_i(A)=R_i(A)-b_i for every nonempty A,
    b=(0,1/16,1/16,1/16),      r(Never)=0.

This defines the data; it is not an assertion of strategic equivalence
under terminal reward translation.

| A | R_0 | R_1 | R_2 | R_3 |
|---|---:|---:|---:|---:|
| 0 | 1 | 3 | -1 | -1 |
| 1 | 4 | 0 | -1 | -1 |
| 01 | 0 | 0 | -1 | 0 |
| 2 | 0 | -1 | 0 | 3 |
| 02 | 1 | 0 | 0 | 1 |
| 12 | 2 | -2 | 0 | 1 |
| 012 | 0 | 1 | -1 | 0 |
| 3 | 0 | -1 | 3 | 0 |
| 03 | 0 | -1 | 0 | -1 |
| 13 | 0 | 0 | 0 | 0 |
| 013 | 1 | 0 | -1 | 0 |
| 23 | 0 | 1 | 1 | 1 |
| 023 | 0 | 0 | 0 | -1 |
| 123 | 1 | 0 | 0 | 0 |
| 0123 | 0 | 1 | 0 | 1 |

For S={0,1,2} and outsider 3, use

    a=(1/8,0,2),    b_withdraw=(1,0,0),
    max(a,b_withdraw)=(1,0,2).

The singleton vector is (1,-1/16,-1/16,-1/16) and l_0^0=0; the other
withdrawal weights vanish. In order 0,1,01,2,02,12,012 the exact slacks are

    D-N: 1/16;
    D-F: (1,5/8,17/8,25/8,1,7/8,17/8);
    D-J: (1,1/2,4,17/8,1,3/4,1).

Thus, for every child profile and every nonincreasing evaluation,

    d_3^f(Lp)<=d_0^f(p)+2d_2^f(p),    E_f(Lp)<=3E_f(p).       (10.1)

Player 0's combined response withdraws an atom at the outsider's private
replica deadline with probability one, and advances a strictly later
clock with probability 1/8. Player 2 uses the ordinary cap map.

### 10.1 Every advancing-only proper-child test fails

If 0 is outside T, the outsider-0 Never inequality is
1<=sum_i lambda_i(-1/16), impossible. All child singletons are negative,
so its positive-singleton relaxation does not apply.

For T={0} or {0,1}, outsider 2's future row at A={0} is respectively
1<=0 or 1<=-3lambda_1, also impossible. For the other five proper
children containing 0, the following outsider has joining gain one at A=T:

    T=02,03,012,013,023;
    k=1, 1, 3,  2,  1.

Every advancing-only child join coefficient is structurally zero at A=T.
These are exact infeasibility witnesses independent of the weights.

### 10.2 A full sixty-coordinate reward neighborhood

Put rho=1/512. Every r' with ||r'-r||_infinity<rho, with Never still zero,
satisfies (10.1) with the same weights and freshly computed l^0.
The floor is 1-Lipschitz. Since sum a=17/8 and sum b_withdraw=1,
the N,F,J slack changes are bounded respectively by

    (25/8)rho,     (25/4)rho,     (33/4)rho.

They are smaller than the corresponding minimum center margins
1/16,5/8,1/2. Hence the raw theorem and child existence give UE
throughout this full-dimensional neighborhood.

Nonpivot own singletons remain negative and s_0 stays positive,
preserving the Never obstructions. The two future obstructions have a
structural zero coefficient and, when present, a coefficient starting
at -3. The five full-child join right sides remain structurally zero.
All positive outside gaps start at one and change by at most 2rho.
Thus every advancing-only proper-child test, including its available
positive-singleton relaxation, still fails.

### 10.3 Actual complete caps

At the center, use q=(1/2,1/3,1,0) at date zero and Never afterwards.

| i | Prescribed U_i | Quit0 | Never | Finite date >0 |
|---|---:|---:|---:|---:|
| 0 | 2/3 | 2/3 | 2/3 | 2/3 |
| 1 | -9/16 | -9/16 | -9/16 | -9/16 |
| 2 | -11/48 | -11/48 | -17/24 | -35/48 |
| 3 | 23/16 | 5/48 | 23/16 | 23/16 |

Every arbitrary response averages these pure values, so U=B and this
is exact terminal Nash, uniform for the same profile. The sure owner's
Never and strictly late values differ and cannot be identified.

### 10.4 Arbitrary child-recipient collision entries

Keep the singleton columns of this center fixed. All thirty-three
nonsingleton reward coordinates for recipients 0,1,2 may be chosen
arbitrarily. The three singleton F rows and N row remain fixed and
strictly feasible with the displayed a,b.

Choose the four recipient-3 entries on nonsingleton child coalitions
large enough to satisfy their F lower bounds. Then choose the seven
recipient-3 entries on A∪{3}, nonempty A⊆{0,1,2}, small enough to
satisfy their respective J upper bounds using the actual child leave
rewards and computed floor. Each is a distinct free coordinate, so
there is no conflict. Strict choices give a nonempty open region in
those remaining eleven coordinates. This does not claim that every
completion of the singleton matrix passes.

## 11. Additional exact scope of the two open classes

### 11.1 Full degree +1 and no nontrivial response-invariant partition

Both center tables have the singleton-difference matrix

    Gamma_ij=r_i({j})-s_i,
    Gamma=[0,3,-1,-1;3,0,-1,-1;-1,-1,0,3;-1,-1,3,0],
    det Gamma=45,
    Gamma^{-1}=(1/15)[2,7,3,3;7,2,3,3;3,3,2,7;3,3,7,2].

For a matrix M, LCP(M,z) means x>=0, w=Mx+z>=0 and x_iw_i=0.
R0 means that the homogeneous problem has only zero. The minimum-map
integer LCP degree of an R0 matrix is independent of the right-hand side;
a unique strictly complementary nonsingular solution has index
sign det M_SS on its positive support S. These classical degree facts
use the coordinatewise map min(x,Mx+z), as in M. S. Gowda,
“Applications of Degree Theory to Linear Complementarity Problems,”
Mathematics of Operations Research 18(4) (1993), Section 2, 869–870
([original article](https://doi.org/10.1287/moor.18.4.868)).

A strictly positive inverse implies R0: nonzero nonnegative slack w
would give x=M^{-1}w>0, forcing w=0 by complementarity; zero slack then
gives x=0. At right-hand side -1, every solution satisfies
x=M^{-1}(1+w)>=M^{-1}1>0, so w=0 and the solution is unique.
Its degree is therefore sign det M. Hence both full center matrices
are R0 of degree +1.

This persists on both neighborhoods. The inverse has row-sum norm one
and smallest entry 2/15. An entrywise reward perturbation by delta
changes the singleton matrix by induced infinity norm at most 6delta.
For delta<1/100,

    ||(Gamma')^{-1}-Gamma^{-1}||_infinity
           <=6delta/(1-6delta)<3/47<2/15.

The Neumann series proves this bound and invertibility all along the
segment. Thus the inverse stays strictly positive and the determinant
stays positive. The same R0 and degree argument applies.

For completeness, define the stationary residual at a product row q by

    alpha_i=product_(j!=i)(1-q_j),
    Q_i=expected r_i(B union {i}) over the opponents' product Quit set B,
    H_i=expected r_i(B) over its nonempty Quit sets,
    Delta_i=(1-alpha_i)Q_i-H_i.

A response-invariant partition requires equality of Delta_i and Delta_j
whenever i,j lie in one block, for every block-constant q. At the
patient center, q=(1,1,1,1) gives Delta=(1,1,-2,1/2).
Only the block {0,1} can remain nontrivial. But at its block-constant
q=(0,0,1,0), Delta_0=2 and Delta_1=-1, excluding that block.
At the deadline center, the common half-hazard point gives

    Delta=(-35/64,-1/8,1/8,-3/8).

All four values are distinct, with minimum separation 11/64, and that
point is block-constant for every partition. It excludes every
nontrivial block.

At a fixed q, changing every reward by at most delta changes Q_i by
at most delta and H_i by at most (1-alpha_i)delta. Thus Delta_i changes
by at most 2delta and pairwise differences by at most 4delta.
The patient witnesses have respective nonzero gaps at least 1/2 and 3;
the deadline witness has minimum gap 11/64. They therefore exclude every
nondiscrete response-invariant partition on the stated neighborhoods.

### 11.2 Nonclaims

The tests are raw sufficient conditions, not a classification of all
parent uniform payoffs or a universal unchanged-child construction.
Infeasibility rules out the stated compiler, not uniform equilibrium.
The different raw cones in Section 8 must not be merged by claiming
one contains the other.

Neither open class is a counterexample to equilibrium existence, and
both have explicit positive strategy examples. Their degree and partition
properties distinguish finite raw tests; they do not say that an existing
full behavioral verifier could not recognize a supplied equilibrium.

The patient theorem controls terminal regrets. Its cancellation variant
and the deadline theorem have the separately proved all-evaluation scope.
Positive stationary-security floors are terminal; their nonpositive
truncations have the all-evaluation scope. None of the Never relaxations
silently asserts finite-horizon transfer with the original numerical bound.

The results do not solve arbitrary Fin4, reduce arbitrary cardinality
to four, or give a normal form for general stochastic games. They do not
supply complexity bounds or an algorithm for an arbitrary specified real
target. Existing low-cardinality existence and terminal uniformization
are inputs, not claimed new results.

## 12. Exact tracked semantic interfaces

The following are existing checked repository declarations, distinct
from the clock compilers and raw classes proved here.

- `quittingBehaviorStoppingLaws_update`,
  `quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws`, and
  `quittingBehaviorDeviationPayoffCap_eq_pureTime` in
  `UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`
  identify independent first-Quit laws, literal unilateral replacements,
  their actual payoff expectations, and the full behavioral pure-time cap.
  Sections 2–5 use exactly that private-law model.
- `prod_stoppingLaw_none_mul_singleton_le_terminalDebt` in
  `UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`
  states (6.1) for actual behavioral laws, with no singleton sign
  assumption before the later division.
- `exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff`
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  takes one specified UE payoff v_S and every positive ε and produces
  an actual terminal ε-Nash profile whose terminal payoff is within
  ε of that target. This is the entrance used in Section 6.
  In the same file,
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`
  consumes actual terminal approximate Nash profiles with errors tending
  to zero and payoffs tending to one fixed full vector.
- `quittingGame_isUniformεEquilibrium_of_terminalNash` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformization.lean`
  converts a terminal ε-Nash profile into a uniform ε'-equilibrium
  for every ε'>ε without changing the prescribed profile. Consequently
  the selected profiles can keep outsiders at Never.
- `exists_finiteDeadlineTimingProfile_approximation` and
  `isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation`
  in
  `UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`
  approximate actual profiles or one specified target by finite product
  menus, preserving payoff and unrestricted-regret control. No sign,
  normality, or early-absorption premise is required.
- `quittingGame_exists_uniformEquilibriumPayoff_onePlayer` in
  `UniformEquilibrium/Quitting/Classification/OnePlayer/Existence.lean`
  supplies UE for an arbitrary Unique player type.
  `quittingGame_exists_uniformEquilibriumPayoff_twoPlayer` in
  `UniformEquilibrium/Quitting/Classification/TwoPlayer/Existence.lean`
  supplies UE for Bool.
  `quittingGame_exists_uniformEquilibriumPayoff_threePlayer` in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`
  supplies UE for Fin 3. Section 6 explains the relabeling for every
  possible nonempty proper child of Fin4.

## 13. Actual-data adapter and Lean handoff

The **withdrawal-row adapter** takes the literal reward table, a nonempty
proper child, and nonnegative weights satisfying one of the finite
systems. It computes all floors, including security LP values if used.
It contains no field asserting a good strategy, continuation, cap bound,
or equilibrium. For Fin4, the existing low-cardinality theorem supplies
the child, the proved comparison controls the actual quiet lift, and
the fixed-target entrance and exit supply the parent conclusion.

A narrow formalization can separate:

1. Finite floor definitions and raw N,F,J predicates for the two criteria.
2. Private pushforward clock laws for advancement, future patient reset,
   cancellation, deadline withdrawal, and the combined randomized kernel.
3. Deterministic pointwise comparisons, their specified converses, and the
   bounded-convergence patient argument against unchanged opponents.
4. The maximum-coefficient identity on disjoint private-clock events.
5. The two-variable security LP and actual stationary guarantee, including
   a possible zero-hazard optimizer and the nonpositive evaluated floor.
6. Full-regret quiet-lift bounds, the joint-Never correction, target
   preservation and the one-/two-/three-player dispatch.
7. The consecutive-calendar rational search and the exact tables,
   separating examples, margins and perturbation estimates above.

The imported behavioral consumers should be reused with their actual
hypotheses. No proof may replace a limit of finite patient-response payoffs
by the payoff of a Never limit, identify a menu cap with a full cap
without the complete date scan, or treat independently coupled child
experiments as a jointly correlated strategy.

