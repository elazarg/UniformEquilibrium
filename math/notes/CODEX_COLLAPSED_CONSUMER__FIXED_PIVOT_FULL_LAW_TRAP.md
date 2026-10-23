# A proper fixed pivot can pin all three observer laws globally

Owner: CODEX_COLLAPSED_CONSUMER.

Status: complete ordinary-mathematics control and finite-calendar
feasibility reduction, independently
[reviewed by CODEX_OBSERVER_PATH](../feedback/CODEX_COLLAPSED_CONSUMER__FIXED_PIVOT_FULL_LAW_TRAP__BY_CODEX_OBSERVER_PATH.md).
Exact rational checks pass. No positive-gap counterexample, global partial-Nash minimum,
new UE class, Lean result, or export is claimed.
Section 9 records the exact continuation-cap constraint in the remaining
global-minimum substitution question; it does not supply that substitution.

## 1. Question and answer

The full-law escape in Section 6 of
[the observer-path note](CODEX_OBSERVER_PATH__GLOBAL_MINIMUM_INCOMING_COLLISION.md)
deletes an observer atom while fixing a proper pivot clock. Is an analogous
observer deletion always available at a positive one-debtor source?

No. The exact table below has a fixed proper geometric pivot clock with
positive mass at EVERY finite date. Each observer has the same unique
strictly dominant complete stopping law: quit at date zero. Consequently
the observer-Nash carrier at this fixed pivot law is a SINGLE point,
even when every observer may replace its entire unrestricted law. That
point has positive payoffs, positive pivot debt, a macroscopic incoming
collision, and AllContinue as its unique full Nash root at continuation U.
Every full singleton column contains a negative entry.

Global uniqueness here holds over every observer deadline and literal
Never, with the pivot's entire law fixed.

The fixed-pivot restriction is essential. An explicit pivot-law change
lowers the debt, and the game has an absorbing exact Nash profile. Thus
the control refutes a universal fixed-pivot deletion lemma, not a consumer
that uses positive gap and minimizing provenance over ALL four laws.

## 2. Complete table and fixed pivot clock

Players are 0,1,2,3, with pivot 0. Set b_1=b_2=1 and b_3=-1. For each
nonempty coalition S assign the pivot reward

    Z_0({0})=0,
    Z_0(S)=1 if 0 belongs to S and |S|>=2,
    Z_0(S)=2 if 0 does not belong to S.

For observer i, if 0 belongs to S set

    Z_i(S)=2 if i belongs to S,
    Z_i(S)=b_i if i does not belong to S.

If 0 does not belong to S, set

    Z_i({i})=0;
    Z_i(S)=-2 if i belongs to S and |S|=2;
    Z_i(S)=-1 if i belongs to S and |S|=3;
    Z_i(S)=-1 if i does not belong to S and |S|=1;
    Z_i(S)=0  if i does not belong to S and |S|=2.

These disjoint rules specify all sixty entries. Live and Never rewards
are zero, and every own singleton is zero. The full singleton matrix is

    Gamma = [ 0  2  2  2 ]
            [ 1  0 -1 -1 ]
            [ 1 -1  0 -1 ]
            [-1 -1 -1  0 ].

Every column has a negative entry. Gamma is R0: a homogeneous
complementarity vector with a nonzero observer coordinate must have pivot
coordinate zero, by the positive pivot row. The remaining observer
zero-diagonal block with all off-diagonal entries -1 has no nonzero
homogeneous complementarity vector. A pivot-only vector violates row 3.

Fix the pivot's complete stopping law to be geometric with hazard

    h=9/10,       s=1-h=1/10,
    Pr(T_0=k)=h s^k for k>=0,       Pr(T_0=Never)=0.       (1)

This law is proper and has full finite support. Therefore every profile
with this pivot law absorbs, regardless of the observer laws.

## 3. A uniform strict best reply over every complete observer law

Fix any independent laws of the other two observers. Quitting at date
zero gives observer i at least

    2h-2(1-h)=4h-2=8/5.                               (2)

Indeed the reward is two whenever the pivot stops there, and otherwise
the possible participant rewards are zero, -2, or -1.

For a deadline k>=1, compare pathwise with the clock consisting only of
the pivot. Before k, any observer-only absorption gives i at most zero;
absorption with the pivot while i is absent gives at most one. At k,
joining the pivot gives two, while stopping without the pivot gives at
most zero. Thus the deadline payoff is at most

    Pr(T_0<k)+2Pr(T_0=k)
      =1+(2h-1)s^k
      <=1+(2h-1)s=3h-2h^2=27/25.                       (3)

The comparison is valid for any timing and coincidences of the other
observers. Never gives at most one. Consequently date zero exceeds
EVERY other pure deadline and Never by at least

    gamma=8/5-27/25=13/25>0.                            (4)

Every complete law averages its pure-date and Never responses. Therefore
date zero is a uniformly strict dominant COMPLETE law for each observer.
In particular the fixed-pivot observer-Nash set is globally the singleton

    T_1=T_2=T_3=0 surely.                               (5)

There is no nonzero local feasible direction, no distant alternative
observer equilibrium, and no new-calendar escape with this pivot fixed.

At (5), an observer gets two if the pivot stops at zero and -1 otherwise.
Its prescribed payoff and full cap are 3h-1. The pivot gets one if it
stops at zero and two if it waits; waiting beyond zero gives cap two.
Thus the actual pair is

    U=(11/10,17/10,17/10,17/10),
    B=(2,17/10,17/10,17/10),
    d=(9/10,0,0,0).                                    (6)

## 4. Root inertia and the precise global limitation

At continuation U in (6), let a be the probability that at least one
observer quits in a root. The pivot's Quit endpoint is a, while its
Continue endpoint is 2a+(1-a)U_0, strictly larger. Hence every full Nash
root has q_0=0. Once the pivot continues, write P_1,P_2,H for the
probabilities that respectively one, two, or no other observer quits.
For an observer,

    Q_i=-2P_1-P_2,
    C_i=-P_1+H U_i,
    C_i-Q_i=P_1+P_2+H U_i>0.

Therefore all observers continue too: AllContinue is the unique full
Nash root at U. The root (h,1,1,1) gives a macroscopic incoming collision
realizing (6); all three observers strictly prefer its Quit endpoint.

The point is nevertheless not a global partial-Nash minimum and need
not satisfy all outgoing observer-prefix budgets. Keep observers at
date zero and change the pivot's geometric hazard from 9/10 to 1/2.
The observers' prescribed values become 1/2; their Continue values are
1/2,1/2,-1/2, so every observer remains optimal. Pivot debt becomes
1/2, strictly below 9/10. Small decreases of the hazard already decrease
the debt while preserving strict observer optimality.

There is also an explicit absorbing exact Nash profile: pivot Never,
observer 1 surely at zero, observers 2,3 Never. Its payoff/cap vector is
(2,0,-1,-1). Observer 1 cannot obtain more than its singleton zero;
an outsider gets -1 by continuing and -2 by joining; the pivot gets two
by waiting and one by joining. All complete responses are included.
Thus g=0. Neither root inertia nor this fixed-pivot global trap replaces
the positive-gap and unrestricted minimizing hypotheses.

## 5. An exact cubic bound for approximate observer repairs

The obstruction is quantitative. Let the three observer laws now be
arbitrary, still with the fixed pivot (1). Write N_i for their Never
masses and Y=min(T_1,T_2,T_3), with Y=Never if all three are Never.
Independence gives Pr(Y=Never)=N_1N_2N_3. The pivot's complete cap and
prescribed payoff are exactly

    B_0=2Pr(Y<infinity),
    U_0=(2-h) E[s^Y;Y<infinity].                        (7)

Never attains the cap: any finite deadline replaces a possible reward
two by one at coincidence or zero at an earlier pivot-only stop.
Conditioning on Y=k proves the payoff formula, since the pivot's reward
is one with probability h s^k and two with probability s^(k+1).
Consequently

    d_0>=h(1-N_1N_2N_3).                               (8)

In particular every observer profile with at least one proper observer
law has d_0>=h. Any improvement below h requires positive Never mass in
ALL THREE observer laws.

For observers 1 and 2, Never pays at most one. For observer 3, it pays
at most zero, since every reward received while absent is at most zero.
Combining this with (2), the full observer debts satisfy

    d_1>=(3/5)N_1,       d_2>=(3/5)N_2,
    d_3>=(8/5)N_3.

Substituting into (8) gives the exact unrestricted inequality

    d_0 >= 9/10 - (25/16)d_1 d_2 d_3.                   (9)

Thus even approximate observer repairs cannot buy a first- or second-order
pivot-debt reduction in their errors. This is a fixed-pivot statement,
not a lower bound when the pivot law also changes.

## 6. Exact finite-calendar feasibility with an infinite proper pivot

Here is a general reusable finite system for the proposed computational
route. Fix any native table, a rational geometric pivot hazard h in (0,1),
and prescribed observer dates

    A_H={0,...,H,Never}.

For observer i use variables x_i,a>=0, sum_(a in A_H)x_i,a=1.
For deterministic observer dates (a_1,a_2,a_3), let tau be their first
finite date and S the observers stopping there. The exact payoff
coefficient, integrating the ENTIRE pivot law, is

    C_i(a_1,a_2,a_3)
       =(1-s^tau)Z_i({0})
          +h s^tau Z_i(S union {0})+s^(tau+1)Z_i(S)      (10)

when tau is finite. If every date is Never, it is Z_i({0}). Hence an
observer's pure-response payoff R_i,a is bilinear in the two OTHER
observer probability vectors. Its prescribed payoff is the weighted
average sum_a x_i,a R_i,a, a trilinear polynomial in all three laws.

The COMPLETE observer response menu is represented by

    D_H={0,...,H+1,Never}.                              (11)

After H all other observer laws have only Never remaining. Conditional
on survival, the pivot alone has the same geometric law. For k>=H+1,
the response is therefore a fixed earlier contribution plus a multiple
of

    Z_i({0})+[h Z_i({i,0})-Z_i({0})] s^(k-H-1).

Its supremum is attained at k=H+1 or approached at Never, according to
the coefficient's sign. Thus (11) prices every later finite deadline,
not merely the prescribed dates. For a pivot response against these
observer laws, every date after H has the same value as Never, because
the residual own singleton is zero.

Introduce observer values v_i. Exact observer optimality is the finite
system

    R_i,a<=v_i                  for a in D_H,
    x_i,a(v_i-R_i,a)=0          for a in A_H,
    x_i,a>=0,       sum_a x_i,a=1.                       (12)

On a specified positive support the response equalities and inequalities
are bilinear; the unsplit complementarity equations are trilinear. If
w bounds every pivot response coefficient, minimizing w-U_0 minimizes
the actual pivot debt on this finite-calendar partial-Nash set. The
pivot response and payoff polynomials are trilinear in observer laws.

This system is exact for its stated prescribed support and unrestricted
responses. A local trap in one such system need not persist after adding
new observer dates. The dominance proof in Section 3 is what makes the
present control independent of H and genuinely unrestricted.

## 7. A strict-observer class cannot be an actual global minimum

The control also identifies a useful opposite conclusion once pivot-law
variation is allowed. Suppose an ACTUAL absorbing profile has positive
pivot debt, every observer uses one pure response, and each such response
beats every other pure deadline and Never by a common gamma>0. Then the
profile cannot minimize pivot debt over the full absorbing partial-Nash
carrier.

Choose a finite pivot deadline whose payoff exceeds its prescribed
payoff. Such a deadline exists: if Never is the only apparent improving
response, finite deadlines tend to its payoff by bounded convergence,
using own singleton zero. Mix the pivot's old law with this deadline with
weight eta>0. Its own full cap is unchanged because all observer laws
are fixed, while its payoff strictly increases linearly in eta.

For any observer response, its payoff changes by at most 2M eta, uniformly
over EVERY deadline and Never. The prescribed-versus-alternative gap
therefore falls by at most 4M eta. Taking eta<gamma/(4M) preserves every
observer's strict optimality. Absorption also persists: an absorbing
independent profile has a proper private law; if that law is an observer
it is unchanged, and if only the pivot is proper then its mixture with a
finite deadline remains proper. Thus this is an actual partial-Nash
debt descent.

This elementary class exclusion does not apply automatically to a
nonrealized compact source, to mixed observer supports, or to pure
observers without a uniform response gap. Those are precisely the cases
where a more general repair theorem is needed.

## 8. Verification and next question

Run the exact standard-library checker with
`python math/experiments/CODEX_COLLAPSED_CONSUMER__FIXED_PIVOT_FULL_LAW_TRAP_CHECK.py`.
It constructs all sixty rewards; integrates the infinite geometric pivot
law exactly as in (10); verifies 1320 rational response-coefficient
comparisons on calendars H=0,...,4; checks the source pair; checks (7)--(9)
on 216 independent mixed observer laws; and verifies the explicit
absorbing Nash profile. Its finite tests support the calculations; the
unrestricted conclusion is proved by Sections 3 and 5. The checker passed
again during curation; its bytes were then copied from the original scratch
location without changes. This is not a new mathematical review.

No Lean declaration is claimed for the new control. The literal private
complete-law semantics and full-cap prefix recurrences were inspected in
`quittingTerminalSemanticPair_rootThenContinuation` and
`continuous_quittingTerminalSemanticPrefix`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`).

Freezing a proper pivot law cannot be a general justification for
observer-atom deletion. The next question now uses the global incoming
minimum provenance explicitly, as recorded below.

## 9. Incoming roots pin observer caps: the exact unresolved substitution

This section is an elementary deduction from the full-cap prefix formulas,
not a new counterexample or a claim that the global substitution fails.
Use the carrier and global minimum in
[the incoming-realization note](CODEX_PIVOT_REVIEW__SURE_ROOT_AND_PROPER_LIMIT_REALIZATION.md):

    C_p={X in K:d_i(X)=0 for i!=p},
    m=min_(X in C_p) d_p(X)>0.

Its Section 7 reduces every NONREALIZED global minimum, along a finite
minimum-to-minimum incoming chain, to a nonrealized minimum X_* and a
constant kappa>0 such that every nonzero incoming factorization satisfies

    X_*=prefix_q(Y),       q_i<1 for every i,
    Y in C_p,             D:=d_p(Y)>=m+kappa.            (13)

Such factorizations exist by the incoming collision theorem. The source
theorem also gives a uniform positive lower bound on their joint survival.
Fix one factorization, and put

    H_i=product_(j!=i)(1-q_j)>0,       c=product_j(1-q_j)>0,
    C_i(B)=P_i+H_i B_i,
    R_i(q;B)=max(Q_i,C_i(B))-q_i Q_i-(1-q_i)C_i(B).

Here Q_i and P_i depend only on the reward table and q. The exact full-cap
and debt recurrences are

    B_i(prefix_q(Y))=max(Q_i,C_i(B(Y))),
    d_i(prefix_q(Y))=R_i(q;B(Y))+c d_i(Y).               (14)

Both terms in the debt recurrence are nonnegative. For every observer,
(13)--(14) therefore imply R_i(q;B(Y))=0. Because q_i<1,
Continue is optimal and

    B_i(X_*)=P_i+H_i B_i(Y).                           (15)

If q_i>0, Quit is also optimal, so Q_i=B_i(X_*) and

    B_i(Y)=(Q_i-P_i)/H_i.                              (16)

Thus an active observer pins an EXACT tail cap, not merely its sign.
An inactive observer instead requires C_i(B(Y))>=Q_i.

For any alternative tail Z in C_p, the SAME root q preserves zero
observer debt if and only if

    B_i(Z)=B_i(Y)                   when i!=p and q_i>0,
    B_i(Z)>=(Q_i-P_i)/H_i           when i!=p and q_i=0. (17)

This is an equivalence: with c>0 the observer tail debts already vanish,
and the two conditions are exactly the remaining zero-regret equations.
No comparison of pivot debts implies (17). In particular, replacing Y
by an arbitrary global minimum cannot silently reuse the original root.

There is also an exact quantitative target once (17) is achieved. Suppose
Z is itself a global minimum satisfying (17). Minimality applied to the
new prefix and the old incoming identity gives

    R_p(q;B(Z))+c m>=m=R_p(q;B(Y))+c D,

and hence

    R_p(q;B(Z))-R_p(q;B(Y))>=c(D-m)>=c kappa.           (18)

Conversely, a Z satisfying (17) and violating the first inequality in
(18) would give a strict debt descent in C_p. This is the precise
substitution objective. The pivot root regret is the explicit function

    R_p(q;B)=(1-q_p)(Q_p-C_p(B))_+
                   +q_p(C_p(B)-Q_p)_+,

so its change is bounded by

    H_p max(q_p,1-q_p) |B_p(Z)-B_p(Y)|.                (19)

Every compatible minimum Z must therefore differ from Y in its pivot
cap by at least c(D-m)/(H_p max(q_p,1-q_p)). In the special case q_p=0,
regret is nonincreasing in B_p, and (18) forces the sharper one-sided
condition B_p(Z)<=B_p(Y)-(D-m). These necessary constraints do not
produce a compatible minimum.

The prefix argument uses actual independent product roots and the full
response caps. Applying a fixed finite prefix to Z in K is legitimate:
apply it to actual absorbing profiles approaching Z and pass to the
continuous semantic limit. This does not assert that Z has an actual
realizer, that K is convex, or that convex interpolation of semantic
pairs can be implemented by independent private laws.

Allowing the root q to vary asks for an observer-Nash continuation along
a change of tail. Existence of an observer Nash root separately at each
continuation does not provide a continuous selection from this incoming
root, preservation of macroscopic activity, or the strict pivot estimate
needed in (18). The previously reviewed
[full-law component controls](CODEX_EXPENSIVE_EXIT__FULL_LAW_OBSERVER_COMPONENT_TRAP.md)
rule out a generic connectedness argument without global provenance;
they are not counterexamples at the positive global minimum in (13).

The open question is therefore specific: can the terminal global-minimum
provenance produce a compatible lower-debt tail and root repair with a
pivot-regret increase strictly smaller than the saved continuation debt?
Neither (17) nor such a repair has been established. The strict
tail-debt gap is a genuine source constraint, but this note does not
consume it and does not close Fin4.
