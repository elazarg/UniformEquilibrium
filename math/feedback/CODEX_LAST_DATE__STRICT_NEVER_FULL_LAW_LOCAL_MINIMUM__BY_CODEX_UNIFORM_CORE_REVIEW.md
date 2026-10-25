# Audit of the strict-Never full-law local minimum

Reviewer: CODEX_UNIFORM_CORE_REVIEW. Independent ordinary-mathematical audit.

**Mathematical PASS.** No unresolved mathematical objection. The introductory
scope correctly restricts the local minimum to exact-observer profiles,
while permitting changes of all four complete laws within that constraint.
This is not an export or a Lean check.

Reviewed entire artifact:
[strict-Never full-law local minimum](../notes/CODEX_LAST_DATE__STRICT_NEVER_FULL_LAW_LOCAL_MINIMUM.md),
SHA256 `963eab1126721ff5e857a8f71c832ae7c6b599f19d88f35bc5f579c87d95811c`.
The final status-only change was verified by reconstructing the previously
reviewed source hash; all mathematical bytes are unchanged.

## 1. Complete table and actual unrestricted caps

The row rules assign all nonempty coalition entries without overlap, with
own singletons zero and absolute bound21/10. I checked the complete source
offers by exact rational enumeration. The declared U,B,d and all three
Never gaps27/200 agree. Because every deviator faces another observer
stopping by date1, every deadline>=2 is equivalent to Never; no later
response is lost by the finite calculation. Affinity covers full independent
stopping laws and all behavioral replacements.

## 2. The local parametrization exhausts full-law variations

A sufficiently small total-variation neighborhood retains both positive
atoms0 and1 for each observer. Independent coupling bounds each offer's
change uniformly in its response date by2M times the total opponent
variation. Thus the source's strict late gap survives uniformly over the
infinite menu. An exact observer cannot assign mass to any date>=2 or
Never. Its entire law is therefore supported on{0,1}.

With three observers, every unilateral deviator still faces a different
bounded observer. All pivot law mass after date1 is consequently equivalent
to Never for both prescribed payoffs and every response offer. The variables
q_1,q_2,q_3,t,x exhaust every nearby semantic profile under the exact-observer
constraint; arbitrary infinite pivot tails introduce no missing direction.

The three date indifferences are the stated F_i. Their q-Jacobian is the
cyclic permutation matrix at x=0, so IFT supplies the unique local solution.
The observer row rules and the resulting equations are cyclically symmetric.
Uniqueness therefore gives q_1=q_2=q_3. I checked
this algebra directly; the common-q family is a consequence, not a symmetric
restriction imposed on the permitted variations.

## 3. One-sided constrained minimum

At every local source profile the observers remain proper. The pivot's
Never offer is1 and every payoff when it participates is at most1, so its
full cap is exactly1. Partitioning according to the pivot date and number
of observers quitting gives the exact debt formula(5).

Independent implicit differentiation of(4), rather than treating q as a
constant, gives

    D_t=0, D_tt=69/85, D_x=33/3400, q_x=3/25

at(t,x,q)=(2/5,0,1/2). All signs agree with the source arithmetic.
D_x>0 holds on a neighborhood, so integrating in the physically feasible
direction x>=0 gives D(t,x)>=D(t,0). The strictly positive D_tt and zero
D_t give the local t minimum. This is strict in the effective variables;
flat changes to irrelevant pivot tails are correctly permitted.

The restriction to exact-observer profiles is essential. If q is held
fixed at1/2 while t is decreased, pivot debt decreases linearly, but observer
indifference fails. The theorem does not claim local minimality in that
unconstrained direction.

## 4. Open-table persistence and global comparison

Under small own-zero table perturbations the strict late gaps and both
pivot date0/date1 cap gaps persist. With observer support{0,1}, every later
pivot offer remains its Never offer, so the selected full cap stays smooth.
First solve observer indifferences by IFT, then solve D_t(t,0)=0 using
D_tt!=0. Positivity of D_x and D_tt persists, giving the claimed open
56-dimensional family of constrained local minima. Uniform late-menu
protection still follows from coupling, not from a finite-menu assumption.

The singleton principal determinants, strict inverse column and R0 claim
check exactly. The full determinant is813/1000>0 and the pivot inverse
column is(1/3,1/3,1/3,1/3). At offset -one, positive x0 would force the
observer sum to1 while the sum of their residual inequalities would give
1/10-3x0/10>=3, impossible. With x0=0 every observer's sole positive
incoming coordinate must be positive, forcing full observer support and
the unique solution(0,10,10,10), with outside slack29. Its positive support
determinant gives degree1. These checks are independent of the local IFT
calculation.

The matrix still has a strictly positive-inverse observer child and
exterior inverse row(10,10,10). Hence it is already in a solved singleton
class; the note explicitly acknowledges that overlap. Its positive
inverse-column and degree checks must not be promoted to a claim that it
survives every arbitrary-counterexample source reduction.

The pivot-only date0 profile is an absorbing exact Nash profile: each
observer's joining payoff is11/10 below its passive singleton0 payoff,
and every pivot response yields its own singleton zero. These strict
observer comparisons persist under small own-zero perturbations. Therefore
the global absorbing debt minimum is zero. The example isolates the missing
global argument; it does not provide a positive global minimum, a trapped
whole component, or a counterexample to Fin4.

No source note was edited in this audit, and no Lean build was run.
