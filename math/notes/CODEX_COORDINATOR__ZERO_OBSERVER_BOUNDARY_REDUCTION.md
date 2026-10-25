# Incoming decomposition reaches a zero-observer-cap boundary

Owner: CODEX_COORDINATOR.

## Current best attempt

A complete ordinary-mathematical boundary reduction: incoming decomposition
continues beyond the global minimum fiber and reaches a nonnegative-cap
tail with a zero observer cap. Its pivot debt is uniformly above the global
minimum. Section 3 gives the precise finite/semantic-limit alternatives;
Section 4 disproves unguarded three-player repair of that boundary. Section 5
reduces every one-zero-observer infinite head to a finite prefix followed by
at most two diluted geometric clocks, preserving its complete semantic pair.
Section 6 identifies an all-zero-cap endpoint with the corner at the first
plateau of the Never-penalized value function, linking the two minimum problems.
Section 7 gives a universal observer-END-or-finite-plateau alternative without
requiring a nonrealized minimum or an all-zero incoming tail. It also extends
the strict pivot margin to every positive penalty. At a source-supplied
strict inverse-column pivot, the absorbing alternative strengthens to an
ALL-END minimum with strictly bounded pivot Never mass. The broader
alternative does not retain Section6's actual-head realization. Section 8
consumes an all-zero incoming endpoint of a nonrealized critical minimum:
it forces an ALL-END absorbing global minimum with pivot Never mass zero.

Sections 1--4 passed [independent adversarial review](../feedback/CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION__BY_CODEX_BOUNDARY_ADVERSARY.md)
at the exact version pinned there. Sections 5--6 passed
[two independent reviews](../feedback/CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION__BY_CODEX_GEOMETRIC_REVIEW.md),
including an adversarial check, at the exact version recorded there.
Section7 has separate review records
[here](../feedback/CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION__BY_CODEX_GLOBAL_PLATEAU_REVIEW.md)
and [here](../feedback/CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION__BY_CODEX_GLOBAL_SYSTEMATIC.md),
including the final strict-column strengthening. Section8 has independent
reviews in the latter record and
[here](../feedback/CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION__BY_CODEX_LAST_DATE.md).
This is not a Lean result or an export. Fin4 remains open: neither the
actual-minimum branch nor a repair that uses the boundary tail's
global-minimum ancestry is resolved.

Let I be any finite player set with at least two players. Each privately
and independently chooses a complete law on the natural dates and Never.
The first nonempty quitting coalition S pays Z(S); AllNever pays zero.
Assume Z_i({i})=0 and |Z_i(S)|<=M, where M>=1. A unilateral replacement
may use ANY complete law, including every deadline and Never.

Let U denote prescribed payoff, B the full response supremum, d=B-U,
and K the compact closure of actual absorbing pairs (U,B). Fix a pivot p,
put C_p={X in K:d_i(X)=0 for i!=p}, and suppose C_p is nonempty with
m=min_Cp d_p>0. Assume EVERY global minimum has positive observer caps.
For generic hypothetical Fin4 counterexamples, these assumptions are
supplied by the [global absorbing source theorem](CODEX_EXPENSIVE_EXIT__ABSORBING_PARTIAL_NASH_MINIMUM.md).
The argument below does not otherwise use the number four.
Define the compact boundary

    F={Y in C_p: B_i(Y)>=0 for every i, min_(i!=p)B_i(Y)=0}.

If X is a nonrealized global minimum, F is nonempty and there are finite
product-root words w_n and points Y_n in C_p with X=Phi_(w_n)(Y_n), such
that either a finite Y_n lies in F, or one nested sequence has

    Y_n -> Y_infinity in F,
    sum_t sum_i q_(t,i)<infinity,
    c_infinity=product_t product_i(1-q_(t,i))>0,
    X=lim_n Phi_(w_n)(Y_infinity).

In the infinite case every finite descendant is nonrealized, but its limit
need not be. The last equality is a semantic limit of finite prefixes,
NOT an executable continuation placed after infinitely many dates.
Moreover kappa_F=min_F d_p-m>0, so the boundary tail has pivot debt at least
m+kappa_F. This is a uniform table/pivot boundary gap, not a solution of Fin4.

## Exact prefix formulas

For a root q write ell(q)=sum_i q_i, H_i=product_(j!=i)(1-q_j),
c=product_i(1-q_i). Q_i is the forced-Quit endpoint and P_i the passive
payoff on nonempty opponent coalitions. Then

    U'_i=q_i Q_i+(1-q_i)P_i+c U_i,
    B'_i=max(Q_i,P_i+H_i B_i),
    d'_i=R_i(q;B)+c d_i,
    R_i=max(Q_i,C_i)-q_i Q_i-(1-q_i)C_i>=0,
    C_i=P_i+H_i B_i.

Finite prefixing preserves K by applying the same word to absorbing
approximants. The [realization theorem](CODEX_PIVOT_REVIEW__SURE_ROOT_AND_PROPER_LIMIT_REALIZATION.md),
Sections 2--3 and 7, proves the two facts used below: a sure incoming root
realizes its entire pair; a vanishing-survival exact chain from a GLOBAL
C_p minimum realizes that minimum. Both facts apply to any finite I.
Neither asserts realization for an arbitrary vanishing-survival cap chain.

## 1. Positive observer caps give an incoming word of length at most two

For an observer i write Gamma_ip=Z_i({p}) and J_ip=Z_i({i,p}).
For arbitrary X in C_p with mu=min_observer B_i(X)>0, put

    delta=min(1/8,mu/(64M)).

There is an exact incoming word of length one or two, with total root
activity at least delta/2. A root in the word may be zero. Its first root,
when present as a compressed head, has only the pivot active. This assertion
uses neither minimality nor a pivot-cap/payoff sign assumption.

Choose absorbing approximants X_n -> X, with all conditional hazards <1,
and epsilon_n=sum_observer d_i(X_n)->0. Mix each private law with a
vanishing amount of a fixed proper geometric law to arrange the hazard
condition. Total-variation continuity preserves every payoff and full cap;
an originally proper private law stays proper, so absorption persists.

The small-root cap bootstrap uses only the observer margins: on any initial small-root segment with
each ell(q)<delta and total ell<=2delta, observer caps stay above mu/2,
Continue is the cap branch, and observer root regret is >=(mu/2)q_i.
Joint survival throughout is >=1-2delta>=3/4. Hence its total observer
hazard A_n obeys

    A_n<=8 epsilon_n/(3mu) ->0.

Indeed |Q_i|<=M ell. While the current cap exceeds Q_i, Continue attains
it and the next cap differs by at most 2M ell. Starting with cap errors
at most mu/8, the cumulative movement is at most 4M delta. The definition
of delta thus keeps Continue strictly above Quit by at least mu/2,
closing the bootstrap and the displayed regret estimate.

There is either a first root of activity >=delta before cumulative small
activity reaches delta, or a first small-root segment whose cumulative
activity reaches delta. This segment exists: bounded total hazard <delta
with every root small would leave positive joint survival, contrary to
absorption.

In the crossing case the segment has total activity in [delta,2delta).
In the early-macroscopic case take the segment strictly before that root;
its total activity is <delta. Extract the conditional semantic pair Z_n
immediately after this segment. Survival >=3/4 and nonnegative debt
recursion imply Z_n has observer debts tending to zero; after subsequence
Z_n -> Z in C_p.

Set t_n=1-product_(segment)(1-q_(n,p)), the pivot's head quitting mass.
Delete every observer hazard in this finite head, leaving all tail laws
unchanged. A complete-law coupling fails with probability <=A_n, so EVERY
prescribed or unilateral response payoff changes by at most 2M A_n.
Full caps therefore change by the same bound. This is uniform over all
response laws, not merely finitely many deadlines.

Pass to t_n ->t. If the segment is nonempty, its pivot-only replacement
has exact identities

    U_p(X)=(1-t)U_p(Z),          B_p(X)=max(0,B_p(Z)),
    U_i(X)=t Gamma_ip+(1-t)U_i(Z)                 (i!=p).

The pivot cap has the zero floor because quitting before the tail earns
own singleton zero. Since both X and Z have zero observer debts,

    B_i(X)=t Gamma_ip+(1-t)B_i(Z)                (i!=p).

Replace the entire head by the single literal root q=t e_p. Its observer
Quit endpoint is t J_ip<=2delta M<mu, below the displayed Continue value
B_i(X). It consequently preserves ALL observer caps and payoffs, as well
as the exact pivot formulas. Thus X=prefix_(t e_p)(Z).

The root MUST be retained when t=0 if the approximating head was nonempty:
prefix_0 clamps negative caps to zero and is not generally the identity.
For a head that is actually empty, omit the compressed root. Pass to a
subsequence distinguishing the empty and nonempty cases.

In the crossing case A_n->0 and total activity >=delta give

    t>=1-exp(-delta)>=delta/2.

So this one compressed root already gives the required activity. In the
early-macroscopic case, compactness also extracts the next root q with
ell(q)>=delta and its tail Y in K, yielding Z=prefix_q(Y). Compose with
the optional compressed pivot root. This gives at most two roots and
the required activity even if t=0. Each exact intermediate point is in
C_p when the word survival is positive, by nonnegative debt recursion.
No unsupported single-nonzero-root conclusion is needed.

## 2. Any negative cap gives an immediate macroscopic incoming root

For any X in C_p with B_k(X)=-nu<0 (k may be the pivot), take initial
roots and their conditional absorbing tails along the same approximants.
Compactness gives X=prefix_q(Y). Since

    B_k(X)>=Q_k(q)>=-M sum_i q_i,

one has ell(q)>=nu/M>0. This argument does not require positive observer
caps. If c(q)>0, zero observer output debts force Y in C_p and zero root
regret for every observer.

## 3. Iteration and convergence to the boundary

Start from the nonrealized global minimum X. Whenever all observer caps
are positive, use Section 1. Otherwise, if some cap is negative, use
Section 2. If neither condition holds, the current point lies in F.

Every root in every chosen finite word is nonsure: a sure root would
realize its output pair by the scalar-cap/sure-root realization theorem,
and preceding finite prefixes would realize X. Every conditional pair
therefore lies in C_p. No finite descendant is actually realizable,
for the same finite-prefix reason.

If iteration never stops, flatten the selected words into roots q_t and
conditional pairs X_t, with X_0=X and

    X_t=prefix_(q_t)(X_(t+1)).

If joint survival tended to zero, the existing global-minimum unrolling
argument would realize X: actual payoffs are recovered, actual caps are
no larger, zero observer debts force their equality, and global minimality
forces pivot-cap equality. Thus its survival limit is strictly positive,
which implies sum_t ell(q_t)<infinity.

For every coordinate the payoff recursion gives

    |U_i(X_t)-U_i(X_(t+1))|<=2M ell(q_t).

Also B_i(X_t)>=Q_i(q_t)>=-M ell(q_t). The cap recursion and the estimate
|P_i+H_i B_i-B_i|<=2M ell(q_t) yield

    |B_i(X_t)-B_i(X_(t+1))|
      <=2M ell(q_t)+(-B_i(X_(t+1)))_+
      <=2M ell(q_t)+M ell(q_(t+1)).

Both coordinate sequences are Cauchy. Their limit Y_infinity belongs to
C_p, and all limiting caps are nonnegative. If its observer caps
were all positive, Section 1 would eventually choose words with a fixed
positive activity lower bound, contradicting summability. Thus
Y_infinity lies in F.

Every finite prefix is 1-Lipschitz in the supplied semantic pair in the
sup norm: payoffs have coefficient c<=1 and each cap is a maximum of a
fixed head value and an affine tail-cap term with coefficient H_i<=1.
Consequently

    ||Phi_(w_n)(Y_infinity)-X||
      <=||Y_infinity-Y_n|| ->0.

Finally F is compact and disjoint from the global minimum fiber by its
positive-observer-cap hypothesis. It is nonempty by the construction.
Thus min_F d_p exists and is strictly greater than m.

The infinite case also retains a concrete comparison operator. Let P be
the ACTUAL nonabsorbing profile using q_t on the natural dates, let N_i
be its Never masses, s=product_i N_i>0, h_i=product_(j!=i)N_j, and e_i
its pure-Never response payoff. The finite-prefix maps converge uniformly
on K to

    Phi(Z).U_i=U_i(P)+s U_i(Z),
    Phi(Z).B_i=max(B_i(P),e_i+h_i B_i(Z)).

Indeed prescribed and passive head payoffs converge by bounded convergence,
survival products converge, and the maximum over finite head deadlines
increases to B_i(P); own singleton zero makes Never the limit of those
deadline responses. The tail coefficients are bounded, giving uniform
convergence. Thus Phi(K) is contained in K and Phi(Y_infinity)=X.
For Z in C_p with the SAME observer caps as Y_infinity, the output observer
pairs are unchanged. Global minimality of X therefore makes Y_infinity a
global minimizer, on that slice, of

    max(B_p(P),e_p+h_p B_p(Z))-s U_p(Z).

This is the inherited minimum property at the boundary. It is not
minimization of d_p there, nor an execution of P followed by a tail at omega.

In the infinite case, any observer with B_i(Y_infinity)>0 has q_(t,i)=0
for all sufficiently large t. Otherwise zero observer root regret gives
B_i(X_t)=Q_i(q_t) at infinitely many active dates, whereas the left side
has positive limit and |Q_i(q_t)|<=M ell(q_t)->0. Thus only the pivot and
zero-cap observers can act arbitrarily late in the selected head. With
exactly one zero observer there are at most two such owners. This does
not restrict the strategy support of the abstract boundary tail itself.

## Scope and overlap

The [earlier incoming-collision theorem](CODEX_OBSERVER_PATH__GLOBAL_MINIMUM_INCOMING_COLLISION.md) applies only to a global minimum
with positive pivot payoff and observer caps. Its uniform lower tail-debt
estimate suppresses the compressed solo-p prefix. Here the two-root
replacement applies OFF that minimum fiber, permitting iteration through
higher-debt tails. The previously retained terminal minimum/tail-gap
selection remains valid, but iteration need not halt there solely because
the next debt exceeds m.

This does not construct a compatible minimum tail, make any cap zero at
the original minimum, produce an actual zero-cap tail at a finite date,
or solve the outsider guard needed for a three-player reduction. Zero
observer cap does not imply that Never is that observer's best reply.

Inspected source formulas: `quittingTerminalSemanticPrefix` and
`quittingTerminalSemanticPair_rootThenContinuation`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`), and
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`). The semantic
endpoint inspected was
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
These existing formulas do not themselves prove the new boundary reduction.
No Lean command ran.

## 4. Zero-cap and Never optimality do not justify three-player repair

Use players 0,1,2,3, pivot 0, and own-singleton/live/AllNever reward zero.
For every nonempty coalition S specify all sixty coordinates by

    Z_0(S)=2 if 1∈S and 0∉S; 1 if 0,1∈S; 0 otherwise.
    Z_1(S)=1 if 0∈S and 1∉S; 2 if 0,1∈S; 0 otherwise.
    Z_2(S)=0 if 2∈S;
           1 if 2∉S and {0,1}⊂S;
          -1 otherwise.
    Z_3(S)=1 if 3∉S; 0 otherwise.

The source has player 0 use a proper geometric law of hazard 1/2 at every
natural date, player 1 Quit at zero, and players 2,3 Never. It absorbs at
zero, and its complete payoff and cap vectors are

    U=(3/2,1,0,1),   B=(2,1,0,1),   d=(1/2,0,0,0).

For player 0, Never obtains 2 and no response exceeds 2. For player 1,
Quit at any finite k gives Pr(T_0<k)+2 Pr(T_0=k)=1; Never gives 1.
Player 2's Quit0 payoff is 0; every positive finite deadline and Never
averages +1 and -1 with equal probabilities, hence is also 0. Player 3's
Never payoff is 1, the maximal reward. Thus ALL pure deadlines and Never
are priced, and mixing cannot increase a cap. In particular observer 2
has zero prescribed payoff, zero cap, and a best-reply Never action; all
other caps and the pivot payoff are strictly positive.

Now delete player 2 and consider ANY independent profile rho in the
remaining three-player game. Let J be the probability that the first
finite quitting coalition contains both 0 and 1, and let nu be the
probability of AllNever. Coupling player 0's actual clock with its Never
replacement gives a pointwise nonnegative gain. The gain is exactly 1 on
every first-coalition event containing both 0 and 1. If player 0 stopped
alone before player 1, Never can only improve its zero reward; first
coalitions omitting 0 give the same reward under this replacement.
Therefore player 0's full debt is at least J.

If rho is epsilon-Nash (all complete unilateral improvements at most
epsilon), J<=epsilon. Restoring player 2 at Never gives

    U_2(Never,rho)=2J-(1-nu)<=2 epsilon-1+nu.

Its Quit0 reply always gives 0, because every coalition containing 2 pays
it 0. Consequently its unrestricted deviation gain is at least

    1-nu-2 epsilon.

For absorbing epsilon-Nash profiles the bound is 1-2 epsilon. It is
uniform over ALL selected approximate equilibria of the deleted game,
including infinite supports and arbitrary calendars. Thus even zero-cap
AND Never-best-reply source data do not license three-player repair of the
remaining laws; every nearly absorbing accurate repair loses the outsider
incentive by a fixed amount.

The full four-player game is solved: let players 1 and 2 Quit0 and let
0 and 3 Never. Payoffs are (2,0,0,1); every full cap equals that payoff.
Hence this control cannot exclude a global-minimum-derived zero face. Any
successful consumer must use that additional global source ancestry.

## 5. One zero observer: at most two geometric clocks after a finite prefix

Joint argument with CODEX_BOUNDARY_CONSUMER_24. This is an exact head
representation theorem, not a boundary repair or a reward-table exclusion.
It applies to any finite I; no genericity assumption is needed.

Suppose the infinite alternative in Section 3 has exactly one zero-cap
observer i at Y=Y_infinity. Then the SAME pair X has a representation

    X=Phi_w(Phi_Q(Y)),

where w is a finite word and only p and i can act in Q. Each nonempty
finite part in Q is a diluted geometric law

    Pr(T_k=t)=f_k theta_k(1-theta_k)^t,
    Pr(T_k=Never)=1-f_k,     0<f_k<1, 0<theta_k<=1.

At most two such clocks are needed. The other head laws are Never.
If B_p(Y)>0, one can arrange that only p acts in Q. If B_p(Y)=0, two
clocks are needed only in the case analyzed below where the pivot's
Never response is cap-active at every sufficiently late original cut.
An empty Q or theta=1 is allowed. The tail Y is unchanged and remains
abstract: Phi_Q(Y) is the limit of finite prefixes, not play after omega.

### 5.1. Outcomes and finite moment replacement

Pass beyond the last activity of every positive-cap observer. Write
alpha_t,beta_t for the conditional finite masses of p,i in the remaining
head, f_p=sum alpha, f_i=sum beta, N_k=1-f_k, and s=N_p N_i. These finite
masses can be made arbitrarily small by taking a late cut. Let a,b,c be
the probabilities of first coalitions {p},{i},{p,i}, respectively. Put

    R_p(t)=sum_(u>=t)alpha_u,   R_i(t)=sum_(u>=t)beta_u,
    c=sum_t alpha_t beta_t,
    v=sum_t beta_t R_p(t),
    a=f_p-v,   b=N_p f_i+v-c.

Thus f_p,f_i,v,c determine every prescribed payoff with the same tail Y.
Set G=Z_i({p}), J=Z_i({p,i}), A=Z_p({i}), C=Z_p({p,i}). Zero observer
debt and N_i>0 force i's Never-through-head branch to attain its cap:

    B_i=G f_p,
    G R_p(t)>=J alpha_t for every t,
    G R_p(t)=J alpha_t whenever beta_t>0.             (5.1)

Indeed all head deadlines have value at most the cap, while the prescribed
payoff averages them and the tail option G f_p with strictly positive
weight N_i. Tail i payoff and cap are both zero. Equality of payoff and
cap forces equality for that option and every supported deadline.

Holding p fixed, any remaining i mass after a finite date can be placed
on at most THREE of its old support dates, preserving its mass and the
two moments (alpha_t,R_p(t)). This preserves a,b,c,s and i's cap. To see
exact finite representability, a countable mean of a bounded subset of
R^d belongs to its convex hull: if the mean is on a proper supporting
face of the closed convex hull, every positive-weight point lies on that
face, reducing dimension. Otherwise it is in the relative interior,
which equals the relative interior of the convex hull itself. Induction
and the finite-dimensional Caratheodory theorem give at most d+1 points.
Apply this with d=2. No limiting date or extra Never atom is used.

The same construction compresses p while holding i fixed, preserving
f_p and the moments (beta_t,R_i(t)). In that case

    v'=sum_t alpha_t R_i(t),
    a=N_i f_p+v'-c,   b=f_i-v'.

These operations retain each owner's original Never mass. Moving finite
mass z changes every response against that owner by at most 2Mz, uniformly
over all complete response laws.

For any positive-cap observer j, every finite head deadline has absolute
payoff at most M(f_p+f_i). Its Never-through-head cap is within
2M(f_p+f_i) of B_j(Y)>0. For a sufficiently late initial cut the latter
is strictly higher, uniformly over ALL redistributions preserving f_p,f_i.
It equals j's prescribed payoff because its tail debt is zero. The same
buffer applies to p when B_p(Y)>0; its cap is then

    A f_i+N_i B_p(Y).                                (5.2)

### 5.2. Positive pivot cap, or a strict finite pivot cap

If B_p(Y)>0, compress i using the three-point construction. All payoffs,
i's cap, the positive observer caps, and (5.2) are preserved exactly.
The earlier finite prefix therefore still gives X. After i's last atom
only p acts; Section 5.3 handles this suffix.

If B_p(Y)=0, the pivot's semantic head cap equals its actual head cap.
Its Never value is A f_i. If at a sufficiently late cut its cap b_p
strictly exceeds A f_i, deadline values converging to A f_i show that
b_p has a finite attainer. Keep a finite prefix containing that attainer.
Choose a later R so all old deadlines at or after R are below b_p by a
fixed margin, and 2M times i's remaining finite mass is smaller than that
margin. Compress only that remaining i mass. Earlier deadlines, including
the attainer, are unchanged; all later deadlines stay below b_p; Never
is unchanged. The entire semantic pair is again preserved. This leaves
only the case where pivot Never is cap-active at every sufficiently late
cut, treated in Section 5.4.

### 5.3. A solo suffix needs at most one geometric clock

After the last i atom, take a further cut so the remaining finite mass
satisfies the positive-observer buffers. Suppose only p acts there, with
finite mass f>0. Its cap
is B_p(Y)>=0, and its payoff is (1-f)U_p(Y). Exact i best response is

    G R(t)>=J alpha_t for every t,    B_i=G f.        (5.3)

If J<=G, putting all f at the first date preserves (5.3), all payoffs, and all
caps. If J>G, feasibility of (5.3) forces G>0: G=0,J>0 forbids atoms,
and for G<0 the inequality is impossible at any positive atom when
J>G. Thus J>G>0, and the diluted geometric law with rate theta=G/J
satisfies (5.3) with equality at every date. It preserves every outcome
probability. The positive observer buffers remain valid. No finite law
with f>0 can satisfy (5.3) in this strict-premium case, since its last
atom has R(t)=alpha_t and would require J<=G.

The identical argument handles a solo-i suffix with pivot tail cap zero
and pivot Never optimal: replace (G,J) by (A,C). Observer i's own cap and
payoff stay zero. Thus this suffix is one root when C<=A, or a diluted
geometric clock with rate A/C when C>A>0; the other nonempty cases are
infeasible. Throughout, earlier finite queries are retained by preserving
the ENTIRE pair at the replaced cut, not merely its prescribed payoff.

### 5.4. Zero pivot cap and a persistent Never optimum

Choose a late cut with the positive-observer buffers. In addition to (5.1),
pivot Never optimality says

    B_p=A f_i,    A R_i(t)>=C beta_t for every t.     (5.4)

If either finite mass is zero, Section 5.3 suffices. Assume f_p f_i>0.
If G=0, (5.1) forces J<=0. Compress p to three old support dates using
Section 5.1. Its cap is independent of its own law. Observer i's cap stays
zero against ANY new p law because J<=0 and G=B_i(Y)=0; its payoff is
preserved by the outcome moments. All positive observers keep their
buffer. After the last p atom the remaining solo-i suffix is handled
by Section 5.3. This includes G=J=0 and requires no division by G.

Suppose G!=0. If c=0, (5.1) implies R_p(t)=0 at every i support date.
All p atoms therefore precede the first i atom, and p has finite support.
Keep that finite prefix and replace the remaining solo-i suffix. This
does not assume a first or last atom for an infinite p law: their existence
here follows from the displayed strict ordering and f_i>0.

It remains that G!=0 and c>0. A contact with alpha_t beta_t>0 gives

    r=G/J in (0,1],    v=c/r,
    a=f_p-c/r,    b=N_p f_i+(1/r-1)c.

Write k=c/(f_p f_i). Since R_p(t)<=f_p, (5.1) gives 0<k<=r.
Multiplying (5.4) by alpha_t and summing gives the additional inequality

    [C+A(1/r-1)] k<=A,                              (5.5)

because sum_t alpha_t R_i(t)=f_p f_i-(1/r-1)c.
Define

    u=k r/[r-k(1-r)] in (0,1].

Replace the two head laws by diluted geometrics with respective masses
f_p,f_i and rates r,u. Their tie probability is exactly

    f_p f_i r u/(r+u-r u)=c.

Every i deadline now ties with Never, since alpha_t=r R_p(t) and Jr=G.
Moreover (5.5) is EXACTLY C u<=A: multiply by the positive denominator
r-k(1-r). Thus every pivot deadline is at most its Never value, since

    deadline_p(t)=A f_i+(C u-A)R_i(t)<=A f_i.

Both full caps, all outcome probabilities, and all positive observer caps
are preserved. This proves the two-clock representation without any sign
restriction on G,J,A,C or any finite-support assumption on the old head.

For this final two-clock block its pivot debt has the explicit form

    d_p(Phi_Q(Y))
      =N_p N_i d_p(Y)+f_p f_i r(A-C u)/(r+u-r u).     (5.6)

The second term is nonnegative by (5.5); it vanishes when C u=A.
Here B_p(Y)=B_i(Y)=0 and U_p(Y)=-d_p(Y)<0. Formula (5.6) does not by
itself give descent: Y has larger debt than the original minimum, and
changing its head moments can destroy the earlier prefix's observer
equalities. The other open cases are actual global minima and boundary
tails with two or more zero observer caps. No new equilibrium class is
claimed by this representation theorem.

## 6. An all-zero-cap endpoint forces a finite penalty plateau

Joint argument with CODEX_MULTIPLE_ZERO_CONSUMPTION_25. This identifies
additional global ancestry, not a contradiction or a new equilibrium class.
It applies to the same finite-player setup; review is linked above.

Let H be the compact closure of ALL actual tuples (U,B,N,e), retaining
original marginal Never masses N and pure-Never response values e. Put

    nu=product_i N_i,   C={Q in H: d_i(Q)=0 for i!=p},
    f(r)=min_(Q in C)[d_p(Q)+r nu(Q)],      r>=0.

Suppose Section 3 sends a NONREALIZED global C_p minimum X to an endpoint
Y in C_p with EVERY cap zero. Write lambda=d_p(Y), so U(Y)=-lambda e_p, where
e_p here denotes the coordinate unit vector, and m<lambda<=M. Let P be
the actual incoming head: the finite word followed by Never, or the
infinite head in Section 3. In both cases nu(P)>0 and X=Phi_P(Y).

Then P is an ACTUAL global minimizer of f(lambda)=m, and

    f(r)<m for 0<=r<lambda,     f(r)=m for r>=lambda,
    f'_+(lambda)=0,             f'_-(lambda)>=nu(P)>0.       (6.1)

Thus lambda is the first finite plateau parameter and a nondifferentiable
corner. All all-zero-cap endpoints produced by Section 3 at this fixed
table and pivot have the SAME debt lambda, regardless of the selected
minimum, incoming head, or calendar. There is no assertion that other
boundary endpoints have the same debt, or that the corner is impossible.

### Zero Never mass and concatenation

The projection of {Q in H:nu(Q)=0} onto (U,B) is exactly K. One inclusion
follows by augmenting any absorbing realizing sequence and extracting its
bounded N,e coordinates. Conversely, for actual Q_n tending to Q with
nu(Q)=0, the least Never mass tends to zero, since

    min_i N_i(Q_n)<=nu(Q_n)^(1/|I|).

Move that mass to a finite date. The new profile absorbs, and coupling
changes every payoff and full cap by at most 2M times the moved mass.
Its pair still tends to Q's pair. Observer debts need only tend to zero;
no exact observer repair is being inferred. Consequently

    min_(Q in C,nu(Q)=0)d_p(Q)=m,       f(r)<=m for all r>=0. (6.2)

For EVERY Q in H, K contains the pair

    U'=U(Q)+nu(Q)U(Y),
    B'_i=max(B_i(Q),e_i(Q)+h_i(Q)B_i(Y))=B_i(Q),
    h_i(Q)=product_(j!=i)N_j(Q).                           (6.3)

To construct it, approximate Q by actual heads, censor their sufficiently
small finite tails to Never, and append an empty FINAL head date. That
date makes the old Never response available as a finite query without
changing the head's cap. Append an absorbing approximant of Y after this
finite head. The exact concatenation formula prices all old and new
responses. Uniform total-variation bounds and a diagonal limit give
(6.3) in K. The last equality uses B(Y)=0 and B_i(Q)>=e_i(Q), which holds
on H. No abstract head is executed before a tail at an infinite date.

Equation (6.3) preserves every observer debt and gives pivot debt
d_p(Q)+lambda nu(Q). For Q in C, global minimality therefore gives
f(lambda)>=m. For the supplied actual head P equality holds, and its
observer debts equal those of X. Thus

    f(lambda)=m=d_p(P)+lambda nu(P),
    0<nu(P)<=m/lambda<1.                                 (6.4)

### The forced corner

The minimum of affine functions with slopes nu in [0,1] is nondecreasing,
concave and 1-Lipschitz. For r<lambda, comparing with P gives

    f(r)<=m-(lambda-r)nu(P)<m.

For r>=lambda, monotonicity and (6.2) give f(r)=m. The right derivative
is zero; the displayed left secant bound and concavity give (6.1).
At the corner an actual positive-Never minimizer coexists with zero-Never
minimizing carrier points. This is the new source link; the general
envelope calculus is already in the
[penalty-transition note](CODEX_SOURCE_ESCAPE__CONSTRAINED_PENALTY_TRANSITION_BOUNDARY.md),
Section 3. Its existing bounds do not rule out such a corner. No converse
from a penalty plateau to an all-zero-cap incoming tail is proved here.

## 7. A universal observer-END-or-finite-plateau alternative

Joint derivation with CODEX_GLOBAL_SELECTION_CREATIVE. This section uses a
fixed native own-zero FIN4 table and its unrestricted actual-law carrier.
It drops the earlier assumptions that the selected minimum is nonrealized
or that an incoming boundary tail has all caps zero. It does not eliminate
either new alternative or claim an actual realization of a semantic point.

Retain H,C,nu,f from Section6 and set

    C0={Y in C:nu(Y)=0},
    m=min_(Y in C0)d_p(Y)>0,
    M0={Y in C0:d_p(Y)=m}.

Assume C0 is nonempty. These hypotheses follow from a positive native
absorbing gap. The global absorbing source theorem also supplies

    B_p(Y)>m at every Y in M0.                         (7.1)

The source theorem is proved in
[the absorbing partial-Nash note](CODEX_EXPENSIVE_EXIT__ABSORBING_PARTIAL_NASH_MINIMUM.md).
Its strict pivot conclusion needs no positive observer-margin assumption.
The properification argument of Section6 identifies C0 with the augmented
absorbing slice: moving a least marginal Never mass to a finite date changes
every prescribed and response payoff, including e, by a quantity tending to
zero, and changes that marginal N by the same vanishing mass.

For every actual law and therefore throughout H,

    d_i>=N_i(B_i-e_i)>=0.                             (7.2)

Consequently every point of C with nu>0 is observer-END, meaning B_i=e_i
for all i!=p. Let E denote this closed subset of C.

**Universal alternative.** At least one of the following holds:

- Some absorbing global minimum in M0 belongs to E.
- There are a finite lambda_*>m and Y_* in C with nu(Y_*)>0 such that

      f(r)<m for 0<=r<lambda_*,
      f(r)=m for r>=lambda_*,
      d_p(Y_*)+lambda_* nu(Y_*)=m.                    (7.3)

  Thus Y_* and EVERY point of M0 are global minimizers at the same critical
  parameter. Y_* is observer-END, but may be only a semantic limit.

The alternatives need not be disjoint. When the first fails, all critical
minimizers with positive Never have a common positive Never lower bound.
If p is a strict inverse-column pivot, the positive-Never critical point in
the second alternative has ALL caps END-active, including the pivot.

### Producing the transition from failure of the first alternative

If M0 misses E, there is epsilon>0 such that

    Y in C, nu(Y)>0, d_p(Y)<m  implies nu(Y)>=epsilon. (7.4)

Otherwise take such points with nu tending to zero. They belong to E by
(7.2). Compactness gives a limit in C0 with debt at most m, hence in M0
intersect E, a contradiction.

AllNever belongs to C with debt0 and nu1. Define

    lambda_*=max_(Y in C,nu(Y)>0) (m-d_p(Y))_+/nu(Y).  (7.5)

Every positive ratio comes from (7.4), so this is a finite attained maximum
of a continuous function on the compact set nu>=epsilon. Its value is at
least m by AllNever. A maximizer Y_* has positive ratio and positive nu.
Formula(7.5) gives d_p+lambda_*nu>=m throughout C, with equality at Y_*
and every point of M0. For r<lambda_*, comparison with Y_* gives

    f(r)<=m-(lambda_*-r)nu(Y_*)<m.

For r>=lambda_*, monotonicity and comparison with M0 give f(r)=m.
This proves the transition, with lambda_*>m established below. Concavity
of the compact affine envelope also gives

    f'_+(lambda_*)=0,
    f'_-(lambda_*)=max_{critical minimizers}nu>=nu(Y_*)>0. (7.6)

The lower bound in(7.4) applies to every positive-Never critical minimizer,
since its debt is m-lambda_*nu<m. There is no claim that these minimizers
are actual clocks or share one calendar with an absorbing minimum.

### Strict pivot margin for EVERY positive penalty

For any fixed r>0 write mu=f(r). Compactness gives mu>0: a zero minimum
would have both d_p=0 and nu=0, contrary to m>0. Also mu<=m. At a
minimizer Y, every observer-Nash root q at B(Y) has, with c=product(1-q_i),

    J_r(Y')=R_p(q;B)+c mu,
    R_p(q;B)>=mu(1-c).                              (7.7)

The exact finite-prefix formulas prove this at semantic points as before.
Take an exact finite Nash root at continuation B-a e_p, where e_p now
denotes the coordinate unit vector and a>=0. Its observers are unchanged
and its pivot regret at B satisfies R_p<=a q_p H_p. For a<mu, (7.7)
forces q=0. AllContinue being Nash then implies B_i>=0 for every observer
and B_p>=a. Letting a increase to mu yields B_p>=mu.

On the critical face B_p=mu, any zero-cap observer i must have

    Delta_ip=Z_i({i,p})-Z_i({p})<=0.                 (7.8)

Indeed, use a=mu+eta. Its pivot continuation is -eta, so q_p>0, and the
same budget gives q_j<=(eta/mu)q_p for all observers j. For eta<mu these
observers are nonsure and must have nonpositive Quit-minus-Continue gaps.
If B_i=0 and Delta_ip=D>0, the event that neither other observer quits
contributes q_p D. The remaining events cost at most2M each, giving

    gap_i>=q_p[D(1-2eta/mu)-4M eta/mu]>0

for small eta, a contradiction. This retains the q_p factor throughout;
no lower bound on the selected root hazard or cap attainment is assumed.

Consider K_r={Y in C:J_r(Y)=mu,B_p(Y)=mu}. It contains no zero-Never point:
such a point would have d_p=mu<=m, hence mu=m and Y in M0, contradicting
(7.1). If K_r were nonempty, choose a point with least N_p>0 on this compact
face. By (7.8), a sufficiently small solo-pivot prefix of hazard t>0 is
observer-Nash, since its observer gaps are

    t Delta_ip-(1-t)B_i<=0.

Its pivot cap stays mu and its pivot root regret is t mu. Formula(7.7)
therefore leaves J_r=mu, while N_p becomes (1-t)N_p. This contradicts its
choice on the SAME face. Thus for every r>0 and every minimizing Y,

    B_p(Y)>f(r),       U_p(Y)>r nu(Y).                (7.9)

This extends the old r<A restriction: the new argument uses the absorbing
strict margin (7.1) to remove zero-Never points from the critical face,
instead of requiring a Never collar on the entire minimizing set.
At continuation B-f(r)e_p every exact Nash root is AllContinue: (7.7)
first forces all observers to Continue, and (7.9) forces the pivot too.

If lambda_*=m, AllNever would minimize J_m with cap B_p=0, contradicting
B_p>=f(m)=m. Hence lambda_*>m as asserted.

### The critical point is all-END at a strict inverse-column pivot

Suppose v=Gamma^(-1)e_p>0, and put S=sum_i v_i, k=S-v_p>0. The existing
inverse-axis construction in
[the constrained-repair proof](CODEX_VARIATIONAL_ESCAPE__CONSTRAINED_REPAIR_AND_CONE_GRAFT_OBSTRUCTION.md),
Section2, supplies semantic tails Q_T with all observer U=B=e=0 and

    b(T)=B_p(Q_T)=e_p(Q_T)=(1-exp(-kT))/k,
    u(T)=U_p(Q_T)=(1-exp(-ST))/S,
    N_i(Q_T)=exp(-v_i T).

Independent fine discrete clocks, an empty final head query and diagonal
limits give these tails and their grafts in H. The empty query retains
the old END cap; no continuous-time law or continuation after infinity is
executed. Grafting Q_T onto an old positive-Never point preserves every
observer payoff and cap and changes the pivot coordinates by

    U_p'=U_p+nu u(T),
    B_p'=max(B_p,e_p+(nu/N_p)b(T)),
    nu'=nu exp(-ST).                                (7.10)

At any positive-Never minimizer of J_r, if B_p>e_p then small T leaves
B_p unchanged and decreases J_r by nu[u(T)+r(1-exp(-ST))]>0. Thus B_p=e_p.
Together with (7.2), this proves all-END at Y_*. The increment in J_r is now

    nu[b(T)/N_p-u(T)-r(1-exp(-ST))].

Its nonnegative right derivative at zero gives

    N_p<=1/(1+rS).                                  (7.11)

Only positive nu and r>0 were needed here; r<A was used in the earlier
argument solely to produce positive nu. At r=lambda_* the present
alternative supplies it directly. A strict inverse-column pivot is
available from the native positive-gap Fin4 source; it is not asserted
for every possible pivot.

### At a strict inverse-column pivot, the absorbing alternative is ALL-END

This strengthening was derived with CODEX_LAST_DATE. Assume the same
strict inverse-column hypothesis and put

    E_all={Y in C: B_i(Y)=e_i(Y) for EVERY player i},
    lambda0=inf{r>=0:f(r)=m},

with inf(empty)=infinity. Then the universal alternative strengthens to:

- Some Y0 in M0 belongs to E_all and satisfies N_p(Y0)<1/(1+mS); or
- the finite critical coexistence in(7.3) holds with lambda_*=lambda0>m
  and a positive-Never ALL-END critical minimizer.

This strengthens the first branch too: the pivot's cap is now END-active
at some absorbing GLOBAL minimum. If lambda0=infinity, one can additionally
choose that ALL-END minimum with N_p=0. These remain semantic statements;
no actual clock or common calendar is inferred.

First f(r) increases to m as r tends to infinity. Choose minimizing Y_n
at r_n tending to infinity. Nonnegative debt gives

    nu(Y_n)<=m/r_n ->0, d_p(Y_n)<=f(r_n)<=m.

A compact cluster point therefore belongs to C0 and has debt at most m,
hence exactly m. Since d_p(Y_n)<=f(r_n), the monotone limit of f is at
least m, proving the claim. This argument does not need the inverse column.

Whenever f(r)<m, EVERY minimizing point has positive nu: a zero-Never
point would have debt at least m. The inverse-axis argument above makes
all such minimizers ALL-END and gives N_p<=1/(1+rS).

If lambda0=infinity, take the preceding sequence with r_n tending to
infinity. Its minimizing points belong to the closed set E_all, and their
N_p tend to zero by the mass bound. The compact cluster point is the
asserted ALL-END member of M0 with N_p=0.

If lambda0 is finite, continuity and monotonicity of f give f(lambda0)=m,
strict inequality below lambda0 and the plateau above it. AllNever gives
m=f(lambda0)<=lambda0. Equality lambda0=m would make AllNever a minimizer
of J_m with B_p=0, contrary to B_p>=f(m)=m; hence lambda0>m.

Take r_n increasing to lambda0 from below and choose minimizing Y_n.
Every Y_n is ALL-END. A compact subsequence tends to Y_* satisfying

    d_p(Y_*)+lambda0 nu(Y_*)=m,
    B_i(Y_*)=e_i(Y_*) for every i,
    N_p(Y_*)<=1/(1+lambda0 S).

If nu(Y_*)=0, this gives the first alternative, with
N_p(Y_*)<=1/(1+lambda0 S)<1/(1+mS). The infinite-plateau limit above
also satisfies that strict bound because N_p=0. Otherwise it gives the
second, with strict sub-plateau values and the plateau already proved.
The alternatives need not be disjoint.

In particular, if M0 misses E_all, lambda0 is finite and positive-Never
critical minimizers exist. They all belong to E_all. A sequence of such
critical minimizers with nu tending to zero would limit to M0 intersect
E_all. Thus their Never masses have one common positive lower bound.
Furthermore J_lambda0>=m throughout C and equality at a positive-Never
critical point give the attained global formula

    lambda0=max_(Y in C,nu(Y)>0) (m-d_p(Y))_+/nu(Y).

This sharper conclusion does not assume that every positive-Never point
of C is all-END; only its minimizing points are used. It also does not
require observer-END activity to be absent at every absorbing minimum.

### Relation to the stronger actual-head case

Section6 already produces a plateau from an all-zero incoming tail and
identifies its parameter with that tail's debt. Its positive-Never minimizer
is an ACTUAL head. The universal alternative needs neither hypothesis,
but loses both the actual-head realization and the explicit debt formula.
The global ratio (7.5) replaces that formula.

The remaining source cases are an observer-END absorbing global minimum,
or a finite global transition with positive-Never and absorbing minimizers.
At a strict inverse pivot, the alternatives can be sharpened to an ALL-END
absorbing minimum with N_p<1/(1+mS), or an ALL-END positive-Never transition
point satisfying the strict payoff and mass bounds above. Neither case is
eliminated. In particular, finite calendarness or a strict margin at ONE
selected absorbing minimum does not rule out an observer-END point at a
different global minimum. No UE closure follows from the alternative.

## 8. Critical all-zero endpoints force a proper-pivot absorbing minimum

Derived with CODEX_NEVER_BOUNDARY_CREATIVE. This section concerns the
same complete-law augmented carrier and the strict inverse-column pivot.

Use Section 7:
H is the compact closure of actual native (U,B,N,e), C imposes all observer
debts zero, m>0 is the absorbing partial-Nash minimum, and lambda>m is a
finite first plateau with f(lambda)=m. Choose a strict inverse-column pivot.
Every positive-Never critical minimum is then ALL-END.

**Boundary consequence.** If such a minimum is nonrealized, its incoming
decomposition reaches a nonnegative-cap, ALL-END endpoint with positive
Never mass and at least one zero observer cap. If every endpoint cap is
zero, there is an ALL-END absorbing global minimum with N_p=0. Thus,
unless that absorbing alternative already occurs, the endpoint also has
at least one strictly positive cap. Actual critical minima and these
mixed boundary endpoints remain open.

### Neutral zero-cap tails force an absorbing ALL-END minimum

Let Q in C satisfy all B_i(Q)=0 and 0<nu_Q<1. The ordinary retained-menu
graft onto a positive-Never critical minimum Y has unchanged full caps,
unchanged observer payoff, and

    J_lambda(Y graft Q)-m
      =nu_Y [d_p(Q)-lambda(1-nu_Q)].

Consequently d_p(Q)>=lambda(1-nu_Q). Equality would make the graft another
positive-Never critical minimum. It must be ALL-END by Section 7. Its pure
Never values are e_i(Y)+h_i(Y)e_i(Q), while its full caps are B_i(Y)=e_i(Y).
Since h_i(Y)>0, equality forces e_i(Q)=0 for EVERY i. (For observers this
also follows from d_i(Q)=0 and N_i(Q)>0.)

With equality and e(Q)=0, repeating this same retained-menu graft gives
points Y_n in H with

    B(Y_n)=B(Y), e(Y_n)=e(Y), U_obs(Y_n)=U_obs(Y),
    N_i(Y_n)=N_i(Y) N_i(Q)^n,
    U_p(Y_n)=U_p(Y)-lambda nu_Y(1-nu_Q^n),
    d_p(Y_n)=m-lambda nu_Y nu_Q^n.

Their limit has nu=0, observer debts zero, pivot debt m and all caps END-
active. In fact N_p(Q)<1: the coupling bound
`|U_p-e_p|<=2M(1-N_p)` passes to H, so equality N_p(Q)=1 would give
U_p(Q)=e_p(Q)=0, whereas d_p(Q)=lambda(1-nu_Q)>0. Hence the limiting
minimum has N_p=0. This proves the asserted ALL-END absorbing alternative,
with a proper pivot in its retained Never coordinates. If this alternative
is absent,

    d_p(Q)>lambda(1-nu_Q)                         (A)

for every such Q. The strict inequality is pointwise; no uniform margin
near AllNever is asserted. If nu_Q=0, END activity is NOT automatic and
this argument does not apply without separately supplying e(Q)=0.

### An inherited all-zero endpoint supplies equality

Suppose a positive-Never critical minimum Y has an actual positive-Never
head P and endpoint Q in H, with all B(Q)=0, such that the semantic head map
retains ALL coordinates and satisfies Y=Phi_P(Q). Finite-prefix limits are
allowed; no continuation after an infinite calendar is executed. Assume
Q in C and nu_Y=nu_P nu_Q, so nu_Q>0.

Because B(Q)=0, Q has U_obs=0. Write

    r=d_p(Q)+lambda nu_Q.

For EVERY Z in C, grafting Q with a retained boundary query gives another
point of C with J_lambda=d_p(Z)+r nu_Z. Global critical minimality therefore
implies f(r)>=m; absorbing comparison gives equality. Hence r>=lambda by
the first-plateau property.

The head P itself has the same observer payoff/cap as Y and lies in C.
The supplied representation gives J_r(P)=m. Since nu_P>0 and J_lambda(P)
>=m, one also has r<=lambda. Therefore r=lambda.

If nu_Q<1, this is the neutral equality just analyzed and supplies an
ALL-END absorbing global minimum with N_p=0. If nu_Q=1, all marginal
Never masses of Q equal one. Native coordinate bounds imply U(Q)=B(Q)=e(Q)
=0, so Q is the AllNever tuple and Y is exactly the actual tuple of P.
Consequently a NONREALIZED positive-Never critical minimum with this
all-zero-cap incoming endpoint forces the ALL-END absorbing branch with
N_p=0.

### The incoming source adapter

For an arbitrary critical source, Section 7 gives nonnegative observer caps
and B_p>m. If an observer cap is already zero, take the source itself as
the mixed boundary endpoint; it is not an all-zero endpoint. Otherwise
all observer caps are positive, and the incoming construction in Sections
1--3 extends to this positive-Never augmented source.
Here nonrealized means that no actual profile realizes the entire tuple;
nonrealizedness of its payoff/cap pair is a sufficient stronger condition.
The only use of absorption in Section 1 was to ensure the first activity
crossing. Here any positive observer cap supplies it instead:

    B_i<=M(1-product_(j!=i)N_j)<=M(1-nu)<=M sum_t ell(q_t).

Choose actual approximants whose every original Never mass is bounded
below by half the corresponding positive source mass. Thus every
conditional hazard is well defined and strictly below one. For approximants
with observer caps at least mu/2, their total activity is at least
mu/(2M), larger than the chosen delta<=mu/(64M). The same small-
root bootstrap, observer deletion coupling and one/two-root compression
therefore give an incoming word. The compressed pivot-only word also
preserves limiting N and e: its total pivot mass is retained, observer
head masses tend to zero, and the same coupling controls pure Never.
The negative-cap incoming-root argument is unchanged.

Retain N and e when extracting every conditional tuple. Positive original
Never masses imply every incoming root is nonsure and, after every finite
word w,

    nu(source)=c(w) nu(tail), hence c(w)>=nu(source)>0.

Thus an infinite selected head has summable activity automatically. The
payoff/cap convergence argument is unchanged; Never coordinates converge
by their product formulas, and e converges by

    e_i(before)=P_i+H_i e_i(after).

If the source is ALL-END, every descendant is ALL-END. Indeed B=e before
and H_i>0 give

    e_i(before)=B_i(before)
      >=P_i+H_i B_i(after)>=P_i+H_i e_i(after)=e_i(before).

Thus B_i(after)=e_i(after). The limiting endpoint retains this equality.
The head map also preserves the augmented formulas

    N_i(source)=N_i(P)N_i(Q),
    e_i(source)=e_i(P)+h_i(P)e_i(Q).

Nonrealizedness passes to every finite descendant, since an actual tail
could be prefixed to realize the source. Activity lower bounds still force
a nonnegative-cap endpoint with at least one zero observer cap. If that
endpoint has ALL caps zero, the preceding equality argument consumes it.
Mixed zero-cap endpoints are not consumed. This does not exclude actual critical minima or the
ALL-END absorbing alternative, and does not prove a new UE class.
