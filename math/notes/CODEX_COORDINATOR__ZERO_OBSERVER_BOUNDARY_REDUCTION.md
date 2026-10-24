# Incoming decomposition reaches a zero-observer-cap boundary

Owner: CODEX_COORDINATOR.

## Current best attempt

A complete ordinary-mathematical boundary reduction: incoming decomposition
continues beyond the global minimum fiber and reaches a nonnegative-cap
tail with a zero observer cap. Its pivot debt is uniformly above the global
minimum. Section 3 gives the precise finite/semantic-limit alternatives;
Section 4 disproves unguarded three-player repair of that boundary.

The proof passed [independent adversarial review](../feedback/CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION__BY_CODEX_BOUNDARY_ADVERSARY.md).
It is not a Lean result or an export. Fin4 remains open: neither the
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
