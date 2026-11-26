# Full-law observer-equilibrium traps and their global boundary

Owner: CODEX_EXPENSIVE_EXIT.

Status: complete ordinary mathematical proofs. Sections 1–7 have
[independent review](../feedback/CODEX_EXPENSIVE_EXIT__FULL_LAW_OBSERVER_COMPONENT_TRAP__BY_CODEX_PIVOT_INDEPENDENT.md).
These are exact obstructions to proposed continuation mechanisms, not
positive-gap games, Fin4 exclusions, or an export. No Lean check is claimed.

The grand-coalition fixture was developed with CODEX_OBSERVER_PATH. The
proper-pivot component argument was derived by CODEX_EXPENSIVE_EXIT;
the root coordinator and CODEX_COLLAPSED_CONSUMER independently supplied
the extension to arbitrary absorbing profiles. The root coordinator also
supplied the quantitative observer-error barrier in Section 5.
CODEX_PIVOT_INDEPENDENT supplied the cyclic negative-column local variant
in Section 7, independently checked and consolidated here by
CODEX_EXPENSIVE_EXIT. CODEX_COLLAPSED_CONSUMER independently supplied a
symmetric precursor and the arbitrary-law proof structure.

The result is stronger than a finite-prefix obstruction. Even allowing
arbitrary replacements of ALL four complete stopping laws, the connected
component of an explicit positive source cannot reach zero pivot debt
while retaining absorption and exact observer best responses. A fixed
positive observer-error tolerance still leaves a topological separation.
The source is an actual minimum on its entire component and a local
minimum in the full absorbing partial-Nash space. It is not a GLOBAL
minimum there; a different component contains an absorbing full Nash
profile. That distinction is the reason this does not consume the
genuine global source.

The component control has nonnegative singleton columns. Section 7 gives
a different table whose columns each contain a negative entry, whose
pivot inverse column is strictly positive, and whose joining triple
determinants are all nonzero. Its positive source is root-inert and a
local minimum against arbitrary complete-law changes. The second result
is local; the entire-component assertion is made only for the first
table. Both tables have an explicit full Nash profile elsewhere.

## 1. Complete reward table and strategy space

There are four players I={0,1,2,3}; player 0 is the pivot. Fix a real
K>1. For EVERY nonempty coalition S, define

    Z_0(S)=2  if 0 is absent,
           1  if 0 is present and S contains an observer,
           0  if S={0};

    Z_i(S)=1  if i is absent,
           K  if S=I,
           0  otherwise,                 i=1,2,3.       (1)

All own singletons are zero. Live and AllNever payoff is zero. These
rules specify all sixty nonempty reward entries.

Every private stopping law is a probability law on N union {Never}.
Laws are independent; the first finite date and its simultaneous quitting
coalition determine the terminal payoff. A unilateral response replaces
the owner's entire law, including all finite deadlines and Never.
Write U_i, B_i and d_i=B_i-U_i for the prescribed payoff, full response
cap and debt.

Let E be the set of all ACTUAL absorbing profiles with exact observer
best responses:

    E={P: P absorbs surely and d_1=d_2=d_3=0}.

No restriction is imposed on the pivot law, on finite support, or on
off-path clocks. Equip E with the topology induced either by weak
convergence on the one-point compactification of N or by total variation.
The proof needs only continuity of each finite atom probability.

For a profile put

    t=Pr(T_0=0),       a_i=Pr(T_i=0),
    a=min(a_1,a_2,a_3),
    E_+={P in E:a>0}.                                   (2)

## 2. Complete response facts

Let tau=min(T_1,T_2,T_3), allowing Never. For every profile, the pivot's
Never response weakly dominates every other complete response, pointwise
under independent coupling. If tau is finite, its Never payoff is 2.
Quitting strictly before tau pays 0, joining at tau pays 1, and quitting
after tau pays 2. If tau is Never, every pivot response pays zero.
Consequently

    B_0=2 Pr(tau<Never),
    d_0=2 Pr(T_0<tau<Never)+Pr(T_0=tau<Never),
    d_0>=t [1-product_i(1-a_i)].                        (3)

This includes every finite deadline, infinite support and literal Never.
It is not a bound on a selected response menu.

In an absorbing independent profile at least one owner h has a proper
law. Indeed absorption is equivalent to product_i Pr(T_i=Never)=0,
and a finite product of nonnegative numbers is zero only if one factor
is zero. Every observer i different from h then has a proper opponent.
Its Never payoff is exactly 1, because absorption occurs without it and
its absent reward is always 1. Thus at least TWO observers satisfy

    B_i>=1.                                           (4)

If the pivot is proper, all three observers satisfy (4). There is no
assertion that a cap satisfying (4) equals 1 in a general equilibrium.

For each observer the pure date-zero payoff is exactly

    Q_i(0)=K t a_j a_k,       {i,j,k}={1,2,3}.          (5)

In an exact observer equilibrium, a_i>0 makes this used pure response
attain its complete cap. To see this directly, every pure response value
is at most B_i, and their average under the prescribed law equals B_i.
A positive atom cannot be placed at a strictly smaller value. Therefore

    a_i>0 implies K t a_j a_k=B_i.                     (6)

No assumption about the conditional tail after a sure root is used.

## 3. The entire positive-atom component has a sharp debt floor

Take P in E_+. For the at least two observer indices supplied by (4),
equation (6) gives K t a_j a_k>=1. Two different such inequalities
involve all three observer atom probabilities. Since t and every a_i
are at most one, they imply

    t>=1/K,       a_i>=1/K for every observer i.         (7)

Choose either of these two inequalities. The event that its two other
observers both quit at zero is contained in the event that some observer
quits at zero. Combining it with (3) yields

    d_0>=t[1-product_i(1-a_i)]>=t a_j a_k>=1/K.         (8)

Thus the continuous statistic a on E takes values only in

    {0} union [1/K,1].                                 (9)

In particular E_+ is both open and closed in E. Every connected subset
of E meeting E_+ lies entirely in E_+, and every point of that subset has
pivot debt at least 1/K. This statement permits arbitrary continuous
changes of the pivot and all observers' complete laws, not only changes
of first-root probabilities or finite observer-Nash prefixes.

### 3.1. An actual source attaining the component minimum

Let all three observers quit surely at date zero. Let the pivot use

    (1/K) delta_0+(1-1/K) delta_1.

The profile absorbs at date zero. Each observer's date-zero response pays
K times the pivot date-zero probability, hence 1. Every later response,
including Never, also pays 1 because the other two observers have already
quit. The pivot's date-zero response pays 1, while every later response
and Never pays 2. Thus the full semantic data are

    U=(2-1/K,1,1,1),
    B=(2,1,1,1),
    d=(1/K,0,0,0).                                    (10)

All four payoffs are strictly positive, all caps equal the corresponding
Never values, and the pivot law is proper. The point lies in E_+, so
(8) proves that it minimizes pivot debt over ALL of E_+, and hence over
its entire connected component. Since E_+ is open in E, it is also a
local minimum among arbitrary absorbing exact-observer profiles.
The same holds with any pivot tail replacing delta_1; the observers
already absorb at date zero.

### 3.2. The exact root game is inert

At continuation U from (10), let w be the probability that some observer
quits at a proposed product root. The pivot's two endpoint values are

    Q_0=w,
    C_0=2w+(1-w)(2-1/K).

Since K>1, C_0-Q_0=w+(1-w)(2-1/K)>0 for every observer root profile.
Every full exact root therefore prescribes pivot Continue. An observer's
Quit endpoint is then zero, since a grand coalition is impossible. Its
Continue endpoint is 1, since its continuation is 1 and every absorbing
coalition omitting it also pays 1. Every observer strictly Continues too.
AllContinue is consequently the unique exact Nash root at U.

Root inertia and an actual componentwise minimum therefore coexist with
a strictly positive pivot debt. They do not imply global minimizing
provenance.

## 4. A positive interior source on the same component

The separation is not caused only by sure observer clocks. For K=8, let
the pivot law be (delta_0+delta_1)/2 and each observer use
(delta_0+Never)/2. Every observer's Never payoff is 1 because the pivot
is proper. Quit0 also pays 8/8=1. A positive finite deadline obtains at
most 1: on every event where its opponents have already stopped it pays
1, while on the remaining event a grand coalition is impossible and
its participant reward is zero. Therefore

    U=(21/16,1,1,1),
    B=(7/4,1,1,1),
    d=(7/16,0,0,0).                                   (11)

Every observer has positive Never mass. The pivot cap is again its Never
value, so all ENDs are active. Literal joint Never is zero because the
pivot is proper.

This source is connected within E_+ to the sharp point (10). For
t in [1/8,1/2], take pivot law t delta_0+(1-t)delta_1 and let all three
observers use a(t)delta_0+(1-a(t))Never, where

    a(t)=(8t)^(-1/2).

Quit0 pays 8t a(t)^2=1; Never pays 1; every positive finite response
is bounded by 1 as above. These are actual observer equilibria and the
laws vary continuously even in total variation. At t=1/2 they give
(11), and at t=1/8 they give (10). Hence the connected component of
the interior source also has exact pivot-debt minimum 1/8.

## 5. A quantitative barrier for approximate observer equilibrium paths

This argument no longer assumes observer equilibrium. Let P be ANY
actual absorbing profile and let a=min_i a_i satisfy 0<a<1/K. Choose
an observer j attaining the minimum. Among the at least two observers
with a proper opponent, choose i different from j. Then B_i>=1 and,
by (5),

    Q_i(0)=K t a_j a_k<=K a.

Every remaining pure response has value at most B_i, so the prescribed
payoff is at most a_i Q_i(0)+(1-a_i)B_i. It follows that

    d_i>=a_i[B_i-Q_i(0)]
        >=a_i(1-Ka)>=a(1-Ka).                         (12)

The final step uses a_i>=a and 1-Ka>0. This is a full-law estimate;
it does not require a local response attainer away from date zero.

For 0<=epsilon<1/(4K), define

    a_-=(1-sqrt(1-4K epsilon))/(2K),
    a_+=(1+sqrt(1-4K epsilon))/(2K).

If every observer debt is at most epsilon, (12) excludes

    a in (a_-,a_+).                                   (13)

Thus the absorbing epsilon-observer-equilibrium space has two separated
parts, a<=a_- and a>=a_+. A continuous path starting at (10) or (11)
cannot reach a profile with a=0 while keeping absorption and all observer
debts at most epsilon. In particular, at a=1/(2K) some observer debt is
at least 1/(4K). The separation persists for a FIXED positive tolerance;
it is not merely a discontinuity at exact equilibrium.

There is also a pivot-debt floor on the upper part. Choose an observer i
with a proper opponent. The inequality preceding (12) gives

    K t a_j a_k=Q_i(0)>=1-epsilon/a_i
                             >=1-epsilon/a.

For a>=a_+>0, (3) therefore yields

    d_0>= [1-epsilon/a]/K
         >=[1-epsilon/a_+]/K=a_+.                     (14)

The last equality uses epsilon=a_+(1-Ka_+). At epsilon=0 this recovers
the sharp exact floor 1/K. No sharpness claim is made for (14) at
positive epsilon.

## 6. Global comparison and the honest source boundary

The table has an actual absorbing full Nash profile outside E_+: let
only observer 1 quit surely at date zero and let everyone else Never.
Its payoff is

    (2,0,1,1).

The pivot attains its global reward upper bound 2. Observers 2 and 3
attain 1, and their finite responses can never form the grand coalition
because the pivot remains Never. Observer 1 has payoff and full cap zero
against three Never opponents. Thus every full debt is zero. In particular
the GLOBAL minimum of d_0 on E is zero, while the component containing
(10) and (11) has minimum 1/K.

This explicitly refutes an arbitrary-source claim that whole-law observer
repair, proper-clock continuation, positive payoffs, all-END activity,
root inertia or local/component minimization must yield a debt-decreasing
path to equilibrium. The exact continuum of all full laws was used in
the lower bounds; a finite-menu approximation is not the obstruction.

It does NOT refute a consumer using the genuine positive-gap global
minimum. The table's singleton columns are nonnegative, and its positive
absorbing gap is already ruled out by the solo-clock producer. Its
component minimum has neither the global source provenance nor the
singleton restrictions of a counterexample candidate. A successful proof
may have to choose a different component from the outset or compare
components using global extremality. This note supplies no such comparison.

The preceding proper-clock continuum result is recorded in Section 11 of
[the full-cap thinning note](CODEX_FIXED_COLUMN_VARIATION__FULL_CAP_THINNING_RENT.md).
It guarantees SOME spanning connected observer-Nash set on a compact
proper-pivot path, without guaranteeing that it contains a specified
initial equilibrium. The present control shows that the missing anchor
cannot simply be added. It also shows that retaining a fixed small
observer approximation error does not automatically connect the branches.

The prefix-trap predecessor is Section 6 of
[the incoming-collision note](CODEX_OBSERVER_PATH__GLOBAL_MINIMUM_INCOMING_COLLISION.md).
There a full observer-law deletion escapes the prefix closure. Here even
the entire absorbing full-law observer-equilibrium component has a fixed
positive debt floor. The distinct stronger scope is the reason this
control is retained.

The full-cap interpretation was inspected in
`quittingTerminalSemanticPair_rootThenContinuation` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` and
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
No Lean command, export edit, or git mutation was performed.

## 7. A local full-law trap with negative columns and a positive inverse column

The following separate table shows that several genuine source
restrictions do not by themselves repair local continuation. Its proof
does not impose absorption on competing profiles. It does not establish
the whole-component separation proved for table (1).

### 7.1. The complete cyclic table

Put eta=1/10. Keep the pivot rewards from (1). For observers define the
passive singleton matrix by

    Gamma_i0=-eta,

    (Gamma_ij)_{i,j=1,2,3}
        =eta [[ 0, 2,-1],
              [-1, 0, 2],
              [ 2,-1, 0]].                            (15)

For every observer i and every nonempty coalition S, set

    Z_i(S)=Gamma_ij  if i is absent and S={j};
           1         if i is absent and |S|>=2;
           2         if S=I;
           Gamma_ij-1 if S={i,j} is an observer-only pair;
           0         in every remaining case.         (16)

All own singletons and AllNever remain zero. Equations (15)–(16),
together with the unchanged pivot rule, specify all sixty rewards.

The full singleton matrix and joining matrix are

    Gamma = [[ 0,    2,     2,     2],
             [-eta,  0, 2 eta,  -eta],
             [-eta,-eta,     0, 2 eta],
             [-eta,2 eta, -eta,     0]],

    L = [[  0,-1,-1,-1],
         [eta, 0,-1,-1],
         [eta,-1, 0,-1],
         [eta,-1,-1, 0]],                             (17)

where L_ij=Z_i({i,j})-Gamma_ij. Every singleton column contains a
negative entry. Direct determinant expansion gives

    det Gamma=42 eta^3,
    Gamma^{-1} e_0=(1,1,1,1)/6.                       (18)

For the second equality, Gamma times the all-ones vector is 6 e_0;
the first equality supplies invertibility. The positive vector
(1/2,1,1,1) also has strictly positive image
(6,eta/2,eta/2,eta/2). Every principal joining triple is nonsingular:
its determinant is -2 on the three observers and 2 eta on a triple
containing the pivot. Thus this example also survives the generic
joining-determinant restriction.

Let all three observers use delta_0 and let the pivot use
(delta_0+delta_1)/2. This actual absorbing profile has

    U=(3/2,1,1,1),
    B=(2,1,1,1),
    d=(1/2,0,0,0).                                   (19)

Indeed, each observer's used Quit0 payoff is 2 times the pivot's
date-zero probability, hence 1. Every later response, including Never,
pays 1 because the two other observers already quit at zero. The
pivot's Never response attains 2 and its prescribed payoff is 3/2.
All literal Never responses attain their complete caps.

The exact finite Nash game with continuation U from (19) has
AllContinue as its unique equilibrium. If w is the probability that
some observer quits at its root, the pivot has

    C_0-Q_0=w+(1-w)(3/2)>0.

Consequently the pivot Continues in every root equilibrium. With that
action fixed, each observer has C_i-Q_i=1 against EACH pure profile of
the other two observers: the pairs of values are (1,0) when neither
quits, (Gamma_ij,Gamma_ij-1) when just j quits, and (1,0) when both
quit. Hence all three observers also strictly Continue.

### 7.2. A lower bound over arbitrary complete stopping laws

Consider ANY independent complete-law profile for (15)–(16) with

    d_1=d_2=d_3=0,
    alpha_i=Pr(T_i=0)>=9/10 for every observer i.

There is no restriction on the pivot law, finite supports, later atoms,
Never masses, or the profile's probability of absorption. Put

    t=Pr(T_0=0),   b_i=1-alpha_i,   u=max_i b_i<=1/10.

For observer i with other observers j,k, write

    A=alpha_j alpha_k,
    D=alpha_j+alpha_k-2A.

Here D is the probability that exactly one of j,k quits at zero.
The date-zero response payoff Q_i and literal Never payoff E_i satisfy

    Q_i<=2tA-(1-2eta)(1-t)D,
    E_i>=(1+eta)(A+tD)-eta.                           (20)

For the first inequality, a grand coalition pays 2. If the pivot does
not quit and exactly one other observer quits, the resulting
observer-only pair pays either 2eta-1 or -eta-1, both at most
-(1-2eta). All remaining participant outcomes at zero pay zero.
For the second inequality, at least two opponents quit at zero with
probability A+tD, giving the passive reward 1. On every remaining
outcome a Never observer gets at least -eta, including the zero payoff
when everyone remains Never. These statements use entire-law response
values; no restriction on a tail response menu is implicit.

Because alpha_i>0 and i is an exact best responder, its used date-zero
response satisfies Q_i=B_i>=E_i. Equation (20) therefore implies

    t [2A-3eta D]
        >=(1+eta)A+(1-2eta)D-eta.                    (21)

The denominator F=2A-3eta D is positive and at most 2: A>=81/100 and
D<=18/100 give F>=783/500. Subtract half of this denominator from the
right side of (21). The remainder is

    H=-eta(1-A)+(1-eta/2)D.                           (22)

In the specified region one has D>=(4/5)(1-A). For example, put
s=b_j+b_k and v=b_j b_k. Then D=s-2v, 1-A=s-v and v<=s/20,
so D-(4/5)(1-A)=s/5-6v/5>=0.

Choose i so that the pair j,k contains an observer with largest deficit
u. Then 1-A>=u, and eta=1/10 gives

    H>=(33/50)(1-A)>=(33/50)u.

Dividing by 0<F<=2 in (21) yields

    t>=1/2+(33/100)u.                                (23)

The pivot reward rule is unchanged, so the exact full-cap identity (3)
applies even when the new profile is nonabsorbing. In particular

    d_0>=t(1-b_1 b_2 b_3)
        >=t-u^3
        >=1/2+(8/25)u.                               (24)

The last step uses u^3<=u/100. This proves an actual local minimum at
(19) in the FULL observer-equilibrium space, for either weak convergence
or total variation of stopping laws. Every change of observer date-zero
atoms within this neighborhood strictly raises pivot debt; pivot-tail
variations may leave the minimum unchanged. The proof also covers
profiles that introduce new dates, have infinite support, or fail to
absorb. There is no claim of a strict local minimum in every coordinate.

### 7.3. The global boundary and an explicit route that raises debt first

Table (15)–(16) still has a full absorbing Nash profile. Let the pivot
and two observers Never and let the remaining observer i quit surely
at zero. The pivot gets its reward upper bound 2. Observer i has payoff
and cap zero against all Never opponents. Each other observer j gets
Gamma_ji; joining at zero gives Gamma_ji-1, while every later response
and Never gives Gamma_ji. Thus all four full debts are zero, even if
one of these equilibrium payoffs is negative.

There is also a two-prefix observer-Nash route from (19) to that profile
which necessarily avoids any assertion of monotone debt descent. First
prepend a sure simultaneous quit by the pivot and observer i. The new
payoff/cap vectors are

    U'=(1,0,1,1),   B'=(2,0,1,1),

with the zero observer coordinate placed at i. The active observer's
Quit payoff is 0 and its Continue payoff is -eta; each other observer
has Continue payoff 1 and joining payoff 0. Thus all observers remain
best responders, while pivot debt rises from 1/2 to 1. Next prepend a
sure solo quit by i. Its two root values are both zero because its new
tail cap is zero. The pivot Continues for payoff 2 instead of joining
for 1; each other observer Continues for Gamma_ji instead of joining
for Gamma_ji-1. This second prefix gives the zero-debt Nash profile
just described.

This is a finite sequence of exact observer-Nash profiles, not a claim
that interpolation between its endpoints preserves observer equilibrium.
It illustrates the exact logical boundary: root inertia, negative entries
in every singleton column, a strictly positive inverse pivot column,
nonsingular joining triples and full-law local minimality can all hold
at the same source, while global pivot-debt minimality fails.

The next question remains a GLOBAL component comparison under positive
gap. Neither control supplies the missing consumer of a genuine global
minimum.
