# A positive opposed-pair head forces later outside activity

## Exact statement

Four players0,1,2,3 privately and independently choose their first Quit time,
with a separate literal Never action. A unilateral deviation replaces that
player's entire behavioral strategy, equivalently its complete first-Quit law.
Own-singleton, live and AllNever rewards are0. All coalition rewards are finite.
Fix only the following rewards to core recipients0,1,3 on coalitions contained
in that core:

| Coalition S | Z0(S) | Z1(S) | Z3(S) |
| --- | ---: | ---: | ---: |
| 0 | 0 | -6 | 1 |
| 1 | -2 | 0 | -1 |
| 3 | 4 | 6 | 0 |
| 01 | -1 | -7 | 0 |
| 03 | 3 | 0 | 2 |
| 13 | k | -1 | -2 |
| 013 | 2 | -8 | 0 |

Every other reward is arbitrary and finite, apart from the stated native own-
singleton/live/AllNever normalization. In particular all rewards to player2,
all rewards on coalitions containing2, and all off-core singleton rewards are
unrestricted. No participant-sign assumption involving2 is imposed.

For an actual independent profile let U be its terminal payoff vector, B its
complete unilateral response-cap vector, e its literal-Never response vector,
and N its ORIGINAL Never marginals. Let C be the Euclidean closure of the
actual bounded tuples(U,B,e,N), and E={X in C:U=B}. Original escaping finite
mass is retained as finite mass, not relabeled Never.

**Theorem.** Suppose k>=2. Let X be an E source with positive ORIGINAL Never
marginals and a genuine first proper Nash row of support03, with genuine E tail
Y and full continuation caps. If U1(X)>0, then

    N2(Y)<1.

Equivalently player2 has some physical finite activity after that genuine03
head. Since the head has q2=0, this also says N2(X)<1. The conclusion permits
all later core support switches, finite and infinite histories, diffuse pieces,
accumulations and isolated terminal marks. It does not require a first013 row.
It holds even when X and Y are compact carrier points without actual natural-
date realizers. No minimum is assigned to Y or any subsequent tail. Neither
the sign of Y1 nor any player2 payoff sign is assumed.

A more general mathematical barrier is proved: for every faithful complete
retained native zero-debt clock on core0,1,3, with positive original Never and
player2 physically Never, k>=2 and w1<=0,w3>0 imply

    Psi(w)=w1/6+w3-min(w0,0)+(w1/6)max(w0,0)<=0.

No cofinality, eventual full013 support, bounded controller, finite number of
switches, positive absorbing gap, or local minimality is needed for this barrier.

## Conjecture-facing change

The original fixed-family global least-Never/source reduction supplies a genuine
first03 row with all original output caps positive. Its compact tail has negative0
and positive3. On the raw sign chamber Z0(13)>=2, the new theorem excludes the
ENTIRE source mode in which player2 has no future physical activity. The result
covers every tail1 sign and every subsequent core history; it uses the genuine
original head rather than a minimizing-tail substitution. Thus the surviving
first03 source must already have N2<1 on this whole sign chamber.

The theorem is a source-class narrowing, not an existence theorem for every table
in the chamber. A finite2 excursion followed by a proper-three-cofinal tail,
other first-row/source modes, and the rest of the fixed family remain open.
No all-table Fin4 closure or uniform-equilibrium payoff is asserted.

## Strategic inputs

The input is an already given genuine03 source head in the actual tuple closure.
Its conditional negative0/positive3 and strict barrier sign are produced below
from the exact head Nash equations and U1(X)>0. The proof constructs an exact
retained representation of Y from any actual realizing sequence, preserving
ALL response queries, first-coalition kernels and original Never marginals.

A first03 head is not produced for arbitrary quitting-game data here: this
result consumes that specified existing source branch. No new tail strategy,
favorable root, clock rate, passive-player sign, cofinality, tail minimum or
chronological repair witness is assumed. In particular no first013 entry or
one-amplitude clock grammar is used.

## Definitions, probability and information

Before absorption there is one live public history at each time. Independent
behavioral randomization is therefore exactly independent first-Quit laws.
The payoff is the expectation of the reward of the earliest nonempty quitting
coalition; literal AllNever pays0. Complete deviations average the pure finite
deadlines and Never, so B is their supremum. All arguments concern expected
terminal payoffs and the ENTIRE response menu. There is no public lottery,
correlated timing, hidden observation, or restriction on unilateral deviations.

For native own-singleton0, complete-law Fubini gives

    B_i-U_i = integral [B_i-response_i(t)] dq_i(t)>=0,
    B_i-U_i >= N_i(B_i-e_i)>=0.

Thus positive original Never and zero debt imply U=B=e. A conditional suffix
has the same property: earlier first coalitions cancel from every reply
comparison, and Fubini restricts to the surviving own law.

## Source correspondence and implementation boundary

The existing checked declaration
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`) identifies a complete
behavioral root/continuation cap with the maximum of immediate Quit and Continue
carrying the genuine full continuation cap. The exact finite-prefix formulas
used below are its independent first-Quit-law form.

The positive semantic endpoint is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
The positive terminal-debt obstruction is characterized by
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean`).
These declarations do not prove the new barrier or its forced-entry consumer.
The present result is ordinary mathematics to be formalized; no new Lean
verification or A/C evidence is claimed. It narrows one source obligation on
the route to those semantic endpoints and does not reach either endpoint alone.

## Proof

### 1. Prefixes and a complete original-Never representation

For a first product row q write h=product_i(1-q_i),
H_i=product_(j!=i)(1-q_j), Q_i for its forced-Quit offer and P_i for its passive
offer on nonempty opponent coalitions. At a tail(U,B,e,N), the exact formulas are

    U'_i=q_i Q_i+(1-q_i)P_i+h U_i,
    B'_i=max(Q_i,P_i+H_i B_i),
    e'_i=P_i+H_i e_i, N'_i=(1-q_i)N_i.

They are continuous and preserve C by prefixing actual realizing sequences.
With d_i=B_i-U_i, their nonnegative decomposition is

    d'_i=q_i(B'_i-Q_i)+(1-q_i)(B'_i-P_i-H_iB_i)+h d_i.

Hence a proper Nash row at an E tail stays in E; conversely a proper genuine
row of an E source has an E tail. If the source has all N_i>0, all its hazards
are strictly less than1. In particular the head's player2 hazard is0, so N2(Y)=N2(X). Suppose
toward a contradiction that this common value is1.

For completeness, every augmented carrier point has the following exact
retained-clock representation. Use actual finite-support realizing profiles:
truncate a far finite tail and move only its vanishing total mass to the SAME
players' Never branches. Independent coupling changes every prescribed and
every pure-response payoff by at most twice a reward bound times moved mass,
uniformly over ALL deadlines and Never. Thus full caps and original limiting N
are preserved. No nonvanishing escaping finite mass is moved to Never.

At each finite realizer use the mean of the four laws. Give each occupied old
date a chronological raw interval in[0,1] of that mean mass, and give Never the
last interval. Player i has constant density at most4 on each old interval.
Coordinates are sampled independently; the chart is deterministic bookkeeping.
Extract weak-star limits of the four bounded densities and a limit of the
finite/Never boundary. Sequential extraction suffices because L1 is separable.

Keep separately the compact sets of old interval endpoints and actual offered
pure tests: an occupied date's midpoint, an old EMPTY date's actual raw cut,
and the final empty finite test. An unoffered empty query is not inserted.
Extract Hausdorff limits. Each component of the complement of the endpoint
limit is the limit of one old atom interval, with constant owner densities
and its sole midpoint test. Collapse that component to its test. The rest
of the endpoint limit outside the test limit is null: each component of the
complement of the test limit contains at most one such endpoint, so there are
only countably many. Retain the remaining cuts, and send the raw interval after
the finite boundary to a SEPARATE Never label.

The resulting compact ordered offered set T has isolated positive mixture
atoms, zero mixture atom at every other test, and a final empty finite mark c.
Original N is preserved exactly by testing the raw Never interval; replacing
its moving boundary by the limiting boundary costs at most4 times the boundary
displacement. If N2=1, the represented player2 law is literal Never.

All first-coalition indicators converge almost everywhere in the independent
raw product cube. Exclude only endpoints of POSITIVE limiting atom intervals,
the finite/Never boundary and equal independent raw coordinates, a null set.
The whole endpoint limit need not be null and is not discarded. Two other
finite coordinates either belong to the same positive limiting old interval
and are eventually tied, or have a retained limiting endpoint between them
and are eventually correctly ordered. Hence the indicators converge in L1.
Independent bounded density products converge weak-star: first test rectangles,
then finite combinations, then all L1 kernels using their uniform bound.
Splitting each integral into the changing-kernel L1 error and the fixed-kernel
weak-star limit proves convergence of every coalition probability and U,e.

The same argument applies to any moving old pure query. Near a positive limiting
atom it is the midpoint of that SAME old atom; at a non-atomic cut its equality
set has zero opponent mass. Each retained query is approached by old queries;
old maximizing queries have convergent subsequences. These two directions prove
that stored B is exactly the maximum over ALL T queries and Never. Responses
are continuous on T: atoms are isolated, and a moving non-atomic cut crosses
vanishing mass. Fubini is retained. This constructs the entire clock used below
from source data; it does not execute an abstract calendar in the original game.

Apply this construction directly to Y. The core-only representation is exact
Nash in the ENTIRE retained menu, with the same original U,B,e,N and every
N_i>0. We now prove its barrier, including any compact earlier portion before
a natural-date suffix.

### 2. Conditional values and bounded variation


For an initial cut x write n_i(x)=N_i+q_i([x,c)). These are ORIGINAL surviving
probabilities, uniformly bounded below by N_i. Condition each independent law
on its own surviving set. Let w_i(x) be the conditional pure-Never payoff.
Earlier first coalitions cancel from any comparison between retained suffix
queries and Never. Since the original full cap is Never, the conditional full
suffix cap is also w_i(x). Retained Fubini and zero original debt show that own
prescribed suffix queries are cap contacts almost everywhere. Thus every
conditional clock has U=B=e=w; no minimum is transferred.

All w_i are bounded-variation functions of the cut. One direct bound comes by
coupling the unnormalized future first-coalition integral: removing physical
mass changes it by at most a finite reward bound times removed mass. Divide by
the opponent-survival products, whose denominators have a positive fixed lower
bound. The total normalized hazard measures satisfy

    integral dq_i/n_i <= (1-N_i)/N_i < infinity.

The w_i are continuous away from physical atoms and have the exact one-product
jump formulas at a retained atom. Limits through increasing retained cuts are
the actual conditional kernel limits, with the ORIGINAL N_i held separately.
At c, all remaining physical finite tails vanish, so w_i(c)=0.

At an atom with conditional hazards(a,b,c3), write c3 as c below when no
confusion with the terminal mark arises. The exact forced offers and passive
offers are

    Q=(-b+3c,-7a-c,2a-2b),
    P=(-2b+4c-kappa*bc,-6a+6c,a-b).

Full caps and Fubini give Q_i<=w_i and q_i(Q_i-w_i)=0. Positive original N
makes every hazard strictly less than1. Conditional values after the atom are

    w0'=(w0-P0)/[(1-b)(1-c)],
    w1'=(w1-P1)/[(1-a)(1-c)],
    w3'=(w3-P3)/[(1-a)(1-b)].

At a non-atomic legal query, the current singleton payoff is0 and no opponent
has a current atom. Therefore every w_i>=0 there. Own non-atomic activity i
can occur only on w_i=0, by retained Fubini.

Let d lambda_i be the continuous part of dq_i/n_i. On this part the conditional
value equations are

    dw_i=sum_(j!=i) (w_i-Gamma_ij) d lambda_j.      (BV)

This follows by removing one infinitesimal independent opponent mass, or by
Stieltjes differentiation of the unnormalized future kernel. Physical ties
have no continuous contribution; they remain in the exact atom jumps.

### 3. The sign region and the zero0/positive1 trap

We work from a source with w1<=0,w3>0 and Psi>0, toward a contradiction.
As long as this region persists, the exact atom inequality

    w3'=(w3-a+b)/[(1-a)(1-b)]
          >=w3/[2(1-a)(1-b)]>0

preserves positive3. At a non-atomic retained point, w0>=0 and w1=0, so
Psi=w3. Thus a continuous first exit through w3=0 would force Psi=0. The
monotonicity proved in the atom and continuous cases below prevents this; the argument can be
localized up to a first exit. At an accumulation of atoms with no physical
atom, conditional values are continuous and the same observation applies.

The source cannot first acquire positive1 by an atom with b>0, because its
next1 is -(a+7c)/[(1-a)(1-c)]<=0. With b=0 and c>0, positive3 forces a>0,
so the row is03 and its next0=-c/(1-c)<0. But positive1 forces b_next=0, and
then Q0_next>=0, incompatible with negative0. The remaining atom that can
produce positive1 is solo0, at w0=0.

The same is true for a continuous first transition to positive1. Before it,
a non-atomic query has w1=0; continuous3 activity is absent while w3>0, and
continuous1 does not change its own value. Hence (BV) can increase w1 only
through continuous0 activity, which requires w0=0.

A state w0=0,w1>0 is a trap contradicting the zero-tail endpoint. Localize to
any future interval on which w1 stays positive. Owner1 has no physical activity
there, because its finite forced offer is nonpositive. Thus every legal query
has b=0, so the full cap inequality gives w0>=Q0=3c>=0. Let S3 be the conditional
probability that owner3 survives from the entry cut to a later cut in this
interval. With owner1 inactive, the exact pure-Never0 decomposition is

    w0(entry)=4(1-S3)+S3*w0(later).

It is independent of owner0's law, and holds across every combination of atoms,
continuous mass and accumulations. Since w0(entry)=0,

    w0(later)=4-4/S3<=0,

strictly if S3<1. The full cap inequality therefore forces S3=1 throughout the
interval: owner3 has no physical activity at all. If S0 is the analogous owner0
survival, the exact pure-Never1 formula becomes

    w1(later)=-6+[w1(entry)+6]/S0>=w1(entry)>0.

Thus the positive1 interval cannot end through a continuous limit, an
accumulation, or a new atom. It extends to the terminal mark, contradicting
w1(c)=0. No cofinality assumption is needed. Uniform positive original Never
makes every S0,S3 strictly positive. This trap does not need positive3 after
entry and does not require a first later atom.

Thus a compact core-only clock from the stated source retains w1<=0. A strict
positive lower bound for Psi then protects w3>0 at every possible continuous
exit or accumulation, as noted above. Boundary w1=0 is allowed; no strict
negative1 invariance or always-active0 assertion is being assumed.

### 4. Atom algebra: solo and pair rows


Write w=(V,-E,F), E>=0,F>0.

For a solo0 row, V=0 and

    E_next=(E-6a)/(1-a), F_next=(F-a)/(1-a),
    (1-a)*Psi_next=Psi.

For pair01, V=-b,E=7a, and with h=(1-a)(1-b),

    V_next=b/(1-b), E_next=a/(1-a),
    F_next=(F-a+b)/h,
    h*Psi_next=Psi.                              (01)

For solo1 at zero1, a=c=0 and the quiet0 comparison is V>=-b. Its next0 is
(V+2b)/(1-b)>0 when V<0, and is positive also for V>=0 and b>0. Therefore

    (1-b)*Psi_next-Psi=b+min(V,0)>=0.             (1)

An empty row preserves Psi. In all these cases Psi>0 implies
Psi_next>=Psi>0.

### 5. Pair03, including its necessary size bound

Here b=0,V=3c,F=2a. The next0 is -c/(1-c). Every following proper core row has
Q0=-b_next+3c_next>-1. Its incoming cap comparison therefore forces

    -c/(1-c)>-1, equivalently c<1/2.              (03-SIZE)

This uses actual positive original Never and the following exact Nash row;
it is not an added smallness hypothesis.

With h=(1-a)(1-c), direct substitution gives

    h*Psi_next-Psi=c(E-4a)/2.                    (03-A)

If E>=4a and Psi>0, this implies Psi_next>=Psi. If E<4a, put

    d=h(1+3c)-1.

A second exact identity is

    h*(Psi_next-Psi)=2a^2(1-c)+(E/6)*d.          (03-B)

If d>=0 this is nonnegative. If d<0, E<4a gives the lower bound

    h*(Psi_next-Psi)
      >=(2a/3)(2-3c)[a(1-c)+c]>=0,

where c<1/2 by(03-SIZE). Thus every possible03 step with Psi>0 satisfies
Psi_next>=Psi>0.

### 6. Full013, all three sign cases, kappa=0

Here E=7a+c, F=2(a-b)>0, so 0<b<a<1. Put h=(1-a)(1-b)(1-c). The exact
next values for kappa=0 are

    V_next=(b-c)/[(1-b)(1-c)],
    E_next=(a+7c)/[(1-a)(1-c)],
    F_next=(a-b)/[(1-a)(1-b)].

We prove h*Psi_next-Psi>=0 without assuming Psi positive.

**A. b<=c.**

The current0 is nonnegative and next0 nonpositive. Exact cancellation gives

    h*Psi_next-Psi=c(3a+4b+c)/2>=0.               (FA)

**B. c<=b<=3c.**

Both current0 and next0 are nonnegative. Let

    R=6(1-c)[h*Psi_next-Psi]
     =a(6bc-7b-15c^2+16c)
        -12bc^2-bc+6b-3c^3+16c^2-6c.            (FB)

For fixed b,c, R is affine in a in the interval[b,1], so it suffices to check
a=b and a=1.

At a=b, R is concave in b because its b^2 coefficient is6c-7<0. The endpoints
of b in[c,min(3c,1)] give

    b=c:   24c^2(1-c),
    b=3c:  2c(3c+2)(3-5c), used when c<=1/3,
    b=1:   (1-c)(3c^2+14c-1), used when c>=1/3.

All are nonnegative; the last bracket is at least4 when c>=1/3.

At a=1, R decreases in b because its b coefficient is

    -12c^2+5c-1<0.

Its minimum is therefore at b=min(3c,1). The endpoints give

    b=3c: c(7+16c-39c^2)>0 when c<=1/3,
    b=1:  (1-c)(3c^2+14c-1)>0 when c>=1/3.

For the first, 39c^2<=13c gives its bracket>=7+3c>0. Thus R>=0 throughout.

**C. b>=3c.**

Now current0 is nonpositive and next0 nonnegative. Direct cancellation gives

    6(1-c)[h*Psi_next-Psi]
      =c[12-5c+b(6-13c)-a(b-6c+5)].              (FC)

Because b>=3c and b<1, one has c<1/3. The coefficient b-6c+5 is positive,
so a<1 bounds the bracket below by

    7+c+b(5-13c)>0.

This proves the claim also in CaseC. The formulas agree at b=c and b=3c.

### 7. Every kappa<=0 and the true retained successor


Only V_next depends on kappa, and

    V_next(kappa)=V_next(0)+kappa*bc/[(1-b)(1-c)]
                  <=V_next(0).

For fixed E_next>=0,F_next>0, Psi(V,-E_next,F_next) is nonincreasing in V:
its slope is-1 for V<0 and-E_next/6 for V>0. Therefore decreasing kappa from0
can only increase Psi_next. The full-step inequalities proved above remain
valid for every kappa<=0.

For a03 atom in the retained clock, its right successor exists because the
atom is isolated in compact T (there is a positive gap and then a closed
nonempty remainder). No physical mass lies between. The next conditional value
there is exactly -c/(1-c). At that true legal query Q0>-1, including Q0=0 at
a non-atomic query or the final mark. Thus c<1/2 as used above; no new deadline
has been inserted. The support catalogue includes all boundary cases: with
w1<0 some a>0 is forced, leaving solo0,01,03,013; at w1=0, b>0 forces solo1,
and otherwise solo0,03,or an empty row remains. All full cases retain the
literal tie terms; no higher-order term has been deleted from the inequalities.

Since h<=1, the atom inequalities above show Psi'>=Psi whenever Psi>0,
through every physical atom and every support switch.

### 8. Continuous pieces and accumulations


On the non-atomic part every w_i>=0. In the sign region w1<=0,w3>0 this means
w1=0; diffuse3 is impossible because its own contact value would need0.
Diffuse1 occurs only at w1=0 and w0>=0. Its exact (BV) derivative gives

    d Psi=(Psi+1) d lambda1 >=0.

For diffuse0, its own contact additionally gives w0=0. Here (BV) gives

    dw1=6 d lambda0, dw3=(w3-1) d lambda0,
    d Psi=(dw1/6)+dw3=Psi d lambda0 >=0.

In fact the nonpositive1 invariant and the derivative on its zero level set
exclude positive diffuse0 mass, but that extra exclusion is unnecessary for
the Psi inequality. Mixed continuous activity is handled by additivity of
(BV); all coefficients above are nonnegative on their physical contact sets.
At w0=0 the two branches of Psi agree; the bounded-variation chain rule for
min/max gives no additional signed contribution. The derivative of a BV
function on a fixed level set is0 for its continuous measure part, so the
formula is unaffected by branch points.

Combining continuous monotonicity with the atom inequalities proves Psi is
nondecreasing throughout the original compact marked clock, including all
accumulations. It starts positive, but w(c)=0 implies Psi(c)=0, a contradiction.
This proves the complete retained-clock barrier.

### 9. The genuine03 head, all tail1 signs, and player2 entry

Let the genuine03 head hazards be (r,0,0,t), with 0<r,t<1. Its active0 and3
current offers are3t and2r, while their passive offers are4t and r. The exact
Nash equations at the genuine E tail Y therefore give

    Y0=-t/(1-t)=-A<0,
    Y3=r/(1-r)=D>0.

The head's passive1 offer is6(t-r), so its ORIGINAL player1 output is

    U1(X)=[Y1+6(A-D)]/[(1+A)(1+D)].              (HEAD1)

If Y1>0, the first retained legal tail query has own1 hazard b=0 because its
forced offer Q1=-7a-c<=0 cannot equal positive Y1 on positive own mass.
Then Q0=3c>=0, contrary to its full-cap inequality Q0<=Y0<0. Thus Y1>0 is
already impossible for a core-only tail, independently of kappa.

If Y1<=0, the compact barrier applies to Y: positive3 and nonpositive1 have
been derived at this SAME original tail. Since Y0<0,

    Psi(Y)=Y1/6+A+D
          =[(1+A)(1+D)/6] U1(X)+2D>0.           (HEAD2)

This contradicts the proved core-only barrier when kappa<=0. Both cases
contradict N2(Y)=1. Therefore N2(Y)<1. The missing mass is genuine finite
player2 probability in the retained representation, not escaped finite mass
relabeled Never. This completes the theorem without a tail1 sign assumption
or any subsequent support hypothesis.

## Exact boundary tests

**An actual positive test realizes the head and the forced entry.** In addition
to the core table with any k>=2, set all rewards to player2 equal to0. Set

    (Z0(2),Z1(2),Z3(2))=(-1/5,-1,1/50),
    Z_i({i,2})=Z_i(2) for each core i in{0,1,3}.

Set all other unused off-core rewards to0. At the tail's conditional dateZERO,
let only player2 quit with probability1/2; everyone else plays literal Never.
Every core player receives

    Y=(-1/10,-1/2,1/100)

in core coordinate order0,1,3. Quitting at that same conditional date ties with
player2 and has the identical value because Z_i({i,2})=Z_i(2); every later
finite deadline and Never has the same value. Player2 always gets0. Thus this
is an actual complete-law four-player E tail with all original Never positive.
There is NO empty date before its conditional singleton2 atom.

Prepend a03 row at GLOBAL dateZERO with r=1/101,t=1/11; the singleton2 tail
atom is now at GLOBAL dateONE. Its exact core outputs are

    U0(X)=3/11, U1(X)=40/1111, U3(X)=2/101,
    Psi(Y)=2/75>2D=1/50.

The two active head players are indifferent by the exact head equations;
player1's head Quit offer is negative and its Continue value positive;
player2 always gets0. The entire two-date profile is therefore exact Nash
against every complete stopping-law replacement. Its original Never marginals
are

    (N0,N1,N2,N3)=(100/101,1,1/2,10/11).

This verifies the actual source/head hypotheses and the strict conclusion
N2=1/2<1. No accuracy-dependent target or unsupported source realization is
used by this test.

**The sign/strict-barrier hypotheses cannot simply be omitted.** Let only
player3 have a finite atom s in(0,1), all other laws literal Never. In the core,
this is exact complete-law Nash:0 gets4s and joining now gives3s;1 gets6s and
joining gives-s;3 gets0 from every reply. Later finite queries equal Never.
Set Z2(3)=Z2(23)=-5. Then2 gets-5s both from Never and
joining at the atom, and every later query gives the same payoff. Thus it is
also an actual four-player zero-debt profile with positive original Never,
for any k>=2 and every finite completion of the unused rewards. Its core value
is(4s,6s,0) and Psi=s(1+4s)>0. It lies outside w1<=0,w3>0 and outside the genuine
head, so it is a necessary domain test rather than a counterexample. Its
absorbing pure3 endpoint is Nash; no positive absorbing-gap claim is made.

At AllNever, w=0 and Psi=0, so the strict-positive barrier correctly supplies
no contradiction. The theorem also makes no assertion when k<2: decreasing
kappa's sign in the proof is an actual hypothesis, not a discarded tie error.

## Adapter and consumer

Given the genuine03 source head in C, continuous finite-prefix identities retain
its full caps and original Never. The existing global first03 source has
positive U1(X), so it supplies the theorem's strict head sign directly.
The exact head equations produce Y0<0,Y3>0. If Y1>0, one full tail query
contradicts core-only play. If Y1<=0, (HEAD2) produces positive Psi at that
SAME genuine tail. No favorable tail sign or minimizing tail is assumed.

If the source had no future2 activity, N2(Y)=1. The complete representation
above retains that identity, and the all-switch compact barrier consumes it.
The output is the strict original probability statement N2(Y)=N2(X)<1.
This is a complete consumer for the entire N2=1 branch of a genuine first03
source on k>=2, not a supplied strategy verifier. The proof does not produce
that source for arbitrary games, and a later finite2 excursion still needs its
own consumer before reaching a terminal semantic endpoint.

## Lean handoff

The new reusable generic pieces are a retained complete-law conditional-value
object with computed full caps and Fubini, its bounded-variation suffix
identities, and the scalar min/max barrier. The original-N preservation and
full-menu representation should be proved from actual realizing sequences,
not included as fields asserting the desired barrier or forced entry.

Likely declaration shapes are a core retained-clock lemma asserting
`Psi initial <= 0` from zero computed debt, positive original Never,
`kappa <= 0`, `initial 1 <= 0`, and `0 < initial 3`; and a genuine03-prefix
corollary asserting `N 2 < 1` from its exact proper Nash row and the original
strict positive1 output. Prove the finite scalar atom inequalities separately,
including the endpoint-concavity certificate and the zero1/solo1 boundary.
Then prove the original-N BV adapter and scalar trap, and finally the exact03
head identities. No structure field should postulate eventual support,
monotonicity of Psi, or the conclusion.

Reuse the checked root/continuation maximum theorem cited above. The terminal
selection and debt-infimum equivalence are semantic endpoints, not new
hypotheses to be assumed. The actual marked compiler and the global barrier
are not currently claimed implemented here. No repository refactor or
additional axioms are prescribed. After implementation the narrow checks are
the directly changed Lean modules with one compiler worker, followed by the
repository trust, import and documentation checks required for promotion.
No Lean command or build is part of the mathematical evidence in this packet.

## Scope and nonclaims

This is a mathematical source-class exclusion, not an existence theorem for
all k>=2 tables. It excludes the ENTIRE N2=1 continuation of a genuine03 head
with positive original player1 output, including compact and diffuse portions,
all tail1 signs, all later core histories and isolated-END cases. It assumes no
first013 entry, positive player2 payoff, cofinality, source attainment or
minimizing tail. It does not consume later finite2 excursions, other first-row
source modes, or arbitrary Fin4. It introduces no L/A/C seal.

## Exact algebra reproduction

The following complete symbolic checker uses Python3 and SymPy. It checks the
head and every atom identity/endpoint factor printed in the proof; the proof
of their signs and the BV argument are the mathematics above, not conclusions
inferred from symbolic output.

```python
import sympy as s

a,b,c,V,E,F=s.symbols('a b c V E F')
zero=lambda z: s.factor(z)==0
A,D,Y1=s.symbols('A D Y1')
r=D/(1+D);t=A/(1+A)
X1=6*(t-r)+(1-r)*(1-t)*Y1
assert zero(X1-(Y1+6*(A-D))/((1+A)*(1+D)))
assert zero((Y1/6+A+D)-((1+A)*(1+D)*X1/6+2*D))
print('PASS: exact genuine03 head output and strict barrier identity')

# Solo0.
assert zero((1-a)*((F-a)/(1-a)-(E-6*a)/(6*(1-a)))-(F-E/6))
# Pair01.
h=(1-a)*(1-b)
Et=a/(1-a);Ft=(F-a+b)/h;Vt=b/(1-b)
assert zero(h*(Ft-Et*(1+Vt)/6)-(F-7*a/6+b))
# Solo1, negative V branch; positive V branch is the same without min term.
assert zero((1-b)*(F+b)/(1-b)-(F-V)-(b+V))
# Pair03.
h=(1-a)*(1-c)
Et=(E-6*a+6*c)/h;Ft=a/(1-a);Vt=-c/(1-c)
ps=2*a-E*(1+3*c)/6;pt=Ft-Et/6-Vt
assert zero(h*pt-ps-c*(E-4*a)/2)
d=h*(1+3*c)-1
assert zero(h*(pt-ps)-2*a*a*(1-c)-E*d/6)
assert zero(2*a*a*(1-c)+4*a*d/6-(2*a/s.Integer(3))*(2-3*c)*(a*(1-c)+c))
print('PASS: solo0/01/solo1 identities and pair03 certificate')

# Full013, kappa=0.
h=(1-a)*(1-b)*(1-c)
Et=(a+7*c)/((1-a)*(1-c))
Ft=(a-b)/((1-a)*(1-b));Vt=(b-c)/((1-b)*(1-c))
psA=2*a-2*b-(7*a+c)*(1+3*c-b)/6
ptA=Ft-Et/6-Vt
assert zero(h*ptA-psA-c*(3*a+4*b+c)/2)
ptBC=Ft-Et*(1+Vt)/6
R=a*(6*b*c-7*b-15*c*c+16*c)-12*b*c*c-b*c+6*b-3*c**3+16*c*c-6*c
assert zero(6*(1-c)*(h*ptBC-psA)-R)
R_ab=s.expand(R.subs(a,b));R_a1=s.expand(R.subs(a,1))
assert s.Poly(R_ab,b).coeff_monomial(b*b)==6*c-7
assert zero(R_ab.subs(b,c)-24*c*c*(1-c))
assert zero(R_ab.subs(b,3*c)-2*c*(3*c+2)*(3-5*c))
assert zero(R_ab.subs(b,1)-(1-c)*(3*c*c+14*c-1))
assert s.Poly(R_a1,b).coeff_monomial(b)==-12*c*c+5*c-1
assert zero(R_a1.subs(b,3*c)-c*(7+16*c-39*c*c))
assert zero(R_a1.subs(b,1)-(1-c)*(3*c*c+14*c-1))
psC=2*a-2*b-(7*a+c)/6-(3*c-b)
RC=c*(12-5*c+b*(6-13*c)-a*(b-6*c+5))
assert zero(6*(1-c)*(h*ptBC-psC)-RC)
assert zero((RC/c).subs(a,1)-(7+c+b*(5-13*c)))
print('PASS: all three full013 cases and exact endpoint positivity factors')
```
