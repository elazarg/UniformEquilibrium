# Zero active payoffs on the original semantic closure force absorbing approximation

## 1. Exact statement

There are four players I={0,1,2,3}. A real reward vector Z(S) is specified
for every nonempty subset S of I. Assume Z_i({i})=0 for each i. The live
state and the event that nobody ever quits pay zero. Fix M>=1 bounding
the absolute value of all sixty rewards.

Each player independently chooses a complete stopping time in the natural
numbers together with a separate point Never. The first finite tied
coalition receives Z. A unilateral deviation may replace the player's
entire law, including every finite deadline and Never. Write U_i for the
prescribed expected reward, B_i for the supremum over all such unilateral
responses, N_i for the ORIGINAL marginal probability of Never, and

    d_i=B_i-U_i,       D=SUM_i d_i,       nu=PRODUCT_i N_i.

Let H be the Euclidean closure of all actual tuples (U,B,N), and set

    E={X in H : B=U},
    alpha=min_(X in E) nu(X),
    A=inf{D(P) : P actual and nu(P)=0}.

The minimum exists: H is compact, and literal AllNever belongs to E.
The quantity A concerns almost-surely ABSORBING profiles. The native
unrestricted debt infimum is already zero because AllNever is exact Nash.

**Semantic renewal theorem.** Suppose X=(U,U,N) belongs to E and

    0<nu(X)<1,       U_i>=0 for every i,
    U_i(1-N_i)=0 for every i.                         (1)

Then A=0. More explicitly, for every epsilon>0 there is an ACTUAL
independent complete-law profile that absorbs almost surely and whose
full unilateral SUM debt is below epsilon. No actual-law realization
of X is assumed.

**Least-Never consequence.** If A>0, every minimizer X=(U,U,N) of nu
on E satisfies U>=0 and alpha>0. If alpha<1, then

    U_i>0 and N_i<1 for at least one player i.        (2)

Thus no all-zero-payoff least-Never source can have alpha<1. If exactly
three payoff coordinates are zero, its unique positive-payoff player
must have strictly positive finite stopping mass. The case alpha=1 is
unaffected. In fact, at these least-Never sources, U=0 if and only if
alpha=1. The statements concern original marginal Never probabilities,
including at semantic closure points.

**Cross-source consequence.** If A>0, X is any least-Never source, and
Y=(V,V,K) is any point of E with V>=0 and PRODUCT_i K_i<1, then

    N_i(X)<1 and V_i>0 for at least one player i.     (2a)

In particular, if some such Y has exactly one positive payoff coordinate
j, every least-Never source has N_j<1. The two sources may have entirely
different approximating laws and calendars.

## 2. Conjecture-facing change and strategic inputs

A hypothetical arbitrary signed four-player counterexample produces a
native own-zero table with A>0; Section 7 gives the complete adapter using
the implemented single-pivot normalization. Compactness then produces the
least-Never source without a calendar assumption. Conclusion (2) excludes
every source below alpha=1 whose finite-mass players all have zero payoff.
In particular it removes the entire all-zero payoff stratum below that
endpoint and the pure-Never-positive-observer part of a three-zero stratum.
The cross-source statement constrains all least-Never sources at once:
their finite-mass supports must meet each nontrivial nonnegative zero-debt
payoff support, not merely their own.

The new source-to-conclusion step is closure-level repetition with original
Never coordinates. It applies even when approximating profiles have small
positive finite masses for players whose limiting N_i is one. No uniform
denominator bound for an infinite periodic replay is needed.

The producer uses only an actual realizing sequence for X, finite tail
censoring, two copies of a finite block, and a final completion of one
player's Never mass. These objects are constructed in the proof. There is
no supplied equilibrium continuation, finite-support source, positive
absorption rate, root selection, or tail-minimum assumption.

The theorem leaves sources with a positive-payoff finite-mass player open.
It does not prove arbitrary signed Fin4 existence, or produce a positive-A
table. Its absorbing approximation is stronger than native UE existence,
which is trivial for an own-zero table.

## 3. Complete-law semantics and finite approximation

Along the unique live history, a behavioral deviation determines a
distribution of its first Quit date, with the probability of never
quitting retained separately. Conversely any such distribution is realized
by its conditional hazards. Private randomization is independent across
players; no public randomizing device is used. A mixed complete response
averages pure finite-deadline and pure Never response payoffs. Therefore
their supremum is exactly B_i, including for a fully history-dependent
unilateral behavioral deviation.

For an actual profile P let e_i(P) be the payoff of its pure Never response.
Since every response payoff is at most B_i, averaging over the prescribed
own law gives

    e_i<=B_i,
    U_i <= N_i e_i+(1-N_i)B_i,
    0<=B_i-e_i <= d_i/N_i                 if N_i>0.  (3)

Consequently, if actual tuples converge to (U,U,N) with every N_i>0,
their pure Never payoffs converge to U_i. This derives the missing
coordinate from the retained data and does not exchange a supremum
with a limit.

For any actual law profile, move all of each player's finite mass after
a sufficiently large date to that player's own Never atom. If the sum
of the moved masses is eta, a coupling changes each prescribed payoff
by at most 2M eta. Against any fixed replacement law of i, only opponents'
changed draws matter, so the same bound is uniform over ALL replacements.
Taking suprema gives |B_i(new)-B_i(old)|<=2M eta. The same estimate applies
to e_i, and the marginal Never coordinates change by at most eta.

Thus every X=(U,U,N) with positive N has a sequence of finite-support
actual profiles P^m for which

    U(P^m)->U, B(P^m)->U, e(P^m)->U, N(P^m)->N.      (4)

The finite horizon may depend on m. Its value will never be held fixed
while passing to the semantic source.

## 4. The exact two-copy operation

Take any actual finite-support block P. Choose L so that every occupied
date is strictly less than L-1. The date L-1 is unused by every player.
It represents the block Never response as a finite response: after all
opponents' finite dates, forced Quit adds only the own singleton zero.
Hence the response payoff at L-1 is e_i. All later finite replies also
have that value. The complete one-block cap B_i is therefore the maximum
over the finitely many deadlines 0,...,L-1.

Each player independently draws a first block time from P_i. If that
draw is finite, it is used. If it is Never, the player draws a fresh
independent time from P_i and uses its shift by L, or retains literal
Never if the second draw is Never. Equivalently, at each reached block
the same private conditional hazards are used. This defines an actual
complete product law on natural dates. Denote the resulting profile by P*P.

Put h_i=PRODUCT_(j!=i) N_j and nu=PRODUCT_j N_j for the block. Directly,

    U_i(P*P)=(1+nu)U_i(P),
    N_i(P*P)=N_i(P)^2,
    B_i(P*P)=max{B_i(P), e_i(P)+h_i B_i(P)}.         (5)

The first identity splits prescribed play according to whether all players
survive the first block. Its probability is nu. For the cap identity, a
pure deadline in the first block has exactly its original block payoff.
A deadline in the second block has payoff

    e_i(P)+h_i g_i,

where g_i is the corresponding first-block response payoff. Opponents'
first-block finite exit contributes e_i(P), and their joint first-block
Never event has probability h_i. Literal Never has payoff
e_i(P)+h_i e_i(P), which is no larger than the second term in (5).
Every later finite deadline has that same payoff. These cases exhaust
all pure responses; arbitrary complete responses average them. The unused
last date ensures the first maximum includes the original Never cap even
if its value is negative. No newly available boundary query is omitted.

Apply (5) to the sequence (4). Continuity of multiplication and maximum
shows that H contains the point X*X given by

    U_i'=(1+nu)U_i,
    B_i'=max{U_i,(1+h_i)U_i},
    N_i'=N_i^2.                                      (6)

This is a statement about a limit of actual finite two-copy laws. It does
not execute an infinite source block before starting a second block.

Under (1), (6) is zero-debt. If U_i=0, both new entries are zero. If
U_i>0, then N_i=1, so h_i=nu and

    B_i'=(1+h_i)U_i=(1+nu)U_i=U_i'.

The new payoffs remain nonnegative and still satisfy U_i'(1-N_i')=0.
The joint Never probability is nu^2. Thus the same operation can be
applied again to its output in H.

The same argument permits DIFFERENT sources. Let X=(U,U,N) belong to E
with every N_i>0, and let Y=(V,V,K) belong to E with V>=0. Choose the
finite padded approximants to X from (4), and any actual approximants
to Y. After surviving the first finite block, use the second actual law,
shifted by the FIRST block's finite length. The second law can be infinite; it
has no prescribed infinite block placed before another law.

For an actual first block P and actual continuation Q, the same response
split gives U_i(P*Q)=U_i(P)+nu(P)U_i(Q) and

    B_i(P*Q)=max{B_i(P), e_i(P)+h_i(P) B_i(Q)},
    N_i(P*Q)=N_i(P)N_i(Q).

Taking the two approximating limits simultaneously proves that H contains

    U_i'=U_i+nu(X)V_i,
    B_i'=U_i+h_i(X)V_i,
    N_i'=N_i K_i,
    d_i'=h_i(X)(1-N_i)V_i.                           (6a)

The maximum simplifies because V_i>=0. These formulas control the full
cap of the continuation, including every finite date and literal Never.
Since all h_i(X)>0, the concatenation is zero-debt exactly when
(1-N_i)V_i=0 for every i.

## 5. Arbitrarily many copies and actual absorbing profiles

Starting from X in (1), iterate the semantic two-copy construction.
For every integer k>=0 it produces a point X_k in E with

    N_i(X_k)=N_i(X)^(2^k),
    nu(X_k)=nu(X)^(2^k).                             (7)

Every X_k is obtained through finite repetitions and limits of actual
finite-support profiles as in Section 4. No infinite concatenation of
unrealized semantic points is used.

Here is a completion estimate for any actual profile P. Choose a player
with the smallest original Never mass n and move that mass to any one
finite date. The resulting profile absorbs almost surely. The mover's
cap is unchanged because it depends only on opponents' laws. Each of
the four prescribed values changes by at most 2Mn, and each of the other
three full caps changes by at most 2Mn. Therefore

    A <= D(P)+14M n <= D(P)+14M nu(P)^(1/4).          (8)

The second inequality follows because every marginal Never mass is at
least n. Uniform coupling controls Never and all finite responses before
their supremum is taken. The right side is continuous on H, so (8)
also holds at every semantic point.

Apply (8) to X_k. By (7),

    0<=A<=14M nu(X)^(2^k/4) ->0.

This proves A=0. To spell out the actual producer, given epsilon>0
choose k making the displayed bound smaller than epsilon/3. Choose an
actual finite-support approximant of X_k with D<epsilon/3 and
14M nu^(1/4)<2epsilon/3. Complete its least Never mass as above; its full
SUM debt is below epsilon and its prescribed play absorbs almost surely.

The order of choices matters: first fix the finite number of copies,
then choose the actual approximation sufficiently accurate. No error is
multiplied through an unbounded number of copies at fixed approximation.

## 6. Least-Never sources and positive active payoff

The set H is compact because U,B belong to [-M,M]^4 and N to [0,1]^4.
Each d_i is nonnegative on actual tuples and hence on H. AllNever gives
a point in E, so E is nonempty compact and alpha is attained. Applying
(8) on E shows

    alpha >= (A/(14M))^4.                            (9)

Assume A>0 and let X=(U,U,N) minimize nu on E. All N_i are positive.
We next prove U>=0 without assuming an actual realization of X.

For independent current Quit probabilities q_i, put

    H_i=PRODUCT_(j!=i)(1-q_j), h=PRODUCT_j(1-q_j).

Let Q_i be the expected current reward when i Quits, and P_i the expected
current reward from nonempty opponent coalitions when i Continues.
Prefixing actual play has the exact full semantic formulas

    U_i'=q_i Q_i+(1-q_i)(P_i+H_i U_i),
    B_i'=max{Q_i,P_i+H_i B_i},
    N_i'=(1-q_i)N_i.                                 (10)

Every pure response either quits now or Continues and then uses an
arbitrary full old response, which proves the cap identity. The formulas
are continuous, so prefixing an actual realizing sequence proves (10)
also maps H into H.

The finite root game with continuation U has a mixed Nash equilibrium.
At such a root, the prescribed payoff in (10) equals the maximum of
its two response endpoints because B=U. Thus the output lies in E.
If any q_i>0, its original joint Never is h alpha<alpha, contradicting
minimality. Every root equilibrium must therefore be AllContinue.
Its Nash inequalities are exactly U_i>=Z_i({i})=0. This proves U>=0.

If alpha<1 and (2) failed, U_i(1-N_i)=0 for every i. Section 5 would
give A=0, a contradiction. Alternatively, the first doubling already
gives an E competitor with Never alpha^2<alpha. If exactly three U_i
are zero, the fourth is positive by hypothesis and must be the player
in (2). In particular its original N_i is strictly below one.

For every actual tuple, |U_i|<=M(1-nu): the reward vanishes on the
original joint Never event and is bounded by M otherwise. This inequality
passes to H. Hence alpha=1 forces U=0. The converse for least-Never
sources follows from the preceding exclusion, proving the claimed
equivalence.

Finally apply (6a) to a least-Never X and a source Y from (2a). If the
asserted intersection were empty, the resulting point would belong to E
and would have joint Never alpha PRODUCT_i K_i<alpha, a contradiction.
This proves the cross-source consequence, including its unique-positive-
coordinate specialization. Only the prefix source must be least-Never;
the continuation source can be any nonnegative-payoff point of E.

## 7. Adapter from arbitrary signed Fin4 no-UE data

Suppose an arbitrary signed four-player table r has no uniform-equilibrium
payoff. The implemented theorem
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`
produces a positive pivot m and a literal normalized table R with

    R_m({m})=1, R_i({i})=0 for i!=m,

which also has no uniform-equilibrium payoff. Its inputs are the
no-uniform-payoff assumption and a reward bound, which exists for the
finite table. The theorem supplies the punishment-normal conditions
needed by its normalization; no unproved invariance under arbitrary
row shifts is assumed here.

By `quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
in `UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean`,

    delta_R=inf_(P actual) D_R(P)>0.

Subtract one from the pivot RECIPIENT row at every nonempty coalition:

    Z_i(S)=R_i(S)-1_(i=m).

Keep the live and AllNever rewards zero. Then all own singletons of Z
are zero. Both R and Z have nonnegative own singletons. For any table
with own singleton s_i>=0, forcing a finite deadline tending to infinity
has payoff tending to its pure Never payoff plus

    s_i PRODUCT_(j!=i) N_j.

On opponents' finite-exit events the deadline eventually occurs later;
on their joint Never event it earns the singleton. Bounded convergence
proves the identity. Hence the finite-deadline supremum already dominates
Never and equals the full cap for both R and Z. This agrees with
`quittingTerminalPayoff_update_finiteTime_tendsto_of_profile` in
`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`.

At an ABSORBING prescribed profile, the pivot's prescribed payoff under
Z is its R payoff minus one. Every finite forced reply also absorbs and
shifts down by one; therefore the full cap shifts down by one too.
Every debt is unchanged. It follows that

    A_Z=inf_(nu(P)=0)D_R(P) >= delta_R>0.             (11)

This constructs exactly the positive-A input to Section 6. It does not
assert that Z lacks a uniform equilibrium: its AllNever profile is
already one. The contradiction uses the absorbing debt infimum only.

## 8. Exact boundary tests

The following formulas specify every entry of each sixty-entry table.
All unspecified rows in a formula are explicitly zero.

### 8.1. Positive observers are allowed

Fix a_1,a_2,a_3>=0. Set Z_0(S)=0 and, for j=1,2,3, set

    Z_j(S)=a_j if 0 belongs to S, and 0 otherwise.

Let player 0 use date 0 with probability p in (0,1), and Never otherwise;
all other players use Never. Its exact full values are

    U=B=(0,p a_1,p a_2,p a_3), N=(1-p,1,1,1).

For an observer, quitting at date 0, later, or Never always gives p a_j;
player 0 always gets zero. After l copies, observers' prescribed and cap
values are [1-(1-p)^l]a_j. Every copied profile is exact Nash and its joint
Never is (1-p)^l. Making player 0 quit surely is an absorbing exact Nash
profile. This test includes nonzero positive payoffs and N_-0=1, the
denominator boundary that infinite-replay formulas can mishandle.

### 8.2. Positive active payoffs really create replay debt

Define Z_0(S)=1 if 1 belongs to S and zero otherwise; define Z_1(S)=1
if 0 belongs to S and zero otherwise; set Z_2(S)=Z_3(S)=0.
Players 0 and 1 each use date 0 with probability 1/2 and Never with
probability 1/2; players 2 and 3 use Never. Every pure response of player
0 or 1 earns 1/2, so

    U=B=(1/2,1/2,0,0), N=(1/2,1/2,1,1), nu=1/4.

Two copies have U_0'=U_1'=5/8 and B_0'=B_1'=3/4. Each active player's
debt is 1/8. Thus nonnegative payoff and positive Never alone do not
make repetition debt-free. Both players quitting surely at date 0 gives
an absorbing exact Nash profile; this control has A=0 and is not a
counterexample to a genuine positive-A source theorem.

### 8.3. Negative passive payoff cannot be ignored

Set Z_1(S)=-1 if 0 belongs to S and zero otherwise, and set every other
row to zero. Let player 0 use date 0 with probability 1/2 and Never
otherwise; every other player uses Never. The exact full values are

    U=B=(0,-1/2,0,0), N=(1/2,1,1,1).

Every response of player 1 gives -1/2: there is no earlier date before
date 0, and joining, waiting, and Never all have that expectation.
Two copies give U_1'=-3/4 and B_1'=-1/2, with debt 1/4. All active
payoffs were zero, but the observer was negative. This verifies the
nonnegative-payoff premise in (1) and the signed maximum in (6).

### 8.4. The AllNever endpoint

At N=(1,1,1,1), actual AllNever has U=B=0 for every own-zero table.
Two-copy repetition leaves that point unchanged. The argument yields
no smaller Never probability there. Thus alpha=1 cannot be discarded
by taking a limit of the strict inequality alpha^2<alpha.

## 9. Implemented correspondence and Lean handoff

The complete-law quantities agree with the implemented unrestricted
behavioral quantities by
`quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff` and
`quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
in `UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`.
The same file's
`abs_quittingStoppingLawReplacementPayoffCap_sub_le_opponents`
provides the uniform cap continuity underlying finite tail censoring.

The implemented
`quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
in `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean` controls an exact
Nash root against a supplied continuation cap. It is useful for Section 6,
but does not supply the whole-block operation in Sections 3--5: that
operation first recovers pure Never payoff at a closure point, keeps the
original marginal Never coordinates, and concatenates finite realizers.
No claim that each root of the new block is Nash against its suffix is
needed or made.

The new formal targets are the following ordinary-mathematical statements:

1. At a positive-Never zero-debt point of the original augmented semantic
   closure, finite-support realizers can also realize pure Never payoff U.
2. The exact two-copy formula (5), including every response query, passes
   to the closure formula (6).
3. Nonnegative zero active payoffs imply arbitrarily small joint Never
   at zero debt, then actual absorbing SUM debt arbitrarily close to zero.
4. A positive-A least-Never source below one has a positive-payoff player
   with N_i<1.
5. More generally, its finite-mass support meets the positive-payoff
   support of every nonnegative zero-debt source with joint Never below
   one, by the two-source concatenation (6a).

The source adapter uses existing checked declarations; the new renewal
and source restrictions are ordinary mathematics to be formalized.
An actual source realizer, an infinite repetition certificate, or the
desired absorbing approximation must not be introduced as an assumed
field in the formal statement.
