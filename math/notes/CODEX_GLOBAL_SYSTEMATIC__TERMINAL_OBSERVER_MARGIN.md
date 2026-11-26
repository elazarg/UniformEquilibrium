# A sharp raw test for simultaneous observer Never margins

Owner: CODEX_GLOBAL_SYSTEMATIC. Complete ordinary-mathematical proof;
review status and artifact hashes are recorded in the accompanying feedback.
Internal result, not an export or a Lean claim.
Fin4 remains open. The raw test below is not supplied automatically by an
arbitrary-counterexample source.

A one-dimensional optimization of twelve rewards gives the exact largest
common observer cap-minus-Never margin, over both actual exact-observer
profiles and their larger semantic partial-Nash carriers. A quantitative
bound handles approximate observer optimality before passing to a limit.
Thus failure of the raw strict-collision test forces a Never-active observer
at an actual OR nonrealized global absorbing partial-Nash minimum.

For actual profiles, Section5 also proves exact finite-calendar realization
of the entire payoff/cap/Never-value/Never-mass tuple when one exact player
has a strict gap above both Never and its late-deadline limit. In native
own-zero tables, one strict observer Never margin suffices.

## 1. Original-game semantics and statement

There are four players I, a pivot p, and observers S=I\{p}. Each privately
and independently draws a complete stopping law on Nat plus a separate
Never label. The first nonempty quitting coalition A pays r(A); live play
and AllNever pay zero. ALL terminal rewards, including own singletons,
are arbitrary signed reals with |r_i(A)|<=M, M>=1. This is a direct theorem
about the original table; it uses no normalization or shift of Never.

Let U_i be prescribed payoff, B_i the full supremum over all unilateral
complete laws, and e_i the payoff from the literal pure-Never response.
Finite deadlines and Never price this entire response menu by affinity.
Write

    d_i=B_i-U_i>=0,       D=sum_(i in S) d_i,
    g=min_(i in S)(B_i-e_i)>=0.

For each observer define

    A_i=r_i(S)-r_i(S\{i}),
    C_i=r_i(I)-r_i(I\{i}),
    L_i(x)=(1-x)A_i+x C_i,
    Lambda_p=max_(0<=x<=1) min_(i in S) L_i(x),
    Lambda_p^+=max(0,Lambda_p).                                (1)

**Quantitative theorem.** Every actual profile, with arbitrary supports
and arbitrary absorption probability, satisfies

    g <= Lambda_p^+ + 4 sqrt(M D).                            (2)

Let H_all be the compact closure of actual tuples (U,B,e), and H_abs the
closure of their absorbing subclass. Here absorbing means that the first
quitting date is finite almost surely. Inequality (2) passes to both
carriers. On E_p={X in H_abs:d_i(X)=0 for i in S}, and also on the analogous
subset of H_all, its exact zero-error consequence is sharp:

    max_(X in E_p) min_(i in S)(B_i-e_i)=Lambda_p^+.            (3)

The SAME maximum is attained over actual absorbing exact-observer
profiles, and over all actual exact-observer profiles. Thus strict positive
margins for all three observers are possible exactly when Lambda_p>0.
When Lambda_p<=0, every augmented partial-Nash point has B_i=e_i for at
least one observer. That owner may depend on the point and its augmented
lift. No positive prescribed Never mass is inferred from a Never best reply.

## 2. The common final-date lemma

First consider any actual profile for which every observer is proper and
EVERY finite deadline used with positive probability by observer i has
response offer V_i(t) exceeding its Never offer e_i by a fixed positive
amount. Exact observer optimality is NOT assumed in this lemma.

Each observer faces another proper observer. Therefore V_i(t)->e_i as
t->infinity: under a coupling of the opponent clocks, some opponent stops
finitely almost surely, and every sufficiently late deadline then has
exactly the Never outcome. Bounded convergence applies even with arbitrary
signed own-singleton rewards. The uniform strict margin consequently makes
each observer's prescribed support finite. Let T_i be its last support date.

If T_i>T_j for different observers i,j, opponent j surely stops before the
used deadline T_i. That deadline is outcome-equivalent to Never for i,
a contradiction. Thus

    T_i=T for all i in S,       a_i=Pr(clock_i=T)>0.           (4)

The pivot also has a_p=Pr(clock_p>=T)>0, where >=T includes Never. Otherwise
it stops surely before each observer's used deadline T, giving the same
contradiction. Put x=Pr(clock_p=T)/a_p in [0,1].

Compare observer i's deadline T with Never. If an opponent stops before T,
the outcomes agree. Conditional on all opponents reaching T, the other two
observers quit there surely and the pivot quits with probability x. Hence

    V_i(T)-e_i
       = a_p product_(j in S\{i}) a_j * L_i(x).               (5)

All factors are positive and at most one. The SAME x therefore satisfies
all three strict terminal comparisons, and

    min_i [V_i(T)-e_i] <= min_i L_i(x) <= Lambda_p.            (6)

For an actual exact-observer profile with B_i>e_i for every observer, the
lemma applies directly. Indeed its prescribed law averages offers at most
B_i to exactly B_i. It therefore places mass only on maximizing responses,
and its Never mass is zero because e_i<B_i. All observers are proper, and
every used offer exceeds Never by B_i-e_i. This argument explains why a
native own-zero assumption is unnecessary. It does not assume that an
absorbing prescribed profile alone gives every player a proper opponent.

## 3. Approximate optimality: condition on near-best finite replies

Fix any actual profile and delta>0. Put

    K=delta+4M D/delta.

If g<=K, inequality g<=Lambda_p^++K is immediate. Suppose instead g>K.
For each observer let F_i be the finite deadlines with

    V_i(t)>=B_i-delta.

Never is excluded because B_i-e_i>=g>delta. Prescribed payoff is an average
of response offers, so the mass rho_i outside F_i satisfies

    rho_i<=d_i/delta.

Condition observer i's complete law on F_i and leave the pivot law fixed.
This operation is defined: g<=2M and g>K imply D/delta<1/2, hence rho_i<1.
Each new observer law is proper. Couple it to the old law so that they agree
except on probability rho_i. Against the changed opponent laws, EVERY pure
response offer and the Never offer change by at most

    2M sum_(j in S\{i}) rho_j <= 2M D/delta.                   (7)

This bound is uniform over all deadlines and all complete responses.
Every USED deadline in the new observer law consequently satisfies

    V_i'(t)-e_i'
       >= (B_i-e_i)-delta-4M D/delta
       >= g-K >0.                                           (8)

The new profile need not be exact observer-Nash. Nevertheless (8) and
properness are precisely the hypotheses of Section2. Its observer supports
are therefore finite with one common last date, and (6) gives

    g-K <= Lambda_p.

Together with the trivial branch, this proves, for every delta>0,

    g<=Lambda_p^+ + delta+4M D/delta.

For D>0 choose delta=2 sqrt(MD), obtaining (2). For D=0 let delta decrease
to zero. All bounds retain original full caps and literal Never values;
no cap from the conditioned profile is substituted for an original cap.

## 4. Sharpness and finite computation

If Lambda_p>0, choose a maximizing x in (1). Let all three observers Quit0
surely, and let the pivot Quit0 with probability x and otherwise Never.
For observer i the two complete response offers are

    Quit0:             (1-x)r_i(S)+x r_i(I),
    later or Never:    (1-x)r_i(S\{i})+x r_i(I\{i}).

Their difference L_i(x) is positive. Thus all observers are exact best
responders, the profile absorbs at zero, and its minimum gap is Lambda_p.
There is no earlier deadline, and arbitrary complete mixtures cannot
exceed these two offers.

If Lambda_p<=0, (2) gives g=0 for every exact-observer profile. Such absorbing
profiles always exist: let p Quit0 surely and choose a finite binary Nash
equilibrium of its three observers. Because the pivot stops immediately,
Continue0, every later deadline and Never are outcome-equivalent for each
observer. This finite equilibrium is exact against every complete law.
Hence zero is attained. These witnesses prove the actual maximum claims;
continuity of (2) gives the augmented upper bounds and proves (3).

The scalar Lambda_p is computed exactly by evaluating min_i L_i(x) at
x=0, x=1 and every intersection L_i(x)=L_j(x) inside [0,1]. Parallel or
identical pairs add no point. There are at most five candidate points.
A maximum of a concave piecewise-affine function occurs at one of these
points, including the case of a constant maximizing segment.

The equivalent finite dual test is

    Lambda_p<=0 iff there exists v>=0, sum_(i in S)v_i=1,
                         v dot A<=0 and v dot C<=0.           (9)

This is the two-action finite minimax identity

    max_x min_i L_i(x)=min_(v in the observer simplex)
                                     max(v dot A,v dot C).

At most two observer rows are needed for a failure certificate. Each row's
strict positivity set {x in [0,1]:L_i(x)>0} is an interval. If their finite
intersection is empty, one is empty or two are disjoint, by the elementary
one-dimensional Helly property, which also allows open endpoints. Minimax
for that one- or two-row subsystem supplies a witness of that support.

## 5. Actual source consequence, overlap and remaining work

For the global absorbing partial-Nash source at a fixed pivot, append the
three bounded Never offers to any actual realizing sequence and extract
a convergent subsequence. This yields a lift in H_abs with the SAME payoff
and full-cap pair. Its observer debts vanish. Thus whenever the table's
Lambda_p<=0, every such lift has a Never-active observer. The conclusion
uses the source's existing zero observer debts, not a fabricated actual
profile, exact repair of its approximants, or a different minimum problem.
It applies to native own-zero sources and arbitrary original signed tables.

The strict opposite branch is also concrete. Any ACTUAL exact-observer
profile with all three Never margins positive has the common terminal
collision (4)--(5).

### Exact finite-calendar realization from one late-cap gap

This result holds for any finite game with at least two players. Let N_j
be the ORIGINAL marginal Never masses and define

    END_i=e_i+r_i({i}) product_(j!=i)N_j.

**Finite-calendar theorem.** If an actual profile has one player i with

    U_i=B_i>max(e_i,END_i),                              (10)

there is an actual finite-calendar profile with EXACTLY the same (U,B,e,N)
and the same prescribed terminal outcome law. No other player needs to
be optimal. After a finite cut, each changed opponent needs at most two
finite atoms among at most |I|-1 common dates. No abstract carrier point
is asserted to have an actual realization.

For a pure deadline t, coupling the opponent clocks and bounded convergence
give V_i(t)->END_i. On an outcome with some finite opponent clock, a late
deadline agrees with Never. When all opponents Never, it pays r_i({i})
instead of zero. This proves the limit for arbitrary signed original tables.

Put kappa=B_i-max(e_i,END_i)>0. Exactness implies that every used response
attains B_i. Thus i uses no Never and has bounded finite support, say up to
T0. Choose T>=T0 such that

    sup_(t>T)V_i(t)<=B_i-3kappa/4,
    2M sum_(j!=i)rho_j(T)<kappa/4,
    rho_j(T)=Pr(T<clock_j<Never).                        (11)

The residual finite masses tend to zero. Prescribed play stops by T0;
every deviator j!=i still faces this unchanged clock. Therefore changes
strictly after T leave the prescribed terminal law, U, and EVERY response
payoff of every j!=i unchanged. They also leave i's offers through T
unchanged, including an attained maximizing deadline. Only its late offers
and its Never value need control.

### Scalar weak-order compression with fixed Never masses

Conditional on every opponent's clock being strictly after T, including
Never, the opponent laws remain independent. First suppose this event has
positive probability. Write each conditional law as

    nu_j=n_j Never+(1-n_j)mu_j,

where mu_j is a proper finite-date law. If n_j=1, choose any mu_j because
it is never used. Let psi be i's conditional passive payoff when i Never.

Generate these laws by independently drawing hypothetical finite dates t_j
from mu_j and independent finite/Never flags with probabilities 1-n_j,n_j.
For a deterministic vector t, average only the flags and call the passive
payoff Phi_n(t). It depends solely on the WEAK ORDER of the finite t_j:
which dates tie and which groups come first. There are finitely many such
ordered partitions of the |I|-1 opponents. All are realized by ranks
0,...,|I|-2 on common fresh dates after T.

The actual psi averages these finitely many values. Choose rank vectors
t_minus,t_plus attaining their minimum and maximum. Then

    Phi_n(t_minus)<=psi<=Phi_n(t_plus).

For a deterministic lambda in[0,1], replace each conditional opponent law by

    n_j Never+(1-n_j)[(1-lambda)delta_(t_minus,j)
                                    +lambda delta_(t_plus,j)].

The opponents randomize independently. Their expected passive payoff is a
continuous polynomial in lambda with the two displayed endpoint values.
The intermediate value theorem gives a lambda with payoff exactly psi.
The parameter is common and deterministic; this is not a correlated lottery
over coalitions. Each n_j is unchanged, and the claimed two-atom and common-
date bounds follow.

Uncondition, retaining all probabilities through T. Every original Never
mass is unchanged. Only the distribution of residual finite mass rho_j(T)
has changed, so the full marginal total variation is at most rho_j(T).
Independent coupling bounds the change in every i-response payoff by
2M sum_j rho_j(T), uniformly over the complete response menu. Matching psi
preserves e_i exactly, because all earlier outcomes are retained.

If the conditioning event has probability zero, some opponent stops by T
surely. Relocate each remaining residual finite mass to a fresh finite date,
retaining all Never masses. This has the same total-variation bound and
cannot change any i-response outcome after T. No zero-probability conditional
law is used.

Keep i's bounded clock unchanged. All new laws have finite support plus
Never. The preceding argument preserves U,e,N and every other player's B.
Player i's early maximizing offer is unchanged; (11) keeps every new late
finite offer below B_i, while its exact Never offer is also below B_i.
Its full cap is therefore exactly B_i. This proves (10).

### Native and original-table consequences

For native own-zero tables END_i=e_i. Thus ONE exact observer with
B_i>e_i suffices for finite-calendar realization of the entire (U,B,e,N).
Any actual native exact-observer tuple lacking such a realization must
have ALL its observers Never-active. A realized global absorbing minimum
with one strict observer margin has the SAME minimizing tuple on a finite
calendar. The proof preserves its minimizing property, rather than merely
approximating its value.

For arbitrary original signed tables, TWO exact observers with strict
Never margins still suffice. Both are proper, so each has a proper opponent
and END_i=e_i. Either therefore satisfies (10). A single strict Never
margin alone does not supply (10) when its own singleton is positive and
every opponent has positive Never mass.

The strict late-cap gap is essential, even when an exact player's own clock
is already bounded. In a two-player native game, give player i rewards
0 at {i}, 1 at {j}, and 2 at {i,j}; give j zero everywhere. Let i Quit0
surely and let j use the proper geometric law with hazard1/2. Every finite
deadline and Never gives i exactly1. Thus U=B=e=(1,0) and N=(0,0), an
absorbing exact Nash profile. Any finite-calendar profile with these Never
masses makes j proper with a last atom of mass alpha>0. Quitting at that
last date gives i exactly1+alpha, contradicting B_i=1. Hence this entire
tuple has no finite-calendar realization. Adding two zero-payoff players
whose Never masses are1 embeds the same obstruction in Fin4. The example
already has UE and only shows why equality in (10) cannot be included.

Neither branch supplies debt descent. A Never-active observer need not use
Never with positive probability. At a terminal strict collision, changing
the pivot's final hazard can alter the used final-date offers while earlier
used offers remain fixed, breaking observer indifferences. No global
component comparison, observer repair, UE class or Fin4 closure is claimed.

The narrow overlap search found special last-sure-date obstructions in
`CODEX_NEGATIVE_CERTIFICATE__ASYMMETRIC_STATIONARY_SEAM_CLOSURE.md` and finite
exact-Nash incompleteness in `CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`.
Those concern particular tables and full Nash profiles; they do not give
the raw margin capacity (3) or the approximate-observer estimate (2).
The [fixed-pivot control](CODEX_COLLAPSED_CONSUMER__FIXED_PIVOT_FULL_LAW_TRAP.md)
excludes pure uniformly strict observers at an actual global minimum.
It does not cover this finite mixed-support branch or augmented limits.

Inspected semantic declarations were
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`
(`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`),
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`), and
`quittingTerminalSemanticPair_rootThenContinuation`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`).
No Lean command ran. The margin formula and quantitative inequality extend
to any number of players at least three, with all but one exact observers;
two observers are needed for their proper-opponent and common-final-date
arguments. The five-candidate computation bound above is specific to Fin4.
The finite-calendar theorem instead applies to any finite number of players
at least two and requires only the one player's exactness and gap (10).
