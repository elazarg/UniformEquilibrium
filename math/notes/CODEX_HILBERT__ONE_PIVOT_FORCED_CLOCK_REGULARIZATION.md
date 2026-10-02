# One-pivot clock regularization: daily-floor failure and a surviving envelope

Identity: CODEX_HILBERT. Status: ordinary-mathematics proof draft, not
independently reviewed or Lean-checked. No export is proposed. The exact
daily-floor regularization fails on the canonical cyclic table for EVERY
equilibrium selector. A different global survival-envelope restriction
admits good selectors on both tested tables and is not ruled out.
Sections11–13 now test an actual minimum-mean selection on the cyclic table.
It yields exact terminal Nash subsequential limits there. This is a solved-
fixture method check, not a new arbitrary-table or hard-residual producer.

## 1. Two genuinely different strategy restrictions

Fix a finite quitting table with bounded rewards |rᵢ(S)|≤M and Never zero.
Only the pivot0 is restricted. All other players retain every complete
behavioral strategy, equivalently every independent stopping law on
X=ℕ∪{Never}. Fix 0<δ<1 and a=1−δ. For a pivot law μ put
Sμ(t)=Pr(T₀≥t), including Never. Distinguish:

    A_δ: Sμ(t+1)≤a Sμ(t) for every t≥0;
    B_δ: Sμ(t)≤a^t for every t≥0.

A_δ is the DAILY hazard floor: the conditional pivot Quit probability is
at least δ at every reached date. It is the law of min(T,G), where T is
an arbitrary voluntary clock and G is an INDEPENDENT geometric clock of
hazard δ. Every reached conditional suffix stays in A_δ.

B_δ is only a GLOBAL envelope measured from the initial date. It permits
zero hazards at later dates if earlier stopping prepaid enough survival
reduction. Conditioning need NOT keep a suffix in B_δ. The two domains
must not be identified. Both are convex compact sets of proper laws and
A_δ⊆B_δ, generally strictly.

For either restriction, an equilibrium below means an exact Nash profile
in that restricted game, not an unrestricted Nash profile. In particular
all nonpivot FULL debts are zero; only the pivot can have unrestricted loss.

## 2. Exact compact-game existence for either domain

Put the weak topology on probability laws over the one-point compact space
X. Finite atoms and finite-head survival complements are continuous, so
the displayed constraints are closed affine inequalities. Each domain is
nonempty (it contains Geomδ), compact, and convex. Its uniform tail bound
Sμ(T)≤a^T also makes its weak and total-variation topologies agree.

Use the product of the pivot domain and three unrestricted weak law spaces.
The terminal payoff truncated to absorptions before T depends continuously
on finitely many atom masses. Its error against the actual payoff is at
most M a^T, UNIFORMLY over all profiles, because the pivot alone screens
the survival event. Thus every prescribed payoff is jointly continuous
on this compact product and affine in each player's marginal law.

The usual compact-convex-game existence argument therefore gives an exact
restricted Nash law. One can avoid any additional fixed-point citation:
uniform continuity supplies finite strategy nets controlling every payoff
against every opponent tuple; finite mixed Nash on those nets gives
restricted approximate equilibria. Each player's private mixture over laws
collapses to its barycenter, which remains in its convex domain. A compact
subsequence and payoff continuity then give exact restricted Nash. The
result is a product of independent laws, not a public lottery over profiles.

For a follower, its full cap is a maximum over its unrestricted compact
law domain and is continuous in the restricted opponent tuple. This does
NOT assert continuity of the pivot's UNRESTRICTED cap when its own domain
is enlarged and the other clocks may escape to Never.

## 3. Exact restricted pivot response formulas

Fix arbitrary opponents and let F(t) be the pivot's original payoff from
the finite pure date t. Let W be its Never payoff. In the canonical class,
its own singleton is1, so sup_t F(t)≥W and the full cap is sup_t F(t).

For A_δ the exact restricted cap is max over t∈ℕ∪{Never} of

    H_A(t)=δΣ[k<t]a^k F(k)+a^t F(t),          t finite;
    H_A(Never)=δΣ[k≥0]a^k F(k).

Indeed every law in A_δ is min(T,G) for an independent T and G: its
voluntary survival is Sμ(t)/a^t, a decreasing sequence defining a complete
law. Maximizing over the voluntary law reduces to its pure dates and Never.
The displayed finite values converge to H_A(Never), so the maximum exists.

For B_δ there is a DIFFERENT formula. Let

    J(g)=max[0≤t≤g]F(t).

Then its restricted cap is

    H_B=δΣ[g≥0]a^g J(g).                              (B)

Every μ∈B_δ is stochastically dominated by G. Couple its T with G so T≤G
by their common quantile representation; then F(T)≤J(G), proving the upper
bound. Conversely, privately sample G and choose the earliest maximizing
t≤G. This actual clock lies in B_δ and attains (B). This is not the
independent censor formula: it allows a privately pre-sampled deadline to
inform the planned clock. The resulting law is still an ordinary private
behavioral strategy in the original quitting game.

For any fixed opponent tuple, H_B tends to the unrestricted cap as δ↓0,
since J(g) increases to sup_t F(t). This pointwise assertion is NOT uniform
over equilibrium opponents varying with δ.

## 4. The canonical cyclic table

Use active players0,1,2, predecessor i−1 modulo three, and dummy3. For
every nonempty S, define

    r₀(S)=1+1_{2∈S} if0∈S; 3·1_{2∈S} otherwise;
    rᵢ(S)=1_{i−1∈S} ifi∈S; 3·1_{i−1∈S}−1 otherwise, i=1,2;
    r₃(S)=0 if3∈S; 1 otherwise.

The own singletons are e₀. The companion
`CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md` gives its exact
period-three terminal Nash profile, so this is a solved game, not a
putative positive-gap counterexample.

THEOREM. For every 0<δ<1/2 the A_δ-restricted game has exactly one
equilibrium product stopping law. It is stationary, with hazards

    q₀=δ,
    q₁=b=δ/[1+√(1−δ+δ²)],
    q₂=c=δ(2−δ)/(1−δ²),
    q₃=0.                                               (C)

The uniqueness concerns complete stopping laws; irrelevant actions after
absorption are not being identified literally. All three nonpivot full
debts vanish. The pivot's full debt tends to2/5 as δ↓0. Thus choosing
δ and an equilibrium together does not repair THIS daily-floor mechanism.

## 5. Every reached suffix of an A_δ equilibrium is Nash

Let qᵢ(t) be its current hazards and Vᵢ(t) its actual suffix payoffs.
Dummy Quit pays0, while Continue has payoff at least q₀(t)≥δ: pivot
absorption at this date pays the absent dummy1, and every dummy payoff is
nonnegative. Thus q₃=0 at every reached date.

No active player quits surely. If q₀=1, player1 strictly Continues, which
forces player2 to Quit surely, after which the pivot prefers lowering its
hazard to δ (Continue pays3, Quit pays2). If q₁=1, player2 Continues and
the pivot strictly chooses Quit surely, contradicting the previous case.
If q₂=1, the pivot chooses exactly δ (again Continue3 versus Quit2);
then player1's Quit-minus-Continue difference is1−2δ>0, forcing q₁=1,
another contradiction. These comparisons are independent of off-path tails.

Hence joint Continue probability is strictly positive at every reached
date, and inductively every finite date is reached. Conditional tails stay
in the SAME feasible domain A_δ. A profitable conditional suffix deviation
could be spliced behind the original prefix, with gain multiplied by its
positive joint reach. Each suffix is therefore restricted Nash. The same
argument legitimizes changing only a current hazard and retaining its own
conditional future law. No subgame-perfect refinement was assumed.

At each date, Quit now is feasible for every player, giving the lower bounds

    V₀≥1+q₂,         V₁≥q₀≥δ,         V₂≥q₁≥0.       (D)

Write aᵢ=1−qᵢ at the current date. Literal Continue endpoints are

    C₀=3q₂+a₁a₂V₀(next),
    C₁=2q₀−a₀q₂+a₀a₂V₁(next),
    C₂=2q₁−a₁q₀+a₀a₁V₂(next).                      (E)

For followers with positive Quit hazard, their hazard is below one, so
their value equals both endpoints: V₁=q₀ ifq₁>0, V₂=q₁ ifq₂>0.
If q₀>δ, the pivot hazard is strictly between its two permitted extremes
δ and1, so V₀=1+q₂=C₀ as well.

## 6. No voluntary pivot quitting is possible

If q₁>0, its equality in (E) gives

    a₀q₂=q₀+a₀a₂V₁(next),

hence q₂≥q₀/a₀>q₀>0. If q₂>0, its equality gives

    a₁q₀=q₁+a₀a₁V₂(next)≥q₁;

in particular q₀>q₁ whenever q₁>0.

Suppose q₀>δ at some date. Its equality and V₀(next)≥1 give

    1−2q₂=a₁a₂V₀(next)≥a₁a₂,
    q₁≥q₂/(1−q₂).

If q₂>0 this says q₁>q₂, whereas the preceding follower inequalities
give q₂>q₀>q₁, a contradiction. Thus q₂=0; also q₁=0, since q₁>0
would force q₂>0. The pivot equality now gives V₀(next)=1.

At any future date with V₀=1, (D) forces q₂=0 and consequently q₁=0.
Bellman and q₀<1 then force V₀(next)=1. Induction leaves both followers
at Never forever. The pivot's daily floor nevertheless makes it stop almost
surely, so player2's actual suffix payoff is−1. This contradicts (D).
Therefore q₀(t)=δ at EVERY date, not merely along one stationary branch.

## 7. The two followers must be stationary as well

Put a=1−δ and h=δ/(1+δ). Whenever q₂>0, V₂=q₁ and (E) imply
q₁≤h. If q₂=0, then q₁=0 and

    V₂=−δ+aV₂(next).

Nonnegativity forces V₂(next)≥δ/a>h. At that next date q₂ therefore
cannot be positive. Repeating the same recurrence would make the bounded
values V₂ grow without bound. Thus q₂>0 at every date, and V₂=q₁≤h.
If q₁ were zero at any date, (E) would give V₂(next)=δ/a>h, impossible.
Hence q₁>0 everywhere too, and V₁=δ everywhere.

Substitution in (E) gives

    q₂(t)=δ(2−δ)/(1−δ²)=c,
    q₁(t)=f(q₁(t+1)),
    f(x)=[δ−a x]/[1+δ−a x].                         (F)

On [0,h], its denominators exceed one, and

    |f(x)−f(y)|≤a|x−y|.

The unique fixed point in this interval is b from (C), solving
(1−δ)b²−2b+δ=0. Iterating the BACKWARD relation (F) for any number m
gives |q₁(t)−b|≤a^m h, hence q₁(t)=b. This proves complete-law
uniqueness. For δ<1/2 the displayed c lies strictly below1, so the
reconstruction is within the claimed domain.

## 8. Exact pivot loss and its nonvanishing limit

At (C), let D=(1−b)(1−c). Pivot Quit-now value and Never value are

    Q=1+c,           W=3c/(1−D).

Since c>δ>b>0 and c<1,
3c−(1+c)(1−D)=c(2−c)−b(1−c²)>0, so W>Q.
Against these stationary opponents its finite pure-date payoff is

    F(t)=W+(Q−W)D^t.

It increases strictly to W. The latest feasible law in A_δ is Geomδ,
which is indeed optimal under the restriction. Its prescribed value is

    U₀=[δ+3c−2δc]/[1−(1−δ)(1−b)(1−c)]
       =W−δ(W−Q)/[1−(1−δ)D].

The full pivot cap is W, and therefore its debt is the positive final
fraction. As δ↓0,

    b/δ→1/2, c/δ→2, U₀→2, W→12/5, d₀→2/5.

These exact algebraic limits were also checked with symbolic arithmetic.
All other full debts are zero by restricted Nash with unrestricted follower
domains. Compact existence plus the uniqueness proof already ensures the
displayed profile is Nash; alternatively, both followers' pure-date payoffs
are constant at δ and b, respectively, verifying their full comparisons
directly. Dummy Never is optimal.

The failure term is an actual forced-preemption loss: the probability the
forced pivot clock beats all opponents stays bounded away from zero as
their own clocks slow with δ. A small daily hazard is not a small integrated
effect. Unlike the earlier all-player censor counterexamples, this proves
failure for EVERY selector with all three followers fully unrestricted and
all own singletons canonical and nonnegative.

## 9. Why this does NOT dispose of the global-envelope domain B_δ

The cyclic table's known exact terminal Nash has pivot hazard1/2 at dates
0,3,6,… and zero elsewhere. Its survival is2^(−ceil(t/3)). Consequently
it belongs to B_δ whenever δ≤1−2^(−1/3), while it never belongs to A_δ.
Since it is already FULL Nash, it is a zero-loss B_δ equilibrium for all
such δ. This is a concrete good selector, not just the absence of a no-go.

The bad stationary profile (C) is ALSO a B_δ equilibrium: its pivot
payoff F(t) is increasing, and Geomδ maximizes every increasing observable
over the stochastically dominated domain B_δ. The followers remain full
best responders. Thus B_δ has both good and bad selectors on the same
table. The every-selector assertion fails, but existence of a good selector
survives. The suffix invariance used in Sections5–7 is exactly the property
B_δ lacks, so that uniqueness proof cannot be imported into it.

On the table data of `gpt/EXACT_EXAMPLE.md`, there is an even simpler
zero-loss selector in BOTH domains. Let only the pivot quit with constant
hazardδ and every follower choose Never. The pivot payoff and full cap
are1. Player1 has Never payoff7 and Quit-now payoff8δ, player2 has Never
payoff7 and Quit-now payoff5δ, and dummy Never attains0. Stationary
pure-time comparison therefore proves exact terminal Nash for δ≤7/8.
This is a direct table calculation, not an additional review of that
submission's finite-menu uniqueness or noncommuting limits.

## 10. Bounded source check and next question

The compact-law route is the proper watchdog boundary in `docs/TOOLKIT.md`.
I inspected `IsProperQuittingBehaviorStrategy` and
`IsQuittingProperStrategicallyApproximable` in
`UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogProperBoundary.lean`.
Its comments explicitly separate proper approximation from the missing
compact-game semantic producer; it does not already assert this one-pivot
restricted equilibrium or a successful removal selector.

The complete stopping-law/pure-response semantics and finite mixed Nash
input are the same named declarations recorded in
`feedback/TRANSFORM__BY_CODEX_HILBERT.md`. The reached-suffix transport
is the elementary positive-reach splice underlying
`timingLawTail_isNash_of_isNash_of_positiveContinue` in
`Diagnostics/Quitting/FiniteDeadlineTimingRecursion.lean`; that declaration
is finite-menu-specific, while the uniform pivot tail makes the present
infinite-clock comparison exact directly. No declaration is attributed an
unwritten infinite-clock telescope.

Earlier owned proper/optional all-player censor notes were read as a
duplication guard. The daily-floor counterexample above is stronger in its
specific one-pivot/all-selector scope, not a generic impossibility result.
The surviving research question is selection in B_δ, whose payoff problem
is compact and whose exact pivot operator is (B). Both tested tables admit
full-safe B_δ selectors. No universal control of its equilibrium pivot loss
has been proved.

## 11. An actual B-equilibrium selector: minimum pivot mean

For fixed δ, select an equilibrium of the B_δ game minimizing E[T₀].
This is not minimization of the missing regret itself. The equilibrium set
is nonempty and compact by Section2. The mean is continuous on B_δ:
its tail-sum formula has uniformly summable remainder bounded by
Σ[t≥K]a^t. Thus the displayed minimum is attained.

On the cyclic table, for every sufficiently small δ its value is at most3.
Indeed the exact period-three equilibrium in Section9 is feasible and its
pivot clock has mean3. Consequently the minimum-mean rule excludes the
stationary bad equilibrium of Section8 once (1−δ)/δ>3. Exclusion of that
one branch alone would NOT prove that the selected equilibrium is good.

Here is the stronger exact consequence. For every sequence δₙ↓0 and every
choice of minimum-mean B_δₙ equilibria, each subsequence has a further
subsequence converging to an ACTUAL full terminal Nash profile, with a
proper pivot. This already gives a terminal-Nash/UE consumer for the
tested table; continuity of the sampled profiles' unrestricted debts is
not needed for that conclusion.

The compact-limit argument is as follows. Bounded pivot mean makes its laws
uniformly tight on ℕ: Pr(T₀≥K)≤3/K. Pass to a weakly convergent subsequence
of all four stopping laws on ℕ∪{Never}. The pivot limit is proper, and its
laws converge in total variation. Finite-head truncation with the uniform
pivot tail bound proves convergence of every prescribed payoff. The same
argument applies to every fixed nonpivot deviation, since that deviation
does not remove the proper pivot. All nonpivot full Nash inequalities pass
to the limit.

For the pivot, fix any finite date t. The clock min(t,Geomδₙ) belongs even
to A_δₙ, hence to B_δₙ. Against arbitrary moving opponents its payoff differs
from pure Quit t by at most2M[1−(1−δₙ)^t], which tends to zero. Restricted
Nash and continuity of each finite-date response payoff imply

    U₀(limit)≥F₀(limit,t) for EVERY finite t.

Because s₀=1 and Never is zero, the finite-date supremum includes or exceeds
the Never response value. Thus the pivot limit also satisfies every full
behavioral comparison. No interchange of a moving late maximizing date
with the limit was used. Independence is retained by taking the product of
the limiting marginal laws, not by retaining an empirical correlated law.

This argument has an IMPORTANT strength limit: uniform tightness of a
selected pivot family produces an EXACT terminal Nash profile. The actual
canonical question only needs unrelated approximate profiles at successive
errors and does not demand any exact limiting equilibrium. Neither UE
existence nor the canonical normalization is asserted to imply a uniform
mean bound. On this fixture the bound3 came from an already known exact
equilibrium, so this is not a new proof of a previously unresolved class.

## 12. Cyclic-specific cap continuity, if one wants the selected profiles

There is an additional exact fact on this particular table: every full Nash
profile whose pivot is proper has all three active clocks proper. It implies
that the minimum-mean B equilibria themselves have full debt tending to
zero, not merely that their subsequential limits are full Nash. This is
optional for the consumer in Section11, not a new general hypothesis.

Proof of the additional fact. At any reached suffix the conditional pivot
law is proper. Dummy Never pays1, so dummy Quit is strictly suboptimal.
No active hazard is sure: q₀=1 forces q₁=0 and q₂=1, making pivot Continue
strictly better; q₁=1 forces q₂=0 and q₀=1; q₂=1 forces q₀=0 and q₁=1.
Thus every finite date has positive joint reach, and every suffix is full
Nash by literal positive-reach splicing.

Its values satisfy V₀≥1+q₂, V₁≥q₀, and V₂≥q₁, while its Continue endpoints
are (E). If q₀>0, it is interior, so its endpoint equality gives
q₁≥q₂/(1−q₂). Were q₂>0, then q₁>0; the two follower equalities give
q₂>q₀>q₁, a contradiction. Hence q₂=0, and the player1 equality rules out
q₁>0 as well. If q₀=0, the player2 equality forbids q₁,q₂ both positive.
At most ONE active player has positive hazard at each date. Thus no
simultaneous first-quit coalition occurs.

In every conditional suffix let pᵢ be the probability its first quitter is
player i. Proper pivot implies p₀+p₁+p₂=1. The exact singleton payoffs and
full Nash floors yield

    V₀=p₀+3p₂≥1,   V₁=2p₀−p₂≥0,   V₂=2p₁−p₀≥0;
    p₁≤2p₂,         p₂≤2p₀,         p₀≤2p₁.

In particular each pᵢ≥1/7. If any active clock had a positive Never atom,
its conditional probability of ever quitting after date t would tend to
zero as t→∞. Its probability of being the suffix's first quitter is no
larger, contradicting the uniform lower bound1/7. This proves properness.

Now take a subsequential limit from Section11. At least one opponent of
the pivot is proper (in fact both active opponents are). Its deleted joint
survival tends to zero. Finite-head approximation therefore controls the
pivot's entire full cap uniformly in a neighborhood of these limiting
opponents: for t≥K, the difference between F₀(t) and W₀ is at most
2M times deleted joint survival at K. Finite-head response values are
continuous, and W₀ has the same truncated-head continuity at this proper
opponent tuple. Hence the moving full pivot caps converge as well.
The limiting debt is zero. Applying this to every subsequence proves

    d₀(σ_δ)→0 as δ↓0 for EVERY minimum-mean B_δ selector

on the cyclic table. All nonpivot debts are identically zero already.
This successful selection test does not extend to arbitrary tables by
pointwise convergence of (B): the proper-opponent conclusion here used the
specific three cyclic singleton inequalities and single-owner structure.

## 13. A second exact B profile and the remaining research boundary

The global-envelope flexibility can also be checked without any selection
limit. On the cyclic table, use at date zero

    q₀=δ,  q₁=δ/(1+δ),  q₂=1/[2(1−δ)],  q₃=0,

and after joint Continue use the full period-three equilibrium starting at
its phase0. For 0<δ≤1−2^(−1/3), the pivot survival is S(1)=1−δ and
S(t)=(1−δ)2^(−ceil((t−1)/3)) for t≥1, so the entire law lies in B_δ.
The conditional periodic tail does not lie in A_δ.

Against the literal suffix values (1,1,0,1), both follower endpoints agree:
C₁=Q₁=δ and C₂=Q₂=δ/(1+δ). Their tail comparisons are full Nash, hence
their complete responses are safe. The pivot Quit-now value is
Q=(3−2δ)/[2(1−δ)], while its best Continue value is
C=(4+δ)/[2(1−δ²)]. Here C>Q. All future finite responses are at most C,
and the supplied periodic pivot tail attains C. Every B_δ law must put at
least δ at date zero, so the prescribed pivot mixture is exactly optimal.
Thus this is an exact B_δ equilibrium with

    U₀=(2−δ³)/(1−δ²),
    d₀=δ(1+2δ²)/[2(1−δ²)]→0.

Again this is a direct actual-law check on the solved cyclic fixture, not
a general producer from compactness. A root singleton matrix alone does
not specify the nonsingleton rewards needed for a new residual-table test.
RENY has been asked for his concrete paired-block completion before trying
this selection outside the solved fixture.

A bounded phrase search in the maintained toolkit and nearby notes found
no verified canonical counterexample to UNRESTRICTED exact terminal Nash
existence. It did find numerous no-stationary, no-finite-clock, and
no-solo-hazard results; none is substituted for the stronger nonexistence
claim. Regardless, uniform mean is not promoted as the universal goal:
its exact-limit conclusion is stronger than what the priority approximate-
selection question requires. Minimum-pivot-loss attainment and its separate
variational analysis are being investigated independently by FRECHET.

## 14. The paired-block matrix fixture: an honest but already solved test

RENY supplied the full table in
`CODEX_RENY__COLLISION_TWO_PHASE_INVERSE_DESIGN_TEST.md`, Section1.
I read its complete table and exact stationary response calculation. Its
canonical version subtracts (0,1,1,1) only on nonempty terminal coalitions.
Its singleton matrix is full standard Q, has a non-projective-Q opposite
principal, and excludes every balanced singleton word, but its collision
completion already has the full stationary Nash root

    q=(1,1/2,1/2,0),   U=(3/2,5/2,−1,−1/4).

The pivot is sure at date zero; its finite response sequence decreases from
3/2 to the Never value4/3 against the two independent stationary half-hazard
opponents. Player1 and player2 are indifferent at their prescribed hazards,
and player3's immediate joining payoff is below Never. Thus this exact
profile belongs to EVERY B_δ and has pivot mean zero.

For this completion the minimum-mean selector therefore has mean zero at
every δ, and EVERY such minimizer is full Nash. The last assertion uses a
simple exact B comparison, rather than knowledge of which minimizer was
chosen. Mean zero forces pivot Quit0 surely. If some finite response t had
F₀(t)>F₀(0), then for t≥1 the actual law

    (1−a^t) Quit0 + a^t Quit t

would be feasible in B_δ and strictly profitable. Thus all finite responses
are capped by F₀(0); canonical s₀=1 includes Never in their supremum. The
followers were unrestricted throughout. This proves full Nash for each
zero-mean minimizer without a limit or an escaping-cap assumption.

This is not new UE coverage. The supplied completion is already covered
by its stationary singleton-base source, as RENY explicitly records using
`QuittingInducedOwnerChamber` in `Diagnostics/Quitting/InducedOwnerChambers.lean`.
It illustrates why the hard singleton matrix does not by itself make a
chosen collision completion a hard reward table. No uniform mean bound or
other successful selection inequality has yet been derived for an arbitrary
canonical table satisfying the actual no-UE consequences.
