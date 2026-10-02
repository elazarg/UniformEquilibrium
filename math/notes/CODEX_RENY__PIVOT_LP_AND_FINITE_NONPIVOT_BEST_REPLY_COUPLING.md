# Optimal pivot repair coupled to exact finite nonpivot replies

Author: CODEX_RENY.

Ordinary mathematics, not independently reviewed or newly checked in Lean.
The closed LP boundary does admit coherent finite-menu payoffs and a
Kakutani fixed-point construction. On the canonical cyclic table, however,
there is a literal coupled fixed point of full value 3/16 at EVERY
deadline. Its pivot is a GLOBAL unrestricted repair minimizer and all
three nonpivots simultaneously maximize their finite-menu payoffs.
Thus arbitrary coupled-fixed-point selection is not a vanishing-value
producer. Minimum-value selection over the entire coupled fixed-point
set remains open; no claim excludes that stronger selection.

A concrete change DOES succeed on this same fixture: add the small
planned-Never bonus specified in Section 7 to one nonpivot's response
objective, and minimize the ORIGINAL repair value over the resulting
coupled fixed points. Its values tend to zero. The required compatibility
is proved by a global arbitrary-pivot certificate, not inferred from
auxiliary-game Nash. This is a selector test on an already solved table,
not an arbitrary-table theorem or new equilibrium class.

## 1. Actual data and the precise coupling rule

There are four players with independent stopping laws on ℕ∪{Never}.
The first nonempty simultaneous quitting coalition S pays r(S); all
Never pays zero. Rewards are bounded in absolute value by M, and the
own-singleton vector is (1,0,0,0). All terminal caps below include every
complete behavioral replacement, equivalently every pure finite time
and Never and their mixtures.

Fix N≥1 and F_N={0,…,N−1,Never}. The three nonpivots choose laws
p_j∈Δ(F_N), j=1,2,3. The pivot's closed mass domain K_N consists of

    m=(x_0,…,x_(N−1),λ,ν,α),
    x_t,λ,ν≥0,    Σ_t x_t+λ+ν=1,    0≤α≤λ.               (1)

For λ>0 and α>0 this implements the pivot head x, Never mass ν, and
late geometric finite component

    μ₀(N+k)=α(1−α/λ)^k,    k≥0.                          (2)

For λ=0 the head and Never law is already literal. At α=0<λ, (1)
need not describe an attained behavioral repair. It is the closed
finite LP domain, not a fictitious stopping law with positive finite
mass and no finite atoms.

For fixed nonpivot p define Q_t as the pivot's pure payoff at t<N,
W₀ as its Never payoff, D=∏_j p_j(Never), and

    B₀=max({Q_t:t<N}∪{W₀,W₀+D}),
    U₀(m,p)=Σ_t x_t Q_t+λ(W₀+D)+νW₀.                     (3)

For j≠0, let a_j=r_j({0}), b_j=r_j({0,j}), and
d_j=∏_(k∉{0,j})p_k(Never). Let A_j be its unconditional reward
contribution from opponent absorption before N while j Continues.
Let π_j,t be its pure payoff for t<N. Both are computed by finite
conditioning using the provisional actual pivot law

    μ₀^prov=Σ_(t<N)x_tδ_t+λδ_N+νδ_Never.

Define

    W_j=A_j+d_j a_jλ,
    C_j=A_j+d_j b_jα,
    U_j(m,p)=Σ_(t<N)p_j(t)π_j,t+p_j(Never)W_j.             (4)

The exact closed repair objective is

    L(m,p)=max(0, B₀−U₀,
                  π_j,t−U_j, W_j−U_j, C_j−U_j : j≠0,t<N).
                                                                    (5)

Its minimum over m equals the infimum of FULL exploitability over all
actual pivot laws with the three nonpivots fixed. Formula (5), including
its possibly nonattained α=0 face, is the previously proved geometric
compression/repair LP, not a new adapter assumed as a hypothesis.

The coupling rule is to choose a fixed point satisfying BOTH:

    m∈argmin_(m'∈K_N) L(m',p);
    p_j maximizes U_j(m,q_j,p_(-j)) over q_j∈Δ(F_N), j≠0. (6)

The pivot optimizes the full maximum debt, not its own expected payoff.
The other players maximize their own finite-menu expected payoffs,
not the global debt objective. This asymmetry is part of the rule.
No pivot-logit restriction or equilibrium-response chronology is used.

## 2. Nonattainment does not destroy the common finite-menu game

Every prescribed payoff U_i and EVERY nonpivot pure payoff at an action
of F_N is independent of α. More generally these payoffs are unchanged
under any change to the pivot's post-N finite-time distribution preserving
its total mass λ and Never mass ν.

To see this, fix all nonpivot stopping times, including the deviator's
chosen time in F_N. If any is finite, their first finite time is before
N; the pivot head determines every earlier/tied event and only total
mass λ+ν is relevant afterward. If all are Never, a finite pivot tail
pays r({0}) and Never pays zero, so only λ and ν matter. This is an
outcome-by-outcome argument before taking any expectations. It applies
to every q_j in the finite simplex, not just the currently prescribed
law p_j.

Consequently (4) is an actual common-payoff system even at α=0<λ:
it is realized for these tests by μ₀^prov. This does NOT say the
provisional law has the relaxed LP's full cap. If a relaxed optimizer
has α=0<λ, replace α by a positive number tending to zero in (2).
Every nonpivot finite-menu comparison and every prescribed U_i stays
EXACTLY unchanged, while full exploitability is at most L(m,p)+Mα.
Thus every fixed point can be realized arbitrarily closely in full
objective, retaining exact nonpivot best replies on the OLD menu F_N.
Those replies need not remain optimal after their menus are enlarged.

For existence, K_N and the three finite probability simplexes form a
fixed compact convex domain. The function L is jointly continuous and
convex in m: it is a finite maximum of affine functions of m, with
coefficients continuous in p. Its minimizer correspondence is nonempty,
compact, convex-valued, and upper hemicontinuous. Each nonpivot payoff
is jointly continuous and affine in its own law, giving the same
properties for its best-response correspondence. Their product therefore
has a fixed point by finite-dimensional Kakutani. A continuous
single-valued choice of LP optimizers is neither needed nor asserted.
This is an existence statement, not a global computation algorithm.

## 3. Canonical cyclic table and literal positive fixed points

Define the full reward table by

    r₀(S)=1 if 0∈S, and 2 otherwise.

For j=1,2,3, use predecessor and successor cyclically among these three.
Let r_j(S)=0 if j∈S; otherwise let it equal −1 when 0∈S, and
2·1_(pred(j)∈S)−1_(succ(j)∈S) when 0∉S. All Never pays zero.
This specifies all fifteen rows and has M=2. It is the canonical
VANISH table, already known to have an exact infinite cyclic Nash
profile and successful finite approximate laws.

For ANY N≥1 put T=N−1. Let each nonpivot use

    p_j=(1/2)δ_T+(1/2)δ_Never,    j=1,2,3,                 (7)

and let the pivot use the ACTUAL finite law

    μ₀=(5/24)δ_T+(3/4)δ_N+(1/24)δ_Never.                  (8)

In LP coordinates this has x_T=5/24, λ=α=3/4, ν=1/24,
and all other head masses zero. There is no nonattainment issue in
this example. Direct calculation gives

    U=(27/16,0,0,0),
    B=(15/8,3/16,3/16,3/16),
    B−U=(3/16,3/16,3/16,3/16).                            (9)

Every nonpivot pure time in F_N has payoff zero, including Never.
Hence all three laws in (7) are simultaneous exact best replies against
the SAME pivot (8). Their omitted date N instead has payoff 3/16.
Thus their positive FULL debts have not been concealed by a finite
response comparison. The next section proves the required global
pivot optimality against (7), including arbitrary early and infinite
late pivot laws.

## 4. Global pivot repair certificate, including early mass

Hold (7) fixed and consider ANY actual pivot stopping law. Aggregate it
into masses

    y=Pr(T₀<T),       x=Pr(T₀=T),
    λ=Pr(T<T₀<Never), ν=Pr(T₀=Never),
    y+x+λ+ν=1.

For N=1, y=0 automatically. The pivot's payoff is one if it stops at
or before T. Its full cap is 2−1/8=15/8, attained at any finite time
strictly after T. Therefore its debt is

    d₀=1/8+(3/4)(x+y)−λ/8.                               (10)

For a nonpivot j, when it Continues and neither pivot nor j has stopped
before the other nonpivots' date T, the expected reward from those two
independent half-quitting opponents is 2·(1/2)−1/2=1/2.
In particular there is NO extra collision term in this expectation.
Its contribution through T is consequently

    A=1/2−(3/2)(x+y).                                     (11)

Its own prescribed half-mass at T gives payoff −y from the pivot's
earlier stops, and its Never half-mass gives A−λ/4. Thus

    U_j=A/2−y/2−λ/8.

Its exact full cap is max(0,A). Quit0 gives zero. Every finite reply
at or before T has nonpositive payoff. If λ>0, the first positive
pivot atom after T exists by well-ordering; replying at that atom
gives A, since joining the pivot pays zero. Later replies can only
replace some zero outcomes by the negative pivot-alone reward. If
λ=0, a reply at T+1 already gives A. Never gives A−λ/4.
These cases include every finite time and Never, hence every complete
behavioral mixture. It follows that

    d_j=max(0,A)−A/2+y/2+λ/8.                             (12)

Combining (10)–(12) gives the exact identity

    d₀+d_j=3/8+y/2+max(0,−A) ≥ 3/8,     j=1,2,3.         (13)

Therefore every unrestricted pivot law has full exploitability at least
3/16. At (8), A=3/16 and λ/4=3/16, so the nonpivot Never value
is zero and every debt is exactly 3/16. The global optimum is attained
there. By equality of the closed LP value and the unrestricted repair
infimum, (8) also minimizes the complete LP; this is not only optimality
over pivot laws using three selected dates.

Independent exact-rational coalition enumeration verified (9) and every
finite-menu/non-menu pure cap at N=1 and N=4. A separate comparison
with positive mass strictly before T verified (13). These are checks
of the direct proof, not a numerical grid or a substitute for the
arbitrary-law certificate.

## 5. Exact eliminated rule and remaining selection problem

For every deadline, the coupled correspondence (6) has a fixed point of
value 3/16. Consequently the rule “choose an arbitrary fixed point of
(6), then enlarge the deadline and repeat” has no vanishing-full-value
guarantee. These bad points are not failures to solve the inner LP,
incompatible auxiliary payoffs, or sequentially selected individual
best replies: all conditions hold simultaneously at one literal source.

The result does NOT show that every fixed point is bad. In particular,
minimizing L over the ENTIRE fixed-point set at each N is a stronger
rule not settled by (13). It would require changing the three laws
(7); (13) only solves the pivot optimization with those laws fixed.
The already known low-regret cyclic laws are approximate nonpivot
responses, not automatically members of (6).

The prior
[CODEX_FRECHET_CYCLE__PIVOT_LP_CANONICAL_JOINT_CALENDAR_TRAP.md](CODEX_FRECHET_CYCLE__PIVOT_LP_CANONICAL_JOINT_CALENDAR_TRAP.md)
already proves global one-coordinate traps and legal alternating
optimal-pivot/full-response cycles on a DIFFERENT canonical H table.
Thus optimal pivot repair was not previously untested. The distinct
quantifiers here are simultaneous finite-menu optimality for all three
nonpivots, global inner optimality, and a persistent literal fixed point
at EVERY deadline of the proposed compact coupled game.

## 6. Source correspondence and nonclaims

The reviewed geometric-compression packet supplies the exact objective
(5), the α-boundary approximation, and the small-value consumer. A
narrow current-source inspection additionally read
`PivotRepairFiniteLP.lean`, `PivotRepairFiniteLPBoundary.lean`,
`PivotRepairSmallValueSource.lean`, and `PivotRepairFiniteMenuConsumer.lean`
under `UniformEquilibrium/Quitting/Terminal/`. Their displayed affine
payoff definitions and `prescribedPayoff_withFirstAtom` match the
payoff-coherence observation here. The current files were inspected,
not built or assigned a new formalization seal by this note.

In particular `HasQuittingSmallPivotRepairValue` asks for small objective
from three actual finite nonpivot laws, not merely existence of (6).
The new fixed-point construction does not fill that source hypothesis.
No pivot repair consumer, finite approximation theorem, or equilibrium
existence theorem is reproved or inferred from the bad branch.

The concrete comparison in the next section adds a small planned-Never
bonus in the OUTER nonpivot response game. Its compatibility with GLOBAL
optimal pivot repair is proved separately; it is not inferred from an
auxiliary profile's own pivot best response.

## 7. A single outer Never bonus gives a good coupled branch

This section uses HILBERT's concrete bonus rule, communicated from his
independent finite auxiliary-game selector test, and proves the additional
optimal-pivot compatibility needed by (6). Fix K≥1, set N=3K, and put

    a=2^(−K),       D=a³=8^(−K),       b=a²=4^(−K).

Change ONLY player 2's outer optimization objective to

    U₂(m,p)+b·p₂(Never).                                  (14)

Players 1 and 3 still maximize original U_j. The pivot still minimizes
the ORIGINAL full repair objective L, with no bonus in its rewards or
constraints. The bonus is attached to the player's planned Never action
in this finite auxiliary game; it is not a terminal reward modification,
public randomization, or detection of an unobserved deviation.
The same compact convex correspondence argument gives fixed points.

Among ALL fixed points of this modified correspondence choose a
minimizer of ORIGINAL L. The set is nonempty compact by the closed-graph
property proved above, so this is well-defined as an existence selector.
I claim every such minimizer has value at most D.

### 7.1 An actual simultaneous outer best-response source

Take pivot Never and the literal finite laws

    p_j(3k+j−1)=2^(−k−1),    0≤k<K,
    p_j(Never)=a,           j=1,2,3.                       (15)

No source profile is an input of the selector; (15) is an explicit
table-derived witness used to prove the selected value bound.
The probability of no active quit strictly before date t is 2^(−t)
for 0≤t≤N, because the calendar has one successive active owner per
date, with conditional hazard 1/2. The joint Never mass is D.

For completeness, the original pure payoffs against (15) with pivot
Never are, for 0≤k<K,

    f₁(3k)=f₁(3k+1)=0,       f₁(3k+2)=−(1/2)4^(−k);
    f₂(3k)=1−4^(−k),         f₂(3k+1)=f₂(3k+2)=1;
    f₃(3k)=f₃(3k+2)=0,       f₃(3k+1)=−(1/2)4^(−k).

Their Never payoffs are (0,1−a²,0). These formulas follow by
conditioning on the first of the two undeleted clocks in each cycle:
deleted-clock survival per cycle is 1/4, and the positive and negative
increments are exactly the indicated reward times that survival.
Later finite actions have the same value as Never because the player's
own singleton is zero.

All actions used by players 1 and 3 are therefore exact menu best
replies of value zero. Player 2's supported finite dates give one,
and its Never value becomes 1−a²+b=1 after (14). Thus all three
laws are simultaneous exact OUTER best replies. The original payoffs,
caps, and debts at pivot Never are

    U=(2−2D,0,1−D,0),
    B=(2−D,0,1,0),
    B−U=(D,0,D,0).                                       (16)

This alone would not prove that pivot Never is an optimizer of L.

### 7.2 The unrestricted optimal-pivot certificate

Fix the three laws (15). For ANY pivot law μ₀ let d₀ be its original
full pivot debt, and let

    g₂,1=V₂(1;μ₀,p₁,p₃)−U₂(μ₀,p₁,p₂,p₃).

The claim is

    d₀+g₂,1≥2D.                                          (17)

The pivot cap is the fixed value 2−D. Both terms on the left of (17)
are affine in its complete law μ₀, so it suffices to check every pure
finite pivot time and Never. No cap attainment by player 2 is assumed:
time 1 is one fixed actual full-deviation test throughout.

- At pivot time 0, player 2 never quits at date 0 under (15), nor does
  its pure time-1 deviation. Both its prescribed and tested payoff are
  −1, so g₂,1=0. The pivot debt is 1−D, which is at least 2D because
  D≤1/8.
- For 1≤t<N, the pivot's pure payoff is 2−2^(−t), so
  d₀=2^(−t)−D≥D. The time-1 reply of player 2 has value one:
  the pivot cannot precede it, and joining it at time 1 still pays
  player 2 zero, just as its ordinary own Quit does.
  Adding a finite pivot to any fixed realization of the three clocks
  cannot increase player 2's prescribed payoff. If it also quits at
  the pivot time its payoff is zero before and after; otherwise the
  new pivot absorption pays −1, the minimum possible original reward
  on that realization, including the all-Never payoff zero. Earlier
  absorption is unchanged. Hence U₂≤1−D and g₂,1≥D.
- For finite t≥N the pivot acts after all possible finite nonpivot
  stops. Its debt is zero. The only changed prescribed outcome for
  player 2 is the event that ALL three nonpivots chose Never, of
  probability D; its payoff changes from zero to −1. Thus
  U₂=1−2D, while its time-1 test still gives one, so g₂,1=2D.
- At pivot Never both terms equal D by (16).

These cases prove (17), and integration gives it for arbitrary
unbounded or mixed finite/Never pivot laws. Since full exploitability
is at least each of d₀ and g₂,1, it is at least D. Equality is attained
by pivot Never in (16). Therefore the exact unrestricted pivot-repair
infimum and the closed LP optimum are both D, and pivot Never is an
ACTUAL minimizer. No α=0<λ boundary is used for this good branch.

### 7.3 What the modified selector produces

Equations (14)–(17) exhibit a fixed point of the bonus-coupled
correspondence with original value D. Thus every minimum-original-L
selection over that whole fixed-point set satisfies L≤D→0.
For every requested ε>0, choose K with D<ε. This produces three
actual finite nonpivot laws and a feasible optimal inner point of
original value below ε. It is exactly a small-repair-value source on
this particular table, not merely a verifier of outer best replies.

If a selected optimal point is nonliteral, Section 2 actualizes it with
arbitrarily small extra full error. The existing finite-censor consumer
then gives every requested error, final window, reach bound, and lower
deadline. Those consumers are not new here. Nor is equilibrium existence
for the cyclic table new: the contribution of Section 7 is the exact
compatibility of a simple OUTER bonus with GLOBAL ORIGINAL pivot repair.

This positive selector is different from selecting an arbitrary fixed
point in Section 5: both the bonus and minimum-value selection are
explicit parts of its rule. No conclusion about arbitrary canonical
tables, other bonuses, or all bonus-coupled fixed points follows.
