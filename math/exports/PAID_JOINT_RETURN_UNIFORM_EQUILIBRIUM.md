# A paid joint return through two opposite-sign pair traps

## 1. Exact statement

There are four players I={0,1,2,3}. At every live date each independently
chooses Continue or Quit; the first nonempty quitter set S absorbs at
r(S) in R^4. Live play and Never give zero. The reward table is finite.
All past actions are public and a deviator may replace its entire private
behavioral law. There is no public randomization device.

Write R* for the following complete table. Coalition strings denote sets.

| Coalition | Reward vector |
| --- | --- |
| 0 | (1,0,4,0) |
| 1 | (0,1,0,4) |
| 2 | (4,0,1,0) |
| 3 | (0,4,0,1) |
| 01 | (-1,1,5/2,3/2) |
| 02 | (5,2,2,2) |
| 03 | (2,3/2,3/2,-1) |
| 12 | (3/2,-3,1,9/2) |
| 13 | (2,5,2,2) |
| 23 | (9/2,3/2,-3,1) |
| 012 | (-1,-1,-1,10) |
| 013 | (-1,-1,10,-1) |
| 023 | (-1,10,-1,-1) |
| 123 | (10,-1,-1,-1) |
| 0123 | (9,9,9,9) |

Let R+ agree with R* except R+_3(23)=1001/1000.

**Theorem.** Each of the following original games has an exact terminal
Nash equilibrium against all complete unilateral behavioral replacements,
and one fixed uniform-equilibrium payoff delivered by that same profile:

1. The table R*. A repeating four-date schedule has supports 02,3,23,13.
2. Every real table r with max_(i,S nonempty)|r_i(S)-R+_i(S)|<=1/100000.
   A repeating four-date schedule has supports 02,23,23,13.

The profiles and targets are produced below from the raw table. Every
scheduled hazard is strictly between zero and one, every player-deleted
opponent family absorbs geometrically, and every suffix is exact terminal
Nash. The same profile supplies every positive finite-horizon accuracy.
The twenty irrelevant coordinates listed in Section 6 may instead be
arbitrary finite real numbers. The conclusion holds for each original
table; there is no reward transformation changing the Never payoff.

These are ordinary mathematical theorems with exact rational arithmetic
certificates. No new Lean result or arbitrary Fin4 solution is claimed.

## 2. Conjecture-facing change and strategic inputs

This is a producer for two simultaneous opposite-sign pair traps. For R*,
all fifteen nonempty marked sets fail the floor-restricted orientation and
passive conditions defined in Section 7. The complete stationary census
in Appendix A also excludes exact stationary equilibrium and its reward
closure. The construction therefore supplies an actual equilibrium where
those static entrances fail. Its additional stopping opportunities are a
singleton-3 phase and a cross-pair-23 phase; the latter also survives when
its owner-3 joining premium is positive.

Every strategic witness is an output: the hazards, four continuation value
rows, all root action comparisons, actual terminal payoffs, full response
caps, and opponent absorption rates. The two finite contraction arguments
produce their roots from explicit raw data; neither a selected equilibrium
nor a continuation annotation is a theorem input. The proof does not call
itself recursively. The remaining obligation is a producer for general
two-opposite-pair tables or arbitrary Fin4, which is not established here.

## 3. Definitions and the behavioral endpoint

For a product hazard row q, let P_q(S)=product_(i in S)q_i times
product_(i outside S)(1-q_i). For a recipient i define

    Q_i(q)=sum_(T subset I-i) P_(q_-i)(T) r_i(T+i),
    b_i(q)=sum_(empty!=T subset I-i) P_(q_-i)(T) r_i(T),
    alpha_i(q)=product_(j!=i)(1-q_j),
    C_i(q,U)=b_i(q)+alpha_i(q)U_i.

The action set has only Quit and Continue. At an active coordinate
0<q_i<1, both endpoints must equal the phase value; at q_i=0,
Continue must give that value and dominate Quit. These finite inequalities
become complete behavioral caps when the continuation values are the
actual periodic payoffs and each player-deleted opponent cycle contracts.
Section 5 proves that implication directly, including literal Never.

Before absorption the only public history is a string of all Continue.
Thus any behavioral law is a private stopping law on natural dates plus
Never. Independent randomization gives independent stopping clocks.
A unilateral replacement averages its deterministic stopping-date and
Never payoffs. Bounding those pure responses bounds every complete law;
no stationary or Markov restriction is imposed on the deviator.

## 4. Source correspondence and implementation boundary

The existing supplied-profile consumer
`isUniformEquilibriumPayoff_of_isQuittingBlockCertificate`
(`UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean`) accepts
periodic product hazards, bounded exact policy values, every action
comparison and absorption/admissibility data. This packet constructs all
those inputs from R* or the displayed raw reward neighborhood.

The supplied two-pair consumer `twoPair_exact_terminal_and_fixedProfile`
(`UniformEquilibrium/Quitting/Cycles/TwoPairExactCertificate.lean`) computes
active and post-phase values but still requires passive transport and
inactive Quit bounds. The symmetric two-pair candidate does not satisfy the
necessary inactive comparison exhibited in Section 7. Their four-phase
repair is new input to the existing periodic consumer, rather than a new
claim about the semantic compiler itself.

`QuittingTerminalExploitabilityWitness.exists_periodicCap_gain`
(`UniformEquilibrium/Quitting/Cycles/TerminalExploitabilityPeriodicProfile.lean`)
retains the unrestricted periodic response cap. The finite-horizon
statements `finiteAverage_delivery_le_of_opponentLiveCesaro_bound` and
`finiteAverage_deviation_gain_le_of_exact_terminalNash_and_opponentLiveCesaro_bound`
(`UniformEquilibrium/Quitting/Cycles/PeriodicFiniteHorizonRate.lean`)
match the direct geometric-tail estimates below. The present arithmetic
producer is ordinary mathematics, not a new checked declaration.

## 5. Proof for the exact table R*

### 5.1 Two scalar equations produce every hazard and value

Fix `g=17/50`. Choose a,b in the rational box

    |a-156714212/10^9| <= 1/10^7,
    |b-289202614/10^9| <= 1/10^7.                           (5.1)

Define the following rational functions:

    v=a+b-3ab,       f=v/(2+v),       d=f/(1+f),
    k=2fg+(1-f)(1-g)(1+a),
    e=(1-k)/(4-k),
    c=1-(1-3a)/[(1-a)(1-4e)],
    D0=2fg+(1-f)(1-g)(1+4b),
    C0=4d+(de)/2+(1-d)(1-e)D0,
    C1=4e-(5de)/2+(1-d)(1-e)(1+4g),
    B1=4c+(1-c)C1.

All displayed denominators are nonzero throughout (5.1). The two
equations still to be solved are

    F0=(1-c)C0-1/(1-b)=0,
    F1=2ab+(1-a)(1-b)B1-1/(1-g)=0.                         (5.2)

Section 5.2 proves there is a unique solution in the box. The prescribed
hazards and the proposed continuation values at its four phases are

| Phase | Hazards `(q0,q1,q2,q3)` | Value vector |
| --- | --- | --- |
| A | `(a,0,b,0)` | `(1+4b,1/(1-g),1+a,(1-3f)/(1-f))` |
| B | `(0,0,0,c)` | `(1/(1-b),B1,(1-3a)/(1-a),1)` |
| C | `(0,0,d,e)` | `(C0,C1,1-4e,1)` |
| D | `(0,f,0,g)` | `(D0,1+4g,k,1+f)` |

All seven scheduled hazards are strictly between zero and one. Their
approximate values, only for interpreting the exact construction, are

    a=.156714211860630, b=.289202613999057,
    c=.095740825952213, d=.118306143236089,
    e=.076287416688099, f=.134180523464583, g=.34.

The singleton phase B is essential to this mechanism. Owner 3 is
indifferent there because its value at the following pair-23 phase is
exactly its singleton reward one. The pair-23 phase then changes the
other players' continuation values before the pair-13 phase. The two
opposite pairs are therefore joined through an actual additional
stopping opportunity, rather than by alternating only their Nash roots.

### 5.2 Exact existence in the rational box

Clearing the denominators in (5.2) gives two bicubic polynomials:

    p0 = 6966a^3b^3-10107a^3b^2+3426a^3b-277a^3
         -9342a^2b^3+6351a^2b^2+4039a^2b-1464a^2
         +3906ab^3+983ab^2-4070ab-11a-522b^3-659b^2+781b,

    p1 = -141966a^3b^3+182259a^3b^2-37158a^3b-2607a^3
         +101574a^2b^3-141a^2b^2-168283a^2b+39522a^2
         -20394ab^3-3371ab^2+53252ab+17313a
         +770b^3-5611b^2-15159b.

More precisely,

    F0=p0/[4(a-1)(b-1)(3ab-a-b-1)(51ab-50a-17b-33)],
    F1=p1/[132(3ab-a-b-1)(51ab-50a-17b-33)].

Let x0 be the center of (5.1), r=`1/10^7`, and

    A = [-1000451318, -207610;
         -2071352271, -70083520] / 10^12.

The matrix A is invertible. Exact rational interval evaluation of each
polynomial derivative on the box gives

    sup_box ||I-A Dp||_infinity < 1/1000,
    ||A p(x0)||_infinity < 1/10^9,
    1/10^9+(1/1000)r < r.                                (5.3)

Here the matrix norm is the maximum absolute row sum. These inequalities
can be verified directly by expanding the displayed polynomials and
bounding each monomial on the rational box. The reproducible checker in
Appendix B uses outward exact rational intervals, with no floating-point
assumption. Its sharper derivative bound is less than `103/10^7`.

Thus `T(x)=x-Ap(x)` maps the closed box strictly into itself and is a
contraction. Banach's theorem gives a unique fixed point. Invertibility
of A makes it a zero of p, and the denominator formulas make it a
solution of (5.2). This proves existence from the fixed reward table;
an equilibrium, strategic root, or numerical optimizer is not an input.

### 5.3 All Bellman and action comparisons

For a phase t and owner i, let `Q_i(t)` be the expected reward if i
Quits immediately while its opponents use the phase's prescribed
hazards. Let `b_i(t)` be the passive reward contribution when at least
one opponent Quits, and let `alpha_i(t)` be the probability that every
opponent Continues. Define

    C_i(t)=b_i(t)+alpha_i(t) U_i(t+1).

Use the actual table in Section 1 in these finite product expectations.
Direct substitution gives `Q_i(t)=C_i(t)` at all seven active
phase/owner pairs, identically in a,b before imposing (5.2). The
prescribed transport

    q_i(t)Q_i(t)+(1-q_i(t))C_i(t)-U_i(t)

is identically zero except for `(t,i)=(A,1)` and `(B,0)`, where it is
respectively F1 and F0. Thus all sixteen Bellman equations hold at the
constructed zero.

For clarity, the reductions successively encode the active comparisons:
the value of owner 3 in C is one; its C comparison gives `d=f/(1+f)`;
its D comparison determines the A value `(1-3f)/(1-f)`; passive
transport through A gives `f=(a+b-3ab)/(2+a+b-3ab)`. Owner 2's C
comparison gives `e=(1-k)/(4-k)`, and its A comparison followed by B
transport gives the formula for c. The remaining active comparisons
fix the displayed owner-0 and owner-1 values. Only the two passive
transports (5.2) remain.

The nine inactive comparisons have strict slack. Exact interval
evaluation throughout the whole box (5.1), using the rational functions
of Section 5.1, gives

    Q_i(t)-C_i(t) < -3/1000

at every inactive phase/owner pair. These are all nine comparisons,
including owner 3 in phase A and owner 2 in the singleton phase B.
Consequently the comparisons remain true at the exact zero; no unused
response date or simultaneous joining action is omitted.

### 5.4 Actual full caps and one fixed uniform target

Repeat the four hazard rows on the literal natural-date calendar. Each
row uses independent private coins. The prescribed probability of
surviving a period is strictly below one, so bounded Bellman iteration
identifies the displayed U vectors with the actual terminal payoffs.

For every deviator i, deleting its own hazards still leaves an opponent
with hazard exceeding `3/20` in each period: use owner 0 for every
`i!=0`, and owner 2 for i=0. Hence its opponents' period survival is
at most `17/20`, independently of i's replacement behavior.

At every phase, both immediate actions are bounded by U. Iterate the
Continue inequality to any finite pure stopping deadline. The resulting
payoff is at most the initial U coordinate. For Never, the bounded
continuation remainder tends to zero with opponent survival, so the
Never payoff also obeys that bound. Every complete behavioral response
induces a private stopping law on the natural dates and Never; its
payoff averages those pure responses. Thus the full behavioral cap is
exactly the prescribed payoff at every phase.

The initial target is the single fixed vector

    u=(1+4b,50/33,1+a,(1-3f)/(1-f)),

where a,b denote the exact zero from Section 5.2. In particular it is
approximately `(2.156810456,1.515151515,1.156714212,.69004965)`.
It is chosen once and does not depend on the requested accuracy.

For a direct uniform bridge, every prescribed or deviating profile
absorbs by the first opponent exit. Its expected absorption date plus
one is at most `4/(1-17/20)=80/3`. The table's absolute rewards are at
most 10. Therefore terminal versus N-stage average payoffs differ by
at most `800/(3N)`, uniformly over all unilateral replacements. The
prescribed N-stage payoff approaches u with this bound, and every
deviation gain is at most `1600/(3N)`. Thus the same profile supplies
every positive uniform accuracy for sufficiently large N.


## 6. Proof for the nonflat paid return

Let R be exactly the table in Section 1 with just one change:

    R_3(23)=1001/1000.

For EVERY real reward table r satisfying

    max_(i,S nonempty) |r_i(S)-R_i(S)| <= 1/100000,          (6.1)

there is an exact proper periodic terminal equilibrium with supports

    02, 23, 23, 13.                                       (6.2)

It has independent private randomization and bounds every complete
unilateral behavioral replacement. Its actual initial payoff is one
fixed uniform-equilibrium target, with the same profile supplying every
accuracy. The live and Never payoffs remain zero. Condition (6.1) is
the entire raw input; H/J or a continuation root is not additionally
assumed. In particular the reward `r_3(23)` is uniformly strictly above
`r_3(3)` throughout this cube. The flat link from Section 5 is absent.

The relevant change is an extra, small positive owner-2 hazard in the
second phase. Owner 3 now receives a strictly positive joining premium
on 23, and the new owner-2 activity pays for the corresponding change
in its continuation comparison. This is an actual additional independent
Quit coin in the original game.

### 6.1 A uniform finite-dimensional root construction

Order the eight active coordinates as

    (A0,A2,B2,B3,C2,C3,D1,D3).

Let their rational center be

    x0=(1568411120007,2869644501486,1177298486,930080404969,
        1178614542459,769092048080,1337423880501,3431264118066)/10^13.

Use the closed sup-norm box `||x-x0||<=rho=1/10000`. Every active
coordinate is strictly between zero and one throughout this box;
in particular the small B2 coordinate has lower bound
`1177298486/10^13-1/10000>0`. Set all nonscheduled hazards to zero.

For a fixed table r, let `P_t(S)` be the phase-t product probability
of coalition S, let `c_t=P_t(empty)`, and define

    z_t=sum_(S nonempty) P_t(S) r(S),
    U_t=[z_t+c_t z_(t+1)+c_t c_(t+1) z_(t+2)
              +c_t c_(t+1)c_(t+2) z_(t+3)]
             /[1-product_t c_t].                         (6.3)

Phases are read modulo four. Formula (6.3) is the exact actual terminal
payoff of the repeating product profile, because the joint cycle
survival is uniformly below one on this box.

Compute Q, b and alpha from the literal reward table as in Section 5.3.
Let `G_r(x)` list `Q_i(t)-b_i(t)-alpha_i(t)U_i(t+1)` on the eight
ordered active coordinates. This is a rational function on the box.
Use the following fixed rational matrix, with every displayed entry
divided by `10^9`:

    A = [169080595,-258131102,10412137,474486148,-44759569,-28348111,2649595,-318962995;
         -174123720,346934192,-196347562,-1306934468,-176789427,80825488,600819556,900447546;
         -20006,43053,-29864,998859702,-29083,-921059857,92781,-720347;
         118917269,114956009,-242647534,333714208,-31480169,-19937711,1863505,-224332120;
         -20030753,43105863,-29900802,-23714037,-29118865,892751019,92896089,-721237511;
         108417482,104805981,54413405,304248949,-249235268,-18177313,1698967,-204524740;
         -25766638,55449396,-38463014,-30504645,-37457166,14785006,119497249,-270893121;
         653133623,-255507249,272695166,1828679930,249261628,-110553697,-1784774,-1200078293].

Exact rational Gaussian elimination shows A is invertible. Exact
interval evaluation of the value formula and its partial derivatives
gives, SIMULTANEOUSLY over every reward table (6.1) and every hazard
point in the stated box,

    ||I-A D G_r(x)||_infinity < 41/500,
    ||A G_r(x0)||_infinity < 183/2000000.                  (6.4)

The bounds are obtained by the product and quotient differentiation
rules applied to (6.3) and the finite endpoint expectations. The
certificate uses rational reward intervals for all sixty coordinates
at once; it does not test a finite sample of nearby games.

Since

    183/2000000+(41/500)(1/10000)=997/10000000<1/10000,

the map `x -> x-A G_r(x)` is a contraction from the hazard box strictly
into itself for each table r. It has a unique fixed point there, which
is a zero of `G_r` because A is invertible. Thus the active hazards
are produced from the raw table without an assumed equilibrium or
implicit-function nondegeneracy hypothesis.

### 6.2 All actions and the original behavioral semantics

The same exact interval evaluation gives, on the entire joint
reward/hazard box,

    Q_i(t)-b_i(t)-alpha_i(t)U_i(t+1)<-3/1000

at every one of the eight inactive phase/owner pairs. At the constructed
zero, every active owner is indifferent and every inactive owner
strictly prefers Continue. Formula (6.3) supplies the actual Bellman
values, so these comparisons concern actual continuation payoffs.

Deleting any one owner still leaves an opponent with a hazard exceeding
`3/20` during each period: owner 0 when the deviator is not 0, and
owner 2 otherwise. Hence the player-deleted cycle survival is at most
`17/20`. The finite-deadline and Never argument in Section 5.4 shows
that the entire behavioral cap equals the prescribed terminal payoff
at every suffix. No restriction to stationary or Markov deviations is
used.

Every original reward in the cube has absolute value below 11. Thus
the same profile gives terminal-to-N-stage delivery error at most
`880/(3N)` and deviation gain at most `1760/(3N)`, uniformly over
all complete unilateral replacements. Its fixed target is the exact
`U_A` from (6.3) at the constructed zero, not a sequence of targets
chosen separately for each accuracy.


The bounds on the following twenty coordinates can be dropped within
this same theorem; each can be any finite real number:

| Coalition | Recipients with irrelevant coordinates |
| --- | --- |
| 01 | 2,3 |
| 03 | 1,2 |
| 12 | 0,3 |
| 012 | 0,2,3 |
| 013 | 1,2,3 |
| 023 | 1,2 |
| 123 | 0,3 |
| 0123 | 0,1,2,3 |

At every prescribed date the only nonempty scheduled supports are
02,23,13 or their subsets. None of the listed coordinates occurs in
the prescribed recipient payoff or in that recipient's Quit or Continue
endpoint under any unilateral replacement. Their values therefore change
neither the actual payoffs nor the full response caps. All singleton
coordinates remain bounded by (6.1), so the no-markset argument also
survives. For this scope extension use any finite absolute bound M on
the original reward table: the uniform delivery and deviation bounds
are respectively `80M/(3N)` and `160M/(3N)`. This is a direct
irrelevant-coordinate observation about the same producer.


## 7. Boundary tests and complete selection checks

### 7.1 Every fixed marked set fails

Here are the precise conditions being tested. Choose nonempty M subset I.
For each unmarked i choose a literal floor ell_i<=0 with ell_i<s_i,
where s_i=r_i({i}), and require every passive reward of i to be at least
ell_i. For a proper support D and positive odds z on D, put

    Phi_i(z)=s_i+sum_(empty!=S subset D-i) z_S [r_i(S+i)-r_i(S)],
    q_i=z_i/(1+z_i) for i in D, and q_i=0 outside D.

The passive condition P requires, on every D disjoint from M,

    [Phi_i(z)>=ell_i for all i in D]
       => [b_k(q)+alpha_k(q)s_k<=s_k for every k in M].

The orientation condition O requires, on every proper D meeting M,

    [Phi_i(z)>=ell_i for all active unmarked i,
     Q_k(q)>s_k for all k in D intersect M]
       => [(-1)^|D| det D Phi_D(z)<=0].

The ledger-weight choices in a proposed producer are additional inputs;
they do not change O or P. We exclude every choice of M and allowed floor,
independently of any scalar or finite-family ledger selection.

On an unmarked singleton support {i}, Phi_i=s_i meets every floor. If k
is marked, P therefore requires q_i[r_k({i})-s_k]<=0. Consequently M
must contain every predecessor in the graph with edges i->k whenever
r_k({i})>s_k. For R* the graph is exactly the two bidirectional pairs
02 and13. Its only nonempty predecessor-closed sets are 02,13,I.

Both pairs 02 and13 have participant premiums (4,1) and joining gaps
(1,-2). For either pair, det D Phi=-(1)(-2)=2>0, and both active Quit
premiums are positive at every positive pair hazard. If that pair lies
in M, no active unmarked floor is present, and O is false. Each of the
three surviving M contains one such pair. All fifteen nonempty marked
sets, all allowed floors, and every ledger family are therefore excluded.

This complete argument also applies to every reward in Section 6: all
positive singleton increments remain near3, all negative increments near
-1, and both pairs retain positive premiums and opposite strict joining
gaps. The twenty irrelevant coordinates do not affect those comparisons.

### 7.2 Further exact raw tests and the two-pair near miss

For R* define L(v)=sum_i(v_i-1), H(S)=sum_i[r_i(S)-1], and
J(S)=sum_(i outside S)[r_i(S+i)-r_i(S)]. The singleton H values are1,
the singleton J values are(-2,-2,-1,0). In order01,02,03,12,13,23,
the pair H values are(0,7,0,0,7,0) and the pair J values are
(-6,-6,-5,-8,-6,-8). Triple H=3 and J=-1; grand H=32.
Thus this exact table lies in the proper H>=0,J<=0 class with strict
singleton H. The neighborhood theorem itself does not require H/J.

Every pair has opposite strict joining gaps, in order

    01:(-1,1), 02:(1,-2), 03:(2,-1),
    12:(-3,1), 13:(1,-2), 23:(-3,1).

Hence no relabeling supplies any scheduled pair requiring both joins
nonnegative or both joins negative. This defeats the necessary pair
premises of `GameTheory.PairedCycle.CrossedMatching.RawSource`,
`GameTheory.PairedCycle.CrossedMatching.WeakRawSource`,
`GameTheory.PairedCycle.CrossedMatching.InverseRawSource`
(`UniformEquilibrium/Quitting/Cycles/CrossedMatchingPhaseSource.lean`)
and `GameTheory.PairedCycle.BelowSingleton.RawFamily`
(`UniformEquilibrium/Quitting/Cycles/BelowSingletonJointPhaseSource.lean`),
independently of their auxiliary weights or cone choices. Each receiver
also has two negative singleton comparisons; the condition
`GameTheory.PairedCycle.RawRegion.eq_partner_of_singleton_lt`
(`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`)
would force each such owner to be its unique scheduled partner.

The positive singleton graph has no Hamiltonian directed cycle, so no
relabeling provides the positive predecessor edges of
`GameTheory.SignedFourCycleSingletonData`
(`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`).
A raw class requiring a recipient with two positive singleton comparisons
also fails. The principal-triple inverse criterion
`exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`)
fails for each deletion: every principal triple inverse has negative
diagonal entries. For instance a triple block has determinant6 and each
corresponding diagonal cofactor is -1 or -9.

The actual all-Quit-at-zero profile has payoff(9,9,9,9). Thus every
nonempty selected subset fails `GameTheory.HasQuittingActualWeakSubsetExclusion`,
and every normalized nonnegative weighting has surplus8, defeating
`GameTheory.HasQuittingActualNonconcentratedGroupExclusion`, for every admissible
concentration parameter. These definitions are in
`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawPredicates.lean`.
This tests all choices, not one coefficient or one grouping.

The implemented `GameTheory.FinFourTwoBlockSingletonFiber.TwoBlockTargetSingletonConditions`
(`UniformEquilibrium/Quitting/Examples/Cyclic/FinFourTwoBlockSingletonFiber.lean`)
requires an off-diagonal singleton comparison zero; all ours are -1 or3.
The singleton matrix of `GameTheory.FullCoreDeadlock.IsDeadlockRationalJointBlockCompletion`
(`UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockRationalPolyhedralBlock.lean`)
has a row with two positive off-diagonal entries; each of ours has one.
Both obstructions survive relabeling and positive recipient-affine changes.

The explicit overlapping period-three visible-affine cylinder consumed by
`exists_periodThreeClearedGapData_and_uniformPayoff_of_visible_affine_reward`
(`UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreePositiveAffineCylinder.lean`)
has radius eta=1/50000000, negative singleton comparisons near-1 and zero
center favorite-pair premiums. To produce ours, its singleton signs must
identify the same favorite matching02,13. A target negative comparison-1
forces the corresponding positive scale alpha<=1/(1-2eta). Each resulting
favorite-pair premium is therefore at most2eta/(1-2eta)<1, whereas ours
are4,1,4,1. All these coordinates are visible. This excludes the stated
explicit cylinder, not an unspecified maximal continuation neighborhood.

Any symmetric positive-hazard solution of the active equations for the
opposite-pair-only schedule02|13, with hazards x for owners0,1 and y for
owners2,3, would give owner3 in the02 phase Quit value1-2x and
continuation value1-2x/(1-x), so its profitable gain is
2x^2/(1-x)>0. This exact comparison explains why satisfying just the
active pair equations is insufficient. The four-phase schedules check
every inactive action as well.

At hazards(1/10,1/4,0,3/4), the active Quit values on013 are
(17/16,71/20,41/40)>1. Thus R* is not proper-triple product-low.
Generic periodic-block, interval-face and algebraic-box verifiers are
supplied-data consumers, not excluded producers: the present proof is
newly supplied successful data for their existing semantic endpoint.
Appendix A separately checks every stationary support and all sure-row
cap sources, avoiding an inference from stationary failure to arbitrary
punishment-tail failure.

## 8. Adapter, consumer and Lean handoff

A raw adapter receives either literal R* or a reward table obeying the
coordinate inequalities in Section 6. For R*, the two-dimensional Banach
argument produces a,b, hence all seven hazards and all value rows. For
the neighborhood, the eight-dimensional argument produces all eight
hazards and the exact geometric payoff formula. No strategic input
remains unproduced. The finite endpoint checks and player-deleted
contraction then instantiate the existing periodic-block consumer; the
proof above also supplies a direct unrestricted-behavior argument.

For formalization, separate the rational polynomial/interval root lemma
from the table-to-profile adapter. Suggested theorem conclusions are
existence of these explicit-support `IsQuittingBlockCertificate` data,
exact all-suffix terminal Nash, and one fixed uniform target with the
stated horizon constants. Do not encode existence of a root or equilibrium
as a raw-class structure field. The exact code in Appendices B and C
specifies finite rational inequalities and symbolic identities to verify;
it is mathematical evidence, not a replacement for a Lean proof.
Use the existing `IsQuittingBlockOnPathValue` and root-action interfaces
in `UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean` and the
finite-horizon consumer named in Section 4. No library refactor is needed.

## 9. Scope and nonclaims

The theorem solves R* and the explicit nonflat raw region in Section 6.
It does not solve every two-opposite-pair table, every H/J table, arbitrary
Fin4, or a general switched marked-cap invariant. No positive unrestricted
regret-gap counterexample is asserted. No claim that every table in the
neighborhood lacks stationary equilibrium is needed or made. The exact
original table supplies the complete stationary separation in Appendix A.

## Appendix A. Complete stationary and sure-source census for R*

### A.1 Complete sure-coordinate cap-root exclusion

Because all passive rewards are nonnegative, every actual full cap is
nonnegative. The following is stronger than a stationary boundary check:
there is no full finite Nash root with a sure coordinate at ANY
continuation annotation B>=0.

If player 0 is sure, player 2 strictly Continues at every complementary
profile. Player 3 then strictly Continues, and player 1 surely Quits.
Owner 0 would get -1 from Quit and 0 from withdrawal. If player 1 is
sure, the corresponding strict cascade makes 3 Continue, then 0 Continue,
then 2 surely Quit. Owner 1 would get -3 instead of 0.

If player 2 is sure, player 1 strictly Continues. The remaining owner-0
and owner-3 gaps, with `(a,c)=(q_0,q_3)`, are

    g_0=1-(13/2)c,  g_3=1-4a.

The complete complementary Nash set is the two pure pairs `(a,c)=(1,0)`
and `(0,1)`, and the mixed point `(1/4,2/13)`. The pure cases fail owner
2's own comparison: its Quit reward is respectively 2 versus passive 4,
or -3 versus passive 0. At the mixed point,

    Q_2=35/52 < b_2=47/52 <= C_2(B).

If player 3 is sure, player 2 strictly Continues. For
`(a,b)=(q_0,q_1)`, the remaining gaps are

    g_0=2-5b,  g_1=1-(7/2)a.

The complete complementary Nash set is `(a,b)=(1,0)`, `(0,1)`, and
`(2/7,2/5)`. The pure cases fail owner 3's comparison, respectively -1
versus 0 and 2 versus 4. At the mixed point,

    Q_3=5/7 < b_3=46/35 <= C_3(B).

These are exhaustive complementary Nash correspondences. They directly
exclude sure-coordinate cap roots; no conclusion about a separate
punishment-tail interface is inferred merely from stationarity.

### A.2 Every nonsure stationary support is excluded

Literal Never makes every stationary equilibrium value nonnegative.
All-Never fails because the singleton rewards are one. A sole active
player is defeated by its cyclic successor, whose passive singleton reward
is zero and whose Quit payoff is positive for every positive hazard.

On adjacent supports 01,12,23,30, the successor's Never payoff is zero
and its forced Quit payoff is respectively 1,1,1, or `1+q_3`.
On support 02, player 2 gets 4 from Never but at most 2 from Quit;
on support 13, player 3 has the same comparison. Thus every pair fails.

For a full-support nonsure stationary profile, every singleton outcome
has positive probability. All proper H values and the grand H value are
nonnegative, while all singleton H are positive. Its terminal value v
therefore has `L(v)>0`. Full active indifference instead gives
`L(v)=sum z_S J(S)<=0`. Thus full support is impossible.

On a proper triple, every active i must satisfy
`Q_i=b_i/(1-alpha_i)`, in particular `Q_i>=b_i`. Write
`F_i=(1-alpha_i)Q_i-b_i`; every such active residual must vanish.

For support 012 set `(a,b,c)=(q_0,q_1,q_2)`. The unchanged owner-1
formulas are `Q_1=1-4c+2ac`, `b_1=2ac`. They imply
`1/6<=c<=1/4`. Also `Q_0>=b_0` implies `b<=1/2`. Owner 0 has residual

    F_0=b(1-2b)-c(3-7b/2+2b^2)+4c^2(1-b)^2.

Since `c<=1/4`, the coefficient after factoring the negative c is at
least `2-3b/2+b^2>=3/2` on this b interval. Hence
`F_0<=1/8-(3/2)c<=-1/8`, contradicting indifference.

For support 023 set `(a,b,c)=(q_0,q_2,q_3)`. Owner 3 satisfies
`Q_3=1-2a=2ab/(a+b-ab)<=2a`, so `a>=1/4`. Owner 2 has

    Q_2=1+a-4c+ac,  b_2=4a-(5/2)ac.

Its necessary `Q_2>=b_2` is stronger than
`1-3a-2c+(3/2)ac>=0`, giving `a<=1/3,c<=2/13`.
Its residual is the auxiliary expression

    a^2-3a+c(1+a/2-2a^2)-c^2(2-a-a^2)

minus the nonnegative quantity `2c(1-a)(a+c-ac)`. The auxiliary expression is
at most `-11/16+2/13=-111/208`, so indifference fails.

For support 013 set `(a,b,c)=(q_0,q_1,q_3)`. Owner 0 satisfies
`Q_0=1-2b+c-bc>=1-2b`, while its Never payoff
`2bc/(b+c-bc)<=2b`; therefore `b>=1/4`. Owner 3 has

    Q_3=1-2a+b-ab,  b_3=4b-(5/2)ab.

The necessary `Q_3>=b_3` gives `b<=1/3,a<=2/13`. Its residual is

    F_3=b^2-3b+a(1+b/2-2b^2)-a^2(2-b-b^2).

The same bounds give `F_3<=-111/208`.

Finally for support 123 set `(a,b,c)=(q_1,q_2,q_3)`. Owner 2 has
`Q_2=1-4c+2ac`, `b_2=2ac`, so `1/6<=c<=1/4`. Owner 1 has

    Q_1=1-4b+4c-2bc,  b_1=4c-(5/2)bc.

The necessary comparison implies `b<=8/31<1/3`. Its residual is

    F_1=b(1-4b)-c(3-3b/2-2b^2)+c^2(4-6b+2b^2).

Factoring the negative c, the remaining coefficient is at least
`2-(5/2)b^2>=31/18`. Therefore
`F_1<=1/16-(31/18)c<=-97/432<0`. This exhausts all supports.

### A.3 Additional raw exclusions and reward closure

For the global inserted-premium floor, write
`W_w(S)=sum_i w_i[r_i(S+i)-1]`. The four singleton forms are

    W0=w2-2w3,  W1=-2w0+w3,
    W2=4w0-4w1, W3=w0+4w1-4w2.

They have the exact separating combination

    3W0+5W1+2W2+W3=-w0-4w1-w2-w3<0

for every nonzero nonnegative w. Thus no such global floor weight exists.
Every player has a negative proper-triple participant reward, so no
player has nonnegative rewards on all coalitions containing it. The grand premium vector `(8,8,8,8)` excludes every nonzero
weighted upper-average test whose necessary grand condition is
nonpositive. A raw test requiring the unweighted inserted-premium sum
P(S)=sum_i[r_i(S+i)-1] to be strictly negative on all singletons fails
at singleton3, where P=1.

The singleton matrix remains

    Gamma=[0,-1,3,-1; -1,0,-1,3; 3,-1,0,-1; -1,3,-1,0].

Its pair principal determinants are -1 or -9, its four triple principal
determinants are 6, and its full determinant is 45. If `p>=0`,
`Gamma p>=0`, and `p_i(Gamma p)_i=0`, a support of size at least two
would give a nonzero vector in an invertible principal block's kernel.
A singleton support fails at a negative external entry. Thus p=0.

This also excludes reward closure of exact stationary equilibria. For
nearby reward tables and exact stationary hazards tending to a nonzero
limit, the Bellman comparisons and terminal payoff pass to the limit.
With at least two active players each owner faces eventual opponent
absorption; with one active player its own limiting singleton payoff 1
beats Never0. Either case supplies the excluded stationary equilibrium.
If the hazards tend to zero, normalize them by their total intensity
to obtain a nonzero probability vector p. Terminal payoffs tend to
`1+Gamma p`. Date-zero Quit gives `Gamma p>=0`, and active indifference
for every `p_i>0` gives `p_i(Gamma p)_i=0`, contradicting the preceding
matrix calculation. This is ordinary mathematics, not a new Lean claim.


### A.4 All singleton and persistent-base punishment selections

The sure-row proof concerns every nonnegative continuation annotation,
not just stationary continuation values or attained best-reply caps.
For any opponent plan, literal Never receives only passive rewards or
zero; every passive reward in R* is nonnegative. Hence every complete
best-reply cap is nonnegative, and so is their infimum chi_j over all
opponent plans. This is the exact quantity `GameTheory.quittingPunishmentValue`
in `UniformEquilibrium/Quitting/Stationary/MinMax.lean`; no attainment
of the infimum is assumed.

`GameTheory.QuittingSingletonBaseCertificate`
(`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingletonBaseSemanticDispatch.lean`)
requires one owner j to Quit surely, every nonowner to satisfy its
induced endpoint Nash comparisons, and the field `owner_floor_balance`
requires

    Q_j >= b_j+alpha_j chi_j.

Because chi_j>=0, choose a continuation annotation with coordinate j
exactly chi_j and all others zero. The other players still face sure
j, so their Continue masses are zero; their comparisons do not depend
on the annotation. This produces precisely a full cap-Nash row with a
sure coordinate at a nonnegative annotation, excluded by A.1. The
argument covers every owner, every opponent Nash choice and every
punishment plan, including approximating sequences for the infimum.
It does not replace the punishment floor by a convenient stationary
continuation.

For `GameTheory.QuittingPersistentBaseCertificate`
(`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseSemanticDispatch.lean`),
the base has at least two sure Quitters. Every player then faces a sure
opponent, so every Continue mass is zero. Its `free_nash`, `base_leave`
and `outsider_join` fields are the full endpoint Nash conditions at
any annotation, including zero. A.1 excludes them for every base,
free set and root. This is a direct all-selection exclusion of these
named successful-face inputs, not an inference from failure of
stationary repetition. It does not classify arbitrary other supplied
nonstationary punishment architectures.

## Appendix B. Complete exact certificate for R*

Save the following code as `CERTIFICATE_ORIGINAL.py` and run it with
Python3 and SymPy. Every asserted inequality is exact rational arithmetic;
SymPy is used only for rational polynomial identities and differentiation.
The decimal output is not a proof premise. Interval arithmetic encloses
products by all endpoint products, reciprocal only across intervals
excluding zero, and sums by endpoint addition. Consequently the finite
assertions are independently reproducible rational bounds.

```python
"""Rational Banach certificate for the four-phase two-pair residual equilibrium.

All assertions use exact rational arithmetic or symbolic rational identities.
The two polynomial equations have a unique root in the displayed box.
At that root the supplied value rows satisfy Bellman, active indifference,
strict inactive Continue inequalities, and opponent-cycle absorption.
The existing periodic-block consumer gives an exact terminal equilibrium
against complete behavioral replacements and the same fixed uniform target.
This script is an arithmetic certificate, not a Lean formalization.
"""
from fractions import Fraction as F
from itertools import product
import sympy as sp


class Interval:
    def __init__(self, lo, hi=None):
        self.lo = F(lo)
        self.hi = F(lo if hi is None else hi)
        assert self.lo <= self.hi

    @staticmethod
    def of(x):
        return x if isinstance(x, Interval) else Interval(x)

    def __add__(self, other):
        y = self.of(other)
        return Interval(self.lo+y.lo, self.hi+y.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -self.of(other)

    def __rsub__(self, other):
        return self.of(other) + -self

    def __mul__(self, other):
        y = self.of(other)
        values = [x*z for x,z in product((self.lo,self.hi),(y.lo,y.hi))]
        return Interval(min(values), max(values))

    __rmul__ = __mul__

    def __truediv__(self, other):
        y = self.of(other)
        assert y.lo*y.hi > 0, (y.lo,y.hi)
        return self * Interval(1/y.hi,1/y.lo)

    def __rtruediv__(self, other):
        return self.of(other) / self

    def __pow__(self, n):
        assert n >= 0
        answer = Interval(1)
        for _ in range(n):
            answer = answer*self
        return answer

    def magnitude(self):
        return max(abs(self.lo),abs(self.hi))

    def display(self):
        return (float(self.lo),float(self.hi))


a,b = sp.symbols('a b')
p = [
    6966*a**3*b**3-10107*a**3*b**2+3426*a**3*b-277*a**3
    -9342*a**2*b**3+6351*a**2*b**2+4039*a**2*b-1464*a**2
    +3906*a*b**3+983*a*b**2-4070*a*b-11*a-522*b**3-659*b**2+781*b,
    -141966*a**3*b**3+182259*a**3*b**2-37158*a**3*b-2607*a**3
    +101574*a**2*b**3-141*a**2*b**2-168283*a**2*b+39522*a**2
    -20394*a*b**3-3371*a*b**2+53252*a*b+17313*a+770*b**3-5611*b**2-15159*b,
]
center = [F(156714212,10**9),F(289202614,10**9)]
radius = F(1,10**7)
box = [Interval(x-radius,x+radius) for x in center]
preconditioner = [[F(-1000451318,10**12),F(-207610,10**12)],
                  [F(-2071352271,10**12),F(-70083520,10**12)]]
assert sp.Matrix(preconditioner).det() != 0


def polynomial(expr, values):
    result = Interval(0)
    for (i,j),coefficient in sp.Poly(expr,a,b).terms():
        result += F(coefficient)*values[0]**i*values[1]**j
    return result


jac = [[polynomial(sp.diff(p[i],x),box) for x in (a,b)] for i in range(2)]
error_jac = [[(1 if i==j else 0)-sum(preconditioner[i][k]*jac[k][j] for k in range(2))
              for j in range(2)] for i in range(2)]
contraction = max(sum(e.magnitude() for e in row) for row in error_jac)
offset = max(abs(sum(preconditioner[i][k]*F(p[k].subs(dict(zip((a,b),center))))
                    for k in range(2))) for i in range(2))
assert contraction < F(1,1000)
assert offset < F(1,10**9)
assert offset + contraction*radius < radius
print('Banach: contraction < 1/1000; center displacement < 1/10^9; radius=1/10^7.')
print('Computed upper bounds:',float(contraction),float(offset))


def construct(a,b):
    g=F(17,50)
    v=a+b-3*a*b
    f=v/(2+v)
    d=f/(1+f)
    k=2*f*g+(1-f)*(1-g)*(1+a)
    e=(1-k)/(4-k)
    c=1-(1-3*a)/((1-a)*(1-4*e))
    D0=2*f*g+(1-f)*(1-g)*(1+4*b)
    C0=4*d+F(1,2)*d*e+(1-d)*(1-e)*D0
    C1=4*e-F(5,2)*d*e+(1-d)*(1-e)*(1+4*g)
    B1=4*c+(1-c)*C1
    q=[[a,0,b,0],[0,0,0,c],[0,0,d,e],[0,f,0,g]]
    U=[[1+4*b,1/(1-g),1+a,(1-3*f)/(1-f)],
       [1/(1-b),B1,(1-3*a)/(1-a),1],
       [C0,C1,1-4*e,1],
       [D0,1+4*g,k,1+f]]
    eq=[(1-c)*C0-1/(1-b),2*a*b+(1-a)*(1-b)*B1-1/(1-g)]
    return q,U,eq


qs,Us,eq = construct(a,b)
den = [4*(a-1)*(b-1)*(3*a*b-a-b-1)*(51*a*b-50*a-17*b-33),
       132*(3*a*b-a-b-1)*(51*a*b-50*a-17*b-33)]
for i in range(2):
    assert sp.cancel(eq[i]-p[i]/den[i]) == 0
    assert polynomial(den[i],box).lo*polynomial(den[i],box).hi > 0

R = {
    1:(1,0,4,0),2:(0,1,0,4),4:(4,0,1,0),8:(0,4,0,1),
    3:(-1,1,F(5,2),F(3,2)),5:(5,2,2,2),9:(2,F(3,2),F(3,2),-1),
    6:(F(3,2),-3,1,F(9,2)),10:(2,5,2,2),12:(F(9,2),F(3,2),-3,1),
    7:(-1,-1,-1,10),11:(-1,-1,10,-1),13:(-1,10,-1,-1),
    14:(10,-1,-1,-1),15:(9,9,9,9),
}
supports=[5,8,12,10]


def endpoints(q,i):
    Q=0; passive=0; alpha=1
    opponents=[j for j in range(4) if j!=i]
    for j in opponents:
        alpha *= 1-q[j]
    for flags in product((0,1),repeat=3):
        S=sum(1<<j for j,flag in zip(opponents,flags) if flag)
        probability=1
        for j,flag in zip(opponents,flags):
            probability *= q[j] if flag else 1-q[j]
        Q += probability*R[S | 1<<i][i]
        if S:
            passive += probability*R[S][i]
    return Q,passive,alpha


# Exact rational identities: all active equations vanish, and only two
# inactive Continue transport equations remain, precisely the two polynomials.
for phase in range(4):
    for i in range(4):
        Q,passive,alpha = endpoints(qs[phase],i)
        C=passive+alpha*Us[(phase+1)%4][i]
        if supports[phase]>>i&1:
            assert sp.cancel(Q-C)==0
        transport=qs[phase][i]*Q+(1-qs[phase][i])*C-Us[phase][i]
        expected=eq[1] if (phase,i)==(0,1) else eq[0] if (phase,i)==(1,0) else 0
        assert sp.cancel(transport-expected)==0, (phase,i)
print('PASS exact symbolic active indifference and all sixteen Bellman identities.')

qi,Ui,_ = construct(*box)
qi=[[Interval.of(x) for x in row] for row in qi]
Ui=[[Interval.of(x) for x in row] for row in Ui]
margin=F(100)
for phase in range(4):
    for i in range(4):
        if supports[phase]>>i&1:
            assert 0 < qi[phase][i].lo <= qi[phase][i].hi < 1
        else:
            Q,passive,alpha=endpoints(qi[phase],i)
            C=passive+alpha*Ui[(phase+1)%4][i]
            gap=Q-C
            assert gap.hi < -F(3,1000), (phase,i,gap.display())
            margin=min(margin,-gap.hi)
            print('Inactive gap',phase,i,gap.display())
for i in range(4):
    opponent_survival=Interval(1)
    for row in qi:
        for j in range(4):
            if j!=i:
                opponent_survival *= 1-row[j]
    assert opponent_survival.hi < 1
print('PASS strict inactive Continue gaps >3/1000 and every opponent cycle absorbs.')
print('Target enclosure:',[x.display() for x in Ui[0]])

```

## Appendix C. Complete simultaneous reward-region certificate

Save the following as `CERTIFICATE_PAID_RETURN.py` and run with Python3.
It uses only the standard-library Fraction type. The interval derivative
class applies the exact sum, product and quotient differentiation rules;
each gradient coordinate encloses the corresponding partial derivative.
The raw reward intervals are independent and treated simultaneously.
The argument in Section 6 turns the verified bounds into a theorem for
every real reward table in the region.

```python
"""Exact simultaneous reward-box certificate for the paid two-pair repair.

Anchor: R* with r_3({2,3}) increased from 1 to 1001/1000.
Word: {0,2}, {2,3}, {2,3}, {1,3}. All eight scheduled hazards are interior.
Every one of the sixty rewards may vary independently within the certified
radius. A common rational Banach map finds an exact periodic equilibrium for
each such table. Values and all complete behavioral response caps coincide.
Only Fraction arithmetic is used for every inequality; floats only display
completed exact bounds. No optimizer output is used as proof.
"""
from fractions import Fraction as F
from itertools import product


class I:
    def __init__(self,lo,hi=None):
        self.lo=F(lo); self.hi=F(lo if hi is None else hi)
        assert self.lo<=self.hi
    @staticmethod
    def of(x): return x if isinstance(x,I) else I(x)
    def __add__(self,o):
        o=I.of(o); return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self,o): return self+-I.of(o)
    def __rsub__(self,o): return I.of(o)+-self
    def __mul__(self,o):
        if isinstance(o,D): return o*self
        o=I.of(o)
        v=[x*y for x,y in product((self.lo,self.hi),(o.lo,o.hi))]
        return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=I.of(o); assert o.lo*o.hi>0
        return self*I(1/o.hi,1/o.lo)
    def __rtruediv__(self,o): return I.of(o)/self
    def mag(self): return max(abs(self.lo),abs(self.hi))
    def out(self): return (float(self.lo),float(self.hi))


class D:
    """An interval value and eight interval partial derivatives."""
    def __init__(self,v,grad=None):
        self.v=I.of(v); self.grad=[I(0)]*8 if grad is None else grad
    @staticmethod
    def of(x): return x if isinstance(x,D) else D(x)
    def __add__(self,o):
        o=D.of(o);return D(self.v+o.v,[x+y for x,y in zip(self.grad,o.grad)])
    __radd__=__add__
    def __neg__(self): return D(-self.v,[-x for x in self.grad])
    def __sub__(self,o): return self+-D.of(o)
    def __rsub__(self,o): return D.of(o)+-self
    def __mul__(self,o):
        o=D.of(o)
        return D(self.v*o.v,[x*o.v+self.v*y for x,y in zip(self.grad,o.grad)])
    __rmul__=__mul__
    def __truediv__(self,o):
        o=D.of(o)
        reciprocal=1/o.v
        return D(self.v*reciprocal,
                 [(x-self.v*reciprocal*y)*reciprocal for x,y in zip(self.grad,o.grad)])
    def __rtruediv__(self,o): return D.of(o)/self


anchor={
    1:(1,0,4,0),2:(0,1,0,4),4:(4,0,1,0),8:(0,4,0,1),
    3:(-1,1,F(5,2),F(3,2)),5:(5,2,2,2),9:(2,F(3,2),F(3,2),-1),
    6:(F(3,2),-3,1,F(9,2)),10:(2,5,2,2),12:(F(9,2),F(3,2),-3,F(1001,1000)),
    7:(-1,-1,-1,10),11:(-1,-1,10,-1),13:(-1,10,-1,-1),
    14:(10,-1,-1,-1),15:(9,9,9,9),
}
SUPPORTS=(5,12,12,10)
ACTIVE=[(k,i) for k in range(4) for i in range(4) if SUPPORTS[k]>>i&1]
CENTER=[F(n,10**13) for n in (
    1568411120007,2869644501486,1177298486,930080404969,
    1178614542459,769092048080,1337423880501,3431264118066)]
RADIUS=F(1,10**4)
REWARD_RADIUS=F(1,10**5)
AINTEGER=[
    [169080595,-258131102,10412137,474486148,-44759569,-28348111,2649595,-318962995],
    [-174123720,346934192,-196347562,-1306934468,-176789427,80825488,600819556,900447546],
    [-20006,43053,-29864,998859702,-29083,-921059857,92781,-720347],
    [118917269,114956009,-242647534,333714208,-31480169,-19937711,1863505,-224332120],
    [-20030753,43105863,-29900802,-23714037,-29118865,892751019,92896089,-721237511],
    [108417482,104805981,54413405,304248949,-249235268,-18177313,1698967,-204524740],
    [-25766638,55449396,-38463014,-30504645,-37457166,14785006,119497249,-270893121],
    [653133623,-255507249,272695166,1828679930,249261628,-110553697,-1784774,-1200078293],
]
A=[[F(x,10**9) for x in row] for row in AINTEGER]


def check_invertible(matrix):
    m=[row[:] for row in matrix]
    for j in range(len(m)):
        pivot=next(i for i in range(j,len(m)) if m[i][j])
        m[j],m[pivot]=m[pivot],m[j]
        for i in range(j+1,len(m)):
            t=m[i][j]/m[j][j]
            m[i]=[x-t*y for x,y in zip(m[i],m[j])]
    assert all(m[j][j] for j in range(len(m)))


def evaluate(hazard_radius):
    R={S:[I(x-REWARD_RADIUS,x+REWARD_RADIUS) for x in row] for S,row in anchor.items()}
    q=[[D(0) for _ in range(4)] for _ in range(4)]
    for j,(k,i) in enumerate(ACTIVE):
        grad=[I(0) for _ in range(8)];grad[j]=I(1)
        q[k][i]=D(I(CENTER[j]-hazard_radius,CENTER[j]+hazard_radius),grad)
    survival=[]; stage=[]
    for row in q:
        mass=[]
        for S in range(16):
            p=D(1)
            for i in range(4): p*=row[i] if S>>i&1 else 1-row[i]
            mass.append(p)
        survival.append(mass[0])
        stage.append([sum((mass[S]*R[S][i] for S in range(1,16)),D(0)) for i in range(4)])
    cycle_survival=D(1)
    for x in survival: cycle_survival*=x
    assert cycle_survival.v.hi<1
    U=[]
    for k in range(4):
        value=[D(0) for _ in range(4)];prefix=D(1)
        for d in range(4):
            t=(k+d)%4
            value=[x+prefix*y for x,y in zip(value,stage[t])]
            prefix*=survival[t]
        U.append([x/(1-cycle_survival) for x in value])
    gap=[];opponent_survivals=[I(1) for _ in range(4)]
    for k in range(4):
        gap.append([])
        for i in range(4):
            others=[j for j in range(4) if j!=i]
            Q=D(0);passive=D(0);alpha=D(1)
            for j in others: alpha*=1-q[k][j]
            opponent_survivals[i]*=alpha.v
            for flags in product((0,1),repeat=3):
                S=sum(1<<j for j,flag in zip(others,flags) if flag)
                p=D(1)
                for j,flag in zip(others,flags): p*=q[k][j] if flag else 1-q[k][j]
                Q+=p*R[S|1<<i][i]
                if S:passive+=p*R[S][i]
            gap[k].append(Q-passive-alpha*U[(k+1)%4][i])
    return q,U,gap,opponent_survivals


if __name__=='__main__':
    check_invertible(A)
    q,U,gaps,opponent_survivals=evaluate(RADIUS)
    J=[gaps[k][i].grad for k,i in ACTIVE]
    norm=F(0)
    for i in range(8):
        rownorm=F(0)
        for j in range(8):
            E=(1 if i==j else 0)-sum((A[i][k]*J[k][j] for k in range(8)),I(0))
            rownorm+=E.mag()
        norm=max(norm,rownorm)
    assert norm<F(41,500),float(norm)
    _,_,center_gaps,_=evaluate(F(0))
    G=[center_gaps[k][i].v for k,i in ACTIVE]
    offset=max(sum((A[i][j]*G[j] for j in range(8)),I(0)).mag() for i in range(8))
    assert offset<F(183,2*10**6),float(offset)
    assert offset+norm*RADIUS<RADIUS
    print('PASS simultaneous Banach certificate for all sixty-coordinate reward perturbations.')
    print('Reward radius:',float(REWARD_RADIUS),'hazard radius:',float(RADIUS))
    print('Contraction:',float(norm),'center displacement:',float(offset))
    for k,i in ACTIVE:
        assert 0<q[k][i].v.lo<=q[k][i].v.hi<1
    worst=F(-100)
    for k in range(4):
        for i in range(4):
            if (k,i) not in ACTIVE:
                assert gaps[k][i].v.hi<-F(3,1000),(k,i,gaps[k][i].v.out())
                worst=max(worst,gaps[k][i].v.hi)
                print('Inactive gap:',k,i,gaps[k][i].v.out())
    assert all(x.hi<1 for x in opponent_survivals)
    print('PASS every inactive Continue gap >3/1000, hazards interior, opponent-cycle absorption.')
    print('Opponent survival upper bounds:',[float(x.hi) for x in opponent_survivals])
    print('Target enclosure:',[x.v.out() for x in U[0]])

```
