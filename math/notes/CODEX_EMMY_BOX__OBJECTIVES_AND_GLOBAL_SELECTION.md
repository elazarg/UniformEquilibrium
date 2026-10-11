# Objectives cannot repair a frozen root alphabet

Author: `CODEX_EMMY_BOX`

Status: **ordinary mathematics, not Lean-checked.** Sections 3--8 are
bounded independently checked by `CODEX_TURING_BOX`, with Proposition 2's
universal exclusion restricted to the two-player table and Proposition 4's
extraction obstruction restricted to the stated root alphabet. The review is
[`CODEX_EMMY_BOX__OBJECTIVES_AND_GLOBAL_SELECTION__BY_CODEX_TURING_BOX.md`](../feedback/CODEX_EMMY_BOX__OBJECTIVES_AND_GLOBAL_SELECTION__BY_CODEX_TURING_BOX.md).
No Lean implementation, export, or new game-class coverage is claimed.
Section12 is a separate unreviewed ordinary proof: positive weighted
coercivity of the COMPLETE stationary odds field forces an already covered
persistent sure-quitter base. It does not obstruct finite-annulus degree
arguments for scaled raw reward classes.
Section13 is a new unreviewed complete proof draft: exogenous public Markov
roots with regeneration rate kappa and pointwise total hazard delta can be
replaced by actual private stationary clocks with full-debt loss at most
40R*delta/kappa. A source producing delta/kappa->0 is NOT established.
Section14 is separate ordinary UNREVIEWED supporting mathematics for the
new cap-chamber route. It reuses the existing standard-Q column-sum
obstruction to produce an ACTUAL pure-clock low-cap/surplus seed on every
nonnegative-own-singleton standard-Q table. It proves no new UE class:
preservation of a suitable closed region remains the global question.

The concrete finding is an objective-independent obstruction to one restricted
operation: freeze an infinite sequence of public root signals, retaining a
fixed positive quit hazard at each selected owner. In the exact game below,
every such word has full terminal exploitability at least `1/12`, while the
unfrozen iid public construction is an exact equilibrium in its public
extension. Changing the legal private roots, rather than the objective,
produces terminal approximate equilibria with the same limiting payoff.

A second exact test, in Section 6, isolates public *memory* rather than
large hazards. A public exact equilibrium with arbitrarily small conditional
total hazards can have a target attained by actual private prescribed
payoffs but excluded from all private uniform-equilibrium payoffs. The
failure is in complete caps. Therefore diffuseness alone does not justify
history-dependent marginal rebalancing or fixed-target public decoding.

This is a sharp test of the restriction, not a new equilibrium class. In
particular, the earlier notebook
[`CODEX_CEDAR__PREDICTABLE_SINGLE_OWNER_DERANDOMIZATION.md`](CODEX_CEDAR__PREDICTABLE_SINGLE_OWNER_DERANDOMIZATION.md)
records a stronger, different-table obstruction to universal one-active
derandomization, including variable hazards. Its status was noticed during
the final narrow overlap check; the present fixed-root calculation must not
be advertised as the first failure of the one-active architecture.

## 1. Self-contained question and semantics

Let `I={0,1,2}`. A quitting game gives each nonempty coalition `S` a terminal
payoff vector `r(S)`. Each live date, players independently choose Quit or
Continue using their private coins and the public history. The first date
with a nonempty quitter set absorbs and pays its reward forever. Never
absorbing pays `0`. Strategies and unilateral deviations are unrestricted
behavioral strategies, not bounded controllers or periodic strategies.

For an ordinary private profile `p`, write

```text
U_i(p) = expected terminal payoff,
B_i(p) = sup over all unilateral behavioral deviations of terminal payoff,
D_i(p) = B_i(p)-U_i(p),
E(p)   = max_i D_i(p).
```

Since retaining one's strategy is permitted, every `D_i>=0`.

**Question.** If a stationary fresh-public-signal profile is an exact public
equilibrium, can some infinite deterministic realization of its root signals
have arbitrarily small ordinary private exploitability, without changing
the corresponding selected private hazards? This asks about all words,
not only periodic words, and therefore tests any scalar, nonlinear,
lexicographic, or Pareto selection rule whose final output remains such a
word. No convexity of the set of independently attainable laws is assumed.

**Answer in this exact example:** no. Every word has `E>=1/12`.
Nevertheless, allowing small simultaneous independent hazards gives `E→0`.

The public profile below belongs to an explicitly different information
structure: at every live date all players see a fresh public signal before
choosing their actions. It is not silently inserted into the project's
ordinary behavioral strategy class.

## 2. The finite table, including an explicit Fin4 padding

Singleton reward vectors are

```text
r({0})=(1,0,2),
r({1})=(2,1,0),
r({2})=(0,2,1).
```

Every coalition of at least two active players pays `(0,0,0)`.
Never pays `(0,0,0)`. Thus rewards lie in `[0,2]`.

For a literal four-player instance add player `3` and put
`A=S∩{0,1,2}`. For an active recipient `i`, set

```text
r_i(S) = displayed singleton reward of A, if A is a singleton;
r_i(S) = 0, if A is empty or has at least two elements.
r_3(S) = 0 for every nonempty S.
```

In every profile considered player `3` Never quits. An active player's
unilateral deviations therefore reproduce exactly the three-player game.
Player `3` always has payoff and cap zero. Membership of `3` in an absorbing
coalition does not change active singleton rewards, but this extra
specification is not needed to identify the active unilateral caps.

## 3. Every frozen half-hazard owner word has a positive full-cap gap

For any deterministic word `a:ℕ→{0,1,2}`, at date `t` let only owner `a_t`
quit with probability `1/2`; the other two players Continue surely. All
coins are private and independent. Denote this actual profile by `p^a`.
Its survival through `t` preceding dates is `2^{-t}`, so it absorbs almost
surely at a singleton. It may be nonperiodic and have unbounded memory.

**Proposition 1.** For every such word, `E(p^a)>=1/12`.

**Proof.** Cyclic relabeling permits `a_0=0`. Let `μ_j` be the conditional
probability that, starting at date `1`, eventual absorption is at owner `j`.
Thus

```text
μ_j = sum_{t>=1 : a_t=j} 2^{-t},
μ_0+μ_1+μ_2=1,
U_0(1)=1+μ_1-μ_2,
U_1(1)=1+μ_2-μ_0,
U_2(1)=1+μ_0-μ_1.
```

Put `E=E(p^a)`. Player `0` may replace only its date-0 half-quit action
by sure Quit or sure Continue and then retain the original tail. The two
payoff differences from the prescribed half-action are opposite numbers,
with magnitude `(1/2)|μ_1-μ_2|`. Both are complete legal deviations. Hence

```text
E >= (1/2)|μ_1-μ_2|.                              (3.1)
```

Player `1` has prescribed date-0 payoff `(1/2)U_1(1)`, because it receives
zero if owner `0` quits. By quitting surely at date `0`, player `1` receives
`1` if `0` Continues and zero in a collision, for total payoff `1/2`.
Consequently

```text
E >= (1/2)(μ_0-μ_2).                              (3.2)
```

In particular `|μ_1-μ_2|<=2E` and `μ_2>=μ_0-2E`. Now distinguish the
three possibilities for the second symbol `b=a_1`.

If `b=0`, then `μ_0>=1/2`. Equations (3.1)--(3.2) imply

```text
μ_2>=μ_0-2E,
μ_1>=μ_2-2E>=μ_0-4E,
1=μ_0+μ_1+μ_2>=3μ_0-6E>=3/2-6E.
```

Therefore `E>=1/12`. This includes the constant word as well as every
word with two initial zeroes.

If `b=1`, then `μ_1>=1/2`. Equation (3.1) gives
`μ_2>=1/2-2E`, whence `μ_0<=2E`. Let `ν` be the conditional absorption
distribution beginning at date `2`. Then

```text
μ=(1/2)e_1+(1/2)ν,
ν_2=2μ_2>=1-4E,
ν_0=2μ_0<=4E.
```

The continuation payoff to owner `1` after date `1` is
`U_1(2)=1+ν_2-ν_0`. Changing only its date-1 half-action to the better of
sure Quit and sure Continue gains `(1/2)|ν_2-ν_0|`, conditional on reaching
that date. Player `1` was prescribed Continue at date `0`, so this complete
root deviation reaches date `1` with probability `1/2`. Thus

```text
E >= (1/4)|ν_2-ν_0| >= (1/4)(1-8E) = 1/4-2E.
```

Again `E>=1/12`. The absolute-value inequality remains valid if its right
side is negative; no smallness assumption on `E` has been inserted.

If `b=2`, then `μ_2>=1/2`, `μ_1>=1/2-2E`, and `μ_0<=2E`. Now

```text
μ=(1/2)e_2+(1/2)ν,
ν_1>=1-4E,
ν_0<=4E,
U_2(2)=1+ν_0-ν_1.
```

Owner `2`'s better date-1 endpoint similarly gives the complete root gain
`(1/4)|ν_0-ν_1|>=1/4-2E`. This proves the final case. QED.

In fact the maximum gain of the finitely many date-0/date-1 endpoint
modifications used in this proof is already at least `1/12`: repeat the
same inequalities with that maximum in place of E. Thus the lower bound
has a concrete finite-prefix deviation witness.

The argument uses no supremum attainment and no cap truncation. Although
only a few simple deviations certify the lower bound, `E` always denotes
the full unrestricted cap, including arbitrary finite quit times and Never.
The whole tail enters only through its exact absorption distribution.

## 4. The same roots with fresh iid public ownership form an exact public NE

Before each live date, draw an independent uniform signal `J∈{0,1,2}`,
seen by all players. Only owner `J` quits with probability `1/2`.
The continuation before the next fresh signal has payoff vector
`v=(1,1,1)`: each date absorbs with probability `1/2`, and the absorbing
owner is uniform.

After observing `J=j`, the selected player has Quit value `1` and Continue
value `v_j=1`; hence its half-action is optimal. An outsider `i≠j` has

```text
Quit value     = 1/2,
Continue value = (1/2)r_i({j})+(1/2)v_i,
```

which is `1/2` or `3/2`. Thus its prescribed Continue action is optimal.

These endpoint comparisons verify the **full** public cap, not merely
one-step stationarity. Under any deviating strategy, at each still-live
date the owner is another player with probability `2/3`, and that opponent
quits with probability `1/2`. Hence live survival under every deviation is
at most `(2/3)^H` through `H` dates. The displayed Bellman inequalities
give the finite telescoping bound with continuation certificate `1`;
the bounded residual vanishes as `H→∞`. All adapted behavioral deviations,
including those using the complete public-signal history and Never, have
value at most `1` before the signal. Therefore the public profile is an
exact terminal Nash equilibrium in the public extension.

Freezing any entire signal sequence returns a word from Proposition 1.
Therefore no objective or selector over those frozen words can yield
vanishing exploitability, despite an exact equilibrium before freezing.

This does not contradict bounded-depth target-free removal of finite
public lotteries: the construction uses infinitely many fresh draws,
and that removal is not required to retain the same root alphabet.

## 5. A legal joint private replacement reaches the same target

At every date let all three active players independently quit with one
common stationary probability `x`, where `0<x<1`. Let player `3`, if
present, Never quit. This is an actual independent private profile, not a
public correlated mixture. Its per-date singleton mass is `x(1-x)^2` for
each active player, and its absorption probability is `1-(1-x)^3`.
Thus each active prescribed payoff is

```text
U(x) = 3x(1-x)^2 / [1-(1-x)^3]
     = 3(1-x)^2 / (3-3x+x^2).                      (5.1)
```

Fix an active recipient. Its two opponents have stationary joint survival
`a=(1-x)^2`. The immediate sure-Quit value and Never value are respectively

```text
Q(x) = a,
N(x) = 2x(1-x)/(1-a) = 2(1-x)/(2-x).
```

Quitting at date `k` has value

```text
N(x)(1-a^k)+a^k Q(x).
```

The difference

```text
N(x)-Q(x) = x(1-x)(3-x)/(2-x) > 0
```

shows every finite pure quit-time payoff is at most Never's. Against these
fixed private opponents, arbitrary behavioral stopping is a mixture of
finite pure times and Never, or equivalently obeys the checked pure-time
extremality theorem cited below. Consequently the unrestricted cap is
exactly `B(x)=N(x)`, attained by Never. There is no missing late-date cap.

The full exploitability is therefore exactly

```text
E(x) = N(x)-U(x)
     = x(1-x)(3-x) / [(2-x)(3-3x+x^2)].             (5.2)
```

For example `x=1/2` gives `U=3/7`, `B=2/3`, `E=5/21`; `x=1/4` gives
`U=27/37`, `B=6/7`, `E=33/259`. As `x↓0`,

```text
U(x)→1,       B(x)→1,       E(x)→0.
```

Thus `x_m=1/(m+2)` is an explicit actual-private terminal approximate Nash
family tending to `(1,1,1)`, or `(1,1,1,0)` after the stated Fin4 padding.
The standard terminal-to-uniform payoff bridge gives that same fixed
uniform-equilibrium payoff. No new general game class is proved here:
this symmetric small-hazard calculation is a homogeneous singleton balance,
and even the profile where all three active players quit surely is an
exact zero-payoff equilibrium in this nonnegative collision-zero table.
The point is the failure and repair of the *specified operation*, not
existence for this already easy table.

## 6. Persistent public state defeats diffuse marginal rebalancing

This is a separate two-player table, not the three-player cyclic table:

```text
r({0})=(1,2),       r({1})=(2,1),
r({0,1})=(0,0),    Never=(0,0).
```

For an explicit Fin4 version add Never players `2,3`, give them reward zero
in every coalition, and define active rewards from
`A=S∩{0,1}`: the displayed row when A is a singleton, zero otherwise.
The **specified public and private example profiles**, with those players
prescribed Never, have two trailing zero coordinates and the same active
unilateral caps. Proposition 2's universal target exclusion is asserted
only for the two-player game. Arbitrary profiles in the padded four-player
game may use the zero-payoff players as random deadlines, so the two-clock
cap formula must not silently be applied to all padded profiles.

At the initial date reveal a fair public bit `J`. Retain it forever as
public state. At every live date only player `J` quits, with probability
`h∈(0,1)`; the other player Never quits. Conditional on either branch,
the owner gets `1` and its opponent gets `2`. The owner cannot get more
than `1` against an opponent who Never quits. The outsider cannot get
more than `2`, and Never attains `2` because the owner eventually quits
almost surely. Thus each branch, and the observed public mixture, is a
full exact terminal Nash equilibrium. The initial public payoff is
`v=(3/2,3/2)`. The conditional total quit hazard is identically `h`,
so this public equilibrium is arbitrarily diffuse as `h↓0`.

If the persistent public state is incorrectly forgotten and its marginals
are independently resampled every date, both private players have hazard
`x=h/2`. Their prescribed payoff and complete cap are

```text
U_i(x)=3(1-x)/(2-x),
B_i(x)=2, attained by Never,
E(x)=(1+x)/(2-x) -> 1/2.
```

Thus the prescribed payoffs tend to the correct public target, but the full
caps do not. This is not the expected-only large-hazard obstruction:
the pointwise conditional total hazard tends to zero here.

The failure is stronger than failure of one averaging formula.

**Proposition 2.** For every actual private profile in this two-player
table, put `κ=max_i |U_i-3/2|`. Its full exploitability obeys

```text
E >= 1/2-κ-sqrt(2κ/3).                              (6.1)
```

In particular `(3/2,3/2)` is not a private uniform-equilibrium payoff,
despite being exactly attainable as an ordinary prescribed payoff and as
an exact public-equilibrium payoff.

**Proof.** Represent the two prescribed private strategies by independent
stopping clocks `X,Y∈ℕ∪{∞}`. Write

```text
p=P(X<∞),       q=P(Y<∞),
A=P(X<Y),      C=P(Y<X),
T=P(X=Y<∞),    N=P(X=Y=∞)=(1-p)(1-q).
```

The terminal payoffs are `U_0=A+2C`, `U_1=2A+C`, so

```text
U_0+U_1=3(A+C)=3(1-N-T).                            (6.2)
```

Against the fixed clock `Y`, quitting at deterministic finite date `k`
has payoff

```text
2P(Y<k)+P(Y>k)=1+P(Y<k)-P(Y=k) <= 1+q.
```

These payoffs tend to `1+q` as `k→∞`, since the atom at date `k` tends
to zero. Never pays `2q<=1+q`. Pure-time extremality therefore gives the
exact complete caps, with no assumption that a finite best date exists:

```text
B_0=1+q,       B_1=1+p.                            (6.3)
```

As an additional exact consistency check,

```text
D_0+D_1=2N+pq+3T >= 0.                            (6.4)
```

Equation (6.2) and the payoff lower bounds imply `N+T<=2κ/3`, hence
`(1-p)(1-q)<=2κ/3`. At least one of `p,q` is therefore at least
`1-sqrt(2κ/3)`. Equation (6.3) gives some player cap at least
`2-sqrt(2κ/3)`, whereas that player's prescribed payoff is at most
`3/2+κ`. Subtraction proves (6.1).

Were `v` a private uniform-equilibrium payoff, the inspected terminal-target
acceptance theorem would provide private terminal approximate Nash profiles
with both `E→0` and `κ→0`, contradicting (6.1). This uses the actual
uniform-payoff notion, not just absence of a stationary exact equilibrium.
QED.

The lower bound `E>=1/2` at exact payoff `v` is sharp. At date `0` let
player `0` quit with probability `1/2` and player `1` Continue. After
survival, at date `1` let player `1` quit surely and player `0` Continue.
This private two-date profile has `A=C=1/2`, `(p,q)=(1/2,1)`,
`U=v`, `B=(2,3/2)`, and `E=1/2`.

Consequently this target obstruction is not a nonconvexity-of-payoff-laws
argument: the desired payoff is already in the actual prescribed-payoff
set. What is lost by forgetting the persistent bit is the joint
prescribed-payoff/full-cap geometry. In a branch where a player owns the
only clock, its refusal produces Never and payoff zero; after marginal
mixing, that player's opponent acquires a positive quit rate, and Never
then yields payoff two.

This does not obstruct target-free selection: the two genuine exact
private equilibrium targets `(1,2)` and `(2,1)` already exist. Nor does it
falsify a theorem restricted to diffuse *no-memory* public roots, or a
disjunction in which solved games are removed before a diffuse source is
requested. Its role is to retain the memory hypothesis in such a theorem.

## 7. What objective selection can and cannot change

### Stationary iid diffuse source selection returns to the homogeneous lane

The following is a concise **ordinary proof/overlap check**, not a new
equilibrium producer. It explains what the positive iid-root averaging
operation can obtain before calendar variation or retained public state
is introduced.

**Proposition 3.** Fix any nonempty finite player set and one bounded
quitting table with original Never payoff zero. For each m, suppose a public
profile uses fresh iid signals and stationary conditional roots
`q_i^m(ω)` depending only on the current signal. Suppose

```text
sum_i q_i^m(ω)<=δ_m almost surely,
δ_m→0,
E_public(m)<=ε_m→0.
```

Put `d_i=r_i({i})`, and define the zero-diagonal singleton comparison
matrix by `M_ij=r_i({j})-d_i`. Then either all `d_i<=0`, in which case
all-Continue is already an exact ordinary equilibrium with payoff zero,
or there exists a simplex vector w satisfying

```text
Mw>=0,       w_i(Mw)_i=0 for every i.              (7.1)
```

Thus a diffuse stationary iid source does not bypass the known homogeneous
singleton LCP obstruction.

**Proof.** Let `λ_i^m=E q_i^m` and `Λ_m=sum_i λ_i^m`.
If `Λ_m=0`, all roots Continue almost surely, prescribed payoff is zero,
and immediate Quit yields `d_i`. If this happens infinitely often, the
vanishing debt bound forces `d_i<=0` for all i. More generally, if any
`d_i>0`, then `Λ_m>0` eventually. Work on that tail, discard finitely many
indices so `δ_m<1`, and take a subsequence on which

```text
w_i^m=λ_i^m/Λ_m -> w_i.
```

The simplex is compact. Compare each one-stage public coalition law to the
categorical law with singleton masses `λ_i^m`. Their total-variation error
is at most `δ_m Λ_m`. The first-categorical-Quit coupling from Turing's
Section 9 therefore shows that prescribed terminal payoffs converge to

```text
v_i=sum_j w_j r_i({j}).
```

Positive `Λ_m` ensures almost-sure absorption within each stationary
profile; no uniform lower bound on `Λ_m` is needed. Immediate sure Quit
has payoff approaching `d_i`, since the probability of any simultaneous
opponent Quit is at most `δ_m`. Hence the full debt bound gives `v_i>=d_i`.

If `0<w_i<1`, opponents have positive total rate eventually. The same
relative categorical coupling applied to the opponents alone shows that
the player's Never deviation has limiting payoff

```text
[sum_{j!=i} w_j r_i({j})]/(1-w_i)
  = (v_i-w_i d_i)/(1-w_i).
```

Since this complete deviation is bounded by the prescribed payoff plus
`ε_m`, its limit is at most `v_i`. Rearrangement yields
`w_i(v_i-d_i)<=0`. Together with `v_i>=d_i`, equality follows.
When `w_i=0`, complementarity is automatic. When `w_i=1`, the singleton
mixture formula itself gives `v_i=d_i`, so complementarity again holds;
no division by `1-w_i` and no nonvertex theorem is used in this case.
Finally `(Mw)_i=v_i-d_i`, proving (7.1). QED.

Here subtracting `d_i` is only the algebra defining the comparison matrix.
It does not change the game's canonical Never payoff to zero a second time:
if the entire payoff table were translated by `-d`, its Never payoff would
be `-d`. All strategic calculations above remain in the original
zero-Never game.

The matrix is the inspected `normalizedSoloMatrix` from
`Classification/LCP/Normalization.lean`. Existing
`isQuittingStationaryUniformEquilibriumPayoff_of_nonvertexHomogeneousWitness`
in `Classification/LCP/HomogeneousProducer.lean` already produces the
nonvertex homogeneous case. This citation makes no producer assertion for
vertices, which are treated separately in the project. Proposition 3 is
only necessity for this source class; it is not an iff classification.
Exogenous calendar-varying no-memory roots are not covered by this compact
stationary-weight argument.

### Consequence for objective changes

The frozen-word gap is independent of objective regularity or how much
global information a selector sees. For every output in that class,
the complete cap test fails by at least `1/12`; an optimal selector cannot
select a point outside its permitted class. Replacing sum-debt by a norm,
nonlinear penalty, Pareto order, or lexicographic rule cannot by itself
repair that missing operation.

The private replacement changes the contemporaneous action law and the
hazard scale. It is not merely a different supported minimum of the old
attainable set. It also illustrates why freezing a public seed is an
unnecessarily narrow notion of derandomization: an honest private profile
need not reuse its realized calendar or its positive-hazard alphabet.

This does **not** prove that objectives are irrelevant once arbitrary roots
and words are admitted. In particular, the present class is not universally
prefix-invariant, and it is not the full semantic carrier. No positive
`HasTerminalExploitabilityGap` statement for unrestricted profiles follows.

## 8. A whole-tree obstruction to selection with unchanged roots

This is an **ordinary proof**, not a counterexample to unrestricted
independent equilibrium existence or to unrestricted-root recovery. It
answers a narrower, concrete accounting question: could the repeated
child-selection/keep-prefix/drop-prefix extraction have a loss depending
only on the player count, rather than the number of public draws, while
never introducing new roots?

Return to the cyclic three-player table of Section 2. Let A be the three
roots in which a single designated owner quits with probability `1/2`.
Let F be the semantic pairs of **finite A-words followed by Never**.
This family is prefix-closed under A, not under all independent roots.
The leaf is actual Never, whose prescribed payoff is zero and whose
unrestricted cap is `(1,1,1)`, not the fictitious zero-cap pair.

**Proposition 4.** Every profile in F has full exploitability at least
`1/48`. Nevertheless, for every positive integer H there is a public tree
with H successive observed owner draws, only roots from A, and leaf Never,
whose full public exploitability is exactly `2^{-H}`.

**Proof of the private lower bound.** Let a word have length H. For H=0,
Never has cap 1 and exploitability 1. If `1<=H<=5`, keep the prescribed
prefix through date `H-2`; at the last owner date replace the owner's
half-action by sure Quit. The conditional prescribed owner payoff at that
last root is `1/2`, since the continuation is Never, while sure Quit pays
1. The complete root gain is therefore

```text
2^{-(H-1)}(1/2)=2^{-H}>=1/32.
```

For `H>=6`, append any infinite A-word after the finite word, instead of
Never. Proposition 1 gives a complete deviation with gain at least `1/12`
in the extended profile. Inspecting that proof, the chosen deviation
changes **only one action at date 0 or 1** to sure Quit or sure Continue,
then resumes the prescribed tail. Changing a half-action to Continue
increases survival through date H by a factor of at most 2; changing it
to Quit cannot increase that survival. Hence the deviation reaches the
appended tail with probability at most `2^{1-H}`.

All rewards are in `[0,2]`. Replacing the appended continuation by Never
therefore lowers this deviation's payoff by at most `2*2^{1-H}`. The
prescribed payoff also only decreases, so its decrease cannot reduce the
certified gain. The same complete deviation in the finite word gives

```text
E >= 1/12-4*2^{-H} >= 1/12-1/16 = 1/48.
```

This lower bound uses only legal complete unilateral replacements.

**Proof of the public upper bound.** At each of the H live dates draw a
fresh uniform public owner and apply its root in A. After survival through
all H dates, everyone Never quits. Prescribed payoffs obey

```text
u_0=0,       u_{k+1}=1/2+(1/2)u_k,
```

so all coordinates are `u_H=1-2^{-H}`. The tail Never has full cap 1.
If the continuation cap vector is `(1,1,1)`, the cap after observing an
owner draw is 1 for that owner, `1/2` for the outsider receiving 0 from
the owner, and `3/2` for the outsider receiving 2. Indeed the owner compares
sure Quit 1 with Continue 1; an outsider compares Quit `1/2` with Continue
`(1/2)r_i({owner})+(1/2)*1`. Averaging over the observed owner draw gives
full cap 1 again. Backward induction therefore gives `B_i=1` exactly at
the initial node for every finite H. The induction includes the full
tail cap, so it does not omit late deadlines or Never.

An explicit complete response attains the lower bound 1: Continue through
all H draw dates, then Quit surely. At each earlier date, opponent
absorption has probability `1/3` and conditional mean reward 1 to the
deviator; survival to the final sure Quit also pays 1. Thus this response
has value 1, matching the Bellman upper bound.

Consequently `E_public=1-u_H=2^{-H}`. QED.

Every extraction that merely selects children and keeps or drops existing
prefixes outputs a finite word over A followed by Never, hence remains in
F. No function `g(x)→0` can satisfy `inf_F E<=g(E_public)` for all these
trees, even with three fixed players. A global debt ledger proving such a
bound cannot rely solely on the same local survival identities and these
restricted extraction operations: those identities hold in this example.
Fixed player count therefore does not bound extraction loss in this
restricted model; no finite-rank claim is being inferred from it.

The missing hypothesis must be stated honestly. F is **not** closed under
all legal independent roots. In this same table, the root where all three
players quit surely is an exact zero-payoff equilibrium. Introducing that
new joint root escapes F immediately. Hence Proposition 4 does not refute
a conjecture-level uniform recovery that may synthesize arbitrary new
roots from the whole public tree; it shows why such a theorem requires
that additional mathematical operation, rather than a better accumulated
constant for existing branch selection.

The lower-bound proof is analytic. A preliminary exact rational enumeration
of words of lengths 0 through 7 agreed with the bound, but no enumeration
is needed or used as proof.

## 9. Bounded independent check of the neighboring convex-tree mechanism

The separately owned review
[`CODEX_TURING_BOX__STATE_INFORMATION_AND_RELAXATION__BY_CODEX_EMMY_BOX.md`](../feedback/CODEX_TURING_BOX__STATE_INFORMATION_AND_RELAXATION__BY_CODEX_EMMY_BOX.md)
checks the primitive prefix formula, constituent choice, zero-survival
case, and recursive signal interpretation of Turing's finite-depth result.
That is a review of its ordinary draft, not a source producer or an export
gate. Its depth-dependent modulus does not imply a uniform-depth recovery.

Turing's subsequently proposed iid one-owner averaging mechanism is a
different possible honest replacement for seed freezing; its status and
proof belong in that author's notebook. The present exact example is a
test case, not an obstruction to such averaging.

## 10. Declaration and source ledger

The prerequisite project documents were read before this work:
root and math `AGENTS.md`, `SOURCES.md`, `GOAL.md`, both research methods,
conference filenames, and bounded `docs/FRONTIER.md` routes.

The following actual Lean declarations and their immediate definitions were
inspected; none formalizes the new frozen-word proposition above.

- `quittingUniformEquilibriumPayoffConjecture` in
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean` fixes the target notion.
- `HasTerminalExploitabilityGap` and
  `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean` distinguish
  a universal ordinary-profile gap from the restricted gap proved here.
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  is the target-free terminal-family existence bridge.
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in the
  same file retains the particular limiting target in Section 5, rather
  than merely asserting some uniform-equilibrium payoff exists.
- `exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff`
  in that same file gives the converse target-acceptance necessity used
  in Proposition 2.
- `quittingTerminalSemanticPair`, `quittingTerminalSemanticPrefix`,
  `quittingTerminalSemanticDebt`, and
  `quittingTerminalSemanticDebt_prefix_le` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean` identify actual
  prescribed payoffs and unrestricted caps under legal private roots.
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` and
  `exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`
  justify using all deterministic dates and Never to compute the full
  ordinary behavioral cap against fixed opponents.
- `quittingHazardStoppingLaw` and `quittingBehaviorStoppingLaw` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean` give the
  independent-private-clock representation.
- `quittingTerminalOutcomeMass_stationary_some_eq_conditionalCoalitionMass`
  in `UniformEquilibrium/Quitting/Stationary/TerminalCoalitionLaw.lean`
  agrees with the stationary first-absorption computation in Section 5.
- `exists_recipientScale_all_minimum_debts_eq` in
  `UniformEquilibrium/Quitting/Terminal/RecipientScaledTerminalSemantics.lean`
  is existing positive-weight selection: weights do not supply a new
  common-debt theorem here.

Additional bounded mechanism inspections included
`Root/CapNashRootStack.lean`, `ControllerTester/FunctionBarrierDuality.lean`,
`Root/StrictAllContinueBasinLinearAbsorptionDefect.lean`,
`Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`, and the
three-player admissible-cycle example. Existing conference notes were read
only in the selected objective, source-menu, convex-tree, and single-owner
routes. No statement here is credited to an unreviewed conference example.
There is no new literature-derived theorem in this note.

For the overlap check in Proposition 3, the exact own-singleton translation
and matrix definitions were additionally read in
`Classification/LCP/Normalization.lean`, the homogeneous predicate in
`Classification/LCP/MatrixClasses.lean`, and the existing nonvertex producer
in `Classification/LCP/HomogeneousProducer.lean`. These do not formalize the
new necessity argument here.

## 11. Decision and concrete remaining question

- **Suspected artificial restriction:** a global objective must choose one
  frozen owner sequence using an unchanged fixed positive-hazard alphabet.
- **Concrete alternative tested:** legal simultaneous stationary independent
  private hazards, with their common scale selected together with the joint
  root; exact full caps include Never.
- **Strongest proved consequence:** the two strategy classes have respectively
  a uniform `1/12` restricted gap and an explicit vanishing-gap family at
  the same limiting target in one exact finite table. This is ordinary
  mathematics with a bounded independent check, not a new table-class theorem.
  In the separate persistent-state table, the exact public target is
  privately payoff-attainable but excluded from private uniform payoffs by
  the full-profile inequality (6.1), also bounded independently checked in
  its stated two-player scope.
  Proposition 3 additionally shows, as a bounded independently checked
  overlap argument,
  why stationary iid diffuse source selection returns to the homogeneous
  singleton LCP lane instead of bypassing the residual obstruction.
  Proposition 4 gives a further bounded independently checked obstruction
  to a depth-uniform whole-tree bound for extraction that preserves the
  root alphabet: honest H-draw public trees have debt `2^{-H}`, whereas all
  outputs of the specified child/prefix extraction have debt at least `1/48`.
- **Exact remaining gap:** no general-game operation has been produced that
  transforms a globally useful relaxed/public point into private roots with
  simultaneous upper control of all caps. The iid stationary case is not a
  macrostate-dependent public construction.
- **Whether to change the main effort:** stop spending effort on objective
  variants whose only outputs are frozen fixed-alphabet owner words. This
  example alone does not justify abandoning scalar objectives over the full
  honest carrier. Prior one-active impossibility results make a genuine
  multi-active/legal-root mechanism essential in any universal compiler.

**Next concrete question:** can a solved-game-or-diffuse-no-memory producer
avoid both the persistent-state obstruction here and the known residual
class, without merely rephrasing existence of honest private equilibria?
Both exact propositions and the full-cap calculations have passed the
bounded review linked above. No export or formalization is requested.
Proposition 3's short necessity argument, including zero-rate and vertex
cases, and Proposition 4's finite-tree/full-cap calculation and restricted
scope also passed the same bounded review. A whole-tree account now needs
an actual operation synthesizing new joint roots; an improved accumulated
bound for the tested child/prefix selection cannot suffice.

## 12. A complete far-odds account collapses to a persistent base

Status: ORDINARY PROOF, not independently reviewed or Lean checked. This
is a direction-changing overlap result, not a new UE producer.

### 12.1 Self-contained question and exact complete field

Fix ANY finite quitting table on n>=2 players, with zero live/Never rewards,
private independent clocks and unrestricted complete unilateral deviations.
No sign, normality or matrix hypothesis is imposed. Can coercivity of a
single nonnegative weighted sum of the ACTUAL stationary endpoint field
give a new global stationary-existence mechanism?

For nonnegative odds x_i=q_i/(1-q_i), define finite polynomials

    D_i(x)=product_(j!=i)(1+x_j),
    a_i(x)=sum_(T subset I\{i}) r_i(T union{i})*product_(j in T)x_j,
    b_i(x)=sum_(nonempty T subset I\{i}) r_i(T)*product_(j in T)x_j,
    F_i(x)=D_i(x)*[a_i(x)-b_i(x)]-a_i(x).

These are defined on the whole closed nonnegative orthant. With the actual
stationary alpha_i=1/D_i, Q_i=a_i/D_i and B_i=b_i/D_i, one has EXACTLY

    F_i=D_i^2*[(1-alpha_i)*Q_i-B_i].                (12.1)

Thus this is the self-consistent stationary endpoint field, not a prescribed
continuation annotation. No terminal law or cap is averaged or convexified.

Assume there is w>=0, w!=0 such that

    sum_i w_i*F_i(x) -> +infinity
        as ||x||_infinity -> infinity through x>=0.  (12.2)

For example, a common positive quadratic lower bound outside a compact set
would imply(12.2). Let A={i:w_i>0}.

### 12.2 Exact consequence: all completions are leave-safe on A

**Proposition.** Condition(12.2) forces |A|>=2 and, for every i in A and
every U subset I\A,

    r_i((A\{i}) union U) <= r_i(A union U).         (12.3)

In particular the table is already covered by the tracked persistent-base
arbitrary-completion producer.

**Proof.** If A={i}, take x_i=t and every other coordinate0. Since F_i
does not depend on its own odds, F_i=0 along this unbounded ray, contradicting
(12.2). Hence A has at least two labels.

Fix i in A and U outside A. Put T=(A\{i}) union U; it is nonempty. Set
x_j=t for j in T and x_j=0 otherwise. The polynomials a_i,b_i on this ray
have degree at most |T|, with top coefficients r_i(T union{i}) and r_i(T).
Also D_i=(1+t)^|T|. Therefore

    F_i(x(t))=[r_i(T union{i})-r_i(T)]*t^(2|T|)
                                      +O(t^(2|T|-1)).

Every other positive-weight recipient j is in T. Its own odds never enters
F_j, so on the SAME ray its degree is at most2(|T|-1). Recipients outside A
have weight0. If the bracket above were negative, the weighted sum would
tend to-minus infinity, contradicting(12.2). It must be nonnegative. This
is exactly(12.3), with no strictness inferred at a zero leading coefficient.

The argument uses an actual boundary support and its leading monomial,
not finite-player label stabilization, a first-order condition, or a
convexity claim about independent laws. This proves the proposition.

### 12.3 Existing full-agency consumer and the failed novelty implication

Condition(12.3) is precisely
`QuittingPersistentBaseComplementLeaveSafe reward A`, defined in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseArbitraryCompletionEscape.lean`.
In that file,
`exists_quittingPersistentBaseCertificate_of_complementLeaveSafe` selects
an actual independent mixed Nash point for ALL complementary players,
and `exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe`
extends it to an exact stationary terminal Nash against every complete
behavioral deviation and a same-profile uniform payoff. These declarations,
their leave-safe definition and their finite-game selection were reopened.
No supplied strategic witness or restriction on complementary rewards is
an input.

Concretely all players of A quit surely at date0. At every realized
complementary coalition U, each base player weakly prefers to stay by(12.3).
The complementary players use the selected finite simultaneous-game Nash.
Because |A|>=2, even after any one player deviates a sure opponent remains;
absorption occurs at date0. Every full behavioral replacement therefore
reduces to its initial mixed action, and the same comparison holds for
every finite-average horizon. This verifies the complete-agency conclusion
without invoking any asymptotic odds or restricted stationary test.

The ordinary odds expansion is consistent with
`quittingRootCoalitionMass_eq_continueMass_mul_prod_odds` in
`UniformEquilibrium/Quitting/Root/InteriorCoalitionOdds.lean`, which was also
read; that declaration does not itself establish the new implication(12.3).

Consequently a positive weighted coercivity certificate for the COMPLETE
stationary odds field is not a way to escape all sure-base source classes:
it logically forces one of them. This does NOT apply to a small-hazard
scaled leading field whose coercivity is used only to bound an intermediate
annulus. Its higher-order actual odds coefficients may have negative far
faces, so(12.2) can fail even when a finite-annulus degree defect produces
an actual equilibrium. A useful global selector must control an appropriate
finite region or use another legal operation; imposing full far-odds
coercivity would unnecessarily return to the solved persistent-base lane.

Current next question: can an actual finite-annulus selection or a joint-law
operation give full cap control without presupposing either an absorbing
sure base or a designated large-reward scaling of the input table?

## 13. Fast public regeneration admits an honest private replacement

Status: COMPLETE ORDINARY PROOF DRAFT, unreviewed and not Lean checked.
This is a new legal joint-clock operation, not an arbitrary-game producer
or a new raw-table UE class. Unlike the iid operation, it allows retained
public Markov memory. Its source premise is substantive: regeneration must
be fast relative to the pointwise conditional quit hazard. No general
sunspot existence theorem is claimed to supply that premise.

### 13.1 Self-contained statement and information

Fix a finite quitting game with |r_i(S)|<=R, zero live and Never payoff,
and independent private randomization. Let Omega be a finite public-state
set. Choose a probability mu, a mu-invariant transition matrix K, and
0<kappa<=1. The EXOGENOUS public state evolves by

    P(x,y)=(1-kappa)*K(x,y)+kappa*mu(y).                  (13.1)

The initial law nu may be arbitrary. At each live date every player sees
the current state x. Conditional on x, player i independently Quits with
probability q_i(x), using fresh private randomness. Subsequent state
transitions follow P independently of those private coins. The public
deviator may use the ENTIRE observed public-state history and arbitrary
private randomization; changing one's actions does not change P.

Assume the POINTWISE bound

    sum_i q_i(x)<=delta<=kappa/4      for every x.         (13.2)

Define lambda_i=sum_x mu(x)*q_i(x). Replace the entire public protocol by
actual PRIVATE INDEPENDENT stationary clocks with hazards lambda_i; a zero
hazard means Never. No public state, seed, signal or shared randomization
is retained in the replacement.

For every player the prescribed terminal payoffs and complete caps satisfy

    |U_i(private)-U_i(public)| <=20R*delta/kappa,
    B_i(private) <= B_i(public)+20R*delta/kappa.           (13.3)

Here the public cap permits all signal-informed deviations, and the private
cap permits every complete independent behavioral replacement, including
all finite deadlines and Never. Thus

    E(private)<=E(public)+40R*delta/kappa.                (13.4)

For initial law nu=mu the constants20 and40 improve to16 and32 by the
same proof. Constants are not the purpose of the result.

More fundamentally, for EVERY subset J of players, the public and private
FIRST STOPPED CLOCK/COALITION laws can be coupled to agree with probability
at least1-10delta/kappa. The stopped outcome includes the absolute date,
the entire simultaneous coalition, and literal Never. This holds uniformly
even if the total averaged hazard of J is arbitrarily tiny. It is the
relative-error statement needed when J is an opponent-deleted set.

### 13.2 Regeneration blocks and a signed one-mark comparison

First take initial law mu. Realize(13.1) by independent reset coins after
each date. Between two resets, the block length N has geometric law on
{1,2,...} with parameter kappa. The block starts at mu; within it the state
uses K. N is independent of the within-block K trajectory and private coins.
Because mu K=mu, EVERY state marginal inside a block conditional on N=n
is mu. Blocks, including their lengths and whole trajectories, are iid.
Attach iid blocks of exactly the same geometric lengths to the private
stationary profile; this is only a coupling device, not its strategy.

Fix ANY J, and put L=sum_(j in J)lambda_j<=delta. Conditional on N=n,
draw all potential coins through all n dates even if an earlier coin would
have stopped play. Let V count all such potential Quit marks. In either
system EV=nL. A block's actual first-stop outcome is either no stop or
(k,S), where1<=k<=n and nonempty S subset J.

Introduce the common finite SIGNED measure rho_n with total mass1:

    rho_n(no stop)=1-nL,
    rho_n(k,{j})=lambda_j for every k,j,
    rho_n(k,S)=0 when |S|>=2.                            (13.5)

It need not be a probability measure when nL>1; the proof never couples
to it or treats its negative mass as a probability. It is only used in
the triangle inequality for the half-l1 norm of finite signed measures.

For either actual block law p_n, its no-stop mass is at least1-nL by the
union bound, and each first-singleton mass is at most lambda_j by its
unconditional one-date marginal. Thus

    (1/2)||p_n-rho_n||_1
        =nL-Pr(first stop is a singleton)
        =E[V-1_{first stop singleton}]
        <=E[V(V-1)] <=n^2*delta*L.                     (13.6)

The first inequality is POINTWISE: V=0 or1 gives zero; when V>=2, both
V-1 and V are bounded by V(V-1). The last inequality sums ordered pairs
of distinct potential marks. At a common date their conditional product
sum is at most(sum_J q)^2<=delta*sum_J q. At different dates, conditional
independence of the private coins gives E[h(X_s)h(X_t)]<=delta*E h(X_s),
where h=sum_J q. Each expectation E h is L. The same bound holds in the
private product system with h=L. This step uses no mixing estimate or
positive lower bound on L.

The common signed measure and triangle inequality therefore give the
actual probability-law comparison

    TV(p_n,p'_n)<=2*n^2*delta*L.                         (13.7)

Its validity for LONG blocks with nL>1 is important: no geometric-block
tail is discarded at an error independent of the rare opponent rate.

### 13.3 Couple until actual absorption, without dividing by a rare rate

Given each shared N, maximally couple the two finite first-stop block
laws. Repeated blocks give iid coupled pairs. Write beta for the chance
that one block's first-stop outcomes differ and p00 for the chance that
both have no stop. Then

    beta<=2delta*L*E[N^2],
    E[N]=1/kappa,       E[N^2]=(2-kappa)/kappa^2.         (13.8)

The private chance a' of a stop within one block satisfies

    a'>=E[V]-E[V(V-1)]
       >=L/kappa-delta*L*(2-kappa)/kappa^2
       >=L/(2kappa).                                   (13.9)

The first inequality follows pointwise from1_{V>0}>=V-V(V-1).
If L>0, the probability of a mismatching block before any matched stop is
at most

    beta/(1-p00) <=beta/a' <=8delta/kappa.               (13.10)

Indeed p00 is at most the private no-stop probability1-a'. Before that
first nonempty-or-mismatching block, both systems have continued through
identical absolute calendar lengths. A matched stopped block agrees in
its precise date and coalition. This proves the complete first-stop-law
coupling, not just a comparison of eventual recipient payoffs.

If L=0, stationarity and nonnegativity imply no player's potential mark
in J ever occurs almost surely; both first-stop laws are literal Never.
No division by L is made in that case. It also covers an empty J.

For arbitrary initial nu, couple the first geometric block length and
declare failure if either system stops before the first reset. Each
probability is at most delta E[N]=delta/kappa. If neither stops, the
following public block begins at mu and the stationary argument applies.
The total failure probability is at most10delta/kappa. The private future
remains independent stationary Bernoulli play after the reset; fake block
boundaries introduce no dependence into its marginal strategy law.

### 13.4 Every deadline, Never, and the semantic consumer

Apply the coupling with J=I to compare prescribed terminal rewards.
Agreement of terminal coalitions gives identical rewards, and every
disagreement costs at most2R. This proves the first line of(13.3).

For player i use J=I\{i}. Insert the SAME deterministic deadline h, or
Never, into both coupled opponent first-stop laws. If opponents stop
before h, at h, or after h, the completed coalition is respectively their
coalition, its union with{i}, or{i}. Literal Never is retained. Exact
agreement of the opponent stopped outcome therefore implies agreement
for EVERY inserted deadline simultaneously. The bound20Rdelta/kappa is
uniform over h and includes Never.

Every complete PRIVATE behavioral replacement is an independent mixture
of those deadlines and Never on the unique live history. The public cap
contains every deterministic deadline ignoring the public state. Taking
the supremum proves the second line of(13.3), then(13.4). Nothing attempts
to identify public informed replies with private replies.

Consequently, if ONE fixed raw game has such public profiles with

    epsilon_m=E(public_m)->0,
    delta_m/kappa_m->0,

the actual private profiles above have complete terminal debts tending
to0. The inspected declaration
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
then selects one fixed uniform-equilibrium payoff. This existence-level
consumer does not require pretending that every produced profile has a
uniform opponent geometric bound when a deleted set is all Never.

### 13.5 Exact boundaries and what is genuinely missing

For kappa=1 there is no retained public state after a date. This recovers
the iid operation in Section9 of
`CODEX_TURING_BOX__STATE_INFORMATION_AND_RELAXATION.md`, with weaker constants;
that proof was read for the comparison. Here kappa<1 permits genuine
state memory across arbitrarily many dates. A constant nonempty-coalition
reward table supplies a simple positive exact-public-Nash test with any
such public-state process and positive average opponent rates: all full
caps and prescribed payoffs are1, and the private replacement is also exact.

Fast regeneration cannot be deleted from this STOPPED-LAW/PAYOFF comparison.
For an exact family take two public states with mu=(1/2,1/2), K=Id,
kappa=delta^2, and at state0 let only player0 Quit with probability delta,
while at state1 only player1 Quits with probability delta/10. The initial
law is mu. Conditional on state j, absorption precedes the first reset
with probability h_j/[h_j+kappa-h_j*kappa]->1. Thus the eventual first
label tends to(1/2,1/2). The replacement has private hazards
(delta/2,delta/20), so its first-singleton label probabilities tend to
(10/11,1/11), with collision mass tending to0. A bounded indicator reward
for first label0 separates prescribed payoffs by9/22 in the limit.
This is NOT asserted to be an approximate public Nash family; it falsifies
only removal of the ratio hypothesis from the general law/payoff comparison.

The zero-regeneration persistent-bit exact public Nash and forbidden
private target in Section6 remain a separate full-cap boundary test.
Small EXPECTED total hazard cannot replace(13.2), even at kappa=1: rare
public all-sure grand-coalition draws produce the earlier iid simultaneous-
quitting counterexample. Both probability mode and regeneration matter.

A narrow search of the quitting Root/Stationary and Diagnostics subtrees
for Markov public roots, Doeblin reset and regeneration/hazard comparison
found no matching declaration. No exhaustive novelty claim is made. The
proof above is not a citation to an external mixing theorem.

What this changes: the iid/no-memory restriction is dispensable for an
actual full-agency replacement operation. What remains open is a genuine
PRODUCER from arbitrary game data (or from a fixed no-UE hypothesis) of
public approximate equilibria satisfying delta/kappa->0. Existing general
sunspot protocols have history-dependent macrostates; they must not be
assigned a uniform reset rate merely because fresh iid noise is present.
The next concrete test is source-level: whether a known public producer
has such a stationary Doeblin component after removing solved exits, or
whether its strategic memory necessarily evolves on the absorption scale.

### 13.6 Bounded application test against the actual kiloblock source

The primary source inspected is Solan--Solan, *Quitting Games and Linear
Complementarity Problems*, source file `sunspot9.tex` in the local source
archive, its construction of kiloblocks in Section3.3.5. It partitions play
into K+1 ordered kiloblocks, selects a type at block beginnings, retains
that type during a block of C_k dates, and prescribes perpetual Continue
in the final kiloblock. A fresh noise draw at every date does not reset
that retained type or counter.

The corresponding exact definitions read in
`Literature/SolanAndSolan2020.lean` are `KiloblockPhase`, `KiloblockMode`,
`precedingKiloblockPhase`, `phaseAfterAttempt`, `nextKiloblockMode`, and
`exists_kiloblockBlueprint`. The latter deliberately chooses each mesh
strictly greater than1 and guarantees a small within-attempt quit hazard.
The control state retains a deterministic remaining-date counter. There
is also a correction in that transcription: failed advance-type attempts
move to the next kiloblock, whereas failed restart-type attempts restart
the current one. The prose partition alone must not be used to replace
both by a common restart.

This literal source does NOT provide(13.1)–(13.2). At decision-date
resolution, a nonfinal state with remaining count at least2 goes to the
same type with a decremented count on survival; a remaining-count1 state
goes to a type-selection phase. Such disjoint next-state supports preclude
a common one-step reset law with positive kappa on those states. The
ordered macro-index and final Continue tail are additional retained state,
not noise that can be averaged independently. Deleting inactive draw
stages does not delete the within-attempt counter.

This is a failure of the PROPOSED DIRECT APPLICATION, not a proof that no
regrouping, different public producer or conditional extraction can ever
supply fast regeneration. Regrouping by a mesh length would replace the
per-date bound by a block absorption bound and would require a new complete
deadline/cap argument; one cannot simply use the old delta at that scale.
No new UE counterexample-class narrowing follows from the present review.

### 13.7 A global source obstruction, not just a missing adapter

There is a stronger reason NOT to propose fast regeneration as the universal
public source. Fix ANY raw table whose singleton comparison matrix Gamma
is R0 and with at least one strictly positive own singleton. There cannot
be a family of public profiles satisfying(13.1)–(13.2) for which BOTH

    E(public_m)->0,          delta_m/kappa_m->0.           (13.11)

This holds even if the finite public-state sets and every Markov parameter
vary with m. Indeed(13.4) would give actual PRIVATE stationary profiles with
full debts tending to0 and total hazards at most delta_m->0, because
kappa_m<=1. Apply Proposition3 to these profiles using a trivial one-point
signal. Its all-Continue alternative is excluded by the positive own
singleton, and its other alternative gives a nonzero homogeneous standard
LCP solution Gamma*w>=0, w_i(Gamma*w)_i=0 on the simplex. This contradicts
R0. The already independently checked Proposition3 treats vertex weights
and zero total hazards separately, so no improper division is hidden here.

Equivalently there exists a strictly positive, table-dependent lower bound
on E(public)+40Rdelta/kappa throughout this public source class: otherwise
a sequence approaching its zero infimum would satisfy(13.11). This is a
WHOLE-source obstruction, not one badly selected public-state branch.

For the paired-hard matrix in Section7 with own singletons1, R0 is already
known. Its own-private stationary profile from a large-reward construction
can exist at a small BUT FIXED hazard for each fixed table; this does not
contradict the obstruction as delta->0 at that SAME table. No game is
claimed to lack UE. The result instead identifies exactly why fast-mixing
diffuse public production cannot close the generic R0 residual regime.

Decision: retain13.1–13.4 as an honest operation, but retire its proposed
universal-source role. A public-memory route that reaches this regime must
retain strategic state on the absorption time scale or use a replacement
that is genuinely nonstationary/macroscopic, not stationary averaging.

## 14. The standard-Q regime already produces actual low-cap surplus seeds

Status: ordinary UNREVIEWED mathematical composition. The matrix
obstruction itself is already checked and is not claimed as new. The
purpose is to identify precisely which input of the successful cap-chamber
mechanism is still missing on general hard data.

### 14.1. Self-contained question and exact seed statement

Let I be any nonempty finite player set. Live and Never pay0. Let r_i(S)
be arbitrary finite terminal rewards, and assume only that all own
singletons s_i=r_i({i}) are nonnegative. Prescribed clocks are independent
complete private laws on Nat union{Never}; caps allow ALL unilateral
complete behavioral replacements. Define the singleton comparison matrix

    Gamma_ij=r_i({j})-s_i,       Gamma_ii=0.

Suppose Gamma is a textbook STANDARD-Q matrix: for every offset y, the
standard LCP w=y+Gamma*x>=0, x>=0, x_i*w_i=0 is solvable.
Fix ANY nonzero weight vector a>=0.

Claim. There is a literal actual pure-clock profile p_j (sole j Quit0,
all other players Never) whose full semantic pair(U,B) satisfies

    B_j=s_j,
    a dot(B-s)>0.

Either this profile is already exact terminal Nash, or for some lambda>0
it is an ACTUAL seed of the nonempty compact chamber

    { (U,B) in actual closed carrier:
          min_i(B_i-s_i)<=0,
          a dot(B-s)>=lambda*max_i(B_i-U_i) }.           (14.1)

No sign condition on passive or coalition rewards, cap-attainment
hypothesis, strategic witness, or supplied low-debt family is used.
The statement produces the seed only, not invariance of(14.1).

### 14.2. Exact proof and all response clocks

Apply standard-Q solvability to offset minus-ones. Its solution x>=0
satisfies Gamma*x>=ones. Hence

    sum_j x_j * [sum_i a_i Gamma_ij]
         = a dot(Gamma*x) >= sum_i a_i >0.

At least one column j has strictly positive weighted sum
C_j=sum_i a_i Gamma_ij>0. This uses only residual feasibility, not
complementarity of that LCP solution.

For sole j Quit0, the actual prescribed payoff is U_i=r_i({j}).
Owner j faces opponents who Never. Its finite response dates all pay
s_j and Never pays0, so B_j=s_j by own nonnegativity. For i!=j,
Quit0 pays r_i({i,j}), while every positive finite deadline and Never
pay r_i({j}). Thus the FULL cap is exactly

    B_i=max{r_i({j}),r_i({i,j})}           (i!=j).

Every complete private response is a mixture of these pure clocks,
so there is no hidden later cap. In particular

    a dot(B-s)>=sum_i a_i[r_i({j})-s_i]=C_j>0,
    D=max_(i!=j) [r_i({i,j})-r_i({j})]_+.

If D=0, all complete response gains vanish and the actual profile is
terminal Nash. If D>0, choose lambda=[a dot(B-s)]/D>0. The seed then
satisfies(14.1), with equality in its surplus inequality. The closed
actual carrier is compact for every fixed finite reward table, so the
chamber is compact and nonempty. It is not claimed convex.

### 14.3. Existing declarations and the remaining global problem

Definitions read: `quittingSingletonMatrix` in
`UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`,
and `StandardLCPSolution`, `IsStandardQMatrix` in
`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`.
The existing matrix theorem
`not_isStandardQ_of_forall_column_sum_nonpos` in
`MathUE/LinearProgramming/ColumnSumQ.lean` is the unweighted special case
of the simple column-sum argument. That file was read in full. The
weighted argument above follows directly from the same standard-Q
definition and does not claim a new linear-programming theorem.

This refines, rather than solves, the arbitrary-game route. On full
standard-Q residual data with nonnegative own singletons, the ACTUAL
low-cap/surplus seed is automatic. The missing global step is to find a
closed region that preserves this advantageous cap geometry while
admitting a nonzero legal root operation at every positive-debt point.
In the passive-triple family, exact cap-Nash root analysis supplies that
preservation and excludes full support by a cap-sum contradiction. No
analogous invariance follows merely from Gamma being standard Q.

In particular, this seed is NOT the unconstrained global debt minimum.
The latter's positive-debt cap floors do not supply(14.1)'s low-cap
condition. Starting from a real pure profile and constraining the domain
remains load-bearing; scalar reweighting of the old minimum does not
replace it. For proper normal cores the matrix hypothesis must be applied
to the ACTUAL retained game, with a separate legal lift if needed: this
section does not silently identify a proper-core seed with a full-game
seed.

Concrete next question: does full hard-residual data force a choice of
a>=0 and a CLOSED subset of(14.1), containing one of these produced
pure seeds, from whose every positive-debt point some nonzero cap-Nash
prefix remains inside? No such choice, universal invariance, or UE
conclusion is asserted here.
