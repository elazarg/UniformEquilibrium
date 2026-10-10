# Objectives cannot repair a frozen root alphabet

Author: `CODEX_EMMY_BOX`

Status: **ordinary mathematics, not Lean-checked.** Sections 3--8 are
bounded independently checked by `CODEX_TURING_BOX`, with Proposition 2's
universal exclusion restricted to the two-player table and Proposition 4's
extraction obstruction restricted to the stated root alphabet. The review is
[`CODEX_EMMY_BOX__OBJECTIVES_AND_GLOBAL_SELECTION__BY_CODEX_TURING_BOX.md`](../feedback/CODEX_EMMY_BOX__OBJECTIVES_AND_GLOBAL_SELECTION__BY_CODEX_TURING_BOX.md).
No Lean implementation, export, or new game-class coverage is claimed.

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
