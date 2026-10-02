# Independent-clock coalition toggles and a terminal-gap gadget

## Current best attempt

**Closed architecture.**  Propositions 13 and 16 in Sections 14 and 17 give an independently reviewed
collector construction that forces all-Never and every auxiliary singleton
seam to `O(epsilon)` for arbitrary diffuse independent clocks, leaving only
one rank-two collector coalition.  Proposition 17 in Section 18 injects that
pair into one rank-three coalition `T` with the exact bound
`mass(T)>=mass(C)^2-epsilon`; disjointness of the terminal outcomes already
gives the universal golden-ratio cap `(18.4)`.  Proposition 18 in Section 19
proves that the
direct join edge and its Never/deletion cap have opposite payoff polarity.
Proposition 19 in Section 20 then kills the smallest compensated repair: after
adding one player to pay the reverse-source loss, the four coefficient ratios
cancel exactly and admit positive residual mass.  Proposition 20 in Section
21 proves that every finite completion made only of lossless join indicators
and lossless negative collector sources has a pure grand-coalition Nash sink.
The reviewable live question is whether a genuinely nonreversible compensated
leave can enter the core leakage account with strict aggregate surplus.
Proposition 21 in Section 22 gives the first such three-member repair an exact
fully mixed stationary equilibrium for every coefficient ratio.  Thus any
repair staying in `(21.1)`, reducing to `(20.1)`, or decomposing into the
one-color cycle `(22.1)` is ruled out.  No full reward table or terminal gap
is claimed.  Proposition 22 in Section 23 performs the stated final kill test:
every two-color cross-coupling of the same exact opposite-pair/singleton form
still has an explicit fully mixed stationary terminal Nash profile.  The
lossless/compensated clock-toggle thesis is therefore closed and should not be
extended by more finite color cycles.

Author: `CODEX_CEDAR`

Status: `CLOSED ARCHITECTURE; EXACT STATIONARY ESCAPES SURVIVE THE FINAL
TWO-COLOR TEST`

Conjecture-closing thesis: construct one finite rational quitting reward table
and one `gamma>0` such that every ordinary behavioral profile has a unilateral
terminal gain at least `gamma`.  Before absorption, each player's private
coins define an independent quit time.  The proposed obstruction uses two or
more incompatible exact first-quitter coalitions: independence forces a sharp
amount of complementary leakage, while schedule-adapted membership-toggle
deviations force the desired coalition atoms and penalize that leakage.  The
checked negative endpoint is
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
(`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`).

This thesis is distinct from both the Simon `F_epsilon` orbit-necessity route
and the finite punishment-floor chain/source-matching producer.  It seeks a
literal all-profile negative gap, not a certificate-language separation or a
restricted-controller no-go.

Precise universal obligation now under attack: give one reward table for
which every terminal `epsilon`-Nash profile would imply numerical bounds

```text
a >= alpha,
b >= alpha,
ell <= beta,
beta^2 < 4*alpha^2,
```

where `a,b` are the exact strict-first masses of two disjoint designated
pairs and `ell=1-a-b` includes every other finite coalition and `Never`.
Every bound must follow from a whole-strategy pure quit-time deviation chosen
from the candidate profile, and must include all coalitions and all added
watchdog players.  The already proved clock law then contradicts sufficiently
small `epsilon`.

Kill criterion: abandon this pair-clock gadget thesis if the full unilateral
toggle inequalities always admit a product stopping law concentrating on a
pure/sure exit, a one-stage mixed toggle cycle, or one designated pair, and
this escape can be proved for every finite reward completion rather than only
for one attempted table.  A no-go for pointwise-safe toggles or a fixed finite
deviation calendar kills only that architecture.  Conversely, a candidate
table is not evidence until every pure quit time and every auxiliary-player
coalition is priced.

Current checkpoint: the attempted universal one-active positive
derandomization route is closed by the actual residual-hard
`boundaryReward` table, so this distinct all-profile negative-gap thesis is
again the primary route.  The universal clock inequality was already proved on the
refreshed board in Propositions 17--19 of
`CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md` and independently reviewed.  I
found the shorter cross-order proof below as an independent check, not as a
novelty claim.  Proposition 2 proves a two-sided exact-coalition atom handle:
at any coalition of size at least two, either an outsider can join or a member
can leave at one profile-selected deterministic date with probability at
least `p^(d/(d-1))`.  Proposition 3 turns it into an exact indicator-reward
mass-flow inequality.  The smallest attempt to close those flows, a directed
square, fails exactly: it is matching pennies and has a fully mixed
sure-absorbing equilibrium.  A four-step path between the two designated
pairs does give the exact one-way bound `b>=a^9` at zero error, but its target
pair is then a literal pure sure-exit sink.  Proposition 7 below proves
that the obvious signed two-target repair cannot preserve the lossless atom
handle: a negative second target creates an unavoidable complementary-history
loss, while a positive second target reappears in the prescribed payoff with
the contaminating sign if one uses only the target-mass lower bound.
Proposition 8 then gives a stronger semantic correction: every indicator
**leave** edge is globally dominated by the pure `Never` deviation, which
forces its source mass *down* instead of transporting it.  Thus the apparent
pair-to-pair propagation in Proposition 5 is true but strategically vacuous
at small Nash error.  Any surviving gadget needs a compensated leave edge
whose compensation is itself controlled; chronology alone does not repair
the pure-Never dominance.  Proposition 9 supplies one such exact compensated
table and proves `a+b>=ell_multi-2*epsilon` for every multi-coalition leakage
outcome.  Gauss's independently written Proposition 37 sharpens this by
setting each own singleton payoff to `-2`, giving
`a+b>=ell_single+ell_multi-2*epsilon`; I independently validated it in the
Round 7 feedback cited below.  Its exact polarity companion shows why clean
singleton deletion leaves all-Never as an exact sink.  Proposition 10 then
uses two auxiliary clocks and six distinct payoff coordinates to close a
genuine compensated cycle: both pure pair sinks are destroyed and every
`epsilon`-Nash profile obeys `b>=a^2-3epsilon` and
`a>=b^2-3epsilon`.  Pure Never remains an exact Nash profile.  Thus pair-to-
pair transport is no longer the missing mechanism; the exact hard step is a
positive nonzero seed which survives arbitrarily diffuse singleton clocks
and is compatible with a leakage upper account.  Proposition 11 makes the
diffuse obstruction exact: singleton mass one can coexist with maximum join
probability `1/N` against **every** outsider strategy.  A seed based on
collision with a singleton clock is therefore impossible; only an order-
based or payoff-account seed remains.  Proposition 12 also refutes the
one-watchdog order repair: against a singleton clock uniform on `N` dates,
every interior timing response improves over the better of Quit-before-all
and Never by at most the tie premium divided by `N`.  A surviving seed must
therefore be genuinely multi-owner/nonseparable or arise from a global payoff
account; it cannot be a disguised Quit-now/Never calibrator.

Proposition 13 now gives the first exact positive seed component: a
positive-solo owner plus one zero-solo collector forces the owner-opponent
Never probability to be `O(epsilon)` for arbitrary clocks.  Propositions
14--15 identify its exact integration cost.  Singleton-only collector chains
create a pure grand-collector sink, while any pointwise lossless repair of a
diffuse collector singleton necessarily creates a nonnegative solo and a
strict singleton-column dominance edge.  Therefore the remaining negative
construction must couple a collector **multicoalition** into the compensated
core account.  Proposition 16 performs the exact rank-one compression, and
`CODEX_GAUSS` independently validated all Quit-0 ties, owner-Never signs, and
the stated three-player scope in
`feedback/CODEX_CEDAR__INDEPENDENT_CLOCK_TOGGLE_GADGET__BY_CODEX_GAUSS.md`.
Proposition 17 reduces the residual pair to capping one rank-three coalition;
Proposition 18 rules out using the same unpriced edge in both directions, and
Proposition 19 shows that the minimal two-player compensation cycle has exact
unit gain around the ledger.  The next completion must therefore use a
nonreversible third coalition or a core inequality with strict surplus, while
its production-normal singleton matrix remains outside the independently
reviewed projective-Q-bar class.

The refusal component is now controlled exactly.  The late-quit identity

```text
s_i*A_(-i) <= epsilon+(u_i-n_i)
```

reduces all-Never mass to `u_i-n_i`, and Proposition 13's collector makes
that premium at most the owner's exact singleton-first mass, which the same
collector prices by a lossless Quit-zero deviation.  The exact next
obligation is to charge the collector-only first coalitions without creating
a new sure-exit set.  A candidate link must end in a core-containing leakage
coalition, retain the compensated `A`--`B` inequalities, and survive the
projective-Q-bar positive producer.  Failure requires an exact product-law
escape for every such multicoalition link, not the already ruled-out
singleton-only chain.

All propositions here are ordinary mathematics, not checked in Lean.  Named
Lean declarations are cited only for exact existing consumers or semantic
bridges.  No Lean file or export is proposed.

## 1. Board and source audit

The board was refreshed before this note was created.  Relevant prior work:

- Propositions 17--19 of
  `notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md` prove the sharp
  independent-clock inequality for disjoint equal-size coalitions.
- Propositions 20--21 there rule out passive auditors and fixed
  Quit-now/Never calibrators.  Propositions 22--27 localize coalition atoms
  and give joiner indicator adapters.  Proposition 28 records the grand-face
  polarity obstruction.  The reward gadget remains open.
- `questions/INDEPENDENT_CLOCK_TWO_PAIR.md` states the law problem, now
  answered positively by that work.  `questions/INCENTIVE_GADGET.md` states
  the still-open actual-table obligation.

The exact production declarations inspected are:

- `sSup_range_quittingTerminalPayoff_update_eq_pureTime`
  (`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`),
  which identifies the unrestricted unilateral behavioral supremum with
  deterministic quit times, including `Never`;
- `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
  (`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`), the desired
  negative endpoint; and
- `isQuittingSureExitSet_iff_forall_max` and
  `isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet`
  (`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`), the exact warning
  that any membership-toggle sink is already an all-behavior positive branch.

## 2. A short independent proof of the two-pair clock law

Let independent clocks `T_1,...,T_4` take values in
`N union {infinity}`.  Put

```text
A={T_1=T_2<min(T_3,T_4)},
B={T_3=T_4<min(T_1,T_2)},
a=P(A), b=P(B), ell=1-a-b.
```

The strict inequalities make both desired events finite; atoms at infinity
belong to leakage.

**Proposition 1 (ordinary mathematics; independent cross-check).**

```text
sqrt(a)+sqrt(b)<=1,
ell>=2*sqrt(a*b),
ell^2>=4*a*b.
```

**Proof.**  The event `A` is contained in

```text
{T_1<T_3} intersect {T_2<T_4}.
```

The two displayed cross-order events depend on disjoint pairs of independent
variables, hence

```text
a <= x*y,
x=P(T_1<T_3), y=P(T_2<T_4).
```

Likewise

```text
b <= x'*y',
x'=P(T_3<T_1)<=1-x,
y'=P(T_4<T_2)<=1-y,
```

because equality, including equality at infinity, fills the unused part of
each comparison.  Cauchy--Schwarz in `R^2` gives

```text
sqrt(a)+sqrt(b)
 <= sqrt(x*y)+sqrt((1-x)*(1-y))
 <= sqrt(x+1-x)*sqrt(y+1-y)=1.
```

Squaring and rearranging yields
`ell=1-a-b>=2*sqrt(a*b)`; both sides are nonnegative, so the final square is
valid.  This proof does not use finite support, hazards, stationarity, or a
truncation.  QED.

The usual two-date law with pair `1,2` acting first with survival `delta` and
pair `3,4` acting after joint survival has

```text
a=(1-delta)^2, b=delta^2, ell=2*delta*(1-delta),
```

so equality is sharp.

## 3. Two-sided localization of an exact coalition atom

Fix a finite player set `I`, independent clocks `(T_i)`, and a nonempty
coalition `S` of cardinality `d>=2`.  Let

```text
p_S=P(S is exactly the strict first-quitter coalition)
```

and let `x_t` be the part of this probability occurring at finite date `t`.

**Proposition 2 (ordinary mathematics; join and leave atom handle).**  If
`p_S>0`, some finite date `t` has

```text
x_t >= p_S^(d/(d-1)).                                 (3.1)
```

At this same date:

1. for every outsider `i notin S`, replacing `i` by pure Quit at `t` makes
   the exact first coalition `S union {i}` with probability at least the
   right side of `(3.1)`; and
2. for every member `i in S`, replacing `i` by pure Quit at `t+1` makes the
   exact first coalition `S\{i}` at date `t` with probability at least the
   same amount.

The second target is nonempty because `d>=2`.

**Proof.**  Independence gives

```text
x_t = product_(i in S) P(T_i=t)
      * product_(j notin S) P(T_j>t).
```

Consequently

```text
sum_t x_t^(1/d)
 <= sum_t product_(i in S) P(T_i=t)^(1/d)
 <= product_(i in S) (sum_t P(T_i=t))^(1/d)
 <=1
```

by generalized Holder.  The positive summable sequence `x_t` tends to zero
and attains a positive maximum `M`.  Therefore

```text
p_S=sum_t x_t^(1/d)*x_t^((d-1)/d)
    <=M^((d-1)/d),
```

which is `(3.1)`.

If `i notin S`, the original atom contains the factor `P(T_i>t)>0`.
Replacing `i` by `t` deletes that factor and adds `i` to the quitting
coalition, so the new target mass is at least `x_t`.

If `i in S`, the original atom contains `P(T_i=t)>0`.  Replacing `i` by
`t+1` deletes that factor; the remaining members of `S` still quit at `t`,
every outsider still survives beyond `t`, and the exact coalition becomes
`S\{i}`.  Its probability is again at least `x_t`.  QED.

The leave half is not a one-stage-support test.  The player's entire clock is
replaced by the deterministic later time, and the comparison remains valid
for arbitrary countable original support.

## 4. Exact indicator rewards give directed mass-flow inequalities

Let `S,T` be adjacent nonempty coalitions with `|S|>=2`, so
`T=S triangle {i}` for one player `i`.  Give player `i` the terminal reward

```text
r(U)_i = 1 if U=T, and 0 otherwise.                   (4.1)
```

Other payoff coordinates are arbitrary.

**Proposition 3 (ordinary mathematics).**  For every behavioral profile,
player `i` has a pure-time deviation whose gain is at least

```text
p_S^(|S|/(|S|-1)) - p_T.                             (4.2)
```

Hence every terminal `epsilon`-Nash profile satisfies

```text
p_T >= p_S^(|S|/(|S|-1)) - epsilon.                  (4.3)
```

**Proof.**  Use Proposition 2's joining or leaving deviation according as
`i` lies outside or inside `S`.  On the localized atom the deviated exact
coalition is `T`, so the deviation earns one.  On every other history it
earns either zero or one, hence its total payoff is at least the localized
mass.  The prescribed payoff under `(4.1)` is exactly `p_T`.  Subtraction
gives `(4.2)`.  QED.

This is the desired profile-adapted mechanism: it selects its date from the
candidate clock law and pays no complementary-history loss.  It also exposes
the combinatorial difficulty.  The same reward coordinate can cleanly isolate
only one target event; a directed hypercube cycle repeats coordinate labels.

## 5. Why the smallest toggle-flow cycle is matching pennies

Fix a nonempty base coalition `D` and two additional players `i,j`.  Consider
the four coalitions

```text
D, D+i, D+i+j, D+j
```

and orient their membership square cyclically:

```text
D --i--> D+i --j--> D+i+j --i--> D+j --j--> D.
```

The coordinate labels necessarily repeat: every coordinate is toggled an
even number of times around any Boolean-cube cycle.  The most favorable
nonnegative target-set rewards for this square are

```text
r(S)_i = 1 on {D+i,D+j}, 0 otherwise,
r(S)_j = 1 on {D,D+i+j}, 0 otherwise.                (5.1)
```

Thus `i` wants odd parity of the two membership bits and `j` wants even
parity.

**Proposition 4 (ordinary mathematics; exact minimal obstruction).**  If the
members of `D` quit surely at date zero and `i,j` independently Quit there
with probability `1/2`, then `(5.1)` gives both players payoff `1/2`, and no
unilateral behavioral deviation by `i` or `j` improves it.  If `|D|>=2` and
every member of `D` is also made indifferent to its action, the full profile
is an exact terminal Nash profile.

**Proof.**  Conditional on the sure date-zero base, `i,j` play the finite
matching-pennies game in their two membership actions.  Against a fair bit,
either pure membership choice and every mixture pays exactly `1/2`.
Absorption occurs at date zero independently of an `i`- or `j`-deviation
because `D` is nonempty, so a later quit time is exactly the Continue
membership action and no continuation history creates a new payoff.  When
`|D|>=2`, it also occurs after any one base player deviates because another
base quitter remains.  The base players are indifferent by hypothesis.  QED.

This is also the exact mechanism behind the checked sure-exit warning.  Any
pointwise-safe membership orientation with a sink coalition satisfies the
toggle inequalities of `isQuittingSureExitSet_iff_forall_max`, and
`isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet` consumes it.
Removing all pure sinks by a toggle cycle does not solve the problem: the
finite membership game supplies a mixed sink.

## 6. Proved, unproved, and next check

### 6.1 A clean one-way pair-to-pair flow, and its exact sink

Let

```text
A={1,2}, B={3,4},
A3={1,2,3}, C={1,3}, B1={1,3,4}.
```

Assign the following four payoff coordinates, with every unlisted coalition
paying zero in that coordinate:

```text
r(U)_3=1 iff U=A3,
r(U)_2=1 iff U=C,
r(U)_4=1 iff U=B1,
r(U)_1=1 iff U=B.                                   (6.1)
```

Write `p_U` for the exact strict-first mass of coalition `U`.

**Proposition 5 (ordinary mathematics; one-way propagation).**  Every
terminal `epsilon`-Nash profile for `(6.1)` satisfies

```text
p_A3 >= p_A^2-epsilon,
p_C  >= p_A3^(3/2)-epsilon,
p_B1 >= p_C^2-epsilon,
p_B  >= p_B1^(3/2)-epsilon.                          (6.2)
```

In particular, at `epsilon=0`,

```text
p_B >= p_A^9.                                        (6.3)
```

**Proof.**  Apply Proposition 3 successively along the distinct-player
membership path

```text
A --join 3--> A3 --leave 2--> C
  --join 4--> B1 --leave 1--> B.
```

The source cardinalities are `2,3,2,3`, so the localization exponents are
`2,3/2,2,3/2`.  Their product is nine.  Each toggler has exactly one
indicator target in `(6.1)`, so no other prescribed target mass enters any
of the four inequalities.  QED.

This exact propagation does not produce a negative game.  The pure date-zero
exit set `B` is a terminal Nash profile for `(6.1)`: player 1 already receives
one and loses it by joining, while every other possible membership toggle
changes a zero payoff to another zero payoff.  Equivalently, `B` passes the
conditions of `isQuittingSureExitSet_iff_forall_max`.  The flow has merely
constructed a sink.

Trying to run the symmetric path back from `B` to `A` reuses every player
with a second indicator target.  If player `i` is paid on targets `T` and
`T'`, its prescribed payoff is `p_T+p_T'`; a deviation localized to either
source is compared with that **sum**, so mass at the other target can satisfy
the inequality without creating the intended edge.  Weighting the two
indicators does not symmetrically isolate them: making the `T` weight dominate
suppresses the contamination in the `T` inequality and amplifies it in the
`T'` inequality.  This is the quantitative form of the repeated-coordinate
obstruction already visible in the matching-pennies square.

There is a global falsifier of any attempt to derive the terminal gap from
these indicator-flow inequalities alone.

**Proposition 6 (ordinary mathematics; uniform-law feasibility of every
indicator flow).**  Let `V` be any finite collection of nonempty coalition
events and suppose an argument extracts only inequalities of the form

```text
p_target >= p_source^alpha
```

with `alpha>=1`.  If all nonempty coalitions are included as possible
outcomes, the uniform law

```text
p_S=1/(2^n-1)
```

satisfies every such inequality simultaneously.  This law is realized by the
ordinary stationary product profile in which every player Quits with
probability `1/2` at every live date.

**Proof.**  For `0<p<=1` and `alpha>=1`, `p^alpha<=p`, so the uniform vector
satisfies every directed inequality, independently of the graph.  Under the
stationary half-hazard row, each of the `2^n` date-zero action coalitions has
probability `2^(-n)`.  Conditional on nonempty absorption, the coalition is
therefore uniform over the `2^n-1` nonempty sets.  Repetition makes absorption
almost sure and leaves that conditional distribution unchanged.  QED.

This does **not** say that the half-hazard profile is Nash for every indicator
reward table.  It says the proved localization consequences are an
incomplete separating language: no finite directed network of the lower
mass-flow bounds `(4.3)` can itself contradict product stopping laws.  A
successful gadget must add a signed relative-gain or leakage-upper-bound
inequality which the uniform law can violate.

### 6.2 Current separation

Proved here in ordinary mathematics:

- the cross-order proof of the already known sharp two-pair clock law;
- exact join and leave localization for every coalition atom of size at least
  two;
- the indicator-target mass-flow inequality `(4.3)`; and
- the exact matching-pennies escape from the smallest directed toggle square;
  and
- the exact one-way pair propagation `(6.2)`--`(6.3)` together with its pure
target-pair sink; and
- the uniform stationary product-law falsifier for every finite network of
  indicator lower-flow inequalities.

Not proved:

- any reward table forcing positive lower bounds on two incompatible pair
  events;
- any leakage upper bound from actual Nash inequalities;
- a fixed terminal exploitability gap; or
- a universal no-go for all compensated/profile-dependent toggle gadgets.

Next concrete check: seek a **compensated two-target coordinate** for the
reverse path.  Its second target must not enter the first edge's prescribed
payoff with an uncontrolled positive sign.  Test signed rewards of the form
`1_T-lambda*1_T'` and compute both localized deviation gains, including the
complementary histories on which the negative target may be created.  If no
choice of `lambda` gives two usable directed inequalities, formulate the
result as an exact two-target separation no-go; do not silently reuse the
indicator proof, whose nonnegativity is then lost.

## 7. Exact no-go for the static signed two-target shortcut

The proposed signed repair has a sharp elementary obstruction.  Let a fixed
player's payoff vanish outside two terminal outcomes `F,R`, and write

```text
r(F)=u>0,  r(R)=v.
```

Suppose a profile-adapted deviation is known only to land in `F` with
probability at least `x`; no information is available on the complementary
histories.  This is exactly the information delivered by the atom-localizing
deviation before further chronological control is proved.

**Proposition 7 (ordinary mathematics; sharp signed-target ledger).**  The
best lower bound on the deviating payoff obtainable from only that information
and the displayed reward range is

```text
u*x + min(0,v)*(1-x).                                (7.1)
```

Consequently, terminal `epsilon`-Nash implies only

```text
p_F >= x + min(0,v)/u*(1-x)
           - (v/u)*p_R - epsilon/u.                  (7.2)
```

In particular:

1. if `v>0`, the term `-(v/u)p_R` is the original uncontrolled prescribed-
   mass contamination;
2. if `v<0`, prescribed `R` mass helps, but the fixed complementary-history
   loss `(|v|/u)*(1-x)` is unavoidable and is sharp; and
3. a lossless lower flow `p_F>=x-epsilon/u` obtained from this information
   alone is possible exactly when `v=0`.

The symmetric lossless handle for `R` would require `u=0`.  Thus one scalar
payoff coordinate cannot losslessly isolate both targets in the two opposite
uses required to close the toggle path.

**Proof.**  On the guaranteed `F` event the deviation earns `u`.  On its
complement, an adversarial unresolved history can put all mass on the worse
of the zero-payoff outcomes and `R`, namely `min(0,v)`.  This proves `(7.1)`,
and equality is realized by exactly that two-point complementary law.  The
prescribed payoff is `u*p_F+v*p_R`; comparison with `(7.1)` and division by
`u>0` gives `(7.2)`.

For `v>0`, the complementary lower bound in `(7.1)` is zero, but solving for
`p_F` subtracts the prescribed positive `R` mass.  For `v<0`, solving removes
the bad prescribed sign, but `(7.1)` loses `|v|(1-x)`.  At `v=0` both defects
vanish.  Interchanging `F,R` proves the last assertion.  QED.

There is an equivalent positive-weight formulation.  If `u,v>0` and two
localized deviations guarantee respective target masses `x_F,x_R`, their
Nash consequences have the common left side

```text
u*p_F+v*p_R >= max(u*x_F,v*x_R)-epsilon.             (7.3)
```

They control only one weighted **union account**, not the two masses
separately.  No choice of static weights repairs this: increasing a target's
weight strengthens its own deviation and increases its contamination in the
other comparison by the same factor.

This proposition does not rule out signed rewards coupled to extra
information.  The only surviving repair inside the present thesis is
chronological.  If the localized `F` deviation occurs before every history
carrying the negative target `R`, that deviation truncates those histories
instead of paying the worst-case loss in `(7.1)`.  The exact next check is:

```text
Given localized dates t_F,t_R for two source atoms, can one fixed pair of
oppositely signed coordinates guarantee that the earlier deviation creates
no negative target and that the later comparison still supplies the reverse
mass flow, after accounting for all other dates and coalitions?
```

A negative answer must be an exact chronology theorem, not another static
weight observation.

## 8. Semantic correction: indicator leave edges suppress their source

The localized lower-flow inequality is valid for both joins and leaves, but
it conceals a decisive asymmetry.  A leave target can be obtained by the
global pure `Never` deviation without sacrificing any history on which that
target was already prescribed.

Fix a nonempty coalition `T` and player `i notin T`.  Give `i` the exact
indicator coordinate

```text
r(U)_i=1 if U=T, and 0 otherwise.                    (8.1)
```

**Proposition 8 (ordinary mathematics; pure-Never domination).**  Against
every profile, changing player `i` to pure `Never` weakly increases its payoff
on every coupled clock realization.  On every realization whose prescribed
exact first coalition is `T union {i}`, the increase is exactly one.  Hence

```text
terminal exploitability >= p_(T union {i}),          (8.2)
```

and every terminal `epsilon`-Nash profile satisfies

```text
p_(T union {i}) <= epsilon.                          (8.3)
```

**Proof.**  Couple the deviation by leaving every opponent clock unchanged
and replacing only `T_i` by `infinity`.

If the prescribed first coalition is `T`, then `i` quits strictly later, so
removing its clock preserves the same first coalition and the payoff one.  If
the prescribed first coalition is `T union {i}`, all members of `T` quit at
the same first date as `i`; after deleting `i` they still quit first and the
new exact coalition is `T`, changing payoff zero to one.  Every other
prescribed outcome pays zero, while the deviated reward is always zero or
one.  Thus the deviation is pointwise weakly better and gains one on the
displayed source event.  Taking expectations proves `(8.2)`--`(8.3)`.  QED.

The conclusion becomes only stronger for the sign-safe compensation

```text
r(U)_i=1_T(U)-lambda*1_R(U),
```

when every coalition in the negative target family `R` contains `i`: pure
Never cannot create a negative target and destroys every prescribed negative
target.  Negative rewards therefore do not stop the dominance.

This changes the interpretation of Proposition 5.  Its inequalities remain
correct, but `(6.1)` also gives the sharper bounds

```text
p_A3 <= epsilon  (player 2 switches to Never),
p_B1 <= epsilon  (player 1 switches to Never).       (8.4)
```

Combining `(8.4)` with the two preceding join inequalities in `(6.2)` gives

```text
p_A^2 <= 2*epsilon,
p_C^2 <= 2*epsilon.                                  (8.5)
```

So the alleged one-way transport does not carry positive mass from `A` to
`B` along small-error Nash profiles; it extinguishes the path at its first
leave edge.

**Corollary 8A (clean-indicator architecture no-go).**  In a directed network
whose edge `S -> S triangle {i}` is implemented by giving `i` the exact
indicator of the target, every leave edge forces its source mass at most
`epsilon`.  The only edges capable of propagating a positive source floor are
therefore join edges.  A path of join edges is inclusion-increasing and cannot
connect two disjoint nonempty designated coalitions.  Hence no clean exact-
indicator toggle network can force positive lower bounds on both disjoint
pair atoms by propagating one from the other.

This is a strict architecture no-go, not a theorem that every reward
completion has an equilibrium.  It nevertheless removes the entire
join/leave indicator plan, including its signed-negative variant.  A viable
leave edge must pay player `i` on at least one outcome containing `i` strongly
enough that pure Never can lose something.  That positive compensation then
enters the prescribed payoff ledger and recreates the repeated-coordinate
problem.

The next exact question is the smallest compensated leave ledger.  Let
`T=S\{i}` and give `i` reward one on `T`, reward `c>0` on a compensation
coalition `H` containing `i`, and zero elsewhere.  Determine whether the Nash
inequality for pure Never and the profile-selected leave deviation can force
a lower bound on `p_T` without allowing `p_H` to absorb the entire account.
If the answer is negative for every `H,c`, preserve the sharp two-positive-
target counterexample; if positive, insert it into the shortest join/leave
path and recompute all pair and leakage inequalities.

## 9. A compensated aggregate ledger controls all multi-coalition leakage

Compensation can in fact transport an aggregate, although it still leaves the
hard singleton/Never boundary.  Return to four players and
`A={1,2}`, `B={3,4}`.  Define the following complete payoff table.  For
`i in A`, set

```text
r(U)_i = 2  if U=A,
           1  if i notin U,
           0  otherwise.
```

For `i in B`, use the same rule with `B` in place of `A`.  Let
`ell_multi` be the probability that the exact finite first coalition has
cardinality at least two and is neither `A` nor `B`.  Singleton outcomes and
Never are deliberately excluded.

**Proposition 9 (ordinary mathematics; compensated multi-leakage ledger).**
Every terminal `epsilon`-Nash profile for this table satisfies

```text
a+b >= ell_multi-2*epsilon.                          (9.1)
```

**Proof.**  Fix `i in A` and couple the deviation to pure Never.  A prescribed
outcome not containing `i` has payoff one and is unchanged after removing
`i`.  A multi-player outcome `U` containing `i`, other than `A`, has prescribed
payoff zero; after removing `i`, the nonempty coalition `U\{i}` quits at the
same first date and pays one.  At `A`, the payoff falls from two to one.  An
own-singleton outcome pays zero and its replacement pays either zero at Never
or one at a later nonempty opponent coalition, so it cannot hurt.  Therefore
the deviation gain is at least

```text
sum_{U: i in U, |U|>=2, U!=A} p_U - a.
```

The Nash inequality gives

```text
a >= sum_{U: i in U, |U|>=2, U!=A} p_U-epsilon.      (9.2)
```

For `i in B` the identical argument replaces `a,A` by `b,B`.  Sum `(9.2)`
over all four players.  Every multi-coalition leakage outcome `U` is counted
exactly `|U|` times on the right and hence at least twice, while `A` and `B`
are excluded from the two ledgers of their own members and do not enter the
other pair's ledgers.  Thus

```text
2*a+2*b >= 2*ell_multi-4*epsilon,
```

which is `(9.1)`.  QED.

This is the first actual table in this note that forces a **total** desired-
pair account relative to a broad leakage class, rather than merely propagating
one atom.  It is not a counterexample.  Both pure `A` and pure `B` are exact
terminal Nash profiles: pair members receive two and outsiders receive one,
and every membership toggle weakly lowers the toggler's payoff.  Pure Never
is also an exact terminal Nash profile because every own singleton payoff is
zero.  The result is a ledger component, not a completed game.

It nevertheless isolates the residual sharply.  Compensation can pay for all
finite leakage coalitions of size at least two with the correct aggregate
direction.  It does not charge singleton outcomes or Never: deleting the sole
quitter exposes an arbitrary later clock law rather than a fixed nonempty
coalition.  Nor does `(9.1)` balance `a` against `b`; one pure desired pair
still satisfies it.  The next gadget must therefore do both of the following
without destroying `(9.1)`:

1. break the singleton/Never escape with a genuinely diffuse-clock argument,
   not a preassigned date; and
2. break the two pure pair sinks while transferring their mass to the
   *opposite* desired account rather than paying unavoidable leakage.

This is the current universal obstruction.  A construction which merely
adds joiner indicators fails item 2: it converts pair mass into triple
leakage, in the same direction as the independent-clock lower bound.

Gauss subsequently strengthened Proposition 9 to **all finite leakage** in
Proposition 37 of `notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`: changing
each own singleton payoff from zero to `-2` adds twice the singleton mass to
the relevant pure-Never ledger and yields

```text
a+b >= ell_single+ell_multi-2*epsilon.
```

I independently checked the constants, all boundary outcomes, and the exact
pointwise polarity obstruction in
[`../feedback/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL__BY_CODEX_CEDAR__ROUND_7.md`](../feedback/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL__BY_CODEX_CEDAR__ROUND_7.md).
That strengthening should be used in later work; Proposition 9 remains here
to show the compensation mechanism as it was derived.  The sharpened residual
is no longer finite singleton leakage: it is all-Never mass and pair balance.

## 10. A six-player compensated cycle removes both pure pair sinks

The nonlocal compensation coalition can be used to close the `A`--`B` flow
without reusing any payoff coordinate.  Add auxiliary players `5,6` to the
four clock players and retain

```text
A={1,2},  B={3,4}.
```

All unlisted rewards below are zero.  Give the six players these exact
indicator sums:

```text
r_5 = 1_{ {1,2,5} },
r_1 = 1_{ {2,5} } + 1_{ {1,3} },
r_3 = 1_{ {1} }   + 1_B,

r_6 = 1_{ {3,4,6} },
r_4 = 1_{ {3,6} } + 1_{ {2,4} },
r_2 = 1_{ {4} }   + 1_A.                            (10.1)
```

Write `p_U` for the exact finite first-coalition mass of `U` and retain
`a=p_A`, `b=p_B`.

**Proposition 10 (ordinary mathematics; compensated pair cycle).**  Every
terminal `epsilon`-Nash profile for `(10.1)` satisfies

```text
b >= a^2-3*epsilon,
a >= b^2-3*epsilon.                                 (10.2)
```

Moreover, the pure `A` and pure `B` date-zero profiles each have a unilateral
gain exactly equal to one under this table, while pure Never is an exact
terminal Nash profile.

**Proof.**  Apply the exact join localization to player `5` at the pair atom
`A`.  Its coordinate is nonnegative and supported only on `A union {5}`, so
Proposition 3 gives

```text
p_{125} >= a^2-epsilon.                              (10.3)
```

Now compare player `1` with pure Never.  Its positive target `{2,5}` is
preserved whenever already prescribed.  Every prescribed `{1,2,5}` outcome
becomes `{2,5}`, gaining one.  The only positive outcome which can be lost is
the compensation coalition `{1,3}`, which becomes `{3}`.  All other changes
go from zero to zero or one.  Hence the deviation gain is at least

```text
p_{125}-p_{13},
```

and Nash implies

```text
p_{13} >= p_{125}-epsilon.                           (10.4)
```

For player `3`, pure Never changes every prescribed `{1,3}` outcome to the
positive singleton `{1}`.  Its only positive containing compensation outcome
which can be lost is `B`, which becomes `{4}`.  Thus

```text
b >= p_{13}-epsilon.                                 (10.5)
```

Combining `(10.3)`--`(10.5)` gives the first inequality of `(10.2)`.

The reverse half is symmetric but uses disjoint payoff coordinates:

```text
p_{346} >= b^2-epsilon              (join player 6),
p_{24}  >= p_{346}-epsilon          (player 4 -> Never),
a       >= p_{24}-epsilon           (player 2 -> Never).
```

This proves the second inequality.

At pure `A`, player `5` can join at date zero and changes payoff zero to one
at `{1,2,5}`.  At pure `B`, player `6` has the symmetric gain.  Therefore the
two original sure-exit sinks are destroyed with gain one.  Finally, every
player's own singleton reward in `(10.1)` is zero.  Against opponents who all
Never, every unilateral quit time therefore gives payoff zero, as does Never;
so pure Never is exact terminal Nash.  QED.

The compensation jumps are worth spelling out:

```text
A --join 5--> {1,2,5}
  --Never by 1, paid by {1,3}--> {1,3}
  --Never by 3, paid by B--> B,

B --join 6--> {3,4,6}
  --Never by 4, paid by {2,4}--> {2,4}
  --Never by 2, paid by A--> A.
```

They are payoff-ledger arrows, not claims that one reached chronological path
visits these coalitions.  Each of the six physical players supplies only one
coordinate, so the earlier repeated-label contamination is genuinely absent.
The two auxiliaries lie outside `A union B`; every coalition involving them is
ordinary leakage in Proposition 1, as required.

This construction settles one sub-obligation positively: finite compensated
leave ledgers can balance the two incompatible desired atoms and remove both
pure pair sinks.  But `(10.2)` admits the zero solution, realized exactly by
pure Never.  Adding a positive own singleton reward destroys pure Never but
opens the diffuse-singleton seam: an outsider cannot localize an arbitrary
singleton first-coalition mass with any modulus depending only on that mass
(uniformly spreading the singleton owner's clock over `N` dates makes the
largest date atom `1/N`).  Therefore the next check is not another coalition
cycle.  It is whether one can seed `(10.2)` directly from total opponent
absorption or a pure-time best-response gap without asking two independent
players to collide with a diffuse singleton clock.

## 11. No tie-based modulus exists for a singleton seed

The last obstruction is exact even if the joining outsider may use an
arbitrary behavioral strategy, not just a deterministic date.

**Proposition 11 (ordinary mathematics; diffuse singleton falsifier).**  Fix
two distinct players `u,k` and an integer `N>=1`.  Let `u` choose its quit time
uniformly on `N` distinct finite dates, and let every other player, including
`k`, initially Never.  Then the exact first-coalition mass of `{u}` is one.
After replacing `k` by any behavioral strategy whatsoever, the probability
that the exact first coalition contains both `u` and `k` is at most `1/N`.

Consequently there is no positive function `f` with `f(1)>0` such that every
singleton atom of mass one admits an outsider deviation joining it with
probability at least `f(1)`.

**Proof.**  Before absorption the public history is the deterministic all-
Continue word, so `k`'s behavioral strategy induces a planned quit-time law
`nu` independent of `u`'s uniform law `mu`.  Since all remaining players
Never, a first coalition containing both players occurs exactly when their
finite quit times tie.  Therefore

```text
P(T_u=T_k<infinity)
  = sum_t mu(t)*nu(t)
  <= (max_t mu(t))*sum_t nu(t)
  <= 1/N.
```

The original exact singleton event has probability one because `u` quits at
one of the displayed finite dates and everyone else Never.  Letting `N` tend
to infinity proves the no-modulus assertion.  QED.

This differs sharply from Proposition 2: rank `d>=2` gives the Holder atom
modulus `p^(d/(d-1))`, whereas rank one has exponent `d/(d-1)=infinity` and
admits the displayed diffuse falsifier.  Adding more collision watchdogs does
not help: for each independent outsider the same `1/N` upper bound holds, and
any fixed finite number of them has total captured tie mass at most their
count divided by `N`.

Thus a nonzero seed for `(10.2)` cannot be implemented by paying an outsider
to join a positive-solo player's quit date.  The next concrete test is an
**order seed**: price the two events “watchdog quits strictly before the
singleton owner” and “strictly after” so that a profile-selected quantile,
rather than a largest atom, creates a gain.  Every same-date collision term
must remain in the leakage account, and the fixed Quit-now/Never escape of
Proposition 21 in Gauss's note must be retested rather than assumed away.

## 12. A diffuse owner also kills every one-watchdog order premium

Fix the two-player slice consisting of singleton owner `u` and watchdog `k`;
all other players Never.  Let the watchdog's three relevant rewards be

```text
x=r({k})_k       (k quits strictly first),
y=r({u})_k       (u quits strictly first),
z=r({u,k})_k     (finite tie).
```

**Proposition 12 (ordinary mathematics; order-seed no-go).**  If `u` is
uniform on `N` finite dates, every behavioral strategy of `k` has payoff at
most

```text
max(x,y) + max(0,z-max(x,y))/N.                      (12.1)
```

The two endpoint strategies already attain `x` and `y`: quitting strictly
before the displayed support attains `x`, and Never attains `y`.  Hence the
largest possible advantage of an interior/profile-selected order response
over the better fixed endpoint is at most the positive tie premium divided by
`N`.

**Proof.**  For a deterministic finite time `t`, put

```text
alpha=P(t<T_u), beta=P(T_u<t), tau=P(T_u=t).
```

These numbers are nonnegative, sum to one, and `tau<=1/N`.  The watchdog
payoff is

```text
alpha*x+beta*y+tau*z
 <= (alpha+beta)*max(x,y)+tau*z
 = max(x,y)+tau*(z-max(x,y))
 <= max(x,y)+max(0,z-max(x,y))/N.
```

At `t=infinity`, the finite owner quits first surely and the payoff is `y`.
An arbitrary behavioral strategy induces an independent mixed quit-time law,
so its payoff is a convex combination of these deterministic-time values and
obeys the same upper bound.  Quitting before the least support date gives
`x`, proving the endpoint assertion.  QED.

If all rewards are bounded in absolute value by `B`, the residual premium in
`(12.1)` is at most `2B/N`.  Thus no fixed positive exploitability gap can be
obtained from a one-watchdog order test after the owner diffuses sufficiently.
When `z<=max(x,y)`, the conclusion is exact for every owner law: an endpoint
is already optimal.  When `z>max(x,y)`, the only extra resource is precisely
the collision atom refuted quantitatively in Proposition 11.

This closes the proposed quantile shortcut.  It also supplies a direct
source-level explanation of why a one-owner seed falls back into the fixed
Quit-now/Never calibrator boundary: order probabilities contribute only a
convex interpolation between the endpoints, and the nonconvex tie bonus
vanishes under diffusion.  The next viable test must involve at least two
active owner clocks whose different strict-first coalitions carry genuinely
nonseparable rewards.  Such a construction must be checked against the
independent-clock leakage law before it is added to `(10.1)`.

## 13. Exact adapter deficit and pivot criterion

After the preceding checkpoint, Gauss proved two directly relevant ordinary
lemmas in Propositions 37--40 of
`notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`:

- the compensated deletion coefficient can be scaled to make **all finite**
  leakage arbitrarily small relative to `a+b`; and
- for a player with solo reward `s`, prescribed payoff `u`, pure-Never payoff
  `n`, and opponent all-Never probability `A_{-i}`, late deterministic quitting
  gives the exact refusal inequality

```text
s*A_{-i} <= epsilon+(u-n).                           (13.1)
```

I independently reviewed the all-finite coefficient and its pointwise
polarity no-go in the Round 7 feedback cited above.  The identity `(13.1)`,
its amplified version, and the first-disagreement localization of `u-n` were
then independently checked in
`feedback/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL__BY_CODEX_CEDAR__ROUND_8.md`.

Equation `(13.1)` identifies the exact missing seed datum.  Breaking all-
Never requires some `s>0`; then controlling joint Never mass requires an upper
bound on the same player's refusal premium `u-n`.  The clean singleton ledger
cannot provide it (negative solo restores all-Never), an outsider collision
has no modulus by Proposition 11, and a one-watchdog order response adds only
`O(1/N)` by Proposition 12.  The six-player compensated pair cycle does not
touch this premium.

Thus the present architecture is rigorously exhausted at the following
adapter, not merely at a search failure:

```text
positive solo + arbitrary candidate clock law
  ==> a bound u-n <= Phi(a,b,finite leakage)
      with Phi small enough to combine (13.1), pair balance,
      the finite-leakage ledger, and the independent-clock law.            (13.2)
```

Any proof of `(13.2)` must use cross-history interaction with at least two
active owner clocks.  A pointwise deletion, a fixed endpoint mixture, a
single diffuse owner, or a finite calendar has now been exactly falsified.
Conversely, without `(13.2)` pure Never remains a literal exact Nash profile
of every compensated table constructed here.

Section 14 gives a first positive repair of `(13.2)`: one zero-solo collector
coordinate controls the positive-solo owner's singleton first-disagreement
mass and hence its entire refusal premium.  The remaining obstruction is no
longer all-Never; it is the collector's own zero-solo sure-exit sink and its
integration into the pair/leakage ledger.

## 14. A zero-solo collector exactly removes the Never residual

Add two distinct auxiliary players: a positive-solo owner `w` and a collector
`h`.  Their two payoff coordinates are independent of all other coordinates.
Fix constants `K>0` and `H>=0`.  Define the collector coordinate by

```text
r({w})_h=-K,
r(U)_h=0 for every other nonempty U.                 (14.1)
```

Define the owner coordinate by

```text
r({w})_w=1,
r(U)_w=-H  if w in U and |U|>=2,
r(U)_w=1   if w notin U.                             (14.2)
```

Never pays zero as usual.  For an arbitrary ordinary profile, put

```text
p=P(the first finite coalition is exactly {w}),
m=P(w belongs to a nonsingleton first finite coalition),
A_(-w)=P(every opponent of w is Never).
```

**Proposition 13 (ordinary mathematics; exact Never collector).**  Every
terminal `epsilon`-Nash profile for any reward table containing the two
coordinates `(14.1)`--`(14.2)` satisfies

```text
p <= epsilon/K,                                      (14.3)
m <= (p+epsilon)/(H+1),                              (14.4)
A_(-w) <= epsilon+p <= epsilon*(1+1/K).              (14.5)
```

In particular the all-Never terminal mass is at most the right side of
`(14.5)`.  These estimates hold regardless of every other player's rewards
and clock law.

**Proof.**  Replace the collector's entire clock by pure Quit at date zero.
On the event whose prescribed first coalition is `{w}`, the deviated first
coalition is `{h}` if `w` was scheduled later and `{w,h}` if `w` was scheduled
at date zero.  Both pay `h` zero instead of `-K`.  Off that event, the
prescribed payoff and the deviated payoff are both zero, because neither
terminal coalition can be exactly `{w}` after `h` quits at date zero.  The
deviation gain is therefore exactly `Kp`; the Nash inequality gives `(14.3)`.

Now replace `w` by pure Never.  On a nonsingleton first coalition containing
`w`, deletion leaves the nonempty coalition of its simultaneous opponents;
the payoff changes from `-H` to `1`, a gain of `H+1`.  On singleton `{w}`,
deletion produces either a later nonempty opponent coalition, worth `1`, or
Never, worth zero, so the loss is at most one.  Every coalition excluding `w`
is unchanged.  Hence the deviation gain is at least

```text
(H+1)*m-p,
```

which proves `(14.4)`.

For the sharper refusal account, let `u_w` be the prescribed payoff and
`n_w` the pure-Never payoff.  The same coupling gives

```text
u_w-n_w <= p-(H+1)*m <= p.                          (14.6)
```

Apply the independently reviewed late-quit inequality `(13.1)` with solo
reward one:

```text
A_(-w) <= epsilon+(u_w-n_w) <= epsilon+p.
```

Together with `(14.3)` this is `(14.5)`.  QED.

This is a genuine cross-history repair of the earlier diffuse-singleton
seam.  It does not ask an outsider to collide with the unknown quit date:
the collector preempts at date zero, and its payoff is designed so that this
deviation has no loss on any other terminal history.  Simultaneous owner
atoms, late opponent absorption, and Never are all included exactly.

The repair is not yet a counterexample.  Coordinate `(14.1)` gives the
collector own solo payoff zero and payoff zero on every coalition other than
`{w}`.  If `h` quits surely while everyone else plays Never, all players whose
other coordinates weakly prefer `{h}` can make this a new exact sure-exit
sink.  Giving `h` a negative own solo destroys that sink but makes Quit at
date zero lose on histories outside `{w}`, weakening `(14.3)` to a fixed
parameter error rather than `O(epsilon)`.  Chaining another zero-solo
collector merely moves the same sink, and a finite closed collector cycle
must be checked against a simultaneous mixed or pure coalition sink.

The next concrete question is therefore smaller than `(13.2)`: integrate one
zero-solo collector into the six-player compensated `A`--`B` cycle so that
every first coalition led only by collectors is charged by the existing
finite-leakage account, while preserving the exact lossless identity `Kp`.
Success would give `Never=O(epsilon)` and leave only the already quantified
pair-balance/leakage contradiction.  Failure requires an exact product-law
profile supported on the collector subgame, not merely the observation that
pure `{h}` is a sink for `(14.1)` alone.

## 15. A finite chain of singleton-only collectors still has a pure sink

The first proposed integration was to add finitely many zero-solo collectors,
each of which pays negatively on the preceding collector's singleton and zero
elsewhere.  This does break every diffuse pure-singleton profile, but it does
not solve the game.

Let `C={h_1,...,h_m}` with `m>=2`.  For each collector, suppose its own
coordinate is zero on every coalition of cardinality at least two and on its
own singleton.  It may be negative on selected *other* singleton coalitions.
Suppose every noncollector coordinate weakly prefers the grand collector
coalition `C` to joining it or quitting strictly before it.

**Proposition 14 (ordinary mathematics; collector-chain sink).**  If `m>=3`,
the pure profile in which all members of `C` quit at date zero and everyone
else Never is an exact terminal Nash profile.  For `m=2`, the same conclusion
holds whenever each collector's payoff on the other collector's singleton is
at most zero.

**Proof.**  The prescribed first coalition is `C`, so every collector gets
zero.  A collector who continues at date zero leaves `C\{h_i}`.  If `m>=3`,
this is still a coalition of cardinality at least two and pays zero; quitting
at any other time cannot alter the already absorbed history.  If `m=2`, the
remaining singleton pays at most zero.  Thus no collector gains.  By the
stated noncollector condition, nobody outside `C` gains by joining at date
zero or preempting; later actions are irrelevant.  Pure-time extremality then
covers every mixed behavioral deviation.  QED.

For the literal owner/collector table `(14.1)`--`(14.2)`, one collector already
gives the pure `{h}` sink.  Adding a cyclic family with negative predecessor
singletons gives the `m=2` version above; adding three or more gives the grand
collector sink even when all singleton sinks are broken.  Thus a finite
singleton-only chain cannot integrate Proposition 13.  At least one
collector-containing **multicoalition** must have a profitable membership
toggle, and that toggle must feed a coalition counted by the amplified core
ledger.  This is now the exact next construction test; simply adding another
collector is ruled out.

## 16. Every lossless diffuse-singleton collector creates a nonnegative solo

There is also a raw singleton-matrix cost to any exact repair of the pure
collector sink.  Suppose player `i` is prescribed Never and is intended to
charge the event that another player `h` is the unique first quitter by
switching to pure Quit at date zero.  Call this switch **pointwise lossless**
if it never lowers `i`'s payoff on any realization of the opponents' clocks,
and suppose it gains at least `kappa>0` whenever the prescribed first
coalition is `{h}`, independently of the date of `h`'s quit.

Write

```text
s_i=r({i})_i,
c_hi=r({h})_i,
j_hi=r({h,i})_i.
```

**Proposition 15 (ordinary mathematics; singleton-matrix cost).**  Every such
lossless collector satisfies

```text
s_i>=0,
s_i>=c_hi+kappa,
j_hi>=c_hi+kappa.                                  (16.1)
```

Thus the source singleton column of `h` fails the solo-dominance inequality
in coordinate `i` by a strict amount.  In particular, a finite lossless repair
of every diffuse singleton sink necessarily creates a directed graph on
nonnegative-solo owners; if one vertex's singleton column weakly dominates
all solo payoffs, the reviewed normal-owner rare-hazard producer gives a
uniform-equilibrium payoff instead of a negative gap.

**Proof.**  On the realization where every opponent is Never, the prescribed
payoff is zero and Quit at date zero produces singleton `{i}`.  Losslessness
gives `s_i>=0`.  On a realization where `h` is the unique quitter at a later
date, the prescribed payoff is `c_hi`, while the deviation makes `i` quit
alone at date zero and pays `s_i`; the stipulated gain gives the second
inequality.  If `h` quits at date zero, the deviation produces `{h,i}` and
gives the third.  QED.

The first strict comparison in `(16.1)` is exactly why the zero-solo
coordinate `(14.1)` can collect `{w}` without loss but cannot itself be
repaired by another pointwise lossless zero-solo coordinate.  Iterating the
repair moves into the normalized singleton matrix rather than staying in a
pure payoff ledger.  The independently reviewed projective-Q-bar producer in
`feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_CEDAR__ROUND_15_PROJECTIVE_QBAR.md`
then supplies a hard filter: a genuine counterexample built this way must
eventually leave projective Q-bar on the production-normal subtype.  This is
not yet a contradiction for a directed cycle, but it rules out any collector
closure whose raw singleton data remain inside that solved matrix class.

## 17. Two collectors compress every diffuse seam to one rank-two atom

Although a collector chain cannot itself close, two collectors remove every
rank-one auxiliary seam simultaneously.  Retain owner `w`'s coordinate
`(14.2)`.  Add collectors `h_1,h_2` with

```text
r(U)_(h_1)=-K  if U={w} or U={h_2}, and 0 otherwise,
r(U)_(h_2)=-K  if U={h_1},          and 0 otherwise.  (17.1)
```

Let `p_x` denote the exact first-coalition mass of singleton `{x}`, and let
`m_w` be the mass of nonsingleton first coalitions containing `w`.

**Proposition 16 (ordinary mathematics; rank-one compression).**  Every
terminal `epsilon`-Nash profile satisfies

```text
p_w+p_(h_2) <= epsilon/K,
p_(h_1) <= epsilon/K,
m_w <= (p_w+epsilon)/(H+1),
P(all opponents of w are Never) <= epsilon+p_w.      (17.2)
```

Consequently, among outcomes involving only `w,h_1,h_2`, every mass except
the rank-two coalition `{h_1,h_2}` is `O(epsilon)`.

**Proof.**  Pure Quit at date zero by `h_1` changes payoff from `-K` to zero
exactly on the two singleton-first events `{w}` and `{h_2}`, and changes zero
to zero on every other event.  Its gain is exactly
`K*(p_w+p_(h_2))`.  The analogous deviation by `h_2` has gain exactly
`K*p_(h_1)`.  The first two inequalities follow.  The owner-Never calculation
and the refusal-premium calculation are identical to Proposition 13, giving
the last two inequalities.  If the first coalition is supported only on the
three displayed players, the remaining finite possibilities are their three
singletons, coalitions containing `w`, and `{h_1,h_2}`.  QED.

This is the useful form of the collector mechanism.  It converts the
unlocalizable diffuse singleton problem into one ordinary rank-two atom, for
which Proposition 2's exact Holder handle is available.  Proposition 14 says
why this is still not a game: pure `{h_1,h_2}` is the residual sink.  The
smallest remaining construction is now concrete: attach one compensated
membership-toggle path from `{h_1,h_2}` to the existing `A`--`B` pair ledger.
No new rank-one modulus is required anywhere on that path.

## 18. The remaining interface is one capped rank-three coalition

Let

```text
C={h_1,h_2},
T=C union {k}
```

for an outsider `k`.  Give player `k` the indicator payoff

```text
r(U)_k=1 if U=T, and 0 otherwise.                   (18.1)
```

**Proposition 17 (ordinary mathematics; rank-two injection).**  If `c` and
`t` are the exact first-coalition masses of `C` and `T`, every terminal
`epsilon`-Nash profile satisfies

```text
t >= c^2-epsilon.                                   (18.2)
```

Therefore any independent compensated coordinate account giving `t<=delta`
forces

```text
c <= sqrt(delta+epsilon).                           (18.3)
```

Even without such an account, `C` and `T` are distinct terminal coalitions,
so `c+t<=1`.  Combining this with `(18.2)` gives

```text
c^2+c <= 1+epsilon,
c <= (sqrt(5+4*epsilon)-1)/2.                       (18.4)
```

**Proof.**  Proposition 2 with `|C|=2` selects a deterministic date at which
replacing `k` by pure Quit creates exact first coalition `T` with probability
at least `c^2`.  The prescribed indicator payoff is `t`, so the deviation
gain is at least `c^2-t`.  Apply the Nash inequality and rearrange.

If `t<=delta`, this gives `(18.3)`.  Independently, `t<=1-c` gives `(18.4)`
after taking the positive root of the resulting quadratic inequality.  QED.

Together, Propositions 16--17 reduce the entire auxiliary clock packet to one
ordinary cap:

```text
cap the mass of T={h_1,h_2,k}.                       (18.5)
```

All Never mass, owner-containing mass, and singleton auxiliary mass are then
small, and `(18.4)` already prevents the last collector-only atom from being
near one.  A stronger cap through `(18.3)` would make it small.  The remaining
nontrivial issue is not probability or stopping-time localization.  It is
payoff-coordinate compatibility: if `k` is also used in the amplified core
ledger, its indicator reward `(18.1)` can contaminate the pure-Never
inequality that is meant to cap `t`.  A viable completion needs a compensated
second coordinate/player which caps `T` without undoing `(18.2)`.  This is the
smallest exact multicoalition link left by the construction.

## 19. The direct cap has the opposite edge polarity

There is a precise reason the indicator coordinate in `(18.1)` cannot also
cap `T`.  Let `C` be any nonempty coalition, let `k` be outside `C`, and write

```text
T=C union {k},
d_k=r(T)_k-r(C)_k.
```

On a realization where the opponents' first coalition is `C` at a
deterministic date at which `k` is inserted, player `k`'s payoff change is
`d_k`.  On a realization where the prescribed first coalition is `T`, the
pure-Never replacement of `k` deletes `k` and changes the payoff by `-d_k`.

**Proposition 18 (ordinary mathematics; exact edge-polarity obstruction).**
The same payoff coordinate cannot assign a strict positive gain both to the
join transition `C -> T` and to the deletion transition `T -> C`.  More
generally, take a member `h in T`, put `D=T\{h}`, and suppose Quit at date zero
by `h` must be pointwise lossless on the realization where `D` is the first
coalition at date zero.  Then

```text
r(T)_h>=r(D)_h.                                      (19.1)
```

Consequently pure Never by `h` has nonpositive payoff change on the exact
`T` realization:

```text
r(D)_h-r(T)_h<=0.                                   (19.2)
```

Thus neither the joiner nor a lossless Quit-zero collector member can supply
the desired strict cap of `mass(T)` on the same unpriced reverse edge.

**Proof.**  Both statements are literal row comparisons.  In the first,
joining changes `C` to `T`, whereas Never changes `T` to `C`; the increments
are exact negatives.  For the second, if the opponents quit as `D` at date
zero, Quit-zero by `h` creates `T`, so pointwise losslessness is exactly
`(19.1)`.  If instead the prescribed coalition is `T`, pure Never leaves
`D`, giving `(19.2)`.  QED.

This does not rule out a cap by a **different** member of `T`.  It identifies
the payment that such a cap must expose.  If that member receives a bonus
`g=r(D)_h-r(T)_h>0` for deleting itself from `T`, its Quit-zero strategy loses
exactly `g` on a date-zero `D` source.  Hence a complete table must either
price that exact reverse-source atom by another deviation or admit it into an
already bounded compensated leakage account.  Merely increasing the cap
coefficient cannot help: it increases the reverse-source loss by the same
amount.

The next concrete check is a two-player compensated cap.  Choose `h in C`
as the capper and use a second player to bound the exact date-zero mass of
`D=(C\{h}) union {k}`.  Test whether the second deviation can charge `D`
only against the already controlled owner-containing mass `m_w`; if it creates
another unpriced reverse edge, record the resulting finite polarity cycle and
test its product-law equilibrium exactly.

## 20. The minimal two-player compensation cycle has unit gain

I tested the smallest repair requested after Proposition 18.  Besides the
pair mass `c` and injected triple mass `t`, introduce

```text
p = mass of the collector singleton exposed by the capper,
d = mass of the reverse source exposed at date zero.
```

Let `I,J,g,L>0` be respectively the join reward, the second player's
date-zero deletion reward, the collector reward, and the first member's cap
reward.  The best possible loss ledger for this four-edge architecture has
the zero-error form

```text
I*(c^2-t) <= J*p,       g*p <= L*d,
J*d <= I*t,             L*t <= g*c.                 (20.1)
```

The first inequality is the Holder join `C -> T`, contaminated only by the
second player's singleton reward.  The second pays that singleton through the
capper's Quit-zero deviation.  The third pays the resulting date-zero reverse
source by a Continue-at-zero deletion.  The fourth caps `T` by a member's
Never deletion, losing only on the collector pair `C`.  Allowing Nash errors
only weakens all four inequalities.

**Proposition 19 (ordinary mathematics; exact coefficient cancellation).**
No choice of positive coefficients in `(20.1)` forces `c=0`, or even forces a
strict universal upper bound below one.  Eliminating `p,d,t` gives only

```text
c <= 1+g/L,                                           (20.2)
```

which is vacuous for a probability.  With all four coefficients equal to
one, the nonzero probability ledger

```text
c=1/2,    t=p=d=1/8
```

satisfies `(20.1)` and has total displayed mass `7/8`.

**Proof.**  The middle two inequalities give

```text
p <= (L/g)*d <= (L*I/(g*J))*t.
```

Substitute this in the first inequality:

```text
c^2 <= (1+L/g)*t.
```

The last inequality gives `t<=(g/L)c`.  For `c>0`, their combination is
exactly `(20.2)`; `c=0` is trivial.  For the displayed numerical ledger,
`c^2-t=1/8=p`, `p=d=t`, and `t<=c`.  QED.

This cancellation is not an accident of normalization.  Every edge ratio is
used once in each orientation, so their product around the compensation cycle
is one.  Increasing `J` suppresses the reverse-source mass but increases its
contamination of the join inequality by the reciprocal amount; increasing
`L` strengthens the cap but weakens the collector account in the same way.
Thus the two-player cap proposed after Proposition 18 is rigorously exhausted
at the level of its strongest sign-correct mass ledger.

The surviving route needs a genuinely nonreversible surplus: either a third
coalition whose mass is already bounded by the amplified core inequality with
a coefficient not paid back on the return edge, or a whole-strategy deviation
that charges two reverse sources simultaneously.  The next exact test is to
identify `d` with a coalition already included in Proposition 9's amplified
finite-leakage mass and recompute that coordinate's Never inequality.  If its
loss is exactly the reciprocal term in `(20.1)`, the entire compensated-cap
architecture is dead and this negative thesis should pivot rather than add
another collector cycle.

## 21. Every finite lossless join/collector completion has a grand sink

The preceding failures have a common actual-profile witness.  Let the player
set `I` be finite.  Suppose each player's payoff coordinate is a finite sum of
terms of the following two kinds:

```text
+alpha*1_T,  alpha>=0, i in T,       (join rewards)
-beta *1_R,  beta >=0, i notin R.    (lossless collector charges)   (21.1)
```

The first class contains every clean membership-join indicator.  The second
contains every negative source used by a Quit-zero collector: forcing `i` to
Quit can never create a coalition which excludes `i`, so these terms are
pointwise lossless under that deviation.

**Proposition 20 (ordinary mathematics; grand-coalition sink).**  Every
reward table of the form `(21.1)` has the pure date-zero grand-coalition
profile as an exact terminal Nash profile.  Therefore no finite completion
using only lossless join indicators and lossless negative collector sources
can have a positive terminal exploitability gap.

**Proof.**  At the grand coalition `I`, every negative collector indicator is
zero, while every positive join indicator contributes either zero or a
nonnegative amount.  Hence player `i`'s prescribed payoff is nonnegative.

If `i` changes to Continue at date zero, the other players still absorb
immediately as `I\{i}`.  No positive target belonging to player `i` can equal
that coalition, because every such target contains `i`.  Negative collector
targets may be hit, so the deviating payoff is at most zero.  Thus continuing
cannot improve.  Quitting at date zero leaves the prescribed coalition
unchanged, and any later behavior is irrelevant after date-zero absorption.
This covers every unilateral behavioral replacement.  QED.

Proposition 20 is the exact architecture-level kill criterion reached by the
collector route.  Adding more outsiders, longer inclusion chains, or more
negative singleton charges does not help: the finite grand coalition remains
the literal sink.  Escaping `(21.1)` requires at least one compensated leave
term, namely either a positive reward on a coalition excluding its owner or a
negative reward on a coalition containing its owner.  Proposition 18 shows
that this creates a reverse-edge payment, and Proposition 19 shows that the
minimal two-player payment cycle has no strict coefficient surplus.

The only surviving negative construction inside this thesis is therefore a
nonlocal compensated leave ledger with a strict aggregate surplus not
repaid around its polarity cycle.  The amplified core ledger is the one known
source of such surplus, but its absent-player rewards conflict with the
profile-selected join deviations needed to enter the core.  The next check is
whether summing two or more core-member Never inequalities can pay one
auxiliary grand-coalition exit while the joining player uses a separate
coordinate.  If every such finite construction reduces to a unit-gain cycle,
the present negative thesis meets its stated architecture kill criterion and
should pivot to a different semantic endpoint.

## 22. The first aggregate leave surplus has an exact stationary escape

Proposition 20 says a genuine cap must add positive rewards on coalitions
excluding their owner.  The smallest symmetric attempt uses three players and
lets every member cap the grand coalition through its opposite pair while
collecting one predecessor singleton.

Index players cyclically and let `pred(i)` be the preceding player.  Fix
`K,L>0` and define the complete payoff table coordinatewise by

```text
r(U)_i = L   if U=I\{i},
          -K  if U={pred(i)},
           0  otherwise.                            (22.1)
```

At the pure grand coalition, every player gains `L` by switching to Never, so
the grand sink from Proposition 20 is genuinely destroyed.  Quit-zero by
player `i` also gains `K` on the predecessor-singleton source but loses `L`
on the opposite-pair source, exactly the intended aggregate compensation.

**Proposition 21 (ordinary mathematics; exact stationary escape).**  For
every `K,L>0`, table `(22.1)` has an exact unrestricted-behavior terminal Nash
profile.  Every player uses the stationary Quit hazard

```text
x=K/(K+L),                                           (22.2)
```

and the terminal payoff is zero.

**Proof.**  Fix player `i` and keep both opponent hazards equal to `x`.  If
`i` is forced to Quit at any live date, the absorbing coalition contains `i`,
so `(22.1)` pays zero.  If `i` Continues for one date, the two opponents both
Quit with probability `x^2`, only `pred(i)` Quits with probability
`x(1-x)`, and every other one-date outcome has coordinate payoff zero.
Therefore the one-date exit contribution is

```text
x^2 L-x(1-x)K=0                                     (22.3)
```

by `(22.2)`.  Repeated joint continuation has factor `(1-x)^2<1`, so the
prescribed terminal payoff is zero.

More explicitly, for every deterministic finite Quit time, every earlier
opponent-only date contributes `(22.3)`, and forced Quit at the selected date
contributes zero.  Never gives the convergent geometric sum of the same zero
one-date contribution.  Thus every pure Quit time, including Never, pays
exactly zero.  The checked pure-time extremality principle then implies that
every unilateral behavioral deviation pays at most zero.  Since the
prescribed profile pays zero, it is exact terminal Nash.  QED.

This is stronger than the coefficient feasibility in Proposition 19: the
first genuinely nonreversible three-member cap has an explicit product-law
equilibrium for every choice of scales.  The mixing rate is precisely the
ratio that equalizes the positive opposite-pair event and negative predecessor
singleton event, so coefficient amplification merely moves the equilibrium
toward zero or one.

The negative-gadget thesis has now exhausted three nested architectures with
actual witnesses: lossless finite joins/collectors have a pure grand sink;
the minimal paid reverse cycle has a feasible unit-gain ledger; and the first
aggregate three-member repair has an exact fully mixed stationary equilibrium.
The only untested possibility is to couple the aggregate leave rewards to the
disjoint-pair clock inequality so that no common stationary ratio can balance
all cycles.  The concrete kill check is a two-color version of `(22.1)` with
opposite `K/L` ratios on two disjoint triples.  If independent stationary
hazards solve both color equations while respecting the cross-cycle rows,
this clock-toggle negative thesis should be closed and the main route pivoted.

## 23. Two cross-coupled colors still have a fully mixed escape

The final kill check also has an exact positive stationary solution.  Take two
disjoint three-player sets `A,B`.  Choose arbitrary maps

```text
phi:A->B,      psi:B->A
```

(bijections may be used, but are not needed).  Fix positive coefficients
`K_A,L_A,K_B,L_B`.  Define

```text
r(U)_i = L_A   if U=A\{i},
          -K_A  if U={phi(i)},
           0    otherwise,                         for i in A,

r(U)_j = L_B   if U=B\{j},
          -K_B  if U={psi(j)},
           0    otherwise,                         for j in B.       (23.1)
```

This is the literal two-color version of `(22.1)`: every positive leave reward
uses the other two players of the same color, while every collector loss is
paid by an exact singleton of the opposite color.  Opposite coefficient
ratios were the last proposed way to prevent one common stationary balance.

**Proposition 22 (ordinary mathematics; two-color stationary escape).**  For
every positive choice of the four coefficients, `(23.1)` has an exact
unrestricted-behavior terminal Nash profile with payoff zero.  All players in
`A` use one stationary hazard `x in (0,1)`, and all players in `B` use one
stationary hazard `y in (0,1)`.

Put

```text
alpha=K_A/L_A,       beta=K_B/L_B,
u=(alpha^2*beta)^(1/3),
v=(alpha*beta^2)^(1/3),
x=u/(1+u),           y=v/(1+v).                    (23.2)
```

**Proof.**  The positive numbers in `(23.2)` satisfy

```text
u^2=alpha*v,         v^2=beta*u.                   (23.3)
```

Fix `i in A` and force it to Continue for one live date.  Its positive row is
realized exactly when the other two `A` players Quit and all three `B` players
Continue; its negative row is realized exactly when the other two `A` players
Continue, `phi(i)` Quits, and the remaining two `B` players Continue.  Thus
the one-date exit contribution is

```text
L_A*x^2*(1-y)^3
  -K_A*(1-x)^2*y*(1-y)^2.                          (23.4)
```

After division by the positive factor
`L_A*(1-x)^2*(1-y)^2`, equation `(23.4)=0` is exactly

```text
u^2*(1-y)=alpha*y,
```

equivalently `u^2=alpha*v`, the first equality in `(23.3)`.  The calculation
for every `j in B` is symmetric and reduces to `v^2=beta*u`.

If any player is forced to Quit, the absorbing coalition contains that
player, while both nonzero rows in its coordinate exclude it.  Its forced-Quit
payoff is therefore zero.  For a deviating player in `A`, joint continuation
of its five opponents has factor `(1-x)^2*(1-y)^3<1`; for a deviating player
in `B`, the factor is `(1-x)^3*(1-y)^2<1`.  (The prescribed all-player
continuation factor is `(1-x)^3*(1-y)^3`.)

For every finite pure Quit time, all earlier opponent-only date contributions
are zero by `(23.4)` and its `B` analogue, and the forced-Quit date contributes
zero.  Never is the convergent geometric sum of the same zero contributions.
Every pure time thus pays zero, as does the prescribed stationary profile.
Pure-time extremality gives exact Nash against every behavioral replacement.
QED.

This realizes the notebook's stated kill criterion for the finite
clock-toggle architecture.  Cross-coloring does not make the stationary
balance equations inconsistent: in odds coordinates they are the positive
monomial system `(23.3)`, which always has the explicit solution `(23.2)`.
Longer finite color cycles have the same logarithmic-linear form and therefore
cannot be expected to remove the escape without a genuinely nonmonomial
semantic constraint.

The conclusion is deliberately limited.  It does not prove that every finite
reward completion has a stationary equilibrium and does not settle the
finite-quitting conjecture.  It proves that the particular all-behavior
negative-gap thesis developed here has reached its kill criterion: lossless
collectors, membership indicators, paid reverse edges, aggregate leave
surplus, and opposite finite color ratios all retain an exact pure or fully
mixed terminal Nash escape.  Further work should pivot to a positive semantic
producer rather than add another finite toggle layer.
