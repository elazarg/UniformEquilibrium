# Cyclic four-player gadgets: a stationary boundary escape

Author: `CODEX_EULER`

Status: `PAUSED AT REVIEWED CHECKPOINT; PROPOSITIONS 16, 20, 22 REVIEWED VALID; SECTIONS 23--30 REMAIN INTERNAL`

Independent review: [`../feedback/CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE__BY_CODEX_CEDAR.md`](../feedback/CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE__BY_CODEX_CEDAR.md).
Section 8 review: [`../feedback/CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE__BY_CODEX_CEDAR__ROUND_2.md`](../feedback/CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE__BY_CODEX_CEDAR__ROUND_2.md).
Sections 9--10 review: [`../feedback/CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE__BY_CODEX_CEDAR__ROUND_3.md`](../feedback/CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE__BY_CODEX_CEDAR__ROUND_3.md).
Open-neighborhood and general-IVT review: [`../feedback/CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE__BY_CODEX_CEDAR__ROUND_4.md`](../feedback/CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE__BY_CODEX_CEDAR__ROUND_4.md).
Pure-orbit and cross-pair review: [`../feedback/CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE__BY_CODEX_CEDAR__ROUND_6.md`](../feedback/CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE__BY_CODEX_CEDAR__ROUND_6.md).
Single-owner review: [`../feedback/CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE__BY_CODEX_CEDAR__ROUND_7.md`](../feedback/CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE__BY_CODEX_CEDAR__ROUND_7.md).
Single-pair and three-active review: [`../feedback/CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE__BY_CODEX_CEDAR__ROUND_8.md`](../feedback/CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE__BY_CODEX_CEDAR__ROUND_8.md).
Projective stationary-boundary review: [`../feedback/CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE__BY_CODEX_CEDAR__ROUND_9.md`](../feedback/CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE__BY_CODEX_CEDAR__ROUND_9.md).
Common-clock boundary review: [`../feedback/CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE__BY_CODEX_CEDAR__ROUND_10.md`](../feedback/CODEX_EULER__CYCLIC_STATIONARY_BOUNDARY_ESCAPE__BY_CODEX_CEDAR__ROUND_10.md).

## Current best attempt

A natural minimal version of the incentive gadget has only the four clock
players and makes the two designated disjoint pairs symmetric by a cyclic
relabeling. For this class, three scalar boundary comparisons already force
an ordinary equilibrium escape.

Let the players be `Z/4Z`, let `rho(i)=i+1`, and assume cyclic equivariance:

```text
r_(rho i)(rho S) = r_i(S)
```

for every nonempty coalition `S`. Define, in player `0`'s coordinate,

```text
d = r_0({0}),
m = (r_0({1}) + r_0({2}) + r_0({3}))/3,
g = r_0({0,1,2,3}),
e = r_0({1,2,3}).
```

**Boundary-escape theorem.** If at least one of

```text
d <= 0,        g >= e,        d >= m
```

holds, then the game has terminal `epsilon`-Nash profiles against unrestricted
behavioral deviations for every `epsilon>0`. More precisely:

- `d<=0` gives the exact all-Never equilibrium;
- `g>=e` gives the exact all-Quit equilibrium;
- if `d>m` and `g<e`, a common strictly interior stationary hazard gives an
  exact terminal Nash equilibrium; and
- if `d=m` and `g<e`, common stationary hazards tending to zero have
  exploitability tending to zero and payoff tending to the fixed vector
  `(d,d,d,d)`.

Thus a cyclically equivariant four-clock counterexample gadget with no
calibrators must lie in the strict residual chamber

```text
0 < d < m,        g < e.                              (R)
```

This does not settle that residual chamber and does not cover extra
calibrator orbits. It is a universal stationary escape theorem for a precise
minimal-gadget class, not a proposed all-game theorem.

The rational example in Section 6 has no pure sure-exit coalition, but it
falls under the strict stationary arm and has an exact fully mixed terminal
Nash profile. It is an exact boundary test showing that the theorem does more
than rediscover a pure sink.

**New reviewed checkpoint (Section 8).**  The canonical Solan--Vieille
table lies in the unresolved strict chamber, but its alternating cross-pair
equilibrium has a nonsingular four-variable active-gap Jacobian.  The
implicit-function theorem therefore gives a full-dimensional open
neighborhood of complete, not necessarily cyclic, four-player reward tables
with exact two-period terminal Nash profiles.  The Jacobian and a rational
interval determinant certificate are written out explicitly.  This new
theorem has survived an independent exact recomputation.

**New reviewed checkpoint (Sections 9--10).**  The natural pair-local architecture
admits a complete pure-equilibrium classification.  If every player's reward
depends only on whether that player and its designated partner belong to the
first quitter coalition, then one of all-Never, all-Quit, a pair transversal,
or a singleton is an exact terminal equilibrium.  This strictly strengthens
the earlier geometric escape for the synchronization-penalty subfamily and
uses all fifteen coalition rows.  A second rational table strictly eliminates
every deterministic first-outcome type but still has an exact alternating-pair
equilibrium.  Both results passed independent falsification review.  The open-
neighborhood addendum and general IVT criterion also passed a separate exact
review.

**New reviewed checkpoint (Sections 14--15).**  In the full eleven-parameter
opposite-pair-count class, all six deterministic outcome orbits are now
classified exactly.  Removing those pure sinks and the common-stationary
boundary leaves two strict join chambers.  Each chamber has an unavoidable
active two-period root: Proposition 7 for designated pairs and Proposition 10
for cross pairs.  A complete rational table is exhibited with no pure or
common-stationary equilibrium but an exact cross-pair periodic equilibrium
whose two target designated-pair atoms are zero.  The only unresolved part of
this architecture is now the inactive-player inequality at those roots; the
note does not claim the two support words are exhaustive when that inequality
fails.

**New reviewed checkpoint (Section 22).**  The vanishing stationary boundary
is now support-complete.  In the positive-surplus chamber, normalized rare
stationary hazards must solve an explicit four-coordinate projective LCP; a
solution exists exactly when both the partner and opposite singleton margins
are nonnegative.  Hence neither strict mixed-sign chamber admits even a
vanishing-error stationary escape with total hazard tending to zero.  The
classification and its approximate-Nash consequence passed independent
review.

**Current nonstationary attack (Sections 23--30).**  The same
mixed-sign chamber admits no anchored cyclic singleton schedule of any finite
period, because symmetric forward/reverse margins force every owner step to
be zero.  More generally, repeating any product-root word whose *total*
period hazard tends to zero homogenizes to the same forbidden projective LCP,
even if the word length diverges.  The surviving regime must therefore have
order-one absorption per changing macroblock or be genuinely nonperiodic.  In
the atomless rank limit, Quit-now and Never deviations force a fixed bias in
whether the first two quitters are designated partners; common/exchangeable
clocks cannot supply it.  A reviewed discrete iid version gives a quantitative
fixed Never gain whenever the common first outcome becomes diffuse and
absorbing, and a reviewed chronological version forces every exact common
Nash clock to recur at a macroscopic hazard.  Exact rational Section 30 data
shows that asymmetric independent clocks can satisfy all Quit-now/Never rank
inequalities while retaining a large intermediate-time deviation.  The live
problem is therefore the full pure-time payoff curve for asymmetric changing
clocks, not another endpoint or finite-support checklist.

## 1. Exact question and scope

The parent question is
[`../questions/INCENTIVE_GADGET.md`](../questions/INCENTIVE_GADGET.md). It
asks for a rational quitting table with a fixed all-behavior terminal
exploitability gap, obtained by forcing two incompatible pair atoms, or an
equilibrium/escape theorem excluding a precisely proposed finite-gadget
class.

This note studies the smallest symmetry-compatible class:

- exactly four clock players and no auxiliary calibrators;
- arbitrary rational rewards on all fifteen nonempty coalitions; and
- invariance only under the regular cyclic action, not under every player
  permutation.

The designated pair atoms may be taken as `{0,2}` and `{1,3}`. The generator
`rho` exchanges them, so cyclic equivariance is the weakest obvious
transitive symmetry making their incentive roles identical.

The conclusion concerns ordinary independent behavioral stopping laws and
unrestricted unilateral deviations. Stationarity is used only to construct
the escaping equilibrium profile; deviations are not restricted to
stationary strategies.

## 2. Sources and prior-work audit

The following exact declarations were inspected:

- `sSup_range_quittingTerminalPayoff_update_eq_pureTime`
  (`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`),
  which reduces a fixed-opponent behavioral best response to deterministic
  Quit times, including `Never`;
- `isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
  `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
  (`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`), which are
  checked all-behavior consumers for an interior stationary root; and
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean`),
  which is the checked fixed-target consumer for the vanishing-hazard boundary
  case.

The nearest existing special classes are different:

- `quittingGame_exists_uniformEquilibriumPayoff_of_permutationSymmetric`
  (`UniformEquilibrium/Quitting/Classification/SymmetricQuittingGame.lean`)
  assumes invariance under every permutation, which is substantially stronger
  than cyclic equivariance;
- the blocker-switch and conditional-face-gap producers use playerwise
  opponent-coordinate face signs, not the one-dimensional equivariant
  boundary comparison proved here; and
- the cyclic singleton producer uses a scheduled owner word and conditions on
  the singleton envy polynomial and every tail. The present profile has all
  four players mixing simultaneously and uses every coalition row.

There is also a directly relevant **weaker conclusion** already checked in
`Quitting/Classification/Circulant/Trichotomy.lean`:
`exists_uniformEquilibriumPayoff_of_circulant_surplus_nonpos` resolves every
circulant normalized singleton matrix whose margin surplus is nonpositive.
For the present cyclic table that surplus is

```text
sum_j (r_0({j})-d) = 3(m-d).
```

Thus the arm `d>=m` was already known to have *some* uniform-equilibrium
payoff.  The new content here is the explicit ordinary terminal profile:
either all Quit, a common interior stationary root, or a common vanishing-
hazard family, with unrestricted terminal regret computed exactly.  This also
identifies the residual chamber `d<m` with the positive-surplus side of the
checked LCP gate.

The finite-watchdog, geometric-security, hard-claimant, sure-exit-core,
indicator-flow, and clock-inequality notes were treated as constraints. This
argument uses none of those architectures. A narrow search found no prior
statement of this explicit four-scalar stationary boundary escape.

## 3. Exact stationary reduction against unrestricted deviations

Fix `h in (0,1]` and let every player Quit at every live date with probability
`h`, independently. By cyclic equivariance, all players face relabelings of
the same stationary opponent environment. It is enough to work in player
`0`'s coordinate.

Let `Q(h)` be player `0`'s payoff from pure Quit at the current live date
against the other three common-`h` roots. Let `W(h)` be the unconditional
one-date payoff contribution from nonempty opponent-only absorption when
player `0` Continues. Put

```text
c(h) = (1-h)^3,
N(h) = W(h)/(1-c(h)).
```

Here `N(h)` is the payoff from pure Never against the stationary opponents.
Both `Q` and `W` are polynomials in `h`, and `1-c(h)>0` for `h>0`.

**Lemma 1 (pure-time segment).** For every finite deterministic Quit time
`t`, player `0`'s payoff is

```text
V(t;h) = (1-c(h)^t) N(h) + c(h)^t Q(h).             (3.1)
```

Pure Never pays `N(h)`. Consequently the unrestricted behavioral best-response
value is

```text
max(Q(h),N(h)).                                      (3.2)
```

**Proof.** At each date strictly before `t`, opponent absorption contributes
`W(h)` and all-opponent continuation has probability `c(h)`. At date `t`,
survival contributes `c(h)^t Q(h)`. Summing the geometric series gives
`(3.1)`. Every behavioral stopping law is a probability mixture of its pure
Quit time, including Never; equivalently one may invoke the checked pure-time
extremality theorem. Since `(3.1)` lies on the segment between `Q(h)` and
`N(h)`, `(3.2)` follows. QED.

Let `U(h)` be the prescribed payoff under the common stationary profile.
One-stage conditioning gives

```text
U(h) = h Q(h) + (1-h)(W(h)+c(h)U(h)).
```

Since

```text
1-(1-h)c(h) = h+(1-h)(1-c(h)),
```

we obtain

```text
U(h) = lambda(h) Q(h) + (1-lambda(h)) N(h),

lambda(h) = h/[h+(1-h)(1-c(h))] in (0,1].          (3.3)
```

Therefore the exact unrestricted terminal exploitability of the common
stationary profile satisfies

```text
0 <= max(Q(h),N(h))-U(h) <= |Q(h)-N(h)|.            (3.4)
```

If `Q(h)=N(h)`, every pure Quit time and Never has the same payoff. The common
stationary profile is then exact Nash against every behavioral replacement,
not merely against stationary deviations.

## 4. The two boundary values

Define

```text
D(h)=Q(h)-N(h),       0<h<=1.
```

It extends continuously to `h=0`. Indeed,

```text
Q(h) -> d.
```

Conditional on at least one of three common-`h` opponents Quitting in the
current date, the Quit set converges as `h->0` to the uniform law on the three
opponent singletons. Hence

```text
N(h) -> m,
D(0) = d-m.                                           (4.1)
```

At `h=1`, all three opponents Quit immediately, so

```text
Q(1)=g,
N(1)=e,
D(1)=g-e.                                           (4.2)
```

These limits use every relevant tie correctly: `Q` includes player `0` in
the current coalition, while `N` excludes it.

## 5. Boundary-escape theorem

**Theorem 2 (cyclic stationary boundary escape; ordinary mathematics).** Let
`r` be any real cyclically equivariant four-player quitting table.

1. If `d<=0`, all-Never is an exact terminal Nash profile.
2. If `g>=e`, all-Quit at date zero is an exact terminal Nash profile.
3. If `d>m` and `g<e`, there is `h_* in (0,1)` for which the common stationary
   profile is an exact unrestricted-behavior terminal Nash profile.
4. If `d=m` and `g<e`, the common stationary profiles with `h->0+` have
   terminal exploitability tending to zero and payoff tending to
   `(d,d,d,d)`.

Consequently, if `d<=0` or `g>=e` or `d>=m`, the game has terminal
`epsilon`-Nash profiles for every `epsilon>0` and hence cannot have a fixed
positive terminal exploitability gap.

**Proof.**

1. At all-Never the prescribed payoff is zero. Every finite pure Quit time
   terminates alone and pays `d<=0`; Never pays zero. Cyclic equivariance makes
   the same statement true for every player.
2. At all-Quit the prescribed terminal coalition is the grand coalition and
   pays `g` to each player. If one player Continues, the other three still
   absorb immediately and pay it `e`; any later behavior is irrelevant. Thus
   `g>=e` is exactly the unilateral inequality.
3. Equations `(4.1)`--`(4.2)` give `D(0)>0>D(1)`. Continuity and the
   intermediate value theorem give `h_* in (0,1)` with `D(h_*)=0`. Lemma 1
   and `(3.3)` show that the stationary profile and every unilateral
   behavioral replacement have the same value.
4. Continuity gives `D(h)->0`, so `(3.4)` gives vanishing exploitability.
   Under the common root, terminal absorption is almost sure and the first
   coalition distribution converges to the uniform law on the four
   singletons. Player `0`'s payoff therefore tends to

   ```text
   (d+3m)/4=d.
   ```

   Equivariance gives the same limit for every coordinate. QED.

In case 3 the checked contracting stationary endpoint compiler applies
directly. In case 4 the checked approximate-target terminal consumer applies
with target `(d,d,d,d)`. These observations place the ordinary calculation at
the project's full uniform-payoff endpoint, but no Lean adapter is claimed
here.

**Corollary 3 (necessary chamber for a cyclic minimal counterexample).** A
cyclically equivariant four-clock table with a fixed positive all-behavior
terminal exploitability gap must satisfy

```text
0 < d < m,       g < e.                              (5.1)
```

This is only a necessary condition. No existence or nonexistence statement is
made inside `(5.1)`.

## 6. Exact rational stress table with no pure sure-exit set

This example checks that the stationary arm is not merely hiding a pure exit.
For a subset `S` of `Z/4Z`, write `S-i={j-i mod 4:j in S}`. Define the table
by

```text
r_i(S)=f(S-i),
```

where the complete nonempty representative table is

```text
A                  f(A)
{0}                 1
{1}                 0
{0,1}               1
{2}                -1
{0,2}               0
{1,2}               2
{0,1,2}            -1
{3}                 0
{0,3}               0
{1,3}              -2
{0,1,3}             1
{2,3}               1
{0,2,3}             2
{1,2,3}             1
{0,1,2,3}          -2.
```

All rewards are integers and the definition is cyclically equivariant. Its
boundary data are

```text
d=1,       m=-1/3,       g=-2,       e=1.
```

Thus Theorem 2 gives an interior exact stationary equilibrium.

For this table the stationary functions are

```text
Q(h)=1-2h+3h^2-4h^3,
W(h)=-h+3h^2-h^3,
1-c(h)=3h-3h^2+h^3.
```

The sign of `D(h)` is the sign of

```text
P(h)=(1-c(h))Q(h)-W(h)
    =h(4-12h+17h^2-23h^3+15h^4-4h^5).
```

The parenthesized polynomial is `3/16>0` at `h=1/2` and
`-9572/759375<0` at `h=8/15`, so an exact stationary root lies in
`(1/2,8/15)`.

There is no pure sure-exit coalition. By cyclic rotation it is enough to
check one representative of each coalition orbit:

- at the empty coalition, player `0` gains `0 -> 1` by Quitting;
- at `{0}`, outsider `2` gains `-1 -> 0` by joining;
- at adjacent pair `{0,1}`, outsider `2` gains `1 -> 2` by joining;
- at opposite pair `{0,2}`, outsider `1` gains `-2 -> 1` by joining;
- at triple `{0,1,2}`, member `0` gains `-1 -> 2` by leaving; and
- at the grand coalition, any member gains `-2 -> 1` by leaving.

Thus the exact stationary escape is essential for this table. It is also not
cardinally or fully permutation symmetric: against singleton `{0}`, players
`1` and `2` receive respectively `0` and `-1`.

This example was first located by a coarse exact-formula search over cyclic
integer tables and then reduced to the displayed rational proof. The search
is evidence only; the polynomial and coalition calculations above are the
proof.

## 7. Relation to the independent-clock gadget and next question

At a common stationary hazard, the two designated opposite-pair atoms have
equal probabilities

```text
a=b=h^2(1-h)^2/[1-(1-h)^4].
```

Every other coalition and Never belongs to `ell=1-a-b`, and the reviewed
clock inequality holds automatically. Since the profile produced by Theorem
2 is an exact or arbitrarily accurate terminal Nash profile, no table in the
escape class can force the inconsistent inequalities requested by
`INCENTIVE_GADGET.md`.

The strict chamber `(5.1)` is the only remaining cyclic four-clock case not
dispatched by this argument. It has a clear interpretation:

- all-Never is unstable because solo quitting pays positively;
- all-Quit is unstable because a member prefers to leave the grand coalition;
  and
- under rare symmetric singleton absorption, a player prefers being an
  outsider on average to becoming the solo quitter.

The next concrete task is to test whether every table in `(5.1)` admits a
diffuse cyclic singleton schedule, or to find an exact rational table in this
chamber that defeats both common-stationary hazards and the checked balanced
singleton compiler. That is a smaller, nonduplicative search space. A result
there would either extend the equilibrium escape to the entire cyclic minimal
gadget class or produce the first credible symmetric seed for the actual
negative gadget.

No Lean file is proposed here.  The later sections record the independently
reviewed resolution of this checkpoint around the canonical boundary table.

## 8. A full-dimensional open cross-block escape around the hard chamber

The Solan--Vieille boundary table lies in the strict chamber `(R)`, so common
stationary hazards do not resolve it.  Nevertheless its exact alternating
cross-pair equilibrium is **nondegenerate**.  The implicit-function theorem
therefore makes this escape stable under arbitrary small perturbations of all
sixty payoff entries, without retaining cyclic symmetry.

This gives a second precise gadget class excluded by an ordinary exact
equilibrium theorem.

### 8.1 Two-phase root equations

Let `r*` be `SolanVieilleBoundary.boundaryReward`.  At phase `A`, only players
`0,2` are active, with continuation probabilities `x0,x2`; at phase `B`, only
players `1,3` are active, with continuation probabilities `x1,x3`.  For a
nearby reward table `r`, write `A_r(x0,x2)` and `B_r(x1,x3)` for the vectors
of unconditional absorbing payoff contributions in the two product roots.
Their joint Continue probabilities are

```text
cA=x0*x2,       cB=x1*x3.
```

Whenever `cA*cB<1`, the literal two-period continuation values are uniquely

```text
uA = (A_r+cA*B_r)/(1-cA*cB),
uB = (B_r+cB*A_r)/(1-cA*cB).                         (8.1)
```

Let

```text
F(r,x0,x2,x1,x3)
```

be the four active Quit-minus-Continue endpoint differences, in the order
`(A,0),(A,2),(B,1),(B,3)`, computed against the opposite-phase value in
`(8.1)`.  This is a rational, hence smooth, map on the open contracting
region.

For `r=r*`, put

```text
a=periodTwoParameter,
b=periodTwoSecondary.
```

The checked active identities in
`FourPlayerPairedSingletonPeriodTwo.lean` give

```text
F(r*,a,b,a,b)=0.                                     (8.2)
```

The same file proves

```text
373/500 < a < 747/1000,
73/100  < b < 74/100.                                (8.3)
```

### 8.2 Exact Jacobian audit

Direct differentiation of `(8.1)` and the four endpoint differences, followed
by the two active identities, gives the Jacobian in variable order
`(x0,x2,x1,x3)`:

```text
J = [ 0      alpha   beta    gamma ]
    [ delta  0       delta   epsilon]
    [ beta   gamma   0       alpha ]
    [ delta  epsilon delta   0      ].               (8.4)
```

Writing `Delta=(1-a^2*b^2)^2`, its five entries are

```text
alpha   = (a^2*b+2*a*b+a-3*b-1)/Delta,
beta    = (-3*a*b^4-a*b^3+a*b^2+2*b^2+b)/Delta,
gamma   = (a^3*b^2-a^2*b^2+a^2*b+2*a*b-3*b)/Delta,
delta   = a*(b^2+3*b-4)/Delta,
epsilon = a^2*(3+b-4*a^2*b)/Delta.                   (8.5)
```

All diagonal zeros in `(8.4)` use `(8.2)`; they are not identities away from
the selected active root.

Exact rational interval arithmetic from `(8.3)` gives the deliberately coarse
bounds

```text
-21/10 < alpha < -9/5,
 12/5  < beta  < 14/5,
 -9/5  < gamma < -7/5,
 -2    < delta < -9/5,
 23/10 < epsilon < 5/2.                              (8.6)
```

For completeness, the symmetry/antisymmetry decomposition of `(8.4)` has
determinants

```text
det_sym  = beta*epsilon-2*delta*(alpha+gamma),
det_anti = beta*epsilon.
```

The second is positive.  From `(8.6)`,

```text
beta*epsilon < 7,
2*delta*(alpha+gamma) > 2*(9/5)*(16/5)=288/25>11,
```

so `det_sym<0`.  Consequently

```text
det J = det_sym*det_anti != 0.                        (8.7)
```

This is a hand-checkable nondegeneracy certificate; the decimal Jacobian is
not being used as evidence.

### 8.3 Open-neighborhood theorem

**Theorem 4 (cross-block structural stability; reviewed ordinary
mathematics).**  There is a Euclidean-open neighborhood `O` of `r*` in the
space of complete four-player reward tables such that every `r in O` has an
exact terminal Nash profile against unrestricted behavioral deviations.  The
profile is two-periodic, with active supports `{0,2}` and `{1,3}` in the two
phases and all four active continuation probabilities strictly between zero
and one.

**Proof.**  By `(8.7)` and the finite-dimensional implicit-function theorem,
after shrinking around `r*` there is a continuous solution

```text
x(r)=(x0(r),x2(r),x1(r),x3(r))
```

of `F(r,x(r))=0`.  Since `(a,b,a,b)` is interior, all four continuation
probabilities remain in `(0,1)` and the two-period roots remain contracting.

At `r*`, every inactive endpoint difference is strictly negative:
`inactivePairGap_neg` and `inactivePrimaryGap_neg` in
`FourPlayerPairedSingletonPeriodTwo.lean`.  Endpoint differences and the
values `(8.1)` are continuous in `(r,x)`, so after shrinking `O` again all
inactive players still strictly prefer Continue.  Active players are exactly
indifferent by `F=0`.  Thus each phase root is exact endpoint Nash against
the next phase value, and `(8.1)` supplies the exact Bellman recursions.

The two-root cycle absorbs with positive probability in every period.  More
importantly for unrestricted deviations, deleting any one player still leaves
at least one opponent with a strictly positive Quit probability in the
two-phase period.  Thus every player-deleted survival product also contracts.
Unrolling the endpoint inequalities controls every deterministic Quit time,
including Never; pure-time extremality then controls every behavioral
deviation.  Equivalently, this is the ordinary-mathematics content of the checked
`periodTwoBlock_isQuittingCyclicContinuationBlock` plus
`periodTwoProfile_isExactTerminalNash` compilation, now applied to the nearby
data.  Hence the periodic profile is exact terminal Nash. QED.

Because rational tables are dense, `O` contains complete rational reward
tables.  None of them can be an incentive gadget with a fixed positive
terminal exploitability gap.  This does not settle tables outside `O`, but it
shows that the canonical strict-chamber paired-clock architecture has an open,
full-dimensional equilibrium escape; breaking cyclic symmetry by a small
rational perturbation does not remove it.

### 8.4 Review disposition

The Round 2 review independently recomputed `(8.4)--(8.6)`, including the
full dependence of the phase values on all four continuation probabilities,
and confirmed the IFT argument in the full reward-table space.  It emphasized
that player-deleted contraction, not joint absorption alone, is the
load-bearing all-behavior hypothesis; that condition is explicit in the proof
above and holds robustly for the paired supports.

## 9. Complete pure escape for pair-local participation tables

The most direct four-clock implementation assigns each clock a designated
partner and makes its payoff depend only on whether it and that partner occur
in the first coalition.  The previously reviewed synchronization-penalty
example found a stationary geometric equilibrium for one such table.  In
fact, the entire four-parameter class has a pure equilibrium.  No timing
calculation is needed.

Let the players be partitioned into two designated pairs, and write `p(i)` for
the partner of `i`.  Fix arbitrary real constants `A,B,C,D`.  For every
nonempty coalition `S`, define the complete reward table by

```text
             i notin S       i in S
p(i) notin S      A             B
p(i) in S         C             D.                  (9.1)
```

Thus `A` is the payoff when the other designated pair stops first, `B` is the
payoff from participating without one's partner, `C` is the payoff from the
partner participating without oneself, and `D` is the payoff when both
partners participate.  Formula `(9.1)` specifies every player's payoff on
all fifteen nonempty coalitions.  As usual, Never pays zero.

**Theorem 5 (pair-local pure-equilibrium classification; ordinary mathematics,
awaiting review).**  Every table `(9.1)` has an exact terminal Nash profile
against unrestricted behavioral deviations.  More explicitly, at least one
of the following profiles works:

1. if `B<=0`, everyone Never quits;
2. if `B>=0` and `D>=C`, everyone Quits at date zero;
3. if `B>=0`, `C>=D`, and `B>=A`, any transversal containing exactly one
   member of each designated pair Quits at date zero;
4. if `B>=0`, `C>=D`, and `A>=B`, any singleton Quits at date zero.

These four regions cover all choices of `A,B,C,D` (ties may be assigned to
either adjacent case).

**Proof.**

In case 1, a unilateral finite stopping time against all-Never produces the
solo payoff `B<=0`, while Never pays zero.  Pure-time extremality therefore
controls every behavioral deviation.

In case 2, the grand coalition terminates at date zero and pays `D` to every
player.  If one player Continues, its partner still Quits and the deviator
receives `C<=D`; later behavior is unreachable.

For case 3, fix a transversal `S` with one member from each designated pair.
Every `i in S` receives `B`.  If it Continues, the other member of `S` still
Quits, but neither `i` nor `p(i)` does, so the deviator receives `A<=B`.
Every `i notin S` has its partner in `S`, receives `C`, and would receive `D`
by joining at date zero, so joining is not profitable because `D<=C`.
The remaining Quitters make all later behavior irrelevant.

For case 4, let only `i` Quit at date zero.  Player `i` receives `B`.  If it
does not Quit at date zero, all opponents Continue forever; any later finite
Quit still pays `B`, while Never pays zero.  Hence `B>=0` makes its prescribed
action optimal among all behavioral stopping laws.  Its partner receives `C`
and would receive `D<=C` by joining.  Each member of the opposite designated
pair receives `A` and would receive `B<=A` by joining.  Since `i` still Quits
at date zero, later behavior of these outsiders is irrelevant.  Thus the
singleton profile is exact Nash.  QED.

The synchronization table from the earlier followup has

```text
A=C=0,       B=E>0,       D=T<0.
```

It lies in case 3, so a cross-pair transversal is already an exact pure
equilibrium; the exact stationary geometric profile is a second escape, not
the simplest one.

This theorem rules out the complete class in which the other designated
pair is payoff-anonymous and only self/partner participation matters.  It
does not cover rewards that distinguish which outsider quits, how many
outsiders quit, or interactions involving calibrators.  Consequently a viable
pair-atom gadget must use at least one such genuinely cross-pair or
calibrator-dependent payoff distinction.

## 10. A rational all-pure-escapes-killed table still has a period-two escape

The first extension beyond Theorem 5 lets a player distinguish how many
members of the opposite designated pair Quit.  That extra information can
eliminate every pure sure-exit coalition without creating a calibrator core.
It still does not produce a terminal gap: the following exact rational table
has a particularly simple two-period equilibrium.

For player `i`, let `p(i)` be its designated partner and let `O_i` be the
opposite designated pair.  Put

```text
k=|S intersect O_i|.
```

Define `r_i(S)` from the membership state of `(i,p(i))` and `k` by

```text
i,p(i) both absent:  A_1=2, A_2=0;
i present alone:     B_0=1, B_1=0, B_2=1;
p(i) present alone:  C_0=0, C_1=1, C_2=1;
i,p(i) both present: D_0=1, D_1=0, D_2=0.          (10.1)
```

Only admissible subscripts occur, so `(10.1)` specifies all four coordinates
on every one of the fifteen nonempty coalitions.  Every reward is rational
and belongs to `{0,1,2}`.

**Lemma 6.1 (every deterministic-clock profile is unstable).**  All-Never and
every profile with a finite first-quitter coalition admit a strict unilateral
improvement.

**Proof.**  A player gains `B_0=1` by quitting alone against all-Never.  Up to
the pair-preserving symmetry, nonempty coalitions have five types:

```text
singleton:             its excluded partner joins,       C_0=0 < D_0=1;
one designated pair:   an opposite outsider joins,       A_2=0 < B_2=1;
one-from-each pair:     a member leaves,                  B_1=0 < A_1=2;
three players:          a full-pair member leaves,        D_1=0 < C_1=1;
grand coalition:        any member leaves,                D_2=0 < C_2=1.
```

If the original first date is positive, the same deviation is made at that
date (joining) or just after it (leaving).  In each row the listed comparison
therefore concerns the literal terminal outcome; it is not only a date-zero
one-shot proxy. QED.

Now alternate phases `X,Y`.  At phase `X`, only the members of the first
designated pair are active; at phase `Y`, only the second pair is active.
Every active player Continues with probability `x` and Quits with probability
`q=1-x`; inactive players Continue surely.

Let `v` be a player's value at the phase where its own pair is active and `w`
its value at the opposite-pair phase.  Direct conditioning under `(10.1)`
gives

```text
v = q + x^2*w,
w = 4*q*x + x^2*v.                                  (10.2)
```

At its active phase, forced Quit pays

```text
x*B_0+q*D_0=1,
```

whereas forced Continue pays `q*C_0+x*w=x*w`.  Therefore active
indifference with `v=1` is equivalent to

```text
x(4*x-3*x^2)=1
<-> (x-1)(3*x^2-x-1)=0.                             (10.3)
```

Let `x` be the unique positive root of

```text
3*x^2-x-1=0,
```

namely `(1+sqrt(13))/6`.  Since the polynomial is negative at `3/4` and
positive at `4/5`,

```text
3/4 < x < 4/5.                                      (10.4)
```

Equations `(10.2)--(10.3)` then give

```text
v=1,       w=4*x-3*x^2=1/x=3*x-1>1.                (10.5)
```

An inactive player who deviates to Quit at the opposite-pair phase receives
`B_0=1` if zero active opponents Quit, `B_1=0` if exactly one Quits, and
`B_2=1` if both Quit.  Its forced-Quit payoff is consequently

```text
x^2+q^2 <= 1 < w.                                   (10.6)
```

Thus inactive players strictly prefer Continue, while active players are
exactly indifferent.

**Theorem 6 (pure-cycle failure and periodic escape; ordinary mathematics,
awaiting review).**  The rational table `(10.1)` has no pure terminal Nash
profile, but the alternating pair profile above is an exact terminal Nash
profile against unrestricted behavioral deviations.

**Proof.**  Lemma 6.1 excludes every deterministic sure-exit profile and
all-Never.  Equations `(10.2)--(10.6)` prove the exact Bellman equalities and
all endpoint-Nash inequalities for the two periodic roots.  Moreover, after
deleting any one player's stopping law, its designated partner still has
positive Quit probability at their active phase, and both members of the
opposite pair have positive Quit probability at the other phase.  Hence every
player-deleted survival product contracts over each two-phase block.
Unrolling the endpoint inequalities controls every pure finite Quit time and
Never; pure-time extremality controls every behavioral stopping law. QED.

The Round 3 review independently checked all fifteen coalition types, the
two value recursions, the inactive gap, and the stronger player-deleted
contraction needed for unrestricted deviations.  It found Theorem 6 valid.

The escape is also nondegenerate.  Let the four active continuation variables
be `(x0,x2,x1,x3)`, in designated-pair phase order, and let `F` be the four
active Quit-minus-Continue gaps after solving the two Bellman vector
equations.  At the symmetric solution `(x,x,x,x)`, direct implicit
differentiation gives

```text
J = [0      alpha  beta   beta ]
    [alpha  0      beta   beta ]
    [beta   beta   0      alpha]
    [beta   beta   alpha  0    ],                    (10.7)

alpha = -1/x-x^3/(1-x^4),
beta  = x*(3*x-2)/(1-x^4).
```

For example, for player `0` the two literal phase values and active gap are

```text
u_X=1-x0+x0*x2*u_Y,
u_Y=2*(x1+x3-2*x1*x3)+x1*x3*u_X,
F_0=1-x2*u_Y.
```

Differentiating these identities yields the first row of `(10.7)`; pair and
phase symmetry give the other rows.

The two within-pair antisymmetric eigenvalues are `-alpha`.  On vectors
constant within each pair, the remaining eigenvalues are
`alpha+2*beta` and `alpha-2*beta`.  Here `alpha<0<beta`, and the selecting
identity `1/x=3*x-1` gives

```text
alpha+2*beta=(3-5*x)/(1-x^4)<0                      (10.8)
```

by `(10.4)`.  Therefore every eigenvalue is nonzero and

```text
det J=alpha^2*(alpha+2*beta)*(alpha-2*beta)>0.       (10.9)
```

**Corollary 6.2 (open mixed-only periodic escape; reviewed ordinary
mathematics).**  There is a full-dimensional Euclidean-open neighborhood
of the complete rational table `(10.1)` such that every table in the
neighborhood has no deterministic-clock terminal Nash profile but does have
an exact two-period terminal Nash profile against unrestricted behavioral
deviations.

**Proof.**  Invertibility `(10.9)` and the implicit-function theorem preserve
the four active equalities with all continuation probabilities interior.
The finitely many inactive endpoint gaps remain strict, and player-deleted
contraction persists.  Hence the all-behavior compilation in Theorem 6 applies
to the nearby periodic roots.  Separately, every one of the finitely many
first-outcome types in Lemma 6.1 has a strict improving toggle at `(10.1)`.
Those inequalities persist after shrinking the reward neighborhood, so every
nearby deterministic-clock profile remains unstable. QED.

Rational tables are dense in this neighborhood.  Thus failure of every pure
clock profile is robust and occurs on nonsymmetric rational tables; it is not
evidence of a positive exploitability gap.

The base table is a direct warning for gadget searches: even a complete rational
reward cycle that strictly kills all sixteen pure first-outcome types (the
fifteen nonempty coalitions and Never) can hide a
small exact periodic equilibrium.  Unlike the local perturbation theorem of
Section 8, the table was designed from the desired pure-deviation polarity and
the periodic escape was solved afterward.  It does not show that all
opposite-pair-sensitive tables have such an escape.

## 11. A general alternating-pair escape criterion

The mechanism in Section 10 is not isolated.  Consider the full eleven-
parameter opposite-pair-count class

```text
(A_1,A_2),
(B_0,B_1,B_2),
(C_0,C_1,C_2),
(D_0,D_1,D_2),                                  (11.1)
```

with the same interpretation as `(10.1)`.  The alternating-pair active
equations see only `A_1,A_2,B_0,C_0,D_0`; the remaining cells enter the
inactive-player inequality.

For an active Continue probability `x in (0,1)`, put `q=1-x` and

```text
Q(x)=x*B_0+q*D_0,

P(x)=(1+x+x^2)*Q(x)-C_0-2*x^2*A_1-x*q*A_2.       (11.2)
```

If `v` is the value at a player's active-pair phase and `w` at its
opposite-pair phase, the exact recursions are

```text
v=q*x*B_0+x*q*C_0+q^2*D_0+x^2*w,
w=2*q*x*A_1+q^2*A_2+x^2*v.                        (11.3)
```

Active indifference is `v=Q(x)=q*C_0+x*w`.  Substitution in `(11.3)` is
equivalent to `P(x)=0`.

**Proposition 7 (alternating-pair IVT producer; reviewed ordinary
mathematics).**  Suppose

```text
D_0>C_0,
3*B_0<C_0+2*A_1.                                  (11.4)
```

Then `P` has a root `xStar in (0,1)`.  If at one such root

```text
xStar^2*B_0+2*xStar*(1-xStar)*B_1+(1-xStar)^2*B_2
  <= [Q(xStar)-(1-xStar)*C_0]/xStar,               (11.5)
```

the alternating designated-pair profile with active Continue probability
`xStar` is an exact terminal Nash profile against unrestricted behavioral
deviations.

**Proof.**  The endpoint signs are

```text
P(0)=D_0-C_0>0,
P(1)=3*B_0-C_0-2*A_1<0.
```

Continuity gives `xStar in (0,1)` with `P(xStar)=0`.  Equations `(11.2)--(11.3)`
then give active indifference with

```text
v=Q(xStar),
w=[Q(xStar)-(1-xStar)*C_0]/xStar.
```

At the opposite-pair phase, an inactive player's forced-Quit payoff is the
left side of `(11.5)`: zero, one, or two active opponents Quit with the
binomial probabilities displayed there, producing `B_0,B_1,B_2`.
Inequality `(11.5)` is therefore exactly the inactive endpoint-Nash clause.
Both active probabilities are positive, so every player-deleted survival
product contracts over the two-phase block.  Unrolling and pure-time
extremality give unrestricted behavioral optimality. QED.

The two signs in `(11.4)` are structurally meaningful.  The first is exactly
the strict partner-joining instability of a singleton.  The second says that
the rare common-stationary boundary points into the residual chamber because
the solo payoff `B_0` is below the average of the partner singleton `C_0` and
the two opposite singletons `A_1`.  Once both signs hold, the active periodic
root is unavoidable.  A prospective gadget in this symmetric class can
escape Proposition 7 only by reversing one of those signs or by making the
inactive Quit expression in `(11.5)` exceed `w` at every active root.

The rational stress table `(10.1)` has

```text
(A_1,A_2)=(2,0),   (B_0,B_1,B_2)=(1,0,1),
(C_0,D_0)=(0,1),
```

so `(11.4)` holds, `(11.2)` reduces to the factorization `(10.3)`, and
`(11.5)` reduces to `(10.6)`.

## 12. Next question

The remaining minimal class consists of opposite-pair-sensitive tables for
which neither a common stationary root nor Proposition 7 solves the endpoint
equations.  A credible gadget seed must first survive exact searches over all
pair-support words, not only eliminate pure coalitions.  The concrete next
problem is the inactive wall: assume `(11.4)` but reverse `(11.5)` at every
root of `P`, then test whether alternating singleton-support words necessarily
produce a different exact periodic escape.

## 13. The complementary four-phase singleton escape

**Post-calculation status.**  The periodic construction below is exact, but
its spectator hypotheses already force a simpler pure equilibrium.  Indeed
the second inequality in `(13.8)` is strictly stronger than `B_1<B<A`, and
the first is `D<=C`.  If `B>=0`, quitting singleton `{i}` at date zero is an
exact equilibrium: its owner does not leave for Never, its partner does not
join, and neither opposite player joins.  If `B<=0`, all-Never is an exact
equilibrium.  Thus Section 13 kills this proposed complementary architecture
but does not enlarge the reviewed escape class.  It is retained because the
anchor algebra identifies why making the singleton word incentive-compatible
reintroduces precisely the pure singleton escape.

The alternating singleton calculation is exactly complementary to two signs
in Proposition 7.  Continue in the opposite-pair-count class `(11.1)` and
write

```text
A=A_1,       B=B_0,       C=C_0,       D=D_0.
```

Assume

```text
A>B>C,
3*B>C+2*A.                                             (13.1)
```

Put

```text
t=(B-C)/(A-B)>2.                                      (13.2)
```

Schedule the singleton owners in the four-phase word

```text
0,2,1,3
```

and repeat.  Only the displayed owner mixes at each phase.  Let the Continue
probabilities in those four phases be

```text
u,v,u,v,
```

respectively.

### Lemma 8.1 (exact cyclic anchor)

For every `t>2`, there are `u,v in (0,1)` satisfying

```text
v*(1-u*v)=t*(1-v),
1-u*v=t*u*v*(1-u).                                  (13.3)
```

**Proof.**  Put

```text
z=(t-sqrt(t^2-4))/2,
v=(z^2+1)/(z+1),
u=z*(z+1)/(z^2+1).                                  (13.4)
```

Since `t>2`, one has `0<z<1`, and `z` is the smaller root of

```text
z^2-t*z+1=0.                                        (13.5)
```

The displayed formulas give `0<u,v<1` and `u*v=z`.  Using
`t=z+1/z`, direct cancellation gives

```text
1-v=u*(1-u)*v^2,
1-u*v=t*u*v*(1-u).                                  (13.5a)
```

Multiplying the second identity by `v` and using the first gives
`v*(1-u*v)=t*(1-v)`, the other identity in `(13.3)`. QED.

For a player whose three future owners occur in the order partner, opposite,
opposite, the condition that its post-own continuation value equal its solo
payoff `B` is

```text
(C-B)*(1-v)+(A-B)*v*(1-u*v)=0.                      (13.6)
```

For a player whose order is opposite, opposite, partner, it is

```text
(A-B)*(1-u*v)+(C-B)*u*v*(1-u)=0.                    (13.7)
```

Since `C-B=-t*(A-B)`, equations `(13.6)--(13.7)` are exactly `(13.3)`.
Thus every scheduled owner is indifferent between Quit and Continue and has
value `B` at its own phase.

The only nonowner deviations that appear are partner joins and opposite joins.
The following two inequalities make all of them unprofitable:

```text
D<=C,
B_1 <= A+(C-B)/(u*v).                               (13.8)
```

The second right side is strictly below `B`, because `A-B>0`, `C-B<0`,
`t>2`, and `u*v<1`.

**Theorem 8 (four-phase singleton escape; ordinary mathematics, awaiting
review).**  Under `(13.1)` and `(13.8)`, the periodic singleton-owner profile
with continuation word `u,v,u,v` supplied by Lemma 8.1 is an exact terminal
Nash profile against unrestricted behavioral deviations.

**Proof.**  The anchor equalities above give exact indifference at every
owner phase.  It remains to check spectators.  If the current owner uses
Continue probability `x`, a partner spectator's forced-Quit payoff is

```text
x*B+(1-x)*D,
```

while its prescribed Continue payoff is its current phase value.  At an
`u`-phase that value is `(1-u)*C+u*B`; at the other partner occurrence it is
`B`.  The condition `D<=C<B` handles both cases.

For an opposite spectator, forced Quit pays

```text
x*B+(1-x)*B_1.                                      (13.9)
```

At the two `u`-phases the smaller of the relevant spectator values is `B`, so
`B_1<B` handles both.  At a `v`-phase the two possible Continue values are

```text
(1-v)*A+v*B,
(1-v)*A+v*((1-u)*C+u*B).                            (13.10)
```

The second is smaller.  Comparing `(13.9)` with that value and dividing by
`1-v>0` gives

```text
B_1 <= A + [v*(1-u)/(1-v)]*(C-B).
```

Equation `(13.5a)` gives `v*(1-u)/(1-v)=1/(u*v)`, so this is exactly the second
condition in `(13.8)`.  All endpoint-Nash inequalities therefore hold.

Every owner has positive Quit probability because `u,v<1`.  After deleting
any one player's clock, the other three owner phases still give a strict
survival contraction in every four-phase block.  Unrolling the exact endpoint
inequalities controls every finite pure Quit time and Never, and the checked
pure-time extremality theorem controls every behavioral stopping law. QED.

At every date only one player has positive Quit probability, and survival over
one full cycle is `(u*v)^2<1`.  Absorption is therefore almost sure and every
terminal coalition is a singleton.  In particular, both designated disjoint-
pair atoms are exactly zero at this equilibrium.  Theorem 8 is thus a direct
escape from the target incidence inequalities, not merely existence of an
equilibrium with unknown first-outcome law.

An exact rational boundary test is

```text
(A_1,A_2)=(2,0),
(B_0,B_1,B_2)=(1,-6,0),
(C_0,C_1,C_2)=(-2,0,0),
(D_0,D_1,D_2)=(-2,0,0).
```

Here `t=3`, `z=(3-sqrt(5))/2`, and `(13.4)` gives algebraic `u,v in (0,1)`.
The opposite-join threshold is

```text
2-3/z = -(5+3*sqrt(5))/2 > -6,
```

so `(13.8)` holds.  The reward table is rational even though its equilibrium
hazards need not be.

### Exact relation to the alternating-pair signs

The rare common-stationary boundary is

```text
3*B=C+2*A.
```

Proposition 7's second sign is the strict side

```text
3*B<C+2*A,
```

where the alternating-pair active polynomial crosses.  Theorem 8 treats the
opposite strict side `3*B>C+2*A` when `A>B>C`.  Its partner-spectator condition
`D<=C` is also complementary to Proposition 7's singleton-destabilizing sign
`D>C`.  Thus the two periodic supports occupy opposite quadrants of the same
two elementary incentive comparisons.

The remaining walls are genuine.  Theorem 8 does not cover `D>C`, because a
partner then wants to join a singleton owner.  Nor does it cover a large
`B_1`, because an opposite spectator joins.  Those are precisely the
directions that can create designated-pair or cross-pair collision mass.  The
next question is whether the failed spectator inequality itself forces a
two-quitter support word, rather than merely moving the obstruction to another
finite architecture.

## 14. Exact pure-orbit reduction for the eleven-parameter class

The Section 13 collapse suggests first removing every pure orbit exactly.
For the opposite-pair-count table `(11.1)`, the five nonempty coalition orbits
are singleton, designated pair, cross pair, triple, and grand coalition.

**Proposition 9 (pure-orbit classification; ordinary mathematics, awaiting
review).**  A date-zero profile with the displayed quitter coalition is an
exact terminal Nash profile precisely under the corresponding conditions:

```text
Never:             B_0 <= 0;
singleton:         B_0 >= 0,  D_0 <= C_0,  B_1 <= A_1;
designated pair:   D_0 >= C_0,  B_2 <= A_2;
cross pair:        B_1 >= A_1,  D_1 <= C_1;
triple:            D_1 >= C_1,  B_2 >= A_2,  D_2 <= C_2;
grand coalition:   D_2 >= C_2.                       (14.1)
```

**Proof.**  At date zero, a coalition member's only relevant toggle is to
Continue, and an outsider's is to join.  For a singleton owner, leaving gives
Never payoff zero; its designated partner compares `C_0` with joined payoff
`D_0`, and either opposite player compares `A_1` with `B_1`.  For a designated
pair, a member compares `D_0` with `C_0`, while either outsider compares
`A_2` with `B_2`.  For a cross pair, a member compares `B_1` with `A_1`, while
either outsider compares `C_1` with `D_1`.  In a triple, the two members of the
contained designated pair compare `D_1` with `C_1`; the remaining member
compares `B_2` with `A_2`; and the outsider compares `C_2` with `D_2`.  At the
grand coalition every member compares `D_2` with `C_2`.  These exhaust all
players and all coalition orbits. QED.

Consequently, if the table has no pure terminal equilibrium, then `B_0>0`,
`D_2<C_2`, and exactly one of the following strict sign patterns holds:

```text
designated-join chamber:
  D_0>C_0,  B_1<A_1,  B_2>A_2,
  D_1<C_1,  D_2<C_2;                                (14.2)

cross-join chamber:
  D_0<C_0,  B_1>A_1,  D_1>C_1,  B_2<A_2,  D_2<C_2. (14.3)
```

Indeed equality `D_0=C_0` is impossible without a pure equilibrium: avoiding
both singleton and designated-pair sinks would force `B_1>A_1` and
`B_2>A_2`; avoiding the cross pair would force `D_1>C_1`, after which the
triple is stable because `D_2<C_2`.

The common-stationary boundary theorem further shows that a table with no
terminal approximate-equilibrium escape of that type must satisfy

```text
3*B_0<C_0+2*A_1.                                    (14.4)
```

Equality already gives the reviewed vanishing-hazard approximate family, and
the reverse strict inequality gives the reviewed interior common stationary
root because `D_2<C_2`.

Thus every opposite-pair-count gadget candidate surviving all pure and common-
stationary tests lies in `(14.2)` or `(14.3)` together with `(14.4)`.
Proposition 7 produces a designated-pair active root in chamber `(14.2)`.
The next proposition supplies the missing cross-pair active root in chamber
`(14.3)`.

## 15. Cross-pair alternating escape

Alternate the cross pairs

```text
{0,1}, {2,3}.
```

At its active phase each member Continues with probability `x` and Quits with
probability `q=1-x`; inactive players Continue surely.  Put

```text
Qx(x)=x*B_0+q*B_1,

Px(x)=(1+x+x^2)*Qx(x)
      -A_1-x^2*(C_0+A_1)-x*q*C_1.                   (15.1)
```

For a player, let `v` be its value at the phase where its cross pair is active
and `w` its value at the other phase.  Exact conditioning gives

```text
v=q*x*B_0+q^2*B_1+x*q*A_1+x^2*w,
w=q*x*(C_0+A_1)+q^2*C_1+x^2*v.                      (15.2)
```

At the active phase, forced Quit pays `Qx(x)` and forced Continue pays
`q*A_1+x*w`.  Active indifference is therefore

```text
v=Qx(x)=q*A_1+x*w,
```

and substitution in `(15.2)` is exactly `Px(x)=0`.

**Proposition 10 (cross-pair IVT producer; ordinary mathematics, awaiting
review).**  Suppose

```text
B_1>A_1,
3*B_0<C_0+2*A_1.                                    (15.3)
```

Then `Px` has a root `xStar in (0,1)`.  If, for one such root,

```text
xStar^2*B_0
  +xStar*(1-xStar)*(D_0+B_1)
  +(1-xStar)^2*D_1
    <= [Qx(xStar)-(1-xStar)*A_1]/xStar,              (15.4)
```

the alternating cross-pair profile is an exact terminal Nash profile against
unrestricted behavioral deviations.

**Proof.**  The endpoint signs are

```text
Px(0)=B_1-A_1>0,
Px(1)=3*B_0-C_0-2*A_1<0.                            (15.5)
```

Continuity gives `xStar in (0,1)`.  Equations `(15.1)--(15.2)` give active
indifference with

```text
v=Qx(xStar),
w=[Qx(xStar)-(1-xStar)*A_1]/xStar.
```

At the inactive phase, the two active opponents are respectively the player's
designated partner and one opposite player.  If the inactive player is forced
to Quit, then zero, only the partner, only the opposite, or both active players
Quit with probabilities `xStar^2`, `xStar*q`, `xStar*q`, and `q^2`.  Its
corresponding rewards are `B_0,D_0,B_1,D_1`.  Thus the left side of `(15.4)`
is exactly its forced-Quit payoff, while `w` is its prescribed Continue value.
This proves every inactive endpoint inequality.

Both members of an active cross pair have positive Quit probability.  After
deleting any one player's clock, at least one active player remains in each
two-phase block, so every deleted survival product contracts strictly.
Unrolling the exact endpoint inequalities controls all finite pure Quit times
and Never; pure-time extremality gives unrestricted behavioral optimality.
QED.

This producer is strictly stronger than the preceding pure/common-stationary
tests.  Consider the complete rational parameter table

```text
(A_1,A_2)=(4,6),
(B_0,B_1,B_2)=(1,5,4),
(C_0,C_1,C_2)=(0,0,-2),
(D_0,D_1,D_2)=(-3,1,-5).                            (15.6)
```

Proposition 9 shows that `(15.6)` has no pure terminal equilibrium: it lies
strictly in chamber `(14.3)`.  Its cross polynomial is

```text
Px(x)=1+x-3*x^2-4*x^3,
```

which has an interior root by `(15.5)`.  At every such root,

```text
w=1/x,
inactive forced-Quit payoff=1,
```

so `(15.4)` is strict.

It also has no common stationary equilibrium.  If every player uses common
Quit probability `h in (0,1]`, the exact Quit-minus-Never gap has the sign of

```text
G(h)=-5+19*h-26*h^2+4*h^3+10*h^4-5*h^5.            (15.7)
```

In the degree-five Bernstein basis on `[0,1]`, the coefficients of `G` are

```text
-5, -6/5, 0, -1, -9/5, -3.
```

They are all nonpositive and at least one strictly negative basis term is
positive at every point, so `G(h)<0` throughout `[0,1]`.  Thus the exact
cross-pair periodic profile is a genuinely new escape for this rational table,
not a rediscovery of a pure or common-stationary root.

At every live date its active pair is cross-designated.  Hence the two target
designated-pair atoms `{0,2}` and `{1,3}` are exactly zero, while absorption is
almost sure.  This profile directly violates the desired lower incidence
bounds.

### Narrowed residual wall

Propositions 7, 9, and 10 reduce the full opposite-pair-count architecture to
two explicit inactive walls.  After excluding pure and common-stationary
escapes:

- in chamber `(14.2)`, every root of the designated-pair polynomial `(11.2)`
  must violate `(11.5)`; and
- in chamber `(14.3)`, every root of the cross-pair polynomial `(15.1)` must
  violate `(15.4)`.

These are finite algebraic conditions on the complete eleven-parameter table,
but they are not yet a universal equilibrium theorem.  Failure of an inactive
inequality means that the allegedly inactive player strictly wants to join
the active pair.  The remaining question is whether continuing that support
enlargement to a three-player-active phase must reach either a pure triple,
the grand coalition, or another exact periodic root.  No finite menu of such
words is asserted exhaustive.

**New reviewed checkpoint (Sections 16--17).**  A rational table survives the
pure, common-stationary, designated-pair-periodic, and cross-pair-periodic
filters, but it has a continuum of exact single-owner stationary equilibria.
Proposition 11 gives the exact interval criterion and controls unrestricted
behavioral deviations by pure-time extremality.  Thus the table is retained
only as a diagnostic showing that the earlier support menu was incomplete.

**New reviewed checkpoint (Sections 18--19).**  Exact stationary compilers
for one active designated pair and for a three-player support have now passed
independent falsification.  A complete rational table survives every earlier
filter in the note but has a strict three-active exact equilibrium, with one
of the desired pair atoms identically zero.  This expands the support audit;
it is not a completeness theorem for the eleven-parameter class.

## 16. A rational survivor of the pure/common/pair-periodic filters

The residual walls are nonempty.  Consider the complete rational table

```text
(A_1,A_2)=(7,10),
(B_0,B_1,B_2)=(1,8,-7),
(C_0,C_1,C_2)=(-4,2,8),
(D_0,D_1,D_2)=(-6,6,-1).                            (16.1)
```

This is a hard test instance, not a claimed quitting-game counterexample.

First, `(16.1)` lies strictly in the cross-join chamber `(14.3)`:

```text
B_0>0,  D_0<C_0,  B_1>A_1,  D_1>C_1,
B_2<A_2,  D_2<C_2.
```

Proposition 9 therefore excludes every pure terminal outcome.

Second, it has no common stationary equilibrium.  The common stationary
Quit-minus-Never gap has the sign of

```text
G(h)=-7+24*h-60*h^2+52*h^3-21*h^4+3*h^5.           (16.2)
```

Its degree-five Bernstein coefficients are

```text
-7, -11/5, -17/5, -27/5, -36/5, -9,
```

so `G(h)<0` on `[0,1]`.

Third, the designated-pair active polynomial `(11.2)` is

```text
P_designated(x)=-2-9*x-3*x^2+7*x^3.                (16.3)
```

Its degree-three Bernstein coefficients are `-2,-5,-9,-7`, so it has no root
on `[0,1]`.

Finally, the cross-pair polynomial is

```text
P_cross(x)=1-x-7*x^3.                               (16.4)
```

It is strictly decreasing and has a unique root `xStar in (2/5,9/20)`.  At
that root the inactive Continue value and forced-Quit payoff are

```text
w=1/xStar,
I=6-10*xStar+5*xStar^2.
```

The difference satisfies

```text
xStar*(I-w)
 =(-2+37*xStar-70*xStar^2)/7 > 0.                   (16.5)
```

The last inequality holds because the concave quadratic is positive at both
`2/5` and `9/20`.  Thus the unique cross-pair active root strictly fails the
inactive-player condition `(15.4)`.

No conclusion about unrestricted exploitability follows from those filters.
Indeed the next section constructs a different exact stationary equilibrium
for `(16.1)`, with only one player using a positive hazard.  The table remains
useful diagnostically because it forced that missing support to be exposed.

## 17. Diffuse single-owner escape

Fix one player `o`.  Let `o` Continue with probability `x in [0,1)` at every
live date and let all other players Continue surely.  The game absorbs almost
surely at singleton `{o}`.  In the opposite-pair-count notation, the owner's
payoff is `B_0`, its designated partner's payoff is `C_0`, and either opposite
player's payoff is `A_1`.

**Proposition 11 (single-owner stationary interval; ordinary mathematics,
independently reviewed valid).**  If

```text
B_0>=0,
x*B_0+(1-x)*D_0 <= C_0,
x*B_0+(1-x)*B_1 <= A_1,                              (17.1)
```

then the displayed single-owner stationary profile is an exact terminal Nash
profile against unrestricted behavioral deviations.  Its two designated-pair
atoms are zero.

**Proof.**  Since every opponent of `o` Never Quits, every finite Quit time of
`o` earns its solo payoff `B_0`, while Never earns zero.  The owner is therefore
optimal because `B_0>=0`.

Consider its designated partner.  Never earns `C_0`.  If the partner Quits at
finite time `t`, then on every earlier absorption it again receives `C_0`.
Conditional on survival to `t`, simultaneous owner Quit pays `D_0` and owner
Continue pays the partner's solo reward `B_0`.  Its pure-time payoff is
therefore on the segment between

```text
C_0,
x*B_0+(1-x)*D_0.
```

The first inequality in the second line of `(17.1)` makes Continue/Never
optimal.

For an opposite player, the same calculation has prescribed/Never payoff
`A_1`, and its finite-time endpoint is

```text
x*B_0+(1-x)*B_1.
```

The last inequality in `(17.1)` makes Continue/Never optimal.  These three
player types exhaust the game.  Pure-time extremality then controls arbitrary
behavioral stopping laws.  Only `o` ever Quits, so absorption is singleton
almost surely and both target pair atoms vanish. QED.

The conditions are an explicit interval test.  In the common strict ordering

```text
D_0<C_0,       B_0<B_1,       B_0<A_1<B_1,
```

they reduce to

```text
(B_1-A_1)/(B_1-B_0)
  <= x <=
(C_0-D_0)/(B_0-D_0),                                (17.2)
```

with the right inequality omitted when `B_0<=D_0` and it is automatically
satisfied.

For the residual table `(16.1)`, `(17.1)` becomes

```text
7*x-6 <= -4,
8-7*x <= 7.
```

Thus every

```text
1/7 <= x <= 2/7
```

gives an exact single-owner terminal equilibrium.  This explains why the
cross-pair spectator wanted to join: reducing the support further, rather than
enlarging it, balances that player's join payoff against the low
partner-collision row.

Proposition 11 adds a third exact filter to the residual walls.  A surviving
cross-join table must make the two linear intervals in `(17.1)` disjoint for
every possible owner.  By symmetry it is enough to test the displayed one.
Failure of this interval is now the concrete next condition for the
three-player-support analysis.

## 18. Single designated-pair stationary escape

There is another support between the single owner and the alternating pairs.
Fix one designated pair.  Let both its members Continue with probability
`x in (0,1)` at every live date, independently, and let the other designated
pair Continue surely.

**Proposition 12 (single active-pair stationary test; reviewed ordinary
mathematics).**  Suppose

```text
x*B_0+(1-x)*D_0=C_0.                                (18.1)
```

Put `q=1-x` and

```text
w=[2*x*A_1+q*A_2]/(1+x),
I=x^2*B_0+2*x*q*B_1+q^2*B_2.                        (18.2)
```

If `I<=w`, the displayed stationary profile is an exact terminal Nash profile
against unrestricted behavioral deviations.

**Proof.**  For either active player, forced Quit pays

```text
Q=x*B_0+q*D_0=C_0.
```

If it Continues, its partner Quits with probability `q`, paying `C_0`; with
probability `x` the same state is reached again.  Thus Continue/Never also has
value `C_0`, and the prescribed mixture is exactly optimal.

For an inactive player, the two active players are both opposite players.
Its prescribed Continue payoff solves

```text
w=2*q*x*A_1+q^2*A_2+x^2*w,
```

which is the first formula in `(18.2)`.  Forced Quit pays `B_0,B_1,B_2`
according as zero, one, or two active opponents Quit, giving exactly `I`.
Thus `I<=w` is the inactive endpoint-Nash condition.

Every active player faces its partner's positive hazard, and every inactive
player faces both active hazards.  Hence every player-deleted opponent
survival contracts.  Unrolling the endpoint inequalities and applying pure-
time extremality gives unrestricted behavioral optimality. QED.

Only the chosen designated pair can be a nonsingleton first coalition.  The
other target designated-pair atom is exactly zero, so this equilibrium again
escapes any attempted uniform positive lower bound on both atoms.

The test resolves the first exact table surviving Proposition 11:

```text
(A_1,A_2)=(6,14),
(B_0,B_1,B_2)=(1,9,-4),
(C_0,C_1,C_2)=(-2,6,8),
(D_0,D_1,D_2)=(-3,11,1).                            (18.3)
```

Its single-owner interval is empty because the partner inequality requires
`x<=1/4`, while the opposite inequality requires `x>=3/8`.  Nevertheless
`(18.1)` selects `x=1/4`.  At this value

```text
w=54/5,
I=19/16,
```

so the inactive inequality is strict.  Thus `(18.3)` has an exact single-
designated-pair stationary equilibrium even though it survives the pure,
common-stationary, alternating-pair, and single-owner filters used to find it.

The remaining cross-join wall must now make both `(17.1)` and `(18.1)--(18.2)`
fail.  These failures have opposite interpretations: the first says no one
owner can balance its partner and opposite joiners, while the second says a
whole designated pair cannot mix without attracting an opposite player.

## 19. Three-active stationary escape

The strict inactive inequality in Proposition 12 points to the next support:
allow the attracting opposite player to mix.  This gives another exact
algebraic filter without treating a finite list of supports as exhaustive.

Activate players `0,1,2`, where `{0,2}` is a designated pair and player `3`
is player `1`'s designated partner.  Players `0,2` Continue with probability
`x in (0,1)`, player `1` Continues with probability `y in (0,1)`, and player
`3` Continues surely.  Put

```text
q=1-x,       s=1-y,

K=x^2*B_0+2*x*q*B_1+q^2*B_2,
W=[2*x*A_1+q*A_2]/(1+x),

R=x*(y*B_0+s*B_1)+q*(y*D_0+s*D_1),                (19.1)

C=[y*(2*x*q*A_1+q^2*A_2)
   +s*(x^2*C_0+2*x*q*C_1+q^2*C_2)]/(1-x^2*y),

T=y*K+s*(x^2*D_0+2*x*q*D_1+q^2*D_2).              (19.2)
```

Here `R` is the value of either active member of `{0,2}`, `K` is the value of
active player `1`, and `C` is the prescribed value of inactive player `3`.

**Proposition 13 (three-active stationary test; reviewed ordinary
mathematics).**  If

```text
K=W,
(1-x*y)*R=x*s*A_1+q*y*C_0+q*s*C_1,
T<=C,                                                (19.3)
```

then the displayed stationary profile is an exact terminal Nash profile
against unrestricted behavioral deviations.

**Proof.**  For active player `1`, whose partner is inactive, forced Quit
against players `0,2` pays `K`.  Forced Continue pays

```text
2*x*q*A_1+q^2*A_2+x^2*K.
```

The first equality in `(19.3)` is exactly equality of these endpoints.

For active player `0` or `2`, forced Quit pays `R`.  If it Continues, the
partner quits alone with probability `q*y`, the active opposite player quits
alone with probability `x*s`, both quit with probability `q*s`, and both
continue with probability `x*y`.  Its Continue endpoint is therefore

```text
x*s*A_1+q*y*C_0+q*s*C_1+x*y*R,
```

so the second equality in `(19.3)` is precisely active indifference.

For inactive player `3`, ordinary Bellman conditioning gives `C` in `(19.2)`.
If it is forced to Quit, the partner-Continue branch pays the `B` expectation
`K`, while the partner-Quit branch pays the displayed `D` expectation.  Its
forced-Quit payoff is consequently `T`; the last inequality makes Continue
optimal.

Every active player faces at least one opponent with a positive Quit hazard,
and the inactive player faces all three active hazards.  Thus every
player-deleted survival product contracts geometrically.  Unrolling the
endpoint equalities and inequality controls every finite pure Quit time and
Never, and pure-time extremality then controls every behavioral deviation.
QED.

The following rational table shows that this support is not subsumed by the
previous filters:

```text
(A_1,A_2)=(0,14),
(B_0,B_1,B_2)=(2,2,-9),
(C_0,C_1,C_2)=(9,3,13),
(D_0,D_1,D_2)=(6,14,-1).                            (19.4)
```

It lies strictly in the cross-join chamber `(14.3)`, since

```text
B_0>0, D_0<C_0, B_1>A_1, D_1>C_1,
B_2<A_2, D_2<C_2.
```

The common stationary Quit-minus-Never numerator, after removing its positive
factor `h`, is

```text
-3+4*h+3*h^2-47*h^3+41*h^4-12*h^5.
```

Its degree-five Bernstein coefficients are

```text
-3, -11/5, -11/10, -22/5, -43/5, -14,
```

so it is strictly negative on `[0,1]`; no common stationary root exists.  The
single-owner conditions are incompatible: the partner
inequality is automatic, but the opposite inequality would require
`2<=A_1=0`.  Equation `(18.1)` has no solution because its left side lies
between `B_0=2` and `D_0=6`, whereas `C_0=9`.

The designated-pair alternating polynomial `(11.2)` is

```text
-3-12*x+16*x^2-4*x^3.
```

Its degree-three Bernstein coefficients are

```text
-3, -7, -17/3, -3,
```

so it has no root on `[0,1]`.  The cross-pair alternating polynomial `(15.1)`
is

```text
2-x-4*x^2.
```

It has a unique root `z in (7/12,3/5)`.  At that root, the inactive gap has
the sign of

```text
z*(I-W)=47*z/2-13>0,
```

where the reduction uses `4*z^2+z-2=0`.  Thus the unique cross-pair root
strictly fails its inactive inequality.

It remains to solve `(19.3)`.  The equality `K=W` reduces to

```text
f(x)=11*x^3-11*x^2-27*x+23=0.                       (19.5)
```

The derivative is negative on `[0,1]`, while

```text
f(3/4)=77/64>0,       f(4/5)=-1/125<0.
```

Hence there is a unique `x in (3/4,4/5)`.  For this `x`, the second active
equality in `(19.3)` becomes

```text
F_x(y)=8*x*(1-x)*y^2+(12*x^2-14)*y+11-9*x=0.        (19.6)
```

Now `F_x(0)>0`,

```text
F_x(1)=(4*x+3)*(x-1)<0,
```

and `F_x` is strictly decreasing on `[0,1]`; for the latter, its derivative
is at most

```text
16*(3/4)*(1/4)+12*(4/5)^2-14<0.
```

Thus `(19.6)` has a unique `y in (0,1)`.  Moreover

```text
F_x(1/2)=4*x^2-7*x+4>0
```

because this quadratic has negative discriminant, so `y>1/2`.

For a direct exact check of the remaining spectator inequality, put

```text
R_C=16*x^2-20*x+13,
R_D=-23*x^2+30*x-1.
```

Using `(1-x^2)*K=14*(1-x)^2`, expansion gives the factorization

```text
(1-x^2*y)*(C-T)
 =(1-y)*[R_C-R_D+x^2*y*(R_D-K)].                    (19.7)
```

On `x in (3/4,4/5)`, `R_D-K=-12*x^2+8*x+8>0`.  Since `y>1/2`, the bracket
in `(19.7)` is at least

```text
L(x)=-6*x^4+4*x^3+43*x^2-50*x+14.
```

The polynomial `L` is increasing on this interval: the crude endpoint bound

```text
L'(x)>=-24*(4/5)^3+12*(3/4)^2+86*(3/4)-50
     =4481/500>0
```

suffices.  Finally `L(3/4)=61/128>0`.  Therefore `C>T`, and Proposition 13
gives an exact terminal Nash profile for `(19.4)`.

Only the active designated pair `{0,2}` can be a designated-pair first
coalition.  The other target atom `{1,3}` is identically zero because player
`3` Never Quits.  Thus `(19.4)` is a further exact escape from the desired
two-pair lower bounds after all prior filters in this note have been imposed.
It remains a support-specific diagnostic, not a completeness theorem for the
eleven-parameter class or for arbitrary finite gadgets.

## 20. Single cross-pair stationary escape

For completeness of the stationary support audit, activate one member of each
designated pair and let the other two players Continue surely.  Let the two
active players use the same Continue probability `x in (0,1)` and put
`q=1-x`.  The active pair is a cross pair, not either of the two target pairs.

**Proposition 14 (single cross-pair stationary test; ordinary mathematics,
awaiting review).**  Suppose

```text
x*B_0+q*B_1=A_1.                                    (20.1)
```

Define

```text
w=[x*q*(C_0+A_1)+q^2*C_1]/(1-x^2),
I=x^2*B_0+x*q*(D_0+B_1)+q^2*D_1.                    (20.2)
```

If `I<=w`, the displayed stationary profile is an exact terminal Nash
profile against unrestricted behavioral deviations.  Both designated-pair
first-outcome atoms are zero.

**Proof.**  An active player's partner is inactive and the other active
player is an opposite.  Forced Quit therefore pays

```text
x*B_0+q*B_1=A_1.
```

Forced Continue pays `q*A_1+x*v`, where `v` is its prescribed stationary
value.  Taking `v=A_1` makes the endpoints equal and satisfies the Bellman
identity.

For either inactive player, exactly one active player is its partner and the
other is an opposite.  Continuing gives `C_0` when only the partner Quits,
`A_1` when only the opposite Quits, `C_1` when both Quit, and returns to the
same state when both Continue.  Its stationary value is exactly `w`.
Forced Quit gives `B_0,D_0,B_1,D_1` in the four corresponding root outcomes,
whose expectation is `I`.  Thus `I<=w` is precisely the remaining endpoint
inequality.

Every player faces at least one active opponent with positive Quit hazard, so
all player-deleted survival products contract.  Endpoint unrolling and
pure-time extremality cover every finite Quit time and Never and hence every
behavioral deviation.  Since the only nonsingleton active coalition contains
one member of each designated pair, neither designated target pair can be the
first-quitter coalition. QED.

Equation `(20.1)` has an interior solution exactly when `A_1` lies strictly
between `B_0` and `B_1`; in that case

```text
x=(A_1-B_1)/(B_0-B_1).
```

This is a useful exact extra filter because it depends only on seven of the
eleven cells.  It is not subsumed algebraically by the single-owner test:
the inactive condition averages both active clocks and can hold even when the
designated-partner inequality for either single owner fails.  Conversely, it
does not imply that one of the earlier periodic supports works.  The ongoing
classification must keep those routes separate and cannot treat their finite
union as exhaustive.

## 21. Two-pair-type fully active stationary root

The remaining stationary support has all four players active but allows the
two designated pairs to use different hazards.  This is distinct from the
common stationary root tested earlier.

For `u,v in (0,1)`, define

```text
Q(u,v)
 =u*[v^2*B_0+2*v*(1-v)*B_1+(1-v)^2*B_2]
 +(1-u)*[v^2*D_0+2*v*(1-v)*D_1+(1-v)^2*D_2],

C(u,v)
 =u*[2*v*(1-v)*A_1+(1-v)^2*A_2]
 +(1-u)*[v^2*C_0+2*v*(1-v)*C_1+(1-v)^2*C_2],

E(u,v)=(1-u*v^2)*Q(u,v)-C(u,v).                    (21.1)
```

Here `u` is the Continue probability of the player's own designated partner,
and `v` is the common Continue probability of the two opposite players.

**Proposition 15 (two-pair-type stationary test; ordinary mathematics,
awaiting review).**  Suppose `x,y in (0,1)` satisfy

```text
E(x,y)=0,        E(y,x)=0.                           (21.2)
```

Let the members of one designated pair Continue with probability `x` at each
live date and the members of the other pair Continue with probability `y`.
Then this stationary profile is an exact terminal Nash profile against
unrestricted behavioral deviations.

**Proof.**  For a member of the first pair, forced Quit has the complete
coalition enumeration `Q(x,y)`.  When it Continues, nonempty opponent
absorption contributes `C(x,y)`, while all three opponents Continue with
probability `x*y^2` and return to the same value.  Taking its stationary value
to be `Q(x,y)`, endpoint indifference is exactly

```text
(1-x*y^2)*Q(x,y)=C(x,y).
```

This is the first equation in `(21.2)`.  Pair symmetry gives the second
equation for either member of the other pair with `x,y` interchanged.  Hence
all four prescribed roots are exact endpoint Nash and satisfy their Bellman
identities.

Every player faces its active partner even after its own hazard is deleted,
so every player-deleted survival product contracts geometrically.  Unrolling
the endpoint equalities controls all finite pure Quit times and Never, and
pure-time extremality covers arbitrary behavioral stopping laws. QED.

The diagonal `x=y` recovers the common stationary equation.  Off-diagonal
solutions are symmetry-broken fully active equilibria and are not detected by
that scalar test.  Proposition 15 is an exact two-polynomial screen, not an
existence theorem: no degree argument establishing a zero of `(21.2)` for all
tables is claimed.  A complete no-go theorem for the eleven-parameter gadget
class would need either such a global argument or a separate treatment of
nonstationary supports; the growing finite list of explicit roots is not
declared exhaustive.

## 22. Exact projective classification of vanishing stationary roots

The support filters above concern macroscopic stationary or periodic roots.
The remaining stationary boundary can be classified without enumerating
non-singleton reward rows.

Put

```text
a=A_1-B_0,          c=C_0-B_0.                       (22.1)
```

Thus `a` is the singleton margin created by an opposite player's singleton,
`c` is the margin created by the designated partner's singleton, and the
normalized singleton surplus is `c+2*a`.

For a nonnegative vector `lambda` on the four players define

```text
g_i(lambda)
 =c*lambda_(p(i))+a*sum_(j opposite i) lambda_j.     (22.2)
```

**Proposition 16 (positive-surplus projective LCP; ordinary mathematics,
awaiting review).**  Suppose `c+2*a>0`.  There is a nonzero vector
`lambda>=0` satisfying

```text
g_i(lambda)>=0,
lambda_i*g_i(lambda)=0                 for every i   (22.3)
```

if and only if

```text
a>=0 and c>=0.                                      (22.4)
```

Consequently, if `c+2*a>0` and either `a<0` or `c<0`, there is no sequence of
stationary terminal `epsilon_n`-Nash profiles for which `epsilon_n->0` and the
positive total marginal Quit hazard tends to zero.

**Proof of the LCP classification.**  If `(22.4)` holds, any singleton-support
vector satisfies `(22.3)`: its active coordinate has `g=0`, its designated
partner sees the nonnegative margin `c`, and the two opposite players see the
nonnegative margin `a`.

Conversely, let `S` be the positive support of a solution.  If `|S|=1`, the
three inactive inequalities give `a>=0,c>=0`.  If `|S|=2` and `S` is a
designated pair, the two active equalities force `c=0`, while either inactive
inequality forces `a>=0`.  If `S` is a cross pair, the active equalities force
`a=0` and the inactive inequalities force `c>=0`.

Every three-player support contains one full designated pair and one member
of the other pair.  The active equality of the unpaired member forces `a=0`;
then either full-pair active equality forces `c=0`.  Finally, if all four
coordinates are positive, every `g_i` is zero, but summing gives

```text
sum_i g_i(lambda)=(c+2*a)*sum_i lambda_i>0,
```

a contradiction.  These cases exhaust the nonempty supports and prove the
equivalence.

**Proof of the stationary consequence.**  Let `p_i^n` be the stationary Quit
probabilities, put `H_n=sum_i p_i^n>0`, assume `H_n->0` and
`epsilon_n->0`, and pass to a subsequence with

```text
lambda_i^n=p_i^n/H_n -> lambda_i,
sum_i lambda_i=1.                                  (22.5)
```

Each stationary profile absorbs almost surely.  Conditional on absorption in
one stationary row, the probability of a collision is `O(H_n)`, and the
singleton probability of player `j` converges to `lambda_j`.  Hence player
`i`'s prescribed terminal payoff converges to

```text
B_0+g_i(lambda).                                    (22.6)
```

Let `Q_i^n` be the payoff from Quit immediately and let `N_i^n` be the payoff
from Never against the stationary opponents.  Quit immediately is a legal
deviation and `Q_i^n->B_0`.  If `lambda_i=0`, terminal
`epsilon_n`-optimality therefore gives

```text
B_0+g_i(lambda)=lim U_i^n >= lim Q_i^n=B_0,
```

so `g_i(lambda)>=0`.

Suppose `0<lambda_i<1`.  One-stage geometric unrolling gives the exact convex
decomposition

```text
U_i^n=theta_i^n*Q_i^n+(1-theta_i^n)*N_i^n,

theta_i^n
 =p_i^n/[p_i^n+(1-p_i^n)*(1-product_(j!=i)(1-p_j^n))].  (22.7)
```

Equation `(22.5)` implies `theta_i^n->lambda_i`, so both convex weights stay
bounded away from zero.  Since both Quit immediately and Never are legal
deviations, `epsilon_n`-Nash optimality says that this convex combination is
within `epsilon_n` of `max(Q_i^n,N_i^n)`.  Hence
`|Q_i^n-N_i^n|->0`, and `(22.6)` gives `g_i(lambda)=0`.  If
`lambda_i=1`, every other coordinate of `lambda` is zero, so
`g_i(lambda)=0` directly from `(22.2)`.  Thus `(22.3)` holds in all cases,
contradicting Proposition 16 in the mixed-sign positive-surplus chamber. QED.

This result is not a stationary-equilibrium existence theorem.  In the easy
strict subchamber `a>0,c>0`, Proposition 11 indeed gives exact single-owner
stationary profiles at sufficiently small positive hazard.  In the hard
mixed-sign subchambers, Proposition 16 says something different: even a
vanishing-error stationary escape cannot disappear into the all-Continue
boundary.  Any stationary approximate-equilibrium family must retain
macroscopic hazard, while a vanishing-hazard escape must be genuinely
nonstationary or use a different payoff mechanism.
This projective classification is support-complete for stationary roots and
does not rely on the finite menu of Sections 17--21.

## 23. No anchored cyclic singleton escape in either mixed-sign chamber

Proposition 16 leaves open genuinely nonstationary profiles.  It is tempting
to attack that boundary by scheduling one small-hazard owner at a time and
letting the owner word and phase survivals vary.  The obstruction to that
route is not a failed search over short words: the complete anchored
single-owner interface is empty in both strict mixed-sign chambers.

The normalized singleton margin matrix of the opposite-pair-count class is

```text
M(i,j)=0              if j=i,
M(i,j)=c              if j=p(i),
M(i,j)=a              if j is opposite i.           (23.1)
```

In particular it is symmetric.  Recall that an anchored cyclic patience
system may have arbitrary finite period, repeated owners, and a different
phase survival in `[0,1)` at every phase.  It requires the exact renewal
recursion and owner anchors, together with the vanishing-hazard spectator
condition that every phase value lie above every player's solo payoff.

**Proposition 17 (symmetric-margin singleton-cycle no-go; ordinary
mathematics, awaiting review).**  If

```text
a*c<0,                                                (23.2)
```

then there is no anchored cyclic patience system of any positive finite
period for the table, regardless of its phase survivals and owner
repetitions.

**Proof.**  Let `w_k` be the owner at phase `k`.  The general anchored
patience identities give

```text
M(w_k,w_(k+1))<=0,
M(w_(k+1),w_k)>=0.                                  (23.3)
```

These are respectively the successor and predecessor patience inequalities.
By symmetry of `(23.1)`, the two displayed quantities are equal.  Hence

```text
M(w_k,w_(k+1))=0.                                   (23.4)
```

Both off-diagonal margins are nonzero under `(23.2)`, so `(23.4)` forces
`w_(k+1)=w_k` at every phase.  The owner word is therefore constant, say
equal to `w`.

The general tolerance consequence of anchored patience says that, for every
player `y`, some scheduled owner has nonnegative margin in row `y`.  Here the
only scheduled owner is `w`.  If `c<0`, choose `y=p(w)`; if `a<0`, choose an
opposite player `y`.  In either case `(23.1)` gives `M(y,w)<0`, a
contradiction. QED.

The two ingredients invoked above are already checked as
`QuittingAnchoredCyclicPatienceSystem.successor_margin_nonpos`,
`QuittingAnchoredCyclicPatienceSystem.predecessor_margin_nonneg`, and
`QuittingAnchoredCyclicPatienceSystem.exists_margin_nonneg` in
`UniformEquilibrium/Quitting/Cycles/AnchoredCyclicPatience.lean`.  The only
new calculation is the four-player specialization `(23.1)`.

This is strictly broader than excluding the four-phase word of Section 13:
the period, owner word, repetitions, and phase survivals are arbitrary.  It
is also strictly narrower than excluding nonstationary terminal approximate
equilibria.  The patience structure is the vanishing-hazard limit of an
anchored single-owner schedule; a profile with two or more simultaneous
hazard carriers, macroscopic collision rows, a period diverging with the
accuracy, or no phasewise anchor need not produce this structure.  Thus the
remaining boundary is now specifically a nonstationary multi-owner or
non-anchored escape, not another finite singleton word search.

## 24. Periodic homogenization forces the same projective LCP

The preceding anchored no-go does not cover a periodic word with several
simultaneous small hazards in a phase.  Nevertheless, no such diffuse
periodic escape exists in the mixed-sign positive-surplus chamber.  The
reason is global rather than phasewise: over a rare-absorption period, the
first-quitter law homogenizes to the vector of aggregate marginal hazards.

For each `n`, let a finite word of product roots be repeated forever.  The
word length may depend on `n`.  Write `q_(n,k,i)` for player `i`'s Quit
probability at row `k` of the word and put

```text
H_n=sum_(k,i) q_(n,k,i).                            (24.1)
```

**Proposition 18 (diffuse periodic homogenization; ordinary mathematics,
awaiting review).**  Suppose `0<H_n->0`, the repeated-word profiles are
terminal `epsilon_n`-Nash with `epsilon_n->0`, and, after taking a
subsequence,

```text
lambda_i=lim_n [sum_k q_(n,k,i)]/H_n.               (24.2)
```

Then `lambda` is a nonzero projective LCP solution:

```text
lambda_i>=0,  sum_i lambda_i=1,
g_i(lambda)>=0,  lambda_i*g_i(lambda)=0.            (24.3)
```

Consequently no such family exists when `c+2*a>0` and `a*c<0`.
The conclusion allows unbounded word lengths, nonuniform roots, simultaneous
hazard carriers, and arbitrary bounded rewards on nonsingleton coalitions.

**Proof.**  Let `A_n` be the probability that a repeated word absorbs during
one traversal.  Since all component actions are independent,

```text
A_n=1-product_(k,i)(1-q_(n,k,i))=H_n+O(H_n^2).      (24.4)
```

Let `s_(n,i)` be the probability that one traversal, started live, first
absorbs at singleton `{i}`.  Expanding at each possible row gives

```text
s_(n,i)=sum_k q_(n,k,i)+O(H_n^2),                   (24.5)
```

uniformly in the word length: the loss from an earlier row or a simultaneous
opponent Quit is bounded by `H_n` times the displayed marginal sum.  The
one-traversal collision probability is `O(H_n^2)`.  Repeating the word makes
the traversals geometric, so division by `A_n` and `(24.2)--(24.5)` show that
the terminal singleton law converges to `lambda` and total collision mass
tends to zero.

It follows that the prescribed payoff of player `i` converges to

```text
U_i^n -> B_0+g_i(lambda).                           (24.6)
```

Quitting immediately against the first product root pays `B_0+O(H_n)`, even
with arbitrary collision rewards.  Terminal approximate Nash therefore
implies `g_i(lambda)>=0` for every `i`.

It remains to prove complementarity.  Let `N_i^n` be player `i`'s payoff from
Never against the repeated opponent word.  If `0<lambda_i<1`, the aggregate
opponent hazard in one word is asymptotic to `(1-lambda_i)H_n`.  Applying the
same one-traversal calculation after deleting player `i` gives

```text
N_i^n -> B_0+g_i(lambda)/(1-lambda_i).              (24.7)
```

Equations `(24.6)--(24.7)` are equivalently the limiting decomposition

```text
lim U_i^n
 =lambda_i*B_0+(1-lambda_i)*lim N_i^n.              (24.8)
```

Both Quit immediately and Never are legal deviations.  Since `U_i^n` is
within `epsilon_n` of both deviation payoffs, `(24.8)` with both coefficients
strictly positive forces

```text
lim U_i^n=B_0=lim N_i^n,
```

and hence `g_i(lambda)=0`.  If `lambda_i=0`, only the already proved
inequality is required.  If `lambda_i=1`, all other coordinates vanish and
`g_i(lambda)=0` directly from `(22.2)`.  This proves `(24.3)`, and
Proposition 16 gives the final contradiction. QED.

The important quantifier is the total hazard **per repeated word** in
`(24.1)`, not the maximum row mesh.  A long word may have tiny individual
roots but order-one aggregate absorption; this proposition does not cover
that regime.  Nor does it cover a genuinely nonperiodic clock law whose
successive blocks change.  It does show that varying the support pattern or
letting the period grow cannot evade Proposition 16 while the entire repeated
macroblock remains diffuse.

## 25. A diffuse escape must carry a fixed first--second rank bias

There is a useful exact diagnostic for the genuinely changing-clock regime.
It is stated in the continuous atomless timing model, not as a theorem about
the repository's discrete-time profiles.  Let the four players choose
independent, almost surely finite quit times in an atomless ordered time
space, so the first and second quitters are almost surely unique.  Terminal
payoffs therefore use only singleton rows.  Write

```text
z_i    =Pr(i is first),
pi_ij  =Pr(i is first and j is second),
P_D    =sum_i pi_(i,p(i)),
P_X    =sum_i sum_(j opposite i) pi_ij.             (25.1)
```

Thus `P_D+P_X=1`.

**Proposition 19 (first--second bias forced by the two elementary
deviations; ordinary mathematics, awaiting review).**  If the atomless
profile is a terminal Nash equilibrium, then for every player `i`,

```text
c*z_(p(i))+a*sum_(j opposite i) z_j >= 0,           (25.2)
c*pi_(i,p(i))+a*sum_(j opposite i) pi_ij <= 0.      (25.3)
```

Consequently:

1. if `a=-r<0` and `c>2*r`, then

   ```text
   P_D <= r/(c+r) < 1/3;                            (25.4)
   ```

2. if `c=-s<0` and `2*a>s`, then

   ```text
   P_D >= a/(a+s) > 1/3.                            (25.5)
   ```

In particular no exchangeable independent clock profile can be an atomless
equilibrium in either strict mixed-sign positive-surplus chamber, because
exchangeability gives `P_D=1/3`.

**Proof.**  Immediate Quit is almost surely a singleton and pays `B_0`.
The prescribed singleton payoff is

```text
U_i=B_0+c*z_(p(i))+a*sum_(j opposite i) z_j,
```

so the immediate-Quit deviation gives `(25.2)`.

Now force player `i` to Never.  Removing `i` leaves player `j` first among
the opponents precisely on the disjoint union of the events

```text
j was first overall,
i was first and j was second.
```

Its probability is therefore `z_j+pi_ij`.  Since
`sum_(j!=i) pi_ij=z_i`, subtracting the prescribed payoff from the Never
payoff cancels the solo baseline and gives

```text
N_i-U_i
 =c*pi_(i,p(i))+a*sum_(j opposite i) pi_ij.
```

The Never deviation proves `(25.3)`.

If `a=-r<0`, summing `(25.3)` over `i` yields

```text
c*P_D<=r*P_X=r*(1-P_D),
```

which is `(25.4)`.  If `c=-s<0`, the same sum gives

```text
a*P_X<=s*P_D,
```

which is `(25.5)`.  The strict comparisons with `1/3` are exactly
`c>2r` and `2a>s`. QED.

This proposition does not exclude asymmetric changing clocks; it identifies
what they must accomplish.  It also explains why exponential or other
exchangeable diffuse races fall back into the projective LCP obstruction.
To turn it into a discrete all-behavior theorem one would need a tight
first--second limit for profiles whose first-tie and Never masses vanish.
Profiles with macroscopic first collisions are outside this calculation and
must instead be controlled through the nonsingleton reward rows.

## 26. Discrete common clocks have a fixed Never gain in the diffuse limit

The exchangeable obstruction has a direct formulation in the repository's
countable-time probability mode.  Let `mu_n` be one behavioral quit-time law
on `Nat union {Never}` and let all four players independently use `mu_n`.
Assume the four-clock first outcome becomes diffuse and absorbing:

```text
Pr_4(first coalition is nonsingleton or Never) -> 0. (26.1)
```

**Proposition 20 (exchangeable diffuse gap; reviewed ordinary
mathematics).**  If

```text
sigma=c+2*a>0,                                      (26.2)
```

then the common-clock profiles in `(26.1)` have terminal exploitability
satisfying

```text
liminf_n max_i [B_i(mu_n^4)-U_i(mu_n^4)]
 >= sigma/12.                                       (26.3)
```

This holds for arbitrary fixed rewards on all nonsingleton coalitions.

More quantitatively, let `R>=1` bound the absolute value of every terminal
reward, and for one common clock law let

```text
ell_4=Pr_4(first coalition is nonsingleton or Never).
```

Then its terminal exploitability is at least

```text
sigma/12-10*R*ell_4^(1/4).                          (26.3a)
```

In particular, exploitability below `sigma/24` forces

```text
ell_4 >= (sigma/(240*R))^4.                         (26.3b)
```

**Proof.**  First note that `(26.1)` automatically passes to the deleted
three-clock race in this iid setting.  Let `p_t=Pr_mu(T=t)` for finite `t`,
let `p_infty=Pr_mu(T=Never)`, and put `delta=sup_t p_t`.  The four-clock
collision event contains the event that all four clocks equal any fixed
finite `t`, so

```text
delta^4<=Pr_4(first coalition is nonsingleton).     (26.4)
```

Thus `delta->0`; the Never part of `(26.1)` also gives `p_infty->0`.  If
`R_t=Pr(T>t)` and `S_t=p_t+R_t`, the exact three-clock collision probability
is

```text
sum_t [3*p_t^2*R_t+p_t^3]
 <=3*delta*sum_t p_t*S_t
 <=3*delta.                                         (26.5)
```

The deleted Never probability is `p_infty^3`, so the three-clock first
outcome is likewise asymptotically singleton and absorbing.

For the quantitative form, put `x=ell_4^(1/4)`.  The same estimates give

```text
delta<=x,
p_infty^3<=x^3,
ell_3<=3*x+x^3,                                     (26.5a)
```

where `ell_3` is the deleted three-clock collision-or-Never probability.
Exchangeability makes every surviving singleton outcome equiprobable.
Replacing a bad outcome of total mass `ell_j` by the corresponding ideal
singleton average changes a bounded payoff by at most `2*R*ell_j`.
Therefore the actual Never gain differs from the ideal gain `sigma/12` by at
most

```text
2*R*(ell_4+ell_3)
 <=2*R*(x^4+3*x+x^3)
 <=10*R*x.                                          (26.5b)
```

This proves `(26.3a)`, and `(26.3b)` follows immediately.

Exchangeability and `(26.1)` make each of the four singleton first outcomes
have probability tending to `1/4`.  Boundedness
of the finite reward table makes every nonsingleton and Never contribution
vanish.  Hence every player's prescribed payoff tends to

```text
(B_0+C_0+2*A_1)/4=B_0+sigma/4.                     (26.6)
```

If player `i` deviates to Never, the other three clocks remain iid with law
`mu_n`.  The preceding deletion estimate and exchangeability make their three
singleton first outcomes equiprobable in the limit.  The deviation payoff
therefore tends to

```text
(C_0+2*A_1)/3=B_0+sigma/3.                         (26.7)
```

The best-response cap dominates this legal Never deviation.  Subtracting
`(26.6)` from `(26.7)` gives `sigma/12`, proving `(26.3)`. QED.

Thus a common-clock approximate equilibrium on the positive-surplus side
must retain a nonvanishing joint first-collision/Never defect.  The deletion
step above depends essentially on all clocks having the same law; the result
is not a lower bound for asymmetric clocks.

## 27. Common restricted equilibria reduce the full tail to one Never atom

The finite-watchdog no-go says that a finite deviation menu cannot prove a
full exploitability gap.  In the cyclic four-player class, however, a common
finite-time restriction has a special exact tail audit: all omitted finite
times lie after the entire restricted support and differ from Never on only
one event.

Fix `N` and let

```text
A_N={0,1,...,N,Never}.
```

**Proposition 21 (cyclic common truncation with exact tail error; ordinary
mathematics, awaiting review).**  Every cyclically equivariant four-player
quitting table has a probability law `mu_N` on `A_N` such that the common
profile `mu_N^4` is a Nash equilibrium against all deviations supported on
`A_N`.  If

```text
q_N=mu_N(Never),
```

then its exploitability against unrestricted behavioral deviations in the
full quitting game is at most

```text
max(B_0,0)*q_N^3.                                   (27.1)
```

Consequently, if a sequence of these common restricted equilibria can be
chosen with `q_N->0`, the original game has terminal approximate Nash
profiles against unrestricted behavioral deviations.

**Proof.**  On the simplex of probability laws `mu` on `A_N`, let `BR(mu)`
be the convex hull of pure times maximizing player `0`'s payoff against three
independent opponents with common law `mu`.  Cyclic equivariance and the fact
that the opponent product is invariant under relabeling make this the same
best-response correspondence for every player.  It is nonempty, convex, and
upper hemicontinuous on a finite-dimensional compact simplex.  Kakutani gives

```text
mu_N in BR(mu_N).
```

Thus every player using `mu_N` is a best response inside `A_N`, proving the
restricted common Nash assertion.  The mixed quit-time law is an ordinary
behavioral stopping law through its hazard representation.

It remains to audit the omitted actions rather than assume them away.  Fix a
finite pure Quit time `t>N`.  If at least one opponent chooses a finite time
in `A_N`, the opponents stop before `t`, so player `i` receives exactly the
same terminal reward as under the pure deviation Never.  If all three
opponents choose Never, the deviation at `t` quits alone and pays `B_0`,
whereas Never produces the zero payoff.  Hence the exact identity is

```text
V_i(t;mu_N^3)=V_i(Never;mu_N^3)+B_0*q_N^3.          (27.2)
```

The restricted Nash inequality already controls Never and every time at most
`N`.  Equation `(27.2)` controls every missing finite pure time, and the
pure-time extremality theorem then controls every behavioral deviation.  The
largest omitted gain is at most `(27.1)`. QED.

This is not the invalid claim that a finite menu is exhaustive.  The special
ordered support makes the infinitely many omitted actions payoff-identical,
and `(27.2)` prices their one difference explicitly.  The unresolved
boundary is also exact: in the hard chamber `B_0>0`, failure of this route
requires every selectable common restricted equilibrium to retain a Never
atom bounded away from zero.  No theorem excluding that boundary mass is
claimed here.

## 28. Exact common chronologies cannot diffuse on positive surplus

The common-clock gap also has a phasewise form for an actual exact terminal
Nash profile.  Retain the polynomials `Q(h),W(h)` from Section 3: `Q(h)` is
the payoff from quitting at a common-`h` root, and `W(h)` is the absorbing
opponent-only contribution when continuing.  If an interior common root is
Nash against scalar successor value `u^+`, then

```text
Q(h)=W(h)+(1-h)^3*u^+.
```

Define

```text
S(h)=[Q(h)-W(h)]/(1-h)^3.                           (28.1)
```

The predecessor and successor values at such a root are `Q(h)` and `S(h)`.
At the all-Continue boundary,

```text
Q(0)=S(0)=B_0,
(Q-S)'(0)=c+2*a=sigma.                              (28.2)
```

Indeed `W'(0)=C_0+2*A_1=3*B_0+sigma`, and differentiating `(28.1)` gives
`S'(0)=Q'(0)-sigma`.

**Proposition 22 (macroscopic-root necessity for exact common clocks;
reviewed ordinary mathematics).**  Suppose `B_0>0` and `sigma>0`.
There is `h_0 in (0,1)` such that no exact terminal Nash profile with a common
behavioral root sequence `(h_t)` can satisfy `h_t->0`.  More precisely, on
every interval of live rows with `0<h_t<=h_0`,

```text
u_t-u_(t+1)>= (sigma/2)*h_t,                        (28.3)
```

where `u_t` is the common prescribed payoff of the actual reached tail.
Thus every exact common-clock terminal Nash profile has either a sure root or
infinitely many roots with `h_t>h_0`.

**Proof.**  By `(28.2)` and continuity, choose `h_0>0` so that

```text
Q(h)-S(h)>=(sigma/2)*h       for 0<h<=h_0.          (28.4)
```

If all prior common roots have positive Continue probability, the all-live
history at date `t` has positive probability.  Exact terminal Nash therefore
implies conditional endpoint Nash at that reached history: a profitable tail
deviation would otherwise give a profitable original deviation after
multiplication by the positive reach probability.  Whenever `0<h_t<1`, both
actions are in the common root's support, so

```text
u_t=Q(h_t),       u_(t+1)=S(h_t).
```

This proves `(28.3)`.  A row with `h_t=0` simply copies the actual tail value;
a row with `h_t=1` already gives the macroscopic alternative.

Now suppose `h_t->0` and there is no sure root.  Summing `(28.3)` after the
sequence enters `[0,h_0]`, and using boundedness of actual terminal payoffs,
shows

```text
sum_t h_t<infinity.                                 (28.5)
```

Hence the common four-clock profile has positive probability of Never from
every sufficiently late tail, while the probability of any later absorption
tends to zero as the tail start tends to infinity.  Bounded rewards imply

```text
u_t->0.                                             (28.6)
```

If positive hazards occur infinitely often, then along those rows
`u_t=Q(h_t)->Q(0)=B_0>0`, contradicting `(28.6)`.  If only finitely many are
positive, the actual tail is eventually all-Never, so `u_t=0`; but at an
all-Continue root immediate Quit pays `B_0>0`, contradicting conditional
Nash.  Therefore `h_t` cannot tend to zero. QED.

This result concerns exact common clocks only.  Approximate terminal Nash does
not automatically give a useful late conditional error after division by a
small reach probability, and asymmetric root sequences have vector rather
than scalar continuation values.  The theorem nevertheless closes the
genuinely nonperiodic **common diffuse** escape, leaving common macroscopic
roots and asymmetric changing clocks as the live regimes.

## 29. Concrete next question: independent rank feasibility

The remaining diffuse boundary is a probability problem before it is a
reward-table problem.  Determine whether four independent atomless clocks can
satisfy `(25.2)--(25.3)` in either strict mixed-sign chamber.  Two normalized
test points are:

```text
(a,c)=(-1,3):
  3*z_partner >= z_cross,
  3*pi_partner <= pi_cross,
  hence P_D<=1/4;

(a,c)=(1,-1):
  z_cross >= z_partner,
  pi_cross <= pi_partner,
  hence P_D>=1/2.                                   (29.1)
```

Here `z_cross` and `pi_cross` mean the sums over the two opposite players for
the displayed row.  A construction would exhibit the asymmetric rank bias
that Sections 23--28 leave alive; an impossibility theorem would exclude all
diffuse singleton-only escapes in that chamber, not merely another finite
support menu.  Any proposed inequality must use independence of the four
clock laws: the four equally weighted cyclic permutations realize the desired
rank patterns as a correlated distribution, so an argument valid for
arbitrary random rankings cannot work.

Even a negative answer to `(29.1)` would still leave macroscopic first ties,
whose incentives depend on the pair/triple/grand rows.  That separation is
intentional: first settle the exact independent-rank boundary, then combine
it with explicit collision-row inequalities rather than silently assuming
diffuseness.

## 30. Exact independent-rank regression: the endpoint inequalities are feasible

The first test point in `(29.1)` is in fact feasible for independent clocks.
Thus Proposition 19 is a genuine filter, not already a contradiction.

Give each player three private real times with no support point shared across
players.  Across all twelve support points, impose the strict order

```text
2a < 2b < 3a < 0a < 0b < 1a
   < 3b < 2c < 3c < 1b < 0c < 1c.                 (30.1)
```

Let the independent probability vectors on each player's three displayed
times be

```text
player 0: (6063,    7, 3930)/10000,
player 1: (6873, 2972,  155)/10000,
player 2: (  64,  622, 9314)/10000,
player 3: (2104, 1764, 6132)/10000.                 (30.2)
```

There are no cross-player ties, although each individual clock law is atomic.
Direct enumeration of the `3^4=81` pure clock tuples
gives first-quitter probabilities, over the common denominator `10^16`,

```text
z=(4464080980800000,
   1986471175016160,
   1387873444951280,
   2161574399232560)/10^16.                         (30.3)
```

**Proposition 23 (endpoint rank feasibility; exact rational experiment,
awaiting review).**  For `(a,c)=(-1,3)`, all four Quit-now inequalities and
all four Never inequalities `(25.2)--(25.3)` hold strictly for `(30.1)--(30.2)`.
In the player order `0,2,1,3`, the eight nonnegative left-hand slacks are

```text
(  15574760605120, 127824684765120,
 9244197368151280,  72709368151280,
  632768771946400, 211326720746400,
  107459099297200,  44281920897200)/10^16.          (30.4)
```

The designated-partner first--second probability is

```text
P_D=2385964326360000/10^16<1/4,                    (30.5)
```

as required by `(25.4)`.

This law is **not** a terminal equilibrium.  For example, take the singleton
baseline `B_0=0`, so partner singleton reward is `3` and either opposite
singleton reward is `-1`.  Player `0`'s prescribed payoff is the first slack
in `(30.4)`, namely

```text
U_0=15574760605120/10^16.
```

If player `0` instead quits strictly after the first two support points in
`(30.1)` and before the third, only its partner player `2` can have stopped.
That partner is early with probability `(64+622)/10000`, so the deviation
pays

```text
3*(686/10000)=1029/5000.
```

The gain is greater than `1/5`.  Hence checking only the two endpoint
deviations Quit-now and Never misses a large profitable intermediate stopping
time, even after all their aggregate rank inequalities are strict.

The calculation changes the concrete next question.  One must exploit the
whole pure-time payoff curve

```text
f_i(t)=B_0
 +c*Pr(partner is first before t)
 +a*Pr(an opposite is first before t),              (30.6)
```

not merely its initial and terminal values.  A successful diffuse no-go
would show that independent clocks satisfying the endpoint signs necessarily
create an interior overshoot for some player; `(30.1)--(30.4)` is now an
exact stress case for that statement.

If literal atomlessness is desired, replace each of the twelve support points
by a sufficiently small disjoint interval and use any continuous density of
the same total mass inside it.  The global block order `(30.1)`, and hence
every first/second probability and inequality above, is unchanged.
