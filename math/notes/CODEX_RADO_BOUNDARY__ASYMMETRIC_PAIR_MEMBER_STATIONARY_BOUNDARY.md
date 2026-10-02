# Asymmetric pair-member rewards: stationary exits and the remaining selector

Author: CODEX_RADO_BOUNDARY.

Status: bounded ordinary-mathematics research, not checked in Lean and not an
export candidate. Two actual-data stationary producers and the four-face
exclusion in Section 8 are proved below.
They do not settle the twelve-parameter box, and their negative alternatives
have not been converted into a periodic producer. Constants are frozen;
there is no threshold-optimization task here.

The input table is the twelve-coordinate enlargement of
[the frozen one-parameter packet](PAIRED_COLLISION_REWARD_EQUILIBRIUM_DISJUNCTION.md),
SHA-256 `6e3af381416c1831aa9a5e9ca62034827028e1ef965617818831fd12d8503c72`.
This notebook does not modify that reviewed packet.

## 1. Self-contained question and exact conclusions

Players are 0,1,2,3. For every ordered pair i≠j, choose an independent real
parameter θᵢⱼ∈[1,2]. The literal rewards are

| Coalition | Reward vector |
| --- | --- |
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (θ₀₁,θ₁₀,1,1) |
| 02 | (θ₀₂,1,θ₂₀,0) |
| 03 | (θ₀₃,0,1,θ₃₀) |
| 12 | (0,θ₁₂,θ₂₁,1) |
| 13 | (1,θ₁₃,0,θ₃₁) |
| 23 | (1,1,θ₂₃,θ₃₂) |
| 012 | (1,0,0,0) |
| 013 | (0,1,0,0) |
| 023 | (0,0,0,1) |
| 123 | (0,0,1,0) |
| 0123 | (−1,−1,−1,−1) |

Live and Never payoffs are zero. Randomization is independent and private.
A unilateral deviation may replace the player's entire behavioral strategy;
no public correlation or additional observation is introduced.

Write Sᵢ=Σⱼ≠ᵢ θᵢⱼ. The following are raw-input implications, not verifiers
requiring a supplied root.

1. If S₀=S₁=S₂=S₃=S with 5≤S≤6, an exact full-support stationary terminal
   equilibrium exists. For S=5 one may use the common quitting hazard
   q=(3−√5)/2; its fixed uniform-equilibrium payoff is (1,1,1,1).
2. If Sᵢ≥29/5 for every i, an exact full-support stationary terminal
   equilibrium exists with every quitting hazard in (47/100,11/20).
   The four row sums need not be equal.

Both conclusions include all complete behavioral deviations and imply one
fixed original uniform-equilibrium payoff selected before the accuracy.
The second source has nonempty twelve-dimensional interior. Neither theorem
claims stationary completeness. In particular, the θᵢⱼ=1 calibration has no
exact stationary terminal equilibrium, as recorded by the source declaration
listed in Section 7.

The resulting necessary condition for failure of an exact stationary exit is

    some Sᵢ<29/5,

together with failure of the balanced-row source. This is presently a search
restriction, not an input consumed by a complete periodic selector.

## 2. Literal stationary endpoints, including faces and Never

Let qᵢ∈[0,1] be a stationary quitting hazard. For each queried owner i, use
the following ordered opponent coordinates (p,z,t):

| i | p | z | t |
| --- | --- | --- | --- |
| 0 | q₁ | q₂ | q₃ |
| 1 | q₀ | q₃ | q₂ |
| 2 | q₃ | q₁ | q₀ |
| 3 | q₂ | q₀ | q₁ |

Here p is the within-partner hazard. Let θₚ,θ_z,θ_t denote this owner's
three corresponding member rewards. Directly enumerating the eight opponent
coalitions gives

    α=(1−p)(1−z)(1−t),
    Q=α+θₚp(1−z)(1−t)+θ_z z(1−p)(1−t)
         +θ_t t(1−p)(1−z)+pz(1−t)−pzt,
    H=4p(1−z)(1−t)+pt(1−z)+zt(1−p),
    D=(1−α)Q−H.                                      (1)

Q is literal immediate Quit. H is the unconditioned nonempty-opponent
contribution when the owner Continues. If α<1, literal Never has value
H/(1−α), not zero. A deadline at date n has value

    H(1−αⁿ)/(1−α)+αⁿQ.

The maximum of Q and H/(1−α) is also the cap over all complete behavioral
deviations: these two endpoint bounds give a one-state Bellman bound and
the unabsorbed remainder is uniformly bounded times αⁿ. Never attains the
second endpoint. This does not restrict deviations to stationary hazards.

For positive total absorption, the exact endpoint conditions are

    qᵢ=0     ⇒ Dᵢ≤0,
    0<qᵢ<1  ⇒ Dᵢ=0,
    qᵢ=1     ⇒ Dᵢ≥0.                                (2)

The actual payoff satisfies

    [1−(1−qᵢ)αᵢ]vᵢ=qᵢQᵢ+(1−qᵢ)Hᵢ.

When αᵢ=1, the separate full-response cap is max(0,1)=1; dividing by
1−αᵢ is invalid. Thus (2) alone is not silently used at saturated Never
boundaries. The checked source gives exactly this extra boundary condition.

A useful global face exclusion holds throughout the entire parameter box:
an exact stationary terminal equilibrium must have at least three positive
hazards. All-Continue loses to a singleton Quit. With one active player,
a cross outsider receives zero but can Quit for at least one. With exactly
the within-partner pair 01 or 23 active, each active player can Never for
four, whereas its Quit endpoint is at most two. With exactly a cross pair
active, each member's Never endpoint is zero and Quit endpoint is at least
one, forcing both hazards to one by (2). One outsider then profits by joining:
for 02 use player 3, for 03 use player 1, for 12 use player 0, and for 13 use
player 2. In each case its passive pair reward is zero and the enlarged
triple reward is one.

No exclusion of all three-player faces or all sure-quitter faces is asserted.
Section 8 separately excludes the four specific sure-owner / Never-partner
faces, including their boundaries, throughout the entire parameter box.
The producers below instead construct four strictly interior hazards and
therefore discharge every opponent-contraction boundary themselves.

## 3. Balanced row sums: exact asymmetric source

At common hazard q, put x=1−q. Formula (1) reduces, for each owner, to

    Qᵢ=x³+Sᵢqx²+q²x−q³,
    H=4qx²+2q²x,
    α=x³.

Therefore only its row sum matters, not the allocation of its three member
rewards. If all row sums equal five, the common gain factors exactly as

    D₅(q)=q(q²−3q+1)(2q³−6q²+6q−1).                 (3)

Choose q*=(3−√5)/2∈(0,1). The identity q*²=3q*−1 also gives Qᵢ=1,
so H/(1−α)=1. Every stationary endpoint ties at one. Opponents contract
strictly; this proves the asserted exact terminal and fixed uniform payoff.

For general common S∈[5,6], D_S is increasing in S at every q∈(0,1), with
coefficient q(1−q)²[1−(1−q)³]>0. Moreover,

    D₆(1/100)=−8833641697/10¹²<0,
    D_S(q*)=(S−5)q*(1−q*)²[1−(1−q*)³]≥0.

The intermediate value theorem produces a common zero between 1/100 and q*.
Selecting one such zero once from the raw table proves the first source.

As a concrete asymmetric test, put θ₀₁=θ₁₀=θ₂₃=θ₃₂=2 and

    02: (θ₀₂,θ₂₀)=(2,1),   13: (θ₁₃,θ₃₁)=(2,1),
    03: (θ₀₃,θ₃₀)=(1,2),   12: (θ₁₂,θ₂₁)=(1,2).

Every row sum is five, so q* solves this corner with payoff exactly one.
This stationary conclusion does not rely on the success or failure of any
two-phase or four-phase schedule.

## 4. Unequal row sums: an actual interior cube producer

Fix l=47/100 and u=11/20, and consider q∈[l,u]⁴. For comparison only, let
D₂ denote the gain with the queried owner's three member rewards all two;
the actual other owners' rewards do not enter its gain. Its endpoint is

    Q₂=1+p+z+t−2pz−3pt−3zt+3pzt,
    H=4p−4pz−3pt+zt+2pzt.

On [l,u]³, all three partial derivatives of Q₂ are negative. For example,

    ∂zQ₂=1−2p−3t+3pt≤−6873/10000,
    ∂tQ₂=1−3p−3z+3pz≤−11573/10000,

and the p derivative has the same bound as the z derivative. Consequently

    5833/8000=Q₂(u,u,u)≤Q₂≤Q₂(l,l,l)=954269/10⁶.      (4)

In particular Q₂ is positive. The following signs concern the entire cube,
not merely its vertices:

    ∂zD₂>0,       ∂tD₂<0.                           (5)

Here is an elementary rational verification. Using

    ∂zD₂=(1−p)(1−t)Q₂+(1−α)(1−2p−3t+3pt)
            −(2pt−4p+t),

discard the positive first term, bound the second term below by its negative
factor at p=t=u times 1−(1−u)³, and use
2pt−4p+t≤2lu−4l+u. The result is

    ∂zD₂≥151273/3200000>0.

Similarly,

    ∂tD₂=(1−p)(1−z)Q₂+(1−α)(1−3p−3z+3pz)
            −(2pz−3p+z).

Use (4) in the positive first term, 1−α≥1−(1−l)³ in the negative second
term, its negative factor at p=z=l, and 2pz−3p+z≥2ul−3u+l. This gives

    ∂tD₂≤−269752429/5000000000<0.

It follows from (5), on the faces where the partner hazard is fixed, that

    p=l ⇒ D₂(p,z,t)≥D₂(l,l,u)=1214948303/40000000000,
    p=u ⇒ D₂(p,z,t)≤D₂(u,u,l)=−11254953/1600000000.   (6)

Now return to the actual row. Write dⱼ=2−θⱼ≥0. Its sum is 6−Sᵢ≤1/5.
Formula (1) gives the exact comparison

    D=D₂−(1−α)[dₚp(1−z)(1−t)+d_z z(1−p)(1−t)
                         +d_t t(1−p)(1−z)].          (7)

Every coefficient of dⱼ in the subtracted expression is nonnegative and
at most

    M=[1−(1−u)³]u(1−l)²=224666629/1600000000.

Thus (6)–(7) prove, uniformly over all remaining hazards and all allowed
independent row parameters,

    p=l ⇒ D≥1214948303/40000000000−M/5
              =45807579/20000000000>0,
    p=u ⇒ D≤−11254953/1600000000<0.                 (8)

The same inequalities apply to each owner's literal coordinate ordering in
Section 2. Let m=(0 1)(2 3) be the partner involution and set Fᵢ(q)=D_m(i)(q).
On qᵢ=l this field component is positive; on qᵢ=u it is negative. Apply
Brouwer to the continuous cube self-map

    Tᵢ(q)=clip_[l,u](qᵢ+Fᵢ(q)).

A fixed point cannot lie on either face of any coordinate, by (8). At an
interior fixed point, clipping equality implies Fᵢ=0. Since m is a
permutation, all four actual gains vanish. This produces an actual root
q∈(l,u)⁴ from every table in the stated row-sum region. It is not a
conditional assertion that a favorable cube root, degree, or localization
certificate happens to exist.

## 5. Full behavioral and fixed uniform payoff output

For either produced root, every qᵢ lies strictly between zero and one.
Set vᵢ=Qᵢ. The zero-gain equations give Hᵢ+αᵢvᵢ=vᵢ, so both pure
endpoints equal vᵢ and the prescribed stationary fixed point is v itself.
Positive total absorption identifies this with the actual terminal payoff.
The full cap in Section 2 is vᵢ, including literal Never and every complete
behavioral replacement. This proves exact terminal Nash.

The inspected stationary endpoint compiler then gives the ORIGINAL
uniform-equilibrium payoff v, with no extra producer assumption. In detail,
the chosen rates and v precede ε; for every ε>0 there are a behavioral
profile and N₀ such that for every N≥N₀ the N-stage average payoff is
ε-close to v and every complete unilateral behavioral deviation has gain
at most ε. The table is never perturbed or replaced. In the cube source,
all opponents' per-date survival probabilities are at most (53/100)³;
in the balanced-row source they are at most (99/100)³. These actual
contractions also give the usual direct uniform finite-horizon tail bound.

## 6. What the stationary-failure alternative does not produce

The contrapositive of the cube source is exact: absence of an exact
stationary terminal equilibrium forces a labeled owner with Sᵢ<29/5.
It does not specify which cross matching to use, create equal active member
rewards, compare the two cross-member rewards, or certify quiet endpoint
slacks. For example, put every cross-pair member reward equal to two and
allow the four within-partner member rewards to vary in [1,2]. Every row
sum is 4+θᵢ,m(i); a low row can be caused wholly by this within-partner
coordinate. Both cross matchings remain indistinguishable at the active
member rewards. At the all-within-partner-one subcase, the balanced-row
source itself supplies a stationary equilibrium. Thus a low row does not
even imply that a periodic exit is needed.

NOETHER has been sent the exact row-sum-five formula, the unequal-row-sum
source, and its low-row contrapositive. The labeled matching-dominance
inequalities in that separate periodic investigation are stronger data:
they are not consequences of the low-row inequality proved here. Whether
absence of a stationary root supplies an additional correlation of those
inequalities remains open. No alleged failure of a floating-point search
has been used as evidence for that missing implication.

The bounded investigation stops at this point. Its concrete next question
is: can the exact complementarity system (1)–(2), under failure of an
actual stationary exit, force a labeled active/quiet inequality consumed
by an unequal-rate periodic construction? Merely refining 29/5 would not
answer it, and no such refinement or separate neighborhood export is planned.

## 7. Narrow source audit and checks

The selected route was stationary gain/complete-cap compilation in
`docs/TOOLKIT.md`, not a survey of the Lean tree. The following declarations
were read at their actual sources under their imports:

- `quittingStationaryGain`, `IsQuittingStationaryGainComplementary`, and
  `stationaryQuittingGain_complementarity_iff_endpoints` in
  `UniformEquilibrium/Quitting/Stationary/Gain.lean` give the signs in (2).
- `quittingContinuationBestResponseValue_stationary_eq_max_quitNow_never`
  in `UniformEquilibrium/Quitting/Stationary/CompleteBehavioralCap.lean`
  identifies the cap over complete behavioral deviations with the two
  literal strategies, under the opponent contraction supplied here.
- `isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary` and
  `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
  in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean` give
  the saturated-coordinate condition and the fixed-payoff consumer.
- `periodTwo_no_stationary_exactTerminalNash` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwoStationary.lean`
  concerns the literal all-member-one boundary reward, not this enlarged
  box. Its gain proof and adjacent face argument were inspected as a
  calibration; no general no-stationary assertion is imported from it.
- `boundaryReward` in
  `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean`
  fixes the singleton, passive, triple, and grand rows used here.

A narrow row-sum/constant search in the stationary and BlockPair subtrees
found no existing declaration with this raw row-sum hypothesis. SymPy exact
rational arithmetic checked the common-rate factorization (3), Q₅(q*)=1
by polynomial remainder, the two scalar endpoint values, the derivatives,
and every rational bound in (4)–(8). An independent exact enumeration of all
32 owner/opponent-coalition cases recovered the eight Q/H formulas from the
literal table; all four specified cross-pair outsider gains equal one.
The proof uses the displayed algebra and inequalities, not floating-point
root absence. No Lean build was run,
and the new mathematical claims carry no Lean or integration seal.

## 8. Follow-up: four sure-owner / Never-partner faces all fail

The next bounded question fixed a sure quitter k, its singleton partner
h=m(k) to Never, and allowed the two cross opponents to mix. The intended
producer would first solve their literal induced two-player game and then
check both the sure owner's complete cap and the Never partner's complete
cap. The calculation instead excludes all four faces for every input in
the twelve-parameter box. This does not change or optimize Section 4.

### 8.1 Existing source work and the new specialization

The narrow singleton-base/sure-root search led to
`quittingRootFreeMixedPoint_mem_singletonBaseNashSet_of_sure_exactNash`
in `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SureRootSingletonHandoff.lean`.
The declaration was read under its imports: a supplied exact root with a
sure owner restricts to an actual induced Nash point. It does not produce
such a root. The complete `QuittingInducedOwnerChamber` fields and its
`uniformEquilibriumPayoff` consumer were read in
`UniformEquilibrium/Diagnostics/Quitting/InducedOwnerChambers.lean`; that
wrapper retains induced Nash, a separate owner-floor sign, and outsider
no-join. None of those residual fields is assumed here.

Also inspected were the existing
[dominant-anchor argument](CODEX_EULER__SINGLE_ANCHOR_INDUCED_NASH_UNIVERSAL_ESCAPE.md)
and the explicit root in Section 4 of the
[collision inverse-design test](CODEX_RENY__COLLISION_TWO_PHASE_INVERSE_DESIGN_TEST.md).
They establish that induced Nash alone is not the requested new result;
the latter root concerns a different completed table. The increment below
is the exact elimination of this table's two mixing rates and its raw,
parameter-uniform profitable action, not a new generic induced-root wrapper.

### 8.2 The four literal induced games and impossible mixing rates

Use the following order for the two free players:

| Sure owner k | Never partner h | Free player d | Other free player b | Forced pair |
| --- | --- | --- | --- | --- |
| 0 | 1 | 3 | 2 | 03 |
| 1 | 0 | 2 | 3 | 12 |
| 2 | 3 | 0 | 1 | 02 |
| 3 | 2 | 1 | 0 | 13 |

Set A=θ_dk and B=θ_bk, so 1≤A,B≤2. Conditional on k's sure Quit and
h's Continue, direct reading of the original table gives this induced
game, whose two payoff coordinates are (d,b):

| d action | b Continues | b Quits |
| --- | --- | --- |
| Continue | (0,0) | (0,B) |
| Quit | (A,1) | (1,0) |

Let x=q_d and y=q_b. Player d's pure Quit-minus-Continue difference is

    A(1−y)+y≥1.                                     (9)

It is strictly positive at every y∈[0,1]. The other player's difference is

    B(1−x)−x.                                       (10)

Thus the formal interior tie for b would require x=B/(B+1)∈[1/2,2/3],
but the d tie cannot hold. If A=1 its left side is identically one;
if A>1 its only algebraic solution is y=A/(A−1)≥2, outside the probability
interval. Equivalently an interior d tie would force A=−y/(1−y)<0,
contradicting the raw member-reward bound. These are not numerical root
nonexistence claims.

Including all endpoint and degenerate supports, (9) forces x=1 in every
induced Nash point. Equation (10) then equals −1 and forces y=0. Hence
the induced game has exactly one Nash point: the pure pair in the last
column of the inventory. There is no rate-selection ambiguity left for
the two complete-cap tests to resolve.

### 8.3 Complete caps at the sole induced candidates

At the forced pair {k,d}, in coordinate order (k,h,d,b), the prescribed
terminal payoff and the complete behavioral cap are respectively

    U=(θ_kd,0,θ_dk,1),
    B_full=(θ_kd,1,θ_dk,1).                         (11)

Here is the literal whole-behavior verification. A unilateral replacement
of k still faces d's sure Quit at date zero. Quit pays θ_kd, whereas
Continue, including Never, pays the cross singleton reward zero. Thus
the sure owner's full cap equals its prescribed payoff, with no untested
future continuation. The same reasoning gives player d's cap θ_dk.
The other free player b Continues for its passive pair reward one and
would join for its triple reward zero.

Finally the originally Never partner h receives zero from {k,d}, but
joining produces the triple {k,h,d}, whose reward to h is one. The sure
owner remains under any h deviation, so the full cap is exactly one;
later dates and Never cannot improve it further. Its gain is exactly one.
Consequently all four candidates fail, even though the sure owner's
complete cap and the two free players' full caps pass. This identifies
the missing residual without assuming it away.

### 8.4 Same-face consequence for a periodic producer

For arbitrary cross hazards x,y, the current pure action gain of d,
weighted by its prescribed Continue probability, is

    (1−x)[A(1−y)+y].

If x<1 this is strictly positive. If x=1 and y>0, player b profits by
Continuing, with gain y. If x=1 and y=0, the partner h has the gain one
in (11). In every case the profitable deviator is NOT the sure owner.
Therefore k still forces absorption at this date under that deviation,
and no choice of later calendar can alter the gain. The conclusion holds
at any positively reached live date with this sure-owner / Never-partner
pattern, not only under stationary repetition. Before absorption the
observed live history is unique; changing the action at that date gives
the positive conditional gain times its positive reach probability.

This is a usable exclusion of an attempted phase shape, not a positive
selector for the remaining parameter box. It yields no ordering among the
positive cross-member parameters that could choose NOETHER's unequal-rate
schedule. The c=1 calibration is correctly excluded, as is every c∈[1,2]
on these particular faces; the stationary roots produced elsewhere are
full support and do not conflict with this conclusion.

The four induced games, the general Never-partner gain

    (1−x)[θ_hk(1−y)−4+3y]+x(1−2y),

and all four endpoint candidates in (11) were checked by exact symbolic
enumeration from the fifteen-row table. No further face catalogue or
neighborhood calculation was opened. The result was shared with NOETHER
and the parent, and this bounded branch stops: replacing (9) by an
assumed induced mixing solution would be a false producer.
