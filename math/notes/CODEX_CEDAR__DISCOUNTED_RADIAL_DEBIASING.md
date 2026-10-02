# CODEX_CEDAR — discounted radial debiasing and the stationary refusal price

## Current best attempt

**Exact reviewable claim.**  Propositions 1--3 compute the literal stationary
terminal value and complete unrestricted regret of a discounted Bellman root.
In the matching regime, a positive active endpoint has a nonvanishing pure-
Never refusal price.  Propositions 4--6 prove that every analytic Bellman germ
of the Solan--Vieille `boundaryReward` is matching, has the unique packet
`cemetery=singleton_i=1/5`, and has refusal limit `1/12` for every player.
Proposition 7 gives an exact same-singleton completion with a pure absorbing
analytic branch, proving that the projective packet alone cannot select the
needed coarse repair.

**Status.**  CLOSED as a conjecture-closing route.  Propositions 1--7 are
proved below as ordinary mathematics from named checked interfaces; the new
combined statements are not checked in Lean.  The local branch-switch thesis
is falsified because every germ of the hard table has the same signed defect.
The broader packet-only thesis is falsified because collision completions with
identical packet data have different coarse analytic branches.  A universal
construction using the full reward table remains open, but no invariant beyond
the already checked special period-two compiler was found.

**Sections to check.**  Section 3 for debiasing and unrestricted regret,
Section 4 for the exact limit, and Sections 5.4--5.6 for the unique packet,
all-germ trichotomy, and same-singleton falsifier.

## 1. Self-contained question

Fix a finite nonempty player set `I` and a quitting reward table `r`.  At one
discount parameter let

- `lambda in (0,1)` be the discount complement and `d=1-lambda`;
- `p_i in [0,1]` be the stationary Quit probabilities;
- `Q=prod_i(1-p_i)` be the joint Continue mass;
- `q_i=prod_{j != i}(1-p_j)` be opponent Continue mass;
- `R in R^I` be the selected root's unconditional absorbing-reward
  contribution; and
- `v in R^I` be a discounted stationary Bellman value.

The exact Bellman conditions used here are

\[
 v=d(R+Qv)                                                     \tag{1.1}
\]

and exact endpoint Nash of the product root against continuation `v`.  No
claim is made about discounted payoff itself being a terminal payoff.

Question: what is the actual terminal payoff of stationary repetition of
`p`, what is its full behavioral exploitability, and which datum must a
vanishing-discount producer add to remove the artificial cemetery price?

## 2. Bounded source audit

The narrow lookup inspected only these declarations and their local
definitions.

- `nonempty_analyticBellmanGerm_quittingGame`,
  `quittingGermValue_eq_smul_rootSuccessorPayoff`, and
  `isεQuittingRootEndpointNash_quittingGermRoot`
  (`UniformEquilibrium/Quitting/Boundary/Analytic/Germ.lean`) supply an
  analytic germ for every quitting table, the exact discounted fixed-point
  equation, and endpoint Nash on the physical discount domain.
- `QuittingGermMatchingLeadingData.value_eq_singleton_mix` and
  `QuittingGermMatchingLeadingData.positive_singleton_pins`
  (`UniformEquilibrium/Quitting/Projective/AnalyticPacket.lean`) identify the
  matching packet and pin every positive leading owner at its solo payoff.
- `quittingStationaryFullRateUnilateralCap`,
  `isεAsymptoticNash_stationary_iff_fullRateUnilateralCap_le`
  (`UniformEquilibrium/Quitting/Stationary/FullRateStationaryVerifier.lean`),
  and `quittingStationaryUnilateralCap_eq_max_div`
  (`UniformEquilibrium/Quitting/Stationary/MinMax.lean`) identify the exact
  unrestricted behavioral best-response cap of a stationary root.
- `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
  (`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`) is the
  checked all-behavior consumer when the debiased root is an endpoint-Nash
  fixed point and every opponent clock contracts.
- `QuittingProjectiveTargetMismatch.equilibrium` and the exact late-Quit
  obstruction in
  `UniformEquilibrium/Quitting/Projective/TargetMismatch.lean` provide the
  smallest source-matched regression.
- `periodTwo_singletonMatrix`, `normalizedSoloMatrix_periodTwo`, and
  `pairedSingletonMatrix_noHomogeneous`
  (`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean`,
  `FourPlayerPairedSingletonResidualHard.lean`, and
  `FourPlayerPairedSingletonLCP.lean`) identify the literal boundary table's
  normalized singleton matrix and exclude a zero-cemetery homogeneous packet.
- `quittingGerm_endpoint_fixedPoint`,
  `quittingGerm_endpoint_endpointNash`,
  `quittingGerm_endpointValue_eq_solo_of_positive_leadingShare`,
  `QuittingGermFastLeadingData.toProjectiveSingletonPacket`, and
  `quittingGermValue_zero_eq_zero_of_discount_dominates`
  (`UniformEquilibrium/Quitting/Classification/ThreePlayer/AuxiliaryShift.lean`
  and `AnalyticPacket.lean`) supply the exact endpoint and nonmatching-order
  alternatives used in Proposition 6.  Despite the directory name, these
  declarations are polymorphic in the finite player type.
- `periodTwo_no_stationary_exactTerminalNash`
  (`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwoStationary.lean`)
  excludes the absorbing endpoint after the full stationary deviation check.

A narrow search for `radial`, `uplift`, `discounted stationary`, and
`endpointNash stationary` found the projective target-mismatch regression and
the general stationary endpoint compiler, but no declaration carrying out
the exact debiasing/regret calculation below.  The checked projective packet
already proves that the raw analytic endpoint need not be a uniform target;
the contribution here is the exact terminal replacement and its playerwise
all-behavior price.

## 3. Exact finite-discount algebra

Write the selected root expectation against a tail `y` as

\[
 F_i(y)=R_i+Qy_i.
\]

For player `i`, write

\[
 \operatorname{Quit}_i
 \quad\hbox{and}\quad
 \operatorname{Cont}_i(y)=E_i+q_i y_i
\]

for the pure-Quit and pure-Continue endpoint values, and put

\[
 D_i(y)=\operatorname{Quit}_i-\operatorname{Cont}_i(y).
\]

### Proposition 1 (exact cemetery debiasing)

Assume (1.1) and `Q<1`.  Define

\[
 \kappa:=\frac{1/d-Q}{1-Q}
       =1+\frac{\lambda}{d(1-Q)},\qquad u:=\kappa v.             \tag{3.1}
\]

Then

\[
 u=R+Qu.                                                       \tag{3.2}
\]

Consequently stationary repetition absorbs almost surely and its literal
terminal payoff vector is exactly `u`.  Moreover

\[
 D_i(u)=D_i(v)-q_i(\kappa-1)v_i.                              \tag{3.3}
\]

#### Proof

Equation (1.1) gives

\[
 R=(1/d-Q)v=(1-Q)u,
\]

which is (3.2).  Since `Q<1`, stationary joint survival is `Q^N -> 0`, so
the unconditional absorbing contribution sums to
`sum_N Q^N R=R/(1-Q)=u`.  Pure Quit has no all-Continue continuation term,
whereas pure Continue changes by exactly `q_i(u_i-v_i)`.  This is (3.3).
All identities are vectorwise exact; there is no asymptotic interchange.

### Proposition 2 (exact unrestricted regret after debiasing)

Assume additionally `q_i<1`.  Let `p_i` be player `i`'s selected Quit
probability and set `D_i:=D_i(u)`.  The gain of pure Quit over the prescribed
terminal payoff is

\[
 (1-p_i)D_i,                                                  \tag{3.4}
\]

and the gain of pure Never is

\[
 -\frac{p_iD_i}{1-q_i}.                                      \tag{3.5}
\]

The exact unrestricted behavioral regret is therefore

\[
 \operatorname{Reg}_i
 =\max\left\{0,(1-p_i)D_i,-\frac{p_iD_i}{1-q_i}\right\}.       \tag{3.6}
\]

If `0<p_i<1`, endpoint Nash against `v` gives `D_i(v)=0`; hence

\[
\operatorname{Reg}_i=
\begin{cases}
 \displaystyle
 \frac{p_iq_i(\kappa-1)v_i}{1-q_i},&v_i>0
       \quad\text{(pure Never)},\\[6pt]
 (1-p_i)q_i(\kappa-1)(-v_i),&v_i<0
       \quad\text{(pure Quit)},\\[3pt]
 0,&v_i=0.
\end{cases}                                                   \tag{3.7}
\]

#### Proof

At the fixed point `u`, selected mixing gives

\[
 u_i=p_i\operatorname{Quit}_i+(1-p_i)\operatorname{Cont}_i(u).
\]

Subtracting yields (3.4) and
`Cont_i(u)-u_i=-p_iD_i`.  Against stationary opponents, pure Never has value
`E_i/(1-q_i)`.  Therefore

\[
 \frac{E_i}{1-q_i}-u_i
 =\frac{\operatorname{Cont}_i(u)-u_i}{1-q_i}
 =-\frac{p_iD_i}{1-q_i},
\]

which is (3.5).  The exact stationary Snell cap is the maximum of pure Quit
and pure Never, so (3.6) covers every history-dependent behavioral deviation,
not only one-shot deviations.  For an interior mixed coordinate,
complementarity gives `D_i(v)=0`; now use (3.3) and split by the sign of
`v_i`.

### Corollary 2A (an exact sign-compatible stationary producer)

Suppose every `q_i<1` and the discounted endpoint signs satisfy

```text
p_i = 0       => v_i >= 0,
0 < p_i < 1   => v_i = 0,
p_i = 1       => v_i <= 0.
```

Then the debiased root is exact endpoint Nash against its actual payoff `u`.
It is therefore an exact terminal Nash profile against unrestricted
behavioral deviations, and `u` is a uniform-equilibrium payoff by
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`.

#### Proof

For `p_i=0`, endpoint Nash at `v` gives `D_i(v)<=0`; since `u_i-v_i>=0`,
(3.3) preserves this inequality.  For an interior coordinate, (3.3) is
unchanged because `v_i=0`.  For `p_i=1`, endpoint Nash gives `D_i(v)>=0`;
since `u_i-v_i<=0`, (3.3) again preserves the required inequality.  Equation
(3.2) is the fixed point, and opponent contraction makes the stationary
boundary packet vacuous.

This corollary is a conditional producer from actual discounted Bellman data,
not a claim that an arbitrary game has a germ with these signs.

## 4. Matching analytic limit

Let `lambda(t)=t^r`, suppose

\[
 \frac{p_i(t)}{\lambda(t)}\longrightarrow a_i\ge0,
 \qquad A:=\sum_j a_j>0,                                      \tag{4.1}
\]

and let `v(t)->v^0`.  Finite product expansion gives

\[
 \frac{1-Q(t)}{\lambda(t)}\to A,qquad
 \kappa(t)-1\to\frac1A.                                     \tag{4.2}
\]

For an owner with `a_i>0`, `p_i(t)` is eventually interior.  If also
`A-a_i>0`, then

\[
 \frac{1-q_i(t)}{\lambda(t)}\to A-a_i.                        \tag{4.3}
\]

### Proposition 3 (nonvanishing radial price)

Under (4.1)--(4.3), the exact stationary regret from (3.7) has the limits

\[
 v_i^0>0\quad\Longrightarrow\quad
 \operatorname{Reg}_i(t)\to
 \frac{a_i}{A-a_i}\frac{v_i^0}{A}>0,                         \tag{4.4}
\]

and

\[
 v_i^0<0\quad\Longrightarrow\quad
 \operatorname{Reg}_i(t)\to\frac{-v_i^0}{A}>0.               \tag{4.5}
\]

Thus stationary repetition of a matching germ cannot itself produce
terminal approximate Nash profiles whenever a same-order active owner has a
nonzero analytic endpoint coordinate.  By
`positive_singleton_pins`, this is exactly a nonzero own singleton payoff on
the matching packet support.

#### Proof

For positive `v_i^0`, substitute (4.2)--(4.3) into the first line of (3.7):
`p_i/(1-q_i)->a_i/(A-a_i)`, `q_i->1`, and
`(kappa-1)v_i->v_i^0/A`.  For negative `v_i^0`, the second line of (3.7) has
`1-p_i->1` and the same last two limits.  No uniform convergence over players
is needed because the player set is finite.

The exceptional case `A=a_i` is intentionally not divided by zero.  It is a
one-leading-owner boundary: opponent absorption occurs at smaller order, and
the refusal price must be analyzed at that later order or by the saturated
stationary boundary condition.  Silently replacing `A-a_i` by `A` would lose
the unique-owner seam.

## 5. Exact tests and surviving producer

### 5.1 Two-player target mismatch

For `QuittingProjectiveTargetMismatch`, the physical parameter is
`lambda=t`, both hazards are `p=t/(1-t)`, and `v=(1,1)`.  Hence
`a_1=a_2=1`, `A=2`, and (4.4) gives for each player

\[
 \operatorname{Reg}_i\to\frac{1}{2}.
\]

This is the exact pure-Never gain: stationary real absorption removes the
cemetery and changes the value from `(1,1)` to `(3/2,3/2)`, while Never lets
the opponent quit alone and pays `2`.  It agrees with the checked target-gap
regression and shows that merely repeating the analytic root cannot preserve
the declared endpoint.

### 5.2 Boundary checks

- If `v_i=0` at an interior active coordinate, the radial change leaves that
  player's endpoint gap exactly unchanged.
- If `p_i=0` and `v_i>=0`, debiasing only makes Continue more attractive, so
  an inactive coordinate remains inactive.
- If `p_i=1` and `v_i<=0`, debiasing only makes Quit more attractive.
- If `q_i=1`, formula (3.5) is unavailable and the correct pure-Never value
  is the saturated boundary `max(0,r_i({i}))`; this is why Corollary 2A uses
  every-player opponent contraction rather than joint absorption alone.
- Nonsingleton rewards are fully present in `R`, `Quit_i`, and `E_i`; the
  proof never replaces them by singleton rows.  Their vanishing is used only
  later, in the matching analytic identification of `a_i` and the packet.

### 5.3 Proposition 4: the four-player boundary price is `1/12`

The Solan--Vieille `boundaryReward` has an exact symmetric discounted branch
which can be derived without selecting an abstract germ.  Give every player
the same Quit probability `p`, put `c=1-p`, and seek one common discounted
live value `v`.  For player `0` (and hence by symmetry every player), direct
enumeration of the eight opponent coalitions gives the forced-Quit value

\[
 \Sigma(p)=c^3+3pc^2+p^2c-p^3=1-2p^2,                         \tag{5.1}
\]

and the absorbing contribution after forcing Continue

\[
 E(p)=4pc^2+2p^2c=4p-6p^2+2p^3.                              \tag{5.2}
\]

Here the singleton of the within-pair partner pays `4`; the two paying
opponent-pair coalitions contribute `2p^2c`.  Every other coefficient follows
from the literal fifteen-row `boundaryReward` table.

Let `lambda` be the discount complement and `d=1-lambda`.  Indifference and
discounted policy evaluation are exactly

\[
 \Sigma(p)=E(p)+c^3v,
 \qquad v=d\Sigma(p).                                         \tag{5.3}
\]

Equivalently

\[
 G(\lambda,p):=
 (1-2p^2)\bigl[1-(1-\lambda)(1-p)^3\bigr]
 -(4p-6p^2+2p^3)=0.                                          \tag{5.4}
\]

At `(lambda,p)=(0,0)`,

\[
 G=0,\qquad \partial_pG=-1,\qquad \partial_\lambda G=1.
\]

The analytic implicit-function theorem therefore gives a unique local real
analytic branch `p(lambda)` with

\[
 p(0)=0,\qquad p'(0)=1.
\]

It is physical and interior for every sufficiently small positive `lambda`.
Using the common root at the live state, value `v=d(1-2p^2)` there, and the
literal absorbing rewards at terminal states gives an exact discounted
stationary Bellman equilibrium: both pure live actions equal `Sigma(p)`, so
every player's selected mixture is a best response and (5.3) is policy
evaluation.

Thus this branch is matching with `a_i=1` for all four players, `A=4`, and
`v_i^0=1`.  Proposition 3 yields the exact limiting all-behavior refusal
price

\[
 \operatorname{Reg}_i\longrightarrow
 \frac{1}{4-1}\frac{1}{4}=\frac1{12}.                         \tag{5.5}
\]

The same number is visible directly.  Cemetery debiasing sends the stationary
terminal payoff to `u_i->5/4`, while pure Never sees only the three opponents
and has value

\[
 \frac{E(p)}{1-c^3}\longrightarrow\frac43;
\]

the difference is `4/3-5/4=1/12`.

This table nevertheless has the checked exact period-two uniform payoff in
`FourPlayerPairedSingletonPeriodTwo.lean` and has no exact stationary
terminal Nash profile by `periodTwo_no_stationary_exactTerminalNash`
(`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwoStationary.lean`).
Therefore its known solution is genuinely nonstationary and removes the
radial refusal price.  It is not a perturbative stationary repetition of the
symmetric analytic branch.

### 5.4 Proposition 5: the matching projective packet is unique

Every matching analytic Bellman germ of `boundaryReward` has the same
normalized first-event packet:

\[
 c=z_0=z_1=z_2=z_3=\frac15,                                  \tag{5.6}
\]

where `c` is cemetery mass and `z_i` is singleton mass.  Equivalently, every
matching leading vector is

\[
 a_0=a_1=a_2=a_3=1.                                         \tag{5.7}
\]

Consequently every matching germ has endpoint value `(1,1,1,1)` and the same
limiting refusal price `1/12` at every coordinate.  In particular, switching
among matching analytic germs at vanishing parameters cannot cancel the
first-order radial defect.

#### Proof

By `periodTwo_singletonMatrix` (equivalently
`normalizedSoloMatrix_periodTwo`), the projective singleton matrix of
`boundaryReward` is

\[
 M=\begin{pmatrix}
 0&3&-1&-1\\
 3&0&-1&-1\\
 -1&-1&0&3\\
 -1&-1&3&0
 \end{pmatrix},
\]

and every own singleton reward is `1`, so the cemetery direction is the
constant vector `-1`.  The projective-packet balance, slack, and
complementarity equations are therefore

\[
\begin{aligned}
 w_0&=-c+3z_1-z_2-z_3, &w_1&=-c+3z_0-z_2-z_3,\\
 w_2&=-c-z_0-z_1+3z_3, &w_3&=-c-z_0-z_1+3z_2,
\end{aligned}                                                \tag{5.8}
\]

with `c,z_i,w_i>=0`, `z_iw_i=0`, and `c+sum_i z_i=1`.

First `c>0`.  If `c=0`, the singleton vector is a homogeneous simplex-LCP
solution for `M`, contrary to the checked theorem
`pairedSingletonMatrix_noHomogeneous`.  Now `w_0,w_1>=0` and `c>0` force
`z_1,z_0>0`; similarly `w_2,w_3>=0` force `z_3,z_2>0`.  Complementarity gives
all four `w_i=0`.  Subtracting the first pair and the second pair in (5.8)
gives

\[
 z_0=z_1=:x,\qquad z_2=z_3=:y.
\]

The equations `w_0=w_2=0` now read

\[
 c=3x-2y=3y-2x,
\]

so `x=y=c`.  Normalization gives `5c=1`, proving (5.6).  The matching packet
constructor has

\[
 c=\frac1{1+\sum_i a_i},\qquad
 z_i=\frac{a_i}{1+\sum_j a_j},
\]

which yields (5.7).  Its singleton mixture is `(1,1,1,1)`, or equivalently
every positive mass is pinned to own singleton payoff `1`.  Proposition 3
then gives `1/12` at every coordinate.  The conclusion concerns normalized
leading data: it does not assert uniqueness of the entire analytic germ or
exclude higher-order differences.

### 5.5 Proposition 6: every analytic germ of the boundary table is matching

Let `g` be any analytic Bellman germ of `boundaryReward`, and let `m` be the
least nonzero order of its Quit-rate family.  Then

\[
 m=g.\mathrm{ramification}.                                  \tag{5.9}
\]

In particular every analytic germ has the packet in Proposition 5 and the
same limiting `1/12` refusal price.  There is no faster, slower, asymmetric,
or absorbing analytic branch available for local defect cancellation.

#### Proof

First the endpoint root is all Continue.  Suppose instead that its joint
Continue mass is below one.  The checked endpoint identities
`quittingGerm_endpoint_fixedPoint` and
`quittingGerm_endpoint_endpointNash` say that the endpoint root has actual
successor value `v=g.value(0)` and is exact endpoint Nash against `v`.
Because it absorbs almost surely, its literal stationary terminal payoff is
`v`.

This endpoint certificate covers every behavioral deviation, including the
only saturation boundary.  If at least two players have positive endpoint
Quit probability, every opponent clock contracts and Proposition 2 with
`kappa=1` gives zero regret.  If exactly one player `i` has positive Quit
probability, every other player's opponent clock still contracts and its
endpoint inequality gives zero regret; player `i` faces opponents who Never
quit, its fixed-point payoff is its own singleton reward `1`, and replacing
its positive stationary clock by pure Never pays `0`, not more.  Thus the
stationary endpoint profile would be an exact terminal Nash profile against
unrestricted behavioral deviations.  This contradicts the checked theorem
`periodTwo_no_stationary_exactTerminalNash`.  Hence the endpoint is all
Continue, so every Quit rate vanishes at zero.

The table is not zero-solo (every own singleton is `1`), so
`quittingGermLeadingOrderNormalization_of_not_isQuittingZeroSolo` supplies a
nondegenerate order `m>=1`, nonnegative leading vector `a` with positive sum,
and the exact trichotomy against the positive ramification `q`.

- If `m<q`, real absorption dominates discount.  The checked fast-data
  construction `QuittingGermFastLeadingData.toProjectiveSingletonPacket`
  produces a cemetery-zero projective singleton packet.  Its singleton masses
  are therefore a homogeneous simplex-LCP solution for
  `pairedSingletonMatrix`, contradicting
  `pairedSingletonMatrix_noHomogeneous`.
- If `q<m`, cemetery dominates real absorption.  The checked theorem
  `quittingGermValue_zero_eq_zero_of_discount_dominates` gives `g.value(0)=0`.
  But some leading share is positive, and
  `quittingGerm_endpointValue_eq_solo_of_positive_leadingShare` pins that
  owner's endpoint coordinate to its own singleton reward `1`, a
  contradiction.

The trichotomy leaves only `m=q`, proving (5.9).  Proposition 5 then applies.
The assertion is about analytic Bellman germs in the checked sense; it does
not claim uniqueness of their higher jets or exclude a finite continuation
whose values make a macroscopic jump.

### 5.6 Proposition 7: the matching packet cannot select the coarse repair

There are two quitting tables with exactly the same singleton rows and hence
the same projective packet data, while one has no exact stationary terminal
Nash profile and the other has a pure exact stationary terminal Nash profile.
Therefore no nonperturbative radial-jump producer can depend only on the
normalized singleton packet.

#### Construction and proof

Keep the checked `stationaryCompletionReward` singleton matrix, but translate
every absorbing reward coordinate by `1`:

\[
 \widehat r(S)_i:=\texttt{stationaryCompletionReward}(S)_i+1. \tag{5.10}
\]

Its singleton row for owner `j` is the paired column
`(0,3,-1,-1)` (with the appropriate pair reindexing) plus the all-ones
vector.  This is exactly the corresponding `boundaryReward` singleton row:
own payoff `1`, partner payoff `4`, and cross-pair payoff `0`.  Hence
`boundaryReward` and `widehat r` have the same own solos, normalized matrix,
cemetery direction, and unique packet (5.6).

For every nonsingleton coalition, however, `stationaryCompletionReward` is
the constant vector `-2`, so `widehat r` is the constant vector `-1`.  Let
player `0` Quit surely at date zero and every other player Continue.  The
prescribed payoff is the singleton row `(1,4,0,0)`.  Player `0` can replace
Quit by Never only for payoff `0<=1`; delaying Quit still gives `1`.  Any
other player can affect the outcome only by joining player `0` at date zero,
which changes its payoff from `4` or `0` to `-1`.  Thus no unilateral
behavioral deviation gains, and this pure stationary profile is an exact
terminal Nash profile.

The distinction persists already at the discounted Bellman level.  For each
discount factor `d=1-lambda`, the constant root with player `0` quitting
surely and all others continuing has value

\[
 v=d\,(1,4,0,0).
\]

Player `0` strictly prefers immediate Quit to Continue when `d<1`; every
other player weakly prefers Continue to joining the `-1` collision.  This is
an absorbing analytic Bellman branch.  Proposition 6 shows that no such branch
exists for `boundaryReward`, despite identical packet data.  The coarse repair
therefore depends essentially on nonsingleton completion data.  This does not
rule out a universal construction using the full reward table; it rules out
the proposed extraction from the radial/projective packet alone.

### 5.7 Route disposition

The exact remaining datum is a **radial compensation edge**.  Given a matching
germ with a nonzero active coordinate, find a second discounted branch or
finite executable block whose continuation changes coordinate `i` by

\[
 q_i(\kappa-1)v_i
\]

with the sign required by (3.3), while keeping every other endpoint Nash
inequality and the literal terminal target controlled.  Proposition 6 kills
every local analytic branch repair on the actual hard table.  The only
meaningful next radial check is whether the known exact odd/even
Nash--Bellman cycle is the output of a **general construction from a nonzero
radial price**, not whether it can be redescribed after the fact.  A candidate
universal statement must take one exact discounted root plus its signed defect
and construct a second literal endpoint-Nash edge with a controlled target
displacement.  The boundary table is the first test; a second completion with
the same singleton matrix but a stationary solution is the necessary
falsifier of any construction that uses only the projective packet.  If the
construction necessarily needs completion-specific collision rows and no
invariant selection principle is found, this radial route is exhausted and
should be closed rather than folded into the existing cycle compiler.

Proposition 7 supplies the stated falsifier: the projective packet alone does
not determine whether the required coarse branch exists.  The full collision
table is indispensable, and the only positive example here is the already
checked special period-two cycle.  No new invariant selection principle was
found.  **This route is therefore CLOSED as a conjecture-closing thesis.**
The reusable output is the exact debias/regret calculation and the hard-table
no-go in Propositions 5--7.

## 6. Proved and unproved separation

**Proved here as ordinary mathematics:** the exact debiased terminal fixed
point (Proposition 1), the unrestricted stationary regret formula
(Proposition 2), the sign-compatible conditional producer (Corollary 2A), and
the matching-limit radial prices (Proposition 3), plus the symmetric analytic
branch and exact `1/12` refusal limit on the four-player boundary table
(Proposition 4), and uniqueness of that table's normalized matching packet
(Proposition 5), exclusion of every nonmatching or absorbing analytic germ on
that table (Proposition 6), and the exact same-singleton/different-completion
falsifier for packet-only coarse selection (Proposition 7).

**Not proved:** existence of a sign-compatible germ for every game; a
universal second-branch selection; a radial compensation schedule; analytic
construction of a nonperturbative compensation edge from arbitrary full
reward data; any new Lean declaration; or the full quitting-game conjecture.
