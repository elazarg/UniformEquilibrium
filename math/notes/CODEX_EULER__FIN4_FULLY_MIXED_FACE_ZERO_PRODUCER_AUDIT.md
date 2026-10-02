# Fin4 fully mixed stationary face-zero criterion and producer audit

## Status

**Ordinary mathematics plus a narrow audit of checked declarations.**  The
exact common-zero compiler and the conditional-face-gap producer cited below
are already Lean checked.  The necessity argument in Theorem 2.1 and the
comparison with the current Fin4 hard residual are written here for review.

The main conclusion is deliberately two-sided.

* There is a clean, exact, all-coalition finite feasibility problem whose
  solution gives a fully mixed stationary equilibrium against unrestricted
  behavioral deviations.
* None of the presently maintained `ResidualHardClass`, full singleton packet,
  pair-base, or strict minimum-fiber fields is a producer for that feasibility
  problem.  The obstruction is not the stationary compiler; it is the missing
  control of nonsingleton face numerators.

This note is not proposed for export.  Its positive implication is already
subsumed by the checked conditional-face-gap machinery, while its negative
part is a source-interface audit rather than an independence theorem for the
entire quantitative hard-residual structure.

## 1. Question and inspected sources

Let $I=\operatorname{Fin}4$, and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a quitting reward table.  When does there exist a hazard vector
$p\in(0,1)^I$ such that the product stationary profile with quitting rates
$p_i$ is an exact terminal Nash equilibrium against every unilateral
behavioral strategy?

The bounded source search used the following declarations.

* `quittingFaceNumerator` and
  `quittingFaceNumerator_eq_one_sub_continueMass_mul_conditionalFaceGap` in
  `UniformEquilibrium/Quitting/Stationary/FaceNumerator.lean`;
* `quittingConditionalFaceGapStationaryCertificateOfFaceNumeratorZero`,
  `exists_stationaryCertificate_of_conditionalFaceGap`, and
  `exists_stationaryCertificate_of_strictConditionalFaceGap` in
  `UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGap.lean`;
* `IsQuittingConditionalFaceGapRange` and
  `exists_stationaryCertificate_of_conditionalFaceGapRange` in
  `UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`;
* `ResidualHardClass` in
  `UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`;
* `FinFourQuantitativeFullSupportHardResidual` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`;
* `FinFourPairBasePaidResetTarget` and
  `QuittingTerminalExploitabilityWitness.exists_finFour_pairBasePaidResetDispatch`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetAlignment.lean`;
* `exists_finFour_strictMinimumPlateau_openDebtHomotopyTube_of_no_uniformPayoff`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`.

The live frontier statement in
`questions/FOUR_PLAYER_SINGLETON_PACKET_DISPATCH.md` was also used to avoid
mistaking a singleton-matrix classification for the missing nonsingleton
producer.

## 2. The exact fully mixed system

Fix $i\in I$.  Write

\[
 c_i(p)=\prod_{j\ne i}(1-p_j),
\]

\[
 Q_i(p)=\sum_{J\subseteq I\setminus\{i\}}
 \left(\prod_{j\in J}p_j\right)
 \left(\prod_{j\notin J,\ j\ne i}(1-p_j)\right)
 r_i(J\cup\{i\}),
\]

and

\[
 A_i(p)=\sum_{\varnothing\ne J\subseteq I\setminus\{i\}}
 \left(\prod_{j\in J}p_j\right)
 \left(\prod_{j\notin J,\ j\ne i}(1-p_j)\right)r_i(J).
\]

These are respectively `continueMassExcl`, `sigmaValue`, and
`excludedValue`.  Define the division-free polynomial

\[
 F_i(p)=(1-c_i(p))Q_i(p)-A_i(p).                 \tag{2.1}
\]

For $p\in(0,1)^I$, put

\[
 N_i(p)=\frac{A_i(p)}{1-c_i(p)}.
\]

Then

\[
 F_i(p)=(1-c_i(p))(Q_i(p)-N_i(p)),              \tag{2.2}
\]

and the factor $1-c_i(p)$ is strictly positive.

### Theorem 2.1 (exact fully mixed stationary criterion)

For a Fin4 reward table, the following are equivalent.

1. There is $p\in(0,1)^I$ such that the stationary product profile with
   hazard $p$ is an exact terminal Nash equilibrium against every unilateral
   behavioral deviation.
2. There is $p\in(0,1)^I$ such that

   \[
   F_i(p)=0\qquad(i\in I).                       \tag{2.3}
   \]

When these conditions hold, the equilibrium payoff is
$U_i=Q_i(p)=N_i(p)$, and it is a uniform-equilibrium payoff.

#### Proof

For $2\Rightarrow1$, take any positive lower box strictly below $p$ and
the upper vector $1$, or simply invoke the common-zero compiler directly.
Equation (2.3) is exactly the hypothesis of
`quittingConditionalFaceGapStationaryCertificateOfFaceNumeratorZero`.
Positivity of all four hazards makes both the joint stationary row and every
deleted-player opponent row contract.  The returned certificate contains the
fixed point, zero endpoint Nash error, exact terminal payoff, unrestricted
behavioral terminal Nash property, and uniform-equilibrium payoff.

For $1\Rightarrow2$, fix player $i$.  All opponents have positive hazards,
so their continuation mass satisfies $c_i(p)<1$.  Against these stationary
opponents, Quit now pays $Q_i(p)$, Never pays $N_i(p)$, and quitting at
finite time $t$ pays

\[
 V_i(t)=N_i(p)+c_i(p)^t\bigl(Q_i(p)-N_i(p)\bigr). \tag{2.4}
\]

The prescribed stationary strategy of $i$, because $0<p_i<1$, assigns
positive probability to both quitting at date zero and first Continuing at
date zero and then using the same stationary strategy.  Exact optimality of
this interior date-zero mixture forces equality of its Quit and Continue
endpoints.  Stationarity then identifies the continuation value with the
prescribed terminal payoff, and the fixed-point identity identifies that
payoff with $Q_i(p)$.  Hence $Q_i(p)=N_i(p)$.  Equation (2.2) gives
$F_i(p)=0$.  This holds for every $i$.  Finally, the checked endpoint
compiler gives the stated unrestricted and uniform-payoff conclusions.  □

### Finite algebraic size

For Fin4, (2.3) is a system of four explicit polynomial equations in four
unknowns, together with $0<p_i<1$.  Each $Q_i,A_i,c_i$ is multilinear in
the three opponent hazards; the division-free $F_i$ has total degree at
most six and degree at most two in each opponent coordinate.  All coefficients
are literal coalition rewards.  Thus this is a finite semialgebraic problem,
not a behavioral-strategy approximation.

The Gray table from
`notes/CODEX_EULER__GRAY_FOUR_CLOCK_STATIONARY_ESCAPE.md` supplies one exact
existence proof for (2.3) by a rational contraction box.  That calculation is
an instance of the common-zero criterion, not a new stationary compiler.

## 3. The strongest checked general producer near this problem

The exact system (2.3) is a verifier until one produces a zero.  The most
general checked producer found in the narrow search is the conditional-face-
gap theorem.

Choose vectors $0\le l<u<1$ and a permutation $b:I\simeq I$.  Suppose
that on the whole box $[l,u]$, for every player $i$,

\[
 \begin{aligned}
 p_{b(i)}=l_{b(i)}&\quad\Longrightarrow\quad F_i(p)>0,\\
 p_{b(i)}=u_{b(i)}&\quad\Longrightarrow\quad F_i(p)\le0.
 \end{aligned}                                      \tag{3.1}
\]

Then `exists_stationaryCertificate_of_conditionalFaceGap` produces a common
zero $p\in(l,u]$.  Since $u_i<1$, it is fully mixed, so Theorem 2.1 gives
an exact stationary terminal Nash profile and a uniform-equilibrium payoff.
Strict negativity on the upper faces places the zero in the open box, but is
not needed for full mixing when $u<1$.

Although the abstract theorem permits any permutation, (3.1) itself forces
the effective assignment to have no fixed point: $F_i$ is independent of
the player's own hazard $p_i$, so opposite signs cannot occur on two faces
which differ only in that coordinate.  Thus on Fin4 only a derangement can
serve as a nonvacuous blocker assignment.

### A literal finite reward-table screen

The checked `ConditionalFaceGapRange` adapter gives a finite family of reward
inequalities implying (3.1).  Here the adapter additionally assumes
$0<l_i$ for every coordinate.  For each player $i$, choose the distinct
blocker $b(i)$, and bound all rewards to $i$ in the following three
classes:

1. $r_i(\{i\}\cup T)$, with $T\subseteq I\setminus\{i,b(i)\}$;
2. $r_i(\{i,b(i)\}\cup T)$, with the same backgrounds $T$;
3. $r_i(S)$, for every nonempty $S\subseteq I\setminus\{i\}$.

Call the first two lower/upper intervals
$[q^0_{i,-},q^0_{i,+}]$ and
$[q^1_{i,-},q^1_{i,+}]$, and the third interval
$[n_{i,-},n_{i,+}]$.  It suffices that

\[
 n_{i,+}< (1-l_{b(i)})q^0_{i,-}+l_{b(i)}q^1_{i,-}, \tag{3.2}
\]

and

\[
 (1-u_{b(i)})q^0_{i,+}+u_{b(i)}q^1_{i,+}\le n_{i,-}. \tag{3.3}
\]

These inequalities say that the conditional Quit endpoint lies strictly
above every Continue outcome on the lower blocker face and weakly below every
Continue outcome on the upper face.  Bernoulli averaging supplies (3.1).
This is a genuine full-coalition hypothesis: it mentions pair, triple, and
grand-coalition rewards, not only the normalized singleton matrix.

`BlockerSwitch.lean` supplies another checked class, but it requires passive
players' payoffs to be constant when they do not quit and is therefore more
special than (3.1) for the present audit.

## 4. What the current Fin4 residual does and does not imply

### 4.1 `ResidualHardClass`, full normal core, and singleton packet

These fields do **not** imply (2.3), (3.1), or (3.2)--(3.3) by any current
declaration.

`ResidualHardClass` is entirely a predicate of `normalizedSoloMatrix reward`:
normal-core nonemptiness, absence of a homogeneous solution, standard-Q on
the normal matrix, and failure of full projective Q-bar.  The full-normal-core
and the full-support packet's mixture and pinning fields are built from
singleton reward vectors (the packet also retains a punishment-floor
inequality).  In contrast, every $F_i$ potentially uses all fifteen nonempty
coalition rewards in receiver row $i$: eight coalitions containing $i$ in
$Q_i$, and seven nonempty coalitions excluding $i$ in $A_i$.

There is a sharp local independence calculation.  Fix an interior hazard
$p$, a player $i$, and a coalition $T\ni i$ with $|T|\ge2$.  The
coefficient of $r_i(T)$ in $F_i(p)$ is

\[
 (1-c_i(p))
 \prod_{j\in T\setminus\{i\}}p_j
 \prod_{j\in I\setminus T}(1-p_j)>0.             \tag{4.1}
\]

Changing this one nonsingleton coordinate therefore moves $F_i(p)$ through
both signs while leaving every singleton reward, hence the normalized solo
matrix and all its LCP predicates, unchanged.  If a whole hazard box has
positive lower bounds, taking $T=I$ makes the coefficient uniformly
positive on the box; a sufficiently large change destroys either desired
face sign without changing singleton data.

This proves nonproduction from the singleton/LCP fields alone.  It is **not**
claimed to preserve the terminal exploitability witness, punishment values,
or every existential source selected in the complete
`FinFourQuantitativeFullSupportHardResidual` structure.  Thus it is not a
counterexample to an as-yet-unproved theorem using all of those fields jointly.

The terminal witness adds a global positive exploitability statement, and
all-player punishment normality adds inequalities between punishment values
and solo rewards.  Neither currently supplies an oriented, simultaneous set
of four face-numerator signs.  If (3.1) could be derived from the complete
no-uniform residual, the checked compiler would immediately contradict that
residual's provenance; this is precisely a possible positive route, not an
already available implication.

### 4.2 Pair-base paid/reset sources

`FinFourPairBasePaidResetTarget` is actual same-profile semantic data, but its
root is on a boundary face: the persistent pair are sure quitters and only the
two complementary coordinates are chosen through a constrained Nash point.
It gives a prescribed zero-debt reset coordinate, unit incidence, and a
source-matched paid debtor.  These facts do not give a positive four-hazard
row, do not solve four equations $F_i=0$, and do not give the opposite-face
signs (3.1).

At most, the constrained-Nash conditions yield one-sided face-numerator signs
at that selected boundary root; the checked lemmas
`quittingFaceNumerator_nonpos_of_constrainedNash_of_lt_one` and
`quittingFaceNumerator_nonneg_of_constrainedNash_of_lower_lt` in
`NormalTerminalGapConstrainedStationary.lean` record exactly this orientation.
Poincare--Miranda needs compatible signs on every point of eight assigned box
faces, with one global derangement.  No current pair-base theorem supplies
that extension from its selected root.

The paid/reset labels also do not automatically define the blocker
derangement.  Different prescribed owners reselect different stationary
profiles and laws.  Treating those four separate selections as the four faces
of one common hazard box would be an invalid source-identification step.

### 4.3 Strict minimum-fiber all-Continue tube

The minimum-fiber theorem gives an open payoff tube in which every exact root
at a tail is uniquely all-Continue.  It is a local exclusion theorem in
continuation-payoff space.  A face-zero stationary certificate instead uses
the endogenous value $U_i=Q_i(p)$, which need not lie in that tube.  Hence
the tube neither supplies (3.1) nor contradicts a face zero elsewhere.

Indeed, if the endogenous value of a proposed positive common zero were shown
to lie in the tube, uniqueness would immediately rule it out.  The missing
statement is exactly such a payoff/source alignment.  The existing pair-base
and cap-port results do not provide it.

## 5. Resulting finite obligation

For the fully mixed stationary lane, the live Fin4 producer question can be
stated without behavioral ambiguity:

> Starting from the complete same-table hard residual, either produce an
> interior solution of the four polynomial equations (2.3), or produce one
> hazard box and one derangement satisfying (3.1), possibly through the finite
> reward ranges (3.2)--(3.3).

Either output enters an already checked unrestricted-behavior compiler.  The
current singleton principal, marked-lasso, pair-base, and minimum-fiber data do
not yet imply either output.  Conversely, failure of the coarse range screen
does not imply absence of an interior root: the Gray calculation uses a local
four-dimensional contraction certificate rather than coalitionwise range
separation.

This cleanly isolates the strongest surviving conditional theorem while
preventing two overclaims:

* a supplied common zero is not a producer from arbitrary hard-residual data;
* the absence of a face-sign box is not a positive all-behavior terminal gap.

## 6. Requested independent check

Please check:

1. the necessity direction of Theorem 2.1, especially the use of interior
   date-zero mixing and opponent contraction;
2. the polynomial degree and coefficient (4.1);
3. the claim that a nonvacuous coordinate assignment in (3.1) must be a
   derangement;
4. the exact scope of the pair-base constrained-Nash signs; and
5. the distinction between independence from singleton/LCP fields and the
   deliberately unproved joint implication from the full hard residual.
