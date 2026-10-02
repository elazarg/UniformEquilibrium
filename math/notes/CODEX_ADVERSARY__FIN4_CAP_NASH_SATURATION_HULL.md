# CODEX adversary: a cap--Nash saturation hull closes every off-minimum descent branch

**Status (2026-08-30).** New ordinary mathematics, not Lean-checked.  This
note gives a formalizable architecture for the strict off-minimum return left
open by
[`CODEX_ADVERSARY__FIN4_OFFMIN_PAID_EXIT_CAPACITY_SLICE.md`](CODEX_ADVERSARY__FIN4_OFFMIN_PAID_EXIT_CAPACITY_SLICE.md),
Section 9.  Instead of selecting an arbitrary infinite sequence of positive
roots, take the smallest closed joint-law set containing the returned source
and invariant under every exact cap--Nash prefix.  Total debt attains a minimum
on this compact hull.  At a hull minimizer, every exact cap--Nash root is all
Continue; otherwise its exact prefix would remain in the hull and strictly
lower debt.  A debt-weighted atom inequality is itself closed and invariant,
so the original finite law atom survives at the hull minimizer.

For a Fin4 hard residual the hull minimizer has an exact dichotomy.  If it is
on the global minimum fibre, the checked same-point causalization packages a
fresh minimum-atom producer with the same residual.  If it remains strictly
off the minimum, it is a source-produced exact neutral obstruction with a
retained finite atom and unique all-Continue cap root.  Thus the arbitrary
real-valued descent branch is eliminated as a separate outcome; the remaining
mathematics is concentrated in this typed neutral passport.  Sections 8--10
strengthen the construction to a law-tight hull, audit its topology and exact
atom scaling, and reduce every strict Fin4 output to full positive-debt
support, a same-law reset-rigid stall, or a unique-owner solo/Never law.
Sections 11--14 attack those three chambers: two exact local regressions rule
out purely static closures, while the solo/Never chamber is strengthened to a
finite cap-binding positive-collision cycle.

## 1. Question and fixed data

Fix a finite quitting game and write

\[
  \mathcal C=
  \operatorname{quittingTerminalSemanticLawCarrier}(r)
\]

for its compact joint semantic/law carrier.  A point is denoted
\(z=(X,\mu)\), where \(X=(u,c)\) is the prescribed-payoff/cap pair and
\(\mu\) is the complete terminal-outcome law.  Put

\[
  D(X)=\sum_i(c_i-u_i).
\]

Assume a global semantic minimum \(m\) with

\[
  0<D_*:=D(m)\le D(X)
  \qquad(X\in\operatorname{proj}_1\mathcal C).
\tag{1}
\]

Let the supplied origin be \(z_0=(X_0,\mu_0)\in\mathcal C\), and fix a
finite coalition \(S\) with

\[
  b_0:=\mu_0(\operatorname{some}S)>0.
\tag{2}
\]

For a product root \(x\), let

\[
  P_x(X,\mu):=
  \bigl(T_xX,\operatorname{LawPrefix}_x\mu\bigr).
\tag{3}
\]

Only roots which are exact Nash against the displayed cap \(X^{cap}\) are
allowed.  This cap condition is essential: it gives the exact debt scaling

\[
  D(T_xX)=q(x)D(X),
  \qquad q(x)=\operatorname{ContinueMass}(x)
                  =1-\operatorname{Abs}(x).
\tag{4}
\]

## 2. The closed exact-prefix saturation hull

### Definition 1 (closed cap--Nash invariant)

A set \(A\) of joint semantic/law points is a closed cap--Nash invariant
above \(z_0\) if

1. \(A\) is closed;
2. \(A\subseteq\mathcal C\);
3. \(z_0\in A\); and
4. whenever \((X,\mu)\in A\) and \(x\) is exact Nash against \(X^{cap}\),
   then \(P_x(X,\mu)\in A\).

The whole carrier \(\mathcal C\) is such an invariant:
`quittingTerminalSemanticLawPrefix_mem_carrier` proves item 4 for every root,
without needing exactness.

### Definition 2 (cap--Nash saturation hull)

Define

\[
  \mathcal H(z_0)
  :=\bigcap\{A:A\text{ is a closed cap--Nash invariant above }z_0\}.
\tag{5}
\]

This is a nonempty closed subset of \(\mathcal C\), hence compact.  It
contains \(z_0\) and is itself invariant under every exact cap--Nash prefix.
It is the smallest object with those properties.  Definition (5), rather
than the closure of finite descendants, is important: exact Nash
correspondences need not be lower hemicontinuous, so a new positive root may
appear only at a limit point.  The intersection construction automatically
closes under that newly appearing root as well.

This is the promised architecture-level state.  It contains all finite exact
prefix descendants, all their compact limits, and every further exact prefix
which becomes available only at such a limit.  No arbitrary endpoint row is
reselected and no history edge is asserted where only carrier closure is
known.

## 3. The debt-weighted atom invariant

The raw inequality \(\mu(S)\ge b_0\) is not prefix invariant because the old
law is multiplied by Continue mass.  The correct homogeneous invariant is

\[
  D(X_0)\,\mu(\operatorname{some}S)
  \ge D(X)\,b_0.
\tag{6}
\]

### Lemma 3 (closed invariant atom cone)

The subset of \(\mathcal C\) satisfying (6) is a closed cap--Nash invariant
above \(z_0\).

### Proof

It is closed by continuity of the debt and law coordinates, and equality
holds at \(z_0\).  Suppose (6) holds at \((X,\mu)\), let \(x\) be exact
cap--Nash there, and put \((Y,\nu)=P_x(X,\mu)\).  The affine law prefix gives

\[
  \nu(\operatorname{some}S)
  =\operatorname{RootMass}_x(S)
     +q(x)\mu(\operatorname{some}S)
  \ge q(x)\mu(\operatorname{some}S).
\tag{7}
\]

Multiplying by \(D(X_0)>0\), using (6), and then (4), gives

\[
 D(X_0)\nu(\operatorname{some}S)
 \ge q(x)D(X)b_0=D(Y)b_0.
\]

Carrier membership follows from the checked joint-law prefix theorem. `QED`

By minimality of (5), every point in \(\mathcal H(z_0)\) satisfies (6).
Together with (1), this gives the uniform floor

\[
  \mu(\operatorname{some}S)
  \ge \frac{D(X)}{D(X_0)}b_0
  \ge \frac{D_*}{D(X_0)}b_0>0
\tag{8}
\]

throughout the entire closed saturation hull, including transfinite-looking
limit/restart behavior.

## 4. Compact minimization produces the neutral point

### Theorem 4 (cap--Nash saturation minimizer)

There is \(z_H=(X_H,\mu_H)\in\mathcal H(z_0)\) such that

\[
 D(X_H)\le D(X)\qquad((X,\mu)\in\mathcal H(z_0)),
\tag{9}
\]

and

\[
 \forall x,\qquad
 x\text{ exact Nash against }X_H^{cap}
 \quad\Longleftrightarrow\quad
 x=\text{all Continue}.
\tag{10}
\]

Moreover

\[
  \mu_H(\operatorname{some}S)
  \ge \frac{D_*}{D(X_0)}b_0>0,
\tag{11}
\]

and the all-Continue joint prefix fixes \(z_H\) exactly.

### Proof

Compactness of \(\mathcal H(z_0)\) and continuity of \(D\) give a minimizer
\(z_H\).  Let \(x\) be any exact cap--Nash root at \(X_H\).  Hull invariance
puts \(P_xz_H\) back in \(\mathcal H(z_0)\), so (9) and the exact account give

\[
  D(X_H)\le D(T_xX_H)
  =D(X_H)-D(X_H)\operatorname{Abs}(x).
\tag{12}
\]

Since \(D(X_H)\ge D_*>0\) and absorption is nonnegative, (12) forces
\(\operatorname{Abs}(x)=0\).  Hence \(q(x)=1\), and
`eq_quittingAllContinueRoot_of_continueMass_eq_one` gives
\(x=\) all Continue.

An exact cap--Nash root exists by `exists_isZeroQuittingRootNash`; applying
the preceding conclusion to it proves that all Continue is exact, and hence
the biconditional (10).  Exact all-Continue Nash is equivalent to the
singleton inequalities needed by the semantic-prefix identity, so its
semantic prefix fixes \(X_H\); its law prefix plainly fixes \(\mu_H\).
Equation (11) is (8). `QED`

Theorem 4 is robust to discontinuous positive roots.  Such a root cannot be
lost at a compact limit: if it appears there, Definition 1 requires its
strictly cheaper prefix to stay inside the same hull, contradicting
minimality.

## 5. The finite chronology account subsumed by the hull

For comparison, every finite exact-prefix chronology

\[
 z_{n+1}=P_{x_n}z_n,qquad
 a_n=\operatorname{Abs}(x_n),qquad z_0\text{ fixed},
\tag{13}
\]

obeys

\[
 D(z_n)-D(z_{n+1})=D(z_n)a_n\ge D_*a_n.
\tag{14}
\]

Therefore

\[
 \sum_{n<N}a_n
 \le\frac{D(X_0)-D(X_N)}{D_*}
 \le\frac{D(X_0)-D_*}{D_*}.
\tag{15}
\]

The old marked atom simultaneously obeys

\[
 \mu_N(\operatorname{some}S)
 \ge\prod_{n<N}(1-a_n)b_0
 =\frac{D(X_N)}{D(X_0)}b_0.
\tag{16}
\]

Thus every infinite selected chronology has summable absorption and retains
a uniform atom floor.  Equations (15)--(16) alone would again leave the
possibility of a newly appearing positive root at its limit.  The saturation
hull is the decoder for exactly that defect: it repeats “take a compact limit,
then close under every new exact root” implicitly until the debt minimizer
forces the neutral alternative (10).

## 6. Typed passport and Fin4 production theorem

The formalization target should be a structure of the following strength.

### Definition 5 (`QuittingCapNashSaturationPassport`)

For a positive global minimum \(m\), an origin \(z_0\in\mathcal C\), and a
positive finite atom \(S\), store:

- the closed compact hull \(\mathcal H\subseteq\mathcal C\);
- origin membership and closure under every exact cap--Nash joint-law prefix;
- the debt-weighted atom inequality (6) on all of \(\mathcal H\);
- a debt-minimizing point \(z_H\in\mathcal H\);
- the retained positive atom bound (11);
- exact-root uniqueness (10); and
- the dichotomy
  \[
    D(X_H)=D_*
    \quad\text{or}\quad
    D_*<D(X_H)\le D(X_0).
  \tag{17}
  \]

All fields are produced by Theorem 4; none is a caller-supplied verifier
hypothesis.

### Theorem 6 (hard-residual saturation output)

Let `residual` be a `FinFourQuantitativeFullSupportHardResidual`.  Given any
joint carrier origin \(z_0\) with a positive finite atom, there is a
`QuittingCapNashSaturationPassport` using the positive global minimum selected
from that same residual.  Its output is exactly one of:

1. **Minimum-law regeneration.**  If \(D(X_H)=D_*\), then \(z_H\) is a
   globally minimizing joint law with a positive finite atom.  The checked
   `finFourHardResidual_minimumLaw_causalSuffixAtom` constructs a causal suffix
   atom at this same point.  Packaging the residual, \(z_H\), its minimum
   proof, the positive infimum identity, and this atom gives a fresh
   `FinFourMinimumAtomProducer` with residual definitionally equal to the
   input residual.

2. **Off-minimum neutral saturation.**  If \(D_*<D(X_H)\), retain the
   passport, the strict inequality, (11), the exact all-Continue self-loop,
   and (10).  This is the new typed obstruction; it is not merely a semantic
   pair with a forgotten source.

### Proof

`FinFourMinimumAtomProducer.exists_residual_eq_of_hardResidual` supplies the
positive global minimum and its exact infimum value.  Apply Theorem 4 to the
given origin and atom.  Split the global lower bound
\(D_*\le D(X_H)\) into equality or strict inequality.  In the equality arm,
rewrite the original minimum theorem along the equality and invoke the
same-point causalization named above, exactly as in the checked proof of
`FinFourStrictRayPositiveRootReturn.nonempty_minimumLawHandoff_or_offMinimumDescent`.
The strict arm is already all the advertised structure. `QED`

### Corollary 7 (production from the current off-minimum return)

For a checked `FinFourStrictRayOffMinimumDescent`, use
`result.returnedPoint` as \(z_0\).  Its carrier membership is checked.  Its
limiting law has a retained positive atom; the positive-root prefix has
positive Continue mass because its returned debt is at least \(D_*>0\), so
the affine law formula retains that atom positively at `returnedPoint`.
Theorem 6 therefore produces a fresh same-residual minimum source or the
off-minimum neutral saturation passport.

The same proof applies to the generic positive-root return constructed from
`exists_offMinimum_retainedLaw_allContinue_or_supportEntry`: use its returned
joint law as origin and the retained atom furnished by the theorem.

In fact the hull can be started one step earlier, at the omega-source itself,
and then subsumes both disjuncts of
`exists_offMinimum_retainedLaw_allContinue_or_supportEntry`.  If a positive
exact root exists, hull invariance includes its returned point and continues
the saturation automatically.  If all Continue is already the unique exact
root, the singleton set containing that joint point is closed and invariant
(the all-Continue semantic and law prefix is the identity), so the saturation
hull is exactly that singleton and the point itself is the neutral minimizer.
Thus no selection between those two root-correspondence outcomes is needed by
the new architecture.

## 7. What has and has not been closed

This architecture genuinely closes the repeated off-minimum *descent*
problem.  There is no longer a need to assign a natural rank to arbitrary
positive real drops or to assume a uniform absorption floor.  Compact
exact-prefix saturation turns all finite, Zeno, and discontinuous-limit
restarts into one minimization problem.

It does not yet prove a uniform equilibrium.  The strict output of (17) is an
off-minimum joint-law point with a retained finite atom and unique
all-Continue cap root.  It has no prescribed-payoff floor, admissible charged
edge, paid-gain decoration, or actual behavioral profile realizing the carrier
point.  Those missing properties should now be attacked as consequences of
the **minimal closed exact-prefix invariant hull**, a stronger and more rigid
object than the earlier isolated inert source.

## 8. Self-audit and law-tight strengthening

### 8.1 Audit of the two load-bearing identities

The hull proof uses no hidden sequential compactness or correspondence
continuity.

1. **Compactness/nonemptiness.**  The family in (5) is nonempty because the
   entire joint semantic/law carrier is closed, contains \(z_0\), and is
   preserved by `quittingTerminalSemanticLawPrefix_mem_carrier` for every
   root.  An arbitrary intersection of closed sets is closed; every member of
   the family contains \(z_0\); and the intersection is a closed subset of the
   compact carrier.  Prefix invariance of the intersection is pointwise: an
   exact root at a point of the intersection can be applied inside every
   member of the defining family.  No approximation of that root at nearby
   caps is used.
2. **Identical scaling factor.**  For a finite terminal atom, the exact law
   formula is
   \[
     \operatorname{LawPrefix}_x(\mu)(\operatorname{some}S)
       =\operatorname{RootCoalitionMass}_x(S)+q(x)\mu(\operatorname{some}S).
   \]
   The old atom is therefore multiplied by precisely
   \(q(x)=\operatorname{quittingStationaryContinueMass}(x)\).  The cap--Nash
   debt theorem multiplies every debt coordinate, and hence total debt, by
   this same \(q(x)\).  Thus (6) is exact.  For `none` there is no fresh term,
   but the same multiplicative identity still holds; the present application
   uses a finite `some S` atom.

The only deliberate closure-level feature is that a hull point need not be
the semantic/law point of one supplied behavioral profile.  This is why the
minimum-equality branch invokes the separate same-point causalization theorem.

### 8.2 Law-tight cap--Nash saturation

There is a useful strictly stronger hull.  Call a closed cap--Nash invariant
**law-tight** when it also satisfies:

> If \((X,\mu)\) is in the set and \((Y,\mu)\) is any joint carrier point
> with the identical complete law and \(D(Y)\le D(X)\), then
> \((Y,\mu)\) is in the set.

Let \(\widehat{\mathcal H}(z_0)\) be the intersection of all closed law-tight
cap--Nash invariants above \(z_0\).  The whole carrier again witnesses
nonemptiness.  The atom cone (6) remains invariant under the new operation:
the law coordinate is unchanged and the right-hand debt only decreases.
Consequently Theorems 4 and 6 hold verbatim for the law-tight hull, and its
minimizer \(\widehat z_H=(\widehat X_H,\widehat\mu_H)\) has the additional
property

\[
 D(\widehat X_H)\le D(Y)
 \quad\text{for every }(Y,\widehat\mu_H)\in\mathcal C.
\tag{18}
\]

Thus the neutral output may be required, without any new caller hypothesis,
to minimize total cap debt on its entire complete-law fibre as well as on its
exact-prefix saturation hull.

### 8.3 The complete hull-minimum face

Let

\[
 \mathcal M=
 \{(X,\mu)\in\widehat{\mathcal H}(z_0):D(X)=D_H\},
 \qquad D_H:=\min_{\widehat{\mathcal H}(z_0)}D.
\tag{19}
\]

Then \(\mathcal M\) is nonempty and compact.  The proof of Theorem 4 applies
at every one of its points, so every point of \(\mathcal M\)

- retains the atom floor (11);
- has all Continue as its unique exact **cap**--Nash root; and
- is fixed by the all-Continue semantic/law prefix.

The word “cap” cannot be dropped: this does not say that all Continue is Nash
against the prescribed payoff coordinate.  In particular the finite-reward
plateau theorems whose Nash hypothesis is against `pair.1` cannot be applied
without a new bridge from cap to prescribed payoff.

There is also a global quantitative inequality.  For every
\((X,\mu)\in\widehat{\mathcal H}(z_0)\) and every exact cap--Nash root \(x\),
prefix closure and minimality give

\[
 D_H\le (1-\operatorname{Abs}(x))D(X),
 \qquad
 \operatorname{Abs}(x)le\frac{D(X)-D_H}{D(X)}.
\tag{20}
\]

Thus exact absorption is linearly undercharged by distance to the hull-minimum
face.  Along every finite selected chain one may sharpen (15) to

\[
 \sum_{n<N}\operatorname{Abs}(x_n)
 \le\frac{D(X_0)-D(X_N)}{D_H}
 \le\frac{D(X_0)-D_H}{D_H}.
\tag{21}
\]

Equations (20)--(21) are the summable-decoder side of the passport.  They
show that no hidden fixed absorption toll survives near \(\mathcal M\), while
the saturation construction ensures that every discontinuously appearing
positive root is charged before the final minimizer is selected.

## 9. Exact fixed-law reset consequence at a strict minimizer

Assume now \(D_*<D_H\), choose \(z=(X,\mu)\in\mathcal M\), and suppose some
owner \(o\) satisfies

\[
 d_o(X)=0,
 \qquad
 \operatorname{OpponentIncidence}_o(\mu)>0.
\tag{22}
\]

Apply the checked fixed-law reset-face dispatch with the global minimum as
source and \((X,\mu)\) as target.  It returns \((R,\mu)\) with

\[
 D_*\le D(R)\le D(X)=D_H.
\tag{23}
\]

Law-tightness puts \((R,\mu)\) back in
\(\widehat{\mathcal H}(z_0)\), so hull minimality reverses (23) and forces

\[
 D(R)=D_H.
\tag{24}
\]

Hence \((R,\mu)\in\mathcal M\) and its unique exact cap root is all Continue.
The absorbing dynamic exit of `QuittingFixedLawResetDispatch` is impossible:
its exact prefix would lie in the hull and have debt strictly below \(D_H\).
The dispatch must take its exact all-Continue fixed-face arm.  All its other
fields survive, including zero owner debt, the fixed complete law, the
opposite-face transfer account, and the hard-residual supported strict toggle.

This is a complete conditional consumer of (22), but its output is a
**reset-rigid neutral point**, not yet a terminal approximation.  It improves
the earlier pair-base audit in two ways: the target law is the actual retained
hull law, and equality (24) follows from produced hull minimality rather than
being assumed.  The remaining failure is now isolated to the checked
all-Continue branch of the reset dispatch.

## 10. Fin4 neutral-form trichotomy

The strict law-tight hull passport has the following exact finite-player
classification.

1. **Full debt support:** \(d_i(X)>0\) for all four players.
2. **Reset-rigid incidence:** some zero-debt owner has positive total opponent
   incidence, so Section 9 produces the same-law reset-rigid neutral point.
3. **Solo/Never law:** there is exactly one zero-debt owner \(o\), every
   zero-debt owner has zero opponent incidence, and the finite part of \(\mu\)
   is supported only on the singleton \(\{o\}\).  Never may carry the
   remaining mass.

To verify exhaustiveness, suppose the zero-debt set is nonempty.  For an owner
\(o\) in it, zero total opponent incidence and nonnegativity of the law imply
that every positive finite atom contains no player distinct from \(o\), hence
is exactly \(\{o\}\).  Because (11) gives at least one positive finite atom,
two distinct zero-debt owners cannot both have zero opponent incidence.  Thus
either some zero-debt owner satisfies (22), or the zero-debt set is the
singleton \(\{o\}\) and the law has the stated solo/Never support.

This trichotomy is a canonical counterexample-certificate target produced
from the hard residual.  A completion need only exclude or consume these
three rigid forms; it no longer has to manage arbitrary repeated off-minimum
positive-root descents.

## 11. Chamber I: all four semantic debts are positive

The all-positive chamber does not collapse by a local root perturbation, even
if every singleton constraint is binding and every player is
punishment-normal. The following exact rational ordinary-mathematics
regression is useful because it has the retained finite-atom shape as well.

For (i\in\{0,1,2,3\}), let (g_i(B)) be the membership increments from the
checked owner-risky table:

\[
\begin{aligned}
g_0(B)&=1_{1\in B}-2\,1_{2\in B}+\tfrac1{100}1_{3\in B},\\
g_1(B)&=1_{0\in B}-2\,1_{2\in B},\\
g_2(B)&=\tfrac25(1_{0\in B}+1_{1\in B})-\tfrac{39}{100}1_{3\in B},\\
g_3(B)&=-1_{0\in B}-1_{1\in B}+1_{2\in B}.
\end{aligned}
\tag{25}
\]

Choose arbitrary passive functions (a_i) on opponent coalitions, subject
only to

\[
 a_i(\varnothing)=1,\qquad
 a_1(\{0\})=0,\quad a_2(\{0\})=\tfrac35,\quad
 a_3(\{0\})=1,
\tag{26}
\]

and define, for every nonempty terminal coalition (A),

\[
 r_i(A)=a_i(A\setminus\{i\})+
   1_{i\in A}\,g_i(A\setminus\{i\}).
\tag{27}
\]

At continuation cap (c=(1,1,1,1)), the Quit-minus-Continue endpoint
difference at every product root is exactly the same homogeneous collision
form as for `FinFourOwnerRiskyStationaryClosure.sharpReward`: the passive
term cancels coalition by coalition, and the empty-coalition term cancels
because (a_i(\varnothing)=c_i). Therefore the exact enumeration behind
`FinFourOwnerRiskyCapLimitRootUniqueness.eq_allContinueRoot_of_isNash`
applies without change: all Continue is the unique exact root. This is also
easy to recheck directly from the four displayed linear collision forms; no
terminal-semantic claim is used in that enumeration.

Now let player (0) Quit at date zero with probability (1/2), let every
other player Continue at date zero, and let everybody Continue forever after
survival. The terminal law is

\[
 \mu=\tfrac12\delta_{\{0\}}+\tfrac12\delta_{\mathrm{Never}}.
\tag{28}
\]

The unrestricted behavioral cap is exactly (c). Player (0) can choose
its singleton payoff (1). After date-zero survival each outsider can also
choose its own singleton payoff (1); at date zero the respective collision
values with player (0) are (1,1,0), so none exceeds (1). The prescribed
payoff and debt vectors are

\[
 u=\left(\tfrac12,0,\tfrac3{10},\tfrac12\right),
 \qquad
 d=c-u=\left(\tfrac12,1,\tfrac7{10},\tfrac12\right).
\tag{29}
\]

Thus every semantic debt is strictly positive, the complete law has a
positive singleton atom, and every singleton is cap-binding, yet the cap root
is uniquely all Continue. Moreover every player is punishment-normal:
`quittingPunishmentValue_le_max_solo` and the nonnegative own singleton value
(1) give (chi_i\le1=r_i(\{i\})).

This does not claim that the table is a positive-minimum hard residual. It
does prove the required no-go: full binding, interior perturbation, parity,
normality, a retained atom, and positive debt in every coordinate do not by
themselves exclude Chamber I. On the actual strict-ray producer one may add
the checked conclusion that the binding set has cardinality three or four;
the regression realizes the allowed cardinality-four arm. A successful
consumer must therefore use a further hard-residual singleton-matrix sign or
chronological source field, not root geometry alone.

## 12. Chamber II: reset-rigid same-law incidence

Section 9 can be iterated over every positive incidence coordinate, but the
iteration has no decreasing state. Each application returns a point with
the identical complete law and debt (D_H); each returned point lies in
\(\mathcal M\), has the same unique all-Continue cap correspondence, and its
dynamic reset exit is again impossible. The `supported_toggle` field is a
strict table inequality on a positive atom. It neither removes that atom
from the law nor changes its mass, and the dispatch contains no rule forcing
the next observer or atom to differ from the previous one. Consequently a
finite-label collision count can repeat forever and is not a rank.

This failure is not merely an absent API. The checked rational
`FinFourEventualAllContinueLocalRegression` has

\[
 \mu=\delta_{\{0,1\}},\qquad
 u=(1,4,1,2),\qquad c=(3,4,2,2),\qquad d=(2,0,1,0),
\tag{30}
\]

positive opponent incidence at a zero-debt owner, punishment normality, and
the hard singleton residual signs, while all Continue is the unique exact
cap root and its maximal cap-prefix orbit is literally constant. The same
file proves that this particular regression has global minimum zero and a
uniform-equilibrium payoff, so it is not a counterexample; it is an exact
fence showing that incidence plus a supported strict toggle does not itself
unstall the cap root.

There are only two mathematically meaningful ways out of Chamber II:

1. turn the supported leave/join toggle into a history-compatible
   own-strategy change whose *total* debt decreases after accounting for all
   other coordinates; or
2. change the complete law and charge that change to a monotone law-support
   or capacity rank.

Neither conclusion follows from `QuittingFixedLawResetDispatch`. Reapplying
same-law minimization is therefore an exact fixed point, not a collision
decoder. This rules out the proposed observer-iteration argument unless one
of the two additional interfaces above is produced.

## 13. Chamber III: singleton/Never law

Write the unique zero-debt owner as (o), and write the law as

\[
 \mu=p\delta_{\{o\}}+(1-p)\delta_{\mathrm{Never}},\qquad p>0.
\tag{31}
\]

There is one useful exact strengthening.

### Lemma 8 (the zero-debt owner is singleton-cap-tight)

At a joint semantic/law carrier point satisfying (31), if
(d_o=0), then

\[
 X^{cap}_o=r_o(\{o\}).
\tag{32}
\]

### Proof

The reward-moment identity gives (X^{pay}_o=p\,r_o(\{o\})), hence
(X^{cap}_o=p\,r_o(\{o\})). If (p=1), this is already (32).

Suppose (p<1). For literal approximating profiles, the joint Never mass
tends to (1-p>0). Hence every player's marginal Never mass is bounded
away from zero. The absence in the limiting law of every finite outcome
containing a player (j\ne o) then forces that player's total finite stopping
mass to tend to zero: the event “(j) stops finitely and every other player
is Never” is a singleton-(j) event and has probability equal to the finite
stopping mass of (j) times the product of the other Never masses. It follows
that the owner's immediate-Quit deviation converges to (r_o(\{o\})), while
the owner's Never deviation converges to zero. Closedness of the envelope
coordinate therefore gives

\[
 X^{cap}_o\ge\max\{0,r_o(\{o\})\}.
\tag{33}
\]

Combining (33) with (X^{cap}_o=p\,r_o(\{o\})), (0<p<1), forces
(r_o(\{o\})=X^{cap}_o=0). `QED`

Lemma 8 feeds the checked solo-probe theorem. Since all Continue is an exact
cap root, every singleton reward is at most the cap. Since it is the unique
exact cap root and (o) is binding, the declaration
`exists_quittingSingletonCollisionGain_pos_of_unique_allContinue` produces a
distinct cap-binding player (j) with

\[
 r_j(\{o,j\})-r_j(\{o\})>0,
 \qquad X^{cap}_j=r_j(\{j\}).
\tag{34}
\]

Repeating this at every newly encountered binding label yields a directed
cycle, of length at least two, inside the cap-binding set. Thus the naive
one-owner all-Never-tail compiler cannot close (31): concentrating the owner
clock into a sure singleton row exposes at least one outsider with a strict
profitable join. Punishment normality controls the owner's refusal floor; it
does not remove this outsider collision gain.

The singleton-clock debt inequality also does not contradict the hull
passport. It would charge the positive singleton mass by the complementary
debt (D_H) only on a chronological window whose shifted tails remain near
(D_H). In a forward prefix realization the retained atom may sit at the
far end of the word, after the shifted tails have climbed back toward the
original source debt. Every fixed near-minimum window can therefore have
zero singleton mass. This is exactly the surviving ballistic marked-atom
seam, now in its one-owner form.

### Exact local regression for the whole chamber

The chamber data, including punishment normality, are mutually consistent.
Use (25) and (27), now with `a_i(∅) = c_i` for
`c = (0,0,0,1)`, and take

\[
 a_1(\{0\})=-1,\qquad a_2(\{0\})=-\tfrac25,\qquad
 a_3(\{0\})=1,
\tag{35}
\]

and let player (0) Quit at date zero with probability (1/2), followed by
the all-Never tail. A direct two-endpoint calculation gives

\[
 \mu=\tfrac12\delta_{\{0\}}+\tfrac12\delta_{\mathrm{Never}},
 \quad
 u=\left(0,-\tfrac12,-\tfrac15,\tfrac12\right),
 \quad
 c=(0,0,0,1),
 \quad
 d=\left(0,\tfrac12,\tfrac15,\tfrac12\right).
\tag{36}
\]

For players (1) and (2), quitting together with player (0) gives zero
and continuing gives a negative value; player (3) optimally waits and gets
its singleton value (1); player (0)'s cap is zero. The passive terms again
cancel from every cap endpoint difference, so the checked owner-risky
collision-form enumeration gives unique all Continue. Normality follows
from (chi_i\le\max(0,r_i(\{i\}))=r_i(\{i\})).

This table is not asserted to satisfy the positive-minimum hard-residual
provenance. It is an exact regression against any proposed implication from
the Chamber III local fields directly to a singleton+Never terminal
equilibrium. The strongest surviving conclusion is (34) and its finite
binding-cycle iteration; consuming that cycle requires a source-compatible
pair/collision chronology.

## 14. Chamber verdict

The strict neutral trichotomy has not been eliminated, but it has been
sharpened enough to rule out three tempting local completions:

- Chamber I survives even with full singleton binding, normality, a positive
  finite atom, and all four debts positive.
- Chamber II is an exact same-law reset fixed point; observer iteration has no
  nonrepeating or decreasing rank.
- Chamber III forces a cap-binding positive-collision cycle, so the literal
  one-owner singleton/Never compiler is unstable rather than terminal.

Accordingly the next valid terminal consumer must use a source-attached
chronology that either charges the Chamber I hard-residual signs, changes law
with a monotone rank in Chamber II, or transports the Chamber III binding
cycle into a pair/collision block before the retained atom escapes the
near-minimum window.

## 15. Remaining concrete question

The next concrete question is:

> Can a positive-minimum Fin4 hard residual contain a strictly off-minimum
> debt minimizer of a closed exact-cap-prefix invariant joint-law hull with a
> positive finite atom and unique all-Continue cap root?

A negative answer completes the branch by minimum-law regeneration.  A
positive answer must realize one of the three forms in Section 10.  The reset
case already collapses to the exact fixed-face stall.  The sharp next attacks
are therefore the full-positive-debt face and the unique-zero-debt
solo/Never-law face; both must use the Fin4 hard-residual table signs or a new
cap-to-prescribed bridge, since exact cap-root uniqueness alone is exhausted.

## Source declarations inspected

- `quittingTerminalSemanticLawCarrier_isCompact`,
  `terminalSemanticLawCarrier_fst_mem_carrier`, and
  `quittingTerminalSemanticLawPrefix_mem_carrier` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`.
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`.
- `capNashPrefix_tailEscape_exact_account` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticStrictTailEscapeReturn.lean`.
- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean` and
  `eq_quittingAllContinueRoot_of_continueMass_eq_one` in
  `UniformEquilibrium/Quitting/Boundary/Analytic/SeamPriceResidual.lean`.
- `finFourHardResidual_minimumLaw_causalSuffixAtom` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumLawFiniteAtom.lean`.
- `QuittingTerminalExploitabilityWitness.exists_fixedLaw_resetFace_dispatch`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceCapReturn.lean`.
- `quittingTerminalSemantic_allContinuePlateau_finiteRewardObstruction` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAllContinuePlateau.lean`
  was inspected as a non-applicable prescribed-payoff-root theorem; the hull
  passport currently supplies exactness only against the cap coordinate.
- `FinFourMinimumAtomProducer` and
  `FinFourMinimumAtomProducer.exists_residual_eq_of_hardResidual` in
  `Research/Quitting/FinFourProducerAtlas/Source.lean`.
- `FinFourStrictRayPositiveRootReturn.returnedPoint_mem`,
  `returnedDebt_eq_limit_sub_charge`,
  `nonempty_minimumLawHandoff_or_offMinimumDescent`, and
  `FinFourStrictRayOffMinimumDescent` in
  `Research/Quitting/FinFourProducerAtlas/StrictRayPositiveRootReturn.lean`.
- `exists_offMinimum_retainedLaw_allContinue_or_supportEntry` in
  `Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean`.
- `exists_quittingSingletonCollisionGain_pos_of_unique_allContinue` in
  `Research/Quitting/BindingCollisionGainPositivity.lean`.
- `eq_allContinueRoot_of_isNash` and `sharpCapLimit_eq_solo` in
  `UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskyCapLimitRootUniqueness.lean`,
  together with the membership-increment definitions in
  `UniformEquilibrium/Quitting/Examples/FinFourOwnerRiskyStationaryClosure.lean`.
- `sum_stageSingletonMass_mul_tailComplementaryDebt_le_epsilon_add_defect`
  and `faceFloor_mul_clockMass_le_epsilon_add_defect` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSingletonClockDebtFace.lean`.
- `exists_quittingAnchoredSingletonClockCompression` and
  `quittingAnchoredSingletonQuitProfile_owner_cap_eq` in
  `Research/Quitting/AnchoredSingletonClockCompression.lean`.
- `QuittingFixedLawResetDispatch.allContinue_of_target_debt_le_source` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFixedLawMinimumTargetStall.lean`
  and `QuittingFixedLawResetDispatch.endpointRoot_or_literalDefect_or_stall`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetEndpointSeam.lean`.
- `pair_semantic_eq`, `exactRoot_eq_allContinue`,
  `maximalPrefixOrbit_pairSemantic_eq`, `neverPair_globalMinimum`, and
  `neverUniformEquilibriumPayoff` in
  `Research/Quitting/FinFourEventualAllContinueLocalRegression.lean`.
- `QuittingInducedOwnerNeverChamber.uniformEquilibriumPayoff` and
  `inducedOwnerNever_continue_sub_quit_pos_gap_of_positiveMinimum` in
  `UniformEquilibrium/Diagnostics/Quitting/InducedOwnerChambers.lean`; these
  require an induced Nash point and outsider no-join signs not supplied by
  the solo/Never hull law.
