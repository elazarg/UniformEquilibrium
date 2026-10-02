# Positive-Never maximum support forces a rectangle excursion

Author: `CODEX_MINER`

Status: **proved ordinary mathematics; independently reviewed PASS; internal
only.**  Independent review:
[`CODEX_EULER`](../feedback/CODEX_MINER__POSITIVE_NEVER_MAX_SUPPORT_RECTANGLE_EXCURSION__BY_CODEX_EULER.md).
The theorem below uses the genuine positive-global-minimum and positive-Never
provenance missing from the local rectangle regressions.  It does not yet
consume the resulting off-minimum corner into a uniform payoff, and therefore
is not an export candidate.

## 1. Question and answer

Start with the reviewed positive-Never late-release packet and its decoded
four profiles

```text
P_n = (source a, source b, common others),
Q_n = (target a, source b, common others),
Y_n = (source a, response b, common others),
Z_n = (target a, response b, common others).
```

The response is one complete pure-time strategy selected against `Q_n`; all
four corners are therefore literal behavioral profiles in one product
rectangle.  Suppose that `Sem(P_n)` converges to a globally minimum semantic
pair `p`, and that the joint outcome laws of `P_n` converge to a minimum law
with positive `Never` coordinate.

Can a new positive-debt coordinate at the decoded corner `Z_n` be exchanged
on the same global minimum fiber without leaving any trace?

Not if the initial positive-Never minimum joint point is selected with
maximal debt-support cardinality among all positive-Never minimum joint
points.  If all four corner limits stayed on the minimum fiber, an executable
proper two-player mixture of the rectangle would also lie on the minimum
fiber, would retain positive joint-Never mass, and would have positive-debt
support equal to the union of the four corner supports.  Any newcomer at a
corner would contradict the maximal selection.

Thus a decoded support entry forces a **fixed off-minimum actual corner**.
If the decoded response endpoint itself stays on the minimum fiber, one of
the two side corners `Q` or `Y` must be off the minimum fiber.  This is a
strict use of global minimality, not a `D_*=0` interface regression.

## 2. Abstract literal rectangle

Let `I` be finite and let `a != b`.  For each `n`, fix a common profile of
the other players and complete behavioral strategies

```text
p^n_a, q^n_a for a,
p^n_b, q^n_b for b.
```

Let `P_n,Q_n,Y_n,Z_n` be the four product corners displayed in Section 1.
Write

```text
x_n = Sem(P_n),  q_n = Sem(Q_n),
y_n = Sem(Y_n),  z_n = Sem(Z_n).
```

Assume, after one common subsequence,

```text
x_n -> x,  q_n -> q,  y_n -> y,  z_n -> z.          (2.1)
```

Let `D_* = D(x)`, assume `x` is a global minimum of terminal semantic debt,
and suppose

```text
D(q)=D(y)=D(z)=D_*.                                 (2.2)
```

Fix `0<lambda<1` and `0<theta<1`.  Define the literal inner profiles

```text
A^0_n = (mix_lambda(p^n_a,q^n_a), p^n_b, others),
A^1_n = (mix_lambda(p^n_a,q^n_a), q^n_b, others),
```

where `mix` is the complete stopping-law mixture used by
`quittingStoppingLawMixtureBehaviorStrategy`.  Then define

```text
W_n = (mix_lambda(p^n_a,q^n_a),
       mix_theta(p^n_b,q^n_b), others).              (2.3)
```

This is an actual product behavioral profile.  It is not a correlated
mixture of the four whole profiles.

## 3. Bilinear minimum-fiber lemma

### Theorem 3.1

Under (2.1)--(2.3), every cluster point `w` of `Sem(W_n)` belongs to the
terminal semantic carrier, lies on the same global minimum fiber, and has
the coordinatewise debt vector

\[
 d(w)=(1-\theta)\bigl((1-\lambda)d(x)+\lambda d(q)\bigr)
      +\theta\bigl((1-\lambda)d(y)+\lambda d(z)\bigr).       \tag{3.1}
\]

Consequently

\[
 \operatorname{supp}_+ d(w)
 =\operatorname{supp}_+d(x)\cup\operatorname{supp}_+d(q)
  \cup\operatorname{supp}_+d(y)\cup\operatorname{supp}_+d(z). \tag{3.2}
\]

### Proof

Put `e^P_n=D(x_n)-D_*`.  Carrier minimality gives `e^P_n>=0`, and
`e^P_n->0`.  Apply
`quittingTerminalSemanticDebt_stoppingLawMixture_chordGap_le_nearMinimum`
to the `a`-edge `P_n--Q_n`.  For every coordinate `i`, its nonnegative chord
gap is bounded by

\[
 e^P_n+\lambda\bigl(D(q_n)-D(x_n)\bigr)\longrightarrow0.     \tag{3.3}
\]

Hence

\[
 d_i(A^0_n)\longrightarrow(1-\lambda)d_i(x)+\lambda d_i(q). \tag{3.4}
\]

Apply the same theorem to the parallel `a`-edge `Y_n--Z_n`.  Its source
excess `D(y_n)-D_*` tends to zero, as does its endpoint-minus-source total
debt.  Therefore

\[
 d_i(A^1_n)\longrightarrow(1-\lambda)d_i(y)+\lambda d_i(z). \tag{3.5}
\]

Summing (3.4)--(3.5) and using (2.2) shows

```text
D(Sem(A^0_n)) -> D_*,   D(Sem(A^1_n)) -> D_*.       (3.6)
```

Now apply the same chord-gap theorem to the literal `b`-edge
`A^0_n--A^1_n` with outer weight `theta`.  Its source excess and its total
endpoint-minus-source difference both tend to zero by (3.6).  The resulting
coordinate gaps tend to zero, and (3.4)--(3.5) give (3.1).

Every `Sem(W_n)` is an actual terminal semantic pair.  Compactness gives a
cluster point in the carrier, and continuity of semantic debt identifies
its debt vector with (3.1).  Summing (3.1) gives `D(w)=D_*`.

All four corner debt vectors are coordinatewise nonnegative because their
limits belong to the carrier.  Every coefficient in (3.1) is strictly
positive.  Thus a coordinate of `d(w)` is positive exactly when it is
positive at at least one corner, proving (3.2). `QED`

## 4. Retaining the positive-Never class

Now work in the joint semantic/law carrier.  Suppose the law component
`mu` of the source limit `(x,mu)` satisfies

```text
mu(Never)>0.                                          (4.1)
```

In the late-release rectangle, `q^n_a` is obtained by moving the source
`Never` clock of `a` to a finite date.  The response `q^n_b` may be finite or
`Never`.  Under (2.3), the event in which both outer mixtures choose their
source branches and all source clocks are `Never` has probability

\[
 (1-\lambda)(1-\theta)\,
   \Pr_{P_n}(\text{all clocks Never}).                \tag{4.2}
\]

It is a subevent of `W_n`'s joint-Never outcome.  Passing to a common
joint-law cluster gives

\[
 \operatorname{Law}(w)(\mathrm{Never})
 \ge (1-\lambda)(1-\theta)\mu(\mathrm{Never})>0.       \tag{4.3}
\]

No whole-profile convexity is used here.  Equation (4.2) is the literal
product of the two independent complete stopping-law mixture choices.

## 5. Maximum-support excursion theorem

### Theorem 5.1

Assume the positive-Never minimum joint-law class is nonempty.  Choose
`(x,mu)` in that class for which

```text
card(supp_+ d(x))                                    (5.1)
```

is maximal.  Such a point exists because the possible cardinalities lie in
the finite set `{0,...,card I}`; no compactness of the strict condition
`mu(Never)>0` is needed.

Let a literal rectangle sequence based at `(x,mu)` satisfy (2.1).  If all
three other semantic corner limits lie on the minimum fiber, then

\[
 \operatorname{supp}_+d(q),\operatorname{supp}_+d(y),
 \operatorname{supp}_+d(z)
 \subseteq \operatorname{supp}_+d(x).                \tag{5.2}
\]

Equivalently, if any corner has a positive-debt newcomer relative to `x`,
then at least one of `q,y,z` has total debt strictly larger than `D_*`.

### Proof

If all corners are minimum points, Theorem 3.1 supplies a minimum semantic
cluster `w`, and Section 4 supplies a compatible joint-law cluster with
positive Never mass.  Its support is the union (3.2), hence contains the
support of `x`.  Maximality (5.1) forces equality of cardinalities and
therefore equality of the two finite sets.  Each other corner support is a
subset of that union, giving (5.2).

For the contrapositive, global minimality gives `D_*<=D(q),D(y),D(z)`.
Failure of equality for at least one corner is therefore strict. `QED`

### Corollary 5.2 (decoded support exchange)

Apply Theorem 5.1 to the reviewed late-release rectangle, after selecting
the starting positive-Never minimum joint point by (5.1) and passing to one
common corner/law subsequence.  If the decoded best-response corner `z` has
a new positive-debt player, then

```text
D(q)>D_* or D(y)>D_* or D(z)>D_*.                    (5.3)
```

If `z` itself is on the minimum fiber—the literal support-exchange case—then

```text
D(q)>D_* or D(y)>D_*.                                (5.4)
```

After a further finite choice, the strict corner in (5.3) or (5.4) is fixed,
and convergence gives a fixed positive excess, for example

```text
D(Q_n) >= D_* + delta
```

eventually for some `delta>0`, or the analogous statement for `Y_n` or
`Z_n`.  The corner is one of the actual profiles in the original literal
rectangle; no carrier point is reselected independently.

## 6. What this does and does not consume

Theorem 5.1 rules out the exact mechanism of the reviewed `D_*=0`
support-rotation regression **when every rectangle corner is asserted to stay
on the genuine minimum fiber**.  A newcomer must instead be paid for by a
fixed off-minimum excursion at an actual side or endpoint corner.

That conclusion is not yet one of the conjecture-closing outputs.  Current
checked declarations do not turn an arbitrary fixed off-minimum rectangle
corner into:

- a payoff near-return;
- a carrier point below `D_*`;
- a recursively regenerated rectangle of smaller natural-valued rank; or
- terminal approximate Nash profiles.

If the off-minimum corner is the response endpoint `Z`, its response player
has zero debt and `resetExcursion_absorbingReturn_or_allContinue_capFace`
gives an absorbing exact cap-prefix descent or another all-Continue cap face.
The absorbing arm is an exact charged edge but not an admissible return; the
all-Continue arm is precisely the maintained inert wall.  If a side corner
`Q` or `Y` is off minimum, even the reset-coordinate hypothesis may be
absent.  Applying the terminal witness there produces an actual full-gap
paid row and the paid-cap descent/inert trichotomy, but does not eliminate its
descent-provenance or inert branches.

Thus the new theorem contracts **same-fiber support exchange** to a fixed
actual excursion, while exposing the exact remaining consumer: use the
source-matched rectangle to return from that excursion with positive charge,
or prove that its all-Continue cap face is incompatible with the original
positive-Never minimum source.  No such final implication is claimed here.

## 7. Source and duplicate audit

Checked declarations inspected:

- `quittingTerminalSemanticDebt_stoppingLawMixture_chordGap_le_nearMinimum`
  in `StoppingLaw/TerminalSemanticStoppingLawMinimumFiberAffine.lean`;
- compactness and membership of the terminal semantic and joint semantic/law
  carriers;
- `resetExcursion_absorbingReturn_or_allContinue_capFace` in
  `TerminalSemanticResetExcursionReturn.lean`;
- the support-drop and re-extraction declarations in
  `StoppingLaw/Endpoint/MinimumFiberSupportDrop.lean` and
  `StoppingLaw/Endpoint/NormalizedCurvaturePaidRow.lean`; and
- the reviewed late-release notes
  `CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY.md` and
  `CODEX_MINER__FIN4_LATE_RELEASE_RECTANGLE_THREE_LABEL_BOUNDARY.md`.

The closest existing discussion is Section 3 of
`CODEX_EULER__FIN4_BALANCED_COMMON_RESPONSE_MINIMUM_FIBER_ATTACK.md`, which
records support union on a single same-minimum stopping-law chord.  It does
not prove the two-coordinate bilinear rectangle theorem, retain positive
Never mass in its executable interior, or use maximal support in the
positive-Never minimum joint class to force an actual off-minimum corner.

The aligned-reset R/I/D/X classification concerns an independently selected
global reset-face minimizer.  It has no literal two-coordinate rectangle
whose proper interior can be used in (3.1), so Theorem 5.1 does not collapse
its abstract support-exchange arm.

## Review request

Please falsify the three successive applications of the near-minimum chord
gap theorem, the bilinear debt formula and support union, the literal
positive-Never lower bound (4.2), the maximal-cardinality selection on the
nonclosed positive-Never class, and the exact scope of Corollary 5.2.  In
particular, check that no whole-profile convexity or attainment is used.
