# Positive-Never rectangle cap ray: minimum-support rotation or a unique-all-Continue fixed point

Author: `CODEX_EULER`

Status: **proved ordinary mathematics; independently reviewed REVISE to PASS
after the scope repairs below; internal only.**  Reviews:
[`CODEX_RAMSEY`](../feedback/CODEX_EULER__POSITIVE_NEVER_RECTANGLE_CAP_RAY_REGENERATION__BY_CODEX_RAMSEY.md)
and
[`CODEX_MINER`](../feedback/CODEX_EULER__POSITIVE_NEVER_RECTANGLE_CAP_RAY_REGENERATION__BY_CODEX_MINER.md).
This is a best-attempt continuation of the reviewed maximum-support rectangle
excursion and of
[`POSITIVE_NEVER_OFF_MINIMUM_CORNER_CAP_FACE_REDUCTION`](CODEX_EULER__POSITIVE_NEVER_OFF_MINIMUM_CORNER_CAP_FACE_REDUCTION.md).
It obtains a one-step lower-ordered positive-Never minimum support whenever
the compact cap ray returns to the minimum.  This is not the checked strict
subset/cardinality support descent and is not iterable.  The exhaustive
remaining arm is a positive-Never off-minimum joint point at which every
exact cap root is all Continue.  No uniform payoff is claimed.

## 1. Self-contained question

Fix a finite quitting table with terminal exploitability gap and positive
global terminal-semantic debt minimum

```text
D_*>0.
```

Let `(x,mu)` be a globally minimum joint semantic/law point with
`mu(Never)>0`.  Choose its positive-debt support `K` maximal under a fixed
total order on subsets which extends strict inclusion.  The reviewed literal
two-coordinate rectangle starts at `(x,mu)` and has a corner limit `c` with
a newcomer

```text
j notin K,   d_j(c)>0.                               (1.1)
```

The maximum-support theorem says that some actual rectangle corner is
off-minimum.  The preceding cap-face reduction consumes any strict
singleton-over-cap gap there.  What can be said in the surviving
all-Continue cap-face arm without dropping the positive-Never provenance?

The corner itself may have zero joint-Never mass.  It is therefore incorrect
to apply positive-Never cap-ray arguments directly to `Q` or `Z`.  The first
step below repairs this by returning to the literal product rectangle.

## 2. Restoring positive Never without losing the newcomer

### Lemma 2.1 (proper interior point)

There is a joint semantic/law carrier point `(z,nu)` obtained as a cluster of
literal proper two-coordinate stopping-law mixtures in the same rectangle
such that

```text
nu(Never)>0,        d_j(z)>0.                         (2.1)
```

Moreover the mixtures may be chosen arbitrarily close to the newcomer corner
`c`.

### Proof

Use the two complete stopping-law mixture parameters of the reviewed
rectangle, but keep each source-branch weight strictly positive.  The event
that both mixture coins choose their source branches and every source clock
is Never has probability

```text
(source weight a)*(source weight b)*mu(Never)>0.      (2.2)
```

This is a literal product-profile event, not a correlated mixture of whole
profiles.  Choose the target weights sufficiently close to the corner and
then pass to the already common corner/law subsequence.  Continuity of
semantic debt and (1.1) preserve `d_j>0`; the fixed positive expression in
(2.2) survives the joint-law limit.  There is no hidden interchange of two
uncontrolled limits here: changing a complete stopping law by a mixture coin
of source weight `epsilon` changes every terminal payoff and every pure-time
deviation payoff by at most `2M*epsilon`.  Applying this successively in the
two player coordinates gives a uniform `O(epsilon_a+epsilon_b)` bound on both
semantic coordinates, independent of the rectangle index.  Hence fixed
proper weights sufficiently close to the desired corner retain the strict
newcomer inequality before the common subsequence limit is taken. `QED`

The point `z` can already lie on the global minimum fiber.  If it does, it is
a positive-Never minimum point with support different from `K`; by maximality
of `K` in the fixed total order, its support lies strictly below `K` in that
chosen order.  This is only a one-step different-support minimum alternative.
It is not strict subset/cardinality descent and does not regenerate the
maximal-support hypothesis.

Henceforth suppose

```text
D(z)>D_*.
```

## 3. The compact debt-and-Never cap ray

Put

```text
c0 = D_*/D(z),                 0<c0<1.                (3.1)
```

Define `Ray(z,nu)` to be the set of joint carrier points `(y,lambda)` for
which there is a scalar `c in [c0,1]` satisfying

```text
d_i(y)=c*d_i(z)       for every i,
lambda(Never)=c*nu(Never).                            (3.2)
```

### Lemma 3.1 (compactness and exact cap invariance)

`Ray(z,nu)` is nonempty and compact.  If `(y,lambda)` belongs to the ray and
`q` is any exact product-root Nash equilibrium against `y.2`, then the joint
semantic/law prefix of `(y,lambda)` by `q` also belongs to the ray.

### Proof

Nonemptiness uses `(z,nu)` with `c=1`.  The joint carrier and `[c0,1]` are
compact, and (3.2) is a finite family of closed equalities; projecting the
resulting compact subset gives compactness.

Let

```text
s = ContinueMass(q) = 1-Absorption(q).
```

The checked exact scaling identities give

```text
d_i(prefix_q(y))       = s*d_i(y) = (s*c)*d_i(z),
Law(prefix_q(y))(Never)= s*lambda(Never)
                         = (s*c)*nu(Never),
D(prefix_q(y))          = s*c*D(z).                  (3.3)
```

The prefixed point is in the joint carrier.  Global minimality gives
`D_*<=s*c*D(z)`, hence `c0<=s*c`; trivially `s*c<=1`.  Thus the new scalar
lies in `[c0,1]`, proving invariance. `QED`

This ray is deliberately larger than the closure of finite reachable words.
That enlargement is essential: the exact-root correspondence need not be
lower hemicontinuous, so closure of the literal reachable set is not known to
be prefix invariant.

## 4. Ray minimization theorem

### Theorem 4.1 (minimum-support rotation or unique-all-Continue fixed point)

Let `(y,lambda)` minimize total semantic debt on `Ray(z,nu)`.  Then

```text
lambda(Never)>0,
supp_+ d(y)=supp_+ d(z),                              (4.1)
```

and every exact product-root Nash equilibrium against `y.2` is the literal
all-Continue root.

Consequently exactly one of the following holds.

1. `D(y)=D_*`.  Then `(y,lambda)` is a positive-Never global-minimum joint
   point retaining the newcomer `j`.  Its support differs from the selected
   greatest support `K` and therefore lies strictly below `K` in the fixed
   finite total order.  This is a one-step different-support minimum return,
   not a strict-subset or iterable support-rank descent.
2. `D(y)>D_*`.  Then `(y,lambda)` is an off-minimum positive-Never point with
   the same newcomer support as `z`, and its exact cap-root correspondence is
   the singleton `{all Continue}`.  Prefixing by that root fixes both its
   semantic pair and complete terminal law.

### Proof

Compactness gives a minimizer.  Its witnessing scalar satisfies `c>=c0>0`.
Since `nu(Never)>0` and every positive coordinate of `d(z)` is multiplied by
the same positive scalar, (4.1) follows.

Let `q` be any exact root against `y.2`; such a root exists.  By Lemma 3.1 its
prefix lies in the same ray.  If `q` had positive absorption, then its
Continue mass `s` would satisfy `s<1`, and (3.3) would give

```text
D(prefix_q(y))=s*D(y)<D(y),
```

contradicting ray minimality.  Hence every exact root has zero absorption.
For a finite product root, zero absorption forces every marginal to be pure
Continue, so `q=allContinue`.  Exactness then gives all singleton cap
inequalities through
`isZeroQuittingRootNash_allContinue_iff_singleton_le`, and
`quittingTerminalSemanticPrefix_allContinue_eq_of_singleton_le_cap` fixes the
semantic pair.  The all-Continue law-prefix identity fixes the complete law.

If `D(y)=D_*`, `(y,lambda)` is an eligible positive-Never minimum point.  Its
support contains `j notin K`, so it differs from `K`; greatestness of `K`
among the occurring positive-Never minimum supports puts the new support
strictly below `K` in the chosen order.  Otherwise it is precisely the second
arm. `QED`

## 5. What provenance survives

The construction retains:

- the original reward table and positive global minimum;
- an actual product-profile approximation from the same literal two-player
  rectangle in Lemma 2.1;
- positive joint-Never mass;
- the newcomer debt label;
- exact joint-law and coordinatewise-debt scaling under every cap prefix; and
- unrestricted behavioral caps in the terminal semantic annotation.

It does **not** retain at the ray minimizer:

- the particular three terminal labels `{a}`, `{b}`, `{a,b}` of the decoded
  late-release atom;
- an attained behavioral profile realizing `(y,lambda)`;
- the original early-window/late-singleton dates;
- a paid first-disagreement row; or
- literal reachability from `z` by one chosen finite cap word.

Arm 1 may be source-realized and causalized by the checked selected-law/source
telescope, but that operation does not preserve the ray, newcomer, or the
oriented rectangle step.  The original greatest support `K` still occurs, so
the maximum-support excursion theorem cannot automatically be reapplied at
the lower-ordered point.  No iteration or maintained rank descent is proved.

Arm 2 is stronger than merely restating the all-Continue cap-face
inequalities: it is a compactly selected off-minimum positive-Never
**unique-root fixed point** on the exact invariant debt/law ray.  The present
note does not contradict or consume that fixed point.

## 6. Exact source audit

The proof uses:

- literal product stopping-law mixtures and the positive-Never lower bound
  from `CODEX_MINER__POSITIVE_NEVER_MAX_SUPPORT_RECTANGLE_EXCURSION`;
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
- `quittingTerminalOutcomeLawPrefix`, its exact Never-coordinate formula,
  and `quittingTerminalSemanticLawPrefix_mem_carrier` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetIncidenceReturn.lean`;
- compactness of the joint semantic/law carrier; and
- `isZeroQuittingRootNash_allContinue_iff_singleton_le` and
  `quittingTerminalSemanticPrefix_allContinue_eq_of_singleton_le_cap` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.

The closest prior result is
`CODEX_RAMSEY__POSITIVE_NEVER_CAP_PREFIX_MOAT_AND_ROTATION_SEAM`, which works
with closures of literal finite cap-word endpoints and correctly identifies
the equal-cardinality rotation seam.  The invariant compact ray above avoids
the unproved lower-hemicontinuity needed to make that reachable closure
prefix invariant, and it upgrades the limiting obstruction to uniqueness of
the all-Continue exact root.  It still does not make the ray minimizer
literally reachable.

## 7. Review request and exact remaining blocker

Please falsify:

1. the proper-interior positive-Never/newcomer simultaneous selection;
2. compactness of `Ray(z,nu)` as a projected closed set;
3. the lower bound `s*c>=c0` from global minimality;
4. exact law/debt scaling and support preservation; and
5. the inference from ray minimality to uniqueness of the all-Continue root.

Neither arm is presently a maintained `FIN4_BT` consumer.  The exact remaining
obstruction is not another weak cap-face inequality.  It
is the existence of an off-minimum, positive-Never joint carrier point whose
complete debt vector and Never mass lie on the rectangle-generated ray and
whose exact cap-root correspondence is uniquely all Continue.  Consuming
that object requires a non-cap predecessor/return retaining the three-label
late-release provenance, which ray minimization itself discards.
