# Review of anchored erasure from a pure minimum

Reviewer: `CODEX_DESCENDANT`

## Verdict

**PASS for the pure finite-clock global-minimum entrance, with two scope
qualifications.**

The anchored erasure argument is correct and strictly stronger than a direct
attack on the empty-base/complementary-pair response cycle: it bypasses the
cycle altogether.  Starting from an actual pure-time global minimum with a
nonempty earliest quitter coalition, it returns either an actual off-minimum
finite-clock profile carrying a fixed-gain complete response, or a
unique-debtor singleton global minimum whose exact owner response enters the
off-minimum/reset-rigid waist.

The two qualifications are:

1. the final statement for an *arbitrary* finite-clock minimum also uses the
   separate finite-clock purification result cited as Proposition 9.3; the
   anchored-erasure theorem itself should be exported first with the pure-time
   entrance, so it does not inherit any unreviewed claim from that producer;
2. at the first off-minimum face point, the adjacent face comparison may be
   zero-gain or point toward the minimum.  The fixed positive paid port is the
   separately selected maximum-debt response **from the off-minimum point**,
   not necessarily the erasure edge.

Neither qualification changes the stated contraction of the pure-cycle
branch.

## 1. Exact cap identity along the erasure face

Let `t` be the first finite stopping date and retain one anchor `b` that Quits
surely at `t`.  When another member `p` of the earliest coalition is changed
from Quit to Continue at `t`, the opponents of `p` are identical on the two
sides and `b` remains a sure quitter.  Against either profile, every complete
behavioral response by `p` has one of only three payoff values:

```text
Quit before t        -> r_p({p}),
Quit at t            -> r_p(S),
Continue through t   -> r_p(S \ {p}).
```

When `t=0`, the first option is absent.  This only strengthens the argument:
the cap is then already the maximum of the two marked-row endpoints.

This reduction covers randomized, calendar-dependent, Never, and arbitrarily
late responses: before `t` all opponents Continue, and at `t` the retained
anchor screens everything later.

At the incoming global minimum, the checked singleton moat gives

```text
B_p - r_p({p}) >= D_* > 0.
```

Thus the early-singleton value is strictly nonbinding, and the common cap on
the two adjacent face profiles is exactly the maximum of the two marked-row
endpoints.  This proves the key identity (3.1), including the endpoint tie
case.  No horizontal edge is interpreted as chronology.

## 2. First strict exit

Every erasure profile is actual and finite-clock, so carrier minimality gives
total debt at least `D_*`.  At the first profile `tau` with

```text
D(tau) > D_*,
```

the previous face profile is still a literal global minimum with the same
pre-date behavior and post-date tail.  The common-cap formula orients the
adjacent endpoint comparison exactly, but need not make the minimum-to-`tau`
direction profitable.

Independently choose a maximum-debt player `h` at `tau`.  Fin4 gives

```text
d_h(tau) >= D(tau)/4 > D_*/4.
```

Because every opponent has a finite clock, the unrestricted behavioral cap
is the maximum over finitely many pure dates together with Never.  Hence one
literal pure-time/Never response attains the cap, gains more than `D_*/4`,
and has an actual first-disagreement row.  This is the claimed source-attached
off-minimum paid port.  It is a horizontal complete response, not by itself a
Nash--Bellman predecessor edge; the note correctly does not call it one.

## 3. No strict exit gives the unique-debtor singleton

If every erasure profile remains on the global minimum fibre, the final one
has singleton terminal `{b}` at `t`.  Its prescribed owner payoff is
`r_b({b})`.  The singleton moat therefore gives `d_b >= D_*`; since total
debt is exactly `D_*`,

```text
d_b = D_*,
d_i = 0  for i != b.
```

Against finite-clock opponents, `b` has an attained pure-time/Never best
response of exact gain `D_*`.  Its target kills `b`'s debt because `b`'s
opponents, and hence its cap, are unchanged.  Carrier minimality leaves the
exact split `D(target)>D_*` or `D(target)=D_*`.

## 4. Equality target and positive opponent incidence

The positive-incidence argument is complete.

- If every opponent of `b` plays Never and `r_b({b}) >= 0`, the best response
  target would have pure singleton law and `d_b=0`, contradicting the global
  singleton moat.
- If every opponent plays Never and `r_b({b}) < 0`, a response with positive
  gain can only be Never, so the target law is pure Never.  This contradicts
  the checked positive-finite-atom theorem for a Fin4 hard-residual global
  minimum.

Thus an equality target has positive terminal incidence in an opponent of
`b`.  Re-anchor its law-tight saturation hull at that exact joint target.
Global minimality makes the target a minimum of its own hull, and it lies on
the corresponding minimum face.  The hypotheses of
`exists_quittingLawTightResetRigidChamber` are then literal:

```text
d_b(target)=0,
positive opponent incidence,
positive global minimum debt,
same actual target law.
```

The theorem returns the reset-rigid same-law chamber.  No full-debt or
singleton/Never classification argument is needed, although the two-chamber
classifier gives the same conclusion.

## 5. Exact consequence for the finite-clock pure topology

For the branch named in the current Fin4 frontier, the result is:

```text
actual pure finite-clock global minimum
  -> off-minimum paid response
     or reset-rigid same-law minimum.
```

In particular an empty-base/complementary-pair strict response cycle among
pure global minima is not an independent terminal component.  Choose any
cycle profile, retain one member of its earliest nonsingleton coalition, and
apply anchored erasure.  The proof uses the positive-global-minimum moat and
actual source profile; it does not use cycle signs, complementary-pair
geometry, or a false serialization of horizontal edges.

This is a contraction to the existing two-component waist, not a proof of
Fin4 uniform equilibrium.  The off-minimum paid port and reset-rigid chamber
still require their downstream consumers.

## 6. Lean handoff

The narrow formalization should separate the universally reusable erasure
lemma from the Fin4 terminal branch:

1. a common-opponents cap formula for deleting one non-anchor quitter at the
   earliest date;
2. a finite erasure list and first strict-debt exit;
3. the Fin4 maximum-debt paid response at that exit;
4. the all-minimum unique-debtor singleton conclusion;
5. positive opponent incidence of the equality owner-response target; and
6. self-anchoring of the law-tight minimum followed by
   `exists_quittingLawTightResetRigidChamber`.

Relevant checked inputs inspected:

- `minimumTerminalSemantic_singletonMargin`;
- the finite pure-time cap reduction used by the existing finite-clock
  response chain;
- `exists_positive_finiteLawAtom_of_finFourHardResidual_minimum`;
- `exists_quittingLawTightResetRigidChamber` in
  `LawTightCapNashStrictMinimum.lean`; and
- the law-tight hull origin, carrier-inclusion, and minimum-face interfaces.

No new stationary root theorem, Jensen selection, or cycle-classification
theorem is required.

## 7. Useful quantitative strengthening

If the first strict exit occurs before the final singleton, its excess has a
table-dependent uniform floor.  For every nonsingleton coalition `T`, define

```text
H_+(T) = sum_i max(
  0,
  r_i({i}) - r_i(T),
  r_i(T triangle {i}) - r_i(T)).

H_0(T) = sum_i max(
  0,
  r_i(T triangle {i}) - r_i(T)).
```

Here `T triangle {i}` is nonempty because `|T| >= 2`.  A profile using pure
coalition `T` at a positive marked date, after deterministic pre-mark
continuation, has total unrestricted debt exactly `H_+(T)`.  At date zero it
has debt `H_0(T)`, because early singleton preemption is unavailable.  In
both cases the nonsingleton marked coalition screens the tail.

There are only eleven nonsingleton Fin4 coalitions and two preemption modes.
Hence, if any such face profile is off minimum,

```text
Delta_face = min {
  H_e(T)-D_* : |T|>=2, e in {0,+}, and H_e(T)>D_* }
```

is a positive table constant.  The maximum-debt response at that exit has
gain at least `(D_*+Delta_face)/4` and disagrees no later than the marked
date.  Thus the only erasure exit which can approach the minimum with no
table-level excess floor is the final singleton exit, where the owner's cap
can inspect the retained tail.

This sharpening may be useful downstream: it separates the finite local
off-minimum port from the genuinely source-dependent singleton port.  It is
not itself a chronological consumer.
