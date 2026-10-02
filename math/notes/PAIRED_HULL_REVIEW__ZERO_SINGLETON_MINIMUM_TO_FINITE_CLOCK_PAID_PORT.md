# Zero-singleton minimum laws enter the finite-clock paid-port descent

Identity: `PAIRED_HULL_REVIEW`

Date: 2026-08-31

Status: **the two components are independently checked production Lean
declarations; their direct end-to-end composition is not a named checked
declaration.** The composition removes the zero-Never/zero-singleton joint-law
branch directly to the existing off-minimum paid port. It does not consume
that port.

## 1. Exact theorem

Let \(I=\operatorname{Fin}4\), and let \(r(S)\in\mathbb R^I\) be a bounded
quitting reward table.  Let

\[
 z=(U,B)
\]

be a point of the terminal-semantic carrier which globally minimizes total
unrestricted behavioral debt,

\[
 D(z)=D_*>0.
\]

Suppose \((z,\mu)\) is a joint terminal-semantic/law carrier point above
\(z\), and

\[
 \mu(\mathrm{Never})=0,
 \qquad
 \mu(\{i\})=0\quad(i\in I).
\tag{1.1}
\]

Then there exist:

1. a product root \(q\in[0,1]^I\) with at least two sure quitters;
2. the literal behavioral profile \(\rho(q)\) which plays \(q\) at date zero
   and Never after all Continue;
3. a finite list of literal unilateral behavioral replacements beginning at
   \(\rho(q)\); and
4. a finite-clock target profile \(\xi\), a player \(h\), and a pure time or
   Never response \(\tau_h\),

such that

\[
 \operatorname{Sem}(\rho(q))=z,
 \qquad
 \mathcal L(\rho(q))=\mu,
\tag{1.2}
\]

\[
 D(\operatorname{Sem}(\xi))>D_*,
\tag{1.3}
\]

and

\[
 U_h(\tau_h,\xi_{-h})-U_h(\xi)
 =d_h(\operatorname{Sem}(\xi))
 >\frac{D_*}{4}.
\tag{1.4}
\]

The response in (1.4) is optimal over the complete behavioral strategy
class.  Its two pure-time/Never endpoints have a literal positive first
disagreement on the same actual target profile.

No full-debt hypothesis \(d_i(z)>0\) for every \(i\) is needed.

## 2. Proof

Because \((z,\mu)\) belongs to the joint carrier, choose actual behavioral
profiles \(\sigma_n\) whose semantic pairs and terminal laws converge jointly
to \((z,\mu)\).

Apply the closed-law product-base theorem from
[`ZERO_SINGLETON_BEHAVIORAL_LAW_PRODUCT_BASE_AND_SURE_CORE_DESCENT.md`](../formalized/ZERO_SINGLETON_BEHAVIORAL_LAW_PRODUCT_BASE_AND_SURE_CORE_DESCENT.md).
Hypothesis (1.1) gives a product vector \(q\) with a sure-quitter core

\[
 K=\{i:q_i=1\},
 \qquad |K|\geq2,
\tag{2.1}
\]

whose one-root law is exactly \(\mu\).

At every positive global minimum, the checked singleton margin gives

\[
 B_i-r_i(\{i\})\geq D_*>0
 \qquad(i\in I).
\tag{2.2}
\]

The complete-cap part of the same product-base theorem therefore applies in
its strict form.  It proves that the unpadded profile \(\rho(q)\), which plays
the product root once and then Never, has exactly the prescribed payoff,
unrestricted behavioral cap, and law displayed by \((z,\mu)\).  This proves
(1.2).  Stationary repetition of \(q\) is semantically equivalent, because
after any unilateral replacement at least one unchanged member of \(K\)
still Quits surely at the first row.

Each player's stopping-time law in \(\rho(q)\) is supported on

\[
 \{0,\infty\}.
\]

Thus \(\rho(q)\) is an actual finite-clock profile attaining the positive
global minimum \(z\).  Apply the Fin4 finite-clock corollary of
`formalized/PURE_FINITE_CLOCK_MINIMUM_DEADLINE_RANK_TO_PAID_PORT.md`. It gives a finite
literal unilateral-replacement ancestry from \(\rho(q)\) to an off-minimum
finite-clock target \(\xi\), then selects a maximum-debt coordinate and a
pure-time/Never cap attainer.  The theorem gives (1.3)--(1.4) and its literal
first-disagreement witness.

This completes the composition.

## 3. What was already proved

The mathematical work is contained in two reviewed, formalized packets.

1. [`ZERO_SINGLETON_BEHAVIORAL_LAW_PRODUCT_BASE_AND_SURE_CORE_DESCENT.md`](../formalized/ZERO_SINGLETON_BEHAVIORAL_LAW_PRODUCT_BASE_AND_SURE_CORE_DESCENT.md)
   proves the closed-law product representation and the exact complete-cap
   root-then-Never realization.  It has two independent reviews.
2. `formalized/PURE_FINITE_CLOCK_MINIMUM_DEADLINE_RANK_TO_PAID_PORT.md` proves that every
   actual Fin4 finite-clock positive global minimum reaches an actual
   off-minimum paid port.  It has three independent reviews.

The first export continued through a full-debt sure-core softening rank and a
positive-singleton output.  That rank remains valid and retains more explicit
product geometry, but it is unnecessary when the desired downstream endpoint
is merely the off-minimum actual paid port: the finite-clock theorem applies
immediately to the exact realization (1.2), without full debt.

The closed-law product root, exact semantic realization, and finite-clock
paid-port descent are production Lean. The direct composition displayed here
has not been packaged as one checked declaration.

## 4. Exact source preservation

The construction does not select an unrelated minimum or law.  It begins
with the supplied joint point \((z,\mu)\), constructs \(q\) from an actual
realizing sequence of that same joint point, and proves literal equality
(1.2).  The finite-clock descent therefore starts at an actual profile
realizing the exact supplied semantic pair and exact supplied terminal law.

The original realizing profiles and any earlier hard residual may be retained
as external provenance.  What is not retained is their literal calendar or
their marked-date chronology.  The product profile is a new exact
realization of the same joint point, and the paid replacement ancestry begins
at that realization.

This distinction matters only for a downstream node demanding the original
marked rows, suffixes, or cap-prefix word definitionally.  The off-minimum
actual paid-port interface needs an actual parent, actual replacements, and
the retained global minimum as provenance; for that interface the
composition is source-adequate.

## 5. The product root is not a Nash root

The phrase “exact product root” must mean exact product-law and semantic
realization.  It does **not** mean an exact one-stage cap-Nash root.

For example, let \(q\) be the pure pair root \(\{0,1\}\).  Give player \(0\)

\[
 r_0(\{0,1\})=0,
 \qquad
 r_0(\{1\})=1.
\]

Then player \(0\) profits by Continuing while player \(1\) Quits.  The root
still has zero Never mass, zero singleton terminal-law mass, and two sure
quitters, but it is not root Nash.

Nothing in (1.1) forces the endpoint complementarity inequalities needed for
root Nash.  This is harmless: the finite-clock descent starts from an
arbitrary finite-clock global-minimum profile and performs literal best
responses; it does not assume its initial root is Nash.

## 6. Sharp hypothesis boundaries

### Positive minimum is needed for the unpadded cap identity

If a realizing sequence waits before its efficient product root, a deviator
may Quit during the waiting period and obtain its singleton reward.  Without
(2.2), compressing the root to date zero can lower the cap.  For example, a
delayed pure-pair source can have singleton option \(10\), while both root
endpoints are \(0\).  Its cap is \(10\), whereas the unpadded root-then-Never
cap is \(0\).

At a positive global minimum, (2.2) says the limiting cap is strictly above
the singleton option, so the option is nonbinding and compression is valid.

### Both law conditions are used

Zero singleton mass alone does not exclude the pure Never law.  Zero Never
mass forces absorption, while zero singleton mass concentrates an efficient
product root onto a sure core of cardinality at least two.

### Arbitrary calendar interventions are not transported

The cap comparison is uniform over one unilateral behavioral response before
taking the supremum.  It does not preserve the law of the same labeled
calendar strategy after moving a root from a late date to date zero.  A player
who Quits at the old calendar date can meet a different coalition after
compression.  Hence (1.2) is an equality of the prescribed joint point and
of scalar unrestricted caps, not a common arbitrary-intervention kernel.

### No consumer is added

The conclusion is the already open actual off-minimum paid port.  The theorem
does not turn its payoff gain into a Nash--Bellman chronology, a charged
return, or a uniform-equilibrium payoff.

## 7. Lean handoff simplification

For the zero-Never/zero-singleton branch, the shortest implementation path is:

1. formalize the closed-law product-root theorem;
2. formalize the strict positive-minimum root-then-Never semantic realization;
3. instantiate the finite-clock minimum-to-paid-port theorem directly.

The full-debt sure-core softening descent and the one-sure-owner response
handoff are not prerequisites for this contraction.  They remain useful only
when their stronger explicit product/sure-core intermediate data are needed.

The composite theorem can be exposed schematically as

```text
finFourMinimumJointLaw_zeroNever_zeroSingleton_exists_offMinimumPaidPort
```

with fields retaining:

* the exact incoming joint point \((z,\mu)\);
* the exact root-then-Never realization;
* the finite literal replacement ancestry;
* the off-minimum target;
* the complete pure-time/Never response of gain \(>D_*/4\); and
* the literal first-disagreement witness.

## 8. Checked declarations inspected

The existing Lean inputs used by the ordinary proofs include:

* `exists_terminalSemanticLawCarrier_lift` and
  `terminalSemanticLawCarrier_rewardMoment` in
  `TerminalSemanticResetIncidenceReturn.lean`;
* `minimumTerminalSemantic_singletonMargin` in
  `TerminalSemanticAuxiliaryNashBudget.lean`; and
* the pure-time extremality and first-disagreement declarations listed in
  `formalized/PURE_FINITE_CLOCK_MINIMUM_DEADLINE_RANK_TO_PAID_PORT.md`.

No declaration implementing the two new exported theorem families was found
under `UniformEquilibrium/` or `Research/` in the narrow symbol search.
