# Adversarial review of the overlapping first-quitter law

Reviewer: CODEX_SPINOZA

Reviewed file: `notes/KEPLER_CLOCKCONE__OVERLAPPING_FIRST_QUITTER_LAW.md`

Reviewed SHA256:
`262f9fe4ec20223a1bb120a0bd4af123b21e109860d9c4cb80384e735716439a`

## Verdicts

- **Core theorem 4.1: PASS.**  The one-step curved-region invariant and its
  arbitrary-clock limit are correct, including atoms, positive `Never` mass,
  and zero-survival histories.
- **Corollary 6.1, the `K_4` pair projections, boundary rigidity, and the
  conditional all-behavior terminal-gap consumer: PASS.**
- **Theorem 5.1 as currently proved: REVISE, narrowly.**  The listed equality
  families appear exhaustive, but the necessity proof uses a false blanket
  strict-convexity assertion in two degenerate cases.  A short explicit
  strict-loss split repairs it; no new equality family results.

This agrees independently with the mathematical issue found in the HAHN
review; I reconstructed the endpoint algebra and equality cases rather than
using that review as evidence.

## 1. Core invariant and clock limit

Writing (Q=1-q), (R=1-r), and
(c=(1-x)QR), the right endpoint of the convex function is

\[
 F(1)=\sqrt{R[xq+(1-x)Q]}+\sqrt{rxQ}.
\]

Two-coordinate Cauchy--Schwarz gives

\[
 F(1)^2\le (R+r)(xq+(1-x)Q+xQ)=xq+Q
 =1-(1-x)q\le1.
\]

The left endpoint is symmetric.  Replacing the future pair
((\alpha,\beta)) by ((u^2,(1-u)^2)) on the upper boundary is legitimate:
both output probabilities are coordinatewise nondecreasing.  Convexity then
bounds the interior by the two endpoints.  This proves the one-step lemma.

For clocks on `Nat union {Never}`, truncating the two desired finite events
at a common date gives the displayed recursion exactly.  The events increase
to the untruncated finite events, so continuity from below and continuity of
square root prove theorem 4.1.  No tightness, eventual absorption, or
stationarity assumption is hidden here.

As an exact small-support check, the one-date cases reduce to

\[
 a=xq(1-r),\qquad b=xr(1-q),
\]

and the claimed inequality follows from the same endpoint calculation.  The
positive equality family (x=1, q+r=1) gives
((a,b)=(q^2,r^2)), confirming the sharp constant and the tie/strict-event
orientation.

## 2. Narrow equality-proof defect and repair

The sentence claiming that (F) is strictly convex at every first
non-all-Continue row is false.  Two exact degeneracies are:

1. (x=0) and at least one of (q,r) is positive.  Both immediate constants
   vanish and (F(u)=\sqrt c) is constant, with (c<1).
2. (x>0) and (q=r=0).  Again (F(u)=\sqrt{1-x}<1) is constant.

Both cases give strict loss and hence cannot occur on a positive-coordinate
equality law.  Outside them, with (c>0) and a non-all-Continue row, at least
one square-root summand has a positive constant term, so the sum really is
strictly convex.  Equality then forces (u\in\{0,1\}).  The endpoint
equalities give respectively

\[
 (x,q,r)=(p,p,0)\quad\text{or}\quad(p,0,p).
\]

If (c=0) and both target events have positive mass, necessarily (x=1),
and equality in the one-date calculation is exactly (q+r=1).  Finally, an
independent pair of countable clocks equal almost surely must share one
deterministic atom, so the stated deterministic future date in the staggered
families is correct.  Thus the classification needs a proof repair, not a
statement change.

## 3. Coalition consequences

For incomparable overlapping coalitions (C,D), an exact (C)-event is
contained in (T_i=T_j<T_k) and an exact (D)-event in
(T_i=T_k<T_j), for (i\in C\cap D), (j\in C\setminus D), and
(k\in D\setminus C).  Monotonicity therefore gives Corollary 6.1 with the
correct inequality direction.  Together with the prior disjoint-edge law,
this accounts for all twelve adjacent and three disjoint pairs of `K_4`
edges.

The boundary claim `sum_e q_e = 1` is also correct.  At the earliest row with
positive absorption, a product Bernoulli law having no supported nonempty
coalition except pairs must have exactly two hazards equal to one and the
other two equal to zero.  That row absorbs surely in one deterministic pair,
so later rows contribute nothing.

## 4. Conditional terminal-gap consumer

The affine forcing assumptions imply

\[
 \sqrt{[\alpha_e-L_eE]_+}+\sqrt{[\alpha_f-L_fE]_+}
 \le \sqrt{q_e}+\sqrt{q_f}\le1.
\]

The function on the left is continuous and nonincreasing.  When its value at
zero exceeds one, its first crossing is positive; consistency makes the
crossing set nonempty.  Hence every actual behavioral profile has maximum
complete debt at least that crossing.  The cap is the full unrestricted
behavioral cap, and pure-time extremality then supplies a finite-time-or-Never
deviation within half the gap.  The use of the checked terminal-gap
equivalence is therefore correctly scoped.

This is only a consumer of the affine pair-mass lower bounds.  Nothing in the
clock inequality produces those bounds or a counterexample table, and the
note says so explicitly.

## Requested repair

Replace the false blanket strict-convexity sentence in Theorem 5.1 by the two
degenerate strict-loss cases above, then apply strict convexity on the
remaining cases.  No repair is needed to Theorem 4.1 or Sections 6--8.

## Exact-hash delta review

Revised file SHA256:
`9905edf64caed317da33a9ffbd9f0675590a557f1a831af3e7465f72fdcb997a`

**PASS.**  The revised necessity proof now separates exactly the two
degenerate configurations identified above.  When both immediate radicands
vanish, a non-all-Continue row has (c<1) and hence the constant value
(F=\sqrt c<1); the sole equality degeneracy is the removable
all-Continue row.  In the remaining (c>0) cases at least one summand has
strictly positive second derivative, so the endpoint reduction and the
existing equality classification follow.  The repair introduces no new
equality family or stronger downstream claim.  The current file has no
control bytes.  My core and add-on verdicts are therefore all **PASS** at
this exact revised hash.
