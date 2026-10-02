# Independent review of `RETAINED_LAW_PREMIUM_RETURN_DESCENT_PLATEAU`

**Reviewer:** `JAMES`  
**Date:** 2026-08-26  
**Source reviewed:**
`notes/CHATGPT_EXTERNAL__RETAINED_LAW_PREMIUM_RETURN_DESCENT_PLATEAU.md`
and `../RETAINED_PREMIUM.md`  

## Summary verdicts

- **Candidate A — REVISE interface, then PASS.**  The compact law-separation
  lemma is correct if the fixed point is supplied together with its genuine
  minimum-on-the-fixed-law-reset-face proof.  Neither the current
  `QuittingFixedLawResetDispatch` nor the public conclusion of
  `exists_fixedLaw_resetFace_minimizer` stores that universal minimality,
  although the latter theorem's proof constructs it internally.
- **Candidate B — PASS conditionally, with metric and source-side exactness
  stated.**  In the finite-law sup metric, a literal prefix changes its suffix
  law by at most `1-survival`, and `1-survival` is bounded by cumulative root
  absorption.  The cap-Nash exactness is required only on the `x_n` source
  side; the same roots may prefix the comparison side merely to transport the
  rectangle atom.
- **Candidate C — PASS.**  The outer-sequence quantifier order is sound, the
  fixed charge floor `a/2` is valid, and every returned finite path lies in
  one source's exact punishment-floor cap chronology.  This is a clean
  Research wrapper around the checked fixed-source theorem.
- **Final reduction — REVISE.**  Conditional on port limits entering a
  separated lower region, the return-versus-uniform-debt-drop dichotomy is
  valid.  The complementary no-entrance region is exact.  Calling that whole
  complement a “unique-all-Continue/delayed-support-entry plateau” is not yet
  an exhaustive theorem.  A semantic `SummablePort` also does not store its
  limiting terminal law; a law-cluster extraction or a law-enriched port must
  be inserted before applying Candidate A.

No part should be exported in its current form.

## 1. Checked premium and the missing minimum field

For the strict bridge branch, put

\[
\delta=D(\texttt{bridge.fixed})-D(\texttt{bridge.global.1})>0.
\]

`QuittingStoppingLawRectangleMinimizerBridge.eventually_literal_lawPremium`
in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/RectangleResetFaceMinimizer.lean`
does prove, on the same literal double-endpoint sequence and with its signed
atom bound retained,

\[
\delta/2<D(x_n)-D(\texttt{bridge.global.1})
\]

eventually.  This part is already checked and correctly scoped as a static
same-law premium rather than chronological charge.

The noted interface defect is real.  `QuittingFixedLawResetDispatch` stores:

- joint semantic/law membership;
- zero observer debt;
- source and target total-debt comparisons;
- transfer and supported-toggle data; and
- the dynamic-exit/all-Continue alternative.

It does **not** store

\[
D(\texttt{fixed})\le D(z.1)
\]

for every joint carrier point `z` having observer debt zero and law `mu`.
The proof of `exists_fixedLaw_resetFace_minimizer` uses
`hcompact.exists_isMinOn` and obtains exactly this fact as `hreturnedMin`, but
the theorem's public existential conclusion also drops that universal field.
Thus it cannot be recovered by projecting `bridge.fixed_dispatch` or by
invoking the current theorem statement after the fact.

The narrow repair is to return, or add to a strengthened bridge, the field

```text
fixed_minimal : forall z in quittingTerminalSemanticLawCarrier reward,
  debt z.1 observer = 0 -> z.2 = mu -> D fixed <= D z.1
```

(equivalently the corresponding `IsMinOn`).  The existing compact minimizer
proof can be refactored to supply it without new mathematics.

## 2. Candidate A: compact strict-law separation

Assume the strengthened `fixed_minimal` field.  Then Candidate A is correct.
If no positive `epsilon0,rho` existed, choose joint carrier points `z_k` with

\[
d_o(z_k.1)\le1/k,
\quad
D(z_k.1)\le D(\texttt{global.1})+\delta/2,
\quad
\operatorname{dist}(z_k.2,\mu)<1/k.
\]

Compactness of `quittingTerminalSemanticLawCarrier`, followed by continuity
of debt, total debt, and law projection, gives a limit `z` with

\[
d_o(z.1)=0,
\qquad z.2=\mu,
\qquad D(z.1)\le D(\texttt{global.1})+\delta/2.
\]

Nonnegativity of carrier debt is used to turn the limiting inequality
`d_o<=0` into equality.  Fixed-law minimality then gives

\[
D(\texttt{global.1})+\delta=D(\texttt{fixed})
\le D(z.1)
\le D(\texttt{global.1})+\delta/2,
\]

a contradiction.  Hence the positive law-distance barrier exists.

The same proof works with any threshold
`D(global.1)+theta*delta` for fixed `theta<1`.  This slack is useful when a
finite prefix only approximates a port limit lying in the inner half.

**Candidate A verdict:** mathematically PASS after the mandatory structure
repair; not derivable from the current public bridge.

## 3. Candidate B: prefix-law displacement and cumulative charge

Let `m` be a suffix terminal law and let a finite literal prefix have suffix
survival `s`.  Repeated use of
`quittingTerminalOutcomeLawPrefix` gives

\[
m_{\mathrm{prefix}}=\nu+s\,m,
\]

where `nu` is the fresh prefix-absorption law and its total mass is `1-s`.
For each terminal outcome `omega`, both
`nu(omega)` and `(1-s)m(omega)` lie in `[0,1-s]`, so

\[
|m_{\mathrm{prefix}}(\omega)-m(\omega)|
=|\nu(\omega)-(1-s)m(\omega)|\le1-s.                \tag{3.1}
\]

With the current finite function-space sup metric, `dist_pi_le_iff` turns
(3.1) into

\[
\operatorname{dist}(m_{\mathrm{prefix}},m)\le1-s.  \tag{3.2}
\]

For an `l1`/total-variation normalization the displayed numerical constant
would change (the elementary `l1` bound is `2(1-s)`), so a formal theorem
must name the metric.  The note's proposed finite-simplex/sup metric supports
the constant one.

If stage absorption is `q_t`, then

\[
s_h=\prod_{t<h}(1-q_t),
\qquad
1-s_h\le\sum_{t<h}q_t.                              \tag{3.3}
\]

Suppose `law(x_n)->mu`, the observer debt of `x_n` tends to zero, and a
source-side exact cap-Nash prefix enters the separated region.  Exact cap
prefix transport gives

\[
D(\widehat x_{n,h})=s_hD(x_n),
\qquad
d_o(\widehat x_{n,h})=s_hd_o(x_n).                  \tag{3.4}
\]

For late `n`, Candidate A yields
`rho <= dist(law(hat x),mu)`, while the triangle inequality, (3.2), and
`dist(law(x_n),mu)<rho/2` give

\[
\rho/2\le1-s_h\le\sum_{t<h}q_t.                    \tag{3.5}
\]

This proves the claimed coercivity.

Only the source `x_n` stack must be exact cap-Nash for (3.4).  Prefixing the
same literal roots to the comparison profile `y_n` scales its terminal law
and the signed rectangle atom by the same `s_h`, but those roots are not
automatically cap-Nash at `y_n`'s envelope.  The statement should avoid
claiming simultaneous exactness on both sides.

If `D_*>0`, global minimality and (3.4) imply

\[
D_*\le s_hD(x_n).
\]

The `D(x_n)` are uniformly bounded, so `s_h` has a uniform positive lower
bound and every already-quantified rectangle atom retains the corresponding
fixed fraction.  Preserve the exact normalization from
`eventually_literal_lawPremium`: its checked atom inequality contains the
factor `Fintype.card (QuittingTerminalOutcome iota)`.  A raw atom lower bound
must not silently drop that factor.

**Candidate B verdict:** PASS as a conditional actual-entrance theorem, after
the metric, triangle term, and source-side exactness qualifications above.
It does not produce an entrance.

## 4. Candidate C: outer-sequence cap return

Candidate C is valid with the stated quantifier order.  Let actual paid cap
sources `source n`, summable ports `port n`, and `a>0` satisfy

\[
a\le A_n:=\texttt{totalAbsorption}(\texttt{source }n)
\]

eventually and

\[
c_n:=\texttt{capDisplacement}(\texttt{source }n,\texttt{port }n)
\longrightarrow0.
\]

For each requested endpoint error `eta>0`, choose one outer index `n` where
both `A_n>=a` and `c_n<eta/2`.  For this fixed source, the finite partial
absorption sums tend to `A_n`, while the cap-orbit values tend to the port cap
limit.  Hence one finite depth `h` satisfies simultaneously

\[
\sum_{t<h}q_{n,t}>a/2,
\qquad
\operatorname{dist}(V_{n,h},V_{n,\infty})<\eta/2.
\]

The triangle inequality and the definition of `capDisplacement` give

\[
\operatorname{dist}(V_{n,h},V_{n,0})<\eta.
\]

The finite orbit segment is exactly the checked punishment-floor admissible
path.  Therefore

```text
chargeFloor := a / 2
```

constructs a
`QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily`.  The outer index
is allowed to depend on `eta`; the family definition requires only one path
per tolerance.  Within that path the source index is fixed, so there is no
cross-source splice.

This is genuinely an outer-sequence wrapper rather than the already checked
fixed-source theorem
`nonempty_cumulativeNearReturnFamily_of_totalAbsorption_pos_of_capDisplacement_zero`
in `PaidCapPortExactTrichotomy.lean`.  Its proof reuses the same convergence
facts and adds exactly one outer-index selection and one triangle inequality.

**Candidate C verdict:** PASS; suitable for a narrow Research declaration.
It is a conditional consumer, not a producer of eventually positive
absorption.

## 5. Applying separation to semantic port limits

A current `SummablePort` stores a semantic port and shifted rows, not a
terminal-law limit.  Thus a statement such as “the limiting law of `L_n` is
away from `mu`” is not directly typed.

There are two valid repairs.

1. Enrich the port with a jointly convergent terminal-law subsequence; or
2. for each fixed `n`, use compactness of the finite law simplex to extract a
   law cluster `nu_n` along a subsequence of the literal cap-prefix profiles.

In the second route, semantic convergence identifies the joint cluster as
`(L_n,nu_n)` in the joint carrier.  Exact coordinate debt scaling gives

\[
d_o(L_n)\le d_o(x_n),
\]

and law-prefix displacement passes to the limit as

\[
\operatorname{dist}(\nu_n,\operatorname{law}(x_n))\le A_n.
\]

If

\[
D(L_n)\le D(\texttt{global.1})+\delta/2,
\]

then Candidate A, `d_o(x_n)->0`, and
`law(x_n)->mu` yield

\[
\liminf_n A_n>0.                                    \tag{5.1}
\]

This is the correct ordinary-mathematics bridge from semantic ports to the
law barrier.  It requires an explicit law-cluster extraction; it is not a
field projection from the current `SummablePort`.

## 6. Exact checked/conditional boundary of the rectangle reduction

The following components are already checked:

- the retained literal premium and atom bound;
- compactness of the joint semantic/law carrier and exact affine law prefix;
- cap-Nash debt scaling along each literal cap-prefix chronology;
- the fixed-source exact cap-port trichotomy;
- quantitative debt descent from positive cap displacement; and
- the fixed-source zero-displacement cumulative-return consumer.

The following components are new but mathematically valid ordinary
mathematics:

- Candidate A after retaining `fixed_minimal`;
- Candidate B in the specified law metric;
- Candidate C; and
- the law-cluster passage in Section 5 above.

Now assume a subsequence of actual rectangle endpoint ports satisfies the
lower-region condition in Section 5.  Equation (5.1) supplies a uniform
absorption floor.  For the nonnegative cap displacements, pass to a further
subsequence on which either:

1. displacement tends to zero, in which case Candidate C gives cumulative
   near-returns and the checked uniform-payoff consumer; or
2. displacement is bounded below by `kappa>0`, in which case the checked
   quantitative trichotomy gives

   \[
   D_*\,{\kappa\over2M}
   \le D(x_n)-D(L_n).
   \]

This **return-or-uniform-same-source-debt-drop** conclusion is correct.  The
debt-drop arm still lacks regeneration or a finite well-founded rank.

If no such lower-region subsequence exists, the exact conclusion is only a
causal **no-lower-entrance/no-lower-port-limit residual**.  It does not follow
that every finite selected root is all-Continue.  Positive-absorption roots
may exist while producing insufficient displacement to cross the chosen
debt threshold, and an outer sequence may have small positive absorption at
every index without any literal zero-absorption source.

The checked `InertStall` conclusion applies when one fixed source has exactly
zero total absorption.  It cannot be promoted automatically to an
asymptotically zero outer sequence.  Likewise, the maximal-absorption selector
and the assertion that positive support can appear only discontinuously at
an unattained limit are not fields or theorems in the current bridge/port
interface.

Therefore the phrase

```text
unique-all-Continue / delayed-support-entry retained-suffix plateau
```

is a useful conjectural label for the desired refinement, but not the proved
third arm of an exhaustive trichotomy.  The current rigorous reduction is:

\[
\boxed{
\begin{array}{c}
\text{lower-region port subsequence}
\Rightarrow
  \text{cumulative return/UE or uniform same-source debt drop};\\
\text{otherwise: no lower-region port subsequence.}
\end{array}}
\]

## 7. Recommendation

Keep the packet internal.  Formalize Candidate C independently if useful.
For Candidates A/B, first expose fixed-law `IsMinOn` and either fix the law
metric explicitly or state the coordinatewise law estimate.  Do not export
the final plateau trichotomy until the no-entrance complement is genuinely
converted into literal all-Continue/inert data or a well-founded regenerated
source.
