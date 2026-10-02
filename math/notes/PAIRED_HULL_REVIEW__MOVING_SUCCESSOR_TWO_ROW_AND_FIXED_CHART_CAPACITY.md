# Moving-successor two-row test and fixed-chart capacity

Identity: PAIRED_HULL_REVIEW  
Date: 2026-08-31  
Status: ordinary mathematics from the named checked one-row identities; no
Fin4 source producer or uniform-equilibrium theorem is claimed

## 1. Question

The approximate-forward-packet route asks for product roots \(q_t\) and
payoffs \(v_t\) with

\[
 v_{t+1}=T_{q_t}(v_t)
\]

literally, one common support-Nash tolerance \(\delta\), one fixed punishment
floor, and arbitrarily large accumulated absorption charge. A local tangent
row may have absorption of order \(t\) but Bellman and endpoint errors of
order \(t^2\). Does that row renew even for two consecutive literal
successors?

The answer is:

1. **yes at the coarse fixed tolerance:** with an interior punishment-floor
   margin, the same root gives two literal successor rows at error \(O(t)\);
2. **no at the cheap tangent scale:** unless the normalized Bellman motion
   vanishes, the second row has support error \(\Omega(t)\), not \(O(t^2)\);
3. a fixed root chart can therefore accumulate only \(O(\delta)\) charge at
   tolerance \(\delta\) before it must switch charts.

Thus the first missing composition is not the second Bellman equality. It is
renewal of the **quadratic error-to-charge ratio** at the moving successor.

## 2. Exact fixed-root formulas

Fix a product root \(q\). Write

\[
 c=\prod_j(1-q_j),
 \qquad a=1-c,
 \qquad h_i=\prod_{j\ne i}(1-q_j).
\]

Here \(a\) is root absorption and \(h_i\) is the probability that all
opponents of \(i\) Continue. The one-row Bellman map is affine:

\[
 T_q(v)_i=A_i(q)+c\,v_i.
\tag{2.1}
\]

Let

\[
 v_{k+1}=T_q(v_k),
 \qquad d=v_1-v_0.
\]

Then

\[
 v_{k+1}-v_k=c^k d,
 \qquad
 v_k-v_0=\left(\sum_{\ell<k}c^\ell\right)d.
\tag{2.2}
\]

When \(a>0\), define the normalized Bellman motion

\[
 w={d\over a}.
\]

Equation (2.2) becomes

\[
 v_k-v_0=(1-c^k)w.
\tag{2.3}
\]

For player \(i\), let \(E_i(v,q)\) be Quit payoff minus Continue payoff.
The tail enters only through the Continue endpoint, so

\[
 E_i(v',q)-E_i(v,q)=-h_i(v'_i-v_i).
\tag{2.4}
\]

Consequently

\[
 E_i(v_k,q)=E_i(v_0,q)-h_i(1-c^k)w_i.
\tag{2.5}
\]

These identities are raw one-stage identities. They use no Nash or minimum
hypothesis.

## 3. Two-row transfer

Suppose \(q\) is support-\(\varepsilon_0\) Nash against \(v_0\). Tail
stability gives

\[
 q\text{ is support-}
 \bigl(\varepsilon_0+\lVert v_k-v_0\rVert_\infty\bigr)
 \text{ Nash against }v_k.
\tag{3.1}
\]

In particular, the two literal rows

\[
 v_0\xrightarrow{q}v_1\xrightarrow{q}v_2
\]

satisfy exact Bellman successor matching, and both are support-\(\delta\)
Nash whenever

\[
 \varepsilon_0+\lVert d\rVert_\infty\leq\delta.
\tag{3.2}
\]

If \(v_0\) is uniformly inside the punishment-floor carrier and
\(v_1,v_2\) are sufficiently close to it, the rationality field also holds.
At a punishment-floor boundary, a separate one-sided motion condition is
necessary; exact successor matching alone does not preserve the floor.

Therefore a local row does not fail merely because the successor moves. Two
rows exist at a coarse tolerance after choosing the scale small enough.

## 4. Loss of quadratic cheapness on the second row

Assume that player \(i\)'s marginal in \(q\) is interior, so both Quit and
Continue are in support. Any support-Nash tolerance for \(q\) against
\(v_k\) is at least

\[
 |E_i(v_k,q)|.
\]

If the first row has tolerance \(\varepsilon_0\), then

\[
 |E_i(v_k,q)|
 \geq h_i(1-c^k)|w_i|-\varepsilon_0.
\tag{4.1}
\]

At the literal second row, \(k=1\), this reads

\[
 \boxed{
 \text{second-row support error}
 \geq h_i|d_i|-\varepsilon_0.}
\tag{4.2}
\]

Now specialize to a tangent row with a small parameter \(t\):

\[
 a_t=s\,t+O(t^2),
 \qquad
 \varepsilon_{0,t}=O(t^2),
 \qquad
 d_t=t z+O(t^2),
\tag{4.3}
\]

where \(s>0\). If \(z_i\ne0\) on one interior active coordinate, then

\[
 h_{i,t}|d_{t,i}|-\varepsilon_{0,t}
 =|z_i|t+O(t^2).
\tag{4.4}
\]

Thus the first row is \(O(t^2)\)-support Nash, but verbatim reuse at its
literal successor is only \(O(t)\)-support Nash. This is the first exact
failure of the naive renewable construction.

The conclusion is stronger than “the tangent extractor is available only at
one limit.” Even if the first root is retained literally and the Bellman
successor is defined exactly, its cheap error-to-charge ratio is destroyed
after one step by the nonzero normalized payoff motion.

## 5. Exact fixed-chart charge bound

Suppose the same root is support-\(\delta\) Nash at every tail
\(v_0,\ldots,v_k\), and \(i\) remains an interior coordinate. Combining
(4.1) with this assumption gives

\[
 h_i(1-c^k)|w_i|\leq\delta+\varepsilon_0.
\tag{5.1}
\]

If

\[
 0<{\delta+\varepsilon_0\over h_i|w_i|}<1,
\]

then, because \(c=1-a\leq e^{-a}\), the raw charge \(ka\) obeys

\[
 \boxed{
 ka
 \leq
 -\log\left(
 1-{\delta+\varepsilon_0\over h_i|w_i|}
 \right).}
\tag{5.2}
\]

For a nondegenerate tangent family, \(h_i\to1\),
\(\varepsilon_0=o(\delta)\), and \(|w_i|\) stays bounded below. The
right-hand side is \(O(\delta)\). Hence a fixed chart cannot accumulate even
order-one charge as \(\delta\downarrow0\), regardless of how small the row
hazard is chosen.

If \(w\to0\) instead, the row has vanishing normalized motion. Provided the
checked rationality/floor hypotheses remain valid, repeating it approaches
its absorbing stationary payoff without leaving the small support/floor
neighborhood. This is precisely the regime of the checked normalized-motion
stationary compiler and of the arbitrary-charge forward packet consumer. It
is not a new counterexample residual.

## 6. What a renewable producer must do

An arbitrarily charged packet must therefore change root charts. With

\[
 v_{m+1}-v_m=a_m w_m,
\]

compact recurrence at large total charge requires weighted cancellation of
the normalized motions \(w_m\). At first order this is a circulation
condition, not a one-row Nashification condition.

The checked FaceCirculationCertificate is a complete special case: its
phase-varying roots and values arrange exactly this cancellation and compile
to arbitrary-charge packets. The Fin4 hard source does not currently produce
such a certificate.

The required moving-source theorem is now precise:

> at the literal successor of each cheap row, re-extract another cheap row
> whose active face, punishment-floor sign, and normalized motion fit a
> finite circulation, with one support tolerance independent of packet
> length.

Selecting unrelated tangent packets at nearby compact points is insufficient;
their first-order source displacements must satisfy the literal successor
equations.

## 7. Exact small regression

The two-player family already recorded in
notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md shows that moving-source
matching is possible without giving arbitrary capacity. Let \(d<0<c\) and

\[
 r(\{0\})=(0,d),\qquad
 r(\{1\})=(d,0),\qquad
 r(\{0,1\})=(c,c).
\]

At equal hazards \(t\), the tail and current values

\[
 y_i^t={t(c-d)\over1-t},
 \qquad
 x_i^t=tc
\]

form an exact Nash--Bellman edge. In the genuine forward Bellman orientation,
the recursion

\[
 t_{n+1}={t_nc\over c-d+t_nc}
\]

gives \(y^{t_{n+1}}=x^{t_n}\), so finite segments can be ordered as literal
successive edges. Because \(d<0\), one has
\(t_{n+1}/t_n\to c/(c-d)<1\); the compatible hazards
decay geometrically in the infinite small-scale direction, and their total
charge is finite.

This is not a counterexample—the table is in a solved boundary regime. It
is an exact regression against the inference

\[
 \text{moving-source re-extraction}
 \Longrightarrow
 \text{unbounded approximate capacity}.
\]

One also needs non-summable projective scale or a returned circulation.

## 8. Relation to the Fin4 counterexample branch

Under a terminal exploitability gap, accurate finite forward packets in one
fixed compact carrier have an explicit finite charge cap; see
notes/CODEX_ADVERSARY__QUANTITATIVE_SUPPORT_PACKET_CAPACITY.md. Thus a
hypothetical counterexample must force one of the following at every attempt
to continue a cheap row:

1. linear support-error growth as in (4.2);
2. violation of a punishment-floor face;
3. summable projective hazard decay as in Section 7; or
4. failure to select the next tangent chart on the literal successor.

This list is the concrete two-row boundary requested by
questions/FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md. It does
not consume bounded capacity. It explains why a local \(O(a^2)\) row is not
yet a renewable forward packet.

## 9. Falsifiable next test

Take one actual full-debt common-prefix fork and the first cheap tangent row
obtained after its cap displacement. At the literal successor, compute

\[
 w={T_q(v)-v\over\operatorname{Abs}(q)}
\]

and the active endpoint face. Then prove one of:

1. a second chart exists whose normalized motion cancels a fixed positive
   fraction of \(w\) while preserving the floor and support error \(O(a^2)\);
2. the projective absorption ratio is bounded away from a summable decay;
3. failure of both produces a finite controller--tester barrier.

A second row with merely \(O(a)\) error is already explained by (4.2) and is
not sufficient.

## Sources inspected

- UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean;
- UniformEquilibrium/Quitting/Root/TailStability.lean;
- UniformEquilibrium/Quitting/Cycles/OwnShiftCycleExactification.lean;
- UniformEquilibrium/Quitting/Boundary/Analytic/SeamPriceResidual.lean;
- UniformEquilibrium/Quitting/Boundary/Repair/SupportEnlargementAlternative.lean;
- UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/NormalizedMotionStationaryPrefixProducer.lean;
- notes/CODEX_ROOT__APPROXIMATE_FORWARD_PACKET_BYPASSES_EXACT_CONNECTOR.md;
- notes/CODEX_ADVERSARY__FIN4_FORCED_PAIR_FORWARD_CAPACITY_GATE.md;
- notes/CODEX_ADVERSARY__QUANTITATIVE_SUPPORT_PACKET_CAPACITY.md; and
- the moving-source tangent analysis in
  notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md.
