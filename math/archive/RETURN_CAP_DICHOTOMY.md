The decisive point is not the length of the counterexample checklist. Those conditions could still coexist because unrestricted best-response caps are nonsmooth: several individually harmless law changes can jointly activate a previously suboptimal stopping time and create **first-order cap leakage**. That is the only mechanism I can still make consistent with all the stated restrictions.

I need to correct one claim from my intermediate analysis. I suggested that balanced individual reset directions could be combined with only quadratic cap error. That is false for a supremum over deviations. A deviation initially behind by \(\lambda\) can gain \(0.6\lambda\) from each of two resets: neither reset changes the cap alone, but their combination raises it by \(0.2\lambda\). The reset-cube curvature machinery exists precisely because this interaction can be first order.

The strongest conclusion I can currently justify is therefore a sharper residual theorem, not yet the final contradiction.

# Cap-switching curvature reduction

Fix a positive-minimum Fin4 source and a flat charged circulation with active movers \(A\), \(|A|\leq4\). Let

$$
\sigma_n\to \sigma_*,
\qquad
\lambda_n\downarrow0,
\qquad
\frac{D(\sigma_n)-D_*}{\lambda_n}\longrightarrow0,
$$

and let \(\sigma_n^B\), \(B\subseteq A\), denote the source-matched reset cube obtained by applying the radial resets of the movers in \(B\).

Write

$$
d_n(B)=
\bigl(d_i(\sigma_n^B)\bigr)_{i<4}.
$$

The individual reset edges have normalized first-order columns \(v^m\), and the circulation relation gives

$$
\sum_{m\in A}\alpha_m v^m=0
$$

for positive weights \(\alpha_m\), while the paid diagonal term satisfies

$$
\sum_{m\in A}\alpha_m(-v^m_m)>0.
$$

The exact cube telescoping identities imply the following dichotomy.

## Theorem — paid return or persistent cap curvature

After passing to a subsequence, one of the following occurs.

### 1. Flat integration

The complete reset macro satisfies

$$
d_n(A)-d_n(\varnothing)=o(\lambda_n)
$$

coordinatewise, while its accumulated mover payment is at least

$$
c\lambda_n+o(\lambda_n)
$$

for some fixed \(c>0\).

Since the source excess is already \(o(\lambda_n)\), this gives a source-faithful positive charged near-return. It is exactly the nonlocal construction required here: all first-order debt is discharged before returning, rather than by restarting a charged local block. The existing near-return consumers then yield a uniform-equilibrium payoff.

### 2. Persistent square curvature

There exist fixed distinct movers \(p,q\), a fixed debt coordinate \(i\), fixed cube context \(B\subseteq A\setminus\{p,q\}\), and \(c>0\), such that

$$
\left|
 d_{n,i}(B\cup\{p,q\})
-d_{n,i}(B\cup\{p\})
-d_{n,i}(B\cup\{q\})
+d_{n,i}(B)
\right|
\ge c\lambda_n
$$

cofinally.

Prescribed payoffs and terminal laws are affine under these radial resets. Consequently this order-\(\lambda_n\) mixed difference must come from the best-response cap:

$$
\left|
 b_{n,i}(B\cup\{p,q\})
-b_{n,i}(B\cup\{p\})
-b_{n,i}(B\cup\{q\})
+b_{n,i}(B)
\right|
\ge c\lambda_n+o(\lambda_n).
$$

Thus every surviving counterexample must exhibit a **first-order two-direction switch of player \(i\)’s optimal stopping law at the law-tight minimum face**.

This is substantially narrower than generic “cap leakage.” The interaction cannot be diffuse among many coordinates, caused by ordinary payoff variation, or spread through an arbitrarily large reset pattern. With four players it localizes to one fixed two-dimensional square and one fixed cap coordinate.

The canonical ray itself cannot eliminate this case: along that ray every debt coordinate and the paid annotation are multiplied by the same survival product, so positive support and normalized debt remain exactly constant while absorption is summable.   The newly constructed law-tight saturation hull does, however, put the square at an attained compact minimum which is closed under exact cap–Nash prefixing and same-law debt-nonincreasing replacement.  At its minimum face, every exact cap–Nash prefix must have continuation mass one, hence every exact root at the displayed cap is all Continue.

So the conjecture is reduced to the following statement.

# The remaining lemma

**Minimum-face cap-switching lemma.**
At a positive law-tight minimum-face point whose exact cap root is uniquely all Continue, source-matched radial reset directions cannot have a nonzero normalized mixed cap difference:

$$
\frac{
 b_i(\sigma^{p,q}_\lambda)
-b_i(\sigma^{p}_\lambda)
-b_i(\sigma^{q}_\lambda)
+b_i(\sigma)
}{\lambda}
\longrightarrow0 .
$$

Equivalently, a persistent first-order kink must produce at least one of:

1. a non-all-Continue exact cap root;
2. a same-law carrier point of strictly lower total debt;
3. a chronological paid return already accepted by the existing consumer.

Any of the three contradicts the positive-minimum counterexample regime.

What remains delicate is the implication from a terminal best-response switch to a current exact cap root. A cap maximizer is a complete stopping-time deviation, not automatically a one-stage Quit action. Relative timing may escape to infinity, exactly as in the bubble phenomenon from the question. Therefore it would be incorrect to claim that root uniqueness by itself already proves the lemma. The checked sign theorem only says that a binding coordinate under unique all-Continue has another binding coordinate with positive collision gain; it does not identify the remote cap-switching deviation with a current root.

Still, this identifies a much smaller object than the previous inert residual:

$$
\boxed{
\text{A Fin4 counterexample must support a persistent first-order
two-reset kink of a pure-time best-response cap at an attained
law-tight minimum face.}
}
$$

Everything else is consumed:

* unbounded exact-block hazard gives a uniform payoff, so counterexamples have bounded capacity;
* positive maximal-root absorption gives strict regeneration, while zero absorption forces all exact cap roots to be all Continue;
* absence of square curvature integrates the balanced circulation into the required nonlocal paid return;
* the reset-cube localization leaves only one fixed \(2\)-face cap switch.

This also suggests the right rank. It is not debt, support, hazard, or absorption. It is the **active optimal-stopping face of the cap**, ordered by the earliest counterfactual stopping-time switch. A persistent mixed kink requires two competing pure stopping times for one player. If their first disagreement remains bounded, it produces a finite chronological root/paid-return witness. If it escapes to infinity, the source-attached atom and finite hazard-capacity bound must carry the disagreement into a suffix bubble. The remaining proof must show that such a bubble either regenerates at a strictly later finite atom rank or becomes invisible at order \(\lambda\), contradicting the assumed curvature lower bound.

That is the viable breakthrough route: replace the failed debt-support descent by a **finite chronological active-face descent**, with the two-reset curvature as its only successor certificate. I have not proved that final escape-to-infinity implication here, so I am not claiming the Fin4 conjecture solved. But the residual has been reduced from the eleven-part inert machine to one precise analytic-chronological phenomenon: first-order cap synergy between two source-matched resets.

The repository’s own task discipline requires exactly this separation between a mathematical reduction, a checked declaration, and a completed consumer; the runbook likewise forbids presenting an uncompiled or conditional bridge as a finished Lean theorem.  
