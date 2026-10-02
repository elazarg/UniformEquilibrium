# Positive-minimum canonical pure rays: uniform paid scale and the finite all-stall residual

Author: `PAIR_WALL_REVIEW`

## Status

Complete ordinary-mathematics finite reduction using the positive global
minimum essentially.  It gives two genuine exits and a quantitatively uniform
finite residual.  The residual still has no known chronological consumer, so
this note does not answer the concentrated-singleton question and is not an
export candidate by itself.

The main new quantitative observation is that normalization by the canonical
ray exactly cancels the possibly large pure-coalition wall: every canonical
ray retains a paid best toggle of limiting gain at least `D_*/4` on Fin4.

## 1. Canonical data for a pure nonsingleton coalition

Assume a quitting table on `Fin 4` has positive global terminal-semantic debt
minimum

\[
 D_*>0.
\]

For each nonsingleton coalition \(C\), define its toggle debts and wall

\[
 h_i(C)=\bigl[r_i(C\mathbin\triangle\{i\})-r_i(C)\bigr]_+,
 \qquad
 H_C=\sum_i h_i(C).                              \tag{1}
\]

The actual pure-\(C\) profile has unrestricted behavioral debt vector
\(h(C)\), hence

\[
 H_C\ge D_*>0.                                   \tag{2}
\]

Run the canonical maximal-absorption exact cap-prefix construction outward
from this pure profile.  Let \(\alpha_{C,k}\) be the joint Continue product
through its first \(k\) roots.  Exact cap-Nash scaling gives

\[
 d_i(C,k)=\alpha_{C,k}h_i(C),
 \qquad
 D(C,k)=\alpha_{C,k}H_C.                         \tag{3}
\]

The sequence decreases and is bounded below by \(D_*\).  Define

\[
 L_C=\lim_kD(C,k),
 \qquad
 \alpha_C=\lim_k\alpha_{C,k}={L_C\over H_C}.     \tag{4}
\]

Then

\[
 D_*\le L_C\le H_C,
 \qquad
 {D_*\over H_C}\le\alpha_C\le1.                \tag{5}
\]

The shifted pure \(C\)-row has stage mass \(\alpha_{C,k}\), so its limiting
mass is \(\alpha_C>0\).

## 2. Positive minimum produces a uniform paid toggle

Choose \(p(C)\) maximizing \(h_i(C)\).  Since there are four players,

\[
 h_{p(C)}(C)\ge {H_C\over4}.                     \tag{6}
\]

At depth \(k\), change the shifted pure row to the best endpoint of
\(p(C)\).  This actual one-date behavioral update has gain

\[
 g_{C,k}=\alpha_{C,k}h_{p(C)}(C),                \tag{7}
\]

and subtracts exactly that amount from the mover's unrestricted whole-profile
debt.  Passing to the limit and using (5)--(6),

\[
 \boxed{
 \lim_k g_{C,k}
 = {L_C\over H_C}h_{p(C)}(C)
 \ge {L_C\over4}
 \ge {D_*\over4}.}                              \tag{8}
\]

Thus no canonical pure-coalition ray can make its best horizontal endpoint
gain evaporate.  The scale is table-independent after normalization by the
positive global minimum.

Because the set of nonsingleton Fin4 coalitions is finite, with

\[
 H_{\max}=\max_C H_C,
\]

all canonical rays also retain the common marked-mass floor

\[
 \alpha_C\ge {D_*\over H_{\max}}>0.              \tag{9}
\]

## 3. The two genuine exits

### Pure-wall equality

If \(H_C=D_*\), the pure-\(C\) profile is itself an actual point of the global
minimum fibre.  Its debt support is exactly

\[
 A_C=\{i:h_i(C)>0\}.                             \tag{10}
\]

For a forced pair \(C=\{j,o\}\) obtained by the strict join
\(\{j\}\to\{j,o\}\), the reverse toggle of \(o\) is strictly negative, so
\(h_o(C)=0\) and \(|A_C|\le3\).  From a maximum-support rank-four minimum
source this feeds the checked minimum-fibre support re-extraction and gives a
strict support descent.

### Ray return

If \(L_C=D_*\), the actual finite maximal-prefix profiles have whole-source
debt tending to \(D_*\), retain the pure marked coalition with limiting mass
\(D_*/H_C>0\), and retain the gain floor (8).  Attaching the selected
minimum-approaching literal tail behind the counterfactual all-Continue
outcome does not change the pure nonsingleton semantic source.  This is the
whole-source-return field missing from the collision compiler.

For the original forced pair, the existing owner-zero and minimum-tail fields
are retained verbatim.  For a later toggled nonsingleton \(C'\), the preceding
mover has zero reverse-toggle debt at the pure \(C'\)-row and can serve as the
zero marked coordinate.  Thus a ray-return vertex supplies the same checked
three-role transfer/limit-chord entrance after the standard source attachment.

## 4. Finite comparison map and its exact residual

On every nonsingleton \(C\), let

\[
 F(C)=C\mathbin\triangle\{p(C)\}.                \tag{11}
\]

If \(F(C)\) is a singleton, the finite nonsingleton comparison stops at the
maintained concentrated-singleton node.  If it is nonsingleton, independently
compute the canonical maximal ray of \(F(C)\) and continue.

This is a finite **table-level comparison**, not yet a literal renewal
operation.  The distinction matters.  The horizontal update at depth \(k\)
retains the whole old canonical prefix.  The standalone canonical ray of
\(F(C)\), by contrast, starts again from the pure \(F(C)\)-row and selects a
new prefix.  Passing from the first actual profile to the second discards one
prefix and inserts another; no unilateral deviation or exact Bellman edge
performs that replacement.

At the successor vertex, the preceding mover has zero pure debt:

\[
 h_{p(C)}(F(C))=0,                               \tag{12}
\]

because (11) reverses a strict improving membership edge.  Exact ray scaling
keeps that coordinate zero throughout the canonical successor ray.

Since there are only eleven nonsingleton coalitions, the process either
reaches a singleton or repeats a nonsingleton coalition.  If any visited
vertex has \(H_C=D_*\) or \(L_C=D_*\), one of Section 3's genuine exits
occurs.  Otherwise finiteness yields fixed positive gaps

\[
 \kappa_H=min_{C\text{ visited}}(H_C-D_*)>0,
 \qquad
 \kappa_L=min_{C\text{ visited}}(L_C-D_*)>0.    \tag{13}
\]

Any repeated segment therefore carries the following uniform passport:

\[
 \boxed{
 \begin{array}{l}
 H_C\ge D_*+\kappa_H,\qquad
 L_C\ge D_*+\kappa_L,\\
 \text{marked mass}\ge D_*/H_{\max},\\
 \text{paid horizontal gain}\ge D_*/4,\\
 d_{p(C)}\text{ vanishes on the entire successor ray.}
 \end{array}}                                    \tag{14}
\]

This is strictly stronger than an unquantified off-minimum stall tag.

### Exact cap-leakage and seam account

Let \(W_{C,k}\) be the common root word above the pure marked row at depth
\(k\).  Write \(J_{C,k}\) for its joint Continue reach and \(R_{C,k,i}\) for
its opponents-only Continue reach for player \(i\).  If \(b(C)\) is the
all-behavior cap vector of the pure \(C\)-profile, then prefixing acts on each
cap coordinate by an increasing piecewise-affine scalar map
\(\Phi_{C,k,i}\), and

\[
 \begin{aligned}
 U_i(W_{C,k}*F(C))-U_i(W_{C,k}*C)
   &=J_{C,k}\bigl(r_i(F(C))-r_i(C)\bigr),\\
 B_i(W_{C,k}*F(C))-B_i(W_{C,k}*C)
   &=\Phi_{C,k,i}(b_i(F(C)))-\Phi_{C,k,i}(b_i(C)),
 \end{aligned}                                  \tag{15}
\]

with

\[
 |\Phi_{C,k,i}(x)-\Phi_{C,k,i}(y)|
 \le R_{C,k,i}|x-y|.                            \tag{16}
\]

Thus, for rewards bounded by \(M\), the cross-coordinate debt leakage obeys

\[
 |\Delta d_i|
 \le R_{C,k,i}|b_i(F(C))-b_i(C)|
      +J_{C,k}|r_i(F(C))-r_i(C)|
 \le4M R_{C,k,i}.                               \tag{17}
\]

For the mover \(p(C)\), the two profiles differ only in that player's own
prescribed strategy, so its whole cap is exactly unchanged and
\(\Delta d_{p(C)}=-g_{C,k}\).  For a spectator, however, (17) is the sharp
available prefix estimate.  The ratio \(R_{C,k,i}/J_{C,k}\) is the reciprocal
of that spectator's own Continue reach and has no source-independent bound.
Consequently spectator cap leakage need not be small relative to the paid
gain.

At a recurrent table-level edge choose a subsequence on which the updated
semantic pairs converge, and write the resulting debt vectors as

\[
 v_C=\alpha_Ch(C),\qquad
 y_C=\lim_{k\text{ in the chosen subsequence}}
      d(W_{C,k}*F(C)).
\]

The horizontal part has the exact form

\[
 y_C-v_C=-g_Ce_{p(C)}+\ell_C,qquad
 (\ell_C)_{p(C)}=0.                             \tag{18}
\]

The restart from the inherited updated profile to the separately canonical
successor introduces the seam

\[
 s_C:=v_{F(C)}-y_C.                             \tag{19}
\]

Even the mover coordinate only gives
\((v_{F(C)})_{p(C)}=(y_C)_{p(C)}=0\); the other three coordinates of
\(s_C\) have no sign.  On a simple comparison cycle, summing gives only

\[
 0=\sum_C\bigl(-g_Ce_{p(C)}+\ell_C+s_C\bigr).  \tag{20}
\]

This is an algebraic tautology, not a signed debt monodromy.  The seams are
not common-response squares, prescribed-payoff edges, or cap-Nash prefix
charges.  Dropping them is exactly the invalid inference that the canonical
ray endpoint of \(F(C)\) is the horizontal-update endpoint from the
\(C\)-ray.

There is no literal workaround which retains the same finite state.  Start
instead from the inherited updated profile \(Y_{C,k}\) and prefix its own
maximal exact roots.  This is source-faithful, but the old word
\(W_{C,k}\), which remains buried inside the suffix, was selected against the
\(C\)-semantics and need not be cap--Nash after the marked row has been
changed to \(F(C)\).  A later marked endpoint gain \(g\) therefore satisfies
only

\[
 d_p(\text{inherited source})\ge g,
 \qquad
 d_p(\text{updated source})
   =d_p(\text{inherited source})-g,             \tag{20a}
\]

not equality of the first quantity with \(g\).  New exact prefixing scales
both sides of the residual debt but cannot remove it.  Hence the zero reverse
mover in (12), the normalized vector \(h(F(C))/H_{F(C)}\), and the uniform
gain (8) belong to the separately restarted pure ray, not to the inherited
literal ray after the first update.

The renewal attempt therefore has an exact fork:

* restarting from the standalone pure coalition preserves the finite label
  state and the \(D_*/4\) scale, but introduces the unproduced seam (19);
* retaining the literal updated profile removes the seam, but loses the
  finite coalition state, the zero-coordinate regeneration, and eventually
  the uniform paid scale.

This fork is the precise obstruction to promoting the finite comparison map
to a source-matched update--re-exactify chronology.

## 5. Why positive minimum does not yet exclude recurrence

There is one further exact quantitative split at each horizontal update.  Let
\(X_{C,k}\) be the depth-\(k\) point on the \(C\)-ray and let \(Y_{C,k}\) be
the literal profile obtained by applying the selected toggle at its shifted
pure row.  The mover's debt drops by exactly \(g_{C,k}\).  Since \(Y_{C,k}\)
is actual, global minimality gives

\[
 \sum_{i\ne p(C)}
   \bigl(d_i(Y_{C,k})-d_i(X_{C,k})\bigr)
 \ge g_{C,k}-\bigl(D(C,k)-D_*\bigr).           \tag{21}
\]

Passing to a subsequence on which the finitely many recipient labels are
fixed, and writing

\[
 g_C={L_C\over H_C}h_{p(C)}(C),
\]

one obtains the exhaustive alternative

\[
 \boxed{
 L_C-D_*\ge {g_C\over2}\ge {D_*\over8}}
 \quad\text{or}\quad
 \boxed{
 \exists r\ne p(C),\quad
 \limsup_k\bigl(d_r(Y_{C,k})-d_r(X_{C,k})\bigr)
 \ge {g_C\over6}\ge {D_*\over24}.}            \tag{22}
\]

Thus every recurrent vertex is either uniformly deep,
\(L_C\ge9D_*/8\), or generates a fixed-scale literal debt transfer to a
different player.  This uses the positive minimum essentially and rules out
the possibility that the paid mover debt simply disappears at an
off-minimum update.  It still does not identify the transferred recipient
with an active coordinate of the original minimum point, nor does it make
the updated profile a point on the successor canonical ray.

Global minimality is used in (2), (5), (8), and (9), but it supplies no
cross-coalition comparison between \(L_C\) and \(L_{F(C)}\).  In particular:

* \(H_C\) need not decrease along an improving toggle;
* the removed mover can be replaced by newly positive debt coordinates;
* canonical re-exactification scales the successor's new debt vector but does
  not restore the old support; and
* exact-prefix charge belongs to separate vertical rays, while the transitions
  between them are horizontal unilateral updates, not admissible Bellman
  edges.

The six-cycle wall regression reviewed in
`STRENGTHENER__PURE_COALITION_WALL_SOURCE_RETURN.md` shows that all \(H_C\)
and all selected gains can be constant around an improving Boolean cycle.
That regression has global minimum zero and therefore is not a counterexample
to the present positive-minimum setting.  It establishes only that no missing
monotonicity follows from the finite reward table identities themselves.

No current theorem consumes (14) or (21)--(22).  Turning its paid horizontal cycle into
chronological charge would assume precisely the horizontal-to-vertical
realization that remains open.  Likewise, calling (12) support descent would
ignore possible entry of other debt coordinates.

Accordingly the exact remaining positive-minimum subproblem is:

> Consume a finite repeated segment carrying (14), or prove that one visited
> canonical ray has \(L_C=D_*\).  Any negative resolution by example would be
> an actual positive-gap Fin4 quitting table.

## 6. Lean correspondence

The wall identity is checked by
`quittingTerminalSemanticDebt_pureSetRoot_eq`.  Canonical ray debt and atom
scaling are checked in
`Research/Quitting/CausalTailEscapeMaxAbsorptionCore.lean`, especially:

```text
quittingMaximalCapPrefixProfile_debt_succ
quittingMaximalCapPrefixProfile_debt_mul_stage_eq
maximalCapPrefix_atomMass_lowerBound.
```

The new finite specialization can be packaged as:

```text
quittingPureCoalition_maximalRay_bestGain_ge_minimum_div_card
FinFourPureCoalitionCanonicalRayExit
FinFourPureCoalitionAllStallCyclePassport.
```

The last object must remain a residual, not be named as an atlas descent,
until it receives a chronological or support-safe consumer.
