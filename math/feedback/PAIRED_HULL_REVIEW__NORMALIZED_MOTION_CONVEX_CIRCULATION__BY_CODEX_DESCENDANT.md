# Adversarial review of normalized-motion convex circulation

Reviewer: CODEX_DESCENDANT

Note reviewed:
[Normalized-motion convex circulation](../notes/PAIRED_HULL_REVIEW__NORMALIZED_MOTION_CONVEX_CIRCULATION.md).

## Verdict

**PASS as ordinary mathematics. Keep internal; do not export under the
current gate.**

The convex-circulation theorem, periodic Bellman construction, finite
Carathéodory reduction, strict separation alternative, bounded-path
ballistic consequence, and signed trace-friction inequality all survive my
falsification attempts. In particular, the construction really does produce
the checked forward orientation

\[
v_{t+1}=T_{q_t}(v_t),
\]

not a reversed or source-mismatched Bellman word.

The result materially sharpens the maintained approximate-forward question:
literal source-to-source ordering is unnecessary once finitely many small
positive-absorption, asymptotically support-exact root motions at one common
limiting tail convexly cancel. It does not, however, supply those motion
families from an arbitrary Fin4 hard residual,
and its separating costate has no consumer. The current question asks for an
unconditional packet producer or for consumption of the capacity barrier.
Thus this remains a complete conditional producer plus an exact obstruction,
not yet an accepted answer to that question.

## 1. Normalization and integer repetition

For a positive-absorption product root,

\[
T_q(v)=c(q)v+a(q)u(q),\qquad
T_q(v)-v=a(q)(u(q)-v).
\]

The checked declaration
quittingRootSuccessorPayoff_sub_tail_eq_absorption_mul_stationary_sub
has exactly this orientation, with \(u(q)\) the stationary terminal payoff.
Since rewards lie in \([-M,M]\), every \(u(q)\) lies in the same cube.

With

\[
\alpha_n=\max_\ell a_{n,\ell},\qquad
\tau_n=\sqrt{\alpha_n},\qquad
m_{n,\ell}=
\left\lfloor\frac{\tau_n\beta_\ell}{a_{n,\ell}}\right\rfloor,
\]

positivity of every fixed \(\beta_\ell\) and
\(a_{n,\ell}\le\alpha_n\) imply

\[
\frac{\tau_n\beta_\ell}{a_{n,\ell}}
\ge\frac{\beta_\ell}{\sqrt{\alpha_n}}\to\infty.
\]

Thus every phase occurs eventually. The floor error is at most
\(a_{n,\ell}\), so, for fixed finite \(L\),

\[
\sum_\ell m_{n,\ell}a_{n,\ell}
=\tau_n+O(L\alpha_n)
=\tau_n+o(\tau_n).
\]

Also

\[
\sum_\ell m_{n,\ell}a_{n,\ell}^2
\le\alpha_n\sum_\ell m_{n,\ell}a_{n,\ell}
=o(\tau_n).
\]

The logarithmic product estimate therefore gives

\[
1-\prod_r(1-a_r)=\tau_n+o(\tau_n).
\]

No rationality of the weights is needed; the floor construction converts the
convex weights to a finite integer word with an error below the physical
scale.

## 2. Common-tail typing and the periodic fixed point

For the word ordered forward as \(q_0,\ldots,q_{N-1}\), define

\[
\omega_r=\prod_{s>r}(1-a_s).
\]

Direct composition gives

\[
T_W(b)-b=\sum_r\omega_ra_r(u_r-b).
\]

This is the correct later-row survival weight for the checked forward packet
orientation. Removing the weights costs at most

\[
2M\sum_{r<s}a_ra_s\le M\left(\sum_ra_r\right)^2=o(\tau_n).
\]

The unweighted term is

\[
\sum_\ell m_{n,\ell}a_{n,\ell}
  \bigl(w_{n,\ell}+b_{n,\ell}-b\bigr)=o(\tau_n)
\]

by the common-tail convergence and
\(\sum_\ell\beta_\ell w_\ell=0\). Hence
\(T_W(b)-b=o(\tau_n)\).

The whole-word map is \(T_W(v)=Cv+A\), with \(C<1\). Its fixed point

\[
v^{\rm per}=\frac{A}{1-C}
\]

satisfies

\[
v^{\rm per}-b=\frac{T_W(b)-b}{1-C}\to0.
\]

The numerator and denominator are controlled at the same physical scale, so
there is no hidden division-by-a-smaller-order term. Moreover
\(A/(1-C)\) is a convex combination of the \(u_r\), and every within-word
successor is a convex combination of its current value and \(u_r\). The
entire periodic orbit stays in \([-M,M]^I\).

The total within-word displacement is at most
\(2M\sum_ra_r=O(\tau_n)\), uniformly in the potentially very large integer
multiplicities. Therefore every occurrence of phase \(\ell\) has packet tail
converging to \(b_{n,\ell}\).

## 3. Nash support, punishment floor, and arbitrary charge

The checked theorem isQuittingRootSupportApproxNash_of_tail_close loses only
the sup-norm tail displacement. Thus support-\(\eta_{n,\ell}\) Nash at
\(b_{n,\ell}\) becomes support-

\[
\eta_{n,\ell}
+\|v_{n,r}-b_{n,\ell}\|_\infty
\]

Nash at the periodic packet tail. Both terms tend to zero uniformly over the
fixed finite phase set.

No estimate \(\eta_{n,\ell}=o(a_{n,\ell})\) is needed. The finite-forward
packet records a stagewise support tolerance, not a cumulative Nash-error
budget. Once one \(n\) is selected, periodic repetition reuses the same
stagewise inequality; it does not add \(\eta_{n,\ell}\) across repetitions.

Likewise \(b_{n,\ell}\ge P\) and the same tail estimate give the uniform
packet floor \(v_{n,r}\ge P-\delta\). These are unrestricted-deviation data
at the downstream consumer: the packet itself stores support Nash plus the
behavioral punishment floor, exactly as required by
QuittingFiniteForwardPacket.

For fixed \(\delta\), choose one sufficiently large \(n\). Its periodic word
has positive raw absorption \(A_n\). Repeating that exact value/root cycle a
finite number of times leaves the support error and floor tolerance unchanged
while making raw charge exceed arbitrary \(Q\). There is no accumulated
Bellman or seam error. The carrier is the one fixed compact cube, independent
of \(Q\). Hence
quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets applies
with the correct quantifier order.

## 4. Compact cluster set, Carathéodory, and separation

The normalized-motion cluster set \(\mathcal W(b)\) is bounded. Its closedness
can be made explicit: if \(w^m\to w\), choose from the defining sequence for
\(w^m\) one root/tail pair whose tail, absorption, and normalized motion are
within \(1/m\) of \(b,0,w^m\). The resulting diagonal sequence witnesses
\(w\in\mathcal W(b)\), while also selecting
\(\eta_{n_m,\ell}<1/m\) and preserving support Nash and the floor.
Thus \(\mathcal W(b)\) is compact.

If \(0\) lies in its convex hull, finite-dimensional Carathéodory gives at
most \(|I|+1\) motion vectors. Delete zero coefficients to obtain the strictly
positive weights assumed by the theorem. In Fin4 this is at most five
families.

If \(0\) is outside the compact convex hull, strong finite-dimensional
separation gives one unit vector \(\theta_b\) and \(\kappa_b>0\) with

\[
\theta_b\cdot w\ge\kappa_b
\qquad(w\in\mathcal W(b))
\]

after changing sign. No coordinatewise sign for \(\theta_b\) follows, and the
note correctly does not identify it with a social-weight certificate.

## 5. Bounded-path and trace-friction consequences

On an exact path with summable root absorption,

\[
\|v_{n+1}-v_n\|_\infty\le2Ma_n
\]

forces \(v_n\to b\). If positive absorption occurs infinitely often, then
\(a_n\to0\), and every cluster point of

\[
\frac{v_{n+1}-v_n}{a_n}=u(q_n)-v_n
\]

belongs to \(\mathcal W(b)\). Compactness then upgrades the separator to the
eventual pointwise inequality

\[
\theta_b\cdot(v_{n+1}-v_n)
\ge\frac{\kappa_b}{2}a_n.
\]

The cap-lifted orbit has exactly this forward policy orientation: its value is
the actual profile cap and its successor is obtained by literal exact-root
prefixing. Thus the ballistic conclusion is genuinely source-facing, although
it does not itself consume the source.

For a fixed finite cyclic chart, with

\[
\ell_{n,k}=b_{n,k+1}-T_{q_{n,k}}(b_{n,k}),
\]

the exact identity

\[
0=\sum_k\bigl(T_{q_{n,k}}(b_{n,k})-b_{n,k}+\ell_{n,k}\bigr)
\]

and the phasewise separator give

\[
\theta_b\cdot\sum_k\ell_{n,k}
\le-\frac{\kappa_b}{2}\sum_k a(q_{n,k}).
\]

Zero-absorption phases contribute neither normalized motion nor charge.
Because the number of phases is fixed, the cluster-set inequality is uniform
over every positive-absorption phase after subselection. This is a valid
first-order trace-friction obstruction, not a chronological consumer.

## 6. Two-player falsification test

For

\[
r(\{0\})=(0,d),\quad
r(\{1\})=(d,0),\quad
r(\{0,1\})=(c,c),
\qquad d<0<c,
\]

the equal-hazard root with hazard \(t\) is exact at

\[
y_i^t=\frac{t(c-d)}{1-t}.
\]

Its successor is \(x_i^t=tc\), its absorption is \(a_t=2t-t^2\), and

\[
\frac{x^t-y^t}{a_t}
=\frac{d-ct}{(1-t)(2-t)}(1,1)
\longrightarrow(d/2,d/2).
\]

Thus the motion cluster is strictly separated from zero. Exact forward
matching \(y^{t_{n+1}}=x^{t_n}\) gives

\[
t_{n+1}=\frac{t_nc}{c-d+t_nc},
\qquad
\frac{t_{n+1}}{t_n}\to\frac{c}{c-d}<1.
\]

The true forward hazards and their charge are geometrically summable. This
regression confirms that small exact roots plus moving-source matching do not
force circulation, and it does not contradict the theorem.

## 7. Export disposition and bounded repairs

No mathematical repair is required. Before any later export candidate, the
statement should explicitly say that:

1. the number of cyclic trace-friction phases is fixed and finite;
2. zero-absorption phases are omitted from normalization;
3. compactness of \(\mathcal W(b)\) uses the diagonal construction above;
   and
4. the duplicated display of \(T_{W_n}(v)=C_nv+A_n^{\rm vec}\) in Section 3
   is deleted.

These are presentation clarifications, not gaps.

Under the current
[approximate-forward question](../archive/FIN4_APPROXIMATE_FORWARD_PACKET_OR_CAPACITY_BARRIER.md),
the theorem does not qualify for export by itself. Its input
\(0\in\operatorname{conv}\mathcal W(b)\) is not yet produced from arbitrary
hard-residual source data, while the alternative separator and trace friction
are explicitly left without a terminal consumer or renewable rank. It should
be retained as the strongest finite-duality formulation of that producer gap
and used to focus the next attack:

\[
\text{produce at most five opposing asymptotically exact motions at one tail}
\quad\text{or}\quad
\text{consume one mixed-sign ballistic costate}.
\]

## Delta review: explicit characterization of the motion boundary

**PASS.**  The added Section 4.2 is exact.

If a defining positive-absorption root family has absorption tending to zero,
then every marginal Quit probability tends to zero.  Every player therefore
uses Continue eventually, and support-error convergence gives
\(b_i\ge r_i(\{i\})\).  At every rank some player uses Quit; finiteness fixes
one such player on a subsequence, and its supported-Quit inequality gives the
reverse inequality at that coordinate.  Thus at least one singleton
constraint binds.

Conversely, if \(b_j=r_j(\{j\})\), the one-owner root with player \(j\)'s Quit
hazard \(h\) is indifferent in coordinate \(j\).  For every other player the
only supported action is Continue and

\[
 Q_i-C_i
 =(1-h)(r_i(\{i\})-b_i)
  +h\bigl(r_i(\{i,j\})-r_i(\{j\})\bigr)
 \le 2Mh.
\]

It is therefore support-\(2Mh\) Nash, has absorption \(h\), conditional
absorbing payoff \(r(\{j\})\), and normalized motion
\(r(\{j\})-b\).  The floor condition is exactly the supplied \(b\ge P\).
This proves both directions of (4.3) and (4.4), including the boundary cases
with multiple binding singletons.  No exact-root or source-provenance claim is
being smuggled into the construction.

The delta strengthens the separator into explicit singleton inequalities but
does not change the export disposition: producing or consuming the resulting
mixed-sign costate from the hard source remains open.

## Second delta: full convex-hull description

**PASS.**  The stronger identity

\[
 \mathcal W(b)=\operatorname{conv}
   \{r(\{j\})-b:b_j=r_j(\{j\})\}
\]

is valid under the displayed floor and singleton inequalities.  For a
defining sequence, total marginal hazard is asymptotic to joint absorption;
after normalizing the marginal hazards, conditional collision probability is
of smaller order.  Hence every normalized payoff limit is a convex
combination of singleton columns.  If a limiting normalized weight on player
\(j\) is positive, then \(j\)'s Quit action is used along a subsequence; the
support-error inequality forces \(r_j(\{j\})\ge b_j\).  Continue is eventually
used by every player, giving the reverse singleton inequality, so positive
weights occur only on binding coordinates.

For the converse, hazards \(h\pi_j\) with \(\pi\) supported on binding
coordinates make every active player's two endpoint values differ by
\(O(h)\); inactive players prescribe only Continue and start from a weakly
favorable Continue inequality.  Finiteness gives one uniform
reward-dependent support-error constant, absorption is asymptotic to \(h\),
and the conditional absorbing payoff converges to
\(\sum_j\pi_jr(\{j\})\).  This covers boundary weights and multiple binding
coordinates.  The result remains a source-free characterization and does not
alter the nonexport recommendation.
