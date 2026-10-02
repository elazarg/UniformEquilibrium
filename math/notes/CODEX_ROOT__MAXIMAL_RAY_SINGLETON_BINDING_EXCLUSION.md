# Singleton binding is impossible on a genuinely infinite maximal cap ray

Author: `CODEX_ROOT`

## Status

Ordinary mathematics, not yet independently reviewed and not Lean checked.
This is a small strengthening of the reviewed tail-normalized cap-flow
theorem.  It does not consume the strict ray: it removes only the singleton
binding support from a genuinely infinite **maximum-absorption** orbit.

## Question

Let

\[
 z_{k+1}=T_{q_k}z_k
\]

be the canonical semantic prefix orbit, where `q_k` maximizes root absorption
among all product roots which are exact Nash against the current unrestricted
behavioral cap vector `b_k`.  Suppose the strict-ray absorption sum is finite,
the roots are not eventually all Continue, and

\[
 b_k\longrightarrow \bar b.
\]

For `s_i=r_i({i})`, define the binding set

\[
 A=\{i:\bar b_i=s_i\}.
\]

Can `A` be a singleton?

## Theorem

Under the hypotheses above,

\[
\boxed{|A|\ne1.}
\]

In particular, for `Fin 4`, every genuinely infinite strict maximal ray has
either an empty binding set or a binding set of cardinality at least two.  The
empty case is also incompatible with nonzero late roots, because every
nonbinding player eventually has zero hazard.  Hence

\[
\boxed{2\le |A|\le4.}
\]

## Proof

The reviewed cap-flow theorem proves that every player outside `A` has zero
Quit hazard in every sufficiently late selected root.  Suppose

\[
 A=\{i\}.
\]

Because the orbit is not eventually all Continue, after deleting finitely
many indices the selected root has the form

\[
 q_k(i)=x_k\in(0,1),
 \qquad q_k(j)=0\quad(j\ne i).
\tag{1}
\]

The summable strict ray has `x_k -> 0`.

Player `i` mixes between Quit and Continue in (1).  Against opponents who all
Continue, those endpoint values are respectively

\[
 Q_i=s_i,
 \qquad C_i=b_{k,i}.
\]

Exact root Nash complementarity therefore gives

\[
\boxed{b_{k,i}=s_i}
\tag{2}
\]

at every sufficiently late index.

For every `j != i`, put

\[
 \delta_j=\bar b_j-s_j>0.
\]

At a candidate root in which only `i` Quits with probability `eta`, player
`j`'s Continue-minus-Quit difference against cap `b_k` is exactly

\[
 (1-\eta)(b_{k,j}-s_j)
 +\eta\bigl(r_j(\{i\})-r_j(\{i,j\})\bigr).
\tag{3}
\]

There are finitely many players.  Choose one fixed `eta in (0,1)` so small
that

\[
 \eta\,\left|r_j(\{i\})-r_j(\{i,j\})\right|
 <(1-\eta)\frac{\delta_j}{2}
\tag{4}
\]

for every `j != i`.  Since `b_(k,j) -> bar b_j`, eventually

\[
 b_{k,j}-s_j>\frac{\delta_j}{2}.
\tag{5}
\]

Equations (3)--(5) say every `j != i` strictly prefers Continue in this fixed
`eta` root.  By (2), player `i` is exactly indifferent.  Thus the product root

\[
 \widehat q(i)=\eta,
 \qquad \widehat q(j)=0\quad(j\ne i)
\]

is exact Nash against `b_k` for every sufficiently large `k`.  Its absorption
is exactly `eta`.

Maximality of the selected root gives

\[
 \eta\le x_k,
\]

contradicting `x_k -> 0`.  Therefore `A` is not a singleton.

If `A` were empty, the reviewed eventual-support theorem would make every
late hazard zero, so the orbit would be eventually all Continue.  This proves
the final cardinality statement.

## Consequence and limitation

The algebraic boundary

\[
 A=\{i\},\qquad \lambda=\Lambda=e_i
\]

still satisfies the tail-normalized solo/collision equations identically,
because both matrices have zero diagonal.  The present theorem excludes that
boundary only because the canonical selector maximizes exact root absorption.
It does not exclude:

* an eventually constant all-Continue ray;
* a proper binding set of size two or three;
* partial current support inside such a binding set; or
* ballistic collision holonomy.

## Sources inspected

* `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean` for the autonomous
  maximum-absorption selector and exact root Nash condition;
* `Research/Quitting/MaximalCapSemanticPrefixReturn.lean` for summability and
  vanishing absorption on the strict ray;
* `exports/STRICT_RAY_TAIL_NORMALIZED_CAP_FLOW.md` for cap convergence and
  eventual support on the binding set.

No statement here is asserted to be a checked Lean declaration.

