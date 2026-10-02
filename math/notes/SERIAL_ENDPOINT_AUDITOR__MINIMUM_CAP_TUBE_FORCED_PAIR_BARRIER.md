# A minimum-cap tube quantitatively forbids exactification of the forced pair

Author: `SERIAL_ENDPOINT_AUDITOR`

## Status

This is an ordinary-mathematics positive-minimum no-go, not a consumer of the
forced-pair packet.  It applies directly to the current cofinal minimum-tail
pure-pair normal form.  A fixed amount of its pair mass cannot survive any
exact or vanishing-error cap--Nash repair whose continuation cap stays near
the minimum fibre.  More quantitatively, retaining unconditional pair mass
at least \(\lambda\) costs a fixed reached cap-defect charge.

Thus the marked pair cannot itself be inserted into a locally exact
chronology by a small perturbation.  A successful consumer must keep the pair
as a counterfactual paid sibling, leave the minimum-cap tube, or spend the
fixed defect through a genuinely new exact-return/regeneration construction.

## Question

Let \(D_*>0\) be the global minimum terminal-semantic debt in a Fin4 game.
Suppose \(z_n\) are actual semantic tails with

\[
 D(z_n)\longrightarrow D_*,
\]

and at a marked row over \(z_n\) the current root is a fixed pure pair.  The
checked forced-pair producer gives one zero-defect owner and a second player
whose marked cap defect is at least \(D_*/3\), while the unconditional pair
mass is at least a fixed \(\lambda>0\).

Can one repair that row, or a finite word containing it, by exact or
vanishing-error cap--Nash roots while retaining the fixed pair mass and the
same near-minimum tail?

The answer is no.

## 1. Uniform linear price around the minimum cap projection

Let

\[
 \mathcal M=\{z:D(z)=D_*\}
\]

be the compact minimum fibre and let

\[
 K_B=\{B(z):z\in\mathcal M\}.
\]

The set \(K_B\) is compact.  At every \(b\in K_B\), all Continue is an exact
root Nash equilibrium.  Under the positive-minimum Fin4 hypothesis it is the
unique exact cap--Nash root.  The minimum-fibre singleton separation also
gives one uniform positive gap

\[
 b_i-r_i(\{i\})\ge\Delta>0
 \qquad(b\in K_B,\ i\in\operatorname{Fin}4).
\]

Apply the compact strict-all-Continue linear absorption theorem to \(K_B\).
There are an open neighborhood \(N_B\supseteq K_B\) and \(c>0\) such that
for every \(b\in N_B\) and every product root \(q\),

\[
 \boxed{
 c\,a(q)\le R(b,q),
 }
 \tag{1}
\]

where

\[
 a(q)=1-\Pr_q(\text{all Continue})
\]

and \(R(b,q)\) is the total root Nash defect against the displayed cap
\(b\).

The relevant checked ingredients are
`exists_open_linearAbsorptionDefect_of_compact_strictAllContinue` in
`Quitting/Root/StrictAllContinueBasinLinearAbsorptionDefect.lean`, together
with the Fin4 minimum-fibre cap-freezing and singleton-separation results in
`TerminalSemanticCapNashNearMinimum.lean` and
`TerminalSemanticFinFourMinimumFiberIsolation.lean`.  The public integrated
linear theorem currently uses the prescribed-payoff projection; the cap
projection specialization above is the same compact argument with \(K_B\).

Since \(B(z_n)\to K_B\) after minimum-fibre subselection, eventually
\(B(z_n)\in N_B\).

## 2. A fixed pair mass has a fixed defect price

For a fixed nonempty coalition \(C\), let

\[
 \beta_C(q)=\Pr_q(Q=C).
\]

Coalition mass is bounded by total absorption:

\[
 0\le \beta_C(q)\le a(q).
\]

Equation (1) therefore gives

\[
 \boxed{c\,\beta_C(q)\le R(b,q).}
 \tag{2}
\]

In particular, if \(\beta_C(q)\ge\rho>0\), then

\[
 R(b,q)\ge c\rho>0.
\tag{3}
\]

Hence such a root cannot be exact cap--Nash.  If it is an
\(\varepsilon\)-cap--Nash root coordinatewise, then

\[
 R(b,q)\le4\varepsilon,
\]

so necessarily

\[
 \boxed{\varepsilon\ge c\rho/4.}
 \tag{4}
\]

Thus no vanishing-error cap--Nash sequence over minimum-tail caps can retain
a fixed conditional pair mass.

For the current literal pure pair, \(\beta_C(q)=1\).  The stronger table-level
screening calculation also gives

\[
 R(B(z_n),q)=\sum_i\delta_i(C)\ge D_*,
\]

and the frozen payer gives one coordinate

\[
 \delta_p(C)\ge D_*/3.
\]

These bounds are independent of the post-date tail.  They show directly that
the pure pair lies in a uniform forbidden neighborhood of the cap--Nash
correspondence; (1)--(4) extend that conclusion to every root retaining a
fixed fraction of its pair mass.

## 3. Finite-word form

Consider a literal finite root word \(q_0,\ldots,q_{T-1}\).  Put

\[
 C_0=1,
 \qquad
 C_t=\prod_{s<t}(1-a(q_s)),
\]

and suppose the displayed continuation cap at every row belongs to \(N_B\).
Let

\[
 \mathcal R=\sum_{t<T}C_tR(b_{t+1},q_t)
\]

be its reached total cap-defect charge.  Summing (1) gives

\[
 \boxed{
 c\sum_{t<T}C_ta(q_t)\le\mathcal R.
 }
 \tag{5}
\]

The sum on the left is exactly the probability that the word absorbs before
its tail:

\[
 \sum_{t<T}C_ta(q_t)=1-C_T.
\tag{6}
\]

If coalition \(C\) occurs at some marked row \(t<T\) with unconditional mass

\[
 C_t\beta_C(q_t)\ge\lambda,
\]

then

\[
 \lambda
 \le C_ta(q_t)
 \le\sum_{s<T}C_sa(q_s).
\]

Combining with (5),

\[
 \boxed{\mathcal R\ge c\lambda.}
\tag{7}
\]

Consequently:

* a finite exact cap--Nash word in the minimum-cap tube has zero absorption
  and cannot contain the marked pair;
* a family whose cumulative reached cap defect tends to zero cannot retain
  the fixed pair atom; and
* any family which does retain it carries a fixed paid cap-defect budget
  \(c\lambda\), whether or not the defect is spread over arbitrarily many
  rows.

This is stronger than a single-root continuity moat: it survives arbitrary
word length and explicitly rules out diluting the repair over many small
roots.

## 4. Exact relation to the current forced-pair target

The dirty checked target currently supplies, on one cofinal chronology:

* a literal post-date reference tail with debt tending to \(D_*\);
* one fixed pure pair at the marked date with unconditional mass
  \(>\lambda\);
* a forced owner with marked defect zero;
* a fixed distinct payer with marked defect at least \(D_*/3\); and
* actual reached gain at least \(\lambda D_*/3\).

Equations (3), (4), and (7) prove that this row cannot be upgraded to an exact
cap row, even approximately, while retaining any fixed fraction of the atom
and remaining in the minimum-cap tube.  In particular, neither local
coordinate correction nor a long sequence of vanishing repairs can construct
the missing exact chronology around the prescribed pair.

This does not contradict the packet: its pair is a deliberately
counterfactual sibling, not an exact prescribed row.  It also does not consume
the packet's fixed paid edge.  The remaining viable operations are now
sharply restricted to:

1. use the pair only as a counterfactual paid/curvature passport while an
   independently exact chronology returns near the source;
2. leave the minimum-cap tube and return with an exact positive charge; or
3. turn the fixed cap-defect budget into an actual minimum-fibre support
   regeneration.

The no-go excludes the fourth apparent route: directly or gradually
exactifying the marked pair in place.

## Lean handoff

The reusable declaration should be a cap-projection counterpart of the
existing prescribed-projection integrated linear theorem, followed by a
finite-prefix telescope:

```text
exists_finFour_minimumCapFiber_linearAbsorptionDefect

minimumCapTube_reachedCoalitionMass_mul_constant_le_reachedDefect
```

The second theorem needs only (1), coalition mass at most absorption, and the
finite survival identity (6).  It makes no attainment claim for the minimum
semantic pair and no best-response supremum is replaced by a stationary one.
