# The first omitted cap child cannot approach the next finite timing Nash law

Author: CODEX_SPINOZA

## Status

**Exact ordinary mathematics; quantitative obstruction, not Lean-checked.**
Let \(p\) be a Nash law of the timing game through deadline \(H\), and suppose
player \(i\)'s first omitted clock \(H+1\) is an unrestricted cap response of
gain at least \(\Gamma\).  Write

\[
 y=p[i\leftarrow H+1].
\]

Under a tablewide terminal exploitability gap \(\Gamma\), no Nash law \(q\) of
the enlarged timing game through deadline \(H+1\) can be close to \(y\):

\[
 \sum_j\operatorname{TV}(y_j,q_j)\ge \frac{\Gamma}{4M}.
\]

Thus the exact cap child cannot be connected to the next enlarged-menu Nash
source by a vanishing, sublinear, or summable full-law seam.  The proof gives
an exhaustive localization.  A full-gap debtor \(k\ne i\) at \(q\) forces a
new positive-solo omitted-clock owner and preserves a fixed Never mass for
the old owner \(i\).  If the debtor is still \(i\), the new boundary date
carries a fixed signed coalition collision, and replacing \(H+1\) by \(H+2\)
is itself a fixed-gain exact-cap edge.

This closes only the direct child-to-next-Nash orientation.  Neither localized
arm is yet a renewable rank or a Nash--Bellman chronology.

## 1. Finite timing conventions

Let \(I\) be a finite player set and let

\[
 |r_j(S)|\le M\qquad(M>0)
\tag{1.1}
\]

for every player \(j\) and nonempty quitting coalition \(S\).  The all-Never
payoff is zero.  For marginal probability laws, use

\[
 \operatorname{TV}(\mu,\nu)
 =\frac12\sum_a|\mu(a)-\nu(a)|.
\tag{1.2}
\]

Let

\[
 A_H=\{0,1,\ldots,H,\mathrm{Never}\}.
\tag{1.3}
\]

Fix a mixed Nash equilibrium \(p\) of the finite timing game on \(A_H\).
Suppose, for one player \(i\), the first omitted pure time is a paid complete
cap response:

\[
 U_i(p[i\leftarrow H+1])-U_i(p)
 =d_i(p)\ge\Gamma.
\tag{1.4}
\]

Put

\[
 y=p[i\leftarrow H+1].
\tag{1.5}
\]

Let \(q\) be an arbitrary mixed Nash equilibrium of the enlarged finite
timing game on \(A_{H+1}\).  Assume the actual behavioral realization of
every profile has a terminal gap

\[
 \max_k d_k(P)\ge\Gamma.
\tag{1.6}
\]

No relation between the equilibrium components containing \(p\) and \(q\)
is assumed.

## 2. The next omitted clock computes the complete debt at \(q\)

All dates through \(H+1\), as well as Never, are controlled actions at the
finite Nash law \(q\).  Every later pure time is payoff-equivalent to
\(H+2\).  Pure-time extremality therefore gives

\[
 d_k(q)
 =\bigl[U_k(q[k\leftarrow H+2])-U_k(q)\bigr]_+
\tag{2.1}
\]

for every \(k\).  By (1.6), choose \(k\) with

\[
 d_k(q)\ge\Gamma.
\tag{2.2}
\]

We compare separately \(k=i\) and \(k\ne i\).

## 3. A changed debtor forces an owner handoff and an old-owner Never floor

Suppose \(k\ne i\).  Since Never is a controlled action at \(q\),

\[
 \begin{aligned}
 d_k(q)
 &\le
 \Bigl[
 U_k(q[k\leftarrow H+2])
 -U_k(q[k\leftarrow\mathrm{Never}])
 \Bigr]_+\\
 &=\left[
 r_k(\{k\})
 \prod_{\ell\ne k}q_\ell(\mathrm{Never})
 \right]_+.
 \end{aligned}
\tag{3.1}
\]

The two pure actions in (3.1) differ only on the all-opponents-Never
cylinder.  Consequently (2.2) implies

\[
 r_k(\{k\})>0,
 \qquad
 r_k(\{k\})\prod_{\ell\ne k}q_\ell(\mathrm{Never})
 \ge\Gamma.
\tag{3.2}
\]

Because \(r_k(\{k\})\le M\) and all marginal probabilities are at most one,

\[
 q_\ell(\mathrm{Never})\ge\Gamma/M
 \qquad(\ell\ne k).
\tag{3.3}
\]

In particular, the old omitted-clock owner satisfies

\[
 q_i(\mathrm{Never})\ge\Gamma/M.
\tag{3.4}
\]

Moreover \(H+2\) is an exact complete cap for player \(k\), and its cap child

\[
 z=q[k\leftarrow H+2]
\tag{3.5}
\]

has a literal singleton-\(k\) terminal atom of mass

\[
 \prod_{\ell\ne k}q_\ell(\mathrm{Never})
 \ge\Gamma/M.
\tag{3.6}
\]

Since \(y_i=\delta_{H+1}\), (3.4) also gives directly

\[
 \operatorname{TV}(y_i,q_i)
 =1-q_i(H+1)
 \ge q_i(\mathrm{Never})
 \ge\Gamma/M.
\tag{3.7}
\]

Thus a changed debtor is a quantitative late-owner handoff, not a small
re-equilibration of the old cap child.

## 4. The same debtor forces a reached boundary collision

Suppose \(k=i\).  The pure action \(H+1\) belongs to the enlarged finite
game, so Nash optimality and (2.1)--(2.2) imply

\[
 U_i(q[i\leftarrow H+2])
 -U_i(q[i\leftarrow H+1])\ge\Gamma.
\tag{4.1}
\]

Against the old opponents \(p_{-i}\), no player has mass at \(H+1\).
Therefore

\[
 U_i(p[i\leftarrow H+2])
 =U_i(p[i\leftarrow H+1]).
\tag{4.2}
\]

Each fixed-pure-time payoff is \(2M\)-Lipschitz in the sum of opponent
total-variation distances.  Applying this once to each side of (4.2) gives

\[
 \Gamma
 \le4M\sum_{j\ne i}\operatorname{TV}(p_j,q_j)
 =4M\sum_{j\ne i}\operatorname{TV}(y_j,q_j).
\tag{4.3}
\]

There is also an exact coalition interpretation.  For a nonempty
\(A\subseteq I\setminus\{i\}\), let \(E_A\) be the event that no opponent
stops before \(H+1\) and precisely the opponents in \(A\) stop at \(H+1\).
Then

\[
 U_i(q[i\leftarrow H+2])
 -U_i(q[i\leftarrow H+1])
 =\sum_{\varnothing\ne A\subseteq I\setminus\{i\}}
 \Pr_q(E_A)
 \bigl(r_i(A)-r_i(A\cup\{i\})\bigr).
\tag{4.4}
\]

Hence at least one nonempty \(A\) satisfies

\[
 \Pr_q(E_A)
 \bigl(r_i(A)-r_i(A\cup\{i\})\bigr)
 \ge\frac{\Gamma}{2^{|I|-1}-1}.
\tag{4.5}
\]

In particular its joining externality is strictly negative, and using the
\(2M\) row bound,

\[
 \Pr_q(E_A)
 \ge
 \frac{\Gamma}{2M(2^{|I|-1}-1)}.
\tag{4.6}
\]

For \(I=\operatorname{Fin}4\), the last denominator is \(14M\).  The two
literal profiles

\[
 q[i\leftarrow H+1]
 \quad\longrightarrow\quad
 q[i\leftarrow H+2]
\tag{4.7}
\]

form a fixed-gain unilateral edge.  The target is an exact complete-cap
response and kills player \(i\)'s debt.  Formula (4.4) identifies the entire
gain as refusal of the reached boundary collision.

## 5. Uniform child-to-next-Nash separation

Combining (3.7) and (4.3) yields the promised estimate:

\[
 \boxed{
 \sum_j\operatorname{TV}(y_j,q_j)
 \ge\frac{\Gamma}{4M}.}
\tag{5.1}
\]

This holds for every choice of the old finite timing Nash \(p\), every paid
first-omitted owner \(i\) satisfying (1.4), and every Nash law \(q\) of the
enlarged menu.  It is stronger than merely saying that a particular
equilibrium-component selection may jump.

Consequently, along any nested finite-menu sequence with a fixed positive
terminal gap, the exact cap children cannot be joined to the next Nash laws
by seams whose summed marginal total variation tends to zero.  In
particular, a charge-relative \(o(1)\) seam, or a summable such seam, is
impossible while the charge is bounded below by \(\Gamma\).

## 6. Application to the off-minimum finite-component arm

The reviewed omitted-clock theorem reduces a bounded pure-clock response
component to either minimum-fibre support descent or a source-supported
off-minimum paid retraction.  In the latter arm it is tempting to make the
exact omitted child the next source by choosing a Nash law of the enlarged
timing menu nearby.  Equation (5.1) rules out exactly that repair under the
global gap.

The only two finite outputs left by the attempted enlargement are:

1. **owner handoff:** a different next debtor \(k\ne i\), with the old owner
   carrying the Never floor (3.4) and the new exact child carrying the
   singleton atom (3.6); or
2. **same-owner refusal collision:** the exact adjacent-clock cap edge (4.7)
   and the reached signed collision row (4.5)--(4.6).

Neither output identifies the next Nash law with the old response ancestry.
The owner-handoff set is not monotone under later re-equilibration, and the
same-owner edge is not an exact Nash--Bellman row.  Thus no renewable finite
rank, terminal approximate Nash profile, or charged return is claimed.

## 7. Sources inspected

- formalized/FINITE_DEADLINE_NASH_PROJECTIVE_BOUNDARY_AND_COMPATIBILITY.md;
- notes/CODEX_SPINOZA__FINITE_COMPONENT_OMITTED_CLOCK_MINIMUM_CHORD_HANDOFF.md;
- notes/SOCIAL_WEIGHT_REVIEW__OFF_MINIMUM_PURE_CLOCK_RESPONSE_CYCLE_TEMPORAL_ATTACK.md;
- formalized/FIN4_SIGNED_SOURCE_RETRACTION_AND_NEAR_MINIMUM_RESPONSE_CYCLE_CONTRACTION.md;
- UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean; and
- UniformEquilibrium/Diagnostics/Quitting/PureTimeCapAttainment.lean.

## 8. Boundary and nonclaims

- The finite menu must contain every old date and Never.  Otherwise (2.1)
  need not identify the first omitted time with the complete cap.
- The bound is in the full marginal stopping-law total variation.  It does
  not assert a lower bound for terminal coalition-law distance: clocks may
  move while terminal coalitions remain unchanged.
- The global terminal gap is essential.  If an enlarged Nash law is already
  terminal Nash, it may equal the old exact cap child.
- The theorem does not orient a finite response cycle and does not improve
  the generic off-minimum paid-port consumer.
- The collision in (4.4) is a refusal-to-join row for the same debtor.  It
  must not be relabeled as a profitable simultaneous Quit row without a
  separate sign conversion.

## Next exact question

Can the same-owner refusal collision (4.4), together with the retained
positive-minimum source retraction, force a source-matched charged return?
Equivalently, can the owner-handoff branch be made monotone in any exact
source-carried state field stronger than the marginal Never masses?  Without
one of those two additions, enlarged-menu Nashification has a uniform seam
floor rather than a summable chronology.
