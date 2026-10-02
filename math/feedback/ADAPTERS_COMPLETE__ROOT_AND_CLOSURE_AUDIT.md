# Audit of ADAPTERS_COMPLETE.md, Sections 5 and 9--11

## Verdict

The repaired four-player calculation is correct. On the displayed
uniform-reach face, the exact cap-root relation is precisely

\[
\mathcal R=\{(t,q):tq=0\},
\]

and its greatest-\(q\) selector has the claimed jump at \(t=0\).

The compact-output exclusion for CW, SD, and bounded Rank is also correct
after the present Section 5 repair: terminal consumers, backward outputs, and
outcome carriers are now explicitly trace-safe and continuous, and the parent
coordinate is retained in the recursive outcome relation.

Three wording clarifications remain advisable:

1. call the operation a **constrained-face maximal exact root**, not an
   unrestricted globally maximal root;
2. state explicitly that the selector's parent port is the whole family
   \(([0,1],t\mapsto\sigma_t)\), rather than one existentially chosen value of
   \(t\); and
3. qualify the approximate-root exception in Section 11: the no-go still
   applies if a decoder is required to expose the exact discontinuous selector
   at its limit.

No change to the reward table or the closure proof is otherwise needed.

## 1. Source payoffs and unrestricted caps

For every nonempty coalition \(S\), the repaired table is

\[
r_a(S)=
\begin{cases}
1,&b\in S,\ a\notin S,\\
0,&\text{otherwise},
\end{cases}
\]

\[
r_b(S)=
\begin{cases}
-1,&b\in S,\\
1,&a\in S,\ b\notin S,\\
0,&a,b\notin S,
\end{cases}
\]

and

\[
r_p(S)=
\begin{cases}
-1,&p\in S,\\
0,&p\notin S
\end{cases}
\qquad(p=c,d).
\]

The all-Never payoff is zero. In the source \(\sigma_t\), players \(a,c,d\)
play Never and \(b\) quits at date \(1\) with probability \(t\).

The prescribed payoff is

\[
U(\sigma_t)=(t,-t,0,0).
\]

The full behavioral cap is

\[
B(\sigma_t)=(t,0,0,0).
\]

Indeed:

- player \(a\) receives \(1\) only if \(b\) quits first without \(a\), an
  event of probability at most \(t\); Never attains \(t\);
- player \(b\) obtains zero by Never, while every finite first quit by \(b\)
  pays \(-1\);
- players \(c,d\) obtain zero by Never, and every outcome in which the
  replacing player is among the first quitters pays \(-1\).

This calculation includes every randomized stopping law, every finite date,
and Never.

## 2. Exact cap-root inequalities

Consider

\[
x(q)=(q,0,0,0),
\qquad 0\le q\le\frac12.
\]

For player \(c\) or \(d\),

\[
Q_p=-1,\qquad C_p=0,
\]

so Continue is strictly optimal.

For player \(b\), quitting produces \(-1\) whether or not \(a\) also quits.
Continuing produces \(1\) when \(a\) quits and otherwise enters continuation
cap \(B_b(\sigma_t)=0\). Hence

\[
Q_b=-1,\qquad C_b=q,
\]

so Continue is again strictly optimal.

For player \(a\),

\[
Q_a=r_a(\{a\})=0,
\qquad
C_a=B_a(\sigma_t)=t.
\]

The exact complementarity inequalities are

\[
q(Q_a-C_a)=-qt\ge0
\]

and

\[
(1-q)(C_a-Q_a)=(1-q)t\ge0.
\]

The second is automatic; the first is equivalent to \(qt=0\). Therefore

\[
x(q)\text{ is an exact cap--Nash root}
\quad\Longleftrightarrow\quad
qt=0
\]

on the displayed face.

Consequently

\[
q^{\max}(t)=
\begin{cases}
0,&t>0,\\
1/2,&t=0.
\end{cases}
\]

Its graph is not closed, while every selected root has continuation reach

\[
1-q^{\max}(t)\ge\frac12.
\]

## 3. The child trace really detects the jump

For the prefixed child \(P_q\sigma_t\), player \(b\)'s prescribed payoff and
cap are

\[
U_b(P_q\sigma_t)=q-(1-q)t,
\qquad
B_b(P_q\sigma_t)=q.
\]

The cap identity follows because \(b\) can Continue at the root, receive \(1\)
if \(a\) quits, and otherwise play Never; any root Quit by \(b\) pays \(-1\).

Along \(t_n=1/n\), the selected root is \(q=0\), so both displayed coordinates
tend to zero. At \(t=0\), the selected root is \(q=1/2\), and both coordinates
equal \(1/2\). Thus both the visible root label and the full terminal semantic
child detect the discontinuity. The child profile itself also jumps in
\(\ell^1\).

## 4. Closure exclusion

The obstruction must be understood as a total operation over the compact
parent port

\[
P=([0,1],t\mapsto\sigma_t).
\]

The elementary replacement from \(\sigma_0\) builds this entire port if its
closed witness relation retains every \(t\in[0,1]\). If \(t\) were merely one
existential choice from the singleton initial port, selecting one convenient
\(t\) would not require a selector over the whole interval.

For this total parent port:

- a CW output is the continuous image of compact proof data, hence its
  visible \((t,q)\)-relation is compact and closed;
- an SD output is continuous on its compact inverse-limit code when the
  root label carries the required uniform summability budget, hence its
  visible relation is closed;
- a bounded Rank output is a finite union of compact terminal and
  successor/backward images, hence is closed.

Exactness and uniqueness would force each complete output relation to equal
the graph of \(q^{\max}\), which is impossible.

The current Section 5 supplies the conditions needed in the last bullet:
compact metrizable outcome carriers, continuous trace-safe terminal consumers,
trace-safe backward compilers, closed branch relations, and the retained parent
coordinate in \(O_k\). Thus the earlier rank-zero discontinuity loophole is
closed.

Equivalently, if compact proof data \(E\) carried a continuous surjection
\(p:E\to[0,1]\) and continuous output \(o:E\to[0,1/2]\) with

\[
o(e)=q^{\max}(p(e)),
\]

then \(p\) would be a compact-to-Hausdorff quotient map and
\(q^{\max}\) would be continuous, a contradiction.

## 5. Exact scope

The operation is maximal only on the fixed face

\[
x_b=x_c=x_d=0,
\qquad
0\le x_a\le\frac12.
\]

At \(t=0\), roots with \(x_a>1/2\) are exact outside this face. Therefore the
result must be described as a no-go for an exact **constrained-face**
maximizer. This is enough to refute a universal adapter claim covering every
exact optimized-root construction, but it does not by itself prove
nonclosedness of an unrestricted globally maximal cap-root selector.

The result also does not exclude:

- recording the whole closed exact-root relation and choosing \(q=0\);
- restricting to a compact subfamily separated from the jump;
- applying the discontinuous maximizer pointwise after one \(t\) has already
  been reconstructed; or
- using finite-accuracy approximate cap roots without promoting an exact
  maximizing root to the decoded trace.

The current Section 11 phrase

> approximate maximal roots with a displayed error converging through one
> decoder

is too broad. If the decoder must converge to and expose the exact selected
root, the same closed-graph obstruction applies. The genuine exception is a
finite-accuracy approximate-root or approximate-optimizer construction whose
decoded trace never claims the exact discontinuous selector.

## Final disposition

The repaired Sections 5 and 9--11 are mathematically sound after the three
scope clarifications above. The example is an exact rational Fin4,
same-continuation, positive-reach obstruction, and the CW/SD/bounded-Rank
exclusion is valid. It should not be advertised as an unrestricted global
maximal-root no-go.
