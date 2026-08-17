# Collision-anchored preemption geometry

Fix a four-player quitting table and a positive margin \(\gamma\). Write

\[
  x \longrightarrow y
  \quad\Longleftrightarrow\quad
  r_y(\{x\})+\gamma\le r_y(\{y\}).
\]

Thus \(y\) preempts \(x\). A collision certificate consists of an owner
\(q\) and a distinct collider \(c\) such that

\[
  \gamma\le r_q(\{q\}),
  \qquad
  r_c(\{q\})+\gamma\le r_c(\{q,c\}).
\]

For a hypothetical counterexample, the preemption walk can be rooted at the
same owner \(q\) that appears in the collision certificate. Every reached
edge extends to another edge. On four players, deleting repetitions after the
first return leaves one of the following six simple lassos.

| Tail and cycle | Required edges | Possible positions of \(c\) |
| --- | --- | --- |
| \((0,2)\) | \(q\to a\to q\) | \(a\), or outside the displayed cycle |
| \((0,3)\) | \(q\to a\to b\to q\) | \(a\), \(b\), or outside |
| \((0,4)\) | \(q\to a\to b\to d\to q\) | \(a\), \(b\), or \(d\) |
| \((1,2)\) | \(q\to a\to b\to a\) | \(a\), \(b\), or outside |
| \((1,3)\) | \(q\to a\to b\to d\to a\) | \(a\), \(b\), or \(d\) |
| \((2,2)\) | \(q\to a\to b\to d\to b\) | \(a\), \(b\), or \(d\) |

Here “outside” means outside the displayed lasso, not outside the player set.
The six rows and the listed marker positions give exactly seventeen marked
geometries up to relabeling.

The example “\(q\to j\), followed by the cycle
\(j\to k\to \ell\to j\)” is the \((1,3)\) row with \(a=j\), \(b=k\), and
\(d=\ell\). Its three marked versions are \(c=j\), \(c=k\), and \(c=\ell\).

## What the positions imply

If \(c\) is the first vertex after \(q\), the collision and preemption
inequalities align at the same payoff coordinate:

\[
  r_c(\{q\})+\gamma
  \le
  \min\bigl\{r_c(\{q,c\}),r_c(\{c\})\bigr\}.
\]

This alignment has two distinct semantic consequences. First consider the
sequential profile in which \(q\) quits at rate \(\lambda\) at stage zero and,
after survival, \(c\) quits surely. If \(c\) instead quits immediately, its
exact gain is

\[
  \lambda\bigl(r_c(\{q,c\})-r_c(\{q\})\bigr).
\]

Thus the collision inequality alone gives gain at least
\(\lambda\gamma\), strictly positive when \(\lambda,\gamma>0\). The solo
preemption inequality does not enter this source-matched calculation. In
particular, an algebraic comparison of convex combinations of the two solo
rows is not by itself a legal periodic-deviation theorem.

Second, consider the simultaneous repair row in which \(c\) quits surely and
\(q\) quits at rate \(\lambda\), followed off path by a punishment of \(c\).
The mechanism is an approximate terminal equilibrium exactly when all three
of the following hold:

1. \(q\)'s prescribed mixture is at least both of \(q\)'s pure endpoints;
2. no spectator gains by joining the quitting set; and
3. \(c\)'s prescribed payoff covers the exact punishment floor.

Alignment makes the prescribed payoff to \(c\) at least
\(r_c(\{q\})+\gamma\). Hence condition 3 is automatic under the scalar bound

\[
  \lambda r_c(\{q\})+(1-\lambda)\chi_c
  \le r_c(\{q\})+\gamma,
\]

where \(\chi_c\) is \(c\)'s punishment value. Under this bound, owner
optimality and spectator no-join are necessary and sufficient for the repair.
Without it, the original three conditions remain the exact characterization.

No such repair can work in a counterexample: it would supply terminal
approximate equilibria below the fixed exploitability gap. More sharply, the
collision certificate alone makes condition 3 automatic at every rate when

\[
  \chi_c\le r_c(\{c\}).
\]

In that case every rate fails through one of the other two conditions: either
the owner's prescribed mixture is not endpoint-optimal, or some spectator has
a profitable join.

These local conditions are jointly feasible. If an irreflexive relation
contains both \(q\to c\) and \(c\to q\), the universal realization above has
the collision certificate, both preemption edges, and an exact rate-one
collision repair at the pair exit \(\{q,c\}\). That pair exit is a sure exit
set, so its reward is a uniform-equilibrium payoff. Consequently, this
universal realization is not a counterexample, and the aligned two-cycle
cases cannot be eliminated from collision/preemption data and local repair
conditions alone. Any exclusion must use global information forced by a
hypothetical counterexample.

If \(q\) lies on the cycle and \(c\) is the vertex immediately before it,
the lasso instead supplies \(c\to q\). That edge is in player \(q\)'s payoff
coordinate, while the collision inequality is in player \(c\)'s coordinate;
there is no algebraic comparison between them without further information.

If \(c\) is another displayed vertex, the only forced link is the directed
path from \(q\) to \(c\). If \(c\) is outside the displayed lasso, the
collision certificate forces no preemption edge involving \(c\).

These statements concern the edges retained by the selected lasso. The full
preemption graph may contain additional edges, so a single table can realize
more than one row or marker position. The classification is exhaustive after
choosing a simple rooted witness and deleting surplus edges; it is not a
partition of full directed graphs.

## Reduction hierarchy

The seventeen marked geometries reduce as follows:

\[
  \text{17 marked positions}
  \longrightarrow
  \text{6 rooted lassos}
  \longrightarrow
  \text{cycle length }2,3,\text{ or }4
  \longrightarrow
  \text{a strict preemption cycle}.
\]

The first map forgets the collider's position. The second forgets the tail
and the distinguished root. The last forgets the cycle length.

No converse holds for a specified root or collider: an unmarked cycle does
not determine how the collision owner reaches it, and an owner-rooted lasso
does not determine where the collider lies.

## Every marked geometry is possible at table level

There is no hidden compatibility condition among these finite inequalities.
Given any irreflexive directed relation \(R\) and any distinct \(q,c\), set
the singleton coordinates to

\[
 r_y(\{x\})=
 \begin{cases}
  1,&x=y,\\
  0,&x\ne y\text{ and }R(x,y),\\
  2,&x\ne y\text{ and not }R(x,y),
 \end{cases}
\]

and set

\[
  r_c(\{q,c\})=r_c(\{q\})+1.
\]

The resulting margin-one preemption relation is exactly \(R\), and
\((q,c)\) is an immediate singleton collision. Taking \(R\) to contain only
the displayed lasso edges realizes every one of the seventeen rows above.
The corresponding normalized gate matrix is explicit:

\[
 M_{y,x}=
 \begin{cases}
  0,&x=y,\\
  -1,&x\ne y\text{ and }R(x,y),\\
  1,&x\ne y\text{ and not }R(x,y).
 \end{cases}
\]

Every vertex on a strict preemption cycle therefore survives every corrected
normal-layer deletion: its predecessor on the cycle remains a distinct
nonpositive gate witness.

Therefore none of the seventeen cases can be eliminated by graph geometry
alone. Any further reduction must use information beyond these finite
inequalities, such as the terminal exploitability barrier, semantic debt, or
an equilibrium construction.
