# Pure-clock cap translation localizes to a date-zero mover

Identity: SOCIAL_WEIGHT_REVIEW

Status: **ordinary mathematics proved below; not Lean-checked.** This is a
strict refinement of the charged off-minimum paid-port arm, not a terminal
consumer. It uses the deterministic-clock provenance of the finite-clock
entrance. It does not apply to arbitrary behavioral response edges.

## 1. Question

The generic paid-response/maximal-root reduction can force a spectator cap
displacement across one unilateral response edge. A general exact example
shows that all of the spectator's pure-response values may translate by the
same amount, so the displacement need not produce response-gap curvature.

For a deterministic pure-clock edge there is an elementary obstruction to
that example: unless the mover changes whether it Quits at date zero, every
spectator has one literal response whose payoff is unchanged across the
edge.

## 2. Setup

Let \(I\) be finite and let \(P,Y\) be actual profiles of deterministic pure
times or Never. Suppose they differ only in player \(p\)'s clock. Let

\[
  V^P_j(q)=U_j(P[j\leftarrow q]),
  \qquad
  V^Y_j(q)=U_j(Y[j\leftarrow q])
\]

for a spectator \(j\ne p\) and a pure time or Never \(q\). Write

\[
  B_j(P)=\max_q V^P_j(q),
  \qquad
  B_j(Y)=\max_q V^Y_j(q).
\tag{2.1}
\]

The maxima are attained. Against deterministic pure-clock opponents, the
payoff of a pure response is determined by its order and tie class relative
to the earliest opponent deadline, so only finitely many payoff values occur.

Assume that both clocks of \(p\) prescribe Continue at date zero. Equivalently,
neither endpoint clock is QuitAt 0. Let \(z_j\) be QuitAt 0.

## 3. Common anchor lemma

### Lemma 3.1

For every spectator \(j\ne p\),

\[
  V^P_j(z_j)=V^Y_j(z_j).
\tag{3.1}
\]

### Proof

Under the response \(z_j\), player \(j\) Quits at date zero. The terminal
coalition is \(j\) together with exactly those opponents other than \(p\) whose
fixed clocks also equal zero. Player \(p\) Continues at zero in both \(P\)
and \(Y\), so the coalition, and hence \(j\)'s terminal reward, is identical.
No later part of either clock is reached. \(\square\)

## 4. Cap displacement gives a start-zero response switch

### Theorem 4.1

If

\[
  |B_j(Y)-B_j(P)|\ge c>0,
\tag{4.1}
\]

then, after possibly exchanging \(P\) and \(Y\), there is a pure time or Never
\(q\ne z_j\) such that

\[
 \bigl[V^Y_j(q)-V^Y_j(z_j)\bigr]
 -\bigl[V^P_j(q)-V^P_j(z_j)\bigr]
 \ge c.
\tag{4.2}
\]

At the higher-cap background, the two source-built counterfactual profiles
obtained by installing \(z_j\) and \(q\) form an actual unilateral edge.
The response \(q\) is exact and gains at least \(c\) over \(z_j\); its target
has zero \(j\)-debt. The first disagreement is exactly zero, its
pre-disagreement reach is one, and its favorable date-zero action is
Continue.

### Proof

Orient the endpoints so that \(B_j(Y)-B_j(P)\ge c\), and choose \(q\) attaining
\(B_j(Y)\). Then

\[
\begin{aligned}
 &\bigl[V^Y_j(q)-V^Y_j(z_j)\bigr]
 -\bigl[V^P_j(q)-V^P_j(z_j)\bigr]\\
 &=V^Y_j(q)-V^P_j(q)\\
 &\ge B_j(Y)-B_j(P)\ge c,
\end{aligned}
\]

where the first equality uses (3.1) and the inequality uses
\(V^P_j(q)\le B_j(P)\). In particular \(q\ne z_j\). If
\(q\) attains \(B_j(Y)\), while \(z_j\) is a feasible response at \(P\).
Using (3.1),

\[
 V^Y_j(q)-V^Y_j(z_j)
 =B_j(Y)-V^P_j(z_j)
 \ge B_j(Y)-B_j(P)
 \ge c.
\]

Thus \(q\) is the exact complete best response at the high endpoint and its
installation leaves \(j\)'s cap fixed while raising its payoff to that cap.
Since \(z_j\) Quits at zero and \(q\ne z_j\) Continues there, the first
disagreement is zero. \(\square\)

### Corollary 4.2 (charged-root constant)

Suppose the uniformly charged arm of the generic paid-response maximal-root
reduction is instantiated by pure-clock endpoint pairs. A fixed spectator
satisfies

\[
  |B_j(Y_n)-B_j(P_n)|\ge {\alpha D_*\over 6}.
\]

If the response mover \(p\) Continues at date zero at both pure-clock
endpoints, then the same source sequence contains a start-zero paid row for a
spectator of gain at least

\[
  {\alpha D_*\over 6}.
\tag{4.3}
\]

This removes pure affine translation and pure-time escape from that subarm.

## 5. Exact boundary

The hypothesis on \(p\)'s date-zero action is necessary. Suppose \(P\) makes
\(p\) Never Quit and \(Y\) makes \(p\) Quit at date zero. Give spectator
\(j\) reward one exactly when \(p\) belongs to the terminal coalition,
independently of \(j\)'s membership, and zero otherwise. With all remaining
players Never, every pure response of \(j\) has value zero at \(P\) and one at
\(Y\). Thus

\[
  B_j(P)=0,
  \qquad B_j(Y)=1,
\]

but every response gap is unchanged. This is the affine-translation
regression from the generic maximal-root reduction, now identified as a
date-zero mover phenomenon.

The example has global minimum zero. It does not show that this boundary is
compatible with the positive-minimum hard residual.

## 6. Exact root re-Nashification can reverse the observer

The start-zero edge cannot in general be turned into an exact cap--Nash root
while preserving its favorable Continue action.

Take four players \(j,k,g,\ell\). Define the terminal rewards of \(k,g,\ell\)
by

\[
 r_i(S)=
 \begin{cases}
 1,&i\notin S,\\
 0,&i\in S,
 \end{cases}
 \qquad i\in\{k,g,\ell\}.
\tag{6.1}
\]

For \(j\), set

\[
 r_j(\{j\})=1,\qquad
 r_j(\{k\})=1,\qquad
 r_j(\{j,k\})=0,
\tag{6.2}
\]

and also

\[
 r_j(\{g,\ell\})=r_j(\{j,g,\ell\})=0;
\tag{6.3}
\]

set its unspecified rewards to zero.

Let the postdate tail make \(g,\ell\) Quit surely and \(j,k\) Never Quit.
Its unrestricted cap is

\[
 b=(0,1,1,1)
\tag{6.4}
\]

in the order \(j,k,g,\ell\). For \(j\), the sure pair \(\{g,\ell\}\)
screens every response and both endpoint rewards are zero. Each of
\(k,g,\ell\) obtains cap one by Continuing while a player outside it Quits.

At the preceding pure root, prescribe \(k\) to Quit and \(g,\ell\) to
Continue. Then \(j\) strictly prefers Continue:

\[
 C_j=r_j(\{k\})=1>0=r_j(\{j,k\})=Q_j.
\tag{6.5}
\]

Thus the two pure-clock profiles with \(j=\) QuitAt 0 and \(j=\) Never form
the exact start-zero paid edge of gain one.

Nevertheless the root game against the actual tail cap (6.4) has a unique
exact product root, and it uses the opposite action for \(j\). Players
\(k,g,\ell\) strictly prefer Continue against every opponent root by (6.1).
Once they Continue, \(j\) compares

\[
 Q_j=r_j(\{j\})=1>0=b_j=C_j.
\tag{6.6}
\]

Hence the unique exact root is

\[
 (j:\mathrm{Quit},\ k:\mathrm{Continue},\
   g:\mathrm{Continue},\ \ell:\mathrm{Continue}).
\tag{6.7}
\]

Fresh exact-root selection changes \(k\)'s action, and that change reverses
the strict endpoint comparison of \(j\). Therefore neither strict margin nor
exact complete-response status is enough to preserve the observer through
root Nashification.

The regression has a zero-debt exact profile using the root (6.7), so its
global minimum is zero. It does not refute a theorem using positive-minimum
ancestry. It does prove that any such theorem must use that global source
information; pure clocks, start-zero reach one, a full unit response gain,
and an attained cap do not suffice.

## 7. Relation to the paid-cap waist

Whenever the charged arm is instantiated on a pure-clock source/response
pair, it therefore has the sharper split

\[
\boxed{
  \text{mover changes date-zero status}
  \quad\text{or}\quad
  \text{a fixed-gain start-zero spectator row}.}
\tag{7.1}
\]

The second output is source-attached and has no escaping disagreement date.
It is nevertheless not yet a consumer. A paid row at date zero is not an
exact cap--Nash root, and horizontal recurrence of such rows is not a forward
Nash--Bellman chronology. If another player already Quits at zero, the row
is a screened same-stage coalition toggle; if no one does, it is a
singleton-versus-continuation edge. The existing same-stage monodromy
impossibility applies only to its stronger producer object and cannot be
invoked on this row alone.

Thus the remaining finite-clock charged obstruction is more precise than
arbitrary affine cap leakage: it is either a literal date-zero mover toggle,
or the still-unconsumed problem of exactifying a source-attached start-zero
paid row without losing its cap and ancestry.

The arbitrary-clock minimum purification theorem supplies pure-clock paid
ports, but its strict target need not be an asymptotically minimum parent of
the two-profile maximal-root reduction. Therefore Corollary 4.2 is a
conditional refinement after those source types are aligned, not by itself
an adapter from every purified off-minimum port.

## 8. Positive-minimum exactification reaches the known inert boundary

The positive-global-minimum hypotheses control one tempting repair, but do
not consume the row. Let (w) be a carrier semantic pair on the positive
global-minimum fibre. Under the Fin4 hard residual, uniform minimum-fibre
singleton separation implies that all Continue is the unique exact product
root against the displayed cap of (w).

Consequently, if the high endpoint in Theorem 4.1 realizes (w), exact
cap--Nash prefixing cannot retain its reached source row as a nontrivial
current root. The only exact prefix is all Continue. It preserves the full
semantic pair and every response value, but shifts the paid first
disagreement from date zero to date one. Repetition gives the literal
zero-charge stack

\[
  w \longmapsto \mathbf C\star w
    \longmapsto \mathbf C^2\star w
    \longmapsto\cdots .
\tag{8.1}
\]

The paid response is transported losslessly but moves to temporal infinity.
Thus positive minimum excludes the action-reversal regression of Section 6
on the minimum fibre, while landing exactly in the already known strict inert
port. It supplies neither absorption charge nor a finite return.

Off the minimum fibre, the conclusion is false. A non-all-Continue exact root
may absorb. The checked minimum-fibre isolation and debt-moat theorem prices
such an exact root by a fixed excess whenever its carrier tail lies outside
the frozen tube. This is the quantitative off-minimum paid-port branch, not a
closure of it. Hence global source data sharpen exactification only to

\[
  \boxed{
    \text{positive exact-root charge and an off-minimum port}
    \quad\text{or}\quad
    \text{lossless all-Continue postponement}.}
\tag{8.2}
\]

This is not a new consumer. It explains why date-zero localization does not
bypass the principal waist: exactification either pays the already named
off-minimum charge or erases the temporal alignment that made the row useful.

## 9. Sources and novelty boundary

The quantitative input is Section 4.1 of
CODEX_DESCENDANT__GENERIC_PAID_RESPONSE_MAXIMAL_ROOT_REDUCTION.md and its
independent review. The deterministic pure-clock provenance is supplied by
[`ARBITRARY_CLOCK_MINIMUM_PURIFICATION_TO_OFF_MINIMUM_PAID_PORT.md`](../formalized/ARBITRARY_CLOCK_MINIMUM_PURIFICATION_TO_OFF_MINIMUM_PAID_PORT.md).

Narrow searches found no existing common-QuitAt-0 anchor lemma or this
date-zero localization of the affine-translation regression. The result is
a strict refinement of one paid-port subarm. It does not consume the
quantitative descent branch, the inert branch, reset rigidity, or the full
Fin4 conjecture. Section 8 is an application of the checked minimum-fibre
isolation/debt-moat package, not a novelty claim.
