# Positive cap curvature can persist behind a literal inert wall

Author: `CODEX_EULER`

Status: **INDEPENDENTLY REVIEWED PASS; INTERNAL INTERFACE NO-GO**

Independent review:
[CODEX_EULER__CURVATURE_INERT_CAP_CHRONOLOGY_SEPARATION__BY_CODEX_RAMSEY.md](../feedback/CODEX_EULER__CURVATURE_INERT_CAP_CHRONOLOGY_SEPARATION__BY_CODEX_RAMSEY.md)

## 1. Question and answer

The prefix-curvature cocycle gives, for a common prefix root, either retained
cap curvature or an immediate-Quit wall.  Can that interface alone force a
prescribed-payoff exact charged chronology, a cumulative positive-charge
return, or a strict support/debt regeneration at a unique-all-Continue cap?

No.  The rational Fin4 table below has all of the following simultaneously.

1. Three literal product stopping-law profiles form a source/midpoint/target
   square with positive cap curvature \(1/4\) in one coordinate.
2. At every one of the six relevant annotations (the three prescribed payoff
   vectors and the three cap vectors), the unique exact one-stage product
   Nash root is literally all Continue.
3. Prefixing all Continue preserves the whole semantic square and its
   curvature exactly, but creates only a zero-charge self-loop.  Iteration
   therefore creates neither cumulative positive charge nor any change of
   debt support or debt value.

Thus the positive-square arm can repeat forever.  A conversion theorem needs
additional source provenance beyond the cap square and the exact prefix
cocycle.  This is a local interface separation, not a counterexample to the
finite-quitting uniform-equilibrium conjecture and not a model satisfying the
positive-global-minimum hard residual.

All caps below are against unrestricted behavioral deviations.  Their exact
calculation uses the checked pure-time extremality of quitting deviations, not
a stationary-strategy restriction.

## 2. A complete rational Fin4 reward table

Let the players be \(1,2,3,4\).  Players \(3,4\) are strict passive dummies.
For a nonempty quitting coalition \(A\), define the active part
\(A^\circ=A\cap\{1,2\}\).  The first two reward coordinates depend only on
\(A^\circ\):

\[
\begin{array}{c|rrrr}
A^\circ & \varnothing & \{1\} & \{2\} & \{1,2\}\\ \hline
r_1(A) & 0 & 0 & 1/2 & 1\\
r_2(A) & 0 & 1 & -1 & 0.
\end{array} \tag{2.1}
\]

For \(d\in\{3,4\}\), set

\[
r_d(A)=\begin{cases}-1,&d\in A,\\0,&d\notin A.\end{cases} \tag{2.2}
\]

This specifies every nonempty coalition row, including dummy-only rows, and
has reward bound \(1\).

At all three profiles below, players \(3,4\) Never quit.  Player \(1\)'s law
is fixed and assigns probability \(1/2\) to each of dates \(0,1\).  Let

\[
S_2=\delta_0,\qquad T_2=\delta_1,\qquad
M_2=\tfrac12\delta_0+\tfrac12\delta_1, \tag{2.3}
\]

and denote the resulting product profiles by \(S,T,M\).  Thus \(M\) is the
literal midpoint of \(S,T\) in player \(2\)'s complete stopping law, with all
other coordinates held fixed.

## 3. Exact terminal payoffs and unrestricted caps

Direct enumeration of the two dates gives

\[
U_S=(3/4,-1/2,0,0),\qquad
U_M=(5/8,0,0,0),\qquad
U_T=(1/2,1/2,0,0). \tag{3.1}
\]

In particular \(U_M=(U_S+U_T)/2\), as required by linearity of the terminal
law.

For player \(1\), against \(S_2\), quitting at date \(0\) ties and pays \(1\),
so \(B_{S,1}=1\).  Against \(T_2\), quitting at date \(1\) ties and pays \(1\),
so \(B_{T,1}=1\).  Against \(M_2\), the pure-time values are

\[
V_1(0)=1/2,\qquad V_1(1)=3/4,\qquad
V_1(t)=1/2\quad(t\ge2\text{ or }t=\infty). \tag{3.2}
\]

Hence \(B_{M,1}=3/4\).

Against player \(1\)'s fixed law, player \(2\)'s pure-time values are

\[
V_2(0)=-1/2,\qquad V_2(1)=1/2,\qquad
V_2(t)=1\quad(t\ge2\text{ or }t=\infty). \tag{3.3}
\]

Thus \(B_{S,2}=B_{M,2}=B_{T,2}=1\).  Each dummy obtains \(0\) by Never and
\(-1\) whenever it quits, so its cap is \(0\).  Therefore

\[
B_S=(1,1,0,0),\qquad B_M=(3/4,1,0,0),\qquad
B_T=(1,1,0,0). \tag{3.4}
\]

The exact pure-time mixture theorem for quitting deviations implies that
\((3.2)\)--\((3.3)\) are the unrestricted behavioral caps: arbitrary behavioral
deviations are mixtures of their pure quit times, including Never.

For midpoint weight \(\lambda=1/2\), the player-\(1\) cap curvature is

\[
C_1=\tfrac12B_{S,1}+\tfrac12B_{T,1}-B_{M,1}=\frac14>0. \tag{3.5}
\]

All other cap-curvature coordinates vanish.

The debt vectors, useful for checking that no hidden rank changes, are

\[
d(S)=(1/4,3/2,0,0),\quad
d(M)=(1/8,1,0,0),\quad
d(T)=(1/2,1/2,0,0). \tag{3.6}
\]

## 4. Every relevant exact root is uniquely all Continue

Let \(Z\) be any vector in

\[
\{U_S,U_M,U_T,B_S,B_M,B_T\}. \tag{4.1}
\]

Consider the one-stage quitting game with continuation value \(Z\).

Each dummy strictly prefers Continue regardless of the other current actions:
quitting pays \(-1\), whereas continuing pays \(0\), either from the current
nonempty coalition or from its zero continuation coordinate.

Given that the dummies Continue, player \(2\) also strictly prefers Continue
for either pure action of player \(1\):

- if player \(1\) Quits, player \(2\)'s Continue payoff is
  \(r_2(\{1\})=1\), while Quit pays \(r_2(\{1,2\})=0\);
- if player \(1\) Continues, Quit pays \(r_2(\{2\})=-1\), while Continue pays
  \(Z_2\ge-1/2\).

Thus in every exact product Nash root player \(2\) Continues surely.  Given
that, player \(1\)'s Quit payoff is \(r_1(\{1\})=0\), while its Continue payoff
is \(Z_1\ge1/2\).  It too Continues surely.  Consequently

\[
\boxed{\text{all Continue is the unique exact product root at every }Z
\text{ in (4.1).}} \tag{4.2}
\]

This uniqueness is an exact endpoint-Nash statement.  Because the cap values
in \((3.4)\) were computed against all behavioral deviations, it does not conceal
a stationary-only best-response assumption.

## 5. Failure of curvature-to-chronology conversion

Prefix all three profiles by the common all-Continue root.  For every observer
the prefix parameters are \(c=1\) and \(A=0\).  At every actual corner its cap
dominates immediate singleton Quit, so every immediate-Quit wall is zero.
The exact curvature cocycle therefore gives

\[
C'_1=C_1=1/4. \tag{5.1}
\]

Equivalently, shifting every player's stopping law by one preserves the
terminal-coalition law, payoff vector, cap vector, and debt vector.  Hence the same
positive source-matched curvature square is available after every finite
number of inert prefixes.

On the other hand, \((4.2)\) says that an exact prefix whose tail annotation is
any relevant prescribed vector \(U_S,U_M,U_T\), or any relevant cap vector,
must be all Continue.  Its absorption is zero and its successor equals its
tail.  Therefore:

- no positive-charge exact prescribed-payoff edge starts from any square
  corner;
- every forward exact prefix orbit initialized with one of these vectors as
  its tail is the constant zero-charge self-loop;
- cumulative absorption is zero, so no positive-charge near-return consumer
  can fire; and
- \((3.6)\), including its support \(\{1,2\}\), is unchanged, so there is no strict
  debt-value or debt-support regeneration.

This disproves the implication

\[
\text{positive actual cap square + exact prefix cocycle + unique allC cap}
\Longrightarrow
\text{charged prescribed chronology / return / strict regeneration}. \tag{5.2}
\]

The example sits forever in the transported-square arm; it need not enter the
wall arm.  Thus a disjunctive renewal scheme whose only stored progress datum
is “positive square or immediate-Quit wall” has no terminating consequence.

## 6. Exact boundary and next legitimate question

The model does **not** satisfy a terminal exploitability witness or a positive
global minimum \(D_*>0\); it is not a Fin4 counterexample.  It also does not
refute a theorem that adds a floor-safe paid row, a tangent-family identity,
or a source-native prescribed-payoff relation as an independent hypothesis.
It shows that those data cannot be recovered from the static curvature square
and cocycle alone.

The direction is important: the example rules out a positive-charge edge
whose **tail** is one of the displayed vectors.  It does not rule out an
unrelated backward edge having one of them as its head.

The remaining legitimate producer question is therefore narrower: does the
specific normalized-curvature paid witness in the full hard residual carry an
extra source-native row or floor relation that rules out the table above and
survives an inert all-Continue prefix?  Reapplying the curvature decoder to
the unchanged square is not progress unless that extra datum changes a
well-founded state.

## 7. Checked interfaces inspected

The ordinary calculations were compared with these current declarations:

- `quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
  `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`;
- `quittingPureTimeDeviationPayoff_sub_rootThenContinuation_shift_one` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/`
  `PaidCapLiftedSummablePort.lean`;
- `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` and
  `quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash`
  in `UniformEquilibrium/Diagnostics/Quitting/`
  `TerminalCapNashEndpointTransport.lean`.

The exact cocycle and its reviewed scope are recorded in
`notes/CHATGPT_EXTERNAL__CURVATURE_PREFIX_RENEWAL.md` and
`feedback/CHATGPT_EXTERNAL__CURVATURE_PREFIX_RENEWAL__BY_CODEX_MINER.md`.
