# Forced-pair data do not determine the induced-owner HOPF sign

## Status

Ordinary mathematics, not checked in Lean.  The reduction to the exact HOPF
entrance uses checked declarations.  The finite four-player table in Section 4
is a complete exact regression for the **local** forced-pair/response-square
data.  It has an all-Never equilibrium and hence does not satisfy the positive
minimum/hard-residual premise.  Thus it is a strategy-class fence, not a
counterexample to a source-attached positive-minimum adapter.

The conclusion is sharp:

* with the induced free set chosen to be the three nonowners, the outsider
  condition is vacuous;
* the forced pair controls one summand in the owner's induced
  Quit-minus-Never average, but neither the induced Nash law nor the other
  summands;
* finite label stabilization cannot repair this missing scalar sign;
* the minimal additional certificate is one induced Nash law at which that
  complete average is nonnegative, together with a nonpositive owner solo
  reward.

No source-faithful HOPF adapter is proved here.

## 1. Question and inspected declarations

Fix a Fin4 quitting table and a source-attached forced-pair or
minimum-response-chord packet.  Can its table inequalities force a checked
`QuittingInducedOwnerNeverChamber`, possibly after stabilizing the finitely
many player and coalition labels?

I inspected:

* `Research/Quitting/HopfCompletionSafeChambers.lean`:
  `QuittingInducedOwnerNeverChamber`, its all-behavior terminal-Nash and
  uniform-payoff consumers, and
  `exists_uniformPayoff_or_inducedOwnerNever_continue_sub_quit_pos_gap`;
* `Research/Quitting/FinFourProducerAtlas/ForcedPair.lean`:
  `FinFourWeakCoreForcedPairPacket`, the literal singleton-to-pair gain, the
  zero forced-owner defect, and the separate payer;
* `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`:
  `FinFourQuantitativeFullSupportHardResidual`;
* `formalized/FIN4_PRESCRIBED_OWNER_LABEL_HANDOFF_ALIGNMENT.md` and its named
  checked induced-base declarations.

The HOPF wrapper is a sufficient-data object.  It is not currently produced by
the atlas source.

## 2. Exact reduction of the entrance

Fix an owner \(h\) and take

\[
F=I\setminus\{h\}.
\]

Then

\[
\{h\}\cup F=I,
\]

so `QuittingInducedOwnerNeverChamber.outsider_no_join` is vacuous.  The finite
induced game has a mixed Nash point.  Consequently the only nonautomatic HOPF
fields are

\[
r_h(\{h\})\le 0                                             \tag{1}
\]

and the existence of an induced Nash point \(\pi\) satisfying

\[
Q_h(\pi)\ge C_h(\pi).                                      \tag{2}
\]

This reduction is useful because it removes the apparent four-part interface:
for the maximal free set there are exactly two scalar gates.

Let \(\mu_\pi(T)\) be the product law on quitting subsets
\(T\subseteq F\) at the induced root, and define

\[
g_h(\varnothing):=r_h(\{h\}),
\qquad
g_h(T):=r_h(T\cup\{h\})-r_h(T)\quad(T\ne\varnothing).
\]

Since the all-Continue outcome after the owner Continues has zero payoff,
direct expansion gives

\[
\boxed{
Q_h(\pi)-C_h(\pi)
=\sum_{T\subseteq F}\mu_\pi(T)g_h(T).
}                                                           \tag{3}
\]

Thus the exact missing certificate is not another local join inequality.  It
is one induced Nash law whose complete weighted owner-membership average in
(3) is nonnegative.

The checked compact alternative makes the obstruction equally exact.  Under
(1), either a point satisfying (2) exists and yields a UE, or there is
\(\gamma>0\) such that

\[
C_h(\pi)-Q_h(\pi)\ge\gamma
\]

for **every** induced Nash point.  In the hard residual, the first arm would
already contradict the terminal exploitability witness.  Hence an adapter
from the hard residual must use the positive-minimum source provenance to rule
out this uniform unsafe margin.  Merely choosing labels cannot do so.

## 3. What the current source inequalities control

For the natural choice \(h=\) `forcedOwner` and
\(j=\) `singletonOwner`, the checked forced-pair packet gives

\[
g_h(\{j\})\ge \gamma_{\rm term}>0.                          \tag{4}
\]

It also gives zero local defect for \(h\) at the resulting pure pair and a
positive defect for a separate payer.  The minimum-response rectangle adds a
source-matched signed response comparison and actual-law regeneration.

None of those fields currently gives:

1. a lower bound for \(\mu_\pi(\{j\})\) at an induced Nash point;
2. signs for \(g_h(T)\) on the other seven backgrounds;
3. the absolute singleton sign (1); or
4. an identity attaching the induced Nash law \(\mu_\pi\) to the regenerated
   minimum joint law.

Equation (4) is therefore one positive summand in (3), not the sign of (3).
Finite pigeonhole extraction can freeze \(h,j\), the payer, and the response
label, but cannot create any of items 1--4.

For example, if \(|r_i(S)|\le R\), a sufficient but deliberately strong
mass-domination certificate is

\[
\mu_\pi(\{j\})\gamma_{\rm term}
\ge 2R\bigl(1-\mu_\pi(\{j\})\bigr).                         \tag{5}
\]

Together with (1), (5) implies (2).  The direct weighted inequality (3) is the
minimal certificate; (5) shows concretely the kind of induced-law incidence
missing from the atlas packet.

## 4. Exact local regression

This table shows that the local forced-pair and response-square data, even
with (1), do not force (2).

Let \(I=\{0,1,2,3\}\).  For every nonempty coalition \(S\), define

\[
r_0(S)=
\begin{cases}
-1,&S=\{0\},\\
 1,&S=\{0,3\},\\
 0,&\text{otherwise},
\end{cases}                                                \tag{6}
\]

\[
r_1(S)=
\begin{cases}
0,&1\notin S,\\
1,&S=\{0,1,3\},\\
-1,&\text{otherwise},
\end{cases}                                                \tag{7}
\]

\[
r_2(S)=
\begin{cases}
0,&2\notin S,\\
1,&S=\{0,2,3\},\\
-1,&\text{otherwise},
\end{cases}                                                \tag{8}
\]

and

\[
r_3(S)=
\begin{cases}
-1,&3\in S,\\
0,&3\notin S.
\end{cases}                                                \tag{9}
\]

All unspecified values are fixed by these formulas; this is a complete
rational reward table.

### 4.1 Forced pair and separate payer

Take the singleton owner \(j=3\), forced owner \(h=0\), and the pure rows

\[
A=\{3\},\qquad B=\{0,3\}.
\]

Then

\[
r_0(B)-r_0(A)=1.                                           \tag{10}
\]

At \(B\), player 0 has zero endpoint defect because leaving gives 0 whereas
staying gives 1.  Player 1 is a separate payer because

\[
r_1(\{0,1,3\})-r_1(\{0,3\})=1.                            \tag{11}
\]

All these are literal date-zero profiles with all-Never tail, so the marked
mass is one and the postmark tail is identical.

### 4.2 Exact positive response square

Use observer 2 and the common pure-Quit response.  The four corners are

\[
A=\{3\},\quad B=\{0,3\},\quad
C=\{2,3\},\quad D=\{0,2,3\}.
\]

The response gains are

\[
U_2(D)-U_2(B)=1,
\qquad
U_2(C)-U_2(A)=-1,
\]

so the exact cross difference is

\[
\boxed{2>0.}                                                \tag{12}
\]

At \(B\), observer 2 has join debt 1; at \(D\), leaving returns only 0, so
observer 2 has zero endpoint debt.  Thus this regression contains the literal
forced pair, a distinct payer, a positive common-response square, and exact
observer-debt removal.

### 4.3 The induced-owner HOPF sign nevertheless fails

Take owner \(h=0\) and free set \(F=\{1,2,3\}\).  In the induced finite game
where 0 quits surely:

* player 3 strictly prefers Continue for every behavior of players 1 and 2;
* once player 3 Continues, player 1 strictly prefers Continue;
* once player 3 Continues, player 2 strictly prefers Continue.

Hence the unique induced Nash point is all-Continue.  At that point

\[
Q_0=r_0(\{0\})=-1,
\qquad
C_0=0.                                                      \tag{13}
\]

The solo sign (1) holds, and there are no outsiders, but (2) fails strictly.
Thus no `QuittingInducedOwnerNeverChamber` exists for the source-selected
owner 0 and maximal free set.

Finally, all-Never is an exact equilibrium because every solo payoff is
\(-1\).  Therefore \(D_*=0\).  This is exactly why the example does not refute
an adapter that genuinely uses the positive-minimum source and minimum-fiber
response-chord hypotheses.  It does prove that the local packet inequalities
and finite labels cannot be that adapter.

## 5. Precise remaining theorem

A source-faithful HOPF adapter can be stated minimally as follows.

> From the positive-minimum forced-pair/minimum-response-chord source, produce
> a stabilized owner \(h\) such that \(r_h(\{h\})\le0\), and an induced Nash
> point on the full complementary free set whose law satisfies (3) with
> nonnegative right-hand side.

The outsider certificate is then automatic, and the checked
`QuittingInducedOwnerNeverChamber` compiler gives an exact terminal Nash
profile against unrestricted behavioral deviations and hence a uniform
equilibrium payoff.

Equivalently, under the hard residual it is enough to contradict the uniform
positive unsafe margin furnished by
`exists_uniformPayoff_or_inducedOwnerNever_continue_sub_quit_pos_gap`.

What remains unknown is a bridge from the regenerated minimum law or response
chord to the distribution of **some induced Nash point**.  The two laws solve
different equilibrium problems, and current source provenance contains no
transport identity between them.

## 6. Next concrete question

Can minimum-response-chord extremality force either

\[
r_h(\{h\})>0
\]

for every candidate owner (which should enter a different checked chamber),
or, for one owner with nonpositive solo reward, rule out a uniform lower bound

\[
C_h(\pi)-Q_h(\pi)\ge\gamma>0
\]

over the complete induced Nash carrier?  This is the exact source-coherence
step.  Another singleton join inequality without induced-law incidence cannot
answer it.
