# Finite duality for exact temporal shadows of paid pure-clock cycles

Author: CODEX_DESCENDANT

## Status

**Exact finite formulation and sharp no-go.** A selected word of literal
first-disagreement roots from a finite pure-clock response cycle admits a
source-attached, floor-admissible exact Nash--Bellman shadow exactly when a
finite affine feasibility system is nonempty. Any feasible word containing
one absorbing root is a positive admissible cycle and therefore yields a
uniform-equilibrium payoff by the checked compiler.

For strict paid moves, own-hazard complementarity collapses the mover's root
hazard to its pure better endpoint. Thus hazard mixing cannot repair the other
three coordinates without either erasing the paid inequality or changing the
literal continuation. Infeasibility has a finite Farkas certificate, but the
certificate can be supported entirely on root-Nash or source-seam mismatch.
Positive global minimality and the hard residual do not exclude such a
certificate; in the no-uniform-payoff branch they require one for every
positive exact-shadow candidate.

After literal source fixation, the dual classification is atomic: a failed
word has either a nonmover root defect, a signed source/Bellman seam, or a
punishment-floor failure. When the source tails already carry the floor
passport, only the first two remain. An exact wide-chamber local regression
below realizes conservative debt transfer together with both a root defect
and a source seam. It is deliberately not claimed to be a global
positive-minimum game.

The finite carrier-style strengthening is also exact. One rational table
has debt at least two on all sixteen pure date-zero coalition profiles and
on every one-player interpolation between them, while retaining a literal
six-state paid full-response cycle and atomic R/S obstructions. A displayed
simultaneous four-player product mixture has total debt (443/400<2).
Therefore all one-coordinate carrier constraints still do not imply global
minimality; the first new constraint appears on genuine multi-coordinate
product mixtures.

The Solan--Vieille boundary table gives an exact regression. Its literal
four-state max-debt response cycle fails the affine system twice: every target
coalition has a continuation-independent profitable toggle, and every
post-date source tail is the zero Never continuation rather than the next
Bellman state. The same table nevertheless has a checked exact period-two
behavioral equilibrium using different roots. Hence finite duality exposes
the missing producer but does not construct it.

## 1. Data from one paid pure-clock edge

Let \(x\to y\) be a literal one-player exact best-response edge between pure
clock profiles, with mover \(m\), gain \(g>0\), and first disagreement date
\(t\). Before \(t\), the profiles agree literally. Rebase at \(t\).

The target row is a pure root, represented by a coalition

\[
 S\subseteq I.
\]

The mover takes its strict better Boolean endpoint in this root. Let
\(w\in\mathbb R^I\) be the prescribed-payoff vector of the target's literal
post-row continuation after everyone Continues at the marked row. This is a
source datum, not a free Bellman annotation.

For a pure root \(S\), define its predecessor map

\[
 T_S(v)=
 \begin{cases}
 v,&S=\varnothing,\\
 r(S),&S\ne\varnothing.
 \end{cases}
\tag{1.1}
\]

For player \(i\), the two endpoint values against tail \(v\) are:

\[
\begin{array}{c|c|c}
 &\text{Continue}&\text{Quit}\\ \hline
i\in S&
 \begin{cases}
 r_i(S\setminus\{i\}),&S\setminus\{i\}\ne\varnothing,\\
 v_i,&S=\{i\},
 \end{cases}
 &r_i(S)\\[4mm]
i\notin S&
 \begin{cases}
 r_i(S),&S\ne\varnothing,\\
 v_i,&S=\varnothing,
 \end{cases}
 &r_i(S\cup\{i\}).
\end{array}
\tag{1.2}
\]

Call these \(C_i(S;v)\) and \(Q_i(S;v)\). They are affine functions of
\(v\).

The source-matched local paid identity is evaluated at \(v=w\). If the
target action of \(m\) is Quit, then

\[
 Q_m(S;w)-C_m(S;w)>0;
\tag{1.3Q}
\]

if it is Continue, the reverse difference is positive.

## 2. Why strict paid hazards become pure

Allow only the mover's Quit probability \(h\in[0,1]\) to vary, keeping the
literal opponents' row fixed. The endpoint difference

\[
 \Delta_m(v)=Q_m(S;v)-C_m(S;v)
\]

is independent of \(h\). Exact product-root complementarity says:

\[
 h>0\Longrightarrow \Delta_m(v)\ge0,
\qquad
 h<1\Longrightarrow \Delta_m(v)\le0.
\tag{2.1}
\]

Therefore:

\[
\Delta_m(v)>0\Longrightarrow h=1,
\qquad
\Delta_m(v)<0\Longrightarrow h=0.
\tag{2.2}
\]

At the literal continuation \(v=w\), a strict paid move forces the mover to
its pure target endpoint. An interior hazard is possible only after changing
the continuation enough to make \(\Delta_m(v)=0\), which deletes the strict
paid inequality. Thus own-hazard mixing cannot simultaneously retain the
source cap passport and repair nonmover Nash defects.

Allowing other players' hazards to move changes the literal opponent profile
against which the full response and its cap were computed. That is a source
seam, not a free Nashification.

## 3. The affine exact-shadow system

Take a nonempty cyclic selection of \(L\) paid edges. For edge \(k\), retain:

* its pure target root \(S_k\);
* its mover \(m_k\) and target endpoint sign;
* its literal continuation payoff \(w_k\);
* its positive local paid floor \(\gamma_k\); and
* its common-prefix/source passport.

Introduce cyclic Bellman annotations

\[
 v_0,\ldots,v_{L-1}\in\mathbb R^I,
\qquad v_L=v_0.
\]

The **abstract exact-shadow system** consists of:

### Bellman equations

\[
 v_k=T_{S_k}(v_{k+1})
 \qquad(0\le k<L).
\tag{3.1}
\]

### Exact root-Nash inequalities

\[
\begin{cases}
 Q_i(S_k;v_{k+1})\ge C_i(S_k;v_{k+1}),&i\in S_k,\\
 C_i(S_k;v_{k+1})\ge Q_i(S_k;v_{k+1}),&i\notin S_k.
\end{cases}
\tag{3.2}
\]

### Retained paid inequalities

With the sign chosen according to the mover's target endpoint,

\[
 \pm\bigl(Q_{m_k}(S_k;v_{k+1})
       -C_{m_k}(S_k;v_{k+1})\bigr)
 \ge\gamma_k>0.
\tag{3.3}
\]

### Punishment-floor and box inequalities

\[
 v_k\ge P
 \quad\text{coordinatewise},
\qquad
 |v_{k,i}|\le R,
\tag{3.4}
\]

where \(P\) is the behavioral punishment vector and \(R\) is the canonical
reward bound.

Every condition (3.1)--(3.4) is affine in the annotations.

The **source-attached exact-shadow system** adds the literal seams

\[
 v_{k+1}=w_k
 \qquad(0\le k<L).
\tag{3.5}
\]

Equation (3.5) is essential. Without it, (3.3) is a new one-stage comparison
against an invented continuation, not the retained whole-profile paid
response. It also retains the cap passport: the opponents and literal tail
against which the selected response was cap-attaining have not changed.

If one wishes to vary root hazards, the exact formulation becomes a finite
polynomial complementarity system. On every strict paid coordinate,
(2.2) reduces it back to the pure target endpoint. The affine system above is
therefore the correct strict source-matched face.

## 4. Exact consequence of feasibility

Suppose (3.1)--(3.5) is feasible. For each \(k\), use the Nash--Bellman state
whose payoff coordinate is \(v_k\) and whose root coordinate is the pure
root \(S_k\). Equations (3.1)--(3.2) give exact Nash--Bellman edges in cyclic
order. Equation (3.4) makes every state punishment-floor admissible.

If at least one \(S_k\ne\varnothing\), the cycle has positive actual
absorption charge; for pure roots its total charge is the number of nonempty
roots. The checked theorem
quittingGame_exists_uniformPayoff_of_positive_admissible_cycle then yields a
uniform-equilibrium payoff.

This conclusion is terminal and unrestricted. It does not identify revision
time with play time: the temporal chronology is the newly verified Bellman
cycle (3.1), not the horizontal response orbit.

## 5. Finite Farkas alternative

After collecting all variables into \(V\), write (3.1)--(3.5) as

\[
 AV\ge b,\qquad EV=f.
\tag{5.1}
\]

Exactly one of the following holds:

1. there is a feasible source-attached exact shadow; or
2. there exist real multipliers \(\lambda\ge0\) and unrestricted
   \(\mu\) such that

   \[
    \lambda^{\mathsf T}A+\mu^{\mathsf T}E=0,
    \qquad
    \lambda^{\mathsf T}b+\mu^{\mathsf T}f>0.
   \tag{5.2}
   \]

This is a finite exact real certificate. It is a rational certificate when
all coefficients in (5.1), including the floor vector, are rational. A
rational reward table alone does not automatically make the behavioral
punishment vector rational: that floor is defined by an unrestricted
min--max value. Thus an executable rational dual additionally needs an exact
ordered-field representation or a separate certificate for the floor
comparisons. The root and literal-seam subsystem has rational coefficients
for rational pure-clock data; its dual obstruction is rational without this
extra floor issue.

Because the roots are pure, this dual is more explicit than general Farkas
separation. If the word contains an absorbing root, the Bellman equations
propagate the next absorbing reward backward through any intervening
all-Continue roots. Feasibility reduces to finitely checking:

* continuation-independent toggle inequalities at nonsingleton roots;
* singleton and all-Continue inequalities against the next propagated
  reward;
* punishment-floor inequalities; and
* the literal source equalities \(v_{k+1}=w_k\).

Hence a minimal dual obstruction can be a single violated root inequality or
a single signed source-seam mismatch. There is no reason for it to involve
the accumulated paid gains.

## 6. Exact Solan--Vieille regression

For the boundary table, the date-zero max-debt response cycle is

\[
 \{2\}\to\{0,2\}\to\{0,2,3\}\to\{2,3\}\to\{2\}.
\tag{6.1}
\]

The selected gains are \(1,1,1,3\). Each target coalition fails exact
root Nash by the next profitable response:

\[
\begin{array}{c|c|c}
\text{target root}&\text{profitable toggle}&\text{gain}\\ \hline
\{0,2\}&3\text{ joins}&1\\
\{0,2,3\}&0\text{ leaves}&1\\
\{2,3\}&3\text{ leaves}&3\\
\{2\}&0\text{ joins}&1.
\end{array}
\tag{6.2}
\]

These are continuation-independent at the nonsingleton roots. At the
singleton root, the outsider join is also independent of the continuation.
Thus (3.2) already fails at every phase.

There is a second independent obstruction. Every edge in (6.1) disagrees at
date zero, and the literal post-date continuation is all Never, with payoff
zero. Source attachment requires

\[
 v_{k+1}=0.
\tag{6.3}
\]

But the next absorbing Bellman predecessor requires

\[
 v_{k+1}=r(S_{k+1}),
\tag{6.4}
\]

and the displayed reward rows are nonzero. Thus a signed seam coordinate
alone is a Farkas certificate.

Nevertheless the same table has the checked exact period-two terminal Nash
profile and uniform-equilibrium payoff. Its Bellman roots and annotations are
not the literal target rows of (6.1). Therefore the dual certificate rejects
only the proposed literal shadow; it is not a counterexample certificate and
does not imply nonexistence of a different exact chronology.

## 7. Test against positive minimality and the hard residual

Positive global minimality does not rule out the dual alternative. If a
positive source-attached floor-admissible cycle were feasible, Section 4
would already give a uniform-equilibrium payoff and contradict the
positive-minimum counterexample branch. Thus that branch necessarily carries
a Farkas obstruction for every candidate positive shadow.

The hard residual also does not impose the missing state seams. It is a
reward/sign and source condition; it does not identify the post-row payoff
of one horizontal response profile with the Bellman predecessor payoff of
the next profile in revision order. The checked boundary table is
residual-hard, has full normal core, and has no exact stationary equilibrium,
yet realizes both kinds of obstruction in Section 6.

The boundary table has zero global minimum, so it is not a counterexample to
the positive-minimum source theorem. Its role is exact and narrower: it
shows that the finite root/seam dual is compatible with every local
hard-residual screen and can coexist with a uniform equilibrium.

Consequently a signed Farkas obstruction is not something the present hard
residual can simply forbid. A successful positive proof needs an additional
producer forcing at least one selected word to avoid both obstruction
classes.

## 8. Exact missing producer

The response cycle supplies:

* finitely many literal profiles;
* complete best-response gains;
* first-disagreement rows; and
* an exact externality ledger around revision space.

It does not supply:

* nonmover exactness at any target first-disagreement root; or
* equality between that edge's literal post-row continuation and the next
  selected Bellman predecessor state.

The missing theorem can now be stated finitely:

> From the positive-minimum source ancestry and the finite pure-clock
> response cycle, select a nonempty cyclic word of paid first-disagreement
> rows for which the affine system (3.1)--(3.5) is feasible; or convert every
> Farkas certificate (5.2) into a previously accepted off-minimum descent,
> support entry, or charged return.

The second clause is essential. Merely extracting a signed dual vector does
not contradict positive minimality; source-seam multipliers can carry the
entire separation. Those equality multipliers are unrestricted in sign and
belong to different horizontal source profiles. They therefore do not form
the nonnegative absorption charge of one ordered chronology, and the existing
signed-seam telescope cannot be applied until an actual target-to-next-source
chain is supplied.

## 9. Sources checked

The exact semantic interfaces used are:

* IsQuittingNashBellmanEdge in
  UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean;
* QuittingPunishmentFloorAdmissibleEdge and the charged relation in
  UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean;
* quittingGame_exists_uniformPayoff_of_positive_admissible_cycle in
  UniformEquilibrium/Quitting/Bellman/Finite/PositiveAdmissibleCycle.lean;
* the finite pure-clock response cycle in
  formalized/FIN4_FINITE_PURE_CLOCK_EXACT_RESPONSE_CYCLE.md; and
* the boundary-table period-two regression in
  UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean
  and
  UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean.

## 10. Conclusion

Finite duality gives an exact decision procedure for any proposed literal
pure-row shadow, but it does not make such a shadow exist. Strict mover
complementarity removes the apparent hazard freedom. The surviving dual may
be a root-local profitable toggle or a mismatch between unrelated literal
continuations.

Thus the finite response cycle is not one missing Farkas calculation away
from a temporal return. The precise barrier is:

\[
\boxed{
\text{revision-cycle recurrence}
\ \not\Longrightarrow\
\text{source-matched Bellman-state recurrence}.}
\]

The useful next target is not local Nashification. It is a producer that
forces cross-profile continuation-state matching, or a theorem that spends
the resulting signed seam dual as accepted chronological charge.

## 11. Minimal-support dual classification after source fixation

The literal equations (3.5) fix every annotation:

\[
 v_{k+1}=w_k.
\]

Substituting these values into (3.1)--(3.4) removes all primal variables.
Consequently every infeasible literal word has an atomic obstruction of one
of the following forms.

### R: a root obstruction

For some phase \(k\) and nonmover \(i\), the target action is not a best
endpoint:

\[
\begin{cases}
 Q_i(S_k;w_k)<C_i(S_k;w_k),&i\in S_k,\\
 C_i(S_k;w_k)<Q_i(S_k;w_k),&i\notin S_k.
\end{cases}
\tag{11.1}
\]

The mover cannot support (11.1), because its literal target endpoint has the
strict paid sign.

### S: a source/Bellman seam obstruction

For some phase and coordinate,

\[
 w_{k-1,i}\ne T_{S_k}(w_k)_i.
\tag{11.2}
\]

This says exactly that the literal tail of the preceding horizontal response
is not the current Bellman payoff of the next selected row.

### F: a punishment-floor obstruction

For some phase and coordinate,

\[
 w_{k-1,i}<P_i.
\tag{11.3}
\]

If the Bellman seam (11.2) holds at that phase, this is equivalently

\[
 T_{S_k}(w_k)_i<P_i.
\]

The canonical box inequalities cannot fail for actual pure-clock payoff
vectors. The paid inequality cannot fail at the literal tail. Hence R, S,
and F are exhaustive for the source-fixed subsystem. If the selected source
tails are already certified above the punishment floor, F is absent and the
finite root/seam subsystem has exactly the two obstruction classes R and S.

Formally a Farkas certificate may use the source-fixing equalities together
with the violated row. After elimination, however, its semantic support is
one phase, one player, and one of the three labels R/S/F.

For any infinite family whose clock alphabet has the Fin4 bound, the cycle
lengths, phases, players, root coalitions, and obstruction labels range over
finite sets. After passage to a subsequence, one may stabilize all of them.
Normalizing a nonzero dual to unit \(\ell^1\)-mass then gives a persistent
root, seam, or floor obstruction. Stabilization does not change its agency:
R remains another player's endpoint comparison, while S remains a signed
equality between different horizontal profiles.

## 12. Why the externality ledger does not orient the dual

The response-cycle ledger gives an edge \(x\to y\) and a nonmover \(j\)
whose prescribed payoff falls by a fixed amount. This is the comparison

\[
 U_j(y)-U_j(x)<0
\tag{12.1}
\]

caused by the mover changing its complete clock.

A root obstruction R is instead player \(j\)'s comparison between changing
its **own** Boolean action and retaining it at one target row. There is no
sign implication from (12.1) to (11.1). Even when the same player occurs in
both statements, the first inequality is an adverse externality and the
second is a profitable response. Their conjunction merely supplies the next
horizontal best-response edge.

Punishment normality likewise does not reverse (11.1). It supplies
punishment values and selected collision signs, not Nash signs at every
coalition appearing in an arbitrary pure-clock orbit.

Source ancestry makes every \(w_k\) literal, which is necessary to state S,
but it gives no equality between \(w_{k-1}\) and
\(T_{S_k}(w_k)\). Thus ancestry exposes the seam obstruction without
removing it.

If the stabilized dual has type R, one recovers a cofinal family of literal
nonmover response rows, not a temporal edge. If it has type S, the multiplier
is unrestricted in sign and no ordered target-to-source chain is present. If
it has type F, one has failed to enter the floor-admissible relation. None of
these conclusions is an accepted paid return or a lower-debt carrier point.

## 13. Wide-chamber positive-minimum passport regression

The failure is compatible with the strongest elementary pointwise
positive-minimum inequalities; it is not confined to the one-debtor token
rotation.

Take players \(0,1,2,3\), the pair \(K=\{0,1\}\), and
\(Y=K\cup\{3\}\). Prescribe the relevant reward coordinates by

\[
\begin{array}{c|cccc}
S&r_0(S)&r_1(S)&r_2(S)&r_3(S)\\ \hline
K&3&3&3&3\\
Y&2&3&3&4\\
\{1\}&4&*&*&*\\
\{0\}&*&3&*&*\\
K\cup\{2\}&*&*&3&*\\
\{1,3\}&3&*&*&*\\
\{0,3\}&*&4&*&*
\end{array}
\tag{13.1}
\]

and set every own singleton reward to one. Omitted entries can be placed
below the displayed comparisons for this local calculation.

At the pure pair profile \(X=M^K\), the exact screened cap/debt data are

\[
 U(X)=(3,3,3,3),\qquad B(X)=(4,3,3,4),\qquad
 d(X)=(1,0,0,1),\qquad D(X)=2.
\tag{13.2}
\]

Player \(3\)'s join \(X\to M^Y\) is a full response of gain one. It harms
player \(0\) by one. At the target \(M^Y\),

\[
 U(M^Y)=(2,3,3,4),\qquad B(M^Y)=(3,4,3,4),
 \qquad d(M^Y)=(1,1,0,0),\qquad D(M^Y)=2,
\tag{13.3}
\]

because players \(0\) and \(1\) profit by leaving to
\(\{1,3\}\) and \(\{0,3\}\), respectively.

Along the radial join chord, the debts may be read directly from (13.1):

\[
 d_0=1,\qquad d_1=t,\qquad d_2=0,\qquad d_3=1-t.
\tag{13.4}
\]

In particular the paid response has the exact conservative leakage ledger

\[
 d(M^Y)-d(X)=(0,1,0,-1).
\tag{13.4a}
\]

The mover's unit debt is annihilated and is replaced by one unit of debt on
player \(1\); total debt does not fall. The harmed player \(0\) remains a
debtor and is also one of the target root's profitable leavers. Thus even
the alignment of a paid gain, an adverse externality, and an exact
same-total-debt transfer does not orient the R-obstruction into descent.

Thus total debt is identically two. Taking the pointwise benchmark
\(D_{\mathrm{ref}}=2\), both endpoints have at least two debt coordinates
across the chord, and

\[
 D_{\mathrm{ref}}=2=2\max_i d_i(X).
\tag{13.5}
\]

This has the wide ratio pattern
\(D_{\mathrm{ref}}=2\max_i d_i(X)\), rather than the excluded one-debtor
pattern \(D_{\mathrm{ref}}=\max_i d_i\).

The pointwise singleton margins also hold with this benchmark:

\[
 B_i(X)-r_i(\{i\})\ge2,
\qquad
 B_i(M^Y)-r_i(\{i\})\ge2.
\tag{13.6}
\]

Every displayed prescribed payoff exceeds the corresponding own singleton
reward. The all-Continue root at each displayed cap is therefore strict.
One may also place a supplied floor \(P\le(1,1,1,1)\) below every displayed
current payoff.

Nevertheless the literal target root \(Y\) has two R-obstructions of size
one: players \(0\) and \(1\) strictly prefer to leave. The literal date-zero
post-row continuation is all Never, so an attempted cyclic splice also has
an S-obstruction unless the next Bellman state is zero.

This is an exact finite **passport regression**, not an actual
positive-minimum quitting game. It verifies compatibility with:

* positive total debt;
* the wide \(D_{\mathrm{ref}}/\max d_i\) ratio pattern;
* minimum singleton margins;
* positive prescribed singleton gaps;
* an affine same-debt chord;
* a fixed paid mover gain; and
* a fixed adverse nonmover externality.

It does not assert that the partial table has a global carrier minimum, the
actual behavioral punishment vector displayed above, or a hard-residual
source. Proving those missing global assertions would amount to constructing
the kind of counterexample presently unknown. The regression's valid
conclusion is narrower: none of the listed pointwise minimum consequences
algebraically excludes the atomic R/S dual.

## 14. Refined negative conclusion

The finite dual can always be stabilized, but its sign pattern need not be
useful.

\[
\boxed{
\begin{array}{c}
\text{paid externality around revision space}\\
+\ \text{positive-minimum pointwise geometry}\\
\not\Longrightarrow\\
\text{a nonnegative chronological dual or lower-debt direction}.
\end{array}}
\tag{14.1}
\]

To progress from the dual, one needs genuinely global information beyond the
current pointwise passports:

1. a theorem co-realizing an R-obstruction as an exact predecessor row with
   the correct next tail;
2. a target-to-next-source identity orienting an S-obstruction; or
3. a theorem converting an F-obstruction into an actual punishment response.

Without one of these, minimal-support Farkas classification returns exactly
the already known horizontal response, seam mismatch, or floor failure.

## 15. Exact finite carrier-style strengthening

The abstract regression in Section 13 can be completed to a rational reward
table which satisfies the benchmark debt floor not only at the two displayed
vertices, but at **every pure date-zero coalition profile and every
one-player interpolation between two such profiles**.

The rows below are indexed by the nonempty coalition mask in binary order:

\[
\begin{array}{c|c@{\qquad}c|c}
1&(1,3,3,0)&\quad 2&(4,1,6,4)\\
3&(3,3,3,3)&4&(5,0,1,7)\\
5&(-2,-3,4,6)&6&(6,6,4,1)\\
7&(-2,7,3,0)&8&(3,5,3,1)\\
9&(1,4,0,7)&10&(3,0,0,7)\\
11&(2,3,3,4)&12&(3,5,6,0)\\
13&(-1,7,6,-3)&14&(-3,5,-3,2)\\
15&(-3,-1,-1,6).&&
\end{array}
\tag{15.1}
\]

This retains every entry in (13.1).

For (k\notin A\), let \(\sigma_{A,k}(t)\) be the actual profile in which
the members of (A) Quit at date zero, player (k) Quits at date zero
with probability (t\), and every other clock is Never. All clocks are Never
after date zero. If (A\ne\varnothing\), termination occurs at date zero
surely. Hence the unrestricted cap of every player is the maximum of its two
date-zero endpoints. If (A=\varnothing\), an unrestricted pure response is
equivalent to Quit at date zero, Quit at a positive date, or Never; these are
the three affine values used below.

Thus (D(\sigma_{A,k}(t))\) is a sum of maxima of finitely many affine
functions. Its minimum is attained at an endpoint or at an intersection of
two of those functions. Direct exact evaluation gives the following minima;
each row lists (A:\min_{t\in[0,1]}D(\sigma_{A,k}(t))\).

\[
\begin{array}{c|l}
k=0&0:4,\ 2:2,\ 4:6,\ 6:3,\ 8:3,\ 10:2,\ 12:7,\ 14:3\\
k=1&0:3,\ 1:2,\ 4:19/8,\ 5:58/5,\ 8:5/2,\ 9:2,
      \ 12:9/4,\ 13:32/5\\
k=2&0:4,\ 1:57/8,\ 2:3,\ 3:2,\ 8:21/8,\ 9:25/4,
      \ 10:3,\ 11:2\\
k=3&0:3,\ 1:22/3,\ 2:5/2,\ 3:2,\ 4:6,\ 5:31/3,
      \ 6:3,\ 7:76/9.
\end{array}
\tag{15.2}
\]

Consequently

\[
 D(\sigma_{A,k}(t))\ge2
 \qquad\text{for every }A,k,t.
\tag{15.3}
\]

The pure profiles also contain a literal max-debt full-response cycle:

\[
 6\xrightarrow{,2:2,}2
 \xrightarrow{,3:3,}10
 \xrightarrow{,1:5,}8
 \xrightarrow{,2:3,}12
 \xrightarrow{,3:7,}4
 \xrightarrow{,1:6,}6.
\tag{15.4}
\]

The label above an arrow is mover:gain. Every edge is an unrestricted full
behavioral best response: at least one unchanged opponent Quits surely at
date zero, so no later clock can improve upon the better date-zero endpoint.
Every target has the next R-obstruction in (15.4), and every literal
post-date tail is all Never. Hence an attempted literal cyclic Bellman shadow
also has the S-obstruction.

This proves that imposing global minimality on all vertices and all
one-coordinate faces of the finite pure-root cube still does not orient the
R/S dual. The regression is now one actual rational reward table rather than
a partial local passport.

## 16. The genuinely global constraint enters in higher-dimensional mixtures

Table (15.1) is not a positive-global-minimum counterexample. The missing
carrier quantifier can already be seen at one simultaneous product root.
Let the date-zero Quit probabilities be

\[
 q=(1/20,\ 1/2,\ 2/5,\ 1/2),
\]

followed by all Never. Exact unrestricted payoff and cap evaluation gives

\[
 U=(993/400,\ 1009/400,\ 217/100,\ 281/100),
\]

\[
 B=(11/4,\ 561/200,\ 199/80,\ 61/20),
\]

and therefore

\[
 d=(107/400,\ 113/400,\ 127/400,\ 6/25),
 \qquad D=443/400<2.
\tag{16.1}
\]

For each player the displayed cap is attained by Quit at the next positive
date after surviving date zero; against these opponents the complete pure
response class is exactly Quit at zero, Quit later, or Never. Thus (16.1) is
an exact behavioral calculation, not a stationary or finite-grid lower
bound.

After scaling (15.1) by (1/7), it is a valid input to the exact-search
reward box. The profile in (16.1) then has maximum exploitability
(127/2800). This immediately rejects the table as a positive-gap candidate
at the benchmark (2/7).

The finite conclusion is sharp:

\[
\boxed{
\begin{array}{c}
\text{pure coalitions + every one-player interpolation}\
\text{+ an exact paid response cycle + atomic R/S duals}
\end{array}
\not\Longrightarrow
\text{positive global minimum}.}
\tag{16.2}
\]

The additional datum is not another source label. It is minimum control on
genuinely simultaneous multi-player product mixtures (and ultimately on the
full behavioral carrier). For this exact table, simultaneous mixing combines
the individually safe coordinate directions into a lower-debt profile.

This suggests a narrower positive route: show that any stabilized R/S dual
arising from the actual positive-minimum source can be combined into a
multi-coordinate product perturbation whose debt falls below (D_*). The
present computation demonstrates that mechanism but does not prove it for an
arbitrary source cycle.
