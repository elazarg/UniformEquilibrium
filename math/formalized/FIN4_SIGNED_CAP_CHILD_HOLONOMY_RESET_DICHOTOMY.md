# A persistent cap child has either a shifted cap or negative payoff holonomy

Authors: CODEX_SPINOZA

Independent reviews:
[CODEX_GROMOV](../feedback/CODEX_SPINOZA__SIGNED_CAP_CHILD_HOLONOMY_AND_RESET_DICHOTOMY__BY_CODEX_GROMOV.md)
and
[CODEX_HAHN](../feedback/CODEX_SPINOZA__SIGNED_CAP_CHILD_HOLONOMY_AND_RESET_DICHOTOMY__BY_CODEX_HAHN.md).

## Exact statement

Let \(I=\operatorname{Fin}4\), let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a bounded quitting reward table, and choose \(M>0\) such that
\(|r_i(S)|\le M\) for every terminal coalition and player. Never pays zero.
Behavioral randomizations are independent across players and dates
conditional on public survival.

Suppose actual profiles \(\tau^n\), exact independent product roots \(q^n\),
and literal cap children \(\zeta^n\) satisfy

\[
 \tau^{n+1}=q^n::\tau^n,\qquad
 \zeta^{n+1}=\bar q^n::\zeta^n,                              \tag{1}
\]

where \(\bar q^n\) is obtained from \(q^n\) by forcing one fixed player
\(b\) to Continue and retaining every outsider marginal. Write

\[
 U^n=U(\tau^n),\qquad W^n=U(\zeta^n),\qquad
 \Delta_i^n=W_i^n-U_i^n,                                    \tag{2}
\]

\[
 h_{n,i}=q_i^n,\qquad
 \bar c_n=\prod_{i\ne b}(1-h_{n,i}).                         \tag{3}
\]

Assume:

1. \(q^n\) is exact root Nash against \(U^n\);
2. every root has positive joint Continue probability;
3. the total marginal hazard is summable:

   \[
    \sum_n\sum_i h_{n,i}<\infty;                             \tag{4}
   \]

4. player \(b\) Quits surely by date \(n\) in every \(\zeta^n\); and
5. for one fixed outsider \(j\ne b\), one depth \(R\), and one
   \(\delta>0\),

   \[
    d_j(\zeta^n)\ge\delta\qquad(n\ge R).                     \tag{5}
   \]

Then the following statements hold.

### Exact affine recurrence and finite total variation

Let \(\mu_n(S)\) be the probability that the set of quitting outsiders
\(I\setminus\{b\}\) is exactly \(S\) under their common marginals.
For every outsider \(i\ne b\),

\[
 \boxed{
 \Delta_i^{n+1}
 =\bar c_n\Delta_i^n+h_{n,b}G_{n,i},}                        \tag{6}
\]

where

\[
\begin{aligned}
G_{n,i}
={}&\bar c_n\bigl(U_i^n-r_i(\{b\})\bigr)\\
 &+\sum_{\varnothing\ne S\subseteq I\setminus\{b\}}
   \mu_n(S)\bigl(r_i(S)-r_i(S\cup\{b\})\bigr).
                                                                    \tag{7}
\end{aligned}
\]

One has

\[
 |G_{n,i}|\le4M                                             \tag{8}
\]

and

\[
 |\Delta_i^{n+1}-\Delta_i^n|
 \le2M(1-\bar c_n)+4Mh_{n,b}.                               \tag{9}
\]

Consequently,

\[
 \sum_n|\Delta_i^{n+1}-\Delta_i^n|<\infty,                  \tag{10}
\]

so \(\Delta_i^n\) converges to a finite limit
\(\Delta_i^\infty\). Its exact signed representation from depth \(R\) is

\[
 \Delta_i^\infty
 =\left(\prod_{n\ge R}\bar c_n\right)\Delta_i^R
  +\sum_{k\ge R}h_{k,b}G_{k,i}
       \left(\prod_{n>k}\bar c_n\right).                     \tag{11}
\]

### Coherent outsider caps

Since \(b\) Quits surely by date \(n\), every outsider cap at \(\zeta^n\)
is attained among

\[
 \{0,1,\ldots,n,\operatorname{Never}\}.
\]

Caps for the fixed player \(j\) may be selected coherently so that their
pure times satisfy

\[
 T_{n+1,j}\in\{0,T_{n,j}+1\},                                \tag{12}
\]

where \(\operatorname{Never}+1=\operatorname{Never}\). Call the first branch
a reset and the second a shift.

Exactly one of the following holds.

1. Only finitely many resets occur. After the last reset, one fixed old
   complete cap is shifted through every later root. This includes the
   permanent-Never subcase.
2. Resets occur at arbitrarily large depths. Then

   \[
    \boxed{\Delta_j^\infty\le-\delta/2<0.}                   \tag{13}
   \]

Thus infinite front cap resets force a fixed negative cross-coordinate
payoff holonomy; they do not approach a source return.

## Conjecture-facing change

The reviewed nested-child theorem reduces the positive-survival exact-cap
branch to one literal child genealogy with one fixed outsider debtor. Its
remaining outsider root-Nash comparison contains the cross-coordinate
displacement \(\Delta_i^n\), which was previously uncontrolled.

This theorem replaces that uncontrolled sequence by an exact
finite-total-variation object and gives a signed exhaustive alternative for
the fixed debtor. Either one old finite/Never cap remains attached at the far
end forever, or cofinal Quit0 resets force the explicit negative limit (13).

Relative to
[FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md](../questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md),
the open obligation is now smaller: consume a shifted two-label far-end cap,
or turn the negative holonomy into a source-compatible Nash
re-equilibration. The theorem itself proves neither consumer.

## Definitions and assumptions

For an actual profile \(\sigma\),

\[
 B_i(\sigma)=\sup_{\beta_i}
 U_i(\sigma[i\leftarrow\beta_i]),\qquad
 d_i(\sigma)=B_i(\sigma)-U_i(\sigma),
\]

with the supremum over all unilateral behavioral strategies, including
calendar-dependent randomization, every finite pure stopping time, and
literal Never.

For player \(i\), let

\[
 Q_i(q_{-i})
\]

be its payoff from Quit at the current root, and write its Continue endpoint
as

\[
 C_i(q_{-i};v_i)=H_i(q_{-i})+s_i(q)v_i,
\]

where \(H_i\) is the absorbing reward contribution and \(s_i(q)\) is
opponent Continue probability.

The profile identity for the children in (1) is literal, not semantic. The
roots \(\bar q^n\) are obtained by changing only \(b\)'s current marginal and
the attached \(b\)-tail. They are Bellman-exact for \(W^n\), but outsider
root Nash is not assumed.

In the arbitrary-game adapter, (4) is forced by checked bounded finite
exact-block capacity, and (5) is forced by transporting one terminal-gap
observer through the nested child genealogy.

## Source correspondence

The direct source is the reviewed theorem
[FIN4_NESTED_TERMINAL_CAP_CHILD_FIXED_DEBTOR_TRANSPORT.md](FIN4_NESTED_TERMINAL_CAP_CHILD_FIXED_DEBTOR_TRANSPORT.md).
It supplies the literal identities (1), positive product, fixed outsider, and
(5) with

\[
 \delta=C_\infty\Gamma>0.
\]

That theorem is derived from the positive-survival source chain
[FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT.md](FIN4_TROPICAL_TWO_NEVER_TO_OFFMINIMUM_PAID_PORT.md),
[FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE.md](FIXED_CAP_PIN_APPROXIMATE_ROOT_DEBT_EXPENDITURE.md),
and
[FIN4_FIRST_EXACT_ROOT_SURVIVAL_OR_UNIQUE_SURE_RESET.md](FIN4_FIRST_EXACT_ROOT_SURVIVAL_OR_UNIQUE_SURE_RESET.md).

The exact positive-survival cap-clock and capacity proof is Section 10 of
[CODEX_SPINOZA__RECURSIVE_LITERAL_U_ROOT_PREFIX_LEDGER_AND_STALL.md](../notes/CODEX_SPINOZA__RECURSIVE_LITERAL_U_ROOT_PREFIX_LEDGER_AND_STALL.md),
frozen at reviewed SHA-256
3823bb3e816de7d3328b0a82045dae42daae9f3cd3a937b7b50bf7a3370052ee.

The reviewed source for the new theorem is
[CODEX_SPINOZA__SIGNED_CAP_CHILD_HOLONOMY_AND_RESET_DICHOTOMY.md](../notes/CODEX_SPINOZA__SIGNED_CAP_CHILD_HOLONOMY_AND_RESET_DICHOTOMY.md),
frozen at SHA-256
29e0bc853b0ff979e3295655a78ef7df83711de22f5ecceb9cb7bc94ee172ed7.
The independent reviews above reconstructed the affine recurrence, the
finite-total-variation argument, coherent cap selection, the reset sign, and
the nonconsumer.

## Proof

### Affine displacement recurrence

Fix \(i\ne b\). Couple \(q^n\) and \(\bar q^n\) by retaining every outsider
action and changing only \(b\)'s Bernoulli action from Quit probability
\(h_{n,b}\) to pure Continue.

If the quitting outsider set is nonempty \(S\), the child law pays
\(r_i(S)\), while the original law mixes \(r_i(S)\) with
\(r_i(S\cup\{b\})\). If no outsider Quits, the child law continues to
\(W_i^n\), while the original law mixes continuation to \(U_i^n\) with the
singleton outcome \(\{b\}\). Subtracting the two Bellman values gives exactly
(6)--(7).

Every prescribed terminal payoff belongs to \([-M,M]\). Each difference in
(7) has absolute value at most \(2M\), so (8) follows. Subtract
\(\Delta_i^n\) from (6):

\[
 \Delta_i^{n+1}-\Delta_i^n
 =-(1-\bar c_n)\Delta_i^n+h_{n,b}G_{n,i}.
\]

Since \(|\Delta_i^n|\le2M\), this proves (9). The union bound gives

\[
 1-\bar c_n\le\sum_{i\ne b}h_{n,i}.
\]

Both right-hand series in (9) are summable by (4), proving (10). Unrolling
(6), then passing to the limit using absolute convergence and the positive
tail products, proves (11).

This proves finite total variation of the displacement increments. It does
not prove summability of the displacement values.

### Recursive cap selection

Fix \(n\). Because \(b\) Quits surely by date \(n\), all outsider pure times
strictly after \(n\) are outcome-equivalent to Never. Behavioral
pure-time extremality therefore makes the complete cap a maximum over the
displayed finite set.

At the new root of \(\zeta^{n+1}=\bar q^n::\zeta^n\), a pure response either
Quits immediately, or Continues and then uses a response in \(\zeta^n\).
The best value in the latter class is attained by a selected old cap. Choose
a maximizing branch and its corresponding time. This gives (12). Finitely
many resets give the eventual-shift arm, including permanent Never.

### The sign at infinitely many resets

Suppose resets occur infinitely often. Define the old and child
Quit-minus-Continue gaps

\[
 E_n^{\rm old}
 =Q_j(q^n_{-j})-C_j(q^n_{-j};U_j^n),
\]

\[
 \bar E_n
 =Q_j(\bar q^n_{-j})-C_j(\bar q^n_{-j};W_j^n).               \tag{14}
\]

Positive joint Continue probability gives \(h_{n,j}<1\). Exact Nash of
\(q^n\) therefore gives

\[
 E_n^{\rm old}\le0.                                         \tag{15}
\]

At a reset, Quit now attains the child cap, and the prescribed own root
marginal is still \(h_{n,j}\). Hence

\[
 d_j(\zeta^{n+1})=(1-h_{n,j})\bar E_n.                       \tag{16}
\]

By (5),

\[
 \bar E_n\ge\delta.                                          \tag{17}
\]

Put

\[
 \bar s_{n,j}=\prod_{\ell\ne b,j}(1-h_{n,\ell}).
\]

Directly subtracting the two endpoint gaps gives

\[
 \bar E_n-E_n^{\rm old}
 =-\bar s_{n,j}\Delta_j^n+R_n,                               \tag{18}
\]

where coupling the Quit endpoint, the Continue absorbing numerator, and the
continuation coefficient yields

\[
 |R_n|\le6Mh_{n,b}.                                         \tag{19}
\]

Equations (15), (17), and (18) imply, at every reset,

\[
 -\bar s_{n,j}\Delta_j^n
 \ge\delta-6Mh_{n,b}.                                       \tag{20}
\]

Summability in (4) gives \(h_{n,b}\to0\) and
\(\bar s_{n,j}\to1\). At every sufficiently late reset,
\(\Delta_j^n\le-\delta/2\). There are infinitely many such indices, while
(10) makes the full sequence converge. Therefore
\(\Delta_j^\infty\le-\delta/2\), proving (13).

## Boundary tests

### Finite total variation does not make the root-Nash seam summable

For outsider \(i\), exact endpoint subtraction between \(q^n\) and
\(\bar q^n\) contains

\[
 -\bar s_{n,i}\Delta_i^n+O(Mh_{n,b}).
\]

The \(O(Mh_{n,b})\) term is summable, but
\(\bar s_{n,i}\to1\). If \(\Delta_i^\infty\ne0\), the root-Nash seam does not
even tend to zero. Thus (10) controls increments, not the Nash errors.

### A zero limit still need not give a summable chronology

The scalar pattern

\[
 h_{n,b}\asymp n^{-2},\qquad
 \Delta_i^n\asymp n^{-1}
\]

has summable increments and zero limiting displacement, but the displacement
values are not summable. This is a falsifier of the scalar inference only,
not a claimed positive-gap quitting table. A sparse subsequence can make the
values summable, but the literal block between selected depths contains every
skipped root and every intermediate seam.

### The reset sign is forced

At a reset with positive debt, Quit is above the child prescribed Continue
endpoint. At the old exact root, Quit is no better than Continue. Removing
\(b\)'s current Quit probability changes the current-row terms only by
\(O(Mh_{n,b})\). The remaining order-one sign is therefore
\(-\Delta_j^n>0\), exactly as quantified in (20).

### The two outputs are not return objects

An eventual shifted cap is a response at the far end of a block, not a
persistent marginal hazard on an accepted spine. A negative limit is a
macroscopic payoff externality, not equality of source and endpoint
semantics.

## Adapter and consumer

The reviewed nested-child packet supplies all hypotheses, including one
fixed player \(j\) and the fixed floor \(\delta=C_\infty\Gamma\). Checked
bounded capacity supplies (4). No label or source is selected independently
at later depths.

The theorem strictly replaces an arbitrary cross-coordinate seam by:

\[
 \boxed{
 \text{eventually shifted finite/Never cap}
 \quad\text{or}\quad
 \Delta_j^\infty\le-\delta/2.}
\]

No named existing consumer accepts either output directly. The shifted cap
remains at an escaping far-end suffix. The negative-holonomy branch produces
cofinally many literal Quit0 cap sources with a fixed gain, but their roots
\(\bar q^n\) are not known Nash for outsiders. Strict-toggle and paid-port
dispatches retain the horizontal response but do not supply the missing
source-compatible Nash re-equilibration.

## Lean handoff

A narrow formalization should separate three declarations.

1. FinFourNestedCapChildren.payoffDisplacement_recurrence: prove (6)--(9) by
   conditioning on \(b\)'s root action.
2. FinFourNestedCapChildren.payoffDisplacement_summable_increment: combine
   (9) with the marginal-hazard sum to obtain (10)--(11).
3. FinFourNestedCapChildren.shiftedCap_or_negativeHolonomy: choose caps by
   (12), prove the reset debt identity (16), establish the explicit remainder
   bound (19), and derive (13).

The formal theorem should distinguish \(\bar c_n\), which includes \(j\)'s
Continue probability, from \(\bar s_{n,j}\), which is opponent Continue mass
for \(j\). It should state summability of
\(|\Delta_i^{n+1}-\Delta_i^n|\), not of \(|\Delta_i^n|\).

The cap selection must retain Never as a fixed point of shifting. No structure
field should assume that \(\bar q^n\) is Nash for outsiders or that the
negative limit is a semantic return.

## Scope and nonclaims

This is reviewed ordinary mathematics, not yet Lean-checked.

The result proves an exact affine recurrence, finite total variation, and the
eventual-shift versus negative-holonomy dichotomy. It does not prove
summability of the displacement values or of outsider root-Nash defects.

It does not turn the shifted cap into a finite-date persistent hazard, turn
negative holonomy into debt descent, preserve root Nash after the owner cap
update, or construct a source return.

No terminal approximate Nash profile, accepted exact/approximate
Nash--Bellman spine, renewable decreasing rank, or uniform-equilibrium payoff
is proved.
