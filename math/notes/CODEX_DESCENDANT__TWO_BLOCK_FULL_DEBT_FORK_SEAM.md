# Two-block full-debt fork test: the first cap seam and the zero-charge barrier

Identity: `CODEX_DESCENDANT`  
Status: ordinary mathematics; exact one-root seam formula and exact Fin4
two-response regression; literal iterated-response obstruction; no full-debt
consumer

## 1. Question

Start with the strongest full-debt input presently available: an actual
profile $X$, a legal one-player stopping-law fork $X\to Y$, a fixed
positive payoff gain, and a finite first-disagreement row reached with a
fixed positive joint probability.  Suppose a finite exact cap--Nash word was
available above $X$.

Can one use $Y$ as the literal source of a second fork while retaining an
exact positive-charge block?  The two-step test separates three operations:

1. the horizontal response $X\to Y$;
2. the exact prefix root above the literal successor $Y$; and
3. a second horizontal response selected from $Y$ or its exact prefix.

The result below identifies the first noncommuting field exactly.  Raising a
target cap creates a Nash error on precisely the old binding Quit mass.  If
fresh exactification instead selects all Continue, arbitrarily many literal
successor blocks exist but all carry zero absorption.  The paid row is still
not one of those exact blocks.

## 2. Exact first-seam formula

Let $x$ be a product root, let $b,b'\in\mathbb R^I$ be two continuation
caps, and fix a player $j$.  Put

\[
 H_j(x)=\prod_{k\ne j}x_k(C),\qquad
 \Delta_j=b'_j-b_j,
\]

and let

\[
 E_j(b,x)=Q_j(x_{-j})-C_j(x_{-j};b_j)
\]

be the Quit-minus-Continue endpoint difference.  Quit payoffs do not depend
on the continuation cap, while the Continue endpoint is affine in its own
cap coordinate.  Hence

\[
 \boxed{E_j(b',x)=E_j(b,x)-H_j(x)\Delta_j.}
 \tag{2.1}
\]

Write $c_j=x_j(C)$ and $q_j=x_j(Q)$.  The exact coordinate Nash defect is

\[
 \delta_j(b,x)
 =c_j(E_j(b,x))_+ + q_j(-E_j(b,x))_+ .
 \tag{2.2}
\]

Consequently, if $x$ is exact against $b$, $0<q_j<1$, and
$\Delta_j>0$, complementarity gives $E_j(b,x)=0$, so

\[
 \boxed{\delta_j(b',x)=q_jH_j(x)\Delta_j.}
 \tag{2.3}
\]

Thus a positive cap rise is not merely a qualitative threat to the old
root.  Its exact first seam is the cap rise multiplied by the root mass on
the now-worse Quit action and by the opponents' Continue mass.

For a pure-Quit binding coordinate the corresponding formula is

\[
 \delta_j(b',x)=\bigl(H_j(x)\Delta_j-E_j(b,x)\bigr)_+,
 \tag{2.4}
\]

while a pure-Continue coordinate remains Nash under a nonnegative cap rise.
Therefore no lower bound follows from $\Delta_j>0$ alone: the affected
coordinate may Continue surely.  Conversely, whenever the old exact charge
uses a mixed affected coordinate, (2.3) is the exact price of retaining that
root.

More generally, at a mixed exact coordinate the signed formula is

\[
 \boxed{
 \delta_j(b',x)=
 q_jH_j(x)(\Delta_j)_+
 +c_jH_j(x)(-\Delta_j)_+.}
\tag{2.3a}
\]

This polarity matters in the vanishing-absorption branch.  If
$x_n\to\mathbf C$, then $q_{j,n}\to0$, while $c_{j,n},H_j(x_n)\to1$.
Therefore a fixed positive cap displacement creates vanishing old-root
error, but a fixed negative displacement creates an order-one error:

\[
 \Delta_j>0\Longrightarrow \delta_j(b',x_n)\to0,
 \qquad
 \Delta_j<0\Longrightarrow
 \delta_j(b',x_n)\to-\Delta_j.
\tag{2.3b}
\]

Thus small root absorption can amortize cap **rises**, because only the old
Quit mass is exposed.  It cannot amortize cap **falls**, because the old
Continue mass tends to one.  A late summable exact ray can transport a
coordinatewise cap-nondecreasing fork with root errors charged to its tail
absorption, but an order-one negative cap displacement is a macroscopic first
seam even arbitrarily deep in the ray.

Equations (2.1)--(2.3) are direct consequences of
`quittingRootContinuePayoff_update_add` and
`quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart`.

## 3. The literal successor and the second fork

Let $p$ be an exact root against $B(X)$, and form the two actual profiles

\[
 \widehat X=p\star X,\qquad \widehat Y=p\star Y.
 \tag{3.1}
\]

The literal successor after the first row of $\widehat Y$ is exactly $Y$.
The source fork remains behind the same root.  But $p$ is an exact first
block for $\widehat Y$ if and only if every coordinate seam such as
(2.2) vanishes at $B(Y)$.  In particular (2.3) makes retention impossible
when a cap-rising spectator was mixed at the old root.

If the seam vanishes, $Y$ is full debt, and $s(p)>0$, exact prefix scaling
gives

\[
 d_i(\widehat Y)=s(p)d_i(Y)>0.
 \tag{3.2}
\]

In the intended positive-global-minimum setting, the survival condition is
automatic after exactness has been established: the prefixed point is in the
carrier, so

\[
 D_*\le D(p\star Y)=s(p)D(Y).
 \tag{3.2a}
\]

Since $D_*>0$, this forces $s(p)>0$.  This argument is unavailable in the
$D_*=0$ regression below.

The actual-reach fork theorem may therefore be applied again to the literal
profile $\widehat Y$.  This does not yet give two chronological paid blocks.
The second output is another unilateral comparison $\widehat Y\to Z$, not a
root--successor edge.

There is an important specification boundary here.  A
`QuittingPaidFirstDisagreementRow` compares two complete pure-time
counterfactuals on the receiving profile.  It does **not** by itself say that
the receiving profile assigns positive probability to the worse action at
the marked root.  Thus it does not automatically instantiate
`QuittingLiteralPositiveActualRowPacket`, and one may not infer

\[
 \operatorname{gain}=L\,\operatorname{Def}.
 \tag{3.3}
\]

That equality is available only when the selected comparison is also the
literal best-endpoint update of the prescribed marked row.  Two cases are
therefore possible.

* A full best response may make the mover's marked action exact and kill its
  debt.  Then the full-debt hypothesis needed to rerun the same chamber
  producer has already been lost.
* A small radial/partial fork can retain full debt.  In that case the target
  generally still assigns positive mass to the worse marked action.  Its
  exact marked-row defect is given by (2.2), and the row is not an exact
  Nash--Bellman edge unless that weighted defect vanishes.

For a sequence of fresh maximal exactifications at $B(Y_n)$, three cases must
be kept separate.  A cofinal uniform positive absorption floor gives the
quantitative charged arm.  Pointwise positive absorptions tending to zero
belong to the vanishing-response maximal-root/reset/off-minimum reduction and
are not consumed merely by positivity.  Exact zero absorption means that the
only exact product root is all Continue.

In the last case the exact prefix has literal successor $Y$, preserves the
complete semantic pair, and has zero absorption.  Repeating it gives as many
extension-compatible rows as desired, but

\[
 \sum_t \operatorname{Abs}(\mathbf C)=0.
 \tag{3.4}
\]

The second fork can be shifted behind these rows because the source profile
is retained literally as the suffix.  This does not turn the horizontal
comparison into a root--successor edge: the exact rows before it have zero
charge, while the marked row is exact only if its prescribed action already
passes the weighted test (2.2).  Thus two consecutive iterations expose a
sharp alternative, not a capacity contradiction:

\[
\boxed{
\begin{array}{l}
\text{retain a positive-absorption old root and pay the explicit cap seam,}\\
\text{or re-exactify by all Continue and retain ancestry with zero charge,}\\
\text{or change the paid root/tail fibre.}
\end{array}}
\tag{3.5}
\]

The third arm is precisely the still-missing commuting seam.

## 4. Two inert iterations in the positive-minimum tube

The maintained positive-minimum architecture itself permits two successive
forks without leaving the inert tube.  This is stronger than the numerical
regression in Section 5.

Let $X_n$ be the actual source sequence converging to a full-debt minimum,
and suppose

\[
 d_i(X_n)\ge\delta>0
 \qquad(i\in\operatorname{Fin}4)
\tag{4.1}
\]

eventually.  Let $T$ be an open cap neighborhood of the limiting cap on
which all Continue is the unique exact product root.  The common-prefix fork
gives a legal full response $F_n$ from $X_n$.  Mix only a fixed sufficiently
small fraction $\lambda_1>0$ of that response into the mover's prescribed
stopping law, and call the actual target $Y_n^1$.

If the source joint law has a fixed positive atom $\mu(S)=m>0$, joint-law
convergence gives source mass at least $m/2$ eventually.  A one-player radial
mixture changes the probability of any fixed terminal outcome by at most its
mixing weight.  The two weights below may therefore also be chosen with
$\lambda_1+\lambda_2<m/4$.  Both inert targets then retain positive mass at
the same terminal $S$.  This is source-attached time-forgetting law
provenance; it is not a marked causal row.

Unilateral total-variation transport bounds every cap change by
$2M\lambda_1$ and every debt change by $4M\lambda_1$.  Choose
$\lambda_1$ so that, eventually,

\[
 B(Y_n^1)\in T,
 \qquad d_i(Y_n^1)\ge\delta/2\quad(i<4).
\tag{4.2}
\]

The first target is therefore still full debt, and its unique fresh exact
root is all Continue.

Now apply the actual-reach profitable-fork theorem directly to the literal
profiles $Y_n^1$.  With the uniform debt floor $\delta/2$, after fixing a
mover on a subsequence it gives a full response with a uniform positive gain
and a uniform positive actual-joint-reach floor.  Mix a sufficiently small
fixed fraction $\lambda_2>0$ of this second response, and call its target
$Y_n^2$.  The same transport estimates, with $\lambda_2$ chosen inside the
remaining cap-tube and debt margins, give

\[
 B(Y_n^2)\in T,
 \qquad d_i(Y_n^2)>0\quad(i<4).
\tag{4.3}
\]

Thus

\[
 X_n\longrightarrow Y_n^1\longrightarrow Y_n^2
\tag{4.4}
\]

is a pair of legal, positive-gain, actually reached stopping-law comparisons
in which the first target is literally the second source and both targets
remain full debt.  Yet fresh maximal-root exactification at both target caps
selects only all Continue and contributes zero absorption.

This proposition does not make the two horizontal arrows in (4.4)
chronological.  It proves that merely asking for two literal
target-to-source iterations does not force a commuting exact block, even in
the positive-minimum source architecture, and even while the same positive
terminal-law atom remains visible.  Any successful two-block theorem must
causalize and strategically use that atom to change the root--tail fibre, or
must extract charge from the cap seam itself.  Positivity of the
time-forgetting law coordinate alone does not suffice.

## 5. Exact Fin4 two-response regression

The following table shows that literal target-to-source iteration of the
fork, full debt, unit reach, and conservative debt transfer can occur twice
while every fresh target root is uniquely all Continue.  The table has
global minimum zero, so it is a local field-independence regression rather
than a counterexample.

Use players $i,j,k,\ell$.  Define two mover coordinates by

\[
 r_i(S)=\mathbf 1_{i\notin S},\qquad
 r_k(S)=\mathbf 1_{k\notin S},
\tag{5.1}
\]

and two spectator coordinates by

\[
 r_j(S)=
 \begin{cases}
 0,&j\in S,\\
 1,&j\notin S, i\in S,\\
 2,&j\notin S, i\notin S,
 \end{cases}
\qquad
 r_\ell(S)=
 \begin{cases}
 0,&\ell\in S,\\
 1,&\ell\notin S, k\in S,\\
 2,&\ell\notin S, k\notin S.
 \end{cases}
\tag{5.2}
\]

At date zero everyone Continues.  At date one let all four players Quit
surely.  Call this profile $X_0$.  Then

\[
 U(X_0)=0,\qquad B(X_0)=(1,1,1,1),\qquad d(X_0)=(1,1,1,1).
\tag{5.3}
\]

For $0<\lambda<1$, change only player $i$'s date-one action so that it
Continues with probability $\lambda$.  Call the target $X_1$.  Direct
calculation gives

\[
 U(X_1)=(\lambda,0,0,0),
\]

\[
 B(X_1)=(1,1+\lambda,1,1),
\]

\[
d(X_1)=(1-\lambda,1+\lambda,1,1),\qquad D(X_1)=4.
\tag{5.4}
\]

The mover gains $\lambda$, the spectator $j$'s cap and debt rise by
$\lambda$, every debt remains positive, and the changed row has joint
reach one.

At the target marked row, mover $i$'s Quit endpoint is zero and its
Continue endpoint is one.  Since the target still assigns Quit probability
$1-\lambda$, its literal marked-row coordinate defect is exactly

\[
 1-\lambda>0.
\tag{5.4a}
\]

Now fix $0<\theta<1$ and, starting from the literal target $X_1$, change
only player $k$'s date-one action so that it Continues with probability
$\theta$.  Call the target $X_2$.  Then

\[
 U(X_2)=(\lambda,0,\theta,0),
\]

\[
 B(X_2)=(1,1+\lambda,1,1+\theta),
\]

and

\[
 d(X_2)=
 (1-\lambda,1+\lambda,1-\theta,1+\theta),
 \qquad D(X_2)=4.
\tag{5.5}
\]

Thus the second mover gains $\theta$, spectator $\ell$'s cap/debt rises by
the same amount, all debts remain positive, and the second fork again has
joint reach one.  The first target is literally the second source.  The
second target's marked-row coordinate defect for mover $k$ is exactly
$1-\theta>0$.

Against $B(X_1)$ and $B(X_2)$, Continue strictly dominates Quit
for every player at every product root.  For $i,k$, Quit always gives zero
and Continue gives one whenever an opponent absorbs and gives cap one at all
Continue.  For $j,\ell$, Quit always gives zero, while Continue gives at
least one on opponent absorption and its strictly positive displayed cap at
all Continue.  Hence all Continue is the unique exact product root at both
target caps.

Fresh exactification after each legal response therefore yields only the
zero-absorption all-Continue prefix.  The two response operations are real,
source-compatible, positively reached, positive-gain forks, but they are
horizontal comparisons at the same terminal row.  They are not two positive
Nash--Bellman blocks.

Finally, this table has $D_*=0$: at all Never, every singleton reward is
zero, so every cap and prescribed payoff is zero.  The regression proves
only that all local two-step fields above are insufficient.  A positive
theorem must use positive-global-minimum provenance to rule out this exact
configuration or must build the missing fibre-changing connector.

## 6. Consequence

The strongest full-debt actual-reach fork can be iterated as an operation on
actual profiles.  Two iterations do not guarantee even one positive exact
chronological block.  The failure is no longer an unspecified ancestry loss:

* if an old binding quitter sees a cap rise, (2.3) is the exact first seam;
* if fresh target roots are uniquely all Continue, literal successors are
  preserved but exact-block capacity does not increase; and
* a full response can kill the mover debt and leave the full-debt chamber,
  while a partial response that retains full debt can retain a positive
  marked-row defect, as the regression shows.

Therefore bounded exact-block capacity can close this route only after a
new theorem charges or eliminates the first seam, or changes the paid
root/tail fibre while preserving a positive fraction of the actual reach.
In particular, the vanishing-root residual has an exact signed refinement:
either the fork is asymptotically cap-nondecreasing and the old roots have
absorption-priced transport error, or some coordinate has a negative cap
seam which does not shrink with root absorption.  Positive global minimum
and the hard-residual source law are the only available hypotheses not
represented in the finite regression.

## 7. Two consecutive full responses at a positive minimum

There is one genuinely source-compatible two-step construction which does
not use root exactification.  It sharpens the obstruction from “the first
target may not be the second source” to an exact cap/law reactivation.

Let actual profiles $X_n^0$ converge jointly in terminal semantics and law to
a global minimum point $x^0$ with full positive-debt support.  Choose a
maximal-debt player $p$, pass to a subsequence fixing it, and replace only
$p$ by an $o(1)$-best behavioral response.  Denote the literal targets by
$X_n^1$.  Then

\[
 U_p(X_n^1)-U_p(X_n^0)\longrightarrow d_p(x^0)\ge D_*/4,
 \qquad d_p(X_n^1)\longrightarrow0.
 \tag{7.1}
\]

If every target cluster is off the minimum fibre, this is already the
source-attached off-minimum paid-port arm.  Otherwise select a minimum cluster
$x^1$.  Since $d_p(x^1)=0$ and $D(x^1)=D_*$, some fixed player $q\ne p$
has

\[
 d_q(x^1)\ge D_*/3.
 \tag{7.2}
\]

Now apply an $o(1)$-best response of $q$ to the **literal profiles
$X_n^1$**, not to an unrelated realizer of $x^1$, and call the targets
$X_n^2$.  Thus the first target is definitionally the second source, and

\[
 U_q(X_n^2)-U_q(X_n^1)\longrightarrow d_q(x^1)\ge D_*/3,
 \qquad d_q(X_n^2)\longrightarrow0.
 \tag{7.3}
\]

Again an off-minimum cluster is a paid-port exit.  Suppose instead that a
selected cluster $x^2$ remains on the minimum fibre.  There are two cases.

### 7.1 Two zeros survive

If $d_p(x^2)=0$, then

\[
 \{p,q\}\subseteq\{i:d_i(x^2)=0\}.
 \tag{7.4}
\]

The positive-debt support has cardinality at most two, a strict drop from the
full support of $x^0$.  Because both replacements were performed on the
literal preceding target sequence, this is not merely a comparison of three
abstract minimum points.  The actual sequence $X_n^2$, its joint-law cluster,
and the two complete response passports are retained.  To reconstruct a
complete Fin4 minimum source at this cluster one must still invoke the
hard-residual positive-finite-atom theorem there and causalize this **same**
literal replacement sequence.  Without those explicit source adapters, the
unconditional output here is a support-at-most-two minimum joint-law cluster
with literal response ancestry, not a regenerated source node.

### 7.2 Exact aggregate leakage and a fixed recipient

No lower bound on reactivation of the particular player $p$ follows.  The
correct quantitative statement uses the entire conservative transfer.  Since
$D(x^1)=D(x^2)=D_*$ and $d_q(x^2)=0$,

\[
 \sum_{i\ne q}\bigl(d_i(x^2)-d_i(x^1)\bigr)
 =d_q(x^1)\ge D_*/3.
 \tag{7.5}
\]

Therefore some fixed recipient $h\ne q$ satisfies

\[
 d_h(x^2)-d_h(x^1)\ge D_*/9.
 \tag{7.6}
\]

For this recipient the exact debt identity is

\[
 d_h(x^2)-d_h(x^1)
 =\bigl(B_h(x^2)-B_h(x^1)\bigr)
  +\bigl(U_h(x^1)-U_h(x^2)\bigr).
 \tag{7.7}
\]

Consequently at least one of the following holds:

\[
 B_h(x^2)-B_h(x^1)\ge D_*/18,
 \tag{7.8}
\]

or

\[
 U_h(x^1)-U_h(x^2)\ge D_*/18.
 \tag{7.9}
\]

In (7.8), an $o(1)$-optimal response for $h$ against the opponents in
$X_n^2$ has payoff at least $D_*/18-o(1)$ more there than the same response
has against the opponents in $X_n^1$.  This is a literal source-matched
response-switch witness created by the second response.

In (7.9), write $\mu^1,\mu^2$ for the two limiting terminal laws.  Since

\[
 U_h(x^1)-U_h(x^2)
 =\sum_T\bigl(\mu^1(T)-\mu^2(T)\bigr)r_h(T),
 \tag{7.10}
\]

and Fin4 has sixteen terminal labels including Never, whose reward is zero,
some fixed nonempty terminal label $T$ satisfies

\[
 \bigl(\mu^1(T)-\mu^2(T)\bigr)r_h(T)\ge D_*/288.
 \tag{7.11}
\]

Thus failure of a two-zero support drop is not an unspecified cap-leakage
event: every minimum-fibre second response yields either a fixed positive
two-response cap switch or a signed terminal-law displacement on one fixed
nonempty label.  Neither alternative is yet a chronological block.  A cap
switch compares one response against two opponent environments, and (7.11)
forgets the causal date of the changed terminal mass.

The already established thin-slice ratio contraction removes the narrow
minimum-return chamber: if its parameter satisfies $\eta<D_*<2\eta$, the
response crossing is quantitatively off minimum.  Hence any surviving
minimum-fibre reactivation above lies in the wide chamber $D_*\ge2\eta$.
That extra aggregate debt does not by itself pay the cap/law seam in
(7.8)--(7.11).  The remaining two-block problem is exactly
to convert one of these source-matched reactivation certificates into a
charged return or to preserve both killed coordinates under the next
response.

## 8. Iteration gives a finite-role response-switch obstruction

The two-response construction iterates honestly as a horizontal response
operation.  It does **not** thereby become a chronological Nash--Bellman
path.

Suppose every selected response target has a minimum-fibre cluster, but no
cluster ever has two zero-debt coordinates.  Recursively choose a realizing
profile sequence for a minimum point $x^k$, select a maximal-debt player
$i_k$, take an $o(1)$-best response of $i_k$ on those literal profiles, and
refine to a convergent target sequence.  Each target sequence is used
definitionally as the next source sequence.  After the first step every
$x^k$ has exactly one zero-debt coordinate.  Hence $i_k$ may be chosen with

\[
 d_{i_k}(x^k)\ge D_*/3,
 \qquad
 d_{i_k}(x^{k+1})=0.
 \tag{8.1}
\]

If a selected target cluster is off minimum, the construction exits to the source-attached
paid-port arm.  If a minimum target preserves the previous zero, it exits to
support at most two.  The only infinite branch is therefore a literal chain
of target/source profile families with minimum-fibre clusters in which the
unique zero coordinate rotates.

At every such source, take sufficiently late actual realizers.  Their selected
mover debt is at least $D_*/6$.  Applying
`positiveDebt_exists_actualJointReach_paidFirstDisagreementRow` with
$\Delta=D_*/6$ gives an actual paid first-disagreement row of gain at least

\[
 {D_*\over24}
 \tag{8.2}
\]

and joint survival to its start at least

\[
 {D_*^2\over1152M^2},
 \tag{8.3}
\]

where $M$ is the reward bound.  Thus the persistent branch does not lose its
actual-reach paid-row scale as the zero rotates.

The exact conservative transfer also repeats.  At each edge,

\[
 \sum_{h\ne i_k}
   \bigl(d_h(x^{k+1})-d_h(x^k)\bigr)
 =d_{i_k}(x^k)\ge D_*/3.
 \tag{8.4}
\]

Consequently a recipient rises by at least $D_*/9$, and the same split as
(7.7)--(7.11) produces either

\[
 B_h(x^{k+1})-B_h(x^k)\ge D_*/18,
 \tag{8.5}
\]

or one signed nonempty terminal-law label contributes at least $D_*/288$ to
the prescribed-payoff fall.  Because the mover, recipient, old-zero label,
cap-versus-law branch, and terminal label all range over finite sets, an
infinite subsequence stabilizes all of this finite role data.

This is the strongest unconditional iteration conclusion.  Compactness may
also make the displayed semantic/law states recurrent, but it does not turn
the intervening full-strategy responses into exact punishment-floor
Nash--Bellman edges.  The paid rows in (8.2) are separately selected
first-disagreement witnesses at their source profiles and may occur at
unrelated dates.  Likewise (8.5) is a counterfactual response comparison,
and the terminal-label alternative has forgotten its causal date.  Therefore
the infinite chain is a **finite-role response-switch obstruction**, not an
admissible return.

A consumer must add one of two genuinely new compatibilities:

1. align the uniformly reached paid rows at consecutive response sources into
   one exact source-to-successor Bellman chronology; or
2. show that a stabilized cap/law switch forces preservation of the previous
   zero, hence the support-at-most-two exit.

Finite player labels alone do not supply either implication.

## 9. Source audit

The named source facts inspected were:

* `positiveDebt_exists_commonPrefix_profitableStoppingLawFork` in
  `fable/lean/FableCommonPrefixFork.lean`;
* `positiveDebt_exists_actualJointReach_paidRow_withSupport` in
  `fable/lean/FableActualReachSupport.lean`;
* `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`;
* exact cap-prefix debt scaling and the maximal-root ledger recorded in
  `CODEX_GATE__MAXIMAL_TARGET_CAP_REROOT_TRICHOTOMY.md`;
* the distinction between `QuittingPaidFirstDisagreementRow` and
  `QuittingLiteralPositiveActualRowPacket`, and the conditional theorem
  `gain_le_nashError_of_literal_root_tail`, in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticLiteralSourceReturnNoGo.lean`;
* the unique-all-Continue open tube recorded in
  `CODEX_GATE__MAXIMAL_TARGET_CAP_REROOT_TRICHOTOMY.md`; and
* bounded exact-block capacity in
  `formalized/UNBOUNDED_FINITE_HAZARD_CAPACITY_COMPILER.md`.

Section 7 additionally uses only compactness of the joint semantic/law
carrier, approximate attainment of each unrestricted behavioral cap, the
identity that changing player $i$ leaves $B_i$ unchanged, and continuity of
prescribed payoff and debt on that carrier.  Its source regeneration claim is
limited to retaining the literal replacement sequence as input.  Complete
source regeneration at a new minimum joint-law cluster additionally requires
the Fin4 hard-residual positive-finite-atom theorem and source-faithful
causalization on that same sequence.  Without those adapters the theorem
returns a joint-law cluster, not a source node.  It does not assert a new
causal marked-row producer.

No source-attached positive-minimum realization of the regression is claimed.
No terminal approximate Nash profile, charged return, or renewable rank is
constructed.
