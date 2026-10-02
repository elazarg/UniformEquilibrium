# Moving cap-chart cocycle and a literal forward-packet lift

Identity: `PAIRED_HULL_REVIEW`  
Status: ordinary mathematics; positive conditional compiler and exact local
regression; no unconditional Fin4 producer

## 1. Question

Suppose one repeatedly performs the two operations that actually occur in the
Fin4 full-debt/reset construction:

1. prefix the current actual profile by an exact cap--Nash product root; and
2. replace one player's complete behavioral strategy by a profitable target,
   using that literal target as the next source.

Can phase-varying exact roots turn these horizontal paid operations into one
finite forward Bellman packet of arbitrarily large absorption charge?

The answer is conditional but exact.  There is one vector cocycle to control:
the signed displacement between the cap of the actual moving source and the
Bellman chart.  Full cap preservation is sufficient but unnecessary.  Signed
cap leakage may cancel after survival transport.  Uniform smallness of every
partial transported sum gives an exact finite forward packet.  Without that
control, literal target-to-source compatibility and even repeated positive
actual reach do not suffice.

## 2. Data and notation

Let (I) be finite.  For a product root (q), write

\[
 c(q)=\Pr_q(\text{all Continue}),
 \qquad
 T_q(v)=\operatorname{quittingRootSuccessorPayoff}(v,q).
\]

The only outcome at which the continuation vector is used is all Continue.
Therefore, for all payoff vectors (v,w),

\[
 \boxed{T_q(v)-T_q(w)=c(q)(v-w).}
 \tag{2.1}
\]

Let (P_m) be actual behavioral profiles and let

\[
 \widehat b_m=B(P_m)
\]

be their unrestricted behavioral cap vectors.  Select an exact cap--Nash root
(q_m) against (widehat b_m), and put

\[
 S_{m+1}=q_m\star P_m.
\]

The exact cap-prefix theorem gives

\[
 B(S_{m+1})=T_{q_m}(\widehat b_m).
 \tag{2.2}
\]

Here (S_{m+1}) is the literal root-then-continuation profile, not an abstract
semantic replacement.  Equation (2.2) follows directly from
`quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
and `quittingTerminalSemanticPair_rootThenContinuation`.

Now let (P_{m+1}) be a literal one-player behavioral replacement of
(S_{m+1}).  This is the paid horizontal target and is, by definition, the
next actual source.  Define its signed cap leakage by

\[
 \ell_{m+1}
 :=B(P_{m+1})-B(S_{m+1}).
 \tag{2.3}
\]

If the mover is (p_m), own-strategy invariance of the unrestricted cap gives

\[
 \ell_{m+1,p_m}=0.
 \tag{2.4}
\]

No analogous statement holds for the other coordinates.

## 3. The moving chart and its exact cocycle

Start the abstract Bellman chart at the actual source cap,

\[
 v_0=\widehat b_0,
\]

and advance it using the phase-varying selected roots:

\[
 v_{m+1}=T_{q_m}(v_m).
 \tag{3.1}
\]

Define the chart error

\[
 e_m=\widehat b_m-v_m.
 \tag{3.2}
\]

Equations (2.1)--(2.3) give the exact recurrence

\[
 \boxed{e_{m+1}=c(q_m)e_m+\ell_{m+1}.}
 \tag{3.3}
\]

Since (e_0=0), this unfolds to

\[
 \boxed{
 e_m=
 \sum_{k=1}^{m}
 \left(\prod_{r=k}^{m-1}c(q_r)\right)\ell_k .}
 \tag{3.4}
\]

The empty product for (k=m) is one.  Thus the relevant seam is not the sum
of absolute cap changes.  It is a signed, survival-transported partial sum.
Phase variation can help only through cancellation in (3.4).

This is the precise form of the moving-successor datum that is absent from a
mere sequence of paid forks.

## 4. Cap-chart control transports exact Nash roots

Assume

\[
 \|e_m\|_\infty\le \varepsilon
 \qquad(0\le m<H).
 \tag{4.1}
\]

The root (q_m) is exact at (widehat b_m).  For player (i), changing only
the continuation cap changes its root endpoint difference by

\[
 -H_i(q_m)(v_{m,i}-\widehat b_{m,i}),
 \qquad 0\le H_i(q_m)\le1.
\]

Hence (q_m) is support-(\varepsilon) Nash at (v_m).  This is exactly the
checked stability theorem
`isQuittingRootSupportApproxNash_of_tail_close`, applied to the exact root at
(widehat b_m).

The distinction is important:

* the policy identity is exact because the chart is defined by (3.1);
* the Nash error is at most the distance from the chart to the actual cap;
* no cap of an arbitrary semantic replacement is used.

## 5. Conditional finite-forward-packet theorem

### Theorem 5.1 -- moving-cap chart lift

Fix (0<\varepsilon\le1) and (A\ge0).  Suppose there are a horizon (H),
actual profiles (P_0,\ldots,P_H), and product roots
(q_0,\ldots,q_{H-1}) such that:

1. (q_m) is exact cap--Nash against (B(P_m));
2. (S_{m+1}=q_m\star P_m) is the literal prefix profile;
3. (P_{m+1}) is a literal one-player behavioral replacement of
   (S_{m+1}) and is the next source;
4. with (v_0=B(P_0)) and (v_{m+1}=T_{q_m}(v_m)),
   
   \[
   \|B(P_m)-v_m\|_\infty\le\varepsilon
   \qquad(0\le m\le H);
   \tag{5.1}
   \]
5. the cumulative root absorption satisfies
   
   \[
   A\le\sum_{m<H}(1-c(q_m)).
   \tag{5.2}
   \]

Then (q_m,v_m) form a `QuittingFiniteForwardPacket` with support error
(\varepsilon) and charge target (A), in one compact payoff box depending
only on the reward bound (not on (H,A), or (\varepsilon\le1)).

### Proof

The policy equations are (3.1).  Section 4 proves support-(\varepsilon)
optimality at every row.  Every unrestricted cap (B(P_m)) is bounded by the
reward box and is at least the punishment value coordinatewise.  Equation
(5.1) therefore puts every (v_m) in the reward box enlarged by one and gives

\[
 v_{m,i}\ge \operatorname{Pun}_i-\varepsilon.
\]

Finally, (5.2) is exactly the packet charge field.  All requirements of the
finite-forward-packet interface follow.  (square)

### Corollary 5.2 -- a sufficient Fin4 producer

If the data in Theorem 5.1 can be produced for every
(0<\varepsilon\le1) and every (A\ge0), inside one fixed reward box, then
the checked finite-forward-packet compiler yields a uniform-equilibrium
payoff.

This is a genuine positive theorem, but it is conditional on the uniform
partial-sum estimate (5.1).  It is not a new source producer.

## 6. What a phase-varying circulation must prove

Using (3.4), hypothesis (5.1) is equivalent to

\[
 \left\|
 \sum_{k=1}^{m}
 \left(\prod_{r=k}^{m-1}c(q_r)\right)\ell_k
 \right\|_\infty
 \le\varepsilon
 \qquad(m\le H).
 \tag{6.1}
\]

Thus a phase-varying circulation needs bounded **every-prefix discrepancy**,
not merely:

* cancellation after the final phase;
* small average leakage;
* return of total debt;
* compact recurrence of the caps; or
* a zero sum of first-order tangent columns.

The requirement at every (m) is forced by support optimality of the root at
that row.  Final cancellation alone can leave an order-one intermediate cap
error and invalidate the intermediate root.

For a one-player response, (2.4) removes the mover coordinate from the new
leakage vector.  In Fin4, each leakage vector is therefore supported on at
most three cap coordinates.  That finite support is not yet an orientation:
the three spectator coordinates can have either sign, and the mover changes
from phase to phase.

## 7. A two-row form

For two phases the exact condition is especially transparent.  Let

\[
 \ell_1=B(P_1)-T_{q_0}(B(P_0)),
\]

\[
 \ell_2=B(P_2)-T_{q_1}(B(P_1)).
\]

Then

\[
 e_1=\ell_1,
 \qquad
 e_2=c(q_1)\ell_1+\ell_2.
 \tag{7.1}
\]

Consequently two literal paid responses yield a support-(\varepsilon)
two-row forward packet provided

\[
 \|\ell_1\|_\infty\le\varepsilon,
 \qquad
 \|c(q_1)\ell_1+\ell_2\|_\infty\le\varepsilon.
 \tag{7.2}
\]

Exact full-cap neutrality, (ell_1=ell_2=0), is sufficient but stronger
than needed.  The second leakage may cancel the transported first leakage.

Conversely, a final cancellation
(c(q_1)\ell_1+\ell_2=0) does not repair a large first seam: (q_1) was
selected against (B(P_1)), while the first chart reaches only (v_1).
The first inequality in (7.2) is indispensable.

## 8. Exact obstruction: positive horizontal reach can coexist with zero
## exact-root charge

The exact Fin4 table in
`CODEX_DESCENDANT__TWO_BLOCK_FULL_DEBT_FORK_SEAM` gives a minimal local
regression.  It has actual profiles

\[
 X_0\longrightarrow X_1\longrightarrow X_2
\]

such that:

* both arrows are literal one-player responses;
* the first target is the second source;
* each mover has a positive whole-profile gain at a row of joint reach one;
* all four debts remain positive and total debt is conserved; and
* spectator caps rise by the corresponding mover gains.

Nevertheless all Continue is the unique exact product root at both target
caps.  Fresh exactification therefore gives

\[
 q_1=q_2=\mathbf C,
 \qquad
 1-c(q_1)=1-c(q_2)=0.
\]

The moving-chart cocycle does not repair this:

* the exact roots contribute no charge;
* (T_{\mathbf C}) is the identity;
* the horizontal spectator-cap rises are the leakage vectors themselves;
* changing phases cannot turn those horizontal gains into Bellman charge.

The example has global minimum (D_*=0), so it does not refute a theorem
using positive-minimum provenance.  It does prove that literal source
identity, positive actual reach, full debt, and phase variation alone are
insufficient.

The maintained positive-minimum architecture permits the same two-step local
shape inside an open uniquely-all-Continue cap tube: small radial responses
remain full debt and inside the tube, but every fresh exact root is still all
Continue.  What is not presently realized there is the complete exact table
regression with (D_*>0).

## 9. Why the priced actual row does not yet close the cocycle

The scratch-checked tight-cycle pricing theorem supplies, in the relevant
limit-tight branch, a fixed lower bound on **actual pre-mark opponent
absorption** and a fixed marked-row cap defect.  These are strong actual
ledger summands.

They do not instantiate (5.2).  The charge in Theorem 5.1 is absorption of
the exact cap--Nash roots (q_m).  In the uniquely-all-Continue tube those
roots have zero absorption, while the actual marked row with positive
absorption has a fixed positive cap defect and therefore cannot be used as a
support-(\varepsilon) root as (\varepsilon\downarrow0).

This is an exact typing separation:

\[
 \begin{array}{c}
 \text{priced actual absorption at a non-Nash marked row}
 \\
 \not\Rightarrow
 \\
 \text{exact-root absorption charge in a forward packet}.
 \end{array}
\]

A successful use of tight-cycle pricing must either convert a fixed fraction
of that actual row into a small-defect root, or use a consumer whose charge is
the actual directed-transport ledger rather than exact-root absorption.

## 10. The smallest missing datum

The missing datum is not another compact endpoint.  It is one of the
following operational alternatives:

1. **bounded transported cap leakage:** construct arbitrarily charged literal
   chains satisfying (6.1) for every prescribed tolerance;
2. **priced seam consumer:** convert failure of (6.1) into a charged return,
   well-founded rank transition, or contradiction to the positive minimum;
3. **actual-to-exact charge conversion:** turn the priced marked-row ledger
   summand into absorption of a support-small cap root.

Without one of these, phase-varying root choice simply reselects an exact root
at each new cap.  It ensures local exactness at the actual source but does not
make the actual cap equal to the previous Bellman successor.  Equation (3.3)
is the invariant that records the failure.

## 11. Exact status and source audit

Proved here as ordinary mathematics:

* the cap-chart cocycle (3.3)--(3.4);
* the support transport from an actual cap to a nearby chart;
* the conditional finite-forward-packet theorem;
* the two-row cancellation criterion; and
* the exact boundary between priced actual absorption and exact-root charge.

Not proved:

* existence of chains satisfying (6.1) with unbounded charge;
* a consumer for failure of (6.1);
* conversion of the tight-cycle actual ledger floor into exact-root charge;
* Fin4 UE; or
* a positive-gap counterexample.

Named declarations inspected:

* `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
  and
  `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `TerminalCapNashEndpointTransport.lean`;
* `quittingTerminalSemanticPair_rootThenContinuation` in
  `TerminalSemanticPair.lean`;
* `isQuittingRootSupportApproxNash_of_tail_close` in `Projective/Lasso.lean`;
* `QuittingFiniteForwardPacket` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets` in
  `Projective/FiniteForwardProjectiveLasso.lean`;
* `quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
  `Root/TerminalDebtPrefix.lean`;
* the exact cap-seam formulas and regression in
  `CODEX_DESCENDANT__TWO_BLOCK_FULL_DEBT_FORK_SEAM.md`; and
* the actual pre-mark absorption and marked-row cap-defect floors in
  `CLAUDE_FABLE__OFF_MINIMUM_INERT_TIGHT_CYCLE_AND_PREMARK_ABSORPTION.md`.

The theorem is a conditional consumer interface, not an unconditional branch
closure.

## 12. Exact finite-word periodic correction

Exact recurrence of the displayed caps is unnecessary. Suppose there are
actual source caps

\[
\widehat b_0,\widehat b_1,\ldots,\widehat b_L
\]

and exact roots \(q_m\) at \(\widehat b_m\), for \(0\le m<L\). Assume
\(\widehat b_{m+1}\) is the cap of the literal paid target used as the next
source. Put

\[
c_m=c(q_m),
\qquad
\ell_{m+1}=\widehat b_{m+1}-T_{q_m}(\widehat b_m),
\tag{12.1}
\]

and

\[
C=\prod_{m<L}c_m.
\]

Assume \(C<1\), equivalently that the word has positive whole-word
absorption. Define

\[
L_{\mathrm{cap}}
=\sum_{k=1}^{L}
  \left(\prod_{r=k}^{L-1}c_r\right)\ell_k.
\tag{12.2}
\]

The cap-chart cocycle is

\[
e_{m+1}=c_me_m+\ell_{m+1},
\qquad
e_L=Ce_0+L_{\mathrm{cap}}.
\tag{12.3}
\]

For the corrected Bellman values

\[
v_m=\widehat b_m-e_m
\]

to form a periodic root word, the required condition is \(v_L=v_0\), not
\(e_L=e_0\). Since the actual endpoint caps may differ, this is

\[
e_L-e_0=\widehat b_L-\widehat b_0.
\]

Consequently the unique periodic initial correction is

\[
\boxed{
e_0=
\frac{L_{\mathrm{cap}}+\widehat b_0-\widehat b_L}{1-C}.}
\tag{12.4}
\]

This sign is forced by substituting (12.3). With (12.4), the iterates satisfy

\[
v_{m+1}=T_{q_m}(v_m),
\qquad
v_L=v_0
\tag{12.5}
\]

literally.

Let

\[
\varepsilon_{\mathrm{word}}
=\max_{0\le m<L}\|e_m\|_\infty.
\tag{12.6}
\]

Every \(q_m\) is support-\(\varepsilon_{\mathrm{word}}\) Nash at \(v_m\),
and every \(v_m\) is above the punishment floor minus that error.
Periodically repeat the finite word \(q_0,\ldots,q_{L-1}\). Its Bellman
equations close exactly, while each turn contributes the positive charge

\[
A_{\mathrm{word}}=\sum_{m<L}(1-c_m)>0.
\]

Arbitrarily many turns therefore produce arbitrarily charged finite-forward
packets at local error \(\varepsilon_{\mathrm{word}}\).

### Corollary 12.1 -- vanishing corrected words close the game

Suppose there is a sequence of finite words such that

\[
A_{\mathrm{word},n}>0,
\qquad
\varepsilon_{\mathrm{word},n}\longrightarrow0.
\tag{12.7}
\]

Then the game has a uniform-equilibrium payoff. For a requested support error,
select one word satisfying (12.7) and repeat it enough times to reach the
requested charge target.

No uniform bound on the number of phases is required. All within-word control
is already contained in the maximum defining
\(\varepsilon_{\mathrm{word},n}\).

The terminal laws and full profiles at the two ends of the word need not
agree. Once the corrected Bellman word is constructed, its periodic root word
is a legitimate abstract forward packet. Actual profiles certify that every
displayed root is exact at its phase cap and that consecutive phase caps come
from literal target-to-next-source handoffs.

## 13. The exact normalized trace-friction invariant

Let the composite Bellman map of the word be

\[
T_{q_{L-1}}\circ\cdots\circ T_{q_0}(v)=A+Cv.
\tag{13.1}
\]

Iterating (12.1) gives

\[
\widehat b_L=A+C\widehat b_0+L_{\mathrm{cap}}.
\tag{13.2}
\]

Therefore the numerator in (12.4) simplifies:

\[
L_{\mathrm{cap}}+\widehat b_0-\widehat b_L
=\widehat b_0-(A+C\widehat b_0).
\tag{13.3}
\]

The periodically repeated root word has prescribed terminal payoff

\[
u_{\mathrm{per}}=\frac{A}{1-C}.
\]

Consequently

\[
\boxed{
e_0
=\frac{\widehat b_0-T_{\mathrm{word}}(\widehat b_0)}{1-C}
=\widehat b_0-u_{\mathrm{per}}.}
\tag{13.4}
\]

The other \(e_m\) are the differences between the corresponding actual phase
caps and the phase payoffs of the same periodic root word. Thus no actual cap
recurrence is needed. The exact criterion is:

> the literal periodic payoff generated by the selected root word is
> uniformly close to every actual cap at which a phase root was selected.

The ratio in (13.4) is not artificial accounting. It is the cap displacement
per unit whole-word absorption, equivalently the cap-to-periodic-payoff
separation. A nonzero limit is a cap-level linear trace friction.

Net endpoint cancellation alone is not enough; every phase error in (12.6)
must be small. A simple sufficient condition is that the cyclically
transported leakage partial sums, after including the endpoint correction in
(12.4), all tend to zero. This remains valid for phase counts tending to
infinity.

The formula separates two falsifiable possibilities.

1. Produce literal handoff words whose periodic Bellman fixed points approach
   all their actual phase caps. Corollary 12.1 consumes them.
2. Prove that a positive lower bound on one phase of (13.4) forces an accepted
   off-minimum, support-entry, persistent-clock, or actual charged-row exit.

The priced tight-cycle row gives a nonvanishing **actual Nash defect**, not a
bound on (13.4). Connecting them remains the actual-row versus exact-root
typing problem identified in Section 9.

## 14. Exact Fin4 regression: scalar slice minimality does not bound trace
## friction

The strict-ascent ledger alternative can coexist with an order-one corrected
cap error even when the displayed root is exact and has fixed positive
absorption.

Use players \(1,2,3,4\). Define

\[
r_1(S)=
\begin{cases}
1,&S=\{1\},\\
0,&\text{otherwise},
\end{cases}
\qquad
r_2(S)=
\begin{cases}
1,&S=\{2\},\\
0,&\text{otherwise}.
\end{cases}
\tag{14.1}
\]

For \(i\in\{3,4\}\), put

\[
r_i(S)=
\begin{cases}
-1,&i\in S,\\
0,&i\notin S.
\end{cases}
\tag{14.2}
\]

Let \(P\) be all Never. Its prescribed payoff and unrestricted cap are

\[
U(P)=0,
\qquad
B(P)=b=(1,1,0,0),
\tag{14.3}
\]

so

\[
d(P)=(1,1,0,0),
\qquad
D(P)=2.
\]

Fix \(0<a<1\). At a product root \(q\), player 1 Quits with probability
\(a\), and players \(2,3,4\) Continue surely. Against the cap \(b\):

* player 1 is indifferent between Quit, which pays \(1\), and Continue,
  which pays \(b_1=1\);
* player 2 is indifferent: Quit and Continue both pay \(1-a\);
* players 3 and 4 strictly prefer Continue, with value \(0\) against Quit
  value \(-1\).

Thus \(q\) is exact cap--Nash at \(b\), with

\[
c(q)=1-a.
\]

The literal prefix \(q\star P\) has

\[
U(q\star P)=(a,0,0,0),
\]

\[
B(q\star P)=T_q(b)=(1,1-a,0,0),
\]

and hence

\[
d(q\star P)=(1-a,1-a,0,0),
\qquad
D(q\star P)=2(1-a).
\tag{14.4}
\]

The cap-defect ledger of the one-row word is exactly zero, while the base debt
is strictly higher:

\[
L=2>\ell=2(1-a),
\qquad
s(q)=\frac{\ell}{L}=1-a.
\tag{14.5}
\]

This is precisely the sharp strict-ascent balance from the positive-passport
suffix ledger.

However, the one-root Bellman map is

\[
T_q(v)=
\bigl(a+(1-a)v_1,\ (1-a)v_2,\ 0,\ 0\bigr).
\tag{14.6}
\]

Its periodic fixed point is

\[
u_{\mathrm{per}}=(1,0,0,0).
\]

Therefore the exact periodic correction at the actual base cap is

\[
\boxed{b-u_{\mathrm{per}}=(0,1,0,0).}
\tag{14.7}
\]

It is independent of \(a\). In particular, neither the zero exact-root
ledger, the positive absorption, nor the sharp equality
\(s=\ell/L\) controls the cap-to-periodic-payoff seam.

The repeated root word is not an equilibrium: player 2's prescribed payoff
is zero and its unrestricted cap is one. The large second coordinate in
(14.7) is exactly that surviving debt.

This table has an exact equilibrium and global \(\eta=0\), so it is not a
counterexample and does not refute a theorem using positive global
exploitability. It proves the narrower logical point:

> normalized-slice minimality, all-cut debt lower bounds, positive exact-root
> absorption, and a vanishing cap-defect ledger do not bound the corrected
> cap cocycle.

The positive global floor or hard-residual geometry must be used in a
genuinely vectorial way. The wide-chamber inequality \(D_*\ge2\eta\) by
itself only permits multiple certificate-scale debtors; it supplies no sign
or cancellation control on the phase corrections \(B-u_{\mathrm{per}}\).

## 15. A macroscopic cap switch cannot be canceled without exact charge

The preceding regression does not mean that arbitrary phase variation can
erase a fixed cap switch for free. There is an elementary metric obstruction
which is independent of the number of intervening phases.

Consider one finite root word \(q_0,\ldots,q_{L-1}\), its exact periodic
Bellman chart

\[
v_{m+1}=T_{q_m}(v_m),\qquad v_L=v_0,
\tag{15.1}
\]

and actual phase caps \(\widehat b_m\). Assume all rewards and chart values
lie in \([-M,M]^I\), and put

\[
\varepsilon_{\mathrm{word}}
=\max_{m<L}\|\widehat b_m-v_m\|_\infty.
\tag{15.2}
\]

For \(0\le a<b<L\), let

\[
A_{a,b}:=\sum_{m=a}^{b-1}(1-c(q_m)).
\tag{15.3}
\]

Since

\[
T_q(v)=c(q)v+(1-c(q))R_q
\]

for a vector \(R_q\in[-M,M]^I\) whenever \(c(q)<1\), and the zero-absorption
case is the identity, every phase satisfies

\[
\|v_{m+1}-v_m\|_\infty
\le 2M(1-c(q_m)).
\tag{15.4}
\]

Therefore

\[
\|v_b-v_a\|_\infty\le2M A_{a,b}.
\tag{15.5}
\]

The two chart errors at the endpoints give the exact useful estimate

\[
\boxed{
\|\widehat b_b-\widehat b_a\|_\infty
\le 2\varepsilon_{\mathrm{word}}+2M A_{a,b}.}
\tag{15.6}
\]

In particular, if two named phase caps are separated by

\[
\|\widehat b_b-\widehat b_a\|_\infty\ge\delta>0,
\tag{15.7}
\]

then

\[
\boxed{
\varepsilon_{\mathrm{word}}\ge\delta/4
\quad\text{or}\quad
A_{a,b}\ge\delta/(4M).}
\tag{15.8}
\]

The constants are deliberately symmetric rather than optimized.

This answers the “third phase” question precisely. Extra phases may cancel
the signed cap cocycle while keeping every intermediate root close to its
actual cap, but then the periodic Bellman values themselves must traverse the
macroscopic cap displacement. Equation (15.4) prices that traversal by
macroscopic exact absorption. A third phase cannot simultaneously make the
chart error and the intervening exact charge vanish.

### Application to the two-response leakage certificate

Suppose the first literal response reaches a minimum point \(x^1\) at which
its first mover has zero debt.  Choose the second mover \(q\) among the other
three players so that

\[
d_q(x^1)\ge D_*/3,
\]

and suppose the second literal response also has a minimum-fibre cluster
\(x^2\).  Killing this selected second mover gives the aggregate identity

\[
\sum_{i\ne q}\bigl(d_i(x^2)-d_i(x^1)\bigr)
=d_q(x^1)\ge D_*/3.
\tag{15.9}
\]

Thus some nonmover debt rises by at least \(D_*/9\). Splitting that rise
between cap and prescribed payoff gives either a fixed cap switch

\[
B_i(x^2)-B_i(x^1)\ge D_*/18
\tag{15.10}
\]

or a fixed signed terminal-payoff/law displacement of the same size.

Suppose a source-derived periodic word contains approximating phases for the
two caps in (15.10). For all sufficiently accurate approximants, one may use
\(\delta<D_*/18\) in (15.8). Taking, for example,
\(\delta=D_*/20\), every such word satisfies

\[
\varepsilon_{\mathrm{word}}\ge D_*/80
\quad\text{or}\quad
A_{a,b}\ge D_*/(80M).
\tag{15.11}
\]

Hence the cap-switch arm is already a rigorous

\[
\text{uniform trace friction}\quad\lor\quad
\text{macroscopic exact-charge segment}
\]

certificate. The signed-law arm is not controlled by (15.6), because exact
root Bellman maps see the continuation cap rather than the prescribed payoff
or full terminal law.

This remains conditional on producing one literal finite root word containing
the two response phases. Compact recurrence of cap vectors alone does not
produce that word with the required target-to-next-source identities.

## 16. The no-uniform-payoff periodic-friction moat

Corollary 12.1 has a useful exact contrapositive. If the game has no
uniform-equilibrium payoff, then there exists

\[
\varepsilon_{\mathrm{fr}}>0
\tag{16.1}
\]

such that every finite positive-absorption word of exact roots selected at
actual phase caps satisfies

\[
\boxed{\varepsilon_{\mathrm{word}}\ge\varepsilon_{\mathrm{fr}}.}
\tag{16.2}
\]

Indeed, failure of (16.2) would give, for each \(n\), one positive-charge word
with \(\varepsilon_{\mathrm{word}}<1/n\). Periodically repeating that selected
word supplies arbitrary charge at the same local error, so Corollary 12.1
would give a uniform-equilibrium payoff.

For a one-root word this says that every positive-absorption exact root at an
actual cap \(b\) is uniformly separated from its own stationary payoff
\(u_q\):

\[
\|b-u_q\|_\infty\ge\varepsilon_{\mathrm{fr}}.
\tag{16.3}
\]

Thus a hypothetical counterexample has a uniform periodic fixed-point moat,
not merely a failure of compact recurrence. The remaining source theorem may
be stated sharply:

> produce one source-derived finite root word with periodic cap friction
> tending to zero, or turn the fixed friction in (16.2) into a hard-residual
> clock, support, signed-law, or off-minimum exit.

The two-response cap-switch theorem and (15.8) show that small friction would
automatically spend macroscopic exact charge. They do not yet produce the
small-friction word.

## 17. The minimum-tube cap switch is permanent periodic friction

For the repaired two-response construction, the cap-switch arm is sharper
than (15.8).  The first phase lies at a positive global minimum.  The checked
minimum-fibre isolation gives an open cap neighborhood in which all Continue
is the unique exact product root.  Moreover, the strict singleton margin at a
positive minimum implies, for all sufficiently close source profiles,

\[
 B_i(P)>r_i(\{i\})\qquad(i\in I).
\tag{17.1}
\]

Thus prefixing such a source by the all-Continue root preserves its complete
semantic pair: its prescribed payoff is unchanged and

\[
 B_i(\mathbf C\star P)=
 \max\{r_i(\{i\}),B_i(P)\}=B_i(P).
\tag{17.2}
\]

Apply this to the literal first target sequence \(X_n^1\) in the two-response
construction.  Insert one all-Continue row and shift the second player's
complete response behind it.  The resulting profiles are still a literal
one-player source--target pair,

\[
 \mathbf C\star X_n^1
 \longrightarrow
 \mathbf C\star X_n^2,
\tag{17.3}
\]

and their caps are exactly \(B(X_n^1)\) and \(B(X_n^2)\).  Hence this is a
genuine moving-successor seam whose selected exact root is \(\mathbf C\).

Now let an arbitrary finite periodic root word contain this seam as two
consecutive **interior** phase caps
\(\widehat b_a,\widehat b_{a+1}\), where \(a+1<L\), with

\[
 q_a=\mathbf C.
\]

For its periodic Bellman chart,

\[
 v_{a+1}=T_{\mathbf C}(v_a)=v_a.
\]

Therefore, independently of every later phase,

\[
 \begin{aligned}
 \|\widehat b_{a+1}-\widehat b_a\|_\infty
 &\le
 \|\widehat b_{a+1}-v_{a+1}\|_\infty
 +\|v_a-\widehat b_a\|_\infty\\
 &\le 2\varepsilon_{\mathrm{word}}.
 \end{aligned}
\tag{17.4}
\]

The repaired two-response leakage identity supplies, in its cap-switch arm,

\[
 \|B(x^2)-B(x^1)\|_\infty\ge D_*/18.
\tag{17.5}
\]

Consequently, for any fixed \(\delta<D_*/18\), all sufficiently accurate
source approximants satisfy

\[
 \boxed{\varepsilon_{\mathrm{word}}\ge\delta/2.}
\tag{17.6}
\]

For example, taking \(\delta=D_*/20\) gives the explicit floor

\[
 \varepsilon_{\mathrm{word}}\ge D_*/40.
\tag{17.7}
\]

This answers the third-phase cancellation question exactly.  A later phase
may cancel the **final** transported cap leakage, and may carry arbitrary
exact-root absorption, but it cannot repair the support error already exposed
at the intermediate all-Continue seam.  The every-prefix requirement in the
finite-forward packet remembers it.

This is an obstruction rather than a consumer.  Under the no-uniform-payoff
hypothesis it is consistent with the uniform periodic-friction moat in
Section 16.  It proves that the cap-switch output of the literal two-response
construction cannot itself be closed by adding a third exact-root phase.  A
successful next step must instead consume the fixed response-switch witness,
change the chart before the all-Continue seam, or use the signed terminal-law
alternative.

## 18. Common-tester reduction and a stable-response regression

The fixed cap friction can be converted into a literal response rectangle,
but that conversion gives exactly the already known reset/reactivation
waist, not a new off-minimum conclusion.

Let \(X_n^1\to x^1\) and \(X_n^2\to x^2\) be the two literal consecutive
minimum-fibre response sequences from Section 15.  They differ only in the
second mover \(q\).  Suppose the selected recipient \(h\ne q\) is in the cap
arm,

\[
B_h(x^2)-B_h(x^1)\ge D_*/18.
\tag{18.1}
\]

Choose an \(o(1)\)-best complete behavioral response \(\tau_{h,n}\) against
\((X_n^2)_{-h}\), and install that **same** response on both sides:

\[
Z_n^1=(\tau_{h,n},(X_n^1)_{-h}),
\qquad
Z_n^2=(\tau_{h,n},(X_n^2)_{-h}).
\tag{18.2}
\]

The horizontal edge \(Z_n^1\to Z_n^2\) is still literally the \(q\)-strategy
replacement, because \(h\ne q\).  Moreover,

\[
U_h(Z_n^2)\ge B_h(X_n^2)-o(1),
\qquad
U_h(Z_n^1)\le B_h(X_n^1).
\]

Hence

\[
\boxed{
U_h(Z_n^2)-U_h(Z_n^1)
\ge D_*/18-o(1).}
\tag{18.3}
\]

The upper vertical target kills \(h\)'s debt:

\[
d_h(Z_n^2)\longrightarrow0.
\tag{18.4}
\]

There is also a fixed incoming paid edge.  The recipient was chosen from

\[
d_h(x^2)-d_h(x^1)\ge D_*/9,
\]

so \(d_h(x^2)\ge D_*/9\).  Consequently the literal vertical replacement

\[
X_n^2\longrightarrow Z_n^2
\]

has asymptotic gain at least \(D_*/9\).

Compactifying \(Z_n^2\) now gives only the familiar exhaustive alternatives:

1. its debt is strictly above \(D_*\), giving an off-minimum paid target;
2. it is minimum and the previously killed coordinate \(q\) remains zero,
   giving two zero coordinates and positive-debt support of size at most two;
3. it is minimum and \(q\) is reactivated, giving the next cap/payoff-law
   response square.

Thus the cap-friction certificate reaches the checked/maintained response-
rectangle and reset-face interfaces.  It does not force the first two arms.
The datum still missing is preservation of the old zero, or a
positive-minimum theorem consuming its reactivation.

### Exact stable-response regression

The table in Section 5 of
`CODEX_DESCENDANT__TWO_BLOCK_FULL_DEBT_FORK_SEAM.md` shows why the cap rise
alone cannot be interpreted as a switch of the active optimal response.
Use its profiles \(X_0,X_1\), where player \(i\) changes its marked action to
Continue with probability \(\lambda\in(0,1)\), and take the cap recipient
\(h=j\).  The caps satisfy

\[
B_j(X_0)=1,
\qquad
B_j(X_1)=1+\lambda.
\tag{18.5}
\]

Let \(\tau_j\) be the single pure response “Continue at the marked date.”
Against \(X_0\)'s opponents it pays \(1\).  Against \(X_1\)'s opponents it
pays

\[
(1-\lambda)\cdot1+\lambda\cdot2=1+\lambda.
\tag{18.6}
\]

Thus the same response \(\tau_j\) attains the cap on both sides and carries
the entire cap displacement.  There is no optimal-response-face switch at
all.  Nevertheless all Continue is the unique exact root at both caps, so
the intervening Bellman chart is constant and every periodic chart containing
the seam has error at least \(\lambda/2\).

This exact Fin4 regression has \(D_*=0\), hence does not settle the
positive-minimum chamber.  It does decisively rule out a local implication

\[
\text{fixed cap friction}
\Longrightarrow
\text{active-response-face descent}.
\]

Positive-global-minimum/source provenance must be used to exclude the stable
common-response rectangle or to orient the reactivated zero.  The existing
adjacent-response and source-faithful response-chord notes isolate precisely
that additional adapter; repeating the supplied-object trichotomy here would
not advance the frontier.

## 19. Exact reset algebra and the smallest literal regression

The wide-chamber inequality does not rule out reactivation by debt algebra.
Let \(B\) be a minimum point at which

\[
d_q(B)=0,\qquad d_h(B)=b>0,
\]

and let \(Z\) be the full response target which kills \(h\)'s debt.  If \(Z\)
is also minimum, then own-cap invariance and exact response gain give

\[
d_h(Z)=0
\]

and the exact conservative account

\[
\boxed{
\sum_{i\ne h}\bigl(d_i(Z)-d_i(B)\bigr)=b.}
\tag{19.1}
\]

This is all that global minimality contributes at the two endpoints.  It
does not force the \(q\)-summand to vanish.  The global max-debt floor only
requires

\[
\max_i d_i(B)\ge\eta,
\qquad
\max_i d_i(Z)\ge\eta.
\tag{19.2}
\]

For instance, the abstract compact two-point carrier

\[
d(B)=(0,1,1,1),
\qquad
d(Z)=(1,0,1,1)
\tag{19.3}
\]

has \(D_*=3\), \(\eta=1\), satisfies the wide inequality
\(D_*\ge2\eta\), and realizes (19.1) with \(b=1\).  Thus no inequality using
only nonnegativity, total-debt minimality, the max-debt floor, one old zero,
and one exact killed debt can exclude reactivation.

There is also a literal one-date four-player quitting realization of every
local cap/payoff/law identity in (19.3).  Label the players \(q,h,a,b\).
All reward coordinates not listed below are zero.  Put

\[
\begin{aligned}
r_h(\{q,a,b\})&=1,\\
r_q(\{a,b\})&=1,\\
r_a(\{q,h,b\})=r_a(\{q,b\})&=1,\\
r_b(\{q,h,a\})=r_b(\{q,a\})&=1.
\end{aligned}
\tag{19.4}
\]

Let \(P\) be the pure one-date profile at which all four players Quit.  Its
law is \(\delta_{\{q,h,a,b\}}\), and direct endpoint comparison gives

\[
U(P)=(0,0,0,0),
\qquad
B(P)=(0,1,1,1),
\qquad
d(P)=(0,1,1,1).
\tag{19.5}
\]

Indeed, \(q\) cannot obtain a positive payoff, whereas each of \(h,a,b\)
obtains one by Continuing while the other three Quit.

Now change only \(h\)'s action to Continue surely, leaving \(q,a,b\) as sure
quitters.  Call the literal target \(Q\).  Its law is
\(\delta_{\{q,a,b\}}\), and

\[
U(Q)=(0,1,0,0),
\qquad
B(Q)=(1,1,1,1),
\qquad
d(Q)=(1,0,1,1).
\tag{19.6}
\]

The response of \(h\) gains exactly one and kills its debt.  Simultaneously,
\(q\)'s Continue response exposes the coalition \(\{a,b\}\), so the old zero
is reactivated by exactly one.  Players \(a,b\) retain unit caps by
Continuing to the listed pair coalitions.  Thus (19.1) is exact, the same
pure response of \(h\) is cap-attaining before and after installation, and
the terminal laws are literal rather than abstract annotations.

This table is not a counterexample.  All singleton rewards are zero, so the
all-Never profile has zero payoff and zero debt; hence the true global
minimum is \(D_*=0\).  The example proves the sharp local boundary:

> the response rectangle, complete behavioral caps, terminal laws, exact
> killed debt, stable common tester, and conservative rotation are mutually
> compatible.  Any theorem excluding the reactivation arm must use the
> positive **global** minimum/source chronology in a way not expressible by
> (19.1)--(19.2).

Accordingly the next viable question is not another debt inequality.  It is
whether positive-minimum causal provenance forbids the literal law change in
(19.5)--(19.6), or charges it through the signed-law/actual-reach machinery.

## 20. Co-realized externality and paid rows still need not compose

The actual-reach localization of a signed payoff change does not by itself
repair the response rectangle.  The four-coalition regression in
`CODEX_DESCENDANT__SIGNED_EXTERNALITY_ACTUAL_REACH_AND_RESPONSE_CYCLE.md`
contains an exact same-source square which makes the obstruction explicit.

At the source coalition \(\{q,k\}\), compare two one-player replacements:

* player \(q\) leaves the coalition, producing \(\{k\}\); this raises
  player \(h\)'s payoff from zero to one;
* player \(h\) joins the coalition, producing \(\{q,h,k\}\); this is an
  actual profitable response for \(h\), again raising its payoff from zero
  to one.

Both rows occur at the same literal date and have joint reach one.  But if
both replacements are installed, the terminal coalition is \(\{h,k\}\),
where \(h\)'s payoff is again zero.  Thus the four \(h\)-payoffs are

\[
\begin{array}{c|cccc}
 &\{q,k\}&\{k\}&\{q,h,k\}&\{h,k\}\\ \hline
 U_h&0&1&1&0,
\end{array}
\tag{20.1}
\]

and the response-square mixed difference is

\[
 0-1-1+0=-2.
\tag{20.2}
\]

Hence the auxiliary \(q\)-controlled externality row and the genuine
\(h\)-paid row can destroy one another at first order.  Their separate
actual-reach certificates do not give an executable two-edge chronology.

The same example also blocks a fixed social-costate repair.  On the directed
cycle, one adjacent payoff increment is \(e_q-e_h\) and the next is
\(e_h-e_q\).  For every nonnegative weight \(\theta\), their weighted gains
are

\[
 \theta_q-\theta_h,
 \qquad
 \theta_h-\theta_q,
\tag{20.3}
\]

whose sum is zero.  No single costate prices both edges strictly positively.

Nor does the positive-minimum singleton moat, viewed only as a local payoff
inequality, exclude this square.  Change every singleton reward in that
regression from zero to \(-1\), leaving all displayed nonsingleton rewards
unchanged.  The displayed caps, debts, response gains, actual reaches, and
the unique all-Continue cap-root proof remain valid (the relevant singleton
Quit comparisons only become less attractive).  At every displayed corner,

\[
 U_i-r_i(\{i\})\ge1,
 \qquad
 B_i-r_i(\{i\})\ge1.
\tag{20.4}
\]

Thus even a uniform strict singleton separation can coexist with the maximal
negative response curl (20.2).  The modified table is still not a
counterexample: all Never has payoff and cap zero, because quitting alone now
pays \(-1\), so the true global minimum remains zero.

This separates the remaining proof obligation sharply.  Neither

\[
 \text{two same-source actually reached rows},
 \qquad
 \text{a fixed nonnegative social price},
 \qquad
 \text{nor strict singleton separation}
\]

forces a return or rank transition.  A successful consumer must use the fact
that the displayed source itself lies on a **positive global minimum with its
retained chronology**, not merely inequalities enjoyed by such a minimum.
The next possible mechanism is therefore a genuinely global law-change
account: either the double-replacement corner is forced off the minimum fibre,
or its negative response curl must regenerate a source with a finite rank
drop.  The local two-row data alone cannot establish either conclusion.
