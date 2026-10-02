# Recursive literal-`U` root prefixes have monotone debt support but may stall

Author: `CODEX_SPINOZA`

## Status

**Complete ordinary-mathematics recursive ledger and exact local stall;
not checked in Lean.**  The independently reviewed structured-source theorem
gives one uniform positive total-debt drop for every exact product root
against the original literal prescribed payoff.  Iterating exact
prescribed-payoff roots after that first step produces an actual nested
semantic sequence with three strong properties:

1. every coordinate debt is nonincreasing, so a killed debt never
   reactivates;
2. the original marked paid option obeys an exact
   opponent-survival-minus-exercise-premium recursion; and
3. the total collision charge, and every wrong-owner singleton charge seen
   by a persistent debtor, are summable.

These facts yield a finite persistent-support classification.  If at least
two debt coordinates remain positive in the limit, every root hazard is
summable.  If exactly one remains, all other players' hazards are summable
and the survivor is a one-persistent owner carrying the terminal gap.

Selecting an exact root of maximal next debt drop gives one further sharp
alternative.  A zero maximum is already the checked all-Continue/solo-owner
equality classification.  If a positive-drop root appears only at a limit of
the orbit, the fixed limit root is a literal fixed-charge approximate
Nash--Bellman row at the prelimit actual sources, with error tending to zero
and no source seam.  This row is admissible for the approximate punishment-
floor packet whenever the prelimit prescribed tails approach the punishment
box.  The structured tropical port does not supply that last condition;
switching from its prescribed payoff to its behavioral cap can create an
order-one root defect on an active positive-debt coordinate.

There is now also an exact answer for the positive-survival continuation of
the structured first root.  Recursive positive-survival exact prefixes renew
the paid player's **complete cap**, but only by shifting the original Quit0
cap one date farther at every step.  Bounded Fin4 exact-block capacity makes
the total marginal hazard of the whole reverse-prefix family summable.
Consequently the original source and paid suffix retain positive reach, while
the exact cap is the deterministic clock at the growing prefix depth.  From
the front of the blocks, the entire construction converges to the constant
all-Continue phantom and the source mark escapes to infinity.

Thus this still does not give a renewable charged Nash--Bellman return.  The
first prefix generally destroys stationarity, the date-zero paid row, and the
cap pin at the singleton payoff.  An exact boundary table can reach a
descendant whose all-Continue root is exact, so subsequent prefixing is the
identity while positive late-tail debt remains.  In the hard Fin4 class, full
normal core does make this identity edge punishment-floor admissible; it does
**not** give it positive absorption, charge, or descent.  The positive-
survival branch is therefore not unclassified: it lands exactly in the
source-marked all-summable moving-clock waist.

## Question

Starting from the structured stationary tropical source, choose an exact
product Nash root against its literal prescribed payoff and prefix that root
to the actual profile.  Repeat the same operation at each actual descendant.
Does the reviewed uniform first debt drop renew, does it produce an infinite
charged exact spine, or does the paid source passport disappear?

## Sources inspected

- `notes/CODEX_NEGATIVE_CERTIFICATE__STRUCTURED_PAID_SOURCE_ONE_STAGE_ROOT_CLASSIFICATION.md`:
  independently reviewed uniform first-step debt drop at the structured
  source.
- `notes/CODEX_SPINOZA__STRUCTURED_STATIONARY_PAID_PORT_EXACTIFICATION_BARRIER.md`:
  literal-`U` debt expenditure, root geometry, and the `U/B` tail split.
- `notes/CODEX_ROOT__PRESCRIBED_PAYOFF_ROOT_LIFTING.md`:
  the independently reviewed general prescribed-payoff root classification.
- `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`:
  `quittingTerminalSemanticDebt_prefix_eq_blockAct`,
  `quittingTerminalSemanticDebt_prefix_le`, and literal-prefix carrier
  closure.
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourOffMinimumChargedBlockerGate.lean`:
  `quittingTerminalSemanticDebtDrop_nonneg_of_exact`,
  `lowerDebt_mul_collisionMass_le_debtDrop_of_exact`, and
  `singletonMass_mul_otherDebt_le_debtDrop_of_exact`.
- `UniformEquilibrium/Quitting/Root/FaceGeometry.lean`:
  exact opponent-survival and exercise-premium faces.
- `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/NormalCorePunishmentNormal.lean`:
  `QuittingLCPClassification.all_punishmentNormal_of_normalCore_eq_univ`.
- `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`:
  `isZeroQuittingRootNash_allContinue_iff_singleton_le`.
- `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`:
  `quittingRootQuitPayoff_le_successor_add_of_isεNash` and
  `quittingRootContinuePayoff_le_successor_add_of_isεNash`.
- `UniformEquilibrium/Quitting/Root/NashDefect.lean`:
  `isεQuittingRootNash_iff_coordinateNashDefect_le` and the exact endpoint-
  mixture formula for coordinate Nash defect.
- `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorForward.lean`:
  `quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge` (the exact
  version of the approximate floor propagation used below).
- `UniformEquilibrium/Quitting/Root/EndpointBackwardStability.lean`:
  exactification by perturbing the reward table, which is deliberately not
  an exactification in the fixed game considered here.
- `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityWitness.lean`
  and
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauTightness.lean`:
  the common terminal gap and its realization by a complete semantic-debt
  coordinate.
- `UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`
  and
  `UniformEquilibrium/Quitting/Bellman/Finite/UnboundedExactBlockHazardCapacity.lean`:
  `finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
  and the literal total marginal-hazard charge of finite exact blocks.
- `notes/CODEX_HILBERT__SOURCE_FAITHFUL_OBSERVER_RETURN_SEAM.md`:
  exact transport of a tail cap through a positive-survival exact prefix,
  and the warning that the retained historical label alone has no return
  consumer.
- `notes/CODEX_NEGATIVE_CERTIFICATE__FIRST_EXACT_ROOT_SURVIVAL_AND_UNIQUE_SURE_RESET.md`:
  the independently reviewed first-root survival split which supplies the
  positive-survival branch refined in Section 10.

## 1. The actual recursive construction

Let `τ⁰` be an actual behavior profile and put

\[
 p^n=(U^n,B^n)
 =\operatorname{SemanticPair}(\tau^n),\qquad
 d_{n,i}=B_i^n-U_i^n,qquad D_n=\sum_i d_{n,i}.                 \tag{1.1}
\]

For every `n`, select any exact independent product root `qⁿ` Nash
against `Uⁿ`, and define the literal descendant

\[
 \tau^{n+1}=q^n\star\tau^n,qquad
 p^{n+1}=T_{q^n}p^n.                                            \tag{1.2}
\]

Finite-game Nash existence supplies `qⁿ`, and literal prefix closure makes
every `pⁿ` an actual terminal-semantic carrier point.  Write

\[
 s_{n,i}=\prod_{j\ne i}(1-q^n_j),qquad
 c_n=\prod_j(1-q^n_j),qquad
 e_{n,i}=\max\{0,\Delta_i(U^n,q^n)\}.                       \tag{1.3}
\]

Here `s_{n,i}` is the opponents' Continue probability and `c_n` is joint
Continue.

## 2. Exact debt and option ledgers

The checked debt action gives, coordinate by coordinate,

\[
 \boxed{d_{n+1,i}=[s_{n,i}d_{n,i}-e_{n,i}]_+.}                 \tag{2.1}
\]

Consequently

\[
 0\le d_{n+1,i}\le d_{n,i},qquad
 0\le D_{n+1}\le D_n.                                        \tag{2.2}
\]

In particular, a zero debt can never reactivate under this recursive
operation:

\[
 d_{n,i}=0\Longrightarrow d_{m,i}=0\quad(m\ge n).            \tag{2.3}
\]

This is an exact finite rank on *actual debt support*, unlike the horizontal
response genealogies in which a killed label may return.  It is not by itself
a terminating rank because a positive coordinate may decrease forever
without reaching zero.

For `m<n`, put

\[
 S_i(m,n)=\prod_{r=m}^{n-1}s_{r,i},qquad S_i(n,n)=1.           \tag{2.4}
\]

Iterating (2.1) gives the exact option-budget formula

\[
 \boxed{
 d_{n,i}=
 \left[
 S_i(0,n)d_{0,i}
 -\sum_{m=0}^{n-1}S_i(m+1,n)e_{m,i}
 \right]_+.}                                                   \tag{2.5}
\]

For the original paid player `b`, whose initial cap is attained by the
marked Quit0 response, (2.5) has literal strategic meaning.  At each new
root, forcing `b` to Continue retains the old response option with factor
`s_{n,b}`; if `b`'s prescribed root action is sure Quit, the immediate
exercise premium `e_{n,b}` is the opportunity cost of reaching the old
tail.  Thus (2.5), not the calendar joint reach
`∏_{r<n} c_r`, is the exact surviving value of the paid passport.

Whenever `d_{n+1,i}>0`, no positive-part clipping occurs and

\[
 d_{n,i}-d_{n+1,i}
 =(1-s_{n,i})d_{n,i}+e_{n,i}.                                  \tag{2.6}
\]

If clipping occurs, that coordinate's entire remaining passport is consumed
and it stays zero forever.

## 3. Global telescopes under the hard residual

Assume a terminal exploitability witness with gap `Γ>0`, and let
`D_*>0` be the global minimum total debt on the compact semantic carrier.
Every actual `pⁿ` then satisfies

\[
 D_n\ge D_*,qquad \max_i d_{n,i}\ge\Gamma.                  \tag{3.1}
\]

Put `δ_n=D_n-D_{n+1}`.  Equations (2.2) and (3.1) give

\[
 \sum_{n=0}^{N-1}\delta_n=D_0-D_N\le D_0-D_*,
 \qquad
 \sum_{n=0}^{\infty}\delta_n\le D_0-D_*,
 \qquad \delta_n\longrightarrow0.                            \tag{3.2}
\]

Let `Coll(qⁿ)` be the root probability of two or more
quitters, and let `μ_n({k})` be its singleton-`k` mass.  The checked
exact-prefix inequalities give

\[
 D_*\operatorname{Coll}(q^n)\le\delta_n,                     \tag{3.3}
\]

and, whenever `j≠k`,

\[
 \mu_n(\{k\})d_{n,j}\le\delta_n.                           \tag{3.4}
\]

Therefore

\[
 \sum_n\operatorname{Coll}(q^n)
 \le {D_0-D_*\over D_*}<\infty.                              \tag{3.5}
\]

Moreover, if `d_{n,j}≥α>0` on a tail, then

\[
 \sum_n\sum_{k\ne j}\mu_n(\{k\})
 \le {3(D_0-D_*)\over\alpha}<\infty.                        \tag{3.6}
\]

Thus all nonsingleton absorption is summable, and every singleton owner other
than a persistent debtor has summable mass.

## 4. Persistent-support classification

Each `d_{n,i}` decreases to a limit `d_{∞,i}≥0`.  Since
`D_n≥D_*`, the persistent set

\[
 P=\{i:d_{\infty,i}>0\}                                     \tag{4.1}
\]

is nonempty.  In fact (3.1) gives

\[
 \max_i d_{\infty,i}\ge\Gamma.                              \tag{4.2}
\]

For every `i∈P`, equation (2.6) holds eventually and
`d_{n,i}≥d_{∞,i}>0`.  Hence

\[
 \sum_n(1-s_{n,i})<\infty,qquad
 \sum_n e_{n,i}<\infty.                                      \tag{4.3}
\]

Because `qⁿ_j≤1-s_{n,i}` for `j≠i`, this yields the following
exhaustive alternatives.

### 4.1 Two or more persistent debtors

If `|P|≥2`, then for every player `j` one may choose
`i∈P∖{j}`.  Equation (4.3) gives

\[
 \sum_n q^n_j<\infty\quad\text{for every }j,
 \qquad
 \sum_n(1-c_n)<\infty.                                       \tag{4.4}
\]

All root hazards are summable and `qⁿ→0`.  This is an exact
all-summable reverse-prefix regime, not automatically a terminal equilibrium:
the finite profiles list the roots in reverse order
`qⁿ⁻¹,…,q⁰,τ⁰`, so their pointwise calendar limit is the
all-Never boundary and may lose all terminal mass at infinity.

### 4.2 One persistent debtor

If `P={k}`, then

\[
 d_{\infty,k}\ge\Gamma,qquad
 \sum_n q^n_j<\infty\quad(j\ne k).                           \tag{4.5}
\]

Only the persistent owner's own root hazards may have nonsummable total
mass.  This is the exact one-persistent reverse spine left by the recursive
construction.  Its exercise premiums are summable by (4.3), but no forward
calendar source or punishment-floor continuation has yet been produced.

For the original paid label `b`, either `b∈P`, in which case its old
cap option survives with positive limiting value and all opponent hazards
are summable, or `d_{n,b}→0`, in which case (2.5) gives the exact
survival/premium account by which the marked passport dies.  A different
positive debtor must then survive, but no identity transfers the original
stationary paid row or singleton cap pin to that label.

## 5. What the reviewed first drop does and does not renew

At the structured stationary source, the independently reviewed one-stage
classification supplies constants `δ₀>0` and `N` such that every
late source root satisfies

\[
 D_1\le D_0-\delta_0.                                        \tag{5.1}
\]

The proof uses four fields simultaneously:

- the source's date-zero stationary Quit margin;
- the fixed debt of the paid label `b`;
- the cap pin `B_b→r_b({b})`; and
- a root absorption floor uniform over all exact root selections.

After (1.2), the old paid row lies strictly inside the tail.  The new profile
need not be stationary, its cap `B_b¹` need not equal or approach the solo
reward, and all-Continue may be an exact root against `U¹`.  Only the
option budget (2.5) survives.  Therefore none of the four source fields needed
to reapply (5.1) follows from literal prefixing.

## 6. Exact one-step-to-all-Continue stall

The loss is real already in a strengthening of the boundary table from
Section 11.3 of
`CODEX_SPINOZA__STRUCTURED_STATIONARY_PAID_PORT_EXACTIFICATION_BARRIER.md`.
Change the two active rewards to

\[
 r_0(\{0,1\})=2,qquad r_0(\{1\})=3,                        \tag{6.1}
\]

For player 2 set every reward on a coalition containing 2 equal to `-1`,
and every reward on a nonempty coalition excluding 2 equal to `2`.  For
player 3 set every reward on a coalition containing 3 equal to `-1`, and
every reward on a nonempty coalition excluding 3 equal to `2`, except keep
`r_3({2})=0`.  Retain the player-1 coordinates from the earlier table and
set remaining player-0/player-1 coordinates to zero.  These assignments leave
the stationary source and player 0's complete paid Quit0 cap unchanged.

Against the source payoff `u=(0,1,-1,0)`, the exact root

\[
 q_0=q_1={1\over2},qquad q_2=q_3=0                            \tag{6.2}
\]

still exists.  Player 0's endpoints are

\[
 Q_0=1+q_1,qquad C_0=3q_1,
\]

and player 1's endpoints remain `Q₁=q₀` and
`C₁=1-q₀`.  Thus both are indifferent at (6.2), while players 2 and 3
strictly Continue as before.

The literal prefixed payoff is

\[
 U^1=(3/2,1/2,5/4,3/2).                                       \tag{6.3}
\]

Every singleton self-reward is at most the corresponding coordinate of
`U¹`:

\[
 (r_0(\{0\}),r_1(\{1\}),r_2(\{2\}),r_3(\{3\}))
 =(1,0,-1,-1)\le U^1.                                        \tag{6.4}
\]

At the tail `U¹`, players 2 and 3 strictly prefer Continue against every
opponent product law: their Quit payoff is `-1`, while their Continue
payoff is a mixture of coordinates at least zero.  Hence they Continue in
every exact root.  Against them, player 0's endpoint difference is

\[
 (1+q_1)-(3/2+3q_1/2)=-(1+q_1)/2<0,                            \tag{6.5}
\]

so player 0 also Continues in every exact root.  Player 1 then compares
Quit payoff zero with Continue payoff `1/2`, and Continues strictly.
Therefore all-Continue is the **unique** exact root against `U¹`.
Every later stage consequently gives

\[
 p^{n}=p^1\quad(n\ge1),qquad
 \delta_n=0\quad(n\ge1),                                    \tag{6.6}
\]

while the first exact prefix retains positive complete tail debt, including
`d_{1,0}=1/2` by (2.1).  The initial source has all the local stationary
paid-row fields, but after one genuine debt drop the recursive exact-root
program can stall forever at the identity root.

The pure singleton exit set `{1}` is a terminal Nash profile.  Its owner
gets zero and is indifferent to leaving; player 0 gets `3` by staying out
rather than `2` by joining; and players 2 and 3 get `2` by staying out
rather than `-1` by joining.  Thus this is not a positive-global-gap
counterexample.  It is an exact falsifier of the claimed
*recursive implication*: stationarity and the cap pin are not inherited by
an actual exact prefix, and monotone debt alone does not force a second
positive drop.  The hard global gap does not itself forbid an all-Continue
exact root at a positive-debt tail; that root simply delays the same
non-equilibrium continuation.

## 7. Exact-block capacity, punishment floors, and chronology audit

Each edge in (1.2) is an exact Nash--Bellman edge against the actual
prescribed payoff `Uⁿ`, and each semantic descendant is literal.  Moreover,
every `Uⁿ` is an actual terminal payoff vector, hence lies in the canonical
reward box.  Reading any finite reverse-prefix word in its true calendar
order and pairing each displayed value with its selected root therefore
gives a `QuittingFiniteExactNashBellmanBlock` in
`quittingNashBellmanBox (quittingRewardBound reward)`.

This is already exactly enough for the checked finite exact-block capacity.
That theorem requires only canonical-box membership and the displayed exact
Nash--Bellman edges; it does **not** require playerwise punishment floors or
membership in a punishment-floor reachable relation.  This is the capacity
input used explicitly in Theorem 10.2 below.

Punishment floors remain a separate issue only for the checked infinite
floor-orbit and charged-return consumers.  Neither root Nash against `Uⁿ`
nor the inequalities `Bⁿ≥Uⁿ` alone imply

\[
 \operatorname{PunishmentValue}_i\le U_i^n.                   \tag{7.1}
\]

There is, however, an exact exception at the identity stall.  In the hard
Fin4 class, full normal core implies punishment normality by
`all_punishmentNormal_of_normalCore_eq_univ`, hence

\[
 \operatorname{PunishmentValue}_i\le r_i(\{i\})
 \quad\hbox{for every }i.                                    \tag{7.2}
\]

If all-Continue is an exact root against `Uⁿ`, then
`isZeroQuittingRootNash_allContinue_iff_singleton_le` gives

\[
 r_i(\{i\})\le U_i^n\quad\hbox{for every }i.                  \tag{7.3}
\]

Thus (7.1) *does* hold at an all-Continue stall.  This closes the floor
question there, but the identity root has zero absorption, zero collision
charge, zero exercise premium, and zero debt drop.  It is a floor-admissible
zero-charge edge, so the exact-block hazard bound counts nothing at that
stage.  For a general non-all-Continue root, punishment normality yields only
the first inequality in (7.2); the needed comparison
`r_i({i})≤U_iⁿ` need not hold for the separate floor-orbit interface.

Likewise, the reverse-prefix list is not a forward projective spine.  At
depth `n` its calendar order is

\[
 q^{n-1},q^{n-2},\ldots,q^0,\tau^0.                           \tag{7.4}
\]

Adding one root changes every previously observed absolute deadline by one.
Even in the all-summable case (4.4), pointwise convergence from the front may
send the absorbing law to infinity.  Treating (7.4) as the forward order
`q⁰,q¹,…` reverses every Bellman successor identity.

Therefore:

- the first uniform drop is a valid actual off-minimum descent;
- debt support is a nonreactivating finite rank, but it need not decrease;
- positive persistent coordinates yield the summability classification
  (4.4)--(4.5);
- the original paid passport has the exact budget (2.5), but loses its
  stationary date-zero and cap-pin fields; and
- every finite reverse word is accepted by the canonical exact-block
  capacity theorem, but the identity stall carries no charge;
- no terminal compiler follows from the capacity bound without a
  source-attached positive charge or a forward-order adapter.

## 8. Maximal-drop selection and a born-root approximate entrance

For a semantic pair `p`, let `R(p)` be the nonempty compact set of exact
product Nash roots against its prescribed payoff, and define

\[
 m(p)=\max_{q\in R(p)}
       \{D(p)-D(T_qp)\}.                                      \tag{8.1}
\]

The objective is continuous in `(p,q)`, so the maximum is attained.  Choose
at each recursive stage a maximizing root.  If `m(pⁿ)=0`, no exact root has
strict debt descent.  The reviewed prescribed-payoff root classification
then gives the exhaustive local conclusion:

- if at least two coordinates of `pⁿ` have positive debt, every exact root
  is all Continue, hence all Continue is the unique exact root;
- if exactly one coordinate `k` has positive debt, every exact root is either
  all Continue or a solo-`k` root with positive `k` hazard, zero exercise
  premium, every opponent pure Continue, and
  `U_kⁿ=r_k({k})`.

Along the maximizing recursion, `m(pⁿ)=δ_n→0` by (3.2).  After taking a
convergent subsequence, one cannot conclude that the limiting point `p` has
`m(p)=0`: the exact Nash-root correspondence is closed but need not be lower
hemicontinuous.  A positive-drop exact root may be born at the limiting
prescribed payoff without being approximated by exact roots at the actual
prelimit payoffs.

That support-entry phenomenon nevertheless has a precise approximate-row
interpretation.  Suppose

\[
 p^{n_r}\longrightarrow p,qquad
 q\in R(p),qquad
 \rho:=D(p)-D(T_qp)>0.                                      \tag{8.2}
\]

The root `q` is not all Continue, so its fixed absorption

\[
 a=\Pr_q(\text{some player Quits})                            \tag{8.3}
\]

is positive.  Let `ε_r` be its maximum one-row deviation gain against
`U^{n_r}`.  Continuity of all finite root endpoint payoffs and exactness at
`U(p)` give

\[
 \epsilon_r\longrightarrow0.                                \tag{8.4}
\]

Prefix the *same* `q` literally to the actual prelimit profile and call its
semantic pair `y_r=T_qp^{n_r}`.  Then

\[
 U(y_r)=F(q,U^{n_r}),qquad
 D(y_r)\longrightarrow D(T_qp)=D(p)-\rho.                    \tag{8.5}
\]

Thus `(q,U^{n_r},U(y_r))` is a source-attached approximate Nash--Bellman row
with exact Bellman evaluation, fixed charge `a`, support-Nash error `ε_r→0`,
literal ancestry, and **zero semantic rebase seam**.  Failure of exact-root
lower hemicontinuity does not obstruct these four fields.

There is also a clean punishment-floor criterion.  Let `P` be the behavioral
punishment vector.  Repeating the proof of
`quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge` with the two
approximate endpoint inequalities from `SuccessorCertificate.lean` gives

\[
 U^{n_r}_i\ge P_i-\eta_r\ \ (\forall i)
 \quad\Longrightarrow\quad
 U_i(y_r)\ge P_i-(\eta_r+\epsilon_r)\ \ (\forall i).          \tag{8.6}
\]

Indeed, when the stationary unilateral cap is realized by Quit, the pure-
Quit endpoint is at most `ε_r` above the successor.  When it is realized by
waiting, its absorbing numerator plus opponent-survival times the tail gives
the same estimate, with the tail shortfall multiplied by a number in
`[0,1]`.  The degenerate all-opponents-Continue row uses either the singleton
Quit endpoint or the tail endpoint.  Hence, if `η_r→0`, (8.2)--(8.6) give
exactly one fixed-charge row accepted by the approximate floor-admissible
packet interface.

The structured tropical paid source explicitly supplies no inequality
`P_i≤U_i`.  Only its complete cap satisfies `P_i≤B_i`, and
`B_i-U_i=d_i` need not tend to zero.  Replacing `U` by `B` does not repair
this for free.  The exact endpoint identity is

\[
 \Delta_i(B,q)=\Delta_i(U,q)-s_i(q)d_i.                       \tag{8.7}
\]

For example, if `0<q_i<1` and `d_i>0`, exactness against `U` gives
`Δ_i(U,q)=0`; against `B`, switching that mixed coordinate to pure Continue
improves its payoff by exactly

\[
 q_i\,s_i(q)\,d_i.                                        \tag{8.8}
\]

This can be order one even though `ε_r→0` in (8.4).  Backward stability by
an own-coalition reward perturbation changes the quitting table and therefore
is not an exactification in the fixed game.  Consequently the born root is
a genuine approximate charged entrance, but it reaches the checked
chronological consumer only under the additional vanishing tail-floor
shortfall in (8.6).  At the supplied port, the remaining obstruction is the
prescribed-payoff/punishment-floor mismatch, not the lack of exactness of the
row itself.

## 9. Summably approximate prefixes obey the same persistent classification

The approximate cap-pin theorem of
`CODEX_HAHN__APPROXIMATE_CAP_PIN_DEBT_DROP_AND_VISIT_BUDGET.md` points to a
more general exact identity.  For an arbitrary product root `q` at a semantic
pair `p=(U,B)`, fix player `i` and write

\[
 x_i=\Pr_q(i\text{ Quits}),\qquad
 s_i=\Pr_q(\text{every opponent of }i\text{ Continues}),
\]

\[
 e_i=Q_i(q_{-i})-C_i(q_{-i};U_i),
\]

and let `ξ_i` be player `i`'s exact coordinate Nash defect of the mixed row
against `U`.  Directly subtracting the prescribed endpoint mixture from the
complete cap gives

\[
 d'_i=\max\{e_i,s_id_i\}-x_ie_i.                              \tag{9.1}
\]

The two sign cases for `e_i`, together with the exact endpoint-mixture
formula for `ξ_i`, give the sharper identity

\[
 \boxed{
 d'_i=[s_id_i-[e_i]_+]_+ + \xi_i.}                           \tag{9.2}
\]

Define the ideal expenditure

\[
 \ell_i=d_i-[s_id_i-[e_i]_+]_+\ge0.                          \tag{9.3}
\]

Then every arbitrary prefix has the exact perturbed ledger

\[
 d'_i=d_i-\ell_i+\xi_i,
 \qquad
 \ell_i\ge(1-s_i)d_i.                                      \tag{9.4}
\]

Now let `p^{n+1}=T_{q^n}p^n` be one literal vertical prefix chain.  The rows
need only be `ε_n`-Nash against the actual prescribed payoffs.  Let
`ξ_{n,i}` be their coordinate defects and assume the stronger, iteration-
appropriate condition

\[
 E:=\sum_n\sum_i\xi_{n,i}<\infty.                            \tag{9.5}
\]

Since every actual semantic debt is nonnegative, telescoping (9.4) gives

\[
 \sum_n\sum_i\ell_{n,i}\le D_0+E.                           \tag{9.6}
\]

Moreover `d_{n+1,i}≤d_{n,i}+ξ_{n,i}`.  Hence the total positive variation
of every debt coordinate is finite; boundedness below then makes its total
negative variation finite as well.  Each `d_{n,i}` therefore has a limit.
Under the hard terminal gap, at least one limiting coordinate is at least
`Γ`, just as in (4.2).

For every persistent coordinate `i`, (9.4)--(9.6) imply

\[
 \sum_n(1-s_{n,i})<\infty.                                  \tag{9.7}
\]

The same proof as Section 4 now yields the exact approximate-chain
classification:

- with at least two persistent debtors, every marginal root hazard is
  summable;
- with a unique persistent debtor `k`, every non-`k` marginal hazard is
  summable.

This also preserves the collision and wrong-owner singleton ledgers.  For
the root coalition law `μ_n`, pointwise algebra gives

\[
 D_*\operatorname{Coll}(q^n)
 \le\sum_i(1-s_{n,i})d_{n,i}
 \le\sum_i\ell_{n,i},                                      \tag{9.8}
\]

and, for `j≠k`,

\[
 \mu_n(\{k\})d_{n,j}
 \le(1-s_{n,j})d_{n,j}\le\ell_{n,j}.                       \tag{9.9}
\]

Thus collision charge and every singleton charge transverse to a persistent
debtor remain summable under (9.5).  A sequence of limit-born approximate
rows with errors chosen, say, below `2^{-n}` cannot evade the prior residual:
it either becomes all-summable or concentrates asymptotically on the unique
persistent owner.  Vanishing row error alone would not suffice.

The cap-pin visit theorem adds a genuine finite conditional rank.  Along the
same literal genealogy, every visit to the chamber

\[
 d_b\ge\gamma,\qquad |B_b-r_b(\{b\})|\le\gamma/4             \tag{9.10}
\]

costs `δ_b` up to `ξ_{n,b}`.  Consequently (9.5) bounds the total number of
returns to (9.10), even if the pin is lost and later recovered by intervening
prefixes.  This counts vertical source re-entry; a horizontal strategy
replacement may replenish the debt and is outside the rank.

### 9.1 The multi-persistent born-root arm is floor-admissible

Run the maximal-drop exact recursion and take a subsequence on which both
`p^n→p` and its selected roots converge.  The limiting selected root is exact
against `U(p)` and has zero debt drop.  If `p` has at least two positive debt
coordinates, the reviewed zero-drop classification forces this limiting root
to be all Continue.  Therefore all Continue is exact against `U(p)`, and the
hard Fin4 normal-core implication gives

\[
 P_i\le r_i(\{i\})\le U_i(p)\qquad(\forall i).               \tag{9.11}
\]

So `U(p)` is punishment-floor admissible, and the prelimit tail shortfalls
in (8.6) tend to zero.  If any positive-drop exact root is born at this same
limit, (8.2)--(8.6) make it a literal fixed-charge approximate floor-
admissible row at sufficiently late actual sources.  In this multi-debtor
case, lower hemicontinuity failure is therefore **not** an unaccounted
exactness obstruction.

The unresolved floor mismatch is narrower: it can survive at a unique-debtor
zero-drop limit whose selected root is the solo-owner equality gate rather
than all Continue.  That gate gives `U_k=r_k({k})` for the persistent owner,
but it need not give `r_j({j})≤U_j` for the three zero-debt outsiders.  A born
root there may consequently have an order-one outsider floor defect, exactly
the mismatch not controlled by (8.6).

## 10. Positive-survival recursion renews only an escaping exact cap clock

The positive-survival arm of the reviewed first-root theorem admits a sharper
exact iteration.  It is a theorem, but its conclusion is the all-summable
moving-clock residual rather than a charged return.

Let `tau^0` be one of the structured stationary sources.  Suppose literal
Quit0 is an exact complete cap for player `b` there and

\[
 d_{0,b}\ge\gamma>0.                                      \tag{10.1}
\]

The reviewed cap-pin theorem also gives, for the first selected root,

\[
 D_1\le D_0-\delta_b                                      \tag{10.1a}
\]

with one fixed `delta_b>0`.  This strict expenditure is retained throughout
the construction, but the cap pin needed to repeat the same fixed decrease
is not.

Run the literal recursion (1.2).  Write

\[
 h_{n,i}=q^n_i,
 \qquad c_n=\prod_i(1-h_{n,i}),
 \qquad s_{n,b}=\prod_{i\ne b}(1-h_{n,i}).                 \tag{10.2}
\]

Assume first that every recursive root has positive joint survival,
`c_n>0`.  Let `A^0` be Quit0 and define `A^(n+1)` by forcing `b` to Continue
at the new root and then using `A^n` in the old tail.  Thus `A^n` is the
literal deterministic quit time `n` in `tau^n`.

### Theorem 10.1 (exact escaping-cap transport)

For every `n`, `A^n` attains player `b`'s complete unrestricted behavioral
cap at `tau^n`, and

\[
 d_{n+1,b}=s_{n,b}d_{n,b},
 \qquad
 d_{N,b}=d_{0,b}\prod_{n<N}s_{n,b}.                         \tag{10.3}
\]

There is also a second, generally non-cap, response at the newest prefix: it
copies `b`'s prescribed root randomization and, conditional on joint
Continue, uses `A^n`.  Its exact gain is

\[
 c_nd_{n,b}=(1-h_{n,b})d_{n+1,b}.                           \tag{10.4}
\]

After installing this copied response, the residual `b`-debt is exactly

\[
 h_{n,b}d_{n+1,b}.                                          \tag{10.5}
\]

In particular, unless `h_(n,b)=0`, the copied delayed paid response cannot be
an exact Nash--Bellman repair: at the new root, Continue has become strictly
better than Quit for `b`, and (10.5) is the exact root support defect.

**Proof.**  Positive joint survival gives `h_(n,b)<1`.  Since `q^n` is exact
Nash against `U^n`, positive Continue probability implies

\[
 Q_b(q^n_{-b})\le C_b(q^n_{-b};U^n_b).                      \tag{10.6}
\]

If `b` also Quits with positive probability, equality holds.  Raising the
tail coordinate from `U^n_b` to `B^n_b` changes the Continue endpoint by
exactly `s_(n,b)d_(n,b)`.  Hence the complete cap at the prefixed profile is
the Continue-then-old-cap branch.  The prescribed prefixed payoff of `b` is
the old Continue endpoint: this is immediate when `h_(n,b)=0`, and follows
from endpoint indifference otherwise.  Subtraction proves the first identity
in (10.3), and induction proves the second.

The copied response changes no root-absorbing outcome.  Joint Continue,
whose exact probability is `c_n`, exposes the old tail cap gain `d_(n,b)`;
this proves (10.4).  The opponents of `b` have not changed, so its complete
cap is still the Continue-then-old-cap value.  Subtracting (10.4) from
`d_(n+1,b)` gives (10.5).  When `h_(n,b)>0`, old exactness made Quit and
Continue equal at the prescribed tail, while the cap-tail replacement raises
only Continue by `s_(n,b)d_(n,b)>0`.  Thus (10.5) is also the literal
support-Nash defect.  `QED`

### Theorem 10.2 (bounded capacity forces positive source reach)

Assume the Fin4 game has no uniform-equilibrium payoff.  Then there is a
finite `K` such that

\[
 \sum_{n<N}\sum_i h_{n,i}\le K\qquad(N\ge1).                \tag{10.7}
\]

Consequently

\[
 \sum_n\sum_i h_{n,i}<\infty,
 \qquad
 C_\infty:=\prod_n c_n>0,                                   \tag{10.8}
\]

and the original structured source, together with its original paid row, is
reached through every finite reverse-prefix word with probability at least
`C_infinity`.  Moreover

\[
 d_{N,b}\ge C_\infty d_{0,b}\ge C_\infty\gamma.             \tag{10.9}
\]

**Proof.**  For each `N`, read the literal word in its true chronological
order:

\[
 q^{N-1},q^{N-2},\ldots,q^0,\tau^0.                         \tag{10.10}
\]

Its displayed values are
`U^N,U^(N-1),...,U^0`.  The Bellman identity is literal prefixing, and every
root is exact Nash against the next displayed value.  Actual terminal payoff
vectors lie in the canonical reward box.  Thus (10.10) is a finite exact
Nash--Bellman block whose hazard charge is exactly the left side of (10.7).
The checked counterexample-side bounded-capacity theorem supplies one common
`K`.

Since all summands are nonnegative, (10.7) gives the series statement.  Each
`h_(n,i)<1` because `c_n>0`; the standard positive-product criterion then
gives `C_infinity>0`.  Literal joint survival through the word is
`product_(n<N)c_n`, proving the source-reach assertion.  Finally
`s_(n,b)>=c_n`, so (10.3) gives (10.9).  `QED`

### Corollary 10.3 (literal terminal cap child and distinct paid debtor)

For every `N`, make the literal unilateral update

\[
 \zeta^N=\tau^N[b\leftarrow A^N].                           \tag{10.10a}
\]

Then `zeta^N` is terminal by date `N`, the edge
`tau^N -> zeta^N` attains `b`'s complete behavioral cap with gain at least
`C_infinity gamma`, and

\[
 d_b(\zeta^N)=0.                                            \tag{10.10b}
\]

The fixed terminal exploitability gap therefore selects a player
`j_N != b` with `d_(j_N)(zeta^N)>=Gamma`.  Along a subsequence the label is
one fixed `j`.  Because `b` surely Quits by date `N`, `j`'s complete response
problem is finite: times after `N` are equivalent to Never, while time `N`
retains the tie outcome.  Hence the cap is attained in

\[
 \{0,1,\ldots,N,\operatorname{Never}\}.                     \tag{10.10c}
\]

Comparing this maximizer with a pure-time component no better than the
prescribed strategy gives a literal paid first-disagreement row of gain
`Gamma`, whose first cut is at most `N`.  If rewards are bounded by `M>0`,
its opponents' live mass is at least `Gamma/(2M)`.

This is an actual two-edge source chronology:

\[
 \tau^N\xrightarrow[\text{clock }N]{b\text{ exact cap}}\zeta^N
 \xrightarrow{j\text{ paid row}}\text{response sibling}.   \tag{10.10d}
\]

It feeds the checked generic paid-row interface, but not a Nash--Bellman
return.  The first edge changes `b` at every prefixed date, and the old exact
root inequalities for the other three players need not survive.

### 10.4 The front limit is exactly the all-Continue phantom

Let `R` bound all terminal rewards.  One prefix changes a prescribed payoff
coordinate by at most

\[
 |U^{n+1}_i-U^n_i|\le2R(1-c_n)\le2R\sum_jh_{n,j}.           \tag{10.11}
\]

Equations (10.7)--(10.8) make `U^n` Cauchy; write its limit as
`U^infinity`.  Also `q^n` tends coordinatewise to all Continue.  Therefore,
viewed from the front of the chronological block (10.10), every fixed finite
window converges to the constant path

\[
 (U^\infty,\mathrm{allContinue}),
 (U^\infty,\mathrm{allContinue}),\ldots .                   \tag{10.12}
\]

Continuity of root Nash defects shows that all Continue is exact against
`U^infinity`; its Bellman action fixes `U^infinity`.  Hence (10.12) is exactly
the canonical all-Continue phantom spine.  The old source remains uniformly
reachable at the **far end of every finite block**, but its position and the
cap clock `A^N` both tend to infinity.  Neither survives at a finite date of
the front limit.

### 10.5 Exact finite obstruction to cap-update Nashification

The failure is already visible before taking a limit.  Replace the old tail
strategy of `b` by its cap while keeping the newest root distribution fixed.
For an outsider `i`, let `Delta_i` be the resulting change in its old-tail
payoff.  Its newest-root Quit-minus-Continue gap changes by exactly

\[
 -s_{n,i}\Delta_i.                                         \tag{10.13}
\]

The structured source controls neither the sign nor the size of these three
numbers.  For `b` itself, (10.5) says that any positive prescribed Quit mass
creates the exact defect `h_(n,b)s_(n,b)d_(n,b)`.  Forcing `b` to Continue
at the newest root removes its own defect, but it also changes the outsiders'
current opponent law; their endpoint differences then contain additional
uncontrolled current-row terms besides (10.13).  Positive survival makes the
continuation terms visible rather than small.  Thus neither version produces
an exact source-reprojected block from cap transport alone.

If some later `c_n` is zero instead, positive carrier debt rules out two sure
quitters at that finite root.  There is one sure owner `k`; every other child
debt is exactly zero and `k` carries all of the positive debt.  This is an
actual unique-debtor cap-tail reset, but repeating its root stationarily or
passing to the checked singleton handoff is a new source construction, not a
literal return of the finite child.

Theorems 10.1--10.2 are the exact producer/consumer verdict for the positive-
survival arm:

\[
 \boxed{\text{renewed exact cap with positive source reach}
 \;=\;\text{escaping clock on a bounded-charge reverse block},}       \tag{10.14}
\]

not a renewable forward source.  Any further consumer must retain a mark at
the far end of an all-summable exact block or control the three signed tail
changes in (10.13).  The existing exact-spine and paid-row consumers do
neither.

## Conjecture-facing conclusion

The recursive literal-`U` construction does not merely return to an
unstructured horizontal response cycle.  It produces a genuine monotone
object: an actual semantic descent with nonreactivating debt support and a
sharp all-summable-versus-one-persistent limit.

Its exact terminal obstruction is also sharp.  After the reviewed first
fixed drop, the process can encounter an all-Continue exact root while
retaining positive late-tail debt.  In that case the source passport has not
been regenerated; it has become a delayed option measured only by (2.5).
Normal-core punishment normality shows that this inert descendant can satisfy
the punishment floors, so the floor condition cannot eliminate it.  Thus the
next useful theorem must either consume the one-persistent reverse spine,
compactify the all-summable reverse-prefix family without losing terminal
mass, or force a positive-hazard root from some global selection principle.
Maximal-drop selection sharpens the last task: a root born at a limit already
has the right fixed-charge approximate Bellman and ancestry fields, but the
tropical source does not initially put its prescribed payoff near the
punishment box.  After maximal-drop iteration, that mismatch is confined to
the unique-persistent solo-owner equality gate; a multi-persistent limiting
all-Continue face is floor-safe.

The positive-survival structured branch is sharper still.  The old paid
option does not disappear algebraically: it stays the exact cap at every
finite descendant and retains a positive source reach.  What disappears is
its finite chronological location.  Bounded capacity forces the surrounding
root hazards to be summable, the cap time tends to infinity, and every fixed
front window tends to the all-Continue phantom.  Thus neither ordinary spine
compactness nor generic paid-row localization sees both the exact root edges
and the far-end source mark at once.

## Next exact question

Can the exact far-end datum in Theorem 10.2 be consumed without moving it to
the front: finite exact Nash--Bellman blocks of unbounded length, uniformly
positive reach to one fixed actual paid source, and one fixed player's exact
cap equal to the terminal-depth clock?  A valid theorem must either compile
that escaping exact cap into terminal approximate Nash profiles or extract a
source-matched return before the mark.  Compactifying the fronts alone is
insufficient, because it gives exactly (10.12).

Separately, if a recursive root has zero survival, the remaining question is
whether its actual finite unique-debtor child can enter the reviewed
singleton-base handoff without replacing it by stationary repetition of its
root.  That is the precise finite-source ancestry seam.
