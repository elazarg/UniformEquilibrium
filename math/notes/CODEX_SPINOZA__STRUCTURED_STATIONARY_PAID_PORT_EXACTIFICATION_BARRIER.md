# Structured stationary paid ports have a macroscopic exactification barrier

Author: `CODEX_SPINOZA`

## Status

**Complete ordinary-mathematics local theorem and conjecture-facing stop;
not checked in Lean.**  The tropical chain supplies more than a generic paid
port: its final source is stationary, its profitable Quit0 row is reached at
date zero, and the all-Continue successor is literally the same source.  This
note proves the strongest consequence of those extra fields that I can
justify.

A root which is exact or approximately Nash and remains locally
source-matched cannot spread the paid Quit incentive over a soft absorbing
block.  It makes the payer almost surely Quit and its Bellman predecessor
stays a fixed distance from the source payoff.  Otherwise the root must move
either the opponents' product law or the payer's tail value by a fixed amount.
For the vanishing-hazard tropical sources, a macroscopic opponent-law move is
itself macroscopic absorption.

For the literal prescribed-payoff tail \(U\), the exact prefix-debt identity
gives more: every debt coordinate weakly decreases and the payer's debt drops
by a fixed amount.  Thus this source must itself lie a fixed total-debt
distance above the global minimum.  The limiting root has three exact
geometric cases.  Two sure quitters give an unrestricted terminal Nash
profile.  One sure quitter leaves only that quitter as a possible debtor and
produces a singleton-base reset candidate, but not the punishment-floor field
required by the checked reset compiler.  A genuinely mixed absorbing root
with no sure quitter remains possible; an exact four-player boundary table
below shows that the structured local paid-source fields do not exclude it.

Thus every attempted exactification has fixed physical charge or a fixed
payoff/source seam.  This is useful exclusion of a small local block, but it
does **not** supply the missing returned source.  Bounded exact-block capacity
would contradict infinitely many such re-entries; the tropical chain produces
only one and does not reproject its sure-Quit target.  The structured fields
therefore still terminate at the existing off-minimum paid-port waist.

## Question

Let \(\tau_n\) be the final stationary source produced by the reviewed
tropical chronology.  A fixed player \(b\) has Quit0 as an exact unrestricted
cap response with gain bounded below, every date-zero Continue probability
tends to one, and conditional on joint Continue the literal successor is
again \(\tau_n\).  Can this row be softened or exactified into a
source-reprojected Nash--Bellman block with positive survival and seam small
relative to its absorption charge?

The local answer is no.  Nash complementarity forces a macroscopic event or
a macroscopic seam.  The global question of returning from that event remains
open.

## Sources inspected

- `questions/FIN4_QUANTITATIVE_PAID_PORT_CONSUMER.md`: accepted chronology,
  rank, and counterexample outputs.
- `notes/CODEX_SNELL__TROPICAL_SUPPORT_FOUR_TWO_OWNER_ENDPOINT_EXIT.md` and
  `notes/CODEX_SPINOZA__SINGLETON_DESCENT_REACTIVATION_OFFMINIMUM_COLLAR.md`:
  the structured stationary source, exact Quit0 cap, and \(D_*\) collar.
- `notes/CHATGPT_EXTERNAL__PAID_CAP_PORT_EXACT_TRICHOTOMY_AND_INERT_STALL.md`:
  the cap-prefix charge/debt trichotomy and inert stall.
- `notes/SOCIAL_WEIGHT_REVIEW__PURE_CLOCK_AFFINE_TRANSLATION_LOCALIZES_TO_DATE_ZERO.md`:
  date-zero localization and the exactification action-reversal boundary.
- `notes/CODEX_DESCENDANT__FINITE_PAID_CYCLE_EXACT_SHADOW_DUALITY.md`:
  the root-Nash/source-seam Farkas obstruction for horizontal paid words.
- `UniformEquilibrium/Quitting/Root/FirstBranch.lean`:
  `IsεQuittingRootNash`.
- `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`:
  `IsεQuittingRootEndpointNash`,
  `quittingRootQuitPayoff_sub_successorPayoff`, and
  `quittingRootContinuePayoff_sub_successorPayoff`.
- `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`:
  `quittingTerminalSemanticDebt_prefix_eq_blockAct` and
  `quittingTerminalSemanticDebt_prefix_le`.
- `UniformEquilibrium/Quitting/Root/TerminalSemanticEqualityStratum.lean`:
  the exact minimum-fibre debt rigidity used for comparison.
- `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseInducedGame.lean`
  and
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/SingletonBaseSameLawResetProducer.lean`:
  the induced singleton-base Nash set and the additional punishment-floor,
  atom, law, and reset fields required by the checked producer.
- `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`:
  `IsQuittingNashBellmanEdge` and the exact Bellman successor map.

## 1. One stationary paid source

Let \(I\) be finite and let all terminal rewards be bounded in absolute value
by \(M>0\).  Fix one stationary behavioral profile \(\tau\), with date-zero
Quit probabilities \(x_i\), prescribed terminal payoff \(u=U(\tau)\), and a
player \(b\).  Assume

\[
 x_b<1,
 \qquad
 Q_b(x_{-b})-u_b\ge \gamma>0,                                  \tag{1.1}
\]

where \(Q_b(x_{-b})\) is the payoff from Quit at date zero against the
source opponents.  In the tropical application Quit0 is the exact complete
behavioral cap and the left side of (1.1) is the selected debt, uniformly
bounded below on a common tail.

For an arbitrary opponent product root \(q_{-b}\) and an arbitrary bounded
tail vector \(v\), let \(\pi_q\) be the distribution of the opponent quitting
set \(A\subseteq I\setminus\{b\}\), and define

\[
\begin{aligned}
 Q_b(q_{-b})
   &=\sum_A\pi_q(A)r_b(A\cup\{b\}),\\
 C_b(q_{-b};v)
   &=\pi_q(\varnothing)v_b
     +\sum_{A\ne\varnothing}\pi_q(A)r_b(A),\\
 \Delta_b(q_{-b};v)&=Q_b(q_{-b})-C_b(q_{-b};v).
                                                                    \tag{1.2}
\end{aligned}
\]

Stationarity says that after player \(b\) and every opponent Continue at the
source row, the continuation is literally \(\tau\).  Hence the one-row
Bellman identity is

\[
 u_b=x_bQ_b(x_{-b})+(1-x_b)C_b(x_{-b};u).                         \tag{1.3}
\]

Combining (1.1)--(1.3) gives the conditional row margin

\[
 \boxed{\Delta_b(x_{-b};u)
   ={Q_b(x_{-b})-u_b\over1-x_b}\ge\gamma.}                       \tag{1.4}
\]

This is the exact gain supplied by the literal stationary successor field.
It is at least the whole-profile Quit0 gain, rather than that gain multiplied
by a small hazard.

## 2. A Lipschitz seam inequality

For distributions on opponent subsets use the \(\ell^1\) distance

\[
 \|\pi_q-\pi_x\|_1=\sum_A|\pi_q(A)-\pi_x(A)|.                    \tag{2.1}
\]

Assume \(|u_b|,|v_b|\le M\).  Then

\[
 \boxed{
 |\Delta_b(q_{-b};v)-\Delta_b(x_{-b};u)|
 \le 2M\|\pi_q-\pi_x\|_1+|v_b-u_b|.}                           \tag{2.2}
\]

Indeed, for fixed tail value \(u_b\), the integrand

\[
 f_u(A)=
 \begin{cases}
 r_b(A\cup\{b\})-r_b(A),&A\ne\varnothing,\\
 r_b(\{b\})-u_b,&A=\varnothing
 \end{cases}                                                     \tag{2.3}
\]

has absolute value at most \(2M\).  Changing the opponent law gives the
first term in (2.2); changing the tail affects only the empty-opponent cell
and gives the second.  Under the standard independent coupling,

\[
 \|\pi_q-\pi_x\|_1
 \le2\sum_{j\ne b}|q_j-x_j|.                                    \tag{2.4}
\]

No terminal-law compactness or differentiability is used.

## 3. Exact and approximate Nash roots cannot stay soft and local

Let \(q\) be a product root against tail \(v\), and suppose it is
\(\varepsilon\)-endpoint-Nash.  Write

\[
 c_b=1-q_b
\]

for the payer's Continue probability.  The exact endpoint-Nash inequality
from `SuccessorCertificate.lean` is

\[
 c_b\Delta_b(q_{-b};v)\le\varepsilon.                            \tag{3.1}
\]

### Theorem 3.1 (local exactification collapse)

If

\[
 2M\|\pi_q-\pi_x\|_1+|v_b-u_b|\le {\gamma\over2},               \tag{3.2}
\]

then

\[
 \Delta_b(q_{-b};v)\ge{\gamma\over2},
 \qquad
 c_b\le {2\varepsilon\over\gamma}.                              \tag{3.3}
\]

In particular, for an exact root \(\varepsilon=0\), player \(b\) Quits
surely.  The root has joint Continue mass zero, so it cannot be a
positive-survival returned block.

For approximate roots with \(\varepsilon\to0\), total absorption tends to
one.  Thus the stationary paid row cannot be implemented by assigning a
small Quit hazard to \(b\): because Continue remains a strictly inferior
endpoint, its root regret is the Continue probability times the fixed
conditional margin, not the Quit hazard times that margin.

### Proof

Equations (1.4), (2.2), and (3.2) give the first inequality in (3.3).
Insert it into (3.1).  The exact statement is the specialization
\(\varepsilon=0\). \(\square\)

## 4. The Bellman predecessor also misses the source

Let

\[
 w=\operatorname{Succ}(q,v)
\]

be the root's Bellman predecessor payoff.  Suppose the hypotheses of
Theorem 3.1 hold and, in addition,

\[
 \|\pi_q-\pi_x\|_1\le {\gamma\over4M}.                            \tag{4.1}
\]

The Quit endpoint does not depend on the tail and satisfies

\[
 Q_b(q_{-b})-u_b
 \ge Q_b(x_{-b})-u_b-M\|\pi_q-\pi_x\|_1
 \ge {3\gamma\over4}.                                           \tag{4.2}
\]

Since \(|Q_b(q_{-b})-C_b(q_{-b};v)|\le2M\),

\[
 |w_b-Q_b(q_{-b})|\le2Mc_b.                                     \tag{4.3}
\]

Combining (3.3), (4.2), and (4.3) gives

\[
 w_b-u_b\ge {3\gamma\over4}-{4M\varepsilon\over\gamma}.       \tag{4.4}
\]

Thus, whenever

\[
 \varepsilon\le {\gamma^2\over16M},                             \tag{4.5}
\]

one has the fixed predecessor seam

\[
 \boxed{w_b-u_b\ge {\gamma\over2}.}                             \tag{4.6}
\]

Consequently there is no sequence of source-local approximate
Nash--Bellman rows whose tail and predecessor both approach the stationary
source while root error tends to zero.  Exact local Nashification does not
merely remove survival; it places the predecessor a fixed payoff distance
from the desired source.

## 5. Macroscopic trichotomy for the tropical sequence

Return to the tropical final sources \(\tau_n\).  On a common tail their
Quit0 gains are at least a fixed \(\gamma>0\), their opponent hazards tend to
zero, and all payoffs are bounded by one common \(M\).  Consider any proposed
\(\varepsilon_n\)-Nash root \(q_n\), bounded tail \(v_n\), and predecessor
\(w_n=\operatorname{Succ}(q_n,v_n)\), with \(\varepsilon_n\to0\).

After passage to a subsequence, at least one of the following holds:

1. **opponent-root displacement:**
   \(\|\pi_{q_n}-\pi_{x_n}\|_1\ge\gamma/(8M)\), hence the opponents'
   root absorption probability has a fixed positive lower bound because
   \(\pi_{x_n}\to\delta_\varnothing\);
2. **tail seam:** \(|v_{n,b}-u_{n,b}|\ge\gamma/4\);
3. **payer collapse and predecessor seam:** \(q_{n,b}\to1\), total root
   absorption tends to one, and \(w_{n,b}-u_{n,b}\ge\gamma/2\) eventually.

The constants are deliberately loose.  If neither item 1 nor item 2 holds,
then (3.2) and (4.1) hold eventually, so Theorem 3.1 and (4.6) give item 3.

This is the exact gain from the structured stationary fields.  A proposed
source-matched exactification cannot hide in a vanishing-absorption local
root.  It must cross a fixed opponent-law/tail seam, or terminate through an
almost sure payer root and a fixed Bellman seam.

## 6. Why the short tropical ancestry does not pay the seam

The finite chronology before the last row consists of at most three Never
updates.  It proves that the final source is an actual stationary descendant
of the unconditional tropical source.  It does not supply any of the data
needed to orient the alternatives in Section 5:

- the proposed root's changed opponent product law is not one of the earlier
  stationary source faces;
- its tail value is not identified with an earlier source payoff or cap;
- its Bellman predecessor is not the next source in the response genealogy;
  and
- the final sure-Quit target is not a renewable stationary singleton source,
  because deleting its new quitter exposes the old owner(s).

The \(D_*\) collar is likewise transverse to (2.2).  It says that the final
source cap satisfies \(B_b=s_b\), whereas every minimum-fibre cap has
\(B_b\ge s_b+D_*\).  It does not identify the continuation payoff coordinate
\(v_b\), the root opponent law, or the predecessor \(w_b\) with a literal
minimum source.  Treating this cap displacement as the tail seam in (3.2)
would be the cap-versus-prescribed-payoff surcharge error already isolated in
the generic paid-port audit.

Bounded exact-block capacity would become decisive **after** a renewable
source-attached return is supplied: Section 5 forces every sufficiently
accurate return attempt to carry fixed absorption or a fixed seam, so an
infinite summable-charge local stack is impossible.  The current tropical
chain supplies only one such port.  Capacity cannot create the missing
successor-to-source identification.

There is also no finite rank in the visible support genealogy.  Never updates
strictly reduce the active stationary support, but the final Quit0 response
reactivates a removed player and its deleted law remembers the old support.
Restarting from the apparent singleton terminal law therefore resets the
rank rather than decreasing it on complete source states.

## 7. The stationary genealogy has the wrong Bellman seam

Stationarity gives an exact formula for trying to reinterpret the literal
response ancestry as temporal play.  Write the one-row payoff map as

\[
 F(q,v)=G(q)+c(q)v,                                               \tag{7.1}
\]

where \(c(q)\) is the joint all-Continue probability and \(G(q)\) is the
absorbing contribution.  If a stationary profile has row \(x\) and payoff
\(u\), then

\[
 u=F(x,u).
\]

Consequently, for every proposed replacement tail \(v\),

\[
 \boxed{F(x,v)-u=c(x)(v-u).}                                    \tag{7.2}
\]

Let \(u^\ell,u^{\ell+1}\) be consecutive stationary payoffs in the tropical
Never genealogy, and let \(i_\ell\) be the response mover.  Installing the
child as a temporal tail behind the parent's literal row gives

\[
 F(x^\ell,u^{\ell+1})_{i_\ell}-u^\ell_{i_\ell}
 =c(x^\ell)
  (u^{\ell+1}_{i_\ell}-u^\ell_{i_\ell}).                        \tag{7.3}
\]

The last factor is exactly the mover's positive whole-profile response gain,
while \(c(x^\ell)\to1\) in the tropical sequence.  Hence the attempted
temporalization retains essentially the entire horizontal payoff seam; it
does not make it small.  The reverse orientation has the same defect with
the opposite sign.

This is stronger than saying abstractly that response time differs from play
time.  The stationarity/self-tail field computes the missing Bellman equality
and shows that it fails by a fixed amount on the very coordinate that paid
for the response.  Earlier ancestry cannot be used as the successor side of
an exact return without a new compensating root.

The final sure-Quit target is different.  Its pure root absorbs surely, so its
prescribed payoff is independent of the hypothetical tail and it does satisfy
a Bellman equation over the old source payoff.  The payer's root inequality
is inherited from its complete Quit0 response.  But no inequality for the
other three players is inherited.  Nashifying those coordinates changes the
opponent product law seen by the payer, landing exactly in item 1 of Section
5 or destroying the payer inequality.  Thus the sure-Quit row repairs the
Bellman equality and loses joint root Nash; the old stationary row has its
own fixed point and loses the source-to-child Bellman equality.

## 8. A charged payoff-tail entrance and the cap-tail obstruction

There is one genuine exact Nash--Bellman object hidden in the structured
port.  For each source payoff \(u_n\), choose a mixed Nash equilibrium
\(q_n\) of the finite one-stage quitting game whose all-Continue payoff is
\(u_n\), and put

\[
 w_n=F(q_n,u_n).                                                  \tag{8.1}
\]

Finite-game Nash existence and (8.1) make \(w_n\to u_n\) an exact
Nash--Bellman edge in the sense of `IsQuittingNashBellmanEdge`.  Moreover its
absorption is uniformly macroscopic.  Apply Section 5 with \(v_n=u_n\) and
\(\varepsilon_n=0\).  Either the opponents' law moves a fixed distance from
the vanishing-hazard source law, in which case opponent absorption is bounded
below, or the payer Quits surely.  Indeed, once
\(\|\pi_{x_n}-\delta_\varnothing\|_1\le\gamma/(16M)\), item 1 gives
opponent absorption at least \(\gamma/(32M)\), while the local alternative
gives payer absorption one.  Thus, with
\(a_0=\min\{1,\gamma/(32M)\}>0\),

\[
 \boxed{\operatorname{Abs}(q_n)\ge a_0}                          \tag{8.2}
\]

for every sufficiently large \(n\).

This is a source-attached charged **entrance**: one may prefix \(q_n\) to the
literal source profile \(\tau_n\), and its continuation payoff in the
Bellman equation is the actual \(U(\tau_n)\).  It is not yet a returned block.
After moving backward to \(w_n\), the stationary source and its paid row have
not been regenerated.  The finite ancestry contains only the payoffs
\(u_n^\ell\), and (7.2) supplies no equality identifying \(w_n\) with any of
them.

More importantly, exact-block debt capacity applies to roots Nash against a
complete cap or to an already punishment-floor-admissible Nash--Bellman
spine.  Prefixing a
root Nash only against \(U(\tau_n)\) does not screen deviations which Continue
through the root and then exploit the non-Nash tail.  Those deviations see
\(B(\tau_n)\), not \(U(\tau_n)\).

If instead one selects an exact root against the cap tail \(B(\tau_n)\), the
payer coordinate has been raised by precisely its source debt:

\[
 B_b(\tau_n)-U_b(\tau_n)\ge\gamma.                               \tag{8.3}
\]

This is already a macroscopic tail seam in Section 5.  The stationary paid
margin therefore supplies no absorption lower bound in the cap-tail game;
all Continue may be exact, which is the maintained inert cap-prefix branch.
We obtain the sharp two-tail fork

\[
\boxed{
\begin{array}{c}
\text{payoff tail }U:\ \text{fixed-charge exact Nash--Bellman entrance,}
\text{ but no complete-tail cap screening};\\
\text{cap tail }B:\ \text{complete-deviation-compatible root,}
\text{ but the paid margin is spent as surcharge and inertness remains.}
\end{array}}                                                     \tag{8.4}
\]

The exact missing state variable is therefore not another support label.  It
is a source-attached equality identifying an admissible continuation value
with both the prescribed payoff used by the charged root and the complete
continuation cap needed to protect deviations in the tail.  Positive debt
says these two coordinates are separated at the payer.

## 9. The asymmetric continuation box is annotation-only

The most favorable asymmetric interpolation still leaves an exact residual.
Let \(U,B\) be the prescribed-payoff and complete-cap vectors of one actual
source profile \(\tau\), put \(d=B-U\ge0\), and choose any coordinatewise
intermediate vector

\[
 U\le V\le B.                                                     \tag{9.1}
\]

Let \(q\) be an exact product root Nash against \(V\), and let \(\rho\) be
the **actual** profile which plays \(q\) once and, after joint Continue,
plays \(\tau\).  Write \(c\) for the root's joint Continue probability and
\(c_{-i}\) for the opponents' joint Continue probability.  For player \(i\),
write \(Q_i(q)\) for its pure-Quit endpoint and \(C_i(q;z_i)\) for its
pure-Continue endpoint when the all-Continue tail pays \(z_i\).

Arbitrary behavioral deviation in \(\rho\) gives the exact cap formula

\[
 B_i(\rho)=\max\{Q_i(q),C_i(q;B_i)\}.                            \tag{9.2}
\]

Indeed, after a deviating Continue action and joint opponent Continue, the
deviator may use its complete best response in the literal tail.  Conversely
every deviation decomposes into its first action and a tail deviation, so no
larger value is possible.  The prescribed payoff is

\[
 U_i(\rho)=F_i(q,U).                                              \tag{9.3}
\]

Exact root Nash against \(V\) gives

\[
 F_i(q,V)=\max\{Q_i(q),C_i(q;V_i)\}.                             \tag{9.4}
\]

Since changing the common tail changes the prescribed root payoff only on
joint Continue,

\[
 F_i(q,V)-F_i(q,U)=c(V_i-U_i).                                  \tag{9.5}
\]

Combining (9.2)--(9.5) gives the exact debt decomposition

\[
\boxed{
 d_i(\rho)=R_i(q,V)+c(V_i-U_i),}                                 \tag{9.6}
\]

where

\[
 R_i(q,V)=
 \max\{Q_i(q),C_i(q;B_i)\}
 -\max\{Q_i(q),C_i(q;V_i)\}                                    \tag{9.7}
\]

satisfies

\[
 0\le R_i(q,V)\le c_{-i}(B_i-V_i).                              \tag{9.8}
\]

If \(q_i<1\), exact root Nash says Continue is a maximizing endpoint, so in
fact

\[
 R_i(q,V)=c_{-i}(B_i-V_i).                                      \tag{9.9}
\]

If \(q_i=1\), then

\[
 R_i(q,V)=
 [C_i(q;U_i)+c_{-i}d_i-Q_i(q)]_+.                               \tag{9.10}
\]

In all cases the simpler unavoidable-tail bound follows:

\[
 \boxed{d_i(\rho)\ge c\,d_i.}                                  \tag{9.11}
\]

This can also be seen directly: the player may copy its prescribed root
randomization and switch only to a cap-attaining continuation on joint
Continue.

### 9.1 The proposed hybrid vector

Now take

\[
 V_b=U_b,
 \qquad V_j=B_j\quad(j\ne b).                                   \tag{9.12}
\]

For every nonmover \(j\ne b\), equations (9.6)--(9.8) give the exact
transport identity

\[
 d_j(\rho)=c\,d_j.                                               \tag{9.13}
\]

Thus putting the nonmover cap coordinates into the one-stage Nash game does
not screen their actual tail deviations; it transports every old debt through
the joint-survival event.

For the paid mover, if \(q_b<1\), (9.9) gives the sharper residual

\[
 \boxed{d_b(\rho)=c_{-b}d_b.}                                   \tag{9.14}
\]

If \(q_b=1\), root absorption is already one and the remaining debt is the
positive part in (9.10).  Consequently, when \(d_b\ge\gamma>0\), every
sequence of hybrid-root prefixes which is terminal \(\varepsilon_n\)-Nash
with \(\varepsilon_n\to0\) has total root absorption tending to one: either
the payer is sure Quit, or (9.14) forces \(c_{-b}\le\varepsilon_n/\gamma\).
There is no positive-survival hybrid return.

### 9.2 The one-coordinate homotopy

More generally set \(V_j=B_j\) for \(j\ne b\) and

\[
 V_b(t)=U_b+t d_b,qquad0\le t\le1.                              \tag{9.15}
\]

If \(q_b(t)<1\), the exact formula becomes

\[
 d_b(\rho_t)
 =c_{-b}(1-t)d_b+c\,t d_b
 =c_{-b}(1-tq_b)d_b.                                            \tag{9.16}
\]

At \(t=0\), Section 8 forces a macroscopic absorbing root but (9.14) leaves
the payer's continuation-cap residual.  At \(t=1\), the root is cap-Nash and
the residual is the usual transported debt \(cd_b\), but the all-Continue
inert root may be selected.  An intermediate-value or equilibrium-index
continuation between these endpoints does not change (9.16).  Unless survival
vanishes, the actual prefixed profile retains positive debt.

There is a more basic source problem: \(V(t)\) is only a coordinatewise
annotation.  The entries \(B_j\) are suprema attained by different unilateral
counterfactual strategies; no single continuation profile is supplied whose
prescribed payoff is \(V(t)\).  The abstract edge

\[
 F(q(t),V(t))\longrightarrow V(t)
\]

is therefore not a source-attached temporal edge.  Prefixing the root to the
only supplied literal tail \(\tau\) instead gives (9.3) and the residual
(9.6).  A component or index theorem can select roots inside the annotated
box, but cannot manufacture the absent common continuation realizer.

The checked Solan--Vieille boundary is the appropriate falsifier for treating
component continuation as source anchoring.  Its literal full-response
four-cycle has fixed gains and exact source seams at the horizontal profiles,
while every proposed literal exact shadow fails root Nash and Bellman seam;
the table's genuine exact period-two equilibrium uses different roots and
continuation states.  Hence finite-game index preserves existence somewhere,
not the root support or literal genealogy needed here.  That table has a
uniform equilibrium and is not a positive-gap counterexample; it tests the
claimed bridge only.

The asymmetric construction therefore sharpens the obstruction but does not
solve it:

\[
\boxed{
\begin{array}{c}
\text{hybrid root Nash at }V
\ +\ \text{literal source tail }U\\
\Longrightarrow
\text{old tail debts transported by }c
\ +\ \text{payer residual (9.14),}
\end{array}}                                                     \tag{9.17}
\]

while treating \(V\) itself as the literal tail is an annotation-only
decoder.

## 10. Literal-\(U\) roots spend a fixed amount of actual debt

The literal payoff tail has one further exact consequence which is invisible
in the payoff-only Bellman equation.  Let

\[
 p=(u,B),\qquad d_i=B_i-u_i\ge0
\]

be the actual terminal semantic pair of the stationary source, and let \(q\)
be any exact product root Nash against \(u\).  Write \(T_qp\) for the actual
semantic pair obtained by prefixing \(q\) to the literal source profile.  Put

\[
 s_i(q)=\prod_{j\ne i}(1-q_j),\qquad
 e_i(q)=\max\{0,\Delta_i(q_{-i};u)\}.
\]

The checked prefix-debt identity is

\[
 \boxed{d_i(T_qp)=[s_i(q)d_i-e_i(q)]_+.}                       \tag{10.1}
\]

In particular,

\[
 d_i(T_qp)\le s_i(q)d_i\le d_i                               \tag{10.2}
\]

for every player.  This is an all-behavior statement: \(d_i\) is the
complete continuation cap minus prescribed payoff, not a root-only endpoint
defect.

Assume now that \(|r_i(S)|\le M\), \(M>0\), and that the source satisfies

\[
 d_b=Q_b(x_{-b})-u_b\ge\gamma>0,
 \qquad
 \|\pi_x-\delta_\varnothing\|_1\le {\gamma\over8M}.       \tag{10.3}
\]

The equality in (10.3) says that Quit0 is a cap-attaining response for the
paid mover \(b\), as it is in the structured tropical port.  Define

\[
 \eta=\min\left\{{\gamma\over2},{\gamma^2\over16M}\right\}>0. \tag{10.4}
\]

### Theorem 10.1 (fixed literal-\(U\) debt expenditure)

Every exact product root Nash \(q\) against \(u\) satisfies

\[
 \boxed{
 d_b(T_qp)\le d_b-\eta,
 \qquad
 D(T_qp)\le D(p)-\eta.}                                      \tag{10.5}
\]

### Proof

Let \(\ell=\|\pi_q-\pi_x\|_1\).  If
\(\ell\le\gamma/(4M)\), (1.4) and (2.2), with the literal tail \(v=u\),
give

\[
 \Delta_b(q_{-b};u)\ge {\gamma\over2}.                       \tag{10.6}
\]

Thus \(e_b(q)\ge\gamma/2\).  Equation (10.1), together with
\(d_b\ge\gamma\), gives

\[
 d_b-[s_b(q)d_b-e_b(q)]_+
 \ge\min\{d_b,e_b(q)\}\ge{\gamma\over2}.                 \tag{10.7}
\]

If instead \(\ell\ge\gamma/(4M)\), let
\(a_{-b}=1-\pi_q(\varnothing)\) be the absorption probability generated by
the root opponents of \(b\).  Since
\(\|\pi_q-\delta_\varnothing\|_1=2a_{-b}\), the triangle inequality and
(10.3) give

\[
 2a_{-b}\ge {\gamma\over4M}-{\gamma\over8M}
 ={\gamma\over8M},
 \qquad a_{-b}\ge {\gamma\over16M}.                          \tag{10.8}
\]

Now (10.1) is at most \((1-a_{-b})d_b\), so the payer's debt drops by at
least \(a_{-b}d_b\ge\gamma^2/(16M)\).  The two cases prove the first part
of (10.5); summing it with (10.2) proves the second. \(\square\)

This turns the literal-\(U\) entrance into a genuine source-attached
quantitative debt transition.  If \(D_*\) is the global minimum of total
debt on the terminal semantic carrier, then \(T_qp\) is another actual
carrier point, and therefore

\[
 \boxed{D(p)\ge D_*+\eta.}                                   \tag{10.9}
\]

In particular, no source satisfying (10.3) can lie within \(\eta\) of the
minimum fibre.  This is the precise place where global minimality acts.  The
tropical port is not supplied as a near-minimum total-debt source: its
reviewed collar is a cap-coordinate separation from a selected minimum.
Consequently (10.9) proves that it is quantitatively off-minimum, but does not
make the one-time expenditure renewable.  The source is buried behind the
new prefix and the paid stationary row is not regenerated.

## 11. Exact geometry of a literal-\(U\) root

Complementarity makes (10.1) especially transparent.  If \(q_i<1\), player
\(i\) uses Continue with positive probability.  Exact root Nash therefore
forces \(e_i(q)=0\), and

\[
 d_i(T_qp)=s_i(q)d_i.                                          \tag{11.1}
\]

If \(q_i=1\), then

\[
 d_i(T_qp)=[s_i(q)d_i-\Delta_i(q_{-i};u)]_+.                   \tag{11.2}
\]

There are three exhaustive sure-support cases.

### 11.1 At least two sure quitters: terminal Nash

If two distinct players Quit surely under \(q\), then after any one player
deviates another sure quitter remains.  The continuation tail is never
reached, and the exact root-Nash inequalities against \(u\) are the complete
unrestricted behavioral inequalities.  Thus the one-stage profile \(q\) is
an exact terminal Nash profile.  Equivalently, every \(s_i(q)=0\) and (10.1)
gives \(d_i(T_qp)=0\) for all \(i\).

This case is impossible under a positive terminal exploitability gap and
directly yields a uniform-equilibrium payoff through the checked terminal
compiler.

### 11.2 Exactly one sure quitter: one explicit owner defect

Suppose \(k\) is the unique sure quitter.  Then \(s_i(q)=0\) for every
\(i\ne k\), so

\[
 d_i(T_qp)=0\quad(i\ne k),                                    \tag{11.3}
\]

whereas the sole remaining coordinate is exactly

\[
 \boxed{
 d_k(T_qp)=
 [C_k(q_{-k};u_k)+s_k(q)d_k-Q_k(q_{-k})]_+.}                   \tag{11.4}
\]

Under a terminal exploitability witness of gap \(\Gamma>0\), the literal
prefix \(q\star\tau\) must have some debt at least \(\Gamma\).  By
(11.3) it is necessarily \(k\), so

\[
 d_k(T_qp)\ge\Gamma.                                         \tag{11.5}
\]

The witnessing response is completely explicit: \(k\) Continues at date
zero and, on the all-opponents-Continue event, uses a cap-attaining response
in the old source tail.  Thus (11.4) is an owner continuation defect, not an
unlabelled compactness loss.

Repeating the row \(q\) stationarily gives an actual singleton-base profile.
Every free player \(i\ne k\) is screened by \(k\)'s sure date-zero Quit,
so the root-Nash inequalities make the free mixed row an exact Nash point of
the induced game with persistent base \(\{k\}\); their complete debts are
zero.  The global terminal gap can only be paid by \(k\).  This is a genuine
stationary unique-debtor **reset candidate**.

It is not yet an instance of
`FinFourSingletonBaseSameLawResetProducer`.  That structure additionally
requires every free player's realized payoff to dominate its punishment
value, as well as a heavy strict-superset atom, the target law, reset
incidence, and an attached global minimum/dispatch.  Exact induced-game Nash
does not imply the punishment-floor inequalities.  Hence the one-sure branch
identifies the exact missing field rather than silently invoking the checked
reset compiler.

### 11.3 No sure quitter: the mixed absorbing residual

If no player Quits surely, then (11.1) holds for all four players.  The root
may nevertheless have fixed absorption, and Theorem 10.1 spends a fixed part
of the payer's debt.  Neither fact identifies an owner or supplies a
stationary reset.

The following exact boundary table shows that this arm cannot be removed
using only the structured stationary paid-source fields.  Number the players
\(0,1,2,3\).  For \(h\in(0,1)\), let the stationary source have player
\(2\) Quit with probability \(h\) at every date and all other players play
Never.  It absorbs almost surely at \(\{2\}\), with payoff

\[
 u=(0,1,-1,0).                                                   \tag{11.6}
\]

Set the following reward coordinates, and set every unspecified coordinate
to zero:

\[
\begin{array}{c|rrrrrrrr}
 &r_0(\{0\})&r_0(\{1\})&r_0(\{0,1\})&r_0(\{0,2\})
 &r_1(\{0\})&r_1(\{1\})&r_1(\{0,1\})&r_1(\{2\})\\ \hline
\text{value}&1&1&0&1&0&0&1&1
\end{array}                                                     \tag{11.7}
\]

For player \(2\), put

\[
 r_2(A)=2\quad(\varnothing\ne A\subseteq\{0,1\}),
 \qquad
 r_2(A\cup\{2\})=-1\quad(A\subseteq\{0,1\}).              \tag{11.8}
\]

For player \(3\), put

\[
 r_3(A)=2\quad(\varnothing\ne A\subseteq\{0,1\}),
 \qquad
 r_3(A\cup\{3\})=-1\quad(A\subseteq\{0,1\}),
 \qquad r_3(\{2\})=0.                                       \tag{11.9}
\]

Finally overwrite the pure-set coordinates needed below by

\[
 r_2(\{2,3\})=r_3(\{2,3\})=1,
 \quad r_0(\{2,3\})=r_1(\{2,3\})=0,
 \quad r_0(\{0,2,3\})=r_1(\{1,2,3\})=0.                  \tag{11.10}
\]

At the stationary source, player \(0\)'s Quit0 payoff and complete cap are
both one: conditional on reaching its chosen stopping date, the only terminal
coalitions are \(\{0\}\) and \(\{0,2\}\), both worth one; waiting only
risks earlier absorption at \(\{2\}\), worth zero.  Thus the source has a
fixed paid Quit0 gain one while its opponent hazard tends to zero.

Against the literal tail (11.6), the exact root game has

\[
 q_0=q_1={1\over2},\qquad q_2=q_3=0.                           \tag{11.11}
\]

For player \(0\), the Quit and Continue endpoints are \(1-q_1\) and
\(q_1\); for player \(1\), they are \(q_0\) and \(1-q_0\).  Hence the
two active players form a matching-pennies root with the unique solution
(11.11).  Player \(2\)'s Continue and Quit endpoints are \(5/4\) and
\(-1\), while player \(3\)'s are \(3/2\) and \(-1\), so both Continue
strictly.  The exact root has absorption \(3/4\) and no sure quitter.

This table deliberately fails the global positive-gap hypothesis.  The pure
stationary exit set \(\{2,3\}\) is a terminal Nash profile: each member
gets one, versus zero after leaving, and each outsider gets zero whether it
joins or stays out.  Therefore the example is not a Fin4 counterexample.  It
is a sharp regression showing that stationary self-tail, vanishing source
hazard, a fixed complete Quit0 gain, and an exact fixed-absorption
literal-\(U\) root do not by themselves force either the two-sure terminal
arm or the one-sure reset arm.  Excluding this mixed case under the hard
residual must use the global gap beyond its one-time lower bound on the
prefixed debt.

## 12. Sharp boundary examples

### 12.1 Local payer collapse

Let player \(k\) use any positive stationary hazard and let \(b\) play
Never.  Set

\[
 r_b(\{k\})=0,qquad r_b(\{b\})=1,
\]

and keep the relevant collision rewards bounded.  Then the stationary source
has \(u_b=0\) and Quit0 gain tending to one as the hazard of \(k\) tends to
zero.  Against the unchanged opponents and tail, every exact Nash root makes
\(b\) Quit surely; every vanishing-error root makes its Continue probability
vanish.  The predecessor payoff tends to one, not to the source payoff zero.

This table may have global minimum zero and is not a counterexample to the
Fin4 conjecture.  It is an exact test showing that stationarity, unit row
reach, literal self-successor, and a fixed Quit margin do not themselves
produce a returned block.

### 12.2 Each nonlocal alternative is real

The strict Quit comparison can be reversed by making an opponent Quit with
macroscopic probability and assigning a sufficiently favorable payoff to
continuing against that opponent.  This realizes item 1.  It can also be
reversed at an all-Continue opponent root by raising only the continuation
coordinate \(v_b\), realizing item 2.  These repairs change exactly the
opponent-law or tail fields charged by (2.2); neither is a free consequence
of the original response ancestry.

## 13. Conjecture-facing verdict

The structured tropical paid port is stronger than a generic port in two
precise ways:

\[
\boxed{
 \text{source-local vanishing-error Nashification}
 \Longrightarrow
 \text{almost-sure payer absorption + fixed predecessor seam}.}
\]

Equivalently, every positive-survival exactification must make a macroscopic
opponent-law or tail move.  This rules out the hoped-for small local
source-reprojected block and shows that any successful consumer must be
genuinely global.

For the literal source payoff tail, it also gives

\[
 \boxed{
 \text{exact Nashification}
 \Longrightarrow
 \text{coordinatewise debt nonincrease + fixed payer-debt expenditure}.}
\]

This proves that the source is a fixed total-debt distance above the global
minimum.  It also classifies the exact sure-support exits: two sure quitters
are terminal, while one sure quitter has one explicit continuation debtor and
lands at a singleton-base reset candidate missing punishment-floor data.  A
no-sure mixed absorbing root remains an exact third case.

The result still does not prove an exact returned Nash--Bellman seam, a
contradiction from bounded exact-block capacity, or a renewable rank.  The
finite tropical ancestry supplies no target-to-next-source equality with
which to iterate the macroscopic alternative.  A bounded real-valued debt
decrease may be spent once along an off-minimum ray.  Therefore the extra
structured fields narrow the remaining consumer to either a punishment-floor
upgrade of the one-sure reset or a genuinely global treatment of the mixed
absorbing root, but they do not yet escape the generic paid-port strongly
connected component.

## Next exact question

In the one-sure branch, can the hard Fin4 hypotheses force the three free
payoffs above their punishment floors, thereby turning the stationary
singleton-base candidate into the checked same-law reset producer?  In the
no-sure branch, can the positive terminal gap and four-player singleton
margins rule out the matching-pennies-type mixed face or turn its fixed debt
expenditure into a source-compatible returned edge?  No current checked
declaration supplies either upgrade.
