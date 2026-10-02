# Anchored erasure plus deadline descent eliminates pure finite-clock minima

Identity: `CODEX_SINGLETON_TIME_RANK`  
Date: 2026-08-31  
Status: **stable ordinary-mathematics candidate; not Lean checked.  Two
independent reviews passed, and their local repairs are incorporated.**

Independent reviews:

- `feedback/CODEX_SINGLETON_TIME_RANK__ANCHORED_ERASURE_AND_DEADLINE_DESCENT__BY_CODEX_DESCENDANT.md`;
- `feedback/CODEX_SINGLETON_TIME_RANK__ANCHORED_ERASURE_AND_DEADLINE_DESCENT__BY_SOCIAL_WEIGHT_REVIEW.md`.

## 1. Question and result

Let \(I\) be a nonempty finite player set, let \(n=|I|\), and let every
player's strategy in an actual quitting profile \(\sigma\) be a canonical
pure stopping time in \(\mathbb N\cup\{\infty\}\).  Suppose its complete
terminal-semantic pair lies in the usual complete behavioral carrier and
attains its positive global minimum:

\[
 D(\operatorname{Sem}(\sigma))=D_*>0,
 \qquad
 D_*\le D(z)\quad
 \text{for every terminal-semantic carrier point }z.
\]

Must one obtain an actual off-minimum paid behavioral edge without treating a
horizontal coalition face as chronological play?

Yes.  The correct argument has two nested finite operations.

1. At the current earliest quitting date, erase all but one anchored quitter.
   Either one erased sibling is off minimum, or the last sibling is a pure
   singleton global minimum.
2. At a singleton global minimum, the owner's exact pure-time response cannot
   stop before the next opponent deadline.  If its target stays minimum, the
   earliest finite deadline strictly increases and the set of active finite
   deadlines strictly shrinks.

Since the initial profile has only finitely many pure stopping times, the
second operation cannot recur indefinitely.  It produces an actual canonical
pure-time profile \(\xi\) with

\[
 D(\operatorname{Sem}(\xi))>D_*,
\tag{1.1}
\]

together with a player \(h\) and a pure time or Never response \(q_h\) such
that

\[
 U_h(q_h,\xi_{-h})-U_h(\xi)
 =d_h(\operatorname{Sem}(\xi))
 \ge \frac{D(\operatorname{Sem}(\xi))}{n}
 >\frac{D_*}{n}.
\tag{1.2}
\]

The response is a complete unrestricted behavioral best response and its
two pure times have a literal paid first disagreement.  A finite list of
explicit unilateral strategy replacements connects \(\sigma\) to \(\xi\).
If \(\xi\) first arises from the singleton-owner response, the construction
also retains the incoming minimum-to-\(\xi\) exact response of gain \(D_*\).

Thus:

\[
\boxed{
\begin{array}{c}
\text{actual canonical pure-time/Never global minimum}\\
\text{with }D_*>0
\end{array}
\Longrightarrow
\text{actual literal-ancestry off-minimum paid port}.}
\tag{1.3}
\]

This repairs the false shortcut that tried to force a profitable outsider
collision at every singleton.  A terminal-gap witness allows an owner-refusal
arm instead.  Deadline descent executes the owner's actual best response on
the retained deterministic tail.

## 2. Canonical pure-time profiles and their finite rank

Write a canonical pure-time profile as

\[
 \sigma=(\tau_i)_{i\in I},
 \qquad
 \tau_i\in\mathbb N\cup\{\infty\}.
\]

Player \(i\) Continues at every date except \(\tau_i\) when
\(\tau_i<\infty\), and Quits surely there.  Let

\[
 H(\sigma)=\{\tau_i:\tau_i<\infty\}
\]

and use the natural-valued rank

\[
 \rho(\sigma)=|H(\sigma)|.
\tag{2.1}
\]

If \(H(\sigma)\ne\varnothing\), put

\[
 t(\sigma)=\min H(\sigma),
 \qquad
 S(\sigma)=\{i:\tau_i=t(\sigma)\}.
\]

The terminal coalition is surely \(S(\sigma)\).  The entire pre-date word is
all Continue.

The all-Never profile is not a positive global minimum.  Indeed, put
\(s_i=r_i(\{i\})\).  Against all-Never opponents the cap is
\(\max\{0,s_i\}\).  If some \(s_i\ge0\), the global-minimum singleton margin

\[
 D_*\le B_i-s_i
\tag{2.2}
\]

would have zero right-hand side.  If every \(s_i<0\), the all-Never profile
has total debt zero.  Both contradict \(D_*>0\).  Hence every canonical pure
global minimum in this argument has \(\rho\ge1\).

## 3. Anchored erasure at one deadline

Let \(t=t(\sigma)\), \(S=S(\sigma)\), and fix an anchor \(b\in S\).  Delete
the other members of \(S\) one at a time by changing their canonical time
from \(t\) to \(\infty\).  For a pure-time strategy this changes only the
date-\(t\) live action: both strategies Continue at every other date.

Every sibling remains an actual canonical pure-time profile, retains the
entire pre-\(t\) word and post-\(t\) tail, and absorbs at \(t\) because the
anchor remains a sure quitter.

Suppose a current sibling with quitter set \(C\ni b,p\) is a global minimum.
Against the fixed opponents of the player \(p\), every behavioral response is
a convex combination of a subset of the following three payoff values:

\[
 s_p,\qquad r_p(C),\qquad r_p(C\setminus\{p\}).
\]

When \(t>0\), the singleton value comes from quitting before \(t\); when
\(t=0\), it need not be attainable and is simply absent from the response
menu.  The other two values come from Quitting at \(t\) and Continuing there.
The anchor screens every later behavior.  In the first case (2.2) gives
\(s_p<B_p\), while in the second case the singleton value was absent anyway.
Therefore in both cases

\[
 B_p=\max\{r_p(C),r_p(C\setminus\{p\})\}.
\tag{3.1}
\]

The same cap applies to both adjacent siblings because only \(p\)'s strategy
changes.  Hence the better endpoint is an exact complete behavioral best
response at the worse endpoint; ties are zero-gain exact responses in either
direction.

Every sibling has debt at least \(D_*\).  If one is the first sibling with
debt strictly greater than \(D_*\), retain it and its preceding literal
minimum sibling.  At the off-minimum sibling, a maximum-debt player \(h\)
satisfies

\[
 d_h\ge \frac{D}{|I|}>\frac{D_*}{|I|}.
\tag{3.2}
\]

Against pure-time opponents, the cap is attained by a pure time or Never.
Its replacement is an actual paid behavioral edge from the off-minimum
profile.  In Fin4 its gain is strictly greater than \(D_*/4\).

If every erasure stays minimum, the last sibling is a literal singleton
minimum with only \(b\) quitting at \(t\).

## 4. Exact response from a singleton minimum

Let \(\sigma\) now be a canonical pure-time global minimum whose earliest
coalition is \(\{b\}\) at date \(t\).  Then

\[
 U_b=s_b,
 \qquad
 d_b=D_*,
 \qquad
 d_i=0\quad(i\ne b).
\tag{4.1}
\]

The proof is the singleton margin (2.2) plus the total-debt equality.

### 4.1 There is a later opponent deadline

First suppose some opponent has a finite deadline.  Let

\[
 u=\min\{\tau_i:i\ne b,\ \tau_i<\infty\}>t,
 \qquad
 A=\{i\ne b:\tau_i=u\}.
\]

Against these deterministic opponents, a pure stopping time of \(b\) has
exactly one of the following values:

\[
 \begin{array}{c|c}
 \text{choice of }b & \text{payoff}\ \\ \hline
 n<u & s_b,\\
 n=u & r_b(A\cup\{b\}),\\
 n>u\text{ or Never} & r_b(A).
 \end{array}
\tag{4.2}
\]

Arbitrary behavioral strategies only convexify these pure-time values.  Since
\(B_b-s_b=D_*>0\), the first line cannot attain the cap.  Therefore an exact
response may be chosen as either QuitAt \(u\) or Never:

\[
 B_b=\max\{r_b(A\cup\{b\}),r_b(A)\}.
\tag{4.3}
\]

The target is an actual canonical pure-time profile.  It terminates at date
\(u\), in \(A\cup\{b\}\) in the first case and in \(A\) in the second.  The
response gains exactly \(D_*\) and kills \(b\)'s debt.

Most importantly,

\[
 H(\text{target})\subseteq H(\sigma)\setminus\{t\}.
\tag{4.4}
\]

QuitAt \(u\) adds no date because \(u\) was already an opponent deadline;
Never adds none.  Hence

\[
 \rho(\text{target})<\rho(\sigma).
\tag{4.5}
\]

### 4.2 Every opponent is Never

If all opponents are Never, every finite stopping time of \(b\) gives
\(s_b\), while Never gives zero.  Since \(B_b>s_b\), one has

\[
 B_b=0>s_b,
\]

and Never is the exact response.  Its target is all Never.  Section 2 shows
that this target cannot remain at the positive global minimum.  Thus this
case is already an off-minimum paid port of gain exactly \(D_*\).

## 5. Finite descent

Start from an actual canonical pure-time/Never global minimum.

1. Apply anchored erasure at its earliest deadline.
2. If a sibling leaves the minimum fibre, use the paid output of Section 3.
3. Otherwise reach the singleton minimum and apply its exact response.
4. If that response target leaves the minimum fibre, it is itself a paid
   minimum-to-off-minimum edge of gain exactly \(D_*\).  Retain that incoming
   edge, and also choose a maximum-debt player at the actual off-minimum target
   to obtain the common outgoing response (1.2).
5. If it remains minimum, (4.5) strictly lowers \(\rho\), and repeat.

Anchored erasure never introduces a finite deadline and retains the current
earliest date through its singleton endpoint.  Every equality response from
that singleton deletes the current earliest date.  Thus only the response
steps recur, and they strictly lower the natural number \(\rho\).  At
\(\rho=1\), the singleton owner sees only Never opponents, so Section 4.2
forces the off-minimum exit.

The construction terminates after at most \(\rho(\sigma)\le |I|\) singleton
response rounds.  For Fin4, each erasure uses at most three one-player
changes.

In either exit mode the final output has the same consumer-facing form: an
actual off-minimum canonical profile with an outgoing complete pure-time
response of gain strictly greater than \(D_*/|I|\).  It also retains a literal
global-minimum sibling.  At an erasure exit this sibling is the preceding
face point and the endpoint comparison may point either way or tie.  At a
singleton-response exit it is the response source and the incoming edge is
oriented toward the off-minimum profile with gain exactly \(D_*\).

## 6. Provenance and chronology

This is a finite literal-profile ancestry construction.

- Every erasure sibling changes one canonical QuitAt \(t\) strategy to
  Never.  Because a canonical pure-time strategy Continues away from its
  selected date, this is literally a one-date change.
- Every singleton response is a legal whole-strategy unilateral replacement
  from QuitAt \(t\) to QuitAt the next existing opponent deadline or Never.
- The off-minimum response is launched from the actual selected off-minimum
  profile.
- No compact carrier point, unrelated law realizer, or newly selected source
  chronology is introduced.

Here “ancestry” means only the supplied actual profile and the displayed
finite list of literal replacements.  It does not automatically retain an
atlas marked atom, a minimum-atom chronology, a cap--Nash prefix stack, or a
post-mark tail passport.

The erasure face itself is not interpreted as a forward best-response path.
Only an individual adjacent comparison is oriented by (3.1).  The temporal
rank is carried by the exact singleton response between two actual profiles,
not by walking around the horizontal face.

## 7. Relation to the hard-residual singleton toggle

A terminal exploitability witness gives the exact disjunction

\[
 \Gamma\le-r_b(\{b\})
 \quad\lor\quad
 \exists c\ne b:\quad
 r_c(\{b\})+\Gamma\le r_c(\{b,c\}).
\tag{7.1}
\]

At a singleton minimum, the second arm is impossible: player \(c\)'s literal
QuitAt \(t\) deviation would give positive debt, contradicting (4.1).  Thus a
hypothetical singleton minimum necessarily lies in the owner-refusal arm

\[
 r_b(\{b\})\le-\Gamma.
\tag{7.2}
\]

This is useful extra table information, but it is not by itself an executable
refusal on the supplied tail.  Later opponents may stop after \(t\).  The
deadline calculation (4.2), not the static empty-coalition comparison, is
what selects the actual response and proves the rank drop.

Thus the hard-residual collision geometry is consistent with, but not needed
for, the finite deadline descent.

## 8. Exact scope and nonclaims

### 8.1 Generic theorem

For every nonempty finite player type, an actual canonical pure-time/Never
profile attaining a positive global minimum produces the output (1.1)--(1.2).
The gain floor is \(D_*/|I|\), and the recursive deadline rank is at most
\(|I|\).  This theorem uses neither Fin4 geometry nor a terminal exploitability
witness beyond whatever external argument supplied the positive global
minimum.

### 8.2 Fin4 finite-clock corollary

The input to the generic theorem must be a **canonical pure-time/Never
profile**, not merely an arbitrary finite-clock profile with a pure first row.
Proposition 9.3 of
`CODEX_SINGLETON_SOURCE__ONE_SURE_OWNER_EXACT_RESPONSE_HANDOFF.md` proves the
needed entrance for Fin4 and has a separate independent PASS review.  Starting
from an actual finite-clock Fin4 global minimum, it performs at most four
purification replacements.  Either it already selects an actual off-minimum
finite-clock profile and an outgoing complete response of gain greater than
\(D_*/4\), or its equality arm returns an actual canonical pure-time/Never
global-minimum profile.  Applying the present theorem in the second arm gives

\[
\boxed{
\text{actual finite-clock Fin4 positive global minimum}
\Longrightarrow
\begin{array}{c}
\text{actual off-minimum profile with literal finite ancestry,}\\
\text{and an outgoing complete response of gain }>D_*/4.
\end{array}}
\tag{8.1}
\]

The strict purification edge itself may have zero or small gain; the stated
\(D_*/4\) response is the additional maximum-debt response launched from its
literal off-minimum target.  No stronger atlas passport is silently inferred
from this ancestry.

### 8.3 Nonclaims

1. The result does not consume the off-minimum paid port, produce a charged
   Nash--Bellman return, or prove a uniform-equilibrium payoff.
2. The deadline rank is renewable only within the actual canonical pure-time
   lane.  It is not asserted for a generic law-tight reset chamber whose
   returned semantic pair may be a nonattained carrier point.
3. The outgoing paid response is a unilateral whole-profile behavioral edge,
   not an exact cap--Nash temporal prefix.
4. No outsider collision is assumed at a negative singleton owner.
5. No horizontal face is serialized as game time.

## 9. Suggested Lean interfaces

```text
pureTimeSingleton_cap_eq_nextCollision_or_refusal
pureTimeSingleton_exactResponse_strictly_decreases_deadlineSupport
pureTimeMinimum_anchorErase_or_deadlineDescent
finiteClockMinimum_exists_offMinimumPaidPort
```

The first two are generic over a finite player type.  The \(D_*/4\) constant
is the Fin4 specialization of the maximum-debt bound.

## 10. Sources inspected

- `quittingPureTimeBehaviorStrategy` and pure-time extremality in
  `BehaviorPureTimeExtremality.lean`;
- `minimumTerminalSemantic_singletonMargin` in
  `TerminalSemanticAuxiliaryNashBudget.lean`;
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `TerminalSemanticPaidFirstDisagreement.lean`;
- `QuittingTerminalExploitabilityWitness.singleton_refusal_or_exists_collision_gain`
  in `TerminalExploitabilityToggles.lean`;
- the independently reviewed finite-clock purification result, Proposition
  9.3 of
  `CODEX_SINGLETON_SOURCE__ONE_SURE_OWNER_EXACT_RESPONSE_HANDOFF.md`.

## 11. Boundary tests and review resolution

Both independent reviews checked the following boundary cases.

1. **Unrestricted responses.**  Against deterministic opponents, the unique
   public live history identifies every behavioral strategy with a
   distribution on pure stopping times and Never.  Equations (3.1) and (4.3)
   therefore compute complete behavioral caps, not stationary or
   finite-horizon caps.
2. **Date zero.**  At \(t=0\), quitting strictly before the anchor is
   unavailable.  Section 3 now uses a subset of the three displayed values;
   (3.1) remains exact.
3. **Literal canonical updates.**  The repository's canonical QuitAt \(t\)
   strategy Continues at every other date.  Its replacement by Never changes
   exactly the date-\(t\) action.  QuitAt \(u\) introduces no new deadline
   because \(u\) was already used by an opponent.
4. **All Never.**  The exclusion in Section 2 uses only the global singleton
   margin and positive minimum debt; it does not need the Fin4 positive-atom
   theorem.
5. **Simultaneous earliest coalition.**  Anchored erasure retains one sure
   quitter until the face reaches a singleton, so every deleted player's late
   behavior remains screened.  The face itself is not a chronology.

The positive-global-minimum provenance is essential.  As a local regression,
take four players, give every player own singleton reward \(-1\), and set
every other reward coordinate to zero.  In the canonical profile where player
\(0\) Quits at date zero and player \(1\) would Quit at date one after refusal,

\[
 U=(-1,0,0,0),\qquad B=(0,0,0,0),\qquad d=(1,0,0,0).
\]

All formal singleton-margin inequalities hold, outsiders have no profitable
collision, and the owner has an executable refusal.  Nevertheless all Never
is an exact equilibrium, so the global minimum debt is zero.  The local
singleton data alone do not imply the theorem; the global positive minimum
and the finite deadline rank do.

The review objections are resolved.  No mathematical objection remains in
either report.  The candidate is stable for a final packaging decision, but
it has not been placed in `exports/` and none of its new statements is claimed
Lean checked.
