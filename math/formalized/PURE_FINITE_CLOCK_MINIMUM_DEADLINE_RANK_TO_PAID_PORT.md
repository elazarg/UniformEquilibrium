# Pure finite-clock minima descend to an off-minimum paid port

Authors: `CODEX_SINGLETON_SOURCE`, `CODEX_SINGLETON_TIME_RANK`

Independent reviews:

- [canonical deadline-rank review by CODEX_DESCENDANT](../feedback/CODEX_SINGLETON_TIME_RANK__ANCHORED_ERASURE_AND_DEADLINE_DESCENT__BY_CODEX_DESCENDANT.md);
- [canonical deadline-rank falsification review by SOCIAL_WEIGHT_REVIEW](../feedback/CODEX_SINGLETON_TIME_RANK__ANCHORED_ERASURE_AND_DEADLINE_DESCENT__BY_SOCIAL_WEIGHT_REVIEW.md); and
- [finite-clock entrance review by SOCIAL_WEIGHT_REVIEW](../feedback/CODEX_SINGLETON_SOURCE__ONE_SURE_OWNER_EXACT_RESPONSE_HANDOFF__PROPOSITIONS_9_1_9_3__BY_SOCIAL_WEIGHT_REVIEW.md).

## Exact statement

Let \(I\) be a nonempty finite player set, let \(r(S)\in\mathbb R^I\) be the
reward of every nonempty quitting coalition, and let

\[
 d_i(U,B)=B_i-U_i,
 \qquad
 D(U,B)=\sum_{i\in I}d_i(U,B).
\]

Here \(U\) is the terminal payoff of an actual behavioral profile and \(B_i\)
is player \(i\)'s unrestricted terminal best-response value against the other
players' complete behavioral strategies.  Suppose that

\[
 D_*:=\min D>0
\]

on the closed terminal-semantic carrier.

A canonical pure-time strategy is `QuitAt t`, for \(t\in\mathbb N\), or
`Never`.  `QuitAt t` Continues at every live date other than \(t\) and Quits
surely at \(t\).  A finite-clock strategy is a behavioral strategy whose
induced stopping-time law on
\(\overline{\mathbb N}=\mathbb N\cup\{\infty\}\) has finite support.

### Canonical theorem

Let \(\sigma\) be an actual profile of canonical pure-time strategies such
that

\[
 D(\operatorname{Sem}(\sigma))=D_*.
\]

Then a finite list of literal unilateral pure-time replacements, starting at
\(\sigma\), produces an actual canonical pure-time profile \(\xi\) such that

\[
 D(\operatorname{Sem}(\xi))>D_*.
\tag{1}
\]

Moreover, there are a player \(h\) and a pure time or Never response \(q_h\)
against \(\xi_{-h}\) with

\[
 U_h(q_h,\xi_{-h})-U_h(\xi)
 =d_h(\operatorname{Sem}(\xi))
 \ge \frac{D(\operatorname{Sem}(\xi))}{|I|}
 >\frac{D_*}{|I|}.
\tag{2}
\]

Thus \(q_h\) is an exact best response in the complete behavioral strategy
class.  Its positive pure-time payoff difference admits a literal first-
disagreement row on the same actual profile.

### Finite-clock Fin4 corollary

Let \(I=\{0,1,2,3\}\), and let \(\sigma_0\) be an actual finite-clock profile
with

\[
 D(\operatorname{Sem}(\sigma_0))=D_*.
\]

Then finitely many literal unilateral replacements produce an actual
off-minimum finite-clock profile \(\xi\), with a retained finite ancestry from
\(\sigma_0\), and an outgoing complete response of gain strictly greater
than \(D_*/4\).  More precisely, at most four minimum-fibre purifications are
needed before either a strict target is found or the canonical theorem
applies; if a purification first leaves the minimum fibre, the displayed
\(D_*/4\) response may be one additional replacement launched from that
strict target.  On that same target there are two pure-time/Never
counterfactuals, the source one chosen from the positive support of the
prescribed stopping law, whose payoff difference is also strictly greater
than \(D_*/4\); they supply the literal paid first-disagreement row.

## Conjecture-facing change

The result eliminates actual finite-clock positive global minima as a
separate terminal component.  Every such profile reaches the mathematical
input of the off-minimum actual paid-port problem: an actual off-minimum
profile, a fixed complete pure-time response, a positive gain floor, and a
literal first-disagreement witness, all with ancestry from the supplied
minimum profile.

It therefore strictly narrows
[the actual paid-cap descent or inert-stall obligation](../questions/FIN4_ACTUAL_PAID_CAP_DESCENT_OR_INERT_STALL.md):
the finite-clock branch does not also require a same-stage cycle or singleton-
refusal consumer.  The off-minimum paid port itself remains open.

## Definitions, probability, and agency

Before absorption, a quitting game has a unique public live history at every
date: everyone has Continued so far.  Against fixed opponents, any behavioral
strategy of one player therefore induces a probability law on
\(\overline{\mathbb N}\).  Its expected payoff is the average of the payoffs
of the corresponding pure times and Never.  This is why every cap calculation
below covers calendar-dependent hazards, private randomization, arbitrarily
late stopping, and Never.  No stationary or finite-horizon restriction is
used.

For a canonical pure profile \(\sigma=(\tau_i)_{i\in I}\), define

\[
 H(\sigma)=\{\tau_i:\tau_i<\infty\},
 \qquad
 \rho(\sigma)=|H(\sigma)|.
\tag{3}
\]

If \(H(\sigma)\ne\varnothing\), let

\[
 t=\min H(\sigma),
 \qquad
 S=\{i:\tau_i=t\}.
\]

Then \(S\) is the sure terminal coalition at date \(t\).

## Proof

### 1. The all-Never profile is not a positive global minimum

Write \(s_i=r_i(\{i\})\).  At every positive global minimum, the singleton
margin is

\[
 D_*\le B_i-s_i
 \qquad(i\in I).
\tag{4}
\]

Against all-Never opponents, \(B_i=\max\{0,s_i\}\).  If some \(s_i\ge0\),
then \(B_i-s_i=0\), contradicting (4).  If every \(s_i<0\), all Never has
total debt zero.  Hence every canonical pure positive global minimum has
\(\rho\ge1\).

### 2. Anchored erasure

Fix an anchor \(b\in S\).  Delete the other members of \(S\), one at a time,
by replacing their `QuitAt t` strategies by Never.  Every sibling is an
actual canonical pure profile.  The anchor still Quits surely at \(t\), so
the game never reaches a later date.

Suppose the current sibling, with quitter set \(C\ni b,p\), is a global
minimum.  Against the fixed opponents of \(p\), every behavioral response has
payoff in the convex hull of a subset of

\[
 s_p,
 \qquad r_p(C),
 \qquad r_p(C\setminus\{p\}).
\tag{5}
\]

The singleton value is available by quitting before \(t\) when \(t>0\); at
\(t=0\) it is absent.  Quitting at \(t\) gives the second value, while
Continuing there gives the third.  The retained anchor screens all subsequent
behavior.  If the singleton value is available, (4) makes it strictly smaller
than \(B_p\).  Consequently in every case

\[
 B_p=\max\{r_p(C),r_p(C\setminus\{p\})\}.
\tag{6}
\]

The same cap applies to the two adjacent siblings because only \(p\)'s own
strategy changes.  Thus the better endpoint is an exact complete behavioral
response at the worse endpoint; a tie has zero gain in either direction.

Every sibling has debt at least \(D_*\).  If some sibling is the first with
debt strictly above \(D_*\), keep it as \(\xi\).  A maximum-debt player \(h\)
then satisfies (2).  Against deterministic pure-time opponents the cap is a
maximum of finitely many payoff values and Never, so a pure time or Never
attains it.

If every erasure stays at the minimum, the last sibling is a literal
singleton minimum with only \(b\) Quitting at \(t\).

### 3. Exact response from a singleton minimum

At the singleton minimum,

\[
 U_b=s_b,
 \qquad d_b=D_*,
 \qquad d_i=0\quad(i\ne b).
\tag{7}
\]

Indeed, (4) gives \(d_b\ge D_*\), while all debts are nonnegative and sum to
\(D_*\).

Suppose first that an opponent has a finite deadline.  Let

\[
 u=\min\{\tau_i:i\ne b,\ \tau_i<\infty\}>t,
 \qquad
 A=\{i\ne b:\tau_i=u\}.
\]

Against these opponents, every pure stopping time of \(b\) has one of the
three values

\[
 \begin{array}{c|c}
 n<u&r_b(\{b\}),\\
 n=u&r_b(A\cup\{b\}),\\
 n>u\text{ or Never}&r_b(A).
 \end{array}
\tag{8}
\]

Arbitrary behavioral responses only average these values.  Since
\(B_b-s_b=D_*>0\), the first value cannot attain the cap.  Hence an exact
response may be chosen as QuitAt \(u\) or Never:

\[
 B_b=\max\{r_b(A\cup\{b\}),r_b(A)\}.
\tag{9}
\]

The response gains exactly \(D_*\) and kills \(b\)'s debt.  If its target is
off minimum, it is the desired paid exit.  If it remains minimum, then

\[
 H(\text{target})\subseteq H(\sigma)\setminus\{t\}.
\tag{10}
\]

QuitAt \(u\) adds no date because \(u\) was already an opponent deadline;
Never adds none.  Thus \(\rho\) strictly decreases.

If every opponent is Never, finite stopping gives \(s_b\) and Never gives
zero.  Since \(B_b>s_b\), Never is the exact response and its target is all
Never.  Section 1 shows that this target cannot remain at the positive global
minimum, so this is an off-minimum paid exit of gain \(D_*\).

### 4. Finite termination

Starting from a canonical pure minimum, apply anchored erasure.  A strict
sibling is an exit.  Otherwise reach the singleton and apply Section 3.  A
strict response target is an exit.  An equality response deletes the current
earliest deadline and returns another actual canonical pure global minimum.

Erasure never introduces a deadline.  Only singleton-response rounds recur,
and (10) strictly decreases the natural-valued rank \(\rho\).  At rank one,
the singleton owner faces only Never opponents and must exit as above.
Therefore the construction terminates after at most
\(\rho(\sigma)\le |I|\) singleton-response rounds.  At the final off-minimum
profile, choose a maximum-debt player to obtain (2).  This proves the
canonical theorem.

### 5. Finite-clock purification in Fin4

Let \(\sigma\) be a finite-clock global-minimum profile, and choose a player
\(h\) whose stopping law \(\pi_h\) is not pure.

If \(d_h(\sigma)>0\), the opponents' finite support makes the complete cap a
maximum over finitely many relevant pure times and Never.  Replace \(h\) by a
pure exact best response.  If \(d_h(\sigma)=0\), write \(V_h(q)\) for the
payoff of pure time \(q\in\overline{\mathbb N}\).  Then

\[
 B_h=U_h=\sum_q\pi_h(q)V_h(q),
 \qquad V_h(q)\le B_h.
\]

Every \(q\) in the positive support of \(\pi_h\) must therefore attain the
cap.  Choose among these finitely many support points one whose completed
profile has least total debt, and replace \(h\) by it.

In either case the replacement is a complete exact response, of positive or
zero gain, and makes \(h\)'s strategy pure.  Carrier minimality says that the
target either remains at \(D_*\) or is strictly off minimum.  In the equality
case repeat with another non-pure coordinate.  Later replacements do not
alter an already purified strategy, so after at most four equality steps the
profile is canonical pure-time/Never.

If a purification first gives a strict target \(\tau\), choose a maximum-debt
player \(p\).  Then

\[
 d_p(\tau)\ge D(\tau)/4>D_*/4.
\]

The opponents are still finite-clock, so a pure time or Never attains \(p\)'s
complete cap.  This one additional response supplies the stated outgoing
paid edge.  If all purifications stay minimum, apply Sections 1--4.  This
proves the Fin4 corollary.

### 6. Literal first disagreement

At a canonical exit, the mover's prescribed strategy and exact response are
already two pure times or a pure time and Never.

At a strict exit during finite-clock purification, the maximum-debt player's
prescribed stopping law \(\pi\) need not yet be pure.  Let \(q^*\) be a pure
cap attainer and write \(V(q)\) for the payoff of pure time \(q\) against the
same fixed opponents.  Then

\[
 d_p=B_p-U_p
 =\sum_q\pi(q)\bigl(V(q^*)-V(q)\bigr).
\tag{11}
\]

Every summand is nonnegative.  Hence some \(q\) in the positive support of
\(\pi\) satisfies

\[
 V(q^*)-V(q)\ge d_p>D_*/4.
\tag{12}
\]

The two pure witnesses \(q,q^*\) have a first live date at which one Quits
and the other Continues.  Before that date their outcomes coincide;
conditioning there gives the exact positive Bellman payoff difference.
The checked pure-time first-disagreement decoder formalizes this step against
the actual opponents and retains the actual continuation.  The pure source
witness in the mixed case is a positive-support component of the prescribed
stopping law; it is not falsely identified with that mixed prescribed
strategy.

## Boundary tests

1. **Date zero.**  At \(t=0\), quitting before the anchored coalition is
   impossible.  Formula (5) uses a subset of its displayed values, and (6)
   remains exact.
2. **Simultaneous earliest coalition.**  The anchor remains a sure quitter
   during every erasure, so the continuation is screened even for a complete
   behavioral replacement.
3. **Ties.**  If QuitAt \(u\) and Never tie in (9), either is an exact response
   and both remove \(t\).  The rank cannot fail through tie-breaking.
4. **All Never.**  Section 1 covers both a nonnegative singleton reward and
   all strictly negative singleton rewards.
5. **Concrete deadline calculation.**  If \(b\) Quits at date zero, an
   opponent coalition \(A\) Quits at date two, and
   \(r_b(\{b\})=0\), \(r_b(A\cup\{b\})=2\), \(r_b(A)=1\), then the exact
   response is QuitAt two and the old deadline zero disappears.  If instead
   the last two values are \(-2\) and \(1\), Never is the exact response and
   the same strict rank drop occurs.
6. **Global-minimum hypothesis is essential.**  Give every player own
   singleton reward \(-1\) and every other reward coordinate zero.  In the
   profile where player \(0\) Quits at date zero and player \(1\) would Quit
   at date one, the local semantic data are
   \(U=(-1,0,0,0)\), \(B=(0,0,0,0)\), and \(d=(1,0,0,0)\).  The owner has an
   executable refusal and outsiders have no profitable collision, but all
   Never is an exact equilibrium and the global minimum is zero.  Local
   singleton data alone do not imply the theorem.

No positive-global-minimum reward table is offered as a boundary example:
its existence is precisely the hypothetical counterexample regime being
reduced.

## Source correspondence

The following checked declarations supply the established semantic facts:

- `quittingPureTimeBehaviorStrategy`,
  `quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy`, and
  `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` give
  the canonical strategies and unrestricted behavioral pure-time
  extremality;
- `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`
  gives (4);
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`
  gives the literal row in Section 6; and
- `QuittingTerminalExploitabilityWitness.singleton_refusal_or_exists_collision_gain`
  in
  `UniformEquilibrium/Quitting/Classification/TerminalExploitabilityToggles.lean`
  is compatible with the singleton endpoint but is not needed by the proof.

A narrow source and conference search found no existing deadline-support
rank theorem or finite-clock-to-paid-port reduction.  The new mathematics is
the anchored erasure, the canonical owner response (9), the renewable rank
(10), and its composition with finite-clock purification.  No paper theorem
is invoked.

## Adapter and consumer

The actual-data adapter is Section 5: a supplied actual finite-clock Fin4
minimum either directly exposes an actual off-minimum paid profile or becomes
a supplied canonical pure minimum.  Sections 1--4 consume the latter into the
same off-minimum paid output.  The complete response and first-disagreement
decoder then supply the fixed paid-port data.

The downstream consumer is intentionally not claimed.  The result hands the
finite-clock lane to
`FIN4_ACTUAL_PAID_CAP_DESCENT_OR_INERT_STALL`; its quantitative descent and
inert outputs remain open.  In particular, literal ancestry is not an atlas
minimum-atom chronology, a cap--Nash prefix stack, or an unchanged post-mark
tail passport.

## Lean handoff

Suggested declarations are:

```text
pureTimeSingleton_cap_eq_nextCollision_or_never
pureTimeSingleton_response_deadlineSupport_strict
pureTimeMinimum_anchorErase_or_deadlineDescent
pureTimeMinimum_exists_offMinimumPaidPort
finiteClockMinimum_purify_or_pureTimeMinimum
finiteClockMinimum_exists_offMinimumPaidPort
```

The first four are generic over a finite player type.  Formalization should
reuse behavioral pure-time extremality for the unrestricted cap, then prove
only finite support, minimum-date, and Finset-cardinality bookkeeping.  The
Fin4 theorem composes these with at most four coordinate purifications and
specializes the maximum-debt bound to \(D_*/4\).

## Scope and nonclaims

1. The result does not consume the off-minimum paid port, prove a charged
   Nash--Bellman return, or yield a uniform-equilibrium payoff.
2. The deadline rank is renewable only in the actual canonical pure-time
   lane.  It is not a rank on arbitrary semantic or law-tight reset points.
3. The outgoing response is a whole-profile behavioral edge, not an exact
   cap--Nash temporal prefix.
4. The erasure face is not serialized as game time.
5. No minimum atom, selected chronology, unchanged suffix, or stronger atlas
   provenance is inferred from the literal ancestry.

## Lean formalization record

Pre-formalization packet SHA-256:
`146d1551edf324c8f5d83f084795e122bf9dad251a75a9defafe388ee8576b5e`.

The checked finite-clock reduction landed in commit
`611aa9747de7994ef06610a1628e625327f5dcab`. Its principal production owners
are
`UniformEquilibrium/Quitting/Paths/PureTimeDeadlineProfile.lean`,
`UniformEquilibrium/Quitting/Paths/PureTimeDeadlineRank.lean`,
`UniformEquilibrium/Diagnostics/Quitting/PureTimeMinimumPaidPort.lean`,
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FiniteClockCanonicalization.lean`,
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FiniteClockMinimumPurification.lean`,
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FiniteClockMinimumPaidPort.lean`,
and
`UniformEquilibrium/Diagnostics/Quitting/FinFourFiniteClockMinimumPaidPort.lean`.

The principal checked declarations are
`finiteClock_canonicalized_deadlineBounded_and_semantic_eq`,
`deadlineBoundedMinimum_purify_or_offMinimum_with_step_bound`,
`finFourDeadlineBoundedMinimum_purify_or_offMinimum_with_four_steps`,
`pureTimeMinimum_exists_offMinimumPaidPort`,
`finiteClockMinimum_exactCapPurification_or_pureTimeDescentPaidPort`, and
`finFourFiniteClockMinimum_exactCapPurification_or_pureTimeDescentPaidPort`.

Evidence seals are `M` and `L`, with branch-local `A` for a supplied actual
finite-clock profile whose terminal semantic debt is the positive global
minimum. The adapter reconstructs that same profile from its stopping laws,
preserves its complete prescribed-payoff/unrestricted-cap semantic pair, and
retains literal finite replacement ancestry. It does not produce the profile,
the positive minimum, or an arbitrary-profile source.

There is no downstream `C`. The checked result returns an actual off-minimum
deadline-bounded or pure-time paid port, including the complete response and
first-disagreement data, but does not consume that port, supply a chronology
or renewable return, or prove a uniform-equilibrium payoff.
