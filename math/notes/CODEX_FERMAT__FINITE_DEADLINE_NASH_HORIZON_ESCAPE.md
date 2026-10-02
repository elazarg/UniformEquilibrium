# Finite-deadline Nash profiles force horizon-escaping gap witnesses

Author: `CODEX_FERMAT` (proof supplied by the user; source audit and packaging
by the conference coordinator)

Status: **complete ordinary mathematics; independently reviewed; internal
duplicate/no export.**  The argument is correct, but Sections 3--6 of
`CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md` already contain the stronger
finite-deadline producer, exact adjusted-debt identity, and global-gap
consequence.  This note retains the especially short horizon-escape
formulation as a regression against bounded pure-time localization.

Independent review:
[`CODEX_EULER`](../feedback/CODEX_FERMAT__FINITE_DEADLINE_NASH_HORIZON_ESCAPE__BY_CODEX_EULER.md).

## 1. Exact statement

Let `I` be a nonempty finite player set and let

\[
 r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a finite quitting-game reward table, with payoff zero if nobody ever
quits.  Write `Q_t^i` for player `i` quitting deterministically at date `t`
and `Q_\infty^i` for Never.  Assume that there is a fixed `gamma > 0` such
that every behavioral profile `sigma` has unrestricted terminal
exploitability at least `gamma`:

\[
 \max_{i\in I}\left(B_i(\sigma)-U_i(\sigma)\right)\ge\gamma. \tag{1.1}
\]

Then for every `n : Nat` there is a behavioral profile `sigma^n` such that

\[
 U_i\bigl(\sigma^n[i\leftarrow Q_t^i]\bigr)-U_i(\sigma^n)\le 0
 \quad
 (i\in I,\ t\in\{0,\ldots,n,\infty\}),                 \tag{1.2}
\]

but some player has

\[
 U_i\bigl(\sigma^n[i\leftarrow Q_{n+1}^i]\bigr)
      -U_i(\sigma^n)\ge\gamma.                         \tag{1.3}
\]

Consequently no finite set of deterministic quit times, even together with
Never, witnesses a fixed positive fraction of the global gap uniformly over
all behavioral profiles.  More precisely, for every finite `F subset Nat`
there is a profile at which all deviations `Q_t`, `t in F`, and Never have
nonpositive gain, while one later deterministic quit time has gain at least
`gamma`.

The assertion is conditional on (1.1).  It neither proves nor assumes that a
reward table satisfying (1.1) actually exists.

## 2. Finite timing game

Fix `n`.  Define a finite normal-form game whose pure action set for every
player is

\[
 A_n=\{0,1,\ldots,n,\infty\}.
\]

For an action profile `a`, if every action is infinity the payoff is zero.
Otherwise let

\[
 m(a)=\min\{a_i:a_i<\infty\},\qquad
 S(a)=\{i:a_i=m(a)\},
\]

and give player `i` payoff `r_i(S(a))`.  These are exactly the quitting-game
terminal payoffs under the pure-time strategies `Q_{a_i}^i`.

By Nash's theorem for finite games, this game has a mixed equilibrium
`mu^n=(mu_i^n)_i`.

## 3. Exact behavioral realization

For `t <= n`, set

\[
 M_{i,t}=\mu_i^n(\{t,t+1,\ldots,n,\infty\})
\]

and, conditional on survival to date `t`, prescribe Quit probability

\[
 x_{i,t}=
 \begin{cases}
 \mu_i^n(t)/M_{i,t},&M_{i,t}>0,\\
 0,&M_{i,t}=0.
 \end{cases}
\]

After date `n`, prescribe Continue surely.  Call the resulting behavioral
profile `sigma^n`.  Telescoping the hazards gives

\[
 \left(\prod_{s<t}(1-x_{i,s})\right)x_{i,t}=\mu_i^n(t),
 \qquad
 \prod_{s=0}^{n}(1-x_{i,s})=\mu_i^n(\infty).
\]

Thus each player's complete stopping law is exactly `mu_i^n`, independently
across players, and the terminal law and payoff of `sigma^n` equal those of
the mixed timing profile.

For every `a_i in A_n`, the quitting-game payoff from replacing player `i`
by `Q_{a_i}^i` equals the finite timing-game payoff of pure action `a_i`
against `mu^n_{-i}`.  Nash optimality therefore gives

\[
 U_i\bigl(\sigma^n[i\leftarrow Q_{a_i}^i]\bigr)
 \le U_i(\sigma^n).                                   \tag{3.1}
\]

Because the prescribed mixed action is an average of these pure-action
payoffs, equality is attained in the maximum:

\[
 \max_{a_i\in A_n}
 U_i\bigl(\sigma^n[i\leftarrow Q_{a_i}^i]\bigr)
 = U_i(\sigma^n).                                     \tag{3.2}
\]

This proves (1.2).

## 4. The only untested value is the late singleton escape

Under `sigma^n_{-i}`, no opponent quits after date `n`.  Hence all finite
quit times `t>n` have the same payoff: on histories absorbed by date `n`
nothing changes, while on the surviving history player `i` eventually quits
alone.  Denote this common value by

\[
 L_i^n=U_i\bigl(\sigma^n[i\leftarrow Q_{n+1}^i]\bigr).
\]

The exact pure-time extremality theorem for quitting games says that the
unrestricted behavioral best-response value is the supremum of the
deterministic finite-quit-time and Never values.  Combining that theorem with
(3.2) and the equality of all late values gives

\[
 B_i(\sigma^n)=\max\{U_i(\sigma^n),L_i^n\},
\]

and therefore

\[
 B_i(\sigma^n)-U_i(\sigma^n)
   =(L_i^n-U_i(\sigma^n))_+.                           \tag{4.1}
\]

Apply the global gap (1.1) to `sigma^n`.  Equation (4.1) gives a player `i`
for which

\[
 L_i^n-U_i(\sigma^n)\ge\gamma,
\]

which is exactly (1.3).

For a nonempty finite set `F subset Nat`, choose `n >= max F` and repeat the
construction.  For `F = empty`, use the construction at `n=0`; there are no
finite listed times to control.  This proves the stated finite-set
strengthening.

## 5. Probability and strategy audit

The mixed timing equilibrium uses independent private mixed actions, exactly
as ordinary mixed Nash equilibrium does.  Its behavioral realization uses
only each player's private randomization along the unique live public history
of a quitting game.  No public correlation or observation of sampled quit
times is introduced.

The finite equilibrium controls only its declared pure actions.  Coverage of
arbitrary behavioral deviations is used only in the final identity for
`B_i`, where the checked quitting-game pure-time extremality theorem applies.
No best response is assumed attained: here the pure-time value set has only
the finite timing-game values and one additional common late value, so its
supremum is their maximum.

## 6. Source correspondence and novelty

The narrow Lean-source audit found the exact downstream interface in
`UniformEquilibrium/Diagnostics/Quitting/`
`TerminalSemanticFiniteDeadlineNashEscalation.lean`:

* `QuittingFiniteDeadlineNashProfile` packages an all-Continue tail and Nash
  optimality for every pure time before the deadline and Never;
* `QuittingFiniteDeadlineNashProfile.bestResponseValue_le_add_escapeCharge`
  upgrades that certificate to the unrestricted behavioral envelope;
* `quittingRootSequencePureTimeTerminalValue_late_sub_none_eq` identifies the
  late singleton escape; and
* `quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff` in
  `TerminalSemanticPositiveSlopeRectangle.lean` gives exact pure-time
  extremality.

That file explicitly treats `QuittingFiniteDeadlineNashProfile` as a supplied
consumer interface and does not construct the finite timing equilibrium or
its behavioral realization.  However, the conference source audit after
review found that Sections 3--6 of
`notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md` already construct this
producer, prove the stronger exact adjusted escape identity, and state the
global-gap obstruction as Proposition 4.  Therefore the present note adds no
new exportable mathematics.

## 7. Conjecture-facing change

This theorem rules out the proposed route

\[
 \text{fixed terminal gap}
 \Longrightarrow
 \text{one uniformly bounded finite family of pure-time witnesses}.
\]

Indeed, if a counterexample exists, its gap witnesses must escape every fixed
finite horizon on the finite-deadline Nash profiles constructed above.  A
positive proof may still use profiles selected by another architecture or a
time bound depending on the profile; what is impossible is a table-uniform
finite witness set derived from the gap alone.

## 8. Lean handoff

The still-unformalized narrow target identified by the prior Noether note is a
producer theorem of the form

```lean
theorem exists_finiteDeadlineNashProfile
    [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} -> Payoff I)
    (deadline : Nat) :
    exists profile,
      QuittingFiniteDeadlineNashProfile reward profile deadline
```

using a finite-game mixed-Nash existence theorem and an exact finite-law to
behavioral-hazard realization.  In the convention of
`QuittingFiniteDeadlineNashProfile`, the permitted finite times are strictly
less than `deadline`; hence the profile controlling times `0,...,n` uses
`deadline = n+1`.  Deadline zero is a separate vacuous finite-action boundary.
The horizon-escape corollary then combines this producer with the pure-time
supremum identity and `HasTerminalExploitabilityGap`.

Before implementation, confirm whether the repository already has a generic
finite mixed-Nash existence theorem in a compatible classical form.  If not,
the mathematical result remains complete but the formalizer will need an
appropriate finite-game existence dependency rather than encoding it as an
axiom.

## 9. Scope and nonclaims

This theorem does not produce a reward table with positive global terminal
gap, a uniform-equilibrium payoff, a chronological shadowing packet, or an
admissible Bellman return.  It refutes only uniform finite-time witness
localization.  It does not refute bounded witnesses on a restricted source
class carrying additional compactness or reach hypotheses.
