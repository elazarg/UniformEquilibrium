# Review of finite-deadline Nash horizon escape

Reviewer: `CODEX_EULER`

Note reviewed:
[`notes/CODEX_FERMAT__FINITE_DEADLINE_NASH_HORIZON_ESCAPE.md`](../notes/CODEX_FERMAT__FINITE_DEADLINE_NASH_HORIZON_ESCAPE.md)

Verdict: **REVISE, then PASS as ordinary mathematics; retain internally and
do not export as new mathematics.**  I found no counterexample to the stated
horizon-escape theorem, including at zero tail masses and against unrestricted
behavioral deviations.  The source/novelty section is materially incomplete:
the finite-deadline producer and, in substance, the same global-gap consequence
already appear in Sections 3--6 of
[`notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md).
Noether's Proposition 3 was independently reviewed in
[`feedback/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_CEDAR.md`](CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION__BY_CODEX_CEDAR.md),
and its Proposition 4 states the stronger adjusted-deficit signature for every
finite-deadline Nash selection.  The current checked Lean module remains only
a consumer, so a Lean producer would still be useful; that does not make this
ordinary-mathematics producer new within the conference record.

## Claim checked

For every `n`, form the finite timing game in which each player chooses one of
`0,...,n,Never`, take a mixed Nash equilibrium, and realize each mixed time law
as a behavioral hazard profile which is surely Continue strictly after date
`n`.  The claim is that every declared pure time and `Never` has gain at most
zero, while a global unrestricted terminal gap `gamma` forces some player to
gain at least `gamma` by quitting at date `n+1`.  Consequently no one finite
set of pure quit times plus `Never` detects a fixed positive fraction of the
gap at every profile.

## Falsification audit

### 1. The finite timing game and its mixed Nash equilibrium

The action set is finite and nonempty, and its payoff at a pure action profile
is exactly the quitting-game terminal payoff of the corresponding deterministic
stopping times.  The generic checked theorem
`GameTheory.exists_isNash_mixed` in `GameTheory/Analysis/Nash.lean` supplies a
mixed Nash equilibrium.  Independent private mixing is exactly the required
probability mode; no public correlation is introduced.

Nash optimality bounds every permitted pure action, including actions outside
the support.  Conversely, the prescribed payoff is the mixed-law average of
those pure-action payoffs.  Hence

`max_(t in {0,...,n,Never}) V_i(t) = U_i`.

This equality does not require a support-indifference argument and remains
valid when some permitted actions have probability zero.

### 2. Hazard realization, including a zero tail

Put

`M_t = mu({t,...,n,Never})`

and use hazard `x_t=mu(t)/M_t` when `M_t>0`, and `x_t=0` when `M_t=0`.
The correct induction invariant is that survival to date `t` equals `M_t`.
If `M_t>0`, multiplication by `1-x_t=M_(t+1)/M_t` advances the invariant.  If
`M_t=0`, all later finite masses and the `Never` mass vanish and the live path
has already acquired zero probability; assigning hazard zero on that
unreachable tail is harmless.  Thus

`Pr(T=t)=mu(t)` and `Pr(T=Never)=mu(Never)`

also in the zero-denominator case.  Applying this coordinatewise preserves the
independent product law and hence all terminal payoffs and unilateral pure-time
payoffs.

This agrees with Noether's exact planned-time representation.  The remaining
Lean obligation is the packaged finite-law-to-hazard realization, not a
mathematical existence gap.

### 3. Equality of all late values

Against the opponents' realized laws, no opponent has finite stopping mass
strictly after `n`.  For any two finite dates `t,t'>n`, an opponent stopping by
`n` fixes the same terminal outcome under both deviations; if all opponents
choose `Never`, either deviation makes player `i` the singleton quitter.
Therefore every `t>n` has the common value

`L_i = V_i(Never) + E_i r_i({i})`,

where `E_i` is the product of the opponents' `Never` masses.  This includes
negative singleton rewards and `E_i=0`.  It matches
`quittingRootSequencePureTimeTerminalValue_late_sub_none_eq` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`.

### 4. Unrestricted behavioral supremum

The checked identity
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean` (and its
best-response wrapper
`quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeRectangle.lean`)
identifies the unrestricted behavioral envelope with the supremum over finite
pure quit times and `Never`.  Those values split into the finite declared set,
whose maximum is `U_i`, and the one common late value `L_i`.  Consequently

`B_i-U_i = max(0,L_i-U_i)`.

No unrestricted best response needs to be attained.  Applying the assumed
global gap therefore selects a player with `L_i-U_i >= gamma`, and date `n+1`
attains that value.  I found no quantifier or conditioning failure here.

## Required repairs

1. **Correct the novelty claim.**  Section 6 must cite Noether Sections 3--6.
   Noether Section 4 already gives the unconditional producer for every finite
   deadline, and Proposition 4 combines it with a global terminal gap to force
   a uniform positive adjusted late deficit at every finite timing Nash
   equilibrium.  The strongest accurate novelty description is a concise,
   independently rederived corollary/no-go presentation, not a new producer.

2. **Handle the empty finite set.**  The sentence “choose `n >= max F`” is
   undefined for `F=empty`.  Say: if `F` is nonempty choose such an `n`; if it
   is empty choose any `n` (for example `0`).

3. **Align the deadline convention.**  In
   `QuittingFiniteDeadlineNashProfile reward profile deadline`, permitted
   finite times satisfy `t < deadline` and the all-Continue tail starts at
   `deadline`.  The note's action set `0,...,n` and tail strictly after `n`
   therefore produce the checked interface at `deadline=n+1`, not `n`.
   A producer quantified over every `deadline : Nat` should treat deadline
   zero separately by the all-`Never` profile, or state only positive
   deadlines and reindex.  Also write “strictly after date `n`” wherever the
   present phrase could be read as including date `n`.

These are statement/source repairs only; they do not change the proof of the
main theorem.

## Duplication and export assessment

`TerminalSemanticFiniteDeadlineNashEscalation.lean` explicitly assumes a
supplied `QuittingFiniteDeadlineNashProfile`; it does not presently contain
the finite-game producer.  Thus formalizing the producer remains a legitimate
code task.  However, conference novelty must also be audited against existing
ordinary mathematics.  Noether already records:

- the exact hazard realization, including zero tails;
- finite mixed-Nash production for every deadline;
- the stronger exact debt identity
  `max(0,E_i r_i({i})-NeverSlack_i)`; and
- under a global gap, a fixed positive adjusted deficit for every deadline
  and every equilibrium selection.

The Fermat theorem follows immediately from those items by observing that the
adjusted deficit is exactly the gain of every late pure time.  I therefore do
not recommend a separate export packet: it fails the source-novelty gate and
does not strictly narrow a current named conjecture residual beyond Noether's
stronger screen.  The note is still useful internally as a clean negative
answer to the bounded-witness proposal and as a compact Lean-corollary target.

## Scope confirmed

The theorem is conditional on a reward table with a uniform all-profile
terminal gap.  It neither constructs such a table nor gives a Bellman path,
punishment-floor edge, returned payoff, uniform-equilibrium payoff, or
counterexample to the quitting-game conjecture.  It rules out only one
table-uniform finite pure-time localization architecture; profile-dependent
times and source-restricted compactness hypotheses remain untouched.
