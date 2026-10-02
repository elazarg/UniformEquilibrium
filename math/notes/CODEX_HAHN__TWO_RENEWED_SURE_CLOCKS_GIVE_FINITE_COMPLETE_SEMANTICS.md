# Two renewed sure clocks give an exact finite-clock semantic representative

Author: `CODEX_HAHN`

## Status

**Exact ordinary mathematics; source strengthening, not a consumer.**  After
two successive distinct-owner renewals, the cap-child profile contains two
distinct prescribed finite sure clocks.  Deleting or replacing any one
player still leaves one of those clocks, so every unilateral outcome is
absorbed by one common finite deadline.  Truncating all strategies after that
deadline therefore preserves both prescribed payoff and every unrestricted
behavioral cap exactly.

This repairs the direct finite-clock semantic adapter failure of a one-clock
child.  It does not make the resulting off-minimum source a global-minimum
finite-clock source, an adjacent pair of finite-timing Nash laws, or a
terminal equilibrium.

## Question

Does iterating the late-reset cap-clock renewal accumulate actual finite-clock
structure, or does every new horizontal cap installation destroy the clock
retained from the preceding phase?

## 1. Two-sure-clock truncation lemma

Let `sigma` be any behavioral profile in a finite quitting game.  Suppose
there are distinct players `a,b` and finite dates `T_a,T_b` such that under
their prescribed strategies, `a` Quits surely no later than `T_a` and `b`
Quits surely no later than `T_b`.  Put

\[
 H=\max\{T_a,T_b\}.
\tag{1}
\]

Construct `sigma^[H]` by retaining every player's prescribed actions through
date `H` and forcing Continue at every later date.  Equivalently, on stopping
laws, retain the atoms at dates at most `H` and move all later finite mass to
Never.

Then

\[
 \boxed{\operatorname{Sem}(\sigma^{[H]})=
        \operatorname{Sem}(\sigma).}
\tag{2}
\]

Moreover `sigma^[H]` is a finite-clock profile with common clock bound `H`.

### Proof

Prescribed play under either profile absorbs by date `H`, so its outcome law
and prescribed payoff are unchanged.

Fix a unilateral deviator `i` and use the same complete behavioral strategy
for `i` against the two opponent profiles.  If `i=a`, player `b` still Quits
surely by `H`.  If `i=b`, player `a` does.  If `i` is different from both,
both sure clocks remain.  In every case the deviating outcome absorbs by
`H`, before any truncated opponent action can be observed or affect the
terminal coalition.  The payoff of **every** complete deviation is therefore
identical against `sigma_(-i)` and `sigma^[H]_(-i)`.  Taking the supremum over
the same unrestricted behavioral deviation class proves equality of the two
caps for `i`.  This holds for every player, proving (2).

After date `H` every truncated strategy Continues surely.  Its stopping law
has support only on dates at most `H` and Never, so the common finite-clock
claim is literal.

The same proof also shows the deletion form: replacing any one player by
Never leaves absorption by `H` under the other prescribed strategies.

## 2. Sure clocks persist through cap-clock renewal

Consider one positive-survival renewal phase with cap owner `b`.  At finite
depth `N`, installing the shifted cap gives the child

\[
 \zeta^N=\tau^N[b\leftarrow A_b^N],
\tag{3}
\]

where `A_b^N` is a deterministic finite clock.  Thus `b` is a prescribed
sure-clock player in `zeta^N`.

Choose the late reset observer `j`.  The renewal theorem has `j!=b` and makes
Quit0 an attained cap for `j` at this actual child.  Rerun the
positive-survival exact-prefix construction with owner `j`.  Installing its
shifted cap at a finite later depth changes only `j`'s complete strategy.
Every other strategy, including `b`'s sure finite clock inside the literal
tail, is unchanged, merely shifted by the new finite prefix length.  The new
child therefore contains two distinct prescribed finite sure clocks, one for
`j` and one for `b`.

Inductively, let `G_m` be the set of players already carrying a prescribed
finite sure clock in a renewed child.  Prefixing shifts their clock dates but
does not remove them.  Installing the next owner's deterministic cap changes
only that owner and leaves every other member of `G_m` unchanged; the owner
itself is again assigned a finite sure clock.  Hence

\[
 G_m\subseteq G_{m+1}.
\tag{4}
\]

In particular, once `|G_m|>=2`, it never falls below two.  At the first
renewal, the new observer `j` is distinct from the already installed owner
`b`; hence this happens after the second cap installation.  Later owner
labels may revisit an earlier player, but monotonicity of `G_m` is unaffected.

There need not be one deadline uniform over all renewal phases.  The theorem
supplies one finite common deadline separately at each child, which is enough
for the exact semantic truncation (2).

## 3. Sequential cap attainment does not give two solved coordinates

Just before installing a new owner's cap, the previously installed owner's
zero debt remains zero through every exact prefix: exact prefix debt action
preserves a zero coordinate.  The new owner replacement then kills the new
owner's debt.

But that horizontal replacement changes an opponent strategy of every old
owner.  It may raise an old owner's unrestricted cap or lower its prescribed
payoff.  Thus after the update the old zero coordinate may reactivate:

\[
 d_b(P)=0,\qquad
 d_j(P[j\leftarrow\beta_j])=0,\qquad
 d_b(P[j\leftarrow\beta_j])\text{ may be positive}.
\tag{5}
\]

The two sure clocks survive, but simultaneous cap optimality need not.  If an
old owner is reactivated, the two-clock lemma does ensure that its new cap is
attained in a finite response problem.  This turns remote cap leakage into a
finite horizontal response, not into an exact predecessor edge.

## 4. Consumer audit

The finite-clock minimum theorem does not apply: a late reset source is
uniformly separated **above** the global minimum debt fibre by the exact
reset-exit theorem.  That consumer assumes that the finite-clock profile
itself realizes the global minimum.

The adjacent-deadline lane does not apply: the construction supplies one
actual finite-clock semantic source, not Nash laws for two adjacent finite
horizons with the required censor/include relation.

The general actual-source pure-time response machinery can now be applied
without a tail-truncation error, but its output is the already known
minimum-entrance or horizontal finite response-cycle alternative.  It does
not serialize those responses into an exact Nash--Bellman chronology.

Finally, two sure clocks do not make the profile terminal Nash.  They screen
all post-deadline tails, but exact root or complete-response optimality can be
destroyed when the other sure-clock player changes strategy, as in (5).

## Source correspondence

The renewable cap-clock phase is
`CODEX_HAHN__LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE`.  The one-clock
adapter failure is
`CODEX_HAHN__TERMINAL_DEPTH_CAP_CHILD_FINITE_CLOCK_ADAPTER_FAILURE`.
The checked finite-clock definition and semantic canonicalization are in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FiniteClockCanonicalization.lean`.
The minimum-only consumer is
`finiteClockMinimum_exactCapPurification_or_pureTimeDescentPaidPort` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/FiniteClockMinimumPaidPort.lean`.

## Scope and nonclaims

This note proves an exact complete-semantic finite-clock representation for
every renewed child after two distinct cap installations.  It does not claim
that the original untruncated strategy profile itself satisfies the syntactic
finite-clock predicate.

It does not prove that two cap owners remain simultaneously solved, that the
source is on the minimum fibre, that a finite response cycle is temporal, or
that a uniform-equilibrium payoff exists.

## Next exact question

In the two-sure-clock source, can the finite cap response which reactivates an
old zero-debt owner be charged against the global boxed capacity restored by
the horizontal update, or can a finite two-owner preemption cycle replenish
that capacity indefinitely?
