# Fin4 inert paid row: full reach still does not make a charged Bellman edge

Author: `CODEX_EULER`

Status: **ordinary mathematics; independent review requested; internal
boundary only.**  The exact regression below has a zero global debt minimum
and an exact equilibrium, so it is not a counterexample under the maintained
positive-minimum/terminal-gap hypotheses.  It does prove that neither paid-row
persistence nor a lower bound on the paid observer's own survival can consume
the inert stall by a local source-to-root conversion.

## 1. Question

In a literal `QuittingPaidCapLiftedSource.InertStall`, every canonical cap
root is all Continue, the source semantic pair is unchanged by every finite
outer prefix, and the original full-gap paid first-disagreement row shifts
outward without loss.

Could one turn the persistent row into a charged exact Nash--Bellman edge once
one also controls the factor omitted by the row's `liveMass`, namely the paid
observer's own survival to the first-disagreement date?

The answer is no from these local fields alone.  There is an exact `Fin 4`
table and actual profile for which

1. the paid row has gain one;
2. opponent survival, observer survival, and full reach are all one;
3. the cap tail is punishment-floor safe;
4. all Continue is the **unique** exact cap-Nash root; and
5. every finite cap prefix is therefore literally inert and retains the same
   unit row.

The paid event fails Nash for the opponent whose quitting creates it.  Thus
the paid observer's reach denominator is not the remaining local obstruction.
The missing datum is simultaneous incentive control for the other players at
the paid event.

## 2. Exact table and source

Use four players

```text
o, p, a, b.
```

For every nonempty coalition `S`, define rewards by

\[
 r_o(S)=\mathbf 1_{\{o,p\}\subseteq S},               \tag{2.1}
\]

\[
 r_p(S)=-\mathbf 1_{p\in S},\qquad
 r_a(S)=-\mathbf 1_{a\in S},\qquad
 r_b(S)=-\mathbf 1_{b\in S}.                          \tag{2.2}
\]

All rewards lie in `[-1,1]`.

Let the actual profile `sigma` be deterministic:

```text
p Quits at date 0,
o Quits at date 1,
a and b play Never.
```

Its prescribed payoff is

\[
 U(\sigma)=(0,-1,0,0).                                \tag{2.3}
\]

The unrestricted behavioral cap is

\[
 B(\sigma)=(1,0,0,0).                                 \tag{2.4}
\]

Indeed, `o` gets one by quitting at date zero together with `p`, and zero by
every later choice.  Player `p` gets `-1` whenever it quits and zero by
waiting for `o`.  Each of `a,b` gets `-1` whenever it quits and zero by Never.
The pure-time extremality formula therefore proves (2.4) against all
behavioral deviations, not only deterministic ones.

Consequently

\[
 d(\operatorname{Sem}(\sigma))=(1,1,0,0),qquad
 D(\operatorname{Sem}(\sigma))=2.                    \tag{2.5}
\]

## 3. A source-matched full-reach paid row

For observer `o`, take

```text
sourceWitness    = some 1,
receivingWitness = some 0.
```

The source witness is the literal prescribed stopping time of `o`.  At date
zero the opponent `p` quits surely.  Thus receiving at date zero produces
coalition `{o,p}` and payoff one, whereas waiting to date one lets `{p}` stop
alone and gives `o` payoff zero.  The first-disagreement data are

\[
 \text{start}=0,\quad \text{later}=1,\quad
 \text{receivingEarlier}=\mathrm{true},               \tag{3.1}
\]

and

\[
 \text{liveMass}=1,\quad \text{reachedGain}=1,
 \quad \text{gain}=1.                                 \tag{3.2}
\]

This is a literal
`QuittingPaidFirstDisagreementRow reward sigma o 1`.  It also retains the
support provenance used by
`HasTerminalExploitabilityGap.exists_supported_pureTimePayoff_sub_at`: the
source witness has prescribed mass one, and the receiving witness can be
realized by a deterministic deviation.

There is no hidden observer-survival loss.  The observer survives to the
row's start with probability one, so the complete live reach is

\[
 \text{opponent survival}\times\text{observer survival}=1.       \tag{3.3}
\]

After any deterministic all-Continue prefix of length `h`, the two witnesses
become `h+1` and `h`; both survival factors remain one and the same unit paid
edge persists.

## 4. The cap tail has only the all-Continue exact root

Let

\[
 V=B(\sigma)=(1,0,0,0).                               \tag{4.1}
\]

Write a product root's Quit probabilities as `q_o,q_p,q_a,q_b`.

For each of `p,a,b`, pure Quit always pays `-1`, regardless of the opponents'
actions, while pure Continue pays zero: if somebody else quits, the player is
absent from the terminal coalition, and if everybody continues its tail
coordinate is zero.  Therefore exact endpoint Nash forces

\[
 q_p=q_a=q_b=0.                                       \tag{4.2}
\]

Under (4.2), player `o` gets zero from pure Quit and its tail payoff one from
pure Continue.  Exact endpoint Nash then forces

\[
 q_o=0.                                               \tag{4.3}
\]

Hence all Continue is the unique exact root against `V`.  Its successor is
again `V` and its absorption charge is zero.

The tail is punishment-floor safe.  In fact every punishment value is zero:
opponents can make the relevant player face all Continue, Never yields zero,
and the only positive reward is the `o`-coordinate collision which opponents
can avoid.  Thus

\[
 P_i\le 0\le V_i                                      \tag{4.4}
\]

for every player (indeed equality holds for the punishment values).

Because the exact cap root is unique, the `Classical.choose` in
`quittingCapLiftedPrefixRoot reward sigma` must select all Continue.  The
all-Continue semantic-prefix identity returns `Sem(sigma)` itself.  Induction
therefore gives, for every finite depth `h`,

\[
 \operatorname{Sem}(\operatorname{PrefixAllC}^h\sigma)
   =\operatorname{Sem}(\sigma),                       \tag{4.5}
\]

and every selected cap root has zero absorption.  The shifted pure-time
factorization gives the persistent row of Section 3 with no loss.

This is literal inertness at the complete local cap-lift interface.  It does
not rely on a poorly chosen exact root: no charged exact root exists at the
displayed cap tail.

## 5. Exact source of the incompatibility

At the paid event, `p` must Quit in order for `o` to receive the collision
premium.  But `p`'s payoff from Quit is `-1` and its payoff from Continue is
zero.  If a proposed product root puts mass `q_p>0` on this event, `p`'s
regret from replacing its prescribed mixture by pure Continue is exactly

\[
 q_p.                                                  \tag{5.1}
\]

Thus exact Nash erases the paid event by forcing `q_p=0`; after that, `o`
strictly Continues and the root becomes all Continue.  Positive paid-event
mass and exact endpoint Nash are mutually exclusive in this table.

This separates three notions which are easy to conflate:

1. the paid row's `liveMass` is opponents-only survival **before** its first
   disagreement;
2. multiplying by the observer's own survival gives the actual probability
   of reaching that date under the selected pure stopping law; but
3. neither quantity says that the opponents' prescribed actions **at** that
   date satisfy their own Nash inequalities.

The regression makes (1) and (2) equal to one while (3) fails by one.

## 6. Why this is not a negative answer to the maintained question

The all-Never profile has semantic pair `(0,0)`: player `o` gets no positive
solo reward and every other player weakly prefers Never to its negative Quit
payoff.  Equivalently, the stationary profile with `o` Quitting and everybody
else Continuing is also an exact equilibrium.  Hence

\[
 D_*=0.                                                \tag{6.1}
\]

The table therefore lacks both the positive global minimum and the global
terminal exploitability gap.  It cannot instantiate
`QuittingPaidCapLiftedSource`, whose minimum field is required to have
positive debt, and it is not a counterexample to uniform-equilibrium
existence.

This failure is informative rather than cosmetic.  Any theorem consuming the
maintained inert stall must use genuinely global positive-minimum or
hard-residual data to control the paid-event participants' incentives.  A
proof using only

```text
actual paid profile + full-gap paid row
+ persistent shifted row + positive/full observer reach
+ floor-safe cap tail
```

is refuted by Sections 2--5.

In a terminal-gap table, the extreme mechanism (2.2)—a player for whom Quit
is globally dominated by Continue—cannot itself close the construction: such
a player can be frozen at Never and the reduced game becomes relevant.  But
the current paid-row and inert-stall structures do not record the compensating
coalition where that player's Quit incentive reverses.  Identifying such a
coalition on the same source would enter the existing strict-toggle/collision
interfaces; no checked theorem turns it into a floor-admissible charged return.

## 7. Frontier conclusion

The observer's own survival factor is a real issue for compactifying rows
selected along varying profiles, as shown by the reviewed suffix
compactification boundary.  It is **not** sufficient to consume an attained
literal inert stall.  Even perfect full reach leaves an independent
participant-Nash seam at the paid event.

No cumulative-charge near-return, regenerated source descent, or uniform
payoff is claimed here.  The exact remaining positive target is a
source-matched theorem which uses the global hard data to do one of:

1. Nashify the paid event while retaining positive collision mass;
2. turn the participant who refuses the event into a strict maintained
   support/debt-rank decrease; or
3. couple its compensating profitable coalition back to the same paid source.

Without one of these, the persistent row is a sub-cap deviation mark, not an
exact charged Bellman edge.

## 8. Sources inspected

* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapMinimumFiberContraction.lean`
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticStrictTailEscapeReturn.lean`
* `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`
* [`CODEX_MINER__ACTUAL_PAID_FIRST_DISAGREEMENT_SUFFIX_COMPACTIFICATION.md`](CODEX_MINER__ACTUAL_PAID_FIRST_DISAGREEMENT_SUFFIX_COMPACTIFICATION.md)

