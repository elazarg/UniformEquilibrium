# Positive-social bubble causal-inert converter no-go

**Owner:** `CODEX_RAMSEY`  
**Status:** `INDEPENDENTLY REVIEWED REVISE -> PASS`  
**Scope:** exact local converter-class no-go; not a counterexample to the
[maintained Fin4 completion roadmap](../questions/README.md)

## 1. Converter being tested

The compact-outcome bubble account adds one datum not present in a bare paid
cap port: when all complete clocks escape to `Never`, a retained finite
coalition atom can carry strictly positive aggregate reward.  A tempting
finite-atom converter is therefore

```text
positive finite causal suffix atom
+ strictly positive escaped social reward
+ source-matched paid pure-time row
+ arbitrarily deep exact cap-Nash prefixes retaining the atom
  => positive exact cap charge or a strict semantic/debt-support descent.
```

The implication is false, even with full atom reach, a floor-safe cap tail,
and selector-independent inertness.  The example below is an actual rational
`Fin 4` quitting table and actual behavioral profiles.  Its global semantic
minimum is zero, so the example isolates the exact additional work which must
be done by the positive-global-minimum and hard-residual hypotheses.

## 2. Reward table

Use players `0,1,2,3` and put

\[
 A=\{0,1\}.
\]

For `i in {0,1,3}`, set, for every nonempty coalition `S`,

\[
 r_i(S)=
 \begin{cases}
 -1,&i\in S,\\
 0,&i\notin S.
 \end{cases}                                             \tag{2.1}
\]

For player `2`, set

\[
 r_2(A)=4,
 \qquad r_2(A\cup\{2\})=5,                              \tag{2.2}
\]

and set every other coordinate `r_2(S)` equal to `-1` when `2 in S` and
equal to `0` when `2 notin S`.  All rewards are integers in `[-1,5]`.

For every integer `n>=1`, let `sigma_n` be the deterministic profile in
which players `0,1` Quit at date `n` and players `2,3` play `Never`.

## 3. Constant unrestricted semantic pair

The prescribed outcome is always `A`, so

\[
 U(\sigma_n)=(-1,-1,4,0).                               \tag{3.1}
\]

The unrestricted behavioral caps are

\[
 B(\sigma_n)=(0,0,5,0).                                 \tag{3.2}
\]

For players `0,1`, quitting at a date `t<=n` gives `-1`, while every date
`t>n`, as well as `Never`, is preempted by the other base player's exit at
`n` and gives `0`.  Player `3` has the same cap comparison.  For player `2`,
quitting before `n` gives `-1`, quitting at `n` gives `5`, and quitting later
or playing `Never` gives `4`.  Pure-time
extremality upgrades these enumerations to all behavioral deviations.
Consequently

\[
 d(\operatorname{Sem}(\sigma_n))=(1,1,1,0),
 \qquad D(\operatorname{Sem}(\sigma_n))=3               \tag{3.3}
\]

for every `n`.

## 4. Positive bubble and a same-source paid row

The terminal outcome law of every `sigma_n` is exactly `delta_A`.  The
complete stopping laws of all four players converge weakly on `Nbar` to
`delta_Never`: the two finite clocks move to infinity and the other two are
already `Never`.  Thus the compact-outcome defect is the unit bubble

\[
 e(A)=1.                                                \tag{4.1}
\]

It has strictly positive social reward:

\[
 R(A)=\sum_i r_i(A)=-1-1+4+0=2>0.                      \tag{4.2}
\]

This is not merely a positive moment.  At the same actual source `sigma_n`,
player `2` has the literal pure-time comparison

```text
source witness    = Never,
receiving witness = date n.
```

The two payoffs are respectively `4` and `5`, hence the gain is one.  No
player quits before `n`, so opponent survival, player `2`'s own survival, and
the full reach of the first-disagreement row are all one.  The paid event is
the actual coalition `A union {2}` at date `n` under the receiving deviation.

## 5. The exact cap correspondence is the singleton all-Continue root

Fix the cap tail

\[
 V=(0,0,5,0).                                          \tag{5.1}
\]

At an arbitrary product root, Quit pays `-1` to each of players `0,1,3`,
independently of the other actions.  Continue pays `0`: if somebody else
Quits, the player is absent and receives `0`, and if nobody Quits the tail
coordinate is `0`.  Exact root Nash therefore forces

\[
 q_0=q_1=q_3=0.                                        \tag{5.2}
\]

Against those three Continue actions, player `2` compares singleton Quit
payoff `-1` with continuation value `5`, so exact Nash also forces `q_2=0`.
Thus

\[
 \operatorname{Nash}(V)=\{\mathbf C\}.                 \tag{5.3}
\]

The tail is punishment-floor safe.  Opponents can force any selected player
to face a coalition on which continuing gives `0`; hence every punishment
value is at most `0`, while every coordinate of `V` is nonnegative.

It follows from (5.3), independently of any root selector, that every finite
cap prefix is literally all Continue.  Its charge is zero, its semantic pair
is still (3.1)--(3.2), its positive-debt support is still `{0,1,2}`, and its
literal suffix atom and unit paid row are merely translated one date outward.
This supplies exact retained causal cap-Nash words of every requested finite
depth, but neither a positive charged edge nor a strict support/debt descent.

## 6. Exact separation and scope

The example refutes the converter of Section 1, including the strengthening
which tries to pay the cap surcharge with the bubble's **positive aggregate
reward**. The general identity behind this numerical account is now proved in
Lean by
`QuittingTerminalSemanticEscapeAccount.debtSum_sub_target_eq_escapeSocialReward_sub_capDropSum`
and its production minimum consequences.
The all-Never limiting profile has semantic debt zero, while the cap jump lost
at the weak limit is

\[
 \sum_i(B_i-\bar B_i)=5.
\]

Therefore

\[
 D(\text{all Never})-3=R(A)-5=2-5=-3.                 \tag{6.1}
\]

Positive escaped social reward need not dominate the escaping cap jump and
does not orient an exact root.

The checked social-sign split closes the nonpositive aggregate-reward chamber,
but it deliberately leaves this strict positive-social arm without a return,
renewal, rank, terminal, or uniform-equilibrium consumer. The regression's
local nonconversion conclusion therefore remains current.

This is stronger than the earlier full-reach paid-row regression in
[`CODEX_EULER__FIN4_INERT_PAID_ROW_FULL_REACH_NONCONVERSION.md`](CODEX_EULER__FIN4_INERT_PAID_ROW_FULL_REACH_NONCONVERSION.md)
in one precise direction: the whole family now exhibits a unit compact
outcome bubble with strictly positive social reward while all complete clocks
escape to `Never`.  It does not strengthen that regression toward the full
counterexample premises.

Indeed, literal all-Never has debt zero here.  The table has neither a
positive global minimum nor a terminal exploitability witness.  It does not
refute the desired full-premise producer.  It proves only that the remaining
proof must use the global minimum/hard residual to control the escaping cap
jump or the paid-event participants; the finite atom, its positive social
moment, and its complete causal prefix provenance do not do so locally.

## 7. Source audit and review request

The ordinary proof uses the checked unrestricted pure-time reduction
`sSup_range_quittingTerminalPayoff_update_eq_pureTime` and the exact
all-Continue fixed-pair theorem
`quittingTerminalSemanticPrefix_allContinue_eq_self_iff_isZeroNash_at_cap`
(with the finite-stack packaging
`capNashRootStack_eq_replicate_allContinue_of_unique_terminalCap`) from
`Research/Quitting/UniqueAllContinueCapStackNoGo.lean`, together with
elementary weak convergence of deterministic stopping laws on `Nbar`.  The
compact-bubble provenance and social-surplus
identity were independently reviewed in
[`feedback/CHATGPT_EXTERNAL__CONCRETE_NONLOCALITY_DERIVATIONS_INTAKE__BY_TESLA_COMPACT_EXCHANGE.md`](../feedback/CHATGPT_EXTERNAL__CONCRETE_NONLOCALITY_DERIVATIONS_INTAKE__BY_TESLA_COMPACT_EXCHANGE.md).

Requested independent checks are: the complete reward-table enumeration,
all-behavior cap (3.2), first-disagreement reach, uniqueness (5.3), floor
safety, weak-law/bubble statement, positive social reward, and the strict
local-only scope relative to the positive-global-minimum Fin4 problem.

The independent review is
[`CODEX_RAMSEY__POSITIVE_SOCIAL_BUBBLE_CAUSAL_INERT_CONVERTER_NOGO__BY_CODEX_EULER.md`](../feedback/CODEX_RAMSEY__POSITIVE_SOCIAL_BUBBLE_CAUSAL_INERT_CONVERTER_NOGO__BY_CODEX_EULER.md).
It found the mathematical result sound after the literal pure-time wording
repair incorporated above and recommends retaining the result internally.
