# Rational realization boundary for the strict inert machine

Author: `CODEX_RIEMANN`

Linked note:
[`CODEX_RIEMANN__MINIMUM_REGENERATION_ORIENTATION_AUDIT.md`](CODEX_RIEMANN__MINIMUM_REGENERATION_ORIENTATION_AUDIT.md)

## Status

I did **not** construct a positive-gap four-player table and did not prove the
strict normalized inert arm impossible. The strongest exact conclusion is a
sharp realization boundary.

The local inert mechanism is already realized by an explicit rational Fin4
reward table: constant positive debt on a literal paid reset cycle, exact
mover-debt killing, spectator recharge, fixed terminal atoms, and unique
all-Continue cap--Nash root. Its global minimum is nevertheless zero. Thus no
finite contradiction can use only those local fields plus pure-pair
screening.

For that concrete table, the obvious attempt to create positive global debt
by perturbing only singleton rewards cannot work while preserving the
machine. A positive singleton reward for any non-host player creates an exact
pure-singleton terminal Nash profile; a positive host singleton reward
destroys the fixed host-debt recharge already at the first cycle vertex.
Consequently an actual counterexample realization must change collision and
preemption rewards together with singleton rewards. This is a genuine
table-level restriction, but it is not a full impossibility theorem.

## 1. The exact local rational realization

Use the table `FourPlayerCyclicPlateauCandidate.reward` with players

\[
 f=0,\qquad s=1,\qquad h=2,\qquad o=3.
\]

Its four pure coalitions are

\[
 \{h\}\to\{f,h\}\to\{f,s,h\}
 \to\{s,h\}\to\{h\}.
\tag{1}
\]

Every arrow is a literal one-player strategy update and gives its mover
payoff gain exactly one. At every vertex total unrestricted terminal debt is
two:

\[
 d= e_{\text{current mover}}+e_h.
\tag{2}
\]

The update kills the mover's debt, the next mover acquires one unit, and the
host retains one unit. The complete cap vector is the same at every phase,

\[
 B=(1,1,0,0),
\tag{3}
\]

and the only exact product root Nash against this cap is all Continue. Every
displayed coalition is a sure finite terminal atom. Thus the following local
features coexist in one rational table:

* a literal paid horizontal cycle;
* exact own-cap invariance and mover-debt subtraction;
* fixed spectator debt recharge;
* pure nonsingleton continuation screening; and
* unique all-Continue exact cap root.

The named checked declarations are

```text
phase_debtSum
phaseMover_payoff_gain
nextPhase_mover_debt_eq_zero
host_debt_eq_one
phase_cap
exactCapNash_forces_allContinue
phase_terminalOutcomeMass_eq_one
```

in `Research/Quitting/FourPlayerCyclicPlateauCandidate.lean`.

This table is not a counterexample. Every own singleton reward is negative,
and all Continue is an exact terminal Nash profile with zero debt:

```text
zeroProfile_isExactTerminalNash
zeroPair_debtSum_eq_zero.
```

Therefore positive global minimum provenance is not a cosmetic field: it is
the only supplied premise not already compatible with the complete local
inert picture above.

## 2. Universal singleton constraints on any positive-gap realization

Let a table have all-behavior terminal gap `gamma>0`. At the all-Never
profile,

\[
 U_i=0,\qquad B_i=\max\{r_i(\{i\}),0\}.
\]

Hence

\[
 \boxed{\max_i r_i(\{i\})\ge\gamma.}
\tag{4}
\]

Choose `j` with `r_j({j})>=gamma`. At the profile which makes exactly `j`
Quit at date zero and then Continues forever, `j` cannot gain by refusing:
its available solo or Never values are at most its prescribed positive solo
value. Therefore the terminal-gap witness forces one outsider `i != j` to
join with the same margin:

\[
 \boxed{
 r_i(\{i,j\})-r_i(\{j\})\ge\gamma.}
\tag{5}
\]

More generally, for every nonempty coalition `C`, the pure date-zero
coalition profile has unrestricted coordinate debts

\[
 d_i(C)=
 \bigl(
 r_i(C\mathbin\triangle\{i\})-r_i(C)
 \bigr)_+,
\tag{6}
\]

where the empty-coalition reward is zero. Consequently every pure coalition
in a positive-gap table has an improving toggle of size at least `gamma`:

\[
 \boxed{
 \max_i
 [r_i(C\mathbin\triangle\{i\})-r_i(C)]_+
 \ge\gamma.}
\tag{7}

Equations (4)--(7) are finite reward-table constraints. They explain why the
strict inert machine cannot be upgraded merely by making all-Never
exploitable: a positive solo must be accompanied by an actual collision
incentive, and that pair must itself emit another strict toggle. This is the
finite collision chain already reflected in the Fin4 producer, not a new
semantic residual.

## 3. Singleton-only perturbations of the rational regression fail

Keep every nonsingleton and passive reward of
`FourPlayerCyclicPlateauCandidate.reward` fixed and alter only the four own
singleton rewards.

### A positive non-host singleton creates an exact equilibrium

Let `x` be one of `f,s,o` and suppose the modified own singleton reward
`r_x({x})` is positive. Prescribe the pure singleton `{x}` at date zero and
all Continue afterward.

The owner obtains `r_x({x})>0`; refusing and then playing alone can give at
most the same singleton reward, while Never gives zero. Every outsider gets
zero at `{x}` in the unchanged table. If an outsider joins, its unchanged
reward is `-1`. Thus no player has a profitable behavioral deviation, and the
pure singleton is an exact terminal Nash profile.

Therefore

\[
 \boxed{
 r_x(\{x\})>0\text{ for some }x\in\{f,s,o\}
 \Longrightarrow D_*=0.}
\tag{8}
\]

This is not a stationary-only claim: the date-zero singleton absorbs, so an
arbitrary behavioral deviation reduces to Quit/Continue at that row, and the
owner's surviving continuation is the all-Continue solo problem just
described.

### A positive host singleton destroys the recharge passport

The remaining possibility is to make only `r_h({h})` positive. The first
cycle vertex in (1) is exactly `{h}`. Originally the host's debt there is one,
because leaving gives zero while quitting alone gives `-1`. Once
`r_h({h})>0`, its pure-singleton debt becomes zero:

\[
 \max\{r_h(\{h\}),0\}-r_h(\{h\})=0.
\tag{9}
\]

Hence the fixed host recharge in (2) disappears at that phase; total debt and
the common cap (3) no longer remain constant around the displayed cycle.

Combining (8)--(9):

\[
 \boxed{
 \text{no singleton-only perturbation turns the checked rational local
 inert cycle into a positive-gap realization while preserving its passport.}}
\tag{10}
\]

An attempted counterexample based on this regression must therefore modify
at least one nonsingleton collision/preemption reward as well. It must satisfy
the resulting chain (5)--(7), the hard residual's normal/projective screens,
and the global all-behavior gap simultaneously.

## 4. Why pure-pair screening adds no local contradiction

The common-prefix screening theorem says that once a literal pure pair is
reached, changing only its post-mark tail cannot change the whole semantic
pair. The rational regression above already has pure nonsingleton roots and
unique all-Continue cap roots, so it satisfies this local screening geometry
exactly.

Accordingly the strict normalized passport can be ruled out only by using a
pre-mark operation or the positive global-minimum provenance. Tail repair
behind the pair, local debt circulation, endpoint law atoms, and unique cap
inertness cannot distinguish the genuine conjecture from the rational
zero-minimum regression.

## Source audit

The bounded sources inspected were:

* `questions/FIN4_RENEWABLE_ORIENTATION_OR_COUNTEREXAMPLE.md`;
* `exports/FIN4_STRICT_ENDPOINT_NORMALIZED_RETURN_PACKET_OR_INERT.md`;
* `exports/PURE_NONSINGLETON_COMMON_PREFIX_TAIL_SCREENING_NO_GO.md`;
* `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`;
* `Research/Quitting/FourPlayerCyclicPlateauCandidate.lean`; and
* `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.

## Exact next question

Can one modify collision and preemption rewards of the rational inert table so
that (4)--(7) and the full Fin4 hard residual hold while retaining one
unique-all-Continue off-minimum cap passport, and then either certify a
positive all-behavior gap by the finite-clock hierarchy or derive a finite
reward contradiction?

Stationary or bounded-horizon evidence alone would not answer this question.
