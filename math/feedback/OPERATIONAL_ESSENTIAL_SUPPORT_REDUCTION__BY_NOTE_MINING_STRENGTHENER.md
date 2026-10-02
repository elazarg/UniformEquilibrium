# Gate review of operational essential support reduction

Reviewer: `NOTE_MINING_STRENGTHENER`

Object reviewed:
`notes/CODEX_CEDAR__OPERATIONAL_ESSENTIAL_SUPPORT_REDUCTION.md`

## Verdict

### Mathematics: PASS, with two wording corrections and one strengthening

Propositions 1--3 are correct.  The exact full-gap finite-time extraction is
valid, the deletion/lift directions are correct, and all deviation statements
range over arbitrary behavioral strategies.  No limiting or subsequence
argument is hidden in the proof.

The sharpest statement is stronger than Proposition 3's final sentence:
for every `0 < epsilon < gamma` and **every** terminal `epsilon`-Nash profile
of the block-deleted game, the same quiet lift has a deleted player and a
finite deterministic Quit time with gain at least the full `gamma`.  The
finite time can moreover be chosen with positive mass in the stopping law of
the particular behavioral gap witness.

Combining this with the separately audited coalition expansion gives a
profile-free block-hitting screen: in a cardinal-minimal counterexample,
every nonempty proper deleted block contains an owner whose solo/Never or
join-toggle pressure against the survivor set is at least `gamma`.  For a
singleton block this holds for the prescribed owner, so every player of a
minimal counterexample has such a finite table certificate.

### Export gate: FAIL as a standalone packet

This is a complete general-cardinality **normal-form theorem**, but not a
cardinality reduction and not a consumer.  It does not bound the cardinality
of a minimal counterexample, reconstruct an ambient equilibrium from a
survivor equilibrium, give compatible witnesses as the deleted block varies,
or feed a current terminal/near-return/rank compiler.  The quiet lift is
proved exploitable; that is the output, not a route to a uniform payoff.

The current export criteria exclude a local or static passport without a
downstream semantic consumer.  The theorem is suitable for a Lean `Research`
handoff, and its sharp inequality could become export-worthy if it closes a
named deletion chamber.  It should not presently be advertised as a complete
general-cardinality reduction of the conjecture.

## 1. Exact strengthened theorem

Let `I` be finite, let `B : Finset I`, let `r` be a quitting reward table,
and let

```text
HasTerminalExploitabilityGap r gamma,
0 < gamma.
```

Let `r_B` be the game on `QuittingBlockSurvivor B`, let `sigma` be one of its
behavioral profiles, and suppose

```text
IsEpsilonAsymptoticNash r_B epsilon sigma,
epsilon < gamma.
```

Let `hatSigma` be the literal ambient lift which makes every member of `B`
play Never.  Then there exist

```text
d : I,
tau : ambient behavioral strategy of d,
t : Nat
```

such that

```text
d in B,
U_r(hatSigma,d) + gamma <= U_r(update hatSigma d tau,d),
U_r(hatSigma,d) + gamma <=
  U_r(update hatSigma d (QuitExactlyAt t),d).
```

The last `t` may be chosen so that

```text
(quittingBehaviorStoppingLaw r tau) (some t) > 0.
```

No positivity hypothesis on `epsilon` is needed for this implication.  The
positivity `0 < epsilon` is needed only when cardinal minimality invokes a
uniform payoff to produce an `epsilon`-Nash survivor profile.

### Proof audit

Apply the exact ambient terminal gap to `hatSigma`, obtaining `d,tau`.  If
`d` survives deletion, then

```text
quittingTerminalPayoff_liftDeletedProfile
quittingTerminalPayoff_update_liftDeletedProfile_eq_deleteDeviation
```

transport both sides of the gain inequality to the survivor game.  The
survivor `epsilon`-Nash inequality then gives `gamma <= epsilon`, a
contradiction.  Hence `d in B`.

For this fixed `tau`, put

```text
mu = quittingBehaviorStoppingLaw r tau
V(q) = payoff after replacing d by the pure-time strategy q.
```

The checked identity

```text
quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
```

gives

```text
U_r(update hatSigma d tau,d) = E_mu[V].
```

Because `d in B`, it is already prescribed Never, and
`Function.update_liftDeletedProfile_never` gives

```text
V(none) = U_r(hatSigma,d).
```

If every positive-mass finite atom had value strictly below
`U_r(hatSigma,d)+gamma`, then every support atom of `mu` would be strictly
below that threshold: the `none` value is also strictly below it because
`gamma>0`.  A PMF has a positive-mass support atom.  Splitting off any such
atom makes the expectation strictly below the threshold, using bounded
rewards and the fact that the real masses sum to one.  This contradicts the
ambient gap.  Therefore one positive-mass atom is `some t` and has value at
least the threshold.

This proves both the exact constant and the stronger support-incidence claim.
It does not infer attainment from an `sSup`.

## 2. Cardinal-minimal corollary

Let `minimal : MinimalFinQuittingCounterexample`, let

```text
n = minimal.playerCount,
gamma = minimal.witness.terminalGap.
```

For every `B : Finset (Fin n)` with `B.Nonempty` and `B != univ`, and for
every `0 < epsilon < gamma`, cardinal minimality gives a uniform-equilibrium
payoff of the block-deleted survivor game and hence a terminal
`epsilon`-Nash profile.  In fact the preceding theorem applies to **every**
such profile.  Thus

```text
forall sigma,
  IsEpsilonAsymptoticNash r_B epsilon sigma ->
  exists d in B, exists t : Nat,
    U_r(Lift_B sigma,d) + gamma <=
      U_r(update (Lift_B sigma) d (QuitExactlyAt t),d).
```

The cardinal calculation is exact:

```text
card (QuittingBlockSurvivor B) = n - B.card < n.
```

`B.Nonempty` gives the strict inequality; `B != univ` makes the survivor
type nonempty, which is required by the smaller-game uniform-payoff theorem.
No restriction/deletion subtype identification is used.

### Singleton specialization

For `B={d}`, the selected deleted owner is necessarily the prescribed `d`.
Hence every player of a cardinal-minimal counterexample has the following
operational property: every sufficiently accurate terminal equilibrium of
the game with that player deleted, when quietly lifted, admits a finite
deterministic deviation by that same player with gain at least `gamma`.

This is stronger and cleaner than the general-block formulation because no
deleted-player selector can switch.

## 3. Profile-free finite table consequence

Let `J=I\B`.  For `d in B`, define

```text
ell_d(J) = min ({0} union {r_d(S) : empty != S subset J}),
P_d(J)   = max (0, r_d({d}) - ell_d(J)),
C_d(J)   = max ({0} union
                {r_d(S union {d}) - r_d(S) : empty != S subset J}).
```

The exact finite-time witness and

```text
quittingRootSequencePureTimeTerminalValue_some_sub_none_eq
quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle
```

give

```text
exists d in B, max (P_d(J)) (C_d(J)) >= gamma.             (1)
```

The selected row and coalition have positive probability, but that
probability need not have a positive lower bound.  The gain in (1) is an
unweighted reward difference.

For a singleton deletion this becomes the table-level condition

```text
forall d, max (P_d(I\{d})) (C_d(I\{d})) >= gamma.          (2)
```

Thus a cardinal-minimal counterexample is operationally irreducible in a
precise finite sense.  Equations (1)--(2) are a genuine strengthening of the
minimal-counterexample normal form, but without a consumer they still do not
bound `n` or construct an ambient equilibrium.

The separately reviewed sharp cap

```text
P + min(1,A) * (C-P)_+
```

is also valid under the stated row-absorption bound.  It should be formalized
with this packet if a deletion chamber needs it; it does not change the
present export verdict.

## 4. All-behavior and probability audit

- The ambient witness `tau` is an arbitrary randomized, calendar-dependent,
  history-dependent behavioral strategy.
- The deletion naturality theorem transports an arbitrary survivor
  deviation, not merely a stationary or pure-time deviation.
- Pure-time reduction is exact only because the particular behavioral
  strategy has a countable stopping-law mixture on `Option Nat`.
- Never mass is retained explicitly as the `none` atom.
- The selected finite time can escape to infinity as the survivor profile
  varies.  No bounded-deadline conclusion follows.
- No compact limit or subsequence is used.  If a sequence of survivor
  profiles is later chosen, finiteness of `B` permits a subsequence with one
  fixed deleted owner, but gives no bounded time and no compatible
  chronology.

## 5. Boundary tests and corrections

### Strict survivor error

The proof requires `epsilon < gamma`.  At `epsilon=gamma`, the survivor Nash
bound and ambient gap can be equal, so the contradiction no longer follows.
The note should say that localization is **not proved** at equality.  It
should not say that localization actually fails there unless an honest
positive-gap table realizing equality is supplied; no such table is known.

### Positive gap

`gamma>0` is essential for excluding the Never atom.  With `gamma=0`, take a
one-player table whose finite Quit reward is `-1` and prescribe Never.  Never
attains gain zero, while no finite quit time does.  Thus exact finite-time
extraction at a zero threshold is false.

### No uniform deadline

The selected `t` cannot be bounded from the reward table and gap alone by the
argument.  Even at one quiet-lift profile, an opponent can be prescribed to
quit at an arbitrarily late deterministic date, making the only profitable
simultaneous join occur at that date.  Any deadline bound needs additional
clock tightness.

### Empty and full blocks

The localization theorem itself proves inconsistency when `B` is empty and
an `epsilon<gamma` survivor Nash profile is supplied.  The cardinal-minimal
producer excludes `B=empty` because there is no deleted output and excludes
`B=univ` because its smaller-game theorem is stated for nonempty player
types.  These are type/producer boundaries, not probability defects.

### No common owner or support kernel

For `B.card>1`, the selected owner may depend on the survivor profile.  A
finite pigeonhole argument can stabilize it only after a sequence and a
subsequence are already supplied.  The stopping times may still escape.
The checked cyclic essentiality regression correctly prevents inferring a
small common support kernel from these local selectors.

## 6. Freshness and current-source comparison

The following parts are checked already:

- cardinal-minimal production of uniform payoffs below `n`;
- exact deletion and deviation naturality;
- the ambient terminal-gap predicate;
- the behavioral stopping-law disintegration; and
- the terminal approximate profile selected from a uniform payoff.

A narrow current-tree search found no named general theorem returning the
same deleted player together with a positive-mass finite deterministic time
at the full weak gap.  That extraction and the block-hitting formulation are
the fresh ordinary-mathematics content.

The Fin4 packet
`formalized/FIN4_DELETION_NEAR_CAP_COLLISION_PRODUCER.md` already uses the
quiet-lift idea and adds the substantive consumer absent here: under a small
solo premium it selects a near-cap finite time, a probability-weighted
nonsingleton collision, and a tail-escape/endpoint-gain dispatch.  The exact
full-gap time of the present theorem does not replace that near-cap selection,
because it need not reduce the deleted player's remaining debt.  Thus this
general note is neither a duplicate of that Fin4 producer nor a stronger
consumer.

## 7. Lean handoff

The narrow generic declaration should combine Propositions 1 and 2 rather
than expose the intermediate arbitrary deviation as the public endpoint:

```text
exists_mem_block_finitePureTime_fullGap_of_liftDeletedProfile_isENash
```

Inputs:

```text
hexploit : HasTerminalExploitabilityGap reward gamma
hgamma   : 0 < gamma
hnash    : IsEpsilonAsymptoticNash deletedReward epsilon sigma
hepsilon : epsilon < gamma
```

Output:

```text
exists d, d in B and exists t : Nat,
  terminalPayoff (Lift_B sigma) d + gamma <=
    terminalPayoff (update (Lift_B sigma) d (QuitExactlyAt t)) d.
```

A stronger internal lemma may retain `tau` and
`stoppingLaw tau (some t) != 0`.  The proof should first localize `tau`, then
apply a generic PMF lemma:

```text
expect_ge_const_add_pos_of_none_eq
  -> exists finite support atom with value at least the threshold.
```

Cardinal-minimal corollaries should be separate:

```text
MinimalFinQuittingCounterexample.exists_blockOperationalFiniteGap
MinimalFinQuittingCounterexample.ownerOperationalFiniteGap
MinimalFinQuittingCounterexample.exists_mem_block_max_solo_joinPressure_ge
```

The last declaration should use the existing `insertMin 0` and `insertMax 0`
block quantities rather than introduce partial minima.

## 8. Exact export condition

Reconsider export only after one of the following is proved:

1. the block-hitting inequalities force a bounded operational support kernel
   or an upper bound on minimal counterexample cardinality;
2. a survivor uniform payoff plus this finite witness compiles to an ambient
   uniform payoff, contradiction, or renewable rank; or
3. the sharp deletion cap closes a named live deletion branch.

Without such a consumer, the result is a correct and worthwhile Research
normal form, not a completed conjecture-facing reduction.
