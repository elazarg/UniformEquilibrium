# Review of signed-influence block gadget no-go

Reviewer: `CODEX_EULER`

## Claim reviewed

I reviewed `notes/CODEX_RAMSEY__SIGNED_INFLUENCE_BLOCK_GADGET_NOGO.md`
against `questions/INCENTIVE_GADGET.md`, the exact sure-exit declarations in
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`, the supplied-potential
consumer in `Quitting/Stationary/TogglePotential.lean`, and every item of
`exports/README.md`.

The theorem concerns every finite reward table whose ordered membership
influences have one fixed weak sign (with a strict witness when nonzero) and
whose every directed influence cycle has positive sign product.  It claims
that such a table has a pure sure-exit coalition and therefore an ordinary
uniform-equilibrium payoff against unrestricted behavioral deviations.

## Verdict

**MATHEMATICAL PASS.**  The SCC sign switch, blockwise monotone construction,
condensation induction, and exact sure-exit handoff are valid.  This is a
genuine negative answer for the precisely defined universal gadget
architecture accepted by `INCENTIVE_GADGET.md`: one exact equilibrium in the
class has at least one of the two strict-first target-pair masses equal to
zero, so the class cannot force both masses uniformly positive at every small
terminal Nash error.

Before an export packet is assembled, I recommend one bounded proof-writing
repair: expand the transformed-gain identity (6) with an explicit background
coalition, as described below.  This is not a mathematical gap, but it removes
the only place where an action reversal is currently hidden inside the phrase
"corresponding original background."  In addition, the universal
unrestricted-class gate in `exports/README.md` requires a second independent
review and explicit falsification attempt.  This review is one such attempt,
not the second one.

## SCC sign-switch audit

Fix a strongly connected component `K` and a root `r`.  If `epsilon_i` is the
sign product on one directed path from `r` to `i`, it is path independent.
Indeed, append one fixed directed return path from `i` to `r` to either of two
forward paths.  Each resulting closed directed walk decomposes into directed
simple cycles, all with positive product.  Cancelling the common return-path
product gives equality of the forward products.  Appending an internal edge
`j->i` of sign `sigma` then gives

```text
epsilon_i=epsilon_j*sigma,
epsilon_i*epsilon_j*sigma=1.
```

No symmetry of the influence graph is used.

For the transformed action calculation, let `T` omit transformed players
`i,j`, let `tau(T)=T symmetric_difference P_K`, and define the original
background for player `i` by

```text
B_i(T)=tau(T) erase {i}.
```

Then the transformed own-action gain is

```text
h_i(T)=epsilon_i*g_i(B_i(T)).
```

There are two cases for `j`:

```text
epsilon_j=+1:
  B_i(T+j)=B_i(T)+j,
  h_i(T+j)-h_i(T)=epsilon_i*d_(j->i)(B_i(T));

epsilon_j=-1:
  B_i(T)=B_i(T+j)+j,
  h_i(T+j)-h_i(T)=-epsilon_i*d_(j->i)(B_i(T+j)).
```

Both are exactly

```text
epsilon_i*epsilon_j*d_(j->i)(S)
```

at the indicated background `S`, which contains neither `i` nor `j`.
Absent influence makes this zero; a nonabsent internal edge and the switching
identity make it nonnegative.  Thus every block is genuinely a finite
strategic-complements game after its own action switch.  This verifies the
sign and orientation in (6).

## Block and condensation audit

Starting from transformed zero and adding any absent player with strictly
positive current gain terminates in at most `|K|` steps.  Every player still
absent has gain at most zero.  If a player was added, its gain at the
background just before addition was positive; later additions weakly increase
that gain, so at the terminal set its reverse leave gain is strictly negative.
Hence the final block action is a pure Nash action against the fixed outside
background.

Order the SCC condensation so every intercomponent edge points forward.  A
later component has no edge into an earlier one.  Sign consistency makes
absence of that edge exact invariance of every earlier player's membership
gain under the later player's action, not merely a missing strict witness.
Therefore later block choices cannot undo any earlier block inequality.
Earlier blocks may influence a later block, but they are already fixed when
that block is solved.  The induction yields a full coalition with no
profitable one-coordinate membership toggle.

This is the strict DAG extension beyond one global polarity.  A global action
switch would require sign consistency on undirected cycles as well; the
three-edge acyclic boundary table in the note violates that stronger condition
while the SCC theorem still applies.

## Sure-exit and all-behavior handoff

At the constructed coalition `S_*`, no profitable membership toggle is
exactly

```text
w_i(S_* erase {i}) <= w_i(S_*)       for i in S_*,
w_i(S_* union {i}) <= w_i(S_*)       for i notin S_*.
```

These are precisely the member and outsider clauses of
`IsQuittingSureExitSet`, including `S_*=empty`.  The checked equivalence
`isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet` covers every
unilateral behavioral strategy, including arbitrary randomized stopping and
Never.  The checked theorem
`isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet` supplies the
uniform payoff.  No finite-watchdog completeness assumption is present.

At this exact pure profile, the first outcome is either Never or one fixed
date-zero coalition.  Two disjoint target-pair coalitions therefore cannot
both have positive strict-first mass; `min(a,b)=0`.  Since the profile has
zero terminal exploitability, the architecture cannot satisfy the producer
requirement for all sufficiently accurate terminal approximate Nash profiles.

## Boundary and scope audit

The acyclic signed triangle is a valid strict positive test: its influence
graph has no directed cycle, it has no single global polarity switch, and the
constructed coalition `{1,3}` passes all membership inequalities.

The odd negative directed cycle is a valid sharp negative test.  Member and
outsider inequalities force alternating membership

```text
i in S  iff  succ(i) notin S,
```

which is impossible on an odd cycle.  This shows that directed-cycle balance
cannot simply be dropped.  It does not claim absence of a non-pure uniform
payoff; the three-player existence theorem supplies one by another route.

The result rules out only sign-consistent tables without a negative directed
influence cycle.  It says nothing about sign-changing influences, tables with
a negative directed cycle, or the existence of the target clock law outside
the constructed pure escape.  Extra calibrators are covered only when they,
too, satisfy the same global architecture hypotheses.

## Source and export-gate conclusion

`TogglePotential.lean` consumes a supplied ordinal potential and does not
derive one or a sure-exit set from SCC-balanced signed influences.  The Gauss
note proves global complements and a single global action switch, and marks
block monotonicity as open.  The SCC/condensation theorem is therefore a real
extension rather than a restatement of those sources.

The result has the importance required by the maintained question and, after
the explicit (6) expansion, has the statement, proof, boundary tests,
actual-table adapter, checked semantic consumer, and Lean handoff required by
the export format.  It should remain internal until the mandatory second
independent unrestricted-class review is recorded and a separate uppercase
packet is audited as a whole.
