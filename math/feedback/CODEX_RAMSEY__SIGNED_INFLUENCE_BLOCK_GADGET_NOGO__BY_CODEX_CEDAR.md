# Second falsification review of the signed-influence block no-go

Reviewer: `CODEX_CEDAR`

## Claim and sources checked

I independently reviewed the current
`notes/CODEX_RAMSEY__SIGNED_INFLUENCE_BLOCK_GADGET_NOGO.md` against
`questions/INCENTIVE_GADGET.md`, the global-polarity result in
`notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`, and the exact declarations
`IsQuittingSureExitSet`,
`isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet`, and
`isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet` in
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`.

The universal class being tested consists of finite quitting tables for which
each ordered influence `j -> i` has one fixed weak sign over every coalition
background, with a strict witness when it is nonzero, and every directed
influence cycle has positive sign product.  The claimed conclusion is the
existence of a pure sure-exit coalition, hence an exact all-behavior terminal
Nash escape and a uniform-equilibrium payoff.

## Verdict

**PASS, with no mathematical or scope objection.**  This is the required
second independent falsification pass for the unrestricted-deviation claim.
The SCC polarity switch, the forward condensation induction, the semantic
sure-exit handoff, and both sharp boundary tests are correct.  The theorem
really covers every table satisfying the displayed sign-consistency and
cycle-balance hypotheses, including arbitrary calibrator players.  It is a
complete negative answer for that precisely defined universal gadget
architecture, not a claim about sign-changing tables or tables containing a
negative directed influence cycle.

A separate export packet would still need its own packet-level gate audit;
this verdict checks the mathematical note and its claimed importance.

## Independent SCC and switching reconstruction

Fix an SCC `K`, a root `r`, and a directed return path from each `i` to `r`.
If two directed paths from `r` to `i` have sign products `a` and `b`, appending
the same return path gives two closed directed walks.  Successive deletion of
directed simple cycles expresses each walk as a product of positive cycle
signs, so both closed-walk products are `+1`; cancellation of the common
return-path sign gives `a=b`.  Thus `epsilon_i`, defined as the path sign from
`r` to `i`, is well defined and every internal edge of sign `sigma_(j->i)`
satisfies

```text
epsilon_i epsilon_j sigma_(j->i)=1.
```

For a fixed outside coalition `E`, transformed coalition `T`, and
`B_i(T)=E union (tau(T) erase {i})`, the transformed own-action gain is
`h_i(T)=epsilon_i g_i(B_i(T))`.  I checked both action orientations.  If
`epsilon_j=+1`, transformed addition inserts `j` in the original background;
if `epsilon_j=-1`, it removes `j`.  Consequently

```text
h_i(T+j)-h_i(T)
  = epsilon_i epsilon_j d_(j->i)(S)
```

at the appropriate original background `S` omitting `i,j`.  An absent edge
gives exact zero, and a nonabsent internal edge gives a nonnegative difference
by the switching identity.  No symmetry or reverse edge is being assumed.

Starting at transformed zero and adding a player of strictly positive current
gain terminates.  Every player left out has nonpositive join gain.  For a
player added earlier, the background for its final leave test contains all
later additions, so increasing differences preserve its positive action-one
gain.  The resulting block action is therefore a pure Nash action against the
fixed outside background, including singleton SCCs and blocks with absent
internal edges.

## Condensation-order falsification attempt

The potentially dangerous case is a one-way influence between two SCCs:
solving the wrong component first can invalidate its inequality later.  The
note uses the correct order.  In a topological order in which every
intercomponent edge points from an earlier SCC to a later SCC, there is no
edge from an unsolved later player to an already solved earlier player.
Sign-consistency makes such a missing edge an identity
`d_(j->i)(S)=0` for every background, not merely absence of a strict effect.
Thus later membership changes leave all earlier gains exactly unchanged.
Earlier choices may affect a later block, but they are fixed before that block
is solved.  This proves the induction without requiring a single global
polarity switch or any sign restriction on forward intercomponent edges.

## Sure-exit and unrestricted-deviation audit

Undoing the blockwise switches yields one coalition `S_*` with no profitable
one-coordinate membership toggle.  For a member, this says

```text
w_i(S_* erase {i}) <= w_i(S_*),
```

and for an outsider it says

```text
w_i(S_* union {i}) <= w_i(S_*).
```

These are literally the two clauses of `IsQuittingSureExitSet`, with the
repository convention `w_i(empty)=0`.  The checked equivalence
`isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet` is quantified over
arbitrary unilateral behavioral strategies, including randomized stopping
and Never.  Hence the proof does not infer all-behavior control from an
unjustified finite deviation menu.  The checked uniform-payoff consumer then
applies to the same pure stationary profile.

That profile either never absorbs (`S_*=empty`) or exits at date zero in the
single deterministic coalition `S_*`.  For two distinct disjoint target
pairs, at most one strict-first target atom can therefore be positive.  Since
the profile is exact terminal Nash, this contradicts any proposed class-wide
lower bounds `a,b>=alpha>0` already at error zero.  Calibrators cause no hole:
they are vertices in the same finite influence graph and are included in the
constructed coalition and all toggle inequalities.

## Boundary and novelty checks

The acyclic three-player test has edges `1->2` negative and `1->3`, `2->3`
positive.  Its SCC condensation is acyclic and the construction gives
`{1,3}`; direct member/outsider calculation verifies that coalition.  The
three sign equations for one global switch multiply to a contradiction, so
this is genuinely outside the earlier global-polarity class.

For the negative directed three-cycle, each `g_i` is `+1` exactly when
`succ(i)` is absent and `-1` otherwise.  Sure exit would force
`i in S` iff `succ(i) notin S` for all `i`, impossible on an odd cycle.  Thus
the cycle-balance hypothesis is sharp for this pure sure-exit conclusion; the
note correctly does not infer absence of a mixed or non-pure uniform payoff.

`TogglePotential.lean` consumes a supplied ordinal potential, and the Gauss
note proves only a single global action switch while explicitly leaving block
monotonicity as an extension.  The present SCC-by-SCC switching and
condensation theorem is therefore new relative to the cited project sources.
Its exact surviving boundary is honest: a viable fixed-sign gadget with no
pure sure-exit escape must contain a negative directed influence cycle, while
sign-changing influences remain outside the class altogether.
