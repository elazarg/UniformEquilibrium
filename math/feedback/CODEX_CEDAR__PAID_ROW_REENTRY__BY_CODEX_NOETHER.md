# Review of bounded-loop exactification and the charged receiving root

Reviewer: `CODEX_NOETHER`
Note reviewed: `notes/CODEX_CEDAR__PAID_ROW_REENTRY.md`
Verdict: the abstract bounded-length exactification lemma, its quitting-game
specialization as a sufficient compact-limit criterion, and the claimed
tail-independence of the earlier-receiving outsider defect are mathematically
valid. I found no counterexample. This does not review or supply the missing
bounded detour from the actual frontier data.

## Claims checked

I checked three substantive claims:

1. uniformly bounded approximate closed walks in a compact metric space with a
   closed edge relation exactify to a finite exact closed walk;
2. the displayed approximate Bellman/Nash/floor conditions are enough to apply
   that argument to the punishment-floor admissible relation; and
3. when the observer Quits surely at the receiving root, the outsider's
   one-stage gain is independent of the chosen continuation payoff.

The exact declarations inspected for the specialization were
`QuittingPunishmentFloorAdmissibleState`,
`QuittingPunishmentFloorAdmissibleEdge`, and
`quittingPunishmentFloorAdmissibleChargedRelation`
(`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`),
and `QuittingPositiveAdmissibleReturn`
(`UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean`).

## Verification

### 1. Bounded-length compact exactification

Passing to a constant return length is legitimate because only the finitely
many values `0,…,K` occur. For that fixed length, compactness of the finite
product gives simultaneous convergence of every vertex. The exact identity
`z_(n,0)=b_n` passes to `z_0=b`, while the vanishing closing error gives
`z_l=a`.

For any convergent edge candidates `e_n→e`, `dist(e_n,R)→0` and closedness of
`R` imply `e∈R`: choose points of `R` within twice the displayed distance (or
use continuity of distance to a closed set), then take the limit. Applying
this to the primary edge and every return edge yields the correctly oriented
walk

`a R b=z_0 R z_1 R … R z_l=a`.

Continuity of `q` preserves `q(a,b)≥delta`. The `l=0` case is also correct:
the closing error forces `a=b`, so the primary edge is a positive self-loop.

### 2. Quitting specialization and orientation

The charged relation has

- source `edge.tail`,
- target `edge.current`, and
- charge equal to the current root's literal absorption mass.

Thus the abstract naming `a=tail`, `b=current`, followed by a return from
`current` to `tail`, matches `QuittingPositiveAdmissibleReturn` exactly.

The floor-admissible state space is a closed subtype of the compact canonical
box: the extra conditions are finitely many weak coordinate inequalities.
For a convergent sequence of the displayed approximate edges,

- the sup-norm Bellman residual tending to zero gives exact Bellman equality;
- the finite family of endpoint-Nash inequalities with error tending to zero
  gives zero-error endpoint Nash;
- the box and floor inequalities survive the limit; and
- continuity of absorption mass preserves the positive primary charge floor.

Therefore one may prove the specialization directly by taking a convergent
subsequence and passing each residual to the limit. The note need not separately
prove that its chosen residual maximum is quantitatively equivalent to metric
distance from the exact edge graph; the direct limit proof already supplies
the abstract lemma's conclusion.

### 3. Earlier-receiving outsider gain does not depend on the tail

At the receiving date the observer's action law is pure Quit. Hence the joint
all-Continue probability is zero. It remains zero after changing only the
outsider's action. In `quittingRootExpectedPayoff_eq_absorbingContribution_add`,
the continuation term is multiplied by this joint all-Continue mass on both
sides, so both continuation terms vanish. The outsider's gain is therefore a
difference of current absorbing contributions alone and is independent of the
continuation payoff vector. The note's conclusion that changing only the tail
cannot repair a fixed outsider defect is valid.

## Boundary and minor formulation checks

- The quantitative residual alternative is the compact contrapositive of the
  exactification lemma. If for some length the compact tuple class is empty,
  that length is simply omitted. If every class is empty, any positive `rho`
  works; this is a harmless degenerate case worth remembering in a formal
  statement.
- The irrational-circle example correctly shows that approximate recurrence
  with unbounded return length does not exactify to a finite cycle.
- The two orientation tables test only the paid-row interface, as the note
  says. They do not refute a producer using the full frontier and terminal
  witness.
- No fixed target, source-data detour, or all-behavior theorem is produced by
  the compact lemma alone.

## Remaining question

The useful next obligation remains exactly the one stated by the author:
derive from the actual paid frontier a primary positive-charge approximate
edge and a return detour with one rank-independent length bound. Without that
bound, the circle example prevents the proposed compactness step.

## Follow-up review: Section 11 no-small-correction and nonlocal datum

Verdict on the new Section 11: `VALID`. The constants are conservative but
correct, the orientation dispatches give the stated fixed lower bounds, and
the continuous-selection packet really produces a positive floor-admissible
self-loop. It remains a sufficient hypothesis, not data produced by the paid
row.

### Coupling modulus and constants

Couple each Bernoulli coordinate under roots `p,q` by the standard maximal
coupling and take the product coupling. The probability of any coordinate
mismatch is at most

`sum_i |p_i-q_i|=d_1(p,q)`.

For an outcome function in `[-M,M]`, the expectation difference is therefore
at most `2M d_1`. An endpoint regret is one pure-updated expectation minus one
prescribed-root expectation. Applying the same estimate to both terms gives
the stated `4M d_1` modulus. Updating one coordinate to a common pure action
only removes a possible mismatch, so no extra factor is missing.

In the earlier-receiving branch,
`QuittingPaidFirstDisagreementRow.exists_outsiderDeviation_of_receivingEarlier`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreementOrientation.lean`)
gives

`gamma*g/(2M) <= L*D`.

Here `0<L<=1`, so the raw reached outsider gain satisfies
`D>=theta=gamma*g/(2M)`. The sure-Quit observer makes both the prescribed root
and the outsider-updated root absorb immediately, hence this gain is
independent of every tail vector. Comparing it at a literal root `q_n` with
the same action's nonpositive gain at an exact endpoint-Nash root `p` gives

`theta<=4M d_1(p,q_n)`.

Thus the lower bound `theta/(4M)` is correct. Its use presupposes the theorem's
stated positive `gamma,g` and small-`eta` hypothesis; Section 11 does not erase
those source hypotheses.

In the later-receiving branch, the paid identity gives reached gain
`R>=g/L>=g`. At the literal deleted-clock tail, pure Continue beats the
observer's prescribed pure Quit by `R`. Changing the root changes the two
expectations by at most `4M d_1`; changing the tail can change the pure-
Continue and prescribed expectations by at most one tail sup-norm each. Hence

`g<=4M d_1(p,q_n)+2||v-x_n||_infinity`

is valid. The factor `2` is conservative when one of the two actions is pure
Quit, but harmless.

### Brouwer packet and existing consumer

Let `K` be a nonempty compact convex subset of the boxed punishment-floor
region and `N(v)` a continuous exact endpoint-Nash root selection with charge
at least `c>0` and successor in `K`. The successor map is continuous and is a
self-map of `K`, so finite-dimensional Brouwer supplies `v*` with

`v*=quittingRootSuccessorPayoff(reward,v*,N(v*))`.

Use the same root coordinate for the current and tail boxed states. The fixed
identity and exact endpoint Nash give an
`IsQuittingNashBellmanEdge`; membership in `K` supplies both floor and box
certificates; and the charge is positive. The nil path from this state to
itself is exactly the return path required by
`quittingGame_exists_uniformPayoff_of_positive_admissible_return`
(`UniformEquilibrium/Quitting/Bellman/Finite/PositiveAdmissibleCycle.lean`).
That checked theorem concludes existence of a uniform-equilibrium payoff.
There is no missing terminal-Nash or unrestricted-deviation premise in this
use of the consumer.

### Test against the `(x,delta)` finite-deadline optimizer

Proposition 9 of `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md` provides
an exact stress test. For

- `r({k})=(1,-1)`;
- `r({j})=(2,-1)`; and
- `r({k,j})=(0,0)`,

the hard-zero-tail backward orbit has unique Nash roots, values

`x_n=(1-1/(2^(n+1)-1), -1+1/(n+1))`,

and root absorption tending to zero. Therefore no continuous exact-Nash
selection on a compact set containing that entire orbit and its limit can
have a uniform positive charge: uniqueness forces the selected roots to
converge to all-Continue. The signed-deficit coordinate records the associated
nonvanishing late debt, but it cannot repair the missing charge.

This does not refute Cedar's packet, because the hard-tail orbit lies below
the punishment floor in the `k` coordinate. In fact the same table gives an
exact positive model of the packet after the nonlocal limit transition. Its
punishment values are `(1,-1)`: the upper bounds follow from all-Continue for
`j` when punishing `k` and from increasingly diffuse finite quit times for `k`
when punishing `j`; the reverse bounds follow from the elementary best-reply
timing alternatives. Put

`K={ (u,-1) : 1<=u<=2 }`

and fix any `c in (0,1]`. Select the root at which `k` Continues surely and
`j` Quits with probability `c`. For every `u in [1,2]`, `k` weakly prefers
Continue and `j` is indifferent, so this is exact endpoint Nash. Its successor
is

`T(u,-1)=(u+c(2-u),-1)`,

which remains in `K`, and its absorption charge is `c`. Brouwer's fixed point
is `(2,-1)`. Thus the packet is not only formally sufficient; it performs the
kind of nonperturbative branch change which the hard-deadline optimizer cannot
make at any finite stage.

The conclusion for the paid-row project is sharp: `(x,delta)` can diagnose why
a local or continuous correction along a vanishing-charge orbit fails, and in
special tables it can suggest a new floor-invariant carrier after taking a
limit. It does not produce, from the paid row alone, either the compact convex
region `K` or a uniformly charged continuous Nash selection on it.

## Second follow-up: universal floor reduction and tight-collision chronology

I refreshed the note and independently checked Sections 19--22. Verdict:
`VALID` ordinary mathematics, with one scope wording point below. These
sections genuinely sharpen the universal obstruction: they start from a
terminal exploitability gap and the actual punishment vector, not from the
earlier paid-like regression.

### Section 19

At the punishment tail `P`, ordinary finite-game Nash gives a product root and
`quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge`
(`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorForward.lean`)
keeps its successor above the floor. Zero absorption is exactly all-Continue,
so endpoint Nash gives `s_i<=P_i`.

Applying `HasTerminalExploitabilityGap` to the literal all-Continue behavioral
profile is legitimate against unrestricted behavioral deviations: with all
opponents silent, the deviator receives only its singleton reward or zero.
Thus some `o` has `gamma<=s_o`. The checked
`quittingPunishmentValue_le_max_solo`
(`UniformEquilibrium/Quitting/Stationary/MinMax.lean`) gives
`P_o<=max(s_o,0)=s_o`, hence `P_o=s_o>=gamma`. The certification arm of
`soloCertification_or_universalJoining`, followed by
`isUniformEquilibriumPayoff_soloReward_of_inactive`
(`UniformEquilibrium/Quitting/Punishment/OwnerSoloCertification.lean`), would
contradict the positive terminal gap. The universal-joining conclusion and
all its rate quantifiers are therefore correct.

### Section 20

For a tight owner `o`, the displayed outsider gap

`J_(o,j)(p)=(1-p)(s_j-P_j)+p(r({o,j})_j-r({o})_j)`

is exact. If no tight outsider has positive collision increment, every tight
outsider is inactive at every rate, while each slack outsider is inactive for
all sufficiently small rates. Finiteness gives one common positive rate, a
positive endpoint-Nash solo row, and the required contradiction. Therefore
the strict successor relation on the finite nonempty tight set exists, has no
self-edge, and contains a directed cycle with a positive minimum increment
`kappa`.

The quantitative `eta*kappa` lower bound is valid for the **solo-owner row**
used in the derivation, with every outsider continuing. If the phrase “any
approximate endpoint-Nash realization” were read as allowing arbitrary other
positive quitter marginals, the factorization need not persist. The local
context makes the intended solo-root scope clear, but it should remain
explicit in any export statement.

### Sections 21--22

The chronology identities check exactly. For a singleton `o` phase with tail
`t` and current `u`, punishment tightness of `j` turns its endpoint inequality
into

`(1-p)(t_j-P_j)>=p(r({o,j})_j-r({o})_j)`.

If `j` owns the following positive phase, active equality pins `t_j=P_j` and
a strict collision edge is impossible. If `j` owns the preceding phase,
`u_j=P_j` forces

`t_j-P_j=p(P_j-r({o})_j)/(1-p)`,

and substitution is feasible exactly when `r({o,j})_j<=P_j`. For a strong
edge, the pure-Quit lower bound gives the stated current excess
`u_j-P_j>=p(r({o,j})_j-P_j)`.

Finally `Delta=A+C` and `Delta>=kappa` imply
`max(A,C)>=kappa/2`; the preemption/strong-forcing two-coloring is exact.
As the note correctly stresses, this is a labelled support cycle, not yet a
payoff-state return or an unrestricted-deviation producer.

### Relation to my current route

Propositions 27--31 of
`notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md` independently start from
the entire selected punishment-floor predecessor orbit. Their signed
paid-window defect is the missing chronological normalization for precisely
the labelled forcing identified here. Neither argument subsumes the other:
the Cedar reduction supplies terminal-gap collision labels, while the Noether
reduction says exactly what source-matched normalized seam must vanish to feed
the checked divergent-path consumer.
