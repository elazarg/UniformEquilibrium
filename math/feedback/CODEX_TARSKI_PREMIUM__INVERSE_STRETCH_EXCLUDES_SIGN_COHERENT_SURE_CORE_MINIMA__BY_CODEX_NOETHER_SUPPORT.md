# Independent review: inverse stretch and sign-coherent sure-core minima

Reviewer: CODEX_NOETHER_SUPPORT.

Verdict: PASS for the stated ordinary-mathematics branch theorem and its
three-sure corollary. No unresolved mathematical objection or required
repair. This is not Lean validation or closure of all mixed sure-core cases.

Reviewed source:
[TARSKI's complete note](../notes/CODEX_TARSKI_PREMIUM__INVERSE_STRETCH_EXCLUDES_SIGN_COHERENT_SURE_CORE_MINIMA.md).
Author-confirmed frozen SHA256:
`dfec6e33e1bfcc80cfaf4699a0cfd42ac2a2b3ac694d646caddd8b897e077cdc`.
All 276 lines were read through EOF. I reconstructed the inverse comparison
and vertex argument before reading the manuscript; I have not used another
reviewer's conclusions. The shorter strict-half argument is my independent
contribution, now included and checked in these exact author bytes.

## 1. Exact claim accepted

There are four players, arbitrary signed rewards in [−1,1], and zero Never
payoff. All profiles are independent actual stopping laws and all unilateral
behavioral responses enter the cap. The source retains an original full-cube
worst table r* with positive value Ω, a fixed positive common membership
stretch α, and a final table r having exactly its 56 stretched non-own-
singleton coordinates. The four own singletons may have been reselected.
The final all-profile value is m>0 with m≤Ω.

An actual UNPADDED date-zero product root q, followed by Never, has at least
two sure quitters and E_r(q)=m. For each owner there is one source-best binary
action whose directed membership gap is nonnegative at EVERY supported
opponent configuration. Under these hypotheses the note constructs an
actual supported pure root with full regret zero at BOTH r and r*. Thus
this branch cannot occur in the retained source.

The condition is pointwise, includes each owner's counterfactual action,
and is not just the nonnegativity of an averaged best-response gap. For a
two-sure root it applies to all four owners, including the two optional
owners. For a genuinely mixed three-sure root the optional owner's condition
is automatic, leaving three core-owner conditions. Its failure forces a
strict sign reversal for some sure owner's Continue-minus-Quit gap across
the two optional actions. This does not consume the sign-reversing branch.

## 2. Independent reconstruction of the full-response argument

At every unilateral intervention against q, a different sure quitter remains
at date zero. Hence the complete cap is precisely the maximum of the two
root membership endpoints. Every later finite date and Never have the same
Continue payoff, and there is no earlier response. Both endpoints avoid the
deviator's own-singleton coordinate. This simultaneously justifies the old
and new table comparison and the eventual pure-root conclusion.

The global singleton moat gives B_i−s_i≥m. Since every debt is at most m,
U_i≥s_i. The manuscript's included all-player-tie proof is complete: if
d_k<m, prepend a private solo hazard h of player k and shift the whole old
profile. The exact complete debts are

    d'_k=d_k+h(U_k−s_k),
    d'_j=max((1−h)(s_j−U_j)+h[r_j({k,j})−r_j({k})],
             (1−h)d_j),                         j≠k.

The owner's cap remains B_k. The nonowner cap has precisely the new initial
Quit branch and the old complete-response branch, including Never. With
0<h<min(1,(m−d_k)/2,m/2), all displayed branches are strictly below m.
This is an actual independent-law competitor and proves all four debts
equal m. It does not presume cap attainment. Applying the moat to an actual
global minimum is legitimate: the actual semantic pair is in the carrier,
and its lower bound extends to the closure by continuity of maximum debt.

The strict-half argument also checks independently. At a unit-cube minimum,
s_i≤B_i−m≤1−m. The actual all-Never regret is a=max_i(s_i)_+≥m. If a=m>0,
that profile is another actual global minimum, but a maximizing positive
singleton owner has B_i=s_i there, violating its moat. Consequently
m<a≤1−m and m<1/2. Neither an additional multiplier nor the source's harmonic
contact is needed.

For a nonnegative old directed gap c, stretching gives T(c)=0 at c=0 and
T(c)=(1−α)c+2α for c>0. On [0,2], T(c)≥c, with equality exactly at 0 and 2.
Let β_i be the probability that owner i uses its non-best action. The
pointwise hypothesis makes the selected action best at BOTH tables, so
independence gives

    d_i(r*,q)=β_i E[c_i],
    d_i(r,q)=β_i E[T(c_i)]=m.

All-player ties imply β_i>0. The decisive genuinely global comparison is

    Ω=η(r*)≤E_(r*)(q)≤m≤Ω.

Thus q is also an actual old-table global minimum. Applying all-player ties
there, not merely equality of the two MAX values, gives equality in every
coordinate. Nonnegative stretch losses and positive support weights force
each relevant directed edge to be exactly 0 or 2.

For a product-supported pure draw X, define A_i as the event that i takes
its non-best action on an edge of gap 2. Its full pure regret is exactly
2·1_(A_i), at both tables. Independence gives Pr(A_i)=m/2; hence the expected
number of losing owners is 2m<1. Some positive-weight vertex has no losing
owner. Selecting that vertex is an actual pure profile, not correlated
play of a proof mixture. The unchanged two-sure core screens all responses
there, proving zero full regret and the contradiction.

## 3. Attempts to falsify the sensitive steps

1. **Replace pointwise coherence by an averaged best reply.** This fails.
   Equally weighted old directed gaps 1 and −1/2 average to 1/4, but their
   stretched average is (1−α)/4. Undoing the stretch then INCREASES the
   averaged debt. This is an exact local algebra test, not an alleged
   global-source counterexample. The manuscript excludes it correctly.

2. **Treat every positive edge as strictly enlarged.** This fails at gap 2.
   Equal pairs also require their separate zero rule. Exact rational checks
   at α=1/4 and c∈{0,1/4,…,2} confirm the two equality cases; the proof keeps
   both. The strict positive α hypothesis is essential for saturation.

3. **Use only m≤1/2 in the vertex count.** Insufficient even for coherent
   unit-cube endpoint data. Take two sure owners and two fair optional bits.
   Let the two core owners lose on optional states 00 and 11, respectively;
   let optional owner 2 lose on 01 and optional owner 3 on 10. Assign each
   listed directed gap 2, all other relevant gaps 0, and take Quit as the
   optional owners' best action. These data are compatible with disjoint
   owner membership pairs in a unit-cube table. Every owner's expected debt
   is 1/2, while every supported vertex has exactly one loser. This is only
   a local/contact pattern, not a positive global minimum. It confirms that
   the separately proved strict-half bound genuinely does work.

4. **Change the four singleton values during the old-table comparison.**
   Harmless at the stated unpadded root because another sure opponent
   absorbs every intervention. It is not harmless for a one-sure root or
   an unexamined silently padded old-table comparison. The manuscript makes
   this distinction explicitly and uses the strict-margin unpadded source.

5. **Infer a pure competitor from an arbitrary correlated intervention.**
   No such step occurs. The product draw is only a counting device, and one
   supported vertex is subsequently selected as the actual profile.
   Likewise the proof neither identifies an old multiplier with a new one
   nor imports the discarded 56-coordinate reward normal.

No attempted falsification survives the exact hypotheses.

## 4. Named-source check and incremental value

I inspected the declarations and their hypotheses in the following files:

- `minimumTerminalSemantic_exploitabilitySingletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`:
  a positive global MAX carrier minimum gives E≤B_i−s_i. It is not by itself
  the all-player-tie theorem. The manuscript proves that extra conclusion.
- `exists_twoSureProductRoot_realizing_jointCarrierPoint_of_strictMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/ZeroSingletonBehavioralLawProductBase.lean`:
  zero Never and zero singleton masses together with strict margins give
  one unpadded two-sure product root realizing the complete semantic pair
  and outcome law. The neighboring nonstrict result instead uses padding.
- `quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card`
  in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`: the full pure
  semantic pair with at least two quitters is tail-independent and its cap
  is the maximum of the insert and erase rewards.

I also checked the complete solo-prefix proof in HILBERT's
`GLOBAL_MAXIMUM_MINIMUM_ALL_PLAYER_TIES` note and the exact construction in
the reviewed `MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION`
packet. The present final proof includes the relevant all-player-tie
argument, rather than depending on an unreviewed declaration of that claim.

A bounded phrase search for inverse stretch, sign-coherent sure cores, and
the losing-event count found no prior instance of this consumer in the
inspected conference corpus. This is not an exhaustive priority claim.
Its substantive addition is a use of the retained ORIGINAL worst table to
consume a genuine branch of the new source reduction. The source's strict
pure-coalition margin is not needed again once the pure exact competitor
is obtained. No new UE existence class, all-root completeness theorem,
normal-core theorem, or full Fin4 conclusion follows.

## 5. Exact-byte acceptance and remaining boundary

The author-confirmed 276-line SHA256 recorded at the top is accepted in
full, including the revised all-player-tie proof, strict-half proof, and
explicit zero-regret conclusion at both tables. No candidate file was
edited by this reviewer. This is mathematical review by source inspection;
no Lean build or new formalization was performed.

The concrete remaining branch is a source-best membership direction that
reverses sign across supported optional actions. Turning those reversals
into a complete independent-law improvement requires further mathematics;
it is not supplied by this accepted proof.

## 6. Final named packet: exact-byte acceptance

I independently read all 465 lines of the author-confirmed final packet
[Inverse membership stretch forces sure-core sign reversal](../formalized/INVERSE_MEMBERSHIP_STRETCH_SURE_CORE_SIGN_REVERSAL.md),
SHA256
`70d9ea22fd61290b1f24fbccdb0df57980a66518e87b7322a61efba810ad5aa7`.
Verdict: PASS, with no mathematical repair requested. The original frozen
source hash above remains unchanged and accepted separately.

The final packet preserves the reviewed argument and its exact source
tradeoff. Its explicit final-table definition of the best action and its
convex-combination wording for randomized full responses are correct.
The three-sure corollary still needs only three core coherences; the
two-sure statement retains all four. The carrier adapter uses the named
STRICT-margin unpadded realization and transports the entire semantic
pair, not just payoff or outcome mass. No multiplier transport is claimed.

I checked the added complete-table fixture convention and both finite
counts. In the successful fixture all four losing events are optional
state 00, of probability 1/8, giving debts 1/4. In the critical-half fixture
the four displayed losing events partition the four equally likely
optional states, giving debts 1/2 and no winning vertex. Both are honestly
marked as non-global local tests because all own singletons are zero.
The signed-gap example has stretched mean 1/2−9α/10 as stated. The added
one-row padding example correctly distinguishes full-cap change from the
unaffected unpadded comparison.

The source correspondence, ordinary-mathematics status, all-behavior scope,
and narrow prospective Lean handoff are correctly retained. No candidate
or export file was edited by this reviewer, and no Lean validation is
asserted. The mathematical objection list remains empty.
