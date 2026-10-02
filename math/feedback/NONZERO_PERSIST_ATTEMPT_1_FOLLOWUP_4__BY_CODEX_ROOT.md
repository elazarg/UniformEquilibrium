# Review of `NONZERO_PERSIST_ATTEMPT_1`, Followup 4

**Reviewer:** `CODEX_ROOT`  
**Status:** central two-cut claim not established; two independent lemmas survive

## Claim reviewed

The followup claims that, on the normalized-return equality arm, replaying an
actualized profile behind its own pure pair row produces the uniformly reached
post-mark two-cut block requested in
`questions/FIN4_POST_MARK_TWO_CUT_RENEWABLE_CHILD_SOURCE.md`.  It then derives a
paid best-response/support handoff and a minimum on a zero-debt face with unique
all-Continue exact cap root.

I inspected the requested question, the statement and proof of
`exports/POSITIVE_MINIMUM_TWO_CUT_COERCIVITY_AND_PAID_SPLICE.md`, the cross-tail
definitions in
`UniformEquilibrium/Quitting/Root/SelfTailClosure.lean`, and the actualizer
interfaces in `Research/Quitting/NormalizedPassportMinimumReturn.lean` and
`Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean`.

## 1. The pure-nonsingleton shield is correct

If the current root is the pure coalition `S` with `|S| >= 2`, every unilateral
replacement still leaves at least one sure quitter at that row.  The
continuation is therefore invisible to:

- the prescribed terminal payoff;
- every player's complete behavioral best-response cap; and
- the prescribed terminal law.

Consequently a common earlier root word followed by that pure row also erases
all dependence on the later tail.  The proposed cross-tail semantic/law
equality is a valid and useful standalone lemma.  It is stronger than the
currently named live-root and post-date-spine equalities in
`SelfTailClosure.lean`.

## 2. The replay does not produce the required paid two-cut

Let the outer parent be

\[
  \pi_n=A_n\triangleright q^S\triangleright\sigma_n,
\]

where `q^S` is the pure pair root.  The followup places the proposed block
inside the restarted copy of `sigma_n`.  The actual probability, from the
parent, of reaching any row strictly after the outer `q^S` is zero.  Thus the
parent reach factor `R` in the reviewed paid-splice theorem is zero.  Any
replacement confined to the replayed tail has zero parent payoff gain and zero
parent debt decrease.

Calling the restarted profile a separate "post-mark port" does not repair this.
The two-cut theorem's splice conclusion multiplies the suffix gain by the
actual reach from the parent.  The question also explicitly asks for parent
reach bounded below and lists use of the positive marked row before the
post-mark continuation as a nonanswer.  The followup itself concedes that
absolute reach past the outer pair is zero.

There is a second indexing mismatch.  With cuts `entryCut=m_n` and
`exitCut=m_n+1` inside the restarted `sigma_n`, the initial pair in the
two-cut debt identity is

\[
  \operatorname{Sem}(\operatorname{Spine}(\sigma_n,m_n)),
\]

not `Sem(sigma_n)`.  The actualizer gives convergence of the whole-profile debt
and the post-`m_n` tail debt, but the followup proves only the global lower bound

\[
  D(\operatorname{Spine}(\sigma_n,m_n))\ge D_*.
\]

It does not prove that this entry suffix is near the minimum.  Equations (22)
and (23) therefore do not verify the start endpoint required by the claimed
one-row application.

One can instead take cuts `0` and `m_n+1` in `sigma_n`; then the endpoint debt
and hazard conditions are plausible.  But the replacement begins before the
retained mark and does not provide the requested post-mark, atom-preserving
splice.  Placing that block behind the outer shield again makes its parent
reach zero.  This is exactly the tradeoff the original question records.

Hence implication (24)/(51) is not proved, and the followup does not answer the
post-mark two-cut producer question.

## 3. The best-response handoff is separate from the replay

At the original reached pure pair row, total debt of its suffix is the sum of
the four endpoint defects.  Global positive minimum debt therefore selects a
player with endpoint defect at least `D_*/4`; the reached mass floor turns this
into a fixed whole-profile unilateral gain.  Replacing that player by an
approximately optimal complete response makes its own debt tend to zero.

This is a valid paid-row-to-response reduction.  It uses the original actual
profiles directly and does not depend on self-tail replay or the two-cut
theorem.  The same-minimum half-mixture/support argument is the existing
canonical support-handoff mechanism and still needs its usual coherence and
renewability hypotheses.  It should not be presented as a consequence of the
new two-cut construction.

## 4. The zero-debt-face minimizer lemma is correct

Let `F_p={z:d_p(z)=0}` inside the compact semantic carrier, and let `Z_p`
minimize total debt on that face.  For an exact cap-Nash root `x`, the exact
prefix decomposition gives

\[
 d_i(T_xZ_p)=c(x)d_i(Z_p).
\]

Thus `T_xZ_p` remains in `F_p` and has total debt `c(x)D(Z_p)`.  Since
`D(Z_p)>=D_*>0`, face minimality forces `c(x)=1`, hence `x` is all-Continue.
One-stage Nash existence then makes all-Continue the unique exact root at that
cap.  The same proof works for any closed face obtained by forcing a fixed set
of debt coordinates to zero.

This is a clean reusable relative-plateau theorem.  It does not consume the
plateau: inserting arbitrary actual tails behind the pure pair preserves the
outer source precisely because those tails are behaviorally unreachable.  A
new theorem is still needed to turn the relative minimizer into an executable
return, a renewable rank decrease, or a terminal consumer.

## Verdict

Retain and separately review/formalize:

1. pure-nonsingleton cross-tail semantic/law shielding; and
2. unique all-Continue exact roots at a positive minimum on a zero-debt face.

Do not claim that the self-replay supplies
`HasUniformlyReachedPostMarkTwoCutBlock` or closes the post-mark producer.  The
proposed block is either behind a sure-absorption row and has zero parent reach,
or is moved before that shield and loses the requested post-mark provenance.
