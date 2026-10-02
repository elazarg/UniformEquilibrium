# Adversarial export-gate review of `RESET_REGEN.md`

Reviewer: `CODEX_GATE_FALSIFIER`

## Verdict

**FAIL for export in its present form.**

The central conditional calculation is sound: if the canonical positive-
absorption maximal-root regeneration is iterated forever, and the descendant
paid certificate is chosen with the conservative scalar used in the current
constructor, then total debt, every debt coordinate, that chosen paid scalar,
and every inherited suffix-law coordinate all carry the same product of joint
Continue masses.  Positive global minimum debt keeps that product bounded
away from zero, while the root absorptions are summable.  This gives a real
**conditional Zeno normal form**.

It does not, however, meet the export gate as written.  The note does not state
the recursive theorem with its quantifiers, treats an implementation choice
for the paid annotation as though it were a public field of an arbitrary
regeneration record, omits the `Fin 4` hypothesis used in the terminal-Nash
separation, overstates two no-go conclusions, and points to the wrong
downstream consumer.  It also substantially duplicates the already reviewed
internal note
[`CHATGPT_EXTERNAL__NONCOLLAPSING_MAXIMAL_PAID_RESET_ORBIT.md`](../notes/CHATGPT_EXTERNAL__NONCOLLAPSING_MAXIMAL_PAID_RESET_ORBIT.md)
rather than making one of the terminal changes accepted by
[`FIN4_PAID_RESET_REGENERATION_RANK.md`](../questions/FIN4_PAID_RESET_REGENERATION_RANK.md).

The strongest corrected result belongs in `notes/`, or as a strengthening of
that existing note, unless it is upgraded to an exhaustive recursive theorem
that the conference judges to be a strict new reduction.

## Claim checked

The intended claim is the following.

Start from an actual paid-cap source whose stored global minimum has debt
`D_* > 0`, together with a reset owner of zero debt and a positive
owner/opponent incidence in the source's actual terminal law.  At each stage,
take the maximum-absorption exact product root against the source's full
behavioral cap.  If its absorption is positive, prefix it literally and
reconstruct the paid/reset source.  If this positive branch occurs forever,
then the resulting actual sources form a summable-absorption Zeno ray with a
uniformly nonvanishing paid/reset passport.

The note then claims that this ray cannot be oriented by the existing support
rank and cannot by itself supply a positive-charge near-return.  It isolates a
new charge-renewal statement as the remaining consumer.

## 1. One-step semantic and law account

### 1.1 Coordinatewise debt scaling: PASS

Let `z_n` be the full terminal semantic pair of the actual source profile,
and let `q_n` be exact Nash against `z_n.2`, the unrestricted behavioral cap.
Put

\[
 c_n=\Pr_{q_n}(\hbox{all Continue}),\qquad a_n=1-c_n.
\]

The checked arbitrary-root identity
`quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul`
in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`
gives, because the cap defect is zero,

\[
 d_i(z_{n+1})=c_n d_i(z_n)
\]

for every player.  Summing gives

\[
 D_{n+1}=c_nD_n.
\]

This is an all-behavior statement.  The second coordinate of the semantic
pair is the full behavioral best-response envelope, so `Never`, arbitrarily
late pure times, randomized clocks, and calendar-dependent behavioral
strategies are not being replaced by a stationary cap.

Positive global minimum debt also correctly rules out `c_n=0`: the literal
prefixed profile is actual, so its total debt is at least `D_*>0`, whereas
the displayed identity would make it zero.

### 1.2 Actual-profile provenance: PASS at each finite step

`MaximalOneStepPaidResetRegeneration.descendant_profile` in
`Research/Quitting/PaidCapMaximalOneStepRegeneration.lean` identifies the
descendant profile with the literal one-root prefix of the parent profile.
The structure also retains the same stored minimum, zero reset-owner debt,
positive incidence in the descendant's actual law, and a fresh fixed-law
reset dispatch.  No carrier point is substituted for the behavioral source
at a finite step.

### 1.3 Incidence and inherited atom transport: PASS, with a terminology fix

Literal law prefixing gives

\[
 \mu_{n+1}\ge c_n\mu_n
\]

for the nonnegative owner/opponent incidence functional.  A **fixed suffix
terminal-law coordinate** is even cleaner: its inherited contribution is
exactly multiplied by `c_n`.  Prefix absorption can add incidence, explaining
the inequality for the aggregate incidence.

The note must not alternate without warning between these objects.  The
displayed `\mu_n` is an incidence, not a source-matched marked-time atom.
Positive incidence can select a positive finite law coordinate because the
outcome set is finite, but it does not by itself retain a marked date or a
causal row.  Any claim of a retained “causal suffix atom” needs that additional
selected coordinate and its literal suffix provenance.

## 2. Paid-gain scaling needs an explicit canonical construction

### Verdict: REPAIR REQUIRED

The current proof of
`maximalOneStepPaidResetRegeneration_or_uniqueAllContinue` constructs its
descendant source with

\[
 g_{n+1}:=c_ng_n.
\]

The shifted pure-time payoff difference is actually multiplied by the paid
observer's opponent-Continue mass `\beta_n`, with `\beta_n\ge c_n`, so the
conservative scalar `c_ng_n` is a legitimate paid lower bound.  The
first-disagreement extractor preserves the two shifted pure-time witnesses.
Thus the intended recursive construction is mathematically valid.

But `MaximalOneStepPaidResetRegeneration` does **not** store

```text
descendant.gain = c_n * source.gain.
```

Its fields identify the descendant profile, minimum, reset debt, incidence,
and dispatch, but an arbitrary inhabitant may use any smaller positive paid
annotation admitted by `QuittingPaidCapLiftedSource`.  Therefore the sentence
“the one-step theorem gives `g_{n+1}=c_ng_n`” is false if read as a theorem
about an arbitrary sequence of regeneration records.

One of the following repairs is mandatory:

1. define the recursive successors by the explicit constructor used in the
   proof, and prove by induction that their annotation is `c_ng_n`; or
2. strengthen the record with

   ```text
   descendant_debt_eq
   descendant_gain_eq
   ```

   and prove those fields in the one-step constructor.

The note must then state the recursion quantifiers.  A correct exhaustive
form is:

```text
either some finite canonical stage has all-Continue as its unique exact cap root,
or there exists an infinite recursively coherent sequence of canonical
positive-absorption descendants satisfying the displayed scaling equations.
```

Merely saying “let successive sources be obtained by repeatedly taking the
positive branch” suppresses the dependence and the finite stopping
alternative.

## 3. Product and summability calculation

### Verdict: PASS after the repair above

For the explicitly constructed infinite ray, put

\[
 P_N=\prod_{n<N}c_n.
\]

Then

\[
 D_N=P_ND_0,qquad d_i(z_N)=P_Nd_i(z_0),qquad g_N=P_Ng_0.
\]

Since every finite descendant is actual and the same `D_*` is a global lower
bound,

\[
 P_N\ge D_*/D_0>0.
\]

The incidence lower bound and paid lower bound follow.  Also

\[
 \sum_{n<N}a_n
 \le -\sum_{n<N}\log c_n
 =-\log P_N
 \le \log(D_0/D_*),
\]

so `\sum a_n<\infty`, `a_n\to0`, and future tails of this absorption sum
tend to zero.  The block absorption identity

\[
 1-\prod_{k=m}^{n-1}c_k=(D_m-D_n)/D_m
\]

is exact.

An exact scalar boundary test shows that nothing stronger follows from these
equations alone.  For example, take

\[
 c_n=\exp(-2^{-n-1}),\quad
 P_n=\prod_{k<n}c_k,quad
 D_n=P_nD_0,quad g_n=P_ng_0.
\]

Then `P_n` has a positive limit, every displayed passport floor survives,
and every late future absorption sum tends to zero.  This is only a scalar
test, not a quitting-game realization, but it proves the sharpness of the
algebraic inference.

## 4. Cauchy and cap-displacement statements

### Verdict: CORRECT BUT UNDER-PROVED

If terminal rewards are bounded in absolute value by `M`, literal law
prefixing gives a total-variation/L1 one-step bound of order `a_n` for the
finite outcome law.  Prescribed payoff therefore changes by at most
`2Ma_n`.  Combining this with exact debt scaling gives a cap change of at
most `4Ma_n` coordinatewise.  Hence the payoff vector, full behavioral cap
vector, and finite terminal-law vector are Cauchy.

The note should state the norm and include these two lines.  “And similarly
for the caps” is too compressed for an export proof involving unrestricted
caps.

For every late source, the **remaining canonical ray** can consequently be
packaged as a summable cap port whose limiting cap displacement tends to
zero.  This is not a statement that every cap port or every admissible path
from that source has small charge.

## 5. Exact scope of the no-go conclusions

### 5.1 Support and normalized-debt rank: PASS

Because `c_n>0`, positive-debt support is exactly constant, and

\[
 d_i(z_n)/D_n=d_i(z_0)/D_0.
\]

Fixed player/reset labels and the Boolean orientation of the shifted paid
witness also remain fixed.  Therefore no rank which is a function only of
those displayed invariants can strictly decrease along this ray.  In
particular, the existing positive-debt-support rank does not orient it.

### 5.2 “The currently available finite ranks cannot orient”: TOO BROAD

The calculation does not rule out a finite rank using root components,
binding faces, newly created prefix atoms, or extra owner-repair data.  The
note later acknowledges exactly this.  The heading and conclusion should be
changed to:

> support, normalized-debt, and retained-label ranks do not orient the
> canonical ray.

That is the proved no-go.

### 5.3 Consecutive canonical charge: PASS

The tail sum `\sum_{k\ge m}a_k` tends to zero.  Therefore blocks made only
from sufficiently late roots of this canonical ray cannot meet a fixed
positive cumulative-absorption floor.  This correctly blocks direct use of
the varying-source cap-port theorem on those late ray tails.

### 5.4 “Available future charge”: TOO BROAD

The ray calculation says nothing about a different exact root, a reset root,
an owner-repaired connector, or an unrelated punishment-floor-admissible path
starting at the same source.  Replace every occurrence of “available future
charge” by “future absorption charge along the canonical maximal-prefix
ray.”  This distinction is the entire open problem.

## 6. Terminal approximate Nash separation

### Verdict: PASS ONLY AFTER STATING `I = Fin 4`

For four players,

\[
 \max_i d_i(z_n)\ge D_n/4\ge D_*/4,
\]

so no descendant itself is a terminal `\varepsilon`-Nash profile for
`\varepsilon<D_*/4`.

The opening theorem is written as though it were generic, while this step
silently uses four players.  State `I=\operatorname{Fin}4` at the outset, or
use `D_*/|I|` for a nonempty finite player type.  This conclusion concerns the
descendants themselves; it does not rule out terminal approximants produced
by another profile construction.

## 7. Reset cap-to-payoff seam

### Verdict: PASS, with the missing hypothesis made explicit

The theorem
`capNash_isZeroNash_at_prescribed_iff_surcharge_eq_liveDebt` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/PairBasePaidResetEndpointSeam.lean`
proves exactly that a root which is exact Nash against a semantic pair's cap
is exact Nash against its prescribed payoff iff, coordinatewise,

\[
 \operatorname{Surcharge}_i
 =c\,d_i.

\]

The fixed-law reset dispatch's returned payoff equals the target payoff only
after using the fact that `(target,mass)` belongs to the joint carrier.  The
maximal regeneration record does retain this as `target_joint`, so the
application is valid.  The note must mention that dependency; it is not a
field of an arbitrary reset dispatch in isolation.

Positive joint survival and positive total returned debt correctly show that
the simpler opponent-survival support-killing converter cannot apply.  This
does not prove the surcharge equality false; it merely shows that it is a new
nontrivial seam.

## 8. The proposed downstream lemma

### Verdict: THE CONSUMER IS MISIDENTIFIED

The displayed “Zeno-passport charge-renewal lemma” asks, for every endpoint
tolerance, for an actual punishment-floor-admissible path with one fixed
positive charge and close prescribed-payoff endpoints.  Once the source and
target admissible states are included, that is already precisely the data of
a `QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily` in
`UniformEquilibrium/Quitting/Projective/CumulativeChargeNearReturn.lean`.
Its consumer gives a uniform-equilibrium payoff directly.

It does **not** feed “through the checked varying-source consumer” in
`PaidCapPortSequenceNearReturn.lean`, whose hypotheses are instead a family of
paid cap sources with an eventual lower bound on their complete selected-port
absorption and cap displacement tending to zero.  The canonical Zeno tails
fail that absorption hypothesis.

The repaired note should either:

- state the charge-renewal lemma directly as construction of the generic
  cumulative near-return family; or
- ask for new paid cap ports with a fixed total-absorption floor and then use
  the varying-source theorem.

These are different producer obligations.

## 9. Boundary and source audit

The sentence claiming that “actual four-player maximal-root Zeno rays of this
kind” are already realized by zero-minimum regression tables is ambiguous.
`Research/Quitting/FinFourMaximalRayZeroMinimumRegressions.lean` checks actual
maximal semantic rays and separately checks local paid/zero-debt fragments on
the same tables.  Its public regression structure is not a complete
`QuittingPaidCapLiftedSource` recursion with the reset dispatch and inherited
incidence used here.  The note may cite it as an actual maximal-ray boundary
test, but must not claim it realizes the full paid/reset Zeno machine unless a
named adapter co-realizing all those fields is supplied.

Conversely, no positive-minimum table realizing the full infinite machine is
known.  That nonclaim is honest and must remain.

## 10. Strongest surviving theorem

The following is supported by the checked one-step semantics and a short
ordinary-mathematics recursion.

> **Conditional canonical Zeno theorem.** Let a finite quitting game have a
> positive global minimum `D_*>0`.  Let `S_0` be an actual paid-cap source with
> a zero-debt reset owner and a positive owner/opponent incidence in its actual
> law.  Suppose the explicitly constructed canonical maximal-root successor
> exists with positive absorption at every recursive stage, and define the
> successor's paid scalar to be `c_n` times its parent's scalar.  Then every
> stage is an actual paid/reset source with the same global minimum; debts and
> the paid scalar scale by `P_n`; incidence is at least `P_n` times its initial
> value; `P_n\ge D_*/D_0`; and the root absorptions are summable.  Therefore
> support, normalized-debt, and fixed-label ranks are constant, while every
> sufficiently late block of this canonical ray has arbitrarily small total
> absorption charge.

The exhaustive version adds the alternative that a finite recursive stage
has all-Continue as its unique exact cap root.

This theorem preserves all-behavior semantics at every finite stage.  It does
not produce a finite rank, a positive charged return, a terminal approximate
Nash profile, a contradiction to the terminal gap, or an actual
positive-minimum Zeno table.

## Required repairs before reconsideration

1. State the finite-player or `Fin 4` theorem and all recursion quantifiers.
2. Make the canonical paid annotation equation part of the construction or
   theorem surface; do not infer it from an arbitrary regeneration record.
3. Distinguish aggregate reset incidence, a fixed suffix-law coordinate, and
   a marked causal atom.
4. Prove the payoff/cap/law Cauchy estimates with a stated norm.
5. Narrow the rank and charge no-go language to the invariants and canonical
   ray actually covered.
6. State the target-joint hypothesis used for returned/target payoff equality.
7. Route a charge-renewal result to the generic cumulative near-return
   consumer, not to the varying-source cap-port theorem.
8. Correct the zero-minimum boundary claim or supply a named adapter realizing
   the complete paid/reset recursion.
9. Add an exact self-contained source audit, boundary tests, and Lean handoff.
10. Explain what is genuinely new beyond the already reviewed noncollapsing
    maximal paid/reset orbit note.  Without such a distinction, this is a
    duplicate internal analysis rather than an export-worthy strict boundary
    change.

