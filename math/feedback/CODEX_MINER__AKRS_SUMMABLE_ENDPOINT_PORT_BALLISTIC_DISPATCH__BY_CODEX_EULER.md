# Independent review of the AGKRS summable-port ballistic dispatch

Reviewer: `CODEX_EULER`

Target:
[`CODEX_MINER__AGKRS_SUMMABLE_ENDPOINT_PORT_BALLISTIC_DISPATCH.md`](../notes/CODEX_MINER__AGKRS_SUMMABLE_ENDPOINT_PORT_BALLISTIC_DISPATCH.md)

Verdict: **REVISE, then PASS.**  The mathematics of Propositions 4.1 and 5.1,
the limiting modulus, zero-charge rigidity, and signed-label constant all
pass.  One mandatory source/novelty repair remains before packet assembly:
compare explicitly with the now checked
`PositiveJointSummablePortPhantomReduction.lean`.  That file reduces every
summable positive-joint port to S.1 or the existing positive-singleton phantom;
it does not contain or subsume the present charge-conditioned returned-port
S.3 consumer or the ballistic displacement modulus.

After that repair, I regard the theorem as a legitimate narrow export
candidate: it closes the **positive-total-charge returned summable-port**
subarm through literal S.3 and replaces the remaining summable-port obligation
by the exhaustive zero-charge phantom / quantitatively displaced signed-port
boundary.  It does not close the whole positive-joint source class or AGKRS
Theorem 3.4.

## 1. Claim and quantifier audit

The maintained input is an actual reached
`QuittingPositiveJointPrefixReachPunishmentEndpoint` together with the
canonical exact-prefix orbit `O` and a
`SummableChargeAllContinuePort`.  Write

\[
 a_t=\operatorname{absorption}(q_t),\qquad
 A=\sum_t a_t,qquad E=v_0,qquad L=\lim_t v_t.
\]

The claimed new statements are:

1. under failure of well-supported S.3, there is `e>0` such that every finite
   orbit segment of positive cumulative charge `C` has endpoint seam
   strictly greater than `e C/(1+C)`;
2. consequently `A>0` and `L=E` imply literal well-supported S.3;
3. under failure of S.3, positive total charge forces
   `max_i |L_i-E_i| >= e A/(1+A)`, while `A=0` makes every root all Continue
   and every orbit value equal to `E`; and
4. the positive-displacement arm feeds the checked fixed signed-terminal-label
   port with the displayed mass constant.

Negating
`QuittingWellSupportedAbsorbingSequenceExistence reward` legitimately gives
one `delta>0` for which no completely absorbing root sequence is support-local
`delta`-Nash at every tail.  A nonpositive witness cannot arise from the
negation because the defining implication is then vacuous.  Taking
`e=delta/2` matches exactly the factor two in
`QuittingFiniteSingleSeamProjectiveLasso.exists_supportRationalDivergentPath`.

## 2. Finite-segment inequality

For `segment=O.toFiniteSegment s N`, the finite-prefix charge is exactly

\[
 C(s,N)=\sum_{t=s}^{s+N-1}a_t,
\]

and its endpoint seam in every coordinate is bounded by

\[
 D(s,N)=\max_i|v_{s+N}(i)-v_s(i)|.
\]

If `C>0` and the weak reverse of (4.1) holds, set

```text
chargeFloor = C,
seamError   = D,
error       = e.
```

The hypotheses of
`exists_singleSeamProjectiveLasso_of_floorPrefix_cumulativePayoffNearReturn`
then match literally:

\[
 D\le e\frac C{1+C}.
\]

The resulting lasso has a support-rational path with support error
`2e=delta` and nonsummable absorption.  The standard survival-product lemma
makes that path completely absorbing, contradicting the selected failure
scale.  Hence the strict inequality is correct.  Positive `C` also excludes
the zero-horizon boundary automatically.

No no-sure-exit or endpoint-specific field is used in this estimate; it is a
valid generic statement for exact punishment-floor orbit segments.

## 3. Returned positive-charge consumer

Assume `A>0` and `L=E`.  For arbitrary lasso error `epsilon>0`, choose
`c=A/2`.  Nonnegative partial charge sums converge increasingly to `A`, so
eventually they exceed `c`.  Since the player type is nonempty and finite,
coordinatewise convergence `v_N -> E` is uniform over players, and eventually

\[
 \max_i|v_N(i)-E(i)|
 \le \epsilon\frac c{1+c}.
\]

The initial finite segment therefore gives a lasso at the arbitrary error
`epsilon`.  The checked
`quittingWellSupportedAbsorbingSequenceExistence_of_singleSeamProjectiveLassos`
consumer yields literal well-supported S.3.  This proof respects all S.3
quantifiers; it does not merely produce one sequence at one tolerance.

This is the genuinely consumed subarm.  A positive summable charge alone is
not enough; the return `L=E` supplies the vanishing seam.

## 4. Infinite modulus and exhaustive split

When `A>0`, the partial charges are eventually positive.  Apply the strict
finite inequality to those initial segments and pass to the limit.  The right
side converges continuously to `e A/(1+A)`, while finite-coordinate
convergence gives

\[
 \max_i|v_N(i)-E(i)|\longrightarrow \max_i|L_i-E_i|.
\]

The limiting inequality is correctly non-strict:

\[
 \max_i|L_i-E_i|\ge e\frac A{1+A}.
\]

If `A=0`, nonnegativity of every `a_t` forces every term to vanish.  Zero
product-root absorption is equivalent to every player's marginal being pure
Continue.  The Bellman policy then gives `v_{t+1}=v_t`, so the entire orbit is
literally constant at `E`.  This is stronger than merely `a_t ->0`.

The advertised three-way dispatch is logically exhaustive by first splitting
on global S.3.  Under `notS3`, split the summable port on `A=0` versus `A>0`.
The latter automatically has the displayed nonzero displacement.  The
no-sure-exit endpoint provenance is retained but is not used to derive the
numeric split.

## 5. Signed terminal label and constants

Put

\[
 \rho=e\frac A{1+A}>0.
\]

Finiteness selects a coordinate with
`rho <= |L(who)-E(who)|`.  Positive displacement forces
`M=quittingRewardBound reward>0`, because all reward and orbit coordinates
lie in the `M` box.  The hypotheses of
`nonempty_summableChargeSignedTerminalPort_of_displacement` are therefore
met with this exact `rho` and `M`.

The checked conclusion is

\[
 \frac{\rho}{2M(2^{|I|}-1)}
 \le \sum_t\Pr_{q_t}(\text{selected nonempty coalition}),
\]

with one fixed player, sign, and coalition.  The note's denominator and
quantifier scope are correct.  This is a mass ledger, not itself an S.3 or
source-regeneration consumer.

## 6. Source and subsumption repair

The current source tree contains
`UniformEquilibrium/Quitting/Classification/Existence/PositiveJointSummablePortPhantomReduction.lean`.
Its theorem

```text
QuittingPositiveJointPrefixReachNoSureExitResidual.
  wellSupported_or_stationary_or_singletonDefect
```

uses the formal all-Continue limit to return S.3, S.1, or the existing
positive-singleton support-Bellman defect.  It is stronger in a different
direction: it applies to every summable port without inspecting total charge.
It does **not** say that a positively charged returned port gives S.3, does
not prove the ballistic lower bound, and does not produce the signed terminal
mass scale.

The reviewed note should add this comparison to Sections 2 and 8.  In the
hard no-S.1/no-S.3 branch, both reductions hold simultaneously: the checked
file supplies a positive-singleton phantom, while the present theorem further
classifies the port as literal zero charge or quantitatively displaced.  No
claim should be made that the signed terminal label consumes the singleton
phantom.

## 7. Frontier and export assessment

After the source-audit repair, the result makes a strict named change to the
summable endpoint obligation in
`questions/AGKRS_THEOREM_3_4_SOURCE_CLOSURE.md`:

* positive total charge plus endpoint return is closed through literal S.3;
* under failure of S.3, the only survivors are a literal constant all-Continue
  phantom or a quantitatively displaced signed summable port.

That is enough for a narrow export candidate because it has the checked
actual endpoint adapter and an actual branch S.3 consumer.  The packet must
retain the following nonclaims:

* no closure of the zero-charge phantom;
* no closure of the displaced signed port;
* no well-founded rank from a real displacement;
* no realization of the formal port limit by one behavioral profile; and
* no unconditional AGKRS Theorem 3.4 conclusion.

