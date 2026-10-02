# Strict-inert diffuse toll: orientation and the remaining closure test

Author: `CODEX_CURIE`

## Status

Current result.  The finite-block orientation lemma below is proved in
ordinary mathematics from the checked strict-basin and literal Bellman
identities.  It converts the supposedly unoriented diffuse toll into one
actual unilateral Continue-through-the-block gain.  The exact screening
theorem in Section 8 shows why this nevertheless cannot affect the supplied
strict-arm whole source: the minimum-anchored repair lies behind a pure
nonsingleton row.  This is a formalizable no-go for the direct signed-toll
argument, not a terminal consumer.  No export is claimed.  The next open
question is the outer prefix ray and its compactified bubble, stated in
Section 9.

## Question

Work in the strict normalized-passport arm of
`questions/FIN4_RENEWABLE_ORIENTATION_OR_COUNTEREXAMPLE.md`.  A
successor-linked finite word starts at a prescribed payoff arbitrarily close
to the compact minimum-fibre payoff set, leaves its strict all-Continue basin,
has maximum row Nash defect tending to zero, and pays a fixed positive
aggregate defect toll.  Can this regime be turned into a source-matched
cumulative return, chronological shadow, renewable finite-rank descent, or a
contradiction?

The first issue is whether the positive aggregate toll is intrinsically
unsigned.  It is not.

## Sources inspected

The bounded source set is:

- `exists_finFour_minimumFiber_linearAbsorptionDefect_of_no_uniformPayoff`
  in
  `UniformEquilibrium/Quitting/Root/StrictAllContinueBasinLinearAbsorptionDefect.lean`;
- `sum_error_ge_of_successorPath_exists_not_mem_linearBasin` in
  `UniformEquilibrium/Quitting/Paths/StrictAllContinueBasinSuccessorPath.lean`;
- `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart` and
  `quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`;
- `quarterGap_mul_absorptionMass_le_totalNashDefect_of_smallAbsorption` in
  `UniformEquilibrium/Quitting/Root/StrictAllContinueBasinLinearAbsorptionDefect.lean`;
- `quittingTerminalDeviationDebt_rootThenContinuation_le_coordinateDefect_add`
  in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`; and
- the opponent-Green definitions and telescope in
  `UniformEquilibrium/Quitting/Root/TerminalDebtGreenAccount.lean`.

The direct Fin4 input is the strict arm of
`Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean`, together with
the normalized slice in `Research/Quitting/NormalizedPassportMinimizer.lean`.

## 1. Use the actual maximum coordinate defect

Let

\[
 v_{t+1}=F_{q_t}(v_t),\qquad 0\le t<L_n,
\]

be a successor-linked path, indexed outward from the terminal continuation.
Put

\[
 \delta_{n,t,i}:=
 \operatorname{Def}_i(v_{n,t},q_{n,t}),\qquad
 e_{n,t}:=\max_i\delta_{n,t,i}.
\]

The root is an exact `e_{n,t}`-Nash root in the approximate sense: all four
coordinate defects are at most `e_{n,t}`.  Thus the first-exit toll can be
applied with this *minimal declared error*, rather than with an arbitrarily
inflated certificate.  If

\[
 \tau:=\frac{c\rho}{16C}>0,
\]

then every word reaching outside the basin satisfies

\[
 \sum_{t<L_n}e_{n,t}\ge\tau.                 \tag{1}
\]

Assume

\[
 \varepsilon_n:=\max_{t<L_n}e_{n,t}\longrightarrow0. \tag{2}
\]

Let `H_n` be the first index at which the partial sum reaches `tau/2`.
Then

\[
 \frac\tau2\le
 \sum_{t<H_n}e_{n,t}
 \le\frac\tau2+\varepsilon_n.                \tag{3}
\]

All tails displayed by these rows still lie inside the basin, because the cut
occurs no later than first exit.

## 2. Every defect in the cut block is Continue-oriented

Inside the strict basin there is a uniform own-singleton gap.  The proof of
`quarterGap_mul_absorptionMass_le_totalNashDefect_of_smallAbsorption` gives the
stronger coordinate fact used internally there: below one fixed absorption
threshold,

\[
 Q_i(v,q)-C_i(v,q)\le-\Delta/4
 \qquad\text{for every }i.                   \tag{4}
\]

On the other hand the linear basin estimate and the definition of `e_{n,t}`
give

\[
 c\,a_{n,t}
 \le\sum_i\delta_{n,t,i}
 \le4e_{n,t},                                \tag{5}
\]

where `a_{n,t}` is total root absorption.  By (2), the maximum absorption in
the word tends to zero.  Hence (4) applies at every row of the cut block for
all large `n`.

Consequently Continue is the unique best Boolean endpoint for every player,
and

\[
 \delta_{n,t,i}
 =q_{n,t,i}\bigl(C_i(v_{n,t},q_{n,t})-
                        Q_i(v_{n,t},q_{n,t})\bigr). \tag{6}
\]

Thus the toll does not switch signs or orientations.  It is the aggregate
cost of prescribed Quit clocks in a region where all players prefer
Continue.

## 3. A uniform opponent-survival floor

From (3)--(5),

\[
 \sum_{t<H_n}a_{n,t}
 \le \frac4c\left(\frac\tau2+\varepsilon_n\right). \tag{7}
\]

For large `n`, every `a_{n,t}\le1/2`.  Since

\[
 \log(1-x)\ge-2x\qquad(0\le x\le1/2),
\]

the joint survival through the cut block obeys the source-independent bound

\[
 \prod_{t<H_n}(1-a_{n,t})
 \ge
 \exp\!\left[-\frac8c
   \left(\frac\tau2+\varepsilon_n\right)\right]. \tag{8}
\]

In particular, after discarding finitely many ranks, it is bounded below by
one constant `kappa>0`.  Playerwise opponent survival is at least joint
survival, so the same `kappa` works for every player.

## 4. Exact Continue-through-the-block gain

By (3) and finite pigeonhole, after a subsequence one fixed player `p`
satisfies

\[
 \sum_{t<H_n}\delta_{n,t,p}\ge\frac\tau8.     \tag{9}
\]

Modify only player `p` so that it plays Continue surely at every row of the
cut block, and afterward resumes the same literal terminal continuation.
This is one legal complete behavioral replacement.

Let `G_{n,t}` be the payoff gain of this replacement through the first `t`
inner rows.  The exact one-row Bellman calculation, using (4), is

\[
 G_{n,t+1}
 =\delta_{n,t,p}
  +\operatorname{OppCont}_p(q_{n,t})G_{n,t},
 \qquad G_{n,0}=0.                           \tag{10}
\]

This is an equality, not the one-sided terminal-debt Green estimate: the
chosen replacement is precisely the better Continue endpoint at every row.
Iterating (10), and using the survival floor (8), yields

\[
 \boxed{G_{n,H_n}\ge\kappa\tau/8>0.}         \tag{11}
\]

Thus the uncovered long-word regime cannot hide its toll among differently
oriented players.  It produces one fixed-label, source-matched, actual
behavioral deviation with a uniform payoff gain.  The replacement changes
only preselected rows, has the same literal terminal continuation, and the
mover's unrestricted cap is unchanged; hence its mover debt decreases by
exactly `G_{n,H_n}`.

## 5. What remains to make this a consumer

Equation (11) is still only a paid finite-block move unless the normalized
slice is used again.  The proposed next step is:

1. choose the passport density thresholds below the original marked-mass and
   historical-gain floors divided by a global debt bound;
2. observe that forcing an outer-prefix player to Continue can only increase
   reach of the retained marked row, so marked mass and historical paid gain
   do not decrease;
3. conclude that the modified decorated point remains in the same normalized
   slice;
4. invoke slice minimality to show total debt cannot decrease; and
5. combine exact mover-debt subtraction with total nondecrease to obtain a
   fixed spectator debt rise.

The endpoint-rise decoder would then turn the same actual source/target pair
into a fixed-charge stopping-law atom alternative.  This would reduce Arm B
to the same source-exact atom object already obtained from paid cycles in Arm
A.  It would still need the final chronological orientation demanded by the
question, so this step is useful only if it can be made renewable rather than
ending at another atom residual.

Two points require checking before claiming even that reduction:

- the repair word must occur on the prefix side of the retained marked event;
  if it lies after the marked date, changing it does not increase marked
  reach and the normalized-slice argument is inapplicable;
- raw-slice closure must contain the simultaneously modified comparison
  sibling, not only the endpoint profile.

## 6. Occupation-flow warning

Normalizing the first-exit words by total absorption does not by itself yield
a forbidden homogeneous singleton-LCP direction.  Before first exit, the
small-root limit is a controlled continuous trajectory

\[
 \dot v(s)=\sum_i h_i(s)\bigl(r(\{i\})-v(s)\bigr),
 \qquad h_i(s)\ge0,                          \tag{12}
\]

with a strictly positive running Nash cost supplied by (4).  An open
trajectory from the minimum tube to its boundary need not satisfy an
algebraic complementarity condition.  The homogeneous no-go becomes relevant
only after a genuine payoff-period closure or a source-matched return has
been proved.  Treating the open occupation path itself as closed would repeat
the nonlocality error.

## 7. Exact placement in the Fin4 adapter: the seam is unavoidable

The source audit resolves the preceding check negatively.

The normalized decorated descendants are obtained by prefixing a word `W`
**before** the forced endpoint profile.  At the marked date that endpoint is
literally a pure pair; this is
`FinFourMinimumReturnForcedPair.pairProfile_eq_literalPureRootCoalitionProfile`
in `Research/Quitting/FinFourProducerAtlas/ForcedPair.lean`.  Thus the
chronological form is

\[
 W\;*\;(\text{pure pair})\;*\;(\text{minimum post-mark tail}). \tag{13}
\]

There are consequently two mutually exclusive placements for a proposed
successor repair.

### Pre-mark placement

A word inserted in `W` has positive reach before the sure-absorbing pair and
can alter the whole semantic point.  But its inner continuation is the
semantic pair of the pure-pair endpoint.  That pair has the table-determined
pure-coalition debt, and in the strict arm it is not the supplied minimum
post-mark tail.  Hence the hypothesis that the successor word starts near the
minimum-fibre payoff set is unavailable.  The checked minimum-tube toll cannot
be applied to this word.

### Post-mark placement

A word inserted after the marked row does start from the supplied minimum
tail, so Sections 1--4 apply and orient its aggregate toll.  But the pure pair
screens this continuation from every unilateral deviation.  If `C` is the
pair, then for every player `i` there is a member of `C\setminus\{i\}` who
still Quits surely after replacing `i`'s complete strategy.  Therefore the
continuation reach is exactly zero on both prescribed and unilateral paths.
The whole-profile gain corresponding to (11) is

\[
 \operatorname{LiveAfterPair}\cdot G_{n,H_n}=0. \tag{14}
\]

It also cannot change the pure-pair whole semantic pair or exactify one of its
toggle defects: those defects are determined solely by the rewards of `C` and
`C\triangle\{i\}`.

Hence no successor word from the current premises is simultaneously:

1. anchored at the minimum post-mark tail;
2. positively reached under a relevant whole-source deviation; and
3. placed before the marked pure pair so that it can alter the inert whole
   point.

This is an exact factorization obstruction, not a missing estimate.

## Corrected conclusion

The diffuse toll itself has a signed occupation orientation: (11) is a valid
actual gain for the repair-tail profile.  But it is not a gain of the strict
normalized-passport whole source.  The current Arm B data place the minimum
anchor and positive whole-source reach on opposite sides of a pure
nonsingleton screening row.

A useful additional premise would have to supply one of:

- a successor-linked repair **before** the mark whose inner continuation is
  nevertheless on the minimum fibre;
- a marked root with positive unilateral continuation reach, rather than the
  literal pure pair; or
- an exact source-matched seam transporting the oriented post-mark gain to a
  pre-mark paid edge.

Without one of these, the vertical-toll regime cannot consume Arm B.  The
remaining honest target is the outer-prefix inert ray itself: orient its
finite exact cap-prefix history or show that its positive nonsingleton bubble
at infinity contradicts positive global minimum.  The post-mark occupation
measure is not that object.

## 8. Formalizable tail-screening theorem

The factorization in (14) admits a stronger, tail-independent statement.
Let `C` be any finite quitting coalition with

\[
 |C|\ge2,
\]

let `W` be an arbitrary finite list of product roots, and let `tau` and
`tau'` be arbitrary behavioral tails.  Define

\[
 P_\tau
 :=W*\bigl((\operatorname{pure} C)*\tau\bigr),
 \qquad
 P_{\tau'}
 :=W*\bigl((\operatorname{pure} C)*\tau'\bigr).
 \tag{15}
\]

Then

\[
 \boxed{\operatorname{Sem}(P_\tau)=\operatorname{Sem}(P_{\tau'}).}
 \tag{16}
\]

In particular, for every player `i`, both the prescribed terminal payoff and
the supremum over **all behavioral unilateral deviations** are equal, and so

\[
 U_i(P_\tau)=U_i(P_{\tau'}),\qquad
 B_i(P_\tau)=B_i(P_{\tau'}),\qquad
 d_i(P_\tau)=d_i(P_{\tau'}),\qquad
 D(P_\tau)=D(P_{\tau'}).
 \tag{17}
\]

The proof is exact.  At the marked pure root, prescribed play absorbs in
`C`.  After replacing any one player's complete strategy, at least one
member of `C` other than that player still Quits surely.  Hence no unilateral
deviation can reach the post-mark tail.  Equivalently, the checked theorem

```text
quittingTerminalSemanticPair_pureSetRootThenContinuation_eq_of_two_le_card
```

in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean` computes the same
explicit semantic pair for both tails.  Prefix the resulting equality by
each root of `W`, using

```text
quittingTerminalSemanticPair_rootThenContinuation
```

in `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`, and induct
on `W`.  This yields (16).  The literal stack constructors are
`quittingLiteralRootStackProfile_cons` and
`quittingLiteralRootStackProfile_append` in
`UniformEquilibrium/Quitting/Root/LiteralExactPrefixStack.lean`.

A suitable Lean adapter is:

```lean
theorem quittingTerminalSemanticPair_literalRootStack_pureSet_screen
    (roots : List (iota -> PMF Bool))
    (C : Finset iota) (hC : 2 <= C.card)
    (first second : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward roots
          (quittingRootThenContinuationProfile reward
            (quittingPureSetRoot C) first)) =
      quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward roots
          (quittingRootThenContinuationProfile reward
            (quittingPureSetRoot C) second))
```

and the debt equalities in (17) are immediate corollaries.

This theorem is deliberately narrow.  It does **not** rule out:

- changing a root in `W` before the pure pair;
- replacing the pair by a non-pure marked root with positive unilateral
  continuation reach;
- a commutator using different prefix words on the two siblings; or
- an independently proved seam which transports a post-mark account to a
  pre-mark paid edge.

### Strict-arm anchor mismatch

The other half of the no-go is not tail screening but hypothesis placement.
The checked linear-basin toll starts from a payoff in the minimum-fibre tube.
For a word inside `W`, the immediate inner continuation is the pure-pair
semantic point, which is table-determined and need not lie in that tube.
For a word after the pair, the inner continuation is the supplied
minimum-fibre tail, but (16) makes it behaviorally invisible from the whole
source.  Thus the current packet places the two required properties on
opposite sides of the screen:

\[
 \boxed{
 \text{minimum anchoring after the pair}
 \quad\vert\quad
 \text{positive whole-source reach before the pair}.}
 \tag{18}
\]

Any direct signed-toll completion must add a theorem crossing (18), not
another estimate on the post-mark word.

## 9. Next question: the outer ray rather than the screened tail

In the strict maximal-prefix ray, the chronological profiles have the form

\[
 q_{k-1}*q_{k-2}*\cdots*q_0*(\operatorname{pure} C)*\tau_k,
 \tag{19}
\]

where the survival product converges to a positive number and the marked
pair is pushed to arbitrarily late calendar dates.  Thus a fixed-calendar
compact stopping-law limit can be all-Never even while the terminal laws
retain a positive nonsingleton bubble and the semantic debts converge to a
strictly positive off-minimum value.

The next useful theorem must act on the **outer prefix laws** in (19), not on
`tau_k`.  Two concrete tests remain:

1. apply the compact outcome-bubble/debt-jump account to the reversed prefix
   stacks and determine whether the retained forced-pair gain or punishment
   normality forces the escaped social reward to be no larger than the cap
   jump; or
2. normalize nonzero maximal exact roots approaching all Continue, while
   retaining the cap-displacement term.  Exact complementarity gives an open
   projective trajectory; it yields the hard residual's forbidden
   homogeneous singleton-LCP direction only if a genuine payoff-period
   closure makes the normalized cap displacement vanish.

The explicit next question is therefore:

> Does the strict outer ray produce a source-matched cap-displacement return,
> or does its compactified nonsingleton bubble violate the positive-minimum
> debt-jump account?

An open occupation path or a positive escaped atom alone is not an acceptable
answer.
