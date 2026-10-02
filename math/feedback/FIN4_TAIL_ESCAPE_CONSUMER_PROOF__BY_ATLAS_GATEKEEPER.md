# Audit of the proposed Fin4 tail-escape consumer

## Verdict

The atom/debt ratio invariant and finite spending account are correct **only
for an additionally supplied profile which co-realizes the high debt and the
marked suffix atom**.  `TailEscapeSubsequence` does not supply such a profile.
The proposed conclusion is not.  In particular:

1. the proposed maximal exactification is initialized at the escaped
   post-row tail, but the retained atom occurs at the row which was cut off;
2. even under an added co-realization premise, the spending arm does **not** satisfy the checked cumulative-payoff
   near-return interface; and
3. replacing the retained marked root by pure coalition siblings preserves
   the literal past, live mass, and post-date tail, but it does **not** preserve
   cap--Nash exactness of the copied past roots.

The claimed rank decrease is consequently not a well-founded conjecture-facing
descent.  It renames the unconsumed stall as a rank-one node whose advertised
downstream interfaces are not instantiated.

The strongest repair from the **current atlas data** is weaker than the split
claimed in the note.  One must either add a theorem transporting a positive
event into the escaped tail, or run an exactification which keeps the marked
row in its suffix while retaining a quantitative off-minimum debt floor.  If
such co-realization is supplied, the honest two-arm refinement is:

- a finite exact cap--Nash chronology with fixed positive weighted absorption
  charge, a retained causal atom, and terminal total debt arbitrarily close to
  the global infimum; or
- an off-minimum maximal-cap stall retaining a fixed causal atom, together
  with source-matched pure endpoint siblings whose copied past is no longer
  asserted exact.

Neither repaired arm is currently consumed.

## Sources and declarations inspected

- `TerminalCapNashChronology.lean`:
  `IsQuittingCapNashRootStack`,
  `exists_quittingCapNashRootStack`,
  `quittingCapNashStackContinueProduct`, and the exact cap-stack debt scaling
  and budget declarations in that file.
- `TerminalCapNashEndpointTransport.lean`:
  `quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash`,
  `capNash_absorptionMass_mul_debtSum_le_debtExcess`, and
  `capNash_absorptionMass_le_debtExcess_div_debtSum`.
- `TerminalSemanticLawCarrierCausalization.lean`:
  `quittingStageCoalitionMass_literalRootStack_add_length`,
  `exists_capNashRootStack_retaining_positiveStage`, and
  `exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom`.
- `TerminalSemanticStrictTailEscapeReturn.lean`:
  `capNashPrefix_tailEscape_exact_account`,
  `capNashReturnSelection_iff_tailEscape_prefix_nearMinimum`, and
  `strictTailEscape_allContinue_stalls`.
- `CumulativeChargeNearReturn.lean`:
  `QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_cumulativePayoffNearReturns`.
- The maintained atlas records described in
  `formalized/FIN4_SOURCE_PRESERVING_SIX_LEAF_PRODUCER_ATLAS.md` and
  `formalized/FIN4_PRODUCER_ATLAS_SEMANTIC_CONNECTIONS.md`, especially
  `FinFourLowTailRow`, `FinFourAtlasConcentratedSingletonEndpoint`, and
  `FinFourMonodromyProducer`.

No checked declaration selecting a maximum-absorption cap--Nash root was found.
Its existence is nevertheless a standard finite-dimensional compactness
fact: the mixed-Nash set is nonempty compact and root absorption is continuous.
It is a new formalization obligation, not a mathematical gap in the repaired
split.

## 1. What is exact

### 1.1 The current `TailEscapeSubsequence` does not co-realize the inputs

For `rows : SelectedRows`, the retained atom mass is

\[
\operatorname{selectedStageMass}(n)
=\Pr_{\operatorname{prefixedProfile}(n)}
  (S\text{ at }\operatorname{shiftedStage}(n)).
\]

By contrast, the escaped semantic tail is

\[
\operatorname{tailPair}(n)
=\operatorname{Sem}\bigl(
  \operatorname{quittingAllContinueProfileSpine}
  (\operatorname{prefixedProfile}(n))
  (\operatorname{shiftedStage}(n)+1)\bigr).
\]

Thus `tailPair` is the continuation strictly **after** the marked row.  The
field `TailEscapeSubsequence.tail_excess_floor` applies to this post-row tail,
while `stage_mass_floor` applies to the original prefixed profile at the row.
The positive event at that row is no longer present in the escaped tail.

Accordingly the first sentence of the proposed construction—choose one
escaped tail `tau` with both `D(tau) >= D_* + h` and retained causal atom mass
`m(tau) > lambda`—is not justified by any field of
`TailEscapeSubsequence`.  The current data contain two source-matched objects,
but not one object satisfying both inequalities.

There is therefore no `m(tau_0)` to which the proposed ratio iteration can be
applied.  This provenance failure precedes the near-return and sibling-cap
failures below.

### 1.2 Conditional exact ratio account

Let `tau_{k+1}` be the profile obtained by prefixing an exact cap--Nash root
`q_k` to `tau_k`, and put

\[
s_k=\Pr_{q_k}(\mathbf C),\qquad a_k=1-s_k.
\]

The checked cap identity gives

\[
D(\tau_{k+1})=s_kD(\tau_k).
\]

If the marked atom lies in the literal suffix, exact stage-mass transport gives

\[
m(\tau_{k+1})=s_km(\tau_k).
\]

As `D(tau_0)>0`, division is legitimate and

\[
\frac{m(\tau_k)}{D(\tau_k)}=
\frac{m(\tau_0)}{D(\tau_0)}.
\]

With `D(tau_k) >= D_*` and a uniform upper bound `D(tau_0) <= D^max`, this
indeed yields

\[
m(\tau_k)\ge \frac{D_*}{D^{\max}}m(\tau_0).
\]

Likewise the finite weighted absorption identity telescopes exactly:

\[
\sum_{k<K}D(\tau_k)a_k=D(\tau_0)-D(\tau_K).
\]

Thus, in the spending arm, one really obtains finite actual cap--Nash words
whose weighted charge is bounded below and whose terminal profile has total
debt arbitrarily close to `D_*`, while the shifted atom retains a fixed mass
floor.

This paragraph is a valid conditional lemma for an additionally supplied
`tau_0` carrying both properties.  It is not an output of the current
tail-escape leaf.

## 2. The spending arm is not a payoff near-return

The checked structure
`QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily` requires, for
every endpoint tolerance, a punishment-floor admissible charged path whose
**payoff annotations** satisfy

\[
|v_{\rm source}(i)-v_{\rm target}(i)|\le\varepsilon
\quad\text{for every }i.
\]

The proposed argument supplies only

\[
D(\tau_K)\le D_*+\eta.
\]

Closeness of a scalar debt objective to its minimum gives no closeness of
either prescribed payoffs or cap vectors, coordinatewise or otherwise.  The
minimum fiber may contain separated points, and the initial escaped tail need
not approach the same minimum point as the endpoint.  The retained terminal
atom also does not provide endpoint payoff closure.

`capNashReturnSelection_iff_tailEscape_prefix_nearMinimum` confirms only a
**debt-neighborhood return**.  It does not construct a
`QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily`.  No “causal
return/near-return compiler” with the premises used in the note was found.

Therefore the strongest valid spending output is:

> For every `eta > 0`, an actual finite exact cap--Nash chronology of fixed
> positive weighted absorption charge, ending at total debt at most
> `D_* + eta`, and retaining the specified shifted atom at a fixed positive
> mass.

This is potentially useful input for a future recurrence or compactness
argument, but it is not yet a UE consumer.

## 3. Pure siblings lose upstream cap exactness

At the retained marked row, replacing only player `i`'s action gives the exact
same-past/same-tail identity

\[
U_i(\pi_{C\triangle\{i\}})-U_i(\pi_C)
=\ell\,[r_i(C\triangle\{i\})-r_i(C)].
\]

The player's best-response envelope is unchanged by changing only that
player's prescribed strategy, so the mover-debt subtraction is exact.  The
live mass is unchanged, and routing a pure endpoint does not lose marked
stage mass.  These parts are valid.

However, a cap--Nash root in the copied past was selected against the cap of
the original suffix.  Changing the later marked row can change that suffix's
unrestricted cap vector.  Hence the copied root word is literal but generally
is **not** an `IsQuittingCapNashRootStack` over any modified sibling.

The pure siblings therefore do not instantiate the existing low-tail atlas
interfaces merely by carrying the original stall stack.  In particular:

- `FinFourAtlasConcentratedSingletonEndpoint` currently projects a
  `FinFourLowTailRow`; the stall endpoint is off-minimum and has no such row;
- `FinFourMonodromyProducer` is produced from the low-tail endpoint dispatch,
  not from an arbitrary off-minimum same-tail toggle cycle; and
- the original exact prefix certificate can be retained only as provenance of
  the unmodified source, with an explicit nonclaim of target-side exactness.

This is the same cap-instability seam that obstructs source-anchored vertical
repair elsewhere in the atlas.

## 4. The finite toggle geometry is only a static refinement

The source-matched pure endpoint dispatch is mathematically legitimate.  A
nonsingleton sink gives a sure-exit terminal Nash profile.  Otherwise a finite
strict path reaches a singleton or a nonsingleton cycle; on Fin4 a simple
nonsingleton cycle has length at most eight and admits the familiar common-host
or complementary-pair geometry.

But the resulting singleton/cycle has an **off-minimum stall passport**, not
the low-tail passport required by the checked atlas constructors.  No theorem
consumes this new passport, regenerates a minimum source, or prevents return to
the raw tail-escape obstruction.  Assigning it natural-number rank one and
declaring that there is no constructor back is not a proof of progress: a rank
is useful only when every rank-one node has a consumer or a proved
rank-decreasing successor.

After first solving the co-realization problem, an honest atlas refinement
could add a named off-minimum cap-stall obligation, not declare a descent:

\[
\begin{array}{c}
\text{tail escape}\Longrightarrow\\
\text{charged exact debt-neighborhood entrance with retained atom}
\quad\lor\quad
\text{off-minimum maximal-cap stall with retained atom}.
\end{array}
\]

Within the second arm, pure endpoint geometry supplies a static
singleton/cycle refinement with same-past/same-tail data and an explicit
warning that cap exactness is source-only.

## 5. Required repairs

To recover the claimed conclusions, one needs at least one genuinely new
bridge:

1. **High-tail/atom co-realization:** place a fixed positive causal event in
   the post-row escaped tail, or retain a quantitative high-debt property on a
   profile which still contains the marked row.
2. **Spending recurrence:** prove that the finite charged debt-neighborhood
   entrances have source and target payoff annotations converging to the same
   vector, with punishment-floor admissibility, so that the checked cumulative
   near-return compiler applies.
3. **Past-cap stability:** repair or reselect the past after each marked-row
   override while preserving the fixed atom/gain scale and source attachment.
4. **Stall consumer:** consume the off-minimum maximal-cap stall directly, or
   regenerate an actual minimum-fiber atlas source with a strict finite rank
   decrease and all required provenance.

Without one of these bridges, the note is a valuable exact decomposition and
diagnosis, but not the asserted consumer proof.

## Export-gate verdict

**NOT EXPORTABLE AS STATED.**  The corrected ratio/telescope and the honest
spending-versus-stall refinement are suitable Research material.  They should
not be exported as a tail-escape consumer, near-return producer, or
well-founded descent.
