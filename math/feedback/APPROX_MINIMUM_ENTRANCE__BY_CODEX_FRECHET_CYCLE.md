# Independent review of APPROX's minimum-entrance response

Reviewer: `CODEX_FRECHET_CYCLE`.

Verdict: **PASS of the mathematical argument in the intended Fin4
positive-global-SUM-minimum context**, with the carrier/actual distinction
below made explicit. No arithmetic or unrestricted-cap gap found. The
claimed final support-Nash producer is correctly left open. This is an
ordinary-mathematics audit, not a Lean check or export approval.

## Frozen surface and scope

The reviewed response is the complete second response in `gpt/APPROX.md`,
beginning “The cap-tight branch can be consumed explicitly” and continuing
to EOF. It was read in full before feedback. The first response was then
read for the packet's context; its repair/equivalence claims are not
reviewed here. No other reviewer report was read.

```text
Whole APPROX SHA:
3a7e5b844186f587a454b9a7437aef72dd1a365acea3ccda36f92c0fa6b0258d

Second-response SHA:
d18f8a88bc1928d6e3ae4c11bd5333741aa7e43e356fe662fab5254756698f73
```

The context requires bounded rewards, all-Never reward zero, independent
product stopping laws, unrestricted unilateral behavioral deviations,
and `D_*>0` as the **global minimum of SUM debt** over the complete
terminal-semantic carrier. The displayed punishment-floor packet uses
`P_i≤s_i`. The contrary-case finite exact-capacity theorem is an external
input, not something proved by this submission. Its required full-box
version is available in the narrowly inspected sources.

The standalone reconstruction is
[`CODEX_FRECHET_CYCLE__SUM_MINIMUM_UNIFORMLY_REACHED_ENTRANCE.md`](../notes/CODEX_FRECHET_CYCLE__SUM_MINIMUM_UNIFORMLY_REACHED_ENTRANCE.md).
It attributes the argument to this submission and exposes the independent
capacity input and its alternative isolation-based justification. That
rewritten surface has not itself received an independent review.

## Valid calculations and falsification checks

1. **Exact cap-debt identity.** With c the joint Continue probability,
   `F_i(q,b)−F_i(q,u)=c(b_i−u_i)`. Therefore
   `d_i(T_qz)=c d_i(z)+g_i(q,b)` is exact. The cap map is max(Quit,
   Continue with a full cap), so it includes finite and Never deviations.
   Its continuous extension preserves the carrier even for unattained
   semantic points.

2. **Weak cap margin.** For a root Nash against `b−t·1`, raising the
   continuation back to b creates defect at most `t q_i α_i` for player i.
   The singleton masses sum to at most absorption. The displayed SUM
   budget thus forces all-Continue when t<D_*, and the limit t↑D_* gives
   `b_i≥s_i+D_*`. No maximum-debt minimum can be silently substituted.

3. **Equality-arm orbit and packet.** The chosen
   `λ=D_*/[2(D_*+2M)]` satisfies
   `(1−λ)D_*−2Mλ=D_*/2`. This keeps every outsider's cap Continue
   branch strictly active. The owner contributes exactly λD_* cap-root
   defect, so each prefix stays at SUM minimum and keeps its owner cap.
   The modified annotations `v_k=s_k`, `v_j=b_j` are within the reward
   box and form an exact Bellman orbit with the fixed independent solo
   root. They need not equal the source's actual prescribed vector.
   This distinction is explicitly allowed by the packet question and
   does not invalidate the construction. Reversing the chronology gives
   a standard finite exact Nash–Bellman block with the same Hλ charge.

4. **Capacity dependency is not circular.** The source
   `finFour_quittingFullBoxExactPredecessor_hasFiniteBudget_of_no_uniformPayoff`
   bounds all full-box exact predecessor paths, not only paths reachable
   from a chosen punishment anchor. Its proof uses the independent finite
   exact-block hazard-capacity theorem. The submission does not assume
   the unbounded approximate-packet producer it is trying to obtain.
   The annotations in fact lie in the canonical reward box because caps
   and singleton rewards do; the chosen numerical bound M may be larger
   without spoiling that fact. Punishment floors hold under P≤s.

5. **Deleting a small prescribed row.** The front cap exceeds immediate
   Quit by at least `D_*+ρ/4`, so Continue is truly its maximizing branch.
   This justifies both the cap-root regret formula and the cap comparison
   across deletion. The rearrangement from (9) to (10) is valid:
   `(1−a)(D_front−D_tail)≥a(D_*+ρ/4−D_front)≥ρa/8`,
   and `0<1−a≤1`. Deletion lowers debt by at least ρa/8 and preserves
   near-minimality. It is not an unrelated-root replacement.

6. **Existence of the first large row.** If all rows were small, the
   deletion inequality bounds the unweighted absorption sum. Its tails
   bound conditional future absorption, hence conditional prescribed
   payoffs tend to zero. Some own singleton is positive because otherwise
   all-Never is exact terminal Nash. The near-minimum payoff lower bound
   therefore contradicts that zero limit. Before the selected row every
   joint survival is at least 1/2, so all the continuations used in this
   argument are genuinely reached.

7. **Reach, both vectors, and the atom.** The bounds
   `Σ_(t<T)a_t≤8ε/ρ`, `reach(T)≥1−8ε/ρ`, and semantic sup-distance
   at most `16Mε/ρ` all check. Prescribed payoff changes are at most
   2Ma per deleted row; the verified cap Continue branch gives the same
   bound for every full cap. The fifteen-coalition argument and reach
   at least 3/4 give the stated strict unconditional atom bound h/20.
   No uniform bound on T follows or is needed.

8. **Limit construction.** One common subsequence of roots and post-row
   semantic pairs exists by finite-dimensional compactness. Prefix
   continuity gives `z_*=T_(q_*)z⁺` with `a(q_*)≥h`. If a selected
   large row has zero joint survival, its post-row behavior can still
   be specified as part of the complete behavioral profile; it is not
   claimed to be a positive-probability conditioned event. This does not
   affect the prefix identity or the carrier limit.

## Necessary wording and hypothesis clarifications

The sentence describing (15) as an “actual ... incoming row at a
minimum-debt point” must not be read as asserting actual attainment of
z_* or z⁺. The valid statement is a **carrier incoming-root
representation with uniformly reached, same-source actual approximants**.
The limiting q_* is an actual product root, but z⁺ may be unattained.

Likewise “uniformly absorbing row” here means one root has absorption
at least h, not eventual almost-sure absorption of the whole profile.
The large row need not be support-Nash against u⁺ or cap-Nash against
b⁺. Its exact debt ledger allows positive root regret and an off-minimum
tail. The submission's final nonclaim correctly preserves this seam.

Outside the intended context, strict cap surplus needs its stated
capacity or equivalent isolation premise. It is not justified by
compactness and D_*>0 alone in an abstract arbitrary prefix system.

## Source correspondence and novelty boundary

The narrow search read the named declarations and needed definitions in:

- `TerminalSemanticCapNashNearMinimum.lean`: the weak margin and
  auxiliary constant-shift budgets are existing results.
- `TerminalSemanticSingletonTightMinimumFaceIteration.lean` and
  `TerminalSemanticMinimumLawFiniteAtom.lean`: controlled solo-prefix
  iteration and strict actual-payoff singleton isolation at positive
  punishment-normal SUM minima are existing. Indeed the proposed
  equality orbit also excludes cap equality without capacity: the
  owner's prescribed coordinate tends to s_k on the compact minimum
  fiber, contradicting the existing strict-isolation theorem.
- `TerminalSemanticFinFourMinimumFiberIsolation.lean`: uniform strict
  actual-payoff isolation is existing. It is not the asserted cap surplus
  `b_i−s_i−D_*>0` verbatim, but the latter follows by the displayed orbit
  and compactness. Treat this as a useful consequence, not new basic
  singleton isolation.
- `LawTightCapNashGlobalMinimumMoat.lean`: the saturation-hull minimum
  inherits the old weak cap margin. It does not provide the source's
  prescribed-row deletion bounds or reach tending to one.
- `TerminalCapNashEndpointTransport.lean`,
  `FinFourFullBoxExactPredecessorCapacity.lean`,
  `FinFourUnboundedExactBlockHazardCapacity.lean`, and
  `FullBoxExactPredecessorAbsorptionBudget.lean`: positivity/no-UE,
  finite full-box capacity, and the reversed chronological adapter were
  checked in place, including the distinguishing full-box definitions.
- `TerminalSemanticFinFourMinimumFiberLinearAbsorptionDefect.lean`:
  the existing approximate-root basin concerns roots against prescribed
  minimum payoffs, not the incoming prescribed row from the possibly
  off-minimum continuation in (15).

No matching theorem for the **first large prescribed row of every
near-minimizer**, with O(ε) prior charge, reach tending to one, and both
semantic vectors preserved, was found in this bounded source set. That
is the strongest candidate addition. This is not an exhaustive novelty
claim and does not establish the missing support-Nash consumer.

The recent strengthened MAX results do not subsume or justify this
argument: all MAX-minimum debts tying at m does not make their sum 4m a
global SUM minimum. Conversely the SUM equality orbit here does not
supply a MAX-region competitor.

Recommendation: retain the corrected carrier/source statement for a
second independent review. Do not export as a completed approximate
packet producer or infer that the final row solves the conjecture.
