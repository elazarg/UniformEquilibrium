# Adversarial review of NONZERO_PERSIST_ATTEMPT_2

Reviewer: Codex Adversary

## Verdict

Theorems 1--3 are correct as ordinary mathematics after minor statement and
handoff corrections. I found no fatal counterexample.

The packet recommendation is nevertheless **DO NOT EXPORT as a completed
answer**. The final source-to-return/source-hull lemma is still unproved, and
the present “equivalent” wording promotes two sufficient producer targets to
a completeness claim. The generic lemmas are useful internal mathematics;
Theorem 3 strictly strengthens the selection mechanism in Attempt 1, but it
still consumes supplied exact blocks rather than producing them from the
Fin4 source.

## Theorem 1: pass, with a nonexclusive disjunction

The minimal-component argument is valid for a merely forward-invariant
compact set. If \(M\) is inclusion-minimal among nonempty compact sets with
\(S(M)\subseteq M\), then for every \(z\in M\),

\[
 \overline{\{S^n z:n\geq0\}}
\]

is itself nonempty, compact, forward invariant, and contained in \(M\);
hence it equals \(M\). Thus it is the **forward** orbit that is dense. No
negative-time/full-orbit density and no invertibility of the one-sided shift
is used. In fact minimality also gives \(S(M)=M\), since \(S(M)\) is another
nonempty compact forward-invariant subset, but the proof does not need this.

For nonempty relatively open
\(U=\{h>\delta\}\), the preimages \(S^{-n}(U)\) cover \(M\). A finite
subcover and the largest selected exponent give the stated uniform return
gap \(L\). Applying it at \(S^{m(L+1)}z\) gives one activity-\(>\delta\)
date in each disjoint interval, hence divergent total activity and one fixed
divergent marginal by finiteness.

If \(h\equiv0\), forward invariance makes every root at every date
all-Continue. Bellman gives \(v_t=v_{t+1}\), and exact Nash gives
\(r_i(\{i\})\leq b_i\). Every such constant spine is an invariant singleton,
so minimality forces \(M\) to be one singleton.

Mandatory wording correction: the two conclusions in (A) are not mutually
exclusive for the original \(K\). In the one-player table with singleton
reward \(1\) and value \(b=1\), both the constant all-Continue spine and the
constant sure-Quit spine are exact fixed spines. Their two-point union is
compact and invariant; it contains both a phantom and a persistent spine.
Replace “exactly the following alternative” by “at least one of the
following holds” or explicitly call it an inclusive disjunction.

The source-facing corollary is correct: if \(K\) contains no constant
all-Continue spine, its minimal component cannot be the zero-activity case.

## Theorem 2 and plateau rigidity: pass

All marginal summability implies

\[
 \sum_t\alpha_t<\infty,\qquad
 \lVert v_t-v_{t+1}\rVert_\infty\leq2K\alpha_t.
\]

Thus \(v_t\to b\). Every marginal hazard tends to zero, so \(x_t\to C\).
For every fixed \(k\),

\[
 (v_{n+k},x_{n+k})\longrightarrow(b,C),
\]

which is exactly convergence of the whole shifted spine in the countable
product topology. Closedness of exact Nash at
\((v_{t+1},x_t)\to(b,C)\) gives \(C\) exact Nash against \(b\), equivalently
\(r_i(\{i\})\leq b_i\).

The Fin4 plateau rigidity is also correctly oriented at the tail. Once
\(v_{t+1}\) enters the open uniqueness tube, exact Nash forces \(x_t=C\),
and Bellman forces \(v_t=v_{t+1}\). The late constant equals the limit \(u\);
backward induction at tail \(u\) makes the entire spine the \(u\)-phantom.
This is exactly the content of
exactNashBellmanPath_eq_anchor_of_tendsto_unique_allContinue.

One concluding sentence must be weakened. An arbitrary all-summable spine
need not itself be a literal phantom; only its whole-shift limit is one.
For example, at a one-player continuation equal to its singleton reward,
the exact roots with hazards \(2^{-(t+1)}\) give a nonconstant all-summable
root spine whose shifts converge to the phantom. Therefore “the
zero-persistent alternative has been reduced completely to a literal
phantom fixed component” is true for **minimal components**, not for every
source orbit. Outside the plateau-limit case, a nonminimal transient can
remain.

## Theorem 3: pass, with explicit constants and adapter

The chronology is correct. In a repeated copy of

\[
 w_0,y_0,\ldots,y_{L-1},w_L,
\]

the last root originally expects \(w_L\), while the next flattened
annotation is \(w_0\). The Bellman seam is at most
\(\Delta=\lVert w_L-w_0\rVert_\infty\), and its mixed unilateral root-Nash
defect is at most \(2\Delta\).

With \(m_n=\lceil1/H_n\rceil\),

\[
 m_nH_n\geq1,\qquad
 m_n\Delta_n\leq\Delta_n/H_n+\Delta_n.
\]

Both terms on the right tend to zero. Common endpoint convergence also
permits a fast subsequence with summable inter-group distances. Hence the
flattened roots have divergent total marginal activity, while Bellman and
mixed-root-Nash errors are absolutely summable. One fixed player is
persistent.

For a completely quantified proof, set for example
\(\varepsilon_0=\varepsilon/8\) if the geometric series is indexed from
zero. The total seam-distance budget is then below \(4\varepsilon_0\);
the Bellman-error sum is below \(\varepsilon\), and the Nash-error sum,
which is at most twice that distance budget, is below \(\varepsilon\).
The present phrase “a fixed numerical factor” is insufficient for an export
proof but is not a mathematical gap.

Mandatory consumer correction: Theorem 3 produces an **approximate**
Nash--Bellman spine. It cannot be fed directly to either
IsCanonicalExactQuittingNashBellmanSpine.isUniformEquilibriumPayoff_soloReward_of_uniquePersistent
or the exact chronological spine adapter. It must invoke the ordinary
summable-residual adapter audited in Attempt 1:

- with two fixed persistent labels, use the diagonal artificial semantic
  chain and its summable prescribed/cap seams, then
  quittingGame_exists_uniformEquilibriumPayoff_of_summableSeams_all_errors;
- with exactly one persistent label, use literal terminal values, Bellman
  tail shadowing, and
  isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits.

The unique-label branch also requires punishment normality of its owner.
The Fin4 no-uniform hard residual supplies normality for all players. Only
after this handoff is it justified to say that Never and arbitrarily late
behavioral deviations are covered. Theorem 3 by itself controls local
one-row deviations only.

## Strict-ray orientation: pass

For the forward exact-cap ray, the checked fields and cap-Nash transport give

\[
 c_{t+1}=F_{x_t}(c_t),\qquad x_t\text{ exact Nash against }c_t.
\]

Thus the chronological block is correctly read backwards:

\[
 c_b,x_{b-1},c_{b-1},\ldots,x_a,c_a.
\]

Its root order, charge, and endpoint seam in (20) are correct. The cap
identity is not a consequence of the semantic-pair forward field alone; it
uses
quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash.
That declaration should be named in the source correspondence.

The scalar ballistic example correctly shows that cap convergence alone
does not imply normalized near-return.

There is a stronger checked boundary worth recording. For late strict-ray
windows, summability makes \(H_n\to0\). Closing an exact open block by its
endpoint seam makes a QuittingReturnedProductBlock with Bellman error
\(O(|I|\Delta_n)\) and endpoint regret \(O(|I|\Delta_n)\). Hence
\(\Delta_n/H_n\to0\) would trigger
hasHomogeneousSimplexSolution_of_vanishing_returnedBlocks, contradicting the
Fin4 hard residual. This is consistent with Theorem 3—(NR) is a winning
contradiction certificate—but it shows that (NR) is not a consequence of
mere convergence and that the checked obstruction is sharper than the
scalar illustration.

## Attempt 1 comparison

Attempt 2 subsumes the compact extraction of Attempt 1 as follows. Attempt 1
extracts exact blocks with

\[
 H_n\geq1,\qquad
 w^n_0,w^n_{L_n}\to b,\qquad
 \Delta_n\to0.
\]

Therefore \(\Delta_n/H_n\leq\Delta_n\to0\), so these blocks satisfy Theorem
3. Conversely, Theorem 3 can work with \(H_n\to0\): repetition amplifies each
small block to unit charge while the normalized seam remains summable. It is
therefore strictly more general than unbounded finite capacity.

Attempt 2 does not replace Attempt 1's downstream adapter. It relies on that
adapter to turn the summable-error persistent chronology into unrestricted
behavioral uniform equilibrium.

## “Equivalent” wording and packet recommendation

The final boxed source lemma is **sufficient**, not proved equivalent. Either
arm would solve the named selection question:

- (NR) gives a summable-error persistent chronology by Theorem 3 and the
  Attempt 1 adapter;
- a phantom-free compact forward-invariant exact-spine hull gives an exact
  persistent spine by Theorem 1.

No converse or strategy-class completeness theorem shows that every valid
Fin4 proof, every source regeneration, or every summable-seam construction
must yield one of those two objects with the required source provenance.
A proof could instead produce terminal approximate Nash profiles, a
renewable source rank, or a different executable consumer. Replace
“equivalent” by:

> It would suffice to prove either of the following two source lemmas.

The draft does not answer
FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION: its source-to-(NR)/hull producer is
explicitly left open. Under exports/README.md, a supplied-block verifier or
conditional compact-hull consumer with its actual-data hypothesis open is
not an exportable packet. Recommendation: retain Theorems 1--3 internally,
fold Theorem 3 into the Attempt 1 line as the normalized strengthening, and
do not send a packet for formalization as a completed question answer.

## Narrow source audit

Inspected declarations:

- IsQuittingNashBellmanEdge,
  quittingNashBellmanBox_isCompact,
  isClosed_quittingNashBellmanEdgeGraph, and
  exists_bounded_exact_quittingNashBellmanSpine in
  UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean;
- IsCanonicalExactQuittingNashBellmanSpine and
  canonicalPhantom_isExactQuittingNashBellmanSpine in
  UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanClockReduction.lean;
- all_marginalQuitHazards_summable_of_no_uniformPayoff in
  UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardNashBellmanSpine.lean;
- exists_finFour_strictMinimumPlateau_openDebtHomotopyTube_of_no_uniformPayoff
  in
  UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean;
- exactNashBellmanPath_eq_anchor_of_tendsto_unique_allContinue in
  UniformEquilibrium/Quitting/Bellman/Finite/AllContinueBasinRigidity.lean;
- QuittingForwardExactCapTail, its forward/exactNash fields, and
  QuittingForwardExactCapTail.totalHazard_summable in
  Research/Quitting/ForwardExactCapTailFlow.lean;
- quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash
  in
  UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean;
- QuittingReturnedProductBlock,
  relativeError_gap_of_noHomogeneous, and
  hasHomogeneousSimplexSolution_of_vanishing_returnedBlocks in
  UniformEquilibrium/Quitting/Stationary/ReturnedBlockTangentObstruction.lean;
- HasTwoPersistentQuittingMarginals.survival in
  UniformEquilibrium/Quitting/Paths/PersistentDeletedClockTwoLabel.lean;
- quittingGame_exists_uniformEquilibriumPayoff_of_summableSeams_all_errors in
  UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalSeamReduction.lean;
- abs_value_sub_soloReward_le_of_bounded_bellman and
  IsCanonicalExactQuittingNashBellmanSpine.isUniformEquilibriumPayoff_soloReward_of_uniquePersistent
  in
  UniformEquilibrium/Quitting/Classification/Existence/NormalUniquePersistentNashBellmanSpine.lean;
- isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits in
  UniformEquilibrium/Quitting/Cycles/ConditionedDeletedClockSoloCompletion.lean.

