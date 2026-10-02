# Chronological C1/C2 moving-window adapter and capacity boundary

Author: `CODEX_SOURCE_GATE`

Status: **ORDINARY C1 ADAPTER AND S.3 DELAYED-SWITCH DRAFT; SECTION 18 IS
ARCHITECTURAL VALIDATION ONLY; CAPACITY TRANSITION NOT SUPPLIED**

## Question and verdict

Fix a finite quitting table and a vanishing-Nash root-sequence family.  Pass
to the checked absorbing-completion diagonal and one chronological marked-law
limit.  At a nonterminal clock fixed point \(t\), ask whether one can select
one sequence of actual cuts \(s_n\), on one shared source subsequence, such
that for every fixed offset \(k\):

1. the actual row \(s_n+k\) is eventually reached with positive probability;
2. the global Nash error divided by that reach tends to zero; and
3. all fixed-offset roots and continuation values can be passed to one
   common infinite Nash--Bellman word.

The answer is **yes**, as ordinary mathematics.  In fact the current C1 cut
contains enough data to prove this without another source selection.  The
answer is also sharply negative for the intended nonzero-persistence use:

> Every fixed-offset limiting root is all-Continue.  The resulting exact
> Nash--Bellman word is a constant all-Continue phantom.  All positive
> chronological charge may escape to offsets tending to infinity.

Thus this adapter does not answer
`questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md`, not even after the
checked one-persistent Fin4 consumer.  It does identify the precise missing
datum for the finite-capacity branch: a marked positive-charge return whose
endpoint is still reached and whose child is extension-compatible with the
same source trace.

The new C1 files visible in the shared worktree are currently untracked at
repository head `a0842d13cbe2c1b2854ef4fb4e671b3970d1f089`.  I therefore use
their declaration statements as the source interface being reviewed, but do
not attach a Lean seal to the strengthening proved below.

## 1. Source interface inspected

The low source is
`QuittingRootSequenceVanishingNashFamily` in
`UniformEquilibrium/Quitting/Paths/VanishingNashRootSequenceFamily.lean`.
It retains actual root sequences \(X^m\), global errors \(e_m\to0\), and
Never probabilities tending to zero.  Its relevant checked consumers are:

- `reach_mul_stageDeviationGain_le`;
- `reach_mul_tailDeviationGain_le`;
- `reachedRootNash`; and
- `shiftedNash_of_reach_ge`.

The absorbing diagonal in
`UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionDiagonal.lean`
supplies completed sequences, completed errors tending to zero, exact global
Nash certificates at those errors, and cutoffs tending to infinity.  It only
preserves each **fixed absolute prefix** eventually; it says nothing by
itself about a moving cut plus all its forward offsets.

`ChronologicalLimit` in
`RootSequenceAbsorbingCompletionChronologicalLimit.lean` retains one shared
weak limit of the globally normalized marked chronological laws.  In the new
worktree file
`RootSequenceAbsorbingCompletionChronologicalC1.lean`, the structure
`ChronologicalPathTimeAdjacentCutLimit` and theorem
`nonempty_chronologicalPathTimeAdjacentCutLimit` give, at every
\(t\in\operatorname{pathTimes}\) with \(t\ne1\), one shared strict rank
sequence and cuts \(s_n\) for which

\[
 c_n(0)\longrightarrow t,
 \qquad c_n(1)\longrightarrow t,
\tag{1}
\]

where

\[
 c_n(k):=\operatorname{Clock}(X_n,s_n+k).
\]

The same cuts recover every cumulative coalition coordinate.  The theorem
`tailVector_tendsto_absorptionPathPayoff_of_cumulativeSubsequenceCuts`
therefore gives

\[
 V_n(0):=\operatorname{TailValue}(X_n,s_n)\longrightarrow
 z:=\operatorname{absorptionPathPayoff}(t).
\tag{2}
\]

The current C1 consumer uses only offsets zero and one.  The next section
shows that the same source ranks and cuts control every fixed offset.

## 2. Fixed-offset live-window theorem

### Theorem 2.1 -- all fixed offsets are live, with vanishing divided error

Use the shared source ranks and cuts above and let \(E_n\) be the completed
global Nash error on rank \(n\).  For every fixed \(k\in\mathbb N\),

\[
 c_n(k)\longrightarrow t,                                      \tag{3}
\]

\[
 R_n(k):=\Pr_{X_n}(\text{survive through }s_n+k)
          =1-c_n(k)\longrightarrow1-t>0,                       \tag{4}
\]

\[
 \frac{E_n}{R_n(k)}\longrightarrow0,                           \tag{5}
\]

and

\[
 a_n(k):=\operatorname{AbsorptionMass}(X_n(s_n+k))
          \longrightarrow0.                                   \tag{6}
\]

In particular, for each fixed \(k\), \(R_n(k)>0\) eventually and the actual
row at offset \(k\) is root Nash against its actual post-row tail at error
\(E_n/R_n(k)\to0\).

#### Proof

Let \(\mu_n\) be the completed chronological law on the shared ranks and
\(\mu\) its weak limit.  The C1 construction proves that the limiting clock
CDF \(F\) is continuous at \(t\).  This follows from the clock-gap law,
\(F(t)=t\), domination \(u\le F(u)\) below one, and \(t<1\).  Equivalently,
the clock marginal of \(\mu\) has no atom at \(t\).

Assume inductively that \(c_n(k)\to t\).  Let

\[
 m_n(k):=c_n(k+1)-c_n(k).
\]

The finite identity
`clock_succ_sub_clock_eq_sum_stageCoalitionMass` identifies \(m_n(k)\)
with the actual, unconditional coalition mass absorbed at row \(s_n+k\).
For any continuity points \(\ell<t<u\), the row clock belongs to
\((\ell,u)\) eventually.  Hence \(m_n(k)\) is bounded by the total
chronological mass of that window.  Weak convergence at the two null
boundaries gives

\[
 \limsup_n m_n(k)\le F(u)-F(\ell).
\]

Let \(\ell\uparrow t\) and \(u\downarrow t\) through continuity points.  The
continuity of \(F\) at \(t\) yields \(m_n(k)\to0\).  Therefore

\[
 c_n(k+1)=c_n(k)+m_n(k)\longrightarrow t,

\]

which proves (3) by induction.  Rows remain inside the finite completion
eventually: a row beyond the sure-solo cutoff has clock one, incompatible
with (3) and \(t<1\).

Equation (4) is the definition of the clock.  Since \(E_n\to0\), (5) follows
by division by the positive limit \(1-t\).  Finally,
`sum_stageCoalitionMass_eq_survival_mul_absorptionMass` gives

\[
 m_n(k)=R_n(k)a_n(k).
\]

Equations (4) and \(m_n(k)\to0\) prove (6).  Reached-stage Nash is exactly
`isεQuittingRootNash_tailVector_of_isεQuittingRootSequenceNash`, or the
source wrapper `reachedRootNash`.  This covers all mixed one-row
replacements; the global source certificate continues to cover arbitrary
behavioral tail replacements in its weighted form.  ∎

### Quantifier audit

The conclusion is

\[
 \forall k\;\exists N_k\;\forall n\ge N_k,\quad R_n(k)>0.
\]

It is not a uniform lower bound simultaneously over all \(k\).  This is the
right quantifier for convergence in the countable product topology, but it
does not control a moving offset \(k=k_n\to\infty\).

## 3. The one-shared-word limit is necessarily phantom

For a fixed player \(i\),
`quittingQuitProbability_le_absorptionMass` gives

\[
 0\le q_i(X_n(s_n+k))\le a_n(k)\longrightarrow0.
\]

Thus for every fixed \(k\), the entire product root converges to
all-Continue.  This happens along the same ranks and cuts, so the root words
converge in the countable product topology:

\[
 (X_n(s_n+k))_{k\ge0}\longrightarrow(C,C,C,\ldots).            \tag{7}
\]

The actual suffix values obey the exact finite Bellman identity
`quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector`.  Their
one-row difference is bounded by a constant times \(a_n(k)\), using
`abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass`.
Together with (2) and (6), finite induction gives, for every fixed \(k\),

\[
 V_n(k)\longrightarrow z.                                    \tag{8}
\]

Now (5), (7), (8), and
`isεQuittingRootEndpointNash_of_tendsto` close every limiting row to exact
endpoint Nash.  Bellman continuity gives

\[
 z=F_C(z)=z.
\]

Consequently the common moving-window limit is the exact bounded spine

\[
 v_k=z,\qquad x_k=C\quad(k\ge0),                               \tag{9}
\]

and all of its marginal hazard series are zero.  Exact Nash at the
all-Continue row says precisely that every singleton own reward is at most
\(z_i\), recovering the lower continuous-clock clause proved by the current
C1 file.

This is not merely failure to choose a clever compact subsequence.  Equation
(6) holds before any root compactification, so every common fixed-column
subsequence has the same all-Continue root word.

The tracked stationary-prefix analogue makes the same boundary explicit.
`exists_quittingPositiveLiveStationaryPrefixLimit_with_liveMass_eq` in
`StationarilyGeneratedPositiveLiveLimit.lean` constructs a common repeated
root and a full countable continuation ray by exactly this positive-reach
division.  Its theorem `wellSupported_or_phantom` gives a completely
absorbing branch when the limiting root absorbs and the all-Continue phantom
when its live mass is one.  At a continuous chronological C1 cut, (6) forces
only the latter geometry.

## 4. Exact uniform-mesh regression

The following Fin4 example shows that arbitrarily large source charge can
escape every fixed offset while all C1/C2 ratios are perfect.

Take the four-player zero reward table.  For \(n\ge1\), let players
\(1,2,3\) always Continue.  At dates \(0\le j<n\), let player \(0\) Quit with
probability

\[
 q^n_j=\frac1{n-j},
\]

and use arbitrary roots after date \(n-1\).  Every behavioral payoff and
every deviation payoff is zero, so this is global exact Nash at error zero.
The last displayed row is sure Quit, hence Never has probability zero.

For \(0\le j\le n\), exact telescoping gives

\[
 S^n_j=\frac{n-j}{n},
 \qquad c^n_j=\frac jn,
 \qquad S^n_jq^n_j=\frac1n.                                  \tag{10}
\]

Thus the chronological clock law is the uniform mesh with mass \(1/n\) at
\(0,1/n,\ldots,(n-1)/n\), all marked by the singleton \(\{0\}\).  It converges
weakly to the uniform clock law \(F(t)=t\).  Fix \(t<1\) and take its finite
CDF cuts \(s_n=\lfloor nt\rfloor+1\) (up to the immaterial endpoint
convention).  For every fixed \(k\),

\[
 S^n_{s_n+k}\longrightarrow1-t,
 \qquad q^n_{s_n+k}\longrightarrow0,
 \qquad \frac{0}{S^n_{s_n+k}}=0.                              \tag{11}
\]

Nevertheless the marginal hazard remaining behind the cut is

\[
 \sum_{j=s_n}^{n-1}q^n_j
   =\sum_{m=1}^{n-s_n}\frac1m\longrightarrow\infty.           \tag{12}
\]

The terminal sure-Quit row occurs at a moving offset.  After it, reach is
zero and the suffix is behaviorally invisible.  Equations (11)--(12) prove
three separate no-go statements:

1. fixed-offset positive reach and divided-error convergence do not retain
   positive total charge in the product limit;
2. even unbounded finite hazard capacity can collapse to the all-Continue
   word under the naive chronological diagonal; and
3. post-zero-reach roots may be changed arbitrarily without affecting the
   original global Nash certificate.

The example already has a uniform payoff, so it is not a Fin4
counterexample.  It is an exact source/API regression.

## 5. Capacity-slice transition

There is a valid abstract rank calculation, but the current chronology does
not instantiate its hypotheses.

Let \(\tau\) be a trace node in a prepend-closed exact source graph and define

\[
 \Phi(\tau)=\sup\{H(B):B\text{ is a legal finite exact extension of }\tau\}.
\]

Suppose an exact high-debt-to-near-minimum return \(B\) goes from \(\tau\) to
\(\tau'\), its hazard charge satisfies

\[
 H(B)\ge\kappa>0,                                             \tag{13}
\]

and every legal extension of \(\tau'\) remains legal after prefixing by
\(B\).  Then

\[
 \Phi(\tau)\ge H(B)+\Phi(\tau')
              \ge\kappa+\Phi(\tau').                         \tag{14}
\]

If the exact debt ledger pays a drop \(\delta>0\) by an absorption event whose
per-unit effect is at most \(2D_{\max}\), with \(D_{\max}>0\), it gives the
advertised choice

\[
 \kappa:=\frac{\delta}{2D_{\max}}.
\tag{15}
\]

Since total absorption is at most total marginal hazard, (15) implies (13).
For finite \(\Phi\), (14) yields the genuine natural rank decrease

\[
 \left\lceil\frac{\Phi(\tau')}{\kappa}\right\rceil
 \le
 \left\lceil\frac{\Phi(\tau)}{\kappa}\right\rceil-1.          \tag{16}
\]

No attainment or upper semicontinuity of \(\Phi\) is used.  The substantive
hypothesis is extension compatibility.

### Why C1/C2 normalization does not realize (14)

The fixed-offset adapter proves local asymptotic exactness.  It does not
provide any of the following nonlocal data:

- a marked return endpoint \(r_n=s_n+L_n\) on the same source ranks;
- positive reach at that moving endpoint, or
  \(E_n/\operatorname{Reach}(r_n)\to0\);
- tightness of the charge \(H(X_n[s_n,r_n))\ge\kappa\) in finitely many
  offsets;
- an exact, rather than asymptotically exact, finite returned block carrying
  that charge; or
- a returned actual source node whose legal extensions remain legal after
  the displayed prefix.

If \(L_n\) were uniformly bounded, (6) would force the charge of the whole
return block to tend to zero.  Hence any positive-\(\kappa\) return visible
from a continuous C1 cut must have \(L_n\to\infty\) or must change the anchor.
The uniform-mesh regression shows that all its charge can then escape every
fixed column.

Worse, if reach becomes zero before or at the returned child, the weighted
global Nash inequality becomes

\[
 0\cdot\operatorname{Gain}\le E_n,
\]

and places no restriction on the subsequent suffix.  Treating such a suffix
as a fresh source can reset \(\Phi\) to an unrelated value, so (14) and (16)
are invalid.  Positive reach at each **fixed** offset does not exclude this:
the first zero-reach row may occur at \(L_n\to\infty\).

Thus reach/error normalization is sufficient to close each fixed limiting
row, but insufficient to preserve the nonlocal capacity accounting.

## 6. A sufficient packet for the missing transition

A source-facing capacity transition would be valid if it retained, on one
common rank sequence:

1. actual cuts \(s_n<r_n\) and the literal intervening root words;
2. a uniform end-reach floor
   \(\operatorname{Reach}(r_n)\ge\rho>0\), or at least the exact ratio
   \(E_n/\operatorname{Reach}(r_n)\to0\);
3. a charge floor \(H(X_n[s_n,r_n))\ge\kappa\);
4. exactification that preserves the charge floor and the complete returned
   state, not only its prescribed payoff vector;
5. convergence or summably controlled decoding of payoff, unrestricted cap,
   terminal law, and every deleted-player law needed by the next consumer;
6. a closed ancestry statement saying that every legal extension of the
   returned child can be prefixed by the displayed block; and
7. a terminal dispatch at the first zero-reach row, rather than source
   regeneration through it.

For bounded \(r_n-s_n\), ordinary finite-product compactness plus (2) is
enough to close the local exact block, but it is incompatible with a positive
charge floor at the continuous C1 anchor.  For unbounded lengths, one needs a
separate charge-tight localization, a summable decoder, or a direct
source-level exact block theorem.  Countable product convergence is not that
theorem.

## 7. Relation to the maintained Fin4 questions

- **Nonzero-persistent spine:** no.  The source-attached limit (9) has no
  persistent marginal.  The construction therefore lands exactly in the
  excluded phantom boundary of
  `questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md`.
- **Finite-capacity branch:** (14)--(16) would give a real well-founded slice
  rank if an extension-compatible exact positive-charge return were supplied.
  The current chronological source supplies neither that return nor its
  reprojection.  Zero-reach rows and moving charge are the two exact failure
  modes.
- **Continuous-clock C1/C2:** the ordinary fixed-offset theorem strengthens
  the present lower-clause source audit, but it does not prove the open
  positive-singleton-derivative upper clause.  A positive derivative is an
  aggregate statement over a shrinking clock interval, whose number of
  discrete rows can diverge; (12) is the model obstruction to reading it from
  fixed columns.
- **Formalization value:** Theorem 2.1 is a clean source theorem worth a
  separate Lean handoff after the current C1 worktree files stabilize.  Its
  correct conclusion should explicitly include (6) and the resulting
  all-Continue word, so it cannot be mistaken for a persistence producer.

## 8. Narrow declaration list

Inspected source declarations:

- `QuittingRootSequenceVanishingNashFamily`, `reachedRootNash`, and
  `shiftedNash_of_reach_ge` in
  `UniformEquilibrium/Quitting/Paths/VanishingNashRootSequenceFamily.lean`;
- `QuittingRootSequenceAbsorbingCompletionDiagonal`, `rank_le_cutoff`,
  `eventually_prefix_eq`, `completedError_tendsto_zero`, and `nash` in
  `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionDiagonal.lean`;
- `ChronologicalLimit`, `law_tendsto`,
  `hasClockGap_chronologicalClockCDF`, and `le_pathTotal` in
  `UniformEquilibrium/Quitting/AbsorptionPath/RootSequenceAbsorbingCompletionChronologicalLimit.lean`;
- `ChronologicalJumpStageLimit` in
  `RootSequenceAbsorbingCompletionChronologicalA3.lean` and
  `ChronologicalJumpRootTailLimit.endpointNash` in
  `RootSequenceAbsorbingCompletionChronologicalJumpPerfection.lean`;
- the worktree declarations `QuittingFiniteCDFCut`,
  `ChronologicalPathTimeAdjacentCutLimit`,
  `nonempty_chronologicalPathTimeAdjacentCutLimit`,
  `tailVector_tendsto_absorptionPathPayoff_of_cumulativeSubsequenceCuts`,
  and `tendsto_rootAbsorptionMass_zero_of_adjacentClocks` in
  `FiniteRootSequenceCDFCut.lean` and
  `RootSequenceAbsorbingCompletionChronologicalC1.lean`;
- `clock_succ_sub_clock_eq_sum_stageCoalitionMass` and the exact open-window
  chronological-law formulas in
  `ChronologicalMarkedRootSequenceLaw.lean` and
  `ChronologicalMarkedRootSequenceJump.lean`;
- `isεQuittingRootEndpointNash_of_tendsto` in
  `UniformEquilibrium/Quitting/Bellman/Finite/EndpointNashClosed.lean`;
- `IsQuittingNashBellmanEdge` and
  `isClosed_quittingNashBellmanEdgeGraph` in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`;
- `IsCanonicalExactQuittingNashBellmanSpine` and
  `canonicalPhantom_isExactQuittingNashBellmanSpine` in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanClockReduction.lean`;
- `exists_quittingPositiveLiveStationaryPrefixLimit_with_liveMass_eq` and
  `QuittingPositiveLiveStationaryPrefixLimit.wellSupported_or_phantom` in
  `UniformEquilibrium/Quitting/Classification/Existence/StationarilyGeneratedPositiveLiveLimit.lean`;
- `quittingQuitProbability_le_absorptionMass` in
  `UniformEquilibrium/Quitting/Stationary/LiveMass.lean`; and
- `quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector` in
  `UniformEquilibrium/Quitting/Paths/SurvivalWindowLanding.lean`.

## Final packet-level verdict

**PASS** the shared moving-window reach/error adapter as ordinary
mathematics.  **FAIL** its use as a nonzero-persistent-spine or capacity-slice
producer.  The fatal issue is not local Nash closure: it is loss of positive
charge and source extension compatibility at a moving endpoint.  The
mandatory repair is the seven-field returned-capacity packet in Section 6.

## 9. Follow-up: the maximal common source packet is larger than Section 6 records

This section supersedes the first three missing-data bullets in Section 5.
The original one-cut C1 object does not store a return endpoint, but two
finite CDF cuts can be selected simultaneously on the same chronological
source ranks.  This supplies a literal positively charged moving block with
positive end reach.  It still does not supply exact root Nash or the strong
ancestry field.

Write

\[
 F(x)=\operatorname{chronologicalClockCDF}(\mu)(x)
\]

for the clock CDF of one `ChronologicalLimit`, and write \(G_S(x)\) for its
marked coalition CDF.  Fix

\[
 0\leq a<b<1,\qquad F(a)<F(b)<1,                         \tag{17}
\]

and assume that \(F\) is continuous at \(a\) and \(b\).

### Theorem 9.1 -- two-continuity-level charged source block

On one strict tail of the source ranks there are actual cuts
\(s_n<r_n\) in the same completed root sequence \(X_n\) such that

\[
 \operatorname{Clock}(X_n,s_n)\longrightarrow F(a),
 \qquad
 \operatorname{Clock}(X_n,r_n)\longrightarrow F(b),       \tag{18}
\]

and, for every coalition \(S\),

\[
 \operatorname{Cum}_S(X_n,s_n)\longrightarrow G_S(a),
 \qquad
 \operatorname{Cum}_S(X_n,r_n)\longrightarrow G_S(b).     \tag{19}
\]

Consequently

\[
 \operatorname{Reach}(r_n)\longrightarrow 1-F(b)>0,       \tag{20}
\]

and the completed global error \(E_n\) satisfies, uniformly over the whole
variable-length block,

\[
 \sup_{s_n\leq j<r_n}
   \frac{E_n}{\operatorname{Reach}(j)}
 \leq \frac{E_n}{\operatorname{Reach}(r_n)}
 \longrightarrow0.                                        \tag{21}
\]

Let

\[
 H_n=\sum_{j=s_n}^{r_n-1}
       \operatorname{AbsorptionMass}(X_n(j)).
\]

Then

\[
 \liminf_n H_n\geq
   \frac{F(b)-F(a)}{1-F(a)}>0.                              \tag{22}
\]

The same lower bound holds if \(H_n\) is replaced by total marginal hazard,
because the sum of the marginal Quit probabilities dominates the one-row
absorption mass.

#### Proof

Choose fixed numbers

\[
 \max\{a,F(a)\}<A<1,
 \qquad
 \max\{b,F(b)\}<B<1.
\]

Weak convergence and continuity at \(a,b\) give
\(F_n(a)\to F(a)\), \(F_n(b)\to F(b)\), and the corresponding marked
coordinate convergence.  Hence eventually \(F_n(a)<A\) and \(F_n(b)<B\).
Apply `nonempty_quittingFiniteCDFCut` twice inside the same finite absorption
certificate, once with \((a,A)\) and once with \((b,B)\).  Its `clock_eq` and
`cumulative_eq` fields give (18)--(19).  Since the limiting clocks are
strictly ordered, monotonicity of the finite clock forces \(s_n<r_n\)
eventually.  Discarding a finite initial set gives the asserted common
source ranks.  Thus no intersection of two independently chosen subsequence
images is being assumed.

Equation (20) is the clock/survival identity, and survival is decreasing in
the cut.  This proves (21) from `completedError_tendsto_zero` and the reached
root-Nash inequality.

Let \(S_n(j)=\operatorname{Reach}(j)\).  Exact product telescoping gives

\[
 \prod_{j=s_n}^{r_n-1}
   \bigl(1-\operatorname{AbsorptionMass}(X_n(j))\bigr)
   =\frac{S_n(r_n)}{S_n(s_n)}.
\]

The finite union bound \(1-\prod_j(1-h_j)\leq\sum_jh_j\) therefore gives

\[
 H_n\geq 1-\frac{S_n(r_n)}{S_n(s_n)}
   =\frac{\operatorname{Clock}(X_n,r_n)-
           \operatorname{Clock}(X_n,s_n)}
          {1-\operatorname{Clock}(X_n,s_n)}.
\]

Passing to the limit proves (22).  Every row of the block retains its actual
post-row tail, so its Bellman equation is exact and its root-Nash defect is
bounded by (21).  This is a uniformly approximate Nash--Bellman block even
when \(r_n-s_n\to\infty\).  It is not an exact Nash--Bellman block.  ∎

### Endpoint payoff decoding

Let \(P\) be the limiting completed prescribed payoff and define

\[
 A_x(i)=\sum_S G_S(x)r_S(i),
 \qquad
 z_x(i)=\frac{P(i)-A_x(i)}{1-F(x)}.                          \tag{23}
\]

The exact prefix/tail identity in `ChronologicalRootSequenceTail.lean`,
together with (18)--(20), gives

\[
 \operatorname{TailValue}(X_n,s_n)\to z_a,
 \qquad
 \operatorname{TailValue}(X_n,r_n)\to z_b.                 \tag{24}
\]

If \(a,b\in\operatorname{pathTimes}(\text{limit.path})\), then
\(F(a)=a\), \(F(b)=b\), continuity follows from the clock-gap argument in
the current C1 file, and (23) is exactly the named
`absorptionPathPayoff` at the two times.  In that specialization the fixed
offset theorem of Sections 2--3 still says that every fixed column after
\(s_n\) converges to all-Continue.  Hence the positive charge in (22) is a
genuinely moving-window quantity.

### Complete finite decorations can share the same further subsequence

At both cuts take the literal shifted root-sequence profiles.  Their
`quittingTerminalSemanticPair`s lie in the compact terminal semantic
carrier.  Their prescribed terminal outcome laws lie in the finite standard
simplex by `quittingTerminalOutcomeMass_mem_stdSimplex`.  For each player,
also set that player's roots to pure Continue and record the resulting
terminal outcome law.  There are only finitely many endpoints, players, and
finite outcome coordinates.  Product compactness therefore gives one
further strict subsequence on which simultaneously:

- both full terminal semantic pairs converge, including unrestricted
  continuation best-response caps;
- both prescribed terminal outcome laws converge; and
- every player-deleted terminal outcome law at both cuts converges.

The prescribed coordinates of the two semantic limits are already fixed by
(24).  This compactification preserves (18)--(22).  It is only convergence
of actual finite decorations.  It does not assert that their coordinatewise
root-word limit realizes any of these terminal laws, and it does not create
a closed source ancestry relation.

Thus one chronological object, after this ordinary two-cut refinement,
co-realizes fields 1, 2, 3, and the finite-outcome/terminal-semantic
compactness part of field 5 of Section 6.  It does not give tightness in a
strong stopping-law topology or actualize the limiting decorations by a
single limiting behavioral source.  It also gives exact Bellman identities
(half of field 4) and the literal equality

\[
 X_n[s_n,\infty)=X_n[s_n,r_n)\mathbin{+\!+}X_n[r_n,\infty)  \tag{25}
\]

for its one displayed child (a weak form of field 6).  Because (20) excludes
zero reach on the selected block, field 7 is locally avoided rather than
globally dispatched.

## 10. Audit of the nearest existing packets

No inspected declaration already combines the remaining fields.

1. `ChronologicalPathTimeAdjacentCutLimit` gives the one-cut payoff and
   divided-error interface.  Theorem 9.1 is the small missing two-cut
   ordinary adapter; it uses the lower finite `QuittingFiniteCDFCut`
   interface and one common chronological law.

2. `QuittingPositiveJointPrefixReachSource` and
   `SourceMatchedPunishmentEndpoint` retain a moving stationary-prefix
   horizon, positive limiting end reach, the literal punishment suffix, its
   unrestricted-behavior divided Nash error, and convergence of its full
   terminal semantic pair.  When its limiting joint survival is strictly
   below one, the repeated prefix also has a positive conditional absorption
   floor.  The declared hypothesis permits joint limit one, however, and the
   packet does not retain both endpoint laws or all deleted laws.

3. `QuittingPositiveJointPrefixReachPunishmentEndpoint.exactPrefixOrbit`
   is exact Nash--Bellman, but it is newly generated from the limiting
   semantic pair.  Its roots are not the literal source prefix, and its
   successor histories are not the source punishment suffixes.  Combining
   `SourceMatchedPunishmentEndpoint` with `exactPrefixOrbit` therefore does
   not combine source ancestry with exactification.

4. `reached_supportPurifiedPrefix_compatible` keeps a concrete reached
   finite window, recomputes exact Bellman values from its actual cutoff
   tail, and quantifies the seam.  Its roots are only support-approximately
   Nash.  The seam is proportional to
   `displacement * horizon`; the chronological hypotheses contain no bound
   forcing this product to zero for the moving length \(r_n-s_n\).  It also
   has no theorem preserving (22) under purification.

5. `QuittingReprojectionConcentratedPacket` and
   `QuittingReprojectionDiffuseWindowPacket` retain actual profiles, a moving
   window, positive normalized coalition mass, and a normalized coordinate
   defect.  They explicitly do not infer an exact-Nash policy or a common
   shifted-tail state.  They supply charge localization, not fields 2, 4, or
   6.

6. `QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily` starts after
   exactification: it assumes exact floor-admissible paths with a charge
   floor and payoff near-return, and its lasso consumer is complete.  It has
   no actual-source producer, end-reach certificate, terminal/deleted-law
   state, or ancestry fibre.

7. `capNashTailEscapeReturnSelection_retains_causalSuffixAtom` is the closest
   one-edge source-preserving gate.  Given an exact cap-Nash selection with
   positive Continue mass, it prefixes the literal continuation and retains
   its causal atom.  The file accurately labels the charged selection as a
   premise, not a producer.  It does not show that the generic chronological
   block selects such a root, nor that all legal extensions of the returned
   child remain prefixable.

8. The sure-solo absorbing completion and the chronological jump packet
   identify terminal/jump rows, but no current returned-capacity structure
   treats the first zero-reach row as a terminal leaf.  They do not justify
   regenerating a child after that row.

The maximal currently justified common packet is therefore

\[
 \boxed{\text{literal two-cut approximate block}
 +\text{positive end reach}+\text{positive charge}
 +\text{finite convergent decorations}+\text{one literal child}.}
\tag{26}
\]

The missing words in (26) are **exact root Nash** and **universal extension
ancestry**.

## 11. Exactification is not a consequence of the retained source fields

Here is a Fin4 regression in which all the analytic source fields of (26)
hold, every Bellman equation is exact, and the unrestricted behavioral Nash
error tends to zero, but no exact block can retain the literal end state and
the complete source terminal law.

Let the only nonzero reward coordinate be

\[
 r_{\{1\}}(0)=1;
\]

all payoffs of players \(1,2,3\), and all other rewards of player \(0\), are
zero.  For \(n\ge2\), use the following absorbing root sequence:

- for the first \(2n^2\) dates, player \(0\) Quits with probability
  \(1/n^2\), and everyone else Continues;
- at date \(2n^2\), player \(1\) Quits with probability \(1/n\);
- at date \(2n^2+1\), player \(2\) Quits surely.

Only player \(0\) can improve.  By never quitting during the first block,
that player obtains at most \(1/n\), while all other terminal outcomes pay
that player zero.  Hence the displayed root sequence is global
\(1/n\)-Nash against arbitrary behavioral deviations, and Never has mass
zero.

Take \(s_n=0\) and \(r_n=n^2\).  Then

\[
 \operatorname{Reach}(r_n)=\left(1-\frac1{n^2}\right)^{n^2}\to e^{-1},
 \qquad
 \sum_{j=s_n}^{r_n-1}\sum_iq_i(X_n(j))=1.                  \tag{27}
\]

All prescribed and deleted terminal outcome laws converge, since they live
in finite simplexes.  The limiting clock CDF is the identity on the diffuse
part containing \(0\) and \(1-e^{-1}\), so these are exactly two continuity
levels of Theorem 9.1.

The actual child at \(r_n\) gives player \(0\) the strictly positive payoff

\[
 \left(1-\frac1{n^2}\right)^{n^2}\frac1n.                 \tag{28}
\]

Consider an exact Nash--Bellman replacement block which keeps that child,
has positive reach to it, and preserves the source terminal outcome law.
All rewards are nonnegative.  At every row, positive reach to the child
makes player \(0\)'s Continue payoff strictly positive.  If player \(0\)
Quits, the absorbing coalition contains player \(0\), so its payoff is zero.
Exact root Nash therefore forces player \(0\)'s Quit probability to be zero
at every replacement row.  But the source block assigns singleton

\[
 1-\left(1-\frac1{n^2}\right)^{n^2}\to1-e^{-1}             \tag{29}
\]

positive terminal mass to \(\{0\}\).  No such exact replacement can preserve
that law.

This regression does not rule out an unrelated limiting exact block after
changing the child by a vanishing payoff amount; indeed the incentive gap in
(28) tends to zero.  It proves the narrower and relevant API statement:
positive reach, positive moving charge, exact Bellman evaluation, complete
law compactness, and vanishing unrestricted Nash error do not produce a
**literal source-state exactification**.  A decoder which changes the state
must quantify that change and prove ancestry separately.

## 12. Universal ancestry is independent even when exactification is free

Use the zero-reward Fin4 table, where every root and every Bellman word at
payoff zero is exact.  Give two history tags \(A\) and \(B\) identical payoff,
cap, terminal-law, deleted-law, and root decorations.  Permit a charged edge
from a parent history to the \(A\)-tagged child, and give that child only a
short continuation.  Give the numerically identical \(B\)-tagged state a
long charged continuation which is forbidden after the parent history.

The literal displayed child equality (25), all exactness fields, and all
finite semantic/law decorations are identical under the two tags.  If the
tags are collapsed and the long \(B\)-continuation is used in the child's
capacity, the inequality

\[
 \Phi(\tau)\geq H(B)+\Phi(\tau')
\]

is false: the long continuation is not prefixable after the displayed edge.
On the correctly tagged history graph it is simply not an extension of the
\(A\)-child.  Thus no semantic, probability, reach, charge, or exact-Nash
field implies universal extension ancestry.  This is independent of the
exactification issue in Section 11.

## 13. The isolated remaining producer question

After Theorem 9.1, the generic clock question is no longer whether a common
moving block, positive end reach, or positive charge can be retained.  The
precise Fin4 source question is the following.

> **Charge-preserving exact history retraction.**  In the positive-minimum
> Fin4 hard residual, does every two-cut block furnished by Theorem 9.1 (or a
> cofinal positive-charge subfamily of them) admit, on one common
> subsequence, an exact punishment-floor Nash--Bellman block of charge at
> least half the bound in (22), whose endpoint payoff/cap and prescribed plus
> every deleted terminal law differ by a controlled vanishing error, and
> whose returned child is a node of a chronological history port for which
> every legal child extension remains legal after prefixing by that exact
> block?

For iterative use, the decoder errors must be summable or have an explicit
triangular summability bound.  The ancestry clause must concern the full
history tag, not only equality of endpoint payoff vectors.  A negative/zero
reach alternative must terminate at the first such row rather than declare
its arbitrary suffix to be a new child.

An affirmative answer is one producer theorem which fills fields 4 and 6;
field 7 is avoided on every positive-end-reach transition and handled by a
separate terminal leaf.  Theorem 9.1 then fills fields 1--3, while the compact
decoration step fills field 5.  Neither
`reached_supportPurifiedPrefix_compatible` nor
`exactPrefixOrbit` proves this retraction: the former is not exact root Nash
and has a moving-length seam, while the latter discards the literal source
word.

Sections 11--12 show that this producer cannot follow from the seven numeric
or topological decorations alone.  It must use a specific Fin4 selection,
reprojection, or history construction.  No such declaration was found in
the inspected chronological, positive-joint, terminal-reprojection, or
positive-minimum packets.

## 14. Updated handoff and declaration list

Theorem 9.1 is a small formalizable adapter.  A useful Lean structure would
store both cuts on one rank sequence, their order, both clock and cumulative
limits, the end-reach limit, and the finite-block conditional absorption
lower bound.  Its proof should use:

- `QuittingFiniteCDFCut`, `nonempty_quittingFiniteCDFCut`, and their
  `clock_eq`/`cumulative_eq` fields in
  `FiniteRootSequenceCDFCut.lean`;
- `ChronologicalLimit.law_tendsto`,
  `tendsto_chronologicalClockCDF_of_continuousAt`, and
  `tendsto_chronologicalCoalitionCDF_of_clockCDF_continuousAt` in the
  chronological-limit stack;
- `completedError_tendsto_zero` and `nash` from the absorbing completion
  diagonal;
- the clock/survival and finite product identities, plus the elementary
  union bound; and
- `quittingRootSequenceTerminalValue_eq_prefixReward_add_survival_mul_tail` from
  `ChronologicalRootSequenceTail.lean` for (23)--(24).

Additional interfaces inspected in this follow-up were:

- `QuittingPositiveJointPrefixReachSource`, `punishment_nash_of_joint_pos`,
  and `punishmentNashError_tendsto_zero` in
  `PositiveJointPrefixReachEndpoint.lean`;
- `SourceMatchedPunishmentEndpoint` and
  `nonempty_sourceMatchedPunishmentEndpoint` in
  `PositiveJointSourceMatchedSummablePortPhantom.lean`;
- `QuittingPositiveJointPrefixReachPunishmentEndpoint.exactPrefixOrbit` in
  `PositiveJointEndpointSequentialReduction.lean`;
- `reached_supportPurifiedPrefix_compatible` and
  `QuittingSourceMatchedSupportPrefixAt` in
  `FinitePrefixCompatibility.lean` and
  `ReachedPrefixCompactification.lean`;
- `QuittingReprojectionConcentratedPacket`,
  `QuittingReprojectionDiffuseWindowPacket`, and
  `exists_concentrated_or_diffuseWindowPacket` in
  `TerminalSemanticResetReprojectionTemporalSplit.lean`;
- `QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily` in
  `CumulativeChargeNearReturn.lean`;
- `capNashTailEscapeReturnSelection_retains_causalSuffixAtom` in
  `Research/Quitting/CausalTailEscapeReturnGate.lean`; and
- `quittingTerminalSemanticCarrier_isCompact`,
  `quittingTerminalOutcomeMass_mem_stdSimplex`, and
  `quittingExtendDeletedRoots` in the terminal-semantic and player-deletion
  source files.

### Updated verdict

**PASS** fields 1--3 and the finite-outcome/terminal-semantic compactness
part of field 5 after the two-cut adapter.  **PASS** exact Bellman
compatibility and one literal child only as partial fields.  **FAIL** strong
stopping-law/source actualization, exact root-Nash source retraction,
universal extension ancestry, and a total zero-reach dispatch.  The
remaining issue is the single Fin4-specific producer question in Section 13,
whose exactification and ancestry clauses are logically independent by
Sections 11--12.

## 15. Comparison with NONZERO_PERSIST_ATTEMPT_1, Followup 1, Section 6

### The two-cut packet does not supply the assumed composable chronology

Followup 1 Section 6 begins with “one composable source-provenant chronology”
of uniformly escaped tails \(z_n\), chooses a maximal exact cap-Nash root
\(x_n\) at each tail, and then charges all selected roots to one finite
capacity \(C_0\).

Theorem 9.1 does not instantiate that hypothesis.  It gives:

- for each rank \(n\), one literal contiguous word between two cuts of the
  same completed source profile;
- exact Bellman evaluation against that profile's actual tails;
- root-Nash error tending uniformly to zero over that word; and
- one literal child suffix at the right cut.

It does not give:

- exact cap-Nash edges inside the word;
- equality of the returned profile at rank \(n\) with the starting source
  state at rank \(n+1\);
- a common proof-relevant origin and compact exact edge graph containing all
  such returned edges;
- an embedding of every legal extension of the right child after the left
  block; or
- a bound which charges roots selected independently at different ranks to
  one path capacity.

The checked self-shift of a FinFourUniformEscapePacket does not fill this
gap either.  Its drop operation removes the first row of the **index
stream**: row \(n\) of the dropped packet is definitionally row \(n+1\) of
the old packet.  It does not say that

\[
 \operatorname{returnedProfile}(n,x_n)
 =
 \operatorname{continuationProfile}(n+1),                  \tag{30}
\]

or that the independently selected roots \(x_n\) form a path in one exact
source graph.  exists_maximalCapNash_halfFloorDispatch is explicitly a
same-tail one-root dispatch and explicitly not a reset compiler.

There is also an orientation obligation.  A root selected against the tail
\(z_n\) gives the chronological edge

\[
 T_{x_n}z_n \xrightarrow{x_n} z_n,
\]

not an edge from \(z_n\) to an independently chosen \(z_{n+1}\).  A
composable sequence must explicitly identify \(T_{x_n}z_n\) with the
preceding history state, or reindex a predecessor chain and prove that every
finite reversal is one legal chronological path.  The atlas's cofinal rank
stream supplies neither identification.

Thus the Followup 1 Section 6 hypothesis is a useful conditional history-port
interface, but it is stronger than both the actual uniform-escape packet and
the two-cut chronology.  Without it, finite capacity of each available
finite block does not imply

\[
 \sum_n\operatorname{Abs}(x_n)<\infty.                     \tag{31}
\]

Independent one-edge blocks can all have the same positive charge while
each has finite individual capacity.

### Conditional audit of the undercharge calculation

Assume the stronger hypothesis literally: the \(x_n\) are successive edges
of one exact source-history path, every finite prefix has total marginal
hazard at most \(C_0\), the states remain in one compact closed
proof-relevant space, and \(D(z_n)\ge D_*+\delta\).
Then the following part of the argument is correct.

1. A \(\delta/2\)-return has

   \[
    \operatorname{Abs}(x_n)\ge
      \kappa_\delta=\frac{\delta}{2D_{\max}},
   \]

   by exact debt scaling.  Since \(h(x_n)\ge\operatorname{Abs}(x_n)\), at
   most \(\lfloor C_0/\kappa_\delta\rfloor\) such path edges occur.

2. On an infinite remaining undercharge tail,

   \[
    \sum_n\operatorname{Abs}(x_n)
    \le \sum_n h(x_n)\le C_0,
   \]

   so \(\operatorname{Abs}(x_n)\to0\).

3. For every player \(i\), not only for the one blocker returned by the
   disjunction, whenever

   \[
    g_{n,i}=r_i(\{i\})-(z_n)^{\rm cap}_i>0,
   \]

   the fixed-tail absorption estimate applied to the maximal exact root
   gives

   \[
    \frac{g_{n,i}}{g_{n,i}+2M}
      \le\operatorname{Abs}(x_n).                           \tag{32}
   \]

   Therefore every positive limiting singleton gap is impossible.  Along a
   compact numerical subsequence \(z_n\to z_\infty\),

   \[
    r_i(\{i\})\le(z_\infty)^{\rm cap}_i
   \]

   for all \(i\), and the all-Continue root is exact Nash against the limiting
   cap.  Continuity of debt also retains
   \(D(z_\infty)\ge D_*+\delta\).

The constants and inequality directions in this conditional calculation are
correct.  Equation (32) should be presented as a fresh application of the
fixed-tail gap bound for each \(i\); the one blocker contained in the
dispatch statement alone does not syntactically quantify it for every
player.

### The conclusion is weaker than a retained strict-inert omega-source

The calculation proves an off-minimum **all-Continue-exact cluster**.  Two
further conclusions in Followup 1 Section 6 do not follow without extra
fields.

First, all-Continue exactness does not imply that the exact cap-Nash
correspondence is the singleton all-Continue root.  A positive-absorption
exact root can appear discontinuously at the limiting cap even though the
selected maximal roots have absorption tending to zero.  The checked theorem
exists_offMinimum_retainedLaw_allContinue_or_supportEntry records the
correct residual disjunction:

\[
 \text{unique all-Continue}
 \quad\text{or}\quad
 \text{a positive-absorption support-entry root}.          \tag{33}
\]

The zero-reward table is the elementary boundary test: all-Continue is exact,
but so is every other root.  Hence “all-Continue-inert” is valid only if
“inert” means merely that all-Continue is one exact root.  It is not valid
for the normalized **strict-inert** packet until the uniqueness arm of (33)
has been selected or the support-entry arm has been consumed.

Second, compact convergence of terminal semantic pairs and finite outcome
laws does not by itself give a retained actual omega-source.  The current
uniform-escape continuation is the post-row tail.  Its checked outcome-law
provenance is real, but the fixed positive marked atom lies at the preceding
row, not inside that continuation.  This is the same pre-tail/post-tail
separation already recorded in the export gate for
POSITIVE_MINIMUM_EXACT_PREFIX_CLOCK_ESCAPE.  Moreover, neither the atlas
stream nor Theorem 9.1 supplies a compact closed ancestry space whose limit
is an actual behavioral descendant.  At most one obtains a carrier cluster
unless strategic-law tightness or a source-faithful decoder is added.

Therefore the sound conclusion from the present checked data is

\[
 \boxed{
 \begin{array}{c}
 \text{if a composable finite-capacity exact history port is supplied,}\\
 \text{then an infinite undercharge path has an off-minimum}\\
 \text{all-Continue-exact semantic/law cluster,}\\
 \text{with residual unique-inert versus support-entry.}
 \end{array}}
 \tag{34}
\]

Calling this a retained strict-inert omega-source additionally requires:

1. the composable source-history/ancestry producer;
2. source-closed actualization of the limiting semantic/law point;
3. retention of whatever marked atom the next consumer uses; and
4. selection of the uniqueness arm in (33), or a consumer for support entry.

These are precisely the source operations absent from the two-cut packet.

## 16. Exact Fin4 charge-loss regression for history retraction

Section 11 showed that a literal complete-law retraction can fail.  The
following stronger regression has zero Never mass and does not rely on
preserving the terminal coalition law.  It shows quantitatively that an exact
block with the same child and an asymptotically source-matched parent must
lose **all** of the source charge.

### The reward table and actual source

Use players \(\operatorname{Fin}4\).  Define

\[
 r_S(0)=
 \begin{cases}
  0,&0\in S,\\
  1,&0\notin S,
 \end{cases}
 \qquad
 r_S(i)=0\quad(i=1,2,3).                                   \tag{35}
\]

Thus player \(0\) receives zero when quitting and one whenever absorption is
caused only by opponents.  Every other player is payoff-indifferent.

For \(n\ge2\), let \(q_n=1/n\).  The actual root sequence is:

1. for dates \(0,\ldots,2n-1\), only player \(0\) Quits, with probability
   \(q_n\);
2. at date \(2n\), only player \(1\) Quits, with probability \(1/n\);
3. at date \(2n+1\), player \(0\) Quits surely.

Never has probability zero.  Players \(1,2,3\) always receive zero.  Player
\(0\)'s maximum payoff under any behavioral deviation is at most \(1/n\),
attained by surviving until the possible singleton-\(\{1\}\) absorption.
The displayed strategy gives a nonnegative payoff.  Therefore the entire
root sequence is global \(1/n\)-Nash against arbitrary behavioral deviations.

Take

\[
 s_n=0,\qquad r_n=n.
\]

The displayed first-half block has

\[
 H_n=\sum_{j=0}^{n-1}\sum_iq_i(X_n(j))=1,                  \tag{36}
\]

\[
 \operatorname{Reach}(r_n)
   =\left(1-\frac1n\right)^n\longrightarrow e^{-1},        \tag{37}
\]

and exact Bellman values.  Its child payoff and parent payoff in coordinate
\(0\) are respectively

\[
 b_n=
 \left(1-\frac1n\right)^n\frac1n,
 \qquad
 a_n=
 \left(1-\frac1n\right)^{2n}\frac1n.                       \tag{38}
\]

Both are positive and tend to zero, with \(a_n<b_n\).  The early stage
masses form the usual fine clock mesh.  The limiting clock CDF is the identity
through the diffuse interval ending at \(1-e^{-2}\); hence the cuts at clock
levels \(0\) and \(1-e^{-1}\) are continuity-level cuts of Theorem 9.1.

### Every exact retraction close to the parent has vanishing charge

Consider any finite exact Nash--Bellman block for the same reward table whose
terminal child has payoff coordinate \(b_n\).  Assume its initial payoff
coordinate \(\widehat a_n\) is asymptotically source-matched:

\[
 |\widehat a_n-a_n|\longrightarrow0.                       \tag{39}
\]

At every row of this exact block, player \(0\)'s successor value is positive.
Indeed it is positive at the child.  If it is positive at a successor, then
player \(0\)'s pure Quit payoff is zero, whereas pure Continue gives either
that positive successor value when all opponents Continue, or the reward one
when an opponent Quits.  Continue is strictly better.  Exact root Nash
therefore forces

\[
 q_0(\widehat x_{n,j})=0                                   \tag{40}
\]

at every row, and backward Bellman evaluation keeps coordinate \(0\)
positive.

Let

\[
 \widehat H_n
   =\sum_j\sum_i q_i(\widehat x_{n,j})
\]

be the exact block's total marginal charge, and let \(A_n\) be its
conditional probability of absorption before reaching the child.  By (40),
all absorption is caused by the three opponents.  At a row, if \(h_j\) is
the probability that at least one opponent Quits, then

\[
 \sum_{i\ne0}q_i(\widehat x_{n,j})\le3h_j.
\]

Consequently

\[
 A_n
 =1-\prod_j(1-h_j)
 \ge1-\exp\left(-\sum_jh_j\right)
 \ge1-\exp(-\widehat H_n/3).                               \tag{41}
\]

Every such opponent absorption pays player \(0\) exactly one, while reaching
the child pays \(b_n\).  Exact Bellman evaluation gives

\[
 \widehat a_n=A_n+(1-A_n)b_n\ge A_n.                       \tag{42}
\]

Equations (38)--(39) imply \(\widehat a_n\to0\), so (42) gives \(A_n\to0\).
Equation (41) then forces

\[
 \widehat H_n\longrightarrow0.                             \tag{43}
\]

In particular, for every fixed \(\theta>0\), no sufficiently late exact
retraction with the same child and vanishing parent-state error can retain
charge \(\theta H_n=\theta\).

### What the three proposed exactification mechanisms do here

- **Finite dynamic debt/payoff minimization.**  Backward exact root
  selection always exists.  Choosing all-Continue at every row keeps the
  parent near (38), but its charge is zero.  Choosing opponent absorption
  creates exact charge, but (41)--(42) moves player \(0\)'s parent payoff a
  fixed positive distance away.

- **Exact cap-root replacement.**  The source charge is carried by player
  \(0\).  Exactness deletes that marginal at every row by (40).  Moving the
  charge to an indifferent opponent changes the parent payoff from a
  survival-discounted \(b_n\) toward one; it is not a source-state
  replacement.

- **Constrained-root homotopy.**  The original charged roots are individually
  close to all-Continue:

  \[
   \sum_i|q_i(X_n(j))-q_i(C)|=\frac1n\to0.
  \]

  Nevertheless their aggregate distance over the block is exactly one.
  Any exact constrained limit removes player \(0\)'s whole marginal charge.
  Thus a per-row modulus of approximation to the exact-root correspondence
  is insufficient when the moving length diverges; an aggregate
  charge-preserving modulus is necessary.

This is an exact Fin4 source/API regression, not a counterexample to the
uniform-equilibrium conjecture.  The displayed full profiles are already
vanishing-error, completely absorbing approximate equilibria.  The
table has a uniform equilibrium and hence does **not** satisfy the maintained
positive-minimum terminal-semantic-debt hypothesis.  The regression therefore
does not refute a retraction theorem which essentially uses that provenance.
It proves the exact narrower boundary: the generic fields supplied by
Theorem 9.1 do not imply the charge-preserving exact history retraction in
Section 13, even if only vanishing parent-state error is requested.  Any
positive theorem must use additional positive-minimum Fin4 source structure
which rules out this owner-to-opponent payoff monotonicity obstruction, or it
must consume the approximate block directly with summable seams rather than
exactify it.

## 17. The surviving literal-block consumer

The last sentence has a precise positive realization.  Exactification is not
needed if the actual two-cut blocks can be put in one executable order and
their **terminal-semantic endpoint seams** are summable.  Most of the
two-persistent consumer is already checked in
`ChronologicalSeamReduction.lean`; the source-facing wrapper below is the
remaining statement.

### 17.1 Block data and the weakest all-behavior hypotheses

For each block index \(k\), let \(L_k>0\), let

\[
 x_{k,0},\ldots,x_{k,L_k-1}
\]

be the literal product roots between two actual source cuts, and let

\[
 Z_{k,j}=(U_{k,j},B_{k,j})
 \qquad(0\leq j\leq L_k)
\]

be the terminal semantic pair of the actual source suffix beginning at that
offset.  Thus \(B_{k,j}\) is the unrestricted behavioral best-response cap,
not a root-only or finite-deadline cap.  Literal chronological prefixing gives

\[
 Z_{k,j}
 =\operatorname{Prefix}_{x_{k,j}}(Z_{k,j+1})
 \qquad(j<L_k).                                             \tag{44}
\]

Assume uniform boundedness, which is automatic for actual terminal semantic
pairs of one finite reward table, and define the two endpoint seams

\[
 d^U_{k,i}=|U_{k,L_k}(i)-U_{k+1,0}(i)|,
 \qquad
 d^B_{k,i}=|B_{k,L_k}(i)-B_{k+1,0}(i)|.                    \tag{45}
\]

The exact quantitative hypotheses for the checked all-behavior block
consumer are:

1. for every player \(i\), both series
   \(\sum_k d^U_{k,i}\) and
   \(\sum_k(d^U_{k,i}+d^B_{k,i})\) converge;
2. the source debt at block starts tends to zero,

   \[
    \delta_k:=\max_i(B_{k,0}(i)-U_{k,0}(i))\longrightarrow0; \tag{46}
   \]

3. the flattened literal root word has vanishing joint survival on every
   suffix and vanishing \(i\)-deleted survival on every suffix for every
   player \(i\).

These are weaker than summability of every rowwise Nash defect.  There is no
factor \(L_k\) in (45)--(46).  In particular, the generic two-cut source gives
(44), boundedness, nonnegative debt, and

\[
 \delta_k\leq
 \frac{E_{n_k}}{\operatorname{Reach}(s_{n_k})}\longrightarrow0           \tag{47}
\]

from its unrestricted behavioral Nash certificate.  It does not by itself
give the endpoint-seam summability or the survival field.

### Theorem 17.1 -- summable semantic seams consume two-persistent blocks

Under (44)--(46) and hypothesis 3, the quitting game has a uniform-equilibrium
payoff against unrestricted behavioral deviations.

#### Proof

Store the displayed data in the checked structure
`QuittingVariableLengthSeamBlocksNat`, with `candidate k j = Z_{k,j}`.
Equation (44) is its `exact_step`; terminal semantic debt is nonnegative; and
the reward bound gives both boundedness fields.  The checked flattening theorem
`QuittingVariableLengthSeamBlocksNat.toSummableSeamSourceNat` puts zero seams
inside blocks and exactly (45) at block ends.

Given an accuracy \(\eta>0\), discard enough initial blocks that the two seam
tails are at most \(\eta\) for every player and \(\delta_k\leq\eta\).  Survival
from every suffix is unchanged by deleting finitely many roots.  The shifted
blocks therefore give a `QuittingSummableSeamSource reward eta`.  Applying
`quittingGame_exists_uniformEquilibriumPayoff_of_summableSeams_all_errors`
for every \(\eta\) proves the claim.  That checked consumer evaluates the
literal flattened behavioral profile and its unrestricted behavioral caps,
including Never and arbitrarily late randomized deviations.  ∎

The probability hypothesis can be replaced by the more usable sufficient
condition that two fixed distinct players \(p,q\) have divergent flattened
marginal hazards.  Then
`HasTwoPersistentQuittingMarginals.survival` gives both joint and every
deleted-player survival.  Conversely, a positive total charge in every block
only gives

\[
 \sum_k\sum_{j<L_k}\sum_i q_i(x_{k,j})=\infty,              \tag{48}
\]

so finiteness selects at least one persistent label, not two.  This is the
only persistence conclusion implied by a charge floor.

### 17.2 The unique-persistent branch needs less seam data but normality

Suppose (48) selects exactly one persistent player \(p\).  Then every opponent
marginal is summable.  Put \(w_t=U_{k,j}\) on the flattened calendar.  Inside
blocks the Bellman recursion is exact; at a block end its residual is at most

\[
 \beta_t=\max_i d^U_{k,i}.                                  \tag{49}
\]

Hence \(\sum_t\beta_t<\infty\).  Let \(\alpha_k\) be a uniform root-Nash
defect for the rows of block \(k\) against their displayed source successor.
The pure-Quit endpoint used below is continuation-invariant, so even at a
block-end row it may be bounded using the original source successor and the
original source current value.  No seam term is added to this Quit bound.
For actual two-cut blocks one may take

\[
 \alpha_k=
 \frac{E_{n_k}}{\operatorname{Reach}(r_{n_k})}\longrightarrow0.          \tag{50}
\]

Choose increasing flattened dates \(t_m\) with
\(q_p(x_{t_m})>0\).  Their block indices tend to infinity, so their source
root-Nash errors tend to zero by (50).  The unique-persistent ledger from the
hazard-capacity export now applies with no unweighted sum of these errors:

\[
 \lVert w_t-U^{\rm flat}_t\rVert_\infty
 \leq\sum_{s\geq t}\beta_s,                                \tag{51}
\]

and the checked bounded-Bellman concentration gives

\[
 \lVert U^{\rm flat}_t-r(\{p\})\rVert_\infty
 \leq2M\,\operatorname{OpponentClockTail}(p,t).             \tag{52}
\]

At the selected \(p\)-positive dates, continuation invariance of the pure-Quit
endpoint and source root Nash give, for every outsider \(i\),

\[
 \operatorname{FixedOpponentsQuitValue}_i(x_{t_m})
 \le w_{t_m}(i)+\alpha_{k(t_m)}.                            \tag{52a}
\]

If \(p\) is punishment-normal, pass (51)--(52), the opponent clock tail, and
the error in (52a) to
`isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits`.  It follows that
\(r(\{p\})\) is a uniform-equilibrium payoff.

This branch uses summability of the **prescribed-payoff** seams, pointwise
\(\alpha_k\to0\), opponent-hazard summability, and owner normality.  It does
not require summability of \(L_k\alpha_k\), nor cap-seam summability.  The
latter is needed by the symmetric all-player shadowing theorem, not by the
normal unique-persistent deleted-Quit consumer.

### 17.3 Combined Fin4 consumer

Consequently, for a punishment-normal finite quitting game, a composable
sequence of actual two-cut blocks produces a uniform-equilibrium payoff if:

1. its total flattened marginal hazard diverges;
2. its prescribed endpoint seams are summable;
3. its blockwise divided source error \(\alpha_k\to0\); and
4. if the flattened stream has at least two persistent labels, its cap seams
   are also summable and its block-start semantic debts tend to zero.

The persistence set of the one flattened schedule is fixed.  If it has one
member, Section 17.2 applies; if it has at least two, Theorem 17.1 applies.
A fixed charge floor per block is stronger than item 1.

The ancestry condition is logically upstream of this consumer.  Any finite
product-root words can be concatenated into a legal behavioral profile of the
quitting game.  To call the result **source-provenant**, however, the returned
child of block \(k\) must be the history parent of block \(k+1\), or an
explicit history retraction must make every such prefix legal.  Numerical
endpoint closeness does not prove this.  Once one composable history supplies
the words, the consumer uses only the literal roots and semantic ledgers above.

### 17.4 Relation to the existing hazard-capacity compiler

There are two different answers to “subsumes.”

- If one assumes a flattened sequence with summable rowwise Bellman and
  Nash residuals, then Theorem B of
  `UNBOUNDED_FINITE_HAZARD_CAPACITY_COMPILER.md` already consumes it.  No new
  consumer is needed.
- The unbounded-capacity **extraction** theorem does not subsume the present
  source problem.  It starts from exact Nash--Bellman blocks of unbounded
  charge and manufactures near-return seams.  The chronological two-cut
  blocks are approximate, can have bounded charge one at a time, and do not
  imply unbounded exact-block capacity after Section 16.
- More importantly, the literal-block theorem is quantitatively stronger
  than applying the rowwise residual adapter mechanically.  The source only
  gives \(\alpha_k\to0\); it need not give
  \(\sum_kL_k\alpha_k<\infty\).  The checked variable-length semantic-pair
  adapter removes this length factor in the two-persistent branch, while the
  unique-persistent ledger samples only \(p\)-positive dates and also needs
  only pointwise vanishing.

Thus the desired positive consumer is mathematically valid and is already
mostly formalized.  Its true missing producer is not another Nash estimate.
It is one source-provenant ordering of positive-charge blocks with summable
prescribed endpoint seams (and, on the multi-persistent arm, summable cap
seams).  The generic fixed-\(a<b\) two-cut packet does not supply this: its
endpoint limits are \(z_a\) and \(z_b\), so unless those coincide the seam
has a nonzero limiting size and cannot be summable.

### Boundary checks

1. **Length amplification.**  Uniform row error
   \(\alpha_k\to0\) does not imply
   \(\sum_kL_k\alpha_k<\infty\); take \(L_k\alpha_k=1\).  This does not refute
   Theorem 17.1 because (46) is a whole-profile unrestricted debt bound, not a
   sum of row bounds.
2. **One-label survival.**  In a one-player game with singleton reward
   negative and Never payoff zero, an exact persistent Bellman ray can be
   defeated by Never.  This is the standard failure of deleted-player
   survival and shows why the unique arm needs punishment normality rather
   than the two-label shadowing argument.
3. **Nonsummable seams.**  At an all-Continue row, prescribed successor error
   is transmitted with coefficient one, as checked by
   `quittingTerminalSemanticPrefix_prescribed_positiveSeam_regression`.
   Therefore merely having seams tend to zero cannot replace a summable tail
   budget.
4. **Fixed two-cut levels.**  If \(z_a\ne z_b\), consecutive copies have seam
   tending to \(\lVert z_b-z_a\rVert_\infty>0\).  Positive charge and positive
   end reach alone therefore do not instantiate the consumer.

## 18. Constructor-SD architecture on a strong semantic-cut atlas

The fixed-level obstruction in the last boundary check can be avoided without
exactification.  The correct construction uses a **chain of clock levels** and
matches the right endpoint of block \(k\) to the left endpoint of block
\(k+1\) through one common chronological limit.  It then decodes the literal
approximate blocks directly.

This section validates the proposed decoder on a **strong post-source
interface**.  It is not a producer from the pre-limit AGKRS S.3 object or from
the Fin4 hard residual.  In addition to the cofinality condition below, it
uses actual terminal semantic pairs and vanishing whole-profile shifted Nash
debt at every selected cut.  Those are the decisive strategic fields, not
consequences of chronological weak convergence:

\[
 F(u)<1\quad(u<1),
 \qquad
 \lim_{u\uparrow1}F(u)=1,                                  \tag{53}
\]

along continuity points of the limiting clock CDF.  A terminal jump or a
clock gap reaching value one is a different chronological branch and is not
silently included in this construction.

### 18.1 Geometric continuity levels

Choose continuity points

\[
 0\le u_0<u_1<u_2<\cdots<1
\]

with \(F(u_k)<F(u_{k+1})<1\) and

\[
 1-F(u_{k+1})\le\frac12(1-F(u_k)).                         \tag{54}
\]

This is possible from (53), after moving each proposed threshold slightly to
a continuity point.  Write \(S_k=1-F(u_k)>0\).

On every sufficiently late completed source rank, apply the finite CDF-cut
constructor simultaneously to the finite list
\(u_0,\ldots,u_m\).  Strict ordering of their limiting clocks makes the
resulting cuts strictly ordered.  At each cut retain:

- the literal shifted source profile;
- its full terminal semantic pair, including the unrestricted behavioral
  cap;
- the prescribed and every deleted terminal outcome law;
- its clock, reach, and completed-error certificate; and
- the exact finite prefix/tail identity to the next cut.

For each fixed \(k\), compactness of the terminal semantic carrier gives a
convergent cut-pair subsequence.  A countable diagonal extraction gives one
strict common rank sequence on which this convergence holds simultaneously
at every \(u_k\).  Denote the semantic limit at \(u_k\) by

\[
 Z_k=(U_k,B_k).                                             \tag{55}
\]

This is one diagonal extraction, not one unrelated subsequence for each
seam.

Choose successively ranks \(n_k\) far enough down that:

\[
 \bigl\|Z(n_k,u_k)-Z_k\bigr\|_\infty\le 2^{-k-4},
 \qquad
 \bigl\|Z(n_k,u_{k+1})-Z_{k+1}\bigr\|_\infty\le2^{-k-4},   \tag{56}
\]

and

\[
 \frac{E_{n_k}}
      {\operatorname{Reach}(n_k,u_{k+1})}
 \le2^{-k-4}.                                               \tag{57}
\]

The positive limit \(S_{k+1}\) of the denominator licenses (57).  Let
\(\mathcal B_k\) denote the literal root word between the two selected cuts
on rank \(n_k\); no exact root replacement is made.

Theorem 9.1 and (54) give the uniform conditional charge floor

\[
 H(\mathcal B_k)
 \ge 1-
   \frac{\operatorname{Reach}(n_k,u_{k+1})}
        {\operatorname{Reach}(n_k,u_k)}
 \ge\frac13                                                 \tag{58}
\]

after increasing \(n_k\) if necessary.  The harmless \(1/3\), rather than
the limiting \(1/2\), absorbs the finite-rank clock error.  Every row of
\(\mathcal B_k\) has root-Nash defect at most \(2^{-k-4}\), by (57), and its
displayed source semantic pairs satisfy exact Bellman/terminal-semantic
prefixing.

At the seam between consecutive selected blocks, (56) gives

\[
 \bigl\|Z(n_k,u_{k+1})-Z(n_{k+1},u_{k+1})\bigr\|_\infty
 \le 2^{-k-3}.                                               \tag{59}
\]

Hence both prescribed and cap seam series converge.  The semantic debt at
the start of block \(k\) is at most the shifted unrestricted Nash error and
therefore tends to zero by (57).

Equations (58)--(59) are exactly the two quantitative fields which the fixed
two-cut packet did not supply: divergent total charge and summable
source-semantic seams on the same selected block code.

### 18.2 The source-faithful summable macro code

The appropriate **SD** object is not a total-variation limit of the original
source profiles.  It is the limit of their **compiled finite subblocks**.

Let \(\widehat\sigma_N\) be the actual product-root profile obtained by
concatenating \(\mathcal B_0,\ldots,\mathcal B_{N-1}\) and then playing
all-Continue forever.  The finite code \(Z_N^{\mathrm{code}}\) retains:

1. the fixed positive-minimum hard-residual source family and the one
   chronological limit;
2. the first \(N+1\) levels \(u_k\);
3. the common diagonal ranks \(n_0,\ldots,n_{N-1}\);
4. both actual cuts and the literal root word of every selected block;
5. the Nash, reach, charge, semantic-pair, law, and deleted-law certificates;
   and
6. the proof that consecutive endpoint annotations satisfy the prescribed
   budget in (59).

For the single selected construction each \(Z_N^{\mathrm{code}}\) may be
taken to be a singleton compact code space; restriction forgets the last
block and is continuous and surjective.  A nontrivial compact family version
takes the closed set of all codes satisfying the same finite inequalities.
The finite macro from \(\widehat\sigma_N\) to
\(\widehat\sigma_{N+1}\) replaces the all-Continue tail after the first \(N\)
blocks by \(\mathcal B_N\) followed by all-Continue.  It is a literal finite
behavioral program.

For player \(i\), let \(a_{N,i}\) be the probability, under the concatenated
marginal schedule, that \(i\)'s first Quit occurs in the newly installed
block \(\mathcal B_N\).  Direct comparison of the two stopping laws gives

\[
 \bigl\|\mu_i(\widehat\sigma_{N+1})
       -\mu_i(\widehat\sigma_N)\bigr\|_1
 =2a_{N,i}.                                                  \tag{60}
\]

The events indexed by \(N\) are disjoint, so

\[
 \sum_N a_{N,i}\le1,
 \qquad
 \sum_N d_\Sigma(\widehat\sigma_{N+1},\widehat\sigma_N)
 \le2|I|.                                                    \tag{61}
\]

Thus (60)--(61) provide the literal **SD** budget.  Constructor SD yields one
actual total-variation limit profile \(\widehat\sigma\), with the complete
unrestricted-response kernel preserved uniformly.  This is stronger than
weak chronological convergence.

Define the ancestry predicate to mean:

> “the output is obtained by the displayed finite or infinite concatenation
> of blocks whose cut certificates all belong to this one recorded source
> family and this one chronological diagonal.”

With every finite certificate retained as a code coordinate, the full
inverse-limit provenance relation is the continuous image of the compact
code space and is closed, exactly as in Constructor SD.  It certifies one
family-source ancestry and one actual compiled controller.  It does **not**
assert that blocks taken from distinct ranks are contiguous descendants in
one member profile; that stronger claim is false at the present API and is
unnecessary for the behavioral compiler.

### 18.3 Consumption in the punishment-normal Fin4 residual

By (58), the flattened marginal charge diverges.  Finiteness selects one
fixed nonempty persistence set \(P\).

- If \(|P|\ge2\), (59), the vanishing block-start debt, and the exact semantic
  prefix identities instantiate Theorem 17.1.  The two persistent labels
  give joint and every deleted-player survival.
- If \(P=\{p\}\), every opponent marginal is summable.  The row defects in
  (57) tend to zero and the prescribed seams in (59) are summable, so Section
  17.2 applies.  The Fin4 hard residual supplies punishment normality of
  \(p\).

Therefore a cofinal semantic-cut atlas satisfying the displayed hypotheses
has a literal terminal approximation producer and hence a uniform-equilibrium
payoff.  The construction never exactifies a charged block, so Section 16 is
not an obstruction; it explains why this approximate **SD** architecture is
the right decoder **once the strong atlas has been supplied**.

### 18.4 Exact scope

The architecture above cannot presently be advertised as an unconditional
positive-minimum theorem.  It would require all of the following source facts:

1. the maintained hard-residual branch decomposition must explicitly route
   every non-C1/C2 terminal jump/gap case to its existing consumer;
2. the C1/C2 branch must expose (53), or the equivalent ability to choose the
   geometric continuity-level chain (54), on the same chronological limit;
3. every selected cut must retain one actual full terminal semantic pair,
   including the unrestricted behavioral cap; and
4. the shifted whole-profile Nash debt, not merely rowwise perfection, must
   vanish after division by cut reach.

No additional exact-root selection, cap-root homotopy, or capacity attainment
is needed **after** these fields are given.  But (3)--(4) are not supplied by
the pre-limit S.3 sequence.  Moreover, if they come from a literal
`QuittingRootSequenceVanishingNashFamily` and its absorbing-completion
diagonal, the current checked source already gives a uniform-equilibrium
payoff through `ChronologicalLimit.payoff_isUniformEquilibriumPayoff`.
Section 18 is therefore architectural validation, not a new same-table
existence proof.

There is also a sharp reason not to demand that the original source profiles
themselves form the **SD** approximants.  In the uniform-mesh example of
Section 4, one player's stopping law is uniform on an interval of calendar
dates whose length tends to infinity.  Those laws have no
total-variation-convergent subsequence even though their chronological clock
laws converge perfectly.  Thus C1/C2 weak compactness cannot produce a
strategic-metric limit of source members.  The compiled truncations
\(\widehat\sigma_N\) avoid this no-go because their successive differences
are the disjoint newly installed masses in (60), making the decoder budget
telescope.

### 18.5 Cumulative-defect and Cauchy-tail audit

No inference in Sections 18.1--18.3 uses
\(\sum_k L_k2^{-k}<\infty\).  There are two distinct consumers.

#### Multi-persistent arm: checked blockwise semantic consumer

For a suffix beginning at block \(K\), use the actual source terminal semantic
pairs \(Z(n_k,u)\) as the candidates inside every block.  Then:

- every within-block semantic-prefix equation is exact;
- candidate debts are nonnegative and uniformly bounded;
- the initial candidate debt is at most
  \[
    \delta_K\le
    E_{n_K}/\operatorname{Reach}(n_K,u_K)\le2^{-K-4};
  \]
- every internal flattened seam is zero;
- by (59), for every player the prescribed seam at block \(k\) is at most
  \(2^{-k-3}\), the cap seam is at most \(2^{-k-3}\), and the total seam is
  at most \(2^{-k-2}\).

Consequently

\[
 \sum_{k\ge K}d^U_{k,i}\le2^{-K-2},
 \qquad
 \sum_{k\ge K}(d^U_{k,i}+d^B_{k,i})\le2^{-K-1}.             \tag{62}
\]

These are exactly the fields passed to the checked theorem
QuittingVariableLengthSeamBlocksNat.toSummableSeamSourceNat, followed by
quittingGame_exists_uniformEquilibriumPayoff_of_summableSeams_all_errors.
That adapter never asks for a sum of rowwise root-Nash defects.  It charges
the whole-profile unrestricted debt only once, at the first candidate of the
shifted block stream, and charges the two semantic endpoint seam series in
(62).  The rowwise estimate (57) is therefore irrelevant to this arm except
as one way to derive the initial whole-profile bound; the stronger direct
derivation uses shiftedNash_of_reach_ge and the definition of the
unrestricted cap.

Explicitly, if the shifted actual source profile is \(\varepsilon\)-Nash,
then for every player \(i\) and every behavioral replacement \(\tau_i\),
\[
 U_i(\sigma[i\leftarrow\tau_i])\le U_i(\sigma)+\varepsilon.
\]
Taking the supremum over \(\tau_i\) gives
\[
 0\le B_i(\sigma)-U_i(\sigma)\le\varepsilon.                \tag{63}
\]
This proves the required initial-debt field without summing local defects.

#### Unique-persistent arm: a sampled checked endpoint consumer

Here the prescribed Bellman residual \(\beta_t\) is zero inside a block and
is at most \(\max_i d^U_{k,i}\) at the block-\(k\) seam.  Hence
\[
 \sum_t\beta_t<\infty.
\]
This summable series proves (51).  Root-Nash defects are not summed.  They are
used only on a selected sequence of \(p\)-positive dates, where (52a) has
error at most \(2^{-k(t_m)-4}\to0\).  The three inputs to the checked endpoint
consumer isUniformEquilibriumPayoff_soloReward_of_deletedQuitLimits may be
taken as
\[
\begin{aligned}
 e_m^{\mathrm{haz}}
   &=\operatorname{OpponentClockCharge}(p,t_m),\\
 e_m^{\mathrm{target}}
   &=\sum_{s\ge t_m}\beta_s+
     2M\,\operatorname{OpponentClockTail}(p,t_m),\\
 e_m^{\mathrm{quit}}
   &=2^{-k(t_m)-4}.
\end{aligned}                                               \tag{64}
\]
All three tend to zero: the unique-persistent hypothesis makes the opponent
clock summable, the Bellman seam series is summable, and block indices tend
to infinity.  Thus this arm also has no hidden \(L_k\)-factor.

#### Exact strategic-metric tail

Let \(a_{k,i}\) be as in (60), now defined in the infinite concatenated
marginal schedule, and put
\[
 A_{N,i}:=\sum_{k\ge N}a_{k,i}.
\]
The finite truncation and the decoded profile agree at every date before
block \(N\).  The truncation places all residual mass at Never, whereas the
decoded law moves precisely \(A_{N,i}\) of that mass to later finite dates.
Therefore
\[
 \|\mu_i(\widehat\sigma)-\mu_i(\widehat\sigma_N)\|_1
 =2A_{N,i},                                                  \tag{65}
\]
and
\[
 d_\Sigma(\widehat\sigma,\widehat\sigma_N)
 =2\sum_iA_{N,i}
 =\sum_{k\ge N}c_k,
 \qquad c_k:=2\sum_i a_{k,i}.                               \tag{66}
\]
Since \(\sum_ka_{k,i}\le1\), monotone convergence gives
\(A_{N,i}\downarrow0\) for every player.  Finiteness of \(I\) makes the
right side of (66) tend to zero.  Equations (65)--(66), not merely the coarse
bound \(\sum_kc_k\le2|I|\), are the required Constructor-SD Cauchy-tail
estimate.

## 19. Exact pre-limit source audit and chronological branch split

This section corrects the source level of Section 18.

### 19.1 The weakest objects actually available

There are three different interfaces, and they must not be identified.

1. `FinFourQuantitativeFullSupportHardResidual` in
   `FullSupportProjectiveQBarResidual.lean` contains a terminal
   exploitability witness, full punishment normality, a full-support
   normalized singleton packet, its quantitative mass floor, and
   `ResidualHardClass`.  It contains no approximate-equilibrium profiles,
   root chronology, terminal semantic cut pairs, or Nash errors.
2. The checked AGKRS pre-limit branch S.3 is
   `QuittingSequentiallyεPerfectAbsorbingExistence`, equivalently
   `QuittingWellSupportedAbsorbingSequenceExistence`.  At every positive
   tolerance it gives one completely absorbing root sequence and rowwise
   perfection, or support-local endpoint optimality, against that sequence's
   own actual continuation vectors.  It gives no whole-profile Nash bound,
   no unrestricted cap coordinate, and no common ancestry between witnesses
   chosen at different tolerances.
3. `QuittingRootSequenceVanishingNashFamily` is much stronger: it gives
   actual whole-profile Nash root sequences with global errors tending to
   zero and Never mass tending to zero.  Its absorbing-completion diagonal
   and any `ChronologicalLimit` already have a checked uniform payoff by
   `ChronologicalLimit.payoff_isUniformEquilibriumPayoff`.

There is an even shorter redundancy test.  If the alleged weaker atlas
retains actual prescribed payoffs \(U_k\), unrestricted behavioral caps
\(B_k\), and \(B_k-U_k\to0\), then those profiles are already terminal
approximate Nash.  Finite-dimensional compact selection plus
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
already gives the desired payoff.  No chronological block decoder is needed.

Consequently Section 18 does **not** use only the pre-limit S.3 interface.
Its uses of (56), (57), (59), (62), and (63) require exactly the missing
unrestricted semantic-cap and whole-profile-debt fields.  The maximal honest
restatement of Section 18 is:

> A cofinal chain of literal finite blocks carrying exact semantic prefix
> identities, full actual endpoint payoff/cap pairs, summable pair seams,
> divergent conditional charge, and vanishing actual block-start debt can be
> decoded by the displayed SD concatenation.

That is a useful decoder validation, but not a producer from the hard
residual or from S.3.

### 19.2 Exact terminal jump and gap branches

For the ordinary AGKRS refusal compactification in
[`AGKRS_FORWARD_TRICHOTOMY_BY_REFUSAL_COMPACTIFICATION.md`](../formalized/AGKRS_FORWARD_TRICHOTOMY_BY_REFUSAL_COMPACTIFICATION.md), the exhaustive
source split is:

1. If every normalized own-singleton payoff is nonpositive, all-Continue is
   an exact stationary profile: branch S.1.
2. If the limiting path has a jump whose post-jump accumulated mass is one,
   the matching genuine source rows yield the instant-punishment branch S.2.
   The positive jump cannot be the vanishing late completion.
3. If there is no such terminal jump, the support-preserving path
   discretization yields completely absorbing sequentially approximately
   perfect sequences: branch S.3.  It does not yield global Nash debt.
4. A nonterminal jump is not a fourth terminal branch.  It supplies the
   exact product-root jump condition SP.1 against a genuine post-jump
   continuation.
5. A continuous clock component supplies the solo-Quit lower inequality;
   positive singleton right rate supplies equality by the refusal lemma.
6. A clock gap or plateau is the A2 identity for the path total.  It becomes
   a terminal case only when a jump exhausts all remaining mass.  A mere
   plateau below one is handled inside the nonterminal path and is not an
   extra output.

At the older checked source boundary,
`QuittingPayoffTable.lowSurvivalPrefix_or_exists_boundedSupportBellmanSpine`
instead returns an actual low-survival approximate prefix or a bounded exact
Bellman/support-local spine.  Neither output by itself contains the cap/debt
atlas of Section 18.

## 20. A source-free normal S.3 delayed-switch compiler

The failure of the cap-atlas adapter does not end the S.3 attack.  There is a
smaller augmentation suggested by the checked support-witness compiler: at a
punishment-normal table, failure of individual rationality at one row has to
spend opponent absorption.  This gives a finite delayed switch and avoids
all cross-tolerance ancestry.

### Theorem 20.1 -- normal S.3 implies a uniform-equilibrium payoff

Let \(I\) be finite and nonempty, let \(r\) be a quitting reward table, and
assume

\[
 \chi_i:=\operatorname{PunishmentValue}_r(i)
 \le a_i:=r_i(\{i\})\qquad(i\in I).                         \tag{67}
\]

If `QuittingSequentiallyεPerfectAbsorbingExistence r` holds, then \(r\) has a
uniform-equilibrium payoff.

This is an ordinary proof draft, not a checked declaration.  Its ingredients
below are all already exposed by named checked lemmas.

#### Quantitative selection

Fix a desired terminal error \(\varepsilon>0\), and put
\(M=\operatorname{quittingRewardBound}(r)\).  Choose
\(0<\theta<1\), \(r_0>0\), a ledger allowance \(\ell>0\), and a punishment
slack \(\zeta>0\), all sufficiently small that

\[
 \ell+r_0+\zeta+7M\theta<\varepsilon/2.                    \tag{68}
\]

Put \(B=\max\{1,2M\}\), choose \(r_0<B\), and set

\[
 c=\frac{r_0}{2B}\in(0,1).
\]

Choose \(L\) with \((1-c)^L\le\theta\).  Finally choose the S.3 row
tolerance \(\eta>0\) so small that

\[
 \eta\le r_0/2,
 \qquad 2\eta\le\ell\theta,
 \qquad (2L+4)\eta<\varepsilon/2.                          \tag{69}
\]

Take a completely absorbing \(\eta\)-perfect root sequence \(x_t\), and
write \(V_t^i\) for its actual continuation payoff from row \(t\).
`supportApproxNash_of_quittingRowεPerfect` makes it support-local at error
\(\alpha=2\eta\).

Complete absorption and
`exists_ownSurvival_crossing_of_completelyAbsorbing` give a first global
support-survival switch \(s\) and a player \(p\) whose own planned survival
through \(s\) is at most \(\theta\).  The checked clock-collapse package,
using \(\alpha\le\ell\theta\), gives

\[
 \operatorname{Ledger}_i(n)\le\ell+\alpha\quad(n\le s),
 \qquad
 \operatorname{QuitRegret}_i(t)\le\alpha\quad(t<s).        \tag{70}
\]

Call a date \(t\ge s\) good for \(p\) when

\[
 V_t^p\ge\chi_p-r_0.                                      \tag{71}
\]

If a date is bad, the rowwise no-profitable-Quit clause gives

\[
 Q_t^p\le V_t^p+\eta<\chi_p-r_0+\eta
                 \le a_p-r_0/2.
\]

The checked quit-endpoint estimate
`abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass`
therefore implies

\[
 \operatorname{OppAbs}_p(x_t)>\frac{r_0}{2B}=c.            \tag{72}
\]

Inspect only \(s,s+1,\ldots,s+L-1\).  Either the first good date \(t\)
occurs, or all \(L\) rows are bad and

\[
 \operatorname{OpponentSurvival}_p(s,s+L)
 \le(1-c)^L\le\theta.                                     \tag{73}
\]

Every extra row adds at most \(\alpha\) to every ledger and has Quit regret
at most \(\alpha\).  Thus at either selected switch \(T\le s+L\),

\[
 \operatorname{Ledger}_i(n)\le\ell+(L+1)\alpha\quad(n\le T),
 \qquad
 \operatorname{QuitRegret}_i(t)\le\alpha\quad(t<T).       \tag{74}
\]

#### The two finite decoder branches

If a good date occurs, use
`exists_quittingTargetClosedTail_le_of_punishmentValue_le` with boundary
\(V_T^p+r_0\) and slack \(\zeta\).  It gives one actual stationary
target-closed tail whose cap for \(p\) is at most
\(V_T^p+r_0+\zeta\).  Player \(p\)'s own survival bound at \(s\) makes the
joint reach at \(T\) at most \(\theta\); for every \(i\ne p\), the same
factor lies in player \(i\)'s deleted survival.  Equations (74), (68), and
(69) therefore instantiate the checked marked phase-switch theorem
`isεAsymptoticNash_quittingPhaseSwitchProfile_marked`.

If there is no good date, (73) makes player \(p\)'s deleted survival at
\(T=s+L\) at most \(\theta\).  For every \(i\ne p\), player \(p\)'s own
survival factor makes player \(i\)'s deleted survival at most \(\theta\).
Thus every deleted survival is small.  Attach any bounded tail and apply the
ordinary `isεAsymptoticNash_quittingPhaseSwitchProfile`, with plan error
bounded from (74).  Its worst displayed error is at most

\[
 \ell+(L+2)\alpha+7M\theta<\varepsilon.                    \tag{75}
\]

In the good branch the corresponding worst bound is

\[
 \max\{\ell+(L+2)\alpha+r_0+\zeta+2M\theta,
          \ell+(L+2)\alpha+7M\theta\}<\varepsilon.         \tag{76}
\]

Hence every positive \(\varepsilon\) has an actual terminal
\(\varepsilon\)-Nash profile against unrestricted behavioral deviations.
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
then selects one fixed uniform-equilibrium payoff.

### 20.2 What this means for the positive-minimum branch

This compiler starts only from S.3, complete absorption, and playerwise
normality.  It assumes neither `ApproximateEquilibriumExistence` nor a
`ChronologicalLimit`.  It also does not manufacture a common infinite cap
atlas: its output at each accuracy is a literal finite prefix of one S.3
source sequence followed by one actual punishment tail.  That finite source
ancestry is exactly what the phase-switch consumer needs, and unrelated
accuracies are allowed by terminal-to-uniform payoff selection.

In a Fin4 hard residual, all players are normal.  Therefore Theorem 20.1, if
independently checked and formalized, would show that the hard residual
cannot also satisfy branch S.3.  This is the sharp positive-minimum statement:
one cannot first add vanishing same-profile cap debt to a positive-minimum
semantic source, because the definition gives the lower bound \(D_*>0\) on
that debt.  Instead the delayed-switch decoder changes the strategy after a
finite source prefix and would contradict \(D_*>0\) by producing new terminal
approximate Nash profiles.

The checked local-global counterexample in
`ErrorExponentRefutation.lean` shows why normality is essential.  Its root
sequence is completely absorbing and exactly row-perfect but has terminal
regret one; the deviating player has solo payoff \(-1\), punishment value
zero, and is therefore abnormal.  The regression is excluded precisely by
(67), not by an unjustified local-to-global assertion.

### 20.3 Narrow formalization handoff

The proof should be formalized as a new consumer, not as an extension of the
chronological-limit files.  A minimal declaration split is:

1. `opponentAbsorptionMass_gt_of_normal_of_rowPerfect_of_not_individualRational`,
   proving (72) from `IsQuittingNormalPlayer`, one
   `QuittingPlayerRowεPerfect` clause, and the existing quit-endpoint bound;
2. `exists_normalSupportDelayedSwitch`, returning the marked player, initial
   support-survival switch, final switch at distance at most \(L\), ledger
   bounds (74), and the disjunction between a good target boundary and
   all-player deleted survival;
3. `exists_terminalNash_of_all_normal_of_sequentiallyPerfectAbsorbing`,
   dispatching that disjunction to the checked marked or ordinary
   phase-switch theorem; and
4. `exists_uniformEquilibriumPayoff_of_all_normal_of_sequentiallyPerfectAbsorbing`,
   applying terminal-to-uniform selection.

The narrow checked source set is:

- `supportApproxNash_of_quittingRowεPerfect` and the S.3 definitions in
  `Existence/WellSupportedAbsorbingSequence.lean` and
  `ExistenceBranches.lean`;
- `quittingSupportApproxNash_survivalSwitchPackage` in
  `Paths/SupportWitnessClockCollapse.lean`;
- `exists_quittingTargetClosedTail_le_of_punishmentValue_le` in
  `Paths/SupportWitnessIndividualRational.lean`;
- `isεAsymptoticNash_quittingPhaseSwitchProfile_marked` and
  `isεAsymptoticNash_quittingPhaseSwitchProfile` in
  `Debt/Marked/PhaseSwitchCap.lean` and
  `Cycles/PhaseSwitchDeviationCap.lean`; and
- the quit-endpoint bound in `Paths/QuitEndpointOpponentBound.lean`.

The first lemma and the delayed-switch product estimate are the only new
mathematics.  The strategic cap, Never deviation, arbitrary behavioral
replacement, and terminal-to-uniform steps should be reused rather than
reproved.

### 20.4 Subsequent checked status

Theorem 20.1 and its finite delayed-switch handoff are now proved in Lean and
recorded in
[`NORMAL_S3_DELAYED_SWITCH_UNIFORM_PAYOFF.md`](../formalized/NORMAL_S3_DELAYED_SWITCH_UNIFORM_PAYOFF.md).
The generic compiler is
`exists_uniformEquilibriumPayoff_of_all_normal_of_sequentiallyPerfectAbsorbing`;
the equivalent well-supported wrapper is also checked. The Fin4 companion
obtains all-player punishment normality from a supplied
`FinFourQuantitativeFullSupportHardResidual`. This remains a conditional
consumer of an already supplied sequentially perfect or well-supported
completely absorbing source. It does not produce that source from arbitrary
approximate equilibria, the corrected Simon fourth output, or the hard
residual itself.
