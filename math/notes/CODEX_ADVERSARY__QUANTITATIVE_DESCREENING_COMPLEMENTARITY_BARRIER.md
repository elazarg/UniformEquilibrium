# Quantitative descreening meets an exact-Nash complementarity barrier

**Author:** `CODEX_ADVERSARY`  
**Status:** **PROVED IN ORDINARY MATHEMATICS FROM THE SOURCE DECLARATIONS
NAMED BELOW; A SOURCE-FAITHFUL PERMEABLE ROW EXISTS WITH FIXED MASS AND GAIN,
BUT IT HAS A FIXED ROOT DEFECT, AND NO SINGLE EXACT ROOT CAN RETAIN THE SAME
DIRECT GAIN**  
**Date:** 2026-08-30

## 1. Exact question and answer

The forced-pair minimum-return packet supplies one literal row with:

- reached live mass at least a fixed resolution λ;
- a pure singleton owner a and a distinct forced owner k;
- a collision premium at least the terminal gap γ;
- a pure pair atom {a,k} of mass at least λ;
- actual forced-owner gain at least λγ; and
- the unchanged post-date minimum-return continuation.

The pure pair is a complete tail screen.  Can it be replaced on the same
literal chronology by a mixed marked row which has positive joint
continuation, positive player-deleted continuation, retained marked mass and
retained gain?

There are two exact answers.

1. **Yes, before imposing root Nash.**  There is an explicit noninfinitesimal
   mixed row on the same prehistory and tail.  It retains at least 3λ/8 of the
   pair atom, gains at least λγ/8 for the forced owner relative to the
   original pure-singleton source, and retains at least λγ/(16M) joint and
   all-player-deleted continuation through the displayed prefix, where M is
   the canonical reward bound.  After the singleton owner is desaturated, the
   remaining one-coordinate forced-owner update has gain at least λγ/4.

2. **No, after imposing exact root Nash while asking for the same direct
   gain.**  The mixed forced owner has endpoint advantage at least γ/2, hence
   coordinate Nash defect at least γ/4 in the displayed half-mixed row.
   More generally, at an exact root every player with positive Quit and
   Continue probabilities is indifferent.  Therefore a positive marked atom,
   positive joint continuation, exact root Nash, and positive same-row
   unilateral endpoint-improvement gain for a member of that atom cannot
   coexist.

Thus descreening is not absent.  What is impossible is the four-way
combination

$$
\text{source-attached direct gain}
+\text{positive marked atom}
+\text{positive joint survival}
+\text{exact root Nash}.
$$

The mixed construction leaves the typed concentrated-packet target class and
has fixed root regret.  Exact punishment-floor roots in the positive terminal
gap branch are uniformly permeable, as Sections 49--51 of
`CODEX_CEDAR__PAID_ROW_REENTRY.md` show, but the current minimum-return
source does not attach its paid gain or literal marked chronology to one of
those roots.

## 2. Source data used

Fix one `FinFourSourcePreservingForcedPairPacket packet` over a
source-preserving singleton frame.  Write:

- a for `packet.singletonOwner`;
- k for `packet.forcedOwner`;
- m for the frame's marked stage;
- L for the live mass reaching m;
- U for the prescribed payoff vector of the literal post-date continuation;
- γ for `source.residual.witness.terminalGap`; and
- λ for `source.minimumSingletonClockResolution`.

The declarations
`forcedOwner_ne_singletonOwner`, `terminalGap_join`,
`pairProfile_eq_purePair`,
`forcedPair_stageMass_eq_liveMass`, and
`resolution_le_forcedPairStageMass` give

$$
a\ne k,\qquad
r_k(\{a,k\})-r_k(\{a\})\ge γ>0,\qquad
L\ge λ>0.
\tag{2.1}
$$

The post-date behavior is literally unchanged by
`forcedPair_postDateSpine_eq_reference`.

Let M be `quittingRewardBound reward`.  Both terminal rewards and U are in
[-M,M].  Equation (2.1) implies M>0 and γ≤2M.

The existing pure forced-pair gain lower bound is
`resolution_mul_terminalGap_le_forcedOwnerGain`.  The construction below
does not claim to preserve its exact numerical gain.  It retains a fixed
eighth of its canonical lower scale λγ relative to the actual pure-singleton
source, and a quarter for the inner one-coordinate update.

## 3. Explicit source-faithful permeable row

Put

$$
η=\frac{γ}{8M}.
\tag{3.1}
$$

Then 0<η≤1/4.  At the marked row define a product root q by

$$
q_a(Q)=1-η,\qquad q_k(Q)=\frac12,\qquad
q_j(Q)=0\quad(j\notin\{a,k\}).
\tag{3.2}
$$

Copy the actual source prehistory before m and the actual reference
continuation after m.  This changes no date other than the mark and makes no
new tail selection.

For comparison, let q⁰ have the same a marginal and all other players,
including k, Continue surely.  Let σᵐⁱˣ and σ⁰ be the two resulting complete
behavioral profiles.  Also let σˢʳᶜ be the packet's actual pure-singleton
profile at this row: a Quits surely and every other player Continues.

### Proposition 3.1 (quantitative literal descreening)

The mixed profile σᵐⁱˣ has all of the following properties.

1. Its conditional pair mass at the marked row is

   $$
   q(\{a,k\})=\frac{1-η}{2}\ge\frac38.
   \tag{3.3}
   $$

   Hence the unconditional pair atom is at least 3L/8≥3λ/8.

2. Its conditional joint Continue probability is

   $$
   c(q)=\frac{η}{2}=\frac{γ}{16M}.
   \tag{3.4}
   $$

3. Every player-deleted Continue probability at the marked row is at least
   η/2.  More exactly, it is 1/2 for a, η for k, and η/2 for either outsider.
   Since opponent-only survival through the copied prehistory dominates its
   joint survival L, the complete displayed prefix has joint and every
   player-deleted survival at least

   $$
   L\frac{η}{2}\ge\frac{λγ}{16M}.
   \tag{3.5}
   $$

4. The actual prescribed payoff gain of k from the packet's pure-singleton
   source σˢʳᶜ to σᵐⁱˣ is at least

   $$
   u_k(σ^{mix})-u_k(σ^{src})\ge\frac{Lγ}{8}
   \ge\frac{λγ}{8}.
   \tag{3.6}
   $$

   The inner one-coordinate update from σ⁰ to σᵐⁱˣ has the stronger bound

   $$
   u_k(σ^{mix})-u_k(σ^0)\ge\frac{Lγ}{4}
   \ge\frac{λγ}{4}.
   \tag{3.7}
   $$

5. The k-coordinate root Nash defect of q at U is at least γ/4.
   In particular q is not exact endpoint Nash and not exact root Nash.

### Proof

The probability identities (3.3)--(3.5) follow by multiplying the two
nontrivial Bernoulli factors.

The forced-owner Quit-minus-Continue endpoint difference depends only on
the opponents.  At q it is

$$
D_k(q)
=(1-η)[r_k(\{a,k\})-r_k(\{a\})]
+η[r_k(\{k\})-U_k].
\tag{3.8}
$$

The first bracket is at least γ by (2.1), and the second is at least -2M.
Therefore

$$
D_k(q)\ge(1-η)γ-2Mη
=γ-ηγ-\frac γ4.
\tag{3.9}
$$

Since η≤1/4, (3.9) is at least γ/2.

Changing k from sure Continue to a half mixture changes the complete
behavioral payoff only when the copied prehistory reaches m.  Conditional on
that event the gain is one half of D_k(q), proving (3.7).

Relative to the actual pure-singleton source, the conditional payoff change
is

$$
\frac{1-η}{2}[r_k(\{a,k\})-r_k(\{a\})]
+\frac η2[r_k(\{k\})+U_k-2r_k(\{a\})].
\tag{3.10}
$$

The second bracket is at least -4M.  Hence (3.10) is at least

$$
\frac{(1-η)γ}{2}-2Mη
=\frac γ4-\frac{ηγ}{2}\ge\frac γ8,
\tag{3.11}
$$

which proves (3.6) after multiplication by L.

Finally, `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart`
gives, because k assigns probability 1/2 to the inferior Continue action,

$$
\operatorname{defect}_k(q)
=\frac12D_k(q)\ge\frac γ4.
\tag{3.12}
$$

This proves all claims.  QED

The construction is deliberately noninfinitesimal: η is fixed by the actual
terminal gap and reward bound.  It therefore supplies genuine causal
transmission rather than a merely positive number tending to zero.

## 4. Exact defect-versus-transmission tradeoff

Keep the a hazard 1-η from (3.1), but let k Quit with an arbitrary
t in (0,1).  Denote this root qᵗ.  The endpoint difference D_k(qᵗ) is
independent of k's own mixing rate and remains at least γ/2.  Hence

$$
c(q^t)=η(1-t),\qquad
\operatorname{defect}_k(q^t)=(1-t)D_k(q^t).
\tag{4.1}
$$

Using η=γ/(8M),

$$
\operatorname{defect}_k(q^t)
\ge 4M\,c(q^t).
\tag{4.2}
$$

Thus every approximate-root sequence inside this literal descreening family
whose root defect tends to zero has joint Continue probability tending to
zero at least as fast:

$$
c(q^t)\le
\frac{\operatorname{defect}_k(q^t)}{4M}.
\tag{4.3}
$$

Taking t→1 recovers the pure screening port.  Keeping a uniform causal
transmission coefficient forces a uniform root defect.  This is the precise
tradeoff which infinitesimal desaturation does not resolve.

## 5. General complementarity no-go

The following theorem is independent of Fin4 and of the punishment floor.

### Theorem 5.1 (no exact permeable paid atom)

Let q be an exact endpoint-Nash product root at tail U.  Let S be a coalition
with positive root mass, and suppose c(q)>0.  For every k∈S:

1. q_k(Q)>0, because S has positive root mass;
2. q_k(C)>0, because c(q)>0; and therefore
3. the k endpoint difference is zero.

Consequently every unilateral change of k's marked marginal, holding the
opponents and tail fixed, has zero payoff effect.  In particular it cannot
have positive same-row best-endpoint gain.

### Proof

The first two statements are immediate from product positivity.  The third is
exactly
`quittingRootEndpointDifference_eq_zero_of_both_probabilities_pos`.
With equal pure endpoint values, every mixture has the same prescribed
successor payoff.  Multiplication by the positive reached live mass preserves
zero.  QED

### Corollary 5.2 (sharp forced-pair alternative)

Suppose a target row carries a positive atom containing the paid player k and
the literal one-date change of k has positive payoff gain.

- If the target is exact root Nash, then k cannot have positive Continue
  probability, so joint Continue is zero.
- If joint Continue is positive, then the target cannot be exact root Nash.

This conclusion does not depend on constants, topology, compactness, or
selection.  It is the support complementarity of a single exact product
root.

The scope is important.  The theorem does not forbid an exact mixed row whose
payoff exceeds the pure source because some opponent marginal also changed.
The gain in (3.6) is of that two-coordinate kind.  What is impossible is
retaining the packet's defining **one-coordinate best-endpoint gain identity**
at an exact permeable target.  The current source does not construct or
control an exact mixed row with the weaker historical two-coordinate gain.

## 6. Why the current typed source cannot contain the mixed row

The current packet adapter is endpoint-valued by construction:

- `QuittingStageAtomConcentratedPacketAdapter.action` is a Boolean;
- `targetProfile` installs `PMF.pure adapter.action`; and
- `target_markedRoot_eq` exposes that pure-coordinate update.

After the first forced update, `pairProfile_eq_purePair` makes the whole
marked row the pure pair.  The paid endpoint remains another pure routed
coalition by `payerTargetProfile_eq_pureRouted`.

Therefore σᵐⁱˣ preserves the actual table, prehistory, mark, tail, owner
labels, and quantitative lower scales, but it is not an inhabitant of the
concentrated-packet adapter's target class.  A mixed adapter would be a new
source type.  Theorem 5.1 shows that merely generalizing the type from a
Boolean action to a PMF cannot also make the target an exact root while
retaining positive direct gain.

The normalized decorated family also stores the historical gain of the pure
endpoint update.  One may carry that scalar as an external label beside an
unrelated exact mixed root, but that does not produce a literal joint
chronology or a same-row gain identity.  It would recreate the disconnected
two-port problem rather than solve it.

## 7. Relation to the uniform no-sure floor boundary

Sections 49--51 of `notes/CODEX_CEDAR__PAID_ROW_REENTRY.md` establish the
complementary floor fact.  Under the actual terminal exploitability gap γ,
every exact root at every boxed tail U≥P satisfies

$$
q_i(Q)\le1-\frac{γ}{4M}
\quad\hbox{for every player }i.
\tag{7.1}
$$

Therefore every exact floor root is uniformly permeable:

$$
c(q)\ge\left(\frac{γ}{4M}\right)^4,
\qquad
c_{-i}(q)\ge\left(\frac{γ}{4M}\right)^3.
\tag{7.2}
$$

This does not contradict Theorem 5.1.  It says exact floor roots have no sure
quitter; hence every active player is mixed and has zero endpoint difference.
Such a root cannot carry the current forced owner's positive direct gain.

The singleton-gap producer in Section 50 adds positive absorption to (7.2),
but it requires an already boxed floor tail with
U_g≤r_g({g})-δ.  The current minimum-return source does not provide this
field:

- its collision premium is r_k({a,k})-r_k({a}), not a singleton gap at a
  floor tail;
- its literal post-date prescribed payoff need not dominate punishment; and
- at a cap tail B, immediate singleton deviation gives B_g≥r_g({g}), the
  opposite inequality.

At the checked law-tight minimum cap face, the stronger theorem
`quittingLawTightCapNashSaturationMinimumFace_rootNash_iff_allContinue`
says the only exact root is all Continue.  That root has maximal permeability
and zero marked mass.  So the current downstream face also cannot supply the
desired combined row.

The floor boundary therefore removes the near-sure exact-root route, while
the present complementarity theorem removes the positive-direct-gain
interior-root route.  A future consumer must separate paid production from
exact Nashification across multiple chronological rows and prove a genuine
return/seam; one row cannot do both jobs.

## 8. Dead ends retained

1. **Desaturate only the forced owner.**  The original singleton owner still
   Quits surely, so joint continuation remains zero.  This changes neither
   law screening nor outsider-cap screening.

2. **Desaturate only the original singleton owner.**  The forced owner still
   Quits surely.  Again joint continuation is zero.

3. **Desaturate both players infinitesimally.**  This gives positive
   continuation but no uniform coefficient.  Moreover the forced owner's
   strict endpoint advantage persists, so approximate exactness pushes its
   Continue probability back to zero according to (4.3).

4. **Nashify at the same floor tail.**  The terminal gap guarantees that the
   resulting exact root is permeable, but neither the paid pair atom nor the
   paid gain is preserved.  At the checked minimum cap face Nashification
   collapses all the way to all Continue.

5. **Carry the old gain as decoration.**  This is formally possible but
   causally empty: the gain and the exact mixed row need not arise from one
   literal same-tail transition.

## 9. What remains open

The current source does produce a quantitatively useful causal row, and the
positive-gap theory produces quantitatively useful exact permeable floor
roots.  The missing object is a **multi-row exactification chronology**:

1. start from the source-faithful paid mixed row;
2. move through one or more exact roots while keeping a controlled positive
   continuation channel; and
3. repay the fixed first-row root defect/payoff displacement and return to a
   source-compatible near-minimum tail.

No current declaration connects those three steps.  The present result is a
strict local impossibility theorem, not a global no-go for a multi-row
consumer and not a uniform-equilibrium conclusion.

## 10. The minimal two-row relaxation still cannot repair the canonical row

The first natural relaxation is a literal two-row block:

$$
p\quad\text{then}\quad q\quad\text{then tail }U,
\tag{10.1}
$$

where p is the source-paid mixed row, q is an exact permeable root at U, and

$$
X=F(q,U)
\tag{10.2}
$$

is the continuation payoff seen by p.  One might hope that changing U to X
neutralizes the first-row defect while the second row supplies exactness and
the block returns near U.

For the canonical p of Proposition 3.1 this is impossible even if q is
arbitrary rather than exact.

### Proposition 10.1 (universal second-row repair no-go)

Keep

$$
p_a(Q)=1-η,\qquad p_k(Q)=\frac12,
\qquad η=\frac γ{8M},
\tag{10.3}
$$

with all outsiders Continuing.  Let τ be **any** complete behavioral
continuation after p, including an exact permeable second row followed by an
arbitrary tail.  Write X for its prescribed payoff vector.  Then

$$
|X_i|\le M
\tag{10.4}
$$

and the first-row k endpoint difference still satisfies

$$
D_k(p;X)\ge\frac γ2.
\tag{10.5}
$$

Consequently:

1. the first-row k root defect is at least γ/4;
2. changing k at that row from the prescribed half mixture to sure Quit is a
   complete behavioral deviation gaining at least Lγ/4; and
3. on the actual source prefix this gain is at least λγ/4.

No choice of q, no aggregate absorption in the second row, and no payoff
return after it can remove this first-disagreement gain.

### Proof

Formula (3.8) used only the bound -M≤U_k≤M.  Replacing U by the payoff X of
an arbitrary continuation leaves the same bound and therefore the same
calculation:

$$
D_k(p;X)
=(1-η)[r_k(\{a,k\})-r_k(\{a\})]
+η[r_k(\{k\})-X_k]
\ge\frac γ2.
\tag{10.6}
$$

The root-defect identity gives γ/4.  The deviator changes only its marked
action, so the conditional gain is exactly one half of (10.6), multiplied by
the prehistory reach L.  QED

This is stronger than failure of a two-row Bellman construction.  It excludes
every later behavioral continuation, even a nonstationary or history-rich
one, because all such continuation payoffs remain in the reward box.

### Proposition 10.2 (necessary desaturation for any exact first row)

Now allow a general first root

$$
p_a(Q)=1-ε,\qquad p_k(Q)=t,
\qquad 0<ε,t<1,
\tag{10.7}
$$

with outsiders Continuing.  Let

$$
A=r_k(\{a,k\})-r_k(\{a\})\ge γ.
\tag{10.8}
$$

If p is exact for k at a bounded continuation payoff X, then

$$
X_k=r_k(\{k\})+\frac{1-ε}{ε}A.
\tag{10.9}
$$

In particular,

$$
ε\ge\frac{A}{A+2M}
\ge\frac γ{γ+2M}.
\tag{10.10}
$$

Thus an exact first row requires a nonperturbative Continue probability for
the original singleton owner.  The canonical value γ/(8M) is strictly below
the necessary boundary because γ≤2M.

### Proof

Since k is interior, exact root Nash makes its Quit and Continue endpoints
equal.  Expanding those two endpoints gives

$$
(1-ε)r_k(\{a,k\})+εr_k(\{k\})
=(1-ε)r_k(\{a\})+εX_k,
$$

which is (10.9).  Since both X_k and r_k({k}) lie in [-M,M],

$$
\frac{1-ε}{ε}A\le2M.
$$

Rearrangement and A≥γ prove (10.10).  QED

Equation (10.9) is the exact two-row port condition.  A future producer must
make the second-row successor hit this prescribed switch value while
simultaneously satisfying the first-root conditions of a and both outsiders.
The current paid source controls none of those three additional equations.

### Proposition 10.3 (return forces second-row motion)

Assume the general first row p is exact for k at X.  Let

$$
V=F(p,X)
$$

be the block's payoff before p.  Exact indifference gives

$$
V_k=(1-ε)r_k(\{a\})+εX_k.
\tag{10.11}
$$

If q is the second row, has absorption α, has successor X=F(q,U), and the
two-row block returns with

$$
|V_k-U_k|\le ζ,
\tag{10.12}
$$

then

$$
(1-ε)|r_k(\{a\})-U_k|
\le 2Mεα+ζ.
\tag{10.13}
$$

Equivalently,

$$
α\ge
\frac{((1-ε)|r_k(\{a\})-U_k|-ζ)_+}{2Mε}.
\tag{10.14}
$$

### Proof

Subtract U_k in (10.11):

$$
V_k-U_k
=(1-ε)[r_k(\{a\})-U_k]+ε[X_k-U_k].
$$

The reverse triangle inequality, (10.12), and the checked one-row Bellman
motion estimate
`abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass`
give

$$
(1-ε)|r_k(\{a\})-U_k|
\le ζ+ε|X_k-U_k|
\le ζ+2Mεα.
$$

This proves (10.13)--(10.14).  QED

The inequality is only necessary.  It does not construct q.  It shows that
once the first row is moved far enough into the interior to permit exactness,
any payoff mismatch between the source singleton value and the final tail
must be paid by literal second-row absorption.  If the right side of (10.14)
exceeds one, a two-row return is impossible.

## 11. Relation to the aggregate-shadow and collision-budget results

This two-row no-go does not duplicate Sections 69 or 73 of
`CODEX_CEDAR__PAID_ROW_REENTRY.md`.

- Proposition 69 begins **after** an exact floor-admissible payoff shadow has
  been produced.  It proves that a closed shadow automatically carries fixed
  aggregate charge.  Proposition 10.1 says the canonical paid mixed row
  cannot be the first exact edge of such a shadow, regardless of the charge
  carried later.

- Proposition 73 begins from an already floor-safe actual carrier and
  iterates literal exact Nash predecessors.  The current minimum-return tail
  has no supplied punishment-floor field, and the canonical paid row has the
  fixed defect (10.5).  Therefore it cannot serve as Proposition 73's first
  prefix edge.

If a redesigned p satisfying (10.9) and all other root equations were
produced, then a two-row near-return with fixed charge would already be
consumed by the reviewed aggregate-block theorem behind Proposition 69.
There is no further charge problem.  The missing source theorem is exactly
the simultaneous production of:

1. a nonperturbatively descreened first root;
2. a second exact root whose successor is the switch vector required by the
   first root;
3. punishment-floor and literal-history compatibility; and
4. the return inequality (10.12).

No current declaration supplies this system.  Proposition 10.1 closes the
canonical two-row attempt; Propositions 10.2--10.3 give the exact necessary
interface for a different two-row producer.  They do not rule out a longer
nonlocal exactification chronology.

## Source declarations inspected

- `FinFourSourcePreservingForcedPairPacket.pairProfile_eq_purePair`,
  `forcedPair_stageMass_eq_liveMass`,
  `resolution_le_forcedPairStageMass`,
  `terminalGap_le_forcedOwnerDefect`,
  `resolution_mul_terminalGap_le_forcedOwnerGain`,
  `payerTargetProfile_eq_pureRouted`, and the post-date spine declarations
  in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingForcedPair.lean`;
- the corresponding minimum-return paid-row declarations in
  `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`;
- `QuittingStageAtomConcentratedPacketAdapter.action`,
  `target_markedRoot_eq`,
  `sourceToTargetGain_eq_liveMass_mul_defect`, and
  `sourceToTargetGain_lowerBound` in
  `Research/Quitting/PositiveStageAtomConcentratedPacket.lean`;
- `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`;
- `quittingRootEndpointDifference_eq_zero_of_both_probabilities_pos` in
  `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`;
- `nearSureRootReplacement` in
  `UniformEquilibrium/Quitting/Root/NearSureRoot.lean`;
- `quittingAtomicBlockerBalance_le_neg_of_terminalExploitabilityGap` in
  `UniformEquilibrium/Quitting/Boundary/Repair/AtomicBlockerCompletion.lean`;
- `abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass` in
  `UniformEquilibrium/Quitting/Debt/Marked/TimeAdvance.lean`; and
- the law-tight hull/minimum-face declarations in
  `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashSaturationHull.lean`
  and `LawTightCapNashMinimumFace.lean`.

The reviewed Sections 43--51, 69, and 73 of
`notes/CODEX_CEDAR__PAID_ROW_REENTRY.md` were used to distinguish this
fixed quantitative descreening from the already-known infinitesimal
desaturation and uniform no-sure floor boundary.  No Lean file or export was
modified.
