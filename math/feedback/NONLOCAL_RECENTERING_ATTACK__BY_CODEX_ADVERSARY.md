# Review of `NONLOCAL_RECENTERING_ATTACK`

**Reviewer:** CODEX_ADVERSARY  
**Verdict:** Sections 2--3 are sound.  Theorem 4.2 is repairable but its proof
omits the centre-depth extraction needed for negative-window provenance.
Lemma 4.3(2) is false as stated.  Proposition 4.4 is correct after the
extraction repair.  The surviving construction is a useful marked-kernel
compactification, but T1--T3 do not yet co-realize the R6 paid port with the
R12 saturation port and do not cross the nonperturbative source-sewing moat.

No fable, Lean, or export file was modified.

## 1. Claims checked

I checked the following claims independently.

1. the solo stationary screen and margin covering criterion;
2. the uniform nonempty-law floor on the compact minimum fibre;
3. existence and negative-half summability of the recentered hazard array;
4. convergence of truncation payoffs and unrestricted caps;
5. survival of the marked pair at the centre; and
6. the asserted identification with existing two-port and omega-chain
   machinery.

The narrow checked-source comparison used:

* `Math.Topology.SourceOmegaChain`, `nonempty_sourceOmegaChain`, and
  `SourceOmegaChain.sourceFiniteWindow_tendsto` in
  `MathUE/Topology/SourceOmegaChain.lean`;
* `FinFourBallisticNormalizedOmegaChain` in
  `Research/Quitting/FinFourProducerAtlas/BallisticNormalizedOmegaChain.lean`;
* `FinFourSourcePreservingSingletonFrame.rootStack_length`,
  `FinFourSourcePreservingCofinalSingletonPacket.sourceRank_strictMono`, and
  the frame `stage` definition in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingSingletonFrames.lean`;
* `FinFourOwnerCompressedSingletonEndpoint.anchor_le_selectedStage` and
  `anchor_eq_rank_add_one` in
  `Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean`;
* `FinFourMinimumReturnPacket.tailDebt_tendsto_minimum` in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionAtlas.lean`;
  and
* the source/provenance limitations recorded for the completion atlas in
  `docs/FRONTIER.md` and `docs/TOOLKIT.md`.

No literature claim is involved.

## 2. Sections 2--3 survive

Lemma 2.1 is correct.  Against the stationary solo owner, a pure outsider
date has gain

$$
 (1-q)^t g_{j,o}(q),
$$

over Never, so pure dates and Never give exactly the displayed screen.  The
owner cap is `max(r_j({j}),0)`.  Corollary 2.2 then follows from the fixed
terminal gap: the owner's debt is strictly below `gamma`, so some outsider's
positive part of `g` is at least `gamma`.  The candidate-B interval is also
computed correctly.

Lemma 3.1 is correct provided R5 has the universal scope stated in the
dossier: every minimum joint carrier law has some positive finite atom.  The
maximum of finitely many law coordinates is continuous and strictly positive
on the compact minimum fibre, hence has a positive minimum.

The discussion after Lemma 3.1 should not reduce the iteration gap to lower
semicontinuity of selected R6 constants.  Uniform floors would help, but the
larger missing field is same-history regeneration: R6 applied to a newly
selected minimum point may choose a different realizing chronology.

## 3. Theorem 4.2: correct conclusion, incomplete extraction

For each fixed negative window, the survival-floor calculation is correct:

$$
 \prod_{t=-s}^{-1}\prod_i(1-y_{t,i})\ge\lambda
 \quad\Longrightarrow\quad
 \sum_{t=-s}^{-1}\sum_i y_{t,i}\le\log(1/\lambda).
$$

Monotone passage in `s` gives the claimed summable negative half.

The proof nevertheless uses, without having selected it, that for every
fixed `s` one eventually has `tau_n >= s`.  The hypothesis does not state
`tau_n -> infinity`, and an arbitrary diagonal subsequence need not have
that property.

The theorem as a bare existence statement can be repaired without adding a
hypothesis: first pass to a subsequence on which either

* `tau_n` is constant; or
* `tau_n -> infinity`.

In the constant case the negative array is eventually the finite actual past
followed by zero padding, so the same bound holds.  In the divergent case the
displayed proof works and every fixed negative window is eventually an
unpadded literal source window.

For the intended **source-faithful two-sided chronology**, the divergent case
is essential.  A bounded centre creates an artificial all-Continue past by
padding and has no arbitrarily deep pre-mark provenance.  The actual
source-preserving Fin4 frames appear to supply the needed divergence, but the
adapter must be stated: source ranks are strictly increasing,
`rootStack.length = sourceRank + 1`, and the selected stage is at or after
that stack (definitionally in the selected-screening arm and by
`anchor_le_selectedStage` in the owner-clock arm).  Thus the concrete marked
dates tend to infinity.  The fable currently neither states nor cites this
adapter.

This compact extraction is not a new general omega-chain mechanism.
`Math.Topology.nonempty_sourceOmegaChain` already provides one common strict
centre subsequence and convergence of every literal centred finite window.
The genuinely additional content here is the survival-floor estimate forcing
the negative half of the limiting hazard array into `ell^1`, plus the proposed
semantic treatment of its truncations.

## 4. Lemma 4.3(2) is false literally

The quantifier `s' >= s` includes equality.  At equality, the asserted bound
becomes

$$
 |B_i(\kappa^{(s)})-max(B_i(\kappa^{(s)}),r_i(\{i\}))|
 \le4R\delta_s.
$$

But `delta_s` excludes the first retained row `-s`, so it does not pay for a
collision at that row.

### Exact counterexample

Take two players `i,j`, reward bound `R=1`, and a kernel with

$$
 y_{-1,j}=1/2,
 \qquad y_{t,k}=0\quad\text{otherwise}.
$$

Set player `i`'s relevant rewards to

$$
 r_i(\{i\})=1,
 \qquad r_i(\{j\})=r_i(\{i,j\})=0.
$$

For `s=1`, `delta_1=sum_{t<-1,k}y_{t,k}=0`.  In `kappa^(1)`, player `j`
quits at the first retained row with probability one half and otherwise
Never quits.  Any finite quitting date of `i` pays one only on the
probability-one-half branch where `j` did not quit, so

$$
 B_i(\kappa^{(1)})=1/2.
$$

Taking `s'=s=1`, the left side of Lemma 4.3(2) is `1/2` and the right side is
zero.  The example even has positive survival from the retained past to the
centre.

### Correct repair

Require `s' > s` in item 2.  The extra window then contains an earlier date
at which the deviator can approximate quitting alone, and all opponent hazard
in that window is bounded by `delta_s`.  The coupling proof gives, with the
draft's safe constant,

$$
 \left|B_i(\kappa^{(s')})-
 \max(B_i(\kappa^{(s)}),r_i(\{i\}))\right|
 \le4R\delta_s.                                       \tag{4.1}
$$

To recover convergence, separately use the newly added first row in
`kappa^(s)`:

$$
 B_i(\kappa^{(s)})\ge r_i(\{i\})-2R\delta_{s-1}
 \qquad(s\ge1).                                       \tag{4.2}
$$

Combining (4.1)--(4.2) gives, for `s'>s>=1`,

$$
 |B_i(\kappa^{(s')})-B_i(\kappa^{(s)})|
 \le4R\delta_s+2R\delta_{s-1}\longrightarrow0.
$$

Thus the cap limit, `b_i >= r_i({i})`, carrier membership, and
`D >= D_*` survive after a real proof repair.  Item 1 is sound as stated.

## 5. Proposition 4.4 survives

After the centre extraction is repaired, Proposition 4.4 is correct.  Each
finite negative-window survival is at least `lambda`, hence so is its limit
and the infinite negative-half survival.  Unconditional marked-pair mass at
least `lambda`, divided by a live probability at most one, gives conditional
row probability at least `lambda`.  The exact-pair probability is a
continuous polynomial of the centre row.  Therefore every truncation has
marked outcome probability at least `lambda^2`.

The conclusion is only marked-atom survival.  The R6 **paid gain**, payer
defect, and cap data depend on the semantic future, not merely the centre
root, and do not pass through pointwise future convergence without T1 or a
stronger uniform-functional convergence theorem.

## 6. T1--T3 do not yet sew the two ports

### T1 is a new tightness hypothesis, not an output

Pointwise convergence of future hazards does not preserve terminal laws or
unrestricted deviation caps.  An equi-tight/equi-summable future envelope
would repair terminal-law convergence, but no cited R6 declaration supplies
it; relative-timing bubbles are expressly allowed by R5/R14.  Even terminal-
law tightness must be strengthened appropriately to transport every
unilateral payoff functional if the paid defect/cap fields are to survive.

### T2 has the wrong currently proved identification

Lemma 4.3 proves only that the past-boundary semantic cap satisfies

$$
 b_i\ge r_i(\{i\}).
$$

That makes all Continue exact against the displayed cap vector.  It does not
make the boundary an R12 strict saturation port.  Missing are the killed
debt coordinate, strict off-minimum total debt, retained law, saturation
hull/minimum-face membership, and any uniqueness or neutrality statement
beyond the elementary solo inequality.

There is also an orientation mismatch.  Minimum return controls the semantic
debt of the **post-mark suffix**.  The truncations `kappa^(s)` start farther
in the pre-mark past and still include the marked absorbing row.  Their limit
need not lie on the minimum fibre merely because the post-mark tails do.
T1 should first identify the future suffix at positive times; a separate
source theorem would then be needed to connect that suffix to the R12
saturation construction.

### T3 lacks ancestry, not merely uniform constants

The implication

> tail debt returns to `D_*`, therefore R6 applies again at a later date in
> the same `sigma_n`

is not established.  Applying R6 to a limiting minimum point may select a new
joint-law lift, a new realizing sequence, and a new chronology.  The current
completion atlas explicitly does not provide outer-entrance regeneration or
equality of the regenerated target law with the original source law.

Uniform atom/reached-mass/gain floors N1 would not fix this.  One needs a
nested same-history producer with later marks `tau'_n>tau_n`, common
subsequences at every finite iteration depth, and an inverse-limit argument
showing that all finite multi-mark windows belong to one kernel.  None is
present.  Consequently the proposed multi-mark recurrence engine remains a
conditional architecture and does not cross the nonperturbative root--tail
sewing wall.

## 7. Strongest honest conclusion and novelty

After the stated repairs, Sections 4.2--4.4 prove the following useful result:

> A sequence of source marks reached with one positive survival floor has a
> subsequential centred hazard kernel whose negative half has total hazard at
> most `log(1/lambda)`.  If the same fixed pair has a positive unconditional
> mass at every centre, that mark survives in every finite-past truncation.
> The truncation semantic pairs converge to a carrier boundary whose cap
> dominates every solo reward.

The extraction itself substantially overlaps the checked `SourceOmegaChain`
centred-window machinery.  The surviving novelty is the logarithmic inert-
past estimate and, after repairing Lemma 4.3, the unrestricted-cap semantics
of the finite-past truncations.

No current result identifies that boundary with the R12 port, transports the
R6 paid fields to the kernel, produces a second same-history mark, or supplies
a terminal/uniform-equilibrium consumer.  Therefore the document should not
claim that it has produced the extension-compatible two-port kernel requested
by dossier Section 7.  It has produced the correct **ambient marked-kernel
space** in which such a coupling could be formulated.
