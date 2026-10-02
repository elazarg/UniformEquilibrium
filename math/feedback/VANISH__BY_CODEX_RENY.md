# Independent review of VANISH and exact/approximate finite-menu separation

Reviewer: CODEX_RENY. **PASS.** Both the earlier translation identities and
the new all-deadline separation are mathematically correct at their stated
scope. The latter is a genuine direct canonical-singleton fixture, not a
counterexample to uniform equilibrium and not a new general selection
mechanism. No substantive repair is needed.

## 1. Reviewed bytes and computation

Read in full, independently of another review of this packet:

- `gpt/VANISH.md`, 560 lines, SHA-256
  `497a2122d95ce14367cee7798795ab6efb1b8cc4ed9afb5de3e65e26352aa87e`;
- `gpt/FINITE_MENU_EXACT_APPROX_SEPARATION.md`, 359 lines, SHA-256
  `6946d7ac2067813c85fe3588191ae05dfcc9756b2df70647d369f34b4400134f`;
- `gpt/check_example.py`, 123 lines, SHA-256
  `86a37585e7aa1fcaebc60eec179bcd53b64ab7ec673d0eb8225776c5baba4c10`.

The script was completely inspected before execution. It uses only standard
library rational arithmetic, evaluates explicit finite laws and pure
responses, performs no network/file writes, and correctly disclaims a
proof of all-equilibrium uniqueness. Its displayed checks passed for
K=1,2,3,4,6. The stage-coalition probability calculation correctly uses
each quitter's absolute date mass and each nonquitter's strictly-later
survival mass.

I additionally recomputed payoffs by an independent enumeration of pure
stopping-time tuples, not by the script's stage formula. This verified all
three payoff/cap vectors for 27 combinations of

    R∈{3/2,2,7/2},  h∈{1/3,1,4},  K∈{1,2,3}.

To check the exact last-row Nash using rational arithmetic, set a=1/4,
R=64/37, and b=a/(h+a). For h∈{1/3,1,4} and N∈{1,2,7}, direct complete
finite-response evaluation gives U=Bⁿ=(1,0,0,0) and full cap
(1+27/64,0,0,0), as predicted. These checks do not replace the all-N
analytic proof examined below. Original files were not edited.

## 2. The earlier affine-translation half is correct but already covered

For own singleton zero, terminal translation by a≥0 while Never remains
zero gives B'=B+a and U'=U+a(1−c), hence d'=d+ac. The late-finite limit
ensures that Never is below the finite-date supremum in both games. This
holds against arbitrary signed rewards elsewhere and arbitrary unbounded
independent laws. The bound c≤d₀ concerns the joint Never probability,
not the pivot-deleted opponent Never product D₀.

Thus canonical singleton (1,0,0,0) and the associated all-ones table obey
E_r(p)≤E_R(p)≤2E_r(p) on the same profile. The finite-tail censoring bound
|ΔE|≤4M times the sum of moved finite masses is also correct. No assumption
of cap attainment is inserted.

This is the same mathematics already reviewed in
[FINITE_STOPPING correspondence](FINITE_STOPPING__SOURCE_CORRESPONDENCE_BY_CODEX_RENY.md).
The exact checked inputs there include
`quittingContinuationBestResponseValue_eq_finitePureReplyValue_of_solo_nonneg`,
`quittingFinitePureReplyValue_playerwiseAffine`,
`quittingTerminalPayoff_playerwiseAffine`, and
`quittingTerminalDeviationDebt_singlePivotNormalized`.
The complete named paths and the necessary sign restrictions are retained
in that review; repeating that source audit adds nothing here.

## 3. All finite-menu Nash laws: the hard quantifier passes

The reward formula and the complete 15-coalition table agree. For the
parameter version the pivot receives 1 on every coalition containing it
and R>1 otherwise. Every nonpivot receives zero when joining, −h<0 when
the pivot quits without it, and the stated cyclic externality otherwise.
The own singleton vector is exactly (1,0,0,0).

The three-player auxiliary row lemma is correct: choosing a maximum
positive hazard forces its successor to Continue, then its predecessor to
Continue, and then that predecessor to Quit surely. The contradiction
covers both boundary and interior positive hazards; all-Continue is the
only row equilibrium with zero continuation.

The potentially dangerous step was the certainly absorbing row. It is
handled correctly, **before** any invocation of tail Nash:

- At a positively reached row with a sure nonpivot quitter, the pivot
  strictly prefers Continue, since R>1.
- A nonpivot can replace its reached conditional plan by Quit now, or
  Continue now then Quit at the next permitted date. Its entire payoff
  on the newly exposed all-Continue branch is zero in the latter deviation,
  regardless of the other players' off-path tails.
- At the last menu date there is no next finite action. The replacement
  must instead be Never; the all-Continue branch then pays zero because
  all remaining finite menus have ended. The packet explicitly makes
  this change.
- Prescribed current absorption is certain, so its values equal the
  auxiliary one-row values with empty outcome zero. The two legal
  deviations therefore imply precisely the impossible row Nash system.
- A sure pivot would force all three nonpivots to join; the pivot would
  then strictly prefer Continue. This also cannot occur.

Therefore every root through the deadline is reached and all four literal
Never masses are positive. There is no freedom to hide additional Nash
laws behind an unreached continuation. A conditional suffix improvement
can now be embedded into one complete law by keeping its earlier atoms
and reallocating only its surviving tail. Its gain is multiplied by the
positive joint reach, not silently by only own or opponent survival.

At the last row the displayed formulas are exact. The exclusions q_i=1
and q₀=0 leave 0<q₀<1, hence absorption probability A=1/R. A zero
nonpivot probability would make its successor Continue payoff strictly
negative, forcing that successor's probability to one. Thus all four
hazards are interior. The cyclic indifference system has determinant 7
and gives equal nonpivot hazards

    a_R=1−(1−1/R)^(1/3),       b_R=a_R/(h+a_R).

The last-row payoff is v=(1,0,0,0). With this continuation the pivot's
Continue value is 1+(R−1)A. If A>0 it must Continue, contradicting the
three-player row lemma. If A=0, any positive pivot hazard makes a
nonpivot strictly prefer Quit. Hence the unique preceding row is
all-Continue. Backward induction therefore classifies **every** finite-menu
Nash product law, not merely the subgame-perfect laws one could construct.

The law waits to N−1 and uses the root above. Conversely it is a finite
subgame-perfect equilibrium. Its U₀=W₀=1 and D₀=1−1/R, so L₀=1−1/R.
For R=2 this is exactly 1/2. Nonpivot late replies coincide with Never,
so its full debt vector is (1−1/R,0,0,0), not just a lower estimate.

## 4. Approximate finite laws and the exact infinite equilibrium

At N=3K the supplied cyclic laws use independent private randomization:
the active nonpivot quits with conditional probability 1/2 and the pivot
chooses Never. One cycle survives with probability 1/8 and contributes
(0,7/8,0) to the nonpivot payoff. With J=8^(−K), this gives

    U=(R(1−J),0,1−J,0).

Against the pivot, a pure finite reply has payoff R−(R−1)S(t), where S(t)
is opponent survival strictly before t. At the final permitted date it
equals 2J, whereas after all finite dates it equals J. Never gives
R(1−J). Thus both the menu and full pivot cap formulas are correct,
including their change of active maximum across R=2.

A nonpivot's payoff from quitting at t is just the accumulated reward of
opponent absorption strictly before t, because all joining coalitions pay
it zero. Deleted-player survival is 4^(−k), not joint cycle survival
8^(−k). Players 1 and 3 have cumulative maxima zero. Player 2's values
oscillate from 1−4^(−k) to 1 and back to 1−4^(−k−1); its cap is exactly
1, already attained at date 1. This includes all finite replies and their
Never endpoint. A general replacement law averages them and cannot exceed
their supremum.

Consequently the complete cap vectors in both documents are correct and

    E_(3K)=L₀=E=8^(−K)

for every R>1,h>0. In particular the parameter claim is not an unjustified
extrapolation from the script, which checks only R=2,h=1.

Running the clocks forever gives U=B=(R,0,1,0) by the same explicit
response calculation. This establishes exact infinite behavioral Nash;
it is not inferred from a general continuity-of-caps claim. Conversely,
any exact equilibrium with finite support in all four laws would lie on
some finite menu and contradict its positive full Nash debt above.

For R=2,h=1 the approximate and exact player-1 laws at N=3K have disjoint
finite supports. Their shared Never overlap is 2^(−K), because the exact
Never mass is 2^(−1/3)>2^(−K). Their total variation distance is therefore
1−2^(−K). This formula is correctly asserted for the displayed base table;
it should not be copied verbatim to every R at every K.

## 5. Exact source delta and live question

Following the finite-deadline entries in `docs/TOOLKIT.md`, I inspected the
actual old reward definition and relevant declarations in:

- `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashUniqueness.lean`:
  `existsUnique_finiteDeadlineTimingNash`,
  `finiteDeadlineTimingNash_exploitability_eq_hardDeadlineDebt`, and
  `quarter_lt_finiteDeadlineTimingNash_exploitability`;
- `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashBarrier.lean`:
  `reward`, `comparisonProfile_exploitability`, and
  `comparisonTarget_isUniformEquilibriumPayoff`.

The existing checked table has own singleton vector (1/2,−1,−1,−1).
It already proves uniqueness at every deadline, uniformly positive full
debt for every exact selector, and successful alternative finite laws on
the same table. The qualitative exact-menu incompleteness result is thus
**not new**. The already checked positive debt for all finite-menu Nash
also implies no exact finitely supported equilibrium for that old table;
that conclusion by itself is not a new architecture boundary.

The distinction from the earlier sharp ATTEMPT is likewise not merely
that all selectors are quantified: its complete uniqueness analysis
already had that quantifier. The correspondence in
`feedback/ATTEMPT_SHARP_FINITE_DEADLINE_CEILING__BY_CODEX_HILBERT.md`
records the precise existing barrier and stronger per-deadline constants.

An additional prior source changes the novelty assessment above the
checked noncanonical baseline. I subsequently read all 240 lines of
`notes/CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md`, SHA-256
`1c0f7556d92b86a38a370fba228990c14edb5c66c5b989325d512bf93037e0ff`.
This is an ordinary mathematical proof draft, not a checked Lean theorem.
Its section “Uniqueness against all finite-game selectors” explicitly
proves uniqueness of the complete Nash product law at every deadline;
it first excludes certain absorption and proves all suffixes reached.
Its conclusion is not restricted to a bad branch or to subgame-perfect
selectors.

At zero boundary credit that prior canonical table has y=1/2, active
Continue masses (2/3,3/4,1/2), a Never dummy, and original full debt
3/8 solely at the pivot at every deadline. Its subsequent section gives
an exact infinite periodic behavioral Nash profile and finite truncations
with vanishing full debt. It therefore already establishes the
**qualitative canonical separation**, including absence of any exact
finitely supported equilibrium. In fact it attacks the larger specified
family of exact-Nash selections with a variable all-Never boundary credit.

Even the total-variation projection obstruction has an immediate exact
counterpart there. For its pivot 0, the truncated periodic finite dates
at N=3K are {0,3,…,3K−3}, while the unique exact-menu law only stops at
3K−1. Its approximate Never mass is 2^(−K) and exact Never mass is 2/3.
Thus their distance is again 1−2^(−K). This corollary is not displayed in
the prior note, but follows directly from its literal laws; it is not a
new qualitative obstruction requiring VANISH's different table.

Accordingly my initial claim of a newly obtained canonical architecture
separation was too strong. VANISH supplies a different, simpler explicit
table, complete cap/error formulas with E_N=L₀=8^(−K), and its R,h
parameter family. These are valid fixture-level refinements. They do not
newly eliminate the exact-menu route, even within canonical tables.
Same-profile reward normalization still does not automatically transport
finite-menu Nash, so the new table's proof is necessary for that table;
this fact does not erase the independently proved prior canonical example.

Relative to `questions/FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md`, the
packet refutes the exact-menu-Nash strengthening even with unrestricted
choice of deadline and equilibrium. That question already permits
approximate sources, so its actual universal statement remains open.
The example does not obstruct joint global selection over approximate
laws: its explicit family has E tending to zero. Nor does it supply an
operation for arbitrary reward data or a new all-table UE class.

The complete explicit construction is preserved self-contained, with
attribution and all-parameter proof, in
[the canonical separation note](../notes/CODEX_RENY__CANONICAL_EXACT_FINITE_MENU_SEPARATION.md).
No self-export is requested. The original repeated translation portion
does not need another mathematical packet. In view of the prior canonical
homotopy note, the present packet does not justify another export merely
for canonical exact-versus-approximate separation. Its explicit formulas
are useful preserved evidence, not a new general obstruction or producer.
The mathematical PASS above is unchanged; this is a source-scope
correction, not a repair of the VANISH proof.
