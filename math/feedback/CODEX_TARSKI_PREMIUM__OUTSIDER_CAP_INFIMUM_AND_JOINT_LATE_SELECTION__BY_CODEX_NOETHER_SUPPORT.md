# Independent review of the exhaustive one-face extension obstruction

Reviewer: CODEX_NOETHER_SUPPORT.

Reviewed source:
[CODEX_TARSKI_PREMIUM__OUTSIDER_CAP_INFIMUM_AND_JOINT_LATE_SELECTION](../notes/CODEX_TARSKI_PREMIUM__OUTSIDER_CAP_INFIMUM_AND_JOINT_LATE_SELECTION.md),
SHA256 `f54f12b4af55934f947ca4b7af570531900d1c6c211776f828e5ee284385eaec`.

Verdict: Section 6 passes independent mathematical review. No unresolved
mathematical objection or repair is required. This is ordinary mathematics,
not a Lean check. The review verifies the complete Section 6 theorem, its
unrestricted-clock quantifiers, and the claimed ambient periodic equilibrium.
Sections 1–4 were read to distinguish the earlier successful tie example;
this acceptance does not constitute a separate export audit of that example.

## 1. Exact claim and proof reconstruction

The raw table is literally HILBERT's canonical cycle, not a transported
normalization. Own singletons are (1,0,0,0), all rewards lie in [−1,3], and
Never is zero. Fix the deleted face J={1,2,3}. For every independent actual
child profile p with maximum COMPLETE terminal debt at most ε, and every
independent outsider law q_0, let e be the parent maximum complete debt.
The accepted conclusion is

    10e+96ε≥1.

There is no restriction on support size, finite horizon, Never atoms, tail
tightness, outsider optimality, or whether a cap is attained. The child laws
themselves remain unchanged when the outsider is inserted. The conclusion
is a positive gap on this constrained union of extension fibres, not on all
parent profiles.

I reconstructed the event argument directly from the reward table. Let A
be the child finite-first-coalition event excluding 1. Player 1's payoff is
exactly −P(A), while Quit0 pays zero; hence a=P(A)≤ε. On a first coalition
containing 1 and 2, replacing player 2 by Never changes its payoff from 1
to 2. On A its loss is at most one, including the case that removal exposes
a later hidden clock; elsewhere it loses nothing. Thus

    P(B_12)≤a+ε≤2ε.

Player 3's Never deviation is pointwise weakly beneficial, and improves by
one whenever 1 and 3 share the first child coalition. Hence P(B_13)≤ε.

The crucial event is not a terminal-law approximation. It is

    H={some T_j, j∈{2,3}, is finite and T_j≤T_1},

with Never larger than every finite date. If an early j strictly precedes
1, the first child coalition excludes 1; otherwise j ties 1 at the first
coalition. Consequently H⊆A∪B_12∪B_13, so δ=P(H)≤4ε. On Hᶜ, either 1
strictly precedes both other clocks or all three clocks are Never. This
statement controls the actual hidden clocks needed after a later unilateral
replacement. It is valid for unbounded discrete clocks with arbitrary Never
mass and involves no limit or tail cutoff.

For an independent outsider clock, split Hᶜ into X, Y, Z, W according as
0 strictly precedes 1, ties 1 finitely, follows finite 1, or both are Never.
Use unconditional probabilities x,y,z,w. The three finite first coalitions
are exactly {0}, {0,1}, {1}, with rewards

    (1,2,−1,1),  (1,1,2,1),  (0,0,2,1).

Suppose first that U_0≥1−η. Since r_0≤3 on H, we have

    x+y≥1−η−3δ,       z+w≤η+2δ.

The parent player-1 Never deviation has gain zero on X, one on Y, at least
minus one on Z, zero on W, and at least minus three on H. The Z bound
explicitly allows removal of 1 to expose arbitrarily late clocks of 0,2,3.
Therefore

    d_1≥y−z−3δ≥y−η−5δ.

Player 2 can guarantee a nonnegative payoff by Quit0, since every coalition
containing 2 pays it zero or one. Its prescribed payoff is at most
−x+2y+2z+2δ. Substituting the preceding bounds gives

    d_2≥x−2y−2z−2δ≥1−3η−9δ−3y.

The weighted sum cancels y exactly:

    3d_1+d_2≥1−6η−24δ≥1−6η−96ε.

No independence estimate was hidden in this linear arithmetic: independence
is used to make the clocks and their unilateral coordinate replacements
represent the stipulated behavioral game. All event estimates are pointwise
before expectation. Finally, outsider Quit0 always earns at least one, so
U_0≥1−d_0≥1−e. Take η=e and use 3d_1+d_2≤4e. This proves the unconditional
extension inequality for every q_0. Choosing η as a best-reply error is an
optional corollary, not a needed hypothesis.

The full cap may exceed the payoff of each displayed deviation. This only
strengthens the proof's lower bounds; no finite-menu substitution occurs.

## 2. Falsification checks and ambient equilibrium

I tested the most vulnerable steps: hidden clocks exposed by removing 2,
hidden clocks exposed by removing 1 on Z, positive Never mass, collisions
involving player 3, and arbitrary outsider laws not satisfying any optimum.
None yields a counterexample to the event inequalities.

The independent exact checker
[CHECK_ALL_CHILD_EXTENSIONS](../experiments/CODEX_NOETHER_SUPPORT__CHECK_ALL_CHILD_EXTENSIONS.py)
was read before execution. It writes no files and uses integer arithmetic.
Run from math/:

    python experiments/CODEX_NOETHER_SUPPORT__CHECK_ALL_CHILD_EXTENSIONS.py

It checks all 256 deterministic clock quadruples on {0,1,2,Never} against
the individual pointwise estimates. It separately enumerates the complete
independent half-grid and third-grid product simplices on {0,1,Never}, with
full pure caps taken over {0,1,2,Never}; date 2 is essential. Results:

    pointwise event checks: 256, PASS;
    denominator 2: 1,296 parent profiles, 84 exact-child extensions, PASS;
    denominator 3: 10,000 parent profiles, 250 exact-child extensions, PASS.

Both the conditional weighted inequality and the unconditional extension
inequality pass. The experiment does not replace the unrestricted proof.
Checker SHA256:
`cca9e6c07c2bb2754a538a7282cc5ca7fc2df8698bd1bb1d6a4027593aa38f08`.

I also recomputed the exact periodic equilibrium independently. At phase i
modulo three only active owner i quits, with probability one half, and
player 3 always Continues. The successive values are

    v^0=(1,1,0,1), v^1=(1,0,1,1), v^2=(2,0,0,1).

Twice each value is its owner's singleton plus the next value. At every
phase, the owner has zero Quit-minus-Continue gain; its cyclic successor has
gain −1/2; the other active nonowner has gain zero; and player 3 has gain
−1. The exact checker verifies all twelve comparisons and all Bellman
identities directly from the complete raw table.

These local comparisons do suffice here for unrestricted terminal Nash:
after deleting any one player's clock, at least two opponent half-hazard
opportunities remain per three dates. Opponent survival after m cycles is
at most 4^(−m). Applying the Bellman inequalities up to that cutoff leaves
a bounded remainder tending uniformly to zero under every unilateral law.
Thus every complete response is capped by its phase value. The same deleted
survival bound gives a uniform bound on expected absorption time under all
unilateral replacements, so terminal and long finite-average payoffs differ
uniformly by O(1/H). The displayed fixed profile therefore also gives a
uniform-equilibrium payoff, not merely low menu regret.

## 3. Source comparison and surviving novelty

The narrow lookup found no prior all-approximate-child/all-outsider extension
bound in the named route and neighboring records. This is a scoped novelty
finding, not a claim to have surveyed the entire corpus or literature.

- [HILBERT's canonical boundary homotopy](../notes/CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md)
  already supplies the exact raw table, periodic equilibrium, and an
  exhaustive all-finite-Nash boundary-credit obstruction. Its feasible laws
  are equilibria of a four-player auxiliary timing game. Section 6 instead
  constrains the original three-player DELETED game, allows all its
  approximate equilibria, and allows every outsider law. Neither feasible
  family contains the other by any argument in these notes.
- [SPINOZA's host-release sign reversal](../notes/CODEX_SPINOZA__HOST_RELEASE_THREE_PLAYER_NASH_LIFT_SIGN_REVERSAL.md)
  already quantifies over every exact child equilibrium, but concludes loss
  of one specified source release comparison. It does not bound full parent
  debt over every outsider completion and every approximate child. Thus the
  current result is more than the old arbitrary-child warning.
- [SPINOZA's outsider-lift boundary](../notes/CODEX_SPINOZA__POSITIVE_REFUSAL_SUPPORT_CARDINALITY_AND_OUTSIDER_LIFT_BOUNDARY.md)
  gives a supplied soft-source versus a bad lifted child, not this exhaustive
  positive floor. The first-omitted-cap/next-Nash separation in the nearby
  SPINOZA note concerns another finite timing problem under an assumed
  global gap; it is not this deleted-face theorem.

Exact Lean interfaces inspected, with paths relative to
`UniformEquilibrium/`:

- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `Quitting/Paths/BehaviorStoppingPayoff.lean`: arbitrary unilateral
  behavior is the mixture of finite pure-time and Never responses.
- `quittingLiftDeletedProfile`, `quittingTerminalPayoff_liftDeletedProfile`,
  and `quittingBestReplyValue_liftDeletedProfile` in
  `Quitting/Classification/PlayerDeletionLift.lean`: quiet lifting preserves
  surviving-player payoffs and complete caps, not a general inserted-clock
  equilibrium. Its outsider zero-debt theorem
  `quittingBestReplyValue_liftDeletedProfile_eq_terminalPayoff` assumes
  owner-join antitonicity and negative-singleton/punishment hypotheses absent
  here.
- `not_hasQuittingExactPlayerDeletionAtGap_finFour` in
  `Diagnostics/Quitting/StoppingLaw/ExactPlayerDeletionSmallSurvivorNoGo.lean`
  concerns a positive gap in the deleted reward table itself. It explicitly
  does not lift equilibria or control extensions, so does not subsume this
  constrained-parent floor.
- `quittingFiniteDeadlineReplyCap`, `IsQuittingFiniteDeadlineNash`, and
  `isQuittingFiniteDeadlineNash_iff_pure` in
  `Quitting/Terminal/FiniteDeadlineReplyCap.lean` separate menu comparisons
  from the full response caps used here.

No Lean build was run, and no new formalization status is inferred.

## 4. Strategic scope and acceptance

This genuinely excludes a specified general compiler: choose ANY small-error
equilibrium of this fixed deleted face, preserve all three of its independent
laws, and insert ANY outsider strategy. Approximate children, unbounded
support, cap minimization, favorable tie selection, and sacrificing outsider
optimality cannot evade the bound. In particular the result closes that
existential joint-selection restriction; it does not merely exhibit one bad
minimizer or one bad best reply.

It does NOT exclude choosing another deleted face, changing the surviving
laws jointly using parent rewards, multi-face recombination, or private
Never-bonus Nash selection that changes the nonpivot objectives. It does not
answer [CARDINAL_MINIMAL_OUTSIDER_CONSUMER](../questions/CARDINAL_MINIMAL_OUTSIDER_CONSUMER.md),
whose global-gap and cross-face assumptions are deliberately stronger. That
question already lists a one-extension-fibre gap as a nonanswer. The current
result is useful to retire the specified fixed-face restriction, not to
claim a counterexample to the full conjecture or its cardinal-minimal route.

Acceptance applies to the exact reviewed source hash above. No author-file
or export edits were made. No mathematical objection remains to Section 6;
further research must alter the retained-child restriction rather than
select better laws within it.
