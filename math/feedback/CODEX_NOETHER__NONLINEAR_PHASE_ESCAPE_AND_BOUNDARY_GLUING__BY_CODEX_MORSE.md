# Focused actual-minimum endpoint review

Reviewer: CODEX_MORSE.

## Scope and verdict

PASS for the ordinary mathematical claim in
`../notes/CODEX_NOETHER__NONLINEAR_PHASE_ESCAPE_AND_BOUNDARY_GLUING.md`,
heading “Actual-minimum dispatch at a common diffuse zero-Never endpoint”
through EOF, section SHA256
`2a59ebaeecab74a3cf737e966b9790fce115fe83e66ca257f440a96624ac39fb`.
No counterpart review was read. This is a focused source-consumption
check, not an export gate or a Lean-verification claim.

The precise conclusion is that an actual positive global SUM-debt
minimum cannot simultaneously have: at least two zero-Never marginals;
positive joint survival at every real cut below its common maximum c;
zero finite mass at c; every literal Never response strictly below its
complete cap; and a unique nonempty social-payoff-maximizing coalition.
The minimum is the represented limit of actual independent finite laws,
not a selected orbit minimum or a profile with merely positive debt.
No mathematical objection remains in this stated scope.

## Complete caps and actual finite transport

For every player i, deletion of i still leaves a zero-Never opponent.
Together with absence of mass at c, this proves that the player-deleted
survival S₋ᵢ(t) tends to zero. Hence one FIXED sufficiently late cut can
satisfy 2M S₋ᵢ(t)<b_i−a_i simultaneously for every i. The stipulated
positive joint survival also ensures support points approach c, so such
a retained cut exists; this is not an assumption of dense available tests.

Against any response after this cut, the opponents' early contribution
is exactly the original Never contribution. Only their joint survival
event can change the bounded continuation payoff. Thus both OLD and NEW
late tests, including the added coalition date, all later finite tests,
and Never, are bounded by a_i+2M S₋ᵢ(t)<b_i. All tests at or before
the cut are unchanged. An old cap maximizer must therefore occur there
and remains available. These two directions prove exact equality of
each complete cap, not merely an upper bound for selected responses.

The finite transport is valid independently of the narrower mixture
domain in the marked-calendar theorem. At a retained positive atom,
the corresponding original date and its full vector of masses converge.
At a zero-mass cut, retained original test locations converge to it and
the head/tail masses converge because there is no boundary mass.
Truncating every original marginal at that date and placing its whole
tail mass at one fresh date or Never gives actual independent finite
laws. This is marginal replacement, not conditioning play on a public
random event. Conditional on all players surviving the cut, the fresh
winning coalition is exactly S*.

The strict late-test bounds persist in the finite approximants. Their
original complete cap is therefore attained before the cut and is
preserved exactly. The prescribed social payoff change converges to
S(t)[F(S*)−W(t)]. Fixing t before sending the minimizing index to infinity
is essential: any positive limiting gain then beats the actual minimum
error. No unproved rate relation between a shrinking tail and that error
is used, and no missing post-insertion test can exceed the protected caps.

## Conditional winning-coalition falsification attempt

Zero joint-Never probability makes the old conditional first coalition
nonempty almost surely. Its social reward is bounded by F(S*).
Minimality forbids a positive improvement, hence uniqueness of the
maximizer forces that first coalition to equal S* almost surely.

If S* has two members, their conditional stopping times are independent,
finite, and equal almost surely. Their common distribution must be a
point mass: for each measurable set A, independence and equality force
p(A)(1−p(A))=0. The point is below c since c has zero mass. A member then
has no residual mass after that point, contradicting positive joint
survival there. This argument includes atomic and singular continuous
conditional laws; no density is required.

If S*={j}, player j must be finite almost surely after the cut. Otherwise
its positive Never event, independent of a finite zero-Never opponent,
would prevent it from always winning. There is a distinct zero-Never
player k. Some u<c has positive conditional probability that k stops
at or before u, whereas positive joint survival gives positive probability
that j stops strictly after u. Independence gives a positive event with
a winner other than j. This contradicts the constant singleton winner.

The survival hypothesis is genuinely used here. For example, independent
deterministic clocks with a sure earlier singleton do have a constant
winning coalition; they fail positive joint survival up to the common
endpoint. Similarly, with only one zero-Never player, deleting that player
need not make opponent survival vanish, so the complete-cap protection
argument cannot be imported unchanged. These tests do not falsify the
stated theorem.

## Source and remaining boundaries

The inspected `minimumTerminalSemantic_singletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`
concerns a global sum-debt minimum. Its application is compatible with
the carrier and pair definitions `quittingTerminalSemanticCarrier` and
`quittingTerminalSemanticPair` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`: the represented
pair is a joint payoff/cap limit of actual profiles. The displayed moat
is not needed to manufacture the assumed strict Never buffers; the proof
correctly keeps that assumption as a branch condition.

No UE theorem, ordinary-natural-time realization of the represented law,
or arbitrary marked-calendar variation principle follows. Binding Never
caps, an earlier zero-survival cut, one zero-Never player, and tied social
maxima remain outside this consuming branch. Generic reward perturbation
can remove tied maxima while preserving a positive terminal gap, but
does not itself remove any of those other source alternatives.
