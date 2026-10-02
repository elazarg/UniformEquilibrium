# Feedback on Quit-Time Compactification, Sections 7--8

Target: [`CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md)
Reviewer: `CODEX_GAUSS`
Verdict: `PARTIAL_CHECK`

## Claim checked

I checked Proposition 5 and the two-player selection boundary in Section 8.
The exact claim is that a coherent backward-induction choice of one-stage Nash
roots has signed adjusted deficits satisfying

`delta_i^(n+1)=c_i^n delta_i^n-ell_i^n`,

so positive debt is nonincreasing, but it need not tend to zero for every such
choice.  I also checked the claimed bad constant-`1/2` selection, the good
geometric selection, and its infinite stationary limit.

I did not re-review the planned-time representation or Proposition 3, which
already has separate feedback from `CODEX_CEDAR`.

## Independent check

### Backward-induction roots

Inductively, `x_n` is the actual payoff of the already constructed `n`-stage
profile.  A mixed Nash root for the one-stage game with all-Continue
continuation `x_n`, prepended to that profile, is Nash in the `(n+1)`-stage
game: after joint Continue the continuation is the prior Nash profile, and at
the new root no player gains by replacing its current mixed action.  Since a
quitting game has only the one live history at each depth, this is the usual
finite backward induction and allows complete behavioral deviations, not only
a single root deviation.

### Signed recursion

Against a deviation by player `i` to `Never`, split the new first root into an
opponent-only quitting event and joint opponent Continue.  If the former has
expected reward `w_i^n` and the latter probability `c_i^n`, then exactly

`W_i^(n+1)=w_i^n+c_i^n W_i^n` and
`A_i^(n+1)=c_i^n A_i^n`.

Thus `B_i^(n+1)=w_i^n+c_i^n B_i^n`.  The one-root value of pure Continue is
`C_i^n=w_i^n+c_i^n x_n(i)`, and root Nash gives
`ell_i^n=x_(n+1)(i)-C_i^n>=0`.  Subtracting gives precisely

`delta_i^(n+1)=c_i^n delta_i^n-ell_i^n`.

Because `0<=c_i^n<=1`, taking positive parts proves
`d_i^(n+1)<=d_i^n`.  Also
`delta_i^n=A_i^n s_i-(x_n(i)-W_i^n)`, so Proposition 3 identifies this
positive part with the actual unrestricted terminal debt of the finite profile.

The positive-limit consequences are consistent.  For a coordinate with
positive limiting debt, `delta_i^n>0` at every rank and
`delta_i^n<=A_i^n s_i`, giving a positive lower bound on `A_i^n`.  A positive
infinite product of the `c_i^n` implies `sum_n(1-c_i^n)<infinity`.  Dividing
the recursion by `A_i^(n+1)` telescopes; since `A_i^(n+1)<=1`, summability of
`ell_i^n/A_i^(n+1)` also gives summability of `ell_i^n`.

### The bad coherent selection

For

`r({1})=(1,0)`, `r({2})=(2,0)`, `r({1,2})=(0,0)`,

at continuation zero let player 1 Continue and player 2 Quit with probability
`1/2`.  Continue gives player 1 expected payoff `1`, whereas Quit gives
`1/2`; player 2 is indifferent at zero.  The root is Nash and has successor
`x_1=(1,0)`.

At continuation `(1,0)`, all Continue is Nash: player 1's solo Quit value is
`1`, and player 2 is again indifferent at zero.  Repeating this root keeps
`x_n=(1,0)`.  At deadline `N`, player 2 quits only at `N-1`, with probability
`1/2`, while player 1 chooses `Never`.  Player 1's finite-game value is `1`;
every early quit also pays `1`, the deadline collision action pays `1/2`, and
`Never` pays `1`.  A formerly unavailable quit at `t>=N` pays
`(1/2)2+(1/2)1=3/2`, so the exact debt is `1/2` for every `N`.

The recursion agrees: initially `c_1^0=1/2`, `ell_1^0=0`, and afterward
`c_1^n=1`, `ell_1^n=0`, hence `delta_1^n=1/2` for all `n>=1`.

### The good coherent selections

If the half-Quit root is chosen at every continuation, then

`x_(n+1)(1)=1+(1/2)x_n(1)`,

so `x_n(1)=2(1-2^-n)`.  It remains a Nash root: player 1's Continue value is
the displayed successor value and its Quit endpoint remains `1/2`; player 2
is indifferent.  The induced time law of player 2 has mass `2^{-(t+1)}` at
`t<N` and `Never` mass `2^-N`.  Player 1 uses `Never`, so its finite-game
Never slack is zero and its late escape charge is exactly `2^-N`; player 2's
debt is zero.  Thus the adjusted maximum is `2^-N`.

There is an even shorter good selection for this particular table: choose
player 2 to Quit surely at the first root.  This is Nash, produces payoff
`(2,0)`, and sets the opponent-`Never` factor for player 1 to zero immediately.
Subsequent all-Continue Nash roots at continuation `(2,0)` preserve zero debt.
This reinforces, rather than alters, the note's existential conclusion.

For the infinite stationary half-Quit profile, player 2 eventually quits
almost surely and the payoff is `(2,0)`.  A player-1 pure quit time `t` has
value

`2(1-2^-t)+2^{-(t+1)} = 2-3*2^{-(t+1)}`,

which approaches `2` from below; `Never` attains `2`.  Pure-time extremality
therefore bounds every behavioral deviation by `2`.  Player 2 receives zero
under every strategy.  The stationary profile is exact terminal Nash as
claimed.

## Source audit

The semantic ingredients cited in the note have the right scope:
`sSup_range_quittingTerminalPayoff_update_eq_pureTime`
(`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`) covers
unrestricted behavioral deviations by pure-time extrema, and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
is the positive endpoint after debt tends to zero.  Proposition 5 and the
selection examples are ordinary mathematics, not existing checked Lean
declarations.

## Findings

- Proposition 5's recursion and monotonicity are correct.
- Both the persistent `1/2` selection and the `2^-N` selection are exact
  coherent backward-induction Nash families.
- The infinite stationary half-Quit profile is exact terminal Nash.
- The example refutes exactly the universal statement: **for every coherent
  backward-induction equilibrium selection, adjusted debt tends to zero**.
- It does not refute the existential statement that every reward table admits
  at least one coherent selection with vanishing debt.  It also does not
  refute a root-optimizing rule which chooses among Nash roots to decrease the
  next adjusted debt.  On this example such optimization succeeds, even in
  one step by choosing sure Quit for player 2.
- A general root-optimizing rule must retain the debt-account state
  `(A_i^n,W_i^n)` or equivalent signed deficits: the continuation vector
  `x_n` alone does not determine the next adjusted-debt objective.  This is a
  formulation requirement, not a counterexample to the proposed repair.

## Suggested next move

Formulate the coherent recursion on the augmented compact state carrying
`x`, `A`, and `W` (or `x`, `A`, and `delta`) and minimize the next maximum
positive deficit over the nonempty compact Nash-root correspondence.  The
remaining mathematical question is whether a positive optimal limit forces a
contradiction or an all-behavior terminal gap; Section 8 supplies no negative
evidence against that existential optimization.

## Export assessment

The checked part is a valid sharp boundary for the planned-time route, but it
does not by itself meet the export gate: the universal selection claim is
refuted, while the conjecture-facing existential/root-optimizing producer
remains open.  No mathematical objection was found in Sections 7--8.
