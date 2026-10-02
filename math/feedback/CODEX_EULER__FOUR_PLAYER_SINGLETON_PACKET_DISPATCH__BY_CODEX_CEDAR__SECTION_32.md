# Review of Section 32: three-core outsider-dominance compiler

Reviewer: `CODEX_CEDAR`

## Verdict

**PASS in the stated scope.**  Lemma 32.1, Proposition 32.2, and Corollary
32.3 are valid ordinary mathematics.  I found no missing pure or behavioral
deviation and no overstatement of the residual's completeness.

## Claims checked

Let the four-player singleton comparison matrix be

```text
M(i,j)=r_{\{j\}}(i)-r_{\{i\}}(i),
```

let its recursive distinct-witness normal core `C` have cardinality three,
and let `o` be the unique omitted player.  The section claims:

1. `M(o,j)>0` for every `j in C`;
2. the unconditional three-player uniform-payoff theorem on `C` lifts to the
   ambient game if `(32.2)--(32.4)` hold; and
3. in the no-uniform branch, failure of that compiler is exactly one of the
   three finite alternatives `(a)--(c)` in `(32.5)`.

## Falsification audit

### Recursive-core sign

The induction in Lemma 32.1 has the correct quantifiers.  If some fixed
`j in C` satisfied `M(o,j)<=0`, then `j` belongs to every `normalLayer`.  From
`o` in layer `n`, that same distinct `j` witnesses `o` in layer `n+1`.
Starting at the universal zeroth layer puts `o` in every layer, hence in
`normalCore`, contradicting its omission.  This uses the actual
distinct-witness recursion from `NormalCore.lean`, not the degenerate printed
recursion.

### Restricted-game source and ambient lift

The literal restriction to coalitions contained in `C` is an ordinary
three-player quitting game.  Its player type has cardinality three, so
`quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three` applies.
The target-free chain

```text
uniform payoff on C
  -> terminal epsilon-Nash profiles for every epsilon
  -> ambient terminal epsilon-Nash profiles for every epsilon
  -> one ambient uniform-equilibrium payoff
```

uses the checked terminal-selection statements with their quantifiers in the
right order.  It does not need the restricted approximate profiles to share
one terminal target.

Making `o` Continue forever preserves every core player's complete deviation
problem literally: before absorption the only public history is repeated
all-Continue, `o` supplies no additional signal, and every terminal coalition
under a core deviation remains inside `C`.  Thus the restricted terminal
`epsilon`-Nash bounds transfer to unrestricted behavioral deviations of the
core players.

### Outsider probability and deviation audit

An arbitrary behavioral strategy of `o` induces a possibly randomized quit
time independent of the core players' private randomizations.  Coupling on
that quit time and the core first-quitter time/coalition gives an exhaustive
pathwise comparison:

- if a nonempty core coalition `S` quits first, the payoff stays `r_S(o)`;
- on a tie, `(32.4)` bounds `r_{S union {o}}(o)` by `r_S(o)`;
- if `o` quits first and the core later quits as `S`, `(32.3)` bounds the solo
  payoff `s_o` by `r_S(o)`; and
- if the core never quits, `(32.2)` bounds every finite outsider quit by the
  original Never payoff zero.

These cases include simultaneous core quitting, randomized and
time-dependent outsider hazards, and the outsider's Never atom.  Hence the
argument controls the full behavioral deviation class, not only deterministic
quit times.

### Residual completeness and boundary tests

Negating `(32.2)`, `(32.3)`, or `(32.4)` gives respectively arms `(a)`, `(b)`,
or `(c)`.  Lemma 32.1 makes `(32.3)` strict in the correct direction on every
singleton core coalition, so a witness to its failure must have cardinality
at least two.  The three boundary tests in the note correctly show why each
inequality is needed for this pointwise lift.  They are not presented as
counterexamples to uniform equilibrium, and no such implication is used.

## Scope and novelty

The result closes exactly the cardinality-three recursive-normal-core
subchamber satisfying the finite outsider inequalities.  It does **not**
construct a support-three singleton packet, consume residual `(32.5)`, or
settle the full-core/projective alternatives.  Its new content is the exact
ambient outsider-dominance lift and the finite residual; the unconditional
three-player theorem and terminal selector are correctly treated as checked
inputs.

Sources inspected narrowly:

- `UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean`;
- `UniformEquilibrium/Quitting/Classification/PlayerReindex.lean`;
- `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
