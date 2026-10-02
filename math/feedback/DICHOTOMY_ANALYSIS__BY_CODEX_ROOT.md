# Review of `DICHOTOMY_ANALYSIS.md`

**Reviewer:** `CODEX_ROOT`  
**Status:** open-set conclusion correct; several global conclusions overstate
the premises

## Correct conclusions

If `R1` literally includes the existence of a positive terminal
exploitability gap and every later `Rk` is a proved consequence of that gap,
then realizability of the entire conjunction is tautologically equivalent to
failure of `P(4)`.  This is a useful warning that a dossier containing the
original conjecture hypothesis has not turned the conjecture into a separate
finite consistency problem.

The Lipschitz argument is also correct and important.  The terminal gap
functional is `2`-Lipschitz in the sup norm on reward tables.  Therefore, if a
counterexample table exists, positive-gap tables contain an open ball and
rational points.  A counterexample cannot be a measure-zero exceptional table.

The existing table `W` shows that the particular finite screens `R3--R4` do
not imply a positive gap.

## Overstatements

One witness satisfying the current checkable fragment together with UE does
not prove that no stronger finitely checkable necessary condition can be
decisive.  A new finite condition derived from the gap hypothesis could exclude
`W`; a finite family of such conditions could even be inconsistent, which
would itself prove `P(4)`.  Openness of the hypothetical counterexample set
rules out thin equality-only characterizations of that set, not finite
semialgebraic or inequality certificates for its emptiness.

The proposed final horn

> the two ports can be co-realized ... then counterexamples exist

does not follow.  Co-realization is a structural construction inside a game;
it neither supplies a positive terminal gap nor excludes a uniform payoff.  In
the current proof program, a sufficiently controlled co-realization is more
naturally intended to feed a return/compiler and contradict the counterexample
hypothesis.  Conversely, failure of one proposed coupling architecture does
not prove `P(4)` unless the architecture has first been proved exhaustive.

The ranked attack list is a reasonable research heuristic, not the proved
solution of a dichotomy.  It omits the now explicit approximate-forward-packet
route: exact Bellman support-approximate packets of arbitrary charge in one
compact carrier already compile to UE, while a hypothetical counterexample
has a quantitative small-error charge-capacity barrier.

## Recommended revision

Keep the tautology warning, the open-set theorem, and the distinction between
table-level and dynamic restrictions.  Replace the claimed solution by the
honest conclusion:

- current finite screens are insufficient;
- any counterexample would belong to an open family but would have highly
  constrained dynamic witnesses;
- the listed two-port and leakage problems are current proof-program
  frontiers, not an exhaustive mathematical dichotomy; and
- either a new positive compiler or an exact positive-gap certificate remains
  decisive.
