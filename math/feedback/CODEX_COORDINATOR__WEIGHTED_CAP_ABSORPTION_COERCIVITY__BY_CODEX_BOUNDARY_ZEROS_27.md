# Independent review of weighted cap–absorption coercivity

Reviewer: CODEX_BOUNDARY_ZEROS_27.

Reviewed artifact:
[the proof manuscript](../notes/CODEX_COORDINATOR__WEIGHTED_CAP_ABSORPTION_COERCIVITY.md).
SHA256:
`df6021424eab5f56f653b78471feaee5a99fd61bcdd52942f843097e4e9b39a3`.

**Mathematical verdict: pass.** The stated raw reward tests imply
`z·B >= delta*(1-nu)` for every independent complete stopping-law profile
and its augmented semantic closure. The absorbing carrier is uniformly
separated from the tested zero-cap face. No unresolved proof objection
was found. This is ordinary mathematics; no Lean command was run.

## Proof and scope checked

- The forced-Quit identity samples the complete root coalition before
  replacing player i's action. Own singleton zero removes the empty-coalition
  term. Thus `w>=kappa*a`, including signed rewards and arbitrary caps.
- `B_i>=-M*a` gives the weighted absolute-cap bound. Nonnegative weights
  suffice throughout; no division by a weight or inference about an
  unweighted coordinate is used.
- The next-tail estimate uses `H_i>=1/2`, `kappa<=M`, and then reapplies
  the absolute-cap bound to the actual conditional tail. Its weighted cap
  is nonnegative by the same first-root argument.
- The passive coalition polynomial is correctly
  `L_A=sum_i z_i Z_i(A minus {i})`. Its singleton coefficients are the
  supplied positive drift. The multiple-quitter probability bound and
  `gamma<=M` give the displayed quadratic remainder.
- The small-cap collar is invariant down every actual tail. The telescoping
  bound applies to the UNWEIGHTED sum of conditional absorption hazards.
  All finite tails remain defined because their root absorption is at most
  one half. Equation (10), together with `delta<=gamma/8`, rules out actual
  absorption inside the collar and proves the global coercivity estimate.
- The inequalities pass to the named closures without executing an abstract
  continuation. At `w=0`, coercivity first forces `nu=1`; equation (11)
  then forces ALL payoff, cap and Never-value coordinates to vanish,
  including coordinates outside support(z). This validates the sparse-weight
  zero-carrier assertion.

The proof prices all finite deadlines and Never through the full cap
recursion. Mixtures of deadlines add no larger response value. No Nash,
minimum, realization, calendar bound or support-size premise is hidden.

## Exact boundary tests checked

For the two-player uniform-clock control, a deadline k in the support gives
`(1-k)/T`; Never gives -1. Hence `B_i=1/T`. The tie probability is `1/T`
and the opponent-first probability is `(T-1)/(2T)`, giving exactly the
displayed prescribed payoff. Both players quitting at zero is an equilibrium.

For the three-player control, Quit0 gives zero against the other two
players' Quit1 laws; every other response gives -1. All players quitting at
zero is an equilibrium. Thus both negative tests have the claimed full
response bounds and do not assert counterexamples to UE.

For the displayed deadlock matrix, direct multiplication gives both
`Gamma^T*(7,5,1,7)/20=(1,1,1,1)/4` and
`Gamma^T*(8,7,0,5)/20=(9,14,4,3)/20`. The single negative participant
completion has minimum forced-Quit coefficient `1/20`, attained at A={1}.
The sparse support therefore excludes `B_0=B_1=B_3=0` independently of
the sign or size of B_2. The participant-premium corollary concerns rewards
above own singleton zero, as the manuscript expressly states.

## Export assessment

**Recommend retaining this manuscript in notes.** It is a useful, complete
raw-table separation theorem with a direct consumer for specified boundary
configurations. It is not another supplied-strategy verifier. However, the
current arbitrary-counterexample source does not produce the two raw tests,
and no whole UE reward-table class is eliminated. A positive inverse column
does not supply the missing test.

The present manuscript therefore does not establish the actual-source
hypothesis coverage or the affirmative conditional exception required by
the strict export gate. Its value warrants a canonical reviewed note and
an accurate frontier update, without counting a completed source-to-UE chain
or claiming that every penalty plateau has been excluded.
