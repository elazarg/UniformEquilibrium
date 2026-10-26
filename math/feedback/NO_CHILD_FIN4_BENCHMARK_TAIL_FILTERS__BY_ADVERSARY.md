# Independent adversarial review of the no-child actual-tail filters

Reviewed `/tmp/FIN4_NO_CHILD_BENCHMARK_ACTUAL_TAIL_FILTERS.md`, SHA256
`df1d4a382cd5ef3254c035648fd0e7ac2df53dba15a5d0afcea90cd0848cdc02`.

**PASS, with the conditional source scope stated in the artifact.**
No unresolved mathematical objection remains. The review covers the entire
artifact, both tail Farkas arguments, the weaker dispersion hypotheses,
all conditioning steps, the I2 and direct I3 exclusions, and the exact
finite last-root control. It does not assert source existence, attainment
of a global minimum, a UE proof, a counterexample, or a new Lean theorem.

## Exact source and conditioning

The benchmark need not have distinct entries throughout a recipient row.
The strengthened statement of dispersion used here is justified by reading
the proof of `UNIFORM_THREE_OWNER_TAIL_DISPERSION.md`, Sections2–6:
nonzero Gamma forces a positive tie mass, J!=Gamma excludes contact ratio1,
and the six cross determinants distinguish the two geometric rates.
No other row-distinctness use occurs in the coupling, normalization,
compactification, unary-response convergence or final absorbing-solo
contradiction. The generic perturbation discussion is source-access
exposition, not a missing step of that universal estimate.

For M>11 the benchmark satisfies these weaker pair assumptions. I checked
its six cross determinants and the four principal joining determinants,
both at M14 and in the displayed symbolic M formulas. Therefore the estimate
is available at the literal repeated-entry benchmark, conditional on its
positive absorbing native gap. The proof does not transfer a selected
minimum across a perturbation.

The required actual-source assumptions remain explicit: independent actual
clock laws, ALL-END, zero observer debts, positive marginal Never masses,
and positive absorbing gap. They make every finite survival conditioning
well-defined and preserve independence. Zero observer debts and the
nonnegative prefix-debt decomposition give zero conditional observer debts.
ALL-END passes to the conditional law because deleted survival is positive.
No conditional cap positivity or conditional global-minimum property is used.

After the finite-support owners' final atoms, each remaining finite mass is
its original tail mass divided by its positive survival mass. Thus beta
really tends to zero along the fixed actual calendar. Any infinite observer
has arbitrarily late positive atoms. These statements do not compactify or
execute an abstract endpoint law.

## I2 and the first two I3p cases

The twelve ordered contact ratios have exactly the stated exception (p,i)
=(1,0). For that pair, the new direct ALL-END argument uses A=-1 and
C=M-1>A. If C>=0 then C a_i<=A f_i is impossible. If -1<C<0, then
C a_i>=C f_i>A f_i since 0<=a_i<=f_i and f_i>0. Hence the all-M>0
I2 exclusion does not depend on cross determinants for unrelated pairs,
including their possible degeneration at M6.

On owner sets023 and123, the specified observer has no positive participant
premium available. Its current Quit payoff is nonpositive, whereas its
Never payoff is strictly positive: each of its two remaining opponents has
positive finite and Never mass, its passive singleton rewards are+1,
and its passive pair reward is0. Applied at a supported observer atom in
the actual conditional tail, this contradicts exact observer optimality.

## Tail expansion and both Farkas combinations

For each recipient, removing events with two or more finite opponents
changes its Never payoff by O(beta^2). Removing simultaneous multiple
current atoms gives the same bound for its immediate Quit payoff. The raw
rewards are fixed and bounded, so these errors are uniform over all dates.
This proves the displayed expansion with total conditional finite mass,
without any assumption about the spacing or relative sizes of atoms.

The pivot mass bound in I3p follows exactly from
D=d_p<=2L f_p beta and dispersion, since epsilon<=f_p. In I3o the pivot
itself now uses Never and is optimal by ALL-END, so total debt is zero;
dispersion gives a fixed positive lower proportion for each of the three
observer finite masses. These are estimates on the actual tails.

I independently expanded the I3p012 combination. It is exactly

 E3+E1+(t/5)E0
 =-(1+t/5)f1+(2-t/5)f2+(5-t)a0+(10-t^2/5)a2+O(beta^2).

At an arbitrarily late observer0 atom, E0=0 and the lower bound f2>=c beta
force a1>0; hence E1=0 too. For t>10 every displayed coefficient is
negative and the f2 term has a fixed linear margin. The O(beta^2) error
cannot compensate it. The nonnegative left side is a contradiction.

The I3o013 combination is exactly

 E1+E3-E0=-f3+(5-t)a0-(t+5)a1+O(beta^2).

At a late observer0 atom the left side is nonnegative. For t>=5 its
right side has a negative linear margin from f3>=c beta. This is again a
contradiction. Thus both three-owner exclusions have the claimed scope.

## Exact finite last-root control and remaining cases

I independently recomputed the full opponent probability sums at
q=(2/5,14/23,1/2,0), with native Never continuation0, obtaining

 P=(-1/2,1/10,102/115,3/230),
 Q=(-1/2,1/10,-88/23,-259/230),
 Q-P=(0,0,-542/115,-131/115).

Because passive nonsingletons are0, the compact P formula is exact; the Q
formula uses the correction18 to the default participant value-5.
The observer equalities, quiet inequality and pivot ALL-END inequality
all hold. The active pivot is not Nash and no such claim is made.
Observer0's negative cap is possible at a descendant and prevents this
control from serving as a positive-cap global minimum. Thus it is only a
valid obstruction to eliminating F using the displayed local conditions.

The final reduction to F or I4 retains the actual-source hypothesis and
keeps inherited endpoints separate. No complete strategy-class exclusion
is claimed for those surviving cases.

## Sources and verification limits

In addition to the complete reviewed artifact, I read the actual-owner
partition and I2 source arguments in
`/tmp/FIN4_ACTUAL_MINIMUM_OWNER_PARTITION.md` and
`/tmp/FIN4_I2_PAIR_TAIL_RESTRICTIONS.md`, and the full applicable dispersion
proof in `math/exports/UNIFORM_THREE_OWNER_TAIL_DISPERSION.md`.
Exact rational calculations reproduced the local control and pair guards.
The proof is ordinary mathematics; no Lean or Lake command was run.

Canonical combined record: [no-child benchmark](../notes/CODEX_COORDINATOR__NO_CHILD_FIN4_BENCHMARK.md).
The reviewed stationary/coverage and actual-tail components are retained
together there; the component hashes above identify the review scope.
